// HZH
// Version: 2.3
// Date 2023-04-04

using System;
using System.Security.Cryptography;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Net;
using System.Windows;
using System.Windows.Controls;
using Newtonsoft.Json.Linq;
using System.Windows.Media;
using System.Xml;
using System.Data.Odbc;
using System.Threading.Tasks;

/*
 * OVERVIEW
 * Help identify updates for deployment to Lenovo fleet of devices: 
 * Prerequisites: 
 * https://www.anoopcnair.com/sccm-third-party-software-updates/
 * https://www.anoopcnair.com/lenovo-update-catalog-v3-for-sccm-third-party/ 
 *
 * Program will download Lenovo updates CAB to a temporary folder when "Check Update" is clicked.
 * A hash will be generated of the CAB file and stored on disk. 
 * CAB will be expanded into appropriate directories. 
 * Note, subsequent clicks of "Check Update" will download updates CAB and match previously file hash 
 * the newly downloaded updates CAB. A difference in hash will indicate new updates from Lenovo which 
 * will then expand the CAB into approproate directories and save new hash to disk. 
 * A match in hash value for previous and newly downloaded CAB will bypass expanding the CAB
 * 
 * Clicking "Select Update" after having selected the desired model will query WSUS DB and SCCM DB 
 * to obtain the UpdateID and CI_ID data and populate LenovoUpdate POD (plain old data) instances. 
 * Based on the model selected: 
 * 1) Model is searched for in JSON of V3 directory. 
 * 2) JSON is searched for whereby the "ParentId" matches the desired model.
 * 3) Values (GUID) of "Members" key of JSON files found in step 2 (BIOS, Drivers & Software) are identified. 
 * 4) GUID of members are searched for in SDP files of V2 directory. Note, these are in XML format. 
 * 5) XML parsed to obtain update name (Title) and KBArticleID node values
 * 6) Gathered information updated to appropriate LenovoUpdate POD instances as a means of storage. 
 * 7) Using matched data from 3 locations (WSUS, SCCM & CAB), PowerShell script is generated based 
 * on user selection. 
 * 
 * Any new model that needs to be added will require searching for specific model name in the extracted
 * CAB and populating the array named "model_list" and recompiling. 
 * 
 * CHANGES - version 2.2
 * 1) Drop down to select DomainB or DomainA WSUS/SCCM dbs. 
 * 2) Add DomainB Lenovo models in the drop down. 
 * 3) Severity column after KB name in selection screen. 
 * 4) Add IsSuperseded clause in SCCM SQL query. 
 * 5) Write to log the GUIDs of model and members so user can manually search CAB exract and WSUS and SCCM 
 * so as to manually step through the process if any suspecion of workflow issues. 
 * 6) Ensure status label updates properly. 
 * 7) Exception handling - logs points and exception to error.log 
 * 8) Modify SCCM SQL query to only include non superseded, non declined updates that are required as per
 * SCCM software update console i.e. "Required" column > 0
 * 
 * CHANGES - version 2.3
 * 1) Add find_sdp_btn_click & associated UI button which allows operator to find SDP (update files)
 * using keyword search. This is to be used for troubleshooting purposes when SCCM/WSUS identifies
 * previously valid updates as superseded (yellow icon) in SCCM console post publishing / sync.
 * 2) Modify create_sug_script method to include PowerShell commands for auto-publishing identified
 * updates. 
 * 
 * TODO - 
 * Option to auto-generate SUG name / description which will populate it with predefined name/desc.
 * a) Lenovo T470s - 20XG - All Required
 * b) Lenovo T470s - 20XG - Deployed
 */

namespace LUI
{
    public partial class MainWindow : Window
    {
        // wsus
        private string wsus_sql_svr;
        private string wsus_db;

        // sccm
        private string sccm_sql_svr;
        private string sccm_db;

        private static string dropbox_model_selection; // dropdown box model selection 
        private static string model_ID; // holds GUID of appropriate model i.e. value of "Id" in JSON
        private static string json_with_updates; // holds filename (GUID) of JSON with all appropriate updates for model

        // temporary placeholders and toggle
        private static string model_placeholder;
        private static string id_placeholder;
        private static bool json_with_updates_found = false;
        private static bool cannot_connect_to_dbs;

        // Used to write to log.txt (breadcrumbs) - non member info i.e. model etc. 
        private static List<string> breadcrumb_update_categories = new List<string>();
        // Used to write to log.txt (breadcrumbs) - key: KB, value: members (updates)
        private static Dictionary<string, string> breadcrumb_members = new Dictionary<string, string>();
        // valid KBs as per WSUS info
        private static HashSet<string> valid_wsus_kbs = new HashSet<string>();
        // holds all values of members from drivers, software & utilities and BIOS JSON files with ParentId as model_ID
        private static HashSet<string> model_specific_updates = new HashSet<string>();
        // {model guid: [title, article id, severity], n}
        private static Dictionary<string, List<string>> update_collection = new Dictionary<string, List<string>>();
        // cleaned version (no superseded updates)
        private static Dictionary<string, List<string>> cleaned_update_collection = new Dictionary<string, List<string>>();
        // final version to be made available with tick box UI for extraction
        private static Dictionary<string, List<string>> cleaned_valid_update_collection = new Dictionary<string, List<string>>();
        // superseded updates (as listed in SDP file under <sdp:SupersededPackages> node)
        // to be used for creation of clean collection with no superseded updates
        private static HashSet<string> superseded_updates_per_sdp = new HashSet<string>();
        // second filter for removing superseded updates & not required updates from check list screen
        private static List<string> superseded_and_not_required_updates = new List<string>();
        // contains mapping of title, description, articleID, updateId & ci_id. Collection of POD instances.
        List<LenovoUpdate> kb_repo = new List<LenovoUpdate>();
        // contains list of SDP file names used for finding keyword in "title" field of SDP
        // mapped as {SDP filename : Title, n}
        private static Dictionary<string, string> keyword_match_sdp_collection = new Dictionary<string, string>();

        // required directories & files
        private string prev_cab_dir = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "prev_cab");
        private string extracted_dir = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "extracted");
        private string script_dir = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "script_output");
        private string error_log = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "error.txt");
        private string log_update_export = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "log.txt");
        private string keyword_export = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "keyword_searches.txt");

        private string[] model_list = { // Only models which are available fleet of devices.
            "ThinkPad T14S Type 20UH 20UJ",
            "ThinkPad T14S Gen 2 Type 20XF 20XG",
            "ThinkPad T14S Gen 3 Type 21CQ 21CR",
            "ThinkPad X12 DETACHABLE Gen 1 Type 20UW 20UV",
        };

        public MainWindow()
        {
            InitializeComponent();

            // check if folders and files exist and create them if not
            if (!Directory.Exists(prev_cab_dir))
            {
                Directory.CreateDirectory(prev_cab_dir);
            }
            if (!Directory.Exists(extracted_dir))
            {
                Directory.CreateDirectory(extracted_dir);
            }
            if (!Directory.Exists(script_dir))
            {
                Directory.CreateDirectory(script_dir);
            }
            if (!File.Exists(error_log))
            {
                File.Create(error_log);
            }

            // populate ComboBox with items from models array
            foreach (string model in model_list)
            {
                drpbox_models.Items.Add(model);
            }

            // populate tenancy options
            drpbox_tenancy.Items.Add("DomainA");
            drpbox_tenancy.Items.Add("DomainB");
        }

        private async void check_updates(object sender, RoutedEventArgs e)
        {
            async void expand_cab()
            {
                // expand the cab file using expand.exe in separate process
                ProcessStartInfo psi = new ProcessStartInfo
                {
                    FileName = "expand.exe",
                    Arguments = $"-F:* \"{prev_cab_dir}\\LenovoUpdatesCatalog2v2.cab\" \"{extracted_dir}\"",
                    UseShellExecute = false,
                    RedirectStandardOutput = true,
                    CreateNoWindow = true // hide the process window
                };
                Process process = new Process { StartInfo = psi };
                process.Start();
                string output = await process.StandardOutput.ReadToEndAsync();
                process.WaitForExit();

                lbl_status.Content = "Metadata updated. Ready to proceed.";
                lbl_status.Foreground = Brushes.Green;
            }

            // update status label
            lbl_status.Content = "Pulling & processing CAB, please wait.";
            lbl_status.Foreground = Brushes.Red;

            // set security protocol to TLS 1.2
            ServicePointManager.SecurityProtocol = SecurityProtocolType.Tls12;

            // download the cab file to root dir - always download when clicked
            using (var client = new WebClient())
            {
                string cab_url = "https://download.lenovo.com/luc/v2/LenovoUpdatesCatalog2v2.cab";
                string cab_file = "LenovoUpdatesCatalog2v2.cab";
                await client.DownloadFileTaskAsync(cab_url, cab_file);
            }

            // check if cab previously downloaded in "prev_cab"
            if (File.Exists(Path.Combine(prev_cab_dir, "LenovoUpdatesCatalog2v2.cab")))
            {
                // check hash - if different then overwrite downloaded cab to prev_cab dir
                string cab_hash_prev = File.ReadAllText("cab_hash.txt").Trim();
                string cab_hash_new = get_file_hash(Path.Combine(prev_cab_dir, "LenovoUpdatesCatalog2v2.cab"));

                if (cab_hash_prev == cab_hash_new)
                {
                    lbl_status.Content = "Identical hash. Ready to proceed.";
                    lbl_status.Foreground = Brushes.Green;
                }
                else // new metadata delete all files and expand cab similar to first time
                {
                    // clear the extracted directory
                    Directory.Delete(extracted_dir, true);
                    // move new cab into appropriate directory
                    write_hash_val_to_file(cab_hash_new, "cab_hash.txt"); // new hash store
                    File.Move("LenovoUpdatesCatalog2v2.cab", Path.Combine(prev_cab_dir, "LenovoUpdatesCatalog2v2.cab"));
                    expand_cab();
                }
            }
            else // first time
            {
                string cab_hash_prev = get_file_hash("LenovoUpdatesCatalog2v2.cab");
                write_hash_val_to_file(cab_hash_prev, "cab_hash.txt");
                File.Move("LenovoUpdatesCatalog2v2.cab", Path.Combine(prev_cab_dir, "LenovoUpdatesCatalog2v2.cab"));
                // calculate hash and store
                expand_cab();
            }
        }

        private List<LenovoUpdate> query_wsus_db_latest_KBs(string wsus_sql_svr, string wsus_db)
        {
            // query WSUS DB to obtain all the 3rd party catalogue update information
            // fields of importance & interest include DefaultTitle & UpdateId - which are needed to identify CI_ID information for updates
            string connection_string = $"Driver=ODBC Driver 17 for SQL Server;Server={wsus_sql_svr};Database={wsus_db};Trusted_Connection=yes;";
            List<LenovoUpdate> updates = new List<LenovoUpdate>();

            using (OdbcConnection connection = new OdbcConnection(connection_string))
            {
                string query = "select DefaultTitle, DefaultDescription, MsrcSeverity, KnowledgebaseArticle, RevisionNumber, UpdateId from PUBLIC_VIEWS.vUpdate where UpdateSource = 'other' and IsDeclined = 0; ;";

                try
                {
                    OdbcCommand command = new OdbcCommand(query, connection);
                    connection.Open();

                    using (OdbcDataReader reader = command.ExecuteReader())
                    {
                        while (reader.Read())
                        {
                            LenovoUpdate update = new LenovoUpdate(); // new POD instance
                            update.DefaultTitle = reader.GetString(0);
                            update.DefaultDescription = reader.GetString(1);
                            update.MsrcSeverity = reader.GetString(2);
                            update.KnowledgebaseArticle = reader.GetString(3);
                            update.RevisionNumber = reader.GetString(4);
                            update.UpdateId = reader.GetString(5);

                            updates.Add(update); // append to POD collection (list)

                            valid_wsus_kbs.Add(reader.GetString(3)); // used to ensure selection window only lists valid updates from WSUS
                        }
                    }
                }
                catch (Exception ex)
                {
                    log_exception("Point: A", ex.Message);
                    cannot_connect_to_dbs = true;
                }
            }
            return updates;
        }

        private void commit_breadcrumbs_to_disk(string sug_name)
        {
            /* Write to log.txt upon exporting of powershell script the following info:
             * Date | time
             * Model
             * Model UID
             * BIOS: UID
             * Update: UID
             * Software: UID
             * Members: 
             * x\n
             */
            try
            {
                using (StreamWriter writer = new StreamWriter(log_update_export, true))
                {
                    DateTime now = DateTime.Now;
                    writer.WriteLine("************************************************************************");
                    writer.WriteLine(now);
                    writer.WriteLine($"SUG Name: {sug_name}");
                    writer.WriteLine($"Model: {dropbox_model_selection}");
                    writer.WriteLine($"Model UID: {model_ID}");
                    writer.WriteLine("Update Category UIDs:");
                    foreach (string category in breadcrumb_update_categories)
                    {
                        writer.WriteLine(category);
                    }

                    writer.WriteLine("Update (members):");
                    foreach (KeyValuePair<string, string> pair in breadcrumb_members)
                    {
                        writer.WriteLine($"KB: {pair.Key}  |  SDP File: {pair.Value}");
                    }
                    writer.WriteLine("************************************************************************\n");
                }
            }
            catch (Exception ex)
            {
                log_exception("Point: B", ex.Message);
            }
        }

        private void obtain_ci_id_sccm_db(string sccm_sql_svr, string sccm_db)
        {
            // based on 3rd party catalogue update information obtained from WSUS, query SCCM DB to obtain
            // CI_ID information for each update. Update the master POD collection (list) kb_repo.
            string connection_string = $"Driver=ODBC Driver 17 for SQL Server;Server={sccm_sql_svr};Database={sccm_db};Trusted_Connection=yes;";

            using (OdbcConnection connection = new OdbcConnection(connection_string))
            {
                try
                {
                    connection.Open();
                    foreach (var kb in kb_repo)
                    {
                        string query = $"select v_UpdateCIs.CI_ID, CI_UniqueID, IsSuperseded, v_Update_ComplianceSummary.NumMissing from v_UpdateCIs join v_Update_ComplianceSummary on v_UpdateCIs.CI_ID = v_Update_ComplianceSummary.CI_ID where v_UpdateCIs.CI_UniqueID = '{kb.UpdateId}';";
                        OdbcCommand command = new OdbcCommand(query, connection);
                        using (OdbcDataReader reader = command.ExecuteReader())
                        {
                            while (reader.Read())
                            {
                                kb.ci_id = reader.GetString(0);
                                if (reader.GetString(2) == "1")
                                {
                                    superseded_and_not_required_updates.Add(kb.KnowledgebaseArticle); // list of superseded KB articles
                                }
                                if (reader.GetString(3) == "0")
                                {
                                    superseded_and_not_required_updates.Add(kb.KnowledgebaseArticle); // 0 required in SCCM Software Update column
                                }
                            }
                        }
                    }
                }
                catch (Exception ex)
                {
                    log_exception("Point: C", ex.Message);
                    cannot_connect_to_dbs = true;
                }
            }
        }

        public class LenovoUpdate // POD - store all relevant information for individual updates
        {
            public string DefaultTitle { get; set; }
            public string DefaultDescription { get; set; }
            public string MsrcSeverity { get; set; }
            public string KnowledgebaseArticle { get; set; }
            public string RevisionNumber { get; set; }
            public string Device { get; set; }
            public string MachineType { get; set; }
            public string ci_id { get; set; }
            public string UpdateId { get; set; }
        }

        private async void find_sdp_btn_click(object sender, RoutedEventArgs e)
        {
            // keyword search SDP files (XML structure) for Title. Format *keyword* where anything with keyword
            // will be appended to SDP_queries.txt

            keyword_match_sdp_collection.Clear(); // reset

            string ask_keyword = create_window_sug(
                    title: "Export list of SDPs",
                    question: "Keyword(s) search for title field in all SDPs:",
                    btn_txt: "Submit"
                    );

            lbl_status.Content = "Exporting SDPs with keyword in title. Please wait.";
            lbl_status.Foreground = Brushes.Red;

            await Task.Run(() => find_keyword_in_sdp_title(ask_keyword));

            lbl_status.Content = "Exported. Ready for new action.";
            lbl_status.Foreground = Brushes.Green;
        }

        private void find_keyword_in_sdp_title(string keyword)
        {
            string path_sdp = Path.Combine(Directory.GetCurrentDirectory(), "Extracted", "V2");

            try
            {
                string[] all_sdp = Directory.GetFiles(path_sdp); // array of all SDP files

                foreach (string file in all_sdp)
                {
                    using (StreamReader reader = new StreamReader(file))
                    {
                        XmlDocument doc = new XmlDocument();
                        doc.Load(file);

                        XmlNamespaceManager nsmgr = new XmlNamespaceManager(doc.NameTable);
                        nsmgr.AddNamespace("sdp", "http://schemas.microsoft.com/wsus/2005/04/CorporatePublishing/SoftwareDistributionPackage.xsd");

                        // title
                        XmlNode titleNode = doc.SelectSingleNode("//sdp:Title", nsmgr);
                        string title = titleNode.InnerText.ToLower();

                        if (title.Contains(keyword.ToLower()))
                        {
                            keyword_match_sdp_collection[Path.GetFileName(file)] = titleNode.InnerText;
                        }
                    }
                }
            }
            catch (Exception ex)
            {
                log_exception("Point: Z", ex.Message);
            }

            try
            { // append to keyword_export file
                using (StreamWriter writer = new StreamWriter(keyword_export, true))
                {
                    DateTime now = DateTime.Now;
                    writer.WriteLine("********************************************************************************************************************************************");
                    writer.WriteLine(now);
                    writer.WriteLine($"Keyword(s): {keyword}");
                    foreach (KeyValuePair<string, string> item_pair in keyword_match_sdp_collection)
                    {
                        writer.WriteLine($"{item_pair.Value} <================> {item_pair.Key}");
                    }
                    writer.WriteLine("********************************************************************************************************************************************\n");
                }
            }
            catch (Exception ex)
            {
                log_exception("Point: Y", ex.Message);
            }
        }

        private async void select_update_btn_click(object sender, RoutedEventArgs e)
        {
            lbl_status.Content = "Processing. Please wait.";
            lbl_status.Foreground = Brushes.Red;

            await Task.Run(() => select_updates());

            lbl_status.Content = "";
            lbl_status.Foreground = Brushes.Green;

            if (cannot_connect_to_dbs == true)
            {
                return;
            }

            // select updates
            Window window_select_updates = new Window();
            window_select_updates.Title = "Select Lenovo Updates to Export";
            window_select_updates.SizeToContent = SizeToContent.Width;
            window_select_updates.WindowStartupLocation = WindowStartupLocation.CenterScreen;

            Grid g = new Grid();
            g.ColumnDefinitions.Add(new ColumnDefinition() { Width = GridLength.Auto });
            g.ColumnDefinitions.Add(new ColumnDefinition() { Width = GridLength.Auto });
            g.ColumnDefinitions.Add(new ColumnDefinition() { Width = GridLength.Auto });
            g.RowDefinitions.Add(new RowDefinition() { Height = GridLength.Auto });

            int rowIndex = 0;

            CheckBox select_all_chkbox = new CheckBox()
            {
                Content = "Select All",
                Margin = new Thickness(15, 2, 10, 2),
                VerticalContentAlignment = VerticalAlignment.Center
            };

            // select all
            select_all_chkbox.Checked += (s, ev) =>
            {
                foreach (var child in g.Children)
                {
                    if (child is CheckBox chkbox && chkbox != select_all_chkbox)
                    {
                        chkbox.IsChecked = true;
                    }
                }
            };

            select_all_chkbox.Unchecked += (s, ev) =>
            {
                foreach (var child in g.Children)
                {
                    if (child is CheckBox chkbox && chkbox != select_all_chkbox)
                    {
                        chkbox.IsChecked = false;
                    }
                }
            };

            g.Children.Add(select_all_chkbox);
            Grid.SetColumn(select_all_chkbox, 0);
            Grid.SetRow(select_all_chkbox, rowIndex);
            Grid.SetColumnSpan(select_all_chkbox, 2);

            rowIndex++;

            foreach (string key in cleaned_valid_update_collection.Keys)
            {
                CheckBox chkbox = new CheckBox() // kb
                {
                    Content = cleaned_valid_update_collection[key][1],
                    Margin = new Thickness(15, 2, 10, 2),
                    VerticalContentAlignment = VerticalAlignment.Center
                };

                Label lbl = new Label() // title
                {
                    Content = cleaned_valid_update_collection[key][0],
                    Margin = new Thickness(15, 2, 10, 2),
                    VerticalContentAlignment = VerticalAlignment.Bottom
                };

                Label lbl2 = new Label() // severity
                {
                    Content = cleaned_valid_update_collection[key][2],
                    Margin = new Thickness(15, 2, 10, 2),
                    VerticalContentAlignment = VerticalAlignment.Bottom
                };

                g.Children.Add(chkbox);
                g.Children.Add(lbl);
                g.Children.Add(lbl2);

                Grid.SetColumn(chkbox, 0);
                Grid.SetRow(chkbox, rowIndex);

                Grid.SetColumn(lbl2, 1);
                Grid.SetRow(lbl2, rowIndex);

                Grid.SetColumn(lbl, 2);
                Grid.SetRow(lbl, rowIndex);

                rowIndex++;
                g.RowDefinitions.Add(new RowDefinition() { Height = GridLength.Auto });
            }

            g.RowDefinitions.Add(new RowDefinition() { Height = GridLength.Auto });

            // gridlines for better view
            for (int i = 0; i < g.ColumnDefinitions.Count; i++)
            {
                for (int j = 0; j < g.RowDefinitions.Count; j++)
                {
                    Border border = new Border();
                    border.BorderThickness = new Thickness(1);
                    border.BorderBrush = Brushes.Black;

                    Grid.SetColumn(border, i);
                    Grid.SetRow(border, j);

                    g.Children.Add(border);
                }
            }

            Button export = new Button()
            {
                Content = "Export",
                Margin = new Thickness(15, 10, 10, 10),
                Width = 80,
                VerticalContentAlignment = VerticalAlignment.Bottom,
                HorizontalContentAlignment = HorizontalAlignment.Center
            };

            export.Click += new RoutedEventHandler(create_sug_script);

            g.Children.Add(export);
            Grid.SetColumn(export, 3);
            Grid.SetColumnSpan(export, 1);
            Grid.SetRow(export, rowIndex);

            ScrollViewer scrollViewer = new ScrollViewer();
            scrollViewer.Content = g;

            window_select_updates.Content = scrollViewer;
            window_select_updates.ShowDialog();
        }

        private void select_updates()
        {
            // reset to false each time
            cannot_connect_to_dbs = false;

            // clear all collections each time "select updates" is clicked
            clear_collections();

            // try and delete unneeded files - without which will generate an exception when processing
            try
            {
                string update_categories = Path.Combine(Directory.GetCurrentDirectory(), "extracted", "V3", "update_categories.json");
                string update_manifest = Path.Combine(Directory.GetCurrentDirectory(), "extracted", "V2", "update_manifest.json");

                if (File.Exists(update_categories))
                {
                    File.Delete(update_categories);
                }
                if (File.Exists(update_manifest))
                {
                    File.Delete(update_manifest);
                }
            }
            catch (Exception ex)
            {
                log_exception("Point: D", ex.Message);
            }

            try
            {
                // query & collate WSUS DB to obtain 3rd party update info 
                kb_repo = query_wsus_db_latest_KBs(wsus_sql_svr, wsus_db);

                // query & collate SCCM DB to obtain CI_ID info for each update
                obtain_ci_id_sccm_db(sccm_sql_svr, sccm_db);

                // CAB demystified
                find_models();
            }
            catch (Exception ex)
            {
                log_exception("Point: E", ex.Message);
            }

            // check if issue querying WSUS or SCCM
            if (cannot_connect_to_dbs == true)
            {
                MessageBox.Show(
                    "Ensure: \n" +
                    "1) Your user account has access to the tenancy's WSUS DB.\n" +
                    "2) WSUS DB is reachable via hostname.\n" +
                    "3) Microsoft ODBC Driver 17 for SQL server is installed on device running this utility.",
                    "Error",
                    MessageBoxButton.OK,
                    MessageBoxImage.Error
                    );
                return;
            }
        }

        private void select_model(object sender, SelectionChangedEventArgs e)
        {
            // Get the selected value from the combo box
            dropbox_model_selection = drpbox_models.SelectedItem as string;
        }

        private void select_tenancy(object sender, SelectionChangedEventArgs e)
        {
            // Tenancy selection
            string selection = drpbox_tenancy.SelectedItem as string;

            if (selection == "DomainA")
            {
                wsus_sql_svr = "DC2PWSCCM01";
                wsus_db = "SUSDB";
                sccm_sql_svr = "DC2PWSCCM01";
                sccm_db = "CM_A01";
            }
            else if (selection == "DomainB")
            {
                wsus_sql_svr = "SWPVCMS1";
                wsus_db = "SUSDB";
                sccm_sql_svr = "SWPVCMS1";
                sccm_db = "CM_GDC";
            }
        }

        private void clear_collections()
        {
            valid_wsus_kbs.Clear();
            model_specific_updates.Clear();
            update_collection.Clear();
            cleaned_update_collection.Clear();
            cleaned_valid_update_collection.Clear();
            superseded_updates_per_sdp.Clear();
            superseded_and_not_required_updates.Clear();
            kb_repo.Clear();
            breadcrumb_update_categories.Clear();
        }

        private void create_sug_script(object sender, RoutedEventArgs e)
        {
            breadcrumb_members.Clear(); // for when different updates are selected in check box window.
            List<string> updates_to_export = new List<string>();
            List<string> ci_ids_to_publish = new List<string>(); // just a list for when to write powershell script.
            string ps_script = $@"";

            // process checked checkboxes
            foreach (object cbox in ((Grid)((Button)sender).Parent).Children)
            {
                if (cbox is CheckBox && ((CheckBox)cbox).IsChecked == true)
                {
                    if (((CheckBox)cbox).Content.ToString() != "Select All")
                    {
                        updates_to_export.Add(((CheckBox)cbox).Content.ToString());
                    }
                }
            }

            if (updates_to_export.Count > 0)
            {
                string name = create_window_sug(
                    title: "SUG Name",
                    question: "Enter the name of the SUG to be created:",
                    btn_txt: "Submit"
                    );
                string description = create_window_sug(
                    title: "SUG Description",
                    question: "Enter the description for the SUG:",
                    btn_txt: "Submit"
                    );
                MessageBoxResult confirm_autopublish = MessageBox.Show(
                    "Add PowerShell commands to auto-publish updates?",
                    "Confirmation", MessageBoxButton.YesNo, MessageBoxImage.Question
                    );

                if (name == "" || description == "")
                {
                    MessageBox.Show(
                        "You can't have the SUG name or description empty.",
                        "Error", MessageBoxButton.OK, MessageBoxImage.Error
                        );
                }
                else
                {
                    try // finally, information in list of POD instances used to create appropriate PS script
                    {
                        ps_script += $"New-CMSoftwareUpdateGroup -Name \"{name}\" -Description \"{description}\"\n";
                        foreach (string article in updates_to_export)
                        {
                            foreach (LenovoUpdate kb in kb_repo)
                            {
                                if (article == kb.KnowledgebaseArticle)
                                {
                                    ps_script += $"Add-CMSoftwareUpdateToGroup -SoftwareUpdateGroupName \"{name}\" -SoftwareUpdateId \"{kb.ci_id}\"\n";
                                    ci_ids_to_publish.Add(kb.ci_id);
                                }
                            }
                        }

                        ps_script += "\n";
                        ps_script += "$cicds_to_publish = @("; // array of cicds

                        for (int i = 0; i < ci_ids_to_publish.Count; i++) {
                            ps_script += "\"" + ci_ids_to_publish[i] + "\"";
                            if (i < ci_ids_to_publish.Count - 1)
                            {
                                ps_script += ", ";
                            }
                        }

                        ps_script += ")\n";

                        if (confirm_autopublish.ToString() == "Yes")
                        {
                            ps_script += "foreach ($item in $cicds_to_publish) {\n";
                            ps_script += @"    try {";
                            ps_script += "\n";
                            ps_script += @"        Get-CMSoftwareUpdate -Fast -Name $item | Publish-CMThirdPartySoftwareUpdateContent -Force";
                            ps_script += "\n";
                            ps_script += @"    } catch {";
                            ps_script += "\n";
                            ps_script += @"        Write-Host $_.Exception.Message";
                            ps_script += "\n";
                            ps_script += @"    }";
                            ps_script += "\n}\n\n";
                        }
                        else // commented out 
                        {
                            ps_script += "# foreach ($item in $cicds_to_publish) {\n";
                            ps_script += @"#     try {";
                            ps_script += "\n#";
                            ps_script += @"         Get-CMSoftwareUpdate -Fast -Name $item | Publish-CMThirdPartySoftwareUpdateContent -Force";
                            ps_script += "\n# ";
                            ps_script += @"    } catch {";
                            ps_script += "\n# ";
                            ps_script += @"        Write-Host $_.Exception.Message";
                            ps_script += "\n# ";
                            ps_script += @"    }";
                            ps_script += "\n# }\n\n";
                        }

                        foreach (string article in updates_to_export)
                        {
                            foreach (LenovoUpdate kb in kb_repo)
                            {
                                if (article == kb.KnowledgebaseArticle)
                                {
                                    ps_script += $"# {article} | {kb.ci_id} | {kb.DefaultTitle}\n";
                                }
                            }
                        }
                        ps_script += "\n";
                        string filename = $@"{name}.ps1";
                        string path = Path.Combine(Directory.GetCurrentDirectory(), "script_output", filename);
                        File.WriteAllText(path, ps_script);
                    }
                    catch (Exception ex)
                    {
                        log_exception("Point: F", ex.Message);
                    }

                    foreach (string article in updates_to_export) // ugly: used for commiting breadcrumbs to disk in log.txt
                    {
                        foreach (KeyValuePair<string, List<string>> update in cleaned_valid_update_collection)
                        {
                            if (update.Key.Contains(article))
                            {
                                try
                                {
                                    breadcrumb_members[article] = update.Value[3];
                                }
                                catch (Exception ex)
                                {
                                    log_exception("Point: G", ex.Message);
                                }
                            }
                        }
                    }
                    commit_breadcrumbs_to_disk(name);
                }
            }
            else
            {
                MessageBox.Show(
                    "You need to select at least one update before exporting.",
                    "Error", MessageBoxButton.OK, MessageBoxImage.Error
                    );
            }
        }

        private string create_window_sug(string title, string question, string btn_txt)
        {
            Window window_sug = new Window();
            window_sug.Title = title;
            window_sug.Width = 300;
            window_sug.Height = 135;

            TextBox input_sug_name = new TextBox();
            input_sug_name.Margin = new Thickness(15, 2, 10, 2);

            Label lbl = new Label();
            lbl.Content = question;
            lbl.Margin = new Thickness(15, 2, 10, 2);

            Button btn = new Button();
            btn.Content = btn_txt;
            btn.Margin = new Thickness(15, 10, 10, 2);
            btn.Width = 60;
            btn.Click += (s, e) =>
            {
                window_sug.DialogResult = true;
            };

            StackPanel panel = new StackPanel();
            panel.Children.Add(lbl);
            panel.Children.Add(input_sug_name);
            panel.Children.Add(btn);

            window_sug.Content = panel;

            bool? dialog_result = window_sug.ShowDialog();
            if (dialog_result == true)
            {
                return input_sug_name.Text;
            }
            else
            {
                return null;
            }
        }

        private void find_models()
        {
            string path = Path.Combine(Directory.GetCurrentDirectory(), "Extracted", "V3");

            // find JSON and values for selected model - i.e. any JSON without any value for "ParentId"
            foreach (string file in Directory.EnumerateFiles(path, "*.json"))
            {
                try
                {
                    JObject json = JObject.Parse(File.ReadAllText(file));

                    foreach (var element in json)
                    {
                        try
                        {
                            if (element.Key == "DisplayName")
                            {
                                model_placeholder = element.Value.ToString();
                            }
                            if (element.Key == "Id")
                            {
                                id_placeholder = element.Value.ToString();
                            }
                            if (element.Key == "ParentId")
                            {
                                if (element.Value.ToString() == "")
                                {
                                    if (dropbox_model_selection == model_placeholder)
                                    {
                                        model_ID = id_placeholder; // extract GUID of model
                                        break;
                                    }
                                }
                            }
                        }
                        catch (Exception ex)
                        {
                            log_exception("Point: H", ex.Message);
                        }
                    }
                }
                catch (Exception ex)
                {
                    log_exception("Point: I", ex.Message);
                }
            }

            // find JSON with identified value in model_ID variable as parent_Id in the JSON file.
            // Once found populate model_specific_updates variable collection with the values 
            // from "Members" key.
            foreach (string file in Directory.EnumerateFiles(path, "*.json"))
            {
                try
                {
                    JObject json = JObject.Parse(File.ReadAllText(file));

                    foreach (var element in json)
                    {
                        try
                        {
                            if (element.Key == "Id")
                            {
                                id_placeholder = element.Value.ToString();
                            }
                            if (element.Key == "ParentId")
                            {
                                if (element.Value.ToString() != "")
                                {
                                    if (element.Value.ToString() == model_ID)
                                    {
                                        json_with_updates_found = true; // toggled! 
                                        json_with_updates = id_placeholder;
                                        breadcrumb_update_categories.Add(id_placeholder);
                                    }
                                }
                            }
                            if (element.Key == "Members") // collate SDP files
                            {
                                if (json_with_updates_found == true)
                                {
                                    JArray member_array = JArray.Parse(element.Value.ToString());

                                    foreach (string update in member_array)
                                    {
                                        model_specific_updates.Add(update.Trim());
                                    }
                                    json_with_updates_found = false; // reset
                                }
                            }
                        }
                        catch (Exception ex)
                        {
                            log_exception("Point: J", ex.Message);
                        }
                    }
                }
                catch (Exception ex)
                {
                    log_exception("Point: K", ex.Message);
                }
            }

            // search SDP files (XML structure) for appropriate Title & KBArticleID
            // siphon off superseded updates into "superseded_updates_per_sdp" collection
            string path_sdp = Path.Combine(Directory.GetCurrentDirectory(), "Extracted", "V2");

            foreach (string update in model_specific_updates) // update is GUID i.e. found in "members" key of json appropriate json.
            {
                try
                {
                    string filename = Path.Combine(path_sdp, $"{update}.SDP");
                    string severity_val;

                    if (File.Exists(filename))
                    {
                        XmlDocument doc = new XmlDocument();
                        doc.Load(filename);

                        XmlNamespaceManager nsmgr = new XmlNamespaceManager(doc.NameTable);
                        nsmgr.AddNamespace("sdp", "http://schemas.microsoft.com/wsus/2005/04/CorporatePublishing/SoftwareDistributionPackage.xsd");

                        // title
                        XmlNode titleNode = doc.SelectSingleNode("//sdp:Title", nsmgr);
                        string title = titleNode.InnerText;

                        // severity
                        XmlNode severityNode = doc.SelectSingleNode("//sdp:UpdateSpecificData", nsmgr);
                        XmlAttribute severity = severityNode.Attributes["MsrcSeverity"];
                        if (severity != null)
                        {
                            severity_val = severity.Value;
                        }
                        else
                        {
                            severity_val = "";
                        }

                        // article ID
                        XmlNode kbArticleIDNode = doc.SelectSingleNode("//sdp:KBArticleID", nsmgr);
                        string kb_article_ID = kbArticleIDNode.InnerText;

                        // superseded updates
                        XmlNode supersededNodeList = doc.SelectSingleNode("//SupersededPackages");
                        if (supersededNodeList != null)
                        {
                            if (supersededNodeList.HasChildNodes)
                            {
                                foreach (XmlNode child in supersededNodeList.ChildNodes)
                                {
                                    superseded_updates_per_sdp.Add(child.InnerText.Trim());
                                }
                            }
                        }

                        update_collection[update] = new List<string> { title, kb_article_ID, severity_val };
                    }
                }
                catch (Exception ex)
                {
                    log_exception("Point: L", ex.Message);
                }
            }

            // iterate over update_collection and check if it exists in superseded_updates_per_sdp list.
            // Only if it doesn't exist add to final collection: cleaned_update_collection 
            // this step removes any superseded updates (based on SDP file information NOT WSUS/SCCM.
            foreach (KeyValuePair<string, List<string>> update in update_collection)
            {
                try
                {
                    if (!superseded_updates_per_sdp.Contains(update.Key))
                    {
                        cleaned_update_collection[update.Key] = update.Value;
                    }
                }
                catch (Exception ex)
                {
                    log_exception("Point: M", ex.Message);
                }
            }

            // final iteration - WSUS being source of truth, only use updates that show in WSUS for 
            // selection screen (tickboxes).
            // key for dictionary is no longer GUID but rather kb_article_ID. Ensures no duplicates! 
            // however add update (member GUID) to value list for purposes of commit_breadcrumbs_to_disk()
            // Also ensure no KB in superseded_and_not_required_updates is also included!
            foreach (string kb in valid_wsus_kbs)
            {
                foreach (KeyValuePair<string, List<string>> update in cleaned_update_collection)
                {
                    if (update.Value.Contains(kb))
                    {
                        if (!superseded_and_not_required_updates.Contains(update.Value[1]))
                        {
                            // [1] == kb_article_ID
                            cleaned_valid_update_collection[update.Value[1]] = update.Value;
                            // title, kb_article_ID, severity_val, update (member guid)
                            cleaned_valid_update_collection[update.Value[1]].Add(update.Key);
                        }
                    }
                }
            }
        }

        private void debugger() // call to print the output from find_models() method.
        {
            foreach (KeyValuePair<string, List<string>> update in cleaned_update_collection)
            {
                foreach (string v in update.Value)
                {
                    if (update.Value.IndexOf(v) == 0)
                    {
                        Console.WriteLine(v);
                    }
                }
            }

            foreach (KeyValuePair<string, List<string>> update in cleaned_update_collection)
            {
                foreach (string v in update.Value)
                {
                    if (update.Value.IndexOf(v) == 1)
                    {
                        Console.WriteLine(v);
                    }
                }
            }

            Console.WriteLine(cleaned_update_collection.Count);
        }

        private string get_file_hash(string file)
        {
            using (FileStream stream = File.OpenRead(file))
            {
                SHA256Managed sha = new SHA256Managed();
                byte[] hash = sha.ComputeHash(stream);
                string hash_string = BitConverter.ToString(hash).Replace("-", "");

                return hash_string;
            }
        }

        private void write_hash_val_to_file(string hash_string, string file)
        {
            using (StreamWriter writer = File.CreateText(file))
            {
                writer.Write(hash_string);
            }
        }

        private void log_exception(string point, string ex)
        {
            try
            {
                using (StreamWriter writer = new StreamWriter(error_log, true))
                {
                    DateTime now = DateTime.Now;
                    writer.WriteLine("********************************");
                    writer.WriteLine(now);
                    writer.WriteLine(point);
                    writer.WriteLine(ex);
                    writer.WriteLine("********************************\n");
                }
            }
            catch (Exception e)
            {
                ;
            }
        }
    }
}

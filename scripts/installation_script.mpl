dir := FileTools:-JoinPath([currentdir(), "/SatQMCert.mla"]);
march('create', dir);
read "src/SatQMCert.mpl";
savelib('SatQMCert', dir);

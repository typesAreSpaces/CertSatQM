PROJECT_NAME=CertSatQM

all : $(PROJECT_NAME).mla
-e 	maple test.mpl

$(PROJECT_NAME).mla: $(PROJECT_NAME).mpl
-e 	archive_maple_project.py $(PROJECT_NAME) $(PROJECT_NAME) $(PROJECT_NAME)

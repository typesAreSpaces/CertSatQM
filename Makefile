PROJECT_NAME=CertSatQM

all : $(PROJECT_NAME).mla
	maple test.mpl

$(PROJECT_NAME).mla: $(PROJECT_NAME).mpl
	archive_maple_project.py $(PROJECT_NAME) $(PROJECT_NAME) $(PROJECT_NAME)

QUIET_MODE=
QUIET_MODE=-q

QUIET_MODE=-q
PROJECT_NAME=CertSatQM
OUTPUT=output.txt

all : $(PROJECT_NAME).mla
	maple test.mpl ${QUIET_MODE} > ${OUTPUT}

$(PROJECT_NAME).mla: $(PROJECT_NAME).mpl
	archive_maple_project.py $(PROJECT_NAME) $(PROJECT_NAME) $(PROJECT_NAME)

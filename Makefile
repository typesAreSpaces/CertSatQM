PROJECT_NAME=CertSatQM
TEST_FILE=test.mpl
OUTPUT=data/output.txt

QUIET_MODE=
QUIET_MODE=-q

QUIET_MODE=

.PHONY: clean all

all: ${OUTPUT}

${OUTPUT}: ${PROJECT_NAME}.mla ${TEST_FILE}
	#maple ${TEST_FILE} ${QUIET_MODE}
	maple ${TEST_FILE} ${QUIET_MODE} > ${OUTPUT}

${PROJECT_NAME}.mla: ${PROJECT_NAME}.mpl
	archive_maple_project.py ${PROJECT_NAME} ${PROJECT_NAME} ${PROJECT_NAME}

clean:
	rm -rf in.dat out.out
	rm -rf ${PROJECT_NAME}.mla

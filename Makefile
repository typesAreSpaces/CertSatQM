PROJECT_NAME=CertSatQM
TEST_FILE=test.mpl
SUFFIX=
LOG_FILE=log_time${SUFFIX}.txt
OUTPUT=output${SUFFIX}.txt

QUIET_MODE=
QUIET_MODE=-q

QUIET_MODE=

.PHONY: clean all

all: ${OUTPUT}

${OUTPUT}: ${PROJECT_NAME}.mla ${TEST_FILE}
	if [ -f ${LOG_FILE} ]; then rm ${LOG_FILE}; fi;
	#maple ${TEST_FILE} ${QUIET_MODE}
	maple ${TEST_FILE} ${QUIET_MODE} > ${OUTPUT}

${PROJECT_NAME}.mla: ${PROJECT_NAME}.mpl
	archive_maple_project.py ${PROJECT_NAME} ${PROJECT_NAME} ${PROJECT_NAME}

clean:
	rm -rf in.dat out.out
	rm -rf ${PROJECT_NAME}.mla

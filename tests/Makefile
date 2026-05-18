TEST_FILE=test-simple.mpl
SUFFIX=
LOG_FILE=log_time${SUFFIX}.txt
OUTPUT=output${SUFFIX}.txt

QUIET_MODE=
QUIET_MODE=-q

QUIET_MODE=

.PHONY: clean ${OUTPUT} check

all: ${OUTPUT}

${OUTPUT}: ${TEST_FILE}
	if [ -f ${LOG_FILE} ]; then rm ${LOG_FILE}; fi;
	maple ${TEST_FILE} ${QUIET_MODE}

check: *.mpl
	time bash check.sh


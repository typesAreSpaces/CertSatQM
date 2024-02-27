QUIET_MODE=
QUIET_MODE=-q

QUIET_MODE=-q
PROJECT_NAME=./../CertSatQM
OUTPUT=../data/output.txt
TEST_FILE=current_test.mpl

all : $(PROJECT_NAME).mla
	maple ${TEST_FILE} ${QUIET_MODE} > ${OUTPUT}

$(PROJECT_NAME).mla: $(PROJECT_NAME).mpl
	${MAKE} -C ../

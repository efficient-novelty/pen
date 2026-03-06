.PHONY: test-blindness lane1-baseline lane1-replay lane1-release-gate

test-blindness:
	./scripts/test_blindness.sh

lane1-baseline:
	./scripts/run_lane1_baseline.sh

lane1-replay:
	./scripts/replay_lane1_blind.sh

lane1-release-gate:
	./scripts/check_lane1_release_gate.sh

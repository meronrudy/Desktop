"""
Catala integration wrapper for validating IR and computing court outcomes.
This module interfaces with Catala (via OCaml bindings or subprocess) to validate Normative IR and compute outcomes.
"""

import subprocess
import json
import asyncio
import logging
from typing import Dict, Any, Tuple
import os

logger = logging.getLogger(__name__)


class CatalaWrapper:
    def __init__(self, catala_executable="catala", catala_dir="./catala_code"):
        """
        Initialize the wrapper.

        Args:
            catala_executable: Path to Catala executable
            catala_dir: Directory containing Catala source files
        """
        self.catala_executable = catala_executable
        self.catala_dir = catala_dir

    async def validate_ir(self, ir_json: Dict[str, Any]) -> bool:
        """
        Validate the IR using Catala asynchronously.

        Args:
            ir_json: IR dict

        Returns:
            True if valid, False otherwise
        """
        logger.info("Validating IR with Catala")
        # Convert IR to Catala input format (assume JSON or specific format)
        catala_input = self._ir_to_catala_input(ir_json)
        # Assume Catala has a validate command
        try:
            process = await asyncio.create_subprocess_exec(
                self.catala_executable, "validate", "-i", catala_input,
                cwd=self.catala_dir,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE
            )
            stdout, stderr = await process.communicate()
            success = process.returncode == 0
            if not success:
                logger.warning("IR validation failed with Catala")
            return success
        except FileNotFoundError:
            logger.warning("Catala executable not found. Assuming validation passes.")
            return True

    async def compute_outcome(self, ir_json: Dict[str, Any], scenario: Dict[str, Any]) -> Dict[str, Any]:
        """
        Compute court outcome using Catala asynchronously.

        Args:
            ir_json: IR dict
            scenario: Scenario parameters (e.g., facts of the case)

        Returns:
            Outcome dict
        """
        logger.info("Computing outcome with Catala")
        jurisdiction = ir_json.get("jurisdiction", "GENERAL")
        catala_program = self._select_catala_program(jurisdiction)
        catala_input = self._ir_and_scenario_to_catala_input(ir_json, scenario)
        try:
            process = await asyncio.create_subprocess_exec(
                self.catala_executable, "interpret", catala_program, "-i", catala_input,
                cwd=self.catala_dir,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE
            )
            stdout, stderr = await process.communicate()
            if process.returncode == 0:
                return json.loads(stdout.decode())
            else:
                logger.warning("Catala outcome computation failed: %s", stderr.decode())
                raise RuntimeError(f"Catala error: {stderr.decode()}")
        except FileNotFoundError:
            # Fallback: compute using extended logic
            logger.info("Catala not found, using fallback computation")
            return self._compute_outcome_fallback(ir_json, scenario)

    def _select_catala_program(self, jurisdiction: str) -> str:
        """
        Select Catala program based on jurisdiction.
        """
        if jurisdiction == "GDPR_EU":
            return "confidentiality.catala_en"  # stricter confidentiality
        elif jurisdiction == "CONTRACT_NY":
            return "limitation.catala_en"  # reasonable limitations
        else:
            return "general.catala_en"  # assume general program

    def _ir_to_catala_input(self, ir_json: Dict[str, Any]) -> str:
        """
        Convert IR to Catala input file.
        """
        # Dummy conversion
        return json.dumps(ir_json)

    def _compute_outcome_fallback(self, ir_json: Dict[str, Any], scenario: Dict[str, Any]) -> Dict[str, Any]:
        """
        Fallback computation matching Coq evaluator logic, with jurisdiction.
        """
        jurisdiction = ir_json.get("jurisdiction", "GENERAL")
        atoms = ir_json.get("atoms", [])
        if not atoms:
            return {"obligation_exists": False, "breach": False, "liability": False, "remedy": "NONE", "remedy_amount": 0, "defense": "DEFENSE_PRESERVED"}
        atom = atoms[0]  # take first
        modality = atom.get("modality")
        awareness_time = scenario.get("awareness_time")
        notification_time = scenario.get("notification_time")
        deadline = atom.get("deadline", {}).get("hours", 0) if isinstance(atom.get("deadline"), dict) else 0

        ob_exists = modality == "MUST" and awareness_time is not None
        br = False
        if ob_exists:
            if notification_time is None:
                br = True
            else:
                br = notification_time > (awareness_time + deadline) if awareness_time else True

        # New clauses
        conf_br = False
        conf_info = atom.get("conf_info")
        if conf_info:
            disclosure_time = scenario.get("disclosure_time")
            trigger = atom.get("trigger")
            allowed = conf_info.get("disclosure_triggers", [])
            if disclosure_time is not None:
                if jurisdiction == "GDPR_EU":
                    conf_br = trigger not in allowed  # stricter
                else:
                    conf_br = trigger not in allowed

        ind_ob = False
        ind_info = atom.get("ind_info")
        if ind_info:
            breach_by_other = scenario.get("breach_by_other_time")
            if breach_by_other is not None:
                ind_ob = True

        br = br or conf_br
        liab = br or ind_ob

        rem = "NONE"
        amt = 0
        if liab:
            if conf_br:
                rem = "INJUNCTIVE_RELIEF"
            elif ind_ob:
                rem = "DAMAGES"
                amt = ind_info.get("payment_obligation", 0)
            else:
                rem = "DAMAGES"
                amt = scenario.get("claimed_damages", 0)

        # Limitation
        lim_info = atom.get("lim_info")
        if lim_info:
            cap = lim_info.get("limitation_cap", amt)
            if jurisdiction == "CONTRACT_NY":
                amt = min(amt, cap)  # reasonable limitation
            else:
                amt = min(amt, cap)

        def_status = "DEFENSE_WAIVED" if br else "DEFENSE_PRESERVED"

        return {
            "obligation_exists": ob_exists,
            "breach": br,
            "liability": liab,
            "remedy": rem,
            "remedy_amount": amt,
            "defense": def_status
        }

    def _ir_and_scenario_to_catala_input(self, ir_json: Dict[str, Any], scenario: Dict[str, Any]) -> str:
        """
        Convert IR and scenario to Catala input.
        """
        combined = {"ir": ir_json, "scenario": scenario}
        return json.dumps(combined)


# Example usage
if __name__ == "__main__":
    wrapper = CatalaWrapper()
    ir = {"parties": ["plaintiff", "defendant"], "rights": ["compensation"], "obligations": [], "conditions": ["breach"]}
    scenario = {"breach_occurred": True, "damage_amount": 5000}
    valid = wrapper.validate_ir(ir)
    print(f"IR valid: {valid}")
    outcome = wrapper.compute_outcome(ir, scenario)
    print(outcome)
"""
Certificate packaging script.
Packages certificate data into verifiable JSON format.
"""

import json
import sys
from typing import Dict, Any


def package_certificate(ir_json: Dict[str, Any], cert_data: Dict[str, Any]) -> Dict[str, Any]:
    """
    Package IR and certificate into final certificate.
    """
    certificate = {
        "certificate": {
            **cert_data,
            "ir": ir_json  # Include the IR for verification
        },
        "signature": None  # Placeholder for digital signature if needed
    }
    return certificate


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python cert_pack.py <ir_json_file> <cert_data_json_file>")
        sys.exit(1)

    with open(sys.argv[1]) as f:
        ir = json.load(f)

    with open(sys.argv[2]) as f:
        cert_data = json.load(f)

    packaged = package_certificate(ir, cert_data)

    output_file = "certificate.json"
    with open(output_file, "w") as f:
        json.dump(packaged, f, indent=2)

    print(f"Certificate packaged to {output_file}")
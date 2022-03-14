import sys
import os.path

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

import tnf

def test_all():
    test_1()

def test_1():
    dnf = [
        [{'pe','a'},[{'Xb'}]], 
        [{'pe','a'}, [{'XXc'}]], 
        [set(), [{'-Xc'}]]
    ]

    dnf2 = [
    [{'pe','a1'},[{'Xb'}]],
    [{'pe','a2'}, [{'Xb'}]],
    [{'-a1'},[{'XXc'}]],
    [{'-pe',}, [{'-Xb'}]]

    ]

    dnf3 = [
    [{'re'},[{'N1'}]],
    [{'pe'}, [{'N2'}]],
    [{'-pe'},[{'N3'}]],
    [set(), [{'N4'}]]

    ]

    dnf4 = [
    [{'re'},[{'N1'}]],
    [{'pe'}, [{'N2'}]],
    [{'-pe'},[{'N3'}]],
    [set(), [{'N4'}]]

    ]

    dnf4 = [
    [{'pe'},[{'N1'}]],
    [{'pe', 'b'}, [set()]],
    [{'pe', 'c', 're'},[{'N3'}]],
    [{'pe', 'c', '-b', '-re'},[{'N4'}]],
    [set(), [{'N5'}]]

    ]
    tnf.TNF(dnf).tnf()
    
test_all()
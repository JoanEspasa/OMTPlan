###
# @file

import argparse
import os


DESCRIPTION = """Planner driver script."""

bound = 100

def _is_valid_file(arg):
    """
    Checks whether input PDDL files exist and are validate
    """

    if not os.path.exists(arg):
        raise argparse.ArgumentTypeError('{} not found!'.format(arg))
    elif not os.path.splitext(arg)[1] == ".pddl":
        raise argparse.ArgumentTypeError('{} is not a valid PDDL file!'.format(arg))
    else:
        return arg


def parse_args():
    """
    Specifies valid arguments for OMTPlan
    """

    parser = argparse.ArgumentParser(description = DESCRIPTION,formatter_class=argparse.ArgumentDefaultsHelpFormatter)

    parser.add_argument('problem', metavar='problem.pddl', help='Path to PDDL problem file', type=_is_valid_file)

    # Optional arguments

    parser.add_argument('-domain', help='Path to PDDL domain file', type=_is_valid_file)

    parser.add_argument('-linear', action='store_true', help='Builds a sequential encoding.')

    parser.add_argument('-parallel', action='store_true', help='Builds a parallel encoding.')

    parser.add_argument('-translate', type=int, help='Builds planning formula without solving. ')

    parser.add_argument('-pprint', action='store_true', help='Prints the plan to file (when one can be found).')

    parser.add_argument('-omt', action='store_true', help='Enables OMT encoding.')

    parser.add_argument('-smt', action='store_true', help='Enables SMT encoding.')

    parser.add_argument('-b', type=int, default=bound, help='Upper bound for OMTPlan search.')


    args = parser.parse_args()

    return args

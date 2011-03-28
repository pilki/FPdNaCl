Require Export Case_Tactics.
Require Export Omega.
Require Export NArith.
Open Scope bool_scope.

Ltac inv H := inversion H; clear H; try subst.

/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectEpisteme.Category.AlgD.C1.Adjoint
public import ProjectEpisteme.Category.AlgD.C1.Comma
public import ProjectEpisteme.Category.AlgD.C1.Limit
public import ProjectEpisteme.Category.AlgD.C1.Nat
public import ProjectEpisteme.Category.AlgD.C1.Yoneda
public import ProjectEpisteme.Category.AlgD.C2.AFT
public import ProjectEpisteme.Category.AlgD.C2.AFTTop
public import ProjectEpisteme.Category.AlgD.C2.Coyoneda
public import ProjectEpisteme.Category.AlgD.C2.End
public import ProjectEpisteme.Category.AlgD.C2.Filtered
public import ProjectEpisteme.Category.AlgD.C2.FilteredTop
public import ProjectEpisteme.Category.AlgD.C2.Kan
public import ProjectEpisteme.Category.AlgD.C2.Sheaf2
public import ProjectEpisteme.Category.AlgD.C2.Simplex
public import ProjectEpisteme.Category.AlgD.C2.SimplexTop
public import ProjectEpisteme.Category.Basic.Comma
public import ProjectEpisteme.Category.Basic.Elements
public import ProjectEpisteme.Category.Basic.FunctorCategory

/-!
# Category track (Mac Lane 2.0)

Aggregates the Category track.

* Source layer: `ProjectEpisteme/Category/AlgD/` (alg-d, 「全ての概念はKan拡張である」), joined
  by `ProjectEpisteme/Category/CWM/` once CWM is cataloged at item level.
* Library layer: `ProjectEpisteme/Category/Basic/`, general results missing from mathlib.

See `docs/Project_Episteme_Category_Strategy.md`.
-/

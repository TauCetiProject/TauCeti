/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Order.SupIndep

/-!
# Products of submodules

Products of submodules commute with indexed suprema, and a family of products is independent
exactly when both families of factors are. The two coordinate copies `Submodule.fst` and
`Submodule.snd` of the factors of a product module are cut out by the vanishing of the other
coordinate and are complementary.

## Main declarations

* `TauCeti.iSup_prod_submodule`: products commute with indexed suprema.
* `TauCeti.iSupIndep_prod_iff`, `iSupIndep.prod`: a family of products is independent exactly
  when both families of factors are.
* `Submodule.mem_fst_iff`, `Submodule.mem_snd_iff`: membership in the coordinate copies of the
  factors.
* `Submodule.isCompl_fst_snd`: the coordinate copies of the two factors are complementary.
-/

public section

namespace Submodule

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N]

/-- A vector of a product module lies in the copy of the first factor exactly when its second
coordinate vanishes. -/
@[simp]
theorem mem_fst_iff {x : M × N} : x ∈ Submodule.fst R M N ↔ x.2 = 0 :=
  mem_comap.trans (mem_bot R)

/-- A vector of a product module lies in the copy of the second factor exactly when its first
coordinate vanishes. -/
@[simp]
theorem mem_snd_iff {x : M × N} : x ∈ Submodule.snd R M N ↔ x.1 = 0 :=
  mem_comap.trans (mem_bot R)

variable (R M N)

/-- The copies of the two factors of a product module are complementary submodules. -/
theorem isCompl_fst_snd : IsCompl (Submodule.fst R M N) (Submodule.snd R M N) :=
  .of_eq (fst_inf_snd R M N) (fst_sup_snd R M N)

end Submodule

namespace TauCeti

/-- Taking products of submodules commutes with indexed suprema, including the empty one. -/
@[simp]
theorem iSup_prod_submodule {R M N : Type*} {ι : Sort*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (P : ι → Submodule R M) (Q : ι → Submodule R N) :
    (⨆ i, (P i).prod (Q i)) = (⨆ i, P i).prod (⨆ i, Q i) := by
  simp only [LinearMap.prod_eq_sup_map, Submodule.map_iSup, iSup_sup_eq]

/-- A family of componentwise products of submodules is independent exactly when both families
of factors are independent. -/
theorem iSupIndep_prod_iff {R M N : Type*} {ι : Sort*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {P : ι → Submodule R M} {Q : ι → Submodule R N} :
    iSupIndep (fun i ↦ (P i).prod (Q i)) ↔ iSupIndep P ∧ iSupIndep Q := by
  simp only [iSupIndep, disjoint_iff, iSup_prod_submodule, Submodule.prod_inf_prod,
    Submodule.prod_eq_bot_iff, forall_and]

/-- Componentwise products of independent families of submodules are independent. -/
theorem _root_.iSupIndep.prod {R M N : Type*} {ι : Sort*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {P : ι → Submodule R M} {Q : ι → Submodule R N}
    (hP : iSupIndep P) (hQ : iSupIndep Q) : iSupIndep (fun i ↦ (P i).prod (Q i)) :=
  iSupIndep_prod_iff.2 ⟨hP, hQ⟩

end TauCeti

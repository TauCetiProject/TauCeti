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
coordinate.

## Main declarations

* `TauCeti.iSup_prod_submodule`: products commute with indexed suprema.
* `TauCeti.iSupIndep_prod_iff`, `iSupIndep.prod`: a family of products is independent exactly
  when both families of factors are.
* `Submodule.mem_fst_iff`, `Submodule.mem_snd_iff`: membership in the coordinate copies of the
  factors.
* `Submodule.isCompl_prod_iff`: two product submodules are complementary exactly when both pairs
  of factor submodules are complementary.
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

/-- Two product submodules are complementary if and only if their factor submodules are
complementary in each coordinate. -/
@[simp]
theorem isCompl_prod_iff {p₁ q₁ : Submodule R M} {p₂ q₂ : Submodule R N} :
    IsCompl (p₁.prod p₂) (q₁.prod q₂) ↔ IsCompl p₁ q₁ ∧ IsCompl p₂ q₂ := by
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, prod_inf_prod,
    prod_sup_prod, prod_eq_bot_iff, prod_eq_top_iff]
  tauto

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
@[simp] theorem iSupIndep_prod_iff {R M N : Type*} {ι : Sort*} [Semiring R]
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

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

A product submodule `p.prod q : Submodule R (M × N)` is, as a module, the product `p × q`.

Products also preserve indexed suprema and independence of families of submodules.

## Main declarations

* `Submodule.prodEquiv`: `↥(p.prod q) ≃ₗ p × q`.
* `TauCeti.iSup_prod_submodule`: products commute with indexed suprema.
* `TauCeti.iSupIndep.prod`: products of independent families are independent.
-/

public section

namespace Submodule

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/-- A product submodule, as a module, is the product of the two submodules.

This is the linear refinement of `AddSubmonoid.prodEquiv`. -/
def prodEquiv (p : Submodule R M) (q : Submodule R N) : ↥(p.prod q) ≃ₗ[R] p × q :=
  { Equiv.Set.prod (p : Set M) (q : Set N) with
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

@[simp]
theorem prodEquiv_apply (p : Submodule R M) (q : Submodule R N) (x : ↥(p.prod q)) :
    prodEquiv p q x = (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩) :=
  (rfl)

@[simp]
theorem prodEquiv_symm_apply (p : Submodule R M) (q : Submodule R N) (x : p × q) :
    (prodEquiv p q).symm x = ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩ :=
  (rfl)

end Submodule

namespace TauCeti

/-- Taking products of submodules commutes with indexed suprema, including the empty one. -/
theorem iSup_prod_submodule {R M N : Type*} {ι : Sort*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (P : ι → Submodule R M) (Q : ι → Submodule R N) :
    (⨆ i, (P i).prod (Q i)) = (⨆ i, P i).prod (⨆ i, Q i) := by
  simp only [LinearMap.prod_eq_sup_map, _root_.Submodule.map_iSup, iSup_sup_eq]

/-- Componentwise products of independent families of submodules are independent.

Use `TauCeti.iSupIndep.prod hP hQ`, or `hP.prod hQ` after `open TauCeti`. -/
theorem iSupIndep.prod {R M N : Type*} {ι : Sort*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {P : ι → Submodule R M} {Q : ι → Submodule R N}
    (hP : iSupIndep P) (hQ : iSupIndep Q) : iSupIndep (fun i ↦ (P i).prod (Q i)) := by
  intro i
  simp only [iSup_prod_submodule, disjoint_iff, _root_.Submodule.prod_inf_prod,
    (hP i).eq_bot, (hQ i).eq_bot, _root_.Submodule.prod_bot]

end TauCeti

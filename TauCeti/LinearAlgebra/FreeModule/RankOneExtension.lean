/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.RankNullity
import TauCeti.LinearAlgebra.Submodule.Primitive

/-!
# Extending a submodule across a saturated step of rank one

Let `R` be a principal ideal domain and `N ≤ N'` submodules of an `R`-module, with `N'` finitely
generated. Suppose `N` is saturated in `N'` (a nonzero multiple `c • z` of `z ∈ N'` lies in `N`
only if `z` does) and `finrank R N' = finrank R N + 1`. Then `N' ⧸ N` is torsion-free of rank one,
hence free on a single generator, and any lift `y` of that generator extends `N` to `N'`: no
nonzero multiple of `y` lies in `N`, and `N'` is spanned by `N` and `y`. The lift matters only
modulo `N`, so every translate `y'` of `y` by `N` extends `N` as well.

The two extension clauses are the hypotheses of `Module.Basis.mkFinSnocOfLE`, so a basis of `N`
extends to a basis of `N'` by any such `y'`. This is the inductive step in building a basis
adapted to a saturated flag, as in Cassels, *An Introduction to the Geometry of Numbers*,
Chapter I, Theorem I.

## Main results

* `Submodule.exists_extending_of_finrank_eq_add_one`: across a saturated step of rank one, some
  `y ∈ N'` extends `N` to `N'`, and so does every translate of `y` by `N`.
-/

public section

open Module

namespace Submodule

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M]

/-- Across a saturated step of rank one, `N ≤ N'` with `finrank R N' = finrank R N + 1`, some
`y ∈ N'` extends `N` to `N'`, and so does every translate of `y` by an element of `N`. The two
extension clauses are the hypotheses of `Module.Basis.mkFinSnocOfLE`. -/
theorem exists_extending_of_finrank_eq_add_one {N N' : Submodule R M} (hle : N ≤ N')
    [Module.Finite R N'] (hsat : ∀ c : R, c ≠ 0 → ∀ z ∈ N', c • z ∈ N → z ∈ N)
    (hrank : finrank R N' = finrank R N + 1) :
    ∃ y ∈ N', ∀ y' : M, y' - y ∈ N →
      (∀ c : R, ∀ x ∈ N, c • y' + x = 0 → c = 0) ∧ ∀ z ∈ N', ∃ c : R, z + c • y' ∈ N := by
  set P : Submodule R N' := N.comap N'.subtype with hP
  have hmemP : ∀ z : N', z ∈ P ↔ (z : M) ∈ N := fun _ ↦ Iff.rfl
  have hQrank : finrank R (N' ⧸ P) = 1 := by
    have h := P.finrank_quotient_add_finrank
    have hPN : finrank R P = finrank R N := (comapSubtypeEquivOfLe hle).finrank_eq
    omega
  have : IsTorsionFree R (N' ⧸ P) :=
    P.isTorsionFree_quotient_of_smul_mem fun c z hc hz ↦
      hsat c hc z z.2 (by simpa only [hmemP, SetLike.val_smul] using hz)
  let e := Module.finBasisOfFinrankEq R (N' ⧸ P) hQrank
  obtain ⟨y, hy⟩ := P.mkQ_surjective (e 0)
  refine ⟨y, y.2, fun y' hy' ↦ ⟨fun c x hx hcx ↦ ?_, fun z hz ↦ ?_⟩⟩
  · by_contra hc
    refine e.ne_zero 0 ?_
    rw [← hy, mkQ_apply, Quotient.mk_eq_zero, hmemP]
    refine hsat c hc y y.2 ?_
    have : c • (y : M) = -x - c • (y' - y) := by
      rw [smul_sub, eq_neg_of_add_eq_zero_left hcx]
      abel
    rw [this]
    exact N.sub_mem (N.neg_mem hx) (N.smul_mem c hy')
  · set r := e.repr (P.mkQ ⟨z, hz⟩) 0
    have hz' : P.mkQ ⟨z, hz⟩ = r • P.mkQ y := by
      rw [hy]
      conv_lhs => rw [← e.sum_repr (P.mkQ ⟨z, hz⟩)]
      simp [r]
    refine ⟨-r, ?_⟩
    have hzy : ⟨z, hz⟩ - r • y ∈ P := by
      rw [← Quotient.mk_eq_zero, ← mkQ_apply, map_sub, map_smul, hz', sub_self]
    rw [hmemP] at hzy
    have : z + (-r) • y' = (z - r • (y : M)) - r • (y' - y) := by
      rw [smul_sub, neg_smul]
      abel
    rw [this]
    exact N.sub_mem (by simpa using hzy) (N.smul_mem r hy')

end Submodule

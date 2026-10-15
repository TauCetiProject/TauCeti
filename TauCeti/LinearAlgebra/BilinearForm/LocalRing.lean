/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
public import TauCeti.LinearAlgebra.BilinearForm.Modular
public import Mathlib.RingTheory.LocalRing.Basic
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.PerfectPairing.Basis

/-!
# Bilinear forms over local rings

This file records consequences of a unit Gram determinant or a perfect pairing over a local ring.
A nonunit diagonal
entry forces a unit off-diagonal entry in the same row. A symmetric perfect pairing with nonunit
diagonal values splits off a binary perfect summand whenever a dual vector takes the value one.
For an even symmetric form when `2` is a
nonunit, such an entry determines a perfect binary summand and an orthogonal decomposition.

## Main results

* `LinearMap.BilinForm.exists_index_ne_zero_isUnit_apply_of_not_isUnit_diag_of_isUnit_det` finds
  a unit off-diagonal entry from a nonunit diagonal entry.
* `LinearMap.BilinForm.IsSymm.exists_binary_isPerfPair_isCompl_orthogonal_of_dual_apply_eq_one`
  splits a binary perfect summand from a perfect pairing with nonunit diagonal values.
* `LinearMap.BilinForm.IsSymm.exists_binary_isPerfPair_isCompl_orthogonal` splits a perfect binary
  summand from an even unimodular form.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  (B : BilinForm R M)

/-- In a positive-rank unimodular form over a local ring, if the first basis vector has
nonunit self-pairing, it pairs to a unit with a different basis vector. -/
theorem exists_index_ne_zero_isUnit_apply_of_not_isUnit_diag_of_isUnit_det
    {n : ℕ} (b : Basis (Fin (n + 1)) R M)
    (hdiag : ¬ IsUnit (B (b 0) (b 0)))
    (hdet : IsUnit (B.toMatrix b).det) :
    ∃ i : Fin (n + 1), i.val ≠ 0 ∧
      IsUnit (B (b 0) (b i)) := by
  obtain ⟨j, _, hj⟩ := IsLocalRing.exists_of_isUnit_sum
    (Matrix.det_succ_row_zero (B.toMatrix b) ▸ hdet)
  have hu : IsUnit (B (b 0) (b j)) := by
    simpa only [toMatrix_apply] using
      isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hj)
  have hj0 : j.val ≠ 0 := by
    intro hj0
    have hj0' : j = 0 := Fin.ext hj0
    subst j
    exact hdiag hu
  exact ⟨j, hj0, hu⟩

/-- In a symmetric form over a local ring where `2` is not a unit, two vectors have a unit Gram
determinant if their mutual pairing is a unit and one self-pairing is divisible by `2`. -/
theorem IsSymm.isUnit_pairGramDet_of_dvd_apply_self (hB : B.IsSymm) {x y : M}
    (hxx2 : (2 : R) ∣ B x x) (h2 : ¬ IsUnit (2 : R))
    (hxy : IsUnit (B x y)) :
    IsUnit (!![B x x, B x y; B y x, B y y] : Matrix (Fin 2) (Fin 2) R).det := by
  have hxx : B x x ∈ nonunits R := by
    rw [mem_nonunits_iff]
    exact fun h ↦ h2 (isUnit_of_dvd_unit hxx2 h)
  have hdiag : B x x * B y y ∈ nonunits R := mul_mem_nonunits_left hxx
  have hoff : IsUnit (B x y * B y x) := hxy.mul (hB.eq x y ▸ hxy)
  have hunit : IsUnit (B x x * B y y - B x y * B y x) := by
    by_contra hdet
    have hneg : -(B x x * B y y - B x y * B y x) ∈ nonunits R := by
      simpa only [mem_nonunits_iff, IsUnit.neg_iff] using hdet
    have hnonunit := IsLocalRing.nonunits_add hdiag hneg
    have hcancel : B x x * B y y + -(B x x * B y y - B x y * B y x) =
        B x y * B y x := by
      ring
    rw [hcancel] at hnonunit
    exact hnonunit hoff
  simpa [Matrix.det_fin_two] using hunit

/-- A symmetric perfect pairing with nonunit diagonal values splits off a binary perfect
pairing if some linear functional takes the value one. The summand is supplied with a basis
and is complementary to its orthogonal complement. -/
theorem IsSymm.exists_binary_isPerfPair_isCompl_orthogonal_of_dual_apply_eq_one
    [B.IsPerfPair] (hB : B.IsSymm)
    (hdiag : ∀ x, ¬ IsUnit (B x x)) (x : M) (f : Module.Dual R M) (hfx : f x = 1) :
    ∃ S : Submodule R M, Nonempty (Basis (Fin 2) R S) ∧
      (B.restrict S).IsPerfPair ∧ IsCompl S (B.orthogonal S) := by
  classical
  obtain ⟨w, hw⟩ := (LinearMap.IsPerfPair.bijective_left B).surjective f
  have hxw : B x w = 1 := by rw [hB.eq, hw, hfx]
  obtain ⟨hli, hmod⟩ := hB.linearIndependent_and_isModular_restrict_span_pair (one_mem _)
    hxw (one_mul (B x x)).symm (one_mul (B w w)).symm
    (fun h ↦ hdiag x (isUnit_of_mul_isUnit_left h))
  have hp := isModular_one_iff.mp hmod
  exact ⟨_, ⟨Basis.span hli⟩, hp,
    B.isCompl_orthogonal_of_restrict_bijective _ (hB.restrict _)
      (LinearMap.IsPerfPair.bijective_left _)⟩

/-- **Even unimodular forms split off a perfect binary summand.** In rank at least two, an even
symmetric form with unit Gram determinant has two basis vectors whose span has rank two, carries
a perfect restriction of the form, and is complementary to its orthogonal complement. -/
theorem IsSymm.exists_binary_isPerfPair_isCompl_orthogonal (hB : B.IsSymm)
    {n : ℕ} (b : Basis (Fin (n + 2)) R M)
    (heven : ∀ x, (2 : R) ∣ B x x) (h2 : ¬ IsUnit (2 : R))
    (hdet : IsUnit (B.toMatrix b).det) :
    ∃ S : Submodule R M,
      finrank R S = 2 ∧ (B.restrict S).IsPerfPair ∧ IsCompl S (B.orthogonal S) := by
  have : B.IsPerfPair := b.isPerfPair_of_isUnit_det B hdet
  obtain ⟨S, ⟨c⟩, hS, hc⟩ :=
    hB.exists_binary_isPerfPair_isCompl_orthogonal_of_dual_apply_eq_one B
      (fun x hx ↦ h2 (isUnit_of_dvd_unit (heven x) hx)) (b 0) (b.coord 0) (by simp)
  refine ⟨S, ?_, hS, hc⟩
  simpa using Module.finrank_eq_card_basis c

end LinearMap.BilinForm

end

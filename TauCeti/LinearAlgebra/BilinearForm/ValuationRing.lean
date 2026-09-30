/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Module
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.RingTheory.Valuation.FinsetDvd

/-!
# Orthogonal bases of symmetric bilinear forms over valuation rings

Over a field in which `2` is invertible every symmetric bilinear form has an orthogonal basis
(`LinearMap.BilinForm.exists_orthogonal_basis`). This file proves the integral analogue: over a
valuation ring `R` in which `2` is a unit, every symmetric bilinear form on a finite free
`R`-module has an orthogonal basis
(`LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_of_isUnit_two`). The main example is `ℤ_p`
for an odd prime `p`, where the result says that every integral quadratic form is equivalent over
`ℤ_p` to a diagonal one; grouping the diagonal entries by valuation gives its Jordan splitting.

The proof picks a vector `x` whose self-pairing `B x x` divides every value of `B`: some Gram
entry `B u w` in a basis divides all the others because divisibility is total in a valuation ring,
and then one of `u`, `w`, `u + w` has self-pairing associated to `B u w`, because
`B (u + w) (u + w) = B u u + B w w + 2 B u w` and `2` is a unit in the local ring `R`. Such an `x`
splits off an orthogonal summand `R ∙ x ⊕ x^⊥`, the complement `x^⊥` is again finite free since
`R` is a local Bézout domain, and induction on the rank finishes.

The hypothesis on `2` cannot be dropped: if a symmetric form has an orthogonal basis, every value
of the form is divisible by any common divisor of its diagonal values
(`LinearMap.BilinForm.iIsOrtho.dvd_apply`). The hyperbolic plane `!![0, 1; 1, 0]` has all
diagonal values in `2R` and the value `1` off the diagonal, so it has an orthogonal basis only if
`2` is a unit (`LinearMap.BilinForm.isUnit_two_of_iIsOrtho_toBilin'_hyperbolic`). Over `ℤ_2` it
has none.

## Main results

* `LinearMap.BilinForm.IsSymm.exists_forall_apply_self_dvd_of_forall_dvd`: over a local ring with
  `2` a unit, if some value `B u w` divides every value then so does a self-pairing.
* `LinearMap.BilinForm.IsSymm.exists_forall_apply_self_dvd`: over a valuation ring with `2` a
  unit, some self-pairing `B x x` divides every value of a symmetric form.
* `LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_of_isUnit_two`: over a valuation ring with
  `2` a unit, a symmetric bilinear form on a finite free module has an orthogonal basis.
* `LinearMap.BilinForm.iIsOrtho.dvd_apply`: along an orthogonal basis, a common divisor of the
  diagonal values divides every value.
* `LinearMap.BilinForm.isUnit_two_of_iIsOrtho_toBilin'_hyperbolic`: if the hyperbolic plane has an
  orthogonal basis then `2` is a unit.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §91C and 92:1.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

/-- A common divisor of the Gram entries of a bilinear form in a basis divides every value of the
form. -/
theorem dvd_apply_of_forall_dvd_basis {ι : Type*} (b : Basis ι R M) {d : R}
    (hd : ∀ i j, d ∣ B (b i) (b j)) (x y : M) : d ∣ B x y := by
  rw [← B.sum_repr_mul_repr_mul b x y]
  refine Finset.dvd_sum fun i _ ↦ Finset.dvd_sum fun j _ ↦ ?_
  simp only [smul_eq_mul]
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (hd i j) _) _

/-- Along an orthogonal basis, a common divisor of the diagonal values of a bilinear form divides
every value of the form. -/
theorem iIsOrtho.dvd_apply {ι : Type*} {b : Basis ι R M} (hb : B.iIsOrtho b) {d : R}
    (hd : ∀ i, d ∣ B (b i) (b i)) (x y : M) : d ∣ B x y := by
  refine dvd_apply_of_forall_dvd_basis b (fun i j ↦ ?_) x y
  obtain rfl | hij := eq_or_ne i j
  · exact hd i
  · rw [iIsOrtho_def.mp hb i j hij]
    exact dvd_zero d

/-- If the hyperbolic plane, the form with Gram matrix `!![0, 1; 1, 0]` on `R²`, has an orthogonal
basis, then `2` is a unit in `R`. So over a ring such as `ℤ_2` the hyperbolic plane is not
diagonalizable. -/
theorem isUnit_two_of_iIsOrtho_toBilin'_hyperbolic {ι : Type*} {b : Basis ι R (Fin 2 → R)}
    (hb : (Matrix.toBilin' !![(0 : R), 1; 1, 0]).iIsOrtho b) : IsUnit (2 : R) := by
  have hd : ∀ v : Fin 2 → R, (2 : R) ∣ Matrix.toBilin' !![(0 : R), 1; 1, 0] v v := fun v ↦
    ⟨v 0 * v 1, by simp [Matrix.toBilin'_apply', Matrix.vecHead, Matrix.vecTail]; ring⟩
  refine isUnit_of_dvd_one ?_
  simpa [Matrix.toBilin'_apply'] using
    hb.dvd_apply (fun i ↦ hd (b i)) (Pi.single 0 1) (Pi.single 1 1)

/-- Over a local ring in which `2` is a unit, if a value `B u w` of a symmetric bilinear form
divides every value of the form, then so does one of the self-pairings `B u u`, `B w w` and
`B (u + w) (u + w)`. -/
theorem IsSymm.exists_forall_apply_self_dvd_of_forall_dvd [IsLocalRing R]
    (hB : B.IsSymm) (h2 : IsUnit (2 : R)) {u w : M} (h : ∀ y z, B u w ∣ B y z) :
    ∃ x, ∀ y z, B x x ∣ B y z := by
  obtain ⟨s, hs⟩ := h u u
  obtain ⟨t, ht⟩ := h w w
  by_cases hsu : IsUnit s
  · exact ⟨u, fun y z ↦ (hs ▸ (Units.mul_right_dvd (u := hsu.unit)).mpr dvd_rfl).trans (h y z)⟩
  by_cases htu : IsUnit t
  · exact ⟨w, fun y z ↦ (ht ▸ (Units.mul_right_dvd (u := htu.unit)).mpr dvd_rfl).trans (h y z)⟩
  -- Both `s` and `t` lie in the maximal ideal, so `s + t + 2` is a unit.
  have hunit : IsUnit (s + t + 2) := by
    by_contra hn
    refine (mem_nonunits_iff.mp ?_) h2
    have := IsLocalRing.nonunits_add (IsLocalRing.nonunits_add hn
      (mem_nonunits_iff.mpr ((IsUnit.neg_iff s).not.mpr hsu)))
      (mem_nonunits_iff.mpr ((IsUnit.neg_iff t).not.mpr htu))
    rwa [show s + t + 2 + -s + -t = 2 by ring] at this
  have huw : B (u + w) (u + w) = B u w * (s + t + 2) := by
    simp only [map_add, LinearMap.add_apply, hs, ht, hB.eq w u]
    ring
  exact ⟨u + w, fun y z ↦
    (huw ▸ (Units.mul_right_dvd (u := hunit.unit)).mpr dvd_rfl).trans (h y z)⟩

variable [IsDomain R] [ValuationRing R]

/-- Over a valuation ring in which `2` is a unit, some self-pairing `B x x` of a symmetric bilinear
form on a finite free module divides every value of the form. -/
theorem IsSymm.exists_forall_apply_self_dvd [Free R M] [Module.Finite R M] (hB : B.IsSymm)
    (h2 : IsUnit (2 : R)) : ∃ x, ∀ y z, B x x ∣ B y z := by
  obtain rfl | hB0 := eq_or_ne B 0
  · exact ⟨0, fun y z ↦ by simp⟩
  have : Nontrivial M := by
    by_contra hM
    rw [not_nontrivial_iff_subsingleton] at hM
    exact hB0 (ext fun y z ↦ by rw [Subsingleton.elim y 0, zero_left, zero_apply])
  let b := Free.chooseBasis R M
  -- A Gram entry of minimal valuation divides every Gram entry, hence every value.
  obtain ⟨⟨i, j⟩, hij⟩ :=
    TauCeti.PreValuationRing.exists_forall_dvd fun p : _ × _ ↦ B (b p.1) (b p.2)
  exact hB.exists_forall_apply_self_dvd_of_forall_dvd h2
    (dvd_apply_of_forall_dvd_basis b fun k l ↦ hij (k, l))

/-- **Diagonalization over a valuation ring.** Over a valuation ring in which `2` is a unit, for
instance `ℤ_p` with `p` odd, every symmetric bilinear form on a finite free module has an
orthogonal basis. -/
theorem IsSymm.exists_orthogonal_basis_of_isUnit_two [Free R M] [Module.Finite R M]
    (hB : B.IsSymm) (h2 : IsUnit (2 : R)) :
    ∃ v : Basis (Fin (finrank R M)) R M, B.iIsOrtho v := by
  induction hd : finrank R M generalizing M with
  | zero => exact ⟨Module.finBasisOfFinrankEq R M hd, fun i ↦ i.elim0⟩
  | succ d ih =>
  obtain rfl | hB0 := eq_or_ne B 0
  · exact ⟨Module.finBasisOfFinrankEq R M hd, fun _ _ _ ↦ rfl⟩
  obtain ⟨x, hx⟩ := hB.exists_forall_apply_self_dvd h2
  have hx0 : B x x ≠ 0 := fun h ↦ hB0 (ext fun y z ↦ zero_dvd_iff.mp (h ▸ hx y z))
  -- `x` splits off, and its orthogonal complement `N` is again finite free, of rank one less.
  have hxR := mem_nonZeroDivisors_of_ne_zero hx0
  have hc := B.isCompl_span_singleton_orthogonal_of_dvd hxR (hx x)
  let N := B.orthogonal (R ∙ x)
  have : Module.Finite R N := .equiv (Submodule.quotientEquivOfIsCompl _ _ hc)
  have : Flat R N := Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  have : Free R N := free_of_flat_of_isLocalRing
  have hN : finrank R (B.orthogonal (R ∙ x)) = d := by
    have h := (R ∙ x).finrank_quotient_add_finrank
    rw [(Submodule.quotientEquivOfIsCompl _ _ hc).finrank_eq,
      ← (LinearEquiv.toSpanNonzeroSingleton R M x fun h ↦ hx0 (by simp [h])).finrank_eq,
      finrank_self, hd] at h
    omega
  obtain ⟨v, hv⟩ := ih (B := B.restrict N) (hB.restrict N) hN
  exact hB.isRefl.exists_orthogonal_basis_of_orthogonal_span_singleton hxR (hx x) hv

end LinearMap.BilinForm

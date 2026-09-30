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
public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
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

The hypothesis on `2` cannot be dropped: the general divisibility and hyperbolic-plane lemmas
in `TauCeti.LinearAlgebra.BilinearForm.Diagonalization` show that the hyperbolic plane
`!![0, 1; 1, 0]` has an orthogonal basis only if `2` is a unit. Over `ℤ_2` it has none.

## Main results

* `LinearMap.BilinForm.IsSymm.exists_forall_apply_self_dvd_of_forall_dvd`: over a local ring with
  `2` a unit, if some value `B u w` divides every value then so does a self-pairing.
* `LinearMap.BilinForm.IsSymm.exists_forall_apply_self_dvd`: over a valuation ring with `2` a
  unit, some self-pairing `B x x` divides every value of a symmetric form.
* `LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_of_isUnit_two`: over a valuation ring with
  `2` a unit, a symmetric bilinear form on a finite free module has an orthogonal basis.
## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §91C and 92:1.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RingTheory.Henselian
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Even.Basic
import TauCeti.LinearAlgebra.BilinearForm.LocalRing
import TauCeti.RingTheory.Henselian.Basic
import TauCeti.RingTheory.LocalRing.Basic

/-!
# Even unimodular forms over Henselian local rings with residue field `𝔽₂`

Let `R` be a Henselian local ring whose residue field has two elements, for instance `ℤ_[2]`.
A symmetric bilinear form `B` over `R` is even when `2` divides every value `B x x`. This file
classifies the even unimodular forms, which are the unimodular Jordan constituents of type II at
the dyadic prime.

The binary forms come first. If `B x y` is a unit, then `B` has a pair `e, f` whose Gram matrix
is either the hyperbolic plane `!![0, 1; 1, 0]` or `!![2, 1; 1, 2]`. Two orthogonal copies of
`!![2, 1; 1, 2]` contain a hyperbolic pair, so an even unimodular form of rank at least four splits
off a hyperbolic plane. Consequently, if `-3` is not a square in `R`, two even unimodular forms of
the same rank are isometric exactly when the product of their Gram determinants is a square. The
hypothesis on `-3` separates the two binary forms, whose determinants are `-1` and `3`.

This is the even half of the classification of unimodular lattices over `ℤ₂`; the odd unimodular
forms, which are diagonalizable, are not treated here. The analogous statement when `2` is a unit
is `LinearMap.BilinForm.IsSymm.equivalent_iff_isSquare_det_mul_det`.

## Main results

* `LinearMap.BilinForm.IsSymm.exists_hyperbolic_or_exists_two_one_one_two`: a symmetric even form
  with a unit value `B x y` has a pair with Gram matrix `!![0, 1; 1, 0]` or `!![2, 1; 1, 2]`.
* `LinearMap.BilinForm.IsSymm.equivalent_iff_isSquare_det_mul_det_of_even`: even unimodular forms
  of the same rank are isometric exactly when the product of their Gram determinants is a square.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93, for unimodular lattices over dyadic
  local rings.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, for integral forms over `ℤ_2`.
-/

public section

open IsLocalRing Module Polynomial
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

section Blocks

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

/-- The Gram matrix of a pair `e, f` with `B e f = 1`. -/
private theorem IsSymm.apply_pair_eq (hB : B.IsSymm) {e f : M} {p q : R} (he : B e e = p)
    (hef : B e f = 1) (hf : B f f = q) :
    ∀ i j, B (![e, f] i) (![e, f] j) = !![p, 1; 1, q] i j := by
  have hfe : B f e = 1 := by rw [← hB.eq, hef]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [he, hef, hf, hfe]

end Blocks

variable {R M N : Type*} [CommRing R] [HenselianLocalRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

section Binary

variable {B : BilinForm R M}

/-- **The isotropic binary case.** If `B e₀ f₀ = 1`, `B e₀ e₀ = 2a` with `a` in the maximal ideal
and `B f₀ f₀ = 2c`, then `B` has a hyperbolic pair. Hensel's lemma solves `c t² + t + a = 0`. -/
private theorem IsSymm.exists_hyperbolic_of_mem_maximalIdeal (hB : B.IsSymm) {e₀ f₀ : M}
    {a c : R} (h₁ : B e₀ f₀ = 1) (ha : B e₀ e₀ = 2 * a) (hc : B f₀ f₀ = 2 * c)
    (ham : a ∈ maximalIdeal R) :
    ∃ e f : M, B e f = 1 ∧ B e e = 0 ∧ B f f = 0 := by
  obtain ⟨t, ht, htm⟩ := Polynomial.exists_isRoot_sub_mem (J := maximalIdeal R)
    (C c * X ^ 2 + X + C a) (a₀ := 0) (by simpa using ham) (by simp)
  have ht : c * t ^ 2 + t + a = 0 := by simpa using ht
  have hs : IsUnit (1 + 2 * c * t) := by
    simpa using isUnit_one_sub_self_of_mem_nonunits (-(2 * c * t))
      ((maximalIdeal R).neg_mem ((maximalIdeal R).mul_mem_left _ (by simpa using htm)))
  have h₂ : B f₀ e₀ = 1 := by rw [← hB.eq, h₁]
  -- `u = e₀ + t f₀` is isotropic and pairs to the unit `1 + 2ct` with `f₀`.
  refine hB.exists_hyperbolic_of_apply_self_eq_zero (u := e₀ + t • f₀)
    (w := (↑hs.unit⁻¹ : R) • f₀) (d := c * (↑hs.unit⁻¹ : R) ^ 2) ?_ ?_ ?_
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h₁, h₂,
      ha, hc]
    linear_combination 2 * ht
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h₁,
      hc]
    linear_combination hs.val_inv_mul
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hc]
    ring

/-- **The anisotropic binary case.** If `B e₀ f₀ = 1`, `B e₀ e₀ = 2a` and `B f₀ f₀ = 2c` with `a`
and `c` units, and the residue field has two elements, then `B` has a pair with Gram matrix
`!![2, 1; 1, 2]`. -/
private theorem IsSymm.exists_two_one_one_two_of_isUnit (hR : Nat.card (ResidueField R) = 2)
    (hB : B.IsSymm) {e₀ f₀ : M} {a c : R} (h₁ : B e₀ f₀ = 1) (ha : B e₀ e₀ = 2 * a)
    (hc : B f₀ f₀ = 2 * c) (hau : IsUnit a) (hcu : IsUnit c) :
    ∃ e f : M, B e f = 1 ∧ B e e = 2 ∧ B f f = 2 := by
  have h2 := two_mem_maximalIdeal_of_card_residueField_eq_two hR
  -- First, `u = t e₀ + f₀` has `B u u = 2`, where `a t² + t + (c - 1) = 0`.
  obtain ⟨t, ht, htm⟩ := Polynomial.exists_isRoot_sub_mem (J := maximalIdeal R)
    (C a * X ^ 2 + X + C (c - 1)) (a₀ := 0)
    (by simpa using sub_one_mem_maximalIdeal_of_card_residueField_eq_two hR hcu)
    (by simp)
  have ht : a * t ^ 2 + t + (c - 1) = 0 := by simpa using ht
  have hs : IsUnit (1 + 2 * a * t) := by
    simpa using isUnit_one_sub_self_of_mem_nonunits (-(2 * a * t))
      ((maximalIdeal R).neg_mem ((maximalIdeal R).mul_mem_left _ (by simpa using htm)))
  have h₂ : B f₀ e₀ = 1 := by rw [← hB.eq, h₁]
  set s : R := ↑hs.unit⁻¹ with hs_def
  have hss : s * (1 + 2 * a * t) = 1 := hs.val_inv_mul
  set u : M := t • e₀ + f₀ with hu_def
  set w : M := s • e₀ with hw_def
  have huu : B u u = 2 := by
    simp only [hu_def, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      h₁, h₂, ha, hc]
    linear_combination 2 * ht
  have huw : B u w = 1 := by
    simp only [hu_def, hw_def, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, h₂, ha]
    linear_combination hss
  have hwu : B w u = 1 := by rw [← hB.eq, huw]
  -- Second, `B w w = 2d` with `d = a s²` a unit, and `D = 4d - 1` is a unit.
  set d : R := a * s ^ 2 with hd_def
  have hww : B w w = 2 * d := by
    simp only [hw_def, map_smul, LinearMap.smul_apply, smul_eq_mul, ha]
    ring
  have hdu : IsUnit d := hau.mul (hs.unit⁻¹.isUnit.pow 2)
  have hD : IsUnit (4 * d - 1) := by
    have := isUnit_one_sub_self_of_mem_nonunits (2 * (2 * d)) ((maximalIdeal R).mul_mem_right _ h2)
    rw [show 4 * d - 1 = -(1 - 2 * (2 * d)) by ring]
    exact this.neg
  -- Third, `f = r u + (1 - 2r) w` pairs to `1` with `u`, and `B f f = 2` once
  -- `D r² - D r + (d - 1) = 0`.
  obtain ⟨r, hr, -⟩ := Polynomial.exists_isRoot_sub_mem (J := maximalIdeal R)
    (C (4 * d - 1) * X ^ 2 - C (4 * d - 1) * X + C (d - 1)) (a₀ := 0)
    (by simpa using sub_one_mem_maximalIdeal_of_card_residueField_eq_two hR hdu)
    (by simpa [derivative_X_pow] using hD.neg.map (Ideal.Quotient.mk (maximalIdeal R)))
  have hr : (4 * d - 1) * r ^ 2 - (4 * d - 1) * r + (d - 1) = 0 := by simpa using hr
  refine ⟨u, r • u + (1 - 2 * r) • w, ?_, huu, ?_⟩
  · simp only [map_add, map_smul, smul_eq_mul, huu, huw]
    ring
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, huu, huw,
      hwu, hww]
    linear_combination 2 * hr

/-- **Binary even unimodular forms in residue characteristic two.** Over a Henselian local ring
whose residue field has two elements, let `B` be a symmetric form with every `B x x` divisible by
`2`. If `B x y` is a unit, then `B` has a pair `e, f` with `B e f = 1` whose Gram matrix is either
the hyperbolic plane `!![0, 1; 1, 0]` or `!![2, 1; 1, 2]`. -/
theorem IsSymm.exists_hyperbolic_or_exists_two_one_one_two (hR : Nat.card (ResidueField R) = 2)
    (hB : B.IsSymm) (heven : ∀ x, 2 ∣ B x x) {x y : M} (hxy : IsUnit (B x y)) :
    ∃ e f : M, B e f = 1 ∧ (B e e = 0 ∧ B f f = 0 ∨ B e e = 2 ∧ B f f = 2) := by
  set y' : M := (↑hxy.unit⁻¹ : R) • y with hy'
  have h₁ : B x y' = 1 := by simp [hy']
  obtain ⟨a, ha⟩ := heven x
  obtain ⟨c, hc⟩ := heven y'
  by_cases ham : a ∈ maximalIdeal R
  · obtain ⟨e, f, h⟩ := hB.exists_hyperbolic_of_mem_maximalIdeal h₁ ha hc ham
    exact ⟨e, f, h.1, Or.inl h.2⟩
  by_cases hcm : c ∈ maximalIdeal R
  · obtain ⟨e, f, h⟩ := hB.exists_hyperbolic_of_mem_maximalIdeal (by rw [← hB.eq, h₁]) hc ha hcm
    exact ⟨e, f, h.1, Or.inl h.2⟩
  obtain ⟨e, f, h⟩ := hB.exists_two_one_one_two_of_isUnit hR h₁ ha hc
    (notMem_maximalIdeal.mp ham) (notMem_maximalIdeal.mp hcm)
  exact ⟨e, f, h.1, Or.inr h.2⟩

/-- **Two orthogonal copies of `!![2, 1; 1, 2]` contain a hyperbolic pair.** If `t² + t = -2`,
then `e₁ + t e₂ + f₂` is isotropic and pairs to `1` with `f₁`. -/
private theorem IsSymm.exists_hyperbolic_of_two_one_one_two (h2 : (2 : R) ∈ maximalIdeal R)
    (hB : B.IsSymm) {e₁ f₁ e₂ f₂ : M} (h₁ : B e₁ f₁ = 1) (he₁ : B e₁ e₁ = 2)
    (hf₁ : B f₁ f₁ = 2) (h₂ : B e₂ f₂ = 1) (he₂ : B e₂ e₂ = 2) (hf₂ : B f₂ f₂ = 2)
    (hee : B e₁ e₂ = 0) (hef : B e₁ f₂ = 0) (hfe : B f₁ e₂ = 0) (hff : B f₁ f₂ = 0) :
    ∃ e f : M, B e f = 1 ∧ B e e = 0 ∧ B f f = 0 := by
  obtain ⟨t, -, ht⟩ := TauCeti.HenselianRing.exists_sq_add_eq_of_mem ((maximalIdeal R).neg_mem h2)
  have hee' : B e₂ e₁ = 0 := by rw [← hB.eq, hee]
  have hef' : B f₂ e₁ = 0 := by rw [← hB.eq, hef]
  have hfe' : B e₂ f₁ = 0 := by rw [← hB.eq, hfe]
  have hff' : B f₂ f₁ = 0 := by rw [← hB.eq, hff]
  have h₂' : B f₂ e₂ = 1 := by rw [← hB.eq, h₂]
  refine hB.exists_hyperbolic_of_apply_self_eq_zero (u := e₁ + t • e₂ + f₂) (w := f₁) (d := 1)
    ?_ ?_ (by rw [hf₁, mul_one])
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, he₁,
      hee, hef, hee', he₂, h₂, hef', h₂', hf₂]
    linear_combination 2 * ht
  · simp [h₁, hfe', hff']

end Binary

section Classification

variable {B : BilinForm R M} {C : BilinForm R N}

/-- **A binary block of an even unimodular form.** If `M` has a basis of size `m + 2` in which the
Gram determinant of `B` is a unit, then `B` has a pair with Gram matrix `!![0, 1; 1, 0]`, or
`m = 0` and `B` has a pair with Gram matrix `!![2, 1; 1, 2]`. -/
private theorem IsSymm.exists_pair_of_even (hR : Nat.card (ResidueField R) = 2) (hB : B.IsSymm)
    (heven : ∀ x, 2 ∣ B x x) {m : ℕ} (b : Basis (Fin (m + 2)) R M)
    (hdet : IsUnit (B.toMatrix b).det) :
    ∃ e f : M, B e f = 1 ∧ (B e e = 0 ∧ B f f = 0 ∨ m = 0 ∧ B e e = 2 ∧ B f f = 2) := by
  have h2 := two_mem_maximalIdeal_of_card_residueField_eq_two hR
  have hdiag : ∀ {P : Type _} [AddCommGroup P] [Module R P] (D : BilinForm R P),
      (∀ x, 2 ∣ D x x) → ∀ x, ¬ IsUnit (D x x) := fun D hD x hx ↦
    (mem_maximalIdeal _).mp h2 (isUnit_of_dvd_unit (hD x) hx)
  obtain ⟨i, -, hi⟩ :=
    exists_index_ne_zero_isUnit_apply_of_not_isUnit_diag_of_isUnit_det B b (hdiag B heven _) hdet
  obtain ⟨e₁, f₁, h₁, hU | hV⟩ := hB.exists_hyperbolic_or_exists_two_one_one_two hR heven hi
  · exact ⟨e₁, f₁, h₁, Or.inl hU⟩
  rcases m with _ | m
  · exact ⟨e₁, f₁, h₁, Or.inr ⟨rfl, hV⟩⟩
  -- Split off the span of `e₁, f₁` and look for a second binary block in its complement.
  have hG := hB.apply_pair_eq hV.1 h₁ hV.2
  have hGdet : IsUnit (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) R).det := by
    rw [Matrix.det_fin_two_of, show (2 : R) * 2 - 1 * 1 = 1 - -2 by ring]
    exact isUnit_one_sub_self_of_mem_nonunits _ ((maximalIdeal R).neg_mem h2)
  obtain ⟨-, t, w, -, hdetT⟩ := hB.exists_basis_orthogonal (k := 2) b hG hGdet
  have hTdet : IsUnit ((B.restrict _).toMatrix t).det := by
    rw [hdetT] at hdet
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hdet)
  have hTeven : ∀ x : B.orthogonal (Submodule.span R (Set.range ![e₁, f₁])),
      2 ∣ B.restrict _ x x := fun x ↦ heven x
  obtain ⟨j, -, hj⟩ := exists_index_ne_zero_isUnit_apply_of_not_isUnit_diag_of_isUnit_det
    (B.restrict _) t (hdiag _ hTeven _) hTdet
  obtain ⟨e₂, f₂, h₂, hU₂ | hV₂⟩ :=
    (hB.restrict _).exists_hyperbolic_or_exists_two_one_one_two hR hTeven hj
  · exact ⟨e₂, f₂, h₂, Or.inl hU₂⟩
  -- Two orthogonal blocks `!![2, 1; 1, 2]` contain a hyperbolic pair.
  have hT (x : M) (hx : x ∈ B.orthogonal (Submodule.span R (Set.range ![e₁, f₁]))) :
      B e₁ x = 0 ∧ B f₁ x = 0 :=
    ⟨hx e₁ (Submodule.subset_span ⟨0, rfl⟩), hx f₁ (Submodule.subset_span ⟨1, rfl⟩)⟩
  obtain ⟨e, f, h⟩ := hB.exists_hyperbolic_of_two_one_one_two h2 h₁ hV.1 hV.2 h₂ hV₂.1 hV₂.2
    (hT _ e₂.2).1 (hT _ f₂.2).1 (hT _ e₂.2).2 (hT _ f₂.2).2
  exact ⟨e, f, h.1, Or.inl h.2⟩

/-- The inductive core of the classification of even unimodular forms. -/
private theorem equivalent_of_isSquare_det_mul_det_of_even (hR : Nat.card (ResidueField R) = 2)
    (h3 : ¬ IsSquare (-3 : R)) (n : ℕ) :
    ∀ {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
      {B : BilinForm R P} {C : BilinForm R Q}, B.IsSymm → C.IsSymm → (∀ x, 2 ∣ B x x) →
      (∀ x, 2 ∣ C x x) → ∀ (b : Basis (Fin n) R P) (c : Basis (Fin n) R Q),
      IsUnit (B.toMatrix b).det → IsUnit (C.toMatrix c).det →
      IsSquare ((B.toMatrix b).det * (C.toMatrix c).det) → B.Equivalent C := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Q _ _ _ _ B C hB hC hBeven hCeven b c hBdet hCdet hsq
  have h2 := two_mem_maximalIdeal_of_card_residueField_eq_two hR
  -- Squares of units cancel from a square.
  have hcancel {u x : R} (hu : IsUnit u) (h : IsSquare (u ^ 2 * x)) : IsSquare x := by
    have := (IsSquare.sq (↑hu.unit⁻¹ : R)).mul h
    rwa [← mul_assoc, ← mul_pow, hu.val_inv_mul, one_pow, one_mul] at this
  rcases n with _ | _ | m
  · -- In rank zero both modules are trivial.
    have hP (x : P) : x = 0 := b.repr.injective (Subsingleton.elim _ _)
    have hφ (x y : P) : C (b.equiv c (Equiv.refl _) x) (b.equiv c (Equiv.refl _) y) = B x y := by
      simp [hP x, hP y]
    exact ⟨{ toLinearEquiv := b.equiv c (Equiv.refl _), map_app' := hφ }⟩
  · -- An even unimodular form has no rank one.
    exfalso
    obtain ⟨i, hi, -⟩ := exists_index_ne_zero_isUnit_apply_of_not_isUnit_diag_of_isUnit_det B b
      (fun h ↦ (mem_maximalIdeal _).mp h2 (isUnit_of_dvd_unit (hBeven _) h)) hBdet
    exact hi (by omega)
  obtain ⟨eB, fB, hB₁, hBp⟩ := hB.exists_pair_of_even hR hBeven b hBdet
  obtain ⟨eC, fC, hC₁, hCp⟩ := hC.exists_pair_of_even hR hCeven c hCdet
  -- If the two binary blocks agree, split them off and use the inductive hypothesis.
  have key (p : R) (hp : IsUnit (p * p - 1)) (heB : B eB eB = p) (hfB : B fB fB = p)
      (heC : C eC eC = p) (hfC : C fC fC = p) : B.Equivalent C := by
    have hGB := hB.apply_pair_eq heB hB₁ hfB
    have hGC := hC.apply_pair_eq heC hC₁ hfC
    have hGdet : IsUnit (!![p, 1; 1, p] : Matrix (Fin 2) (Fin 2) R).det := by
      simpa [Matrix.det_fin_two_of] using hp
    obtain ⟨hcB, tB, wB, hwB, hdetB⟩ := hB.exists_basis_orthogonal (k := 2) b hGB hGdet
    obtain ⟨hcC, tC, wC, hwC, hdetC⟩ := hC.exists_basis_orthogonal (k := 2) c hGC hGdet
    refine hB.equivalent_of_equivalent_restrict_orthogonal hC hGB hGC hGdet hcB hcC
      (ih m (by omega) (hB.restrict _) (hC.restrict _) (fun x ↦ hBeven x) (fun x ↦ hCeven x) tB tC
        ?_ ?_ ?_)
    · rw [hdetB] at hBdet
      exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hBdet)
    · rw [hdetC] at hCdet
      exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hCdet)
    · rw [hdetB, hdetC] at hsq
      refine hcancel ((hwB.mul hwC).mul hGdet) ?_
      convert hsq using 1
      ring
  -- Blocks of different types occur only in rank two, where the determinants differ by `-3`.
  have mixed (p q : R) (hpq : (p * p - 1) * (q * q - 1) = -3) (hm : m = 0)
      (heB : B eB eB = p) (hfB : B fB fB = p) (heC : C eC eC = q) (hfC : C fC fC = q) :
      B.Equivalent C := by
    subst hm
    have hGB := hB.apply_pair_eq heB hB₁ hfB
    have hGC := hC.apply_pair_eq heC hC₁ hfC
    have hunit : IsUnit ((p * p - 1) * (q * q - 1)) := by
      rw [hpq, show (-3 : R) = -(1 - -2) by ring]
      exact (isUnit_one_sub_self_of_mem_nonunits _ ((maximalIdeal R).neg_mem h2)).neg
    obtain ⟨-, tB, wB, hwB, hdetB⟩ := hB.exists_basis_orthogonal (k := 2) b hGB
      (by simpa [Matrix.det_fin_two_of] using isUnit_of_mul_isUnit_left hunit)
    obtain ⟨-, tC, wC, hwC, hdetC⟩ := hC.exists_basis_orthogonal (k := 2) c hGC
      (by simpa [Matrix.det_fin_two_of] using isUnit_of_mul_isUnit_right hunit)
    rw [hdetB, hdetC] at hsq
    refine absurd (hcancel (hwB.mul hwC) ?_) h3
    convert hsq using 1
    simp [Matrix.det_fin_two_of, ← hpq]
    ring
  have h3u : IsUnit ((0 : R) * 0 - 1) := by simp
  have h3v : IsUnit ((2 : R) * 2 - 1) := by
    rw [show (2 : R) * 2 - 1 = 1 - -2 by ring]
    exact isUnit_one_sub_self_of_mem_nonunits _ ((maximalIdeal R).neg_mem h2)
  rcases hBp with ⟨heB, hfB⟩ | ⟨hm, heB, hfB⟩ <;> rcases hCp with ⟨heC, hfC⟩ | ⟨hm', heC, hfC⟩
  · exact key 0 h3u heB hfB heC hfC
  · exact mixed 0 2 (by ring) hm' heB hfB heC hfC
  · exact mixed 2 0 (by ring) hm heB hfB heC hfC
  · exact key 2 h3v heB hfB heC hfC

/-- **Classification of even unimodular forms in residue characteristic two.** Let `R` be a
Henselian local ring whose residue field has two elements and in which `-3` is not a square, for
instance `ℤ_[2]`. Two symmetric forms with every `B x x` divisible by `2` and with unit Gram
determinants in bases of the same size are isometric exactly when the product of those
determinants is a square. -/
theorem IsSymm.equivalent_iff_isSquare_det_mul_det_of_even (hR : Nat.card (ResidueField R) = 2)
    (h3 : ¬ IsSquare (-3 : R)) (hB : B.IsSymm) (hC : C.IsSymm) (hBeven : ∀ x, 2 ∣ B x x)
    (hCeven : ∀ x, 2 ∣ C x x) {n : ℕ} (b : Basis (Fin n) R M) (c : Basis (Fin n) R N)
    (hBdet : IsUnit (B.toMatrix b).det) (hCdet : IsUnit (C.toMatrix c).det) :
    B.Equivalent C ↔ IsSquare ((B.toMatrix b).det * (C.toMatrix c).det) :=
  ⟨fun h ↦ h.isSquare_det_mul_det b c, equivalent_of_isSquare_det_mul_det_of_even hR h3 n hB hC
    hBeven hCeven b c hBdet hCdet⟩

end Classification

end LinearMap.BilinForm

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
import TauCeti.LinearAlgebra.Matrix.Hermitian.LocalRing
import TauCeti.NumberTheory.NumberField.CMField.IntegralAdeleNorm
import TauCeti.NumberTheory.NumberField.CMField.ResidueField
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IntegralAdelesEquiv

/-!
# Orthonormal bases of unimodular hermitian forms over the integral finite adeles

Let `E` be a CM field with complex conjugation `x ↦ conj x`, and `Ô = ∏_w O_w` its integral finite
adeles, with conjugation `a ↦ conj a`, which carries the component at a finite place `w` to the
component at `conj w`. This file proves that every hermitian matrix `b` over `Ô` that is invertible
over `Ô` has an orthonormal basis: `kᴴ * b * k = 1` for some `k ∈ GL_n(Ô)`. As in
`NumberField.IsCMField.exists_star_mul_self_eq_of_forall_conjPlace_eq`, this needs every finite
place `w` with `conj w = w` to lie over an odd prime and to be unramified over the maximal real
subfield `E⁺`, which holds when `E` contains a primitive fourth and a primitive seventh root of
unity, for instance a primitive `5040`-th root of unity.

The proof is place by place, through `Ô ≃ ∏_w O_w`
(`IsDedekindDomain.FiniteAdeleRing.integralAdelesEquivPi`).

* At a place `w` with `conj w = w`, the component `b_w` is an invertible hermitian matrix over the
  local ring `O_w` for the involution `t ↦ conj t`. Units of `O_w` fixed by conjugation are norms
  (`IsDedekindDomain.HeightOneSpectrum.exists_adicCompletionCongr_mul_self_eq`) and `1/2 + 1/2 = 1`,
  so `b_w` has an orthonormal basis (`Matrix.IsHermitian.exists_conjTranspose_mul_mul_eq_one`).
* The places `w` with `conj w ≠ w` come in pairs `{w, conj w}`, and the equation `kᴴ * b * k = 1`
  at `w` reads `conj (k_{conj w})ᵀ * b_w * k_w = 1`. For one place of each pair (chosen by a
  well-ordering of the places), `k_w = b_w⁻¹` and `k_{conj w} = 1` solve it, and the equation at
  `conj w` is its conjugate transpose.

## Main results

* `NumberField.IsCMField.exists_conjTranspose_mul_mul_eq_one_of_forall_conjPlace_eq`: every
  invertible hermitian matrix `b` over `Ô` satisfies `kᴴ * b * k = 1` for some `k ∈ GL_n(Ô)`, when
  every place fixed by conjugation is odd and unramified over `E⁺`.
* `NumberField.IsCMField.exists_conjTranspose_mul_mul_eq_one_of_isPrimitiveRoot`: the same when
  `E` contains a primitive fourth and a primitive seventh root of unity.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §92 (unimodular lattices over local rings).
* `grh-lean`, https://github.com/lsernau/grh-lean, file `src/Lib/Adelic/Witt/WittTheorem.lean`
  (declarations `New.exists_orthonormal_Ô` and `New.exists_orthonormal_frame_Ô`); Apache 2.0,
  Copyright 2026 Anthropic, PBC. The statement, under the `5040` condition, follows those
  declarations; the proof here, place by place through the Gram–Schmidt process over a local ring,
  is independent of that code.
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing Matrix

namespace NumberField.IsCMField

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

section ConjIntegers

variable {w : HeightOneSpectrum (𝓞 E)} (h : w.conjPlace = w)

-- The restriction to `O_w` of the automorphism `t ↦ conj t` of `E_w` (the proof of
-- `IsDedekindDomain.HeightOneSpectrum.exists_adicCompletionCongr_mul_self_eq` builds it inline
-- too). It is private: this file uses it only to view `O_w` as a ring with involution, through
-- `starRingOfConjPlaceEq`, and states nothing about it.
/-- At a place `w` with `conj w = w`, the automorphism `t ↦ conj t` of `E_w` restricted to the
integers `O_w`. -/
private noncomputable def conjIntegers :
    w.adicCompletionIntegers E →+* w.adicCompletionIntegers E :=
  have hmem (x : w.adicCompletion E) (hx : x ∈ w.adicCompletionIntegers E) :
      HeightOneSpectrum.adicCompletionCongr w w _
        (HeightOneSpectrum.valuation_complexConj_of_conjPlace_eq h) x ∈
          w.adicCompletionIntegers E := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
    rwa [HeightOneSpectrum.valued_adicCompletionCongr]
  (HeightOneSpectrum.adicCompletionCongr w w _
      (HeightOneSpectrum.valuation_complexConj_of_conjPlace_eq h) :
        w.adicCompletion E →+* w.adicCompletion E).restrict _ _ hmem

private theorem coe_conjIntegers (x : w.adicCompletionIntegers E) :
    (conjIntegers h x : w.adicCompletion E) = HeightOneSpectrum.adicCompletionCongr w w _
      (HeightOneSpectrum.valuation_complexConj_of_conjPlace_eq h) x :=
  (rfl)

private theorem conjIntegers_conjIntegers (x : w.adicCompletionIntegers E) :
    conjIntegers h (conjIntegers h x) = x :=
  Subtype.ext (by
    rw [coe_conjIntegers, coe_conjIntegers,
      HeightOneSpectrum.adicCompletionCongr_complexConj_apply_apply h])

/-- `O_w` as a ring with involution `t ↦ conj t`, at a place `w` with `conj w = w`. It is used only
locally, to apply results about rings with involution to `O_w`. -/
private noncomputable abbrev starRingOfConjPlaceEq : StarRing (w.adicCompletionIntegers E) where
  star := conjIntegers h
  star_involutive := conjIntegers_conjIntegers h
  star_mul x y := by rw [map_mul, mul_comm]
  star_add := map_add _

/-- **Orthonormal bases over `O_w` at a place fixed by conjugation.** Let `w` be a finite place
with `conj w = w`, not over `2` and unramified over `E⁺`. Every invertible matrix `B` over `O_w`
that is hermitian for `t ↦ conj t` satisfies `conj Kᵀ * B * K = 1` for some `K`. -/
private theorem exists_transpose_map_conjIntegers_mul_mul_eq_one {n : Type*} [Fintype n]
    [DecidableEq n] (h2 : (2 : 𝓞 E) ∉ w.asIdeal)
    (hne : ∃ x, ringOfIntegersComplexConj E x - x ∉ w.asIdeal)
    {B : Matrix n n (w.adicCompletionIntegers E)} (hB : (B.map (conjIntegers h))ᵀ = B)
    (hBu : IsUnit B) : ∃ K : Matrix n n (w.adicCompletionIntegers E),
      (K.map (conjIntegers h))ᵀ * B * K = 1 := by
  let := starRingOfConjPlaceEq h
  -- for this involution, `star = conjIntegers h`, so `Mᴴ = (M.map (conjIntegers h))ᵀ`
  have hct (M : Matrix n n (w.adicCompletionIntegers E)) : Mᴴ = (M.map (conjIntegers h))ᵀ :=
    (rfl)
  -- conjugation-fixed units are norms
  have hnorm (u : w.adicCompletionIntegers E) (hu : IsUnit u) (hσu : star u = u) :
      ∃ y, star y * y = u := by
    obtain ⟨y, hy, hyu⟩ := HeightOneSpectrum.exists_adicCompletionCongr_mul_self_eq h h2 hne
      (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 hu)
      (by rw [← coe_conjIntegers h]; exact congrArg Subtype.val hσu)
    exact ⟨⟨y, hy⟩, Subtype.ext hyu⟩
  -- `t = 1/2` has `t + star t = 1`
  have h2O : IsUnit (2 : w.adicCompletionIntegers E) := by
    rw [← map_ofNat (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) 2]
    exact (w.isUnit_algebraMap_adicCompletionIntegers_iff (K := E) 2).2 h2
  set t : w.adicCompletionIntegers E := ↑h2O.unit⁻¹
  have ht₁ : 2 * t = 1 := IsUnit.mul_val_inv h2O
  have ht₂ : 2 * star t = 1 := by
    rw [← star_ofNat (R := w.adicCompletionIntegers E) 2, ← star_mul, mul_comm, ht₁, star_one]
  have hBh : B.IsHermitian := by rw [Matrix.IsHermitian, hct, hB]
  obtain ⟨K, hK⟩ := hBh.exists_conjTranspose_mul_mul_eq_one hnorm
    (t := t) (by linear_combination star t * ht₁ + (1 - t) * ht₂) hBu
  exact ⟨K, hct K ▸ hK⟩

end ConjIntegers

section Global

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [IsCMField E] in
/-- The component at `w` of an integral finite adele, in `O_w`. -/
private noncomputable abbrev evalAt (w : HeightOneSpectrum (𝓞 E)) :
    integralAdeles (𝓞 E) E →+* w.adicCompletionIntegers E :=
  (Pi.evalRingHom _ w).comp (integralAdelesEquivPi (𝓞 E) E).toRingHom

omit [IsCMField E] in
private theorem coe_evalAt (w : HeightOneSpectrum (𝓞 E)) (a : integralAdeles (𝓞 E) E) :
    (evalAt w a : w.adicCompletion E) = (a : 𝔸ᶠ[E]) w :=
  coe_integralAdelesEquivPi_apply a w

omit [IsCMField E] in
/-- A matrix over `Ô` is determined by its components. -/
private theorem matrix_ext_evalAt {M M' : Matrix n n (integralAdeles (𝓞 E) E)}
    (h : ∀ w, (evalAt w).mapMatrix M = (evalAt w).mapMatrix M') : M = M' :=
  Matrix.ext fun i j ↦ (integralAdelesEquivPi (𝓞 E) E).injective (funext fun w ↦
    congrFun (congrFun (h w) i) j)

omit [IsCMField E] in
/-- Every family of matrices over the `O_w` is the family of components of a matrix over `Ô`. -/
private theorem exists_mapMatrix_evalAt_eq
    (K : ∀ w : HeightOneSpectrum (𝓞 E), Matrix n n (w.adicCompletionIntegers E)) :
    ∃ k : Matrix n n (integralAdeles (𝓞 E) E), ∀ w, (evalAt w).mapMatrix k = K w :=
  ⟨Matrix.of fun i j ↦ (integralAdelesEquivPi (𝓞 E) E).symm fun w ↦ K w i j, fun w ↦
    Matrix.ext fun i j ↦ by
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingHom.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply,
        Pi.evalRingHom_apply]⟩

/-- At a place `w` with `conj w = w`, the component of `kᴴ` is the conjugate transpose of the
component of `k` for `t ↦ conj t`. -/
private theorem mapMatrix_evalAt_conjTranspose_of_conjPlace_eq {w : HeightOneSpectrum (𝓞 E)}
    (h : w.conjPlace = w) (k : Matrix n n (integralAdeles (𝓞 E) E)) :
    (evalAt w).mapMatrix kᴴ = (((evalAt w).mapMatrix k).map (conjIntegers h))ᵀ := by
  refine Matrix.ext fun i j ↦ Subtype.ext ?_
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply, coe_evalAt,
    coe_star_integralAdeles, star_apply_eq_adicCompletionCongr
      (HeightOneSpectrum.valuation_complexConj_of_conjPlace_eq h), ← coe_evalAt,
    Matrix.transpose_apply, Matrix.map_apply, coe_conjIntegers, RingHom.mapMatrix_apply,
    Matrix.map_apply]

/-- If the component of `k` at `conj w` is `1`, then so is the component of `kᴴ` at `w`: it is
its image under conjugation `E_{conj w} ≃ E_w`. -/
private theorem mapMatrix_evalAt_conjTranspose_eq_one {w : HeightOneSpectrum (𝓞 E)}
    {k : Matrix n n (integralAdeles (𝓞 E) E)} (h : (evalAt w.conjPlace).mapMatrix k = 1) :
    (evalAt w).mapMatrix kᴴ = 1 := by
  refine Matrix.ext fun i j ↦ Subtype.ext ?_
  have hc := congrArg (Subtype.val : _ → w.conjPlace.adicCompletion E)
    (congrFun (congrFun h j) i)
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, coe_evalAt] at hc
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply, coe_evalAt,
    coe_star_integralAdeles, star_apply_eq_adicCompletionCongr
      (HeightOneSpectrum.valuation_complexConj w), hc]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply_eq]
  · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]


/-- **Orthonormal bases of unimodular hermitian forms over the integral finite adeles.** Let `E`
be a CM field in which every finite place `w` with `conj w = w` lies over an odd prime and is
unramified over the maximal real subfield, that is `conj x - x ∉ w` for some integer `x`. Then
every hermitian matrix `b` over the integral finite adeles `Ô` that is invertible over `Ô`
satisfies `kᴴ * b * k = 1` for some `k ∈ GL_n(Ô)`. -/
theorem exists_conjTranspose_mul_mul_eq_one_of_forall_conjPlace_eq
    (h2 : ∀ w : HeightOneSpectrum (𝓞 E), w.conjPlace = w → (2 : 𝓞 E) ∉ w.asIdeal)
    (hne : ∀ w : HeightOneSpectrum (𝓞 E), w.conjPlace = w →
      ∃ x, ringOfIntegersComplexConj E x - x ∉ w.asIdeal)
    {b : Matrix n n (integralAdeles (𝓞 E) E)} (hb : b.IsHermitian) (hu : IsUnit b) :
    ∃ k : GL n (integralAdeles (𝓞 E) E),
      (k : Matrix n n (integralAdeles (𝓞 E) E))ᴴ * b * k = 1 := by
  classical
  -- it suffices to find `k` with `kᴴ * b * k = 1`, which is then invertible
  suffices h : ∃ k : Matrix n n (integralAdeles (𝓞 E) E), kᴴ * b * k = 1 by
    obtain ⟨k, hk⟩ := h
    exact ⟨((Matrix.isUnit_iff_isUnit_det k).2 (Matrix.isUnit_det_of_left_inverse hk)).unit, hk⟩
  -- an orthonormal basis of the component `b_w` at each place fixed by conjugation
  have hloc (w : HeightOneSpectrum (𝓞 E)) (h : w.conjPlace = w) :
      ∃ K : Matrix n n (w.adicCompletionIntegers E),
        (K.map (conjIntegers h))ᵀ * (evalAt w).mapMatrix b * K = 1 :=
    exists_transpose_map_conjIntegers_mul_mul_eq_one h (h2 w h) (hne w h)
      (by rw [← mapMatrix_evalAt_conjTranspose_of_conjPlace_eq, hb.eq]) (hu.map _)
  choose Kloc hKloc using hloc
  -- the components of `k`: a local orthonormal basis at `w = conj w`, and `b_w⁻¹`, `1` at the
  -- first and the second place of a split pair
  obtain ⟨k, hk⟩ := exists_mapMatrix_evalAt_eq fun w ↦ if h : w.conjPlace = w then Kloc w h
    else if WellOrderingRel w w.conjPlace then ((evalAt w).mapMatrix b)⁻¹ else 1
  refine ⟨k, matrix_ext_evalAt fun w ↦ ?_⟩
  rw [map_one]
  -- `kᴴ * b * k` is `1` at the places fixed by conjugation and at the first place of each pair
  have hfirst (w : HeightOneSpectrum (𝓞 E)) (hw : w.conjPlace = w ∨ WellOrderingRel w w.conjPlace) :
      (evalAt w).mapMatrix (kᴴ * b * k) = 1 := by
    rw [map_mul, map_mul]
    by_cases h : w.conjPlace = w
    · rw [mapMatrix_evalAt_conjTranspose_of_conjPlace_eq h, hk, dite_eq_left h,
        hKloc]
    have hr : WellOrderingRel w w.conjPlace := hw.resolve_left h
    have hK' : (evalAt w.conjPlace).mapMatrix k = 1 := by
      rw [hk, dite_eq_right (by rw [HeightOneSpectrum.conjPlace_conjPlace]; exact Ne.symm h),
        ite_eq_right (by rw [HeightOneSpectrum.conjPlace_conjPlace]; exact asymm hr)]
    rw [mapMatrix_evalAt_conjTranspose_eq_one hK', Matrix.one_mul, hk,
      dite_eq_right h, ite_eq_left hr]
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (hu.map _))
  by_cases hw : w.conjPlace = w ∨ WellOrderingRel w w.conjPlace
  · exact hfirst w hw
  -- at the second place of a pair, `kᴴ * b * k` is `1` since it is hermitian and `1` at `conj w`
  have hr : WellOrderingRel w.conjPlace w := by
    obtain ⟨hw₁, hw₂⟩ := not_or.1 hw
    exact (trichotomous_of WellOrderingRel w w.conjPlace).resolve_left hw₂ |>.resolve_left
      (Ne.symm hw₁)
  rw [← Matrix.isHermitian_conjTranspose_mul_mul k hb]
  exact mapMatrix_evalAt_conjTranspose_eq_one
    (hfirst w.conjPlace (Or.inr (by rwa [HeightOneSpectrum.conjPlace_conjPlace])))

/-- **Orthonormal bases of unimodular hermitian forms over the integral finite adeles, under the
`5040` condition.** If the CM field `E` contains a primitive fourth and a primitive seventh root of
unity (for instance a primitive `5040`-th root of unity), every hermitian matrix `b` over the
integral finite adeles `Ô` that is invertible over `Ô` satisfies `kᴴ * b * k = 1` for some
`k ∈ GL_n(Ô)`. -/
theorem exists_conjTranspose_mul_mul_eq_one_of_isPrimitiveRoot {ζ₄ ζ₇ : E}
    (h₄ : IsPrimitiveRoot ζ₄ 4) (h₇ : IsPrimitiveRoot ζ₇ 7)
    {b : Matrix n n (integralAdeles (𝓞 E) E)} (hb : b.IsHermitian) (hu : IsUnit b) :
    ∃ k : GL n (integralAdeles (𝓞 E) E),
      (k : Matrix n n (integralAdeles (𝓞 E) E))ᴴ * b * k = 1 :=
  exists_conjTranspose_mul_mul_eq_one_of_forall_conjPlace_eq
    (fun w h ↦ (two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot h₄ h₇ w.asIdeal
      (HeightOneSpectrum.map_asIdeal_of_conjPlace_eq h)).1)
    (fun w h ↦ (two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot h₄ h₇ w.asIdeal
      (HeightOneSpectrum.map_asIdeal_of_conjPlace_eq h)).2)
    hb hu

end Global

end NumberField.IsCMField

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import TauCeti.Analysis.SpecialFunctions.Complex.TwoPiI

/-!
# The embedding space of a Tate twist and its integral coordinates

Let `F` be a number field and `k` a natural number. Write `ℝ(k) = (2πi)^k ℝ` and
`ℤ(k) = (2πi)^k ℤ` for the real and integral Tate twists inside `ℂ`. The *embedding Tate space*
`tateEmbeddingSpace F k` is the real vector space of functions `v` on the complex embeddings of
`F` with values in `ℝ(k)` that commute with complex conjugation, `v (conj σ) = conj (v σ)`; the
*embedding Tate lattice* `tateEmbeddingLattice F k` consists of those with values in `ℤ(k)`.
For `k = n - 1` these are the target `Vₙ(F)` of Borel's regulator on `K_{2n-1}(F)` and its
coordinate lattice `Cₙ(F)` (Burgos, Proposition 9.22 and Corollary 9.23).

Dividing by `(2πi)^k` turns `v` into a real function with `v (conj σ) = (-1)^k v σ`: a real
embedding contributes a coordinate only in even twist, and each pair of complex embeddings
contributes one coordinate. Selecting `w.embedding` at every infinite place `w` that carries a
coordinate gives a continuous linear equivalence with `ℝ^d`, where `d = r₁ + r₂` for even `k` and
`d = r₂` for odd `k`, carrying the lattice onto `ℤ^d`. The space keeps the norm and topology it
inherits from `(F →+* ℂ) → ℂ`; the equivalence is a homeomorphism for them, and the lattice has
covolume `1` for the coordinate Haar measure transported from `ℝ^d`.

## Main definitions

* `TauCeti.NumberField.tateEmbeddingSpace F k`: the conjugation-equivariant `ℝ(k)`-valued functions
  on the complex embeddings of `F`, a real subspace of `(F →+* ℂ) → ℂ`.
* `TauCeti.NumberField.tateEmbeddingLattice F k`: its `ℤ(k)`-valued elements.
* `TauCeti.NumberField.tateEmbeddingCoord F k σ`: the real coordinate `v σ / (2πi)^k`.
* `TauCeti.NumberField.tateEmbeddingCoordEquiv F k`: the continuous linear equivalence with
  `TateEmbeddingIndex F k → ℝ` given by the coordinates at the embeddings `w.embedding`.
* `TauCeti.NumberField.tateEmbeddingMeasure F k`: the coordinate Haar measure.

## Main results

* `TauCeti.NumberField.tateEmbeddingCoord_conjugate`: `v (conj σ)` has coordinate
  `(-1)^k` times that of `v σ`.
* `TauCeti.NumberField.finrank_tateEmbeddingSpace_of_even`,
  `TauCeti.NumberField.finrank_tateEmbeddingSpace_of_odd`: the dimension is `r₁ + r₂` in even and
  `r₂` in odd twist.
* `TauCeti.NumberField.finrank_tateEmbeddingSpace_pred`: in twist `n - 1` for `1 ≤ n`, the
  dimension is `r₂` for even `n` and `r₁ + r₂` for odd `n`.
* `TauCeti.NumberField.tateEmbeddingSpace_ext_embedding`,
  `TauCeti.NumberField.mem_tateEmbeddingLattice_iff_tateEmbeddingCoordEquiv`: the selected
  coordinates already determine an element, and their integrality characterizes the lattice.
* `TauCeti.NumberField.covolume_tateEmbeddingLattice`: the lattice is a `ℤ`-lattice of covolume
  `1` for the coordinate Haar measure.
* `TauCeti.NumberField.measurePreserving_tateEmbeddingCoord`: the coordinates at any other choice
  of one embedding per place also carry the coordinate Haar measure to Lebesgue measure.

## References

* J. I. Burgos Gil, *The regulators of Beilinson and Borel*, CRM Monograph Series 15, American
  Mathematical Society, 2002, Proposition 9.22 and Corollary 9.23.
-/

public section

noncomputable section

open NumberField NumberField.InfinitePlace ComplexConjugate MeasureTheory Module

namespace TauCeti.NumberField

variable (F : Type*) [Field F] (k : ℕ)

/-- The conjugation-equivariant functions on the complex embeddings of `F` with values in the
real Tate twist `ℝ(k) = (2πi)^k ℝ`. For `k = n - 1` this is the target `Vₙ(F)` of Borel's
regulator on `K_{2n-1}(F)`. -/
def tateEmbeddingSpace : Submodule ℝ ((F →+* ℂ) → ℂ) where
  carrier := {v | (∀ σ, ∃ r : ℝ, v σ = r * (2 * Real.pi * Complex.I) ^ k) ∧
    ∀ σ, v (ComplexEmbedding.conjugate σ) = conj (v σ)}
  add_mem' := by
    rintro v v' ⟨hv, hcv⟩ ⟨hv', hcv'⟩
    refine ⟨fun σ ↦ ?_, fun σ ↦ by simp [hcv, hcv']⟩
    obtain ⟨r, hr⟩ := hv σ
    obtain ⟨r', hr'⟩ := hv' σ
    exact ⟨r + r', by simp [hr, hr', add_mul]⟩
  zero_mem' := ⟨fun _ ↦ ⟨0, by simp⟩, fun _ ↦ by simp⟩
  smul_mem' := by
    rintro c v ⟨hv, hcv⟩
    refine ⟨fun σ ↦ ?_, fun σ ↦ by simp [hcv, Complex.real_smul]⟩
    obtain ⟨r, hr⟩ := hv σ
    exact ⟨c * r, by simp [hr, Complex.real_smul, mul_assoc]⟩

variable {F k} in
@[simp]
theorem mem_tateEmbeddingSpace_iff {v : (F →+* ℂ) → ℂ} :
    v ∈ tateEmbeddingSpace F k ↔
      (∀ σ, ∃ r : ℝ, v σ = r * (2 * Real.pi * Complex.I) ^ k) ∧
        ∀ σ, v (ComplexEmbedding.conjugate σ) = conj (v σ) :=
  Iff.rfl

/-- The real coordinate `v σ / (2πi)^k` of an element of the embedding Tate space at a complex
embedding `σ`. -/
def tateEmbeddingCoord (σ : F →+* ℂ) : tateEmbeddingSpace F k →ₗ[ℝ] ℝ where
  toFun v := ((v : (F →+* ℂ) → ℂ) σ / (2 * Real.pi * Complex.I) ^ k).re
  map_add' v v' := by simp [add_div]
  map_smul' c v := by simp [Complex.real_smul, mul_div_assoc]

variable {F k}

theorem tateEmbeddingCoord_apply (σ : F →+* ℂ) (v : tateEmbeddingSpace F k) :
    tateEmbeddingCoord F k σ v =
      ((v : (F →+* ℂ) → ℂ) σ / (2 * Real.pi * Complex.I) ^ k).re :=
  (rfl)

/-- An element of the embedding Tate space takes the value `r * (2πi)^k` at `σ`, where `r` is its
coordinate at `σ`. -/
theorem ofReal_tateEmbeddingCoord_mul_two_pi_I_pow (v : tateEmbeddingSpace F k) (σ : F →+* ℂ) :
    (tateEmbeddingCoord F k σ v : ℂ) * (2 * Real.pi * Complex.I) ^ k =
      (v : (F →+* ℂ) → ℂ) σ := by
  obtain ⟨r, hr⟩ := v.property.1 σ
  have h : (2 * Real.pi * Complex.I : ℂ) ^ k ≠ 0 := pow_ne_zero _ Complex.two_pi_I_ne_zero
  simp [tateEmbeddingCoord, hr, h]

/-- The coordinate of `v` at `σ` is `r` exactly when `v σ = r * (2πi)^k`. -/
theorem tateEmbeddingCoord_eq_iff {v : tateEmbeddingSpace F k} {σ : F →+* ℂ} {r : ℝ} :
    tateEmbeddingCoord F k σ v = r ↔
      (v : (F →+* ℂ) → ℂ) σ = r * (2 * Real.pi * Complex.I) ^ k := by
  have h : (2 * Real.pi * Complex.I : ℂ) ^ k ≠ 0 := pow_ne_zero _ Complex.two_pi_I_ne_zero
  rw [← ofReal_tateEmbeddingCoord_mul_two_pi_I_pow, mul_left_inj' h, Complex.ofReal_inj]

/-- Two elements of the embedding Tate space with the same coordinates are equal. -/
theorem tateEmbeddingSpace_ext {v v' : tateEmbeddingSpace F k}
    (h : ∀ σ, tateEmbeddingCoord F k σ v = tateEmbeddingCoord F k σ v') : v = v' := by
  ext σ
  rw [← ofReal_tateEmbeddingCoord_mul_two_pi_I_pow, ← ofReal_tateEmbeddingCoord_mul_two_pi_I_pow,
    h]

/-- Replacing an embedding by its complex conjugate multiplies the coordinate by `(-1)^k`. -/
@[simp]
theorem tateEmbeddingCoord_conjugate (v : tateEmbeddingSpace F k) (σ : F →+* ℂ) :
    tateEmbeddingCoord F k (ComplexEmbedding.conjugate σ) v =
      (-1) ^ k * tateEmbeddingCoord F k σ v := by
  rw [tateEmbeddingCoord_eq_iff, v.property.2 σ, ← ofReal_tateEmbeddingCoord_mul_two_pi_I_pow,
      map_mul,
    Complex.conj_ofReal, Complex.conj_two_pi_I_pow]
  push_cast
  ring

/-- The coordinate at `σ` is `(-1)^k` times the coordinate at the complex conjugate of `σ`. -/
theorem tateEmbeddingCoord_eq_neg_one_pow_mul_conjugate (v : tateEmbeddingSpace F k)
    (σ : F →+* ℂ) :
    tateEmbeddingCoord F k σ v =
      (-1) ^ k * tateEmbeddingCoord F k (ComplexEmbedding.conjugate σ) v := by
  rw [tateEmbeddingCoord_conjugate, ← mul_assoc, ← mul_pow]
  simp

/-- In odd twist the coordinate at a real embedding vanishes. -/
theorem tateEmbeddingCoord_eq_zero_of_isReal (hk : Odd k) (v : tateEmbeddingSpace F k)
    {σ : F →+* ℂ} (hσ : ComplexEmbedding.IsReal σ) : tateEmbeddingCoord F k σ v = 0 := by
  have h := tateEmbeddingCoord_conjugate v σ
  rw [ComplexEmbedding.isReal_iff.mp hσ, hk.neg_one_pow] at h
  linarith

/-- The coordinate at an embedding `σ` equals the coordinate at the chosen embedding
`(mk σ).embedding` of its place, or is `(-1)^k` times it. -/
theorem tateEmbeddingCoord_eq_or_eq_neg_one_pow_mul (v : tateEmbeddingSpace F k) (σ : F →+* ℂ) :
    tateEmbeddingCoord F k σ v = tateEmbeddingCoord F k (mk σ).embedding v ∨
      tateEmbeddingCoord F k σ v = (-1) ^ k * tateEmbeddingCoord F k (mk σ).embedding v := by
  rcases embedding_mk_eq σ with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h, ← tateEmbeddingCoord_eq_neg_one_pow_mul_conjugate])

variable (F k)

/-- The infinite places of `F` that carry a coordinate of `tateEmbeddingSpace F k`: every place in
even twist, and only the complex places in odd twist. -/
abbrev TateEmbeddingIndex : Type _ := {w : InfinitePlace F // Even k ∨ w.IsComplex}

variable {F k}

/-- If `σ` is not real or the twist is even, its place carries a coordinate. -/
private theorem even_or_isComplex_mk {σ : F →+* ℂ} (h : Even k ∨ ¬ComplexEmbedding.IsReal σ) :
    Even k ∨ (mk σ).IsComplex := by
  rwa [isComplex_mk_iff]

open scoped Classical in
/-- The coordinate data, extended by zero to the real places in odd twist. -/
private def placeCoord (c : TateEmbeddingIndex F k → ℝ) (w : InfinitePlace F) : ℝ :=
  if h : Even k ∨ w.IsComplex then c ⟨w, h⟩ else 0

private theorem placeCoord_eq_zero (c : TateEmbeddingIndex F k → ℝ) (hk : Odd k) {σ : F →+* ℂ}
    (hσ : ComplexEmbedding.IsReal σ) : placeCoord c (mk σ) = 0 := by
  simp [placeCoord, isComplex_mk_iff, hσ, Nat.not_even_iff_odd.mpr hk]

open scoped Classical in
/-- The coordinate data, extended from the selected embeddings to all embeddings. -/
private def extendCoord (c : TateEmbeddingIndex F k → ℝ) (σ : F →+* ℂ) : ℝ :=
  (if (mk σ).embedding = σ then 1 else (-1) ^ k) * placeCoord c (mk σ)

private theorem extendCoord_conjugate (c : TateEmbeddingIndex F k → ℝ) (σ : F →+* ℂ) :
    extendCoord c (ComplexEmbedding.conjugate σ) = (-1) ^ k * extendCoord c σ := by
  simp only [extendCoord, mk_conjugate_eq]
  by_cases hr : ComplexEmbedding.IsReal σ
  · rw [ComplexEmbedding.isReal_iff.mp hr]
    rcases Nat.even_or_odd k with hk | hk
    · simp [hk.neg_one_pow]
    · simp [placeCoord_eq_zero c hk hr]
  · have hne : ComplexEmbedding.conjugate σ ≠ σ := fun h ↦ hr (ComplexEmbedding.isReal_iff.mpr h)
    rcases embedding_mk_eq σ with h | h
    · simp [h, hne.symm]
    · simp [h, hne, ← mul_assoc, ← mul_pow]

private theorem extendCoord_embedding (c : TateEmbeddingIndex F k → ℝ)
    (w : TateEmbeddingIndex F k) : extendCoord c w.val.embedding = c w := by
  simp [extendCoord, placeCoord, mk_embedding, w.property]

/-- The element of the embedding Tate space with prescribed coordinates at the chosen embeddings
`w.embedding`. -/
private def ofCoord (c : TateEmbeddingIndex F k → ℝ) : tateEmbeddingSpace F k :=
  ⟨fun σ ↦ (extendCoord c σ : ℂ) * (2 * Real.pi * Complex.I) ^ k,
    fun σ ↦ ⟨_, rfl⟩, fun σ ↦ by
      dsimp only
      rw [map_mul, Complex.conj_ofReal, Complex.conj_two_pi_I_pow, extendCoord_conjugate]
      push_cast
      ring⟩

private theorem tateEmbeddingCoord_ofCoord (c : TateEmbeddingIndex F k → ℝ) (σ : F →+* ℂ) :
    tateEmbeddingCoord F k σ (ofCoord c) = extendCoord c σ :=
  tateEmbeddingCoord_eq_iff.mpr rfl

private theorem extendCoord_tateEmbeddingCoord (v : tateEmbeddingSpace F k) (σ : F →+* ℂ) :
    extendCoord (fun w : TateEmbeddingIndex F k ↦ tateEmbeddingCoord F k w.val.embedding v) σ =
      tateEmbeddingCoord F k σ v := by
  by_cases h : Even k ∨ ¬ComplexEmbedding.IsReal σ
  · simp only [extendCoord, placeCoord, even_or_isComplex_mk h, dite_true]
    rcases embedding_mk_eq σ with h' | h'
    · simp [h']
    · split_ifs with h''
      · rw [one_mul, h'']
      · rw [h', ← tateEmbeddingCoord_eq_neg_one_pow_mul_conjugate]
  · rw [not_or, Nat.not_even_iff_odd, not_not] at h
    simp [extendCoord, placeCoord_eq_zero _ h.1 h.2, tateEmbeddingCoord_eq_zero_of_isReal h.1 v h.2]

variable (F k) [NumberField F]

instance : Fintype (TateEmbeddingIndex F k) := Fintype.ofFinite _

/-- The coordinates at the embeddings `w.embedding` of the infinite places carrying a
coordinate identify the embedding Tate space with `ℝ^d`. -/
def tateEmbeddingCoordEquiv : tateEmbeddingSpace F k ≃L[ℝ] (TateEmbeddingIndex F k → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun v w := tateEmbeddingCoord F k w.val.embedding v
      map_add' v v' := by ext; simp
      map_smul' c v := by ext; simp
      invFun := ofCoord
      left_inv v := tateEmbeddingSpace_ext fun σ ↦ by
        rw [tateEmbeddingCoord_ofCoord, extendCoord_tateEmbeddingCoord]
      right_inv c := by
        ext w
        simp [tateEmbeddingCoord_ofCoord, extendCoord_embedding] }

variable {F k}

@[simp]
theorem tateEmbeddingCoordEquiv_apply (v : tateEmbeddingSpace F k) (w : TateEmbeddingIndex F k) :
    tateEmbeddingCoordEquiv F k v w = tateEmbeddingCoord F k w.val.embedding v :=
  (rfl)

/-- The element with prescribed coordinates at the chosen embeddings has those coordinates. -/
@[simp]
theorem tateEmbeddingCoord_tateEmbeddingCoordEquiv_symm (c : TateEmbeddingIndex F k → ℝ)
    (w : TateEmbeddingIndex F k) :
    tateEmbeddingCoord F k w.val.embedding ((tateEmbeddingCoordEquiv F k).symm c) = c w :=
  congr_fun ((tateEmbeddingCoordEquiv F k).apply_symm_apply c) w

/-- Two elements of the embedding Tate space with the same coordinates at the chosen embeddings
`w.embedding` are equal. -/
theorem tateEmbeddingSpace_ext_embedding {v v' : tateEmbeddingSpace F k}
    (h : ∀ w : TateEmbeddingIndex F k,
      tateEmbeddingCoord F k w.val.embedding v = tateEmbeddingCoord F k w.val.embedding v') :
    v = v' :=
  (tateEmbeddingCoordEquiv F k).injective (funext h)

variable (F k) in
/-- The real dimension of the embedding Tate space is the number of places carrying a
coordinate. -/
theorem finrank_tateEmbeddingSpace :
    finrank ℝ (tateEmbeddingSpace F k) = Fintype.card (TateEmbeddingIndex F k) := by
  rw [(tateEmbeddingCoordEquiv F k).toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card]

/-- In even twist the embedding Tate space has dimension `r₁ + r₂`. -/
theorem finrank_tateEmbeddingSpace_of_even (hk : Even k) :
    finrank ℝ (tateEmbeddingSpace F k) = nrRealPlaces F + nrComplexPlaces F := by
  rw [finrank_tateEmbeddingSpace, ← card_eq_nrRealPlaces_add_nrComplexPlaces]
  exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ Or.inl hk)

/-- In odd twist the embedding Tate space has dimension `r₂`. -/
theorem finrank_tateEmbeddingSpace_of_odd (hk : Odd k) :
    finrank ℝ (tateEmbeddingSpace F k) = nrComplexPlaces F := by
  rw [finrank_tateEmbeddingSpace, Fintype.card_eq_nat_card, nrComplexPlaces,
    Fintype.card_eq_nat_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ by simp [Nat.not_even_iff_odd.mpr hk])

variable (F) in
/-- In twist `n - 1` for `1 ≤ n`, the embedding Tate space has dimension `r₂` for even `n`
and `r₁ + r₂` for odd `n`. -/
theorem finrank_tateEmbeddingSpace_pred {n : ℕ} (hn : 1 ≤ n) :
    finrank ℝ (tateEmbeddingSpace F (n - 1)) =
      (if Even n then 0 else nrRealPlaces F) + nrComplexPlaces F := by
  rcases Nat.even_or_odd n with he | ho
  · have h : Odd (n - 1) := by
      rw [Nat.odd_sub hn]
      simp [he]
    simp [he, finrank_tateEmbeddingSpace_of_odd (F := F) h]
  · have h : Even (n - 1) := by
      rw [Nat.even_sub hn]
      simpa using ho
    simp [Nat.not_even_iff_odd.mpr ho, finrank_tateEmbeddingSpace_of_even (F := F) h]

variable (F k) in
/-- The embedding Tate lattice: the elements of the embedding Tate space with values in the
integral Tate twist `ℤ(k) = (2πi)^k ℤ`. For `k = n - 1` this is the coordinate lattice `Cₙ(F)`. -/
def tateEmbeddingLattice : Submodule ℤ (tateEmbeddingSpace F k) where
  carrier := {v | ∀ σ, ∃ m : ℤ, (v : (F →+* ℂ) → ℂ) σ = m * (2 * Real.pi * Complex.I) ^ k}
  add_mem' := by
    rintro v v' hv hv' σ
    obtain ⟨m, hm⟩ := hv σ
    obtain ⟨m', hm'⟩ := hv' σ
    exact ⟨m + m', by simp [hm, hm', add_mul]⟩
  zero_mem' _ := ⟨0, by simp⟩
  smul_mem' := by
    rintro c v hv σ
    obtain ⟨m, hm⟩ := hv σ
    exact ⟨c * m, by simp [hm, mul_assoc]⟩

omit [NumberField F] in
@[simp]
theorem mem_tateEmbeddingLattice_iff {v : tateEmbeddingSpace F k} :
    v ∈ tateEmbeddingLattice F k ↔
      ∀ σ, ∃ m : ℤ, (v : (F →+* ℂ) → ℂ) σ = m * (2 * Real.pi * Complex.I) ^ k :=
  Iff.rfl

omit [NumberField F] in
/-- An element of the embedding Tate space lies in the lattice exactly when all of its
coordinates are integers. -/
theorem mem_tateEmbeddingLattice_iff_tateEmbeddingCoord {v : tateEmbeddingSpace F k} :
    v ∈ tateEmbeddingLattice F k ↔ ∀ σ, ∃ m : ℤ, tateEmbeddingCoord F k σ v = m := by
  simp only [mem_tateEmbeddingLattice_iff, tateEmbeddingCoord_eq_iff, Complex.ofReal_intCast]

/-- Integrality of the coordinates at the chosen embeddings `w.embedding` already characterizes
the embedding Tate lattice. -/
theorem mem_tateEmbeddingLattice_iff_tateEmbeddingCoordEquiv {v : tateEmbeddingSpace F k} :
    v ∈ tateEmbeddingLattice F k ↔
      ∀ w : TateEmbeddingIndex F k, ∃ m : ℤ, tateEmbeddingCoordEquiv F k v w = m := by
  refine ⟨fun hv w ↦ mem_tateEmbeddingLattice_iff_tateEmbeddingCoord.mp hv _, fun hv ↦ ?_⟩
  refine mem_tateEmbeddingLattice_iff_tateEmbeddingCoord.mpr fun σ ↦ ?_
  by_cases h : Even k ∨ ¬ComplexEmbedding.IsReal σ
  · obtain ⟨m, hm⟩ := hv ⟨mk σ, even_or_isComplex_mk h⟩
    rw [tateEmbeddingCoordEquiv_apply] at hm
    rcases tateEmbeddingCoord_eq_or_eq_neg_one_pow_mul v σ with h' | h'
    · exact ⟨m, h'.trans hm⟩
    · exact ⟨(-1) ^ k * m, by rw [h', hm]; push_cast; ring⟩
  · rw [not_or, Nat.not_even_iff_odd, not_not] at h
    exact ⟨0, by simp [tateEmbeddingCoord_eq_zero_of_isReal h.1 v h.2]⟩

variable (F k) in
/-- The coordinate equivalence identifies the embedding Tate lattice with the standard lattice
`ℤ^d`. -/
theorem tateEmbeddingLattice_eq_comap :
    tateEmbeddingLattice F k = ZLattice.comap ℝ
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (TateEmbeddingIndex F k))))
      (tateEmbeddingCoordEquiv F k).toLinearMap := by
  ext v
  rw [mem_tateEmbeddingLattice_iff_tateEmbeddingCoordEquiv, ← SetLike.mem_coe, ZLattice.coe_comap,
    Set.mem_preimage, SetLike.mem_coe, Basis.mem_span_iff_repr_mem]
  simp [eq_comm]

instance : DiscreteTopology (tateEmbeddingLattice F k) := by
  rw [tateEmbeddingLattice_eq_comap]
  infer_instance

instance : IsZLattice ℝ (tateEmbeddingLattice F k) where
  span_top := by
    rw [tateEmbeddingLattice_eq_comap]
    exact IsZLattice.span_top

variable (F k) in
/-- The coordinate Haar measure on the embedding Tate space: the image of Lebesgue measure on
`ℝ^d` under the inverse of the coordinate equivalence. -/
def tateEmbeddingMeasure : Measure (tateEmbeddingSpace F k) :=
  Measure.map (tateEmbeddingCoordEquiv F k).symm volume

instance : (tateEmbeddingMeasure F k).IsAddHaarMeasure :=
  (tateEmbeddingCoordEquiv F k).symm.isAddHaarMeasure_map volume

variable (F k) in
/-- The coordinate equivalence carries the coordinate Haar measure to Lebesgue measure. -/
theorem measurePreserving_tateEmbeddingCoordEquiv :
    MeasurePreserving (tateEmbeddingCoordEquiv F k) (tateEmbeddingMeasure F k) volume := by
  refine ⟨(tateEmbeddingCoordEquiv F k).continuous.measurable, ?_⟩
  rw [tateEmbeddingMeasure, Measure.map_map (tateEmbeddingCoordEquiv F k).continuous.measurable
    (tateEmbeddingCoordEquiv F k).symm.continuous.measurable]
  simp

variable (F k) in
/-- The embedding Tate lattice has covolume `1` for the coordinate Haar measure. -/
theorem covolume_tateEmbeddingLattice :
    ZLattice.covolume (tateEmbeddingLattice F k) (tateEmbeddingMeasure F k) = 1 := by
  classical
  rw [tateEmbeddingLattice_eq_comap, ZLattice.covolume_comap _ volume _
    (measurePreserving_tateEmbeddingCoordEquiv F k), ZLattice.covolume_eq_measure_fundamentalDomain
    _ volume (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (TateEmbeddingIndex F k)) volume),
    ZSpan.volume_real_fundamentalDomain, ← Pi.basisFun_det_apply, Basis.det_self, abs_one]

/-- For any choice `s` of one embedding at each infinite place, the coordinates at the embeddings
`s w` carry the coordinate Haar measure to Lebesgue measure: changing the embedding chosen at a
complex place only multiplies its coordinate by `(-1)^k`. -/
theorem measurePreserving_tateEmbeddingCoord (s : InfinitePlace F → F →+* ℂ)
    (hs : ∀ w, mk (s w) = w) :
    MeasurePreserving (fun v (w : TateEmbeddingIndex F k) ↦ tateEmbeddingCoord F k (s w.val) v)
      (tateEmbeddingMeasure F k) volume := by
  have hε (w : TateEmbeddingIndex F k) : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ v, tateEmbeddingCoord F k (s w.val) v = ε * tateEmbeddingCoordEquiv F k v w := by
    rcases mk_eq_iff.mp ((mk_embedding w.val).trans (hs w.val).symm) with h | h
    · exact ⟨1, Or.inl rfl, fun v ↦ by simp [h]⟩
    · exact ⟨(-1) ^ k, neg_one_pow_eq_or ℝ k, fun v ↦ by
        simp [← h, tateEmbeddingCoord_conjugate]⟩
  choose ε hε₁ hε₂ using hε
  have hfun : (fun v (w : TateEmbeddingIndex F k) ↦ tateEmbeddingCoord F k (s w.val) v) =
      (fun c w ↦ ε w * c w) ∘ tateEmbeddingCoordEquiv F k :=
    funext fun v ↦ funext fun w ↦ hε₂ w v
  rw [hfun]
  refine MeasurePreserving.comp (volume_preserving_pi fun w ↦ ?_)
    (measurePreserving_tateEmbeddingCoordEquiv F k)
  rcases hε₁ w with h | h
  · convert MeasurePreserving.id (volume : Measure ℝ) using 1
    funext x
    simp [h]
  · convert Measure.measurePreserving_neg (volume : Measure ℝ) using 1
    funext x
    simp [h]

end TauCeti.NumberField

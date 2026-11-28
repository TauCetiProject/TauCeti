/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
import TauCeti.NumberTheory.NumberField.CMField.ConjCompletion
import TauCeti.LinearAlgebra.Matrix.Hermitian.LocalRing
import TauCeti.NumberTheory.NumberField.CMField.IntegralAdeleNorm
import TauCeti.NumberTheory.NumberField.CMField.ResidueField
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup

/-!
# Orthonormal bases of unimodular hermitian matrices over the integral finite adeles

Let `E` be a CM field with complex conjugation `x ↦ conj x`, and `Ô = ∏_w O_w` its integral
finite adeles with the conjugation `a ↦ conj a`, which carries the component at a finite place
`w` to the component at `conj w`. This file proves that every hermitian matrix `b` over `Ô`
whose determinant is a unit of `Ô` is congruent to the identity: `kᴴ * b * k = 1` for some `k`,
necessarily invertible over `Ô`. In other words, a unimodular hermitian form on `Ôⁿ` has an
orthonormal basis, provided every finite place `w` with `conj w = w` lies over an odd prime and is
unramified over the maximal real subfield `E⁺`. This holds when `E` contains a primitive fourth
and a primitive seventh root of unity, for instance a primitive `5040`-th root of unity. For
`n = 1` the statement is that conjugation-fixed units of `Ô` are norms
(`NumberField.IsCMField.exists_star_mul_self_eq_of_forall_conjPlace_eq`), which the proof uses.

The proof is place by place.

* At a place `w` with `conj w = w`, conjugation is an involution of the local ring `O_w` in which
  `2` is a unit and the conjugation-fixed units are norms, and Gram–Schmidt over a local ring
  (`Matrix.IsHermitian.exists_conjTranspose_mul_mul_eq_one`) gives a local orthonormal basis
  (`IsDedekindDomain.HeightOneSpectrum.exists_transpose_map_mul_mul_eq_one_of_conjPlace_eq`).
* The places `w` with `conj w ≠ w` come in pairs `{w, conj w}`. Taking the components of `k` to
  be those of `b⁻¹` at one place of each pair (chosen by a well-ordering of the places) and those
  of `1` at the other gives `kᴴ * b * k = 1` at both, as `b` is hermitian.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.exists_transpose_map_mul_mul_eq_one_of_conjPlace_eq`: at a
  place `w` with `conj w = w`, odd and unramified over `E⁺`, a matrix with entries in `O_w`,
  hermitian for conjugation and with unit determinant, has an orthonormal basis over `O_w`.
* `NumberField.IsCMField.exists_conjTranspose_mul_mul_eq_one_of_forall_conjPlace_eq`: a hermitian
  matrix over `Ô` with unit determinant satisfies `kᴴ * b * k = 1` for some `k` over `Ô`, when
  every place fixed by conjugation is odd and unramified over `E⁺`.
* `NumberField.IsCMField.exists_conjTranspose_mul_mul_eq_one_of_isPrimitiveRoot`: the same when
  `E` contains a primitive fourth and a primitive seventh root of unity.

## References

* R. Jacobowitz, *Hermitian forms over local fields*, Amer. J. Math. 84 (1962), 441–465, for
  unimodular hermitian lattices over local rings of integers.
* `grh-lean`, https://github.com/lsernau/grh-lean, file `src/Lib/Adelic/Witt/WittTheorem.lean`
  (declaration `New.exists_orthonormal_Ô`); Apache 2.0, Copyright 2026 Anthropic, PBC. The
  statement, under the `5040` condition, follows that declaration; the proof here, place by place
  through Gram–Schmidt over the local rings `O_w`, is independent of that code.
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- **Orthonormal bases at a place fixed by conjugation.** Let `w` be a finite place of a CM field
with `conj w = w`, not over `2` and unramified over the maximal real subfield, that is with
`conj x - x ∉ w` for some integer `x`, and let `t ↦ conj t` be the automorphism of `E_w` extending
the conjugation of `E`. A matrix `B` with entries in `O_w`, hermitian for this conjugation
(`(conj B)ᵀ = B`) and with determinant a unit of `O_w`, satisfies `(conj K)ᵀ * B * K = 1` for some
matrix `K` with entries in `O_w`. -/
theorem exists_transpose_map_mul_mul_eq_one_of_conjPlace_eq
    {w : HeightOneSpectrum (𝓞 E)} (h : w.conjPlace = w) (h2 : (2 : 𝓞 E) ∉ w.asIdeal)
    (hne : ∃ x, ringOfIntegersComplexConj E x - x ∉ w.asIdeal)
    {B : Matrix ι ι (w.adicCompletion E)} (hB : ∀ i j, B i j ∈ w.adicCompletionIntegers E)
    (hBσ : (B.map (adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h)))ᵀ = B)
    (hdet : Valued.v B.det = 1) :
    ∃ K : Matrix ι ι (w.adicCompletion E), (∀ i j, K i j ∈ w.adicCompletionIntegers E) ∧
      (K.map (adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h)))ᵀ * B * K =
        1 := by
  set σ := adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h)
  -- conjugation preserves `O_w`, where it is an involution: a star structure on `O_w`
  have hσmem (x : w.adicCompletion E) (hx : x ∈ w.adicCompletionIntegers E) :
      σ x ∈ w.adicCompletionIntegers E := by
    rw [mem_adicCompletionIntegers] at hx ⊢
    rwa [valued_adicCompletionCongr]
  let σO : w.adicCompletionIntegers E →+* w.adicCompletionIntegers E :=
    (σ : w.adicCompletion E →+* w.adicCompletion E).restrict _ _ hσmem
  have hσO (x : w.adicCompletionIntegers E) : (σO x : w.adicCompletion E) = σ x := rfl
  let _ : StarRing (w.adicCompletionIntegers E) :=
    { star := σO
      star_involutive x := Subtype.ext (by
        rw [hσO, hσO, adicCompletionCongr_complexConj_apply_apply h])
      star_mul x y := by rw [map_mul, mul_comm]
      star_add := map_add σO }
  have hstar (x : w.adicCompletionIntegers E) :
      ((star x : w.adicCompletionIntegers E) : w.adicCompletion E) = σ x := rfl
  -- `B` as a unimodular hermitian matrix over the local ring `O_w`
  let BO : Matrix ι ι (w.adicCompletionIntegers E) := of fun i j ↦ ⟨B i j, hB i j⟩
  have hBO : BO.map (w.adicCompletionIntegers E).subtype = B := by
    ext i j
    rfl
  have hBO_herm : BO.IsHermitian := by
    refine Matrix.ext fun i j ↦ Subtype.ext ?_
    rw [conjTranspose_apply, hstar]
    exact congrFun (congrFun hBσ i) j
  have hBO_det : IsUnit BO.det := by
    rw [adicCompletionIntegers.isUnit_iff_valued_eq_one, ← hdet, ← hBO]
    exact congrArg Valued.v ((w.adicCompletionIntegers E).subtype.map_det BO)
  -- the trace `1 + conj 1 = 2` is a unit of `O_w`, and conjugation-fixed units are norms
  have h2O : IsUnit (1 + star 1 : w.adicCompletionIntegers E) := by
    rw [star_one, one_add_one_eq_two, ← map_ofNat (algebraMap (𝓞 E) _) 2]
    exact (w.isUnit_algebraMap_adicCompletionIntegers_iff (K := E) 2).2 h2
  have hnorm (u : w.adicCompletionIntegers E) (hu : IsUnit u) (hsu : star u = u) :
      ∃ y, star y * y = u := by
    obtain ⟨y, hy, hyu⟩ := exists_adicCompletionCongr_mul_self_eq h h2 hne
      (adicCompletionIntegers.isUnit_iff_valued_eq_one.1 hu) (by rw [← hstar, hsu])
    exact ⟨⟨y, hy⟩, Subtype.ext hyu⟩
  obtain ⟨KO, -, hKO⟩ := hBO_herm.exists_conjTranspose_mul_mul_eq_one hBO_det h2O hnorm
  refine ⟨KO.map (w.adicCompletionIntegers E).subtype, fun i j ↦ (KO i j).property, ?_⟩
  have hKOσ : ((KO.map (w.adicCompletionIntegers E).subtype).map σ)ᵀ =
      KOᴴ.map (w.adicCompletionIntegers E).subtype := by
    ext i j
    rfl
  rw [hKOσ, ← hBO, ← Matrix.map_mul, ← Matrix.map_mul, hKO,
    Matrix.map_one _ (map_zero _) (map_one _)]

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField.IsCMField

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι : Type*}

/-! ### Matrices over `Ô`, place by place -/

/-- The components at a place `w'` of the conjugate transpose of a matrix over `Ô` are the
conjugates of the components of its transpose at the conjugate place `w` of `w'`. -/
private theorem map_conjTranspose_apply_place {w w' : HeightOneSpectrum (𝓞 E)}
    (hw : ∀ x, w'.valuation E ((complexConj E).toRingEquiv x) = w.valuation E x)
    (M : Matrix ι ι (integralAdeles (𝓞 E) E)) :
    Mᴴ.map (fun a ↦ (a : 𝔸ᶠ[E]) w') =
      ((M.map (fun a ↦ (a : 𝔸ᶠ[E]) w)).map (HeightOneSpectrum.adicCompletionCongr w w' _ hw))ᵀ :=
  Matrix.ext fun i j ↦ by
    simp only [map_apply, conjTranspose_apply, transpose_apply, coe_star_integralAdeles,
      star_apply_eq_adicCompletionCongr hw]

/-- The components at a place `w'` of a congruence `Mᴴ * b * N` of matrices over `Ô`, in terms of
the components of `M` at the conjugate place `w` of `w'`. -/
private theorem map_conjTranspose_mul_mul_apply_place [Fintype ι]
    {w w' : HeightOneSpectrum (𝓞 E)}
    (hw : ∀ x, w'.valuation E ((complexConj E).toRingEquiv x) = w.valuation E x)
    (M b N : Matrix ι ι (integralAdeles (𝓞 E) E)) :
    (Mᴴ * b * N).map (fun a ↦ (a : 𝔸ᶠ[E]) w') =
      ((M.map (fun a ↦ (a : 𝔸ᶠ[E]) w)).map (HeightOneSpectrum.adicCompletionCongr w w' _ hw))ᵀ *
        b.map (fun a ↦ (a : 𝔸ᶠ[E]) w') * N.map (fun a ↦ (a : 𝔸ᶠ[E]) w') := by
  -- the components at `w'` are a ring homomorphism, `RestrictedProduct.evalRingHom`
  have hmul (A B : Matrix ι ι (integralAdeles (𝓞 E) E)) : (A * B).map (fun a ↦ (a : 𝔸ᶠ[E]) w') =
      A.map (fun a ↦ (a : 𝔸ᶠ[E]) w') * B.map (fun a ↦ (a : 𝔸ᶠ[E]) w') :=
    Matrix.map_mul (f := (RestrictedProduct.evalRingHom _ w').comp
      (integralAdeles (𝓞 E) E).val.toRingHom)
  rw [hmul, hmul, map_conjTranspose_apply_place hw]

omit [IsCMField E] in
/-- The components at a finite place of the determinant of a matrix over `Ô` with unit
determinant are units of `O_w`. -/
private theorem valued_det_map_apply_place [Fintype ι] [DecidableEq ι]
    {b : Matrix ι ι (integralAdeles (𝓞 E) E)}
    (hdet : IsUnit b.det) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (b.map (fun a ↦ (a : 𝔸ᶠ[E]) w)).det = 1 := by
  have hunits : Units.map ((integralAdeles (𝓞 E) E).val.toRingHom :
      integralAdeles (𝓞 E) E →* 𝔸ᶠ[E]) hdet.unit ∈ integralUnits (𝓞 E) E := by
    rw [← range_units_map_val_eq_integralUnits]
    exact ⟨_, rfl⟩
  rw [show (b.map fun a ↦ (a : 𝔸ᶠ[E]) w).det = _ from ((RestrictedProduct.evalRingHom _ w).comp
    (integralAdeles (𝓞 E) E).val.toRingHom).map_det b |>.symm]
  exact mem_integralUnits_iff.1 hunits w

open Classical in
/-- **The congruence on a split pair.** Let `w` be a finite place with `conj w ≠ w` and `b` a
hermitian matrix over `Ô` with unit determinant. If `k` agrees with `b⁻¹` at the first place of
the pair `{w, conj w}` (for a well-ordering of the places) and with `1` at the second, then
`kᴴ * b * k = 1` at `w`. -/
private theorem map_conjTranspose_mul_mul_apply_place_eq_one [Fintype ι] [DecidableEq ι]
    {b k : Matrix ι ι (integralAdeles (𝓞 E) E)} (hb : b.IsHermitian) (hdet : IsUnit b.det)
    {w : HeightOneSpectrum (𝓞 E)} (h : w.conjPlace ≠ w)
    (h₁ : k.map (fun a ↦ (a : 𝔸ᶠ[E]) w) =
      (if WellOrderingRel w w.conjPlace then b⁻¹ else 1).map (fun a ↦ (a : 𝔸ᶠ[E]) w))
    (h₂ : k.map (fun a ↦ (a : 𝔸ᶠ[E]) w.conjPlace) =
      (if WellOrderingRel w.conjPlace w then b⁻¹ else 1).map (fun a ↦ (a : 𝔸ᶠ[E]) w.conjPlace)) :
    (kᴴ * b * k).map (fun a ↦ (a : 𝔸ᶠ[E]) w) = 1 := by
  -- `k` agrees with `N₁` at `w` and with `N₂` at `conj w`, where `N₂ᴴ * b * N₁ = 1`
  suffices hN : (if WellOrderingRel w.conjPlace w then b⁻¹ else 1)ᴴ * b *
      (if WellOrderingRel w w.conjPlace then b⁻¹ else 1) = 1 by
    rw [map_conjTranspose_mul_mul_apply_place (HeightOneSpectrum.valuation_complexConj w), h₁,
      h₂, ← map_conjTranspose_mul_mul_apply_place, hN]
    exact Matrix.map_one _ rfl rfl
  rcases trichotomous_of WellOrderingRel w w.conjPlace with hr | heq | hr
  · -- the first place of the pair
    simp only [hr, asymm hr, ↓reduceIte]
    rw [conjTranspose_one, Matrix.one_mul, mul_nonsing_inv b hdet]
  · exact absurd heq.symm h
  · -- the second place of the pair
    have hinv := congrArg conjTranspose (mul_nonsing_inv b hdet)
    rw [conjTranspose_mul, conjTranspose_one, hb.eq] at hinv
    simp only [hr, asymm hr, ↓reduceIte]
    rw [Matrix.mul_one, hinv]

/-- **Unimodular hermitian matrices over the integral finite adeles have orthonormal bases.** Let
`E` be a CM field in which every finite place `w` with `conj w = w` lies over an odd prime and is
unramified over the maximal real subfield, that is `conj x - x ∉ w` for some integer `x`. Then
every hermitian matrix `b` over the integral finite adeles `Ô` whose determinant is a unit of `Ô`
satisfies `kᴴ * b * k = 1` for some invertible matrix `k` over `Ô`. -/
theorem exists_conjTranspose_mul_mul_eq_one_of_forall_conjPlace_eq [Fintype ι] [DecidableEq ι]
    (h2 : ∀ w : HeightOneSpectrum (𝓞 E), w.conjPlace = w → (2 : 𝓞 E) ∉ w.asIdeal)
    (hne : ∀ w : HeightOneSpectrum (𝓞 E), w.conjPlace = w →
      ∃ x, ringOfIntegersComplexConj E x - x ∉ w.asIdeal)
    {b : Matrix ι ι (integralAdeles (𝓞 E) E)} (hb : b.IsHermitian) (hdet : IsUnit b.det) :
    ∃ k : Matrix ι ι (integralAdeles (𝓞 E) E), IsUnit k ∧ kᴴ * b * k = 1 := by
  classical
  -- local orthonormal bases at the places fixed by conjugation
  have hloc (w : HeightOneSpectrum (𝓞 E)) (h : w.conjPlace = w) :=
    HeightOneSpectrum.exists_transpose_map_mul_mul_eq_one_of_conjPlace_eq h (h2 w h) (hne w h)
      (B := b.map fun a ↦ (a : 𝔸ᶠ[E]) w) (fun i j ↦ mem_integralAdeles.1 (b i j).property w)
      (by rw [← map_conjTranspose_apply_place, hb.eq]) (valued_det_map_apply_place hdet w)
  choose K hKmem hK using hloc
  -- the components of `k`: a local basis at `w = conj w`, and `b⁻¹`, `1` on a split pair
  let Kc (w : HeightOneSpectrum (𝓞 E)) : Matrix ι ι (w.adicCompletion E) :=
    if h : w.conjPlace = w then K w h
    else (if WellOrderingRel w w.conjPlace then b⁻¹ else 1).map (fun a ↦ (a : 𝔸ᶠ[E]) w)
  have hKc_mem (w : HeightOneSpectrum (𝓞 E)) (i j : ι) :
      Kc w i j ∈ w.adicCompletionIntegers E := by
    simp only [Kc]
    split_ifs with h
    · exact hKmem w h i j
    · exact mem_integralAdeles.1 (b⁻¹ i j).property w
    · exact mem_integralAdeles.1 ((1 : Matrix ι ι (integralAdeles (𝓞 E) E)) i j).property w
  let k : Matrix ι ι (integralAdeles (𝓞 E) E) := of fun i j ↦
    ⟨integralEmbedding fun w ↦ ⟨Kc w i j, hKc_mem w i j⟩,
      mem_integralAdeles.2 fun w ↦ by rw [integralEmbedding_apply]; exact hKc_mem w i j⟩
  have hk (w : HeightOneSpectrum (𝓞 E)) : k.map (fun a ↦ (a : 𝔸ᶠ[E]) w) = Kc w :=
    Matrix.ext fun i j ↦ integralEmbedding_apply _ w
  -- `kᴴ * b * k = 1` at every place
  have hplace (w : HeightOneSpectrum (𝓞 E)) : (kᴴ * b * k).map (fun a ↦ (a : 𝔸ᶠ[E]) w) =
      (1 : Matrix ι ι (integralAdeles (𝓞 E) E)).map (fun a ↦ (a : 𝔸ᶠ[E]) w) := by
    rw [Matrix.map_one _ rfl rfl]
    by_cases h : w.conjPlace = w
    · rw [map_conjTranspose_mul_mul_apply_place
        (HeightOneSpectrum.valuation_complexConj_of_conjPlace_eq h), hk w]
      simpa only [Kc, h, ↓reduceDIte] using hK w h
    -- a split pair: `k` agrees with `b⁻¹` at its first place and with `1` at its second
    refine map_conjTranspose_mul_mul_apply_place_eq_one hb hdet h ?_ ?_ <;> rw [hk] <;>
      simp only [Kc, h, Ne.symm h, HeightOneSpectrum.conjPlace_conjPlace, ↓reduceDIte]
  refine ⟨k, ?_⟩
  have hkb : kᴴ * b * k = 1 := Matrix.ext fun i j ↦
    Subtype.ext (FiniteAdeleRing.ext E fun w ↦ congrFun (congrFun (hplace w) i) j)
  exact ⟨IsUnit.of_mul_eq_one_right _ hkb, hkb⟩

/-- **Unimodular hermitian matrices over the integral finite adeles have orthonormal bases, under
the `5040` condition.** If the CM field `E` contains a primitive fourth and a primitive seventh
root of unity (for instance a primitive `5040`-th root of unity), every hermitian matrix `b` over
the integral finite adeles `Ô` whose determinant is a unit of `Ô` satisfies `kᴴ * b * k = 1` for
some invertible matrix `k` over `Ô`. -/
theorem exists_conjTranspose_mul_mul_eq_one_of_isPrimitiveRoot [Fintype ι] [DecidableEq ι]
    {ζ₄ ζ₇ : E}
    (h₄ : IsPrimitiveRoot ζ₄ 4) (h₇ : IsPrimitiveRoot ζ₇ 7)
    {b : Matrix ι ι (integralAdeles (𝓞 E) E)} (hb : b.IsHermitian) (hdet : IsUnit b.det) :
    ∃ k : Matrix ι ι (integralAdeles (𝓞 E) E), IsUnit k ∧ kᴴ * b * k = 1 :=
  exists_conjTranspose_mul_mul_eq_one_of_forall_conjPlace_eq
    (fun w h ↦ (two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot h₄ h₇ w.asIdeal
      (HeightOneSpectrum.map_asIdeal_of_conjPlace_eq h)).1)
    (fun w h ↦ (two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot h₄ h₇ w.asIdeal
      (HeightOneSpectrum.map_asIdeal_of_conjPlace_eq h)).2)
    hb hdet

end NumberField.IsCMField

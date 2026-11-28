/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
public import TauCeti.NumberTheory.NumberField.CMField.ConjCompletion
import TauCeti.LinearAlgebra.Matrix.Hermitian.LocalRing
import TauCeti.NumberTheory.NumberField.CMField.IntegralAdeleNorm
import TauCeti.NumberTheory.NumberField.CMField.ResidueField

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
(`NumberField.IsCMField.exists_star_mul_self_eq_of_forall_conjPlace_eq`).
The fixed-place proof uses the local norm lemma
`IsDedekindDomain.HeightOneSpectrum.exists_adicCompletionCongr_mul_self_eq`; the well-ordered
split-pair assembly follows the proof of
`NumberField.IsCMField.exists_star_mul_self_eq_of_forall_conjPlace_eq`.

The proof is place by place.

* At a place `w` with `conj w = w`, conjugation is an involution of the local ring `O_w` in which
  `2` is a unit and the conjugation-fixed units are norms, and Gram–Schmidt over a local ring
  (`Matrix.IsHermitian.exists_conjTranspose_mul_mul_eq_one`) gives a local orthonormal basis
  (`IsDedekindDomain.HeightOneSpectrum.exists_conjTranspose_mul_mul_eq_one_of_conjPlace_eq`).
* The places `w` with `conj w ≠ w` come in pairs `{w, conj w}`. Taking the components of `k` to
  be those of `b⁻¹` at one place of each pair (chosen by a well-ordering of the places) and those
  of `1` at the other gives `kᴴ * b * k = 1` at both, as `b` is hermitian.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.exists_conjTranspose_mul_mul_eq_one_of_conjPlace_eq`: at a
  place `w` with `conj w = w`, odd and unramified over `E⁺`, a matrix with entries in `O_w`,
  hermitian for conjugation and with unit determinant, has an orthonormal basis over `O_w`.
* `Matrix.IsHermitian.exists_conjTranspose_mul_mul_eq_one_of_forall_conjPlace_eq`: a hermitian
  matrix over `Ô` with unit determinant satisfies `kᴴ * b * k = 1` for some `k` over `Ô`, when
  every place fixed by conjugation is odd and unramified over `E⁺`.
* `Matrix.IsHermitian.exists_conjTranspose_mul_mul_eq_one_of_isPrimitiveRoot`: the same when
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

/-- **Orthonormal bases at a place fixed by conjugation.** At an odd place unramified over
the maximal real subfield, a unimodular hermitian matrix over the completion integers admits an
orthonormal basis for the star structure `adicCompletionIntegersStarRing`. -/
theorem exists_conjTranspose_mul_mul_eq_one_of_conjPlace_eq
    (w : HeightOneSpectrum (𝓞 E)) (h : w.conjPlace = w) (h2 : (2 : 𝓞 E) ∉ w.asIdeal)
    (hne : ∃ x, ringOfIntegersComplexConj E x - x ∉ w.asIdeal) :
    let _ := w.adicCompletionIntegersStarRing h
    ∀ {B : Matrix ι ι (w.adicCompletionIntegers E)}, B.IsHermitian → IsUnit B.det →
      ∃ K : Matrix ι ι (w.adicCompletionIntegers E), IsUnit K ∧ Kᴴ * B * K = 1 := by
  let _ := w.adicCompletionIntegersStarRing h
  dsimp only
  intro B hB hdet
  have hstar := w.coe_star_adicCompletionIntegers h
  have h2O : IsUnit (1 + star 1 : w.adicCompletionIntegers E) := by
    rw [star_one, one_add_one_eq_two, ← map_ofNat (algebraMap (𝓞 E) _) 2]
    exact (w.isUnit_algebraMap_adicCompletionIntegers_iff (K := E) 2).2 h2
  have hnorm (u : w.adicCompletionIntegers E) (hu : IsUnit u) (hsu : star u = u) :
      ∃ y, star y * y = u := by
    obtain ⟨y, hy, hyu⟩ := exists_adicCompletionCongr_mul_self_eq h h2 hne
      (adicCompletionIntegers.isUnit_iff_valued_eq_one.1 hu) (by rw [← hstar, hsu])
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change ((star (⟨y, hy⟩ : w.adicCompletionIntegers E) : w.adicCompletionIntegers E) :
      w.adicCompletion E) * y = u
    rwa [hstar]
  exact hB.exists_conjTranspose_mul_mul_eq_one hdet h2O hnorm

end IsDedekindDomain.HeightOneSpectrum

namespace Matrix.IsHermitian

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι : Type*}

/-! ### Matrices over `Ô`, place by place -/

/-- The components at a place `w'` of a congruence `Mᴴ * b * N` of matrices over `Ô`, in terms of
the components of `M` at the conjugate place `w` of `w'`. -/
private theorem map_conjTranspose_mul_mul_apply_place [Fintype ι]
    {w w' : HeightOneSpectrum (𝓞 E)}
    (hw : ∀ x, w'.valuation E ((complexConj E).toRingEquiv x) = w.valuation E x)
    (M b N : Matrix ι ι (integralAdeles (𝓞 E) E)) :
    (Mᴴ * b * N).map ((w'.adicCompletionIntegers E).subtype.comp (integralProj E w')) =
      ((M.map ((w.adicCompletionIntegers E).subtype.comp (integralProj E w))).map
        (HeightOneSpectrum.adicCompletionCongr w w' _ hw))ᵀ *
        b.map ((w'.adicCompletionIntegers E).subtype.comp (integralProj E w')) *
        N.map ((w'.adicCompletionIntegers E).subtype.comp (integralProj E w')) := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_conjTranspose_apply_place M hw]

open Classical in
/-- **The congruence on a split pair.** Let `w` be a finite place with `conj w ≠ w` and `b` a
hermitian matrix over `Ô` with unit determinant. If `k` agrees with `b⁻¹` at the first place of
the pair `{w, conj w}` (for a well-ordering of the places) and with `1` at the second, then
`kᴴ * b * k = 1` at `w`. -/
private theorem map_conjTranspose_mul_mul_apply_place_eq_one [Fintype ι] [DecidableEq ι]
    {b k : Matrix ι ι (integralAdeles (𝓞 E) E)} (hb : b.IsHermitian) (hdet : IsUnit b.det)
    {w : HeightOneSpectrum (𝓞 E)} (h : w.conjPlace ≠ w)
    (h₁ : k.map ((w.adicCompletionIntegers E).subtype.comp (integralProj E w)) =
      (if WellOrderingRel w w.conjPlace then b⁻¹ else 1).map
        ((w.adicCompletionIntegers E).subtype.comp (integralProj E w)))
    (h₂ : k.map ((w.conjPlace.adicCompletionIntegers E).subtype.comp (integralProj E w.conjPlace)) =
      (if WellOrderingRel w.conjPlace w then b⁻¹ else 1).map
        ((w.conjPlace.adicCompletionIntegers E).subtype.comp (integralProj E w.conjPlace))) :
    (kᴴ * b * k).map ((w.adicCompletionIntegers E).subtype.comp (integralProj E w)) = 1 := by
  -- `k` agrees with `N₁` at `w` and with `N₂` at `conj w`, where `N₂ᴴ * b * N₁ = 1`
  suffices hN : (if WellOrderingRel w.conjPlace w then b⁻¹ else 1)ᴴ * b *
      (if WellOrderingRel w w.conjPlace then b⁻¹ else 1) = 1 by
    rw [map_conjTranspose_mul_mul_apply_place (HeightOneSpectrum.valuation_complexConj w), h₁,
      h₂, ← map_conjTranspose_mul_mul_apply_place, hN]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rcases trichotomous_of WellOrderingRel w w.conjPlace with hr | heq | hr
  · -- the first place of the pair
    simp only [hr, asymm hr, ↓reduceIte]
    rw [conjTranspose_one, Matrix.one_mul, mul_nonsing_inv b hdet]
  · exact absurd heq.symm h
  · -- the second place of the pair
    have hinv := congrArg Matrix.conjTranspose (mul_nonsing_inv b hdet)
    rw [conjTranspose_mul, conjTranspose_one, hb.eq] at hinv
    simp only [hr, asymm hr, ↓reduceIte]
    rw [Matrix.mul_one, hinv]

/-- Project the integral local orthonormal basis into the completion for the assembly over
all places. -/
private theorem exists_local_congruence [Fintype ι] [DecidableEq ι]
    {b : Matrix ι ι (integralAdeles (𝓞 E) E)} (hb : b.IsHermitian) (hdet : IsUnit b.det)
    (w : HeightOneSpectrum (𝓞 E)) (h : w.conjPlace = w)
    (h2 : (2 : 𝓞 E) ∉ w.asIdeal)
    (hne : ∃ x, ringOfIntegersComplexConj E x - x ∉ w.asIdeal) :
      ∃ K : Matrix ι ι (w.adicCompletion E),
        (∀ i j, K i j ∈ w.adicCompletionIntegers E) ∧
        (K.map (HeightOneSpectrum.adicCompletionCongr w w _
          (HeightOneSpectrum.valuation_complexConj_of_conjPlace_eq h)))ᵀ *
          b.map ((w.adicCompletionIntegers E).subtype.comp (integralProj E w)) * K = 1 := by
  let _ := w.adicCompletionIntegersStarRing h
  let B := b.map (integralProj E w)
  have hB : B.IsHermitian := by
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    rw [conjTranspose_apply, w.coe_star_adicCompletionIntegers h]
    have hp := congrArg (fun M ↦ M.map
      ((w.adicCompletionIntegers E).subtype.comp (integralProj E w))) hb.eq
    rw [Matrix.map_conjTranspose_apply_place b
      (HeightOneSpectrum.valuation_complexConj_of_conjPlace_eq h)] at hp
    exact congrFun (congrFun hp i) j
  have hdetB : IsUnit B.det := by
    change IsUnit (b.map (integralProj E w)).det
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map _
  obtain ⟨KO, -, hKO⟩ := w.exists_conjTranspose_mul_mul_eq_one_of_conjPlace_eq h
    h2 hne hB hdetB
  refine ⟨KO.map (w.adicCompletionIntegers E).subtype, fun i j ↦ (KO i j).property, ?_⟩
  have hKOσ : ((KO.map (w.adicCompletionIntegers E).subtype).map
      (HeightOneSpectrum.adicCompletionCongr w w _
        (HeightOneSpectrum.valuation_complexConj_of_conjPlace_eq h)))ᵀ =
      KOᴴ.map (w.adicCompletionIntegers E).subtype := by
    ext i j
    simp only [map_apply, transpose_apply, conjTranspose_apply,
      ValuationSubring.subtype_apply, w.coe_star_adicCompletionIntegers h]
  rw [hKOσ]
  simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _),
    B, Matrix.map_map, RingHom.coe_comp] using
    congrArg (fun M ↦ M.map (w.adicCompletionIntegers E).subtype) hKO

/-- **Unimodular hermitian matrices over the integral finite adeles have orthonormal bases.** Let
`E` be a CM field in which every finite place `w` with `conj w = w` lies over an odd prime and is
unramified over the maximal real subfield, that is `conj x - x ∉ w` for some integer `x`. Then
every hermitian matrix `b` over the integral finite adeles `Ô` whose determinant is a unit of `Ô`
satisfies `kᴴ * b * k = 1` for some invertible matrix `k` over `Ô`. -/
theorem exists_conjTranspose_mul_mul_eq_one_of_forall_conjPlace_eq [Fintype ι] [DecidableEq ι]
    {b : Matrix ι ι (integralAdeles (𝓞 E) E)} (hb : b.IsHermitian)
    (h2 : ∀ w : HeightOneSpectrum (𝓞 E), w.conjPlace = w → (2 : 𝓞 E) ∉ w.asIdeal)
    (hne : ∀ w : HeightOneSpectrum (𝓞 E), w.conjPlace = w →
      ∃ x, ringOfIntegersComplexConj E x - x ∉ w.asIdeal)
    (hdet : IsUnit b.det) :
    ∃ k : Matrix ι ι (integralAdeles (𝓞 E) E), IsUnit k ∧ kᴴ * b * k = 1 := by
  classical
  have hloc (w : HeightOneSpectrum (𝓞 E)) (h : w.conjPlace = w) :=
    exists_local_congruence hb hdet w h (h2 w h) (hne w h)
  choose K hKmem hK using hloc
  let Kc (w : HeightOneSpectrum (𝓞 E)) : Matrix ι ι (w.adicCompletion E) :=
    if h : w.conjPlace = w then K w h
    else (if WellOrderingRel w w.conjPlace then b⁻¹ else 1).map
      ((w.adicCompletionIntegers E).subtype.comp (integralProj E w))
  have hKc_mem (w : HeightOneSpectrum (𝓞 E)) (i j : ι) :
      Kc w i j ∈ w.adicCompletionIntegers E := by
    simp only [Kc]
    split_ifs with h
    · exact hKmem w h i j
    · exact ((integralProj E w) (b⁻¹ i j)).property
    · exact ((integralProj E w) ((1 : Matrix ι ι (integralAdeles (𝓞 E) E)) i j)).property
  let k : Matrix ι ι (integralAdeles (𝓞 E) E) := of fun i j ↦
    ⟨integralEmbedding fun w ↦ ⟨Kc w i j, hKc_mem w i j⟩,
      mem_integralAdeles.2 fun w ↦ by rw [integralEmbedding_apply]; exact hKc_mem w i j⟩
  have hk (w : HeightOneSpectrum (𝓞 E)) :
      k.map ((w.adicCompletionIntegers E).subtype.comp (integralProj E w)) = Kc w :=
    Matrix.ext fun i j ↦ by
      simp only [map_apply, RingHom.comp_apply, ValuationSubring.subtype_apply,
        coe_integralProj_apply]
      exact integralEmbedding_apply _ w
  have hplace (w : HeightOneSpectrum (𝓞 E)) : (kᴴ * b * k).map
        ((w.adicCompletionIntegers E).subtype.comp (integralProj E w)) =
      (1 : Matrix ι ι (integralAdeles (𝓞 E) E)).map
        ((w.adicCompletionIntegers E).subtype.comp (integralProj E w)) := by
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    by_cases h : w.conjPlace = w
    · rw [map_conjTranspose_mul_mul_apply_place
        (HeightOneSpectrum.valuation_complexConj_of_conjPlace_eq h), hk w]
      simpa only [Kc, h, ↓reduceDIte] using hK w h
    -- a split pair: `k` agrees with `b⁻¹` at its first place and with `1` at its second
    refine map_conjTranspose_mul_mul_apply_place_eq_one hb hdet h ?_ ?_ <;> rw [hk] <;>
      simp only [Kc, h, Ne.symm h, HeightOneSpectrum.conjPlace_conjPlace, ↓reduceDIte]
  refine ⟨k, ?_⟩
  have hkb : kᴴ * b * k = 1 := Matrix.ext fun i j ↦
    Subtype.ext (FiniteAdeleRing.ext E fun w ↦ by
      simpa only [map_apply, RingHom.comp_apply, ValuationSubring.subtype_apply,
        coe_integralProj_apply] using congrFun (congrFun (hplace w) i) j)
  exact ⟨IsUnit.of_mul_eq_one_right _ hkb, hkb⟩

/-- **Unimodular hermitian matrices over the integral finite adeles have orthonormal bases, under
the `5040` condition.** If the CM field `E` contains a primitive fourth and a primitive seventh
root of unity (for instance a primitive `5040`-th root of unity), every hermitian matrix `b` over
the integral finite adeles `Ô` whose determinant is a unit of `Ô` satisfies `kᴴ * b * k = 1` for
some invertible matrix `k` over `Ô`. -/
theorem exists_conjTranspose_mul_mul_eq_one_of_isPrimitiveRoot [Fintype ι] [DecidableEq ι]
    {b : Matrix ι ι (integralAdeles (𝓞 E) E)} (hb : b.IsHermitian)
    {ζ₄ ζ₇ : E}
    (h₄ : IsPrimitiveRoot ζ₄ 4) (h₇ : IsPrimitiveRoot ζ₇ 7)
    (hdet : IsUnit b.det) :
    ∃ k : Matrix ι ι (integralAdeles (𝓞 E) E), IsUnit k ∧ kᴴ * b * k = 1 :=
  hb.exists_conjTranspose_mul_mul_eq_one_of_forall_conjPlace_eq
    (fun w h ↦ (two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot h₄ h₇ w.asIdeal
      (HeightOneSpectrum.map_asIdeal_of_conjPlace_eq h)).1)
    (fun w h ↦ (two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot h₄ h₇ w.asIdeal
      (HeightOneSpectrum.map_asIdeal_of_conjPlace_eq h)).2)
    hdet

end Matrix.IsHermitian

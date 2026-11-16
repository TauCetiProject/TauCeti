/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Basic
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Inverse

import TauCeti.Data.SignType.Basic

/-!
# The full archimedean value of a presentation

Let `χ` be a presentation at a modulus `𝔪` of an algebraic Hecke character of a number field `K`,
with algebraic infinity type `n`. In Neukirch's decomposition `χ((a)) = χ_f(a) χ_∞(a)` of a
Größencharakter on principal ideals (VII §6, (6.1)), the full archimedean factor `χ_∞`
(`Grossencharacter.archimedeanValue`) multiplies the algebraic monomial `∏_τ τ(a) ^ (n τ)` by the
real sign twist `sgn(τ_w a) ^ (ε_w - n_w)` at each real place `w ∈ 𝔪.infinitePart`, where `ε_w`
is the real parity of `χ.toHeckeCharacter` (outside `𝔪.infinitePart`, the two parities already
agree by `Grossencharacter.realParity_eq`).

On every nonzero element of `K`, this coincides with the product of all infinite components of
`χ.toHeckeCharacter` (`archimedeanValue_eq_prod_infiniteComponent`), without any sign hypothesis.
On elements congruent to `1` modulo `𝔪`, positivity at `𝔪.infinitePart` kills the sign twists, so
`archimedeanValue` reduces to the algebraic monomial (`archimedeanValue_eq_of_isCongrOne`).

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.archimedeanValue`: the full archimedean value `χ_∞(x)` on
  `K`, including real sign twists.

## Main results

* `TauCeti.LFunctions.Grossencharacter.archimedeanValue_mul`,
  `TauCeti.LFunctions.Grossencharacter.archimedeanValue_inv`, and
  `TauCeti.LFunctions.Grossencharacter.archimedeanValue_ne_zero`: multiplicativity and
  nonvanishing on `K`.
* `TauCeti.LFunctions.Grossencharacter.archimedeanValue_eq_prod_infiniteComponent`: on `Kˣ`,
  `archimedeanValue` is the product of all infinite components of `χ.toHeckeCharacter`.
* `TauCeti.LFunctions.Grossencharacter.archimedeanValue_eq_of_isCongrOne`: on elements congruent
  to `1` modulo `𝔪`, `archimedeanValue` reduces to the algebraic monomial.
* `TauCeti.LFunctions.Grossencharacter.archimedeanValue_inverse` and
  `TauCeti.LFunctions.Grossencharacter.archimedeanValue_congr`: behavior under inversion and
  independence of the choice of presentation.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
* A. Weil, *Basic Number Theory*, Chapter VII, §3.
-/

public section
noncomputable section

open NumberField NumberField.InfinitePlace.Completion
open scoped NumberField

namespace TauCeti.LFunctions.Grossencharacter

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **The full archimedean value** of a presentation `χ` at `x ∈ K`: the algebraic monomial
`∏_τ τ(x) ^ (n τ)` multiplied, at each real place `w ∈ 𝔪.infinitePart`, by
`sgn(τ_w x) ^ (ε_w - n_w)`, where `ε_w` is the real parity of `χ.toHeckeCharacter`. Outside
`𝔪.infinitePart`, the parity difference vanishes by `realParity_eq`, so on `Kˣ` the full value
agrees with the product of all infinite components of `χ.toHeckeCharacter`
(`archimedeanValue_eq_prod_infiniteComponent`). -/
def archimedeanValue (χ : Grossencharacter K 𝔪) (x : K) : ℂ :=
  (∏ τ : K →+* ℂ, τ x ^ χ.infinityType τ) *
    ∏ w ∈ 𝔪.infinitePart,
      (SignType.sign (InfinitePlace.embedding_of_isReal w.2 x) : ℂ) ^
        (χ.toHeckeCharacter.infinityType.realParity w -
          (χ.infinityType w.1.embedding : ZMod 2)).val

/-- The defining equation of the full archimedean value. -/
theorem archimedeanValue_def (χ : Grossencharacter K 𝔪) (x : K) :
    χ.archimedeanValue x =
      (∏ τ : K →+* ℂ, τ x ^ χ.infinityType τ) *
        ∏ w ∈ 𝔪.infinitePart,
          (SignType.sign (InfinitePlace.embedding_of_isReal w.2 x) : ℂ) ^
            (χ.toHeckeCharacter.infinityType.realParity w -
              (χ.infinityType w.1.embedding : ZMod 2)).val :=
  (rfl)

/-- Every power of a real sign in `ℂ` is its own inverse, including at `0`. -/
private theorem coe_sign_pow_inv (r : ℝ) (n : ℕ) :
    ((SignType.sign r : ℂ) ^ n)⁻¹ = (SignType.sign r : ℂ) ^ n := by
  rw [← inv_pow]
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · simp [sign_neg hr]
  · simp
  · simp [sign_pos hr]

/-- The full archimedean value at `1` is `1`. -/
@[simp]
theorem archimedeanValue_one (χ : Grossencharacter K 𝔪) : χ.archimedeanValue 1 = 1 := by
  simp [archimedeanValue]

/-- The full archimedean value is multiplicative on `K`. -/
theorem archimedeanValue_mul (χ : Grossencharacter K 𝔪) (x y : K) :
    χ.archimedeanValue (x * y) = χ.archimedeanValue x * χ.archimedeanValue y := by
  simp only [archimedeanValue, map_mul, mul_zpow, sign_mul, SignType.coe_mul, mul_pow,
    Finset.prod_mul_distrib]
  ring

/-- The full archimedean value respects inversion on `K`. -/
theorem archimedeanValue_inv (χ : Grossencharacter K 𝔪) (x : K) :
    χ.archimedeanValue x⁻¹ = (χ.archimedeanValue x)⁻¹ := by
  simp only [archimedeanValue, map_inv₀, inv_zpow, TauCeti.sign_inv,
    Finset.prod_inv_distrib, mul_inv]
  congr 1
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun _ _ ↦ (coe_sign_pow_inv _ _).symm

/-- The full archimedean value respects division on `K`. -/
theorem archimedeanValue_div (χ : Grossencharacter K 𝔪) (x y : K) :
    χ.archimedeanValue (x / y) = χ.archimedeanValue x / χ.archimedeanValue y := by
  rw [div_eq_mul_inv, archimedeanValue_mul, archimedeanValue_inv, div_eq_mul_inv]

/-- The full archimedean value is nonzero on nonzero elements of `K`. -/
theorem archimedeanValue_ne_zero (χ : Grossencharacter K 𝔪) {x : K} (hx : x ≠ 0) :
    χ.archimedeanValue x ≠ 0 := by
  refine mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun τ _ ↦ zpow_ne_zero _ ((map_ne_zero τ).mpr hx))
    (Finset.prod_ne_zero_iff.mpr fun w _ ↦ pow_ne_zero _ ?_)
  have hr : InfinitePlace.embedding_of_isReal w.2 x ≠ 0 := (map_ne_zero _).mpr hx
  rcases lt_or_gt_of_ne hr with h | h
  · simp [sign_neg h]
  · simp [sign_pos h]

/-- At a real place `w`, the infinite component of `χ.toHeckeCharacter` at `x : Kˣ` equals the
algebraic power `w.embedding x ^ n_w` twisted by `sgn(τ_w x) ^ (ε_w - n_w)`. -/
private theorem coe_infiniteComponent_real_eq (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsReal}) (x : Kˣ) :
    (χ.toHeckeCharacter.infiniteComponent w.1
        (Units.map (algebraMap K w.1.Completion).toMonoidHom x) : ℂ) =
      w.1.embedding (x : K) ^ χ.infinityType w.1.embedding *
        (SignType.sign (InfinitePlace.embedding_of_isReal w.2 (x : K)) : ℂ) ^
          (χ.toHeckeCharacter.infinityType.realParity w -
            (χ.infinityType w.1.embedding : ZMod 2)).val := by
  set n := χ.infinityType w.1.embedding
  set ε := χ.toHeckeCharacter.infinityType.realParity w
  have htransport :
      χ.toHeckeCharacter.infiniteComponent w.1
          (Units.map (algebraMap K w.1.Completion).toMonoidHom x) =
        χ.toHeckeCharacter.realComponent w
          (Units.map (InfinitePlace.embedding_of_isReal w.2).toMonoidHom x) := by
    rw [HeckeCharacter.realComponent_apply]
    congr 1
    apply (Units.mapContinuousMulEquiv (continuousMulEquivRealOfIsReal w.2)).injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    apply Units.ext
    exact (continuousMulEquivRealOfIsReal_apply w.2 _).trans
      (by simp [NumberField.InfinitePlace.Completion.algebraMap_apply_eq_coe])
  have hre : χ.toHeckeCharacter.infinityType.realExponent w = (n : ℂ) := by
    have h := (ContinuousInfinityType.agreesOnIdentityComponent_iff _ _).mp
      χ.agreesOnIdentityComponent
    simpa [n] using congrFun h.1 w
  have hsplit : realUnitsCharacter (n : ℂ) ε =
      realUnitsCharacter (n : ℂ) (n : ZMod 2) * realUnitsCharacter 0 (ε - (n : ZMod 2)) := by
    rw [← realUnitsCharacter_add, add_zero, add_sub_cancel]
  rw [htransport, HeckeCharacter.realComponent_eq, hre, hsplit, ContinuousMonoidHom.mul_apply,
    Units.val_mul, coe_realUnitsCharacter_intCast, realUnitsCharacter_zero_left]
  simp only [ContinuousMonoidHom.pow_apply, Units.val_pow_eq_pow_val, coe_realSignCharacter_apply,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    InfinitePlace.embedding_of_isReal_apply]

/-- At a complex place `w`, the infinite component of `χ.toHeckeCharacter` at `x : Kˣ` equals the
product of the two conjugate algebraic powers. -/
private theorem coe_infiniteComponent_complex_eq (χ : Grossencharacter K 𝔪)
    (w : {w : InfinitePlace K // w.IsComplex}) (x : Kˣ) :
    (χ.toHeckeCharacter.infiniteComponent w.1
        (Units.map (algebraMap K w.1.Completion).toMonoidHom x) : ℂ) =
      w.1.embedding (x : K) ^ χ.infinityType w.1.embedding *
        ComplexEmbedding.conjugate w.1.embedding (x : K) ^
          χ.infinityType (ComplexEmbedding.conjugate w.1.embedding) := by
  have htransport :
      χ.toHeckeCharacter.infiniteComponent w.1
          (Units.map (algebraMap K w.1.Completion).toMonoidHom x) =
        χ.toHeckeCharacter.complexComponent w (Units.map w.1.embedding.toMonoidHom x) := by
    rw [HeckeCharacter.complexComponent_apply]
    congr 1
    apply (Units.mapContinuousMulEquiv (continuousMulEquivComplexOfIsComplex w.2)).injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    apply Units.ext
    exact (continuousMulEquivComplexOfIsComplex_apply w.2 _).trans
      (by simp [NumberField.InfinitePlace.Completion.algebraMap_apply_eq_coe])
  obtain ⟨_, hce, hck⟩ := (ContinuousInfinityType.agreesOnIdentityComponent_iff _ _).mp
    χ.agreesOnIdentityComponent
  rw [htransport, HeckeCharacter.complexComponent_eq, congrFun hce w, congrFun hck w]
  simp only [AlgebraicInfinityType.toContinuous_complexExponent,
    AlgebraicInfinityType.toContinuous_complexAngularFrequency]
  simpa [ComplexEmbedding.conjugate_coe_eq] using
    coe_complexUnitsCharacter_intCast (χ.infinityType w.1.embedding)
      (χ.infinityType (ComplexEmbedding.conjugate w.1.embedding))
      (Units.map w.1.embedding.toMonoidHom x)

/-- **The full archimedean value is the product of all infinite components.** For every `x : Kˣ`,
without any sign condition, `χ.archimedeanValue x` equals the product over all infinite places of
the infinite components of `χ.toHeckeCharacter`. -/
theorem archimedeanValue_eq_prod_infiniteComponent (χ : Grossencharacter K 𝔪) (x : Kˣ) :
    χ.archimedeanValue (x : K) =
      ∏ w : InfinitePlace K,
        (χ.toHeckeCharacter.infiniteComponent w
          (Units.map (algebraMap K w.Completion).toMonoidHom x) : ℂ) := by
  classical
  have hsign :
      (∏ w ∈ 𝔪.infinitePart,
        (SignType.sign (InfinitePlace.embedding_of_isReal w.2 (x : K)) : ℂ) ^
          (χ.toHeckeCharacter.infinityType.realParity w -
            (χ.infinityType w.1.embedding : ZMod 2)).val) =
      ∏ w : InfinitePlace K,
        if hw : w.IsReal then
          (SignType.sign (InfinitePlace.embedding_of_isReal hw (x : K)) : ℂ) ^
            (χ.toHeckeCharacter.infinityType.realParity ⟨w, hw⟩ -
              (χ.infinityType w.embedding : ZMod 2)).val
        else 1 := by
    symm
    rw [Finset.prod_dite, Finset.prod_const_one, mul_one]
    refine (Finset.prod_bij_ne_one
      (fun w _ _ ↦ ⟨w.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.2⟩⟩)
      (fun _ _ _ ↦ Finset.mem_univ _)
      (fun _ _ _ _ _ _ h ↦ Subtype.ext (Subtype.mk.inj h))
      (fun w _ hne ↦ ?_) (fun _ _ _ ↦ rfl)).symm
    refine ⟨⟨w.1, (Finset.mem_filter.mp w.2).2⟩, ?_, fun h ↦ hne h, rfl⟩
    by_contra hnot
    apply hne
    rw [χ.realParity_eq ⟨w.1, (Finset.mem_filter.mp w.2).2⟩ hnot,
      AlgebraicInfinityType.toContinuous_realParity, sub_self, ZMod.val_zero, pow_zero]
  rw [archimedeanValue, hsign, ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  by_cases hw : w.IsReal
  · have hfiber : (Finset.univ.filter fun σ : K →+* ℂ ↦ InfinitePlace.mk σ = w) =
        {w.embedding} := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      have h := InfinitePlace.mk_eq_iff (φ := w.embedding) (ψ := σ)
      rw [InfinitePlace.mk_embedding, InfinitePlace.conjugate_embedding_eq_of_isReal hw,
        or_self] at h
      simpa only [eq_comm] using h
    rw [hfiber, Finset.prod_singleton, dite_eq_left hw]
    exact (coe_infiniteComponent_real_eq χ ⟨w, hw⟩ x).symm
  · have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h ↦
      hw (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
    have hfiber : (Finset.univ.filter fun σ : K →+* ℂ ↦ InfinitePlace.mk σ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      have h := InfinitePlace.mk_eq_iff (φ := w.embedding) (ψ := σ)
      rw [InfinitePlace.mk_embedding] at h
      simpa only [eq_comm] using h
    rw [hfiber, Finset.prod_pair hne, dite_eq_right hw, mul_one]
    exact (coe_infiniteComponent_complex_eq χ ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩
      x).symm

/-- On elements congruent to `1` modulo `𝔪`, the full archimedean value reduces to the algebraic
monomial because `x` is positive at every real place of `𝔪.infinitePart`. -/
theorem archimedeanValue_eq_of_isCongrOne (χ : Grossencharacter K 𝔪) {x : Kˣ}
    (hx : IsCongrOne 𝔪 x) :
    χ.archimedeanValue (x : K) = ∏ τ : K →+* ℂ, τ (x : K) ^ χ.infinityType τ := by
  rw [archimedeanValue]
  have h1 :
      (∏ w ∈ 𝔪.infinitePart,
        (SignType.sign (InfinitePlace.embedding_of_isReal w.2 (x : K)) : ℂ) ^
          (χ.toHeckeCharacter.infinityType.realParity w -
            (χ.infinityType w.1.embedding : ZMod 2)).val) = 1 :=
    Finset.prod_eq_one fun w hw ↦ by
      rw [sign_pos ((isCongrOne_iff.mp hx).2 w hw), SignType.coe_one, one_pow]
  rw [h1, mul_one]

/-- Inversion of a presentation inverts its full archimedean value. -/
@[simp]
theorem archimedeanValue_inverse (χ : Grossencharacter K 𝔪) (x : K) :
    χ.inverse.archimedeanValue x = (χ.archimedeanValue x)⁻¹ := by
  have hpar (w : {w : InfinitePlace K // w.IsReal}) :
      χ.inverse.toHeckeCharacter.infinityType.realParity w -
          (χ.inverse.infinityType w.1.embedding : ZMod 2) =
        χ.toHeckeCharacter.infinityType.realParity w -
          (χ.infinityType w.1.embedding : ZMod 2) := by
    simp only [toHeckeCharacter_inverse, infinityType_inverse, HeckeCharacter.infinityType_inv,
      ContinuousInfinityType.neg_realParity, Pi.neg_apply, Int.cast_neg]
    generalize χ.toHeckeCharacter.infinityType.realParity w = a
    generalize (χ.infinityType w.1.embedding : ZMod 2) = b
    revert a b
    decide
  rw [archimedeanValue, archimedeanValue, mul_inv, ← Finset.prod_inv_distrib,
    ← Finset.prod_inv_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ ↦ ?_
    simp [zpow_neg]
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [hpar w, coe_sign_pow_inv]

/-- The full archimedean value depends only on the underlying Hecke character. -/
theorem archimedeanValue_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) (x : K) :
    χ.archimedeanValue x = ψ.archimedeanValue x := by
  classical
  have hn : χ.infinityType = ψ.infinityType :=
    AlgebraicInfinityType.agreesOnIdentityComponent_toContinuous_iff.mp
      (χ.agreesOnIdentityComponent.symm.trans (h ▸ ψ.agreesOnIdentityComponent))
  rw [archimedeanValue, archimedeanValue, hn, h]
  congr 1
  have hχ :
      (∏ w ∈ 𝔪.infinitePart,
        (SignType.sign (InfinitePlace.embedding_of_isReal w.2 x) : ℂ) ^
          (ψ.toHeckeCharacter.infinityType.realParity w -
            (ψ.infinityType w.1.embedding : ZMod 2)).val) =
      ∏ w ∈ 𝔪.infinitePart ∪ 𝔫.infinitePart,
        (SignType.sign (InfinitePlace.embedding_of_isReal w.2 x) : ℂ) ^
          (ψ.toHeckeCharacter.infinityType.realParity w -
            (ψ.infinityType w.1.embedding : ZMod 2)).val := by
    refine Finset.prod_subset Finset.subset_union_left fun w _ hw ↦ ?_
    rw [← h, ← hn, χ.realParity_eq w hw, AlgebraicInfinityType.toContinuous_realParity,
      sub_self, ZMod.val_zero, pow_zero]
  have hψ :
      (∏ w ∈ 𝔫.infinitePart,
        (SignType.sign (InfinitePlace.embedding_of_isReal w.2 x) : ℂ) ^
          (ψ.toHeckeCharacter.infinityType.realParity w -
            (ψ.infinityType w.1.embedding : ZMod 2)).val) =
      ∏ w ∈ 𝔪.infinitePart ∪ 𝔫.infinitePart,
        (SignType.sign (InfinitePlace.embedding_of_isReal w.2 x) : ℂ) ^
          (ψ.toHeckeCharacter.infinityType.realParity w -
            (ψ.infinityType w.1.embedding : ZMod 2)).val := by
    refine Finset.prod_subset Finset.subset_union_right fun w _ hw ↦ ?_
    rw [ψ.realParity_eq w hw, AlgebraicInfinityType.toContinuous_realParity, sub_self,
      ZMod.val_zero, pow_zero]
  exact hχ.trans hψ.symm

/-- For the presentation of a ray class character, the full archimedean value is the product of
the real sign characters over `𝔪.infinitePart`. -/
theorem archimedeanValue_ofRayClassCharacter (η : RayClassCharacter 𝔪) (x : K) :
    (ofRayClassCharacter η).archimedeanValue x =
      ∏ w ∈ 𝔪.infinitePart,
        (SignType.sign (InfinitePlace.embedding_of_isReal w.2 x) : ℂ) ^
          ((HeckeCharacter.ofRayClassCharacter 𝔪 η).infinityType.realParity w).val := by
  simp [archimedeanValue]

/-- The trivial ray class character has identically `1` archimedean value on all of `K`. -/
@[simp]
theorem archimedeanValue_ofRayClassCharacter_one (x : K) :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).archimedeanValue x = 1 := by
  simp [archimedeanValue]

end TauCeti.LFunctions.Grossencharacter

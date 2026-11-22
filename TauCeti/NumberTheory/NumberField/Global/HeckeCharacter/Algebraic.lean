/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.InfinityType
public import TauCeti.NumberTheory.NumberField.Global.InfinityType.IdentityComponent
public import TauCeti.NumberTheory.NumberField.TotallyPositive

/-!
# Algebraic Hecke characters

A Hecke character is **algebraic** (of Weil type `A₀`) when its archimedean parameters agree
with those of integer exponents at the complex embeddings on the identity component.  Thus signs
at real places are deliberately ignored.  In particular every finite-order Hecke character is
algebraic, including characters with nontrivial real signs.

On a global element the product of the infinite components equals the embedding monomial of a
matching algebraic infinity type multiplied by real sign twists where the parities differ
(`coe_prod_infiniteComponent_eq_embeddingCharacter_mul_sign`), and equals that monomial directly
when the element is positive at those real places
(`coe_prod_infiniteComponent_eq_embeddingCharacter_of_realParity`), in particular on totally
positive elements (`coe_prod_infiniteComponent_eq_embeddingCharacter`).

The unitary norm characters `c ↦ ‖c‖ ^ (it)` provide the basic separation from arbitrary
continuous Hecke characters.  When `t ≠ 0`, their archimedean modulus exponents are nonzero and
purely imaginary, so they are neither algebraic nor of finite order.

## Main definitions

* `TauCeti.GlobalNumberFields.HeckeCharacter.IsAlgebraic`: Weil's type `A₀` condition.
* `TauCeti.GlobalNumberFields.HeckeCharacter.normCharacter`: the unitary norm character
  `c ↦ ‖c‖ ^ (it)`.

## Main results

* `TauCeti.GlobalNumberFields.HeckeCharacter.isAlgebraic_of_isFiniteOrder`: finite-order Hecke
  characters are algebraic.
* `HeckeCharacter.coe_prod_infiniteComponent_eq_embeddingCharacter_mul_sign`,
  `HeckeCharacter.coe_prod_infiniteComponent_eq_embeddingCharacter_of_realParity`,
  `HeckeCharacter.coe_prod_infiniteComponent_eq_embeddingCharacter`:
  comparison of the product of infinite components with the embedding monomial of a matching
  algebraic infinity type.
* `TauCeti.GlobalNumberFields.HeckeCharacter.not_isAlgebraic_normCharacter`: a nontrivial unitary
  norm character is not algebraic.
* `TauCeti.GlobalNumberFields.HeckeCharacter.not_isFiniteOrder_normCharacter`: a nontrivial
  unitary norm character does not have finite order.

## References

* A. Weil, *Basic Number Theory*, Chapter VII, §3.
-/

public section
noncomputable section

open NumberField
open scoped NumberField NNReal

namespace TauCeti.GlobalNumberFields

namespace HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

/-! ### Algebraicity -/

/-- A Hecke character is **algebraic** (of Weil type `A₀`) when its infinity type agrees with
the continuous infinity type of integer embedding exponents on the identity component.  Real sign
parities are not constrained. -/
def IsAlgebraic (χ : HeckeCharacter K) : Prop :=
  χ.infinityType.IsAlgebraicOnIdentityComponent

/-- Algebraicity is witnessed by integer embedding exponents whose continuous infinity type
agrees with that of the character on the identity component. -/
theorem isAlgebraic_iff_exists_agreesOnIdentityComponent {χ : HeckeCharacter K} :
    χ.IsAlgebraic ↔
      ∃ n : AlgebraicInfinityType K,
        χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n) :=
  ContinuousInfinityType.isAlgebraicOnIdentityComponent_iff_exists_agreesOnIdentityComponent
    χ.infinityType

/-- Algebraicity is equivalent to an algebraic infinity type together with an unrestricted
finite-order sign twist at the real places. -/
theorem isAlgebraic_iff {χ : HeckeCharacter K} :
    χ.IsAlgebraic ↔
      ∃ (n : AlgebraicInfinityType K) (e : FiniteOrderInfinityType K),
        χ.infinityType =
          AlgebraicInfinityType.toContinuous n + FiniteOrderInfinityType.toContinuous e :=
  ContinuousInfinityType.isAlgebraicOnIdentityComponent_iff χ.infinityType

/-- The trivial Hecke character is algebraic. -/
@[simp]
theorem isAlgebraic_one : (1 : HeckeCharacter K).IsAlgebraic := by
  rw [isAlgebraic_iff]
  exact ⟨0, 0, by simp⟩

/-- A product of algebraic Hecke characters is algebraic. -/
theorem IsAlgebraic.mul {χ ψ : HeckeCharacter K} (hχ : χ.IsAlgebraic)
    (hψ : ψ.IsAlgebraic) : (χ * ψ).IsAlgebraic := by
  rw [isAlgebraic_iff] at hχ hψ ⊢
  obtain ⟨n, e, hn⟩ := hχ
  obtain ⟨m, f, hm⟩ := hψ
  refine ⟨n + m, e + f, ?_⟩
  rw [infinityType_mul, hn, hm, map_add, map_add]
  abel

/-- The inverse of an algebraic Hecke character is algebraic. -/
theorem IsAlgebraic.inv {χ : HeckeCharacter K} (hχ : χ.IsAlgebraic) : χ⁻¹.IsAlgebraic := by
  rw [isAlgebraic_iff] at hχ ⊢
  obtain ⟨n, e, h⟩ := hχ
  refine ⟨-n, -e, ?_⟩
  rw [infinityType_inv, h, map_neg, map_neg]
  abel

/-- Multiplication by an algebraic Hecke character on the right preserves and reflects
algebraicity. -/
theorem IsAlgebraic.mul_iff_left {χ ψ : HeckeCharacter K} (hψ : ψ.IsAlgebraic) :
    (χ * ψ).IsAlgebraic ↔ χ.IsAlgebraic := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mul hψ⟩
  simpa only [mul_inv_cancel_right] using h.mul hψ.inv

/-- Multiplication by an algebraic Hecke character on the left preserves and reflects
algebraicity. -/
theorem IsAlgebraic.mul_iff_right {χ ψ : HeckeCharacter K} (hχ : χ.IsAlgebraic) :
    (χ * ψ).IsAlgebraic ↔ ψ.IsAlgebraic := by
  simpa only [mul_comm χ] using hχ.mul_iff_left (χ := ψ)

/-- Every natural power of an algebraic Hecke character is algebraic. -/
theorem IsAlgebraic.pow {χ : HeckeCharacter K} (hχ : χ.IsAlgebraic) (m : ℕ) :
    (χ ^ m).IsAlgebraic := by
  induction m with
  | zero => simp
  | succ m ih => simpa [pow_succ] using ih.mul hχ

/-- **Every finite-order Hecke character is algebraic.** Its infinity type consists only of real
signs, hence agrees with the zero algebraic infinity type on the identity component. -/
theorem isAlgebraic_of_isFiniteOrder {χ : HeckeCharacter K} (hχ : χ.IsFiniteOrder) :
    χ.IsAlgebraic := by
  obtain ⟨e, he⟩ := exists_finiteOrderInfinityType hχ
  rw [isAlgebraic_iff]
  exact ⟨0, e, by simpa using he⟩

/-- A Hecke character pulled back from a ray class character is algebraic. -/
theorem isAlgebraic_ofRayClassCharacter {m : Modulus K} (e : RayClassCharacter m) :
    (ofRayClassCharacter m e).IsAlgebraic :=
  isAlgebraic_of_isFiniteOrder (isFiniteOrder_ofRayClassCharacter e)

/-! ### Archimedean component comparisons -/

/-- At a real place, the component of `χ` at `x : Kˣ` equals the monomial of an algebraic
infinity type `n` with `χ.infinityType = n + e`, twisted by `sgn(τ_w x) ^ (e w).val`. -/
theorem coe_infiniteComponent_real_of_eq_add (χ : HeckeCharacter K) (n : AlgebraicInfinityType K)
    (e : FiniteOrderInfinityType K)
    (hn : χ.infinityType = AlgebraicInfinityType.toContinuous n +
      FiniteOrderInfinityType.toContinuous e)
    (w : {w : InfinitePlace K // w.IsReal}) (x : Kˣ) :
    (χ.infiniteComponent w.val (Units.map (algebraMap K w.val.Completion).toMonoidHom x) : ℂ) =
      w.val.embedding (x : K) ^ n w.val.embedding *
        (SignType.sign (InfinitePlace.embedding_of_isReal w.property (x : K)) : ℂ) ^
          (e w).val := by
  rw [infiniteComponent_map_algebraMap_eq_realComponent, realComponent_eq, hn]
  simp only [ContinuousInfinityType.add_realExponent, ContinuousInfinityType.add_realParity,
    Pi.add_apply, AlgebraicInfinityType.toContinuous_realExponent,
    AlgebraicInfinityType.toContinuous_realParity,
    FiniteOrderInfinityType.toContinuous_realExponent,
    FiniteOrderInfinityType.toContinuous_realParity, add_zero]
  have hsplit : realUnitsCharacter (n w.val.embedding : ℂ)
        ((n w.val.embedding : ZMod 2) + e w) =
      realUnitsCharacter (n w.val.embedding : ℂ) (n w.val.embedding : ZMod 2) *
        realUnitsCharacter 0 (e w) := by
    rw [← realUnitsCharacter_add, add_zero]
  rw [hsplit, ContinuousMonoidHom.mul_apply, Units.val_mul, coe_realUnitsCharacter_intCast,
    realUnitsCharacter_zero_left]
  simp only [ContinuousMonoidHom.pow_apply, Units.val_pow_eq_pow_val, coe_realSignCharacter_apply,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    InfinitePlace.embedding_of_isReal_apply]

/-- At a complex place, the component of `χ` at `x : Kˣ` equals the product of the two conjugate
embeddings at `w` each raised to the exponent assigned to that embedding by an algebraic infinity
type `n` with `χ.infinityType = n + e`. -/
theorem coe_infiniteComponent_complex (χ : HeckeCharacter K)
    (n : AlgebraicInfinityType K)
    (e : FiniteOrderInfinityType K)
    (hn : χ.infinityType = AlgebraicInfinityType.toContinuous n +
      FiniteOrderInfinityType.toContinuous e)
    (w : {w : InfinitePlace K // w.IsComplex}) (x : Kˣ) :
    (χ.infiniteComponent w.val (Units.map (algebraMap K w.val.Completion).toMonoidHom x) : ℂ) =
      w.val.embedding (x : K) ^ n w.val.embedding *
        ComplexEmbedding.conjugate w.val.embedding (x : K) ^
          n (ComplexEmbedding.conjugate w.val.embedding) := by
  rw [infiniteComponent_map_algebraMap_eq_complexComponent, complexComponent_eq, hn]
  simp only [ContinuousInfinityType.add_complexExponent, Pi.add_apply,
    AlgebraicInfinityType.toContinuous_complexExponent,
    FiniteOrderInfinityType.toContinuous_complexExponent, add_zero,
    ContinuousInfinityType.add_complexAngularFrequency,
    AlgebraicInfinityType.toContinuous_complexAngularFrequency,
    FiniteOrderInfinityType.toContinuous_complexAngularFrequency]
  simpa [ComplexEmbedding.conjugate_coe_eq] using
    coe_complexUnitsCharacter_intCast (n w.val.embedding)
      (n (ComplexEmbedding.conjugate w.val.embedding)) (Units.map w.val.embedding.toMonoidHom x)

open scoped Classical in
/-- Reindex a product over a finset of real places containing the support of `f` to a product over
all infinite places extended by `1` at complex places. -/
private theorem prod_real_dite_eq_of_subset {M : Type*} [CommMonoid M]
    (S : Finset {w : InfinitePlace K // w.IsReal}) (f : {w : InfinitePlace K // w.IsReal} → M)
    (hS : ∀ w : {w : InfinitePlace K // w.IsReal}, f w ≠ 1 → w ∈ S) :
    (∏ w ∈ S, f w) = ∏ w : InfinitePlace K, if hw : w.IsReal then f ⟨w, hw⟩ else 1 := by
  symm
  rw [Finset.prod_dite, Finset.prod_const_one, mul_one]
  refine (Finset.prod_bij_ne_one
    (fun w _ _ ↦ ⟨w.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.property⟩⟩)
    (fun _ _ _ ↦ Finset.mem_univ _)
    (fun _ _ _ _ _ _ h ↦ Subtype.ext (Subtype.mk.inj h))
    (fun w _ hne ↦ ⟨⟨w.val, (Finset.mem_filter.mp w.property).2⟩,
      hS _ hne, fun h ↦ hne h, rfl⟩)
    (fun _ _ _ ↦ rfl)).symm

/-- For every `x : Kˣ`, the product of the infinite components of `χ` equals the embedding
monomial of a matching algebraic infinity type `n` multiplied by the real sign twists
`sgn(τ_w x) ^ (χ.realParity w - n_w)` over any finset `S` of real places containing all real
places where the parities differ. -/
theorem coe_prod_infiniteComponent_eq_embeddingCharacter_mul_sign (χ : HeckeCharacter K)
    (n : AlgebraicInfinityType K)
    (hn : χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n))
    (S : Finset {w : InfinitePlace K // w.IsReal})
    (hS : ∀ w : {w : InfinitePlace K // w.IsReal},
      χ.infinityType.realParity w ≠ (AlgebraicInfinityType.toContinuous n).realParity w → w ∈ S)
    (x : Kˣ) :
    ((∏ w : InfinitePlace K,
      χ.infiniteComponent w (Units.map (algebraMap K w.Completion).toMonoidHom x)) : ℂ) =
      (n.embeddingCharacter x : ℂ) *
        ∏ w ∈ S,
          (SignType.sign (InfinitePlace.embedding_of_isReal w.property (x : K)) : ℂ) ^
            (χ.infinityType.realParity w -
              (AlgebraicInfinityType.toContinuous n).realParity w).val := by
  classical
  obtain ⟨e, he⟩ :=
    (ContinuousInfinityType.agreesOnIdentityComponent_iff_exists_finiteOrderInfinityType
      χ.infinityType (AlgebraicInfinityType.toContinuous n)).mp hn
  have he_eq (w : {w : InfinitePlace K // w.IsReal}) :
      χ.infinityType.realParity w - (AlgebraicInfinityType.toContinuous n).realParity w = e w := by
    simp [he]
  have hsign :
      (∏ w ∈ S,
        (SignType.sign (InfinitePlace.embedding_of_isReal w.property (x : K)) : ℂ) ^
          (χ.infinityType.realParity w -
            (AlgebraicInfinityType.toContinuous n).realParity w).val) =
      ∏ w : InfinitePlace K,
        if hw : w.IsReal then
          (SignType.sign (InfinitePlace.embedding_of_isReal hw (x : K)) : ℂ) ^
            (e ⟨w, hw⟩).val
        else 1 := by
    simp_rw [he_eq]
    refine prod_real_dite_eq_of_subset (M := ℂ) S _ fun w hne ↦ hS w fun hpar ↦ hne ?_
    have he0 : e w = 0 := by rw [← he_eq, hpar, sub_self]
    simp [he0]
  rw [AlgebraicInfinityType.coe_embeddingCharacter_apply, hsign,
    ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  by_cases hw : w.IsReal
  · rw [InfinitePlace.filter_mk_eq_of_isReal hw, Finset.prod_singleton, dite_eq_left hw]
    exact coe_infiniteComponent_real_of_eq_add χ n e he ⟨w, hw⟩ x
  · have hcx : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    rw [InfinitePlace.filter_mk_eq,
      Finset.prod_pair (InfinitePlace.embedding_ne_conjugate_of_isComplex hcx),
      dite_eq_right hw, mul_one]
    exact coe_infiniteComponent_complex χ n e he ⟨w, hcx⟩ x

/-- The product of the infinite components of `χ` at `x` is exactly the monomial of an algebraic
infinity type `n` matching the character on the identity component, provided `x` is positive at
every real place where the sign parity of `χ` differs from the parity of `n`. -/
theorem coe_prod_infiniteComponent_eq_embeddingCharacter_of_realParity (χ : HeckeCharacter K)
    (n : AlgebraicInfinityType K)
    (hn : χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n))
    (x : Kˣ) (hx : ∀ w : {w : InfinitePlace K // w.IsReal},
      χ.infinityType.realParity w ≠ (AlgebraicInfinityType.toContinuous n).realParity w →
        0 < InfinitePlace.embedding_of_isReal w.property (x : K)) :
    ((∏ w : InfinitePlace K,
      χ.infiniteComponent w (Units.map (algebraMap K w.Completion).toMonoidHom x)) : ℂ) =
      (n.embeddingCharacter x : ℂ) := by
  classical
  rw [coe_prod_infiniteComponent_eq_embeddingCharacter_mul_sign χ n hn
    Finset.univ (fun w _ ↦ Finset.mem_univ w) x]
  have h1 :
      (∏ w : {w : InfinitePlace K // w.IsReal},
        (SignType.sign (InfinitePlace.embedding_of_isReal w.property (x : K)) : ℂ) ^
          (χ.infinityType.realParity w -
            (AlgebraicInfinityType.toContinuous n).realParity w).val) = 1 :=
    Finset.prod_eq_one fun w _ ↦ by
      by_cases hpar :
          χ.infinityType.realParity w = (AlgebraicInfinityType.toContinuous n).realParity w
      · simp [hpar]
      · simp [sign_pos (hx w hpar)]
  rw [h1, mul_one]

/-- On totally positive global elements, the product of the infinite components is exactly the
monomial of any algebraic infinity type matching the character on the identity component. -/
theorem coe_prod_infiniteComponent_eq_embeddingCharacter (χ : HeckeCharacter K)
    (n : AlgebraicInfinityType K)
    (hn : χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n))
    (x : Kˣ) (hx : IsTotallyPositive (x : K)) :
    ((∏ w : InfinitePlace K,
      χ.infiniteComponent w (Units.map (algebraMap K w.Completion).toMonoidHom x)) : ℂ) =
      (n.embeddingCharacter x : ℂ) :=
  χ.coe_prod_infiniteComponent_eq_embeddingCharacter_of_realParity n hn x fun w _ ↦
    (isTotallyPositive_iff.mp hx) w.val w.property

/-! ### A nonalgebraic unitary family -/

/-- The **unitary norm character** `c ↦ ‖c‖ ^ (it)` for `t : ℝ`. -/
def normCharacter (K : Type*) [Field K] [NumberField K] (t : ℝ) : HeckeCharacter K :=
  normPow K (Complex.I * t)

/-- The unitary norm character is the norm-power character with exponent `it`. -/
theorem normCharacter_def (t : ℝ) : normCharacter K t = normPow K (Complex.I * t) :=
  (rfl)

/-- The value of the unitary norm character at an idele class is `‖c‖ ^ (it)`. -/
@[simp]
theorem normCharacter_apply (t : ℝ)
    (c : IdeleClassGroup (NumberField.RingOfIntegers K) K) :
    ((normCharacter K t c : ℂˣ) : ℂ) =
      (((ideleClassNorm c : ℝ≥0) : ℝ) : ℂ) ^ (Complex.I * t) := by
  rw [normCharacter_def, normPow_apply]

/-- The unitary norm character with parameter zero is trivial. -/
@[simp]
theorem normCharacter_zero : normCharacter K 0 = 1 := by
  rw [normCharacter_def]
  simp

/-- Adding parameters multiplies the corresponding unitary norm characters. -/
theorem normCharacter_add (s t : ℝ) :
    normCharacter K (s + t) = normCharacter K s * normCharacter K t := by
  rw [normCharacter_def, normCharacter_def, normCharacter_def]
  push_cast
  rw [mul_add, normPow_add]

/-- Negating the parameter inverts the unitary norm character. -/
theorem normCharacter_neg (t : ℝ) : normCharacter K (-t) = (normCharacter K t)⁻¹ := by
  rw [normCharacter_def, normCharacter_def]
  push_cast
  rw [mul_neg, normPow_neg]

/-- The infinity type of `c ↦ ‖c‖ ^ (it)` has exponent `it` at real places and `2it` at
complex places, with no sign parity or angular frequency. -/
theorem infinityType_normCharacter (t : ℝ) :
    (normCharacter K t).infinityType =
      { realExponent := fun _ ↦ Complex.I * t
        realParity := 0
        complexExponent := fun _ ↦ 2 * (Complex.I * t)
        complexAngularFrequency := 0 } := by
  rw [normCharacter_def, infinityType_normPow]

/-- The unitary norm character has shift zero. -/
@[simp]
theorem shift_normCharacter (t : ℝ) : (normCharacter K t).shift = 0 := by
  simp [normCharacter_def]

/-- **A nontrivial unitary norm character is not algebraic.** Its nonzero purely imaginary
archimedean exponent cannot be the sum of integer embedding exponents. -/
theorem not_isAlgebraic_normCharacter {t : ℝ} (ht : t ≠ 0) :
    ¬ (normCharacter K t).IsAlgebraic := by
  rw [isAlgebraic_iff]
  rintro ⟨n, e, hn⟩
  rw [infinityType_normCharacter] at hn
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  rcases w.isReal_or_isComplex with hw | hw
  · have h := congrArg (fun u : ContinuousInfinityType K ↦ u.realExponent ⟨w, hw⟩) hn
    have him := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add, ContinuousInfinityType.add_realExponent,
      Pi.add_apply, AlgebraicInfinityType.toContinuous_realExponent,
      FiniteOrderInfinityType.toContinuous_realExponent, add_zero, Complex.intCast_im] at him
    exact ht him
  · have h := congrArg (fun u : ContinuousInfinityType K ↦ u.complexExponent ⟨w, hw⟩) hn
    have him := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.re_ofNat, Complex.I_re, Complex.ofReal_im, mul_zero,
      Complex.I_im, Complex.ofReal_re, one_mul, zero_add, Complex.im_ofNat, Complex.mul_re,
      zero_mul, sub_self, ContinuousInfinityType.add_complexExponent, Pi.add_apply,
      AlgebraicInfinityType.toContinuous_complexExponent,
      FiniteOrderInfinityType.toContinuous_complexExponent, Complex.add_im, Complex.intCast_im,
      Complex.zero_im] at him
    exact ht (by linarith)

/-- **A nontrivial unitary norm character does not have finite order.** -/
theorem not_isFiniteOrder_normCharacter {t : ℝ} (ht : t ≠ 0) :
    ¬ (normCharacter K t).IsFiniteOrder := by
  rw [normCharacter_def, isFiniteOrder_normPow_iff]
  simp [ht]

end HeckeCharacter

end TauCeti.GlobalNumberFields

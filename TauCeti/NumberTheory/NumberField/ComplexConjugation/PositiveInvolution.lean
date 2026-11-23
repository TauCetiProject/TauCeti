/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.Trace.Basic
import TauCeti.NumberTheory.NumberField.SignApproximation

/-!
# Positive involutions of number fields

Let `K` be a number field and `σ : K →+* K` a ring endomorphism such that the trace form
`x ↦ Tr_{K/ℚ}(x σ(x))` is positive definite: `0 < Tr_{K/ℚ}(x σ(x))` for every `x ≠ 0`. Then every
complex embedding `φ` of `K` satisfies `φ ∘ σ = conj ∘ φ`
(`TauCeti.NumberField.comp_eq_conjugate_of_trace_mul_pos`). Consequently either `σ` is the
identity and `K` is totally real, or `σ` is not the identity, `K` is a CM field and `σ` is its
complex conjugation (`TauCeti.NumberField.isTotallyReal_and_eq_id_or_isCMField_of_trace_mul_pos`);
in both cases the fixed field of `σ` is totally real. This is the field case of the classification
of positive involutions: on the centre of a simple algebra with positive involution, the
involution is the identity of a totally real field or the conjugation of a CM field.

The proof uses weak approximation at the infinite places
(`NumberField.exists_forall_infinitePlace_sub_lt`). Write
`Tr(x σ(x)) = ∑_ψ ψ(x) ψ(σ x)` over the complex embeddings `ψ`. Approximating a family of
targets `a_v`, one for each infinite place `v`, gives a sequence along which the traces converge
to `∑_ψ ψ(a_{|ψ|}) (ψ ∘ σ)(a_{|ψ ∘ σ|})`, whose real part is therefore nonnegative. If
`φ ∘ σ` and `φ` define different places, the targets `1` at `|φ|` and `-1` at `|φ ∘ σ|` make that
real part at most `-1`. If they define the same place but `φ ∘ σ ≠ conj ∘ φ`, then `σ = id` and `φ`
is not real, and a target `β` with `Re (φ β)² < 0` at `|φ|` makes it negative.

## Main results

* `TauCeti.NumberField.comp_eq_conjugate_of_trace_mul_pos`: `φ ∘ σ = conj ∘ φ` for every complex
  embedding `φ`.
* `TauCeti.NumberField.isTotallyReal_eqLocusField_of_trace_mul_pos`: the fixed field of `σ` is
  totally real.
* `TauCeti.NumberField.isTotallyReal_of_trace_mul_self_pos`: if `Tr(x²) > 0` for `x ≠ 0`, then
  `K` is totally real.
* `TauCeti.NumberField.isCMField_of_trace_mul_pos` and
  `TauCeti.NumberField.eq_complexConj_of_trace_mul_pos`: if `σ ≠ id`, then `K` is CM and `σ` is
  its complex conjugation.
* `TauCeti.NumberField.isTotallyReal_and_eq_id_or_isCMField_of_trace_mul_pos`: the dichotomy.

## References

* J. S. Milne, *Introduction to Shimura varieties*, Proposition 8.10 and Definition 8.11.
* D. Mumford, *Abelian varieties*, §21.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding Filter Topology

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {σ : K →+* K}

/-- The trace of a number field over `ℚ` is the sum of its complex embeddings. -/
private theorem algebraMap_trace_eq_sum (x : K) :
    algebraMap ℚ ℂ (Algebra.trace ℚ K x) = ∑ φ : K →+* ℂ, φ x := by
  rw [trace_eq_sum_embeddings (E := ℂ)]
  exact (Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _ fun _ => rfl).symm

/-- A ring endomorphism of a number field is surjective. -/
private theorem surjective_of_ringHom (σ : K →+* K) : Function.Surjective σ :=
  (Algebra.IsAlgebraic.algHom_bijective σ.toRatAlgHom).2

/-- Composition with a ring endomorphism is injective on infinite places. -/
private theorem mk_eq_mk_of_mk_comp_eq_mk_comp {φ ψ : K →+* ℂ}
    (h : mk (ψ.comp σ) = mk (φ.comp σ)) : mk ψ = mk φ := by
  have hσ := surjective_of_ringHom σ
  rw [mk_eq_iff] at h ⊢
  refine h.imp (fun h => ?_) fun h => ?_
  · exact (RingHom.cancel_right hσ).1 h
  · exact (RingHom.cancel_right hσ).1 h

/-- **The approximation step.** If the trace form `x ↦ Tr(x σ(x))` is nonnegative, then for every
family of targets `a_v`, one for each infinite place, the real part of
`∑_ψ ψ(a_{|ψ|}) (ψ ∘ σ)(a_{|ψ ∘ σ|})` is nonnegative. -/
private theorem re_sum_nonneg (hσ : ∀ x : K, 0 ≤ Algebra.trace ℚ K (x * σ x))
    (a : InfinitePlace K → K) :
    0 ≤ (∑ ψ : K →+* ℂ, ψ (a (mk ψ)) * (ψ.comp σ) (a (mk (ψ.comp σ)))).re := by
  choose x hx using fun n : ℕ => exists_forall_infinitePlace_sub_lt a
    (fun _ => 1 / ((n : ℝ) + 1)) fun _ => Nat.one_div_pos_of_nat
  have hlim (ψ : K →+* ℂ) : Tendsto (fun n => ψ (x n)) atTop (𝓝 (ψ (a (mk ψ)))) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
      (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat)
    rw [← map_sub, ← InfinitePlace.apply]
    exact (hx n (mk ψ)).le
  have hsum : Tendsto (fun n => ∑ ψ : K →+* ℂ, ψ (x n) * (ψ.comp σ) (x n)) atTop
      (𝓝 (∑ ψ : K →+* ℂ, ψ (a (mk ψ)) * (ψ.comp σ) (a (mk (ψ.comp σ))))) :=
    tendsto_finsetSum _ fun ψ _ => (hlim ψ).mul (hlim (ψ.comp σ))
  refine ge_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp hsum) fun n => ?_
  simp only [Function.comp_apply, RingHom.coe_comp, ← map_mul, ← algebraMap_trace_eq_sum]
  simpa using hσ (x n)

/-- A real part of a sum is negative if every term has nonpositive real part and one term has
negative real part. -/
private theorem re_sum_neg {f : (K →+* ℂ) → ℂ} (φ : K →+* ℂ) (hle : ∀ ψ, (f ψ).re ≤ 0)
    (hlt : (f φ).re < 0) : (∑ ψ, f ψ).re < 0 := by
  classical
  rw [Complex.re_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ φ)]
  exact add_neg_of_neg_of_nonpos hlt (Finset.sum_nonpos fun ψ _ => hle ψ)

/-- A complex embedding that is not real takes a value with negative real square at some
element. -/
private theorem exists_re_sq_neg {φ : K →+* ℂ} (hφ : ¬ ComplexEmbedding.IsReal φ) :
    ∃ β : K, (φ β ^ 2).re < 0 := by
  obtain ⟨γ, hγ⟩ : ∃ γ, conjugate φ γ ≠ φ γ := by
    by_contra! h
    exact hφ (ComplexEmbedding.isReal_iff.2 (RingHom.ext h))
  have him : 0 < |(φ γ).im| := by
    refine abs_pos.2 fun h => hγ ?_
    rw [conjugate_coe_eq, Complex.conj_eq_iff_im]
    exact h
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show (φ γ).re - |(φ γ).im| < (φ γ).re + |(φ γ).im| by
    linarith)
  refine ⟨γ - q, ?_⟩
  have hlt : |(φ γ).re - q| < |(φ γ).im| := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have := sq_lt_sq.2 hlt
  simp only [map_sub, map_ratCast, sq, Complex.mul_re, Complex.sub_re, Complex.ratCast_re,
    Complex.sub_im, Complex.ratCast_im, sub_zero]
  nlinarith [sq_abs ((φ γ).re - q), sq_abs (φ γ).im]

/-- The case of `TauCeti.NumberField.comp_eq_conjugate_of_trace_mul_pos` where `φ` and `φ ∘ σ`
define the same place: then `σ = id`, `φ` is not real, and a target `β` with `Re (φ β)² < 0` at
`|φ|` makes the approximated trace negative. -/
private theorem false_of_mk_comp_eq (hσ : ∀ x : K, 0 ≤ Algebra.trace ℚ K (x * σ x))
    {φ : K →+* ℂ} (hne : φ.comp σ ≠ conjugate φ) (hw : mk (φ.comp σ) = mk φ) : False := by
  classical
  have hφσ : φ.comp σ = φ := by
    rcases mk_eq_iff.1 hw with h | h
    · exact h
    · have h' := congrArg conjugate h
      rw [involutive_conjugate] at h'
      exact absurd h' hne
  have hid : σ = RingHom.id K := RingHom.ext fun x => φ.injective (RingHom.congr_fun hφσ x)
  subst hid
  have hφ : ¬ ComplexEmbedding.IsReal φ := fun h =>
    hne (by rw [RingHom.comp_id, ComplexEmbedding.isReal_iff.1 h])
  obtain ⟨β, hβ⟩ := exists_re_sq_neg hφ
  refine (re_sum_nonneg hσ fun v => if v = mk φ then β else 0).not_gt
    (re_sum_neg φ (fun ψ => ?_) ?_)
  · simp only [RingHom.comp_id]
    split_ifs with h
    · rcases mk_eq_iff.1 h.symm with rfl | rfl
      · rw [← sq]; exact hβ.le
      · rw [← sq, conjugate_coe_eq, ← map_pow, Complex.conj_re]; exact hβ.le
    · simp
  · simpa [← sq] using hβ

/-- The case of `TauCeti.NumberField.comp_eq_conjugate_of_trace_mul_pos` where `φ` and `φ ∘ σ`
define different places: the targets `1` at `|φ|` and `-1` at `|φ ∘ σ|` make the approximated
trace at most `-1`. -/
private theorem false_of_mk_comp_ne (hσ : ∀ x : K, 0 ≤ Algebra.trace ℚ K (x * σ x))
    {φ : K →+* ℂ} (hw : mk (φ.comp σ) ≠ mk φ) : False := by
  classical
  let a : InfinitePlace K → K := fun v => if v = mk φ then 1 else if v = mk (φ.comp σ) then -1
    else 0
  have ha (ψ : K →+* ℂ) : ψ (a (mk ψ)) =
      if mk ψ = mk φ then 1 else if mk ψ = mk (φ.comp σ) then -1 else 0 := by
    simp only [a]
    split_ifs <;> simp
  have hcomp {ψ : K →+* ℂ} (h : mk ψ = mk φ) : mk (ψ.comp σ) = mk (φ.comp σ) := by
    rcases mk_eq_iff.1 h with h | h
    · rw [h]
    · rw [← h]
      exact (mk_conjugate_eq (ψ.comp σ)).symm
  refine (re_sum_nonneg hσ a).not_gt (re_sum_neg φ (fun ψ => ?_) ?_)
  · rw [ha, ha (ψ.comp σ)]
    by_cases h₁ : mk ψ = mk φ
    · simp [h₁, hcomp h₁, hw]
    by_cases h₂ : mk ψ = mk (φ.comp σ)
    · have h₃ : mk (ψ.comp σ) ≠ mk (φ.comp σ) := fun h => h₁ (mk_eq_mk_of_mk_comp_eq_mk_comp h)
      split_ifs <;> simp_all
    · simp [h₁, h₂]
  · rw [ha, ha (φ.comp σ)]
    simp [hw]

/-- **A positive involution is complex conjugation in every embedding.** If
`0 < Tr_{K/ℚ}(x σ(x))` for every nonzero `x` of a number field `K`, then `φ ∘ σ = conj ∘ φ` for
every complex embedding `φ` of `K`. -/
theorem comp_eq_conjugate_of_trace_mul_pos
    (hσ : ∀ x : K, x ≠ 0 → 0 < Algebra.trace ℚ K (x * σ x)) (φ : K →+* ℂ) :
    φ.comp σ = conjugate φ := by
  have hnonneg (x : K) : 0 ≤ Algebra.trace ℚ K (x * σ x) := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (hσ x hx).le
  by_contra hne
  by_cases hw : mk (φ.comp σ) = mk φ
  · exact false_of_mk_comp_eq hnonneg hne hw
  · exact false_of_mk_comp_ne hnonneg hw

/-- The pointwise form of `TauCeti.NumberField.comp_eq_conjugate_of_trace_mul_pos`. -/
private theorem apply_eq_conj_of_trace_mul_pos
    (hσ : ∀ x : K, x ≠ 0 → 0 < Algebra.trace ℚ K (x * σ x)) (φ : K →+* ℂ) (x : K) :
    φ (σ x) = (starRingEnd ℂ) (φ x) :=
  RingHom.congr_fun (comp_eq_conjugate_of_trace_mul_pos hσ φ) x

/-- **The fixed field of a positive involution is totally real.** -/
theorem isTotallyReal_eqLocusField_of_trace_mul_pos
    (hσ : ∀ x : K, x ≠ 0 → 0 < Algebra.trace ℚ K (x * σ x)) :
    IsTotallyReal (σ.eqLocusField (RingHom.id K)) := by
  refine isTotallyReal_iff_le_maximalRealSubfield.2 fun x hx φ => ?_
  have hx' : σ x = x := hx
  rw [RCLike.star_def, ← apply_eq_conj_of_trace_mul_pos hσ, hx']

/-- **A positive definite trace form is totally real.** If `0 < Tr_{K/ℚ}(x²)` for every nonzero
`x` of a number field `K`, then `K` is totally real. -/
theorem isTotallyReal_of_trace_mul_self_pos
    (h : ∀ x : K, x ≠ 0 → 0 < Algebra.trace ℚ K (x * x)) : IsTotallyReal K where
  isReal w := by
    rw [← mk_embedding w, isReal_mk_iff, ComplexEmbedding.isReal_iff]
    exact ((comp_eq_conjugate_of_trace_mul_pos (σ := RingHom.id K) h _).symm.trans
      (RingHom.comp_id _))

/-- A positive involution is an involution: `σ (σ x) = x`. -/
private theorem apply_apply_of_trace_mul_pos
    (hσ : ∀ x : K, x ≠ 0 → 0 < Algebra.trace ℚ K (x * σ x)) (x : K) : σ (σ x) = x := by
  let φ : K →+* ℂ := Classical.arbitrary _
  refine φ.injective ?_
  rw [apply_eq_conj_of_trace_mul_pos hσ, apply_eq_conj_of_trace_mul_pos hσ, Complex.conj_conj]

/-- **A positive involution other than the identity makes `K` a CM field.** -/
theorem isCMField_of_trace_mul_pos (hσ : ∀ x : K, x ≠ 0 → 0 < Algebra.trace ℚ K (x * σ x))
    (hne : σ ≠ RingHom.id K) : IsCMField K := by
  have hconj := comp_eq_conjugate_of_trace_mul_pos hσ
  have : IsTotallyComplex K := ⟨fun w => by
    rw [← mk_embedding w, isComplex_mk_iff, ComplexEmbedding.isReal_iff]
    intro h
    refine hne (RingHom.ext fun x => (embedding w).injective ?_)
    rw [← RingHom.comp_apply, hconj, h, RingHom.id_apply]⟩
  have hinv := apply_apply_of_trace_mul_pos hσ
  let τ : K ≃ₐ[ℚ] K :=
    (RingEquiv.ofBijective σ ⟨σ.injective, surjective_of_ringHom σ⟩).toRatAlgEquiv
  have hτx (x : K) : τ x = σ x := rfl
  have hτ : τ ≠ 1 := fun h => hne (RingHom.ext fun x => by
    simpa [hτx] using AlgEquiv.congr_fun h x)
  have hτ2 : orderOf τ = 2 :=
    orderOf_eq_prime (AlgEquiv.ext fun x => by rw [sq, AlgEquiv.mul_apply, hτx, hτx, hinv]; rfl) hτ
  have hcard : Nat.card (Subgroup.zpowers τ) = 2 := by rw [Nat.card_zpowers, hτ2]
  have : Finite (Subgroup.zpowers τ) := Nat.finite_of_card_ne_zero (by omega)
  let F := FixedPoints.subfield (Subgroup.zpowers τ) K
  have : IsTotallyReal F := isTotallyReal_iff_le_maximalRealSubfield.2 fun x hx φ => by
    have hx' : σ x = x := by simpa [hτx] using hx ⟨τ, Subgroup.mem_zpowers τ⟩
    rw [RCLike.star_def, ← apply_eq_conj_of_trace_mul_pos hσ, hx']
  have : Algebra.IsQuadraticExtension F K :=
    ⟨by rw [← IsGaloisGroup.card_eq_finrank (Subgroup.zpowers τ) F K, hcard]⟩
  exact IsCMField.ofCMExtension F K

/-- **A positive involution other than the identity is complex conjugation.** On a CM field, a
positive involution `σ ≠ id` is `IsCMField.complexConj`. -/
theorem eq_complexConj_of_trace_mul_pos [IsCMField K]
    (hσ : ∀ x : K, x ≠ 0 → 0 < Algebra.trace ℚ K (x * σ x)) (x : K) :
    σ x = IsCMField.complexConj K x := by
  let φ : K →+* ℂ := Classical.arbitrary _
  refine φ.injective ?_
  rw [apply_eq_conj_of_trace_mul_pos hσ, IsCMField.complexEmbedding_complexConj]

/-- **Classification of positive involutions of a number field.** If `0 < Tr_{K/ℚ}(x σ(x))` for
every nonzero `x`, then either `K` is totally real and `σ` is the identity, or `K` is a CM field
and `σ` is its complex conjugation. -/
theorem isTotallyReal_and_eq_id_or_isCMField_of_trace_mul_pos
    (hσ : ∀ x : K, x ≠ 0 → 0 < Algebra.trace ℚ K (x * σ x)) :
    (IsTotallyReal K ∧ σ = RingHom.id K) ∨
      ∃ _ : IsCMField K, ∀ x, σ x = IsCMField.complexConj K x := by
  by_cases hne : σ = RingHom.id K
  · subst hne
    exact .inl ⟨isTotallyReal_of_trace_mul_self_pos hσ, rfl⟩
  · have := isCMField_of_trace_mul_pos hσ hne
    exact .inr ⟨this, eq_complexConj_of_trace_mul_pos hσ⟩

end TauCeti.NumberField

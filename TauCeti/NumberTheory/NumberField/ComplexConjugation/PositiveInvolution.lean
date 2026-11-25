/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import TauCeti.NumberTheory.NumberField.ComplexEmbedding.IsReal
import TauCeti.NumberTheory.NumberField.InfinitePlace.Trace
import TauCeti.NumberTheory.NumberField.InfinitePlace.Transport
import TauCeti.NumberTheory.NumberField.SignApproximation

/-!
# Positive involutions of number fields

Let `K` be a number field and `σ : K →+* K` a ring endomorphism such that the trace form
`x ↦ Tr_{K/ℚ}(x σ(x))` is positive semidefinite: `0 ≤ Tr_{K/ℚ}(x σ(x))` for every `x`. This holds in
particular for a positive involution, where `0 < Tr_{K/ℚ}(x σ(x))` for every `x ≠ 0`. Then every
complex embedding `φ` of `K` satisfies `φ ∘ σ = conj ∘ φ`
(`TauCeti.NumberField.comp_eq_conjugate_of_trace_mul_nonneg`). Consequently either `σ` is the
identity and `K` is totally real, or `σ` is not the identity, `K` is a CM field and `σ` is its
complex conjugation; in both cases the fixed field of `σ` is totally real. This is the field case
of the classification of positive involutions: on the centre of a simple algebra with positive
involution, the involution is the identity of a totally real field or the conjugation of a CM
field.

The proof uses weak approximation at the infinite places
(`NumberField.exists_forall_infinitePlace_sub_lt`). Write
`Tr(x σ(x)) = ∑_ψ ψ(x) ψ(σ x)` over the complex embeddings `ψ`. Approximating a family of
targets `a_v`, one for each infinite place `v`, gives a sequence along which the traces converge
to `∑_ψ ψ(a_{|ψ|}) (ψ ∘ σ)(a_{|ψ ∘ σ|})`, whose real part is therefore nonnegative. If
`φ ∘ σ` and `φ` define different places, the targets `1` at `|φ|` and `-1` at `|φ ∘ σ|` make that
real part at most `-1`. If they define the same place but `φ ∘ σ ≠ conj ∘ φ`, then `σ = id` and `φ`
is not real, and a target `β` with `Re ((φ β)²) < 0` at `|φ|` makes it negative.

## Main results

* `TauCeti.NumberField.comp_eq_conjugate_of_trace_mul_nonneg`: `φ ∘ σ = conj ∘ φ` for every
  complex embedding `φ`, with pointwise form
  `TauCeti.NumberField.apply_eq_conj_of_trace_mul_nonneg`: `φ (σ x) = conj (φ x)`.
* `TauCeti.NumberField.apply_apply_of_trace_mul_nonneg`: `σ` is an involution.
* `TauCeti.NumberField.isTotallyReal_eqLocusField_of_trace_mul_nonneg`: the fixed field of `σ` is
  totally real.
* `TauCeti.NumberField.isTotallyReal_of_trace_mul_self_nonneg`: if `Tr(x²) ≥ 0` for every `x`, then
  `K` is totally real.
* `TauCeti.NumberField.isCMField_of_trace_mul_nonneg`: if `σ ≠ id`, then `K` is a CM field.
* `TauCeti.NumberField.apply_eq_complexConj_apply_of_trace_mul_nonneg`: on a field with an
  `IsCMField` instance, `σ x = IsCMField.complexConj K x` for every `x`.
* `isTotallyReal_and_eq_id_or_isCMField_and_eq_complexConj_of_trace_mul_nonneg` (in
  `TauCeti.NumberField`): the dichotomy.

## References

* J. S. Milne, *Introduction to Shimura varieties*, Proposition 8.10 and Definition 8.11.
* D. Mumford, *Abelian varieties*, §21.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding Filter Topology

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {σ : K →+* K}

/-- A ring endomorphism `σ` of a number field as a `ℚ`-algebra automorphism: it is bijective since
`K` is algebraic over `ℚ`. -/
private noncomputable def algEquivOfRingHom (σ : K →+* K) : K ≃ₐ[ℚ] K :=
  AlgEquiv.ofBijective σ.toRatAlgHom (Algebra.IsAlgebraic.algHom_bijective _)

@[simp]
private theorem algEquivOfRingHom_apply (σ : K →+* K) (x : K) : algEquivOfRingHom σ x = σ x := by
  rw [algEquivOfRingHom, AlgEquiv.ofBijective_apply, RingHom.toRatAlgHom_apply]

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
  simp only [Function.comp_apply, RingHom.coe_comp, ← map_mul,
    ← algebraMap_trace_eq_sum_ringHom]
  simpa using hσ (x n)

/-- The case of `TauCeti.NumberField.comp_eq_conjugate_of_trace_mul_nonneg` where `φ` and `φ ∘ σ`
define the same place: then `σ = id`, `φ` is not real, and a target `β` with `Re ((φ β)²) < 0` at
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
  obtain ⟨β, hβ⟩ := exists_re_sq_neg_of_not_isReal hφ
  refine (re_sum_nonneg hσ fun v => if v = mk φ then β else 0).not_gt ?_
  rw [Complex.re_sum]
  refine Finset.sum_neg' (fun ψ _ => ?_) ⟨φ, Finset.mem_univ φ, by simpa [← sq] using hβ⟩
  simp only [RingHom.comp_id]
  split_ifs with h
  · rcases mk_eq_iff.1 h.symm with rfl | rfl
    · rw [← sq]; exact hβ.le
    · rw [← sq, conjugate_coe_eq, ← map_pow, Complex.conj_re]; exact hβ.le
  · simp

/-- The case of `TauCeti.NumberField.comp_eq_conjugate_of_trace_mul_nonneg` where `φ` and `φ ∘ σ`
define different places: the targets `1` at `|φ|` and `-1` at `|φ ∘ σ|` make the approximated
trace at most `-1`. -/
private theorem false_of_mk_comp_ne (hσ : ∀ x : K, 0 ≤ Algebra.trace ℚ K (x * σ x))
    {φ : K →+* ℂ} (hw : mk (φ.comp σ) ≠ mk φ) : False := by
  classical
  let e : K ≃+* K := (algEquivOfRingHom σ).toRingEquiv
  have he (w : InfinitePlace K) : equivOfRingEquiv e.symm w = w.comap σ := by
    rw [equivOfRingEquiv_eq_comap, RingEquiv.symm_symm]
    exact congrArg w.comap (RingHom.ext fun x => algEquivOfRingHom_apply σ x)
  let a : InfinitePlace K → K := fun v => if v = mk φ then 1 else if v = mk (φ.comp σ) then -1
    else 0
  have ha (ψ : K →+* ℂ) : ψ (a (mk ψ)) =
      if mk ψ = mk φ then 1 else if mk ψ = mk (φ.comp σ) then -1 else 0 := by
    simp only [a]
    split_ifs <;> simp
  have hcomp {ψ : K →+* ℂ} (h : mk ψ = mk φ) : mk (ψ.comp σ) = mk (φ.comp σ) := by
    rw [← comap_mk, ← comap_mk, h]
  refine (re_sum_nonneg hσ a).not_gt ?_
  rw [Complex.re_sum]
  refine Finset.sum_neg' (fun ψ _ => ?_) ⟨φ, Finset.mem_univ φ, ?_⟩
  · rw [ha, ha (ψ.comp σ)]
    by_cases h₁ : mk ψ = mk φ
    · simp [h₁, hcomp h₁, hw]
    by_cases h₂ : mk ψ = mk (φ.comp σ)
    · have h₃ : mk (ψ.comp σ) ≠ mk (φ.comp σ) := fun h =>
        h₁ ((equivOfRingEquiv e.symm).injective (by rwa [he, he, comap_mk, comap_mk]))
      split_ifs <;> simp_all
    · simp [h₁, h₂]
  · rw [ha, ha (φ.comp σ)]
    simp [hw]

/-- **A positive involution is complex conjugation in every embedding.** If
`0 ≤ Tr_{K/ℚ}(x σ(x))` for every `x` of a number field `K`, as for a positive involution, then
`φ ∘ σ = conj ∘ φ` for every complex embedding `φ` of `K`. -/
theorem comp_eq_conjugate_of_trace_mul_nonneg
    (hσ : ∀ x : K, 0 ≤ Algebra.trace ℚ K (x * σ x)) (φ : K →+* ℂ) :
    φ.comp σ = conjugate φ := by
  by_contra hne
  by_cases hw : mk (φ.comp σ) = mk φ
  · exact false_of_mk_comp_eq hσ hne hw
  · exact false_of_mk_comp_ne hσ hw

/-- The pointwise form of `TauCeti.NumberField.comp_eq_conjugate_of_trace_mul_nonneg`: if
`0 ≤ Tr_{K/ℚ}(x σ(x))` for every `x`, then `φ (σ x) = conj (φ x)` for every complex embedding
`φ`. -/
theorem apply_eq_conj_of_trace_mul_nonneg
    (hσ : ∀ x : K, 0 ≤ Algebra.trace ℚ K (x * σ x)) (φ : K →+* ℂ) (x : K) :
    φ (σ x) = (starRingEnd ℂ) (φ x) := by
  simpa only [RingHom.comp_apply, conjugate_coe_eq] using
    RingHom.congr_fun (comp_eq_conjugate_of_trace_mul_nonneg hσ φ) x

/-- **A positive involution is an involution**: if `0 ≤ Tr_{K/ℚ}(x σ(x))` for every `x`, then
`σ (σ x) = x`. -/
@[simp]
theorem apply_apply_of_trace_mul_nonneg
    (hσ : ∀ x : K, 0 ≤ Algebra.trace ℚ K (x * σ x)) (x : K) : σ (σ x) = x := by
  let φ : K →+* ℂ := Classical.arbitrary _
  refine φ.injective ?_
  rw [apply_eq_conj_of_trace_mul_nonneg hσ, apply_eq_conj_of_trace_mul_nonneg hσ,
    Complex.conj_conj]

/-- **The fixed field of a positive involution is totally real.** -/
theorem isTotallyReal_eqLocusField_of_trace_mul_nonneg
    (hσ : ∀ x : K, 0 ≤ Algebra.trace ℚ K (x * σ x)) :
    IsTotallyReal (σ.eqLocusField (RingHom.id K)) := by
  refine isTotallyReal_iff_le_maximalRealSubfield.2 fun x hx => ?_
  rw [RingHom.mem_eqLocusField, RingHom.id_apply] at hx
  rw [mem_maximalRealSubfield_iff]
  intro φ
  rw [RCLike.star_def, ← apply_eq_conj_of_trace_mul_nonneg hσ, hx]

/-- **A positive semidefinite trace form implies total reality.** If `0 ≤ Tr_{K/ℚ}(x²)` for every
`x` of a number field `K`, then `K` is totally real. -/
theorem isTotallyReal_of_trace_mul_self_nonneg
    (h : ∀ x : K, 0 ≤ Algebra.trace ℚ K (x * x)) : IsTotallyReal K where
  isReal w := by
    rw [← mk_embedding w, isReal_mk_iff, ComplexEmbedding.isReal_iff]
    exact ((comp_eq_conjugate_of_trace_mul_nonneg (σ := RingHom.id K)
      (fun x => by simpa using h x) _).symm.trans (RingHom.comp_id _))

/-- **A positive involution other than the identity makes `K` a CM field.** If
`0 ≤ Tr_{K/ℚ}(x σ(x))` for every `x` and `σ ≠ id`, then `K` is a CM field. No Galois hypothesis on
`K / ℚ` is needed. -/
theorem isCMField_of_trace_mul_nonneg (hσ : ∀ x : K, 0 ≤ Algebra.trace ℚ K (x * σ x))
    (hne : σ ≠ RingHom.id K) : IsCMField K := by
  -- This adapts the fixed-field argument of Mathlib's `IsCMField.of_forall_isConj`, which assumes
  -- `IsGalois ℚ K`: working with the order-two subgroup generated by `σ` and `IsGaloisGroup` for
  -- its fixed field removes that hypothesis.
  let τ : K ≃ₐ[ℚ] K := algEquivOfRingHom σ
  have hτx (x : K) : τ x = σ x := algEquivOfRingHom_apply σ x
  have hconj (φ : K →+* ℂ) : ComplexEmbedding.IsConj φ τ := by
    rw [ComplexEmbedding.IsConj, ← comp_eq_conjugate_of_trace_mul_nonneg hσ φ]
    ext x
    simp only [RingHom.comp_apply, RingHom.coe_coe, hτx]
  have hτ : τ ≠ 1 := fun h => hne (RingHom.ext fun x => by
    rw [← hτx, h, AlgEquiv.one_apply, RingHom.id_apply])
  have : IsTotallyComplex K := ⟨fun w => by
    rw [← mk_embedding w, isComplex_mk_iff]
    exact (isConj_ne_one_iff (hconj _)).1 hτ⟩
  have hτ2 : orderOf τ = 2 := orderOf_isConj_two_of_ne_one (hconj (Classical.arbitrary _)) hτ
  have hcard : Nat.card (Subgroup.zpowers τ) = 2 := by rw [Nat.card_zpowers, hτ2]
  have : Finite (Subgroup.zpowers τ) := Nat.finite_of_card_ne_zero (by omega)
  let F := FixedPoints.subfield (Subgroup.zpowers τ) K
  -- The fixed field of the group generated by `τ` lies in the fixed field of `σ`.
  have hF : F ≤ σ.eqLocusField (RingHom.id K) := fun x hx => by
    have hτfix : τ x = x := hx ⟨τ, Subgroup.mem_zpowers τ⟩
    rw [RingHom.mem_eqLocusField, RingHom.id_apply, ← hτx, hτfix]
  have : IsTotallyReal F := isTotallyReal_iff_le_maximalRealSubfield.2
    (hF.trans (isTotallyReal_iff_le_maximalRealSubfield.1
      (isTotallyReal_eqLocusField_of_trace_mul_nonneg hσ)))
  have : Algebra.IsQuadraticExtension F K :=
    ⟨by rw [← IsGaloisGroup.card_eq_finrank (Subgroup.zpowers τ) F K, hcard]⟩
  exact IsCMField.ofCMExtension F K

/-- **A positive involution is the complex conjugation of a CM field.** If `K` has an
`IsCMField` instance and `0 ≤ Tr_{K/ℚ}(x σ(x))` for every `x`, then
`σ x = IsCMField.complexConj K x` for every `x`. With `σ ≠ id`,
`TauCeti.NumberField.isCMField_of_trace_mul_nonneg` provides the instance. -/
theorem apply_eq_complexConj_apply_of_trace_mul_nonneg [IsCMField K]
    (hσ : ∀ x : K, 0 ≤ Algebra.trace ℚ K (x * σ x)) (x : K) :
    σ x = IsCMField.complexConj K x := by
  let φ : K →+* ℂ := Classical.arbitrary _
  refine φ.injective ?_
  rw [apply_eq_conj_of_trace_mul_nonneg hσ, IsCMField.complexEmbedding_complexConj]

/-- **Classification of positive involutions of a number field.** If `0 ≤ Tr_{K/ℚ}(x σ(x))` for
every `x`, then either `K` is totally real and `σ` is the identity, or `K` is a CM field and `σ`
is its complex conjugation. -/
theorem isTotallyReal_and_eq_id_or_isCMField_and_eq_complexConj_of_trace_mul_nonneg
    (hσ : ∀ x : K, 0 ≤ Algebra.trace ℚ K (x * σ x)) :
    (IsTotallyReal K ∧ σ = RingHom.id K) ∨
      ∃ _ : IsCMField K, ∀ x, σ x = IsCMField.complexConj K x := by
  by_cases hne : σ = RingHom.id K
  · subst hne
    exact .inl ⟨isTotallyReal_of_trace_mul_self_nonneg fun x => by simpa using hσ x, rfl⟩
  · have := isCMField_of_trace_mul_nonneg hσ hne
    exact .inr ⟨this, apply_eq_complexConj_apply_of_trace_mul_nonneg hσ⟩

end TauCeti.NumberField

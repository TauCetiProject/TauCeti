/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric

/-!
# Norm-preserving lifts through `⋆`-homomorphisms

Let `φ : A → B` be a `⋆`-homomorphism between (possibly nonunital) complex C⋆-algebras, for
instance the quotient map `A → A ⧸ I` by a closed two-sided ideal. A `⋆`-homomorphism is
contractive, so every preimage `a` of `b` has `‖b‖ ≤ ‖a‖`. This file shows that for `b` in the
range of `φ` the bound is attained, and that order-theoretic properties of `b` can be lifted along
with its norm:

* `NonUnitalStarAlgHom.exists_apply_eq_norm_eq`: every `b` in the range of `φ` has a preimage of
  the same norm;
* `NonUnitalStarAlgHom.exists_isSelfAdjoint_apply_eq_norm_eq`: every self-adjoint `b` in the
  range has a self-adjoint preimage of the same norm;
* `NonUnitalStarAlgHom.exists_nonneg_apply_eq_norm_eq`: every positive `b` in the range has a
  positive preimage of the same norm. In particular positive contractions lift to positive
  contractions through a surjective `φ`.

The quotient-specialization `TwoSidedIdeal.Quotient.exists_norm_mk_eq` lives in
`TauCeti.Analysis.CStarAlgebra.Quotient`.

## Implementation notes

The self-adjoint lift comes from the real part `s` of an arbitrary preimage of `b` by applying
the non-unital continuous functional calculus with the function clamping the spectrum to
`[-‖b‖, ‖b‖]`, and the positive lift is the positive part of the self-adjoint lift. Both functions
are the identity on the quasispectrum of `b`, and `⋆`-homomorphisms commute with the functional
calculus (`NonUnitalStarAlgHomClass.map_cfcₙ`). For an arbitrary `b = φ c` with `r = ‖b‖ > 0`, the
preimage is `c - c * h(c⋆c)` where `h t = max 0 (√t - r) / √t`: the function `h` vanishes on
`[0, r ^ 2] ⊇ σₙ(b⋆b)`, while `t * (1 - h t) ^ 2 = min t (r ^ 2)` bounds the norm.

## References

* B. Blackadar, *Operator Algebras: Theory of C⋆-Algebras and von Neumann Algebras*,
  Encyclopaedia of Mathematical Sciences 122, Springer, 2006, §II.5.1 (quotients of
  C⋆-algebras).
-/

public section

open scoped CStarAlgebra ComplexStarModule

namespace NonUnitalStarAlgHom

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- If `f` is the identity on the quasispectrum of `b = φ s` for a self-adjoint `s`, then
`cfcₙ f s` is another preimage of `b`. -/
private theorem apply_cfcₙ_eq (φ : F) {s : A} (hs : IsSelfAdjoint s) {b : B} (hsb : φ s = b)
    {f : ℝ → ℝ} (hf : Continuous f) (hfb : ∀ x ∈ quasispectrum ℝ b, f x = x) :
    φ (cfcₙ f s) = b := by
  subst hsb
  have hf₀ : f 0 = 0 := hfb 0 (quasispectrum.zero_mem ℝ _)
  rw [NonUnitalStarAlgHomClass.map_cfcₙ (S := ℂ) φ f s (hf₀ := hf₀) (hφ := map_continuous φ)
    (hφa := hs.map φ), cfcₙ_congr (g := id) hfb, cfcₙ_id ℝ (φ s) (hs.map φ)]

/-- A `⋆`-homomorphism of C⋆-algebras is contractive, so every preimage of `b` has norm at
least `‖b‖`. -/
private theorem norm_le_of_apply_eq (φ : F) {a : A} {b : B} (h : φ a = b) : ‖b‖ ≤ ‖a‖ :=
  h ▸ norm_apply_le φ a

/-- A `⋆`-homomorphism of C⋆-algebras maps some self-adjoint element of the same norm onto any
given self-adjoint element of its range. -/
theorem exists_isSelfAdjoint_apply_eq_norm_eq (φ : F) {b : B} (hbφ : b ∈ Set.range φ)
    (hb : IsSelfAdjoint b) : ∃ a, IsSelfAdjoint a ∧ φ a = b ∧ ‖a‖ = ‖b‖ := by
  obtain ⟨c, rfl⟩ := hbφ
  -- The real part of `c` is a self-adjoint preimage of `φ c`, which we then clamp.
  obtain ⟨s, hs, hsc⟩ : ∃ s : A, IsSelfAdjoint s ∧ φ s = φ c :=
    ⟨ℜ c, (ℜ c).property, by rw [map_realPart, hb.coe_realPart]⟩
  set r := ‖φ c‖
  have hr : 0 ≤ r := norm_nonneg _
  let f : ℝ → ℝ := fun t ↦ max (-r) (min t r)
  have hf : Continuous f := by fun_prop
  have hfa : φ (cfcₙ f s) = φ c := apply_cfcₙ_eq φ hs hsc hf fun x hx ↦ by
    obtain ⟨h₀, h₁⟩ : -r ≤ x ∧ x ≤ r :=
      abs_le.1 (Real.norm_eq_abs x ▸ quasispectrum.norm_le_norm_of_mem hx)
    simp only [f, min_eq_left h₁, max_eq_right h₀]
  refine ⟨cfcₙ f s, cfcₙ_predicate f s, hfa, le_antisymm (norm_cfcₙ_le fun x _ ↦ ?_) ?_⟩
  · simp only [Real.norm_eq_abs, abs_le, f]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  · exact norm_le_of_apply_eq φ hfa

/-- The cutoff `t ↦ max 0 (√t - r) / √t` is continuous for `r > 0`: it vanishes on
`(-∞, r ^ 2)`, a neighbourhood of every `t ≤ 0`, where `√t` vanishes. -/
private theorem continuous_cutoff {r : ℝ} (hr : 0 < r) :
    Continuous fun t : ℝ ↦ max 0 (√t - r) / √t := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  rcases lt_or_ge 0 t with ht | ht
  · exact (continuous_const.max (Real.continuous_sqrt.sub continuous_const)).continuousAt.div
      Real.continuous_sqrt.continuousAt (Real.sqrt_pos.2 ht).ne'
  · refine ContinuousAt.congr (f := fun _ ↦ (0 : ℝ)) continuousAt_const ?_
    filter_upwards [eventually_lt_nhds (ht.trans_lt (pow_pos hr 2))] with u hu
    rw [max_eq_left (sub_nonpos.2 ((Real.sqrt_lt' hr).2 hu).le), zero_div]

/-- For `t ≥ 0` and `r > 0`, damping `t` by the cutoff gives `t * (1 - h t) ^ 2 = min t (r ^ 2)`,
which is at most `r ^ 2`. -/
private theorem mul_one_sub_cutoff_sq_le {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    t * (1 - max 0 (√t - r) / √t) ^ 2 ≤ r ^ 2 := by
  rcases le_or_gt √t r with hle | hlt
  · rw [max_eq_left (sub_nonpos.2 hle), zero_div, sub_zero, one_pow, mul_one]
    exact (Real.sqrt_le_left hr.le).1 hle
  · have hu : 0 < √t := hr.trans hlt
    have : 1 - (√t - r) / √t = r / √t := by field_simp; ring
    rw [max_eq_right (sub_nonneg.2 hlt.le), this, div_pow, Real.sq_sqrt ht]
    exact (mul_div_cancel₀ _ (Real.sqrt_pos.1 hu).ne').le

/-- Every element of the range of a `⋆`-homomorphism of C⋆-algebras has a preimage of the same
norm. For a quotient map this says that the quotient norm is attained. -/
theorem exists_apply_eq_norm_eq (φ : F) {b : B} (hbφ : b ∈ Set.range φ) :
    ∃ a, φ a = b ∧ ‖a‖ = ‖b‖ := by
  obtain ⟨c, rfl⟩ := hbφ
  set r := ‖φ c‖
  rcases (norm_nonneg (φ c)).eq_or_lt with hr | hr
  · exact ⟨0, by simp [norm_eq_zero.1 hr.symm], by simp [r, ← hr]⟩
  -- `A` carries no order here; the spectral order provides the `StarOrderedRing` structure
  -- needed below for `star_mul_self_nonneg` and `quasispectrum_nonneg_of_nonneg`.
  let _ := CStarAlgebra.spectralOrder A
  have _ := CStarAlgebra.spectralOrderedRing A
  -- Make the cutoff opaque, so that the `cfcₙ` side goals and `simp` do not unfold its body;
  -- `hdef` recovers the formula where it is needed.
  obtain ⟨h, hh, hdef⟩ : ∃ h : ℝ → ℝ, Continuous h ∧ ∀ t, h t = max 0 (√t - r) / √t :=
    ⟨_, continuous_cutoff hr, fun _ ↦ rfl⟩
  -- The cutoff vanishes at `0`, as the non-unital calculus requires.
  have : h 0 = 0 := by simp [hdef]
  have hsa : IsSelfAdjoint (star c * c) := .star_mul_self c
  set H := cfcₙ h (star c * c)
  have hH : IsSelfAdjoint H := cfcₙ_predicate h _
  -- `φ` maps the cutoff of `c⋆c` to the cutoff of `b⋆b`, which vanishes.
  have hφH : φ H = 0 := by
    rw [NonUnitalStarAlgHomClass.map_cfcₙ (S := ℂ) φ h _ (hφ := map_continuous φ)
      (hφa := hsa.map φ), map_mul, map_star]
    refine (cfcₙ_congr (g := 0) fun t ht ↦ ?_).trans (cfcₙ_zero ℝ _)
    have ht' : t ≤ r ^ 2 := by
      have := (Real.le_norm_self t).trans (quasispectrum.norm_le_norm_of_mem ht)
      rwa [CStarRing.norm_star_mul_self, ← sq] at this
    rw [Pi.zero_apply, hdef, max_eq_left (sub_nonpos.2 ((Real.sqrt_le_left hr.le).2 ht')),
      zero_div]
  -- `(c - c * H)⋆ (c - c * H)` is `cfcₙ (fun t ↦ t * (1 - h t) ^ 2) (c⋆c)`, of norm at most `r²`.
  have hnorm : ‖star (c - c * H) * (c - c * H)‖ ≤ r ^ 2 := by
    have key : star (c - c * H) * (c - c * H) =
        cfcₙ (fun t ↦ t - t * h t - h t * t + h t * t * h t) (star c * c) := by
      rw [cfcₙ_add .., cfcₙ_sub .., cfcₙ_sub .., cfcₙ_mul .., cfcₙ_mul .., cfcₙ_mul ..,
        cfcₙ_mul .., cfcₙ_id' ℝ (star c * c)]
      simp only [star_sub, star_mul, hH.star_eq]
      noncomm_ring
    rw [key]
    refine norm_cfcₙ_le fun t ht ↦ ?_
    have ht₀ : 0 ≤ t := quasispectrum_nonneg_of_nonneg _ (star_mul_self_nonneg c) t ht
    rw [show t - t * h t - h t * t + h t * t * h t = t * (1 - h t) ^ 2 by ring, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), hdef]
    exact mul_one_sub_cutoff_sq_le hr ht₀
  have hφa : φ (c - c * H) = φ c := by simp [hφH]
  refine ⟨c - c * H, hφa, le_antisymm ?_ (norm_le_of_apply_eq φ hφa)⟩
  rw [← sq_le_sq₀ (norm_nonneg _) hr.le, sq, ← CStarRing.norm_star_mul_self]
  exact hnorm

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

/-- A `⋆`-homomorphism of C⋆-algebras maps some positive element of the same norm onto any given
positive element of its range. In particular, positive contractions lift to positive contractions
through a surjective `φ`. -/
theorem exists_nonneg_apply_eq_norm_eq (φ : F) {b : B} (hbφ : b ∈ Set.range φ) (hb : 0 ≤ b) :
    ∃ a, 0 ≤ a ∧ φ a = b ∧ ‖a‖ = ‖b‖ := by
  obtain ⟨s, hs, hsb, hsn⟩ := exists_isSelfAdjoint_apply_eq_norm_eq φ hbφ hb.isSelfAdjoint
  -- The positive part of `s` is still a preimage: `(·⁺)` is the identity on `σₙ(b) ⊆ [0, ∞)`.
  have hφs : φ s⁺ = b := apply_cfcₙ_eq φ hs hsb (by fun_prop) fun x hx ↦
    posPart_eq_self.2 (quasispectrum_nonneg_of_nonneg _ hb x hx)
  exact ⟨s⁺, CFC.posPart_nonneg s, hφs,
    ((CStarAlgebra.norm_posPart_le s).trans hsn.le).antisymm (norm_le_of_apply_eq φ hφs)⟩

end NonUnitalStarAlgHom

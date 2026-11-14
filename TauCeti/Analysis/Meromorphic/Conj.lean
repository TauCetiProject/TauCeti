/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Divisor
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Reflecting a function across the real axis

For `f : ℂ → ℂ`, the reflected function `conj ∘ f ∘ conj` is again holomorphic, meromorphic, and
has the same order, at the reflected point. Mathlib records the differentiable case as
`DifferentiableAt.conj_conj`; this file supplies the analytic and meromorphic versions together
with the invariance of `meromorphicOrderAt`.

These are the statements needed to transport the analytic properties of a completed L-function to
its dual, whose completed function is the reflection of the original one. Combining this order
invariance with a functional symmetry `f (1 - z) = c * conj (f (conj z))` shows that the
whole-plane divisor of `f` is invariant under `z ↦ 1 - conj z` and induces an involutive
permutation of its support.

## Main results

* `AnalyticAt.conj_conj`, `TauCeti.analyticAt_conj_conj_iff`: reflection preserves analyticity.
* `MeromorphicAt.conj_conj`, `TauCeti.meromorphicAt_conj_conj_iff`, `Meromorphic.conj_conj`:
  reflection preserves meromorphy.
* `TauCeti.meromorphicOrderAt_conj_conj`: reflection preserves the order of a meromorphic
  function.
* `TauCeti.divisor_one_sub_conj`, `TauCeti.divisorSupportOneSubConj`: invariance of the
  whole-plane divisor and the induced support permutation `ρ ↦ 1 - conj ρ` under
  `f (1 - z) = c * conj (f (conj z))`.
-/

public section

open ComplexConjugate Filter Topology

variable {f : ℂ → ℂ} {x : ℂ}

/-- If `f` is analytic at `x`, then `conj ∘ f ∘ conj` is analytic at `conj x`. This is the
one-variable case of `AnalyticAt.star_star`. -/
theorem AnalyticAt.conj_conj (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (conj ∘ f ∘ conj) (conj x) := by
  simpa only [Complex.star_def] using hf.star_star

/-- A function `f` is analytic at `conj x` iff `conj ∘ f ∘ conj` is analytic at `x`. -/
@[simp]
theorem TauCeti.analyticAt_conj_conj_iff :
    AnalyticAt ℂ (conj ∘ f ∘ conj) x ↔ AnalyticAt ℂ f (conj x) :=
  ⟨fun hf ↦ by simpa [Function.comp_def] using hf.conj_conj, fun hf ↦ by
    simpa using hf.conj_conj⟩

/-- If `f` is meromorphic at `x`, then `conj ∘ f ∘ conj` is meromorphic at `conj x`. -/
theorem MeromorphicAt.conj_conj (hf : MeromorphicAt f x) :
    MeromorphicAt (conj ∘ f ∘ conj) (conj x) := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, hn.conj_conj.congr (Eventually.of_forall fun z ↦ ?_)⟩
  simp

/-- A function `f` is meromorphic at `conj x` iff `conj ∘ f ∘ conj` is meromorphic at `x`. -/
@[simp]
theorem TauCeti.meromorphicAt_conj_conj_iff :
    MeromorphicAt (conj ∘ f ∘ conj) x ↔ MeromorphicAt f (conj x) :=
  ⟨fun hf ↦ by simpa [Function.comp_def] using hf.conj_conj, fun hf ↦ by
    simpa using hf.conj_conj⟩

/-- If `f` is meromorphic on `ℂ`, then so is `conj ∘ f ∘ conj`. -/
theorem Meromorphic.conj_conj (hf : Meromorphic f) : Meromorphic (conj ∘ f ∘ conj) :=
  fun _ ↦ TauCeti.meromorphicAt_conj_conj_iff.2 (hf _)

/-- Reflection across the real axis preserves the order of a meromorphic function:
the order of `conj ∘ f ∘ conj` at `x` is the order of `f` at `conj x`. -/
@[simp]
theorem TauCeti.meromorphicOrderAt_conj_conj :
    meromorphicOrderAt (conj ∘ f ∘ conj) x = meromorphicOrderAt f (conj x) := by
  by_cases hf : MeromorphicAt f (conj x)
  swap
  · rw [meromorphicOrderAt_of_not_meromorphicAt hf,
      meromorphicOrderAt_of_not_meromorphicAt (meromorphicAt_conj_conj_iff.not.2 hf)]
  -- Conjugation carries the punctured neighbourhoods of `x` to those of `conj x`.
  have hconj : Tendsto conj (𝓝[≠] x) (𝓝[≠] (conj x)) :=
    Complex.continuous_conj.continuousWithinAt.tendsto_nhdsWithin fun z hz ↦
      (starRingEnd ℂ).injective.ne hz
  cases h : meromorphicOrderAt f (conj x) with
  | top =>
    rw [meromorphicOrderAt_eq_top_iff] at h ⊢
    filter_upwards [hconj.eventually h] with z hz
    simp [hz]
  | coe n =>
    obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 h
    refine (meromorphicOrderAt_eq_int_iff (meromorphicAt_conj_conj_iff.2 hf)).2
      ⟨conj ∘ g ∘ conj, analyticAt_conj_conj_iff.2 hg, by simpa using hg0, ?_⟩
    filter_upwards [hconj.eventually hfg] with z hz
    simp [hz]

/-- Under a functional-conjugation symmetry `f (1 - z) = c * conj (f (conj z))`, the whole-plane
divisor of `f` is invariant under `z ↦ 1 - conj z`. -/
theorem TauCeti.divisor_one_sub_conj {f : ℂ → ℂ} {c : ℂ}
    (hfe : ∀ z : ℂ, f (1 - z) = c * conj (f (conj z))) (z : ℂ) :
    MeromorphicOn.divisor f Set.univ (1 - conj z) = MeromorphicOn.divisor f Set.univ z := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hf0 : f = 0 := funext fun w ↦ by simpa using hfe (1 - w)
    simp [hf0]
  · by_cases hm : MeromorphicOn f Set.univ
    · have hm1 : meromorphicOrderAt (fun w : ℂ ↦ f (1 - w)) (conj z) =
          meromorphicOrderAt f (1 - conj z) :=
        meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) (g := fun w : ℂ ↦ 1 - w) (by fun_prop)
          (by simp)
      have hsmul : (fun w : ℂ ↦ c * conj (f (conj w))) = c • (conj ∘ f ∘ conj) := by
        ext w
        simp [Function.comp_def, smul_eq_mul]
      have hm2 : meromorphicOrderAt (fun w : ℂ ↦ c * conj (f (conj w))) (conj z) =
          meromorphicOrderAt f z := by
        rw [hsmul, meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc,
          TauCeti.meromorphicOrderAt_conj_conj, Complex.conj_conj]
      have hmo : meromorphicOrderAt f (1 - conj z) = meromorphicOrderAt f z := by
        rw [← hm1, funext hfe, hm2]
      rw [hm.divisor_apply (Set.mem_univ _), hm.divisor_apply (Set.mem_univ _), hmo]
    · simp [MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn hm]

/-- Under a functional-conjugation symmetry `f (1 - z) = c * conj (f (conj z))`, the involution
`ρ ↦ 1 - conj ρ` restricts to a permutation of `(MeromorphicOn.divisor f Set.univ).support`. -/
noncomputable def TauCeti.divisorSupportOneSubConj {f : ℂ → ℂ} {c : ℂ}
    (hfe : ∀ z : ℂ, f (1 - z) = c * conj (f (conj z))) :
    Equiv.Perm (MeromorphicOn.divisor f Set.univ).support :=
  Function.Involutive.toPerm
    (fun ρ ↦ ⟨1 - conj (ρ : ℂ), Function.mem_support.mpr <| by
      rw [divisor_one_sub_conj hfe]
      exact Function.mem_support.mp ρ.property⟩)
    fun ρ ↦ by ext; simp

/-- The support permutation `divisorSupportOneSubConj` acts on the underlying point by
`ρ ↦ 1 - conj ρ`. -/
@[simp]
theorem TauCeti.coe_divisorSupportOneSubConj_apply {f : ℂ → ℂ} {c : ℂ}
    (hfe : ∀ z : ℂ, f (1 - z) = c * conj (f (conj z)))
    (ρ : (MeromorphicOn.divisor f Set.univ).support) :
    (divisorSupportOneSubConj hfe ρ : ℂ) = 1 - conj (ρ : ℂ) :=
  (rfl)

/-- `divisorSupportOneSubConj` is its own inverse. -/
@[simp]
theorem TauCeti.divisorSupportOneSubConj_symm {f : ℂ → ℂ} {c : ℂ}
    (hfe : ∀ z : ℂ, f (1 - z) = c * conj (f (conj z))) :
    (divisorSupportOneSubConj hfe).symm = divisorSupportOneSubConj hfe :=
  (rfl)

/-- `divisorSupportOneSubConj` is an involution on the divisor support. -/
@[simp]
theorem TauCeti.divisorSupportOneSubConj_apply_apply {f : ℂ → ℂ} {c : ℂ}
    (hfe : ∀ z : ℂ, f (1 - z) = c * conj (f (conj z)))
    (ρ : (MeromorphicOn.divisor f Set.univ).support) :
    divisorSupportOneSubConj hfe (divisorSupportOneSubConj hfe ρ) = ρ := by
  ext
  simp

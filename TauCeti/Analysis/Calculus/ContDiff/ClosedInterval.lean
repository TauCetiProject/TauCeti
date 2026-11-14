/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import TauCeti.Analysis.Calculus.IteratedDeriv.Within

/-!
# Continuous derivative jets on a closed interval

On a nondegenerate closed time interval `a < b`, derivatives at the endpoints are one-sided.
An interior derivative with a continuous extension to the closed interval is the derivative
within that interval, including at its endpoints (this also holds for `b ≤ a`, where the interval
has at most one point). For `a < b`, applying this observation successively identifies every field
of a continuous derivative jet with `iteratedDerivWithin`; on a singleton the interior conditions
are vacuous and the higher fields are arbitrary, so this identification needs `a < b`.

The jet criterion `contDiffOn_Icc_iff_exists_continuous_jet` characterizes finite-order
smoothness on a closed interval, degenerate or not, using only continuous fields and ordinary
interior derivatives. It allows time derivatives of functions on closed slabs to be specified by
continuous extensions without choosing an extension of the function outside the slab.
The codomain may itself be a space of continuous multilinear maps.

The endpoint argument uses Mathlib's
`hasFDerivWithinAt_closure_of_tendsto_fderiv`; higher orders use
`iteratedDerivWithin_succ` and the native criterion for `ContDiffOn` in terms of iterated
derivatives. No completeness assumption on the codomain is needed.

`ContDiffOn.isBounded_image_deriv` bounds the derivative of a `C¹` function on a closed interval:
it agrees with the continuous within-interval derivative away from the two endpoints.
`TauCeti.contDiffOn_one_Icc_of_derivWithin_eq` glues `C¹` smoothness across an interior point when
the two one-sided within-interval derivatives agree there.
-/

public section

open Set Filter Topology
open scoped ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {a b : ℝ} {f g : ℝ → F}

/-- A continuous extension of an interior derivative is the derivative within the closed
interval, also at its two endpoints. -/
theorem hasDerivWithinAt_Icc_of_continuousOn
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) {x : ℝ} (hx : x ∈ Icc a b) :
    HasDerivWithinAt f (g x) (Icc a b) x := by
  rcases lt_or_ge a b with hab | hba
  swap
  · rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    exact .of_subsingleton (subsingleton_Icc_of_ge hba)
  have hlim : Tendsto (fderiv ℝ f) (𝓝[Ioo a b] x)
      (𝓝 (ContinuousLinearMap.toSpanSingleton ℝ (g x))) := by
    have h := (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := F)).continuous.tendsto (g x)
    apply (h.comp ((hg x hx).mono Ioo_subset_Icc_self)).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hd y hy).hasFDerivAt.fderiv.symm
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← closure_Ioo hab.ne]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy ↦ (hd y hy).differentiableAt.differentiableWithinAt)
    (convex_Ioo a b) isOpen_Ioo _ hlim
  intro y hy
  rw [closure_Ioo hab.ne] at hy
  exact (hf y hy).mono Ioo_subset_Icc_self

/-- Every field in a finite continuous interior derivative jet is the corresponding iterated
derivative within the closed interval. In particular its endpoint values are canonical. -/
theorem eqOn_iteratedDerivWithin_Icc_of_continuous_jet (hab : a < b)
    {n : ℕ} {J : ℕ → ℝ → F} (hzero : EqOn (J 0) f (Icc a b))
    (hc : ∀ j ≤ n, ContinuousOn (J j) (Icc a b))
    (hd : ∀ j < n, ∀ x ∈ Ioo a b, HasDerivAt (J j) (J (j + 1) x) x)
    {j : ℕ} (hj : j ≤ n) : EqOn (iteratedDerivWithin j f (Icc a b)) (J j) (Icc a b) := by
  induction j with
  | zero => simpa using hzero.symm
  | succ j ih =>
    have hjn : j < n := by omega
    have heq := ih (by omega)
    intro x hx
    rw [iteratedDerivWithin_succ, derivWithin_congr heq (heq hx)]
    exact (hasDerivWithinAt_Icc_of_continuousOn (hc j (by omega))
      (hc (j + 1) hj) (hd j hjn) hx).derivWithin (uniqueDiffOn_Icc hab x hx)

/-- A finite continuous derivative jet in the interior yields smoothness up to both endpoints.
Only the jet values on the closed interval matter. -/
theorem contDiffOn_Icc_of_continuous_jet
    {n : ℕ} {J : ℕ → ℝ → F} (hzero : EqOn (J 0) f (Icc a b))
    (hc : ∀ j ≤ n, ContinuousOn (J j) (Icc a b))
    (hd : ∀ j < n, ∀ x ∈ Ioo a b, HasDerivAt (J j) (J (j + 1) x) x) :
    ContDiffOn ℝ n f (Icc a b) := by
  rcases lt_or_ge a b with hab | hba
  swap
  · intro x hx
    rw [(subsingleton_Icc_of_ge hba).eq_singleton_of_mem hx]
    exact contDiffWithinAt_singleton
  apply (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
    (uniqueDiffOn_Icc hab)).2
  constructor
  · intro j hj
    exact (hc j hj).congr
      (eqOn_iteratedDerivWithin_Icc_of_continuous_jet hab hzero hc hd hj)
  · intro j hj x hx
    have heq := eqOn_iteratedDerivWithin_Icc_of_continuous_jet hab hzero hc hd
      (Nat.le_of_lt hj)
    exact ((hasDerivWithinAt_Icc_of_continuousOn (hc j (by omega))
      (hc (j + 1) (by omega)) (hd j hj) hx).congr heq (heq hx)).differentiableWithinAt

/-- Finite-order smoothness on a closed interval is equivalent to the existence
of continuous derivative fields satisfying the ordinary derivative identities in the interior.
There is no condition on the fields outside the interval or above the specified order. -/
theorem contDiffOn_Icc_iff_exists_continuous_jet {n : ℕ} :
    ContDiffOn ℝ n f (Icc a b) ↔
      ∃ J : ℕ → ℝ → F, EqOn (J 0) f (Icc a b) ∧
        (∀ j ≤ n, ContinuousOn (J j) (Icc a b)) ∧
        ∀ j < n, ∀ x ∈ Ioo a b, HasDerivAt (J j) (J (j + 1) x) x := by
  rcases lt_or_ge a b with hab | hba
  swap
  · refine ⟨fun _ ↦ ⟨fun _ ↦ f, eqOn_refl _ _,
      fun _ _ ↦ (subsingleton_Icc_of_ge hba).continuousOn _, fun j _ x hx ↦ ?_⟩,
      fun ⟨J, hzero, hc, hd⟩ ↦ contDiffOn_Icc_of_continuous_jet hzero hc hd⟩
    exact absurd hx.2 (not_lt.2 (hba.trans hx.1.le))
  constructor
  · intro hf
    refine ⟨fun j ↦ iteratedDerivWithin j f (Icc a b), ?_, ?_, ?_⟩
    · simp only [iteratedDerivWithin_zero]
      exact eqOn_refl _ _
    · intro j hj
      exact hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) (uniqueDiffOn_Icc hab)
    · intro j hj x hx
      exact hf.hasDerivAt_iteratedDerivWithin (mod_cast hj) (Icc_mem_nhds hx.1 hx.2)
  · rintro ⟨J, hzero, hc, hd⟩
    exact contDiffOn_Icc_of_continuous_jet hzero hc hd

/-- If `f` is `C¹` on `[a, c]` and `[c, b]` with matching within-interval derivatives at `c`, then
`f` is `C¹` on `[a, b]`. When `c ≤ a` or `b ≤ c`, one of `[a, c]`, `[c, b]` already covers
`[a, b]`. -/
theorem contDiffOn_one_Icc_of_derivWithin_eq {c : ℝ}
    (hf₁ : ContDiffOn ℝ 1 f (Icc a c)) (hf₂ : ContDiffOn ℝ 1 f (Icc c b))
    (hderiv : derivWithin f (Icc a c) c = derivWithin f (Icc c b) c) :
    ContDiffOn ℝ 1 f (Icc a b) := by
  rcases le_or_gt c a with hca | hac
  · exact hf₂.mono (Icc_subset_Icc hca le_rfl)
  rcases le_or_gt b c with hbc | hcb
  · exact hf₁.mono (Icc_subset_Icc le_rfl hbc)
  let g : ℝ → F := fun t ↦ if t ≤ c then derivWithin f (Icc a c) t else derivWithin f (Icc c b) t
  have hg₁ : ContinuousOn g (Icc a c) :=
    (hf₁.continuousOn_derivWithin (uniqueDiffOn_Icc hac) le_rfl).congr fun t ht ↦ by simp [g, ht.2]
  have hg₂ : ContinuousOn g (Icc c b) :=
    (hf₂.continuousOn_derivWithin (uniqueDiffOn_Icc hcb) le_rfl).congr fun t ht ↦ by
      dsimp only [g]
      split_ifs with htc
      · obtain rfl : t = c := le_antisymm htc ht.1
        exact hderiv
      · rfl
  have hg : ContinuousOn g (Icc a b) :=
    Icc_union_Icc_eq_Icc hac.le hcb.le ▸ hg₁.union_of_isClosed hg₂ isClosed_Icc isClosed_Icc
  have hf : ContinuousOn f (Icc a b) :=
    Icc_union_Icc_eq_Icc hac.le hcb.le ▸
      hf₁.continuousOn.union_of_isClosed hf₂.continuousOn isClosed_Icc isClosed_Icc
  refine contDiffOn_Icc_of_continuous_jet (n := 1)
    (J := fun j ↦ if j = 0 then f else g) (eqOn_refl _ _)
    (fun j hj ↦ by rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl; exacts [hf, hg])
    fun j hj t ht ↦ ?_
  obtain rfl : j = 0 := by omega
  simp only [↓reduceIte, Nat.zero_add, one_ne_zero]
  rcases lt_trichotomy t c with htc | rfl | hct
  · simpa only [g, htc.le, ↓reduceIte] using
      (hf₁.differentiableOn one_ne_zero t ⟨ht.1.le, htc.le⟩).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds ht.1 htc)
  · have hd₁ : HasDerivWithinAt f (g t) (Iic t) t := by
      simpa only [g, le_rfl, ↓reduceIte] using
        (hf₁.differentiableOn one_ne_zero t ⟨hac.le, le_rfl⟩).hasDerivWithinAt
          |>.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hac)
    have hd₂ : HasDerivWithinAt f (g t) (Ici t) t := by
      simpa only [g, le_rfl, ↓reduceIte, hderiv] using
        (hf₂.differentiableOn one_ne_zero t ⟨le_rfl, hcb.le⟩).hasDerivWithinAt
          |>.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hcb)
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hd₁.union hd₂
  · simpa only [g, hct.not_ge, ↓reduceIte] using
      (hf₂.differentiableOn one_ne_zero t ⟨hct.le, ht.2.le⟩).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds hct ht.2)

end TauCeti

/-- The derivative of a function that is `C¹` on a closed interval has bounded image on that
interval. At the two endpoints `deriv f` may differ from the one-sided derivative, but these
contribute only two values. -/
theorem ContDiffOn.isBounded_image_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a b : ℝ} {n : ℕ∞ω} (hf : ContDiffOn ℝ n f (Icc a b)) (hn : 1 ≤ n) :
    Bornology.IsBounded (deriv f '' Icc a b) := by
  rcases lt_or_ge a b with hab | hba
  swap
  · exact ((subsingleton_Icc_of_ge hba).image _).finite.isBounded
  have hdw : Bornology.IsBounded (derivWithin f (Icc a b) '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn
      (hf.continuousOn_derivWithin (uniqueDiffOn_Icc hab) hn)).isBounded
  refine (hdw.union (Set.toFinite {deriv f a, deriv f b}).isBounded).subset ?_
  rintro y ⟨t, ht, rfl⟩
  rcases eq_or_ne t a with rfl | hta
  · simp
  rcases eq_or_ne t b with rfl | htb
  · simp
  exact Or.inl ⟨t, ht, derivWithin_of_mem_nhds (Icc_mem_nhds (ht.1.lt_of_ne' hta)
    (ht.2.lt_of_ne htb))⟩

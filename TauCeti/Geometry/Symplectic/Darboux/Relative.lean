/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
import TauCeti.Analysis.Calculus.DifferentialForm.Relative
import TauCeti.Geometry.Symplectic.Darboux.Basic
import TauCeti.Geometry.Symplectic.WittExtension
import TauCeti.LinearAlgebra.BilinearMap.Multilinear

/-!
# The relative Darboux theorem in adapted coordinates

Let `E` and `N` be finite-dimensional real normed spaces. In adapted coordinates an embedded
submanifold is the zero section `E × {0}` of `E × N`, included by `q ↦ (q, 0)`, whose differential
is `ContinuousLinearMap.inl ℝ E N`. Let `ω₀`, `ω₁` be closed two-forms of class `C^r` (`r ≥ 1`)
near a point `(q₀, 0)`, nondegenerate at that point, with the same pullback to the zero section:
`ω₀(q, 0)` and `ω₁(q, 0)` agree on pairs of vectors of `E × {0}`, for every `q`. The pullbacks may
have any rank, and away from the zero section the forms are unrelated.

The **relative Darboux theorem**
(`TauCeti.exists_diffeomorph_fix_zeroSection_eventually_compContinuousLinearMap_fderiv_eq`) says
that `ω₀` and `ω₁` have symplectomorphic germs at `(q₀, 0)` by a germ fixing the zero section: some
`C^r` diffeomorphism `ψ` of `E × N` fixes every point `(q, 0)` with `q` near `q₀`, and pulls `ω₁`
back to `ω₀` near `(q₀, 0)`.

It is proved in two steps.

* **The relative Moser step** treats the case where `ω₀` and `ω₁` agree as full forms at
  `(q₀, 0)`. On a ball around `(q₀, 0)`, which is stable under the fibre scaling
  `(q, n) ↦ (q, t • n)` for `t ∈ [0, 1]`, the relative Poincaré lemma
  (`Convex.exists_contDiffOn_relative_primitive`) gives a one-form `β` with `dβ = ω₁ - ω₀`,
  vanishing as a full covector at every point of the zero section since `ω₁ - ω₀` pulls back to
  zero there. Moser's lemma
  (`TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_of_extDeriv_eq`)
  applied to this primitive gives a diffeomorphism fixing the zeros of `β`, hence the zero section.
* **The linear step.** The identity of `E × {0}` preserves the restrictions of the forms at
  `(q₀, 0)`, so Witt's extension theorem
  (`TauCeti.SymplecticForm.exists_isSymplectomorphism_extend`) extends it to a linear
  symplectomorphism `A` from `(E × N, ω₀(q₀, 0))` to `(E × N, ω₁(q₀, 0))`. It fixes the zero
  section pointwise, so `A^* ω₁` agrees with `ω₀` as a full form at `(q₀, 0)` and has the same
  pullback to the zero section as `ω₀`; hence the relative Moser step applies to `ω₀` and `A^* ω₁`.

As in `TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq`, forms are Mathlib's
continuous alternating maps with its exterior derivative `extDeriv`, the pullback of `ω` along `ψ`
at `x` is `(ω (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)`, and nondegeneracy of `ω(x)` says that
no nonzero `v` has `ω(x)(v, w) = 0` for every `w`.

## References

* A. Weinstein, *Symplectic manifolds and their Lagrangian submanifolds*, Advances in Mathematics
  6 (1971), 329–346 (the relative Darboux theorem).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 6–7 (the relative Poincaré lemma and Moser's relative theorem).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser's argument).
-/

public section

open Set Filter Topology Metric
open scoped Manifold

namespace TauCeti

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]

/-- **The relative Moser step.** Let `ω₀`, `ω₁` be closed `C^r` two-forms (`r ≥ 1`) on an open
subset `W` of `E × N` containing `(q₀, 0)`, which agree and are nondegenerate at `(q₀, 0)` and have
the same pullback to the zero section `E × {0}`. Then some `C^r` diffeomorphism `ψ` of `E × N` fixes
every point `(q, 0)` with `q` near `q₀` and pulls `ω₁` back to `ω₀` near `(q₀, 0)`. The relative
Darboux theorem below removes the hypothesis that the forms agree at `(q₀, 0)`. -/
private theorem exists_diffeomorph_fix_zeroSection_of_eq
    {ω₀ ω₁ : E × N → (E × N) [⋀^Fin 2]→L[ℝ] ℝ} {W : Set (E × N)} {q₀ : E} {r : ℕ∞}
    (hr : 1 ≤ r) (hW : IsOpen W) (hq₀ : (q₀, (0 : N)) ∈ W) (hω₀ : ContDiffOn ℝ r ω₀ W)
    (hω₁ : ContDiffOn ℝ r ω₁ W) (hdω₀ : ∀ x ∈ W, extDeriv ω₀ x = 0)
    (hdω₁ : ∀ x ∈ W, extDeriv ω₁ x = 0)
    (htan : ∀ q : E, (q, (0 : N)) ∈ W →
      (ω₁ (q, 0)).compContinuousLinearMap (.inl ℝ E N) =
        (ω₀ (q, 0)).compContinuousLinearMap (.inl ℝ E N))
    (heq : ω₁ (q₀, 0) = ω₀ (q₀, 0)) (hnd : ∀ v, (∀ w, ω₀ (q₀, 0) ![v, w] = 0) → v = 0) :
    ∃ ψ : (E × N) ≃ₘ^r⟮𝓘(ℝ, E × N), 𝓘(ℝ, E × N)⟯ (E × N),
      (∀ᶠ q in 𝓝 q₀, ψ (q, 0) = (q, 0)) ∧
      ∀ᶠ x in 𝓝 (q₀, (0 : N)), (ω₁ (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x) = ω₀ x := by
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
    exact (lt_of_lt_of_le zero_lt_one this).ne'
  -- A ball around `(q₀, 0)` inside `W`; for the product norm it is stable under fibre scaling.
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hW _ hq₀
  have hscale : ∀ x ∈ ball (q₀, (0 : N)) ρ, ∀ t ∈ Icc (0 : ℝ) 1,
      (x.1, t • x.2) ∈ ball (q₀, (0 : N)) ρ := by
    intro x hx t ht
    rw [mem_ball, Prod.dist_eq] at hx ⊢
    refine lt_of_le_of_lt (max_le_max le_rfl ?_) hx
    simp only [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  -- The difference `ω₁ - ω₀` is closed and pulls back to zero on the zero section.
  have hd : ∀ x ∈ ball (q₀, (0 : N)) ρ, extDeriv (fun y ↦ ω₁ y - ω₀ y) x = 0 := fun x hx ↦ by
    have h₀ := (hω₀.differentiableOn hr0).differentiableAt (hW.mem_nhds (hρW hx))
    have h₁ := (hω₁.differentiableOn hr0).differentiableAt (hW.mem_nhds (hρW hx))
    have e : (fun y ↦ ω₁ y - ω₀ y) = ω₁ + (-1 : ℝ) • ω₀ := by
      funext y
      ext v
      simp [sub_eq_add_neg]
    rw [e, extDeriv_add h₁ (h₀.const_smul (-1 : ℝ)), extDeriv_smul, hdω₁ x (hρW hx),
      hdω₀ x (hρW hx), smul_zero, add_zero]
  have hzero : ∀ q : E, (q, (0 : N)) ∈ ball (q₀, (0 : N)) ρ →
      (ω₁ (q, 0) - ω₀ (q, 0)).compContinuousLinearMap (.inl ℝ E N) = 0 := fun q hq ↦ by
    ext v
    simpa [sub_eq_zero] using congrArg (· v) (htan q (hρW hq))
  -- A primitive of `ω₁ - ω₀` vanishing along the zero section (the relative Poincaré lemma).
  obtain ⟨β, hβ, hβ0, hdβ⟩ := (convex_ball (q₀, (0 : N)) ρ).exists_contDiffOn_relative_primitive
    (k := 1) isOpen_ball hr ((hω₁.mono hρW).sub (hω₀.mono hρW)) hscale hd hzero
  -- Moser's lemma for this primitive: the resulting diffeomorphism fixes the zeros of `β`.
  obtain ⟨ψ, hfix, hψ⟩ :=
    exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_of_extDeriv_eq hr isOpen_ball
      (mem_ball_self hρ) (hω₀.mono hρW) (hω₁.mono hρW) hβ (fun x hx ↦ hdω₀ x (hρW hx))
      (fun x hx ↦ hdω₁ x (hρW hx)) hdβ (hβ0 q₀) heq hnd
  refine ⟨ψ, ?_, hψ⟩
  have hi : Tendsto (fun q : E ↦ (q, (0 : N))) (𝓝 q₀) (𝓝 (q₀, 0)) :=
    (continuous_id.prodMk continuous_const).tendsto q₀
  filter_upwards [hi.eventually hfix] with q hq using hq (hβ0 q)

/-- **The relative Darboux theorem** in adapted coordinates. Let `ω₀`, `ω₁` be closed `C^r`
two-forms (`r ≥ 1`) on an open subset `W` of `E × N` containing `(q₀, 0)`, both nondegenerate at
`(q₀, 0)`, with the same pullback to the zero section `E × {0}`. Then some `C^r` diffeomorphism `ψ`
of `E × N` fixes every point `(q, 0)` with `q` near `q₀` and pulls `ω₁` back to `ω₀` near `(q₀, 0)`.
The pullback to the zero section may be degenerate, of any rank. -/
theorem exists_diffeomorph_fix_zeroSection_eventually_compContinuousLinearMap_fderiv_eq
    {ω₀ ω₁ : E × N → (E × N) [⋀^Fin 2]→L[ℝ] ℝ} {W : Set (E × N)} {q₀ : E} {r : ℕ∞}
    (hr : 1 ≤ r) (hW : IsOpen W) (hq₀ : (q₀, (0 : N)) ∈ W) (hω₀ : ContDiffOn ℝ r ω₀ W)
    (hω₁ : ContDiffOn ℝ r ω₁ W) (hdω₀ : ∀ x ∈ W, extDeriv ω₀ x = 0)
    (hdω₁ : ∀ x ∈ W, extDeriv ω₁ x = 0)
    (htan : ∀ q : E, (q, (0 : N)) ∈ W →
      (ω₁ (q, 0)).compContinuousLinearMap (.inl ℝ E N) =
        (ω₀ (q, 0)).compContinuousLinearMap (.inl ℝ E N))
    (hnd₀ : ∀ v, (∀ w, ω₀ (q₀, 0) ![v, w] = 0) → v = 0)
    (hnd₁ : ∀ v, (∀ w, ω₁ (q₀, 0) ![v, w] = 0) → v = 0) :
    ∃ ψ : (E × N) ≃ₘ^r⟮𝓘(ℝ, E × N), 𝓘(ℝ, E × N)⟯ (E × N),
      (∀ᶠ q in 𝓝 q₀, ψ (q, 0) = (q, 0)) ∧
      ∀ᶠ x in 𝓝 (q₀, (0 : N)), (ω₁ (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x) = ω₀ x := by
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
    exact (lt_of_lt_of_le zero_lt_one this).ne'
  -- The values at `(q₀, 0)` as symplectic forms on `E × N`.
  let σ (a : (E × N) [⋀^Fin 2]→L[ℝ] ℝ) (ha : ∀ v, (∀ w, a ![v, w] = 0) → v = 0) :
      SymplecticForm (E × N) :=
    { toBilinForm := a.toAlternatingMap.toMultilinearMap.toBilinMap
      isAlt := a.toAlternatingMap.isAlt_toBilinMap
      nondegenerate :=
        (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
          (LinearMap.BilinForm.IsAlt.isRefl a.toAlternatingMap.isAlt_toBilinMap)).2
          fun v hv ↦ ha v fun w ↦ by simpa using hv w }
  have hσ (a) (ha) (v w : E × N) : σ a ha v w = a ![v, w] :=
    MultilinearMap.toBilinMap_apply _ v w
  -- Witt's extension theorem: the identity of the zero section extends to a linear
  -- symplectomorphism `A` from `ω₀ (q₀, 0)` to `ω₁ (q₀, 0)`.
  let S : Submodule ℝ (E × N) := LinearMap.range (LinearMap.inl ℝ E N)
  obtain ⟨e, he, heS⟩ := SymplecticForm.exists_isSymplectomorphism_extend
    (σ _ hnd₀) (σ _ hnd₁) rfl S.subtype S.injective_subtype fun x y ↦ by
      obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      have h := congrArg (fun c ↦ c ![a, b]) (htan q₀ hq₀)
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
      simp only [hσ, Submodule.coe_subtype, ← ha, ← hb]
      convert h using 2 <;> ext i <;> fin_cases i <;> rfl
  let A : (E × N) ≃L[ℝ] (E × N) := e.toContinuousLinearEquiv
  have hA (v w : E × N) : ω₁ (q₀, 0) ![A v, A w] = ω₀ (q₀, 0) ![v, w] :=
    ((hσ _ hnd₁ (e v) (e w)).symm.trans (he.apply v w)).trans (hσ _ hnd₀ v w)
  have hAinl (q : E) : A (q, 0) = (q, 0) := heS ⟨(q, 0), q, rfl⟩
  -- The pulled-back form `A^* ω₁` satisfies the hypotheses of the relative Moser step.
  let ω₁' : E × N → (E × N) [⋀^Fin 2]→L[ℝ] ℝ :=
    fun x ↦ (ω₁ (A x)).compContinuousLinearMap (A : (E × N) →L[ℝ] (E × N))
  have hω₁'_eq : ω₁' = fun x ↦ (ω₁ (A x)).compContinuousLinearMap (fderiv ℝ A x) := by
    funext x
    rw [A.fderiv]
  have hW' : IsOpen (W ∩ A ⁻¹' W) := hW.inter (hW.preimage A.continuous)
  have hq₀' : (q₀, (0 : N)) ∈ W ∩ A ⁻¹' W := ⟨hq₀, by rw [mem_preimage, hAinl]; exact hq₀⟩
  have hω₁' : ContDiffOn ℝ r ω₁' (W ∩ A ⁻¹' W) := by
    have h := (ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin 2) (F := ℝ)
      (A : (E × N) →L[ℝ] (E × N))).contDiff.comp_contDiffOn
      (hω₁.comp A.contDiff.contDiffOn fun x (hx : x ∈ W ∩ A ⁻¹' W) ↦ hx.2)
    exact h.congr fun x _ ↦
      (ContinuousAlternatingMap.compContinuousLinearMapCLM_apply _ _).symm
  have hdω₁' : ∀ x ∈ W ∩ A ⁻¹' W, extDeriv ω₁' x = 0 := fun x hx ↦ by
    rw [hω₁'_eq, extDeriv_pullback ((hω₁.differentiableOn hr0).differentiableAt (hW.mem_nhds hx.2))
      (A.contDiff (n := ⊤)).contDiffAt le_top, hdω₁ _ hx.2]
    ext v
    simp
  have htan' : ∀ q : E, (q, (0 : N)) ∈ W ∩ A ⁻¹' W →
      (ω₁' (q, 0)).compContinuousLinearMap (.inl ℝ E N) =
        (ω₀ (q, 0)).compContinuousLinearMap (.inl ℝ E N) := fun q hq ↦ by
    rw [← htan q hq.1]
    ext v
    simp only [ω₁', ContinuousAlternatingMap.compContinuousLinearMap_apply, hAinl]
    congr 1
    funext i
    simp [hAinl]
  have heq' : ω₁' (q₀, 0) = ω₀ (q₀, 0) := by
    ext v
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    simp only [ω₁', ContinuousAlternatingMap.compContinuousLinearMap_apply, hAinl]
    rw [← hA]
    congr 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨ψ, hfix, hψ⟩ :=
    exists_diffeomorph_fix_zeroSection_of_eq hr hW'
      hq₀' (hω₀.mono inter_subset_left) hω₁' (fun x hx ↦ hdω₀ x hx.1) hdω₁' htan' heq' hnd₀
  -- Compose with the linear symplectomorphism `A`.
  let Φ : (E × N) ≃ₘ^r⟮𝓘(ℝ, E × N), 𝓘(ℝ, E × N)⟯ (E × N) :=
    ψ.trans
      { toEquiv := A.toLinearEquiv.toEquiv
        contMDiff_toFun := A.contDiff.contMDiff
        contMDiff_invFun := A.symm.contDiff.contMDiff }
  have hΦ : ⇑Φ = A ∘ ψ := (rfl)
  refine ⟨Φ, ?_, ?_⟩
  · filter_upwards [hfix] with q hq
    rw [hΦ, Function.comp_apply, hq, hAinl]
  · filter_upwards [hψ] with x hx
    rw [← hx, hΦ, A.comp_fderiv]
    ext v
    simp [ω₁', Function.comp_def]

end TauCeti

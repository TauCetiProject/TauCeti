/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Dual.Bimodule
import TauCeti.Analysis.Normed.Module.Dual.ClusterPt

/-!
# Basic closure and restriction lemmas for bounded derivations

Let `A` be a normed algebra acting on a seminormed space `E` through bounded bilinear maps
`L R : A →L[𝕜] E →L[𝕜] E`, and let `D` be a bounded derivation from `A` into a bounded bimodule
or a dual bimodule `E*`. This file provides basic algebraic and submodule-restriction tools:

* inner derivations satisfy the derivation law (`TauCeti.flip_sub_flip_mul_apply`), and
  subtracting an inner derivation from a bounded derivation preserves it
  (`TauCeti.sub_flip_sub_flip_mul_apply`);
* restricting the values of a dual-valued bounded derivation to a jointly invariant submodule `p`
  preserves the derivation law for the restricted actions
  (`Submodule.precomp_subtypeL_comp_mul_apply`);
* when the restriction to a jointly invariant submodule `p` is inner, Hahn–Banach extension
  produces a bounded derivation `D₁` annihilating `p` such that `D` equals `D₁` plus an inner
  derivation (`TauCeti.exists_eq_add_dualAction_sub_dualAction_of_restrict`);
* when `A` has a bounded right approximate identity, any bounded derivation into `E*` annihilating
  all left action products `L b x` is inner
  (`TauCeti.exists_eq_dualAction_sub_dualAction_of_forall_apply_left_eq_zero`).

## Main results

* `TauCeti.flip_sub_flip_mul_apply` and `TauCeti.sub_flip_sub_flip_mul_apply`: inner derivations
  satisfy the derivation law, and bounded derivations are closed under subtracting inner
  derivations.
* `Submodule.precomp_subtypeL_comp_mul_apply`: restricting a dual-valued derivation to a jointly
  invariant submodule preserves its Leibniz law.
* `TauCeti.exists_eq_add_dualAction_sub_dualAction_of_restrict`: Hahn–Banach reduction of a bounded
  derivation that is inner on a jointly invariant submodule to a derivation vanishing on that
  submodule plus an inner derivation.
* `TauCeti.exists_eq_dualAction_sub_dualAction_of_forall_apply_left_eq_zero`: weak-star innerness
  for a bounded derivation into `E*` annihilating all left action products over an algebra with a
  bounded right approximate identity.
-/

public section

noncomputable section

open Filter Topology ContinuousLinearMap

namespace TauCeti

section DerivationHelpers

variable {𝕜 A E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup A] [NormedSpace 𝕜 A] [Mul A]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An inner derivation `a ↦ L a x - R a x` into a bounded bimodule satisfies the derivation
law. -/
theorem flip_sub_flip_mul_apply {L R : A →L[𝕜] F →L[𝕜] F}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (x : F) (a b : A) :
    (L.flip x - R.flip x) (a * b) =
      L a ((L.flip x - R.flip x) b) + R b ((L.flip x - R.flip x) a) := by
  simp only [sub_apply, flip_apply, map_sub, hL, hR, hLR]
  abel

/-- Subtracting an inner derivation from a bounded derivation into a bounded bimodule yields a
bounded derivation. -/
theorem sub_flip_sub_flip_mul_apply {L R : A →L[𝕜] F →L[𝕜] F}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) {D : A →L[𝕜] F}
    (hD : ∀ a b, D (a * b) = L a (D b) + R b (D a)) (x : F) (a b : A) :
    (D - (L.flip x - R.flip x)) (a * b) =
      L a ((D - (L.flip x - R.flip x)) b) + R b ((D - (L.flip x - R.flip x)) a) := by
  simp only [sub_apply, hD a b, flip_sub_flip_mul_apply hL hR hLR x a b, map_sub]
  abel

/-- Restricting the values of a dual-valued bounded derivation to any jointly invariant submodule
preserves its Leibniz law for the restricted actions. -/
theorem _root_.Submodule.precomp_subtypeL_comp_mul_apply {L R : A →L[𝕜] E →L[𝕜] E}
    (p : Submodule 𝕜 E)
    (hLp : ∀ a, ∀ x ∈ p, L a x ∈ p) (hRp : ∀ a, ∀ x ∈ p, R a x ∈ p)
    {D : A →L[𝕜] StrongDual 𝕜 E}
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) (a b : A) :
    ((precomp 𝕜 p.subtypeL) ∘L D) (a * b) =
      dualAction (R.restrictAction p hRp) a (((precomp 𝕜 p.subtypeL) ∘L D) b) +
        dualAction (L.restrictAction p hLp) b (((precomp 𝕜 p.subtypeL) ∘L D) a) := by
  simp only [comp_apply, hD, map_add, precomp_apply, dualAction_restrictAction_comp_subtypeL]

/-- If a bounded derivation `D : A →L[𝕜] E*` restricts to an inner derivation on a jointly invariant
submodule `p`, Hahn–Banach produces a bounded derivation `D₁` annihilating `p` and an element
`ψ : E*` with `D a = D₁ a + (dualAction R a ψ - dualAction L a ψ)`. -/
theorem exists_eq_add_dualAction_sub_dualAction_of_restrict [IsRCLikeNormedField 𝕜]
    {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    (p : Submodule 𝕜 E) (hLp : ∀ a, ∀ x ∈ p, L a x ∈ p) (hRp : ∀ a, ∀ x ∈ p, R a x ∈ p)
    {D : A →L[𝕜] StrongDual 𝕜 E}
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a))
    (hp : ∃ ψ₀ : StrongDual 𝕜 p,
      ∀ a, (D a).comp p.subtypeL =
        dualAction (R.restrictAction p hRp) a ψ₀ -
        dualAction (L.restrictAction p hLp) a ψ₀) :
    ∃ (ψ : StrongDual 𝕜 E) (D₁ : A →L[𝕜] StrongDual 𝕜 E),
      (∀ a b, D₁ (a * b) = dualAction R a (D₁ b) + dualAction L b (D₁ a)) ∧
      (∀ a, ∀ x ∈ p, D₁ a x = 0) ∧
      (∀ a, D a = D₁ a + (dualAction R a ψ - dualAction L a ψ)) := by
  obtain ⟨ψ₀, hψ₀⟩ := hp
  obtain ⟨ψ, hψ⟩ := StrongDual.exists_extension p ψ₀
  have hψ_comp : ψ.comp p.subtypeL = ψ₀ := by ext x; exact hψ x
  refine ⟨ψ, D - ((dualAction R).flip ψ - (dualAction L).flip ψ),
    sub_flip_sub_flip_mul_apply (dualAction_mul_apply_of_right hR) (dualAction_mul_apply_of_left hL)
      (dualAction_apply_dualAction_apply_comm hLR) hD ψ,
    fun a x hx ↦ ?_, fun a ↦ ?_⟩
  · have hcomp : (D a - (dualAction R a ψ - dualAction L a ψ)).comp p.subtypeL = 0 := by
      rw [sub_comp, sub_comp, hψ₀ a, ← dualAction_restrictAction_comp_subtypeL R p hRp a ψ,
        ← dualAction_restrictAction_comp_subtypeL L p hLp a ψ, hψ_comp, sub_self]
    simpa only [sub_apply, flip_apply, comp_apply, Submodule.subtypeL_apply, zero_apply] using
      congrArg (fun f : StrongDual 𝕜 p ↦ f ⟨x, hx⟩) hcomp
  · simp

/-- Weak-star residual innerness: if `A` has a bounded right approximate identity, then any
bounded derivation `D : A →L[𝕜] E*` annihilating all left action products `L b x` is inner. -/
theorem exists_eq_dualAction_sub_dualAction_of_forall_apply_left_eq_zero
    [IsRCLikeNormedField 𝕜] {L R : A →L[𝕜] E →L[𝕜] E}
    {l : Filter A} [l.NeBot] {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ a, Tendsto (a * ·) l (𝓝 a))
    (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a))
    (hD_L : ∀ a b x, D a (L b x) = 0) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  have : ProperSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  -- Since `D a (L b x) = 0`, we have `D a · b = 0` and hence `D (a * b) = a · D b`.
  have hD_mul (a b : A) (x : E) : D (a * b) x = D b (R a x) := by
    have h := congr($(hD a b) x)
    simp only [add_apply, dualAction_apply_apply, hD_L, add_zero] at h
    exact h
  -- Take a weak-star limit `φ` of `D e` along an ultrafilter finer than `l`.
  have hC₁ : ∀ᶠ e in Ultrafilter.of l, ‖D e‖ ≤ ‖D‖ * C :=
    mem_of_superset (Ultrafilter.of_le l hC) fun e he ↦
      (D.le_opNorm e).trans (mul_le_mul_of_nonneg_left he (norm_nonneg D))
  obtain ⟨φ, -, hφ⟩ := (Ultrafilter.of l).exists_tendsto_toWeakDual D hC₁
  have hφ_eval (x : E) : Tendsto (fun e ↦ D e x) (Ultrafilter.of l) (𝓝 (φ x)) :=
    ((WeakDual.eval_continuous x).tendsto (StrongDual.toWeakDual φ)).comp hφ
  have hφR (a : A) (x : E) : φ (R a x) = D a x := by
    refine tendsto_nhds_unique (hφ_eval (R a x)) ?_
    have hlim : Tendsto (fun e ↦ D (a * e) x) (Ultrafilter.of l) (𝓝 (D a x)) :=
      (((ContinuousLinearMap.apply 𝕜 𝕜 x).continuous.tendsto (D a)).comp
        ((D.continuous.tendsto a).comp (hl a))).mono_left (Ultrafilter.of_le l)
    exact hlim.congr fun e ↦ hD_mul a e x
  have hφL (a : A) (x : E) : φ (L a x) = 0 := by
    refine tendsto_nhds_unique (hφ_eval (L a x)) ?_
    simp [hD_L _ a x]
  refine ⟨φ, fun a ↦ ?_⟩
  ext x
  simp only [sub_apply, dualAction_apply_apply, hφR, hφL, sub_zero]

end DerivationHelpers

end TauCeti

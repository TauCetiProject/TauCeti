/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ApproximateUnit
public import TauCeti.Analysis.Normed.Algebra.Derivation.Basic
public import TauCeti.Analysis.Normed.Module.Essential
import TauCeti.Analysis.Normed.Module.Dual.ClusterPt
import TauCeti.Topology.ApproximateUnit

/-!
# Essential-module reductions for bounded derivations

Let `A` be a normed algebra with a bounded approximate identity, and let `E` be a bounded
`A`-bimodule with left action `L` and right action `R`. Write `E_L = L.essentialSubmodule` and
`E_R = R.essentialSubmodule` for the one-sided essential submodules, and
`E_ess = essentialBimoduleSubmodule L R` for the two-sided essential submodule (the closed linear
span of `A · E · A`, which coincides with `E_L ⊓ E_R` in the presence of a bounded approximate
identity).

Using the basic derivation restriction and Hahn–Banach residual lemmas from
`TauCeti.Analysis.Normed.Algebra.Derivation.Basic`, this file proves the classical reductions of
innerness for bounded derivations into dual bimodules to essential submodules (Runde, Proposition
2.1.5):

1. **Left-essential reduction.** Given a bounded right approximate identity, a bounded derivation
   `D : A →L[𝕜] E*` is inner as soon as its restriction to `E_L` is inner. Extending the
   implementing functional from `E_L` to `E` by Hahn–Banach leaves a residual derivation `D₁`
   annihilating `E_L`, so `D₁ a · b = 0` and hence `D₁ (a * b) = a · D₁ b`; any weak-star limit of
   `D₁ e` along an ultrafilter finer than the approximate identity implements `D₁`.
2. **Right-essential reduction.** After the same Hahn–Banach reduction on `E_R`, transporting only
   the residual derivation to the opposite algebra `Aᵐᵒᵖ` reduces directly to the weak-star
   residual innerness lemma.
3. **Two-sided reduction.** Applying the left- and right-essential reductions successively shows
   that in the presence of a bounded two-sided approximate identity, `D` is inner as soon as its
   restriction to `E_ess = E_L ⊓ E_R` is inner.

## Main results

* `TauCeti.exists_eq_dualAction_sub_dualAction_of_restrict_leftEssential` and
  `TauCeti.exists_eq_dualAction_sub_dualAction_of_restrict_rightEssential`: one-sided essential
  reductions for bounded derivations into dual bimodules.
* `TauCeti.exists_eq_dualAction_sub_dualAction_of_restrict_essential`: full reduction of a bounded
  derivation into a dual bimodule to the essential part `essentialBimoduleSubmodule L R`.

## References

* V. Runde, *Lectures on Amenability*, Springer, 2002, Proposition 2.1.5.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.8.
-/

public section

noncomputable section

open Filter Topology Submodule ContinuousLinearMap

namespace TauCeti

section Reduction

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NonUnitalSeminormedRing A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {L R : A →L[𝕜] E →L[𝕜] E}

/-- Weak-star residual innerness: if `A` has a bounded right approximate identity, then any
bounded derivation `D₁ : A →L[𝕜] E*` annihilating all left action products `L b x` is inner. -/
private theorem exists_eq_dualAction_sub_dualAction_of_forall_apply_left_eq_zero
    {l : Filter A} [l.NeBot] {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ a, Tendsto (a * ·) l (𝓝 a))
    (D₁ : A →L[𝕜] StrongDual 𝕜 E)
    (hD₁ : ∀ a b, D₁ (a * b) = dualAction R a (D₁ b) + dualAction L b (D₁ a))
    (hD₁_L : ∀ a b x, D₁ a (L b x) = 0) :
    ∃ φ₁ : StrongDual 𝕜 E, ∀ a, D₁ a = dualAction R a φ₁ - dualAction L a φ₁ := by
  have : ProperSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  -- Since `D₁ a (L b x) = 0`, we have `D₁ a · b = 0` and hence `D₁ (a * b) = a · D₁ b`.
  have hD₁_mul (a b : A) (x : E) : D₁ (a * b) x = D₁ b (R a x) := by
    have h := congr($(hD₁ a b) x)
    simp only [add_apply, dualAction_apply_apply, hD₁_L, add_zero] at h
    exact h
  -- Take a weak-star limit `φ₁` of `D₁ e` along an ultrafilter finer than `l`.
  have hC₁ : ∀ᶠ e in Ultrafilter.of l, ‖D₁ e‖ ≤ ‖D₁‖ * C :=
    mem_of_superset (Ultrafilter.of_le l hC) fun e he ↦
      (D₁.le_opNorm e).trans (mul_le_mul_of_nonneg_left he (norm_nonneg D₁))
  obtain ⟨φ₁, -, hφ₁⟩ := (Ultrafilter.of l).exists_tendsto_toWeakDual D₁ hC₁
  have hφ₁_eval (x : E) : Tendsto (fun e ↦ D₁ e x) (Ultrafilter.of l) (𝓝 (φ₁ x)) :=
    ((WeakDual.eval_continuous x).tendsto (StrongDual.toWeakDual φ₁)).comp hφ₁
  have hφ₁R (a : A) (x : E) : φ₁ (R a x) = D₁ a x := by
    refine tendsto_nhds_unique (hφ₁_eval (R a x)) ?_
    have hlim : Tendsto (fun e ↦ D₁ (a * e) x) (Ultrafilter.of l) (𝓝 (D₁ a x)) :=
      (((D₁.continuous.clm_apply (continuous_const (y := x))).tendsto a).comp (hl a)).mono_left
        (Ultrafilter.of_le l)
    exact hlim.congr fun e ↦ hD₁_mul a e x
  have hφ₁L (a : A) (x : E) : φ₁ (L a x) = 0 := by
    refine tendsto_nhds_unique (hφ₁_eval (L a x)) ?_
    simp [hD₁_L _ a x]
  refine ⟨φ₁, fun a ↦ ?_⟩
  ext x
  simp only [sub_apply, dualAction_apply_apply, hφ₁R, hφ₁L, sub_zero]

/-- **Left-essential reduction.** If `A` has a bounded right approximate identity, then a bounded
derivation `D : A →L[𝕜] E*` is inner as soon as its restriction to the left-essential part
`L.essentialSubmodule` is inner. -/
theorem exists_eq_dualAction_sub_dualAction_of_restrict_leftEssential
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    {l : Filter A} [l.NeBot] {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ a, Tendsto (a * ·) l (𝓝 a))
    (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a))
    (hEL : ∃ ψ₀ : StrongDual 𝕜 L.essentialSubmodule,
      ∀ a, (D a).comp L.essentialSubmodule.subtypeL =
        dualAction (R.restrictAction L.essentialSubmodule fun a _ hx ↦
          apply_mem_essentialSubmodule_of_comm hLR a hx) a ψ₀ -
        dualAction (L.restrictAction L.essentialSubmodule fun a x _ ↦
          apply_mem_essentialSubmodule L a x) a ψ₀) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  have hL_inv : ∀ a, ∀ x ∈ L.essentialSubmodule, L a x ∈ L.essentialSubmodule :=
    fun a x _ ↦ apply_mem_essentialSubmodule L a x
  have hR_inv : ∀ a, ∀ x ∈ L.essentialSubmodule, R a x ∈ L.essentialSubmodule :=
    fun a _ hx ↦ apply_mem_essentialSubmodule_of_comm hLR a hx
  obtain ⟨ψ, D₁, hD₁, hD₁_EL, hD_eq⟩ :=
    exists_residual_derivation_of_restrict hL hR hLR L.essentialSubmodule hL_inv hR_inv hD hEL
  obtain ⟨φ₁, hφ₁⟩ := exists_eq_dualAction_sub_dualAction_of_forall_apply_left_eq_zero hC hl D₁
    hD₁ fun a b x ↦ hD₁_EL a (L b x) (apply_mem_essentialSubmodule L b x)
  refine ⟨ψ + φ₁, fun a ↦ ?_⟩
  ext x
  have hDa := congr($(hD_eq a) x)
  have hD₁a := congr($(hφ₁ a) x)
  simp only [add_apply, sub_apply, dualAction_apply_apply] at hDa hD₁a ⊢
  rw [hDa, hD₁a]
  ring

/-- **Right-essential reduction.** If `A` has a bounded left approximate identity, then a bounded
derivation `D : A →L[𝕜] E*` is inner as soon as its restriction to the right-essential part
`R.essentialSubmodule` is inner. -/
theorem exists_eq_dualAction_sub_dualAction_of_restrict_rightEssential
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    {l : Filter A} [l.NeBot] {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ a, Tendsto (· * a) l (𝓝 a))
    (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a))
    (hER : ∃ ψ₀ : StrongDual 𝕜 R.essentialSubmodule,
      ∀ a, (D a).comp R.essentialSubmodule.subtypeL =
        dualAction (R.restrictAction R.essentialSubmodule fun a x _ ↦
          apply_mem_essentialSubmodule R a x) a ψ₀ -
        dualAction (L.restrictAction R.essentialSubmodule fun a _ hx ↦
          apply_mem_essentialSubmodule_of_comm (fun b c y ↦ (hLR c b y).symm) a hx) a ψ₀) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  have hL_inv : ∀ a, ∀ x ∈ R.essentialSubmodule, L a x ∈ R.essentialSubmodule :=
    fun a _ hx ↦ apply_mem_essentialSubmodule_of_comm (fun b c y ↦ (hLR c b y).symm) a hx
  have hR_inv : ∀ a, ∀ x ∈ R.essentialSubmodule, R a x ∈ R.essentialSubmodule :=
    fun a x _ ↦ apply_mem_essentialSubmodule R a x
  obtain ⟨ψ, D₁, hD₁, hD₁_ER, hD_eq⟩ :=
    exists_residual_derivation_of_restrict hL hR hLR R.essentialSubmodule hL_inv hR_inv hD hER
  let Lop : Aᵐᵒᵖ →L[𝕜] E →L[𝕜] E := R.compUnop
  let Rop : Aᵐᵒᵖ →L[𝕜] E →L[𝕜] E := L.compUnop
  let D₁op : Aᵐᵒᵖ →L[𝕜] StrongDual 𝕜 E := D₁.compUnop
  have hD₁op (a b : Aᵐᵒᵖ) :
      D₁op (a * b) = dualAction Rop a (D₁op b) + dualAction Lop b (D₁op a) := by
    ext x
    simp only [D₁op, Lop, Rop, compUnop_apply, MulOpposite.unop_mul, hD₁, add_apply,
      dualAction_apply_apply]
    exact add_comm _ _
  obtain ⟨φ₁, hφ₁⟩ := exists_eq_dualAction_sub_dualAction_of_forall_apply_left_eq_zero
    (L := Lop) (R := Rop) (l := l.map MulOpposite.op) (Filter.eventually_map.2 hC)
    (tendsto_mul_left_map_op hl) D₁op hD₁op
    fun a b x ↦ by
      simpa only [D₁op, Lop, compUnop_apply] using
        hD₁_ER a.unop (R b.unop x) (apply_mem_essentialSubmodule R b.unop x)
  refine ⟨ψ - φ₁, fun a ↦ ?_⟩
  ext x
  have hDa := congr($(hD_eq a) x)
  have hD₁a := congr($(hφ₁ (MulOpposite.op a)) x)
  simp only [D₁op, Rop, Lop, compUnop_apply, MulOpposite.unop_op,
    sub_apply, add_apply, dualAction_apply_apply] at hDa hD₁a ⊢
  rw [hDa, hD₁a]
  ring

/-- **Essential-part reduction for a bounded derivation.** If `A` has a bounded two-sided
approximate identity, then a bounded derivation `D : A →L[𝕜] E*` is inner as soon as its
restriction to the essential part `essentialBimoduleSubmodule L R` is inner. -/
theorem exists_eq_dualAction_sub_dualAction_of_restrict_essential
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    {l : Filter A} (hl : l.IsApproximateUnit) {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a))
    (hEss : ∃ ψ₀ : StrongDual 𝕜 (essentialBimoduleSubmodule L R),
      ∀ a, (D a).comp (essentialBimoduleSubmodule L R).subtypeL =
        dualAction (R.restrictAction (essentialBimoduleSubmodule L R) fun a _ hx ↦
          apply_right_mem_essentialBimoduleSubmodule hR hLR a hx) a ψ₀ -
        dualAction (L.restrictAction (essentialBimoduleSubmodule L R) fun a _ hx ↦
          apply_left_mem_essentialBimoduleSubmodule hL a hx) a ψ₀) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  have := hl.neBot
  let EL := L.essentialSubmodule
  have hLL_inv : ∀ a, ∀ x ∈ EL, L a x ∈ EL := fun a x _ ↦ apply_mem_essentialSubmodule L a x
  have hRL_inv : ∀ a, ∀ x ∈ EL, R a x ∈ EL :=
    fun a _ hx ↦ apply_mem_essentialSubmodule_of_comm hLR a hx
  let LL : A →L[𝕜] EL →L[𝕜] EL := L.restrictAction EL hLL_inv
  let RL : A →L[𝕜] EL →L[𝕜] EL := R.restrictAction EL hRL_inv
  have hLL : ∀ a b x, LL (a * b) x = LL a (LL b x) :=
    L.restrictAction_mul_apply_of_left hL EL hLL_inv
  have hRL : ∀ a b x, RL (a * b) x = RL b (RL a x) :=
    R.restrictAction_mul_apply_of_right hR EL hRL_inv
  have hLRL : ∀ a b x, LL a (RL b x) = RL b (LL a x) :=
    restrictAction_apply_comm hLR EL hLL_inv hRL_inv
  -- Step 1: reduce `E` to `EL`.
  let DL : A →L[𝕜] StrongDual 𝕜 EL := (precomp 𝕜 EL.subtypeL) ∘L D
  have hDL := precomp_subtypeL_comp_derivation EL hLL_inv hRL_inv hD
  suffices ∃ ψL : StrongDual 𝕜 EL, ∀ a, DL a = dualAction RL a ψL - dualAction LL a ψL by
    obtain ⟨ψL, hψL⟩ := this
    exact exists_eq_dualAction_sub_dualAction_of_restrict_leftEssential hL hR hLR hC
      hl.tendsto_mul_left D hD
      ⟨ψL, fun a ↦ by simpa only [DL, comp_apply, precomp_apply] using hψL a⟩
  -- Step 2: reduce `EL` to its right-essential part `RL.essentialSubmodule`, which embeds into
  -- `essentialBimoduleSubmodule L R`.
  refine exists_eq_dualAction_sub_dualAction_of_restrict_rightEssential hLL hRL hLRL hC
    hl.tendsto_mul_right DL hDL ?_
  obtain ⟨ι, hι_coe, hιR, hιL⟩ :=
    exists_continuousLinearMap_restrictAction_essentialBimoduleSubmodule hL hR hLR
  obtain ⟨ψ₀, hψ₀⟩ := hEss
  refine ⟨precomp 𝕜 ι ψ₀, fun a ↦ ?_⟩
  have h1 : (DL a).comp RL.essentialSubmodule.subtypeL =
      precomp 𝕜 ι ((D a).comp (essentialBimoduleSubmodule L R).subtypeL) := by
    ext x
    simp only [DL, comp_apply, precomp_apply, Submodule.subtypeL_apply, hι_coe]
  rw [h1, hψ₀ a, map_sub, precomp_dualAction_apply hιR, precomp_dualAction_apply hιL]

end Reduction

end TauCeti

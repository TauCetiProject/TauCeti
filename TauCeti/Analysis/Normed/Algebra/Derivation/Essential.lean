/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Derivation.Basic
public import TauCeti.Analysis.Normed.Module.Essential
import TauCeti.Analysis.Normed.Module.Dual.ClusterPt

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
2. **Right-essential reduction.** Transporting to the opposite algebra `Aᵐᵒᵖ` reduces the symmetric
   statement for a bounded left approximate identity and `E_R` directly to the left-essential
   reduction.
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

/-- Lift an ambient intertwining identity `T (M₁ a x) = M₂ b (T x)` to restricted actions along a
map `ι : p₁ → p₂` compatible with the subtype inclusions (`(ι x : E₂) = T (x : E₁)`). -/
private theorem restrictAction_intertwine {𝕜 B₁ B₂ E₁ E₂ : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup B₁] [NormedSpace 𝕜 B₁]
    [SeminormedAddCommGroup B₂] [NormedSpace 𝕜 B₂]
    [SeminormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    [SeminormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    {M₁ : B₁ →L[𝕜] E₁ →L[𝕜] E₁} {M₂ : B₂ →L[𝕜] E₂ →L[𝕜] E₂}
    {p₁ : Submodule 𝕜 E₁} {p₂ : Submodule 𝕜 E₂}
    {hp₁ : ∀ a x, x ∈ p₁ → M₁ a x ∈ p₁} {hp₂ : ∀ b y, y ∈ p₂ → M₂ b y ∈ p₂}
    {ι : p₁ → p₂} (T : E₁ → E₂) (hι : ∀ x : p₁, (ι x : E₂) = T (x : E₁))
    {a : B₁} {b : B₂} (hM : ∀ x : E₁, T (M₁ a x) = M₂ b (T x)) (x : p₁) :
    ι (M₁.restrictAction p₁ hp₁ a x) = M₂.restrictAction p₂ hp₂ b (ι x) :=
  Subtype.ext <| by
    rw [hι, coe_restrictAction_apply, hM, ← hι, coe_restrictAction_apply]

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [ProperSpace 𝕜]
  [NonUnitalSeminormedRing A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {L R : A →L[𝕜] E →L[𝕜] E}

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
  -- Since `L b x ∈ L.essentialSubmodule`, `D₁ a · b = 0` and hence `D₁ (a * b) = a · D₁ b`.
  have hD₁_mul (a b : A) (x : E) : D₁ (a * b) x = D₁ b (R a x) := by
    have h := congr($(hD₁ a b) x)
    have h0 : D₁ a (L b x) = 0 := hD₁_EL a (L b x) (apply_mem_essentialSubmodule L b x)
    simp only [add_apply, dualAction_apply_apply, h0, add_zero] at h
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
    simp [hD₁_EL _ (L a x) (apply_mem_essentialSubmodule L a x)]
  refine ⟨ψ + φ₁, fun a ↦ ?_⟩
  ext x
  have hDa := congr($(hD_eq a) x)
  simp only [add_apply, sub_apply, dualAction_apply_apply, hφ₁R, hφ₁L] at hDa ⊢
  rw [hDa]
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
  let unopL : Aᵐᵒᵖ →L[𝕜] A := (MulOpposite.opContinuousLinearEquiv 𝕜 (M := A)).symm
  let Lop : Aᵐᵒᵖ →L[𝕜] E →L[𝕜] E := R.comp unopL
  let Rop : Aᵐᵒᵖ →L[𝕜] E →L[𝕜] E := L.comp unopL
  have hLop (a b : Aᵐᵒᵖ) (x : E) : Lop (a * b) x = Lop a (Lop b x) := by
    simp [Lop, unopL, hR]
  have hRop (a b : Aᵐᵒᵖ) (x : E) : Rop (a * b) x = Rop b (Rop a x) := by
    simp [Rop, unopL, hL]
  have hLRop (a b : Aᵐᵒᵖ) (x : E) : Lop a (Rop b x) = Rop b (Lop a x) := by
    simp [Lop, Rop, unopL, hLR]
  have hCop : ∀ᶠ e in l.map MulOpposite.op, ‖e‖ ≤ C :=
    eventually_map.2 <| hC.mono fun e he ↦ by rw [MulOpposite.norm_op]; exact he
  have hlop : ∀ a : Aᵐᵒᵖ, Tendsto (a * ·) (l.map MulOpposite.op) (𝓝 a) := fun a ↦ by
    rw [tendsto_map'_iff]
    simpa only [Function.comp_def, MulOpposite.op_mul, MulOpposite.op_unop] using
      (MulOpposite.continuous_op.tendsto a.unop).comp (hl a.unop)
  let Dop : Aᵐᵒᵖ →L[𝕜] StrongDual 𝕜 E := D.comp unopL
  have hDop (a b : Aᵐᵒᵖ) :
      Dop (a * b) = dualAction Rop a (Dop b) + dualAction Lop b (Dop a) := by
    ext x
    simp only [Dop, Lop, Rop, unopL, comp_apply, ContinuousLinearEquiv.coe_coe,
      MulOpposite.opContinuousLinearEquiv_symm_apply, MulOpposite.unop_mul, hD, add_apply,
      dualAction_apply_apply]
    exact add_comm _ _
  have hE_eq : Lop.essentialSubmodule = R.essentialSubmodule := by
    have hset : Set.range (fun p : Aᵐᵒᵖ × E ↦ Lop p.1 p.2) =
        Set.range fun p : A × E ↦ R p.1 p.2 :=
      (MulOpposite.unop_surjective.prodMap Function.surjective_id).range_comp
        (fun p : A × E ↦ R p.1 p.2)
    simp only [essentialSubmodule_eq_topologicalClosure_span, hset]
  obtain ⟨ψ₀, hψ₀⟩ := hER
  let eSub : Lop.essentialSubmodule →L[𝕜] R.essentialSubmodule :=
    (LinearIsometryEquiv.ofEq _ _ hE_eq).toLinearIsometry.toContinuousLinearMap
  have heSub_coe (x : Lop.essentialSubmodule) : (eSub x : E) = (x : E) :=
    LinearIsometryEquiv.coe_ofEq_apply hE_eq x
  obtain ⟨φ, hφ⟩ := exists_eq_dualAction_sub_dualAction_of_restrict_leftEssential
    hLop hRop hLRop hCop hlop Dop hDop ⟨-(ψ₀.comp eSub), fun a ↦ by
      ext x
      have hx := congr($(hψ₀ a.unop) (eSub x))
      have hRe :
          eSub (Lop.restrictAction Lop.essentialSubmodule (fun a x _ ↦
              apply_mem_essentialSubmodule Lop a x) a x) =
            R.restrictAction R.essentialSubmodule (fun a x _ ↦
              apply_mem_essentialSubmodule R a x) a.unop (eSub x) :=
        restrictAction_intertwine id heSub_coe (fun y ↦ by simp [Lop, unopL]) x
      have hLe :
          eSub (Rop.restrictAction Lop.essentialSubmodule (fun a _ hx ↦
              apply_mem_essentialSubmodule_of_comm hLRop a hx) a x) =
            L.restrictAction R.essentialSubmodule (fun a _ hx ↦
              apply_mem_essentialSubmodule_of_comm (fun b c y ↦ (hLR c b y).symm) a hx) a.unop
              (eSub x) :=
        restrictAction_intertwine id heSub_coe (fun y ↦ by simp [Rop, unopL]) x
      simp only [comp_apply, Submodule.subtypeL_apply, heSub_coe, sub_apply,
        dualAction_apply_apply, neg_apply, Dop, unopL, ContinuousLinearEquiv.coe_coe,
        MulOpposite.opContinuousLinearEquiv_symm_apply] at hx ⊢
      rw [hx, ← hRe, ← hLe]
      abel⟩
  refine ⟨-φ, fun a ↦ ?_⟩
  ext x
  have hax := congr($(hφ (MulOpposite.op a)) x)
  simp only [Dop, comp_apply, unopL, ContinuousLinearEquiv.coe_coe,
    MulOpposite.opContinuousLinearEquiv_symm_apply, MulOpposite.unop_op, Rop, Lop,
    sub_apply, dualAction_apply_apply] at hax
  simp only [sub_apply, dualAction_apply_apply, neg_apply, hax]
  abel

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
      hl.tendsto_mul_left D hD ⟨ψL, hψL⟩
  -- Step 2: reduce `EL` to its right-essential part `ELR`, which maps into
  -- `essentialBimoduleSubmodule L R`.
  refine exists_eq_dualAction_sub_dualAction_of_restrict_rightEssential hLL hRL hLRL hC
    hl.tendsto_mul_right DL hDL ?_
  let ELR := RL.essentialSubmodule
  have hELR_mem (x : ELR) :
      (EL.subtypeL.comp ELR.subtypeL) x ∈ essentialBimoduleSubmodule L R := by
    simp only [comp_apply, Submodule.subtypeL_apply]
    rw [essentialBimoduleSubmodule_eq_inf hR hLR hC hl.tendsto_mul_left]
    refine ⟨x.val.property, ?_⟩
    exact (essentialSubmodule_le_iff (M := RL) (p := R.essentialSubmodule.comap EL.subtype)
      ((isClosed_essentialSubmodule R).preimage continuous_subtypeVal)).2
      (fun a y ↦ by
        simp only [Submodule.mem_comap, Submodule.coe_subtype, RL, coe_restrictAction_apply]
        exact apply_mem_essentialSubmodule R a y.val)
      x.property
  let ι : ELR →L[𝕜] essentialBimoduleSubmodule L R :=
    (EL.subtypeL.comp ELR.subtypeL).codRestrict (essentialBimoduleSubmodule L R) hELR_mem
  have hι_coe (x : ELR) : (ι x : E) = (x.val : E) := by
    simp only [ι, coe_codRestrict_apply, comp_apply, Submodule.subtypeL_apply]
  have hιR (a : A) (x : ELR) :
      ι (RL.restrictAction ELR (fun a y _ ↦ apply_mem_essentialSubmodule RL a y) a x) =
        R.restrictAction (essentialBimoduleSubmodule L R)
          (fun a _ hx ↦ apply_right_mem_essentialBimoduleSubmodule hR hLR a hx) a (ι x) :=
    restrictAction_intertwine EL.subtype hι_coe
      (fun y ↦ coe_restrictAction_apply R EL hRL_inv a y) x
  have hιL (a : A) (x : ELR) :
      ι (LL.restrictAction ELR (fun a _ hy ↦
          apply_mem_essentialSubmodule_of_comm (fun b c y ↦ (hLRL c b y).symm) a hy) a x) =
        L.restrictAction (essentialBimoduleSubmodule L R)
          (fun a _ hx ↦ apply_left_mem_essentialBimoduleSubmodule hL a hx) a (ι x) :=
    restrictAction_intertwine EL.subtype hι_coe
      (fun y ↦ coe_restrictAction_apply L EL hLL_inv a y) x
  obtain ⟨ψ₀, hψ₀⟩ := hEss
  refine ⟨precomp 𝕜 ι ψ₀, fun a ↦ ?_⟩
  have h1 : (DL a).comp ELR.subtypeL =
      precomp 𝕜 ι ((D a).comp (essentialBimoduleSubmodule L R).subtypeL) := by
    ext x
    simp only [DL, comp_apply, precomp_apply, Submodule.subtypeL_apply, hι_coe]
  rw [h1, hψ₀ a, map_sub, precomp_dualAction_apply hιR, precomp_dualAction_apply hιL]

end Reduction

end TauCeti

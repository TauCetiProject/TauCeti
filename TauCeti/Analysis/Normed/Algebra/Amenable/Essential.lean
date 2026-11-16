/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Amenable.Basic
public import TauCeti.Analysis.Normed.Module.Essential
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Reduction of amenability to essential bimodules

Let `A` be a normed algebra with a bounded two-sided approximate identity, and let `E` be a bounded
`A`-bimodule with left action `L` and right action `R`. The left-essential part `E_L` is the closed
linear span of `A · E`, the right-essential part `E_R` is the closed linear span of `E · A`, and
the essential part `E_ess` is the closed linear span of `A · E · A`. Both `E_L` and `E_R` are
closed sub-bimodules of `E`, and in the presence of a bounded two-sided approximate identity
`E_ess = E_L ⊓ E_R` is itself both left- and right-essential.

This file proves the classical reduction of bounded derivations into dual bimodules to the
essential part (Runde, Proposition 2.1.5):

1. Given a bounded right approximate identity, a bounded derivation `D : A →L[𝕜] E*` is inner as
   soon as its restriction to `E_L` is inner. Extending the implementing functional from `E_L` to
   `E` by Hahn–Banach leaves a derivation `D₁` annihilating `E_L`, so `D₁ a · b = 0` and hence
   `D₁ (a * b) = a · D₁ b`; any weak-star limit of `D₁ e` along an ultrafilter finer than the
   approximate identity implements `D₁`.
2. Symmetrically, given a bounded left approximate identity, `D` is inner as soon as its
   restriction to `E_R` is inner.
3. Applying the two reductions successively (from `E` to `E_L`, and from `E_L` to its
   right-essential part `E_L ⊓ E_R`) shows that when `A` has a bounded two-sided approximate
   identity, `A` is amenable if and only if every bounded derivation into the dual of an essential
   Banach `A`-bimodule is inner.

## Main results

* `TauCeti.topologicalClosure_span_left_inf_right_eq`: with a bounded two-sided approximate
  identity, `E_L ⊓ E_R = closure (span (A · E · A))`.
* `TauCeti.exists_eq_dualAction_sub_dualAction_of_restrict_leftEssential` and
  `TauCeti.exists_eq_dualAction_sub_dualAction_of_restrict_rightEssential`: one-sided reductions
  for bounded derivations into dual bimodules.
* `TauCeti.exists_eq_dualAction_sub_dualAction_of_restrict_essential`: full reduction of a single
  bounded derivation to the essential part `E_L ⊓ E_R`.
* `TauCeti.isAmenable_iff_essential`: a normed algebra with a bounded two-sided approximate
  identity is amenable if and only if every bounded derivation into the dual of an essential
  Banach bimodule is inner.

## References

* V. Runde, *Lectures on Amenability*, Springer, 2002, Proposition 2.1.5.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.8.
-/

public section

noncomputable section

universe u v

open Filter Topology Submodule ContinuousLinearMap

namespace TauCeti

section EssentialPart

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {L R : A →L[𝕜] E →L[𝕜] E}

/-- In a bounded bimodule over a normed algebra with a bounded two-sided approximate identity, the
intersection of the left-essential and right-essential parts equals the closed linear span of
`A · E · A`. -/
theorem topologicalClosure_span_left_inf_right_eq
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) {l : Filter A} (hl : l.IsApproximateUnit)
    {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C) :
    (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure ⊓
        (span 𝕜 (Set.range fun p : A × E ↦ R p.1 p.2)).topologicalClosure =
      (span 𝕜 (Set.range fun p : A × A × E ↦ L p.1 (R p.2.1 p.2.2))).topologicalClosure := by
  have := hl.neBot
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxL, hxR⟩
    -- Along `l`, `L e (R e x) - x = L e (R e x - x) + (L e x - x) → 0`.
    have hLx := tendsto_apply_of_mem_topologicalClosure_span L hL hC hl.tendsto_mul_right hxL
    have hRx := tendsto_apply_of_mem_topologicalClosure_span_right R hR hC hl.tendsto_mul_left hxR
    have hLRx : Tendsto (fun e ↦ L e (R e x)) l (𝓝 x) := by
      rw [tendsto_iff_norm_sub_tendsto_zero] at hLx hRx ⊢
      have hdom : Tendsto (fun e ↦ ‖L‖ * |C| * ‖R e x - x‖ + ‖L e x - x‖) l (𝓝 0) := by
        simpa using (hRx.const_mul (‖L‖ * |C|)).add hLx
      refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ hdom
      filter_upwards [hC] with e he
      calc ‖L e (R e x) - x‖
          = ‖L e (R e x - x) + (L e x - x)‖ := by rw [map_sub]; abel_nf
        _ ≤ ‖L e (R e x - x)‖ + ‖L e x - x‖ := norm_add_le _ _
        _ ≤ ‖L‖ * ‖e‖ * ‖R e x - x‖ + ‖L e x - x‖ := by gcongr; exact L.le_opNorm₂ _ _
        _ ≤ ‖L‖ * |C| * ‖R e x - x‖ + ‖L e x - x‖ := by gcongr; exact he.trans (le_abs_self C)
    exact (isClosed_topologicalClosure _).mem_of_tendsto hLRx <| .of_forall fun e ↦
      le_topologicalClosure _ <| subset_span ⟨(e, e, x), rfl⟩
  · refine topologicalClosure_minimal _ (span_le.2 ?_) ?_
    · rintro _ ⟨⟨a, b, x⟩, rfl⟩
      refine ⟨apply_mem_topologicalClosure_span L a (R b x), ?_⟩
      dsimp only
      rw [hLR]
      exact apply_mem_topologicalClosure_span R b (L a x)
    · rw [Submodule.coe_inf]
      exact (isClosed_topologicalClosure _).inter (isClosed_topologicalClosure _)

end EssentialPart

section Reduction

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [ProperSpace 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {L R : A →L[𝕜] E →L[𝕜] E}

omit [IsRCLikeNormedField 𝕜] [ProperSpace 𝕜] in
/-- Subtracting an inner derivation from a bounded derivation yields a bounded derivation. -/
private theorem derivation_sub_inner
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) {D : A →L[𝕜] StrongDual 𝕜 E}
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) (ψ : StrongDual 𝕜 E)
    (a b : A) :
    (D - ((dualAction R).flip ψ - (dualAction L).flip ψ)) (a * b) =
      dualAction R a ((D - ((dualAction R).flip ψ - (dualAction L).flip ψ)) b) +
        dualAction L b ((D - ((dualAction R).flip ψ - (dualAction L).flip ψ)) a) := by
  ext x
  have h := congr($(hD a b) x)
  simp only [sub_apply, flip_apply, add_apply, dualAction_apply_apply, h, hL, hR, hLR]
  ring

omit [IsRCLikeNormedField 𝕜] in
/-- Banach–Alaoglu: a bounded operator `D₁ : A →L[𝕜] E*` has a pointwise (weak-star) limit along
the ultrafilter `Ultrafilter.of l` whenever `l` is eventually bounded. -/
private theorem exists_weakStar_tendsto_ultrafilter {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (D₁ : A →L[𝕜] StrongDual 𝕜 E) :
    ∃ φ : StrongDual 𝕜 E, ∀ x : E, Tendsto (fun e ↦ D₁ e x) (Ultrafilter.of l) (𝓝 (φ x)) := by
  set U := Ultrafilter.of l
  obtain ⟨φw, -, hφ⟩ :=
    (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 E) (‖D₁‖ * C)).ultrafilter_le_nhds'
      (U.map (StrongDual.toWeakDual ∘ D₁))
      (Ultrafilter.mem_map.2 <| mem_of_superset (Ultrafilter.of_le l hC) fun e he ↦ by
        simpa using (D₁.le_opNorm e).trans (mul_le_mul_of_nonneg_left he (norm_nonneg D₁)))
  exact ⟨WeakDual.toStrongDual φw, fun x ↦ ((WeakDual.eval_continuous x).tendsto φw).comp hφ⟩

/-- **Left-essential reduction.** If `A` has a bounded right approximate identity, then a bounded
derivation `D : A →L[𝕜] E*` is inner as soon as its restriction to the left-essential part
`E_L = closure (span (A · E))` is inner. -/
theorem exists_eq_dualAction_sub_dualAction_of_restrict_leftEssential
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    {l : Filter A} [l.NeBot] {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ a, Tendsto (a * ·) l (𝓝 a))
    (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a))
    (hEL : ∃ ψ₀ : StrongDual 𝕜 (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure,
      ∀ a, (D a).comp (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure.subtypeL =
        dualAction (R.restrictSubmodule _ fun a _ hx ↦
          apply_mem_topologicalClosure_span_of_comm hLR a hx) a ψ₀ -
        dualAction (L.restrictSubmodule _ fun a x _ ↦
          apply_mem_topologicalClosure_span L a x) a ψ₀) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  let EL := (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure
  have hL_inv : ∀ a, ∀ x ∈ EL, L a x ∈ EL := fun a x _ ↦ apply_mem_topologicalClosure_span L a x
  have hR_inv : ∀ a, ∀ x ∈ EL, R a x ∈ EL :=
    fun a _ hx ↦ apply_mem_topologicalClosure_span_of_comm hLR a hx
  obtain ⟨ψ₀, hψ₀⟩ := hEL
  obtain ⟨ψ, hψ⟩ := StrongDual.exists_extension EL ψ₀
  -- Subtract the inner derivation of `ψ` to obtain a derivation `D₁` vanishing on `EL`.
  let D₁ : A →L[𝕜] StrongDual 𝕜 E := D - ((dualAction R).flip ψ - (dualAction L).flip ψ)
  have hD₁ (a b : A) : D₁ (a * b) = dualAction R a (D₁ b) + dualAction L b (D₁ a) :=
    derivation_sub_inner hL hR hLR hD ψ a b
  have hD₁x (a : A) (x : E) : D₁ a x = D a x - (ψ (R a x) - ψ (L a x)) := by simp [D₁]
  have hD₁_EL (a : A) (x : E) (hx : x ∈ EL) : D₁ a x = 0 := by
    have h1 := congr($(hψ₀ a) ⟨x, hx⟩)
    simp only [comp_apply, Submodule.subtypeL_apply, sub_apply, dualAction_apply_apply] at h1
    rw [hD₁x, ← coe_restrictSubmodule_apply R EL hR_inv a ⟨x, hx⟩,
      ← coe_restrictSubmodule_apply L EL hL_inv a ⟨x, hx⟩, hψ, hψ, h1, sub_self]
  -- Since `L b x ∈ EL`, `D₁ a · b = 0` and hence `D₁ (a * b) = a · D₁ b`.
  have hD₁_mul (a b : A) (x : E) : D₁ (a * b) x = D₁ b (R a x) := by
    have h := congr($(hD₁ a b) x)
    have h0 : D₁ a (L b x) = 0 := hD₁_EL a (L b x) (apply_mem_topologicalClosure_span L b x)
    simp only [add_apply, dualAction_apply_apply, h0, add_zero] at h
    exact h
  -- Take a weak-star limit `φ₁` of `D₁ e` along an ultrafilter finer than `l`.
  obtain ⟨φ₁, hφ₁_eval⟩ := exists_weakStar_tendsto_ultrafilter hC D₁
  have hφ₁R (a : A) (x : E) : φ₁ (R a x) = D₁ a x := by
    refine tendsto_nhds_unique (hφ₁_eval (R a x)) ?_
    have hlim : Tendsto (fun e ↦ D₁ (a * e) x) (Ultrafilter.of l) (𝓝 (D₁ a x)) :=
      (((D₁.continuous.clm_apply (continuous_const (y := x))).tendsto a).comp (hl a)).mono_left
        (Ultrafilter.of_le l)
    exact hlim.congr fun e ↦ hD₁_mul a e x
  have hφ₁L (a : A) (x : E) : φ₁ (L a x) = 0 := by
    refine tendsto_nhds_unique (hφ₁_eval (L a x)) ?_
    simp [hD₁_EL _ (L a x) (apply_mem_topologicalClosure_span L a x)]
  refine ⟨ψ + φ₁, fun a ↦ ?_⟩
  ext x
  simp only [sub_apply, dualAction_apply_apply, add_apply, hφ₁R, hφ₁L, hD₁x]
  ring

/-- **Right-essential reduction.** If `A` has a bounded left approximate identity, then a bounded
derivation `D : A →L[𝕜] E*` is inner as soon as its restriction to the right-essential part
`E_R = closure (span (E · A))` is inner. -/
theorem exists_eq_dualAction_sub_dualAction_of_restrict_rightEssential
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    {l : Filter A} [l.NeBot] {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ a, Tendsto (· * a) l (𝓝 a))
    (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a))
    (hER : ∃ ψ₀ : StrongDual 𝕜 (span 𝕜 (Set.range fun p : A × E ↦ R p.1 p.2)).topologicalClosure,
      ∀ a, (D a).comp (span 𝕜 (Set.range fun p : A × E ↦ R p.1 p.2)).topologicalClosure.subtypeL =
        dualAction (R.restrictSubmodule _ fun a x _ ↦
          apply_mem_topologicalClosure_span R a x) a ψ₀ -
        dualAction (L.restrictSubmodule _ fun a _ hx ↦
          apply_mem_topologicalClosure_span_of_comm (fun b c y ↦ (hLR c b y).symm) a hx) a ψ₀) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  let ER := (span 𝕜 (Set.range fun p : A × E ↦ R p.1 p.2)).topologicalClosure
  have hR_inv : ∀ a, ∀ x ∈ ER, R a x ∈ ER := fun a x _ ↦ apply_mem_topologicalClosure_span R a x
  have hL_inv : ∀ a, ∀ x ∈ ER, L a x ∈ ER :=
    fun a _ hx ↦ apply_mem_topologicalClosure_span_of_comm (fun b c y ↦ (hLR c b y).symm) a hx
  obtain ⟨ψ₀, hψ₀⟩ := hER
  obtain ⟨ψ, hψ⟩ := StrongDual.exists_extension ER ψ₀
  -- Subtract the inner derivation of `ψ` to obtain a derivation `D₁` vanishing on `ER`.
  let D₁ : A →L[𝕜] StrongDual 𝕜 E := D - ((dualAction R).flip ψ - (dualAction L).flip ψ)
  have hD₁ (a b : A) : D₁ (a * b) = dualAction R a (D₁ b) + dualAction L b (D₁ a) :=
    derivation_sub_inner hL hR hLR hD ψ a b
  have hD₁x (a : A) (x : E) : D₁ a x = D a x - (ψ (R a x) - ψ (L a x)) := by simp [D₁]
  have hD₁_ER (a : A) (x : E) (hx : x ∈ ER) : D₁ a x = 0 := by
    have h1 := congr($(hψ₀ a) ⟨x, hx⟩)
    simp only [comp_apply, Submodule.subtypeL_apply, sub_apply, dualAction_apply_apply] at h1
    rw [hD₁x, ← coe_restrictSubmodule_apply R ER hR_inv a ⟨x, hx⟩,
      ← coe_restrictSubmodule_apply L ER hL_inv a ⟨x, hx⟩, hψ, hψ, h1, sub_self]
  -- Since `R a x ∈ ER`, `a · D₁ b = 0` and hence `D₁ (a * b) = D₁ a · b`.
  have hD₁_mul (a b : A) (x : E) : D₁ (a * b) x = D₁ a (L b x) := by
    have h := congr($(hD₁ a b) x)
    have h0 : D₁ b (R a x) = 0 := hD₁_ER b (R a x) (apply_mem_topologicalClosure_span R a x)
    simp only [add_apply, dualAction_apply_apply, h0, zero_add] at h
    exact h
  -- Take a weak-star limit `φ₁` of `D₁ e` along an ultrafilter finer than `l`.
  obtain ⟨φ₁, hφ₁_eval⟩ := exists_weakStar_tendsto_ultrafilter hC D₁
  have hφ₁L (a : A) (x : E) : φ₁ (L a x) = D₁ a x := by
    refine tendsto_nhds_unique (hφ₁_eval (L a x)) ?_
    have hlim : Tendsto (fun e ↦ D₁ (e * a) x) (Ultrafilter.of l) (𝓝 (D₁ a x)) :=
      (((D₁.continuous.clm_apply (continuous_const (y := x))).tendsto a).comp (hl a)).mono_left
        (Ultrafilter.of_le l)
    exact hlim.congr fun e ↦ hD₁_mul e a x
  have hφ₁R (a : A) (x : E) : φ₁ (R a x) = 0 := by
    refine tendsto_nhds_unique (hφ₁_eval (R a x)) ?_
    simp [hD₁_ER _ (R a x) (apply_mem_topologicalClosure_span R a x)]
  refine ⟨ψ - φ₁, fun a ↦ ?_⟩
  ext x
  simp only [sub_apply, dualAction_apply_apply, hφ₁R, hφ₁L, hD₁x]
  ring

/-- **Essential-part reduction for a bounded derivation.** If `A` has a bounded two-sided
approximate identity, then a bounded derivation `D : A →L[𝕜] E*` is inner as soon as its
restriction to the essential part `E_L ⊓ E_R` is inner. -/
theorem exists_eq_dualAction_sub_dualAction_of_restrict_essential
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    {l : Filter A} (hl : l.IsApproximateUnit) {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a))
    (hEss : ∃ ψ₀ : StrongDual 𝕜
        ↥((span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure ⊓
          (span 𝕜 (Set.range fun p : A × E ↦ R p.1 p.2)).topologicalClosure),
      ∀ a, (D a).comp ((span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure ⊓
          (span 𝕜 (Set.range fun p : A × E ↦ R p.1 p.2)).topologicalClosure).subtypeL =
        dualAction (R.restrictSubmodule
          ((span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure ⊓
            (span 𝕜 (Set.range fun p : A × E ↦ R p.1 p.2)).topologicalClosure)
          fun a _ hx ↦ ⟨apply_mem_topologicalClosure_span_of_comm hLR a hx.1,
            apply_mem_topologicalClosure_span R a _⟩) a ψ₀ -
        dualAction (L.restrictSubmodule
          ((span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure ⊓
            (span 𝕜 (Set.range fun p : A × E ↦ R p.1 p.2)).topologicalClosure)
          fun a _ hx ↦ ⟨apply_mem_topologicalClosure_span L a _,
            apply_mem_topologicalClosure_span_of_comm (fun b c y ↦ (hLR c b y).symm) a hx.2⟩)
          a ψ₀) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  have := hl.neBot
  let EL := (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure
  let ER := (span 𝕜 (Set.range fun p : A × E ↦ R p.1 p.2)).topologicalClosure
  have hLL_inv : ∀ a, ∀ x ∈ EL, L a x ∈ EL := fun a x _ ↦ apply_mem_topologicalClosure_span L a x
  have hRL_inv : ∀ a, ∀ x ∈ EL, R a x ∈ EL :=
    fun a _ hx ↦ apply_mem_topologicalClosure_span_of_comm hLR a hx
  let LL : A →L[𝕜] EL →L[𝕜] EL := L.restrictSubmodule EL hLL_inv
  let RL : A →L[𝕜] EL →L[𝕜] EL := R.restrictSubmodule EL hRL_inv
  have hLL := restrictSubmodule_mul_apply_of_left hL EL hLL_inv
  have hRL := restrictSubmodule_mul_apply_of_right hR EL hRL_inv
  have hLRL := restrictSubmodule_apply_comm hLR EL hLL_inv hRL_inv
  -- Step 1: reduce `E` to `EL`.
  let DL : A →L[𝕜] StrongDual 𝕜 EL := (precomp 𝕜 EL.subtypeL) ∘L D
  have hDL : ∀ a b, DL (a * b) = dualAction RL a (DL b) + dualAction LL b (DL a) := by
    intro a b
    ext x
    simpa [DL, LL, RL] using congr($(hD a b) x.1)
  suffices ∃ ψL : StrongDual 𝕜 EL, ∀ a, DL a = dualAction RL a ψL - dualAction LL a ψL by
    obtain ⟨ψL, hψL⟩ := this
    exact exists_eq_dualAction_sub_dualAction_of_restrict_leftEssential hL hR hLR hC
      hl.tendsto_mul_left D hD ⟨ψL, fun a ↦ by simpa [DL] using hψL a⟩
  -- Step 2: reduce `EL` to its right-essential part `ELR`, which maps into `EL ⊓ ER`.
  refine exists_eq_dualAction_sub_dualAction_of_restrict_rightEssential hLL hRL hLRL hC
    hl.tendsto_mul_right DL hDL ?_
  let ELR := (span 𝕜 (Set.range fun p : A × EL ↦ RL p.1 p.2)).topologicalClosure
  -- Every `x : ELR` lies in `ER`, because `R e x.1 = (RL e x).1 → x.1`.
  have hELR_mem (x : ELR) : (x.1 : E) ∈ EL ⊓ ER := by
    refine ⟨x.1.2, ?_⟩
    have ht := tendsto_apply_of_mem_topologicalClosure_span_right RL hRL hC
      hl.tendsto_mul_left x.2
    have htE : Tendsto (fun e ↦ R e (x.1 : E)) l (𝓝 (x.1 : E)) :=
      ((EL.subtypeL.continuous.tendsto x.1).comp ht).congr fun e ↦
        coe_restrictSubmodule_apply R EL hRL_inv e x.1
    exact (tendsto_apply_iff_mem_topologicalClosure_span_right R hR hC hl.tendsto_mul_left).1 htE
  let ι : ELR →L[𝕜] ↥(EL ⊓ ER) :=
    (EL.subtypeL.comp ELR.subtypeL).codRestrict (EL ⊓ ER) hELR_mem
  have hι_coe (x : ELR) : (ι x : E) = (x.1 : E) := rfl
  have hιR (a : A) (x : ELR) :
      ι (RL.restrictSubmodule ELR (fun a y _ ↦ apply_mem_topologicalClosure_span RL a y) a x) =
        R.restrictSubmodule (EL ⊓ ER)
          (fun a _ hx ↦ ⟨apply_mem_topologicalClosure_span_of_comm hLR a hx.1,
            apply_mem_topologicalClosure_span R a _⟩) a (ι x) := by
    apply SetLike.coe_eq_coe.1
    rw [hι_coe, coe_restrictSubmodule_apply, coe_restrictSubmodule_apply, ← hι_coe x]
    exact (coe_restrictSubmodule_apply R (EL ⊓ ER) _ a (ι x)).symm
  have hιL (a : A) (x : ELR) :
      ι (LL.restrictSubmodule ELR (fun a _ hy ↦
          apply_mem_topologicalClosure_span_of_comm (fun b c y ↦ (hLRL c b y).symm) a hy) a x) =
        L.restrictSubmodule (EL ⊓ ER)
          (fun a _ hx ↦ ⟨apply_mem_topologicalClosure_span L a _,
            apply_mem_topologicalClosure_span_of_comm (fun b c y ↦ (hLR c b y).symm) a hx.2⟩)
          a (ι x) := by
    apply SetLike.coe_eq_coe.1
    rw [hι_coe, coe_restrictSubmodule_apply, coe_restrictSubmodule_apply, ← hι_coe x]
    exact (coe_restrictSubmodule_apply L (EL ⊓ ER) _ a (ι x)).symm
  obtain ⟨ψ₀, hψ₀⟩ := hEss
  refine ⟨ψ₀.comp ι, fun a ↦ ?_⟩
  ext x
  have hx := congr($(hψ₀ a) (ι x))
  simp only [comp_apply, Submodule.subtypeL_apply, sub_apply, dualAction_apply_apply] at hx ⊢
  rw [hιR, hιL]
  simp only [DL, comp_apply, precomp_apply, Submodule.subtypeL_apply]
  rw [← hι_coe x]
  exact hx

/-- **Reduction of amenability to essential bimodules** (Runde, Proposition 2.1.5). A normed
algebra with a bounded two-sided approximate identity is amenable if and only if every bounded
derivation into the dual of an essential Banach `A`-bimodule (in the universe of `A`) is inner. -/
theorem isAmenable_iff_essential {𝕜 : Type v} {A : Type u} [NontriviallyNormedField 𝕜]
    [IsRCLikeNormedField 𝕜] [ProperSpace 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    {l : Filter A} (hl : l.IsApproximateUnit) {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C) :
    IsAmenable 𝕜 A ↔
      ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
        (L R : A →L[𝕜] E →L[𝕜] E),
        (∀ a b x, L (a * b) x = L a (L b x)) →
        (∀ a b x, R (a * b) x = R b (R a x)) →
        (∀ a b x, L a (R b x) = R b (L a x)) →
        (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure = ⊤ →
        (span 𝕜 (Set.range fun p : A × E ↦ R p.1 p.2)).topologicalClosure = ⊤ →
        ∀ D : A →L[𝕜] StrongDual 𝕜 E,
          (∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) →
          ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  have := hl.neBot
  rw [isAmenable_def]
  constructor
  · intro h E _ _ _ L R hL hR hLR _ _ D hD
    exact h E L R hL hR hLR D hD
  · intro h E _ _ _ L R hL hR hLR D hD
    let Eess := (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure ⊓
      (span 𝕜 (Set.range fun p : A × E ↦ R p.1 p.2)).topologicalClosure
    have hclosed : IsClosed (Eess : Set E) := by
      rw [Submodule.coe_inf]
      exact (isClosed_topologicalClosure _).inter (isClosed_topologicalClosure _)
    have : CompleteSpace Eess := hclosed.completeSpace_coe
    have hL_inv : ∀ a, ∀ x ∈ Eess, L a x ∈ Eess := fun a _ hx ↦
      ⟨apply_mem_topologicalClosure_span L a _,
        apply_mem_topologicalClosure_span_of_comm (fun b c y ↦ (hLR c b y).symm) a hx.2⟩
    have hR_inv : ∀ a, ∀ x ∈ Eess, R a x ∈ Eess := fun a _ hx ↦
      ⟨apply_mem_topologicalClosure_span_of_comm hLR a hx.1,
        apply_mem_topologicalClosure_span R a _⟩
    let Less : A →L[𝕜] Eess →L[𝕜] Eess := L.restrictSubmodule Eess hL_inv
    let Ress : A →L[𝕜] Eess →L[𝕜] Eess := R.restrictSubmodule Eess hR_inv
    have hLess := restrictSubmodule_mul_apply_of_left hL Eess hL_inv
    have hRess := restrictSubmodule_mul_apply_of_right hR Eess hR_inv
    have hLRess := restrictSubmodule_apply_comm hLR Eess hL_inv hR_inv
    have hL_top : (span 𝕜 (Set.range fun p : A × Eess ↦ Less p.1 p.2)).topologicalClosure = ⊤ := by
      rw [eq_top_iff]
      intro x _
      refine (tendsto_apply_iff_mem_topologicalClosure_span Less hLess hC hl.tendsto_mul_right).1 ?_
      exact tendsto_subtype_rng.2 <|
        (tendsto_apply_of_mem_topologicalClosure_span L hL hC hl.tendsto_mul_right x.2.1).congr
          fun e ↦ (coe_restrictSubmodule_apply L Eess hL_inv e x).symm
    have hR_top : (span 𝕜 (Set.range fun p : A × Eess ↦ Ress p.1 p.2)).topologicalClosure = ⊤ := by
      rw [eq_top_iff]
      intro x _
      refine (tendsto_apply_iff_mem_topologicalClosure_span_right Ress hRess hC
        hl.tendsto_mul_left).1 ?_
      exact tendsto_subtype_rng.2 <|
        (tendsto_apply_of_mem_topologicalClosure_span_right R hR hC hl.tendsto_mul_left x.2.2).congr
          fun e ↦ (coe_restrictSubmodule_apply R Eess hR_inv e x).symm
    let Dess : A →L[𝕜] StrongDual 𝕜 Eess := (precomp 𝕜 Eess.subtypeL) ∘L D
    have hDess : ∀ a b, Dess (a * b) = dualAction Ress a (Dess b) + dualAction Less b (Dess a) := by
      intro a b
      ext x
      simpa [Dess, Less, Ress] using congr($(hD a b) x.1)
    obtain ⟨ψ₀, hψ₀⟩ := h Eess Less Ress hLess hRess hLRess hL_top hR_top Dess hDess
    exact exists_eq_dualAction_sub_dualAction_of_restrict_essential hL hR hLR hl hC D hD
      ⟨ψ₀, fun a ↦ by simpa [Dess] using hψ₀ a⟩

end Reduction

end TauCeti

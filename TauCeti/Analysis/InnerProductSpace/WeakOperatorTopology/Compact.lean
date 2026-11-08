/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Compactness of operator balls in the weak operator topology

Let `E` be a normed space and `F` a complete inner product space over `ℝ` or `ℂ`. This file proves
that every closed norm ball of `E →L[𝕜] F` is compact in the weak operator topology, taken on
Mathlib's copy `E →WOT[𝕜] F` (`ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall`), and
hence that every norm-bounded set of operators has weak operator compact closure
(`ContinuousLinearMapWOT.isCompact_closure_image_ofCLM_of_isBounded`).

The analytic input is `ContinuousLinearMapWOT.exists_norm_le_tendsto_of_tendsto_inner`: a family of
operators that is eventually bounded in norm by `r` and whose matrix coefficients `⟪y, A x⟫`
all converge has a weak operator limit, and that limit has norm at most `r`. The limiting
coefficients form a sesquilinear form bounded by `r`, which the Riesz representation turns
back into an operator. Compactness of a ball then follows by applying this to an ultrafilter:
each coefficient ranges over a compact disc of scalars, so it converges along the ultrafilter.

Weak operator compactness of the unit ball is the operator analogue of the Banach–Alaoglu
theorem. It gives weak operator cluster points of bounded nets of operators, and the compactness
of the unit ball of a von Neumann algebra.

## References

Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, §5.1, for the weak operator
compactness of the unit ball of `B(H)`.
-/

public section

open Filter Metric
open scoped Topology InnerProductSpace ComplexConjugate

namespace ContinuousLinearMapWOT

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A family of operators that is eventually bounded in norm by `r`, and whose matrix
coefficients `⟪y, f a x⟫` all converge, converges in the weak operator topology to an operator of
norm at most `r`. -/
theorem exists_norm_le_tendsto_of_tendsto_inner {α : Type*} {l : Filter α} [l.NeBot]
    {f : α → E →L[𝕜] F} {r : ℝ} (hf : ∀ᶠ a in l, ‖f a‖ ≤ r)
    (hlim : ∀ x y, ∃ c, Tendsto (fun a => ⟪y, f a x⟫_𝕜) l (𝓝 c)) :
    ∃ T : E →L[𝕜] F, ‖T‖ ≤ r ∧ Tendsto (fun a => ofCLM (f a)) l (𝓝 (ofCLM T)) := by
  choose g hg using hlim
  have hr : 0 ≤ r := by
    obtain ⟨a, ha⟩ := hf.exists
    exact (norm_nonneg _).trans ha
  -- The limiting coefficients `g x y` are linear in `x`, conjugate-linear in `y`, and bounded.
  have hadd₁ (x x' y) : g (x + x') y = g x y + g x' y :=
    tendsto_nhds_unique (hg (x + x') y) (by simpa [inner_add_right] using (hg x y).add (hg x' y))
  have hsmul₁ (c : 𝕜) (x y) : g (c • x) y = c * g x y :=
    tendsto_nhds_unique (hg (c • x) y) (by simpa [inner_smul_right] using (hg x y).const_mul c)
  have hadd₂ (x y y') : g x (y + y') = g x y + g x y' :=
    tendsto_nhds_unique (hg x (y + y')) (by simpa [inner_add_left] using (hg x y).add (hg x y'))
  have hsmul₂ (c : 𝕜) (x y) : g x (c • y) = conj c * g x y :=
    tendsto_nhds_unique (hg x (c • y))
      (by simpa [inner_smul_left] using (hg x y).const_mul (conj c))
  have hbound (x y) : ‖g x y‖ ≤ r * ‖x‖ * ‖y‖ := by
    refine le_of_tendsto (hg x y).norm (hf.mono fun a ha => ?_)
    calc ‖⟪y, f a x⟫_𝕜‖ ≤ ‖y‖ * ‖f a x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (r * ‖x‖) := by gcongr; exact (f a).le_of_opNorm_le ha x
      _ = r * ‖x‖ * ‖y‖ := by ring
  -- The conjugate form `x ↦ (y ↦ conj (g x y))` is a bounded conjugate-linear map into the dual
  -- of `F`; composing with the inverse Riesz isomorphism gives the limit operator.
  let B : E →L⋆[𝕜] F →L[𝕜] 𝕜 :=
    (LinearMap.mk₂'ₛₗ (starRingEnd 𝕜) (RingHom.id 𝕜) (fun x y => conj (g x y))
      (fun x x' y => by simp [hadd₁]) (fun c x y => by simp [hsmul₁])
      (fun x y y' => by simp [hadd₂]) (fun c x y => by simp [hsmul₂])).mkContinuous₂ r
      (fun x y => by simpa using hbound x y)
  let T : E →L[𝕜] F :=
    ((InnerProductSpace.toDual 𝕜 F).symm : StrongDual 𝕜 F →L⋆[𝕜] F).comp B
  have hT (x y) : ⟪y, T x⟫_𝕜 = g x y := by
    rw [← inner_conj_symm]
    simp [T, B, InnerProductSpace.toDual_symm_apply]
  refine ⟨T, T.opNorm_le_bound hr fun x => ?_, ?_⟩
  · calc ‖T x‖ = ‖B x‖ := by simp [T]
      _ ≤ ‖B‖ * ‖x‖ := B.le_opNorm x
      _ ≤ r * ‖x‖ := by gcongr; exact LinearMap.mkContinuous₂_norm_le _ hr _
  · refine tendsto_iff_forall_inner_apply_tendsto.mpr fun x y => ?_
    simpa [hT] using hg x y

/-- **Weak operator compactness of operator balls.** Every closed norm ball of bounded operators
from a normed space to a complete inner product space is compact in the weak operator
topology. -/
theorem isCompact_image_ofCLM_closedBall (A : E →L[𝕜] F) (r : ℝ) :
    IsCompact (ofCLM '' closedBall A r : Set (E →WOT[𝕜] F)) := by
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro 𝒰 h𝒰
  have hball : ∀ᶠ T in (𝒰 : Filter (E →WOT[𝕜] F)), ‖toCLM T - A‖ ≤ r := by
    filter_upwards [le_principal_iff.mp h𝒰] with T ⟨S, hS, hST⟩
    rwa [← hST, toCLM_ofCLM, ← dist_eq_norm, ← mem_closedBall]
  -- Each matrix coefficient of `T - A` stays in a compact disc, so it converges along `𝒰`.
  have hlim (x : E) (y : F) :
      ∃ c, Tendsto (fun T => ⟪y, (toCLM T - A) x⟫_𝕜) (𝒰 : Filter (E →WOT[𝕜] F)) (𝓝 c) := by
    let φ : (E →WOT[𝕜] F) → 𝕜 := fun T => ⟪y, (toCLM T - A) x⟫_𝕜
    have hmem : closedBall (0 : 𝕜) (r * ‖x‖ * ‖y‖) ∈ 𝒰.map φ := by
      refine Ultrafilter.mem_map.mpr (Filter.mem_of_superset hball fun T hT => ?_)
      rw [Set.mem_preimage, mem_closedBall_zero_iff]
      calc ‖φ T‖ ≤ ‖y‖ * ‖(toCLM T - A) x‖ := norm_inner_le_norm _ _
        _ ≤ ‖y‖ * (r * ‖x‖) := by gcongr; exact (toCLM T - A).le_of_opNorm_le hT x
        _ = r * ‖x‖ * ‖y‖ := by ring
    obtain ⟨c, -, hc⟩ := (isCompact_closedBall (0 : 𝕜) _).ultrafilter_le_nhds _
      (le_principal_iff.mpr hmem)
    exact ⟨c, by rwa [Ultrafilter.coe_map] at hc⟩
  obtain ⟨S, hS, hlimS⟩ := exists_norm_le_tendsto_of_tendsto_inner hball hlim
  refine ⟨ofCLM (S + A), ⟨S + A, ?_, rfl⟩, ?_⟩
  · rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
  · have h := hlimS.add_const (ofCLM A)
    simp only [ofCLM_toCLM, sub_add_cancel, ← ofCLM_add] at h
    exact tendsto_id'.mp h

/-- A norm-bounded set of operators from a normed space to a complete inner product space has
compact closure in the weak operator topology. -/
theorem isCompact_closure_image_ofCLM_of_isBounded {s : Set (E →L[𝕜] F)}
    (hs : Bornology.IsBounded s) :
    IsCompact (closure (ofCLM '' s : Set (E →WOT[𝕜] F))) := by
  obtain ⟨r, hr⟩ := hs.subset_closedBall 0
  exact (isCompact_image_ofCLM_closedBall (0 : E →L[𝕜] F) r).closure_of_subset (Set.image_mono hr)

end ContinuousLinearMapWOT

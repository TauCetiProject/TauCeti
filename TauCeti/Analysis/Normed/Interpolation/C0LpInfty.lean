/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.Regular
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Dual
import TauCeti.Analysis.Normed.Module.Dual.Adjoint

/-!
# The non-regular couple `(C₀(ℕ, E), ℓ^∞(ℕ, E))`

`CompatibleCouple.c0LpInfty 𝕜 E` embeds `C₀(ℕ, E)` and `ℓ^∞(ℕ, E)` into `ℓ^∞(ℕ, E)`. Its
intersection `C₀(ℕ, E)` is surjective (hence dense) in the first endpoint
(`c0LpInfty_interFst_surjective`, `denseRange_c0LpInfty_interFst`) and not dense in the second when
`E` is nontrivial (`not_denseRange_c0LpInfty_interSnd`), so the couple is not regular
(`not_isRegular_c0LpInfty`) and dual restriction on the second endpoint is not injective
(`not_injective_precomp_c0LpInfty_interSnd`).

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §2.7 and §4.2.
-/

public noncomputable section

open Filter Set Topology
open scoped ENNReal ZeroAtInfty

namespace TauCeti.CompatibleCouple

variable (𝕜 E : Type*) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The compatible couple `(C₀(ℕ, E), ℓ^∞(ℕ, E))` inside `ℓ^∞(ℕ, E)`, whose intersection is
`C₀(ℕ, E)`: dense in the first endpoint and closed in the second. -/
def c0LpInfty : CompatibleCouple 𝕜 C₀(ℕ, E) (lp (fun _ : ℕ ↦ E) ∞) (lp (fun _ : ℕ ↦ E) ∞) where
  embed₀ := (ZeroAtInftyContinuousMap.toLpInfty 𝕜).toContinuousLinearMap
  embed₁ := ContinuousLinearMap.id 𝕜 _
  embed₀_injective := (ZeroAtInftyContinuousMap.toLpInfty 𝕜).injective
  embed₁_injective := Function.injective_id

@[simp] theorem c0LpInfty_embed₀ :
    (c0LpInfty 𝕜 E).embed₀ = (ZeroAtInftyContinuousMap.toLpInfty 𝕜).toContinuousLinearMap := (rfl)

@[simp] theorem c0LpInfty_embed₁ : (c0LpInfty 𝕜 E).embed₁ = ContinuousLinearMap.id 𝕜 _ := (rfl)

/-- The first projection from the intersection of `(C₀(ℕ, E), ℓ^∞(ℕ, E))` onto `C₀(ℕ, E)` is
surjective. -/
theorem c0LpInfty_interFst_surjective : Function.Surjective (c0LpInfty 𝕜 E).interFst := fun f =>
  ⟨⟨(f, ZeroAtInftyContinuousMap.toLpInfty 𝕜 f), (c0LpInfty 𝕜 E).mem_inter_iff.2 rfl⟩, by simp⟩

/-- The intersection of `(C₀(ℕ, E), ℓ^∞(ℕ, E))` is dense in the first endpoint `C₀(ℕ, E)`. -/
theorem denseRange_c0LpInfty_interFst : DenseRange (c0LpInfty 𝕜 E).interFst :=
  (c0LpInfty_interFst_surjective 𝕜 E).denseRange

/-- When `E` is nontrivial, the intersection of `(C₀(ℕ, E), ℓ^∞(ℕ, E))` is not dense in `ℓ^∞(ℕ, E)`:
any nonzero constant sequence `e` has distance at least `‖e‖ / 2` from every null sequence. -/
theorem not_denseRange_c0LpInfty_interSnd [Nontrivial E] :
    ¬ DenseRange (c0LpInfty 𝕜 E).interSnd := by
  intro hd; obtain ⟨e, he⟩ := exists_ne (0 : E)
  have he0 : 0 < ‖e‖ := norm_pos_iff.2 he
  let u : lp (fun _ : ℕ ↦ E) ∞ :=
    ⟨fun _ => e, memℓp_infty ⟨‖e‖, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩⟩
  obtain ⟨_, ⟨x, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 (hd u) (‖e‖ / 2) (half_pos he0)
  obtain ⟨n, hn⟩ := (((by simpa using (zero_at_infty x.1.1).norm :
    Tendsto (fun n : ℕ => ‖x.1.1 n‖) atTop (𝓝 0))).eventually (gt_mem_nhds (half_pos he0))).exists
  have hcoord := lp.norm_apply_le_norm ENNReal.top_ne_zero (u - (c0LpInfty 𝕜 E).interSnd x) n
  have hx : x.1.2 = ZeroAtInftyContinuousMap.toLpInfty 𝕜 x.1.1 := by
    simpa using ((c0LpInfty 𝕜 E).mem_inter_iff.1 x.2).symm
  have hsub : ‖e‖ - ‖x.1.1 n‖ ≤ ‖(u - (c0LpInfty 𝕜 E).interSnd x) n‖ := by
    rw [lp.coeFn_sub, Pi.sub_apply, interSnd_apply, hx, ZeroAtInftyContinuousMap.toLpInfty_apply]
    exact norm_sub_norm_le e (x.1.1 n)
  rw [dist_eq_norm] at hy; linarith

/-- When `E` is nontrivial, `(C₀(ℕ, E), ℓ^∞(ℕ, E))` is not regular. -/
theorem not_isRegular_c0LpInfty [Nontrivial E] : ¬ (c0LpInfty 𝕜 E).IsRegular :=
  fun h => not_denseRange_c0LpInfty_interSnd 𝕜 E h.denseRange_interSnd

/-- Over `RCLike` scalars and for nontrivial `E`, restriction from `(ℓ^∞(ℕ, E))*` to
`(C₀(ℕ, E) ∩ ℓ^∞(ℕ, E))*` is not injective. -/
theorem not_injective_precomp_c0LpInfty_interSnd {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [Nontrivial E] : ¬ Function.Injective
      (ContinuousLinearMap.precomp 𝕜 (c0LpInfty 𝕜 E).interSnd :
        StrongDual 𝕜 (lp (fun _ : ℕ ↦ E) ∞) →L[𝕜] StrongDual 𝕜 (c0LpInfty 𝕜 E).inter) :=
  mt (ContinuousLinearMap.injective_precomp_iff_denseRange _).1
    (not_denseRange_c0LpInfty_interSnd 𝕜 E)

end TauCeti.CompatibleCouple

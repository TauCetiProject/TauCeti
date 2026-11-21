/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.IntegralCurve.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# A strict Lyapunov function for a continuation field

Let `V` be a continuation field on `M × ℝ` from a vector field `X₀` to a vector field `X₁` at
rate `C > 0` (`TauCeti.IsContinuationField`): in the open slab `M × (0, 1)` its time component is
`C t (1 - t²)`, and its space component is `X₀` near `t = 0` and `X₁` near `t = 1`. Suppose that
`f₀` does not increase along `X₀` and `f₁` does not increase along `X₁`, as for pseudo-gradients
adapted to `f₀` and `f₁` (`TauCeti.IsAdaptedPseudoGradient.mvfderiv_apply_nonpos`). This file
constructs a function on the slab that strictly increases along every trajectory of `V` through
it, so that `V` is gradient-like on the open slab, as `X₀` and `X₁` are for `-f₀` and `-f₁`.

Let `F` be a `C¹` function on `M × ℝ` interpolating between the two functions in time: equal to
`f₀ (x)` near `t = 0` and to `f₁ (x)` near `t = 1`, uniformly in `x`. When `f₀` and `f₁` are `C¹`,
such an interpolation exists, for instance `f₀ (x) + ρ (3 t - 1) (f₁ (x) - f₀ (x))` with `ρ` a
smooth transition from `0` to `1` (`TauCeti.IsContinuationField.exists_strictMono_mul_snd_sub`).
For a large constant `K` the function

`L (x, t) = K t - F (x, t)`

is a **strict Lyapunov function** for `V` on the open slab: its derivative
`K · C t (1 - t²) - dF(V)` along `V` is positive at every point of `M × (0, 1)`
(`TauCeti.IsContinuationField.eventually_forall_mvfderiv_apply_lt_mul_snd`). Near the two ends
this holds for every `K > 0`, since there `F` is `f₀` or `f₁`, which do not increase along the
space component `X₀` or `X₁`, while `t` strictly increases. On the compact middle slab
`M × [δ, 1 - δ]` the derivative `dF(V)` is bounded by continuity, while the base field
`t (1 - t²)` is bounded below by `δ² > 0`, so a large `K` dominates it.

Consequently `L` strictly increases along every integral curve of `V` meeting the open slab
(`TauCeti.IsContinuationField.eventually_strictMono_mul_snd_sub`). Along a trajectory from
`(p, 0)` to `(q, 1)` it runs from `-f₀ (p)` to `K - f₁ (q)`, and stays strictly between these
values (`TauCeti.IsContinuationField.eventually_mul_snd_sub_mem_Ioo`).

## Main results

In the namespace `TauCeti.IsContinuationField`:

* `eventually_forall_mvfderiv_apply_lt_mul_snd`: for all large `K`, `dF(V) < K C t (1 - t²)` at
  every point of the open slab, that is, `L = K t - F` has positive derivative along `V` there.
* `eventually_strictMono_mul_snd_sub`: for all large `K`, `L` strictly increases along every
  integral curve of `V` meeting the open slab.
* `eventually_mul_snd_sub_mem_Ioo`: along a trajectory from `(p, 0)` to `(q, 1)`, the values of `L`
  lie strictly between its limits `-f₀ (p)` and `K - f₁ (q)`.
* `exists_strictMono_mul_snd_sub`: for `C¹` functions `f₀` and `f₁` there is a `C¹` function `F`,
  equal to `f₀` for `t ≤ 1 / 3` and to `f₁` for `t ≥ 2 / 3`, such that for all large `K` the
  function `K t - F` strictly increases along every trajectory of `V` through the slab and stays
  strictly between its limits along every trajectory from `(p, 0)` to `(q, 1)`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (continuation maps from functions on `M × [0, 1]`).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-! ### The Lyapunov function of a continuation field -/

namespace IsContinuationField

variable [IsManifold 𝓘(ℝ, E) 1 M] [CompactSpace M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {C : ℝ}
  {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z} {F : M × ℝ → ℝ}

variable (hV : IsContinuationField X₀ X₁ C V) (hC : 0 < C)
  (hVc : Continuous fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))
  (hF : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ) 1 F)
  (hF₀ : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x, F (x, t) = f₀ x)
  (hF₁ : ∀ᶠ t in 𝓝[<] (1 : ℝ), ∀ x, F (x, t) = f₁ x)
  (hX₀ : ∀ x, mvfderiv 𝓘(ℝ, E) f₀ x (X₀ x) ≤ 0) (hX₁ : ∀ x, mvfderiv 𝓘(ℝ, E) f₁ x (X₁ x) ≤ 0)
include hV hC hVc hF hF₀ hF₁ hX₀ hX₁

/-- **The derivative of the interpolation along a continuation field is dominated by the base
field.** For all large `K`, the derivative `dF(V)` of the interpolation `F` along the continuation
field `V` is less than `K` times the time component `C t (1 - t²)` of `V`, at every point of the
open slab. Equivalently, `K t - F` has positive derivative along `V` there: it is a strict
Lyapunov function for `V` on `M × (0, 1)`. -/
theorem eventually_forall_mvfderiv_apply_lt_mul_snd :
    ∀ᶠ K in atTop, ∀ z : M × ℝ, z.2 ∈ Ioo 0 1 →
      mvfderiv (𝓘(ℝ, E).prod 𝓘(ℝ)) F z (V z) < K * (V z : E × ℝ).2 := by
  -- Near the two ends, `F` is `f₀` or `f₁` and the space component of `V` is `X₀` or `X₁`.
  obtain ⟨u, hu0 : 0 < u, hu⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.1 (hF₀.and hV.eventually_fst_eq_left)
  obtain ⟨l, hl1 : l < 1, hl⟩ :=
    mem_nhdsLT_iff_exists_Ioo_subset.1 (hF₁.and hV.eventually_fst_eq_right)
  set δ := min u (1 - l)
  have hδ : 0 < δ := lt_min hu0 (by linarith)
  -- Where `F` is `f ∘ Prod.fst` near `(x, t)`, its derivative is that of `f` on the space part.
  have hfst {f : M → ℝ} {s : Set ℝ} (hs : IsOpen s) (hFs : ∀ t ∈ s, ∀ x, F (x, t) = f x) {x : M}
      {t : ℝ} (ht : t ∈ s) :
      mvfderiv (𝓘(ℝ, E).prod 𝓘(ℝ)) F (x, t) (V (x, t)) =
        mvfderiv 𝓘(ℝ, E) f x (V (x, t) : E × ℝ).1 := by
    have hev : F =ᶠ[𝓝 (x, t)] f ∘ Prod.fst := by
      filter_upwards [(hs.preimage continuous_snd).mem_nhds ht] with z hz
      exact hFs z.2 hz z.1
    rw [hev.mvfderiv_eq, mvfderiv_comp_fst_apply]
  -- So the derivative along `V` is nonpositive outside the inner slab `M × [δ, 1 - δ]`.
  have hend : ∀ x ∈ (univ : Set M), ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ Icc δ (1 - δ) →
      mvfderiv (𝓘(ℝ, E).prod 𝓘(ℝ)) F (x, t) (V (x, t)) ≤ 0 := by
    intro x _ t ht htδ
    rcases not_and_or.1 htδ with h | h
    · have ht' : t ∈ Ioo 0 u := ⟨ht.1, (not_le.1 h).trans_le (min_le_left _ _)⟩
      rw [hfst isOpen_Ioo (fun t ht ↦ (hu ht).1) ht', (hu ht').2 x]
      exact hX₀ x
    · have ht' : t ∈ Ioo l 1 :=
        ⟨by linarith [min_le_right u (1 - l), not_le.1 h], ht.2⟩
      rw [hfst isOpen_Ioo (fun t ht ↦ (hl ht).1) ht', (hl ht').2 x]
      exact hX₁ x
  -- On the compact inner slab the derivative along `V` is continuous, hence bounded.
  have hcont : Continuous fun z : M × ℝ ↦ mvfderiv (𝓘(ℝ, E).prod 𝓘(ℝ)) F z (V z) :=
    ((hF.contMDiff_mvfderiv_apply (m := 0) (by simp)).comp
      (contMDiff_zero_iff.2 hVc :
        ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent 0 _)).continuous
  obtain ⟨K₀, -, hK₀⟩ := isCompact_univ.exists_forall_le_mul_one_sub_sq
    (g := fun x t ↦ mvfderiv (𝓘(ℝ, E).prod 𝓘(ℝ)) F (x, t) (V (x, t))) hδ
    hcont.continuousOn hend
  filter_upwards [eventually_gt_atTop (K₀ / C)] with K hK z hz
  have hpos : 0 < z.2 * (1 - z.2 ^ 2) := mul_one_sub_sq_pos_of_mem_Ioo hz
  have hKC : K₀ < K * C := (div_lt_iff₀ hC).1 hK
  calc mvfderiv (𝓘(ℝ, E).prod 𝓘(ℝ)) F z (V z) ≤ K₀ * z.2 * (1 - z.2 ^ 2) := hK₀ z.1 trivial z.2 hz
    _ = K₀ * (z.2 * (1 - z.2 ^ 2)) := mul_assoc _ _ _
    _ < K * C * (z.2 * (1 - z.2 ^ 2)) := mul_lt_mul_of_pos_right hKC hpos
    _ = K * (V z : E × ℝ).2 := by rw [hV.snd_eq z hz]; ring

/-- **A strict Lyapunov function for a continuation field.** For all large `K`, the function
`K t - F (x, t)` strictly increases along every integral curve of the continuation field `V`
meeting the open slab. -/
theorem eventually_strictMono_mul_snd_sub :
    ∀ᶠ K in atTop, ∀ γ : ℝ → M × ℝ, IsMIntegralCurve γ V → ∀ s₀, (γ s₀).2 ∈ Ioo 0 1 →
      StrictMono fun s ↦ K * (γ s).2 - F (γ s) := by
  filter_upwards [hV.eventually_forall_mvfderiv_apply_lt_mul_snd hC hVc hF hF₀ hF₁ hX₀ hX₁]
    with K hK γ hγ s₀ h₀
  -- The derivative of `K t - F` along `γ` is `K (V (γ s)).2 - dF(V (γ s))`, which is positive
  -- since `γ` stays in the open slab.
  have hd (s : ℝ) : HasDerivAt (fun s ↦ K * (γ s).2 - F (γ s))
      (K * (V (γ s) : E × ℝ).2 - mvfderiv (𝓘(ℝ, E).prod 𝓘(ℝ)) F (γ s) (V (γ s))) s :=
    ((IsMIntegralCurve.hasDerivAt_snd hγ s).const_mul K).sub
      (Manifold.hasDerivAt_comp_curve ((hF (γ s)).mdifferentiableAt one_ne_zero) (hγ s))
  exact strictMono_of_hasDerivAt_pos hd fun s ↦
    sub_pos.2 (hK (γ s) (hV.snd_mem_Ioo hγ h₀ hC.ne' s))

/-- **The Lyapunov function along a continuation trajectory.** For all large `K`, along an
integral curve `γ` of the continuation field `V` from `(p, 0)` at `-∞` to `(q, 1)` at `+∞`, the
function `K t - F` takes values strictly between its limits `-f₀ (p)` and `K - f₁ (q)`. In
particular `f₁ (q) - f₀ (p) < K`. -/
theorem eventually_mul_snd_sub_mem_Ioo :
    ∀ᶠ K in atTop, ∀ {p q : M} (γ : ℝ → M × ℝ), IsMIntegralCurve γ V →
      Tendsto γ atBot (𝓝 (p, 0)) → Tendsto γ atTop (𝓝 (q, 1)) →
        ∀ s, K * (γ s).2 - F (γ s) ∈ Ioo (-f₀ p) (K - f₁ q) := by
  filter_upwards [hV.eventually_strictMono_mul_snd_sub hC hVc hF hF₀ hF₁ hX₀ hX₁]
    with K hK p q γ hγ hp hq s
  -- The curve meets the open slab, since its time component runs from `0` to `1`.
  obtain ⟨s₀, hs₀⟩ :=
    (((continuous_snd.tendsto _).comp hp).eventually (gt_mem_nhds one_half_pos)).exists
  obtain ⟨s₁, hs₁⟩ :=
    (((continuous_snd.tendsto _).comp hq).eventually (lt_mem_nhds one_half_lt_one)).exists
  obtain ⟨s', hs'⟩ := intermediate_value_univ s₀ s₁ (continuous_snd.comp hγ.continuous)
    ⟨hs₀.le, hs₁.le⟩
  have hmono := hK γ hγ s' (by rw [Function.comp_apply] at hs'; rw [hs']; norm_num)
  have hL : Continuous fun z : M × ℝ ↦ K * z.2 - F z :=
    (continuous_const.mul continuous_snd).sub hF.continuous
  -- By continuity, `F` is `f₀` on the level `t = 0` and `f₁` on the level `t = 1` themselves.
  have hval {f : M → ℝ} {c : ℝ} {s : Set ℝ} [(𝓝[s] c).NeBot]
      (hFs : ∀ᶠ t in 𝓝[s] c, ∀ x, F (x, t) = f x) (x : M) : F (x, c) = f x :=
    tendsto_nhds_unique
      (((hF.continuous.comp (Continuous.prodMk_right x)).tendsto c).mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hFs.mono fun _ ht ↦ (ht x).symm))
  -- The limits of `K t - F` along `γ` are its values at `(p, 0)` and `(q, 1)`.
  have hbot : Tendsto (fun s ↦ K * (γ s).2 - F (γ s)) atBot (𝓝 (-f₀ p)) := by
    have := (hL.tendsto (p, 0)).comp hp
    rwa [hval hF₀ p, mul_zero, zero_sub] at this
  have htop : Tendsto (fun s ↦ K * (γ s).2 - F (γ s)) atTop (𝓝 (K - f₁ q)) := by
    have := (hL.tendsto (q, 1)).comp hq
    rwa [hval hF₁ q, mul_one] at this
  exact ⟨(hmono.monotone.le_of_tendsto hbot (s - 1)).trans_lt (hmono (by linarith)),
    (hmono (by linarith : s < s + 1)).trans_le (hmono.monotone.ge_of_tendsto htop (s + 1))⟩

end IsContinuationField

/-- **Existence of a strict Lyapunov function for a continuation field.** Let `V` be a continuous
continuation field from `X₀` to `X₁` at rate `C > 0`, and let `f₀` and `f₁` be `C¹` functions
that do not increase along `X₀` and `X₁`. Then there is a `C¹` function `F` on `M × ℝ`, equal to
`f₀` for `t ≤ 1 / 3` and to `f₁` for `t ≥ 2 / 3`, such that for all large `K` the function
`K t - F (x, t)` strictly increases along every integral curve of `V` meeting the open slab, and
along every integral curve from `(p, 0)` at `-∞` to `(q, 1)` at `+∞` takes values strictly between
`-f₀ (p)` and `K - f₁ (q)`. -/
theorem IsContinuationField.exists_strictMono_mul_snd_sub [IsManifold 𝓘(ℝ, E) 1 M]
    [CompactSpace M] {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {C : ℝ}
    {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z} (hV : IsContinuationField X₀ X₁ C V)
    (hC : 0 < C)
    (hVc : Continuous fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 1 f₀) (hf₁ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 1 f₁)
    (hX₀ : ∀ x, mvfderiv 𝓘(ℝ, E) f₀ x (X₀ x) ≤ 0) (hX₁ : ∀ x, mvfderiv 𝓘(ℝ, E) f₁ x (X₁ x) ≤ 0) :
    ∃ F : M × ℝ → ℝ, ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ) 1 F ∧
      (∀ x t, t ≤ 1 / 3 → F (x, t) = f₀ x) ∧ (∀ x t, 2 / 3 ≤ t → F (x, t) = f₁ x) ∧
      ∀ᶠ K in atTop,
        (∀ γ : ℝ → M × ℝ, IsMIntegralCurve γ V → ∀ s₀, (γ s₀).2 ∈ Ioo 0 1 →
          StrictMono fun s ↦ K * (γ s).2 - F (γ s)) ∧
        ∀ {p q : M} (γ : ℝ → M × ℝ), IsMIntegralCurve γ V →
          Tendsto γ atBot (𝓝 (p, 0)) → Tendsto γ atTop (𝓝 (q, 1)) →
            ∀ s, K * (γ s).2 - F (γ s) ∈ Ioo (-f₀ p) (K - f₁ q) := by
  -- Interpolate: `F (x, t) = f₀ x + ρ (3 t - 1) (f₁ x - f₀ x)` for the smooth transition `ρ`
  -- from `0` to `1`.
  set Φ : ℝ × ℝ × ℝ → ℝ := fun w ↦ w.1 + Real.smoothTransition (3 * w.2.2 - 1) * (w.2.1 - w.1)
  have hΦ : ContDiff ℝ 1 Φ :=
    contDiff_fst.add ((Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (contDiff_snd.comp contDiff_snd)).sub contDiff_const)).mul
        ((contDiff_fst.comp contDiff_snd).sub contDiff_fst))
  set F : M × ℝ → ℝ := fun z ↦ Φ (f₀ z.1, f₁ z.1, z.2)
  have hF : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ) 1 F :=
    hΦ.contMDiff.comp ((hf₀.comp contMDiff_fst).prodMk_space
      ((hf₁.comp contMDiff_fst).prodMk_space contMDiff_snd))
  have hF₀ (x : M) (t : ℝ) (ht : t ≤ 1 / 3) : F (x, t) = f₀ x := by
    simp [F, Φ, Real.smoothTransition.zero_of_nonpos (by linarith : 3 * t - 1 ≤ 0)]
  have hF₁ (x : M) (t : ℝ) (ht : 2 / 3 ≤ t) : F (x, t) = f₁ x := by
    simp [F, Φ, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 * t - 1)]
  have hF₀' : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x, F (x, t) = f₀ x :=
    eventually_nhdsWithin_of_eventually_nhds
      ((gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3)).mono fun t ht x ↦ hF₀ x t ht.le)
  have hF₁' : ∀ᶠ t in 𝓝[<] (1 : ℝ), ∀ x, F (x, t) = f₁ x :=
    eventually_nhdsWithin_of_eventually_nhds
      ((lt_mem_nhds (by norm_num : (2 / 3 : ℝ) < 1)).mono fun t ht x ↦ hF₁ x t ht.le)
  exact ⟨F, hF, hF₀, hF₁, (hV.eventually_strictMono_mul_snd_sub hC hVc hF hF₀' hF₁' hX₀ hX₁).and
    (hV.eventually_mul_snd_sub_mem_Ioo hC hVc hF hF₀' hF₁' hX₀ hX₁)⟩

end TauCeti

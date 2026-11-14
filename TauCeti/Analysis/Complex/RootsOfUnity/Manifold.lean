/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RootsOfUnity.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Power
public import TauCeti.Geometry.Manifold.Instances.OpenBall.Basic

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.Analysis.Complex.RootsOfUnity.Quotient
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# The rotated disc as a complex manifold

The open disc `TauCeti.rootsOfUnityBall m r` of radius `r` about `0` in `ℂ` is an open subset of
`ℂ`, so it is a complex manifold modelled on `ℂ`, with the charts of `ℂ` restricted to it. The
group `rootsOfUnity m ℂ` of `m`-th roots of unity acts on it by the rotations `u ↦ ζ u`, which
are restrictions of complex linear maps of `ℂ`, hence holomorphic.

These instances make the disc with its rotations a base to which the manifold and quotient
constructions for actions by `C^n` maps apply, for instance families of complex tori over the disc
on which the rotations lift.

## Main declarations

* `TauCeti.rootsOfUnityBall.opens`: the disc as an open subset of `ℂ`, whose subtype is the
  disc itself.
* `TauCeti.rootsOfUnityBall.instChartedSpace`, `TauCeti.rootsOfUnityBall.instIsManifold`: the disc
  is a `C^n` manifold modelled on `ℂ` for every `n`; for `n = ω` it is a complex manifold.
* `TauCeti.rootsOfUnityBall.contMDiff_val`: the inclusion of the disc into `ℂ` is holomorphic.
* `TauCeti.rootsOfUnityBall.coe_chartAt_symm`: the inverse of a chart of the disc is the identity
  of `ℂ` on its target.
* `TauCeti.rootsOfUnityBall.instContMDiffConstSMul`: the rotations act on the disc by `C^n` maps,
  that is, by biholomorphisms.
* `TauCeti.rootsOfUnityBall.exists_contMDiffAt_root_and_log`: near a nonzero point, the power map
  `u ↦ u ^ m` between the discs has a holomorphic local section together with a holomorphic
  logarithm of it.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {m : ℕ} [NeZero m] {r : ℝ} {n : ℕ∞ω}

namespace rootsOfUnityBall

variable (m r) in
/-- The disc of radius `r` as an open subset of `ℂ`. Its carrier is `Metric.ball 0 r`, the carrier
of `rootsOfUnityBall m r`, so its subtype is definitionally the subtype of `rootsOfUnityBall m r`;
the instances below transfer the open-subset manifold structure of `ℂ` along this equality. -/
noncomputable def opens : TopologicalSpace.Opens ℂ :=
  ⟨rootsOfUnityBall m r, isOpen_rootsOfUnityBall⟩

/-- The disc of radius `r` is an open subset of `ℂ`, so it inherits the charts of `ℂ`. -/
noncomputable instance instChartedSpace : ChartedSpace ℂ (rootsOfUnityBall m r) :=
  inferInstanceAs (ChartedSpace ℂ (opens m r))

/-- The disc of radius `r` is a `C^n` manifold modelled on `ℂ`; for `n = ω` it is a complex
manifold. -/
instance instIsManifold : IsManifold 𝓘(ℂ) n (rootsOfUnityBall m r) :=
  inferInstanceAs (IsManifold 𝓘(ℂ) n (opens m r))

/-- The rotations by the `m`-th roots of unity act on the disc of radius `r` by `C^n` maps; for
`n = ω` they are biholomorphisms of the disc. -/
instance instContMDiffConstSMul : ContMDiffConstSMul 𝓘(ℂ) n (rootsOfUnity m ℂ)
    (rootsOfUnityBall m r) where
  contMDiff_const_smul ζ := by
    have h : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (Subtype.val ∘ fun u : opens m r ↦
        (⟨ζ • (u : ℂ), (rootsOfUnityBall m r).smul_mem ζ u.2⟩ : opens m r)) :=
      (contMDiff_iff_contDiff.2 (contDiff_const_smul ((ζ : ℂˣ) : ℂ))).comp contMDiff_subtype_val
    exact fun u ↦ (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).1 (h u)

/-- The inclusion of the disc of radius `r` into `ℂ` is `C^n`; it is holomorphic. -/
theorem contMDiff_val : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n ((↑) : rootsOfUnityBall m r → ℂ) :=
  contMDiff_subtype_val (U := opens m r)

/-- The charts of the disc are restrictions of the identity chart of `ℂ`: the inverse of a chart
sends each point of its target to that point of the disc. -/
theorem coe_chartAt_symm (u : rootsOfUnityBall m r) {w : ℂ} (hw : w ∈ (chartAt ℂ u).target) :
    ((chartAt ℂ u).symm w : ℂ) = w := by
  -- The charts of the disc are by definition those of `opens m r`, which
  -- `TopologicalSpace.Opens.chartAt_eq` identifies with restrictions of the charts of `ℂ`; the
  -- chart of `ℂ` at `u` is the identity (`chartAt_self_eq`).
  have h : chartAt ℂ u = (chartAt ℂ (u : ℂ)).subtypeRestr (s := opens m r) ⟨u⟩ :=
    TopologicalSpace.Opens.chartAt_eq (x := (u : opens m r))
  rw [h] at hw ⊢
  exact (chartAt ℂ (u : ℂ)).subtypeRestr_symm_apply ⟨u⟩ hw

end rootsOfUnityBall

/-- The inclusion of the rotated disc into `ℂ` is a local biholomorphism. -/
theorem isLocalDiffeomorph_coe_rootsOfUnityBall {n : ℕ∞ω} :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) n ((↑) : rootsOfUnityBall m r → ℂ) :=
  isLocalDiffeomorph_subtype_val (U := ⟨_, isOpen_rootsOfUnityBall⟩)

/-- The coordinate `u ↦ u ^ m` of the quotient of the rotated disc is holomorphic. -/
theorem contMDiff_coe_pow_rootsOfUnityBall {n : ℕ∞ω} :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n fun u : rootsOfUnityBall m r ↦ (u : ℂ) ^ m :=
  (contDiff_id.pow m).contMDiff.comp isLocalDiffeomorph_coe_rootsOfUnityBall.contMDiff

/-- The power map between the two discs is holomorphic for their open-subset atlases. -/
theorem rootsOfUnityBall.contMDiff_powMap {n : ℕ∞ω} :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (rootsOfUnityBall.powMap m r) := by
  apply (contMDiff_subtypeVal_ball_comp_iff _).1
  simpa only [Function.comp_def, rootsOfUnityBall.coe_powMap] using
    (contMDiff_coe_pow_rootsOfUnityBall (m := m) (r := r) (n := n))

/-- **The quotient coordinate is a local biholomorphism off the centre.** For `1 ≤ n`, the map
`u ↦ u ^ m` from the rotated disc to `ℂ` is a `C^n` local diffeomorphism at every point other
than the centre. -/
theorem isLocalDiffeomorphAt_coe_pow_rootsOfUnityBall {n : ℕ∞ω} (hn : 1 ≤ n)
    {u : rootsOfUnityBall m r} (hu : (u : ℂ) ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) n (fun u : rootsOfUnityBall m r ↦ (u : ℂ) ^ m) u :=
  IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ)) (P := ℂ) (isLocalDiffeomorph_coe_rootsOfUnityBall u)
    (isLocalDiffeomorphAt_pow hn (NeZero.ne m) hu)

/-- **Holomorphic local roots and their logarithms.** For `0 ≤ r` and `t₀ ≠ 0` in the disc of
radius `r ^ m`, there are maps `L` to `ℂ` and `w` to the disc of radius `r`, both `C^n` at `t₀`
(holomorphic for `n ≠ 0`), such that every `t ≠ 0` has `w t ^ m = t` and `exp (L t) = w t`. Near
`t₀` they are given by the branch `L t = log z₀ + (1 / m) log (t / z₀ ^ m)` for an `m`-th root `z₀`
of `t₀`, which is holomorphic even when `t₀` lies on the branch cut of the principal logarithm. -/
theorem rootsOfUnityBall.exists_contMDiffAt_root_and_log (hr : 0 ≤ r)
    {t₀ : Metric.ball (0 : ℂ) (r ^ m)} (ht₀ : (t₀ : ℂ) ≠ 0) :
    ∃ (L : Metric.ball (0 : ℂ) (r ^ m) → ℂ)
      (w : Metric.ball (0 : ℂ) (r ^ m) → rootsOfUnityBall m r),
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n L t₀ ∧ ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n w t₀ ∧
        ∀ t : Metric.ball (0 : ℂ) (r ^ m), (t : ℂ) ≠ 0 →
          rootsOfUnityBall.powMap m r (w t) = t ∧ Complex.exp (L t) = w t := by
  set z₀ := rootsOfUnityBall.rootMap hr t₀
  have hz₀m : (z₀ : ℂ) ^ m = t₀ := by
    rw [← rootsOfUnityBall.coe_powMap, rootsOfUnityBall.powMap_rootMap]
  have hz₀ : (z₀ : ℂ) ≠ 0 := fun h ↦ ht₀ (by rw [← hz₀m, h, zero_pow (NeZero.ne m)])
  let L : Metric.ball (0 : ℂ) (r ^ m) → ℂ := fun t ↦
    Complex.log z₀ + (m : ℂ)⁻¹ * Complex.log (t / (z₀ : ℂ) ^ m)
  have hmem (t : Metric.ball (0 : ℂ) (r ^ m)) : Complex.exp (L t) ∈ rootsOfUnityBall m r := by
    by_cases ht : (t : ℂ) = 0
    · simp only [L, ht, zero_div, Complex.log_zero, mul_zero, add_zero, Complex.exp_log hz₀]
      exact z₀.2
    · rw [mem_rootsOfUnityBall, ← pow_lt_pow_iff_left₀ (norm_nonneg _) hr (NeZero.ne m),
        ← norm_pow, Complex.exp_log_add_inv_mul_log_div_pow hz₀ ht, ← mem_ball_zero_iff]
      exact t.2
  -- The branch is holomorphic at `t₀`, where `t / z₀ ^ m = 1` lies in the slit plane.
  have hlog : ContDiffAt ℂ n (fun t ↦ Complex.log (t / (z₀ : ℂ) ^ m)) t₀ := by
    have h := (Complex.contDiffAt_log (n := n) (x := (t₀ : ℂ) / (z₀ : ℂ) ^ m)
      (by rw [hz₀m, div_self ht₀]; exact Complex.one_mem_slitPlane)).comp (t₀ : ℂ)
      (contDiffAt_id.div_const ((z₀ : ℂ) ^ m))
    exact h
  have hL : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n L t₀ := by
    have h := ((contDiffAt_const (c := Complex.log z₀)).add
      ((contDiffAt_const (c := (m : ℂ)⁻¹)).mul hlog)).contMDiffAt.comp t₀
      (contMDiff_subtypeVal_ball (I := 𝓘(ℂ)) (n := n) (c := (0 : ℂ)) (r := r ^ m)).contMDiffAt
    exact h
  let w : Metric.ball (0 : ℂ) (r ^ m) → rootsOfUnityBall m r := fun t ↦
    ⟨Complex.exp (L t), hmem t⟩
  have hexp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n (((↑) : rootsOfUnityBall m r → ℂ) ∘ w) t₀ :=
    Complex.contDiff_exp.contMDiff.contMDiffAt.comp t₀ hL
  refine ⟨L, w, hL, ?_, fun t ht ↦ ⟨?_, rfl⟩⟩
  · -- The inclusion of the disc of radius `r` is a local diffeomorphism.
    exact contMDiffWithinAt_univ.1 (ContMDiffWithinAt.of_comp_isLocalDiffeomorph
      (isLocalDiffeomorph_coe_rootsOfUnityBall _)
      ((Topology.IsInducing.subtypeVal.continuousAt_iff (f := w)).2
        hexp.continuousAt).continuousWithinAt
      (contMDiffWithinAt_univ.2 hexp))
  · exact Subtype.ext (by
      rw [rootsOfUnityBall.coe_powMap]; exact Complex.exp_log_add_inv_mul_log_div_pow hz₀ ht)

end TauCeti

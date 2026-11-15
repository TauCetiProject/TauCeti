/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Linear
import TauCeti.Analysis.Normed.Operator.NondegenerateIterate
import TauCeti.Dynamics.PeriodicPts.LocalPerturbation

/-!
# Making a periodic orbit nondegenerate in finitely many iterates by a local perturbation

Let `φ : E → E` be a map of a finite-dimensional real normed space and `p` a periodic point of
period `k`, with linearized return map `L`, the derivative of `φ^[k]` at `p`. The `m`-fold cover
of the orbit is nondegenerate when `L ^ m` does not have `1` as an eigenvalue. Kupka–Smale type
genericity statements make all covers of bounded multiplicity nondegenerate by an arbitrarily
small perturbation localized near one point of the orbit. This includes the resonant case, where
the orbit is nondegenerate but some cover is not, as for `L = -1` and its double cover, so the
perturbation must treat all the required iterates at once.

The perturbation used here is linear near `p`: for a cutoff function `χ` equal to `1` near `p`
and an operator `B`, the **local linear perturbation**
(`TauCeti.localLinearPerturbation`) is

`ψ_B(x) = x + χ(x) • B (x - p)`.

It fixes `p`, is the identity outside the support of `χ`, and has derivative `1 + B` at `p`. Its
displacement `ψ_B(x) - x = χ(x) • B (x - p)` is linear in `B`
(`TauCeti.localLinearPerturbation_sub_self`), so for a fixed cutoff the size of the perturbation is
controlled by `‖B‖` alone. If the support of `χ` avoids the other points
of the orbit, then `p` is still a periodic point of period `k` of `φ ∘ ψ_B`, and its linearized
return map is `L * (1 + B)` (`HasFDerivAt.iterate_comp_of_eventuallyEq_id`). For a generic `B` no
power `(L * (1 + B)) ^ m` with `m` in a prescribed set of positive integers has the
eigenvalue `1` (`ContinuousLinearMap.dense_setOf_forall_det_one_sub_pow_mul_ne_zero`), so such
`B` can be found of arbitrarily small norm. The prescribed set can be finite, as for the closed
orbits of bounded period, or consist of all positive integers.

For the closed orbits of a vector field this is the statement about return maps: the first-return
map of a transverse section is a map `φ` of this kind, and the covers of the closed orbit are the
iterates of its fixed point.

## Main definitions

* `TauCeti.localLinearPerturbation χ p B`: the map `x ↦ x + χ x • B (x - p)`.

## Main results

* `TauCeti.hasFDerivAt_localLinearPerturbation`: its derivative at `p` is `1 + B` when `χ = 1`
  near `p`.
* `TauCeti.contDiff_localLinearPerturbation`: it is as smooth as its cutoff.
* `TauCeti.localLinearPerturbation_eventuallyEq_id`: it is the identity near every point outside
  the support of `χ`.
* `TauCeti.exists_norm_lt_isPeriodicPt_comp_localLinearPerturbation`: for a cutoff whose support
  avoids the other orbit points, an arbitrarily small `B` keeps `p` periodic of period `k`, with
  linearized return map `L * (1 + B)` whose powers `(L * (1 + B)) ^ m`, `m ∈ s`, do not have the
  eigenvalue `1`.
* `TauCeti.exists_cutoff_forall_exists_norm_lt_isPeriodicPt_comp_localLinearPerturbation`: for
  the minimal period, a smooth compactly supported cutoff inside any prescribed neighbourhood of
  `p` exists, so that the orbit can be made nondegenerate in the covers `m ∈ s` by
  arbitrarily small local linear perturbations.

## References

* J. Palis and W. de Melo, *Geometric Theory of Dynamical Systems*, Springer, 1982, Chapter 3, §3
  (the Kupka–Smale theorem, where the periodic orbits of bounded period are made hyperbolic by
  perturbations localized near one point of each orbit).
* M. M. Peixoto, *On an approximation theorem of Kupka and Smale*, J. Differential Equations
  **3** (1967), 214–227, §2.
-/

public section

open Filter Function Topology
open scoped ContDiff

namespace TauCeti

section General

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {χ : E → 𝕜} {p x : E} {B : E →L[𝕜] E}

/-- The **local linear perturbation** `x ↦ x + χ x • B (x - p)` of the identity at `p`, with
cutoff `χ` and linear part `B`. When `χ = 1` near `p` it agrees near `p` with the affine map
`x ↦ x + B (x - p)`, and it is the identity wherever `χ` vanishes. -/
noncomputable def localLinearPerturbation (χ : E → 𝕜) (p : E) (B : E →L[𝕜] E) (x : E) : E :=
  x + χ x • B (x - p)

theorem localLinearPerturbation_apply (χ : E → 𝕜) (p : E) (B : E →L[𝕜] E) (x : E) :
    localLinearPerturbation χ p B x = x + χ x • B (x - p) :=
  (rfl)

/-- The displacement of a local linear perturbation, which is linear in `B`. -/
theorem localLinearPerturbation_sub_self (χ : E → 𝕜) (p : E) (B : E →L[𝕜] E) (x : E) :
    localLinearPerturbation χ p B x - x = χ x • B (x - p) := by
  rw [localLinearPerturbation_apply, add_sub_cancel_left]

/-- A local linear perturbation fixes its base point. -/
@[simp]
theorem localLinearPerturbation_self (χ : E → 𝕜) (p : E) (B : E →L[𝕜] E) :
    localLinearPerturbation χ p B p = p := by
  simp [localLinearPerturbation_apply]

/-- The local linear perturbation with linear part `0` is the identity. -/
@[simp]
theorem localLinearPerturbation_zero (χ : E → 𝕜) (p : E) :
    localLinearPerturbation χ p (0 : E →L[𝕜] E) = id := by
  ext x
  simp [localLinearPerturbation_apply]

theorem norm_localLinearPerturbation_sub_self_le (χ : E → 𝕜) (p : E) (B : E →L[𝕜] E) (x : E) :
    ‖localLinearPerturbation χ p B x - x‖ ≤ ‖χ x‖ * (‖B‖ * ‖x - p‖) := by
  rw [localLinearPerturbation_sub_self, norm_smul]
  gcongr
  exact B.le_opNorm _

/-- A local linear perturbation is the identity near every point outside the support of its
cutoff. -/
theorem localLinearPerturbation_eventuallyEq_id (hx : x ∉ tsupport χ) :
    localLinearPerturbation χ p B =ᶠ[𝓝 x] id := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
  simp [localLinearPerturbation_apply, hy]

/-- A local linear perturbation is as smooth as its cutoff. -/
theorem contDiff_localLinearPerturbation {n : WithTop ℕ∞} (hχ : ContDiff 𝕜 n χ) :
    ContDiff 𝕜 n (localLinearPerturbation χ p B) := by
  unfold TauCeti.localLinearPerturbation
  fun_prop

/-- **The derivative of a local linear perturbation at its base point.** If the cutoff is `1`
near `p`, the derivative at `p` is `1 + B`. -/
theorem hasFDerivAt_localLinearPerturbation (hχ : χ =ᶠ[𝓝 p] 1) :
    HasFDerivAt (localLinearPerturbation χ p B) (1 + B) p := by
  have h : HasFDerivAt (fun x : E ↦ x + B (x - p)) (1 + B) p := by
    convert (hasFDerivAt_id p).add (B.hasFDerivAt.comp p ((hasFDerivAt_id p).sub_const p))
      using 1 <;> ext v <;> simp
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hχ] with x hx
  simp [localLinearPerturbation_apply, hx]

end General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {φ : E → E} {p : E} {k : ℕ} {L : E →L[ℝ] E} {s : Set ℕ}

/-- **Making the covers of a periodic orbit nondegenerate by a small local perturbation.** Let `p`
be a periodic point of period `k > 0` of `φ`, with linearized return map `L`, and let `χ` be a
cutoff equal to `1` near `p` whose support avoids the other orbit points `φ^[j] p`, `0 < j < k`.
For a set `s` of positive integers and every `δ > 0` there is an operator `B` with
`‖B‖ < δ` such that `p` is a periodic point of period `k` of `φ ∘ ψ_B`, where `ψ_B` is the local
linear perturbation `x ↦ x + χ x • B (x - p)`, its linearized return map is `L * (1 + B)`, and no
power `(L * (1 + B)) ^ m` with `m ∈ s` has the eigenvalue `1`. -/
theorem exists_norm_lt_isPeriodicPt_comp_localLinearPerturbation {χ : E → ℝ} (hk : 0 < k)
    (hp : IsPeriodicPt φ k p) (hL : HasFDerivAt φ^[k] L p)
    (hφ : ∀ j < k, ContinuousAt φ (φ^[j] p)) (hχ : χ =ᶠ[𝓝 p] 1)
    (hχk : ∀ j, 0 < j → j < k → φ^[j] p ∉ tsupport χ) (h0 : 0 ∉ s)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : E →L[ℝ] E, ‖B‖ < δ ∧ IsPeriodicPt (φ ∘ localLinearPerturbation χ p B) k p ∧
      HasFDerivAt (φ ∘ localLinearPerturbation χ p B)^[k] (L * (1 + B)) p ∧
      ∀ m ∈ s, (1 - (L * (1 + B)) ^ m).det ≠ 0 := by
  obtain ⟨B, hB, hBs⟩ :=
    ContinuousLinearMap.exists_norm_lt_forall_det_one_sub_pow_mul_one_add_ne_zero L h0 hδ
  have hid : ∀ j, 0 < j → j < k →
      localLinearPerturbation χ p B =ᶠ[𝓝 (φ^[j] p)] id := fun j hj hjk ↦
    localLinearPerturbation_eventuallyEq_id (hχk j hj hjk)
  have hψ := hasFDerivAt_localLinearPerturbation (B := B) hχ
  have hiter := iterate_comp_eventuallyEq_of_eventuallyEq_id hk
    (localLinearPerturbation_self χ p B) hψ.continuousAt hφ hid
  refine ⟨B, hB, ?_, ?_, hBs⟩
  · rw [IsPeriodicPt, IsFixedPt, hiter.eq_of_nhds, comp_apply, localLinearPerturbation_self]
    exact hp
  · exact hL.iterate_comp_of_eventuallyEq_id hψ hk (localLinearPerturbation_self χ p B) hφ hid

/-- **Making a periodic orbit nondegenerate in prescribed covers by arbitrarily small local
perturbations.** Let `p` be a periodic point of `φ` of minimal period `k`, with linearized return
map `L`, and let `U` be a neighbourhood of `p`. There is a smooth compactly supported cutoff `χ`,
supported in `U`, such that for every `δ > 0` some local linear perturbation
`ψ_B(x) = x + χ x • B (x - p)` with `‖B‖ < δ` keeps `p` periodic of period `k` for `φ ∘ ψ_B`, with
linearized return map `L * (1 + B)`, none of whose powers `(L * (1 + B)) ^ m`, `m ∈ s`, has the
eigenvalue `1`. The cutoff does not depend on `δ`, and the displacement `χ(x) • B (x - p)` of
`ψ_B` is linear in `B`, so the perturbations are as small as `‖B‖`. -/
theorem exists_cutoff_forall_exists_norm_lt_isPeriodicPt_comp_localLinearPerturbation
    [FiniteDimensional ℝ E] (hp : p ∈ periodicPts φ) (hL : HasFDerivAt φ^[minimalPeriod φ p] L p)
    (hφ : ∀ j < minimalPeriod φ p, ContinuousAt φ (φ^[j] p)) {U : Set E} (hU : U ∈ 𝓝 p)
    (h0 : 0 ∉ s) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ χ =ᶠ[𝓝 p] 1 ∧
      ∀ δ : ℝ, 0 < δ → ∃ B : E →L[ℝ] E, ‖B‖ < δ ∧
        IsPeriodicPt (φ ∘ localLinearPerturbation χ p B) (minimalPeriod φ p) p ∧
        HasFDerivAt (φ ∘ localLinearPerturbation χ p B)^[minimalPeriod φ p] (L * (1 + B)) p ∧
        ∀ m ∈ s, (1 - (L * (1 + B)) ^ m).det ≠ 0 := by
  set k := minimalPeriod φ p
  have hk : 0 < k := minimalPeriod_pos_of_mem_periodicPts hp
  -- The other orbit points form a finite set not containing `p`.
  set O : Set E := (fun j ↦ φ^[j] p) '' Set.Ioo 0 k
  have hpO : p ∉ O := by
    rintro ⟨j, ⟨hj, hjk⟩, hjp⟩
    have := iterate_injOn_Iio_minimalPeriod (f := φ) (x := p) (Set.mem_Iio.2 hjk)
      (Set.mem_Iio.2 hk) (by simpa using hjp)
    omega
  have hUO : U ∩ Oᶜ ∈ 𝓝 p :=
    inter_mem hU (((Set.finite_Ioo 0 k).image _).isClosed.isOpen_compl.mem_nhds hpO)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hUO
  let f : ContDiffBump p := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hrOut : f.rOut = ε / 2 := rfl
  have hsupp : tsupport f ⊆ U ∩ Oᶜ := by
    rw [f.tsupport_eq, hrOut]
    exact (Metric.closedBall_subset_ball (by linarith)).trans hεU
  refine ⟨f, f.contDiff, f.hasCompactSupport, hsupp.trans Set.inter_subset_left, f.eventuallyEq_one,
    fun δ hδ ↦ exists_norm_lt_isPeriodicPt_comp_localLinearPerturbation hk
      (isPeriodicPt_minimalPeriod φ p) hL hφ f.eventuallyEq_one (fun j hj hjk hjO ↦ ?_) h0 hδ⟩
  exact (hsupp hjO).2 ⟨j, ⟨hj, hjk⟩, rfl⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.LocalInjectivity
public import TauCeti.Geometry.Symplectic.Floer.Translation.Kernel
public import TauCeti.Topology.Instances.Real.SliceInjective
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Regular points of Floer trajectories

Let `u : ℝ × ℝ → V` be a Floer trajectory in a symplectic vector space, converging to the loops
`xm` and `xp` as `s → -∞` and `s → +∞`. Floer, Hofer and Salamon prove transversality for the
moduli spaces of Floer trajectories with respect to variations of a time-dependent almost complex
structure `J_t` at their *regular points*: the points `(s, t)` with

* `∂ₛu(s, t) ≠ 0`,
* `u(s, t) ≠ xm(t)` and `u(s, t) ≠ xp(t)`, and
* `u(s', t) ≠ u(s, t)` for every `s' ≠ s`

(`TauCeti.Floer.regularPoints`). The last condition says that `(s, t)` is the only preimage of
`(u(s, t), t)` under the map `(s, t) ↦ (u(s, t), t)`: a variation of `J_t` supported near
`u(s, t)` at time `t` is then felt by the trajectory only near `(s, t)`.
`TauCeti.SymplecticForm.eq_zero_of_integral_apply_deriv_floerOperator_eq_zero` is the related
statement detecting cokernel elements of the linearized operator by variations of a
time-independent `J` at injective points `z₀` of `u` (where `u z` near `u z₀` forces `z` near
`z₀`) with `∂ₜu - X_{K_t}(u) ≠ 0`.

This file proves two parts of the theorem of Floer, Hofer and Salamon that the regular points of
a nonstationary trajectory form an open dense set.

* **Openness.** If `u` is `C¹` and converges uniformly to continuous loops `xm` and `xp`, the
  regular points form an open set (`TauCeti.Floer.isOpen_regularPoints`). The topological core
  (`TauCeti.eventually_forall_slice_eq_imp_eq_of_tendsto`) needs only a continuous map into a
  Hausdorff space with limits along the ends, and injectivity of `(s, t) ↦ (u(s, t), t)` near the
  point, which `∂ₛu ≠ 0` provides (`TauCeti.Floer.exists_mem_nhds_injOn_of_fderiv_apply_ne_zero`,
  from the injectivity of its derivative). The limits confine the competitors `s'` to a compact
  interval, and a compactness argument separates `u(s', t)` from `u(s, t)` uniformly nearby.
* **Separation from the asymptotic orbits.** On an open set where `u(s, t) = x(t)`, `u` does not
  depend on `s`, so `∂ₛu` vanishes there
  (`TauCeti.Floer.interior_setOf_eq_subset_setOf_fderiv_apply_eq_zero`). As the zeros of `∂ₛu` are
  isolated unless `u` is stationary
  (`SymplecticForm.setOf_fderiv_apply_ne_zero_mem_codiscreteWithin_of_floerOperator_eq_zero`),
  the points where `∂ₛu ≠ 0`, `u ≠ xm` and `u ≠ xp` form a dense set for every nonstationary
  Floer trajectory
  (`TauCeti.Floer.dense_setOf_fderiv_apply_ne_zero_and_ne_and_ne_of_floerOperator_eq_zero`).

The density of the points satisfying the third condition is not proved here.

## References

* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. **80** (1995), 251–292 (the regular points of a Floer trajectory).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7** (1999), 143–229.
-/

public section

open Filter Function Metric Set Topology

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {u : ℝ × ℝ → V} {x xm xp : ℝ → V}

/-- **A nonvanishing `∂ₛu` makes `(s, t) ↦ (u(s, t), t)` injective nearby.** If `u` is `C¹` at
`z₀` with `∂ₛu(z₀) ≠ 0`, then two points near `z₀` on one horizontal line `t = const` have
different images under `u`. -/
theorem exists_mem_nhds_injOn_of_fderiv_apply_ne_zero {z₀ : ℝ × ℝ} (hu : ContDiffAt ℝ 1 u z₀)
    (h : fderiv ℝ u z₀ stdComplexLineReal ≠ 0) :
    ∃ U ∈ 𝓝 z₀, InjOn (fun z ↦ (u z, z.2)) U := by
  have hd : fderiv ℝ (fun z ↦ (u z, z.2)) z₀ =
      (fderiv ℝ u z₀).prod (ContinuousLinearMap.snd ℝ ℝ ℝ) :=
    ((hu.differentiableAt one_ne_zero).hasFDerivAt.prodMk (hasFDerivAt_snd (p := z₀))).fderiv
  -- The derivative `v ↦ (du v, v.2)` is injective: `v.2 = 0` makes `v` a multiple of `∂ₛ`.
  have hinj : Injective (fderiv ℝ (fun z ↦ (u z, z.2)) z₀) := by
    rw [hd, injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj hv
    have hv' : v = v.1 • stdComplexLineReal := by
      ext <;> simp_all [stdComplexLineReal_eq]
    rw [hv', map_smul, smul_eq_zero] at h₁
    rw [hv', h₁.resolve_right h, zero_smul]
  simpa only [nhdsWithin_univ] using
    ((hu.prodMk contDiffAt_snd).contDiffWithinAt (s := univ)).exists_nhdsWithin_injOn
      one_ne_zero convex_univ (mem_univ _) uniqueDiffWithinAt_univ (by rwa [fderivWithin_univ])

/-- The regular points of Floer, Hofer and Salamon of a map `u : ℝ × ℝ → V` relative to loops
`xm` and `xp`: the points `(s, t)` with `∂ₛu(s, t) ≠ 0`, `u(s, t) ≠ xm(t)`, `u(s, t) ≠ xp(t)`
and `u(s', t) ≠ u(s, t)` for all `s' ≠ s`. For a Floer trajectory, `xm` and `xp` are its
asymptotic orbits. -/
def regularPoints (u : ℝ × ℝ → V) (xm xp : ℝ → V) : Set (ℝ × ℝ) :=
  {z | fderiv ℝ u z stdComplexLineReal ≠ 0 ∧ u z ≠ xm z.2 ∧ u z ≠ xp z.2 ∧
    ∀ s, u (s, z.2) = u z → s = z.1}

@[simp]
theorem mem_regularPoints {z : ℝ × ℝ} :
    z ∈ regularPoints u xm xp ↔ fderiv ℝ u z stdComplexLineReal ≠ 0 ∧ u z ≠ xm z.2 ∧
      u z ≠ xp z.2 ∧ ∀ s, u (s, z.2) = u z → s = z.1 :=
  Iff.rfl

/-- **The regular points form an open set.** If `u` is `C¹` and converges, uniformly in `t`, to
continuous loops `xm` and `xp` as `s → -∞` and `s → +∞`, then its regular points form an open
subset of `ℝ × ℝ`. -/
theorem isOpen_regularPoints (hu : ContDiff ℝ 1 u) (hxm : Continuous xm) (hxp : Continuous xp)
    (hm : TendstoUniformly (fun s t ↦ u (s, t)) xm atBot)
    (hp : TendstoUniformly (fun s t ↦ u (s, t)) xp atTop) :
    IsOpen (regularPoints u xm xp) := by
  -- Uniform convergence along an end gives convergence as `s` tends to the end and `t → t₀`.
  have hlim {l : Filter ℝ} {x : ℝ → V} (h : TendstoUniformly (fun s t ↦ u (s, t)) x l)
      (hx : Continuous x) (t₀ : ℝ) : Tendsto u (l ×ˢ 𝓝 t₀) (𝓝 (x t₀)) := by
    have h' : TendstoUniformly (fun (p : ℝ × ℝ) t ↦ u (p.1, t)) x (l ×ˢ 𝓝 t₀) :=
      fun U hU ↦ tendsto_fst.eventually (h U hU)
    exact h'.tendsto_comp hx.continuousAt tendsto_snd
  have hcont : Continuous u := hu.continuous
  refine isOpen_iff_mem_nhds.2 fun z hz ↦ ?_
  obtain ⟨hd, hmz, hpz, hinj⟩ := hz
  filter_upwards [((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousAt
      |>.eventually_ne hd,
    (hcont.continuousAt.ne_iff_eventually_ne (hxm.comp continuous_snd).continuousAt).1 hmz,
    (hcont.continuousAt.ne_iff_eventually_ne (hxp.comp continuous_snd).continuousAt).1 hpz,
    eventually_forall_slice_eq_imp_eq_of_tendsto hcont (hlim hm hxm z.2) (hlim hp hxp z.2)
      (exists_mem_nhds_injOn_of_fderiv_apply_ne_zero hu.contDiffAt hd) hmz hpz hinj]
    with w h₁ h₂ h₃ h₄
  exact ⟨h₁, h₂, h₃, h₄⟩

/-- **`∂ₛu` vanishes where `u` follows a loop.** On the interior of the set of points where
`u(s, t) = x(t)`, the map `u` does not depend on `s`, so `∂ₛu = 0` there. -/
theorem interior_setOf_eq_subset_setOf_fderiv_apply_eq_zero :
    interior {z : ℝ × ℝ | u z = x z.2} ⊆ {z | fderiv ℝ u z stdComplexLineReal = 0} := by
  intro z hz
  by_cases hd : DifferentiableAt ℝ u z
  · rw [mem_ofPred_eq, ← hd.lineDeriv_eq_fderiv]
    have ht : Tendsto (fun c : ℝ ↦ z + c • stdComplexLineReal) (𝓝 0) (𝓝 z) := by
      simpa using ((continuous_id.smul continuous_const).const_add z).tendsto (0 : ℝ)
    have hconst : (fun c : ℝ ↦ u (z + c • stdComplexLineReal)) =ᶠ[𝓝 0] fun _ ↦ x z.2 := by
      filter_upwards [ht.eventually (mem_interior_iff_mem_nhds.1 hz)] with c hc
      simpa [stdComplexLineReal_eq] using hc
    rw [lineDeriv, hconst.deriv_eq, deriv_const]
  · simp [fderiv_zero_of_not_differentiableAt hd]

/-- **Points away from the critical points of `s ↦ u` and from two loops are dense.** Let `u` be
continuous, with `∂ₛu ≠ 0` on a dense set, and let `xm` and `xp` be continuous loops. Then the
points where `∂ₛu ≠ 0`, `u(s, t) ≠ xm(t)` and `u(s, t) ≠ xp(t)` form a dense set. -/
theorem dense_setOf_fderiv_apply_ne_zero_and_ne_and_ne (hu : Continuous u)
    (hxm : Continuous xm) (hxp : Continuous xp)
    (h : Dense {z | fderiv ℝ u z stdComplexLineReal ≠ 0}) :
    Dense {z | fderiv ℝ u z stdComplexLineReal ≠ 0 ∧ u z ≠ xm z.2 ∧ u z ≠ xp z.2} := by
  -- The points where `u` meets a continuous loop form a closed set with empty interior.
  have hloop {x : ℝ → V} (hx : Continuous x) :
      Dense {z : ℝ × ℝ | u z ≠ x z.2} ∧ IsOpen {z : ℝ × ℝ | u z ≠ x z.2} := by
    refine ⟨?_, isOpen_ne_fun hu (hx.comp continuous_snd)⟩
    have hcrit : interior {z | fderiv ℝ u z stdComplexLineReal = 0} = ∅ :=
      interior_eq_empty_iff_dense_compl.2 (by simpa only [compl_ofPred] using h)
    have hint : interior {z : ℝ × ℝ | u z = x z.2} = ∅ :=
      subset_empty_iff.1 (hcrit ▸ interior_maximal
        interior_setOf_eq_subset_setOf_fderiv_apply_eq_zero isOpen_interior)
    simpa only [compl_ofPred] using interior_eq_empty_iff_dense_compl.1 hint
  obtain ⟨hdm, hom⟩ := hloop hxm
  obtain ⟨hdp, hop⟩ := hloop hxp
  simpa only [ofPred_and, inter_assoc] using
    (h.inter_of_isOpen_right hdm hom).inter_of_isOpen_right hdp hop

/-- **Separation from the asymptotic orbits.** Let `u` be a `C²` solution of the Floer equation
`∂ₛu - X_{K_s}(u) + J(u)(∂ₜu - X_{K_t}(u)) = 0` on `ℝ × ℝ` whose data `J`, `K_s`, `K_t` are
invariant under small translations in `s`, as for a Floer trajectory, with `J` of class `C¹`, the
Hamiltonians of class `C²` near the graph of `u` and `J(z, u z)² = -1`. If `u` is not stationary,
that is `∂ₛu` does not vanish identically, then for continuous loops `xm` and `xp` the points where
`∂ₛu ≠ 0`, `u(s, t) ≠ xm(t)` and `u(s, t) ≠ xp(t)` form a dense set. -/
theorem dense_setOf_fderiv_apply_ne_zero_and_ne_and_ne_of_floerOperator_eq_zero
    {ω : SymplecticForm V} [FiniteDimensional ℝ V] {J : ℝ × ℝ → V → V →L[ℝ] V}
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hJs : ∀ z, ∀ᶠ c : ℝ in 𝓝 0, J (z + c • stdComplexLineReal) = J z)
    (hKss : ∀ z, ∀ᶠ c : ℝ in 𝓝 0, Ks (z + c • stdComplexLineReal) = Ks z)
    (hKts : ∀ z, ∀ᶠ c : ℝ in 𝓝 0, Kt (z + c • stdComplexLineReal) = Kt z)
    (hJ : ∀ z, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 2 u)
    (hF : ∀ z, ω.floerOperator J Ks Kt u z = 0) (hne : ∃ z, fderiv ℝ u z stdComplexLineReal ≠ 0)
    (hxm : Continuous xm) (hxp : Continuous xp) :
    Dense {z | fderiv ℝ u z stdComplexLineReal ≠ 0 ∧ u z ≠ xm z.2 ∧ u z ≠ xp z.2} := by
  -- The zeros of `∂ₛu` are isolated, so its nonzeros are dense.
  have hcod :=
    SymplecticForm.setOf_fderiv_apply_ne_zero_mem_codiscreteWithin_of_floerOperator_eq_zero
      isOpen_univ isPreconnected_univ (fun z _ ↦ hJs z) (fun z _ ↦ hKss z) (fun z _ ↦ hKts z)
      (fun z _ ↦ hJ z) (fun z _ ↦ hJJ z) (fun z _ ↦ hKs z) (fun z _ ↦ hKt z) hu.contDiffOn
      (fun z _ ↦ hF z) (by simpa using hne)
  refine dense_setOf_fderiv_apply_ne_zero_and_ne_and_ne hu.continuous hxm hxp fun z ↦ ?_
  have hz : {z | fderiv ℝ u z stdComplexLineReal ≠ 0} ∈ 𝓝[≠] z := by
    simpa only [compl_univ, union_empty] using
      mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hcod z (mem_univ z)
  exact mem_closure_iff_frequently.2
    ((Filter.Eventually.frequently hz).filter_mono nhdsWithin_le_nhds)

end TauCeti.Floer

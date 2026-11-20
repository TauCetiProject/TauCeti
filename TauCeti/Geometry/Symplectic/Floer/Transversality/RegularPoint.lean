/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import TauCeti.Geometry.Symplectic.Floer.Translation.Kernel

/-!
# Regular points of Floer trajectories

Let `u : ℝ × ℝ → V` be a Floer trajectory in a symplectic vector space, converging to the loops
`xm` and `xp` as `s → -∞` and `s → +∞`. Transversality for the moduli spaces of Floer
trajectories with respect to variations of a time-dependent almost complex structure `J_t` is
proved at the *regular points* of Floer, Hofer and Salamon: the points `(s, t)` with

* `∂ₛu(s, t) ≠ 0`,
* `u(s, t) ≠ xm(t)` and `u(s, t) ≠ xp(t)`, and
* `u(s', t) ≠ u(s, t)` for every `s' ≠ s`

(`TauCeti.Floer.regularPoints`). The last condition says that `(s, t)` is the only preimage of
`(u(s, t), t)` under the map `(s, t) ↦ (u(s, t), t)`: a variation of `J_t` supported near
`u(s, t)` at time `t` is then felt by the trajectory only near `(s, t)`. At such points, variations
of `J` detect cokernel elements of the linearized operator
(`TauCeti.SymplecticForm.eq_zero_of_integral_apply_deriv_floerOperator_eq_zero`).

This file proves two parts of the theorem of Floer, Hofer and Salamon that the regular points of
a nonstationary trajectory form an open dense set.

* **Openness.** If `u` is `C¹` and converges uniformly to continuous loops `xm` and `xp`, the
  regular points form an open set (`TauCeti.Floer.isOpen_regularPoints`). The topological core
  (`TauCeti.Floer.eventually_forall_apply_eq_imp_eq`) needs only a continuous map into a Hausdorff
  space with limits along the ends, and injectivity of `(s, t) ↦ (u(s, t), t)` near the point,
  which `∂ₛu ≠ 0` provides (`TauCeti.Floer.exists_mem_nhds_injOn_of_fderiv_apply_ne_zero`). The
  limits confine the competitors `s'` to a compact interval, and a compactness argument separates
  `u(s', t)` from `u(s, t)` uniformly nearby.
* **Separation from the asymptotic orbits.** On an open set where `u(s, t) = x(t)`, `u` does not
  depend on `s`, so `∂ₛu` vanishes there
  (`TauCeti.Floer.interior_setOf_eq_subset_setOf_fderiv_apply_eq_zero`). As the zeros of `∂ₛu` are
  isolated unless `u` is stationary
  (`SymplecticForm.setOf_fderiv_apply_ne_zero_mem_codiscreteWithin_of_floerOperator_eq_zero`),
  the points where `∂ₛu ≠ 0`, `u ≠ xm` and `u ≠ xp` form a dense open set for every nonstationary
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

section Topological

variable {X : Type*} [TopologicalSpace X] [T2Space X] {u : ℝ × ℝ → X} {xm xp : ℝ → X}

/-- **Isolated points of the slices persist nearby.** Let `u : ℝ × ℝ → X` be continuous, with
values in a Hausdorff space, and suppose that `u(s, t)` tends to `xm(t₀)` and `xp(t₀)` as
`s → -∞` and `s → +∞` and `t → t₀`. Let `z₀ = (s₀, t₀)` be a point near which
`(s, t) ↦ (u(s, t), t)` is injective, with `u(z₀) ≠ xm(t₀)`, `u(z₀) ≠ xp(t₀)` and
`u(s, t₀) ≠ u(z₀)` for all `s ≠ s₀`. Then every point `(s, t)` near `z₀` has the last property:
`u(s', t) ≠ u(s, t)` for all `s' ≠ s`. -/
theorem eventually_forall_apply_eq_imp_eq {z₀ : ℝ × ℝ} (hu : Continuous u)
    (hm : Tendsto u (atBot ×ˢ 𝓝 z₀.2) (𝓝 (xm z₀.2)))
    (hp : Tendsto u (atTop ×ˢ 𝓝 z₀.2) (𝓝 (xp z₀.2)))
    (hinj : ∃ U ∈ 𝓝 z₀, InjOn (fun z ↦ (u z, z.2)) U)
    (hm₀ : u z₀ ≠ xm z₀.2) (hp₀ : u z₀ ≠ xp z₀.2) (h₀ : ∀ s, u (s, z₀.2) = u z₀ → s = z₀.1) :
    ∀ᶠ z in 𝓝 z₀, ∀ s, u (s, z.2) = u z → s = z.1 := by
  obtain ⟨s₀, t₀⟩ := z₀
  obtain ⟨U, hU, hinj⟩ := hinj
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
  -- Along an end, `u` stays near the asymptotic value, away from a neighbourhood of `u z₀`.
  have hend {l : Filter ℝ} {x : ℝ → X} (h : Tendsto u (l ×ˢ 𝓝 t₀) (𝓝 (x t₀)))
      (hne : u (s₀, t₀) ≠ x t₀) :
      ∃ p : ℝ → Prop, (∀ᶠ s in l, p s) ∧ ∀ᶠ z in 𝓝 (s₀, t₀), ∀ s, p s → u (s, z.2) ≠ u z := by
    obtain ⟨A, B, hA, hB, hAx, hBx, hAB⟩ := t2_separation hne
    obtain ⟨p, hp, q, hq, hpq⟩ := eventually_prod_iff.1 (h (hB.mem_nhds hBx))
    refine ⟨p, hp, ?_⟩
    filter_upwards [hu.continuousAt.preimage_mem_nhds (hA.mem_nhds hAx),
      continuousAt_snd.preimage_mem_nhds hq] with z hzA hzq s hs heq
    exact disjoint_left.1 hAB hzA (heq ▸ hpq hs hzq)
  obtain ⟨pm, hpm, hevm⟩ := hend hm hm₀
  obtain ⟨pp, hpp, hevp⟩ := hend hp hp₀
  obtain ⟨Sm, hSm⟩ := eventually_atBot.1 hpm
  obtain ⟨Sp, hSp⟩ := eventually_atTop.1 hpp
  -- On the compact rest of the slice, `u` is separated from `u z₀` uniformly nearby.
  have hmid : ∀ᶠ z in 𝓝 (s₀, t₀), ∀ s ∈ Icc Sm Sp \ ball s₀ δ, u (s, z.2) ≠ u z := by
    refine (isCompact_Icc.diff isOpen_ball).eventually_forall_of_forall_eventually
      (P := fun z s ↦ u (s, z.2) ≠ u z) fun s hs ↦ ?_
    have hne : u (s, t₀) ≠ u (s₀, t₀) := fun h ↦
      hs.2 (h₀ s h ▸ mem_ball_self hδ)
    exact ((hu.comp (by fun_prop)).continuousAt.ne_iff_eventually_ne
      (hu.comp continuous_fst).continuousAt).1 hne
  filter_upwards [hevm, hevp, hmid, ball_mem_nhds _ hδ] with z h₁ h₂ h₃ hz s hs
  by_cases hsδ : s ∈ ball s₀ δ
  · -- Near `s₀` the slice is injective.
    rw [← ball_prod_same] at hz
    have hsz : (s, z.2) ∈ U := hδU (by rw [← ball_prod_same]; exact ⟨hsδ, hz.2⟩)
    have hzU : z ∈ U := hδU (by rw [← ball_prod_same]; exact hz)
    exact congrArg Prod.fst (hinj hsz hzU (Prod.ext hs rfl))
  · -- Otherwise `s` lies far along an end or in the compact rest of the slice.
    exfalso
    rcases le_or_gt s Sm with hle | hlt
    · exact h₁ s (hSm s hle) hs
    rcases le_or_gt Sp s with hle' | hlt'
    · exact h₂ s (hSp s hle') hs
    · exact h₃ s ⟨⟨hlt.le, hlt'.le⟩, hsδ⟩ hs

end Topological

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {u : ℝ × ℝ → V} {x xm xp : ℝ → V}

/-- **A nonvanishing `∂ₛu` makes `(s, t) ↦ (u(s, t), t)` injective nearby.** If `u` is `C¹` at
`z₀` with `∂ₛu(z₀) ≠ 0`, then two points near `z₀` on one horizontal line `t = const` have
different images under `u`. -/
theorem exists_mem_nhds_injOn_of_fderiv_apply_ne_zero {z₀ : ℝ × ℝ} (hu : ContDiffAt ℝ 1 u z₀)
    (h : fderiv ℝ u z₀ stdComplexLineReal ≠ 0) :
    ∃ U ∈ 𝓝 z₀, InjOn (fun z ↦ (u z, z.2)) U := by
  obtain ⟨a, b⟩ := z₀
  -- A functional `φ` with `φ (∂ₛu) > 0` near `z₀` makes `φ ∘ u` increasing in `s`.
  obtain ⟨φ, -, hφ⟩ := exists_dual_vector ℝ _ (norm_ne_zero_iff.2 h)
  have hcont : ContinuousAt (fun z ↦ φ (fderiv ℝ u z stdComplexLineReal)) (a, b) :=
    φ.continuous.continuousAt.comp
      ((hu.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const)
  have hpos : ∀ᶠ z in 𝓝 (a, b), 0 < φ (fderiv ℝ u z stdComplexLineReal) :=
    hcont.eventually (lt_mem_nhds (by simpa [hφ] using h))
  have hdiff : ∀ᶠ z in 𝓝 (a, b), DifferentiableAt ℝ u z :=
    (hu.eventually (by simp)).mono fun z hz ↦ hz.differentiableAt one_ne_zero
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (hpos.and hdiff)
  refine ⟨ball (a, b) δ, ball_mem_nhds _ hδ, ?_⟩
  rintro ⟨s, t⟩ hp ⟨s', t'⟩ hq heq
  obtain ⟨hu', rfl⟩ := Prod.mk.inj heq
  rw [← ball_prod_same] at hp hq
  have hline {σ : ℝ} (hσ : σ ∈ ball a δ) : (σ, t) ∈ ball (a, b) δ := by
    rw [← ball_prod_same]; exact ⟨hσ, hp.2⟩
  have hderiv {σ : ℝ} (hσ : σ ∈ ball a δ) :
      HasDerivAt (fun σ ↦ φ (u (σ, t))) (φ (fderiv ℝ u (σ, t) stdComplexLineReal)) σ := by
    have hl : HasDerivAt (fun σ : ℝ ↦ (σ, t)) stdComplexLineReal σ :=
      (hasDerivAt_id σ).prodMk (hasDerivAt_const σ t)
    exact φ.hasFDerivAt.comp_hasDerivAt σ
      ((hball (hline hσ)).2.hasFDerivAt.comp_hasDerivAt σ hl)
  have hmono : StrictMonoOn (fun σ ↦ φ (u (σ, t))) (ball a δ) := by
    refine strictMonoOn_of_deriv_pos (convex_ball a δ)
      (fun σ hσ ↦ (hderiv hσ).continuousAt.continuousWithinAt) fun σ hσ ↦ ?_
    rw [isOpen_ball.interior_eq] at hσ
    rw [(hderiv hσ).deriv]
    exact (hball (hline hσ)).1
  exact Prod.ext (hmono.injOn hp.1 hq.1 (congrArg φ hu')) rfl

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
    eventually_forall_apply_eq_imp_eq hcont (hlim hm hxm z.2) (hlim hp hxp z.2)
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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.LocalInjectivity
public import TauCeti.Geometry.Symplectic.Floer.Translation.Kernel
public import TauCeti.Topology.Instances.Real.SliceInjective
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import TauCeti.Dynamics.Flow.Translation

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

This file proves the theorem of Floer, Hofer and Salamon that the regular points of a
nonstationary trajectory form an open dense set, in three parts.

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
* **Density.** For a nonstationary trajectory of a Floer equation whose data `J_t` and `H_t` do
  not depend on `s`, the regular points are dense
  (`TauCeti.Floer.dense_regularPoints_of_floerOperator_eq_zero`). Suppose an open set `U` contains
  none. By Baire's theorem, on a smaller open set the competitors `s'` can be chosen continuously,
  as a function `φ(s, t)`, at points where `∂ₛu ≠ 0`
  (`TauCeti.exists_continuousOn_slice_eq_of_forall_exists_ne`): the critical points of
  `s ↦ u(s, t)` are countable
  (`TauCeti.Floer.countable_setOf_fderiv_apply_eq_zero_of_floerOperator_eq_zero`). Since
  `(s, t) ↦ (u(s, t), t)` is an immersion there, `φ` is differentiable
  (`TauCeti.Floer.exists_hasFDerivAt_of_eventually_slice_eq`), and differentiating
  `u(φ(s, t), t) = u(s, t)` with the Floer equation at both points shows `∂ₛφ = 1` and `∂ₜφ = 0`
  (`TauCeti.Floer.hasFDerivAt_fst_of_floerOperator_eq_zero`), because `∂ₛu` and `J ∂ₛu` are
  linearly independent. So `φ(s, t) = s + c` with `c ≠ 0`
  (`TauCeti.Floer.exists_eventually_eq_add_of_floerOperator_eq_zero`), and `u` agrees with its
  translate `u(· + c, ·)` on an open set. By unique continuation it is periodic in `s`
  (`TauCeti.SymplecticForm.periodic_of_floerOperator_eq_zero_of_eqOn`), which its limits along the
  ends forbid at points away from the asymptotic orbits.

## References

* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. **80** (1995), 251–292 (the regular points of a Floer trajectory, and
  the proof of their density followed here).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7** (1999), 143–229.
-/

public section

open Filter Function Metric Set Topology

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {u : ℝ × ℝ → V} {x xm xp : ℝ → V}

/-- **The derivative of `(s, t) ↦ (u(s, t), t)` is injective where `∂ₛu ≠ 0`.** For a linear map
`L : ℝ × ℝ → V` with `L(1, 0) ≠ 0`, the map `v ↦ (L v, v.2)` is injective. -/
theorem injective_prod_snd_of_apply_ne_zero {L : ℝ × ℝ →L[ℝ] V} (h : L stdComplexLineReal ≠ 0) :
    Injective (L.prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj hv
  have hv' : v = v.1 • stdComplexLineReal := by
    ext <;> simp_all [stdComplexLineReal_eq]
  rw [hv', map_smul, smul_eq_zero] at h₁
  rw [hv', h₁.resolve_right h, zero_smul]

/-- **A nonvanishing `∂ₛu` makes `(s, t) ↦ (u(s, t), t)` injective nearby.** If `u` is `C¹` at
`z₀` with `∂ₛu(z₀) ≠ 0`, then two points near `z₀` on one horizontal line `t = const` have
different images under `u`. -/
theorem exists_mem_nhds_injOn_of_fderiv_apply_ne_zero {z₀ : ℝ × ℝ} (hu : ContDiffAt ℝ 1 u z₀)
    (h : fderiv ℝ u z₀ stdComplexLineReal ≠ 0) :
    ∃ U ∈ 𝓝 z₀, InjOn (fun z ↦ (u z, z.2)) U := by
  have hd : fderiv ℝ (fun z ↦ (u z, z.2)) z₀ =
      (fderiv ℝ u z₀).prod (ContinuousLinearMap.snd ℝ ℝ ℝ) :=
    ((hu.differentiableAt one_ne_zero).hasFDerivAt.prodMk (hasFDerivAt_snd (p := z₀))).fderiv
  simpa only [nhdsWithin_univ] using
    ((hu.prodMk contDiffAt_snd).contDiffWithinAt (s := univ)).exists_nhdsWithin_injOn
      one_ne_zero convex_univ (mem_univ _) uniqueDiffWithinAt_univ
      (by rw [fderivWithin_univ, hd]; exact injective_prod_snd_of_apply_ne_zero h)

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

/-! ### Density of the regular points -/

/-- **A continuous competitor on the slices of `u` is differentiable where `∂ₛu ≠ 0`.** Let `u` be
differentiable at `z` and at `(φ(z), z.2)`, with `∂ₛu(φ(z), z.2) ≠ 0`, let `φ` be continuous at
`z`, and let `u(φ(w), w.2) = u(w)` for `w` near `z`. Then `φ` has a derivative `φ'` at `z`, and
`du(z) = du(φ(z), z.2) ∘ (φ', dt)`, the chain rule for `u(φ(w), w.2) = u(w)`. -/
theorem exists_hasFDerivAt_of_eventually_slice_eq [FiniteDimensional ℝ V] {φ : ℝ × ℝ → ℝ}
    {z : ℝ × ℝ} (huz : DifferentiableAt ℝ u z) (huφ : DifferentiableAt ℝ u (φ z, z.2))
    (hφ : ContinuousAt φ z) (heq : ∀ᶠ w in 𝓝 z, u (φ w, w.2) = u w)
    (hd : fderiv ℝ u (φ z, z.2) stdComplexLineReal ≠ 0) :
    ∃ φ' : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt φ φ' z ∧
      fderiv ℝ u (φ z, z.2) ∘L φ'.prod (ContinuousLinearMap.snd ℝ ℝ ℝ) = fderiv ℝ u z := by
  -- `w ↦ (φ w, w.2)` lifts `w ↦ (u w, w.2)` through `(s, t) ↦ (u(s, t), t)`, whose derivative at
  -- `(φ z, z.2)` has a left inverse, so it is differentiable at `z`.
  obtain ⟨π, hπ⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (injective_prod_snd_of_apply_ne_zero hd)
  have hg : HasFDerivAt (fun w ↦ (φ w, w.2))
      (π ∘L (fderiv ℝ u z).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) z :=
    HasFDerivAt.of_comp_of_leftInverse (f := fun q : ℝ × ℝ ↦ (u q, q.2))
      (hφ.prodMk continuousAt_snd) (huφ.hasFDerivAt.prodMk hasFDerivAt_snd)
      (huz.hasFDerivAt.prodMk hasFDerivAt_snd) (heq.mono fun w hw ↦ by simp [hw]) hπ
  have hφ' := hasFDerivAt_fst.comp z hg
  refine ⟨_, hφ', ?_⟩
  -- The derivative of `w ↦ (φ w, w.2)` is `(φ', snd)`, and the chain rule applies to it.
  have hg' := hφ'.prodMk (hasFDerivAt_snd (p := z))
  exact ((huφ.hasFDerivAt.comp z hg').congr_of_eventuallyEq (heq.mono fun w hw ↦ hw.symm)).unique
    huz.hasFDerivAt

/-- **A competitor on the slices of a Floer solution is a translate to first order.** Let `u` solve
the Floer equation `∂ₛu - X_{K_s}(u) + J_t(u)(∂ₜu - X_{K_t}(u)) = 0` at `z` and at `(φ(z), z.2)`,
for data `J_t`, `K_s`, `K_t` depending only on `t`, with `J_t(u(z))² = -1`. Suppose that `φ` is
continuous at `z`, that `u(φ(w), w.2) = u(w)` for all `w` near `z`, and that
`∂ₛu(φ(z), z.2) ≠ 0`. Then `φ` is differentiable at `z` with derivative `(s, t) ↦ s`. -/
theorem hasFDerivAt_fst_of_floerOperator_eq_zero {ω : SymplecticForm V} [FiniteDimensional ℝ V]
    {J : ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ → V → ℝ} {φ : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hJJ : J z.2 (u z) ∘L J z.2 (u z) = -ContinuousLinearMap.id ℝ V)
    (huz : DifferentiableAt ℝ u z) (huφ : DifferentiableAt ℝ u (φ z, z.2))
    (hFz : ω.floerOperator (fun p ↦ J p.2) (fun p ↦ Ks p.2) (fun p ↦ Kt p.2) u z = 0)
    (hFφ : ω.floerOperator (fun p ↦ J p.2) (fun p ↦ Ks p.2) (fun p ↦ Kt p.2) u (φ z, z.2) = 0)
    (hφ : ContinuousAt φ z) (heq : ∀ᶠ w in 𝓝 z, u (φ w, w.2) = u w)
    (hd : fderiv ℝ u (φ z, z.2) stdComplexLineReal ≠ 0) :
    HasFDerivAt φ (ContinuousLinearMap.fst ℝ ℝ ℝ) z := by
  obtain ⟨φ', hφ', hL⟩ := exists_hasFDerivAt_of_eventually_slice_eq huz huφ hφ heq hd
  set L := fderiv ℝ u (φ z, z.2)
  set a := L stdComplexLineReal
  set l := φ' stdComplexLineReal
  set m := φ' stdComplexLineImag
  -- The chain rule gives `∂ₛu(z) = l a` and `∂ₜu(z) = m a + ∂ₜu(φ z, z.2)`.
  have hb : fderiv ℝ u z stdComplexLineReal = l • a := by
    rw [← hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ← map_smul]
    congr 1
    simp [l, stdComplexLineReal_eq]
  have hc : fderiv ℝ u z stdComplexLineImag = m • a + L stdComplexLineImag := by
    rw [← hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ← map_smul,
      ← map_add]
    congr 1
    ext <;> simp [m, stdComplexLineReal_eq, stdComplexLineImag_eq]
  -- Subtracting the Floer equations at `z` and at `(φ z, z.2)`, where the data agree, gives
  -- `(l - 1) a + m J a = 0`. As `a ≠ 0` and `J² = -1`, `a` and `J a` are independent.
  let Jc : AlmostComplexStructure V :=
    ⟨(J z.2 (u z) : V →ₗ[ℝ] V), LinearMap.ext fun v ↦ by simpa using congr($hJJ v)⟩
  -- `Jc` applies `J z.2 (u z)`, through the coercions to linear maps.
  have hJc (v : V) : Jc v = J z.2 (u z) v := rfl
  have hkey : (l - 1) • a + m • Jc a = 0 := by
    rw [SymplecticForm.floerOperator_def] at hFz hFφ
    simp only [heq.self_of_nhds] at hFφ
    have h := congr($hFz - $hFφ)
    rw [hb, hc, sub_zero] at h
    rw [hJc, ← map_smul (J z.2 (u z)) m a]
    calc (l - 1) • a + J z.2 (u z) (m • a)
        = l • a - ω.hamiltonianVectorField (Ks z.2) (u z) +
            J z.2 (u z) (m • a + L stdComplexLineImag -
              ω.hamiltonianVectorField (Kt z.2) (u z)) -
          (a - ω.hamiltonianVectorField (Ks z.2) (u z) +
            J z.2 (u z) (L stdComplexLineImag - ω.hamiltonianVectorField (Kt z.2) (u z))) := by
          simp only [map_sub, map_add, sub_smul, one_smul]
          abel
      _ = 0 := h
  obtain ⟨hl, hm⟩ := LinearIndependent.pair_iff.1 (Jc.linearIndependent_pair hd) _ _ hkey
  -- Hence `φ'` sends `(1, 0)` to `1` and `(0, 1)` to `0`.
  convert hφ' using 1
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hv : v = v.1 • stdComplexLineReal + v.2 • stdComplexLineImag := by
    ext <;> simp [stdComplexLineReal_eq, stdComplexLineImag_eq]
  have hl' : φ' stdComplexLineReal = 1 := sub_eq_zero.1 hl
  have hm' : φ' stdComplexLineImag = 0 := hm
  rw [hv]
  simp only [map_add, map_smul, hl', hm']
  simp [stdComplexLineReal_eq, stdComplexLineImag_eq]

/-- **A continuous competitor on the slices of a Floer trajectory is a translate.** Let `u` be a
differentiable solution of the Floer equation `∂ₛu - X_{K_s}(u) + J_t(u)(∂ₜu - X_{K_t}(u)) = 0` on
`ℝ × ℝ`, for data depending only on `t`, with `J_t(u)² = -1` along `u`. Let `φ` be continuous on
an open set `W`, with `u(φ(z), z.2) = u(z)` and `∂ₛu(φ(z), z.2) ≠ 0` for every `z ∈ W`. Then near
every point of `W`, `φ(s, t) = s + c` for a constant `c`. -/
theorem exists_eventually_eq_add_of_floerOperator_eq_zero {ω : SymplecticForm V}
    [FiniteDimensional ℝ V] {J : ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ → V → ℝ} {φ : ℝ × ℝ → ℝ}
    {W : Set (ℝ × ℝ)} (hJJ : ∀ z, J z.2 (u z) ∘L J z.2 (u z) = -ContinuousLinearMap.id ℝ V)
    (hu : Differentiable ℝ u)
    (hF : ∀ z, ω.floerOperator (fun p ↦ J p.2) (fun p ↦ Ks p.2) (fun p ↦ Kt p.2) u z = 0)
    (hW : IsOpen W) (hφc : ContinuousOn φ W) (hφu : ∀ z ∈ W, u (φ z, z.2) = u z)
    (hφd : ∀ z ∈ W, fderiv ℝ u (φ z, z.2) stdComplexLineReal ≠ 0) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ W) :
    ∃ c, ∀ᶠ z in 𝓝 z₀, φ z = z.1 + c := by
  -- `φ - fst` has derivative zero on `W`, so it is constant on a ball around `z₀`.
  have hd (z) (hz : z ∈ W) : HasFDerivAt (fun w ↦ φ w - w.1) (0 : ℝ × ℝ →L[ℝ] ℝ) z := by
    have h := (hasFDerivAt_fst_of_floerOperator_eq_zero (hJJ z) (hu z) (hu _) (hF z) (hF _)
      ((hφc z hz).continuousAt (hW.mem_nhds hz)) (Filter.eventually_of_mem (hW.mem_nhds hz) hφu)
        (hφd z hz)).sub (hasFDerivAt_fst (p := z))
    rwa [sub_self] at h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW z₀ hz₀
  refine ⟨φ z₀ - z₀.1, Filter.eventually_of_mem (ball_mem_nhds z₀ hε) fun z hz ↦ ?_⟩
  have h := isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball z₀ ε).isPreconnected
    (fun w hw ↦ (hd w (hball hw)).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hd w (hball hw)).fderiv) hz (mem_ball_self hε)
  linarith

/-- **The critical points of a nonstationary Floer trajectory are countable.** Let `u` be a `C²`
solution of the Floer equation `∂ₛu - X_{K_s}(u) + J(u)(∂ₜu - X_{K_t}(u)) = 0` on `ℝ × ℝ` whose data
`J`, `K_s`, `K_t` are invariant under small translations in `s`, with `J` of class `C¹`, the
Hamiltonians of class `C²` near the graph of `u` and `J(z, u z)² = -1`. If `u` is not stationary,
that is `∂ₛu` does not vanish identically, then the points where `∂ₛu = 0` form a countable set. -/
theorem countable_setOf_fderiv_apply_eq_zero_of_floerOperator_eq_zero {ω : SymplecticForm V}
    [FiniteDimensional ℝ V] {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
    (hJs : ∀ z, ∀ᶠ c : ℝ in 𝓝 0, J (z + c • stdComplexLineReal) = J z)
    (hKss : ∀ z, ∀ᶠ c : ℝ in 𝓝 0, Ks (z + c • stdComplexLineReal) = Ks z)
    (hKts : ∀ z, ∀ᶠ c : ℝ in 𝓝 0, Kt (z + c • stdComplexLineReal) = Kt z)
    (hJ : ∀ z, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 2 u)
    (hF : ∀ z, ω.floerOperator J Ks Kt u z = 0) (hne : ∃ z, fderiv ℝ u z stdComplexLineReal ≠ 0) :
    {z | fderiv ℝ u z stdComplexLineReal = 0}.Countable := by
  -- The zeros of `∂ₛu` are isolated, so they form a discrete, hence countable, set.
  have hcod :=
    SymplecticForm.setOf_fderiv_apply_ne_zero_mem_codiscreteWithin_of_floerOperator_eq_zero
      isOpen_univ isPreconnected_univ (fun z _ ↦ hJs z) (fun z _ ↦ hKss z) (fun z _ ↦ hKts z)
      (fun z _ ↦ hJ z) (fun z _ ↦ hJJ z) (fun z _ ↦ hKs z) (fun z _ ↦ hKt z) hu.contDiffOn
      (fun z _ ↦ hF z) (by simpa using hne)
  have hdisc : IsDiscrete ({z | fderiv ℝ u z stdComplexLineReal = 0} ∩ univ) :=
    isDiscrete_of_codiscreteWithin (by simpa only [compl_ofPred] using hcod)
  exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete (by simpa using hdisc)

omit [NormedSpace ℝ V] in
/-- If `u` is `(c, 0)`-periodic with `c ≠ 0` and `u(s, t)` tends to `a` as `s → -∞` and to `b`
as `s → +∞`, then `u(z) = a` or `u(z) = b` at every point `z` of the slice `t`: translating `z` by
multiples of `c` along its slice runs into an end. -/
private theorem eq_or_eq_of_periodic_of_tendsto {c : ℝ} (hper : Periodic u (c, 0)) (hc : c ≠ 0)
    {z : ℝ × ℝ} {a b : V} (hm : Tendsto (fun s ↦ u (s, z.2)) atBot (𝓝 a))
    (hp : Tendsto (fun s ↦ u (s, z.2)) atTop (𝓝 b)) : u z = a ∨ u z = b := by
  have hend {l : Filter ℝ} {x : V} (hx : Tendsto (fun s ↦ u (s, z.2)) l (𝓝 x))
      (hl : Tendsto (fun n : ℕ ↦ z.1 + n * c) atTop l) : u z = x :=
    hper.eq_of_tendsto_of_tendsto_add_nsmul (l := l.map fun s ↦ (s, z.2)) (tendsto_map'_iff.2 hx)
      ((tendsto_map.comp hl).congr fun n ↦ by ext <;> simp)
  rcases hc.lt_or_gt with hc | hc
  · exact .inl (hend hm (tendsto_atBot_add_const_left _ _
      (tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg hc)))
  · exact .inr (hend hp (tendsto_atTop_add_const_left _ _
      (tendsto_natCast_atTop_atTop.atTop_mul_const hc)))

/-- **The regular points of a nonstationary Floer trajectory are dense** (Floer, Hofer and
Salamon). Let `u` be a `C²` solution on `ℝ × ℝ` of the Floer equation
`∂ₛu + J_t(u)(∂ₜu - X_{H_t}(u)) = 0`, for a `C¹` family `J_t` with `J_t(u)² = -1` along `u` and a
`C²` Hamiltonian `H`. Suppose `u(s, t)` tends to `xm(t)` as `s → -∞` and to `xp(t)` as `s → +∞`,
for continuous loops `xm` and `xp`. If `u` is not stationary, that is `∂ₛu` does not vanish
identically, then its regular points are dense in `ℝ × ℝ`. -/
theorem dense_regularPoints_of_floerOperator_eq_zero {ω : SymplecticForm V} [FiniteDimensional ℝ V]
    {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} (hJ : ContDiff ℝ 1 (fun p : ℝ × V ↦ J p.1 p.2))
    (hJJ : ∀ z, J z.2 (u z) ∘L J z.2 (u z) = -ContinuousLinearMap.id ℝ V)
    (hH : ContDiff ℝ 2 (uncurry H)) (hu : ContDiff ℝ 2 u)
    (hF : ∀ z, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u z = 0)
    (hne : ∃ z, fderiv ℝ u z stdComplexLineReal ≠ 0) (hxm : Continuous xm) (hxp : Continuous xp)
    (hm : ∀ t, Tendsto (fun s ↦ u (s, t)) atBot (𝓝 (xm t)))
    (hp : ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (xp t))) :
    Dense (regularPoints u xm xp) := by
  -- The points with `∂ₛu ≠ 0` away from the asymptotic orbits form a dense open set `D`.
  have hG : IsOpen {z | fderiv ℝ u z stdComplexLineReal ≠ 0} :=
    isOpen_ne_fun ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      continuous_const
  -- The data `J_t`, `0` and `H_t`, seen on `ℝ × ℝ`, are invariant in `s` and regular along `u`.
  have hinv {α : Type _} (f : ℝ → α) (z : ℝ × ℝ) : ∀ᶠ c : ℝ in 𝓝 0,
      (fun p : ℝ × ℝ ↦ f p.2) (z + c • stdComplexLineReal) = (fun p ↦ f p.2) z :=
    Eventually.of_forall fun c ↦ by simp [stdComplexLineReal_eq]
  have hJ' (z : ℝ × ℝ) : ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1.2 p.2) (z, u z) :=
    (hJ.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)).contDiffAt
  have hH' (z : ℝ × ℝ) : ContDiffAt ℝ 2 (uncurry fun p : ℝ × ℝ ↦ H p.2) (z, u z) :=
    (hH.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)).contDiffAt
  have hK₀ (z : ℝ × ℝ) : ContDiffAt ℝ 2 (uncurry fun (_ : ℝ × ℝ) (_ : V) ↦ (0 : ℝ)) (z, u z) :=
    contDiff_const.contDiffAt
  have hD := dense_setOf_fderiv_apply_ne_zero_and_ne_and_ne_of_floerOperator_eq_zero (hinv J)
    (hinv fun _ _ ↦ (0 : ℝ)) (hinv H) hJ' hJJ hK₀ hH' hu hF hne hxm hxp
  have hDo : IsOpen {z | fderiv ℝ u z stdComplexLineReal ≠ 0 ∧ u z ≠ xm z.2 ∧ u z ≠ xp z.2} :=
    hG.inter ((isOpen_ne_fun hu.continuous (hxm.comp continuous_snd)).inter
      (isOpen_ne_fun hu.continuous (hxp.comp continuous_snd)))
  -- Suppose an open set `U` has no regular point. The competitors of the points of `U ∩ D` are
  -- then chosen continuously on an open `W`, away from the countably many critical points.
  refine dense_iff_inter_open.2 fun U hU hUne ↦ not_not.1 fun hR ↦ ?_
  obtain ⟨W, hWU, hWo, ⟨z₀, hz₀⟩, φ, hφc, hφ⟩ := exists_continuousOn_slice_eq_of_forall_exists_ne
    hu.continuous hG (fun p hp ↦
      exists_mem_nhds_injOn_of_fderiv_apply_ne_zero (hu.of_le (by norm_num)).contDiffAt hp)
    (by simpa only [compl_ofPred, not_not] using
      countable_setOf_fderiv_apply_eq_zero_of_floerOperator_eq_zero (hinv J)
          (hinv fun _ _ ↦ (0 : ℝ)) (hinv H) hJ' hJJ hK₀ hH' hu hF hne)
    (hU.inter hDo) (hD.inter_open_nonempty U hU hUne) fun z hz ↦ by
      have hzR : z ∉ regularPoints u xm xp := fun h ↦ hR ⟨z, hz.1, h⟩
      simp only [mem_regularPoints, not_and, not_forall] at hzR
      obtain ⟨s, hs, hsz⟩ := hzR hz.2.1 hz.2.2.1 hz.2.2.2
      exact ⟨s, hsz, hs⟩
  -- By the Floer equation `φ(z) = z.1 + c` near `z₀`, with `c ≠ 0`; so `u(s + c, t) = u(s, t)`
  -- near `z₀`, hence everywhere, by unique continuation.
  obtain ⟨c, hc⟩ := exists_eventually_eq_add_of_floerOperator_eq_zero (Ks := fun _ _ ↦ 0)
    (Kt := H) hJJ (hu.differentiable (by norm_num)) hF hWo hφc (fun z hz ↦ (hφ z hz).2.1)
    (fun z hz ↦ (hφ z hz).2.2) hz₀
  have hc₀ : c ≠ 0 := fun h ↦ (hφ z₀ hz₀).1 (by simpa [h] using hc.self_of_nhds)
  obtain ⟨B, hB, hBo, hz₀B⟩ := _root_.mem_nhds_iff.1 (inter_mem hc (hWo.mem_nhds hz₀))
  have hper : Periodic u (c, 0) :=
    SymplecticForm.periodic_of_floerOperator_eq_zero_of_eqOn hJ hJJ hH (hu.of_le (by norm_num))
      hF hBo ⟨z₀, hz₀B⟩ fun z hz ↦
        (hφ z (hB hz).2).2.1.symm.trans (congrArg u (Prod.ext (hB hz).1 (add_zero _).symm))
  -- So `u(z₀)` is the value of an asymptotic orbit, contrary to `z₀ ∈ D`.
  obtain ⟨-, hzm, hzp⟩ := (hWU hz₀).2
  exact (eq_or_eq_of_periodic_of_tendsto hper hc₀ (hm z₀.2) (hp z₀.2)).elim hzm hzp

end TauCeti.Floer

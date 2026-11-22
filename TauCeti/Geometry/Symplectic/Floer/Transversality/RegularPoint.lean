/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.LocalInjectivity
public import TauCeti.Geometry.Symplectic.Floer.Translation.Kernel
public import TauCeti.Topology.Instances.Real.SliceInjective
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Dynamics.Flow.Translation
import TauCeti.Topology.Baire.Lemmas

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
nonstationary trajectory form an open dense set.

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
* **Density.** For a nonstationary `C²` Floer trajectory `u` with the cylindrical datum
  `K = H_t dt` and an `s`-independent `J_t`, converging pointwise to `xm` and `xp`, the regular
  points are dense (`TauCeti.Floer.dense_regularPoints`). Suppose that a nonempty open set `W` of
  points with `∂ₛu ≠ 0`, `u ≠ xm` and `u ≠ xp` contains no regular point, so that every point
  `z ∈ W` has a partner `s ≠ z.1` with `u(s, z.2) = u z`. The zeros of `∂ₛu` are isolated, hence
  countably many, and the Baire category theorem
  (`IsOpen.exists_inter_interior_nonempty_of_subset_iUnion`) gives a nonempty open `U ⊆ W`, a
  compact set `D` on which `∂ₛu ≠ 0` and `(s, t) ↦ (u(s, t), t)` is injective, and `ε > 0` such
  that every `z ∈ U` has a unique partner `φ z` with `(φ z, z.2) ∈ D` and `|φ z - z.1| ≥ ε`. By
  compactness and uniqueness `φ` is continuous, and by the inverse function theorem applied to
  `(s, t) ↦ (ℓ(u(s, t)), t)`, for a linear form `ℓ` with `ℓ(∂ₛu) ≠ 0` at the partner, `φ` is
  differentiable. Differentiating `u(φ(s, t), t) = u(s, t)` and comparing the Floer equations at
  the two points, which share `J_t` and `X_{H_t}`, gives
  `(∂ₛφ - 1) ∂ₛu + ∂ₜφ J_t ∂ₛu = 0` at the partner. Since `∂ₛu` and `J_t ∂ₛu` are linearly
  independent, `φ(s, t) = s + c` on a ball, with `|c| ≥ ε`. So `u` agrees with its translate by
  `(c, 0)` on an open set, hence everywhere by unique continuation
  (`TauCeti.SymplecticForm.periodic_of_floerOperator_eq_zero_of_eqOn`). Iterating the period moves
  a point of `W` to an end, where `u` is the asymptotic orbit, a contradiction.

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

/-! ### Density of the regular points -/

section Dense

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ}

/-- **The derivative of a slice partner.** Let `u` solve the Floer equation
`∂ₛu + J_t(u)(∂ₜu - X_{H_t}(u)) = 0` for cylindrical data at `z₀` and at `w₀ = (φ z₀, z₀.2)`, and
let `u(φ(s, t), t) = u(s, t)` near `z₀`. If `φ` is differentiable at `z₀`, `u` is differentiable at
`w₀`, `J_t(u z₀)² = -1` and `∂ₛu(w₀) ≠ 0`, then the derivative of `φ` at `z₀` is
`(σ, τ) ↦ σ`. -/
private theorem fderiv_eq_fst_of_eventually_comp_eq {φ : ℝ × ℝ → ℝ} {z₀ : ℝ × ℝ}
    (hφ : DifferentiableAt ℝ φ z₀) (hu₁ : DifferentiableAt ℝ u (φ z₀, z₀.2))
    (heq : ∀ᶠ z in 𝓝 z₀, u (φ z, z.2) = u z)
    (hJJ : J z₀.2 (u z₀) ∘L J z₀.2 (u z₀) = -ContinuousLinearMap.id ℝ V)
    (hF₀ : ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u z₀ = 0)
    (hF₁ : ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u (φ z₀, z₀.2) = 0)
    (ha : fderiv ℝ u (φ z₀, z₀.2) stdComplexLineReal ≠ 0) :
    fderiv ℝ φ z₀ = ContinuousLinearMap.fst ℝ ℝ ℝ := by
  -- The two Floer equations share `J` and `X_H`, since `u` takes the same value at the same time.
  have hu : u (φ z₀, z₀.2) = u z₀ := heq.self_of_nhds
  rw [SymplecticForm.floerOperator_def] at hF₀ hF₁
  simp only [hu] at hF₁
  set L := fderiv ℝ φ z₀
  set A := fderiv ℝ u (φ z₀, z₀.2)
  -- Differentiating `u(φ(s, t), t) = u(s, t)` expresses `du(z₀)` through `A` and `L`.
  have hD : fderiv ℝ u z₀ = A.comp (L.prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) :=
    ((hu₁.hasFDerivAt.comp z₀
      (hφ.hasFDerivAt.prodMk (hasFDerivAt_snd (p := z₀)))).congr_of_eventuallyEq
      (heq.mono fun _ h ↦ h.symm)).fderiv
  have h₁ : fderiv ℝ u z₀ stdComplexLineReal =
      L stdComplexLineReal • A stdComplexLineReal := by
    rw [hD, ← map_smul]
    simp [stdComplexLineReal_eq]
  have h₂ : fderiv ℝ u z₀ stdComplexLineImag =
      L stdComplexLineImag • A stdComplexLineReal + A stdComplexLineImag := by
    rw [hD, ← map_smul, ← map_add]
    simp [stdComplexLineReal_eq, stdComplexLineImag_eq]
  set j := J z₀.2 (u z₀)
  have hlin : (L stdComplexLineReal - 1) • A stdComplexLineReal +
      L stdComplexLineImag • j (A stdComplexLineReal) = 0 := by
    have h := congrArg₂ HSub.hSub hF₀ hF₁
    rw [sub_zero] at h
    rw [← h, h₁, h₂]
    simp only [map_sub, map_add, map_smul, sub_smul, one_smul]
    abel
  -- A nonzero vector and its image under `j` are linearly independent.
  let jc : AlmostComplexStructure V :=
    ⟨j.toLinearMap, by ext v; simpa using congrArg (fun T ↦ T v) hJJ⟩
  obtain ⟨hα, hβ⟩ := LinearIndependent.pair_iff.1 (jc.linearIndependent_pair ha) _ _ hlin
  refine ContinuousLinearMap.prod_ext (ContinuousLinearMap.ext_ring ?_)
    (ContinuousLinearMap.ext_ring ?_)
  · simpa [stdComplexLineReal_eq, sub_eq_zero] using hα
  · simpa [stdComplexLineImag_eq] using hβ

omit [FiniteDimensional ℝ V] in
/-- **A slice partner is differentiable.** Let `u` be `C¹` at `w₀ = (φ z₀, z₀.2)` with
`∂ₛu(w₀) ≠ 0`, differentiable at `z₀`, and let `u(φ(s, t), t) = u(s, t)` near `z₀`. If `φ` is
continuous at `z₀`, then it is differentiable at `z₀`. -/
private theorem differentiableAt_of_eventually_comp_eq {φ : ℝ × ℝ → ℝ} {z₀ : ℝ × ℝ}
    (hφ : ContinuousAt φ z₀) (hu₀ : DifferentiableAt ℝ u z₀)
    (hu₁ : ContDiffAt ℝ 1 u (φ z₀, z₀.2))
    (ha : fderiv ℝ u (φ z₀, z₀.2) stdComplexLineReal ≠ 0)
    (heq : ∀ᶠ z in 𝓝 z₀, u (φ z, z.2) = u z) : DifferentiableAt ℝ φ z₀ := by
  set w₀ : ℝ × ℝ := (φ z₀, z₀.2)
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_ne_zero (R := ℝ) ha
  -- The map `G w = (ℓ(u w), w.2)` has an invertible derivative at `w₀`.
  set G : ℝ × ℝ → ℝ × ℝ := fun w ↦ (ℓ (u w), w.2)
  set G' : ℝ × ℝ →L[ℝ] ℝ × ℝ := (ℓ.comp (fderiv ℝ u w₀)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hG : HasStrictFDerivAt G G' w₀ :=
    (ℓ.hasStrictFDerivAt.comp w₀ (hu₁.hasStrictFDerivAt_fderiv one_ne_zero)).prodMk
      hasStrictFDerivAt_snd
  have hinj : Injective G' := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj hv
    have hv' : v = v.1 • stdComplexLineReal := by
      ext <;> simp_all [G', stdComplexLineReal_eq]
    rw [hv'] at h₁ ⊢
    simp only [map_smul, smul_eq_mul, mul_eq_zero] at h₁
    simp [h₁.resolve_right hℓ]
  set E := (LinearEquiv.ofInjectiveEndo (G' : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) hinj).toContinuousLinearEquiv
  have hE : HasStrictFDerivAt G (E : ℝ × ℝ →L[ℝ] ℝ × ℝ) w₀ := by
    convert hG using 1
    exact ContinuousLinearMap.ext fun v ↦ by simp [E]
  -- Near `z₀`, the partner `(φ z, z.2)` is the local inverse of `G` at `(ℓ(u z), z.2)`.
  have hψ : Tendsto (fun z : ℝ × ℝ ↦ (φ z, z.2)) (𝓝 z₀) (𝓝 w₀) := hφ.prodMk continuousAt_snd
  have hloc : φ =ᶠ[𝓝 z₀] fun z ↦ (hE.localInverse G E w₀ (ℓ (u z), z.2)).1 := by
    filter_upwards [hψ.eventually hE.eventually_left_inverse, heq] with z h₁ h₂
    simp only [G, h₂] at h₁
    rw [h₁]
  have hd : DifferentiableAt ℝ (hE.localInverse G E w₀) (ℓ (u z₀), z₀.2) := by
    have h := hE.to_localInverse.differentiableAt
    rwa [show G w₀ = (ℓ (u z₀), z₀.2) by simp [G, w₀, heq.self_of_nhds]] at h
  exact ((hd.comp z₀ ((ℓ.differentiableAt.comp z₀ hu₀).prodMk differentiableAt_snd)).fst
    ).congr_of_eventuallyEq hloc

omit [FiniteDimensional ℝ V] in
/-- Around a point `w` where `∂ₛu ≠ 0`, every topological basis of `ℝ × ℝ` has a member `b ∋ w`
with compact closure on which `∂ₛu ≠ 0` and `(s, t) ↦ (u(s, t), t)` is injective. -/
private theorem exists_mem_basis_isCompact_closure (hu : ContDiff ℝ 1 u)
    {B : Set (Set (ℝ × ℝ))} (hB : TopologicalSpace.IsTopologicalBasis B) {w : ℝ × ℝ}
    (hw : fderiv ℝ u w stdComplexLineReal ≠ 0) :
    ∃ b ∈ B, w ∈ b ∧ IsCompact (closure b) ∧
      (∀ w' ∈ closure b, fderiv ℝ u w' stdComplexLineReal ≠ 0) ∧
      InjOn (fun w' ↦ (u w', w'.2)) (closure b) := by
  obtain ⟨N, hN, hinjN⟩ := exists_mem_nhds_injOn_of_fderiv_apply_ne_zero hu.contDiffAt hw
  have hN' : {w' | fderiv ℝ u w' stdComplexLineReal ≠ 0} ∈ 𝓝 w :=
    ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousAt.eventually_ne hw
  obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhds_iff.1 (inter_mem hN hN')
  obtain ⟨b, hbB, hwb, hbδ⟩ :=
    hB.exists_subset_of_mem_open (mem_ball_self (half_pos hδ)) isOpen_ball
  have hcl : closure b ⊆ ball w δ := (closure_mono hbδ).trans
    (closure_ball_subset_closedBall.trans (closedBall_subset_ball (half_lt_self hδ)))
  exact ⟨b, hbB, hwb, (isCompact_closedBall w δ).of_isClosed_subset isClosed_closure
    (hcl.trans ball_subset_closedBall), fun w' hw' ↦ (hδN (hcl hw')).2,
    hinjN.mono fun w' hw' ↦ (hδN (hcl hw')).1⟩

omit [FiniteDimensional ℝ V] in
/-- **Localizing the slice partners.** Let `u` be `C¹` with countably many zeros of `∂ₛu`. If every
point `z` of a nonempty open set `W` has a partner `s ≠ z.1` on its slice, `u(s, z.2) = u z`, then
there are a nonempty open set `U`, a compact set `D` on which `∂ₛu ≠ 0` and
`(s, t) ↦ (u(s, t), t)` is injective, and `ε > 0` such that every point of `U` has a partner in `D`
at distance at least `ε` on its slice. -/
private theorem exists_isCompact_forall_exists_slicePartner (hu : ContDiff ℝ 1 u)
    (hcrit : {w : ℝ × ℝ | fderiv ℝ u w stdComplexLineReal = 0}.Countable) {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hne : W.Nonempty) (hpart : ∀ z ∈ W, ∃ s ≠ z.1, u (s, z.2) = u z) :
    ∃ U D : Set (ℝ × ℝ), ∃ ε : ℝ, IsOpen U ∧ U.Nonempty ∧ IsCompact D ∧
      (∀ w ∈ D, fderiv ℝ u w stdComplexLineReal ≠ 0) ∧ InjOn (fun w ↦ (u w, w.2)) D ∧ 0 < ε ∧
      ∀ z ∈ U, ∃ s, (s, z.2) ∈ D ∧ ε ≤ |s - z.1| ∧ u (s, z.2) = u z := by
  classical
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis (ℝ × ℝ)
  have := hBc.to_subtype
  have := hcrit.to_subtype
  set Good : Set (ℝ × ℝ) → Prop := fun D ↦ IsCompact D ∧
    (∀ w ∈ D, fderiv ℝ u w stdComplexLineReal ≠ 0) ∧ InjOn (fun w ↦ (u w, w.2)) D
  set S : Set (ℝ × ℝ) → ℝ → Set (ℝ × ℝ) := fun D ε ↦
    {z | ∃ s, (s, z.2) ∈ D ∧ ε ≤ |s - z.1| ∧ u (s, z.2) = u z}
  -- The closed cover: partners in a good closed basic set, or partners at zeros of `∂ₛu`.
  set F : (B × ℕ) ⊕ {w : ℝ × ℝ // fderiv ℝ u w stdComplexLineReal = 0} → Set (ℝ × ℝ) :=
    fun i ↦ i.elim (fun p ↦ if Good (closure p.1.val) then
      S (closure p.1.val) ((p.2 + 1 : ℝ)⁻¹) else ∅) fun c ↦ {z | z.2 = c.val.2 ∧ u z = u c.val}
  have hF : ∀ i, IsClosed (F i) := by
    rintro (⟨b, m⟩ | c)
    · by_cases hg : Good (closure b.val)
      · simpa [F, S, hg] using isClosed_setOf_exists_slicePartner hu.continuous hg.1 _
      · simp [F, hg]
    · exact (isClosed_eq continuous_snd continuous_const).inter
        (isClosed_eq hu.continuous continuous_const)
  have hcov : W ⊆ ⋃ i, F i := by
    intro z hz
    obtain ⟨s, hs, hus⟩ := hpart z hz
    by_cases hc : fderiv ℝ u (s, z.2) stdComplexLineReal = 0
    · exact mem_iUnion.2 ⟨.inr ⟨(s, z.2), hc⟩, rfl, hus.symm⟩
    obtain ⟨b, hbB, hsb, hgood⟩ := exists_mem_basis_isCompact_closure hu hB hc
    replace hgood : Good (closure b) := hgood
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (abs_pos.2 (sub_ne_zero.2 hs))
    refine mem_iUnion.2 ⟨.inl (⟨b, hbB⟩, m), ?_⟩
    simp only [F, Sum.elim_inl, hgood, ↓reduceIte]
    exact ⟨s, subset_closure hsb, by simpa [one_div] using hm.le, hus⟩
  obtain ⟨i, z₀, -, hz₀⟩ := hW.exists_inter_interior_nonempty_of_subset_iUnion hne hF hcov
  rcases i with ⟨b, m⟩ | c
  · by_cases hg : Good (closure b.val)
    · refine ⟨interior (F (.inl (b, m))), closure b.val, ((m : ℝ) + 1)⁻¹, isOpen_interior,
        ⟨z₀, hz₀⟩, hg.1, hg.2.1, hg.2.2, by positivity, fun z hz ↦ ?_⟩
      simpa [F, S, hg] using interior_subset hz
    · simp [F, hg] at hz₀
  · -- A set of points on one horizontal line has empty interior.
    have h : interior {z : ℝ × ℝ | z.2 = c.val.2 ∧ u z = u c.val} ⊆ ∅ :=
      (interior_mono (s := {z : ℝ × ℝ | z.2 = c.val.2 ∧ u z = u c.val})
        (t := (univ : Set ℝ) ×ˢ {c.val.2}) fun z hz ↦
          ⟨mem_univ z.1, mem_singleton_iff.2 hz.1⟩).trans
        (by rw [interior_prod_eq, interior_singleton, prod_empty])
    exact (h hz₀).elim

/-- **Uniform slice partners give a period.** Let `u` be a `C¹` solution of the Floer equation
`∂ₛu + J_t(u)(∂ₜu - X_{H_t}(u)) = 0`, for a `C¹` family `J_t` with `J_t(u)² = -1` along `u` and a
`C²` Hamiltonian `H`. Suppose that on a nonempty open set `U` every point has a partner in a compact
set `D`, at distance at least `ε > 0` on its slice, where `∂ₛu ≠ 0` on `D` and
`(s, t) ↦ (u(s, t), t)` is injective on `D`. Then `u` has a period `(c, 0)` with `c ≠ 0`. -/
private theorem exists_ne_zero_periodic_of_forall_exists_slicePartner
    (hJ : ContDiff ℝ 1 (fun p : ℝ × V ↦ J p.1 p.2))
    (hJJ : ∀ z, J z.2 (u z) ∘L J z.2 (u z) = -ContinuousLinearMap.id ℝ V)
    (hH : ContDiff ℝ 2 (uncurry H)) (hu : ContDiff ℝ 1 u)
    (hF : ∀ z, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u z = 0)
    {U D : Set (ℝ × ℝ)} {ε : ℝ} (hU : IsOpen U) (hUne : U.Nonempty) (hD : IsCompact D)
    (hDs : ∀ w ∈ D, fderiv ℝ u w stdComplexLineReal ≠ 0) (hinj : InjOn (fun w ↦ (u w, w.2)) D)
    (hε : 0 < ε) (hpart : ∀ z ∈ U, ∃ s, (s, z.2) ∈ D ∧ ε ≤ |s - z.1| ∧ u (s, z.2) = u z) :
    ∃ c ≠ 0, Periodic u (c, 0) := by
  classical
  set φ : ℝ × ℝ → ℝ := fun z ↦
    Classical.epsilon fun s ↦ (s, z.2) ∈ D ∧ ε ≤ |s - z.1| ∧ u (s, z.2) = u z
  have hφ (z : ℝ × ℝ) (hz : z ∈ U) :
      (φ z, z.2) ∈ D ∧ ε ≤ |φ z - z.1| ∧ u (φ z, z.2) = u z :=
    Classical.epsilon_spec (hpart z hz)
  have heq (z₀ : ℝ × ℝ) (hz₀ : z₀ ∈ U) : ∀ᶠ z in 𝓝 z₀, u (φ z, z.2) = u z :=
    eventually_of_mem (hU.mem_nhds hz₀) fun z hz ↦ (hφ z hz).2.2
  have hdiff (z : ℝ × ℝ) (hz : z ∈ U) : DifferentiableAt ℝ φ z :=
    differentiableAt_of_eventually_comp_eq
      (continuousAt_of_forall_slicePartner hu.continuous hD hinj hU
        (fun z hz ↦ ⟨(hφ z hz).1, (hφ z hz).2.2⟩) hz)
      (hu.differentiable one_ne_zero z)
      hu.contDiffAt (hDs _ (hφ z hz).1) (heq z hz)
  have hfd (z : ℝ × ℝ) (hz : z ∈ U) : fderiv ℝ φ z = ContinuousLinearMap.fst ℝ ℝ ℝ :=
    fderiv_eq_fst_of_eventually_comp_eq (hdiff z hz) (hu.differentiable one_ne_zero _) (heq z hz)
      (hJJ z) (hF z) (hF _) (hDs _ (hφ z hz).1)
  -- On a ball in `U`, the partner is a fixed translate, `φ z = z.1 + c`.
  obtain ⟨z₀, hz₀⟩ := hUne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  obtain ⟨c, hc⟩ := isOpen_ball.exists_eq_add_of_fderiv_eq (convex_ball z₀ r).isPreconnected
    (fun z hz ↦ (hdiff z (hball hz)).differentiableWithinAt) differentiableOn_fst
    fun z hz ↦ by rw [hfd z (hball hz), fderiv_fst]
  refine ⟨c, ?_, SymplecticForm.periodic_of_floerOperator_eq_zero_of_eqOn hJ hJJ hH hu hF
    isOpen_ball ⟨z₀, mem_ball_self hr⟩ fun z hz ↦ ?_⟩
  · have h := (hφ z₀ hz₀).2.1
    rw [hc (mem_ball_self hr), add_sub_cancel_left] at h
    exact abs_pos.1 (hε.trans_le h)
  · have h := (hφ z (hball hz)).2.2
    rw [hc hz] at h
    simp only at h ⊢
    rw [show z + (c, 0) = (z.1 + c, z.2) from Prod.ext rfl (add_zero z.2), h]

/-- **The regular points of a nonstationary Floer trajectory are dense** (Floer, Hofer and
Salamon). Let `u` be a `C²` solution on `ℝ × ℝ` of the Floer equation
`∂ₛu + J_t(u)(∂ₜu - X_{H_t}(u)) = 0`, for a `C¹` family `J_t` with `J_t(u)² = -1` along `u` and a
`C²` Hamiltonian `H`, converging pointwise in `t` to continuous loops `xm` and `xp` as `s → -∞`
and `s → +∞`. If `u` is not stationary, its regular points form a dense subset of `ℝ × ℝ`. -/
theorem dense_regularPoints (hJ : ContDiff ℝ 1 (fun p : ℝ × V ↦ J p.1 p.2))
    (hJJ : ∀ z, J z.2 (u z) ∘L J z.2 (u z) = -ContinuousLinearMap.id ℝ V)
    (hH : ContDiff ℝ 2 (uncurry H)) (hu : ContDiff ℝ 2 u)
    (hF : ∀ z, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u z = 0)
    (hne : ∃ z, fderiv ℝ u z stdComplexLineReal ≠ 0) (hxm : Continuous xm) (hxp : Continuous xp)
    (hm : ∀ t, Tendsto (fun s ↦ u (s, t)) atBot (𝓝 (xm t)))
    (hp : ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (xp t))) :
    Dense (regularPoints u xm xp) := by
  have hJ' : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1.2 p.2) :=
    hJ.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  have hKt : ContDiff ℝ 2 (uncurry fun (p : ℝ × ℝ) ↦ H p.2) :=
    hH.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  have hs (z : ℝ × ℝ) : ∀ᶠ c : ℝ in 𝓝 0, (z + c • stdComplexLineReal).2 = z.2 :=
    Eventually.of_forall fun c ↦ by simp [stdComplexLineReal_eq]
  have hsJ (z : ℝ × ℝ) : ∀ᶠ c : ℝ in 𝓝 0,
      (fun p : ℝ × ℝ ↦ J p.2) (z + c • stdComplexLineReal) = J z.2 :=
    (hs z).mono fun c h ↦ by simp only [h]
  have hsH (z : ℝ × ℝ) : ∀ᶠ c : ℝ in 𝓝 0,
      (fun p : ℝ × ℝ ↦ H p.2) (z + c • stdComplexLineReal) = H z.2 :=
    (hs z).mono fun c h ↦ by simp only [h]
  -- The points with `∂ₛu ≠ 0` away from the asymptotic orbits form a dense open set `G`.
  set G := {z : ℝ × ℝ | fderiv ℝ u z stdComplexLineReal ≠ 0 ∧ u z ≠ xm z.2 ∧ u z ≠ xp z.2}
  have hGd : Dense G := dense_setOf_fderiv_apply_ne_zero_and_ne_and_ne_of_floerOperator_eq_zero
    hsJ (fun _ ↦ Eventually.of_forall fun _ ↦ rfl) hsH (fun _ ↦ hJ'.contDiffAt) hJJ
    (fun _ ↦ contDiff_const.contDiffAt) (fun _ ↦ hKt.contDiffAt) hu hF hne hxm hxp
  have hGo : IsOpen G :=
    (isOpen_ne_fun ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      continuous_const).inter ((isOpen_ne_fun hu.continuous (hxm.comp continuous_snd)).inter
        (isOpen_ne_fun hu.continuous (hxp.comp continuous_snd)))
  -- The zeros of `∂ₛu` are isolated, hence countable.
  have hcod :=
    SymplecticForm.setOf_fderiv_apply_ne_zero_mem_codiscreteWithin_of_floerOperator_eq_zero
    isOpen_univ isPreconnected_univ (fun z _ ↦ hsJ z) (fun _ _ ↦ Eventually.of_forall fun _ ↦ rfl)
    (fun z _ ↦ hsH z) (fun _ _ ↦ hJ'.contDiffAt) (fun z _ ↦ hJJ z)
    (fun _ _ ↦ contDiff_const.contDiffAt) (fun _ _ ↦ hKt.contDiffAt) hu.contDiffOn
    (fun z _ ↦ hF z) (by simpa using hne)
  have hcrit : {w : ℝ × ℝ | fderiv ℝ u w stdComplexLineReal = 0}.Countable := by
    refine (countable_iUnion fun n : ℕ ↦ ((isCompact_closedBall (0 : ℝ × ℝ) n
      ).finite_sdiff_of_mem_codiscreteWithin (codiscreteWithin_mono (subset_univ _) hcod)
      ).countable).mono fun w hw ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (dist w 0)
    exact mem_iUnion.2 ⟨n, mem_closedBall.2 hn, fun h ↦ h hw⟩
  refine dense_iff_inter_open.2 fun U hU hUne ↦ ?_
  by_contra hreg
  obtain ⟨z₀, hz₀U, hz₀G⟩ := dense_iff_inter_open.1 hGd U hU hUne
  -- Without regular points in `U`, every point of `U ∩ G` has a partner on its slice.
  have hpart : ∀ z ∈ U ∩ G, ∃ s ≠ z.1, u (s, z.2) = u z := by
    rintro z ⟨hzU, hzG⟩
    by_contra! h
    exact hreg ⟨z, hzU, hzG.1, hzG.2.1, hzG.2.2, fun s hs ↦ by_contra fun hsz ↦ h s hsz hs⟩
  obtain ⟨U₀, D, ε, hU₀, hU₀ne, hD, hDs, hinj, hε, hpart₀⟩ :=
    exists_isCompact_forall_exists_slicePartner (hu.of_le (by norm_num)) hcrit (hU.inter hGo)
      ⟨z₀, hz₀U, hz₀G⟩ hpart
  obtain ⟨c, hc, hper⟩ := exists_ne_zero_periodic_of_forall_exists_slicePartner hJ hJJ hH
    (hu.of_le (by norm_num)) hF hU₀ hU₀ne hD hDs hinj hε hpart₀
  -- A period `(c, 0)` with `c ≠ 0` moves `z₀` to an end, where `u` is an asymptotic orbit.
  have hslice : Periodic (fun s ↦ u (s, z₀.2)) c := fun s ↦ by simpa using hper (s, z₀.2)
  exact (hslice.eq_or_eq_of_tendsto hc (hm _) (hp _) z₀.1).elim hz₀G.2.1 hz₀G.2.2

end Dense

end TauCeti.Floer

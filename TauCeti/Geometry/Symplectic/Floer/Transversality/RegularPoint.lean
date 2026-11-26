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
nonstationary trajectory form an open dense set. The argument uses the Floer equation only on a
band `ℝ × T` over an open interval `T`, and is carried out there: for `T = ℝ` this is the plane of
a Floer cylinder, and for `T = (0, 1)` the open strip on which a Floer strip between two
Lagrangians solves the equation. The boundary conditions of a strip play no role. The proof has
three parts.

* **Openness.** If `u` is `C¹` on the band and converges uniformly on `T` to loops `xm` and `xp`
  continuous on `T`, the regular points in the band form an open set
  (`TauCeti.Floer.isOpen_univ_prod_inter_regularPoints`, and `TauCeti.Floer.isOpen_regularPoints`
  for `T = ℝ`). The topological core (`TauCeti.eventually_forall_slice_eq_imp_eq_of_tendsto`)
  needs only a map into a Hausdorff space continuous along the slice, with limits along the ends,
  and injectivity
  of `(s, t) ↦ (u(s, t), t)` near the point, which `∂ₛu ≠ 0` provides
  (`TauCeti.Floer.exists_mem_nhds_injOn_of_fderiv_apply_ne_zero`, from the injectivity of its
  derivative). The limits confine the competitors `s'` to a compact interval, and a compactness
  argument separates `u(s', t)` from `u(s, t)` uniformly nearby.
* **Separation from the asymptotic orbits.** On an open set where `u(s, t) = x(t)`, `u` does not
  depend on `s`, so `∂ₛu` vanishes there
  (`TauCeti.Floer.interior_setOf_eq_subset_setOf_fderiv_apply_eq_zero`). As the zeros of `∂ₛu`
  in the band are isolated unless `u` is stationary
  (`SymplecticForm.setOf_fderiv_apply_ne_zero_mem_codiscreteWithin_of_floerOperator_eq_zero`),
  the points where `∂ₛu ≠ 0`, `u ≠ xm` and `u ≠ xp` are dense in the band for every nonstationary
  solution of a Floer equation on it
  (`Floer.subset_closure_inter_setOf_fderiv_apply_ne_zero_and_ne_and_ne_of_floerOperator_eq_zero`).
* **Density.** For a nonstationary solution on the band of a Floer equation whose data `J_t` and
  `H_t` do not depend on `s`, converging pointwise on `T` to loops `xm` and `xp` continuous on
  `T`, the regular points in the band are dense in the band
  (`TauCeti.Floer.subset_closure_inter_regularPoints`, and `TauCeti.Floer.dense_regularPoints`
  for `T = ℝ`). Suppose an open set `U` meets the band but contains no regular point of it. By
  Baire's theorem, on a smaller open set the competitors `s'` can be chosen continuously, as a
  function `φ(s, t)`, at points where `∂ₛu ≠ 0`
  (`TauCeti.exists_continuousOn_slice_eq_of_forall_exists_ne`): the competitors stay in the band,
  where the critical points of `s ↦ u(s, t)` are countable
  (`TauCeti.Floer.countable_inter_setOf_fderiv_apply_eq_zero_of_floerOperator_eq_zero`). Since
  `(s, t) ↦ (u(s, t), t)` is an immersion there, `φ` is differentiable
  (`TauCeti.Floer.exists_hasFDerivAt_of_eventually_slice_eq`), and differentiating
  `u(φ(s, t), t) = u(s, t)` with the Floer equation at both points shows `∂ₛφ = 1` and `∂ₜφ = 0`
  (`TauCeti.Floer.hasFDerivAt_fst_of_floerOperator_eq_zero`), because `∂ₛu` and `J ∂ₛu` are
  linearly independent. So `φ(s, t) = s + c` with `c ≠ 0`
  (`TauCeti.Floer.exists_eventually_eq_add_of_floerOperator_eq_zero`), and `u` agrees with its
  translate `u(· + c, ·)` on an open set. By unique continuation it agrees with it on the band
  (`TauCeti.SymplecticForm.eqOn_comp_add_of_floerOperator_eq_zero_of_eqOn`), so its slices are
  periodic in `s`, which their limits along the ends forbid at points away from the asymptotic
  orbits (`Function.Periodic.eq_or_eq_of_tendsto`).

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

/-- **The regular points in a band form an open set.** Let `T ⊆ ℝ` be open. If `u` is `C¹` on the
band `ℝ × T` and converges, uniformly for `t ∈ T`, to loops `xm` and `xp` continuous on `T` as
`s → -∞` and `s → +∞`, then its regular points in the band form an open subset of `ℝ × ℝ`. -/
theorem isOpen_univ_prod_inter_regularPoints {T : Set ℝ} (hT : IsOpen T)
    (hu : ContDiffOn ℝ 1 u (univ ×ˢ T))
    (hxm : ContinuousOn xm T) (hxp : ContinuousOn xp T)
    (hm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot T)
    (hp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop T) :
    IsOpen (univ ×ˢ T ∩ regularPoints u xm xp) := by
  -- Uniform convergence along an end gives convergence as `s` tends to the end and `t → t₀ ∈ T`.
  have hlim {l : Filter ℝ} {x : ℝ → V} (h : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l T)
      (hx : ContinuousOn x T) {t₀ : ℝ} (ht₀ : t₀ ∈ T) : Tendsto u (l ×ˢ 𝓝 t₀) (𝓝 (x t₀)) := by
    have h' : TendstoUniformlyOn (fun (p : ℝ × ℝ) t ↦ u (p.1, t)) x (l ×ˢ 𝓝 t₀) T :=
      fun U hU ↦ tendsto_fst.eventually (h U hU)
    exact h'.tendsto_comp (hx.continuousWithinAt ht₀)
      (tendsto_nhdsWithin_iff.2 ⟨tendsto_snd, tendsto_snd.eventually (hT.mem_nhds ht₀)⟩)
  have hB : IsOpen (univ ×ˢ T : Set (ℝ × ℝ)) := isOpen_univ.prod hT
  refine isOpen_iff_mem_nhds.2 fun z hz ↦ ?_
  obtain ⟨⟨-, hzT⟩, hd, hmz, hpz, hinj⟩ := hz
  -- `u` is continuous along the slice through `z`, which lies in the band.
  have hcont (s : ℝ) : ContinuousAt u (s, z.2) :=
    hu.continuousOn.continuousAt (hB.mem_nhds ⟨mem_univ s, hzT⟩)
  have hzB : univ ×ˢ T ∈ 𝓝 z := hB.mem_nhds ⟨mem_univ _, hzT⟩
  have hx {x : ℝ → V} (hx : ContinuousOn x T) : ContinuousAt (fun w : ℝ × ℝ ↦ x w.2) z :=
    (hx.continuousAt (hT.mem_nhds hzT)).comp continuous_snd.continuousAt
  filter_upwards [continuous_snd.continuousAt.eventually_mem (hT.mem_nhds hzT),
    ((hu.continuousOn_fderiv_of_isOpen hB le_rfl).continuousAt hzB).clm_apply continuousAt_const
      |>.eventually_ne hd,
    ((hcont z.1).ne_iff_eventually_ne (hx hxm)).1 hmz,
    ((hcont z.1).ne_iff_eventually_ne (hx hxp)).1 hpz,
    eventually_forall_slice_eq_imp_eq_of_tendsto hcont (hlim hm hxm hzT) (hlim hp hxp hzT)
      (exists_mem_nhds_injOn_of_fderiv_apply_ne_zero (hu.contDiffAt hzB) hd) hmz hpz hinj]
    with w h₀ h₁ h₂ h₃ h₄
  exact ⟨⟨mem_univ _, h₀⟩, h₁, h₂, h₃, h₄⟩

/-- **The regular points form an open set.** If `u` is `C¹` and converges, uniformly in `t`, to
continuous loops `xm` and `xp` as `s → -∞` and `s → +∞`, then its regular points form an open
subset of `ℝ × ℝ`. -/
theorem isOpen_regularPoints (hu : ContDiff ℝ 1 u) (hxm : Continuous xm) (hxp : Continuous xp)
    (hm : TendstoUniformly (fun s t ↦ u (s, t)) xm atBot)
    (hp : TendstoUniformly (fun s t ↦ u (s, t)) xp atTop) :
    IsOpen (regularPoints u xm xp) := by
  simpa using isOpen_univ_prod_inter_regularPoints isOpen_univ hu.contDiffOn hxm.continuousOn
    hxp.continuousOn hm.tendstoUniformlyOn hp.tendstoUniformlyOn

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

omit [NormedSpace ℝ V] in
/-- The points of a band `ℝ × T`, for an open `T`, at which a map `u` continuous on the band differs
from a loop continuous on `T` form an open set. -/
private theorem isOpen_univ_prod_inter_setOf_ne {T : Set ℝ} (hT : IsOpen T)
    (hu : ContinuousOn u (univ ×ˢ T)) (hx : ContinuousOn x T) :
    IsOpen (univ ×ˢ T ∩ {z | u z ≠ x z.2}) :=
  (hu.prodMk (hx.comp continuousOn_snd mapsTo_snd_prod)).isOpen_inter_preimage
    (isOpen_univ.prod hT) (isOpen_ne_fun continuous_fst continuous_snd)

/-- **Points away from the critical points of `s ↦ u` and from two loops are dense in a band.**
Let `T ⊆ ℝ` be open, let `u` be continuous on the band `ℝ × T`, with `∂ₛu ≠ 0` on a dense subset
of the band,
and let `xm` and `xp` be loops continuous on `T`. Then the points of the band where `∂ₛu ≠ 0`,
`u(s, t) ≠ xm(t)` and `u(s, t) ≠ xp(t)` are dense in the band. -/
theorem subset_closure_inter_setOf_fderiv_apply_ne_zero_and_ne_and_ne {T : Set ℝ} (hT : IsOpen T)
    (hu : ContinuousOn u (univ ×ˢ T)) (hxm : ContinuousOn xm T) (hxp : ContinuousOn xp T)
    (h : univ ×ˢ T ⊆ closure (univ ×ˢ T ∩ {z | fderiv ℝ u z stdComplexLineReal ≠ 0})) :
    univ ×ˢ T ⊆ closure (univ ×ˢ T ∩
      {z | fderiv ℝ u z stdComplexLineReal ≠ 0 ∧ u z ≠ xm z.2 ∧ u z ≠ xp z.2}) := by
  -- Every nonempty open subset of the band contains a point where `∂ₛu ≠ 0`.
  have hcrit {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOT : O ⊆ univ ×ˢ T) (hOne : O.Nonempty) :
      (O ∩ {z | fderiv ℝ u z stdComplexLineReal ≠ 0}).Nonempty := by
    obtain ⟨z, hz⟩ := hOne
    obtain ⟨w, hwO, -, hw⟩ := mem_closure_iff.1 (h (hOT hz)) O hO hz
    exact ⟨w, hwO, hw⟩
  -- So it is not contained in the set where `u` follows a loop, on whose interior `∂ₛu = 0`.
  have hloop {x : ℝ → V} (hx : ContinuousOn x T) {O : Set (ℝ × ℝ)} (hO : IsOpen O)
      (hOT : O ⊆ univ ×ˢ T) (hOne : O.Nonempty) :
      IsOpen (O ∩ {z | u z ≠ x z.2}) ∧ (O ∩ {z | u z ≠ x z.2}).Nonempty := by
    refine ⟨?_, not_not.1 fun hne ↦ ?_⟩
    · have h' := hO.inter (isOpen_univ_prod_inter_setOf_ne hT hu hx)
      rwa [← inter_assoc, inter_eq_left.2 hOT] at h'
    · have hsub : O ⊆ {z | u z = x z.2} := fun z hz ↦ not_not.1 fun h' ↦ hne ⟨z, hz, h'⟩
      obtain ⟨z, hzO, hz⟩ := hcrit hO hOT hOne
      exact hz (interior_setOf_eq_subset_setOf_fderiv_apply_eq_zero (interior_maximal hsub hO hzO))
  intro z hz
  refine mem_closure_iff.2 fun o ho hzo ↦ ?_
  have h₁ : o ∩ univ ×ˢ T ⊆ univ ×ˢ T := inter_subset_right
  obtain ⟨ho₂, hne₂⟩ := hloop hxm (ho.inter (isOpen_univ.prod hT)) h₁ ⟨z, hzo, hz⟩
  obtain ⟨ho₃, hne₃⟩ := hloop hxp ho₂ (inter_subset_left.trans h₁) hne₂
  obtain ⟨w, ⟨⟨⟨hwo, hwT⟩, hwm⟩, hwp⟩, hw⟩ :=
    hcrit ho₃ (inter_subset_left.trans (inter_subset_left.trans h₁)) hne₃
  exact ⟨w, hwo, hwT, hw, hwm, hwp⟩

/-- **Separation from the asymptotic orbits.** Let `T ⊆ ℝ` be open and preconnected, and let `u`
be a map, `C²` on the band `ℝ × T`, solving the Floer equation
`∂ₛu - X_{K_s}(u) + J(u)(∂ₜu - X_{K_t}(u)) = 0` there, whose data `J`, `K_s`, `K_t` are invariant
under small translations in `s`, as for a Floer trajectory, with `J` of class `C¹`, the
Hamiltonians of class `C²` near the graph of `u` and `J(z, u z)² = -1` on the band. If `u` is not
stationary on the band, that is `∂ₛu` does not vanish identically there, then for loops `xm` and
`xp` continuous on `T` the points of the band where `∂ₛu ≠ 0`, `u(s, t) ≠ xm(t)` and
`u(s, t) ≠ xp(t)` are dense in the band. -/
theorem subset_closure_inter_setOf_fderiv_apply_ne_zero_and_ne_and_ne_of_floerOperator_eq_zero
    {ω : SymplecticForm V} [FiniteDimensional ℝ V] {J : ℝ × ℝ → V → V →L[ℝ] V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {T : Set ℝ} (hT : IsOpen T) (hTc : IsPreconnected T)
    (hJs : ∀ z ∈ univ ×ˢ T, ∀ᶠ c : ℝ in 𝓝 0, J (z + c • stdComplexLineReal) = J z)
    (hKss : ∀ z ∈ univ ×ˢ T, ∀ᶠ c : ℝ in 𝓝 0, Ks (z + c • stdComplexLineReal) = Ks z)
    (hKts : ∀ z ∈ univ ×ˢ T, ∀ᶠ c : ℝ in 𝓝 0, Kt (z + c • stdComplexLineReal) = Kt z)
    (hJ : ∀ z ∈ univ ×ˢ T, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ univ ×ˢ T, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ univ ×ˢ T, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ univ ×ˢ T, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ContDiffOn ℝ 2 u (univ ×ˢ T)) (hF : ∀ z ∈ univ ×ˢ T, ω.floerOperator J Ks Kt u z = 0)
    (hne : ∃ z ∈ univ ×ˢ T, fderiv ℝ u z stdComplexLineReal ≠ 0) (hxm : ContinuousOn xm T)
    (hxp : ContinuousOn xp T) :
    univ ×ˢ T ⊆ closure (univ ×ˢ T ∩
      {z | fderiv ℝ u z stdComplexLineReal ≠ 0 ∧ u z ≠ xm z.2 ∧ u z ≠ xp z.2}) := by
  have hB : IsOpen (univ ×ˢ T : Set (ℝ × ℝ)) := isOpen_univ.prod hT
  -- The zeros of `∂ₛu` are isolated in the band, so its nonzeros are dense there.
  have hcod :=
    SymplecticForm.setOf_fderiv_apply_ne_zero_mem_codiscreteWithin_of_floerOperator_eq_zero
      hB ((isPreconnected_univ (α := ℝ)).prod hTc) hJs hKss hKts hJ hJJ hKs hKt hu hF hne
  refine subset_closure_inter_setOf_fderiv_apply_ne_zero_and_ne_and_ne hT hu.continuousOn hxm hxp
    fun z hz ↦ mem_closure_iff_frequently.2 ?_
  have h : univ ×ˢ T ∩ {z | fderiv ℝ u z stdComplexLineReal ≠ 0} ∈ 𝓝[≠] z := by
    filter_upwards [mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hcod z hz,
      mem_nhdsWithin_of_mem_nhds (hB.mem_nhds hz)] with w hw hwB
    exact ⟨hwB, ((mem_union _ _ _).1 hw).resolve_right fun h ↦ h hwB⟩
  exact (Eventually.frequently h).filter_mono nhdsWithin_le_nhds

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

/-- **A continuous competitor on the slices of a Floer solution is a translate.** Let `u` be a map,
differentiable at every point of a band `ℝ × T`, solving the Floer equation
`∂ₛu - X_{K_s}(u) + J_t(u)(∂ₜu - X_{K_t}(u)) = 0` there, for data depending only on `t`, with
`J_t(u)² = -1` along `u` on the band. Let `φ` be continuous on an open subset `W` of the band,
with `u(φ(z), z.2) = u(z)` and `∂ₛu(φ(z), z.2) ≠ 0` for every `z ∈ W`. Then near every point of
`W`, `φ(s, t) = s + c` for a constant `c`. -/
theorem exists_eventually_eq_add_of_floerOperator_eq_zero {ω : SymplecticForm V}
    [FiniteDimensional ℝ V] {J : ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ → V → ℝ} {φ : ℝ × ℝ → ℝ}
    {T : Set ℝ} {W : Set (ℝ × ℝ)}
    (hJJ : ∀ z ∈ univ ×ˢ T, J z.2 (u z) ∘L J z.2 (u z) = -ContinuousLinearMap.id ℝ V)
    (hu : ∀ z ∈ univ ×ˢ T, DifferentiableAt ℝ u z)
    (hF : ∀ z ∈ univ ×ˢ T,
      ω.floerOperator (fun p ↦ J p.2) (fun p ↦ Ks p.2) (fun p ↦ Kt p.2) u z = 0)
    (hW : IsOpen W) (hWT : W ⊆ univ ×ˢ T) (hφc : ContinuousOn φ W)
    (hφu : ∀ z ∈ W, u (φ z, z.2) = u z)
    (hφd : ∀ z ∈ W, fderiv ℝ u (φ z, z.2) stdComplexLineReal ≠ 0) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ W) :
    ∃ c, ∀ᶠ z in 𝓝 z₀, φ z = z.1 + c := by
  -- `φ - fst` has derivative zero on `W`, so it is constant on a ball around `z₀`.
  have hd (z) (hz : z ∈ W) : HasFDerivAt (fun w ↦ φ w - w.1) (0 : ℝ × ℝ →L[ℝ] ℝ) z := by
    have hφz : (φ z, z.2) ∈ univ ×ˢ T := ⟨mem_univ _, (hWT hz).2⟩
    have h := (hasFDerivAt_fst_of_floerOperator_eq_zero (hJJ z (hWT hz)) (hu z (hWT hz))
      (hu _ hφz) (hF z (hWT hz)) (hF _ hφz)
      ((hφc z hz).continuousAt (hW.mem_nhds hz)) (Filter.eventually_of_mem (hW.mem_nhds hz) hφu)
        (hφd z hz)).sub (hasFDerivAt_fst (p := z))
    rwa [sub_self] at h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW z₀ hz₀
  refine ⟨φ z₀ - z₀.1, Filter.eventually_of_mem (ball_mem_nhds z₀ hε) fun z hz ↦ ?_⟩
  have h := isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball z₀ ε).isPreconnected
    (fun w hw ↦ (hd w (hball hw)).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hd w (hball hw)).fderiv) hz (mem_ball_self hε)
  linarith

/-- **The critical points of a nonstationary Floer solution are countable.** Let `u` be `C²` on
a connected open set `Ω ⊆ ℝ × ℝ` and solve the Floer equation
`∂ₛu - X_{K_s}(u) + J(u)(∂ₜu - X_{K_t}(u)) = 0` there, where the data `J`, `K_s`, `K_t` are
invariant under small translations in `s`, `J` is `C¹` and the Hamiltonians are `C²` near the graph
of `u`, and `J(z, u z)² = -1` on `Ω`. If `u` is not stationary on `Ω`, that is `∂ₛu` does not
vanish identically there, then the points of `Ω` where `∂ₛu = 0` form a countable set. -/
theorem countable_inter_setOf_fderiv_apply_eq_zero_of_floerOperator_eq_zero
    {ω : SymplecticForm V} [FiniteDimensional ℝ V] {J : ℝ × ℝ → V → V →L[ℝ] V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJs : ∀ z ∈ Ω, ∀ᶠ c : ℝ in 𝓝 0, J (z + c • stdComplexLineReal) = J z)
    (hKss : ∀ z ∈ Ω, ∀ᶠ c : ℝ in 𝓝 0, Ks (z + c • stdComplexLineReal) = Ks z)
    (hKts : ∀ z ∈ Ω, ∀ᶠ c : ℝ in 𝓝 0, Kt (z + c • stdComplexLineReal) = Kt z)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 2 u Ω)
    (hF : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hne : ∃ z ∈ Ω, fderiv ℝ u z stdComplexLineReal ≠ 0) :
    (Ω ∩ {z | fderiv ℝ u z stdComplexLineReal = 0}).Countable := by
  -- The zeros of `∂ₛu` in `Ω` are isolated, so they form a discrete, hence countable, set.
  have hcod :=
    SymplecticForm.setOf_fderiv_apply_ne_zero_mem_codiscreteWithin_of_floerOperator_eq_zero
      hΩ hΩc hJs hKss hKts hJ hJJ hKs hKt hu hF hne
  have hdisc : IsDiscrete ({z | fderiv ℝ u z stdComplexLineReal = 0} ∩ Ω) :=
    isDiscrete_of_codiscreteWithin (by simpa only [compl_ofPred] using hcod)
  rw [inter_comm]
  exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc

/-- The points of a band `ℝ × T`, for an open `T`, where `∂ₛu ≠ 0` form an open set, for a map `u`
that is `C¹` on the band. -/
private theorem isOpen_univ_prod_inter_setOf_fderiv_apply_ne_zero {T : Set ℝ} (hT : IsOpen T)
    (hu : ContDiffOn ℝ 1 u (univ ×ˢ T)) :
    IsOpen (univ ×ˢ T ∩ {z | fderiv ℝ u z stdComplexLineReal ≠ 0}) :=
  ((hu.continuousOn_fderiv_of_isOpen (isOpen_univ.prod hT) le_rfl).clm_apply
    continuousOn_const).isOpen_inter_preimage (isOpen_univ.prod hT) isOpen_ne

/-- The points of a band `ℝ × T`, for an open `T`, where `∂ₛu ≠ 0` and `u` differs from two loops
continuous on `T` form an open set, for a map `u` that is `C¹` on the band. -/
private theorem isOpen_univ_prod_inter_setOf_fderiv_apply_ne_zero_and_ne_and_ne {T : Set ℝ}
    (hT : IsOpen T) (hu : ContDiffOn ℝ 1 u (univ ×ˢ T)) (hxm : ContinuousOn xm T)
    (hxp : ContinuousOn xp T) :
    IsOpen (univ ×ˢ T ∩
      {z | fderiv ℝ u z stdComplexLineReal ≠ 0 ∧ u z ≠ xm z.2 ∧ u z ≠ xp z.2}) := by
  have he : univ ×ˢ T ∩
      {z | fderiv ℝ u z stdComplexLineReal ≠ 0 ∧ u z ≠ xm z.2 ∧ u z ≠ xp z.2} =
      (univ ×ˢ T ∩ {z | fderiv ℝ u z stdComplexLineReal ≠ 0}) ∩
        ((univ ×ˢ T ∩ {z | u z ≠ xm z.2}) ∩ (univ ×ˢ T ∩ {z | u z ≠ xp z.2})) := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  rw [he]
  exact (isOpen_univ_prod_inter_setOf_fderiv_apply_ne_zero hT hu).inter
    ((isOpen_univ_prod_inter_setOf_ne hT hu.continuousOn hxm).inter
      (isOpen_univ_prod_inter_setOf_ne hT hu.continuousOn hxp))

/-- **A Floer solution agreeing with a translate takes only asymptotic values.** Let `T ⊆ ℝ` be
open and preconnected, and let `u` be a map, `C¹` on the band `ℝ × T`, solving the Floer equation
`∂ₛu + J_t(u)(∂ₜu - X_{H_t}(u)) = 0` there, for a `C¹` family `J_t` with
`J_t(u)² = -1` along `u` on the band and a `C²` Hamiltonian `H`, with `u(s, t) → xm(t)` as
`s → -∞` and `u(s, t) → xp(t)` as `s → +∞` for every `t ∈ T`. If `u(s + c, t) = u(s, t)` on a
nonempty open subset of the band, for some `c ≠ 0`, then `u(s, t)` is `xm(t)` or `xp(t)` at every
point of the band. -/
theorem eq_or_eq_of_eqOn_comp_add_of_floerOperator_eq_zero {ω : SymplecticForm V}
    [FiniteDimensional ℝ V] {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {T : Set ℝ} (hT : IsOpen T)
    (hTc : IsPreconnected T) (hJ : ContDiff ℝ 1 (fun p : ℝ × V ↦ J p.1 p.2))
    (hJJ : ∀ z ∈ univ ×ˢ T, J z.2 (u z) ∘L J z.2 (u z) = -ContinuousLinearMap.id ℝ V)
    (hH : ContDiff ℝ 2 (uncurry H)) (hu : ContDiffOn ℝ 1 u (univ ×ˢ T))
    (hF : ∀ z ∈ univ ×ˢ T,
      ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u z = 0)
    (hm : ∀ t ∈ T, Tendsto (fun s ↦ u (s, t)) atBot (𝓝 (xm t)))
    (hp : ∀ t ∈ T, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (xp t))) {c : ℝ} (hc : c ≠ 0)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hUne : U.Nonempty) (hUT : U ⊆ univ ×ˢ T)
    (hUc : EqOn u (fun z ↦ u (z + (c, 0))) U) {z : ℝ × ℝ} (hz : z ∈ univ ×ˢ T) :
    u z = xm z.2 ∨ u z = xp z.2 := by
  -- By unique continuation `u` agrees with its translate on the band, so the slice through `z` is
  -- periodic, and a periodic map with limits at both ends takes only these values.
  have hper := SymplecticForm.eqOn_comp_add_of_floerOperator_eq_zero_of_eqOn hT hTc hJ hJJ hH hu
    hF hU hUne hUT hUc
  have hslice : Periodic (fun s ↦ u (s, z.2)) c := fun s ↦ by
    simpa using (hper (show (s, z.2) ∈ univ ×ˢ T from ⟨mem_univ s, hz.2⟩)).symm
  exact hslice.eq_or_eq_of_tendsto hc (hm _ hz.2) (hp _ hz.2) z.1

/-- **The regular points of a nonstationary Floer solution are dense in its band** (Floer, Hofer
and Salamon). Let `T ⊆ ℝ` be open and preconnected, and let `u` be a map, `C²` on the band
`ℝ × T`, solving the Floer equation `∂ₛu + J_t(u)(∂ₜu - X_{H_t}(u)) = 0` there, for a `C¹` family
`J_t` with `J_t(u)² = -1` along `u` on the band and a `C²` Hamiltonian `H`. Suppose `u(s, t)`
tends to `xm(t)` as `s → -∞` and to `xp(t)` as `s → +∞` for every `t ∈ T`, for loops `xm` and
`xp` continuous on `T`. If `u` is not stationary on the band, that is `∂ₛu` does not vanish
identically there, then its regular points in the band are dense in the band. For `T = (0, 1)`
this is the density of the regular points of a Floer strip between two Lagrangians, which need
only be `C²` on the open strip and solve the equation there; no boundary condition enters. -/
theorem subset_closure_inter_regularPoints {ω : SymplecticForm V} [FiniteDimensional ℝ V]
    {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {T : Set ℝ} (hT : IsOpen T) (hTc : IsPreconnected T)
    (hJ : ContDiff ℝ 1 (fun p : ℝ × V ↦ J p.1 p.2))
    (hJJ : ∀ z ∈ univ ×ˢ T, J z.2 (u z) ∘L J z.2 (u z) = -ContinuousLinearMap.id ℝ V)
    (hH : ContDiff ℝ 2 (uncurry H)) (hu : ContDiffOn ℝ 2 u (univ ×ˢ T))
    (hF : ∀ z ∈ univ ×ˢ T,
      ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u z = 0)
    (hne : ∃ z ∈ univ ×ˢ T, fderiv ℝ u z stdComplexLineReal ≠ 0) (hxm : ContinuousOn xm T)
    (hxp : ContinuousOn xp T) (hm : ∀ t ∈ T, Tendsto (fun s ↦ u (s, t)) atBot (𝓝 (xm t)))
    (hp : ∀ t ∈ T, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (xp t))) :
    univ ×ˢ T ⊆ closure (univ ×ˢ T ∩ regularPoints u xm xp) := by
  have hB : IsOpen (univ ×ˢ T : Set (ℝ × ℝ)) := isOpen_univ.prod hT
  have hBc : IsPreconnected (univ ×ˢ T : Set (ℝ × ℝ)) := (isPreconnected_univ (α := ℝ)).prod hTc
  have hu1 : ContDiffOn ℝ 1 u (univ ×ˢ T) := hu.of_le one_le_two
  have hG := isOpen_univ_prod_inter_setOf_fderiv_apply_ne_zero hT hu1
  -- The data `J_t`, `0` and `H_t`, seen on `ℝ × ℝ`, are invariant in `s` and regular along `u`.
  have hinv {α : Type _} (f : ℝ → α) (z : ℝ × ℝ) (_ : z ∈ univ ×ˢ T) : ∀ᶠ c : ℝ in 𝓝 0,
      (fun p : ℝ × ℝ ↦ f p.2) (z + c • stdComplexLineReal) = (fun p ↦ f p.2) z :=
    Eventually.of_forall fun c ↦ by simp [stdComplexLineReal_eq]
  have hJ' (z : ℝ × ℝ) (_ : z ∈ univ ×ˢ T) :
      ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1.2 p.2) (z, u z) :=
    (hJ.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)).contDiffAt
  have hH' (z : ℝ × ℝ) (_ : z ∈ univ ×ˢ T) :
      ContDiffAt ℝ 2 (uncurry fun p : ℝ × ℝ ↦ H p.2) (z, u z) :=
    (hH.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)).contDiffAt
  have hK₀ (z : ℝ × ℝ) (_ : z ∈ univ ×ˢ T) :
      ContDiffAt ℝ 2 (uncurry fun (_ : ℝ × ℝ) (_ : V) ↦ (0 : ℝ)) (z, u z) :=
    contDiff_const.contDiffAt
  -- The points of the band with `∂ₛu ≠ 0` away from the asymptotic orbits form an open set `D`,
  -- dense in the band.
  have hD := subset_closure_inter_setOf_fderiv_apply_ne_zero_and_ne_and_ne_of_floerOperator_eq_zero
    hT hTc (hinv J) (hinv fun _ _ ↦ (0 : ℝ)) (hinv H) hJ' hJJ hK₀ hH' hu hF hne hxm hxp
  -- Suppose an open set `U` meeting the band has no regular point in the band. The competitors of
  -- the points of `U ∩ D` lie in the band, so they are chosen continuously on an open `W`, away
  -- from the countably many critical points in the band.
  have hGc : (univ ×ˢ T \ (univ ×ˢ T ∩ {z | fderiv ℝ u z stdComplexLineReal ≠ 0})).Countable := by
    refine (countable_inter_setOf_fderiv_apply_eq_zero_of_floerOperator_eq_zero hB hBc (hinv J)
      (hinv fun _ _ ↦ (0 : ℝ)) (hinv H) hJ' hJJ hK₀ hH' hu hF hne).mono fun w hw ↦ ?_
    exact ⟨hw.1, not_not.1 fun h ↦ hw.2 ⟨hw.1, h⟩⟩
  intro z hz
  refine mem_closure_iff.2 fun U hU hzU ↦ not_not.1 fun hR ↦ ?_
  obtain ⟨W, hWU, hWo, ⟨z₀, hz₀⟩, φ, hφc, hφ⟩ := exists_continuousOn_slice_eq_of_forall_exists_ne
    hu.continuousOn hB hG inter_subset_left (fun p hp ↦
      exists_mem_nhds_injOn_of_fderiv_apply_ne_zero (hu1.contDiffAt (hB.mem_nhds hp.1)) hp.2) hGc
    (hU.inter (isOpen_univ_prod_inter_setOf_fderiv_apply_ne_zero_and_ne_and_ne hT hu1 hxm hxp))
    (fun w hw ↦ hw.2.1) (mem_closure_iff.1 (hD hz) U hU hzU) fun w hw ↦ by
      have hwR : w ∉ regularPoints u xm xp := fun h ↦ hR ⟨w, hw.1, hw.2.1, h⟩
      simp only [mem_regularPoints, not_and, not_forall] at hwR
      obtain ⟨s, hs, hsw⟩ := hwR hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2
      exact ⟨s, hsw, ⟨mem_univ _, hw.2.1.2⟩, hs⟩
  -- By the Floer equation `φ(z) = z.1 + c` near `z₀`, with `c ≠ 0`; so `u(s + c, t) = u(s, t)`
  -- near `z₀`, hence on the band, by unique continuation.
  obtain ⟨c, hc⟩ := exists_eventually_eq_add_of_floerOperator_eq_zero (Ks := fun _ _ ↦ 0)
    (Kt := H) hJJ (fun w hw ↦ (hu1.differentiableOn one_ne_zero).differentiableAt (hB.mem_nhds hw))
    hF hWo (fun w hw ↦ (hWU hw).2.1) hφc (fun w hw ↦ (hφ w hw).2.1) (fun w hw ↦ (hφ w hw).2.2.2)
    hz₀
  have hc₀ : c ≠ 0 := fun h ↦ (hφ z₀ hz₀).1 (by simpa [h] using hc.self_of_nhds)
  obtain ⟨N, hN, hNo, hz₀N⟩ := _root_.mem_nhds_iff.1 (inter_mem hc (hWo.mem_nhds hz₀))
  -- So `u(z₀)` is the value of an asymptotic orbit, contrary to `z₀ ∈ D`.
  obtain ⟨hz₀B, -, hzm, hzp⟩ := (hWU hz₀).2
  exact (eq_or_eq_of_eqOn_comp_add_of_floerOperator_eq_zero hT hTc hJ hJJ hH hu1 hF hm hp hc₀ hNo
    ⟨z₀, hz₀N⟩ (fun w hw ↦ (hWU (hN hw).2).2.1)
    (fun w hw ↦
      (hφ w (hN hw).2).2.1.symm.trans (congrArg u (Prod.ext (hN hw).1 (add_zero _).symm)))
    hz₀B).elim hzm hzp

/-- **The regular points of a nonstationary Floer trajectory are dense** (Floer, Hofer and
Salamon). Let `u` be a `C²` solution on `ℝ × ℝ` of the Floer equation
`∂ₛu + J_t(u)(∂ₜu - X_{H_t}(u)) = 0`, for a `C¹` family `J_t` with `J_t(u)² = -1` along `u` and a
`C²` Hamiltonian `H`. Suppose `u(s, t)` tends to `xm(t)` as `s → -∞` and to `xp(t)` as `s → +∞`,
for continuous loops `xm` and `xp`. If `u` is not stationary, that is `∂ₛu` does not vanish
identically, then its regular points are dense in `ℝ × ℝ`. -/
theorem dense_regularPoints {ω : SymplecticForm V} [FiniteDimensional ℝ V]
    {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} (hJ : ContDiff ℝ 1 (fun p : ℝ × V ↦ J p.1 p.2))
    (hJJ : ∀ z, J z.2 (u z) ∘L J z.2 (u z) = -ContinuousLinearMap.id ℝ V)
    (hH : ContDiff ℝ 2 (uncurry H)) (hu : ContDiff ℝ 2 u)
    (hF : ∀ z, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u z = 0)
    (hne : ∃ z, fderiv ℝ u z stdComplexLineReal ≠ 0) (hxm : Continuous xm) (hxp : Continuous xp)
    (hm : ∀ t, Tendsto (fun s ↦ u (s, t)) atBot (𝓝 (xm t)))
    (hp : ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (xp t))) :
    Dense (regularPoints u xm xp) := by
  obtain ⟨z, hz⟩ := hne
  have h := subset_closure_inter_regularPoints isOpen_univ isPreconnected_univ hJ
    (fun z _ ↦ hJJ z) hH hu.contDiffOn (fun z _ ↦ hF z) ⟨z, by simp, hz⟩ hxm.continuousOn
    hxp.continuousOn
    (fun t _ ↦ hm t) (fun t _ ↦ hp t)
  rw [dense_iff_closure_eq, ← univ_subset_iff]
  simpa using h

end TauCeti.Floer

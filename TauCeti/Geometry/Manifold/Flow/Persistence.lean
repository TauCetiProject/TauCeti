/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Parametric

/-!
# Nondegeneracy of closed orbits is an open condition in families of vector fields

Let `v a` be a family of vector fields on a Hausdorff boundaryless finite-dimensional manifold `M`,
indexed by the points `a` of a Hausdorff boundaryless Banach manifold `N` and jointly `C¹`. A
closed orbit of `v a` through `p` with return time `T` is *nondegenerate* when, for some local
section `{g = g p}` transverse to `v a` at `p`, `1` is not an eigenvalue of the linearized return
map `TauCeti.returnDerivative (v a) g T p`; by `TauCeti.hasEigenvalue_returnDerivative_iff` this
does not depend on the section or on the point of the orbit. This file proves that nondegeneracy
of the closed orbits in a compact window is an open condition on the parameter.

* **Local persistence.** If the closed orbit of `v a₀` through `p` with return time `T₀` is
  nondegenerate for the section `{g = g p}`, then every closed orbit of `v a` through a point `x`
  with return time `t`, for `(a, t, x)` close to `(a₀, T₀, p)`, is nondegenerate for the section
  `{g = g x}` (`TauCeti.eventually_not_hasEigenvalue_returnDerivative_of_flowOf_eq`). Flowing `x`
  for a short time into the section through `p`
  (`TauCeti.exists_eventually_flowOf_mem_level_and_tendsto`) lands on a closed orbit of `v a`
  through that section with return time `t`. Near `(a₀, T₀, p)` these are the continued orbits of
  `TauCeti.exists_contMDiffAt_closedOrbit_continuation`, which are nondegenerate, and
  nondegeneracy moves back along the orbit to `x`.
* **Compact windows.** Let `S` be a compact set of pairs `(t, x)` in the flow domain of `v a₀`
  such that every closed-orbit solution `flowOf (v a₀) t x = x` in `S` is nondegenerate. Then for
  every `a` near `a₀` the set `S` lies in the flow domain of `v a` and every closed-orbit solution
  of `v a` in `S` is nondegenerate
  (`TauCeti.eventually_subset_flowDomain_and_forall_not_hasEigenvalue_returnDerivative`). The pairs
  of `S` that are not solutions for `v a₀` stay non-solutions nearby, since the flow depends
  continuously on the parameter, and the tube lemma assembles these local statements over `S`. So
  the parameters for which this holds form an open set
  (`TauCeti.isOpen_setOf_subset_flowDomain_and_forall_not_hasEigenvalue_returnDerivative`).

This is the openness step for nondegenerate closed orbits (a weaker condition than the
hyperbolicity in the Kupka–Smale theorem), stated for families: for a family of perturbations of a
field, small perturbations keep the closed orbits in a compact window nondegenerate. By
`TauCeti.finite_image_fst_setOf_flowOf_eq`, the perturbed fields then have finitely many periods
of closed orbits in the window.

## Main results

* `TauCeti.exists_eventually_flowOf_mem_level_and_tendsto`: nearby points flow into a transverse
  section, uniformly in the parameter.
* `TauCeti.eventually_not_hasEigenvalue_returnDerivative_of_flowOf_eq`: closed orbits near a
  nondegenerate one, of nearby fields and with nearby return times, are nondegenerate.
* `TauCeti.eventually_subset_flowDomain_and_forall_not_hasEigenvalue_returnDerivative`: the closed
  orbits in a compact window stay nondegenerate under small changes of the parameter.
* `TauCeti.isOpen_setOf_subset_flowDomain_and_forall_not_hasEigenvalue_returnDerivative`: the
  parameters whose closed orbits in a compact window are nondegenerate form an open set.

## References

* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 3, §3
  (persistence of hyperbolic closed orbits) and §4 (the Kupka–Smale theorem, whose openness step
  for hyperbolic closed orbits is the compactness argument adapted here).
* M. M. Peixoto, *On an approximation theorem of Kupka and Smale*, J. Differential Equations 3
  (1967), 214–227, §2.
-/

public section

open Function Manifold Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M F G N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N] [T2Space N]
  [IsManifold J 1 N] [BoundarylessManifold J N]
  {v : N → (x : M) → TangentSpace I x} {a₀ : N}

variable (hv : ContMDiff (J.prod I) I.tangent 1
  (fun z : N × M ↦ (⟨z.2, v z.1 z.2⟩ : TangentBundle I M)))
include hv

/-- **Flowing into a transverse section, uniformly in the parameter.** Let `v` be a jointly `C¹`
family of vector fields, and let `g` be `C¹` at `p` with `dg_p (v a₀ p) ≠ 0`, so that `{g = g p}`
is a local section through `p` transverse to `v a₀`. Then each `x` near `p` reaches the section
under the flow of each `v a` with `a` near `a₀`, at a time `σ (a, x)`, and the point reached tends
to `p` as `(a, x)` tends to `(a₀, p)`. -/
theorem exists_eventually_flowOf_mem_level_and_tendsto [CompleteSpace E] {g : M → ℝ} {p : M}
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g p) (hgv : mvfderiv I g p (v a₀ p) ≠ 0) :
    ∃ σ : N × M → ℝ, (∀ᶠ z in 𝓝 (a₀, p), (σ z, z.2) ∈ flowDomain (v z.1) ∧
      g (flowOf (v z.1) (σ z) z.2) = g p) ∧
      Tendsto (fun z : N × M ↦ flowOf (v z.1) (σ z) z.2) (𝓝 (a₀, p)) (𝓝 p) := by
  set V := verticalField J v
  have hV : CMDiff 1 (fun z : N × M ↦ (⟨z, V z⟩ : TangentBundle (J.prod I) (N × M))) :=
    contMDiff_verticalField hv
  -- The time is the hitting time of the vertical field, and the point reached is read off from
  -- the time-`0` transition of the vertical field onto the section `{g ∘ Prod.snd = g p}`.
  have h0 : ((0 : ℝ), (a₀, p)) ∈ flowDomain V := mem_flowDomain_zero hV _
  have hflow0 : flowOf V 0 (a₀, p) = (a₀, p) := flowOf_zero V _
  have hG : ContMDiffAt (J.prod I) 𝓘(ℝ) 1 (g ∘ Prod.snd) (flowOf V 0 (a₀, p)) := by
    rw [hflow0]
    exact hg.comp _ contMDiffAt_snd
  have hGV : mvfderiv (J.prod I) (g ∘ Prod.snd) (flowOf V 0 (a₀, p))
      (V (flowOf V 0 (a₀, p))) ≠ 0 := by
    rwa [hflow0, mvfderiv_comp_snd_verticalField]
  refine ⟨flowHittingTime V (g ∘ Prod.snd) 0 (a₀, p), ?_, ?_⟩
  · filter_upwards [eventually_flowHittingTime hV h0 hG hGV] with ⟨a, x⟩ ⟨hdom, hlev⟩
    rw [mem_flowDomain_verticalField_iff] at hdom
    rw [hflow0, comp_apply, comp_apply, flowOf_verticalField (hv.apply_param a)] at hlev
    exact ⟨hdom, hlev⟩
  · have h := (continuousAt_flowTransition hV h0 hG hGV).tendsto
    rw [flowTransition_self, hflow0] at h
    refine (continuous_snd.tendsto _).comp h |>.congr fun ⟨a, x⟩ ↦ ?_
    rw [comp_apply, flowTransition_apply, flowOf_verticalField (hv.apply_param a)]

variable [FiniteDimensional ℝ E]

/-- **Closed orbits near a nondegenerate closed orbit are nondegenerate.** Let `v` be a jointly
`C¹` family of vector fields, and let `p` return to itself at time `T₀` under the flow of `v a₀`.
Suppose that `g` is `C¹` at `p` with `dg_p (v a₀ p) ≠ 0`, and that `1` is not an eigenvalue of the
linearized return map of the section `{g = g p}`. Then for every `(a, t, x)` close to
`(a₀, T₀, p)` such that `x` returns to itself at time `t` under the flow of `v a`, the same
function `g` cuts out a section through `x` transverse to `v a`, and `1` is not an eigenvalue of
its linearized return map. -/
theorem eventually_not_hasEigenvalue_returnDerivative_of_flowOf_eq {g : M → ℝ} {T₀ : ℝ} {p : M}
    (hP : (T₀, p) ∈ flowDomain (v a₀)) (hp : flowOf (v a₀) T₀ p = p)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g p) (hgv : mvfderiv I g p (v a₀ p) ≠ 0)
    (hnd : ¬(returnDerivative (v a₀) g T₀ p).HasEigenvalue 1) :
    ∀ᶠ y in 𝓝 (a₀, T₀, p), flowOf (v y.1) y.2.1 y.2.2 = y.2.2 →
      ContMDiffAt I 𝓘(ℝ) 1 g y.2.2 ∧ mvfderiv I g y.2.2 (v y.1 y.2.2) ≠ 0 ∧
        ¬(returnDerivative (v y.1) g y.2.1 y.2.2).HasEigenvalue 1 := by
  obtain ⟨τ, c, -, -, -, -, horbit, huniq⟩ :=
    exists_contMDiffAt_closedOrbit_continuation (n := 1) le_rfl hv hP hp hg hgv hnd
  obtain ⟨σ, hlev, hπ⟩ := exists_eventually_flowOf_mem_level_and_tendsto hv hg hgv
  -- Pull every local statement back to `𝓝 (a₀, T₀, p)`, along the map flowing `x` into the
  -- section through `p`.
  have hpair : Tendsto (fun y : N × ℝ × M ↦ (y.1, y.2.2)) (𝓝 (a₀, T₀, p)) (𝓝 (a₀, p)) :=
    (continuous_fst.prodMk continuous_snd.snd).tendsto _
  have hproj : Tendsto (fun y : N × ℝ × M ↦ (y.1, y.2.1, flowOf (v y.1) (σ (y.1, y.2.2)) y.2.2))
      (𝓝 (a₀, T₀, p)) (𝓝 (a₀, T₀, p)) :=
    (continuous_fst.tendsto _).prodMk_nhds
      ((continuous_snd.fst.tendsto _).prodMk_nhds (hπ.comp hpair))
  -- Near `(a₀, p)`, `g` is still `C¹` and transverse to the fields of the family.
  have hgnear :=
    eventually_contMDiffAt_and_mvfderiv_apply_ne_zero hv.continuous.continuousAt hg hgv
  filter_upwards [hpair.eventually hlev, hproj.eventually huniq,
    (continuous_fst.tendsto _).eventually horbit,
    eventually_mem_flowDomain_param hv hP, hpair.eventually hgnear,
    (hpair.comp hproj).eventually hgnear]
    with ⟨a, t, x⟩ ⟨hσdom, hσg⟩ hu ⟨_, _, _, _, hndc⟩ htx ⟨hgx, hgvx⟩ ⟨hgx', hgvx'⟩ hper
  dsimp only [comp_apply] at hσdom hσg hu hndc hgx hgvx hgx' hgvx' hper ⊢
  -- The point `x' = flowOf (v a) (σ (a, x)) x` lies on the section through `p` and returns to
  -- itself at time `t`, so it is the continued orbit `c a`, with return time `τ a = t`.
  set x' := flowOf (v a) (σ (a, x)) x
  obtain ⟨-, hper'⟩ := flowOf_flowOf_of_flowOf_eq (hv.apply_param a) hσdom htx hper
  obtain ⟨ht, hx'⟩ := hu.1 ⟨hper', hσg⟩
  rw [← ht, ← hx'] at hndc
  refine ⟨hgx, hgvx, ?_⟩
  rwa [hasEigenvalue_returnDerivative_iff (hv.apply_param a) hσdom rfl htx hper hgx hgvx hgx' hgvx']

variable {S : Set (ℝ × M)}

/-- **Nondegeneracy of the closed orbits in a compact window is an open condition.** Let `v` be a
jointly `C¹` family of vector fields and `S` a compact set of pairs `(t, x)` in the flow domain of
`v a₀` such that, whenever `x` returns to itself at time `t` under the flow of `v a₀` with
`(t, x) ∈ S`, the closed orbit through `x` is nondegenerate at return time `t` for some transverse
section. Then for every parameter `a` near `a₀` the set `S` lies in the flow domain of `v a`, and
every closed orbit of `v a` through a point `x` with return time `t`, with `(t, x) ∈ S`, is
nondegenerate at return time `t` for some transverse section. -/
theorem eventually_subset_flowDomain_and_forall_not_hasEigenvalue_returnDerivative
    (hS : IsCompact S) (hSD : S ⊆ flowDomain (v a₀))
    (hnd : ∀ x ∈ S, flowOf (v a₀) x.1 x.2 = x.2 → ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g x.2 ∧
      mvfderiv I g x.2 (v a₀ x.2) ≠ 0 ∧ ¬(returnDerivative (v a₀) g x.1 x.2).HasEigenvalue 1) :
    ∀ᶠ a in 𝓝 a₀, S ⊆ flowDomain (v a) ∧ ∀ x ∈ S, flowOf (v a) x.1 x.2 = x.2 →
      ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g x.2 ∧ mvfderiv I g x.2 (v a x.2) ≠ 0 ∧
        ¬(returnDerivative (v a) g x.1 x.2).HasEigenvalue 1 := by
  suffices h : ∀ y ∈ S, ∀ᶠ z : N × (ℝ × M) in 𝓝 (a₀, y), z.2 ∈ flowDomain (v z.1) ∧
      (flowOf (v z.1) z.2.1 z.2.2 = z.2.2 → ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g z.2.2 ∧
        mvfderiv I g z.2.2 (v z.1 z.2.2) ≠ 0 ∧
          ¬(returnDerivative (v z.1) g z.2.1 z.2.2).HasEigenvalue 1) by
    filter_upwards [hS.eventually_forall_of_forall_eventually (P := fun a y ↦
      y ∈ flowDomain (v a) ∧ (flowOf (v a) y.1 y.2 = y.2 → ∃ g : M → ℝ,
        ContMDiffAt I 𝓘(ℝ) 1 g y.2 ∧ mvfderiv I g y.2 (v a y.2) ≠ 0 ∧
          ¬(returnDerivative (v a) g y.1 y.2).HasEigenvalue 1)) h] with a ha
    exact ⟨fun y hy ↦ (ha y hy).1, fun y hy ↦ (ha y hy).2⟩
  rintro ⟨t, x⟩ hy
  have hdom := eventually_mem_flowDomain_param hv (hSD hy)
  by_cases hper : flowOf (v a₀) t x = x
  · -- A closed orbit of `v a₀`: the nearby closed orbits are nondegenerate.
    obtain ⟨g, hg, hgv, hndg⟩ := hnd (t, x) hy hper
    filter_upwards [hdom,
      eventually_not_hasEigenvalue_returnDerivative_of_flowOf_eq hv (hSD hy) hper hg hgv hndg]
      with z hz hzg
    exact ⟨hz, fun hzper ↦ ⟨g, hzg hzper⟩⟩
  · -- Not a closed orbit of `v a₀`: by continuity of the flow, nor of the nearby fields.
    have hcont : ContinuousAt (fun z : N × (ℝ × M) ↦ (flowOf (v z.1) z.2.1 z.2.2, z.2.2))
        (a₀, (t, x)) :=
      (contMDiffAt_flowOf_param le_rfl hv (hSD hy)).continuousAt.prodMk
        continuous_snd.snd.continuousAt
    filter_upwards [hdom, hcont.eventually ((isClosed_diagonal (X := M)).isOpen_compl.mem_nhds
      (mt mem_diagonal_iff.1 hper))] with z hz hzper
    exact ⟨hz, fun h ↦ absurd h hzper⟩

/-- **The parameters with nondegenerate closed orbits in a compact window form an open set.** For
a jointly `C¹` family of vector fields and a compact set `S` of pairs `(t, x)`, the parameters `a`
such that `S` lies in the flow domain of `v a` and every closed orbit of `v a` through a point `x`
with return time `t`, with `(t, x) ∈ S`, is nondegenerate at return time `t` for some transverse
section, form an open set. -/
theorem isOpen_setOf_subset_flowDomain_and_forall_not_hasEigenvalue_returnDerivative
    (hS : IsCompact S) :
    IsOpen {a | S ⊆ flowDomain (v a) ∧ ∀ x ∈ S, flowOf (v a) x.1 x.2 = x.2 →
      ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g x.2 ∧ mvfderiv I g x.2 (v a x.2) ≠ 0 ∧
        ¬(returnDerivative (v a) g x.1 x.2).HasEigenvalue 1} :=
  isOpen_iff_mem_nhds.2 fun _ ha ↦
    eventually_subset_flowDomain_and_forall_not_hasEigenvalue_returnDerivative hv hS ha.1 ha.2

end TauCeti

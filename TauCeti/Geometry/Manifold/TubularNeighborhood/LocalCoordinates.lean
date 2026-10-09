/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RangeProjection
public import TauCeti.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth local normal coordinates

For a map `g : E → V` into a finite-dimensional real inner product space, fix the normal
space at `u₀`. The map `normalParametrization g u₀` sends `(u, w)` to `g u` plus the
orthogonal projection of `w` onto the normal space at `u`. For a `C^(n+1)` immersion this
map is `C^n`, and near `(u₀, 0)` it is a partial diffeomorphism with a `C^n` inverse.
These are the local coordinates of the addition map on the normal bundle, used to upgrade
a topological tubular neighbourhood to a smooth one. No compactness or global injectivity
of the immersion is required.

The derivative at the zero section is `(du, dw) ↦ Dg du + dw`. Mathlib's product
decomposition for complementary subspaces identifies it as an isomorphism, and the inverse
function theorem supplies regularity on the whole inverse chart.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  the normal-bundle addition map and proof of Theorem 6.24.
-/

public section

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section Complete

/-- The normal-bundle addition map in projected coordinates from the normal space at `u₀`. -/
def normalParametrization (g : E → V) (u₀ : E) : E × (fderiv ℝ g u₀).rangeᗮ → V :=
  fun p => g p.1 + (fderiv ℝ g p.1).rangeᗮ.starProjection p.2

/-- The parametrization adds the projected reference normal vector to the core map. -/
@[simp] theorem normalParametrization_apply (g : E → V) (u₀ : E)
    (p : E × (fderiv ℝ g u₀).rangeᗮ) :
    normalParametrization g u₀ p = g p.1 + (fderiv ℝ g p.1).rangeᗮ.starProjection p.2 :=
  (rfl)

variable [CompleteSpace V]

/-- Normal parametrizations lose one derivative, just as the normal projection does.
Only injectivity of the differential at the base point of `p` is needed. -/
theorem contDiffAt_normalParametrization {g : E → V} (u₀ : E) {n : WithTop ℕ∞}
    {p : E × (fderiv ℝ g u₀).rangeᗮ} (hg : ContDiffAt ℝ (n + 1) g p.1)
    (hinj : Injective (fderiv ℝ g p.1)) :
    ContDiffAt ℝ n (normalParametrization g u₀) p := by
  have hQ := hg.fderiv_right_succ.starProjection_orthogonal_range hinj
  exact ((hg.of_le (le_add_of_nonneg_right (by simp))).comp p contDiffAt_fst).add
    ((hQ.comp p contDiffAt_fst).clm_apply
      ((fderiv ℝ g u₀).rangeᗮ.subtypeL.contDiff.contDiffAt.comp p contDiffAt_snd))

/-- At the zero section the derivative adds a tangent vector and a normal vector.
The derivative of the moving projection contributes zero there. -/
theorem hasFDerivAt_normalParametrization {g : E → V} {u₀ : E}
    (hg : ContDiffAt ℝ 2 g u₀) (hinj : Injective (fderiv ℝ g u₀)) :
    HasFDerivAt (normalParametrization g u₀)
      ((fderiv ℝ g u₀).coprod (fderiv ℝ g u₀).rangeᗮ.subtypeL) (u₀, 0) := by
  let W := (fderiv ℝ g u₀).rangeᗮ
  let Q : E → V →L[ℝ] V := fun u => (fderiv ℝ g u).rangeᗮ.starProjection
  have hQ : ContDiffAt ℝ 1 Q u₀ :=
    (hg.fderiv_right (m := 1) (by norm_num)).starProjection_orthogonal_range hinj
  have hc : HasFDerivAt (fun p : E × W => Q p.1)
      ((fderiv ℝ Q u₀).comp (ContinuousLinearMap.fst ℝ E W)) (u₀, 0) :=
    HasFDerivAt.comp (g := Q) (f := Prod.fst) (u₀, (0 : W))
      (hQ.differentiableAt one_ne_zero).hasFDerivAt hasFDerivAt_fst
  have hw : HasFDerivAt (fun p : E × W => (p.2 : V))
      (W.subtypeL.comp (ContinuousLinearMap.snd ℝ E W)) (u₀, 0) :=
    W.subtypeL.hasFDerivAt.comp (u₀, (0 : W)) hasFDerivAt_snd
  have hcore : HasFDerivAt (fun p : E × W => g p.1)
      ((fderiv ℝ g u₀).comp (ContinuousLinearMap.fst ℝ E W)) (u₀, 0) :=
    (hg.differentiableAt (by norm_num)).hasFDerivAt.comp (u₀, (0 : W)) hasFDerivAt_fst
  apply (hcore.add (hc.clm_apply hw)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  simp [W, Q, ContinuousLinearMap.coprod_apply,
    Submodule.starProjection_eq_self_iff.mpr p.2.property]

end Complete

variable [FiniteDimensional ℝ V]

/-- A `C^(n+1)` map on an open set with injective differential at `u₀` admits `C^n`
local normal coordinates there. The source lies over the given open set and consists
of immersion points. Both the parametrization and its inverse are smooth on their
entire domains; `n = ∞` and `n = ω` are allowed. -/
theorem exists_partialDiffeomorph_normalParametrization {g : E → V} {s : Set E} {u₀ : E}
    {n : WithTop ℕ∞} (hg : ContDiffOn ℝ (n + 1) g s) (hs : IsOpen s) (hu₀ : u₀ ∈ s)
    (hinj : Injective (fderiv ℝ g u₀)) (hn : 1 ≤ n) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E × (fderiv ℝ g u₀).rangeᗮ) 𝓘(ℝ, V)
        (E × (fderiv ℝ g u₀).rangeᗮ) V n,
      (Φ : E × (fderiv ℝ g u₀).rangeᗮ → V) = normalParametrization g u₀ ∧
      (u₀, 0) ∈ Φ.source ∧
      ∀ p ∈ Φ.source, p.1 ∈ s ∧ Injective (fderiv ℝ g p.1) := by
  let U := s ∩ {u | Injective (fderiv ℝ g u)}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro u hu
    exact inter_mem (hs.mem_nhds hu.1)
      ((hg.contDiffAt (hs.mem_nhds hu.1)).fderiv_right_succ.continuousAt.preimage_mem_nhds
        (ContinuousLinearMap.isOpen_injective.mem_nhds hu.2))
  have hreg : ContDiffOn ℝ n (normalParametrization g u₀) (U ×ˢ univ) := by
    intro p hp
    exact (contDiffAt_normalParametrization u₀
      (hg.contDiffAt (hs.mem_nhds hp.1.1)) hp.1.2).contDiffWithinAt
  let A := fderiv ℝ g u₀
  let W := A.rangeᗮ
  let e : (E × W) ≃L[ℝ] V :=
    (((LinearEquiv.ofInjective (A : E →ₗ[ℝ] V) hinj).prodCongr
      (LinearEquiv.refl ℝ W)).trans
        (A.range.prodEquivOfIsCompl W (Submodule.isCompl_orthogonal _))).toContinuousLinearEquiv
  have he : (e : E × W →L[ℝ] V) = A.coprod W.subtypeL := by
    apply ContinuousLinearMap.ext
    intro p
    simp [e, ContinuousLinearMap.coprod_apply, Submodule.coe_prodEquivOfIsCompl']
  have hderiv := hasFDerivAt_normalParametrization
    ((hg.contDiffAt (hs.mem_nhds hu₀)).of_le (by calc
      (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
      _ ≤ n + 1 := add_le_add hn le_rfl)) hinj
  have hederiv : (e : E × W →L[ℝ] V) = fderiv ℝ (normalParametrization g u₀) (u₀, 0) :=
    he.trans hderiv.fderiv.symm
  obtain ⟨Θ, hΘ, hcenter, hsource, hinverse⟩ := ContDiffOn.exists_openPartialHomeomorph hreg
    (a := (u₀, (0 : W))) (hU.prod isOpen_univ) ⟨⟨hu₀, hinj⟩, mem_univ _⟩ hn hederiv
  have hforward : ContDiffOn ℝ n Θ Θ.source := hΘ.symm ▸ hreg.mono hsource
  let Φ := PartialDiffeomorph.ofOpenPartialHomeomorph Θ hforward hinverse
  have hΦ := PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv Θ hforward hinverse
  have hΦsource : Φ.source = Θ.source := congrArg PartialEquiv.source hΦ
  refine ⟨Φ, ?_, hΦsource.symm ▸ hcenter, ?_⟩
  · exact (congrArg (fun e : PartialEquiv (E × W) V => (e : E × W → V)) hΦ).trans
      (Θ.coe_toPartialEquiv.trans hΘ)
  · intro p hp
    exact (hsource (hΦsource ▸ hp)).1

/-- The inverse normal coordinates give a smooth local retraction in parameter space.
Near `g u₀`, every point is a normal displacement from `g (r y)`, and `r` recovers the
parameter on a neighbourhood of `u₀`. This is a local statement about one immersed patch;
it does not assert a global retraction for a self-intersecting immersion. -/
theorem exists_contDiffOn_normalRetraction {g : E → V} {s : Set E} {u₀ : E}
    {n : WithTop ℕ∞} (hg : ContDiffOn ℝ (n + 1) g s) (hs : IsOpen s) (hu₀ : u₀ ∈ s)
    (hinj : Injective (fderiv ℝ g u₀)) (hn : 1 ≤ n) :
    ∃ U : Set E, IsOpen U ∧ u₀ ∈ U ∧ U ⊆ s ∧
      ∃ t : Set V, IsOpen t ∧ g u₀ ∈ t ∧ g '' U ⊆ t ∧
        ∃ r : V → E, ContDiffOn ℝ n r t ∧
          (∀ u ∈ U, r (g u) = u) ∧
          ∀ y ∈ t, r y ∈ U ∧ y - g (r y) ∈ (fderiv ℝ g (r y)).rangeᗮ := by
  obtain ⟨Φ, hΦ, hcenter, hsource⟩ :=
    exists_partialDiffeomorph_normalParametrization hg hs hu₀ hinj hn
  let U := (fun u : E => (u, (0 : (fderiv ℝ g u₀).rangeᗮ))) ⁻¹' Φ.source
  let r : V → E := fun y => (Φ.toPartialEquiv.symm y).1
  have hzero (u : E) : Φ (u, 0) = g u :=
    by simpa using congrFun hΦ (u, 0)
  have hU : IsOpen U := Φ.open_source.preimage (continuous_id.prodMk continuous_const)
  have hleft (u : E) (hu : u ∈ U) : r (g u) = u := by
    have h : Φ.toPartialEquiv.symm (g u) = (u, 0) := by
      rw [← hzero u]
      exact Φ.toPartialEquiv.left_inv hu
    exact congrArg Prod.fst h
  have hr : ContDiffOn ℝ n r Φ.target :=
    (contMDiffOn_iff_contDiffOn.mp Φ.symm.contMDiffOn).fst
  let t := Φ.target ∩ r ⁻¹' U
  have ht : IsOpen t := hr.continuousOn.isOpen_inter_preimage Φ.open_target hU
  have hUt : g '' U ⊆ t := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hzero u]
      exact Φ.toPartialEquiv.map_source hu
    · simpa only [mem_preimage, hleft u hu] using hu
  refine ⟨U, hU, hcenter, fun u hu => (hsource (u, 0) hu).1,
    t, ht, hUt ⟨u₀, hcenter, rfl⟩, hUt, r, hr.mono inter_subset_left, hleft, ?_⟩
  intro y hy
  refine ⟨hy.2, ?_⟩
  have hright : normalParametrization g u₀ (Φ.toPartialEquiv.symm y) = y :=
    (congrFun hΦ _).symm.trans (Φ.toPartialEquiv.right_inv hy.1)
  rw [normalParametrization_apply] at hright
  have hnormal := Submodule.starProjection_apply_mem
    (fderiv ℝ g (r y)).rangeᗮ (Φ.toPartialEquiv.symm y).2
  exact (eq_sub_of_add_eq' hright).symm ▸ hnormal

end TauCeti

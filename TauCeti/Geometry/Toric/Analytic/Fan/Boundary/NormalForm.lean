/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Manifold

/-!
# The normal-crossings form of the toric boundary

The boundary of the analytic realization of a regular fan is the union of the ray-indexed
components `TauCeti.Toric.Fan.analyticBoundaryComponent`. In the affine chart of a cone `σ`, read
in the regular coordinates of an integral basis extending the primitive ray generators of `σ`,
these components are coordinate hyperplanes: a point of the chart lies in the component of a ray
`ρ` exactly when `ρ` is a ray of `σ` and the coordinate indexed by `ρ` vanishes. Components of rays
outside `σ` miss the chart.

Taking for `σ` the cone whose torus orbit contains a given point, and identifying the regular
coordinates linearly with `ℂ ^ n`, this gives the simple-normal-crossings normal form of the
boundary: near every point there is a holomorphic chart of the realization, defined on the whole
affine chart of `σ` and biholomorphic onto its image, together with an injection from the
components through the point to the coordinate indices, such that a point of the chart lies in a
component exactly when that component passes through the given point and the corresponding
coordinate vanishes. In particular every boundary component is a closed complex hypersurface,
locally a coordinate hyperplane.

## Main declarations

* `TauCeti.Toric.Fan.analyticAffineChartι_mem_analyticBoundaryComponent_iff`: in the regular
  coordinates of an affine chart, a boundary component is the vanishing locus of the coordinate
  of its ray.
* `TauCeti.Toric.Fan.exists_partialDiffeomorph_analyticBoundaryComponent_normalForm`: the toric
  boundary has the holomorphic coordinate-hyperplane normal form near every point.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§2.1 and 3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.2 and §4.1.
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)

/-- In the regular coordinates of the affine chart of a cone `σ`, a point lies in the boundary
component of a ray `ρ` exactly when `ρ` is a ray of `σ` and the coordinate indexed by `ρ`
vanishes. -/
theorem analyticAffineChartι_mem_analyticBoundaryComponent_iff (σ : Φ.cones) {ι : Type*}
    {b : Module.Basis (ToricRay σ.1 ⊕ ι) ℤ N}
    (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ))) (ρ : Φ.Ray)
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) :
    Φ.analyticAffineChartι hΦ σ x ∈ Φ.analyticBoundaryComponent hΦ ρ ↔
      ∃ h : ρ.toCone ≤ σ, (coneChartEquiv Φ.lattice
        ((isRegular_iff.mp hΦ) σ.1 σ.2).toIsToricCone hb x).1 (ρ.toToricRay Φ σ h) = 0 := by
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  by_cases h : ρ.toCone ≤ σ
  · have hF : Φ.orbitFace h =
        (ρ.toToricRay Φ σ h).1 :=
      PointedCone.Face.ext fun v ↦ SetLike.ext_iff.mp
        ((Φ.coe_orbitFace h).trans (Ray.toPointedCone_toToricRay Φ ρ σ h).symm) v
    rw [exists_prop_of_true h]
    refine (Set.ext_iff.1 (Φ.preimage_analyticAffineChartι_analyticBoundaryComponent hΦ h) x).trans
      ?_
    rw [hF]
    exact Set.ext_iff.1 (closure_affineConeOrbit_toricRay_eq_setOf_coneChartEquiv_fst_eq_zero
      Φ.lattice hσ hb (ρ.toToricRay Φ σ h) (analyticChartGenerators Φ σ).2) x
  · refine iff_of_false (fun hx ↦ ?_) fun ⟨h', _⟩ ↦ h h'
    exact Set.notMem_empty x <| (Set.ext_iff.1
      (Φ.preimage_analyticAffineChartι_analyticBoundaryComponent_of_not_le hΦ h) x).1 hx

/-- The toric boundary has the holomorphic coordinate-hyperplane normal form near every point `x`
of the realization. There are a biholomorphism `e` from an open neighbourhood of `x` onto an open
subset of `ℂ ^ n`, for `n` the rank of the lattice, and an injection `j` from the set `s` of
boundary components through `x` to the coordinate indices, such that a point of the neighbourhood
lies in a boundary component exactly when that component passes through `x` and the coordinate
it is assigned vanishes. -/
theorem exists_partialDiffeomorph_analyticBoundaryComponent_normalForm
    (x : Φ.analyticRealization hΦ) (n : ℕ∞ω) :
    letI := Φ.analyticChartedSpace hΦ
    ∃ (s : Set Φ.Ray) (j : s ↪ Fin (Module.finrank ℤ N))
      (e : PartialDiffeomorph 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ)
        𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) (Φ.analyticRealization hΦ)
        (Fin (Module.finrank ℤ N) → ℂ) n),
      x ∈ e.source ∧ (∀ ρ, x ∈ Φ.analyticBoundaryComponent hΦ ρ ↔ ρ ∈ s) ∧
        ∀ y ∈ e.source, ∀ ρ,
          y ∈ Φ.analyticBoundaryComponent hΦ ρ ↔ ∃ hρ : ρ ∈ s, e y (j ⟨ρ, hρ⟩) = 0 := by
  let _ := Φ.analyticChartedSpace hΦ
  -- Step 1: choose regular coordinates on the affine chart of the cone `σ` whose orbit contains
  -- `x`, and identify them linearly with `ℂ ^ n`.
  obtain ⟨σ, hxσ⟩ := Φ.exists_mem_analyticConeOrbit hΦ x
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  obtain ⟨l, B, hB⟩ := hσ.exists_basis_sum
  have : Finite (ToricRay σ.1) := ToricRay.finite_of_fg hσ.fg
  let κ := Finite.equivFin (ToricRay σ.1)
  have hk : Nat.card (ToricRay σ.1) + l = Module.finrank ℤ N := by
    rw [Module.finrank_eq_nat_card_basis B, Nat.card_sum, Nat.card_eq_fintype_card (α := Fin l),
      Fintype.card_fin]
  let eN : Fin (Nat.card (ToricRay σ.1)) ⊕ Fin l ≃ Fin (Module.finrank ℤ N) :=
    finSumFinEquiv.trans (finCongr hk)
  let L : ((Fin (Nat.card (ToricRay σ.1)) → ℂ) × (Fin l → ℂ)) ≃L[ℂ]
      (Fin (Module.finrank ℤ N) → ℂ) :=
    ((LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ).symm.trans
      (LinearEquiv.funCongrLeft ℂ ℂ eN.symm)).toContinuousLinearEquiv
  let g := (analyticChartGenerators Φ σ).2
  let _ := affinePointTopology g
  let _ := coneChartedSpace Φ.lattice hσ.toIsToricCone hB κ g
  have := isManifold_coneChartedSpace Φ.lattice hσ.toIsToricCone hB κ g n
  -- Step 2: `e` inverts the chart inclusion, then applies the regular chart and `L`.
  let P := Φ.analyticAffineChartPartialDiffeomorph hΦ σ hB κ g n
  let C := extChartPartialDiffeomorph 𝓘(ℂ, (Fin (Nat.card (ToricRay σ.1)) → ℂ) × (Fin l → ℂ)) n
    (P.symm x)
  let D : PartialDiffeomorph _ _ _ _ n := PartialDiffeomorph.ofOpenPartialHomeomorph
    L.toHomeomorph.toOpenPartialHomeomorph (by simpa using L.contDiff.contDiffOn)
    (by simpa using L.symm.contDiff.contDiffOn)
  let e := P.symm.trans (C.trans D)
  -- On the affine chart, `e` is the ambient regular chart followed by `L`.
  have hP (x' : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) :
      P.symm (Φ.analyticAffineChartι hΦ σ x') = x' := by
    rw [← Φ.analyticAffineChartPartialDiffeomorph_apply hΦ σ hB κ g n x']
    exact P.toPartialEquiv.left_inv (by simp [P])
  have he (x' : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) :
      e (Φ.analyticAffineChartι hΦ σ x') =
        L (coneChartAmbient Φ.lattice hσ.toIsToricCone hB κ x') := by
    conv_rhs => rw [← hP x']
    simp [e, C, D, coe_coneChartedSpace_chartAt]
  have hsource : ∀ y ∈ e.source, ∃ x' : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1),
      Φ.analyticAffineChartι hΦ σ x' = y := by
    intro y hy
    have hy' : y ∈ P.target := hy.1
    rwa [Φ.analyticAffineChartPartialDiffeomorph_target hΦ σ hB κ g n] at hy'
  have hxe : x ∈ e.source := by
    obtain ⟨x', -, rfl⟩ := (Φ.analyticConeOrbit_def hΦ σ).subset hxσ
    simp [e, C, D, P, BoundarylessManifold.isInteriorPoint, coe_coneChartedSpace_chartAt]
  -- Step 3: the components through `x` are those of the rays of `σ`, and the coordinate of a ray
  -- vanishes exactly on its component.
  refine ⟨{ρ | ρ.toCone ≤ σ}, (Φ.rayEquiv σ).toEmbedding.trans
    (κ.toEmbedding.trans (Function.Embedding.inl.trans eN.toEmbedding)), e, hxe,
    fun ρ ↦ Φ.mem_analyticBoundaryComponent_iff hΦ hxσ, ?_⟩
  rintro y hy ρ
  obtain ⟨x', rfl⟩ := hsource y hy
  rw [analyticAffineChartι_mem_analyticBoundaryComponent_iff Φ hΦ σ hB ρ x', he]
  simp [L, eN, LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow]

end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.LeastCone
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Torus

/-!
# Orbit and affine-chart preimages under toric maps

The analytic map of a morphism of regular fans sends the distinguished point of a source cone
to that of its least target cone. Equivariance then sends the whole source orbit into the orbit
of that cone. It need not map onto the target orbit: the induced torus homomorphism need not
be surjective.

The orbit partition gives exact preimage formulas. The preimage of a target orbit is the union
of the source orbits whose least target cone is that cone; the preimage of an affine chart is
the union of the source orbits whose cones map into its cone. These formulas include empty fans
and provide the cone-by-cone description needed for restrictions and properness.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.1 and §2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.3.
-/

public section

open CategoryTheory Multiplicative Set

namespace TauCeti.Toric.FanHom

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  (f : FanHom Φ Ψ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

/-- Mapping the distinguished point of a source cone into any containing target chart gives
that of the least target cone, viewed as a face of the chosen target cone. -/
theorem analyticChartMap_distinguishedPoint {σ : Φ.cones} {τ : Ψ.cones}
    (h : MapsTo f.realMap (σ.1 : Set V) (τ.1 : Set V')) :
    f.analyticChartMap hΦ hΨ h (distinguishedPoint Φ.lattice (⊤ : σ.1.Face)) =
      distinguishedPoint Ψ.lattice
        (⟨f.leastCone σ.2, Ψ.isFaceOf_of_le τ.2 (f.leastCone_mem σ.2)
          (f.leastCone_le σ.2 τ.2 (by rintro _ ⟨x, hx, rfl⟩; exact h hx))⟩ : τ.1.Face) := by
  classical
  -- The bundled chart carrier is the affine complex-point carrier; full transparency
  -- lets the chart formula apply to its distinguished point.
  erw [analyticChartMap_apply]
  refine AffineSemigroupComplexPoint.ext fun m ↦ ?_
  rw [AffineSemigroupComplexPoint.comap_apply_single,
    distinguishedPoint_apply_single, distinguishedPoint_apply_single]
  have hchar : (dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap
      f.map_lattice h m : N →+ ℤ) = (m : N' →+ ℤ).comp f.latticeMap := by
    ext n
    simp
  have hvanish := f.realCharacter_eq_zero_on_leastCone_iff σ.2
    (dualSemigroup_anti Ψ.lattice
      (f.leastCone_le σ.2 τ.2 (by rintro _ ⟨x, hx, rfl⟩; exact h hx)) m.2)
  simp only [hchar]
  exact if_congr hvanish.symm rfl rfl

/-- Analytic toric maps send distinguished points to the distinguished points of the least
target cones. -/
@[simp]
theorem analyticMap_analyticDistinguishedPoint (σ : Φ.cones) :
    f.analyticMap hΦ hΨ (Φ.analyticDistinguishedPoint hΦ σ) =
      Ψ.analyticDistinguishedPoint hΨ ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩ := by
  rw [Fan.analyticDistinguishedPoint_def]
  -- As above, the distinguished point uses the underlying affine-point carrier.
  erw [f.analyticMap_analyticAffineChartι_of_mapsTo hΦ hΨ
      (υ := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩) (f.mapsTo_leastCone σ.2),
    f.analyticChartMap_distinguishedPoint]
  exact Ψ.analyticAffineChartι_distinguishedPoint hΨ le_rfl

/-- The orbit of a source cone maps into the orbit of its least target cone. No surjectivity of
the lattice map or its torus homomorphism is required. -/
theorem mapsTo_analyticConeOrbit (σ : Φ.cones) :
    MapsTo (f.analyticMap hΦ hΨ) (Φ.analyticConeOrbit hΦ σ)
      (Ψ.analyticConeOrbit hΨ ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩) := by
  intro x hx
  rw [Φ.analyticConeOrbit_eq_orbit hΦ] at hx
  obtain ⟨t, rfl⟩ := hx
  rw [f.analyticMap_smul, f.analyticMap_analyticDistinguishedPoint,
    Ψ.analyticConeOrbit_eq_orbit hΨ]
  exact MulAction.mem_orbit _ _

/-- On the orbit of `σ`, membership of the image in the orbit of `τ` is equivalent to `τ` being
the least target cone of `σ`. -/
theorem analyticMap_mem_analyticConeOrbit_iff {σ : Φ.cones} {τ : Ψ.cones}
    {x : Φ.analyticRealization hΦ} (hx : x ∈ Φ.analyticConeOrbit hΦ σ) :
    f.analyticMap hΦ hΨ x ∈ Ψ.analyticConeOrbit hΨ τ ↔ f.leastCone σ.2 = τ.1 := by
  have hm := f.mapsTo_analyticConeOrbit hΦ hΨ σ hx
  exact ⟨fun h ↦ congrArg Subtype.val (Ψ.eq_of_mem_analyticConeOrbit hΨ hm h),
    fun h ↦ (Subtype.ext h : ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩ = τ) ▸ hm⟩

/-- The preimage of a target orbit is exactly the union of the source orbits with that least
target cone. -/
theorem preimage_analyticMap_analyticConeOrbit (τ : Ψ.cones) :
    f.analyticMap hΦ hΨ ⁻¹' Ψ.analyticConeOrbit hΨ τ =
      ⋃ σ : Φ.cones, ⋃ (_ : f.leastCone σ.2 = τ.1), Φ.analyticConeOrbit hΦ σ := by
  ext x
  obtain ⟨σ, hx⟩ := Φ.exists_mem_analyticConeOrbit hΦ x
  rw [mem_preimage, f.analyticMap_mem_analyticConeOrbit_iff hΦ hΨ hx, mem_iUnion₂]
  exact ⟨fun h ↦ ⟨σ, h, hx⟩, fun ⟨σ', h, hx'⟩ ↦
    Φ.eq_of_mem_analyticConeOrbit hΦ hx' hx ▸ h⟩

/-- On a source orbit, membership of the image in a target affine chart is precisely containment
of the least target cone in the chart's cone. -/
theorem analyticMap_mem_range_analyticAffineChartι_iff {σ : Φ.cones} {τ : Ψ.cones}
    {x : Φ.analyticRealization hΦ} (hx : x ∈ Φ.analyticConeOrbit hΦ σ) :
    f.analyticMap hΦ hΨ x ∈ range (Ψ.analyticAffineChartι hΨ τ) ↔ f.leastCone σ.2 ≤ τ.1 :=
  Ψ.mem_range_analyticAffineChartι_iff hΨ (f.mapsTo_analyticConeOrbit hΦ hΨ σ hx)

/-- The preimage of an affine target chart is the union of the source orbits whose cones map
into its cone. -/
theorem preimage_analyticMap_range_analyticAffineChartι (τ : Ψ.cones) :
    f.analyticMap hΦ hΨ ⁻¹' range (Ψ.analyticAffineChartι hΨ τ) =
      ⋃ σ : Φ.cones, ⋃ (_ : σ.1.map f.realMap ≤ τ.1), Φ.analyticConeOrbit hΦ σ := by
  ext x
  obtain ⟨σ, hx⟩ := Φ.exists_mem_analyticConeOrbit hΦ x
  rw [mem_preimage, f.analyticMap_mem_range_analyticAffineChartι_iff hΦ hΨ hx, mem_iUnion₂]
  constructor
  · intro h
    exact ⟨σ, (f.map_le_leastCone σ.2).trans h, hx⟩
  · rintro ⟨σ', h, hx'⟩
    have heq := Φ.eq_of_mem_analyticConeOrbit hΦ hx' hx
    subst σ'
    exact f.leastCone_le σ.2 τ.2 h

end TauCeti.Toric.FanHom

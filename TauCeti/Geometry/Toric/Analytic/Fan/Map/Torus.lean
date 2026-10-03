/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.DenseTorus
public import TauCeti.Geometry.Toric.Analytic.Fan.Topology

/-!
# Toric maps on the dense complex torus

The analytic map of a fan morphism is equivariant for the complex-torus homomorphism induced by
its lattice map. On the canonical dense torus inclusion it agrees with that homomorphism.
Since analytic fan realizations are Hausdorff, this restriction determines the analytic map
uniquely among continuous maps. Thus the lattice map determines its extension to the fan
realization without reference to choices of affine coordinates.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.3.
-/

public section

open CategoryTheory Multiplicative

namespace TauCeti.Toric.FanHom

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  (f : FanHom Φ Ψ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

/-- The map between affine charts is equivariant for the torus homomorphism induced by the
lattice map of the fan morphism. -/
theorem analyticChartMap_smul {σ : Φ.cones} {τ : Ψ.cones}
    (h : Set.MapsTo f.realMap (σ.1 : Set V) (τ.1 : Set V'))
    (t : ComplexTorus N) (x : (Φ.analyticAffineChartDiagram).obj σ) :
    f.analyticChartMap h (t • x) =
      complexTorusMap f.latticeMap t • f.analyticChartMap h x := by
  rw [analyticChartMap_apply, analyticChartMap_apply]
  -- The bundled chart carriers and their actions are the affine complex-point carriers and
  -- actions; restate the goal there so the monomial evaluation API applies.
  change AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) at x
  change AffineSemigroupComplexPoint.comap
      (dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice h) (t • x) =
    complexTorusMap f.latticeMap t • AffineSemigroupComplexPoint.comap
      (dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice h) x
  rw [AffineSemigroupComplexPoint.ambient_smul_def,
    AffineSemigroupComplexPoint.comap_smul,
    AffineSemigroupComplexPoint.ambient_smul_def]
  congr 1
  ext m
  simp only [AddChar.compAddMonoidHom_apply, AddSubmonoid.coe_subtype,
    complexTorusMap_apply, characterEvaluation_apply]
  apply congrArg (fun m ↦ (t m : ℂ))
  ext n
  simp

/-- Analytic toric maps are equivariant for the lattice-induced homomorphism of complex tori. -/
@[simp]
theorem analyticMap_smul (t : ComplexTorus N) (x : Φ.analyticRealization hΦ) :
    f.analyticMap hΦ hΨ (t • x) = complexTorusMap f.latticeMap t • f.analyticMap hΦ hΨ x := by
  obtain ⟨σ, y, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ x
  simp only [Fan.smul_analyticAffineChartι, analyticMap_analyticAffineChartι,
    analyticChartMap_smul]

/-- On the canonical dense torus inclusion, the analytic toric map is the homomorphism of tori
induced by the underlying lattice map. The fan morphism supplies target nonemptiness from
source nonemptiness; any other target witness gives a definitionally equal inclusion. -/
@[simp]
theorem analyticMap_analyticTorusι (hΦ0 : Nonempty Φ.cones) (t : ComplexTorus N) :
    f.analyticMap hΦ hΨ (Φ.analyticTorusι hΦ hΦ0 t) =
      Ψ.analyticTorusι hΨ ⟨⟨f.leastCone hΦ0.some.2, f.leastCone_mem hΦ0.some.2⟩⟩
        (complexTorusMap f.latticeMap t) := by
  let σ := hΦ0.some
  let τ : Ψ.cones := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩
  rw [Φ.analyticTorusι_eq_analyticAffineChartι hΦ hΦ0 σ,
    Ψ.analyticTorusι_eq_analyticAffineChartι hΨ ⟨τ⟩ τ]
  -- The chart formula uses the bundled `TopCat` carrier, whereas the torus formula uses its
  -- underlying affine complex points. Full transparency identifies these carriers and actions.
  erw [f.analyticMap_analyticAffineChartι_of_mapsTo hΦ hΨ (υ := τ)
    (f.mapsTo_leastCone σ.2), f.analyticChartMap_smul]
  congr 2
  erw [analyticChartMap_apply, AffineSemigroupComplexPoint.comap_default]

/-- A continuous map is the analytic toric map exactly when it extends the lattice-induced map
of dense tori. Source nonemptiness is needed to define the canonical torus inclusions;
the fan morphism supplies target nonemptiness. Any other target witness gives the same
statement by definitional equality. -/
theorem eq_analyticMap_iff (hΦ0 : Nonempty Φ.cones)
    {g : Φ.analyticRealization hΦ ⟶ Ψ.analyticRealization hΨ} :
    g = f.analyticMap hΦ hΨ ↔ ∀ t, g (Φ.analyticTorusι hΦ hΦ0 t) =
      Ψ.analyticTorusι hΨ ⟨⟨f.leastCone hΦ0.some.2, f.leastCone_mem hΦ0.some.2⟩⟩
        (complexTorusMap f.latticeMap t) := by
  constructor
  · rintro rfl t
    exact f.analyticMap_analyticTorusι hΦ hΨ hΦ0 t
  · intro h
    apply Φ.analyticRealization_hom_ext_torus hΦ hΦ0
    intro t
    rw [h, f.analyticMap_analyticTorusι hΦ hΨ hΦ0]

end TauCeti.Toric.FanHom

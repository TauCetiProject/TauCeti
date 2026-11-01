/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import TauCeti.Analysis.Calculus.ContDiff.Pi
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Finite products of manifolds

Mathlib charts a finite product `∀ i, M i` of charted spaces by the products of charts of the
factors (`piChartedSpace`), modelled on `ModelWithCorners.pi I`. This file proves that these charts
form a `C^n` atlas when every factor is a `C^n` manifold, so that a finite product of `C^n`
manifolds is a `C^n` manifold (`TauCeti.instIsManifoldPi`). The transition maps of product
charts are the products of the transition maps of the factors, and a finite product of `C^n` maps
is `C^n` (`ContDiffOn.piMap`). The extended chart of the product at `x` is the product of the
extended charts of the factors at the coordinates of `x` (`TauCeti.extChartAt_pi`), and the
product of boundaryless models is boundaryless.

These are the finite-product analogues of Mathlib's `IsManifold.prod`, `contDiffGroupoid_prod` and
`ModelWithCorners.range_eq_univ_prod` for binary products. They make tori `∀ i, AddCircle (p i)`,
and more generally finite products of circles, lines and other manifolds, into manifolds.

## Main declarations

* `ModelWithCorners.coe_pi`, `ModelWithCorners.coe_pi_symm`, `ModelWithCorners.range_pi`: the
  product model acts coordinatewise, with range the product of the ranges.
* `TauCeti.contDiffGroupoid_pi`: a finite product of `C^n` open partial homeomorphisms of the
  model spaces is `C^n` for the product model.
* `TauCeti.instIsManifoldPi`: a finite product of `C^n` manifolds is a `C^n` manifold.
* `TauCeti.extChartAt_pi`: the extended charts of a finite product.
-/

public section

open Set

namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {H : ι → Type*} [∀ i, TopologicalSpace (H i)]

/-- The product model with corners acts coordinatewise. -/
@[simp, mfld_simps]
theorem coe_pi (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)) :
    ⇑(ModelWithCorners.pi I) = Pi.map fun i ↦ I i :=
  (rfl)

/-- The inverse of the product model with corners acts coordinatewise. -/
@[simp, mfld_simps]
theorem coe_pi_symm (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)) :
    ⇑(ModelWithCorners.pi I).symm = Pi.map fun i ↦ (I i).symm :=
  (rfl)

/-- The range of the product model with corners is the product of the ranges. -/
theorem range_pi (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)) :
    range (ModelWithCorners.pi I) = univ.pi fun i ↦ range (I i) := by
  rw [coe_pi, range_piMap]

/-- A finite product of boundaryless models with corners is boundaryless. -/
instance pi_boundaryless (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)) [∀ i, (I i).Boundaryless] :
    (ModelWithCorners.pi I).Boundaryless :=
  ⟨by rw [range_pi, ← pi_univ univ]; exact congrArg _ (funext fun i ↦ (I i).range_eq_univ)⟩

end ModelWithCorners

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {H : ι → Type*} [∀ i, TopologicalSpace (H i)] {I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)}
  {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
  {n : WithTop ℕ∞}

/-- A finite product of `C^n` open partial homeomorphisms of the model spaces is `C^n` for the
product model with corners. -/
theorem contDiffGroupoid_pi {e : ∀ i, OpenPartialHomeomorph (H i) (H i)}
    (he : ∀ i, e i ∈ contDiffGroupoid n (I i)) :
    OpenPartialHomeomorph.pi e ∈ contDiffGroupoid n (ModelWithCorners.pi I) := by
  -- Read in the product model, a product of open partial homeomorphisms is the product of the
  -- maps read in the factor models, on the product of their domains.
  have key : ∀ e : ∀ i, OpenPartialHomeomorph (H i) (H i),
      (∀ i, ContDiffOn 𝕜 n (I i ∘ e i ∘ (I i).symm) ((I i).symm ⁻¹' (e i).source ∩ range (I i))) →
      ContDiffOn 𝕜 n
        (ModelWithCorners.pi I ∘ OpenPartialHomeomorph.pi e ∘ (ModelWithCorners.pi I).symm)
        ((ModelWithCorners.pi I).symm ⁻¹' (OpenPartialHomeomorph.pi e).source ∩
          range (ModelWithCorners.pi I)) := by
    intro e he
    convert ContDiffOn.piMap he using 1
    · ext x
      simp
    · rw [ModelWithCorners.range_pi]
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_univ_pi]
      -- The source of `OpenPartialHomeomorph.pi e` is the product of the sources, as a set of
      -- `ModelPi H`, on which `Set.mem_univ_pi` does not fire.
      exact ⟨fun ⟨h₁, h₂⟩ i ↦ ⟨h₁ i trivial, h₂ i⟩, fun h ↦ ⟨fun i _ ↦ (h i).1, fun i ↦ (h i).2⟩⟩
  refine ⟨key e fun i ↦ (he i).1, ?_⟩
  rw [OpenPartialHomeomorph.pi_symm]
  exact key (fun i ↦ (e i).symm) fun i ↦ (he i).2

/-- A finite product of `C^n` manifolds is a `C^n` manifold, modelled on the product model with
corners. -/
instance instIsManifoldPi [∀ i, IsManifold (I i) n (M i)] :
    IsManifold (ModelWithCorners.pi I) n (∀ i, M i) where
  compatible := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    rw [OpenPartialHomeomorph.pi_symm, OpenPartialHomeomorph.pi_trans]
    exact contDiffGroupoid_pi fun i ↦
      (contDiffGroupoid n (I i)).compatible (hf i trivial) (hg i trivial)

/-- The extended chart of a finite product at `x` is the product of the extended charts of the
factors at the coordinates of `x`. -/
theorem extChartAt_pi (x : ∀ i, M i) :
    extChartAt (ModelWithCorners.pi I) x = PartialEquiv.pi fun i ↦ extChartAt (I i) (x i) :=
  PartialEquiv.pi_trans _ _

end TauCeti

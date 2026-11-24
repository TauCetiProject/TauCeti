/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import TauCeti.Geometry.Symplectic.JHolomorphic.Varying
public import TauCeti.Geometry.Symplectic.Prod.Skew

/-!
# Holomorphic graphs in skew products

Let `J₁` be a family of almost complex structures on `V`, and let `J₂(p)` and `A(p) : V →ₗ[ℝ] W`
depend on a point `p` of `V × W`. Put on `V × W` the pointwise skew product
`J(p) = J₁(p.1).skewProd (J₂ p) (A p)` of `TauCeti.Geometry.Symplectic.Prod.Skew`. This is Gromov's
graph construction: the graph `z ↦ (z, u z)` of a map `u : V → W` is `J`-holomorphic at `z`
exactly when `u` is differentiable there and `du(z) - A(z, u z)` is complex linear from `J₁(z)` to
`J₂(z, u z)` (`TauCeti.AlmostComplexStructure.isJHolomorphicAt_graph_skewProd_iff`). Choosing
`A` turns an inhomogeneous Cauchy–Riemann equation for `u` into the holomorphicity of its graph.

The projection to `V` is holomorphic for `J₁`
(`TauCeti.AlmostComplexStructure.isJHolomorphicAt_fst_skewProd`,
`TauCeti.AlmostComplexStructure.isJHolomorphic_fst_skewProd`), so the first component of a
`J`-holomorphic map is `J₁`-holomorphic (`TauCeti.IsJHolomorphicAt.fst_of_skewProd`). A map into a
single fibre `{z} × W` is `J`-holomorphic exactly when it is holomorphic for the structures
`J₂(z, ·)` of that fibre, even when the horizontal structure varies along the fibre
(`TauCeti.AlmostComplexStructure.isJHolomorphicAt_prodMk_right_skewProd_iff`,
`TauCeti.AlmostComplexStructure.isJHolomorphic_prodMk_right_skewProd_iff`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1.
-/

public section

namespace TauCeti.AlmostComplexStructure

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {J₁ : V → AlmostComplexStructure V} {J₂ : V × W → AlmostComplexStructure W}
  {A : V × W → V →ₗ[ℝ] W} {u : V → W}

/-- **Gromov's graph construction.** The graph of `u` is holomorphic at `z` into the pointwise
skew product of `J₁` and `J₂` along `A` exactly when `u` is differentiable at `z` and
`du(z) - A(z, u z)` is complex linear from `J₁(z)` to `J₂(z, u z)`. -/
theorem isJHolomorphicAt_graph_skewProd_iff {z : V} :
    IsJHolomorphicAt J₁ (fun p ↦ (J₁ p.1).skewProd (J₂ p) (A p)) (fun w ↦ (w, u w)) z ↔
      DifferentiableAt ℝ u z ∧
        IsComplexLinearMap (J₁ z) (J₂ (z, u z)) ((fderiv ℝ u z : V →ₗ[ℝ] W) - A (z, u z)) := by
  have hgraph (hu : DifferentiableAt ℝ u z) :
      HasFDerivAt (fun w ↦ (w, u w)) ((ContinuousLinearMap.id ℝ V).prod (fderiv ℝ u z)) z :=
    (hasFDerivAt_id z).prodMk hu.hasFDerivAt
  have hlin : IsComplexLinearMap (J₁ z) ((J₁ z).skewProd (J₂ (z, u z)) (A (z, u z)))
        ((ContinuousLinearMap.id ℝ V).prod (fderiv ℝ u z) : V →ₗ[ℝ] V × W) ↔
      IsComplexLinearMap (J₁ z) (J₂ (z, u z)) ((fderiv ℝ u z : V →ₗ[ℝ] W) - A (z, u z)) := by
    rw [ContinuousLinearMap.coe_prod, ContinuousLinearMap.coe_id,
      isComplexLinearMap_id_prod_skewProd_iff]
  rw [isJHolomorphicAt_iff]
  constructor
  · rintro ⟨f', hf', hf'lin⟩
    have hu : DifferentiableAt ℝ u z := hf'.differentiableAt.snd
    rw [hf'.unique (hgraph hu)] at hf'lin
    exact ⟨hu, hlin.mp hf'lin⟩
  · rintro ⟨hu, hulin⟩
    exact ⟨_, hgraph hu, hlin.mpr hulin⟩

/-- **Gromov's graph construction, globally.** The graph of `u` is holomorphic into the pointwise
skew product of `J₁` and `J₂` along `A` exactly when `u` is differentiable and
`du(z) - A(z, u z)` is complex linear from `J₁(z)` to `J₂(z, u z)` at every `z`. -/
theorem isJHolomorphic_graph_skewProd_iff :
    IsJHolomorphic J₁ (fun p ↦ (J₁ p.1).skewProd (J₂ p) (A p)) (fun w ↦ (w, u w)) ↔
      Differentiable ℝ u ∧
        ∀ z, IsComplexLinearMap (J₁ z) (J₂ (z, u z)) ((fderiv ℝ u z : V →ₗ[ℝ] W) - A (z, u z)) := by
  simp only [isJHolomorphic_iff, isJHolomorphicAt_graph_skewProd_iff]
  exact forall_and

/-- **The projection to the base is holomorphic** at every point, from the pointwise skew product
to `J₁`. -/
theorem isJHolomorphicAt_fst_skewProd (p : V × W) :
    IsJHolomorphicAt (fun p ↦ (J₁ p.1).skewProd (J₂ p) (A p)) J₁ Prod.fst p :=
  isJHolomorphicAt_of_hasFDerivAt hasFDerivAt_fst (isComplexLinearMap_skewProd_fst _ _ _)

/-- **The projection to the base is holomorphic** from the pointwise skew product to `J₁`. -/
theorem isJHolomorphic_fst_skewProd :
    IsJHolomorphic (fun p ↦ (J₁ p.1).skewProd (J₂ p) (A p)) J₁ Prod.fst :=
  (isJHolomorphic_iff _ _ _).2 isJHolomorphicAt_fst_skewProd

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] {J : U → AlmostComplexStructure U}

/-- The first component of a map holomorphic at `y` into the pointwise skew product of `J₁` and
`J₂` is holomorphic at `y` for `J₁`. -/
theorem _root_.TauCeti.IsJHolomorphicAt.fst_of_skewProd {f : U → V × W} {y : U}
    (hf : IsJHolomorphicAt J (fun p ↦ (J₁ p.1).skewProd (J₂ p) (A p)) f y) :
    IsJHolomorphicAt J J₁ (fun y ↦ (f y).1) y := by
  obtain ⟨f', hf', hlin⟩ := (isJHolomorphicAt_iff _ _ _ _).mp hf
  rw [isComplexLinearMap_skewProd_iff] at hlin
  refine isJHolomorphicAt_of_hasFDerivAt (hasFDerivAt_fst.comp y hf') ?_
  rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.coe_fst]
  exact hlin.1

/-- **Vertical maps.** A map `y ↦ (z, g y)` into the fibre over a fixed point `z` is holomorphic
at `y` into the pointwise skew product exactly when `g` is holomorphic at `y` for the structures
`J₂(z, ·)` of that fibre. The horizontal structures `J₁` may vary along the fibre, since a vertical
map has no horizontal derivative. -/
theorem isJHolomorphicAt_prodMk_right_skewProd_iff {J₁ : V × W → AlmostComplexStructure V}
    {g : U → W} {z : V} {y : U} :
    IsJHolomorphicAt J (fun p ↦ (J₁ p).skewProd (J₂ p) (A p)) (fun y ↦ (z, g y)) y ↔
      IsJHolomorphicAt J (fun w ↦ J₂ (z, w)) g y := by
  have hvert {g' : U →L[ℝ] W} (hg : HasFDerivAt g g' y) :
      HasFDerivAt (fun y ↦ (z, g y)) ((0 : U →L[ℝ] V).prod g') y :=
    (hasFDerivAt_const z y).prodMk hg
  have hlin (g' : U →L[ℝ] W) :
      IsComplexLinearMap (J y) ((J₁ (z, g y)).skewProd (J₂ (z, g y)) (A (z, g y)))
          ((0 : U →L[ℝ] V).prod g' : U →ₗ[ℝ] V × W) ↔
        IsComplexLinearMap (J y) (J₂ (z, g y)) (g' : U →ₗ[ℝ] W) := by
    rw [isComplexLinearMap_skewProd_iff, ContinuousLinearMap.coe_prod, LinearMap.fst_prod,
      LinearMap.snd_prod, ContinuousLinearMap.toLinearMap_zero, LinearMap.comp_zero, sub_zero]
    exact and_iff_right (isComplexLinearMap_zero _ _)
  rw [isJHolomorphicAt_iff, isJHolomorphicAt_iff]
  constructor
  · rintro ⟨f', hf', hf'lin⟩
    have hg : DifferentiableAt ℝ g y := hf'.differentiableAt.snd
    rw [hf'.unique (hvert hg.hasFDerivAt)] at hf'lin
    exact ⟨_, hg.hasFDerivAt, (hlin _).mp hf'lin⟩
  · rintro ⟨g', hg', hglin⟩
    exact ⟨_, hvert hg', (hlin g').mpr hglin⟩

/-- **Vertical maps, globally.** A map `y ↦ (z, g y)` into the fibre over a fixed point `z` is
holomorphic into the pointwise skew product exactly when `g` is holomorphic for the structures
`J₂(z, ·)` of that fibre. -/
theorem isJHolomorphic_prodMk_right_skewProd_iff {J₁ : V × W → AlmostComplexStructure V}
    {g : U → W} {z : V} :
    IsJHolomorphic J (fun p ↦ (J₁ p).skewProd (J₂ p) (A p)) (fun y ↦ (z, g y)) ↔
      IsJHolomorphic J (fun w ↦ J₂ (z, w)) g := by
  simp only [isJHolomorphic_iff, isJHolomorphicAt_prodMk_right_skewProd_iff]

end TauCeti.AlmostComplexStructure

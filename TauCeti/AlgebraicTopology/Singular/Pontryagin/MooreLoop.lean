/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.Pontryagin.Basic
public import TauCeti.Topology.PathSpace.Moore.Comparison.TransSymm

/-!
# Pontryagin products of families of loops through a chosen path

Let `F : A → Path x y` and `G : B → Path x y` be continuous families of paths from `x` to `y`, and
`r` a further path from `x` to `y`. The family of loops `(a, b) ↦ F a · (G b)⁻¹` at `x`, read in the
Moore loop space `Ω_x X`, is homotopic to the pointwise product of the two families of loops
`a ↦ F a · r⁻¹` and `b ↦ r · (G b)⁻¹` (`Path.homotopic_mooreLoopTransSymm_mulMooreLoopVia`). On
singular homology with coefficients in a commutative ring `k`, the image of a cross product
`a × b` under the first family is therefore the Pontryagin product of the images of `a` and `b`
under the other two (`TauCeti.pontryaginMul_map_mooreLoopTransSymm`):

`(F · G⁻¹)_* (a × b) = (F · r⁻¹)_* a · (r · G⁻¹)_* b` in `H_*(Ω_x X; k)`.

This is how Barraud–Damian–Humilière–Oancea compute the homology class of a family of loops
`γ_w · γ_u⁻¹` built from two families of meridians of a sphere, in the proof of their Proposition
6.17: inserting a fixed meridian `γ_{u₀}` turns it into a Pontryagin product.

## Main results

* `TauCeti.pontryaginMul_map_mooreLoopTransSymm`: the class of a family `F · G⁻¹` on a cross product
  is the Pontryagin product of the classes of `F · r⁻¹` and `r · G⁻¹`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, proof of Proposition 6.17.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.C.
-/

public noncomputable section

open CategoryTheory MonoidalCategory MonObj TopCat AlgebraicTopology TensorProduct

universe u

namespace TauCeti

variable {k : Type u} [CommRing k] {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A]
  [TopologicalSpace B] {x y : X}

/-- **The class of a family of loops through a chosen path.** For continuous families `F` and `G`
of paths from `x` to `y` and a path `r` from `x` to `y`, the image of a cross product `a × b` under
the family of Moore loops `(a, b) ↦ F a · (G b)⁻¹` is the Pontryagin product of the images of `a`
under `a ↦ F a · r⁻¹` and of `b` under `b ↦ r · (G b)⁻¹`. -/
theorem pontryaginMul_map_mooreLoopTransSymm (F : C(A, Path x y)) (G : C(B, Path x y))
    (r : Path x y) (p q n : ℕ) (h : p + q = n)
    (a : ((singularHomologyFunctor (ModuleCat.{u} k) p).obj (𝟙_ _)).obj (TopCat.of A))
    (b : ((singularHomologyFunctor (ModuleCat.{u} k) q).obj (𝟙_ _)).obj (TopCat.of B)) :
    pontryaginMul k (TopCat.of (MooreLoopSpace X x)) p q n h
        (((singularHomologyFunctor (ModuleCat.{u} k) p).obj (𝟙_ _)).map
          (ofHom ((Path.mooreLoopTransSymm x y).comp (F.prodMk (.const A r)))) a)
        (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (𝟙_ _)).map
          (ofHom ((Path.mooreLoopTransSymm x y).comp ((ContinuousMap.const B r).prodMk G))) b) =
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).map
          (ofHom ((Path.mooreLoopTransSymm x y).comp (F.prodMap G)))
        (((singularHomologyFunctor (ModuleCat.{u} k) n).map (λ_ (𝟙_ _)).hom).app
          (TopCat.of A ⊗ TopCat.of B)
          (singularHomologyCross (TopCat.of A) (TopCat.of B) (𝟙_ (ModuleCat.{u} k)) (𝟙_ _) p q n h
            (a ⊗ₜ b))) := by
  rw [pontryaginMul_map_map]
  -- the pointwise product of the two families is `Path.mulMooreLoopVia r` on `(F a, G b)`
  have hfac : (ofHom ((Path.mooreLoopTransSymm x y).comp (F.prodMk (.const A r))) ⊗ₘ
      ofHom ((Path.mooreLoopTransSymm x y).comp ((ContinuousMap.const B r).prodMk G))) ≫
        μ[TopCat.of (MooreLoopSpace X x)] =
      ofHom ((Path.mulMooreLoopVia r).comp (F.prodMap G)) := by
    refine TopCat.ext fun ab ↦ ?_
    rw [ConcreteCategory.comp_apply, of_mul_apply, TopCat.tensor_apply]
    simp only [hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.prod_eval,
      ContinuousMap.const_apply, Path.mooreLoopTransSymm_apply]
    exact (Path.mulMooreLoopVia_apply r (F ab.1, G ab.2)).symm
  obtain ⟨H⟩ := (Path.homotopic_mooreLoopTransSymm_mulMooreLoopVia r).symm.comp
    (ContinuousMap.Homotopic.refl (F.prodMap G))
  -- the two maps out of `A ⊗ B`, the domain of the cross product
  have hH : ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).map
        (ofHom ((Path.mulMooreLoopVia r).comp (F.prodMap G)) :
          TopCat.of A ⊗ TopCat.of B ⟶ TopCat.of (MooreLoopSpace X x)) =
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).map
        (ofHom ((Path.mooreLoopTransSymm x y).comp (F.prodMap G)) :
          TopCat.of A ⊗ TopCat.of B ⟶ TopCat.of (MooreLoopSpace X x)) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H _ n
  rw [hfac]
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hH) _

end TauCeti

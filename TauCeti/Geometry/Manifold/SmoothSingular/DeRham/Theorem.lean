/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.SingularCohomology
public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.Geometry.Manifold.DeRham.DegreeZero
public import TauCeti.Geometry.Manifold.DeRham.HomotopyInvariance
import Mathlib.Geometry.Manifold.Instances.Icc
import TauCeti.AlgebraicTopology.Cohomology.Point
import TauCeti.Geometry.Manifold.ContMDiff.Contraction
import TauCeti.Geometry.Manifold.Topology

/-!
# The de Rham theorem: the base cases

Let `M` be a Hausdorff `σ`-compact smooth manifold modelled on a finite-dimensional real model
with corners. The de Rham theorem asserts that the de Rham homomorphism
`TauCeti.deRhamHom I M k : H^k_dR(M) → Hᵏ(M; ℝ)` is bijective in every degree. This file proves
the cases on which a Mayer–Vietoris induction over open sets starts.

* **Degree zero.** A degree-zero de Rham class is a locally constant function
  (`TauCeti.deRhamCohomologyZeroEquiv`), and a degree-zero singular class is determined by its
  values at points (`TauCeti.singularCohomologyZeroEval`). The de Rham homomorphism preserves these
  values (`TauCeti.singularCohomologyZeroEval_deRhamHom`), because the integral of a function over
  a `0`-simplex is its value at the vertex. Since a manifold is locally path-connected, the
  functions constant on path components are the locally constant ones, so `deRhamHom I M 0` is
  bijective on every manifold (`TauCeti.bijective_deRhamHom_zero`).
* **The empty manifold.** Both sides vanish in every degree
  (`TauCeti.bijective_deRhamHom_of_isEmpty`).
* **Smoothly contractible manifolds.** If a smooth homotopy contracts `M` to a point, both sides
  vanish in positive degrees (`TauCeti.subsingleton_deRhamCohomology_of_contraction` and
  `TauCeti.isZero_singularCohomology_of_contractibleSpace`), so `deRhamHom I M k` is bijective in
  every degree (`TauCeti.bijective_deRhamHom_of_contraction`). This applies to every nonempty
  open subset of a chart domain whose image in the chart is star-convex
  (`TauCeti.bijective_deRhamHom_of_starConvex_image_extChartAt`), boundary and corners included.

## Main results

* `TauCeti.singularCohomologyZeroEval_deRhamHom`: in degree zero, the de Rham homomorphism
  preserves values at points.
* `TauCeti.bijective_deRhamHom_zero`: the de Rham theorem in degree zero.
* `TauCeti.bijective_deRhamHom_of_isEmpty`, `TauCeti.bijective_deRhamHom_of_contraction`,
  `TauCeti.bijective_deRhamHom_of_starConvex_image_extChartAt`: the de Rham theorem on the empty
  manifold, on smoothly contractible manifolds and on star-convex chart domains.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18 (the proof of Theorem 18.14).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type) [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

/-- **The de Rham homomorphism preserves values in degree zero**: the singular class
`deRhamHom c` of a degree-zero de Rham class `c` takes at each point `x` the value at `x` of the
locally constant function representing `c`. -/
@[simp]
theorem singularCohomologyZeroEval_deRhamHom (c : deRhamCohomology I M 0) (x : M) :
    singularCohomologyZeroEval (X := TopCat.of M) x (deRhamHom I M 0 c) =
      deRhamCohomologyZeroEquiv I M c x := by
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective I 0 c
  -- The class of the point `x` is the image of the class of the smooth `0`-simplex at `x`. The
  -- coefficients of `singularCohomologyZeroEval` are `𝟙_ (ModuleCat ℝ)`, which is
  -- `ModuleCat.of ℝ ℝ` by definition.
  have hx := congr(ModuleCat.Hom.hom
    $(ιHomology₀_smoothSingularHomologyIso_hom I M (ModuleCat.of ℝ ℝ) x) 1)
  simp only [SSet.ιHomology₀_def, ModuleCat.hom_comp, LinearMap.comp_apply] at hx
  replace hx : (singularHomology₀Section (𝟙_ (ModuleCat ℝ)) (X := TopCat.of M) x).hom 1 = _ :=
    hx.symm
  -- So the value at `x` is the integral of `φ` over the smooth `0`-simplex at `x`.
  rw [singularCohomologyZeroEval_apply, ModuleCat.hom_comp, LinearMap.comp_apply, hx,
    singularKronecker_deRhamHom_mk_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i_assoc,
    ConcreteCategory.comp_apply, integrationCochain_ιChainComplex]
  -- The integral of a function over the smooth `0`-simplex at `x` is its value at `x`.
  rw [RoughForm.eq_ofFunction φ.val.val, SmoothSimplex.integral_equiv₀_symm_ofFunction]
  simp

/-- **The de Rham theorem in degree zero**: on every Hausdorff `σ`-compact smooth manifold
modelled on a finite-dimensional real model with corners, the de Rham homomorphism
`H⁰_dR(M) → H⁰(M; ℝ)` is bijective. Both sides are the real functions on `M` that are constant on
path components. -/
theorem bijective_deRhamHom_zero : Function.Bijective (deRhamHom I M 0) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc ↦ ?_, fun u ↦ ?_⟩
  · refine (deRhamCohomologyZeroEquiv I M).map_eq_zero_iff.1 (LocallyConstant.ext fun x ↦ ?_)
    rw [← singularCohomologyZeroEval_deRhamHom, hc, map_zero, LocallyConstant.zero_apply]
  · -- The values of `u` are constant on path components, which are open in a manifold.
    have := I.locallyPathConnectedSpace_of_chartedSpace M
    have hu : IsLocallyConstant fun x ↦ singularCohomologyZeroEval (X := TopCat.of M) x u :=
      (IsLocallyConstant.iff_exists_open _).2 fun x ↦
        ⟨pathComponent x, IsOpen.pathComponent x, mem_pathComponent_self x,
          fun y hy ↦ (singularCohomologyZeroEval_eq_of_joined (mem_pathComponent_iff.1 hy) u).symm⟩
    refine ⟨(deRhamCohomologyZeroEquiv I M).symm ⟨_, hu⟩,
      singularCohomologyZero_ext fun x ↦ ?_⟩
    rw [singularCohomologyZeroEval_deRhamHom, LinearEquiv.apply_symm_apply,
      LocallyConstant.coe_mk]

/-- **The de Rham theorem on the empty manifold**: both de Rham and singular cohomology of the
empty manifold vanish, so the de Rham homomorphism is bijective in every degree. -/
theorem bijective_deRhamHom_of_isEmpty [IsEmpty M] (k : ℕ) :
    Function.Bijective (deRhamHom I M k) := by
  have := (deRhamCohomology.mk_surjective I (M := M) k).subsingleton
  have := ModuleCat.subsingleton_of_isZero (isZero_singularCohomology_of_isEmpty
    (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) (TopCat.of M) k)
  exact Function.bijective_of_subsingleton' _

/-- **The de Rham theorem on a smoothly contractible manifold**: if `F : M × [0, 1] → M` is a
smooth homotopy from the identity of `M` to the constant map at `c`, then the de Rham
homomorphism of `M` is bijective in every degree. In positive degrees both sides vanish; in
degree zero this is `TauCeti.bijective_deRhamHom_zero`. -/
theorem bijective_deRhamHom_of_contraction {F : M × Icc (0 : ℝ) 1 → M}
    (hF : ContMDiff (I.prod (𝓡∂ 1)) I ∞ F) {c : M} (hF₀ : ∀ x, F (x, 0) = x)
    (hF₁ : ∀ x, F (x, 1) = c) (k : ℕ) : Function.Bijective (deRhamHom I M k) := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact bijective_deRhamHom_zero I M
  have := subsingleton_deRhamCohomology_of_contraction hF hF₀ hF₁ hk
  -- `F` is a homotopy from the identity to a constant map, so `M` is contractible.
  have : ContractibleSpace (TopCat.of M) := (contractible_iff_id_nullhomotopic _).2
    ⟨c, ⟨{ toFun := fun p ↦ F (p.2, p.1)
           continuous_toFun := hF.continuous.comp continuous_swap
           map_zero_left := hF₀
           map_one_left := hF₁ }⟩⟩
  have := ModuleCat.subsingleton_of_isZero (isZero_singularCohomology_of_contractibleSpace
    (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) (TopCat.of M) hk)
  exact Function.bijective_of_subsingleton' _

omit [SigmaCompactSpace M] in
/-- **The de Rham theorem on star-convex chart domains**: if an open subset `U` of `M` lies in the
domain of the extended chart at `x` and its image in the chart is star-convex about the image of a
point `c ∈ U`, then the de Rham homomorphism of `U` is bijective in every degree. The manifold may
have boundary or corners. -/
theorem bijective_deRhamHom_of_starConvex_image_extChartAt {x : M} {U : TopologicalSpace.Opens M}
    [SigmaCompactSpace U] (hU : (U : Set M) ⊆ (extChartAt I x).source) (c : U)
    (hc : StarConvex ℝ (extChartAt I x c) (extChartAt I x '' (U : Set M))) (k : ℕ) :
    Function.Bijective (deRhamHom I U k) := by
  obtain ⟨F, hF, hF₀, hF₁⟩ := exists_contMDiff_contraction_of_starConvex_image_extChartAt
    (n := ⊤) hU c hc
  exact bijective_deRhamHom_of_contraction I U (F := fun p ↦ F (p.2.val, p.1))
    (hF.comp ((contMDiff_subtypeVal_Icc.comp contMDiff_snd).prodMk contMDiff_fst))
    (fun z ↦ hF₀ z) (fun z ↦ hF₁ z) k


end TauCeti

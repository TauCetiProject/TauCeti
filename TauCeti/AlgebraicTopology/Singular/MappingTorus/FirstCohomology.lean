/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Torsion
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
import TauCeti.LinearAlgebra.Determinant.IdSub

/-!
# The first cohomology of a mapping torus

Let `φ : F ≃ₜ F` be a homeomorphism of a path-connected space and `T_φ` its mapping torus, with
singular homology taken with coefficients in a domain `k`. The Wang sequence ends with

  `H₁(F) ⟶ H₁(F) ⟶ H₁(T_φ) ⟶ H₀(F) ⟶ 0`,

with maps `𝟙 - φ_*`, the fibre inclusion and the Wang connecting morphism `δ`
(`TauCeti.MappingTorus.wangδ`), and `H₀(F) ≅ k` by the augmentation. Suppose that `H₁(F)` is free
of finite rank and `det (𝟙 - φ_*) ≠ 0` on it, so that `φ_*` has no eigenvalue one. Then the
image of the fibre is the torsion submodule of `H₁(T_φ)`
(`TauCeti.MappingTorus.torsion_homology_one_eq_range_homologyMap_fibreInclusionChainMap`), and
by exactness this is the kernel of `δ`. Hence:

* `H₁(T_φ)` modulo torsion is `H₀(F)`, through `δ`
  (`TauCeti.MappingTorus.homologyOneQuotTorsionEquiv`);
* every morphism `H₁(T_φ) ⟶ M` into a torsion-free module `M` vanishes on the torsion, so it
  factors uniquely through `δ` (`TauCeti.MappingTorus.bijective_leftComp_wangδ_zero`).

With the universal coefficient theorem in degree one, where the Kronecker map
`H¹(T_φ; M) ⟶ Hom(H₁(T_φ), M)` is bijective because `H₀(T_φ)` is free
(`TopCat.singularKronecker_bijective_of_projective_homology_lt`), this computes the first
cohomology of the mapping torus with torsion-free coefficients:

`H¹(T_φ; M) ≃ Hom(H₀(F), M) ≃ M`

(`TauCeti.MappingTorus.cohomologyOneEquivHom`, `TauCeti.MappingTorus.cohomologyOneEquiv`). The
class corresponding to `m ∈ M` evaluates on `c ∈ H₁(T_φ)` to `ε(δ c) • m`, where `ε` is the
augmentation of `H₀(F)` (`TauCeti.MappingTorus.singularKronecker_cohomologyOneEquiv_symm_apply`).
So, up to the coefficient `m`, the only degree-one class is the one evaluating to `ε ∘ δ`.
Geometrically `ε ∘ δ` counts how many times a cycle winds around the base circle of the mapping
torus; that comparison with the projection `T_φ → S¹` is not made here.

For a closed orientable surface `F`, `H₁(F; ℤ)` is free of finite rank. If the integral
determinant `det (1 - φ_*)` is nonzero, then `H¹(Y_φ; ℤ) ≅ ℤ`, with no torsion, while the
torsion of `H₁(Y_φ; ℤ)` has order `|det (1 - φ_*)|`
(`TauCeti.MappingTorus.card_torsion_homology_one_eq_natAbs_det`). By the splitting of the
cohomology of a product with a circle (`TopCat.singularCohomologySphereProdEquiv`), this makes the
summand `θ ⌣ pr₂^* H¹(Y_φ; ℤ)` of `H²(S¹ × Y_φ; ℤ)` a single copy of `ℤ`. The integral
determinant is nonzero exactly when `b₁(Y_φ) = 1` over `ℚ`, or over any field of characteristic
zero (`TauCeti.MappingTorus.finrank_homology_one_eq_one_iff_det_int_ne_zero`).

## Main results

* `TauCeti.MappingTorus.det_id_sub_homologyMap_monodromyChainMap_symm_ne_zero_iff`: the
  hypothesis `det (𝟙 - φ_*) ≠ 0` is the same for `φ` and `φ⁻¹`.
* `TauCeti.MappingTorus.ker_wangδ_zero_eq_torsion`: the kernel of `δ : H₁(T_φ) ⟶ H₀(F)` is the
  torsion submodule.
* `TauCeti.MappingTorus.homologyOneQuotTorsionEquiv`: `H₁(T_φ) ⧸ torsion ≃ H₀(F)`.
* `TauCeti.MappingTorus.bijective_leftComp_wangδ_zero`: precomposition with `δ` is a bijection
  `Hom(H₀(F), M) ≃ Hom(H₁(T_φ), M)` for a torsion-free module `M`.
* `TauCeti.MappingTorus.cohomologyOneEquivHom`: `H¹(T_φ; M) ≃ Hom(H₀(F), M)`.
* `TauCeti.MappingTorus.cohomologyOneEquiv`: `H¹(T_φ; M) ≃ M`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Example 2.48 (the Wang sequence of a mapping torus), and Section 3.1,
  Theorem 3.2 (the universal coefficient theorem).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

universe w

namespace TauCeti.MappingTorus

variable {k : Type w} [CommRing k] [IsDomain k] {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)

omit [IsDomain k] in
/-- **The monodromy and its inverse.** On `Hₙ(F)`, `det (𝟙 - (φ⁻¹)_*) ≠ 0` exactly when
`det (𝟙 - φ_*) ≠ 0`, since `(φ⁻¹)_*` and `φ_*` are mutually inverse
(`LinearMap.det_id_sub_ne_zero_iff_of_comp_eq_id`). -/
theorem det_id_sub_homologyMap_monodromyChainMap_symm_ne_zero_iff (n : ℕ) :
    (LinearMap.id -
      (homologyMap (monodromyChainMap φ.symm (ModuleCat.of k k)) n).hom).det ≠ 0 ↔
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom).det ≠ 0 := by
  refine LinearMap.det_id_sub_ne_zero_iff_of_comp_eq_id ?_
  rw [← ModuleCat.hom_comp, ← homologyMap_comp, monodromyChainMap_def, monodromyChainMap_def,
    ← Functor.map_comp, ← TopCat.ofHom_comp]
  have h : (⟨φ.symm, φ.symm.continuous⟩ : C(F, F)).comp ⟨φ, φ.continuous⟩ = ContinuousMap.id F :=
    ContinuousMap.ext φ.symm_apply_apply
  rw [h, TopCat.ofHom_id, CategoryTheory.Functor.map_id, homologyMap_id, ModuleCat.hom_id]

/-- **The kernel of the Wang connecting morphism is the torsion.** If `H₁(F)` is free of finite
rank and `det (𝟙 - φ_*) ≠ 0` on it, the kernel of `δ : H₁(T_φ) ⟶ H₀(F)` is the torsion
submodule of `H₁(T_φ)`. -/
theorem ker_wangδ_zero_eq_torsion
    [Module.Free k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)]
    [Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)]
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0) :
    LinearMap.ker (wangδ φ (ModuleCat.of k k) 0).hom =
      Submodule.torsion k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology 1) := by
  rw [← range_homologyMap_fibreInclusionChainMap,
    torsion_homology_one_eq_range_homologyMap_fibreInclusionChainMap φ hdet]

variable [PathConnectedSpace F]

variable [Module.Free k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
    (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)]
  [Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
    (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)]

/-- **The first homology of a mapping torus modulo torsion.** If `F` is path-connected, `H₁(F)` is
free of finite rank and `det (𝟙 - φ_*) ≠ 0` on it, the Wang connecting morphism induces an
isomorphism `H₁(T_φ) ⧸ torsion ≃ H₀(F)`, and `H₀(F) ≅ k` by the augmentation. -/
def homologyOneQuotTorsionEquiv
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0) :
    ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology 1 ⧸
      Submodule.torsion k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology 1)) ≃ₗ[k]
      (((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of F)).homology 0 :=
  (Submodule.quotEquivOfEq _ _ (ker_wangδ_zero_eq_torsion φ hdet).symm).trans
    ((wangδ φ (ModuleCat.of k k) 0).hom.quotKerEquivOfSurjective
      ((ModuleCat.epi_iff_surjective _).1 inferInstance))

/-- The isomorphism `homologyOneQuotTorsionEquiv` sends the class of `c` to `δ c`. -/
@[simp]
theorem homologyOneQuotTorsionEquiv_mk
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0)
    (c : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology 1) :
    homologyOneQuotTorsionEquiv φ hdet (Submodule.Quotient.mk c) =
      (wangδ φ (ModuleCat.of k k) 0).hom c :=
  (rfl)

variable (M : ModuleCat.{w} k) [Module.IsTorsionFree k M]

/-- **Morphisms out of the first homology of a mapping torus.** If `F` is path-connected, `H₁(F)`
is free of finite rank and `det (𝟙 - φ_*) ≠ 0` on it, then for a torsion-free module `M` every
morphism `H₁(T_φ) ⟶ M` factors uniquely through the Wang connecting morphism
`δ : H₁(T_φ) ⟶ H₀(F)`: precomposition with `δ` is a bijection
`Hom(H₀(F), M) ≃ Hom(H₁(T_φ), M)`. -/
theorem bijective_leftComp_wangδ_zero
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0) :
    Function.Bijective (Linear.leftComp k M (wangδ φ (ModuleCat.of k k) 0)) := by
  refine ⟨fun g g' h ↦ (cancel_epi (wangδ φ (ModuleCat.of k k) 0)).1 h, fun f ↦ ?_⟩
  -- A morphism into a torsion-free module vanishes on the torsion, so it factors through the
  -- quotient by the torsion, which `δ` identifies with `H₀(F)`.
  refine ⟨(ModuleCat.homLinearEquiv (S := k)).symm
    ((Submodule.torsion k _).liftQ f.hom f.hom.torsion_le_ker ∘ₗ
      (homologyOneQuotTorsionEquiv φ hdet).symm.toLinearMap),
    ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)⟩
  simp [-homologyOneQuotTorsionEquiv_mk, ← homologyOneQuotTorsionEquiv_mk φ hdet c]

/-- **The first cohomology of a mapping torus, as morphisms out of `H₀(F)`.** If `F` is
path-connected, `H₁(F)` is free of finite rank and `det (𝟙 - φ_*) ≠ 0` on it, then for a
torsion-free module `M` the first cohomology `H¹(T_φ; M)` is `Hom(H₀(F), M)`: a class corresponds
to the morphism through which its Kronecker evaluation on `H₁(T_φ)` factors via the Wang connecting
morphism (`TauCeti.MappingTorus.wangδ_zero_comp_cohomologyOneEquivHom`). -/
def cohomologyOneEquivHom
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0) :
    (TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k M 1 ≃ₗ[k]
      ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of F)).homology 0 ⟶ M) :=
  (LinearEquiv.ofBijective _
    ((TopCat.of (MappingTorus φ)).singularKronecker_bijective_of_projective_homology_lt M 1
      fun j hj ↦ by
        obtain rfl : j = 0 := by omega
        exact ModuleCat.projective_of_free (Module.Free.chooseBasis k _))).trans
    (LinearEquiv.ofBijective _ (bijective_leftComp_wangδ_zero φ M hdet)).symm

/-- The Kronecker evaluation of a class of `H¹(T_φ; M)` is the Wang connecting morphism followed
by the morphism `cohomologyOneEquivHom` assigns to the class. -/
@[simp, reassoc]
theorem wangδ_zero_comp_cohomologyOneEquivHom
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0)
    (α : (TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k M 1) :
    wangδ φ (ModuleCat.of k k) 0 ≫ cohomologyOneEquivHom φ M hdet α =
      (TopCat.of (MappingTorus φ)).singularKronecker k 1 α :=
  (LinearEquiv.ofBijective _ (bijective_leftComp_wangδ_zero φ M hdet)).apply_symm_apply _

/-- The Kronecker evaluation of the class that `cohomologyOneEquivHom` assigns to a morphism
`g : H₀(F) ⟶ M` is the Wang connecting morphism followed by `g`. -/
@[simp, reassoc]
theorem singularKronecker_cohomologyOneEquivHom_symm
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0)
    (g : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 0 ⟶ M) :
    (TopCat.of (MappingTorus φ)).singularKronecker k 1 ((cohomologyOneEquivHom φ M hdet).symm g) =
      wangδ φ (ModuleCat.of k k) 0 ≫ g := by
  rw [← wangδ_zero_comp_cohomologyOneEquivHom φ M hdet, LinearEquiv.apply_symm_apply]

/-- **The first cohomology of a mapping torus.** If `F` is path-connected, `H₁(F)` is free of
finite rank and `det (𝟙 - φ_*) ≠ 0` on it, then for a torsion-free module `M`,
`H¹(T_φ; M) ≃ M`. The class corresponding to `m` evaluates on `c ∈ H₁(T_φ)` to `ε(δ c) • m`,
with `δ` the Wang connecting morphism and `ε` the augmentation of `H₀(F)`
(`TauCeti.MappingTorus.singularKronecker_cohomologyOneEquiv_symm_apply`). With `k = M = ℤ` and a
closed orientable surface `F`, this is `H¹(Y_φ; ℤ) ≅ ℤ` when the integral determinant
`det (1 - φ_*)` is nonzero, which is the condition `b₁(Y_φ) = 1` over `ℚ`
(`TauCeti.MappingTorus.finrank_homology_one_eq_one_iff_det_int_ne_zero`). -/
def cohomologyOneEquiv
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0) :
    (TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k M 1 ≃ₗ[k] M :=
  (cohomologyOneEquivHom φ M hdet).trans
    ((ModuleCat.homLinearEquiv (S := k)).trans
      ((LinearEquiv.arrowCongr
        (asIso ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k))).toLinearEquiv
        (LinearEquiv.refl k M)).trans (LinearMap.ringLmapEquivSelf k k M)))

/-- `cohomologyOneEquiv` sends a class to the value at `ε⁻¹ 1` of the morphism
`H₀(F) ⟶ M` that `cohomologyOneEquivHom` assigns to it. -/
theorem cohomologyOneEquiv_apply
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0)
    (α : (TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k M 1) :
    cohomologyOneEquiv φ M hdet α = (cohomologyOneEquivHom φ M hdet α).hom
      ((inv ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k))).hom 1) :=
  (rfl)

/-- The class of `H¹(T_φ; M)` corresponding to `m ∈ M` evaluates on `c ∈ H₁(T_φ)` to `ε(δ c) • m`,
where `δ` is the Wang connecting morphism and `ε` the augmentation of `H₀(F)`. -/
@[simp]
theorem singularKronecker_cohomologyOneEquiv_symm_apply
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0) (m : M)
    (c : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology 1) :
    ((TopCat.of (MappingTorus φ)).singularKronecker k 1
        ((cohomologyOneEquiv φ M hdet).symm m)).hom c =
      (TopCat.of F).singularHomology₀ε (ModuleCat.of k k) ((wangδ φ (ModuleCat.of k k) 0).hom c) •
        m := by
  have h := ConcreteCategory.congr_hom
    (wangδ_zero_comp_cohomologyOneEquivHom φ M hdet ((cohomologyOneEquiv φ M hdet).symm m)) c
  rw [ConcreteCategory.comp_apply] at h
  refine h.symm.trans ?_
  generalize (wangδ φ (ModuleCat.of k k) 0).hom c = x
  -- The morphism attached to the class is determined by its value `m` on the class `ε⁻¹ 1`.
  have hm : (cohomologyOneEquivHom φ M hdet ((cohomologyOneEquiv φ M hdet).symm m)).hom
      ((inv ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k))).hom 1) = m := by
    rw [← cohomologyOneEquiv_apply, LinearEquiv.apply_symm_apply]
  have hx : x = (TopCat.of F).singularHomology₀ε (ModuleCat.of k k) x •
      (inv ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k))).hom 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
    exact (ConcreteCategory.congr_hom
      (IsIso.hom_inv_id ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k))) x).symm
  calc _ = (cohomologyOneEquivHom φ M hdet ((cohomologyOneEquiv φ M hdet).symm m)).hom
        ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k) x •
          (inv ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k))).hom 1) := congrArg _ hx
    _ = _ := (map_smul _ _ _).trans (congrArg _ hm)

end TauCeti.MappingTorus

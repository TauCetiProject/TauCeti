/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.BaseCircle
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.FirstCohomology
public import TauCeti.Geometry.Manifold.DeRham.MappingTorus
import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit

/-!
# The integral class of the time form of a mapping torus

Let `φ` be a diffeomorphism of a manifold `M` and `Y_φ` its smooth mapping torus, with closed time
form `dt` and time period homomorphism `N : H₁(Y_φ; ℤ) → ℤ`, `N(h) = ∫_h dt`
(`TauCeti.SmoothMappingTorus.intTimePeriodHom`). This file compares `N` with the Wang sequence of
`Y_φ` and defines the integral cohomology class of `dt`.

**The time period is the Wang class.** Through the homeomorphism of `Y_φ` with the topological
mapping torus of `φ⁻¹` (`TauCeti.SmoothMappingTorus.homeomorphMappingTorus`), the Wang class
`ε ∘ δ : H₁(Y_φ; ℤ) → ℤ` (`TauCeti.MappingTorus.wangClass`) is `N` times the universal sign
`TauCeti.MappingTorus.circleWangSign`
(`TauCeti.SmoothMappingTorus.wangClass_singularHomologyMap_homeomorphMappingTorus`), which is `-1`
(`TauCeti.MappingTorus.circleWangSign_eq_neg_one`). Both factor
through the projection to the circle `ℝ / ℤ`: `N` as the winding number of the image class
(`TauCeti.SmoothMappingTorus.intTimePeriodHom_eq_firstHomologyAddEquiv`), the Wang class as the
Wang class of the circle
(`TauCeti.MappingTorus.wangClass_eq_singularHomologyMap_proj_comp_circleWangClass`). Hence, for a
path-connected fibre:

* `N` is surjective (`TauCeti.SmoothMappingTorus.intTimePeriodHom_surjective`), because the Wang
  connecting morphism `H₁(Y_φ) → H₀(M) ≅ ℤ` is;
* if moreover `H₁(M; ℤ)` is free of finite rank and `det (1 - φ_*) ≠ 0` on it, so that
  `b₁(Y_φ) = 1`, the kernel of `N` is exactly the torsion of `H₁(Y_φ; ℤ)`
  (`TauCeti.SmoothMappingTorus.intTimePeriodHom_eq_zero_iff`), by the computation of the kernel of
  the Wang connecting morphism (`TauCeti.MappingTorus.ker_wangδ_zero_eq_torsion`). So `N`
  identifies `H₁(Y_φ; ℤ)` modulo torsion with `ℤ`: for a class `g` of time period one, every
  class `c` differs from `N(c) • g` by an element of finite order
  (`TauCeti.SmoothMappingTorus.isOfFinAddOrder_sub_intTimePeriodHom_zsmul`). In particular the
  class of the closed orbit through a point of period `d` is `d • g` modulo torsion
  (`TauCeti.SmoothMappingTorus.isOfFinAddOrder_closedOrbitHomologyClass_sub_zsmul`): when
  `b₁(Y_φ) = 1`, the real period of a closed orbit is its divisibility in homology modulo torsion,
  while the torsion part of its class is not determined by the period.

**The class of `dt`.** Since `H₀(Y_φ; ℤ)` is free, the Kronecker map identifies `H¹(Y_φ; ℤ)` with
`Hom(H₁(Y_φ; ℤ), ℤ)` (`TopCat.singularKroneckerEquivOne`), and the **time class**
`[dt] ∈ H¹(Y_φ; ℤ)` (`TauCeti.SmoothMappingTorus.timeClass`) is the class corresponding to `N`: its
pairing with a class is that class's period of `dt`
(`TauCeti.SmoothMappingTorus.intCast_singularKronecker_timeClass`). It is the integral class of the
closed form `dt`, defined for every mapping torus, and it is the pullback `proj^* θ` of the angular
class `θ = [ds]` of the circle (`AddCircle.angularClass`) along the projection `Y_φ → ℝ / ℤ`
(`TauCeti.SmoothMappingTorus.singularCohomologyMap_proj_angularClass`). When `b₁(Y_φ) = 1` it
generates `H¹(Y_φ; ℤ) ≅ ℤ`: every class is a unique integer multiple of `[dt]`
(`TauCeti.SmoothMappingTorus.exists_eq_zsmul_timeClass`,
`TauCeti.SmoothMappingTorus.zsmul_timeClass_eq_zero_iff`). So for a surface diffeomorphism with
`b₁(Y_φ) = 1`, the class `a` in the generator `θ_p ⌣ pr₂^* a` of `H²((ℝ / pℤ)_s × Y_φ; ℤ)` modulo
torsion can be taken to be `[dt]`, the integral class of the time form. Here `θ_p = [ds]` is the
angular class of `ℝ / pℤ` (`AddCircle.angularClass p`), and the basis `pr₂^* v`, `θ_p ⌣ pr₂^* a` is
the one of `TauCeti.AlgebraicTopology.Singular.MappingTorus.CircleProduct`, read through
`TauCeti.SmoothMappingTorus.homeomorphMappingTorus`.

## Main results

* `TauCeti.SmoothMappingTorus.wangClass_singularHomologyMap_homeomorphMappingTorus`: the Wang class
  is `circleWangSign` times the time period.
* `TauCeti.SmoothMappingTorus.intTimePeriodHom_surjective`: for a path-connected fibre the time
  period is onto `ℤ`.
* `TauCeti.SmoothMappingTorus.intTimePeriodHom_eq_zero_iff`: when `b₁(Y_φ) = 1`, a class has time
  period zero exactly when it has finite order.
* `TauCeti.SmoothMappingTorus.timeClass`: the integral class `[dt] ∈ H¹(Y_φ; ℤ)`.
* `TauCeti.SmoothMappingTorus.singularCohomologyMap_proj_angularClass`: `[dt] = proj^* θ`.
* `TauCeti.SmoothMappingTorus.exists_eq_zsmul_timeClass`,
  `TauCeti.SmoothMappingTorus.zsmul_timeClass_eq_zero_iff`: when `b₁(Y_φ) = 1`, `[dt]` generates
  `H¹(Y_φ; ℤ) ≅ ℤ`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Example 2.48 (the Wang sequence of a mapping
  torus), and Section 3.1, Theorem 3.2 (the universal coefficient theorem).
* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and
  Seiberg–Witten invariants of 3-manifolds*, Topology 38 (1999), 861–888, Section 2.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory TauCeti.MappingTorus
open scoped Manifold ContDiff

-- The Kronecker map is stated with the linear structure of `ModuleCat ℤ` as a category of modules
-- over a commutative ring, which instance search would otherwise not find.
attribute [local instance 1100] ModuleCat.instLinear

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] (φ : M ≃ₘ⟮I, I⟯ M)

/-! ### The time period and the Wang class -/

/-- **The time period is a winding number.** The time period of a class of `H₁(Y_φ; ℤ)` is the
winding number of its image under the projection `Y_φ → ℝ / ℤ`. -/
theorem intTimePeriodHom_eq_firstHomologyAddEquiv
    (c : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology 1) :
    intTimePeriodHom φ c = AddCircle.firstHomologyAddEquiv 1
      (ContinuousMap.singularHomologyMap ℤ 1 ⟨proj φ, (contMDiff_proj φ).continuous⟩ c) := by
  refine Int.cast_injective (α := ℝ) ?_
  rw [intCast_intTimePeriodHom, timePeriodHom_eq_homologyPeriodHom_singularHomologyMap_proj,
    AddCircle.homologyPeriodHom_timeForm, mul_one]

/-- **The Wang class of a mapping torus is its time period, up to a universal sign.** Through the
homeomorphism of `Y_φ` with the topological mapping torus of `φ⁻¹`, the Wang class
`ε ∘ δ : H₁(Y_φ; ℤ) → ℤ` is `circleWangSign = -1` times the time period `N(c) = ∫_c dt`. -/
theorem wangClass_singularHomologyMap_homeomorphMappingTorus
    (c : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology 1) :
    (wangClass (ModuleCat.of ℤ ℤ) φ.toHomeomorph.symm).hom
        (ContinuousMap.singularHomologyMap ℤ 1
          ⟨homeomorphMappingTorus φ, (homeomorphMappingTorus φ).continuous⟩ c) =
      circleWangSign * intTimePeriodHom φ c := by
  -- Both sides factor through the projection to the circle, and the homeomorphism lies over it.
  have hproj : (⟨MappingTorus.proj φ.toHomeomorph.symm, MappingTorus.continuous_proj _⟩ :
        C(MappingTorus φ.toHomeomorph.symm, UnitAddCircle)).comp
        ⟨homeomorphMappingTorus φ, (homeomorphMappingTorus φ).continuous⟩ =
      ⟨proj φ, (contMDiff_proj φ).continuous⟩ :=
    ContinuousMap.ext (proj_homeomorphMappingTorus φ)
  calc _ = (circleWangClass (ModuleCat.of ℤ ℤ)).hom
        (ContinuousMap.singularHomologyMap ℤ 1 ⟨proj φ, (contMDiff_proj φ).continuous⟩ c) := by
        rw [wangClass_eq_singularHomologyMap_proj_comp_circleWangClass, ← hproj,
          ContinuousMap.singularHomologyMap_comp]
        simp only [ContinuousMap.singularHomologyMap_eq_singularHomologyFunctor_map,
          ModuleCat.hom_comp]
        -- `rw [LinearMap.comp_apply]` cannot see through the two spellings of `H₁` here.
        exact LinearMap.comp_apply _ _ _
    _ = _ := by rw [circleWangClass_hom_apply, intTimePeriodHom_eq_firstHomologyAddEquiv, mul_comm]

/-- The time period is `circleWangSign` times the Wang class, read through the homeomorphism of
`Y_φ` with the topological mapping torus of `φ⁻¹`. -/
theorem intTimePeriodHom_eq_circleWangSign_mul_wangClass
    (c : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology 1) :
    intTimePeriodHom φ c = circleWangSign * (wangClass (ModuleCat.of ℤ ℤ) φ.toHomeomorph.symm).hom
        (ContinuousMap.singularHomologyMap ℤ 1
          ⟨homeomorphMappingTorus φ, (homeomorphMappingTorus φ).continuous⟩ c) := by
  rw [wangClass_singularHomologyMap_homeomorphMappingTorus, circleWangSign_eq_neg_one, neg_one_mul,
    neg_one_mul, neg_neg]

/-! ### The integral class of `dt` -/

/-- The time period homomorphism as a morphism `H₁(Y_φ; ℤ) ⟶ ℤ` of `ℤ`-modules. The `ℤ`-module
structure of a homology module is not definitionally the canonical one `AddCommGroup.toIntModule`
of `AddMonoidHom.toIntLinearMap`, so linearity is proved through `int_smul_eq_zsmul`. -/
private def intTimePeriodModuleHom :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (𝟙_ (ModuleCat.{0} ℤ))).obj (TopCat.of (SmoothMappingTorus φ)) ⟶ 𝟙_ (ModuleCat.{0} ℤ) :=
  ModuleCat.ofHom
    { toFun := intTimePeriodHom φ
      map_add' := map_add _
      map_smul' := fun n c ↦ (congrArg (intTimePeriodHom φ) (int_smul_eq_zsmul _ n c)).trans
        (map_zsmul _ n c) }

/-- **The integral class of the time form** `[dt] ∈ H¹(Y_φ; ℤ)`: under the universal coefficient
isomorphism `H¹(Y_φ; ℤ) ≃ Hom(H₁(Y_φ; ℤ), ℤ)`, the class of the time period homomorphism, so that
it pairs with each class of `H₁(Y_φ; ℤ)` to its period `∫ dt`
(`TauCeti.SmoothMappingTorus.singularKronecker_timeClass`). -/
def timeClass : (TopCat.of (SmoothMappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
    (𝟙_ (ModuleCat.{0} ℤ)) 1 :=
  ((TopCat.of (SmoothMappingTorus φ)).singularKroneckerEquivOne (𝟙_ (ModuleCat.{0} ℤ))).symm
    (intTimePeriodModuleHom φ)

/-- The integral class of `dt` evaluates a class of `H₁(Y_φ; ℤ)` to its time period. -/
@[simp]
theorem singularKronecker_timeClass
    (c : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology 1) :
    (TopCat.of (SmoothMappingTorus φ)).singularKronecker ℤ 1 (timeClass φ) c =
      intTimePeriodHom φ c := by
  have h := ((TopCat.of (SmoothMappingTorus φ)).singularKroneckerEquivOne
    (𝟙_ (ModuleCat.{0} ℤ))).apply_symm_apply (intTimePeriodModuleHom φ)
  rw [TopCat.singularKroneckerEquivOne_apply] at h
  -- `intTimePeriodModuleHom φ` evaluates as `intTimePeriodHom φ` by its definition.
  exact congr($h c)

/-- **`[dt]` is the integral class of `dt`**: its pairing with a class of `H₁(Y_φ; ℤ)` is the
integral of the closed form `dt` over that class. -/
theorem intCast_singularKronecker_timeClass
    (c : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology 1) :
    (((TopCat.of (SmoothMappingTorus φ)).singularKronecker ℤ 1 (timeClass φ) c : ℤ) : ℝ) =
      homologyPeriodHom (timeForm φ).val c := by
  rw [singularKronecker_timeClass, intCast_intTimePeriodHom, timePeriodHom_def]

/-- **The integral class of `dt` is characterized by its periods**: a class of `H¹(Y_φ; ℤ)` is
`[dt]` exactly when it evaluates every class of `H₁(Y_φ; ℤ)` to its time period. -/
theorem eq_timeClass_iff
    (a : (TopCat.of (SmoothMappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (𝟙_ (ModuleCat.{0} ℤ)) 1) :
    a = timeClass φ ↔ ∀ c, (TopCat.of (SmoothMappingTorus φ)).singularKronecker ℤ 1 a c =
      intTimePeriodHom φ c := by
  refine ⟨fun h c ↦ h ▸ singularKronecker_timeClass φ c, fun h ↦ ?_⟩
  exact TopCat.singularCohomology_one_ext _ fun c ↦
    (h c).trans (singularKronecker_timeClass φ c).symm

/-- **`[dt]` is the pullback of the angular class**: the integral class of `dt` is the pullback
`proj^* θ` of the angular class `θ = [ds]` of `ℝ / ℤ` along the projection `Y_φ → ℝ / ℤ`, since
the time period of a class is the winding number of its image. -/
theorem singularCohomologyMap_proj_angularClass :
    TopCat.singularCohomologyMap (TopCat.ofHom ⟨proj φ, (contMDiff_proj φ).continuous⟩) 1
      (AddCircle.angularClass 1) = timeClass φ := by
  refine (eq_timeClass_iff φ _).2 fun c ↦ ?_
  rw [TopCat.singularKronecker_naturality]
  -- The composite applied to `c` is the pairing of `θ` with the image of `c` by definition
  -- (`ContinuousMap.singularHomologyMap_eq_singularHomologyFunctor_map`).
  exact (AddCircle.singularKronecker_angularClass 1
    (ContinuousMap.singularHomologyMap ℤ 1 ⟨proj φ, (contMDiff_proj φ).continuous⟩ c)).trans
      (intTimePeriodHom_eq_firstHomologyAddEquiv φ c).symm

/-! ### The time period modulo torsion -/

/-- **The time period is onto.** For a path-connected fibre, every integer is the time period of a
class of `H₁(Y_φ; ℤ)`: the Wang connecting morphism `H₁(Y_φ) → H₀(M)` and the augmentation
`H₀(M) → ℤ` are onto. -/
theorem intTimePeriodHom_surjective [PathConnectedSpace M] :
    Function.Surjective (intTimePeriodHom φ) := by
  intro n
  obtain ⟨x₀⟩ := PathConnectedSpace.nonempty (X := M)
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective
    (wangδ φ.toHomeomorph.symm (ModuleCat.of ℤ ℤ) 0)).1 inferInstance
    (singularHomology₀Section (ModuleCat.of ℤ ℤ) (X := TopCat.of M) x₀ (circleWangSign * n))
  refine ⟨ContinuousMap.singularHomologyMap ℤ 1
    ⟨(homeomorphMappingTorus φ).symm, (homeomorphMappingTorus φ).symm.continuous⟩ x, ?_⟩
  rw [intTimePeriodHom_eq_circleWangSign_mul_wangClass,
    (homeomorphMappingTorus φ).singularHomologyMap_apply_symm_apply,
    wangClass_hom_apply_singularChains, hx,
    TauCeti.singularHomology₀Section_singularHomology₀ε_apply, circleWangSign_eq_neg_one,
    neg_one_mul, neg_one_mul, neg_neg]

/-- For a path-connected fibre, some class of `H₁(Y_φ; ℤ)` pairs to `1` with the integral class of
`dt`: a class of time period one. -/
theorem exists_singularKronecker_timeClass_eq_one [PathConnectedSpace M] :
    ∃ g : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (𝟙_ (ModuleCat.{0} ℤ))).obj (TopCat.of (SmoothMappingTorus φ)),
      ((TopCat.of (SmoothMappingTorus φ)).singularKronecker ℤ 1 (timeClass φ)).hom g = 1 :=
  (intTimePeriodHom_surjective φ 1).imp fun g hg ↦ (singularKronecker_timeClass φ g).trans hg

/-- **`[dt]` has infinite order.** For a path-connected fibre, an integer multiple of the integral
class of `dt` vanishes only for the integer zero: it pairs to that integer with a class of time
period one. -/
theorem zsmul_timeClass_eq_zero_iff [PathConnectedSpace M] {n : ℤ} :
    n • timeClass φ = 0 ↔ n = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, zero_smul]⟩
  obtain ⟨g, hg⟩ := exists_singularKronecker_timeClass_eq_one φ
  -- Pairing `n • [dt] = 0` with the class `g` of time period one gives `n = 0`.
  have hK : ((TopCat.of (SmoothMappingTorus φ)).singularKronecker ℤ 1 (n • timeClass φ)).hom g =
      0 := by
    rw [h, map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
  rwa [map_zsmul, ModuleCat.hom_zsmul, LinearMap.smul_apply, hg, smul_eq_mul, mul_one] at hK

variable [PathConnectedSpace M]
  [Module.Free ℤ (((singularChains ℤ).obj (TopCat.of M)).homology 1)]
  [Module.Finite ℤ (((singularChains ℤ).obj (TopCat.of M)).homology 1)]

/-- **The kernel of the time period is the torsion.** Let the fibre `M` be path-connected with
`H₁(M; ℤ)` free of finite rank, and let `det (1 - φ_*) ≠ 0` on it, so that `b₁(Y_φ) = 1`. Then a
class of `H₁(Y_φ; ℤ)` has time period `∫ dt` zero exactly when it has finite order. -/
theorem intTimePeriodHom_eq_zero_iff
    (hdet : (LinearMap.id -
      (HomologicalComplex.homologyMap
        (monodromyChainMap φ.toHomeomorph (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    (c : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology 1) :
    intTimePeriodHom φ c = 0 ↔ IsOfFinAddOrder c := by
  set x := ContinuousMap.singularHomologyMap ℤ 1
    ⟨homeomorphMappingTorus φ, (homeomorphMappingTorus φ).continuous⟩ c
  -- The kernel of the Wang connecting morphism is the torsion of `H₁(T_{φ⁻¹})`.
  have hker := SetLike.ext_iff.1 (ker_wangδ_zero_eq_torsion φ.toHomeomorph.symm
    ((det_id_sub_homologyMap_monodromyChainMap_symm_ne_zero_iff φ.toHomeomorph 1).2 hdet)) x
  rw [LinearMap.mem_ker] at hker
  rw [intTimePeriodHom_eq_circleWangSign_mul_wangClass, circleWangSign_eq_neg_one, neg_one_mul,
    neg_eq_zero]
  -- `x` lies in the homology of `singularChains ℤ`, the source of `wangClass` only definitionally,
  -- so the lemma is applied by unification rather than by `rw`.
  refine (wangClass_hom_eq_zero_iff φ.toHomeomorph.symm (ModuleCat.of ℤ ℤ) x).trans ?_
  rw [hker, ← Submodule.mem_toAddSubgroup]
  -- The torsion submodule for the module structure of `ModuleCat ℤ` is the group torsion; the two
  -- `ℤ`-module structures agree because `Module ℤ` is a subsingleton.
  rw [show (Submodule.torsion ℤ (((singularChains ℤ).obj
      (TopCat.of (MappingTorus φ.toHomeomorph.symm))).homology 1)).toAddSubgroup =
      AddCommGroup.torsion _ by
        convert Submodule.torsion_int
        exact Subsingleton.elim _ _, AddCommGroup.mem_torsion]
  exact (homeomorphMappingTorus φ).isOfFinAddOrder_singularHomologyMap_iff

/-- **`H₁(Y_φ; ℤ)` modulo torsion is generated by a class of time period one.** When
`b₁(Y_φ) = 1`, for a class `g` with `∫_g dt = 1`, every class `c` differs from `N(c) • g` by an
element of finite order, where `N(c) = ∫_c dt`. -/
theorem isOfFinAddOrder_sub_intTimePeriodHom_zsmul
    (hdet : (LinearMap.id -
      (HomologicalComplex.homologyMap
        (monodromyChainMap φ.toHomeomorph (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    {g : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology 1}
    (hg : intTimePeriodHom φ g = 1)
    (c : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology 1) :
    IsOfFinAddOrder (c - intTimePeriodHom φ c • g) := by
  rw [← intTimePeriodHom_eq_zero_iff φ hdet, map_sub, map_zsmul, hg, smul_eq_mul, mul_one, sub_self]

/-- **Closed orbits modulo torsion.** When `b₁(Y_φ) = 1`, the class of the closed orbit through a
point of period `d` is `d • g` modulo torsion, for every class `g` of time period one. -/
theorem isOfFinAddOrder_closedOrbitHomologyClass_sub_zsmul
    (hdet : (LinearMap.id -
      (HomologicalComplex.homologyMap
        (monodromyChainMap φ.toHomeomorph (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    {g : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology 1}
    (hg : intTimePeriodHom φ g = 1) {d : ℕ} {x : M} (hx : Function.IsPeriodicPt φ d x) :
    IsOfFinAddOrder (closedOrbitHomologyClass hx - (d : ℤ) • g) := by
  simpa [intTimePeriodHom_closedOrbitHomologyClass] using
    isOfFinAddOrder_sub_intTimePeriodHom_zsmul φ hdet hg (closedOrbitHomologyClass hx)

/-- **`[dt]` generates `H¹(Y_φ; ℤ)`.** Let the fibre `M` be path-connected with `H₁(M; ℤ)` free of
finite rank, and let `det (1 - φ_*) ≠ 0` on it, so that `b₁(Y_φ) = 1`. Then every class of
`H¹(Y_φ; ℤ)` is an integer multiple of the integral class of `dt`; the integer is unique by
`TauCeti.SmoothMappingTorus.zsmul_timeClass_eq_zero_iff`. -/
theorem exists_eq_zsmul_timeClass
    (hdet : (LinearMap.id -
      (HomologicalComplex.homologyMap
        (monodromyChainMap φ.toHomeomorph (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    (a : (TopCat.of (SmoothMappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (𝟙_ (ModuleCat.{0} ℤ)) 1) :
    ∃ n : ℤ, a = n • timeClass φ := by
  obtain ⟨g, hg⟩ := exists_singularKronecker_timeClass_eq_one φ
  set f := ((TopCat.of (SmoothMappingTorus φ)).singularKronecker ℤ 1 a).hom
  refine ⟨f g, TopCat.singularCohomology_one_ext _ fun c ↦ ?_⟩
  rw [map_zsmul]
  -- The pairings are evaluated through `ConcreteCategory.hom`, which is `ModuleCat.Hom.hom`.
  change f c = ModuleCat.Hom.hom
    ((f g : ℤ) • (TopCat.of (SmoothMappingTorus φ)).singularKronecker ℤ 1 (timeClass φ)) c
  -- The pairing with `a` kills the torsion class `c - N(c) • g`, so it sends `c` to `N(c) f(g)`.
  have htor : IsOfFinAddOrder (c - intTimePeriodHom φ c • g) :=
    isOfFinAddOrder_sub_intTimePeriodHom_zsmul φ hdet
      ((singularKronecker_timeClass φ g).symm.trans hg) c
  have hc : f (c - intTimePeriodHom φ c • g) = 0 :=
    IsOfFinAddOrder.eq_zero' (G := ℤ) (f.toAddMonoidHom.isOfFinAddOrder htor)
  rw [map_sub, map_zsmul, sub_eq_zero, smul_eq_mul] at hc
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, hc, smul_eq_mul, mul_comm]
  exact congrArg _ (singularKronecker_timeClass φ c).symm

end TauCeti.SmoothMappingTorus

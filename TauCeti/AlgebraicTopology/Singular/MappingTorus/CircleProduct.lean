/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.AddCircle
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.BaseCircle
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.FirstCohomology
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.SecondCohomology
import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient

/-!
# The first and second cohomology of `(ℝ / pℤ) × Y_φ`

Let `F` be a closed connected oriented surface and `φ : F ≃ₜ F` an orientation-preserving
homeomorphism with `det (1 - φ_*) ≠ 0` on `H₁(F; ℤ)`, so that the mapping torus `Y_φ` has
`b₁(Y_φ) = 1`. The symplectic suspension of an area-preserving `φ` is `X = (ℝ / ℤ)_s × Y_φ`, and
Taubes's line labels on `X` are written in two classes: the pullback `pr₂^* v` of a class
`v ∈ H²(Y_φ; ℤ)` pairing to one with the fibre class, and the class `t = [ds] ⌣ pr₂^* a`, where
`[ds]` is the angular class of the circle factor and `a` generates `H¹(Y_φ; ℤ) ≅ ℤ`; when `a` is
the class `[dt]` of the base circle of `Y_φ`, `t = [ds ∧ dt]`. This file proves that these two
classes are a basis of `H²(X; ℤ)` modulo torsion, keeping every torsion label:

* every class of `H²((ℝ / pℤ) × Y_φ; ℤ)` differs from `m • pr₂^* v + c • t` by an element of finite
  order, for some integers `m` and `c`
  (`TauCeti.MappingTorus.exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd`);
* `m • pr₂^* v + c • t` has finite order only for `m = c = 0`
  (`TauCeti.MappingTorus.isOfFinAddOrder_smul_add_smul_addCircleProd_iff`), so `m` and `c` are
  unique;
* as for every space `Y`, the classes of finite order of `H²((ℝ / pℤ) × Y_φ; ℤ)` are exactly the
  pullbacks of the classes of finite order of `H²(Y_φ; ℤ)`
  (`TopCat.isOfFinAddOrder_iff_exists_singularCohomologyMap_snd_addCircle` with `n = 1`, since
  `H¹(Y_φ; ℤ)` is torsion-free by `TopCat.isAddTorsionFree_singularCohomology_one`).

The first statement is the spanning hypothesis `hspan` of the intersection-form results for the
pair `v, t` in `TauCeti.LinearAlgebra.BilinearForm.HyperbolicPair` and
`TauCeti.Geometry.Symplectic.Manifold.Suspension.Chamber`, such as
`LinearMap.BilinForm.even_apply_self_of_isOfFinAddOrder_span` and
`LinearMap.BilinForm.sigPos_toQuadraticMap_baseChange_eq_one_of_isOfFinAddOrder_span`, applied to
`H = H²(X; ℤ)` with its cohomology `ℤ`-module structure.

The proof combines three computations. The cohomology of a product with a circle splits as
`H²((ℝ / pℤ) × Y; ℤ) ≅ H²(Y; ℤ) × H¹(Y; ℤ)` by slant products
(`TopCat.singularCohomologyAddCircleProdSlantEquiv`), so a basis modulo torsion of each factor
gives one of the product (`TopCat.exists_isOfFinAddOrder_sub_smul_add_smul_addCircle`,
`TopCat.isOfFinAddOrder_smul_add_smul_addCircle_iff`). The factor `H¹(Y_φ; ℤ)` is `ℤ`
(`TauCeti.MappingTorus.cohomologyOneEquiv`) and torsion-free
(`TopCat.isAddTorsionFree_singularCohomology_one`), so a generator has infinite order. The factor
`H²(Y_φ; ℤ)` is `ℤ` modulo torsion, detected by evaluation on the fibre class
(`TauCeti.MappingTorus.isOfFinAddOrder_sub_evalFundamentalClass_smul`). The fibre class is built
from singular chains with coefficients in `ULift ℤ`, so the class `v` is read there through the
change of chain coefficients `TopCat.singularCohomologyChainCoefficientMap` along
`TauCeti.uliftIntIso`, an isomorphism
(`TauCeti.MappingTorus.isOfFinAddOrder_sub_evalFundamentalClass_chainCoefficientMap_smul`).

For the generator `a` one may take the base class `[dt] = proj^* θ_1` of the mapping torus
(`TauCeti.MappingTorus.baseClass`), which generates `H¹(Y_φ; ℤ)` by
`TauCeti.MappingTorus.exists_eq_zsmul_baseClass`; then `t = pr₁^* θ_p ⌣ pr₂^* [dt]`.

Against the homology cross product `[ℝ / pℤ] × y` of the circuit class with a class
`y ∈ H₃(Y_φ; ℤ)`, the cup pairings of the two classes are `v · v = t · t = 0` and
`v · t = t · v = ⟨v ⌣ a, y⟩`
(`TopCat.singularCupPairing_snd_snd_addCircle_singularHomologyCross`,
`TopCat.singularCupPairing_fst_snd_fst_snd_addCircle_singularHomologyCross`,
`TopCat.singularCupPairing_snd_fst_snd_addCircle_singularHomologyCross` and
`TopCat.singularCupPairing_fst_snd_snd_addCircle_singularHomologyCross`). For `a = [dt]` there is
a class `y` with `⟨v ⌣ [dt], y⟩ = ⟨v, i_*[F]⟩ = 1`, one whose image under the Wang connecting
morphism is `±[F]`
(`TauCeti.MappingTorus.exists_singularCupPairing_baseClass_eq_evalFundamentalClass`), so `v, t`
is a hyperbolic pair of the cup pairing against `[ℝ / pℤ] × y`. For the fundamental class `[Y_φ]`
itself, that `⟨v ⌣ a, [Y_φ]⟩ = 1` for a suitable generator `a`, which makes `v, t` a hyperbolic
pair of the intersection form, follows from Poincaré duality on `Y_φ`
(`TauCeti.MappingTorus.exists_forall_eq_zsmul_and_singularCupPairing_eq_one`).

**The first cohomology.** For a path-connected `Y`, the same slant decomposition in degree one,
`H¹((ℝ / pℤ) × Y; ℤ) ≃ H¹(Y; ℤ) × H⁰(Y; ℤ)`, together with `H⁰(Y; ℤ) ≅ ℤ`
(`TauCeti.singularCohomologyZeroEvalEquiv`), extends a basis of `H¹(Y; ℤ)` by `pr₁^* θ_p` to a basis
of `H¹((ℝ / pℤ) × Y; ℤ)` (`TopCat.singularCohomologyOneAddCircleProdBasis`). Since `H¹(Y_φ; ℤ)`
has the basis `[dt]` (`TauCeti.MappingTorus.basisBaseClass`), the angular class `pr₁^* θ_p` of the
circle factor and the base class `pr₂^* [dt]` form a basis of `H¹((ℝ / pℤ) × Y_φ; ℤ)`
(`TauCeti.MappingTorus.basisAddCircleProd`). This only needs a path-connected fibre with
`H₁(F; ℤ)` free of finite rank and `det (1 - φ_*) ≠ 0`. For `p = 1` the basis is `([ds], [dt])`,
in the order of the product homology orientation `e₀ ∧ i[ds] ∧ i[dt] ∧ e₊`. It gives the
coordinates `νₛ, νₜ` in which the Seiberg–Witten wall class of the suspension is `q νₛ νₜ`
(`TauCeti.SmoothMappingTorus.halfCupInsertionForm_two_smul_sub_eq_smul_det`).

**Integral cohomology.** That theorem, and the cup pairing it is computed with, are stated in the
model `TopCat.integralCohomology` of integral cohomology, with chains in `ULift ℤ`. Through the
comparison `TopCat.integralCohomologyEquiv`, which carries integral cup products to cup products
with unit coefficients (`TopCat.integralCohomologyEquiv_integralCup`), the basis reads there as
`TauCeti.MappingTorus.integralBasisAddCircleProd`, and the integral cup product of its two vectors
is the class `t = pr₁^* θ_p ⌣ pr₂^* [dt]`
(`TauCeti.MappingTorus.integralCohomologyEquiv_integralCup_integralBasisAddCircleProd`). For an
integral class `v ∈ H²(Y_φ; ℤ)` pairing to one with the fibre, `pr₂^* v` and this cup product form
a basis of the integral `H²((ℝ / pℤ) × Y_φ; ℤ)` modulo torsion
(`exists_isOfFinAddOrder_sub_smul_add_smul_integralCup_integralBasisAddCircleProd`,
`isOfFinAddOrder_smul_add_smul_integralCup_integralBasisAddCircleProd_iff`, in the namespace
`TauCeti.MappingTorus`):
these are the basis `(aₛ, aₜ)` with `aₛ ⌣ aₜ = t` of the wall class and the spanning hypothesis
`hspan` of the chamber results, in the model where the cup pairing is defined.

## Main results

* `TauCeti.MappingTorus.exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd`: `pr₂^* v` and
  `t` span `H²((ℝ / pℤ) × Y_φ; ℤ)` modulo torsion.
* `TauCeti.MappingTorus.isOfFinAddOrder_smul_add_smul_addCircleProd_iff`: they are independent
  modulo torsion.
* `TauCeti.MappingTorus.basisAddCircleProd`: the basis `(pr₁^* θ_p, pr₂^* [dt])` of
  `H¹((ℝ / pℤ) × Y_φ; ℤ)`.
* `TauCeti.MappingTorus.integralBasisAddCircleProd`: the same basis in integral cohomology, with
  `TauCeti.MappingTorus.integralCohomologyEquiv_integralCup_integralBasisAddCircleProd` its cup
  product.
* `exists_isOfFinAddOrder_sub_smul_add_smul_integralCup_integralBasisAddCircleProd` and
  `isOfFinAddOrder_smul_add_smul_integralCup_integralBasisAddCircleProd_iff`, in the namespace
  `TauCeti.MappingTorus`: `pr₂^* v` and that cup product span the integral `H²` modulo torsion,
  independently.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 3.15 (the Künneth formula) and Example 2.48 (the Wang sequence of a mapping torus).
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex Module

attribute [local instance 1100] ModuleCat.instLinear

namespace TauCeti.MappingTorus

variable {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F)

/-! ### The first cohomology of `(ℝ / pℤ) × Y_φ` -/

section FirstCohomology

variable (p : ℝ) [Fact (0 < p)]

variable [PathConnectedSpace F]
  [Module.Free ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
  [Module.Finite ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]

/-- **The basis `([ds], [dt])` of `H¹((ℝ / pℤ) × Y_φ; ℤ)`.** If `F` is path-connected, `H₁(F; ℤ)`
is free of finite rank and `det (1 - φ_*) ≠ 0` on it, the angular class `pr₁^* θ_p` of the circle
factor and the base class `pr₂^* [dt]` of the mapping torus form a basis, in this order: the basis
`TopCat.singularCohomologyOneAddCircleProdBasis` built from the basis `[dt]` of `H¹(Y_φ; ℤ)`
(`TauCeti.MappingTorus.basisBaseClass`). For `p = 1` these are the classes `[ds]` and `[dt]` of the
symplectic suspension `(ℝ / ℤ)_s × Y_φ`. The basis lives in the cohomology computed from chains
with coefficients in `ℤ`; `TauCeti.MappingTorus.integralBasisAddCircleProd` is the same basis in
`TopCat.integralCohomology`, where the wall class
`TauCeti.SmoothMappingTorus.halfCupInsertionForm_two_smul_sub_eq_smul_det` is stated. -/
def basisAddCircleProd
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    Module.Basis (Fin 2) ℤ
      ((TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCohomology
        (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 1) :=
  -- `basisBaseClass` is a basis of the cohomology with coefficients `ModuleCat.of ℤ ℤ`, used here
  -- for the coefficients `𝟙_ (ModuleCat ℤ)`: the two objects agree by definition.
  (TopCat.singularCohomologyOneAddCircleProdBasis _ (basisBaseClass φ hdet)).reindex
    (finSuccEquiv 1).symm

/-- The first vector of `basisAddCircleProd` is the angular class `[ds] = pr₁^* θ_p`. -/
@[simp]
lemma basisAddCircleProd_zero
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    basisAddCircleProd φ p hdet 0 = TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst
      (TopCat.of (AddCircle p)) (TopCat.of (MappingTorus φ))) 1 (AddCircle.angularClass p) := by
  simp [basisAddCircleProd]

/-- The second vector of `basisAddCircleProd` is the base class `[dt] = pr₂^* [dt]`. -/
@[simp]
lemma basisAddCircleProd_one
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    basisAddCircleProd φ p hdet 1 = TopCat.singularCohomologyMap (M := 𝟙_ (ModuleCat.{0} ℤ))
      (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p)) (TopCat.of (MappingTorus φ))) 1
      (baseClass φ) := by
  simp only [basisAddCircleProd, Module.Basis.reindex_apply, Equiv.symm_symm,
    show finSuccEquiv 1 1 = some 0 from rfl, TopCat.singularCohomologyOneAddCircleProdBasis_some]
  -- `baseClass` has coefficients `ModuleCat.of ℤ ℤ`, read here as `𝟙_ (ModuleCat ℤ)`: the two
  -- objects agree by definition but not syntactically, so `simp` cannot use
  -- `basisBaseClass_apply`.
  exact congrArg _ (basisBaseClass_apply φ hdet 0)

/-- The first coordinate of `x` in `basisAddCircleProd`, the coefficient of `[ds]`, is the value at
any point `y` of the slant product `x / [ℝ / pℤ] ∈ H⁰(Y_φ; ℤ)` by the circuit class. -/
lemma basisAddCircleProd_repr_zero
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    (x : (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCohomology
      (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 1) (y : MappingTorus φ) :
    (basisAddCircleProd φ p hdet).repr x 0 =
      singularCohomologyZeroEval (X := TopCat.of (MappingTorus φ)) y
        (TopCat.singularSlant ℤ (𝟙_ (ModuleCat.{0} ℤ)) _ (TopCat.of (MappingTorus φ))
          (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom 1 0 1 (add_comm 1 0) (AddCircle.fundamentalClass p)
          x) := by
  rw [basisAddCircleProd, Module.Basis.repr_reindex_apply, Equiv.symm_symm, finSuccEquiv_zero,
    TopCat.singularCohomologyOneAddCircleProdBasis_repr_none _ _ _ y]

/-- The second coordinate of `x` in `basisAddCircleProd`, the coefficient of `[dt]`, is the
coordinate in `basisBaseClass` of the slant product `x / [0]` by the class of `0`. -/
@[simp]
lemma basisAddCircleProd_repr_one
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    (x : (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCohomology
      (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 1) :
    (basisAddCircleProd φ p hdet).repr x 1 =
      (basisBaseClass φ hdet).repr
        (TopCat.singularSlant ℤ (𝟙_ (ModuleCat.{0} ℤ)) _ (TopCat.of (MappingTorus φ))
          (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom 0 1 1 (zero_add _)
          (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{0} ℤ)) (0 : AddCircle p) (1 : ℤ)) x)
        0 := by
  rw [basisAddCircleProd, Module.Basis.repr_reindex_apply, Equiv.symm_symm,
    show finSuccEquiv 1 1 = some 0 from rfl,
    TopCat.singularCohomologyOneAddCircleProdBasis_repr_some]

/-- **The basis `([ds], [dt])` of `H¹((ℝ / pℤ) × Y_φ; ℤ)` in integral cohomology**: the basis
`TauCeti.MappingTorus.basisAddCircleProd` read in `TopCat.integralCohomology`, the model of the
cup pairing and of the Seiberg–Witten wall class, through `TopCat.integralCohomologyEquiv`. -/
def integralBasisAddCircleProd
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    Module.Basis (Fin 2) ℤ
      ((TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).integralCohomology 1) :=
  (basisAddCircleProd φ p hdet).map
    ((TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).integralCohomologyEquiv 1).symm

/-- The vectors of `integralBasisAddCircleProd` correspond to those of `basisAddCircleProd`, the
classes `[ds]` and `[dt]`. -/
@[simp]
lemma integralCohomologyEquiv_integralBasisAddCircleProd
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) (i : Fin 2) :
    (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).integralCohomologyEquiv 1
        (integralBasisAddCircleProd φ p hdet i) = basisAddCircleProd φ p hdet i := by
  simp [integralBasisAddCircleProd]

/-- The coordinates of an integral class `x` in `integralBasisAddCircleProd` are those of its
unit-coefficient image in `basisAddCircleProd`, computed by `basisAddCircleProd_repr_zero` and
`basisAddCircleProd_repr_one`. -/
@[simp]
lemma integralBasisAddCircleProd_repr
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    (x : (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).integralCohomology 1) :
    (integralBasisAddCircleProd φ p hdet).repr x = (basisAddCircleProd φ p hdet).repr
      ((TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).integralCohomologyEquiv 1 x) := by
  rw [integralBasisAddCircleProd, Module.Basis.map_repr, LinearEquiv.symm_symm]
  rfl

/-- **The cup product of the basis is `[ds] ⌣ [dt]`.** The integral cup product of the two vectors
of `integralBasisAddCircleProd` is, in unit coefficients, the class
`t = pr₁^* θ_p ⌣ pr₂^* [dt]` of
`TauCeti.MappingTorus.exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd`; for `p = 1` it is
the class `[ds ∧ dt]`. -/
theorem integralCohomologyEquiv_integralCup_integralBasisAddCircleProd
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).integralCohomologyEquiv 2
        ((TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).integralCup 1 1 2 rfl
          (integralBasisAddCircleProd φ p hdet 0) (integralBasisAddCircleProd φ p hdet 1)) =
      (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCup ℤ
        (λ_ (𝟙_ (ModuleCat.{0} ℤ))).inv (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom 1 1 2 rfl
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst (TopCat.of (AddCircle p))
          (TopCat.of (MappingTorus φ))) 1 (AddCircle.angularClass p))
        (TopCat.singularCohomologyMap (M := 𝟙_ (ModuleCat.{0} ℤ)) (CartesianMonoidalCategory.snd
          (TopCat.of (AddCircle p)) (TopCat.of (MappingTorus φ))) 1 (baseClass φ)) := by
  rw [TopCat.integralCohomologyEquiv_integralCup,
    integralCohomologyEquiv_integralBasisAddCircleProd,
    integralCohomologyEquiv_integralBasisAddCircleProd, basisAddCircleProd_zero,
    basisAddCircleProd_one]

end FirstCohomology

variable [Module.Free ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
  [Module.Finite ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]

variable {E : Type} [T2Space F] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E F] [CompactSpace F] [ConnectedSpace F]
  (o : HomologicalOrientation F E 2) (hn : finrank ℝ E = 2)

/-! ### The second cohomology of `(ℝ / pℤ) × Y_φ` modulo torsion -/

variable {p : ℝ} [Fact (0 < p)]

/-- **`H²((ℝ / pℤ) × Y_φ; ℤ)` is spanned modulo torsion by `pr₂^* v` and `θ_p ⌣ pr₂^* a`.** Let `φ`
be an orientation-preserving homeomorphism of a closed connected oriented surface `F` with
`det (1 - φ_*) ≠ 0` on `H₁(F; ℤ)`, let `v ∈ H²(Y_φ; ℤ)` pair to one with the fibre class and let
`a` generate `H¹(Y_φ; ℤ)`. Then every class `x ∈ H²((ℝ / pℤ) × Y_φ; ℤ)` differs from
`m • pr₂^* v + c • (pr₁^* θ_p ⌣ pr₂^* a)` by an element of finite order, for some integers `m`
and `c`, where `θ_p` is the angular class of the circle. For `p = 1`, `θ_1 = [ds]`, and when `a`
is the class `[dt]` of the base circle of `Y_φ` the second class is `t = [ds ∧ dt]`. -/
theorem exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd
    (hφ : o.mapFundamentalClass hn ⟨φ, φ.continuous⟩ = o.fundamentalClass hn)
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    {v : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℤ) 2}
    (hv : o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) (incl φ)
      ((TopCat.of (MappingTorus φ)).singularCohomologyChainCoefficientMap ℤ (ModuleCat.of ℤ ℤ)
        uliftIntIso.hom 2 v) = 1)
    {a : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℤ) 1} (ha : ∀ c, ∃ m : ℤ, c = m • a)
    (x : (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCohomology
      (𝟙_ (ModuleCat.{0} ℤ)) ℤ (ModuleCat.of ℤ ℤ) 2) :
    ∃ m c : ℤ, IsOfFinAddOrder (x -
      (m • TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p))
          (TopCat.of (MappingTorus φ))) 2 v +
        c • (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCup ℤ
          (λ_ (𝟙_ (ModuleCat.{0} ℤ))).inv (λ_ (ModuleCat.of ℤ ℤ)).hom 1 1 2 rfl
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst (TopCat.of (AddCircle p))
            (TopCat.of (MappingTorus φ))) 1 (AddCircle.angularClass p))
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p))
            (TopCat.of (MappingTorus φ))) 1 a))) :=
  TopCat.exists_isOfFinAddOrder_sub_smul_add_smul_addCircle (n := 1) _ _
    (fun b ↦ ⟨_, isOfFinAddOrder_sub_evalFundamentalClass_chainCoefficientMap_smul φ o hn hφ hdet
      hv b⟩)
    (fun c ↦ (ha c).imp fun m hm ↦ by rw [hm, sub_self]; exact IsOfFinAddOrder.zero) x

/-- **`pr₂^* v` and `θ_p ⌣ pr₂^* a` are independent modulo torsion.** Under the hypotheses of
`TauCeti.MappingTorus.exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd`, the class
`m • pr₂^* v + c • (pr₁^* θ_p ⌣ pr₂^* a)` of `H²((ℝ / pℤ) × Y_φ; ℤ)` has finite order only for
`m = c = 0`. So the two classes form a basis of `H²((ℝ / pℤ) × Y_φ; ℤ)` modulo torsion, and the
integers `m` and `c` of the decomposition are unique. -/
theorem isOfFinAddOrder_smul_add_smul_addCircleProd_iff
    (hφ : o.mapFundamentalClass hn ⟨φ, φ.continuous⟩ = o.fundamentalClass hn)
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    {v : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℤ) 2}
    (hv : o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) (incl φ)
      ((TopCat.of (MappingTorus φ)).singularCohomologyChainCoefficientMap ℤ (ModuleCat.of ℤ ℤ)
        uliftIntIso.hom 2 v) = 1)
    {a : (TopCat.of (MappingTorus φ)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℤ) 1} (ha : ∀ c, ∃ m : ℤ, c = m • a) (m c : ℤ) :
    IsOfFinAddOrder
      (m • TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p))
          (TopCat.of (MappingTorus φ))) 2 v +
        c • (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).singularCup ℤ
          (λ_ (𝟙_ (ModuleCat.{0} ℤ))).inv (λ_ (ModuleCat.of ℤ ℤ)).hom 1 1 2 rfl
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst (TopCat.of (AddCircle p))
            (TopCat.of (MappingTorus φ))) 1 (AddCircle.angularClass p))
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p))
            (TopCat.of (MappingTorus φ))) 1 a)) ↔
      m = 0 ∧ c = 0 := by
  have := ChartedSpace.locallyPathConnectedSpace E F
  have : PathConnectedSpace F := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  -- The generator `a` of `H¹(Y_φ; ℤ) ≅ ℤ` is nonzero, and `H¹(Y_φ; ℤ)` is torsion-free.
  obtain ⟨k, hk⟩ := ha ((cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet).symm 1)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact one_ne_zero ((cohomologyOneEquiv φ (ModuleCat.of ℤ ℤ) hdet).symm.map_eq_zero_iff.1
      (hk.trans (zsmul_zero k)))
  have ha' : ∀ m : ℤ, IsOfFinAddOrder (m • a) → m = 0 := fun _ hm ↦
    (IsAddTorsionFree.zsmul_eq_zero_iff_left ha0).1 ((isOfFinAddOrder_iff_eq_zero _).1 hm)
  exact TopCat.isOfFinAddOrder_smul_add_smul_addCircle_iff (n := 1) _ _
    (fun _ hm ↦ eq_zero_of_isOfFinAddOrder_smul_of_evalFundamentalClass_eq_one φ o hn hφ hdet hv hm)
    ha' m c

/-! ### The second cohomology of `(ℝ / pℤ) × Y_φ` in integral cohomology -/

section IntegralCohomology

/- The statements below are about `TopCat.integralCohomology`, which carries the `ℤ`-linear
structure `CategoryTheory.Linear.preadditiveIntLinear`; it takes precedence here over the local
instance `ModuleCat.instLinear` of the unit-coefficient statements above, so that pullbacks of
integral classes are elaborated in integral cohomology. -/
attribute [local instance 1200] Linear.preadditiveIntLinear

/-- Every class of `H²(Y_φ; ℤ)`, read with unit coefficients, differs from a multiple of a class
`v` pairing to one with the fibre by an element of finite order. -/
private theorem exists_isOfFinAddOrder_sub_smul_integralCohomologyEquiv
    (hφ : o.mapFundamentalClass hn ⟨φ, φ.continuous⟩ = o.fundamentalClass hn)
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    {v : (TopCat.of (MappingTorus φ)).integralCohomology 2}
    (hv : o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) (incl φ) v = 1) (b) :
    ∃ m : ℤ,
      IsOfFinAddOrder (b - m • (TopCat.of (MappingTorus φ)).integralCohomologyEquiv 2 v) := by
  set e := (TopCat.of (MappingTorus φ)).integralCohomologyEquiv 2
  refine ⟨o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) (incl φ) (e.symm b), ?_⟩
  simpa using e.toLinearMap.toAddMonoidHom.isOfFinAddOrder
    (isOfFinAddOrder_sub_evalFundamentalClass_smul φ o hn hφ hdet hv (e.symm b))

variable [PathConnectedSpace F]

/-- **`H²((ℝ / pℤ) × Y_φ; ℤ)` is spanned modulo torsion by `pr₂^* v` and `[ds] ⌣ [dt]`.** Let `φ`
be an orientation-preserving homeomorphism of a closed connected oriented surface `F` with
`det (1 - φ_*) ≠ 0` on `H₁(F; ℤ)`, and let `v ∈ H²(Y_φ; ℤ)` pair to one with the fibre class. Then
every integral class `x ∈ H²((ℝ / pℤ) × Y_φ; ℤ)` differs from `m • pr₂^* v + c • (b₀ ⌣ b₁)` by an
element of finite order, for some integers `m` and `c`, where `(b₀, b₁)` is the basis
`TauCeti.MappingTorus.integralBasisAddCircleProd` of `H¹`. This is the integral form of
`TauCeti.MappingTorus.exists_isOfFinAddOrder_sub_smul_add_smul_addCircleProd`, in the model of the
cup pairing. -/
theorem exists_isOfFinAddOrder_sub_smul_add_smul_integralCup_integralBasisAddCircleProd
    (hφ : o.mapFundamentalClass hn ⟨φ, φ.continuous⟩ = o.fundamentalClass hn)
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    {v : (TopCat.of (MappingTorus φ)).integralCohomology 2}
    (hv : o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) (incl φ) v = 1)
    (x : (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).integralCohomology 2) :
    ∃ m c : ℤ, IsOfFinAddOrder (x -
      (m • TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p))
          (TopCat.of (MappingTorus φ))) 2 v +
        c • (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).integralCup 1 1 2 rfl
          (integralBasisAddCircleProd φ p hdet 0) (integralBasisAddCircleProd φ p hdet 1))) := by
  set e := (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).integralCohomologyEquiv 2
  obtain ⟨m, c, h⟩ := TopCat.exists_isOfFinAddOrder_sub_smul_add_smul_addCircle (p := p) (n := 1)
    _ _ (exists_isOfFinAddOrder_sub_smul_integralCohomologyEquiv φ o hn hφ hdet hv)
    (fun c ↦ (exists_eq_zsmul_baseClass φ hdet c).imp fun m hm ↦ by
      rw [hm, sub_self]; exact IsOfFinAddOrder.zero) (e x)
  refine ⟨m, c, ?_⟩
  have h' := e.symm.toLinearMap.toAddMonoidHom.isOfFinAddOrder h
  rw [← TopCat.integralCohomologyEquiv_naturality,
    ← integralCohomologyEquiv_integralCup_integralBasisAddCircleProd φ p hdet] at h'
  simpa [e] using h'

/-- **`pr₂^* v` and `[ds] ⌣ [dt]` are independent modulo torsion.** Under the hypotheses of
`exists_isOfFinAddOrder_sub_smul_add_smul_integralCup_integralBasisAddCircleProd`, the integral
class `m • pr₂^* v + c • (b₀ ⌣ b₁)` has finite order only for `m = c = 0`. So the two
classes form a basis of `H²((ℝ / pℤ) × Y_φ; ℤ)` modulo torsion. -/
theorem isOfFinAddOrder_smul_add_smul_integralCup_integralBasisAddCircleProd_iff
    (hφ : o.mapFundamentalClass hn ⟨φ, φ.continuous⟩ = o.fundamentalClass hn)
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0)
    {v : (TopCat.of (MappingTorus φ)).integralCohomology 2}
    (hv : o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) (incl φ) v = 1) (m c : ℤ) :
    IsOfFinAddOrder
      (m • TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd (TopCat.of (AddCircle p))
          (TopCat.of (MappingTorus φ))) 2 v +
        c • (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).integralCup 1 1 2 rfl
          (integralBasisAddCircleProd φ p hdet 0) (integralBasisAddCircleProd φ p hdet 1)) ↔
      m = 0 ∧ c = 0 := by
  set e := (TopCat.of (AddCircle p) ⊗ TopCat.of (MappingTorus φ)).integralCohomologyEquiv 2
  set eY := (TopCat.of (MappingTorus φ)).integralCohomologyEquiv 2
  -- No nonzero multiple of `v` has finite order: it pairs to `m` with the fibre class.
  have hv' : ∀ m : ℤ, IsOfFinAddOrder (m • eY v) → m = 0 := fun m hm ↦ by
    have h := (isOfFinAddOrder_iff_evalFundamentalClass_eq_zero φ o hn hφ hdet (m • v)).1
      (by simpa [eY] using eY.symm.toLinearMap.toAddMonoidHom.isOfFinAddOrder hm)
    simpa [hv] using h
  -- No nonzero multiple of the base class has finite order: it is a basis vector.
  have ha' : ∀ m : ℤ, IsOfFinAddOrder (m • baseClass φ) → m = 0 := fun m hm ↦
    (IsAddTorsionFree.zsmul_eq_zero_iff_left (by simpa using (basisBaseClass φ hdet).ne_zero 0)).1
      ((isOfFinAddOrder_iff_eq_zero _).1 hm)
  rw [← (TopCat.isOfFinAddOrder_smul_add_smul_addCircle_iff (p := p) (n := 1) _ _ hv' ha' m c),
    ← (show Function.Injective e.toLinearMap.toAddMonoidHom from e.injective).isOfFinAddOrder_iff]
  simp [e, eY, TopCat.integralCohomologyEquiv_naturality,
    integralCohomologyEquiv_integralCup_integralBasisAddCircleProd]

end IntegralCohomology

end TauCeti.MappingTorus

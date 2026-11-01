/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.Point

/-!
# Singular cohomology of a point

The singular cochains of a one-point space `X`, with coefficients `Hom(-, M)` applied to singular
chains with coefficients in `R`, are cochain homotopy equivalent to the module `Hom(R, M)` placed
in degree zero (`TauCeti.pointSingularCochainHomotopyEquiv`). This is the contravariant image of
the chain contraction `TauCeti.pointSingularChainHomotopyEquiv`, so it holds for arbitrary
coefficients: positive-degree singular cohomology of a point vanishes
(`TauCeti.isZero_singularCohomology_point`) without any projectivity, injectivity or
hereditary-ring hypothesis, as a universal coefficient argument would need. In degree zero the
comparison evaluates a cocycle on the unique singular vertex
(`TauCeti.singularCohomologyPointZeroIso`), and it sends the class of a constant cocycle, such as
the unit of the cup product, to its value.

Consequently a nullhomotopic map, which factors through a point up to homotopy, induces zero on
positive-degree singular cohomology (`TopCat.singularCohomologyMap_eq_zero_of_nullhomotopic`),
and positive-degree singular cohomology of a contractible space vanishes
(`TauCeti.isZero_singularCohomology_of_contractibleSpace`). For the open sets of a categorical
cover in the sense of Lusternik and Schnirelmann, whose inclusions are nullhomotopic, this says
that every positive-degree class restricts to zero on each open of the cover, which is the input
to the cup-length lower bound for the Lusternik–Schnirelmann category.

## Main declarations

* `TauCeti.pointSingularCochainHomotopyEquiv`: the cochain homotopy equivalence between the
  singular cochains of a point and `Hom(R, M)` in degree zero, and
  `TauCeti.pointSingularCochainHomotopyEquiv_hom_f_zero_apply`, its formula in degree zero.
* `TauCeti.isZero_singularCohomology_point`: `Hⁿ(pt; M) = 0` for `n ≠ 0`.
* `TauCeti.singularCohomologyPointZeroIso`: `H⁰(pt; M) ≅ Hom(R, M)`, by evaluation on the unique
  vertex (`TauCeti.singularCohomologyPointZeroIso_hom_homologyπ_apply`).
* `TopCat.singularCohomologyMap_eq_zero_of_nullhomotopic` and
  `TauCeti.isZero_singularCohomology_of_contractibleSpace`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 3.1 and 3.2.
* O. Cornea, G. Lupton, J. Oprea, D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, AMS, 2003, Section 1.5, for the cup-length bound.
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  (R : C) (k : Type*) [Ring k] [Linear k C] (M : C)

section Point

variable (X : TopCat.{w}) [Unique X]

/-- **The singular cochains of a point contract onto `Hom(R, M)` in degree zero.** For a
one-point space `X`, the singular cochain complex `Hom(C(X; R), M)` is cochain homotopy
equivalent to the module `Hom(R, M)` placed in degree zero. The forward map evaluates a
zero-cochain on the unique singular vertex. -/
def pointSingularCochainHomotopyEquiv :
    HomotopyEquiv (X.singularCochainComplex R k M)
      ((CochainComplex.single₀ (ModuleCat.{v} k)).obj (ModuleCat.of k (R ⟶ M))) :=
  ((pointSingularChainHomotopyEquiv R X).linearYonedaFunctorMap k M).symm.trans
    (HomotopyEquiv.ofIso (ChainComplex.linearYonedaObjSingle₀Iso k R M))

/-- In degree zero, the contraction of the singular cochains of a point evaluates a cochain on the
unique singular vertex. -/
lemma pointSingularCochainHomotopyEquiv_hom_f_zero_apply
    (σ : (TopCat.toSSet.obj X) _⦋0⦌) (a : ((TopCat.toSSet.obj X).chainComplex R).X 0 ⟶ M) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (ModuleCat.of k (R ⟶ M))).hom
        ((pointSingularCochainHomotopyEquiv R k M X).hom.f 0 a) =
      (TopCat.toSSet.obj X).ιChainComplex σ ≫ a := by
  rw [pointSingularCochainHomotopyEquiv, HomotopyEquiv.trans_hom, HomotopyEquiv.symm_hom,
    HomotopyEquiv.linearYonedaFunctorMap_inv]
  -- The forward map precomposes with the inverse chain contraction and then identifies
  -- `Hom(R[0], M)` with `Hom(R, M)[0]`. Evaluating that composite at `a` is definitional, but
  -- `ConcreteCategory.comp_apply` does not fire: the target of the first map is
  -- `(linearYonedaFunctor k M).obj _`, only defeq to the source `linearYonedaObj` of the second.
  calc _ = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (ModuleCat.of k (R ⟶ M))).hom
          ((ChainComplex.linearYonedaObjSingle₀Iso k R M).hom.f 0
            ((pointSingularChainHomotopyEquiv R X).inv.f 0 ≫ a)) := rfl
    _ = (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 R).inv ≫
          (pointSingularChainHomotopyEquiv R X).inv.f 0 ≫ a :=
        ChainComplex.linearYonedaObjSingle₀Iso_hom_f_zero_apply k R M _
    _ = (TopCat.toSSet.obj X).ιChainComplex σ ≫ a := by
        rw [pointSingularChainHomotopyEquiv_inv_f_zero R X σ, Category.assoc, Iso.inv_hom_id_assoc]

/-- **The positive-degree singular cohomology of a point vanishes**, for arbitrary coefficients. -/
theorem isZero_singularCohomology_point {n : ℕ} (hn : n ≠ 0) :
    IsZero (X.singularCohomology R k M n) :=
  (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℕ) 0
    (ModuleCat.of k (R ⟶ M)) n hn).of_iso
      ((pointSingularCochainHomotopyEquiv R k M X).toHomologyIso n)

/-- The degree-zero singular cohomology of a point is the module `Hom(R, M)`. The class of a
cocycle is sent to its value on the unique singular vertex
(`TauCeti.singularCohomologyPointZeroIso_hom_homologyπ_apply`). -/
def singularCohomologyPointZeroIso : X.singularCohomology R k M 0 ≅ ModuleCat.of k (R ⟶ M) :=
  (pointSingularCochainHomotopyEquiv R k M X).toHomologyIso 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 _

/-- The comparison of the degree-zero singular cohomology of a point with `Hom(R, M)` is induced
by the contraction of the singular cochains. -/
@[reassoc]
lemma homologyπ_singularCohomologyPointZeroIso_hom :
    (X.singularCochainComplex R k M).homologyπ 0 ≫ (singularCohomologyPointZeroIso R k M X).hom =
      (X.singularCochainComplex R k M).iCycles 0 ≫
        (pointSingularCochainHomotopyEquiv R k M X).hom.f 0 ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
            (ModuleCat.of k (R ⟶ M))).hom := by
  simp only [singularCohomologyPointZeroIso, Iso.trans_hom, HomotopyEquiv.toHomologyIso,
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom, HomologicalComplex.cyclesMap_i_assoc]

/-- The comparison of the degree-zero singular cohomology of a point with `Hom(R, M)` sends the
class of a zero-cocycle to its value on the unique singular vertex. -/
lemma singularCohomologyPointZeroIso_hom_homologyπ_apply (σ : (TopCat.toSSet.obj X) _⦋0⦌)
    (a : (X.singularCochainComplex R k M).cycles 0) :
    (singularCohomologyPointZeroIso R k M X).hom ((X.singularCochainComplex R k M).homologyπ 0 a) =
      (TopCat.toSSet.obj X).ιChainComplex σ ≫ (X.singularCochainComplex R k M).iCycles 0 a := by
  rw [← ConcreteCategory.comp_apply, homologyπ_singularCohomologyPointZeroIso_hom]
  exact pointSingularCochainHomotopyEquiv_hom_f_zero_apply R k M X σ _

/-- The class of the constant zero-cocycle with value `e : R ⟶ M`, for instance the unit of the
cup product, corresponds to `e` in the degree-zero singular cohomology of a point. -/
lemma singularCohomologyPointZeroIso_hom_constSingularCocycle (e : R ⟶ M) :
    (singularCohomologyPointZeroIso R k M X).hom
        ((X.singularCochainComplex R k M).homologyπ 0 (X.constSingularCocycle k e)) = e := by
  rw [singularCohomologyPointZeroIso_hom_homologyπ_apply R k M X
    ((X.toSSetObjEquiv _).symm (ContinuousMap.const _ default))]
  simp

end Point

end TauCeti

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  {R : C} {k : Type*} [Ring k] [Linear k C] {M : C}

/-- **A nullhomotopic map induces zero on positive-degree singular cohomology**: up to homotopy
it factors through a point, whose positive-degree cohomology vanishes. -/
theorem singularCohomologyMap_eq_zero_of_nullhomotopic {X Y : TopCat.{w}} {f : X ⟶ Y}
    (hf : f.hom.Nullhomotopic) {n : ℕ} (hn : n ≠ 0) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := M) f n = 0 := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  let p : X ⟶ TopCat.of PUnit.{w + 1} := TopCat.ofHom (ContinuousMap.const X PUnit.unit)
  let s : TopCat.of PUnit.{w + 1} ⟶ Y := TopCat.ofHom (ContinuousMap.const _ y)
  -- The underlying continuous map of `p ≫ s` is `ContinuousMap.const X y` by definition, so `H`
  -- is a homotopy from `f` to `p ≫ s`.
  rw [TopCat.Homotopy.congr_singularCohomologyMap (f := f) (g := p ≫ s) H R k M n,
    singularCohomologyMap_comp,
    (TauCeti.isZero_singularCohomology_point R k M (TopCat.of PUnit.{w + 1}) hn).eq_of_tgt
      (TopCat.singularCohomologyMap s n) 0, zero_comp]

end TopCat

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  (R : C) (k : Type*) [Ring k] [Linear k C] (M : C)

/-- **The positive-degree singular cohomology of a contractible space vanishes**, for arbitrary
coefficients. -/
theorem isZero_singularCohomology_of_contractibleSpace (X : TopCat.{w}) [ContractibleSpace X]
    {n : ℕ} (hn : n ≠ 0) : IsZero (X.singularCohomology R k M n) := by
  rw [IsZero.iff_id_eq_zero, ← TopCat.singularCohomologyMap_id]
  exact TopCat.singularCohomologyMap_eq_zero_of_nullhomotopic (f := 𝟙 X) (id_nullhomotopic X) hn

end TauCeti

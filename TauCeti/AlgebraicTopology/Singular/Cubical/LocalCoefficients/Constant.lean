/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import TauCeti.AlgebraicTopology.Singular.Cubical.ChainComplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.ChainComplex

/-!
# Constant coefficients in cubical chains

Cubical chains with coefficients in the constant local system with fibre `R` are the ordinary
cubical chains with coefficients in `R`.  On unnormalized chains this is the standard equivalence
between the direct sum of copies of `R`, indexed by the singular cubes, and the finitely supported
functions on those cubes.  It sends the summand of a cube to the corresponding singleton chain.

The equivalence commutes with boundaries and carries the degenerate submodule onto the ordinary
degenerate submodule, so it descends to normalized chains and gives an isomorphism of chain
complexes.  This isomorphism is natural in the space.

## Main definitions

* `TauCeti.LocalCoefficientSystem.twistedCubicalChainConstantEquiv`: the equivalence on
  unnormalized chains.
* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainConstantEquiv`: the equivalence on
  normalized chains.
* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainComplexConstantIso`: the induced
  isomorphism of chain complexes.

## Main statements

* `TauCeti.LocalCoefficientSystem.twistedCubicalChainConstantEquiv_ofCube` and
  `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainConstantEquiv_ofCube`: both
  equivalences send a cube with a coefficient to the corresponding singleton chain.
* `TauCeti.LocalCoefficientSystem.twistedCubicalChainConstantEquiv_boundary` and
  `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainConstantEquiv_boundary`: both
  equivalences commute with boundaries.
* `TauCeti.LocalCoefficientSystem.twistedCubicalChainConstantEquiv_degenerate`: it identifies the
  degenerate submodules.
* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainComplexConstantIso_hom_naturality`:
  the chain-complex isomorphism commutes with maps of spaces.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and XIV.
-/

public section

noncomputable section

open CategoryTheory Finsupp

universe u v

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}

variable (R X) in
/-- Cubical chains with coefficients in the constant rank-one local system are ordinary cubical
chains.  The equivalence forgets that the copy of `R` attached to each cube was presented as a
dependent direct summand. -/
def twistedCubicalChainConstantEquiv (n : ℕ) :
    ((constantFunctor X).obj (ModuleCat.of R R)).TwistedCubicalChain n ≃ₗ[R]
      CubicalChain X R n :=
  open scoped Classical in
  DirectSum.congrLinearEquiv (fun c : SingularCube X n ↦
      (eqToIso (constantFunctor_obj_obj X (ModuleCat.of R R)
        (FundamentalGroupoid.mk (c 0)))).toLinearEquiv) ≪≫ₗ
    (finsuppLEquivDirectSum R R (SingularCube X n)).symm

/-- The constant-coefficient equivalence sends a cube with a coefficient to the corresponding
singleton chain. -/
theorem twistedCubicalChainConstantEquiv_ofCube {n : ℕ} (c : SingularCube X n)
    (a : ((constantFunctor X).obj (ModuleCat.of R R)).obj (FundamentalGroupoid.mk (c 0))) :
    twistedCubicalChainConstantEquiv R X n
        (TwistedCubicalChain.ofCube ((constantFunctor X).obj (ModuleCat.of R R)) c a) =
      single c ((eqToIso (constantFunctor_obj_obj X (ModuleCat.of R R)
        (FundamentalGroupoid.mk (c 0)))).hom a) := by
  classical
  rw [twistedCubicalChainConstantEquiv, TwistedCubicalChain.ofCube_eq_lof,
    LinearEquiv.trans_apply, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
  exact finsuppLEquivDirectSum_symm_lof R R (SingularCube X n) c _

/-- On the summand indexed by a cube, the constant-coefficient equivalence is the corresponding
singleton map. -/
theorem twistedCubicalChainConstantEquiv_comp_ofCube {n : ℕ} (c : SingularCube X n) :
    (twistedCubicalChainConstantEquiv R X n).toLinearMap ∘ₗ
        (TwistedCubicalChain.ofCube ((constantFunctor X).obj (ModuleCat.of R R)) c ∘ₗ
          (eqToIso (constantFunctor_obj_obj X (ModuleCat.of R R)
            (FundamentalGroupoid.mk (c 0)))).inv.hom) =
      Finsupp.lsingle c := by
  apply LinearMap.ext
  intro a
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    twistedCubicalChainConstantEquiv_ofCube, Iso.inv_hom_id_apply, Finsupp.lsingle_apply]

/-- The constant-coefficient equivalence commutes with cubical boundaries. -/
theorem twistedCubicalChainConstantEquiv_boundary (n : ℕ) :
    (twistedCubicalChainConstantEquiv R X n).toLinearMap ∘ₗ
        TwistedCubicalChain.boundary ((constantFunctor X).obj (ModuleCat.of R R)) n =
      CubicalChain.boundary X R n ∘ₗ
        (twistedCubicalChainConstantEquiv R X (n + 1)).toLinearMap := by
  refine TwistedCubicalChain.hom_ext fun c ↦ LinearMap.ext fun a ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    TwistedCubicalChain.boundary_ofCube, map_sum, map_zsmul, map_sub,
    twistedCubicalChainConstantEquiv_ofCube, TwistedCubicalChain.ofSubcube_apply,
    CubicalChain.boundary_single]
  simp only [constantFunctor_obj_map]
  simp_rw [SingularCube.comp_face_id]
  simp only [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rfl

/-- Under the constant-coefficient equivalence, the locally coefficiented degenerate chains are
exactly the ordinary degenerate chains. -/
theorem twistedCubicalChainConstantEquiv_degenerate (n : ℕ) :
    (TwistedCubicalChain.degenerate ((constantFunctor X).obj (ModuleCat.of R R)) n).map
        (twistedCubicalChainConstantEquiv R X n).toLinearMap =
      CubicalChain.degenerate X R n := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine TwistedCubicalChain.degenerate_le fun c hc a ↦ ?_
    rw [Submodule.mem_comap]
    rw [LinearEquiv.coe_coe, twistedCubicalChainConstantEquiv_ofCube]
    exact CubicalChain.single_mem_degenerate R hc _
  · rw [CubicalChain.degenerate_def]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    let e := eqToIso (constantFunctor_obj_obj X (ModuleCat.of R R)
      (FundamentalGroupoid.mk (c 0)))
    refine ⟨TwistedCubicalChain.ofCube ((constantFunctor X).obj (ModuleCat.of R R)) c
      (e.inv 1), TwistedCubicalChain.ofCube_mem_degenerate hc (e.inv 1), ?_⟩
    rw [LinearEquiv.coe_coe, twistedCubicalChainConstantEquiv_ofCube]
    exact congrArg (single c) (Iso.inv_hom_id_apply e 1)

variable (R X) in
/-- Normalized cubical chains with coefficients in the constant rank-one local system are ordinary
normalized cubical chains. -/
def normalizedTwistedCubicalChainConstantEquiv (n : ℕ) :
    ((constantFunctor X).obj (ModuleCat.of R R)).NormalizedTwistedCubicalChain n ≃ₗ[R]
      NormalizedCubicalChain X R n :=
  Submodule.Quotient.equiv _ _ (twistedCubicalChainConstantEquiv R X n)
    (twistedCubicalChainConstantEquiv_degenerate n)

/-- The normalized constant-coefficient equivalence sends the class of a chain to the class of
its image under the unnormalized equivalence. -/
@[simp]
theorem normalizedTwistedCubicalChainConstantEquiv_mk {n : ℕ}
    (x : ((constantFunctor X).obj (ModuleCat.of R R)).TwistedCubicalChain n) :
    normalizedTwistedCubicalChainConstantEquiv R X n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (twistedCubicalChainConstantEquiv R X n x) := by
  rw [normalizedTwistedCubicalChainConstantEquiv, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply, LinearEquiv.coe_coe]

/-- The normalized constant-coefficient equivalence sends the class of a cube with a coefficient
to the class of the corresponding singleton chain. -/
theorem normalizedTwistedCubicalChainConstantEquiv_ofCube {n : ℕ} (c : SingularCube X n)
    (a : ((constantFunctor X).obj (ModuleCat.of R R)).obj (FundamentalGroupoid.mk (c 0))) :
    normalizedTwistedCubicalChainConstantEquiv R X n
        (NormalizedTwistedCubicalChain.ofCube ((constantFunctor X).obj (ModuleCat.of R R)) c a) =
      Submodule.Quotient.mk (single c ((eqToIso (constantFunctor_obj_obj X (ModuleCat.of R R)
        (FundamentalGroupoid.mk (c 0)))).hom a)) := by
  rw [NormalizedTwistedCubicalChain.ofCube_apply, normalizedTwistedCubicalChainConstantEquiv_mk,
    twistedCubicalChainConstantEquiv_ofCube]

/-- The normalized constant-coefficient equivalence commutes with normalized cubical boundaries. -/
theorem normalizedTwistedCubicalChainConstantEquiv_boundary (n : ℕ) :
    (normalizedTwistedCubicalChainConstantEquiv R X n).toLinearMap ∘ₗ
        NormalizedTwistedCubicalChain.boundary ((constantFunctor X).obj (ModuleCat.of R R)) n =
      NormalizedCubicalChain.boundary X R n ∘ₗ
        (normalizedTwistedCubicalChainConstantEquiv R X (n + 1)).toLinearMap := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    Submodule.mkQ_apply, NormalizedTwistedCubicalChain.boundary_mk,
    normalizedTwistedCubicalChainConstantEquiv_mk, NormalizedCubicalChain.boundary_mk] using
    congrArg Submodule.Quotient.mk (LinearMap.congr_fun (twistedCubicalChainConstantEquiv_boundary
      (R := R) (X := X) n) x)

/-- The normalized constant-coefficient equivalence is natural in the space. -/
theorem normalizedTwistedCubicalChainConstantEquiv_naturality {Y : TopCat.{v}}
    (f : C(X, Y)) (n : ℕ) :
    (normalizedTwistedCubicalChainConstantEquiv R Y n).toLinearMap ∘ₗ
        NormalizedTwistedCubicalChain.map f
          ((constantFunctor Y).obj (ModuleCat.of R R)) n =
      NormalizedCubicalChain.map R f n ∘ₗ
        (normalizedTwistedCubicalChainConstantEquiv R X n).toLinearMap ∘ₗ
          NormalizedTwistedCubicalChain.coefficientMap
            (pullbackConstantIso f (ModuleCat.of R R)).hom n := by
  refine NormalizedTwistedCubicalChain.hom_ext fun c ↦ LinearMap.ext fun a ↦ ?_
  -- The fibres of the constant systems and of their pullback are all `R` by definition, since
  -- `constantFunctor_obj_obj` is `rfl`; so the transports `(eqToIso _).hom` produced by
  -- `normalizedTwistedCubicalChainConstantEquiv_ofCube` are identities and `a` serves as an
  -- element of `R` throughout.  The component of `pullbackConstantIso` is removed in the last
  -- step by `pullbackConstantIso_hom_app`.
  calc
    _ = (Submodule.Quotient.mk (single (f.comp c) a) : NormalizedCubicalChain Y R n) :=
      (congrArg _ (NormalizedTwistedCubicalChain.map_ofCube c a)).trans
        (normalizedTwistedCubicalChainConstantEquiv_ofCube (f.comp c) a)
    _ = NormalizedCubicalChain.map R f n (Submodule.Quotient.mk (single c a)) :=
      ((NormalizedCubicalChain.map_mk (R := R) f _).trans
        (congrArg _ (CubicalChain.map_single (R := R) f c a))).symm
    _ = NormalizedCubicalChain.map R f n (normalizedTwistedCubicalChainConstantEquiv R X n
          (NormalizedTwistedCubicalChain.ofCube _ c (𝟙 (ModuleCat.of R R) a))) :=
      congrArg _ (normalizedTwistedCubicalChainConstantEquiv_ofCube c _).symm
    _ = _ := congrArg _ ((congrArg (fun b ↦ normalizedTwistedCubicalChainConstantEquiv R X n
          (NormalizedTwistedCubicalChain.ofCube _ c b))
        (ConcreteCategory.congr_hom (pullbackConstantIso_hom_app f _ _) a)).symm.trans
      (congrArg _ (NormalizedTwistedCubicalChain.coefficientMap_ofCube _ c a).symm))

variable {Z : TopCat.{u}}

variable (R Z) in
/-- The normalized cubical chain complex of the constant rank-one local system is the ordinary
normalized cubical chain complex. -/
def normalizedTwistedCubicalChainComplexConstantIso :
    ((constantFunctor Z).obj (ModuleCat.of R R)).normalizedTwistedCubicalChainComplex ≅
      (normalizedCubicalChainComplex R).obj Z := by
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (normalizedTwistedCubicalChainConstantEquiv R Z n).toModuleIso) fun i j hij ↦ by
      obtain rfl : j + 1 = i := hij
      simp only [LinearEquiv.toModuleIso_hom, normalizedTwistedCubicalChainComplex,
        normalizedCubicalChainComplex, normalizedCubicalChainComplexObj, ChainComplex.of_d,
        ← ModuleCat.ofHom_comp]
      exact congrArg ModuleCat.ofHom
        (normalizedTwistedCubicalChainConstantEquiv_boundary (R := R) (X := Z) j).symm

/-- The forward chain-complex isomorphism has the normalized constant-coefficient equivalence as
its component in each degree. -/
@[simp]
theorem normalizedTwistedCubicalChainComplexConstantIso_hom_f (n : ℕ) :
    (normalizedTwistedCubicalChainComplexConstantIso R Z).hom.f n =
      ModuleCat.ofHom (normalizedTwistedCubicalChainConstantEquiv R Z n).toLinearMap :=
  (rfl)

/-- The inverse chain-complex isomorphism has the inverse normalized constant-coefficient
equivalence as its component in each degree. -/
@[simp]
theorem normalizedTwistedCubicalChainComplexConstantIso_inv_f (n : ℕ) :
    (normalizedTwistedCubicalChainComplexConstantIso R Z).inv.f n =
      ModuleCat.ofHom (normalizedTwistedCubicalChainConstantEquiv R Z n).symm.toLinearMap :=
  (rfl)

/-- The chain-complex identification of constant-coefficient cubical chains is natural in the
space. -/
@[reassoc]
theorem normalizedTwistedCubicalChainComplexConstantIso_hom_naturality
    {W : TopCat.{u}} (f : Z ⟶ W) :
    normalizedTwistedCubicalChainComplexMap f.hom
          ((constantFunctor W).obj (ModuleCat.of R R)) ≫
        (normalizedTwistedCubicalChainComplexConstantIso R W).hom =
      normalizedTwistedCubicalChainComplexCoefficientMap
          (pullbackConstantIso f.hom (ModuleCat.of R R)).hom ≫
          (normalizedTwistedCubicalChainComplexConstantIso R Z).hom ≫
          (normalizedCubicalChainComplex R).map f := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, normalizedTwistedCubicalChainComplexMap_f,
    normalizedTwistedCubicalChainComplexCoefficientMap_f,
    normalizedTwistedCubicalChainComplexConstantIso_hom_f, normalizedCubicalChainComplex_map_f]
  exact congrArg ModuleCat.ofHom
    (normalizedTwistedCubicalChainConstantEquiv_naturality (R := R) (f := f.hom) n)

end LocalCoefficientSystem

end TauCeti

end

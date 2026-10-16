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
degenerate submodule, so it descends to normalized chains.

## Main definitions

* `TauCeti.LocalCoefficientSystem.twistedCubicalChainConstantEquiv`: the equivalence on
  unnormalized chains.
* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainConstantEquiv`: the equivalence on
  normalized chains.

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
      CubicalChain X R n := by
  let L := (constantFunctor X).obj (ModuleCat.of R R)
  let e (c : SingularCube X n) : L.obj (FundamentalGroupoid.mk (c 0)) ≅ ModuleCat.of R R :=
    eqToIso (constantFunctor_obj_obj X (ModuleCat.of R R) _)
  let toMap : L.TwistedCubicalChain n →ₗ[R] CubicalChain X R n :=
    TwistedCubicalChain.desc L fun c ↦ Finsupp.lsingle c ∘ₗ (e c).hom.hom
  let invMap : CubicalChain X R n →ₗ[R] L.TwistedCubicalChain n :=
    Finsupp.linearCombination R fun c ↦ TwistedCubicalChain.ofCube L c ((e c).inv 1)
  have hRight : toMap ∘ₗ invMap = LinearMap.id := by
    refine Finsupp.lhom_ext' fun c ↦ LinearMap.ext fun a ↦ ?_
    dsimp only [toMap, invMap]
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply]
    rw [Finsupp.linearCombination_single, map_smul,
      TwistedCubicalChain.desc_ofCube, LinearMap.comp_apply,
      Iso.inv_hom_id_apply]
    simp
  have hLeft : invMap ∘ₗ toMap = LinearMap.id := by
    refine TwistedCubicalChain.hom_ext fun c ↦ LinearMap.ext fun a ↦ ?_
    dsimp only [toMap, invMap]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [TwistedCubicalChain.desc_ofCube, LinearMap.comp_apply, Finsupp.lsingle_apply,
      Finsupp.linearCombination_single, ← map_smul, LinearMap.id_apply]
    congr 1
    calc
      (e c).hom a • (e c).inv 1 = (e c).inv ((e c).hom a • 1) :=
        ((e c).inv.hom.map_smul _ _).symm
      _ = (e c).inv ((e c).hom a) := by rw [smul_eq_mul, mul_one]
      _ = a := Iso.hom_inv_id_apply (e c) a
  exact
    { toLinearMap := toMap
      invFun := invMap
      left_inv := fun x ↦ LinearMap.congr_fun hLeft x
      right_inv := fun x ↦ LinearMap.congr_fun hRight x }

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
  unfold twistedCubicalChainConstantEquiv
  simp only [LinearMap.coe_comp, Function.comp_apply, TwistedCubicalChain.desc_ofCube,
    Iso.inv_hom_id_apply]

/-- The constant-coefficient equivalence commutes with cubical boundaries. -/
theorem twistedCubicalChainConstantEquiv_boundary (n : ℕ) :
    (twistedCubicalChainConstantEquiv R X n).toLinearMap ∘ₗ
        TwistedCubicalChain.boundary ((constantFunctor X).obj (ModuleCat.of R R)) n =
      CubicalChain.boundary X R n ∘ₗ
        (twistedCubicalChainConstantEquiv R X (n + 1)).toLinearMap := by
  unfold twistedCubicalChainConstantEquiv constantFunctor
  refine TwistedCubicalChain.hom_ext fun c ↦ LinearMap.ext fun a ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, TwistedCubicalChain.boundary_ofCube,
    map_sum, map_zsmul, map_sub, TwistedCubicalChain.desc_ofCube,
    TwistedCubicalChain.ofSubcube_apply, Finsupp.lsingle_apply,
    CubicalChain.boundary_single]
  simp only [Int.reduceNeg, ContinuousMap.comp_apply, Functor.const_obj_obj,
    Functor.const_obj_map, ModuleCat.hom_id, LinearMap.id_coe, id_eq]
  simp_rw [SingularCube.comp_face_id]
  simp only [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one]

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
    unfold twistedCubicalChainConstantEquiv
    dsimp only
    rw [TwistedCubicalChain.desc_ofCube, LinearMap.comp_apply,
      Finsupp.lsingle_apply]
    exact CubicalChain.single_mem_degenerate R hc _
  · rw [CubicalChain.degenerate_def]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    let e := eqToIso (constantFunctor_obj_obj X (ModuleCat.of R R)
      (FundamentalGroupoid.mk (c 0)))
    refine ⟨TwistedCubicalChain.ofCube ((constantFunctor X).obj (ModuleCat.of R R)) c
      (e.inv 1), TwistedCubicalChain.ofCube_mem_degenerate hc (e.inv 1), ?_⟩
    unfold twistedCubicalChainConstantEquiv
    dsimp only
    rw [TwistedCubicalChain.desc_ofCube, LinearMap.comp_apply,
      Finsupp.lsingle_apply]
    exact congrArg (single c) (Iso.inv_hom_id_apply e 1)

variable (R X) in
/-- Normalized cubical chains with coefficients in the constant rank-one local system are ordinary
normalized cubical chains. -/
def normalizedTwistedCubicalChainConstantEquiv (n : ℕ) :
    ((constantFunctor X).obj (ModuleCat.of R R)).NormalizedTwistedCubicalChain n ≃ₗ[R]
      NormalizedCubicalChain X R n :=
  Submodule.Quotient.equiv _ _ (twistedCubicalChainConstantEquiv R X n)
    (twistedCubicalChainConstantEquiv_degenerate n)

end LocalCoefficientSystem

end TauCeti

end

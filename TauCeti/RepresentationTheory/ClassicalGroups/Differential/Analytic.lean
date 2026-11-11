/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Rational.Analytic
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Differential
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions.Analytic
import TauCeti.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Analytic and algebraic differentials of rational representations

For a rational representation of the complex general linear group, differentiation of its
holomorphic action at the identity agrees with the algebraic differential obtained from its
coordinate-algebra comodule. The comparison uses the native open-submanifold charts on `GLₙ(ℂ)`.

## Main results

* `TauCeti.IsRationalRep.mvfderiv_dual_apply_one`: the comparison for matrix coefficients,
  without a norm on the representation space.
* `TauCeti.IsRationalRep.mvfderiv_apply_one`: the comparison for the orbit of each vector.
* `TauCeti.IsRationalRep.mvfderiv_toContinuousLinearMap_one`: the operator-valued comparison.
* `TauCeti.IsRationalRep.exists_linearEquiv_mvfderiv_glIrreducible`: the actual analytic
  differential intertwines with the action on the named highest-weight module.

## References

* `TauCeti.RepresentationTheory.ClassicalGroups.Weight.Differential`, for the rational
  highest-weight classification used in the analytic intertwining statement.

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  §3.5, Theorem 3.28: the induced Lie algebra map is the derivative at the identity.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter III, §8, Propositions (8.6)–(8.7), pp.154–155, for holomorphic representations of the
  classical complexifications.
-/

public section

open scoped ContDiff Manifold Matrix.Norms.Operator
open Matrix Manifold WithConv
attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance 100] LieRing.ofAssociativeRing
noncomputable section

namespace TauCeti.GeneralLinear

variable {n : ℕ}

local notation "O" => coordinateHopfAlgebra ℂ n
local notation "I" => 𝓘(ℂ, Matrix (Fin n) (Fin n) ℂ)

private def coordinateValue (f : O) (g : GL (Fin n) ℂ) : ℂ :=
  (generalLinearToPoint n g).ofConv f

private theorem smooth_coordinateValue (f : O) : ContMDiff I 𝓘(ℂ) ω (coordinateValue f) :=
  TauCeti.Matrix.GeneralLinearGroup.contMDiff_of_mem_rationalFunctions
    (mem_rationalFunctions_iff_exists_generalLinearToPoint_apply_eq.mpr ⟨f, fun _ => rfl⟩)

private theorem coordinateValue_one (f : O) :
    coordinateValue f (1 : GL (Fin n) ℂ) = Coalgebra.counit (R := ℂ) f := by
  simp only [coordinateValue, generalLinearToPoint_one, AlgHom.convOne_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

private def analyticTangent (v : TangentSpace I (1 : GL (Fin n) ℂ)) :
    Derivation ℂ O (Bialgebra.CounitAlgebra ℂ O ℂ) :=
  Derivation.mk'
    { toFun := fun f => (Bialgebra.CounitAlgebra.algEquivSelf ℂ O ℂ).symm
        (mvfderiv I (coordinateValue f) 1 v)
      map_add' := fun f g => by
        apply (Bialgebra.CounitAlgebra.algEquivSelf ℂ O ℂ).injective
        simp only [map_add, AlgEquiv.apply_symm_apply]
        have he : coordinateValue (f + g) = coordinateValue f + coordinateValue g :=
          funext fun a => map_add (generalLinearToPoint n a).ofConv f g
        rw [he, mvfderiv_add ((smooth_coordinateValue f).mdifferentiable (by simp) 1)
          ((smooth_coordinateValue g).mdifferentiable (by simp) 1)]
        exact add_apply _ _ v
      map_smul' := fun c f => by
        apply (Bialgebra.CounitAlgebra.algEquivSelf ℂ O ℂ).injective
        simp only [map_smul, AlgEquiv.apply_symm_apply]
        have he : coordinateValue (c • f) = c • coordinateValue f :=
          funext fun a => (generalLinearToPoint (R := ℂ) n a).ofConv.toLinearMap.map_smul c f
        rw [he, TauCeti.mvfderiv_const_smul_field]
        exact Pi.smul_apply c (mvfderiv I (coordinateValue f) 1) v }
    (fun f g => by
      apply (Bialgebra.CounitAlgebra.algEquivSelf ℂ O ℂ).injective
      simp only [map_add, Bialgebra.CounitAlgebra.algEquivSelf_smul,
        Algebra.algebraMap_self, RingHom.id_apply]
      -- Evaluate the constructor's linear map before transporting the result.
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      simp only [AlgEquiv.apply_symm_apply]
      have he : coordinateValue (f * g) = coordinateValue f * coordinateValue g :=
        funext fun a => map_mul (generalLinearToPoint n a).ofConv f g
      rw [he, mvfderiv_mul ((smooth_coordinateValue f).mdifferentiable (by simp) 1)
        ((smooth_coordinateValue g).mdifferentiable (by simp) 1)]
      simp only [add_apply, smul_apply, smul_eq_mul,
        coordinateValue_one])

private theorem analyticTangent_apply (v : TangentSpace I (1 : GL (Fin n) ℂ)) (f : O) :
    Bialgebra.CounitAlgebra.algEquivSelf ℂ O ℂ (analyticTangent v f) =
      mvfderiv I (coordinateValue f) 1 v := by
  rw [analyticTangent, Derivation.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    AlgEquiv.apply_symm_apply]

private theorem tangentMatrix_analyticTangent (v : TangentSpace I (1 : GL (Fin n) ℂ)) :
    tangentMatrix n (analyticTangent v) =
      mvfderiv I (fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ)) 1 v := by
  ext i j
  rw [tangentMatrix_apply, analyticTangent_apply]
  have he : coordinateValue (coordinateHopfAlgebraAlgEquiv ℂ n
      (coordinateRingMap ℂ n (MvPolynomial.X (i, j)))) =
      (fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) i j) :=
    funext fun g => generalLinearToPoint_apply n g i j
  rw [he]
  let e := (Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap
  exact e.mvfderiv_comp_apply
    ((Units.contMDiff_val (𝕜 := ℂ) (R := Matrix (Fin n) (Fin n) ℂ) (n := ω)).mdifferentiable
      (by simp) 1) v

private theorem analyticTangent_eq (v : TangentSpace I (1 : GL (Fin n) ℂ)) :
    analyticTangent v = (tangentLieEquivMatrix (R := ℂ) (B := ℂ) n).symm v := by
  have hv : mvfderiv I (fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ)) 1 v = v := by
    rw [Units.mvfderiv_val]
    exact ContinuousLinearMap.id_apply v
  have h := (tangentMatrix_analyticTangent v).trans hv
  rw [← tangentLieEquivMatrix_apply] at h
  exact (tangentLieEquivMatrix (R := ℂ) (B := ℂ) n).toLinearEquiv.eq_symm_apply.mpr h

end TauCeti.GeneralLinear

namespace TauCeti.IsRationalRep

open GeneralLinear

variable {n : ℕ}

local notation "O" => coordinateHopfAlgebra ℂ n
local notation "I" => 𝓘(ℂ, Matrix (Fin n) (Fin n) ℂ)

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- The derivative of each matrix coefficient at the identity is the coefficient of the
algebraic differential. No norm on the representation space is required. -/
theorem mvfderiv_dual_apply_one (hρ : IsRationalRep ρ) (φ : Module.Dual ℂ W) (w : W)
    (v : TangentSpace I (1 : GL (Fin n) ℂ)) :
    mvfderiv I (fun g : GL (Fin n) ℂ => φ (ρ g w)) 1 v =
      φ (hρ.differential v w) := by
  let _ := hρ.comodule
  have hc : coordinateValue (Comodule.matrixCoefficient (R := ℂ) (C := O) φ w) =
      (fun g : GL (Fin n) ℂ => φ (ρ g w)) := by
    funext g
    rw [coordinateValue, Comodule.apply_matrixCoefficient,
      hρ.basePointsRepresentation_comodule]
  calc
    _ = Bialgebra.CounitAlgebra.algEquivSelf ℂ O ℂ
        (analyticTangent v (Comodule.matrixCoefficient (R := ℂ) (C := O) φ w)) := by
      rw [analyticTangent_apply, hc]
    _ = φ (Comodule.differential (R := ℂ) (H := O) (M := W) (analyticTangent v) w) :=
      Derivation.apply_matrixCoefficient _ φ w
    _ = _ := by
      rw [analyticTangent_eq]
      exact congrArg (fun L : Module.End ℂ W => φ (L w))
        (hρ.differential_apply (v : Matrix (Fin n) (Fin n) ℂ)).symm

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {σ : Representation ℂ (GL (Fin n) ℂ) V}

/-- The derivative at the identity of the orbit of a vector agrees with the algebraic
differential of the rational representation. -/
theorem mvfderiv_apply_one (hσ : IsRationalRep σ) (w : V)
    (v : TangentSpace I (1 : GL (Fin n) ℂ)) :
    mvfderiv I (fun g : GL (Fin n) ℂ => σ g w) 1 v =
      hσ.differential v w := by
  let _ : FiniteDimensional ℂ V := hσ.finite
  have hact : MDifferentiableAt I 𝓘(ℂ, V) (fun g : GL (Fin n) ℂ => σ g w) 1 := by
    have ha := (ContinuousLinearMap.apply ℂ V w).contDiff.contMDiff.comp
      hσ.contMDiff_toContinuousLinearMap
    exact (ha.congr (fun g => Module.End.toContinuousLinearMap_apply _ _)).mdifferentiable
      (by simp) 1
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro φ
  calc
    _ = mvfderiv I (fun g : GL (Fin n) ℂ => φ (σ g w)) 1 v :=
      (φ.mvfderiv_comp_apply hact v).symm
    _ = _ := mvfderiv_dual_apply_one hσ φ.toLinearMap w v

/-- The operator-valued manifold derivative at the identity is the algebraic differential,
viewed as a continuous operator. -/
theorem mvfderiv_toContinuousLinearMap_one (hσ : IsRationalRep σ)
    (v : TangentSpace I (1 : GL (Fin n) ℂ)) :
    let _ : FiniteDimensional ℂ V := hσ.finite
    mvfderiv I (fun g : GL (Fin n) ℂ => Module.End.toContinuousLinearMap V (σ g)) 1 v =
      Module.End.toContinuousLinearMap V (hσ.differential v) := by
  let _ : FiniteDimensional ℂ V := hσ.finite
  ext w
  calc
    _ = mvfderiv I (fun g : GL (Fin n) ℂ => σ g w) 1 v := by
      have he := (ContinuousLinearMap.apply ℂ V w).mvfderiv_comp_apply
        (hσ.contMDiff_toContinuousLinearMap.mdifferentiable (by simp) 1) v
      simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
        Module.End.toContinuousLinearMap_apply] using he.symm
    _ = _ := by rw [mvfderiv_apply_one hσ, Module.End.toContinuousLinearMap_apply]


/-- An irreducible rational representation with highest weight `λ` has a linear equivalence
with the named highest-weight module that intertwines the manifold derivative of its action. -/
theorem exists_linearEquiv_mvfderiv_glIrreducible (hσ : IsRationalRep σ)
    [σ.IsIrreducible] {l : DominantWeight n} {w : V} (hw0 : w ≠ 0)
    (hwl : w ∈ weightSpace σ l.1)
    (hw : ∀ (i j : Fin n) (hij : i < j) (c : ℂ), σ (transvectionUnit hij.ne c) w = w) :
    ∃ e : V ≃ₗ[ℂ] glIrreducible n (fun i ↦ (l.1 i : ℂ)),
      ∀ (X : Matrix (Fin n) (Fin n) ℂ) (v : V),
        e (mvfderiv 𝓘(ℂ, Matrix (Fin n) (Fin n) ℂ)
          (fun g : GL (Fin n) ℂ => σ g v) 1 X) = ⁅X, e v⁆ := by
  let _ := LieRingModule.compLieHom V hσ.differential
  obtain ⟨e⟩ := hσ.nonempty_lieModuleEquiv_glIrreducible hw0 hwl hw
  refine ⟨e.toLinearEquiv, fun X v => ?_⟩
  calc
    _ = e (hσ.differential X v) := congrArg e (hσ.mvfderiv_apply_one v X)
    _ = _ := e.map_lie X v

end Normed

end TauCeti.IsRationalRep

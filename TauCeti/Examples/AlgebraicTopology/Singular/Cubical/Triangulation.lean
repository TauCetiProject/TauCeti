/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Triangulation.Shuffle
public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalized
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Native endpoint and sign clients

These clients distinguish the positive integral reference from the native cubical boundary,
and distinguish raw singular chains from any proposed normalized descent. Noncommutative
matrix coefficients, the zero ring and the actual empty space are retained.
-/

public section
noncomputable section
open CategoryTheory Limits Simplicial Equiv Equiv.Perm Convexity
open TauCeti.CubicalChain TauCeti.SingularCube
namespace TauCeti.Examples.OrderedCubicalTriangulation

/-- The actual positive coordinate interval cube. -/
def intervalCube : SingularCube (TopCat.of unitInterval) 1 :=
  ⟨fun x ↦ x 0, continuous_apply 0⟩

/-- The literal positive interval is the existing singular interval simplex. -/
lemma positive_interval :
    orderedTriangulation (TopCat.of unitInterval) (ModuleCat.of ℤ ℤ) 1
      (Finsupp.single intervalCube 1) =
      ((TopCat.toSSet.obj (TopCat.of unitInterval)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        (TauCeti.TopCat.simplex₁ (ContinuousMap.id unitInterval))).hom 1 := by
  rw [orderedTriangulation_single, orderedChain_one]
  rfl

/-- The native degree-one map has the opposite sign from the positive interval reference. -/
lemma native_negative_interval :
    nativeOrderedTriangulation (TopCat.of unitInterval) (ModuleCat.of ℤ ℤ) 1
      (Finsupp.single intervalCube 1) =
      -(((TopCat.toSSet.obj (TopCat.of unitInterval)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        (TauCeti.TopCat.simplex₁ (ContinuousMap.id unitInterval))).hom 1) := by
  rw [nativeOrderedTriangulation_apply, positive_interval]
  simp only [pow_one, neg_one_zsmul]

/-- Positive triangulation has endpoint boundary `[1] − [0]`. -/
lemma positive_interval_boundary :
    (((TopCat.toSSet.obj (TopCat.of unitInterval)).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0).hom
      (orderedTriangulation (TopCat.of unitInterval) (ModuleCat.of ℤ ℤ) 1
        (Finsupp.single intervalCube 1)) =
      ((TopCat.toSSet.obj (TopCat.of unitInterval)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        (TopCat.toSSetObj₀Equiv.symm 1)).hom 1 -
      ((TopCat.toSSet.obj (TopCat.of unitInterval)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        (TopCat.toSSetObj₀Equiv.symm 0)).hom 1 := by
  rw [positive_interval]
  have hc := SSet.ιChainComplex_d (TopCat.toSSet.obj (TopCat.of unitInterval))
    (ModuleCat.of ℤ ℤ)
      (TauCeti.TopCat.simplex₁ (X := TopCat.of unitInterval) (ContinuousMap.id unitInterval))
  have hc' : (TopCat.toSSet.obj (TopCat.of unitInterval)).ιChainComplex
      (R := ModuleCat.of ℤ ℤ)
      (TauCeti.TopCat.simplex₁ (ContinuousMap.id unitInterval)) ≫
      ((TopCat.toSSet.obj (TopCat.of unitInterval)).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0 =
        (TopCat.toSSet.obj (TopCat.of unitInterval)).ιChainComplex
          (TopCat.toSSetObj₀Equiv.symm 1) -
        (TopCat.toSSet.obj (TopCat.of unitInterval)).ιChainComplex
          (TopCat.toSSetObj₀Equiv.symm 0) := by
    simpa only [Nat.zero_add, Fin.succ_zero_eq_one, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      pow_zero, pow_one, one_smul, neg_one_zsmul, add_zero, sub_eq_add_neg,
      TauCeti.TopCat.δ_zero_simplex₁, TauCeti.TopCat.δ_one_simplex₁,
      ContinuousMap.id_apply] using hc
  have h := congrArg (fun f ↦ f.hom (1 : ℤ)) hc'
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_sub, LinearMap.sub_apply] using h

/-- The native degree-one boundary is `[0] − [1]`, rather than the positive reference. -/
lemma native_interval_boundary :
    (((TopCat.toSSet.obj (TopCat.of unitInterval)).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0).hom
      (nativeOrderedTriangulation (TopCat.of unitInterval) (ModuleCat.of ℤ ℤ) 1
        (Finsupp.single intervalCube 1)) =
      ((TopCat.toSSet.obj (TopCat.of unitInterval)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        (TopCat.toSSetObj₀Equiv.symm 0)).hom 1 -
      ((TopCat.toSSet.obj (TopCat.of unitInterval)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        (TopCat.toSSetObj₀Equiv.symm 1)).hom 1 := by
  rw [nativeOrderedTriangulation_apply]
  simp only [pow_one, neg_one_zsmul, map_neg]
  rw [positive_interval_boundary, neg_sub]

/-- The degree-zero law applies to an actual point, and preserves its coefficient. -/
lemma point_augmentation (a : ℤ) :
    TauCeti.singularAugment ℤ (TopCat.of PUnit)
      (orderedTriangulation (TopCat.of PUnit) (ModuleCat.of ℤ ℤ) 0
        (Finsupp.single (SingularCube.point PUnit.unit) a)) = a :=
  singularAugment_orderedTriangulation_single _ _

private lemma perm_two_cases (π : Perm (Fin 2)) : π = 1 ∨ π = swap 0 1 := by
  fin_cases π <;> decide

/-- The square is literally the two ordered triangular singular simplices, with opposite signs. -/
lemma square_two_triangles :
    (orderedChain (X := TopCat.of (Fin 2 → unitInterval)) (ContinuousMap.id (Fin 2 →
      unitInterval)) (ModuleCat.of ℤ ℤ)).hom 1 =
      ((TopCat.toSSet.obj (TopCat.of (Fin 2 → unitInterval))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ)
        (((TopCat.of (Fin 2 → unitInterval)).toSSetObjEquiv _).symm (staircaseSimplex 1))).hom 1 -
      ((TopCat.toSSet.obj (TopCat.of (Fin 2 → unitInterval))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ)
        (((TopCat.of (Fin 2 → unitInterval)).toSSetObjEquiv _).symm
          (staircaseSimplex (swap 0 1)))).hom 1 := by
  simp only [orderedChain_eq_sum, ContinuousMap.id_comp, Units.smul_def,
    ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul]
  have hu : (Finset.univ : Finset (Perm (Fin 2))) = {1, swap 0 1} := by
    ext π
    simpa using perm_two_cases π
  rw [hu, Finset.sum_pair (by decide)]
  simp only [Perm.sign_one, Units.val_one, one_zsmul,
    Perm.sign_swap (show (0 : Fin 2) ≠ 1 by decide), Units.val_neg,
    neg_one_zsmul, sub_eq_add_neg, LinearMap.neg_apply]

/-- The two actual triangles have exactly the same geometric diagonal face. -/
lemma square_diagonal :
    (staircaseSimplex (swap (0 : Fin 2) 1)).comp
      ⟨StdSimplex.map (1 : Fin 3).succAbove, by fun_prop⟩ =
      (staircaseSimplex (1 : Perm (Fin 2))).comp
        ⟨StdSimplex.map (1 : Fin 3).succAbove, by fun_prop⟩ := by
  have h0 : (0 : Fin 1).castSucc = (0 : Fin 2) := rfl
  have h1 : (0 : Fin 1).succ = (1 : Fin 2) := rfl
  have h2 : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
  apply ContinuousMap.ext
  intro w
  simpa only [one_mul, h0, h1, h2, ContinuousMap.comp_apply, ContinuousMap.coe_mk] using
    staircaseSimplex_mul_swap_face (1 : Perm (Fin 2)) (0 : Fin 1) w

/-- The square boundary retains the ordered right, left, top and bottom edges. -/
lemma square_boundary :
    orderedChain (ContinuousMap.id (Fin 2 → unitInterval)) (ModuleCat.of ℤ ℤ) ≫
      ((TopCat.toSSet.obj (TopCat.of (Fin 2 → unitInterval))).chainComplex
        (ModuleCat.of ℤ ℤ)).d 2 1 =
      (orderedChain (SingularCube.face 0 1
        (ContinuousMap.id (Fin 2 → unitInterval))) (ModuleCat.of ℤ ℤ) -
       orderedChain (SingularCube.face 0 0
        (ContinuousMap.id (Fin 2 → unitInterval))) (ModuleCat.of ℤ ℤ)) -
      (orderedChain (SingularCube.face 1 1
        (ContinuousMap.id (Fin 2 → unitInterval))) (ModuleCat.of ℤ ℤ) -
       orderedChain (SingularCube.face 1 0
        (ContinuousMap.id (Fin 2 → unitInterval))) (ModuleCat.of ℤ ℤ)) := by
  simpa only [Nat.reduceAdd, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_one_zsmul, sub_eq_add_neg, neg_add_rev, neg_neg] using orderedChain_boundary (X
      := TopCat.of (Fin 2 → unitInterval)) (ContinuousMap.id (Fin 2 → unitInterval)) (ModuleCat.of
        ℤ ℤ)

/-- The empty source has no raw cubical chains, in every degree. -/
lemma empty_chains (n : ℕ) (a : SingularCube (TopCat.of PEmpty) n →₀ ℤ) : a = 0 := by
  ext c
  exact (c 0).elim

/-- On the actual empty source both triangulations vanish. -/
lemma empty_orderedTriangulation (n : ℕ) (a : SingularCube (TopCat.of PEmpty) n →₀ ℤ) :
    orderedTriangulation (TopCat.of PEmpty) (ModuleCat.of ℤ ℤ) n a = 0 ∧
      nativeOrderedTriangulation (TopCat.of PEmpty) (ModuleCat.of ℤ ℤ) n a = 0 := by
  rw [empty_chains n a]
  simp only [map_zero, and_self]

/-- The zero ring is admitted literally, without any nontriviality hypothesis. -/
lemma zero_ring (n : ℕ) (a : SingularCube (TopCat.of PUnit) n →₀ ZMod 1) :
    nativeOrderedTriangulation (TopCat.of PUnit) (ModuleCat.of (ZMod 1) (ZMod 1)) n a = 0 := by
  have ha : a = 0 := Subsingleton.elim _ _
  rw [ha, map_zero]

/-- The constant interval is an actual degenerate cubical generator. -/
def constantInterval : SingularCube (TopCat.of PUnit) 1 := ContinuousMap.const _ PUnit.unit

/-- The native normalized cubical quotient kills the constant interval. -/
lemma constantInterval_normalized :
    NormalizedCubicalChain.ofCube (TopCat.of PUnit) ℤ constantInterval = 0 := by
  apply NormalizedCubicalChain.ofCube_eq_zero
  apply SingularCube.isDegenerate_iff.mpr
  refine ⟨0, SingularCube.isDegenerateAt_iff.mpr ?_⟩
  intro x t
  rfl

/-- Raw singular chains retain the nonzero degenerate singular simplex. -/
lemma constantInterval_raw_ne_zero :
    orderedTriangulation (TopCat.of PUnit) (ModuleCat.of ℤ ℤ) 1
      (Finsupp.single constantInterval 1) ≠ 0 := by
  rw [orderedTriangulation_single, orderedChain_one]
  intro h
  have hd := congrArg (TauCeti.chainsDesc (fun _ ↦ (1 : ℤ))) h
  rw [TauCeti.chainsDesc_simplexChain_one] at hd
  have hz := (TauCeti.chainsDesc (k := ℤ) (X := TopCat.of PUnit) (n := 1)
    (fun _ ↦ (1 : ℤ))).map_zero
  exact one_ne_zero (hd.trans hz)

/-- No map out of the normalized cubical quotient can equal this raw positive
  triangulation. -/
lemma no_raw_normalized_descent :
    ¬ ∃ L : NormalizedCubicalChain (TopCat.of PUnit) ℤ 1 →ₗ[ℤ]
      (((TopCat.toSSet.obj (TopCat.of PUnit)).chainComplex (ModuleCat.of ℤ ℤ)).X 1),
        ∀ c, L (NormalizedCubicalChain.ofCube (TopCat.of PUnit) ℤ c) =
          orderedTriangulation (TopCat.of PUnit) (ModuleCat.of ℤ ℤ) 1 (Finsupp.single c 1) := by
  rintro ⟨L, hL⟩
  have h := hL constantInterval
  rw [constantInterval_normalized, map_zero] at h
  exact constantInterval_raw_ne_zero h.symm

/-- Matrix coefficients form a genuinely noncommutative coefficient ring. -/
def matrixUnit (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℤ := Matrix.single i j 1

/-- The matrix coefficient test cannot be reduced to commutative scalar multiplication. -/
lemma matrixUnits_do_not_commute : matrixUnit 0 1 * matrixUnit 1 0 ≠
    matrixUnit 1 0 * matrixUnit 0 1 := by
  intro h
  have h00 := congrArg (fun a ↦ a 0 0) h
  norm_num [matrixUnit, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single] at h00

/-- Evaluation of a native coefficient module over the noncommutative matrix ring. -/
def matrixCoefficientEval :
    ModuleCat.of (Matrix (Fin 2) (Fin 2) ℤ) (Fin 2 → Matrix (Fin 2) (Fin 2) ℤ) ⟶
      ModuleCat.of (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ) :=
  ModuleCat.ofHom (LinearMap.proj 0)

/-- Positive triangulation commutes with a concrete noncommutative module map in every
  degree. -/
lemma matrix_coefficient_naturality (n : ℕ)
    (a : SingularCube (TopCat.of unitInterval) n →₀ (Fin 2 → Matrix (Fin 2) (Fin 2) ℤ)) :
    ((((SSet.chainComplexFunctor (ModuleCat (Matrix (Fin 2) (Fin 2) ℤ))).map
      matrixCoefficientEval).app (TopCat.toSSet.obj (TopCat.of unitInterval))).f n).hom
      (orderedTriangulation (TopCat.of unitInterval) _ n a) =
        orderedTriangulation (TopCat.of unitInterval) _ n
          (Finsupp.mapRange.linearMap matrixCoefficientEval.hom a) := by
  exact LinearMap.congr_fun (orderedTriangulation_coefficient_naturality matrixCoefficientEval n) a

/-- The sign-corrected map retains that same actual noncommutative coefficient naturality. -/
lemma matrix_native_coefficient_naturality (n : ℕ)
    (a : SingularCube (TopCat.of unitInterval) n →₀ (Fin 2 → Matrix (Fin 2) (Fin 2) ℤ)) :
    ((((SSet.chainComplexFunctor (ModuleCat (Matrix (Fin 2) (Fin 2) ℤ))).map
      matrixCoefficientEval).app (TopCat.toSSet.obj (TopCat.of unitInterval))).f n).hom
      (nativeOrderedTriangulation (TopCat.of unitInterval) _ n a) =
        nativeOrderedTriangulation (TopCat.of unitInterval) _ n
          (Finsupp.mapRange.linearMap matrixCoefficientEval.hom a) := by
  exact LinearMap.congr_fun (nativeOrderedTriangulation_coefficient_naturality
    matrixCoefficientEval n) a

/-- The literal integral comparison is available in a high dimension without new hypotheses. -/
lemma integral_dimension_seven :
    iteratedIntegralShuffle 7 =
      (orderedChain (X := TopCat.of (Fin 7 → unitInterval)) (ContinuousMap.id (Fin 7 →
        unitInterval)) (ModuleCat.of ℤ ℤ)).hom 1 :=
  iteratedIntegralShuffle_eq_orderedChain 7

/-- The original integer ring acts on a coefficient module in a strictly larger universe. -/
def largeIntegerCoefficients : ModuleCat.{1} ℤ := ModuleCat.of ℤ (ULift.{1} ℤ)

/-- A genuinely larger-universe point space uses the original, unlifted integer scalars. -/
def largePoint : TopCat.{1} := TopCat.of (ULift.{1} PUnit.{1})

/-- The bundled native map accepts the larger space and coefficients without enlarging ℤ. -/
example : rawCubicalChainComplexObj.{1, 0, 1} largePoint largeIntegerCoefficients ⟶
    (TopCat.toSSet.obj largePoint).chainComplex largeIntegerCoefficients :=
  orderedTriangulationChainMap.{0, 1, 1} largePoint largeIntegerCoefficients

/-- The point law retains the actual nonzero lifted integer coefficient. -/
example : orderedTriangulation.{0, 1, 1} largePoint largeIntegerCoefficients 0
    (Finsupp.single (SingularCube.point (ULift.up PUnit.unit)) (ULift.up (1 : ℤ))) =
      ((TopCat.toSSet.obj largePoint).ιChainComplex (R := largeIntegerCoefficients)
        (TopCat.toSSetObj₀Equiv.symm (ULift.up PUnit.unit))).hom (ULift.up 1) := by
  exact orderedTriangulation_single_zero.{0, 1, 1} _ _ _

/-- The large coefficient is detected by the native coproduct retraction, so it is not zero. -/
example : orderedTriangulation.{0, 1, 1} largePoint largeIntegerCoefficients 0
    (Finsupp.single (SingularCube.point (ULift.up PUnit.unit)) (ULift.up (1 : ℤ))) ≠ 0 := by
  -- Expose the named example carriers before native rewrites at implicit transparency.
  unfold largePoint largeIntegerCoefficients
  rw [orderedTriangulation_single_zero.{0, 1, 1}]
  let σ : (TopCat.toSSet.obj (TopCat.of (ULift.{1} PUnit.{1}))) _⦋0⦌ :=
    TopCat.toSSetObj₀Equiv.symm (ULift.up PUnit.unit)
  let d : (((TopCat.toSSet.obj (TopCat.of (ULift.{1} PUnit.{1}))).chainComplex
      (ModuleCat.of ℤ (ULift.{1} ℤ))).X 0) →ₗ[ℤ] ULift.{1} ℤ :=
    (Cofan.IsColimit.desc
    ((TopCat.toSSet.obj (TopCat.of (ULift.{1} PUnit.{1}))).isColimitChainComplexXCofan
      (ModuleCat.of ℤ (ULift.{1} ℤ)) 0)
    (fun _ ↦ 𝟙 (ModuleCat.of ℤ (ULift.{1} ℤ)))).hom
  have hd := Cofan.IsColimit.fac
    ((TopCat.toSSet.obj (TopCat.of (ULift.{1} PUnit.{1}))).isColimitChainComplexXCofan
      (ModuleCat.of ℤ (ULift.{1} ℤ)) 0)
    (fun _ ↦ 𝟙 (ModuleCat.of ℤ (ULift.{1} ℤ))) σ
  simp only [SSet.chainComplexXCofan, Cofan.inj, Cofan.mk_ι_app] at hd
  intro h
  simp only [SingularCube.point_apply] at h
  have he := congrArg (fun g ↦ g.hom (ULift.up (1 : ℤ))) hd
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] at he
  have hz := congrArg d h
  rw [d.map_zero] at hz
  exact (by decide : (ULift.up (1 : ℤ) : ULift.{1} ℤ) ≠ 0) (he.symm.trans hz)

/-- Coefficient naturality remains native and R-linear across the universe separation. -/
example (n : ℕ) :
    ((((SSet.chainComplexFunctor (ModuleCat.{1} ℤ)).map
      (ModuleCat.ofHom (2 • (LinearMap.id : ULift.{1} ℤ →ₗ[ℤ] ULift.{1} ℤ)))).app
      (TopCat.toSSet.obj largePoint)).f n).hom ∘ₗ
        nativeOrderedTriangulation.{0, 1, 1} largePoint largeIntegerCoefficients n =
      nativeOrderedTriangulation.{0, 1, 1} largePoint largeIntegerCoefficients n ∘ₗ
        Finsupp.mapRange.linearMap (2 • (LinearMap.id : ULift.{1} ℤ →ₗ[ℤ] ULift.{1} ℤ)) := by
  exact nativeOrderedTriangulation_coefficient_naturality.{0, 1, 1} _ _

/-- Ordinary point spaces also admit the genuinely larger native coefficient object. -/
example : rawCubicalChainComplexObj.{1, 0, 0} (TopCat.of PUnit.{1}) largeIntegerCoefficients ⟶
    (TopCat.toSSet.obj (TopCat.of PUnit.{1})).chainComplex largeIntegerCoefficients :=
  orderedTriangulationChainMap.{0, 0, 1} (TopCat.of PUnit.{1}) largeIntegerCoefficients

/-- The small point keeps its lifted integer coefficient; the base is not lifted. -/
example : orderedTriangulation.{0, 0, 1} (TopCat.of PUnit.{1}) largeIntegerCoefficients 0
    (Finsupp.single (SingularCube.point PUnit.unit) (ULift.up (1 : ℤ))) =
      ((TopCat.toSSet.obj (TopCat.of PUnit.{1})).ιChainComplex (R := largeIntegerCoefficients)
        (TopCat.toSSetObj₀Equiv.symm PUnit.unit)).hom (ULift.up 1) := by
  exact orderedTriangulation_single_zero.{0, 0, 1} _ _ _

end TauCeti.Examples.OrderedCubicalTriangulation

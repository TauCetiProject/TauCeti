/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OfMulAction
public import TauCeti.RepresentationTheory.OfMulAction.OrbitBasis
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Gram geometry of orbit averages

An invariant rational matrix induces a rational bilinear form on a permutation
representation. Its restriction to the invariant subspace has an explicit Gram
matrix in the basis of normalized orbit sums. Positive definiteness descends to
that matrix, and the orbit projection preserves pairing against invariant vectors.
-/

public noncomputable section

open MonoidAlgebra MulAction Module Representation TauCeti

namespace Matrix

variable {Γ I : Type*} [Group Γ] [MulAction Γ I] [Fintype I]

open Classical in
/-- The sum of one column over a row orbit, evaluated at a representative of the column orbit. -/
def orbitColumnSum {M : Type*} [AddCommMonoid M]
    (A : Matrix I I M) (O P : orbitRel.Quotient Γ I) : M :=
  ∑ i ∈ Finset.univ.filter (fun i ↦ Quotient.mk (orbitRel Γ I) i = O), A i P.out

open Classical in
/-- The orbit column sum is the filtered row sum at the chosen column representative. -/
theorem orbitColumnSum_def {M : Type*} [AddCommMonoid M]
    (A : Matrix I I M) (O P : orbitRel.Quotient Γ I) :
    orbitColumnSum A O P =
      ∑ i ∈ Finset.univ.filter (fun i ↦ Quotient.mk (orbitRel Γ I) i = O), A i P.out :=
  (rfl)

open Classical in
/-- Invariance of the original matrix makes its orbit column sum independent of the
chosen representative of the column orbit. -/
theorem orbitColumnSum_eq_sum {M : Type*} [AddCommMonoid M] (A : Matrix I I M)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j)
    (O P : orbitRel.Quotient Γ I) (j : I) (hj : Quotient.mk (orbitRel Γ I) j = P) :
    orbitColumnSum A O P =
      ∑ i ∈ Finset.univ.filter (fun i ↦ Quotient.mk (orbitRel Γ I) i = O), A i j := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : Γ, g • j = (Quotient.mk (orbitRel Γ I) j).out :=
    Quotient.mk_out (s := orbitRel Γ I) j
  rw [hj] at hg
  rw [orbitColumnSum_def]
  rw [← hg]
  symm
  apply Finset.sum_bij (fun i _ ↦ g • i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      orbitRel.Quotient.quotient_smul_eq] using hi
  · intro i hi k hk h
    exact MulAction.injective g h
  · intro i hi
    refine ⟨g⁻¹ • i, ?_, by simp⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      orbitRel.Quotient.quotient_smul_eq] using hi
  · intro i hi
    exact (hact g i j).symm

open Classical in
/-- Pairing an orbit-average basis vector with a standard basis vector gives the normalized
orbit column sum. -/
theorem toBilin_ofMulActionOrbitBasis_single [DecidableEq I] (A : Matrix I I ℚ)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j)
    (O : orbitRel.Quotient Γ I) (j : I) :
    toBilin (MonoidAlgebra.basis I ℚ) A
        (ofMulActionOrbitBasis Γ I O).val (MonoidAlgebra.single j 1) =
      (orbitColumnSum A O (Quotient.mk (orbitRel Γ I) j) : ℚ) /
        (Nat.card O.orbit : ℚ) := by
  classical
  have hs (i : I) :
      toBilin (MonoidAlgebra.basis I ℚ) A
          (MonoidAlgebra.single i 1) (MonoidAlgebra.single j 1) = A i j := by
    simpa only [LinearMap.BilinForm.toMatrix_apply, MonoidAlgebra.basis_apply] using
      congr_fun (congr_fun (LinearMap.BilinForm.toMatrix_toBilin
        (MonoidAlgebra.basis I ℚ) A) i) j
  rw [ofMulActionOrbitBasis_eq_sum]
  simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, hs]
  rw [← orbitColumnSum_eq_sum A hact O _ j rfl]
  ring

open Classical in
/-- The actual Gram entry of two orbit averages is the orbit column sum divided by the
size of the row orbit. This formula does not require symmetry or positive definiteness. -/
theorem toBilin_ofMulActionOrbitBasis [DecidableEq I] (A : Matrix I I ℚ)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j)
    (O P : orbitRel.Quotient Γ I) :
    toBilin (MonoidAlgebra.basis I ℚ) A
        (ofMulActionOrbitBasis Γ I O).val (ofMulActionOrbitBasis Γ I P).val =
      (orbitColumnSum A O P : ℚ) / (Nat.card O.orbit : ℚ) := by
  classical
  rw [ofMulActionOrbitBasis_eq_sum Γ I P, map_smul, map_sum]
  simp only [smul_eq_mul, toBilin_ofMulActionOrbitBasis_single A hact]
  calc
    _ = (Nat.card P.orbit : ℚ)⁻¹ *
        ∑ _j ∈ Finset.univ.filter (fun j ↦ Quotient.mk (orbitRel Γ I) j = P),
          (orbitColumnSum A O P : ℚ) / (Nat.card O.orbit : ℚ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = _ := by
      rw [Finset.sum_const, P.card_filter_quotient_mk, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr P.card_orbit_ne_zero), one_mul]

open Classical in
/-- The matrix of the restricted bilinear form in the orbit-average basis is the
normalized orbit column-sum matrix. -/
theorem toMatrix_restrict_ofMulActionOrbitBasis [DecidableEq I]
    [Fintype (orbitRel.Quotient Γ I)] [DecidableEq (orbitRel.Quotient Γ I)]
    (A : Matrix I I ℚ)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j) :
    ((toBilin (MonoidAlgebra.basis I ℚ) A).restrict
      (ofMulAction ℚ Γ I).invariants).toMatrix (ofMulActionOrbitBasis Γ I) =
      fun O P ↦ (orbitColumnSum A O P : ℚ) / (Nat.card O.orbit : ℚ) := by
  classical
  ext O P
  rw [LinearMap.BilinForm.toMatrix_apply]
  exact toBilin_ofMulActionOrbitBasis A hact O P

open Classical in
/-- Positive definiteness of an invariant rational matrix descends to the actual Gram
matrix of the normalized orbit sums. -/
theorem posDef_orbitColumnSum (A : Matrix I I ℚ)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j)
    (hA : A.PosDef) :
    Matrix.PosDef (fun O P : orbitRel.Quotient Γ I ↦
      (orbitColumnSum A O P : ℚ) / (Nat.card O.orbit : ℚ)) := by
  classical
  let B := toBilin (MonoidAlgebra.basis I ℚ) A
  have hB : B.IsSymm := by
    simpa only [B, isSymm_toBilin_iff_isSymm] using
      (isHermitian_iff_isSymm.mp hA.isHermitian)
  have hpos : B.toQuadraticMap.PosDef := by
    apply (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
      (MonoidAlgebra.basis I ℚ) B hB).mpr
    simpa only [B, LinearMap.BilinForm.toMatrix_toBilin] using hA
  have hres : (B.restrict (ofMulAction ℚ Γ I).invariants).toQuadraticMap.PosDef := by
    intro w hw
    exact hpos w.val (fun h ↦ hw (Subtype.ext h))
  rw [← toMatrix_restrict_ofMulActionOrbitBasis A hact]
  exact (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
    (ofMulActionOrbitBasis Γ I) (B.restrict (ofMulAction ℚ Γ I).invariants)
    (hB.restrict _)).mp hres

open Classical in
/-- Orbit projection preserves the pairing against every invariant vector. Neither
symmetry nor positive definiteness of the original matrix is required. -/
theorem toBilin_ofMulActionOrbitProjection [DecidableEq I] (A : Matrix I I ℚ)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j)
    (x : ℚ[I]) (w : (ofMulAction ℚ Γ I).invariants) :
    toBilin (MonoidAlgebra.basis I ℚ) A
        (ofMulActionOrbitProjection Γ I x).val w.val =
      toBilin (MonoidAlgebra.basis I ℚ) A x w.val := by
  classical
  let B := toBilin (MonoidAlgebra.basis I ℚ) A
  have hconst (i j : I) (hij : Quotient.mk (orbitRel Γ I) i =
      Quotient.mk (orbitRel Γ I) j) :
      B (MonoidAlgebra.single i 1) w.val = B (MonoidAlgebra.single j 1) w.val := by
    obtain ⟨g, hg⟩ : ∃ g : Γ, g • j = i := Quotient.exact hij
    have h := toBilin_ofMulAction A hact g (MonoidAlgebra.single j 1) w.val
    simpa only [ofMulAction_single, hg, w.property g] using h
  have hav (i : I) :
      B (ofMulActionOrbitBasis Γ I (Quotient.mk (orbitRel Γ I) i)).val w.val =
        B (MonoidAlgebra.single i 1) w.val := by
    let O : orbitRel.Quotient Γ I := Quotient.mk (orbitRel Γ I) i
    rw [ofMulActionOrbitBasis_eq_sum]
    simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
    calc
      _ = (Nat.card O.orbit : ℚ)⁻¹ *
          ∑ _j ∈ Finset.univ.filter (fun j ↦ Quotient.mk (orbitRel Γ I) j = O),
            B (MonoidAlgebra.single i 1) w.val := by
        congr 1
        exact Finset.sum_congr rfl fun j hj ↦ hconst j i (Finset.mem_filter.mp hj).2
      _ = _ := by
        rw [Finset.sum_const, O.card_filter_quotient_mk, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (Nat.cast_ne_zero.mpr O.card_orbit_ne_zero), one_mul]
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, Submodule.coe_add, LinearMap.add_apply, hx, hy]
  | single i r =>
      have hs : MonoidAlgebra.single i r = r • MonoidAlgebra.single i (1 : ℚ) := by simp
      rw [ofMulActionOrbitProjection_single, Submodule.coe_smul, map_smul,
        LinearMap.smul_apply, hs, map_smul, LinearMap.smul_apply]
      exact congrArg (r • ·) (hav i)

open Classical in
/-- Orbit projection can be moved between the two arguments of an invariant bilinear form.
No symmetry or nondegeneracy hypothesis on the matrix is required. -/
theorem toBilin_ofMulActionOrbitProjection_eq [DecidableEq I] (A : Matrix I I ℚ)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j)
    (x y : ℚ[I]) :
    toBilin (MonoidAlgebra.basis I ℚ) A
        (ofMulActionOrbitProjection Γ I x).val y =
      toBilin (MonoidAlgebra.basis I ℚ) A
        x (ofMulActionOrbitProjection Γ I y).val := by
  classical
  let B := toBilin (MonoidAlgebra.basis I ℚ) A
  have htranspose : toBilin (MonoidAlgebra.basis I ℚ) A.transpose = B.flip := by
    apply (LinearMap.BilinForm.ext_iff_basis (MonoidAlgebra.basis I ℚ)).mpr
    intro i j
    -- Unfold the local form B; evaluating flip exchanges its two arguments.
    change toBilin (MonoidAlgebra.basis I ℚ) A.transpose
        (MonoidAlgebra.basis I ℚ i) (MonoidAlgebra.basis I ℚ j) =
      toBilin (MonoidAlgebra.basis I ℚ) A
        (MonoidAlgebra.basis I ℚ j) (MonoidAlgebra.basis I ℚ i)
    rw [← LinearMap.BilinForm.toMatrix_apply, ← LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_toBilin, LinearMap.BilinForm.toMatrix_toBilin]
    rfl
  have hactT (g : Γ) (i j : I) : A.transpose (g • i) (g • j) = A.transpose i j :=
    hact g j i
  -- Applying the first-slot result to the transpose gives the second-slot identity.
  have hright := toBilin_ofMulActionOrbitProjection A.transpose hactT y
    (ofMulActionOrbitProjection Γ I x)
  rw [htranspose] at hright
  calc
    _ = B (ofMulActionOrbitProjection Γ I x).val
        (ofMulActionOrbitProjection Γ I y).val := hright.symm
    _ = _ := toBilin_ofMulActionOrbitProjection A hact x (ofMulActionOrbitProjection Γ I y)

end Matrix

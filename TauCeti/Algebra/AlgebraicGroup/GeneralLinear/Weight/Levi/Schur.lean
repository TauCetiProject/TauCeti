/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi.Geometry
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Block.Triangular
public import TauCeti.LinearAlgebra.Matrix.Kronecker.Power
public import TauCeti.RingTheory.MvPolynomial.Evaluation.Dual

/-!
# The Schur map for a weight Levi

The entries of the `d`-fold Kronecker power of the generic block-diagonal matrix are
homogeneous of degree `d`. Applying a linear functional on that homogeneous component to
these entries gives the Schur map. Over a local ring with residue field of size at least
`d + N`, Kronecker powers of the invertible block-diagonal matrices span its image, even
after mapping the matrices to another coefficient ring.

This is the block-diagonal version of the spanning argument in Benson and Doty,
*Schur–Weyl duality over finite fields*, and corresponds to
`New.Average.eq_top_of_schurMap_eq_leviMonomialValues` in lsernau/grh-lean at `72fead1`.
-/

public noncomputable section

open Matrix MvPolynomial

namespace TauCeti.GeneralLinear

variable {N d : ℕ} {R : Type*} [CommRing R]

/-- Every entry of the generic block-diagonal matrix is homogeneous of degree one. -/
theorem isHomogeneous_weightLeviPolynomialGenericMatrix (w : Fin N → ℤ) (i j : Fin N) :
    (weightLeviPolynomialGenericMatrix R w i j).IsHomogeneous 1 := by
  by_cases h : w i = w j
  · rw [weightLeviPolynomialGenericMatrix_apply_of_eq R w h]
    exact isHomogeneous_X _ _
  · rw [weightLeviPolynomialGenericMatrix_apply_of_ne R w h]
    exact isHomogeneous_zero _ _ _

/-- The determinant of the generic block-diagonal matrix is homogeneous of degree `N`. -/
theorem isHomogeneous_det_weightLeviPolynomialGenericMatrix (w : Fin N → ℤ) :
    (weightLeviPolynomialGenericMatrix R w).det.IsHomogeneous N := by
  rw [det_apply']
  apply IsHomogeneous.sum
  intro s _
  have hp := IsHomogeneous.prod Finset.univ
    (fun i ↦ weightLeviPolynomialGenericMatrix R w (s i) i) (fun _ ↦ 1)
    (fun i _ ↦ isHomogeneous_weightLeviPolynomialGenericMatrix w (s i) i (R := R))
  simpa using hp.C_mul ((Equiv.Perm.sign s : ℤ) : R)

/-- Each entry of the generic Kronecker power represents a degree-`d` polynomial. -/
theorem isHomogeneous_kroneckerPower_weightLeviPolynomialGenericMatrix (w : Fin N → ℤ)
    (a b : Fin d → Fin N) :
    ((weightLeviPolynomialGenericMatrix R w).kroneckerPower (Fin d) a b).IsHomogeneous d := by
  rw [kroneckerPower_apply]
  simpa using IsHomogeneous.prod Finset.univ
    (fun i ↦ weightLeviPolynomialGenericMatrix R w (a i) (b i)) (fun _ ↦ 1)
    (fun i _ ↦ isHomogeneous_weightLeviPolynomialGenericMatrix w (a i) (b i) (R := R))

/-- Apply a functional on degree-`d` polynomials to the entries of the generic Kronecker power. -/
def blockSchurMap (w : Fin N → ℤ) (d : ℕ) :
    Module.Dual R (homogeneousSubmodule (WeightLeviIndex w) R d) →ₗ[R]
      Matrix (Fin d → Fin N) (Fin d → Fin N) R where
  toFun l := Matrix.of fun a b ↦ l
    ⟨(weightLeviPolynomialGenericMatrix R w).kroneckerPower (Fin d) a b,
      isHomogeneous_kroneckerPower_weightLeviPolynomialGenericMatrix w a b⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Each matrix entry of the Schur map is the functional applied to the corresponding
homogeneous entry of the generic Kronecker power. -/
@[simp]
theorem blockSchurMap_apply (w : Fin N → ℤ)
    (l : Module.Dual R (homogeneousSubmodule (WeightLeviIndex w) R d)) (a b : Fin d → Fin N) :
    blockSchurMap w d l a b = l
      ⟨(weightLeviPolynomialGenericMatrix R w).kroneckerPower (Fin d) a b,
        isHomogeneous_kroneckerPower_weightLeviPolynomialGenericMatrix w a b⟩ := (rfl)

/-- The Schur map sends evaluation to the Kronecker power of the evaluated matrix. -/
@[simp]
theorem blockSchurMap_aeval (w : Fin N → ℤ) (y : WeightLeviIndex w → R) :
    blockSchurMap w d ((aeval y).toLinearMap.comp
        (homogeneousSubmodule (WeightLeviIndex w) R d).subtype) =
      ((weightLeviPolynomialGenericMatrix R w).map (eval y)).kroneckerPower (Fin d) := by
  ext a b
  simp [kroneckerPower_apply]

/-- Over a local ring `W` with residue field of size at least `d + N`, the `d`-fold Kronecker
powers of Levi matrices, mapped along `ι`, span the image of the block Schur map over `R`. -/
theorem span_kroneckerPower_leviSubgroup_eq_range {W : Type*} [CommRing W] [IsLocalRing W]
    (w : Fin N → ℤ) (ι : W →+* R)
    (hcard : ((d + N : ℕ) : Cardinal) ≤ Cardinal.mk (IsLocalRing.ResidueField W)) :
    Submodule.span R (Set.range fun g : TauCeti.leviSubgroup w W ↦
      (((g.val : GL (Fin N) W) : Matrix (Fin N) (Fin N) W).map ι).kroneckerPower (Fin d)) =
      LinearMap.range (blockSchurMap w d) := by
  let G := weightLeviPolynomialGenericMatrix W w
  -- The unit locus of the generic determinant parametrizes the Levi subgroup.
  have hpoint (g : TauCeti.leviSubgroup w W) :
      ∃ y : {y : WeightLeviIndex w → W // IsUnit (eval y G.det)}, G.map (eval y.val) =
        (g.val : Matrix (Fin N) (Fin N) W) := by
    let y : WeightLeviIndex w → W := fun ij ↦ (g.val : Matrix (Fin N) (Fin N) W) ij.val.1 ij.val.2
    have hy : G.map (eval y) = (g.val : Matrix (Fin N) (Fin N) W) := by
      ext i j
      by_cases hwij : w i = w j
      · simp [G, hwij, y]
      · simp [G, hwij, (TauCeti.mem_leviSubgroup w).mp g.property i j hwij]
    refine ⟨⟨y, ?_⟩, hy⟩
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hy]
    exact (Matrix.isUnit_iff_isUnit_det _).mp g.val.isUnit
  obtain ⟨y₀, _⟩ := hpoint 1
  have h := (isHomogeneous_det_weightLeviPolynomialGenericMatrix (R := W) w).span_range_aeval_eq_top
    ι hcard ⟨y₀.val, y₀.property⟩
  have hh := congrArg (Submodule.map (blockSchurMap w d)) h
  rw [Submodule.map_top, Submodule.map_span, ← Set.range_comp] at hh
  rw [← hh]
  have hmap (y : WeightLeviIndex w → W) :
      (weightLeviPolynomialGenericMatrix R w).map (eval (ι ∘ y)) = (G.map (eval y)).map ι := by
    ext i j
    by_cases hij : w i = w j <;> simp [G, hij]
  congr 1
  ext A
  simp only [Set.mem_range, Function.comp_apply, blockSchurMap_aeval, hmap]
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨y, hy⟩ := hpoint g
    exact ⟨y, by rw [hy]⟩
  · rintro ⟨y, rfl⟩
    have hy : IsUnit (G.map (eval y.val)).det := by
      simpa only [RingHom.map_det, RingHom.mapMatrix_apply] using y.property
    let g : GL (Fin N) W := Matrix.GeneralLinearGroup.mk'' _ hy
    exact ⟨⟨g, (TauCeti.mem_leviSubgroup w).2 fun i j hij ↦ by simp [g, G, hij]⟩, rfl⟩

end TauCeti.GeneralLinear

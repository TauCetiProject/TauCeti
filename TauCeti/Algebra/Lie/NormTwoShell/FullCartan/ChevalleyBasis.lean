/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.ChevalleyBasis
public import TauCeti.Algebra.Lie.NormTwoShell.FullCartan.Basic

/-!
# A normalized root basis over the full Cartan lattice

The signed shell algebra `Matrix.FullShellLieAlgebra D` retains the full cocharacter group
`Y`, rather than just the coroot lattice. We transport the inverse-lift normalization of
`Matrix.ShellLieAlgebra.normalizedRoot` to this algebra. Its opposite-root bracket is then
exactly the coroot in `Y`, not a signed coroot. The positive simple pinning is unchanged.

Given any integral basis of `Y`, `Matrix.FullShellLieAlgebra.normalizedBasis` joins its Cartan
vectors to the normalized root vectors. Its coordinate equations give an integral inverse;
no integral splitting of the coroot lattice from the central directions is required. The
root-vector and bracket constructions allow arbitrary abelian `Y`; only the basis construction
requires a supplied basis. The same basis remains a basis after arbitrary-ring scalar extension
by `Module.Basis.baseChange`.

The signs and root-string constants are those already constructed in
`TauCeti.Algebra.Lie.NormTwoShell.ChevalleyBasis`, not a second normalization convention.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016), §1.
* J. C. Jantzen, *Representations of Algebraic Groups*, second edition (2003), Part II,
  Chapter 1, for the full cocharacter lattice and the integral Chevalley form.
-/

public section

namespace Matrix.FullShellLieAlgebra

open Module

variable {I : Type*} [Fintype I] [LinearOrder I] {B : Matrix I I ℤ}
  {Y : Type*} [AddCommGroup Y] (D : ShellCartanDatum B Y)

/-- The root vector normalized by the inverse-lift sign of the ordered cover. -/
noncomputable def normalizedRoot (a : B.normTwoShell) : FullShellLieAlgebra D :=
  ShellLieAlgebra.normalizationSign B a • root D a

/-- The full-Cartan normalization uses exactly the shell algebra's normalization sign. -/
theorem normalizedRoot_def (a : B.normTwoShell) :
    normalizedRoot D a = ShellLieAlgebra.normalizationSign B a • root D a := (rfl)

/-- The normalized vector has zero Cartan coordinate and a signed unit root coordinate. -/
@[simp]
theorem equivProd_normalizedRoot (a : B.normTwoShell) :
    equivProd D (normalizedRoot D a) =
      (0, ShellLieAlgebra.normalizationSign B a • Finsupp.single a 1) := by
  simp [normalizedRoot_def, Units.smul_def]

/-- The coroot-lattice comparison carries normalized root vectors to normalized root vectors. -/
@[simp]
theorem toFull_normalizedRoot (a : B.normTwoShell) :
    toFull D (ShellLieAlgebra.normalizedRoot B a) = normalizedRoot D a := by
  simp [ShellLieAlgebra.normalizedRoot_def, normalizedRoot_def, Units.smul_def]

/-- Positive root vectors keep their original parameters. -/
@[simp]
theorem normalizedRoot_of_nonneg {a : B.normTwoShell} (ha : 0 ≤ (a : I → ℤ)) :
    normalizedRoot D a = root D a := by
  simp [normalizedRoot_def, ShellLieAlgebra.normalizationSign_of_nonneg ha]

/-- On roots that are not nonnegative, use the ordered inverse-lift sign. -/
@[simp]
theorem normalizedRoot_of_not_nonneg {a : B.normTwoShell} (ha : ¬0 ≤ (a : I → ℤ)) :
    normalizedRoot D a = (B.orderedSignForm a a).negOnePow • root D a := by
  rw [normalizedRoot_def, ShellLieAlgebra.normalizationSign_of_not_nonneg ha]

/-- The Cartan action retains the actual pairing with the full cocharacter group. -/
@[simp]
theorem cartan_lie_normalizedRoot (y : Y) (a : B.normTwoShell) :
    ⁅cartan D y, normalizedRoot D a⁆ = D.weight a y • normalizedRoot D a := by
  rw [normalizedRoot_def, FullShellLieAlgebra.lie_units_smul, cartan_lie_root, smul_comm]

-- Root brackets transport even without symmetry of B: only the Cartan action uses symmetry.
private theorem normalizedRoot_lie_normalizedRoot_eq_toFull (a b : B.normTwoShell) :
    ⁅normalizedRoot D a, normalizedRoot D b⁆ =
      toFull D ⁅ShellLieAlgebra.normalizedRoot B a, ShellLieAlgebra.normalizedRoot B b⁆ := by
  simp [normalizedRoot_def, ShellLieAlgebra.normalizedRoot_lie_normalizedRoot,
    Units.smul_def, smul_smul, mul_comm]

/-- Opposite normalized roots bracket to the actual coroot in the full Cartan group. -/
@[simp]
theorem normalizedRoot_lie_normalizedRoot_of_add_eq_zero (hB : B.PosDef)
    (hev : ∀ i, Even (B i i)) (hoff : ∀ i j, i ≠ j → B i j ≤ 0)
    {a b : B.normTwoShell} (h : (a : I → ℤ) + b = 0) :
    ⁅normalizedRoot D a, normalizedRoot D b⁆ = cartan D (D.coroot a) := by
  rw [normalizedRoot_lie_normalizedRoot_eq_toFull,
    ShellLieAlgebra.normalizedRoot_lie_normalizedRoot_of_add_eq_zero hB hev hoff h,
    toFull_cartan]

/-- Root-sum brackets have the same integral unit coefficients as the coroot-lattice algebra. -/
@[simp]
theorem normalizedRoot_lie_normalizedRoot_of_mem {a b : B.normTwoShell}
    (h : (a : I → ℤ) + b ∈ B.normTwoShell) :
    ⁅normalizedRoot D a, normalizedRoot D b⁆ =
      ShellLieAlgebra.structureConstant B a b • normalizedRoot D ⟨_, h⟩ := by
  rw [normalizedRoot_lie_normalizedRoot_eq_toFull,
    ShellLieAlgebra.normalizedRoot_lie_normalizedRoot_of_mem h]
  simp [Units.smul_def]

/-- Roots whose sum is neither a root nor zero commute in the normalized basis. -/
@[simp]
theorem normalizedRoot_lie_normalizedRoot_of_notMem_of_add_ne_zero {a b : B.normTwoShell}
    (h : (a : I → ℤ) + b ∉ B.normTwoShell) (h' : (a : I → ℤ) + b ≠ 0) :
    ⁅normalizedRoot D a, normalizedRoot D b⁆ = 0 := by
  rw [normalizedRoot_lie_normalizedRoot_eq_toFull,
    ShellLieAlgebra.normalizedRoot_lie_normalizedRoot_of_notMem_of_add_ne_zero h h', map_zero]

/-- Normalization fixes the positive simple root vectors. -/
theorem normalizedRoot_single (hdiag : ∀ i, B i i = 2) (i : I) :
    normalizedRoot D ⟨Pi.single i 1, single_mem_normTwoShell (hdiag i)⟩ =
      root D ⟨Pi.single i 1, single_mem_normTwoShell (hdiag i)⟩ :=
  normalizedRoot_of_nonneg D (Pi.single_nonneg.mpr zero_le_one)

/-- Normalization also fixes the negative simple root vectors. -/
theorem normalizedRoot_neg_single (hdiag : ∀ i, B i i = 2) (i : I) :
    normalizedRoot D
        ⟨-Pi.single i 1, neg_mem_normTwoShell.mpr (single_mem_normTwoShell (hdiag i))⟩ =
      root D ⟨-Pi.single i 1, neg_mem_normTwoShell.mpr (single_mem_normTwoShell (hdiag i))⟩ := by
  have h : ¬0 ≤ (-Pi.single i 1 : I → ℤ) := fun h ↦ by simpa using h i
  rw [normalizedRoot_of_not_nonneg D h]
  simp

variable {J : Type*} (bY : Basis J ℤ Y)

/-- An integral basis consisting of the full Cartan basis and the normalized root vectors. -/
noncomputable def normalizedBasis : Basis (J ⊕ B.normTwoShell) ℤ (FullShellLieAlgebra D) :=
  (bY.prod ((Finsupp.basisSingleOne : Basis B.normTwoShell ℤ (B.normTwoShell →₀ ℤ)).unitsSMul
    fun a ↦ ShellLieAlgebra.normalizationSign B a)).map (equivProd D).symm

/-- The Cartan part of the normalized basis is the supplied basis of the full lattice. -/
@[simp]
theorem normalizedBasis_inl (j : J) :
    normalizedBasis D bY (.inl j) = cartan D (bY j) := by
  apply (equivProd D).injective
  simp [normalizedBasis]

/-- The root part of the normalized basis consists of inverse-lift normalized root vectors. -/
@[simp]
theorem normalizedBasis_inr (a : B.normTwoShell) :
    normalizedBasis D bY (.inr a) = normalizedRoot D a := by
  apply (equivProd D).injective
  simp [normalizedBasis, Basis.unitsSMul_apply, normalizedRoot_def, Units.smul_def]

/-- Cartan coordinates are the coordinates in the actual full Cartan lattice. -/
@[simp]
theorem normalizedBasis_repr_inl (x : FullShellLieAlgebra D) (j : J) :
    (normalizedBasis D bY).repr x (.inl j) = bY.repr (equivProd D x).1 j := by
  simp [normalizedBasis]

/-- Root coordinates are multiplied by the normalization sign, which is its own inverse. -/
@[simp]
theorem normalizedBasis_repr_inr (x : FullShellLieAlgebra D) (a : B.normTwoShell) :
    (normalizedBasis D bY).repr x (.inr a) =
      ShellLieAlgebra.normalizationSign B a • (equivProd D x).2 a := by
  simp [normalizedBasis, Basis.repr_unitsSMul, Int.units_inv_eq_self]

end Matrix.FullShellLieAlgebra

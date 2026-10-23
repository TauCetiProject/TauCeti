/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Semisimple.Rigid
public import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Character

/-!
# The Frobenius–Perron character of a fusion category

The Grothendieck ring `TauCeti.SplitK0 C` of a finite semisimple monoidal category has the basis
`TauCeti.SplitK0.simpleBasis C` of simple classes, and its structure constants in that basis are
multiplicities, hence nonnegative: it is a ℤ₊-ring. For a fusion category (rigid, with simple
unit, over an algebraically closed field `k` with finite-dimensional morphism spaces) it is
moreover transitive (`TauCeti.sum_fusionCoeff_pos_right`). So the Perron–Frobenius argument of
`TauCeti/LinearAlgebra/Matrix/PerronFrobenius/Character.lean` applies: there is exactly one ring
homomorphism `SplitK0 C →+* ℝ` taking nonnegative values on the simple classes. This is the
**Frobenius–Perron character** `TauCeti.SplitK0.frobeniusPerronChar k C`. Its values on the
simple classes are positive, and its value on a simple class `S` is the spectral radius of the
fusion matrix of `S`. Its value at the class of an object is the Frobenius–Perron dimension of
that object.

By uniqueness, the character does not depend on `k`: any two fields for which `C` satisfies the
hypotheses give the same ring homomorphism (`TauCeti.SplitK0.eq_frobeniusPerronChar`).

## Main declarations

* `TauCeti.SplitK0.frobeniusPerronChar k C`: the Frobenius–Perron character.
* `TauCeti.SplitK0.frobeniusPerronChar_simpleBasis_pos`: it is positive on the simple classes.
* `TauCeti.SplitK0.eq_frobeniusPerronChar`: it is the only ring homomorphism to `ℝ` which is
  nonnegative on the simple classes.
* `TauCeti.SplitK0.spectralRadius_fusionMatrix`: its value on a simple class is the spectral
  radius of the fusion matrix.

## References

* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*, Mathematical Surveys and
  Monographs **205**, AMS (2015), Sections 3.3 (Frobenius–Perron dimensions of transitive
  ℤ₊-rings) and 4.5 (Frobenius–Perron dimensions in a fusion category).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

open scoped Matrix

namespace TauCeti

universe w w' v u

namespace SplitK0

section Fusion

variable (k : Type w') [Field k] [IsAlgClosed k] {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [RigidCategory C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] [Simple (𝟙_ C)]
  [EssentiallySmall.{w} C]

include k in
/-- **Transitivity** of the Grothendieck ring of a fusion category, in coordinates: every simple
class occurs in the product of any basis element with the sum of all simple classes. -/
theorem sum_simpleBasis_repr_simpleBasis_mul_simpleBasis_pos [Fintype (SimpleClasses C)]
    (T U : SimpleClasses C) :
    0 < ∑ S, (simpleBasis C).repr (simpleBasis C T * simpleBasis C S) U := by
  simp_rw [simpleBasis_repr_simpleBasis_mul_simpleBasis_eq_fusionCoeff k]
  exact_mod_cast sum_fusionCoeff_pos_right k T U

section Finite

variable [Finite (SimpleClasses C)]

include k in
/-- The Grothendieck ring of a fusion category has exactly one ring homomorphism to `ℝ` which is
nonnegative on the simple classes. -/
theorem existsUnique_ringHom_simpleBasis_nonneg :
    ∃! χ : SplitK0 C →+* ℝ, ∀ S, 0 ≤ χ (simpleBasis C S) :=
  have := Fintype.ofFinite (SimpleClasses C)
  have : Nonempty (SimpleClasses C) := ⟨SimpleClasses.classOf (𝟙_ C)⟩
  (simpleBasis C).existsUnique_ringHom_nonneg simpleBasis_repr_simpleBasis_mul_simpleBasis_nonneg
    (sum_simpleBasis_repr_simpleBasis_mul_simpleBasis_pos k)

variable (C) in
/-- The **Frobenius–Perron character** of a fusion category: the unique ring homomorphism from
the Grothendieck ring to `ℝ` which is nonnegative on the simple classes
(`TauCeti.SplitK0.eq_frobeniusPerronChar`). Its value at the class of an object is the
Frobenius–Perron dimension of that object. -/
def frobeniusPerronChar : SplitK0 C →+* ℝ :=
  (existsUnique_ringHom_simpleBasis_nonneg k).exists.choose

/-- A ring homomorphism from the Grothendieck ring of a fusion category to `ℝ` which is
nonnegative on the simple classes is the Frobenius–Perron character. -/
theorem eq_frobeniusPerronChar {χ : SplitK0 C →+* ℝ} (hχ : ∀ S, 0 ≤ χ (simpleBasis C S)) :
    χ = frobeniusPerronChar k C :=
  (existsUnique_ringHom_simpleBasis_nonneg k).unique hχ
    (existsUnique_ringHom_simpleBasis_nonneg k).exists.choose_spec

/-- The Frobenius–Perron character is positive on the simple classes. -/
theorem frobeniusPerronChar_simpleBasis_pos (S : SimpleClasses C) :
    0 < frobeniusPerronChar k C (simpleBasis C S) :=
  have := Fintype.ofFinite (SimpleClasses C)
  (simpleBasis C).ringHom_apply_pos_of_nonneg
    (sum_simpleBasis_repr_simpleBasis_mul_simpleBasis_pos k)
    (existsUnique_ringHom_simpleBasis_nonneg k).exists.choose_spec S

end Finite

/-- The value of the Frobenius–Perron character on a simple class `S` is the spectral radius of
the fusion matrix of `S`. -/
theorem spectralRadius_fusionMatrix [Fintype (SimpleClasses C)] (S : SimpleClasses C) :
    spectralRadius ℂ ((fusionMatrix k S).map (Nat.cast : ℕ → ℂ)) =
      ENNReal.ofReal (frobeniusPerronChar k C (simpleBasis C S)) := by
  classical
  rw [show (fusionMatrix k S).map (Nat.cast : ℕ → ℂ) =
      ((fusionMatrix k S).map (Nat.cast : ℕ → ℤ)).map Int.cast by ext; simp,
    fusionMatrix_eq_transpose_leftMulMatrix k, Matrix.transpose_map,
    Matrix.spectralRadius_transpose]
  exact (simpleBasis C).spectralRadius_leftMulMatrix
    simpleBasis_repr_simpleBasis_mul_simpleBasis_nonneg
    (sum_simpleBasis_repr_simpleBasis_mul_simpleBasis_pos k)
    (fun S ↦ (frobeniusPerronChar_simpleBasis_pos k S).le)
    fun T ↦ by rw [Module.Basis.repr_self, Finsupp.single_apply]; split_ifs <;> norm_num

end Fusion

end SplitK0

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Semisimple.Character
public import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Character

/-!
# The Frobenius–Perron character and dimension of a fusion category

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

The **Frobenius–Perron dimension** `TauCeti.frobeniusPerronDim k X` of an object `X` is the value
of the character at the class of `X`. It is multiplicative on tensor products, additive on
biproducts, `1` on the tensor unit, and invariant under taking duals, since the character is
real and characters of the Grothendieck ring intertwine duality with complex conjugation
(`TauCeti.SplitK0.ringHom_apply_dual`). It is the sum of the dimensions of the simple summands of
`X`, counted with multiplicity, so it is nonnegative and monotone along monomorphisms and
epimorphisms. A nonzero object `X` has Frobenius–Perron dimension at least `1`, because the
coevaluation embeds the unit into `X ⊗ Xᘁ`, whose dimension is the square of that of `X`. So the
Frobenius–Perron dimension vanishes exactly on zero objects.

## Main declarations

* `TauCeti.SplitK0.frobeniusPerronChar k C`: the Frobenius–Perron character.
* `TauCeti.SplitK0.frobeniusPerronChar_simpleBasis_pos`: it is positive on the simple classes.
* `TauCeti.SplitK0.eq_frobeniusPerronChar`: it is the only ring homomorphism to `ℝ` which is
  nonnegative on the simple classes.
* `TauCeti.SplitK0.spectralRadius_fusionMatrix`: its value on a simple class is the spectral
  radius of the fusion matrix.
* `TauCeti.frobeniusPerronDim k X`: the Frobenius–Perron dimension of an object.
* `TauCeti.frobeniusPerronDim_tensorObj`, `TauCeti.frobeniusPerronDim_tensorUnit` and
  `TauCeti.frobeniusPerronDim_biprod`: it is multiplicative, normalized and additive.
* `TauCeti.frobeniusPerronDim_rightDual` and `TauCeti.frobeniusPerronDim_leftDual`: it is
  invariant under duality.
* `TauCeti.frobeniusPerronDim_eq_sum`: it is the sum over the simple summands.
* `TauCeti.frobeniusPerronDim_le_of_mono` and `TauCeti.frobeniusPerronDim_le_of_epi`: it is
  monotone along monomorphisms and epimorphisms.
* `TauCeti.one_le_frobeniusPerronDim`, `TauCeti.frobeniusPerronDim_eq_zero_iff` and
  `TauCeti.frobeniusPerronDim_pos_iff`: it is at least one on nonzero objects, and vanishes
  exactly on zero objects.

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

section Dim

variable (k : Type w') [Field k] [IsAlgClosed k] {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [RigidCategory C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] [Simple (𝟙_ C)]
  [EssentiallySmall.{w} C] [Finite (SimpleClasses C)]

/-- The **Frobenius–Perron dimension** of an object of a fusion category: the value of the
Frobenius–Perron character `TauCeti.SplitK0.frobeniusPerronChar` at the class of the object. -/
def frobeniusPerronDim (X : C) : ℝ :=
  SplitK0.frobeniusPerronChar k C (SplitK0.of X)

/-- The Frobenius–Perron character at the class of an object is its Frobenius–Perron
dimension. -/
@[simp]
theorem SplitK0.frobeniusPerronChar_of (X : C) :
    frobeniusPerronChar k C (of X) = frobeniusPerronDim k X :=
  (rfl)

/-- Isomorphic objects have the same Frobenius–Perron dimension. -/
theorem frobeniusPerronDim_eq_of_iso {X Y : C} (e : X ≅ Y) :
    frobeniusPerronDim k X = frobeniusPerronDim k Y := by
  rw [← SplitK0.frobeniusPerronChar_of, SplitK0.of_congr e, SplitK0.frobeniusPerronChar_of]

/-- The Frobenius–Perron dimension is multiplicative. -/
@[simp]
theorem frobeniusPerronDim_tensorObj (X Y : C) :
    frobeniusPerronDim k (X ⊗ Y) = frobeniusPerronDim k X * frobeniusPerronDim k Y := by
  rw [← SplitK0.frobeniusPerronChar_of, ← SplitK0.of_mul_of, map_mul,
    SplitK0.frobeniusPerronChar_of, SplitK0.frobeniusPerronChar_of]

/-- The tensor unit has Frobenius–Perron dimension one. -/
@[simp]
theorem frobeniusPerronDim_tensorUnit : frobeniusPerronDim k (𝟙_ C) = 1 := by
  rw [← SplitK0.frobeniusPerronChar_of, ← SplitK0.one_def, map_one]

/-- The Frobenius–Perron dimension is additive on biproducts. -/
@[simp]
theorem frobeniusPerronDim_biprod (X Y : C) :
    frobeniusPerronDim k (X ⊞ Y) = frobeniusPerronDim k X + frobeniusPerronDim k Y := by
  rw [← SplitK0.frobeniusPerronChar_of, SplitK0.of_biprod, map_add,
    SplitK0.frobeniusPerronChar_of, SplitK0.frobeniusPerronChar_of]

/-- A zero object has Frobenius–Perron dimension zero. -/
theorem frobeniusPerronDim_eq_zero_of_isZero {X : C} (hX : IsZero X) :
    frobeniusPerronDim k X = 0 := by
  rw [← SplitK0.frobeniusPerronChar_of, SplitK0.of_eq_zero_of_isZero hX, map_zero]

open ZeroObject in
/-- The zero object has Frobenius–Perron dimension zero. -/
@[simp]
theorem frobeniusPerronDim_zero : frobeniusPerronDim k (0 : C) = 0 :=
  frobeniusPerronDim_eq_zero_of_isZero k (isZero_zero C)

/-- A right dual has the same Frobenius–Perron dimension as the object. -/
@[simp]
theorem frobeniusPerronDim_rightDual (X : C) :
    frobeniusPerronDim k Xᘁ = frobeniusPerronDim k X := by
  rw [← SplitK0.frobeniusPerronChar_of, ← SplitK0.dual_of,
    SplitK0.ringHom_apply_dual k (SplitK0.frobeniusPerronChar k C), RCLike.conj_to_real,
    SplitK0.frobeniusPerronChar_of]

/-- A left dual has the same Frobenius–Perron dimension as the object. -/
@[simp]
theorem frobeniusPerronDim_leftDual (X : C) :
    frobeniusPerronDim k (ᘁX) = frobeniusPerronDim k X := by
  -- `X` and the chosen right dual of `ᘁX` are both right duals of `ᘁX`, hence isomorphic.
  rw [← frobeniusPerronDim_rightDual k (ᘁX)]
  exact frobeniusPerronDim_eq_of_iso k
    (rightDualIso (RightRigidCategory.rightDual (ᘁX)).exact HasLeftDual.exact)

/-- A simple object has positive Frobenius–Perron dimension. -/
theorem frobeniusPerronDim_pos_of_simple (X : C) [Simple X] : 0 < frobeniusPerronDim k X := by
  rw [← SplitK0.frobeniusPerronChar_of, SplitK0.of_eq_simpleBasis]
  exact SplitK0.frobeniusPerronChar_simpleBasis_pos k _

/-- The Frobenius–Perron dimension of an object is the sum of the Frobenius–Perron dimensions of
its simple summands, counted with multiplicity. -/
theorem frobeniusPerronDim_eq_sum [Fintype (SimpleClasses C)] (X : C) :
    frobeniusPerronDim k X =
      ∑ S, (simpleMultiplicities X S : ℝ) * frobeniusPerronDim k S.repr := by
  rw [← SplitK0.frobeniusPerronChar_of, SplitK0.of_eq_sum, map_finsuppSum,
    Finsupp.sum_fintype _ _ (by simp)]
  simp

/-- The Frobenius–Perron dimension is nonnegative. -/
theorem frobeniusPerronDim_nonneg (X : C) : 0 ≤ frobeniusPerronDim k X := by
  have := Fintype.ofFinite (SimpleClasses C)
  rw [frobeniusPerronDim_eq_sum]
  exact Finset.sum_nonneg fun S _ ↦
    mul_nonneg (Nat.cast_nonneg _) (frobeniusPerronDim_pos_of_simple k S.repr).le

/-- The Frobenius–Perron dimension of an object is the sum, over the simple classes `S`, of the
dimension of the morphisms from `S` to the object times the Frobenius–Perron dimension of `S`. -/
private theorem frobeniusPerronDim_eq_sum_finrank_hom [Fintype (SimpleClasses C)] (X : C) :
    frobeniusPerronDim k X =
      ∑ S : SimpleClasses C, (Module.finrank k (S.repr ⟶ X) : ℝ) * frobeniusPerronDim k S.repr := by
  simp [frobeniusPerronDim_eq_sum k X]

/-- The Frobenius–Perron dimension of an object is the sum, over the simple classes `S`, of the
dimension of the morphisms from the object to `S` times the Frobenius–Perron dimension of `S`. -/
private theorem frobeniusPerronDim_eq_sum_finrank_homTo [Fintype (SimpleClasses C)] (X : C) :
    frobeniusPerronDim k X =
      ∑ S : SimpleClasses C, (Module.finrank k (X ⟶ S.repr) : ℝ) * frobeniusPerronDim k S.repr := by
  simp [frobeniusPerronDim_eq_sum k X]

/-- The Frobenius–Perron dimension is monotone along monomorphisms. -/
theorem frobeniusPerronDim_le_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    frobeniusPerronDim k X ≤ frobeniusPerronDim k Y := by
  have := Fintype.ofFinite (SimpleClasses C)
  rw [frobeniusPerronDim_eq_sum_finrank_hom, frobeniusPerronDim_eq_sum_finrank_hom]
  -- Composition with `f` embeds the morphisms from each simple object into `X` into those into `Y`.
  refine Finset.sum_le_sum fun S _ ↦ mul_le_mul_of_nonneg_right ?_
    (frobeniusPerronDim_pos_of_simple k S.repr).le
  exact_mod_cast LinearMap.finrank_le_finrank_of_injective (f := Linear.rightComp k S.repr f)
    fun g h hgh ↦ (cancel_mono f).1 hgh

/-- The Frobenius–Perron dimension is monotone along epimorphisms. -/
theorem frobeniusPerronDim_le_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    frobeniusPerronDim k Y ≤ frobeniusPerronDim k X := by
  have := Fintype.ofFinite (SimpleClasses C)
  rw [frobeniusPerronDim_eq_sum_finrank_homTo, frobeniusPerronDim_eq_sum_finrank_homTo]
  -- Composition with `f` embeds the morphisms from `Y` to each simple object into those from `X`.
  refine Finset.sum_le_sum fun S _ ↦ mul_le_mul_of_nonneg_right ?_
    (frobeniusPerronDim_pos_of_simple k S.repr).le
  exact_mod_cast LinearMap.finrank_le_finrank_of_injective (f := Linear.leftComp k S.repr f)
    fun g h hgh ↦ (cancel_epi f).1 hgh

/-- A nonzero object has Frobenius–Perron dimension at least one. -/
theorem one_le_frobeniusPerronDim {X : C} (hX : ¬IsZero X) : 1 ≤ frobeniusPerronDim k X := by
  -- The coevaluation is a nonzero morphism out of the simple unit, hence a monomorphism.
  have : Mono (η_ X Xᘁ) := mono_of_nonzero_from_simple (coevaluation_ne_zero hX)
  have h := frobeniusPerronDim_le_of_mono k (η_ X Xᘁ)
  rw [frobeniusPerronDim_tensorUnit, frobeniusPerronDim_tensorObj,
    frobeniusPerronDim_rightDual] at h
  nlinarith [frobeniusPerronDim_nonneg k X]

/-- An object has Frobenius–Perron dimension zero exactly when it is a zero object. -/
@[simp]
theorem frobeniusPerronDim_eq_zero_iff (X : C) : frobeniusPerronDim k X = 0 ↔ IsZero X :=
  ⟨fun h ↦ by_contra fun hX ↦ by linarith [one_le_frobeniusPerronDim k hX],
    frobeniusPerronDim_eq_zero_of_isZero k⟩

/-- An object has positive Frobenius–Perron dimension exactly when it is nonzero. -/
theorem frobeniusPerronDim_pos_iff (X : C) : 0 < frobeniusPerronDim k X ↔ ¬IsZero X := by
  rw [(frobeniusPerronDim_nonneg k X).lt_iff_ne', Ne, frobeniusPerronDim_eq_zero_iff]

end Dim

end TauCeti

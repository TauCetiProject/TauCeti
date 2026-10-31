/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.FrobeniusPerron
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Semisimple

/-!
# Pseudo-unitary fusion categories

Let `C` be a pivotal fusion category over `ℂ`. Reading endomorphisms of the tensor unit as complex
numbers through `TauCeti.endAlgEquivOfSimple ℂ (𝟙_ C)`, its global dimension
`globalDim C = ∑ S, leftDim S ≫ leftDim Sᘁ` is `∑ S, |dim_L S|²`, because the left dimension of
`Sᘁ` is the complex conjugate of that of `S`. Since `|dim_L S| ≤ FPdim S` for every simple `S`, the
global dimension is a nonnegative real number bounded by the Frobenius–Perron dimension
`TauCeti.frobeniusPerronGlobalDim ℂ C = ∑ S, (FPdim S)²` of the category
(`TauCeti.endAlgEquivOfSimple_globalDim` and `TauCeti.norm_globalDim_le_frobeniusPerronGlobalDim`).

The category is **pseudo-unitary** when the two agree. This is a property of `C`: the global
dimension does not depend on the pivotal structure. Comparing the two sums term by term, `C` is
pseudo-unitary exactly when `|dim_L X| = FPdim X` for every simple object `X`.

A pivotal structure whose left dimensions are the Frobenius–Perron dimensions,
`dim_L X = FPdim X` for every simple `X`, witnesses pseudo-unitarity. There is at most one such
pivotal structure, because two pivotal structures with the same nonzero dimensions on the simple
objects are equal, and it is spherical, because its right dimensions `dim_R X = conj (dim_L X)`
are then real and equal to the left ones.

## Main declarations

* `TauCeti.IsPseudoUnitary`: a complex pivotal fusion category is pseudo-unitary when its global
  dimension is its Frobenius–Perron dimension.
* `TauCeti.isPseudoUnitary_iff_norm_leftDim_eq` and
  `TauCeti.isPseudoUnitary_iff_norm_rightDim_eq`: pseudo-unitarity means that the categorical
  dimensions of every simple object have absolute value its Frobenius–Perron dimension.
* `TauCeti.isPseudoUnitary_pivotalCategory_iff`: pseudo-unitarity does not depend on the pivotal
  structure.
* `TauCeti.IsPseudoUnitary.of_leftDim_eq_frobeniusPerronDim`: a pivotal structure whose left
  dimensions are the Frobenius–Perron dimensions makes the category pseudo-unitary;
  `TauCeti.PivotalCategory.eq_of_leftDim_eq_frobeniusPerronDim`: there is at most one such
  pivotal structure; `TauCeti.sphericalCategory_of_leftDim_eq_frobeniusPerronDim`: it is
  spherical.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  §8.4, Proposition 8.23
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §9.4
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace TauCeti

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [RigidCategory C] [Linear ℂ C] [MonoidalLinear ℂ C] [IsFiniteSemisimpleCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)] [EssentiallySmall.{w} C]

section GlobalDim

variable [Fintype (SimpleClasses C)]

/-- A complex pivotal fusion category is **pseudo-unitary** when its global dimension is its
Frobenius–Perron dimension `∑ S, (FPdim S)²`. This does not depend on the pivotal structure
(`TauCeti.isPseudoUnitary_pivotalCategory_iff`). -/
class IsPseudoUnitary [PivotalCategory C] : Prop where
  /-- The global dimension is the Frobenius–Perron dimension of the category. -/
  globalDim_eq : globalDim C = (frobeniusPerronGlobalDim.{w} ℂ C : ℂ) • 𝟙 (𝟙_ C)

section Pivotal

variable [PivotalCategory C]

/-- The defining property of a pseudo-unitary category. -/
theorem isPseudoUnitary_iff_globalDim_eq :
    IsPseudoUnitary.{w} C ↔ globalDim C = (frobeniusPerronGlobalDim.{w} ℂ C : ℂ) • 𝟙 (𝟙_ C) :=
  ⟨fun h ↦ h.globalDim_eq, fun h ↦ ⟨h⟩⟩

variable {C}

/-- A complex pivotal fusion category is pseudo-unitary if and only if the left dimension of every
simple object has absolute value its Frobenius–Perron dimension. -/
theorem isPseudoUnitary_iff_norm_leftDim_eq :
    IsPseudoUnitary.{w} C ↔ ∀ (X : C) [Simple X],
      ‖endAlgEquivOfSimple ℂ (𝟙_ C) (End.of (leftDim X))‖ = frobeniusPerronDim.{w} ℂ X := by
  -- Both dimensions are invariant under isomorphism, so it suffices to test the representatives
  -- of the simple classes.
  have hrepr : (∀ (X : C) [Simple X],
      ‖endAlgEquivOfSimple ℂ (𝟙_ C) (End.of (leftDim X))‖ = frobeniusPerronDim.{w} ℂ X) ↔
      ∀ S : SimpleClasses C, ‖endAlgEquivOfSimple ℂ (𝟙_ C) (End.of (leftDim S.repr))‖ =
        frobeniusPerronDim.{w} ℂ S.repr := by
    refine ⟨fun h S ↦ h S.repr, fun h X _ ↦ ?_⟩
    rw [← leftDim_congr (SimpleClasses.classOfReprIso X),
      ← frobeniusPerronDim_eq_of_iso ℂ (SimpleClasses.classOfReprIso X), h]
  -- The global dimension is `∑ S, |dim_L S|²`, termwise at most `∑ S, (FPdim S)²`.
  have hle (S : SimpleClasses C) :
      ‖endAlgEquivOfSimple ℂ (𝟙_ C) (End.of (leftDim S.repr))‖ ^ 2 ≤
        frobeniusPerronDim.{w} ℂ S.repr ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_leftDim_le_frobeniusPerronDim S.repr) 2
  rw [hrepr]
  calc IsPseudoUnitary.{w} C
      ↔ endAlgEquivOfSimple ℂ (𝟙_ C) (End.of (globalDim C)) = frobeniusPerronGlobalDim.{w} ℂ C :=
        (isPseudoUnitary_iff_globalDim_eq C).trans (endAlgEquivOfSimple_apply_eq_iff _ _).symm
    _ ↔ ∑ S : SimpleClasses C, ‖endAlgEquivOfSimple ℂ (𝟙_ C) (End.of (leftDim S.repr))‖ ^ 2 =
        ∑ S : SimpleClasses C, frobeniusPerronDim.{w} ℂ S.repr ^ 2 := by
      rw [endAlgEquivOfSimple_globalDim, frobeniusPerronGlobalDim_def, Complex.ofReal_inj]
    _ ↔ ∀ S ∈ (Finset.univ : Finset (SimpleClasses C)),
        ‖endAlgEquivOfSimple ℂ (𝟙_ C) (End.of (leftDim S.repr))‖ ^ 2 =
          frobeniusPerronDim.{w} ℂ S.repr ^ 2 :=
      Finset.sum_eq_sum_iff_of_le fun S _ ↦ hle S
    _ ↔ _ := by
      simp only [Finset.mem_univ, true_implies]
      exact forall_congr' fun S ↦ sq_eq_sq₀ (norm_nonneg _) (frobeniusPerronDim_nonneg ℂ S.repr)

/-- A complex pivotal fusion category is pseudo-unitary if and only if the right dimension of every
simple object has absolute value its Frobenius–Perron dimension. -/
theorem isPseudoUnitary_iff_norm_rightDim_eq :
    IsPseudoUnitary.{w} C ↔ ∀ (X : C) [Simple X],
      ‖endAlgEquivOfSimple ℂ (𝟙_ C) (End.of (rightDim X))‖ = frobeniusPerronDim.{w} ℂ X := by
  simp only [norm_rightDim_eq_norm_leftDim, isPseudoUnitary_iff_norm_leftDim_eq]

/-- A complex pivotal fusion category is pseudo-unitary as soon as the left dimension of every
simple object is its Frobenius–Perron dimension. -/
theorem IsPseudoUnitary.of_leftDim_eq_frobeniusPerronDim
    (h : ∀ (X : C) [Simple X], leftDim X = (frobeniusPerronDim.{w} ℂ X : ℂ) • 𝟙 (𝟙_ C)) :
    IsPseudoUnitary.{w} C :=
  isPseudoUnitary_iff_norm_leftDim_eq.2 fun X _ ↦ by
    rw [(endAlgEquivOfSimple_apply_eq_iff _ _).2 (h X), Complex.norm_real,
      Real.norm_of_nonneg (frobeniusPerronDim_nonneg ℂ X)]

end Pivotal

/-- Pseudo-unitarity of a complex fusion category does not depend on the pivotal structure used
to define the global dimension. -/
theorem isPseudoUnitary_pivotalCategory_iff (P Q : PivotalCategory C) :
    @IsPseudoUnitary.{w} C _ _ _ _ _ _ _ _ _ _ _ _ P ↔
      @IsPseudoUnitary.{w} C _ _ _ _ _ _ _ _ _ _ _ _ Q := by
  rw [isPseudoUnitary_iff_globalDim_eq, isPseudoUnitary_iff_globalDim_eq,
    globalDim_pivotalCategory_eq C ℂ P Q]

end GlobalDim

variable {C} [Finite (SimpleClasses C)]

/-- If the left dimension of every simple object of a complex pivotal fusion category is its
Frobenius–Perron dimension, then the pivotal structure is spherical. -/
theorem sphericalCategory_of_leftDim_eq_frobeniusPerronDim [PivotalCategory C]
    (h : ∀ (X : C) [Simple X], leftDim X = (frobeniusPerronDim.{w} ℂ X : ℂ) • 𝟙 (𝟙_ C)) :
    SphericalCategory C :=
  (sphericalCategory_iff_leftDim_eq_rightDim ℂ).2 fun X _ ↦ by
    -- The right dimension character is the conjugate of the left one, and the Frobenius–Perron
    -- dimension is real.
    have hX : SplitK0.leftDimChar.{w} ℂ C (SplitK0.of X) = frobeniusPerronDim.{w} ℂ X := by
      rw [SplitK0.leftDimChar_of, endAlgEquivOfSimple_apply_eq_iff, h X]
    rw [← SplitK0.leftDimChar_of_smul_id.{w} ℂ X, ← SplitK0.rightDimChar_of_smul_id.{w} ℂ X,
      SplitK0.rightDimChar_apply_eq_conj, hX, Complex.conj_ofReal]

/-- A complex fusion category has at most one pivotal structure whose left dimension of every
simple object is its Frobenius–Perron dimension. -/
theorem PivotalCategory.eq_of_leftDim_eq_frobeniusPerronDim {P Q : PivotalCategory C}
    (hP : ∀ (X : C) [Simple X],
      @leftDim C _ _ _ P X = (frobeniusPerronDim.{w} ℂ X : ℂ) • 𝟙 (𝟙_ C))
    (hQ : ∀ (X : C) [Simple X],
      @leftDim C _ _ _ Q X = (frobeniusPerronDim.{w} ℂ X : ℂ) • 𝟙 (𝟙_ C)) :
    P = Q :=
  ext_of_leftDim ℂ (fun X _ ↦ (hP X).trans (hQ X).symm) fun X _ ↦ by
    rw [hQ X]
    exact smul_ne_zero (Complex.ofReal_ne_zero.2 (frobeniusPerronDim_pos_of_simple ℂ X).ne')
      (id_nonzero _)

end TauCeti

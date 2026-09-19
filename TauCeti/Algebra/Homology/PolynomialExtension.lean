/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.RingDivision
public import TauCeti.Algebra.Homology.HomotopyCofiber

/-!
# Mapping cones of `X - a` on a polynomial extension of a complex

Let `K` be a complex of modules over a commutative ring `A`. Its polynomial extension
`K[X] = A[X] ⊗[A] K` is again a complex of `A`-modules, and multiplication by any polynomial
`p : A[X]` is a chain endomorphism of it. For `a : A`, the mapping cone of multiplication by
`X - a` on `K[X]` is homotopy equivalent to `K`.

The reason is that the short exact sequence of `A`-modules

`0 ⟶ A[X] ⟶ A[X] ⟶ A ⟶ 0`,

given by multiplication by `X - a` followed by evaluation at `a`, is split by division by `X - a`
and by the inclusion of constants. Tensoring with `K` keeps it split in the category of complexes,
so `CategoryTheory.ShortComplex.Splitting.homotopyCofiberHomotopyEquiv` applies.

This is the algebra behind the stabilization invariance of grid homology: the complex of a
stabilized grid diagram is identified with the mapping cone of `V₁ - V₂` on the polynomial
extension `GC⁻(G)[V₁]` of the complex of the original diagram, and the homotopy equivalence here
compares that cone with `GC⁻(G)` itself.

## Main definitions

* `HomologicalComplex.polynomialExtension`: the complex `A[X] ⊗[A] K`.
* `HomologicalComplex.polynomialExtensionMul`: multiplication by a polynomial on `A[X] ⊗[A] K`.
* `HomologicalComplex.polynomialExtensionEval`: evaluation at `a`, a chain map `A[X] ⊗[A] K ⟶ K`.
* `HomologicalComplex.polynomialExtensionConst`: the inclusion `K ⟶ A[X] ⊗[A] K` of constants.
* `HomologicalComplex.polynomialExtensionMulXSubCHomotopyEquiv`: the homotopy equivalence between
  the mapping cone of multiplication by `X - C a` and `K`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, Section 5.2.
-/

public section

open CategoryTheory Category MonoidalCategory Polynomial

universe u

namespace HomologicalComplex

variable {A : Type u} [CommRing A] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{u} A) c)

/-- The polynomial extension `A[X] ⊗[A] K` of a complex `K` of `A`-modules: its terms are
`A[X] ⊗[A] K.X i` and its differentials are `A[X] ⊗ K.d i j`. -/
noncomputable abbrev polynomialExtension : HomologicalComplex (ModuleCat.{u} A) c :=
  ((tensorLeft (ModuleCat.of A A[X])).mapHomologicalComplex c).obj K

/-- Multiplication by a polynomial `p : A[X]` on the polynomial extension `A[X] ⊗[A] K`. -/
noncomputable def polynomialExtensionMul (p : A[X]) :
    K.polynomialExtension ⟶ K.polynomialExtension :=
  (NatTrans.mapHomologicalComplex
    ((curriedTensor _).map (ModuleCat.ofHom (LinearMap.mulLeft A p))) c).app K

/-- Multiplication by `p` acts on `A[X] ⊗ K.X i` through the first factor. -/
@[simp]
theorem polynomialExtensionMul_f (p : A[X]) (i : ι) :
    (K.polynomialExtensionMul p).f i = ModuleCat.ofHom (LinearMap.mulLeft A p) ▷ K.X i :=
  (rfl)

/-- Multiplication by the zero polynomial is the zero chain map. -/
@[simp]
theorem polynomialExtensionMul_zero : K.polynomialExtensionMul 0 = 0 := by
  ext i : 1
  simp

/-- Multiplication by the constant polynomial `1` is the identity chain map. -/
@[simp]
theorem polynomialExtensionMul_one : K.polynomialExtensionMul 1 = 𝟙 _ := by
  ext i : 1
  simp

/-- Multiplication by a sum of polynomials is the sum of their multiplication chain maps. -/
@[simp]
theorem polynomialExtensionMul_add (p q : A[X]) :
    K.polynomialExtensionMul (p + q) = K.polynomialExtensionMul p + K.polynomialExtensionMul q := by
  ext i : 1
  have h : LinearMap.mulLeft A (p + q) =
      LinearMap.mulLeft A p + LinearMap.mulLeft A q := by
    apply LinearMap.ext
    intro r
    simp only [LinearMap.add_apply, LinearMap.mulLeft_apply, add_mul]
  simp [h]

/-- Multiplication by the negative of a polynomial is the negative multiplication chain map. -/
@[simp]
theorem polynomialExtensionMul_neg (p : A[X]) :
    K.polynomialExtensionMul (-p) = -K.polynomialExtensionMul p := by
  apply eq_neg_of_add_eq_zero_left
  rw [← K.polynomialExtensionMul_add]
  simp

/-- Composing multiplication by two polynomials is multiplication by their product. -/
@[simp]
theorem polynomialExtensionMul_comp (p q : A[X]) :
    K.polynomialExtensionMul p ≫ K.polynomialExtensionMul q = K.polynomialExtensionMul (p * q) := by
  ext i : 1
  have h : ModuleCat.ofHom (LinearMap.mulLeft A p) ≫
      ModuleCat.ofHom (LinearMap.mulLeft A q) =
      ModuleCat.ofHom (LinearMap.mulLeft A (p * q)) :=
    ModuleCat.hom_ext <| LinearMap.ext fun r ↦ by
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        LinearMap.mulLeft_apply]
      ac_rfl
  simp [← comp_whiskerRight, h]

/-- Evaluation at `a : A`, as the chain map `A[X] ⊗[A] K ⟶ K`. -/
noncomputable def polynomialExtensionEval (a : A) : K.polynomialExtension ⟶ K where
  f i := ModuleCat.ofHom (Polynomial.leval a) ▷ K.X i ≫ (λ_ (K.X i)).hom
  comm' i j _ := by
    simp only [Functor.mapHomologicalComplex_obj_d, curriedTensor_obj_map, assoc]
    rw [← leftUnitor_naturality]
    exact (whisker_exchange_assoc _ _ _).symm

/-- Evaluation at `a` evaluates the first tensor factor of `A[X] ⊗ K.X i`. -/
@[simp]
theorem polynomialExtensionEval_f (a : A) (i : ι) :
    (K.polynomialExtensionEval a).f i =
      ModuleCat.ofHom (Polynomial.leval a) ▷ K.X i ≫ (λ_ (K.X i)).hom :=
  (rfl)

/-- The inclusion of `K` into `A[X] ⊗[A] K` as the constant polynomials. -/
noncomputable def polynomialExtensionConst : K ⟶ K.polynomialExtension where
  f i := (λ_ (K.X i)).inv ≫ ModuleCat.ofHom (Algebra.linearMap A A[X]) ▷ K.X i
  comm' i j _ := by
    simp only [Functor.mapHomologicalComplex_obj_d, curriedTensor_obj_map, assoc]
    rw [leftUnitor_inv_naturality_assoc]
    exact _ ≫= (whisker_exchange _ _).symm

/-- The inclusion of constants sends `x : K.X i` to `1 ⊗ x`. -/
@[simp]
theorem polynomialExtensionConst_f (i : ι) :
    K.polynomialExtensionConst.f i =
      (λ_ (K.X i)).inv ≫ ModuleCat.ofHom (Algebra.linearMap A A[X]) ▷ K.X i :=
  (rfl)

/-- Evaluation at `a` kills the multiples of `X - C a`. -/
@[reassoc (attr := simp)]
theorem polynomialExtensionMul_X_sub_C_comp_polynomialExtensionEval (a : A) :
    K.polynomialExtensionMul (Polynomial.X - C a) ≫ K.polynomialExtensionEval a = 0 := by
  ext i : 1
  have : ModuleCat.ofHom (LinearMap.mulLeft A (Polynomial.X - C a)) ≫
      ModuleCat.ofHom (Polynomial.leval a) = 0 :=
    ModuleCat.hom_ext <| LinearMap.ext fun p ↦ by simp
  simp [← comp_whiskerRight_assoc, this]

/-- A constant polynomial evaluates to itself. -/
@[reassoc (attr := simp)]
theorem polynomialExtensionConst_comp_polynomialExtensionEval (a : A) :
    K.polynomialExtensionConst ≫ K.polynomialExtensionEval a = 𝟙 K := by
  ext i : 1
  have : ModuleCat.ofHom (Algebra.linearMap A A[X]) ≫ ModuleCat.ofHom (Polynomial.leval a) =
      𝟙 (ModuleCat.of A A) :=
    ModuleCat.hom_ext <| LinearMap.ext fun r ↦ by simp
  simp [← comp_whiskerRight_assoc, this]

/-- Multiplication by `X - C a` followed by evaluation at `a`, as a short complex of complexes. -/
private noncomputable abbrev evalShortComplex (a : A) :
    ShortComplex (HomologicalComplex (ModuleCat.{u} A) c) :=
  ShortComplex.mk _ _ (K.polynomialExtensionMul_X_sub_C_comp_polynomialExtensionEval a)

/-- The splitting of `evalShortComplex K a` by division by `X - C a` and by constants. -/
private noncomputable def evalShortComplexSplitting (a : A) : (K.evalShortComplex a).Splitting where
  r := (NatTrans.mapHomologicalComplex
    ((curriedTensor _).map (ModuleCat.ofHom (divByMonicHom (Polynomial.X - C a)))) c).app K
  s := K.polynomialExtensionConst
  f_r := by
    ext i : 1
    have : ModuleCat.ofHom (LinearMap.mulLeft A (Polynomial.X - C a)) ≫
        ModuleCat.ofHom (divByMonicHom (Polynomial.X - C a)) = 𝟙 _ :=
      ModuleCat.hom_ext <| LinearMap.ext fun p ↦ by
        simp [mul_divByMonic_cancel_left p (monic_X_sub_C a)]
    simp [← comp_whiskerRight, this]
  s_g := K.polynomialExtensionConst_comp_polynomialExtensionEval a
  id := by
    ext i : 1
    have : ModuleCat.ofHom (divByMonicHom (Polynomial.X - C a)) ≫
        ModuleCat.ofHom (LinearMap.mulLeft A (Polynomial.X - C a)) +
          ModuleCat.ofHom (Polynomial.leval a) ≫ ModuleCat.ofHom (Algebra.linearMap A A[X]) =
        𝟙 _ :=
      ModuleCat.hom_ext <| LinearMap.ext fun p ↦ by
        simpa [← modByMonic_X_sub_C_eq_C_eval, add_comm] using
          modByMonic_add_div p (Polynomial.X - C a)
    simp [← comp_whiskerRight, ← MonoidalPreadditive.add_whiskerRight, this]

/-- The mapping cone of multiplication by `X - C a` on the polynomial extension `A[X] ⊗[A] K` is
homotopy equivalent to `K`, provided every index of the complex shape is the target of a
relation. The map from the cone is induced by evaluation at `a`, and its homotopy inverse is the
inclusion of the constant polynomials. -/
noncomputable def polynomialExtensionMulXSubCHomotopyEquiv [DecidableRel c.Rel]
    (hc : ∀ j, ∃ i, c.Rel i j) (a : A) :
    HomotopyEquiv (homotopyCofiber (K.polynomialExtensionMul (Polynomial.X - C a))) K :=
  (K.evalShortComplexSplitting a).homotopyCofiberHomotopyEquiv hc

/-- The map from the mapping cone in `polynomialExtensionMulXSubCHomotopyEquiv` is induced by
evaluation at `a`. -/
@[simp]
theorem polynomialExtensionMulXSubCHomotopyEquiv_hom [DecidableRel c.Rel]
    (hc : ∀ j, ∃ i, c.Rel i j) (a : A) :
    (K.polynomialExtensionMulXSubCHomotopyEquiv hc a).hom =
      homotopyCofiber.desc _ (K.polynomialExtensionEval a)
        (Homotopy.ofEq (K.polynomialExtensionMul_X_sub_C_comp_polynomialExtensionEval a)) :=
  (K.evalShortComplexSplitting a).homotopyCofiberHomotopyEquiv_hom hc

/-- The homotopy inverse in `polynomialExtensionMulXSubCHomotopyEquiv` is the inclusion of the
constant polynomials into the `A[X] ⊗[A] K`-summand of the mapping cone. -/
@[simp]
theorem polynomialExtensionMulXSubCHomotopyEquiv_inv [DecidableRel c.Rel]
    (hc : ∀ j, ∃ i, c.Rel i j) (a : A) :
    (K.polynomialExtensionMulXSubCHomotopyEquiv hc a).inv =
      K.polynomialExtensionConst ≫ homotopyCofiber.inr _ :=
  (K.evalShortComplexSplitting a).homotopyCofiberHomotopyEquiv_inv hc

end HomologicalComplex

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import TauCeti.CategoryTheory.Linear.Endomorphism
public import TauCeti.Combinatorics.PlanarMatching.Category
import Mathlib.Data.ZMod.Basic
import TauCeti.Combinatorics.PlanarMatching.DyckWord

/-!
# The linear Temperley–Lieb category

Given a commutative ring `R` and a loop value `δ : R`, the **linear Temperley–Lieb category**
`TauCeti.TLCat R δ` has one object `TLCat.of n` for each natural number `n` of boundary points, and
its morphism module `X ⟶ Y` is the free `R`-module on the circle-free Temperley–Lieb diagrams from
`X.as` bottom points to `Y.as` top points — that is, on `TauCeti.PlanarMatching (X.as + Y.as)`.
Two basis matchings `x : PlanarMatching (X.as + Y.as)` and `y : PlanarMatching (Y.as + Z.as)`
compose by gluing along the `Y.as` middle points and evaluating each closed circle at `δ`:

`diagBasis X Y x ≫ diagBasis Y Z y =
  δ ^ glueMiddleCircles Y.as (x.append y) • diagBasis X Z (glueMiddle Y.as (x.append y))`.

Associativity and the identity laws follow directly from the diagram-level associativity and unit
laws of `TauCeti.TLDiagram.comp`, because gluing matchings without initial circles records both the
glued matching and the number of circles closed in the middle.

The combinatorial diagram category `TauCeti.TLDiagCat`, which keeps closed circles as a formal count
rather than evaluating them, maps to `TLCat R δ` at every loop value `δ` through the functor
`TauCeti.TLCat.linearize R δ : TLDiagCat ⥤ TLCat R δ` sending a diagram `D` with `c` circles to
`δ ^ c` times its underlying matching. Together with `TauCeti.TLCat.liftDiag`, this presents
`TLCat R δ` by its universal property among functors from `TLDiagCat` into `R`-linear categories
that evaluate each closed circle to `δ`.

At the empty boundary `of 0`, the endomorphism `R`-algebra is canonically isomorphic to `R`
(`TauCeti.TLCat.endZeroAlgEquiv`), and the closed circle in `TLDiagCat` maps to `δ • 𝟙 (of 0)`. The
cup `of 0 ⟶ of 2` is always a monomorphism and the cap `of 2 ⟶ of 0` is always an epimorphism, for
every `R` and `δ`, whereas `cup ≫ cap = δ • 𝟙 (of 0)` is a monomorphism (or epimorphism) if and
only if `δ ∈ nonZeroDivisors R`, and an isomorphism if and only if `IsUnit δ`.

## Main definitions

* `TauCeti.TLCat R δ`: the `R`-linear Temperley–Lieb category at loop value `δ`, with objects
  `TLCat.of n` and morphisms represented by `TauCeti.TLCat.Hom.coeff`.
* `TauCeti.TLCat.diagBasis X Y`: the `R`-basis of `X ⟶ Y` indexed by
  `PlanarMatching (X.as + Y.as)`.
* `TauCeti.TLCat.linearize R δ`: the functor `TLDiagCat ⥤ TLCat R δ` evaluating each closed circle
  at `δ`.
* `TauCeti.TLCat.liftDiag`: the universal property extending a circle-evaluating functor
  `TLDiagCat ⥤ D` into an `R`-linear category `D` to an additive `R`-linear functor `TLCat R δ ⥤ D`.
* `TauCeti.TLCat.cup`, `TauCeti.TLCat.cap`: the cup `of 0 ⟶ of 2` and cap `of 2 ⟶ of 0`.
* `TauCeti.TLCat.endZeroAlgEquiv`: the `R`-algebra isomorphism `End (of 0) ≃ₐ[R] R`.
* `TauCeti.TLCat.dragRight`, `TauCeti.TLCat.dragLeft`, `TauCeti.TLCat.rotateHom`,
  `TauCeti.TLCat.verticalReflectHom`, `TauCeti.TLCat.reflectHom`: the linear equivalences on
  morphism modules induced by corner-dragging, counterclockwise rotation, and vertical and
  horizontal reflection of diagrams.
* `TauCeti.TLCat.mapRingHom`: the additive base-change functor `TLCat R δ ⥤ TLCat S δ'` along a ring
  homomorphism `φ : R →+* S` with `φ δ = δ'`.

## Main results

* `TauCeti.TLCat.diagBasis_comp_diagBasis`: **the loop rule** on basis matchings.
* `TauCeti.TLCat.finrank_hom_of_add_eq_two_mul`, `TauCeti.TLCat.finrank_end_of`: when
  `X.as + Y.as = 2 * k`, the module `X ⟶ Y` is free of rank `catalan k`; in particular `End (of n)`
  has rank `catalan n`, and `X ⟶ Y` vanishes when `X.as + Y.as` is odd.
* `TauCeti.TLCat.cup_comp_cap`: `cup ≫ cap = δ • 𝟙 (of 0)`.
* `TauCeti.TLCat.mono_diagBasis_zero_left`, `TauCeti.TLCat.epi_diagBasis_zero_right`: every basis
  morphism out of `of 0` is a monomorphism and every basis morphism into `of 0` is an epimorphism
  (in particular `Mono cup` and `Epi cap` for every `R` and `δ`), whereas `cap` is never a
  monomorphism and `cup` is never an epimorphism over a nontrivial ring.
* `TauCeti.TLCat.mono_smul_id_zero_iff`, `TauCeti.TLCat.isIso_smul_id_zero_iff`: `r • 𝟙 (of 0)` is a
  monomorphism (or epimorphism) iff `r ∈ nonZeroDivisors R`, and an isomorphism iff `IsUnit r`.

## Implementation notes

Mathlib's `CategoryTheory.Linear R C` requires `Preadditive C`, which equips each hom-set with an
`AddCommGroup` structure, and compatibility of composition with scalar multiplication on both sides
at `End (of 0) ≃ R` requires `R` to be commutative; accordingly the category, preadditive and
`R`-linear instances on `TLCat R δ` are registered uniformly over `[CommRing R]`, using the global
`Preadditive.homGroup` and `Linear.homModule` instances so that no `AddCommGroup` or `Module`
diamonds can arise on morphism types or on `TLCat ℤ δ`.

Objects live in `Type` while morphism modules `X ⟶ Y` live in `Type u` for `R : Type u`, wrapped in
one-field structures `TLCat` and `TLCat.Hom` (matching `TauCeti.TLDiagCat` and
`TauCeti.BrauerAlgebra`).

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v

/-- The **linear Temperley–Lieb category** over a commutative ring `R` at loop value `δ : R`.
An object `TLCat.of n` represents `n` boundary points, and a morphism `X ⟶ Y` is a formal
`R`-linear combination of planar matchings of `X.as + Y.as` points (`TauCeti.TLCat.diagBasis`),
composed by gluing along the middle boundary and weighting each closed circle by `δ`. -/
@[ext]
structure TLCat (R : Type u) (δ : R) : Type where
  /-- The object of the linear Temperley–Lieb category with `n` boundary points. -/
  of ::
  /-- The number of boundary points of an object of the linear Temperley–Lieb category. -/
  as : ℕ

namespace TLCat

section Objects

variable {R : Type u} {δ : R}

instance : DecidableEq (TLCat R δ) :=
  fun X Y => decidable_of_iff (X.as = Y.as) TLCat.ext_iff.symm

@[simp]
theorem of_as (X : TLCat R δ) : of X.as = X := (rfl)

theorem of_injective : Function.Injective (of (R := R) (δ := δ)) :=
  fun _ _ h => congrArg as h

theorem of_inj {n m : ℕ} : (of n : TLCat R δ) = of m ↔ n = m :=
  of_injective.eq_iff

end Objects

/-! ### Morphisms and loop-weighted composition -/

/-- A morphism `X ⟶ Y` of the linear Temperley–Lieb category: its coefficients in the basis of
planar matchings of the `X.as + Y.as` boundary points. -/
@[ext]
structure Hom {R : Type u} [Zero R] {δ : R} (X Y : TLCat R δ) : Type u where
  /-- The morphism with the given coefficients in the planar-matching basis. -/
  ofCoeff ::
  /-- The coefficients of a morphism in the planar-matching basis. -/
  coeff : PlanarMatching (X.as + Y.as) →₀ R

section Category

variable {R : Type u} [CommRing R] {δ : R}

@[simp]
theorem Hom.coeff_ofCoeff {X Y : TLCat R δ} (f : PlanarMatching (X.as + Y.as) →₀ R) :
    (Hom.ofCoeff f : Hom X Y).coeff = f := (rfl)

@[simp]
theorem Hom.ofCoeff_coeff {X Y : TLCat R δ} (f : Hom X Y) :
    Hom.ofCoeff f.coeff = f := (rfl)

/-- Loop-weighted gluing of planar-matching coefficient vectors, bilinear in both arguments:
on basis vectors `(x, y)` it produces `δ ^ glueMiddleCircles m (x.append y)` times the basis
vector of `glueMiddle m (x.append y)`. -/
noncomputable def compCoeff (δ : R) {n m p : ℕ} :
    (PlanarMatching (n + m) →₀ R) →ₗ[R]
      (PlanarMatching (m + p) →₀ R) →ₗ[R]
        (PlanarMatching (n + p) →₀ R) :=
  Finsupp.lsum R fun x => LinearMap.smulRight LinearMap.id
    (Finsupp.lsum R fun y =>
      δ ^ PlanarMatching.glueMiddleCircles m (x.append y) •
        Finsupp.lsingle (PlanarMatching.glueMiddle m (x.append y)))

/-- Loop-weighted gluing on two basis vectors of planar-matching coefficients. -/
theorem compCoeff_single_single (δ : R) {n m p : ℕ}
    (x : PlanarMatching (n + m)) (y : PlanarMatching (m + p)) (a b : R) :
    compCoeff δ (Finsupp.single x a) (Finsupp.single y b) =
      Finsupp.single (PlanarMatching.glueMiddle m (x.append y))
        (δ ^ PlanarMatching.glueMiddleCircles m (x.append y) * (a * b)) := by
  simp only [compCoeff, Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_apply,
    LinearMap.smul_apply, Finsupp.lsingle_apply, Finsupp.smul_single, smul_eq_mul]
  congr 1
  ring

/-- Associativity of loop-weighted gluing on coefficients, inherited from
`TauCeti.TLDiagram.comp_assoc`. -/
theorem compCoeff_assoc (δ : R) {n m p q : ℕ}
    (f : PlanarMatching (n + m) →₀ R) (g : PlanarMatching (m + p) →₀ R)
    (h : PlanarMatching (p + q) →₀ R) :
    compCoeff δ (compCoeff δ f g) h = compCoeff δ f (compCoeff δ g h) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | single x a =>
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | single y b =>
  induction h using Finsupp.induction_linear with
  | zero => simp
  | add h₁ h₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | single z c =>
  have hassoc := TLDiagram.comp_assoc (⟨x, 0⟩ : TLDiagram n m) ⟨y, 0⟩ ⟨z, 0⟩
  have hm : PlanarMatching.glueMiddle p ((PlanarMatching.glueMiddle m (x.append y)).append z) =
      PlanarMatching.glueMiddle m (x.append (PlanarMatching.glueMiddle p (y.append z))) := by
    simpa [TLDiagram.matching_comp] using congrArg TLDiagram.matching hassoc
  have hc : PlanarMatching.glueMiddleCircles m (x.append y) +
        PlanarMatching.glueMiddleCircles p
          ((PlanarMatching.glueMiddle m (x.append y)).append z) =
      PlanarMatching.glueMiddleCircles p (y.append z) +
        PlanarMatching.glueMiddleCircles m
          (x.append (PlanarMatching.glueMiddle p (y.append z))) := by
    simpa [TLDiagram.circles_comp, add_comm] using congrArg TLDiagram.circles hassoc
  simp only [compCoeff_single_single, hm]
  congr 1
  calc δ ^ PlanarMatching.glueMiddleCircles p
          ((PlanarMatching.glueMiddle m (x.append y)).append z) *
        (δ ^ PlanarMatching.glueMiddleCircles m (x.append y) * (a * b) * c)
      = δ ^ (PlanarMatching.glueMiddleCircles m (x.append y) +
          PlanarMatching.glueMiddleCircles p
            ((PlanarMatching.glueMiddle m (x.append y)).append z)) * (a * b * c) := by
        rw [pow_add]; ring
    _ = δ ^ PlanarMatching.glueMiddleCircles m
          (x.append (PlanarMatching.glueMiddle p (y.append z))) *
        (a * (δ ^ PlanarMatching.glueMiddleCircles p (y.append z) * (b * c))) := by
        rw [hc, pow_add]; ring

/-- The nested matching is a left unit for loop-weighted gluing on coefficients. -/
theorem compCoeff_id_left (δ : R) {n m : ℕ} (f : PlanarMatching (n + m) →₀ R) :
    compCoeff δ (Finsupp.single (PlanarMatching.nested n) 1) f = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | single x a => simp [compCoeff_single_single]

/-- The nested matching is a right unit for loop-weighted gluing on coefficients. -/
theorem compCoeff_id_right (δ : R) {n m : ℕ} (f : PlanarMatching (n + m) →₀ R) :
    compCoeff δ f (Finsupp.single (PlanarMatching.nested m) 1) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | single x a => simp [compCoeff_single_single]

noncomputable instance : Category.{u} (TLCat R δ) where
  Hom := Hom
  id X := ⟨Finsupp.single (PlanarMatching.nested X.as) 1⟩
  comp f g := ⟨compCoeff δ f.coeff g.coeff⟩
  id_comp f := Hom.ext (compCoeff_id_left δ f.coeff)
  comp_id f := Hom.ext (compCoeff_id_right δ f.coeff)
  assoc f g h := Hom.ext (compCoeff_assoc δ f.coeff g.coeff h.coeff)

variable {X Y Z : TLCat R δ}

/-- Two morphisms of `TLCat R δ` are equal when their planar-matching coefficients are equal. -/
@[ext]
theorem hom_ext {f g : X ⟶ Y} (h : f.coeff = g.coeff) : f = g :=
  Hom.ext h

/-- The coefficients of the identity morphism `𝟙 X`: `1` on the nested matching and `0`
elsewhere. -/
@[simp]
theorem coeff_id (X : TLCat R δ) :
    (𝟙 X : X ⟶ X).coeff = Finsupp.single (PlanarMatching.nested X.as) 1 := (rfl)

/-- The coefficients of a composite `f ≫ g` are given by `compCoeff`. -/
theorem coeff_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).coeff = compCoeff δ f.coeff g.coeff := (rfl)

/-- Equivalence between morphisms `X ⟶ Y` and finitely supported coefficient functions on
`PlanarMatching (X.as + Y.as)`. -/
def coeffEquiv (X Y : TLCat R δ) : (X ⟶ Y) ≃ (PlanarMatching (X.as + Y.as) →₀ R) where
  toFun f := f.coeff
  invFun f := Hom.ofCoeff f
  left_inv _ := (rfl)
  right_inv _ := (rfl)

@[simp]
theorem coeffEquiv_apply (f : X ⟶ Y) : coeffEquiv X Y f = f.coeff := (rfl)

@[simp]
theorem coeffEquiv_symm_apply (f : PlanarMatching (X.as + Y.as) →₀ R) :
    (coeffEquiv X Y).symm f = Hom.ofCoeff f := (rfl)

noncomputable instance [DecidableEq R] (X Y : TLCat R δ) : DecidableEq (X ⟶ Y) :=
  (coeffEquiv X Y).decidableEq

noncomputable instance : Preadditive (TLCat R δ) where
  homGroup X Y := (coeffEquiv X Y).addCommGroup
  add_comp _ _ _ f₁ f₂ g := hom_ext <| by
    simp only [coeff_comp]
    exact LinearMap.congr_fun (map_add (compCoeff δ) f₁.coeff f₂.coeff) g.coeff
  comp_add _ _ _ f g₁ g₂ := hom_ext <| by
    simp only [coeff_comp]
    exact map_add (compCoeff δ f.coeff) g₁.coeff g₂.coeff

@[simp]
theorem coeff_zero : (0 : X ⟶ Y).coeff = 0 := (rfl)

@[simp]
theorem coeff_add (f g : X ⟶ Y) : (f + g).coeff = f.coeff + g.coeff := (rfl)

@[simp]
theorem coeff_neg (f : X ⟶ Y) : (-f).coeff = -f.coeff := (rfl)

@[simp]
theorem coeff_sub (f g : X ⟶ Y) : (f - g).coeff = f.coeff - g.coeff := (rfl)

@[simp]
theorem coeff_nsmul (n : ℕ) (f : X ⟶ Y) : (n • f).coeff = n • f.coeff := (rfl)

@[simp]
theorem coeff_zsmul (n : ℤ) (f : X ⟶ Y) : (n • f).coeff = n • f.coeff := (rfl)

/-- Additive equivalence between morphisms `X ⟶ Y` and finitely supported coefficient functions on
`PlanarMatching (X.as + Y.as)`. -/
noncomputable def coeffAddEquiv (X Y : TLCat R δ) :
    (X ⟶ Y) ≃+ (PlanarMatching (X.as + Y.as) →₀ R) :=
  (coeffEquiv X Y).addEquiv

@[simp]
theorem coeffAddEquiv_apply (f : X ⟶ Y) : coeffAddEquiv X Y f = f.coeff := (rfl)

@[simp]
theorem coeffAddEquiv_symm_apply (f : PlanarMatching (X.as + Y.as) →₀ R) :
    (coeffAddEquiv X Y).symm f = Hom.ofCoeff f := (rfl)

@[simp]
theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (∑ i ∈ s, f i).coeff = ∑ i ∈ s, (f i).coeff :=
  map_sum (coeffAddEquiv X Y) f s

noncomputable instance : CategoryTheory.Linear R (TLCat R δ) where
  homModule X Y := (coeffAddEquiv X Y).module R
  smul_comp _ _ _ r f g := hom_ext <| by
    simp only [coeff_comp]
    exact LinearMap.congr_fun ((compCoeff δ).map_smul r f.coeff) g.coeff
  comp_smul _ _ _ f r g := hom_ext <| by
    simp only [coeff_comp]
    exact (compCoeff δ f.coeff).map_smul r g.coeff

@[simp]
theorem coeff_smul (r : R) (f : X ⟶ Y) : (r • f).coeff = r • f.coeff := (rfl)

/-- `R`-linear equivalence between morphisms `X ⟶ Y` and finitely supported coefficient functions
on `PlanarMatching (X.as + Y.as)`. -/
noncomputable def coeffLinearEquiv (X Y : TLCat R δ) :
    (X ⟶ Y) ≃ₗ[R] (PlanarMatching (X.as + Y.as) →₀ R) :=
  (coeffAddEquiv X Y).linearEquiv R

@[simp]
theorem coeffLinearEquiv_apply (f : X ⟶ Y) : coeffLinearEquiv X Y f = f.coeff := (rfl)

@[simp]
theorem coeffLinearEquiv_symm_apply (f : PlanarMatching (X.as + Y.as) →₀ R) :
    (coeffLinearEquiv X Y).symm f = Hom.ofCoeff f := (rfl)

/-! ### The diagram basis and Hom-module ranks -/

/-- **The diagram basis** of `X ⟶ Y` in `TLCat R δ`, indexed by the planar matchings of the
`X.as + Y.as` boundary points. -/
noncomputable def diagBasis (X Y : TLCat R δ) :
    Module.Basis (PlanarMatching (X.as + Y.as)) R (X ⟶ Y) :=
  .ofRepr (coeffLinearEquiv X Y)

@[simp]
theorem diagBasis_repr (f : X ⟶ Y) : (diagBasis X Y).repr f = f.coeff := (rfl)

@[simp]
theorem coeff_diagBasis (x : PlanarMatching (X.as + Y.as)) :
    (diagBasis X Y x).coeff = Finsupp.single x 1 := by
  simp [diagBasis]

@[simp]
theorem ofCoeff_single (x : PlanarMatching (X.as + Y.as)) (r : R) :
    (Hom.ofCoeff (Finsupp.single x r) : X ⟶ Y) = r • diagBasis X Y x :=
  hom_ext <| by simp [Finsupp.smul_single]

/-- The identity morphism `𝟙 X` is the basis element of the nested planar matching. -/
theorem id_eq_diagBasis (X : TLCat R δ) :
    (𝟙 X : X ⟶ X) = diagBasis X X (PlanarMatching.nested X.as) :=
  hom_ext <| by simp

/-- **The loop rule.** Composing two planar-matching basis morphisms glues their matchings along
the middle boundary and multiplies by `δ` raised to the number of closed circles formed there. -/
@[simp, reassoc]
theorem diagBasis_comp_diagBasis (x : PlanarMatching (X.as + Y.as))
    (y : PlanarMatching (Y.as + Z.as)) :
    diagBasis X Y x ≫ diagBasis Y Z y =
      δ ^ PlanarMatching.glueMiddleCircles Y.as (x.append y) •
        diagBasis X Z (PlanarMatching.glueMiddle Y.as (x.append y)) :=
  hom_ext <| by simp [coeff_comp, compCoeff_single_single, Finsupp.smul_single]

/-- When gluing `x` and `y` along `Y` closes no circle, their composite is the glued matching
with no scalar factor. -/
theorem diagBasis_comp_diagBasis_of_glueMiddleCircles_eq_zero
    {x : PlanarMatching (X.as + Y.as)} {y : PlanarMatching (Y.as + Z.as)}
    (h : PlanarMatching.glueMiddleCircles Y.as (x.append y) = 0) :
    diagBasis X Y x ≫ diagBasis Y Z y =
      diagBasis X Z (PlanarMatching.glueMiddle Y.as (x.append y)) := by
  rw [diagBasis_comp_diagBasis, h, pow_zero, one_smul]

theorem diagBasis_ne_zero [Nontrivial R] (x : PlanarMatching (X.as + Y.as)) :
    diagBasis X Y x ≠ 0 :=
  (diagBasis X Y).ne_zero x

instance (X Y : TLCat R δ) : Module.Free R (X ⟶ Y) :=
  .of_basis (diagBasis X Y)

instance (X Y : TLCat R δ) : Module.Finite R (X ⟶ Y) :=
  .of_basis (diagBasis X Y)

/-- Every morphism `X ⟶ Y` is zero when the total number `X.as + Y.as` of boundary points is not
even, since there is no planar matching of an odd number of points. -/
theorem hom_eq_zero_of_not_even (h : ¬ Even (X.as + Y.as)) (f : X ⟶ Y) : f = 0 := by
  have := PlanarMatching.isEmpty_of_not_even h
  exact hom_ext (Subsingleton.elim _ _)

theorem subsingleton_hom_of_not_even (h : ¬ Even (X.as + Y.as)) : Subsingleton (X ⟶ Y) :=
  ⟨fun f g => (hom_eq_zero_of_not_even h f).trans (hom_eq_zero_of_not_even h g).symm⟩

theorem subsingleton_hom_of_odd (h : Odd (X.as + Y.as)) : Subsingleton (X ⟶ Y) :=
  subsingleton_hom_of_not_even (Nat.not_even_iff_odd.mpr h)

/-- Over a nontrivial base ring, `X ⟶ Y` is nontrivial if and only if `X.as + Y.as` is even. -/
theorem nontrivial_hom_iff [Nontrivial R] : Nontrivial (X ⟶ Y) ↔ Even (X.as + Y.as) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hne
    have := subsingleton_hom_of_not_even (X := X) (Y := Y) hne
    exact false_of_nontrivial_of_subsingleton (X ⟶ Y)
  · obtain ⟨x⟩ := PlanarMatching.nonempty_iff.mpr h
    exact ⟨⟨diagBasis X Y x, 0, diagBasis_ne_zero x⟩⟩

/-- The rank of `X ⟶ Y` over `R` is the number of planar matchings of `X.as + Y.as` points. -/
theorem finrank_hom [StrongRankCondition R] (X Y : TLCat R δ) :
    Module.finrank R (X ⟶ Y) = Nat.card (PlanarMatching (X.as + Y.as)) :=
  Module.finrank_eq_nat_card_basis (diagBasis X Y)

theorem finrank_hom_of_not_even [StrongRankCondition R] {X Y : TLCat R δ}
    (h : ¬ Even (X.as + Y.as)) : Module.finrank R (X ⟶ Y) = 0 := by
  have := PlanarMatching.isEmpty_of_not_even h
  simp [finrank_hom]

theorem finrank_hom_of_odd [StrongRankCondition R] {X Y : TLCat R δ}
    (h : Odd (X.as + Y.as)) : Module.finrank R (X ⟶ Y) = 0 :=
  finrank_hom_of_not_even (Nat.not_even_iff_odd.mpr h)

/-- **Catalan rank of morphism modules.** When `X.as + Y.as = 2 * k`, the module `X ⟶ Y` is free
of rank `catalan k`. -/
theorem finrank_hom_of_add_eq_two_mul [StrongRankCondition R] {X Y : TLCat R δ} {k : ℕ}
    (h : X.as + Y.as = 2 * k) : Module.finrank R (X ⟶ Y) = catalan k := by
  rw [finrank_hom, h, PlanarMatching.card_planarMatching]

@[simp]
theorem finrank_hom_of_same [StrongRankCondition R] (n : ℕ) :
    Module.finrank R ((of n : TLCat R δ) ⟶ of n) = catalan n :=
  finrank_hom_of_add_eq_two_mul (two_mul n).symm

/-- **Catalan rank of endomorphism algebras.** The endomorphism `R`-algebra `End (of n)` is free of
rank `catalan n`. -/
@[simp]
theorem finrank_end_of [StrongRankCondition R] (n : ℕ) :
    Module.finrank R (End (of n : TLCat R δ)) = catalan n :=
  (End.linearEquiv (R := R) (X := (of n : TLCat R δ))).finrank_eq.trans (finrank_hom_of_same n)

/-! ### The linearization functor and universal property -/

variable (R δ) in
/-- **The linearization functor** `TLDiagCat ⥤ TLCat R δ`: sends an object `of n` to `of n` and
a Temperley–Lieb diagram `D` with `c` closed circles to `δ ^ c` times the basis morphism of its
planar matching.

Marked `@[expose, implicit_reducible]` so `((linearize R δ).obj X)` reduces in dependent morphism
types `(linearize R δ).obj X ⟶ (linearize R δ).obj Y` without `eqToHom`. -/
@[expose, implicit_reducible]
noncomputable def linearize : TLDiagCat ⥤ TLCat R δ where
  obj X := of X.as
  map {X Y} f := δ ^ f.diagram.circles • diagBasis (of X.as) (of Y.as) f.diagram.matching
  map_id X := by
    simp [id_eq_diagBasis]
  map_comp {X Y Z} f g := by
    rw [TLDiagCat.diagram_comp, TLDiagram.circles_comp, TLDiagram.matching_comp,
      Linear.smul_comp, Linear.comp_smul,
      diagBasis_comp_diagBasis (X := of X.as) (Y := of Y.as) (Z := of Z.as),
      smul_smul, smul_smul, pow_add, pow_add]

@[simp]
theorem linearize_obj_as (X : TLDiagCat) : ((linearize R δ).obj X).as = X.as := (rfl)

@[simp]
theorem linearize_obj_of (n : ℕ) : (linearize R δ).obj (.of n) = of n := (rfl)

theorem linearize_map {X Y : TLDiagCat} (f : X ⟶ Y) :
    (linearize R δ).map f =
      δ ^ f.diagram.circles • diagBasis (of X.as) (of Y.as) f.diagram.matching := (rfl)

@[simp]
theorem linearize_map_mk {n m : ℕ} (x : PlanarMatching (n + m)) (c : ℕ) :
    (linearize R δ).map (TLDiagCat.Hom.mk ⟨x, c⟩ : .of n ⟶ .of m) =
      δ ^ c • diagBasis (of n) (of m) x := (rfl)

instance : (linearize R δ).EssSurj where
  mem_essImage Y := ⟨.of Y.as, ⟨Iso.refl Y⟩⟩

/-- The image of `TLDiagCat` morphisms under `linearize R δ` spans every morphism module of
`TLCat R δ` over `R`. -/
theorem span_range_linearize_map (X Y : TLDiagCat) :
    Submodule.span R (Set.range ((linearize R δ).map : (X ⟶ Y) → _)) = ⊤ := by
  rw [eq_top_iff, ← (diagBasis ((linearize R δ).obj X) ((linearize R δ).obj Y)).span_eq,
    Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  refine Submodule.subset_span ⟨TLDiagCat.Hom.mk ⟨x, 0⟩, ?_⟩
  simp only [linearize_map, pow_zero, one_smul]
  rfl

section UniversalProperty

variable {D : Type*} [Category.{v} D] [Preadditive D] [CategoryTheory.Linear R D]

section LiftDiag

variable (F : TLDiagCat ⥤ D)
  (hF : ∀ {n m : ℕ} (x : PlanarMatching (n + m)) (c : ℕ),
    F.map (TLDiagCat.Hom.mk ⟨x, c + 1⟩ : .of n ⟶ .of m) =
      δ • F.map (TLDiagCat.Hom.mk ⟨x, c⟩ : .of n ⟶ .of m))

include hF in
private theorem liftDiag_map_mk_circles {n m : ℕ} (x : PlanarMatching (n + m)) (c : ℕ) :
    F.map (TLDiagCat.Hom.mk ⟨x, c⟩ : .of n ⟶ .of m) =
      δ ^ c • F.map (TLDiagCat.Hom.mk ⟨x, 0⟩ : .of n ⟶ .of m) := by
  induction c with
  | zero => simp
  | succ c ih => rw [hF x c, ih, smul_smul, ← pow_succ']

/-- **Diagram-linearization universal property of `TLCat R δ`.** Any functor `F : TLDiagCat ⥤ D`
into an `R`-linear category `D` that evaluates each closed circle to a factor of `δ` extends to an
additive `R`-linear functor `TLCat R δ ⥤ D`.

Marked `@[expose, implicit_reducible]` so `((liftDiag F hF).obj X)` reduces to
`F.obj (TLDiagCat.of X.as)` in dependent morphism types without `eqToHom`. -/
@[expose, implicit_reducible]
noncomputable def liftDiag : TLCat R δ ⥤ D where
  obj X := F.obj (TLDiagCat.of X.as)
  map {X Y} := (diagBasis X Y).constr R fun x =>
    F.map (TLDiagCat.Hom.mk ⟨x, 0⟩ : TLDiagCat.of X.as ⟶ TLDiagCat.of Y.as)
  map_id X := by
    rw [id_eq_diagBasis, Module.Basis.constr_basis]
    have hid :
        (TLDiagCat.Hom.mk ⟨PlanarMatching.nested X.as, 0⟩ :
          TLDiagCat.of X.as ⟶ TLDiagCat.of X.as) = 𝟙 (TLDiagCat.of X.as) :=
      TLDiagCat.hom_ext (TLDiagram.ext (by simp) (by simp))
    rw [hid, CategoryTheory.Functor.map_id]
  map_comp {X Y Z} f g := by
    let φ (A B : TLCat R δ) :
        (A ⟶ B) →ₗ[R] (F.obj (TLDiagCat.of A.as) ⟶ F.obj (TLDiagCat.of B.as)) :=
      (diagBasis A B).constr R fun x =>
        F.map (TLDiagCat.Hom.mk ⟨x, 0⟩ : TLDiagCat.of A.as ⟶ TLDiagCat.of B.as)
    exact LinearMap.congr_fun₂
      (f := (Linear.comp (S := R) X Y Z).compr₂ (φ X Z))
      (g := (Linear.comp (S := R) (F.obj (TLDiagCat.of X.as)) (F.obj (TLDiagCat.of Y.as))
        (F.obj (TLDiagCat.of Z.as))).compl₁₂ (φ X Y) (φ Y Z))
      ((diagBasis X Y).ext fun x => (diagBasis Y Z).ext fun y => by
        simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, Linear.comp_apply,
          Linear.leftComp_apply, diagBasis_comp_diagBasis, map_smul, φ,
          Module.Basis.constr_basis, ← F.map_comp]
        have hcomp :
            ((TLDiagCat.Hom.mk ⟨x, 0⟩ : TLDiagCat.of X.as ⟶ TLDiagCat.of Y.as) ≫
              (TLDiagCat.Hom.mk ⟨y, 0⟩ : TLDiagCat.of Y.as ⟶ TLDiagCat.of Z.as)) =
            TLDiagCat.Hom.mk ⟨PlanarMatching.glueMiddle Y.as (x.append y),
              PlanarMatching.glueMiddleCircles Y.as (x.append y)⟩ :=
          TLDiagCat.hom_ext (TLDiagram.ext (by simp) (by simp))
        rw [hcomp]
        exact (liftDiag_map_mk_circles F hF _ _).symm) f g

@[simp]
theorem liftDiag_obj (X : TLCat R δ) :
    (liftDiag F hF).obj X = F.obj (TLDiagCat.of X.as) := (rfl)

@[simp]
theorem liftDiag_map_diagBasis {X Y : TLCat R δ} (x : PlanarMatching (X.as + Y.as)) :
    (liftDiag F hF).map (diagBasis X Y x) =
      F.map (TLDiagCat.Hom.mk ⟨x, 0⟩ : TLDiagCat.of X.as ⟶ TLDiagCat.of Y.as) :=
  (diagBasis X Y).constr_basis R _ x

instance : (liftDiag F hF).Additive where
  map_add {_ _} f g := map_add ((diagBasis _ _).constr R _) f g

instance : (liftDiag F hF).Linear R where
  map_smul {_ _} f r := ((diagBasis _ _).constr R _).map_smul r f

@[simp]
theorem liftDiag_map_linearize_map {X Y : TLDiagCat} (f : X ⟶ Y) :
    (liftDiag F hF).map ((linearize R δ).map f) = F.map f := by
  rw [linearize_map, Functor.map_smul,
    liftDiag_map_diagBasis F hF (X := of X.as) (Y := of Y.as) f.diagram.matching,
    ← liftDiag_map_mk_circles F hF f.diagram.matching f.diagram.circles]
  rfl

/-- `linearize R δ` followed by `liftDiag F hF` is naturally isomorphic to `F`. -/
noncomputable def linearizeLiftDiagIso : linearize R δ ⋙ liftDiag F hF ≅ F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by simp)

@[simp]
theorem linearizeLiftDiagIso_hom_app (X : TLDiagCat) :
    (linearizeLiftDiagIso F hF).hom.app X = 𝟙 (F.obj X) := (rfl)

@[simp]
theorem linearizeLiftDiagIso_inv_app (X : TLDiagCat) :
    (linearizeLiftDiagIso F hF).inv.app X = 𝟙 (F.obj X) := (rfl)

end LiftDiag

/-- **Uniqueness half of the diagram-linearization universal property.** Any natural isomorphism
between the restrictions of two additive `R`-linear functors `TLCat R δ ⥤ D` along `linearize R δ`
lifts to a natural isomorphism between the functors themselves. -/
noncomputable def functorIsoOfLinearizeIso {G₁ G₂ : TLCat R δ ⥤ D}
    [G₁.Additive] [G₁.Linear R] [G₂.Additive] [G₂.Linear R]
    (α : linearize R δ ⋙ G₁ ≅ linearize R δ ⋙ G₂) : G₁ ≅ G₂ :=
  NatIso.ofComponents (fun X => α.app (TLDiagCat.of X.as)) fun {X Y} f =>
    LinearMap.congr_fun
      (f := (Linear.rightComp R _ (α.hom.app (TLDiagCat.of Y.as))).comp (G₁.mapLinearMap R))
      (g := (Linear.leftComp R _ (α.hom.app (TLDiagCat.of X.as))).comp (G₂.mapLinearMap R))
      ((diagBasis X Y).ext fun x => by
        have hnat := α.hom.naturality
          (TLDiagCat.Hom.mk ⟨x, 0⟩ : TLDiagCat.of X.as ⟶ TLDiagCat.of Y.as)
        dsimp only [Functor.comp_obj, Functor.comp_map, linearize] at hnat
        simpa [of_as] using hnat) f

@[simp]
theorem functorIsoOfLinearizeIso_hom_app {G₁ G₂ : TLCat R δ ⥤ D}
    [G₁.Additive] [G₁.Linear R] [G₂.Additive] [G₂.Linear R]
    (α : linearize R δ ⋙ G₁ ≅ linearize R δ ⋙ G₂) (X : TLCat R δ) :
    (functorIsoOfLinearizeIso α).hom.app X = α.hom.app (TLDiagCat.of X.as) := (rfl)

@[simp]
theorem functorIsoOfLinearizeIso_inv_app {G₁ G₂ : TLCat R δ ⥤ D}
    [G₁.Additive] [G₁.Linear R] [G₂.Additive] [G₂.Linear R]
    (α : linearize R δ ⋙ G₁ ≅ linearize R δ ⋙ G₂) (X : TLCat R δ) :
    (functorIsoOfLinearizeIso α).inv.app X = α.inv.app (TLDiagCat.of X.as) := (rfl)

end UniversalProperty

/-! ### Cup, cap, the circle relation, and `End (of 0)` -/

/-- The **cup** `of 0 ⟶ of 2` in `TLCat R δ`, basis morphism of `TLDiagram.cup.matching`. -/
noncomputable def cup : (of 0 : TLCat R δ) ⟶ of 2 :=
  diagBasis (of 0) (of 2) TLDiagram.cup.matching

/-- The **cap** `of 2 ⟶ of 0` in `TLCat R δ`, basis morphism of `TLDiagram.cap.matching`. -/
noncomputable def cap : (of 2 : TLCat R δ) ⟶ of 0 :=
  diagBasis (of 2) (of 0) TLDiagram.cap.matching

theorem cup_eq_diagBasis :
    (cup : (of 0 : TLCat R δ) ⟶ of 2) = diagBasis (of 0) (of 2) TLDiagram.cup.matching := (rfl)

theorem cap_eq_diagBasis :
    (cap : (of 2 : TLCat R δ) ⟶ of 0) = diagBasis (of 2) (of 0) TLDiagram.cap.matching := (rfl)

@[simp]
theorem linearize_map_cup :
    (linearize R δ).map TLDiagCat.cup = (cup : (of 0 : TLCat R δ) ⟶ of 2) := by
  simp [linearize_map, cup]

@[simp]
theorem linearize_map_cap :
    (linearize R δ).map TLDiagCat.cap = (cap : (of 2 : TLCat R δ) ⟶ of 0) := by
  simp [linearize_map, cap]

/-- The closed circle in `TLDiagCat` evaluates to `δ • 𝟙 (of 0)` in `TLCat R δ`. -/
@[simp]
theorem linearize_map_circle :
    (linearize R δ).map TLDiagCat.circle = δ • 𝟙 (of 0 : TLCat R δ) := by
  simp [linearize_map, id_eq_diagBasis]

/-- **The loop relation**: a cup followed by a cap is `δ` times the identity on `of 0`. -/
@[simp, reassoc]
theorem cup_comp_cap :
    (cup : (of 0 : TLCat R δ) ⟶ of 2) ≫ cap = δ • 𝟙 (of 0 : TLCat R δ) := by
  rw [← linearize_map_cup, ← linearize_map_cap, ← Functor.map_comp,
    TLDiagCat.cup_comp_cap, linearize_map_circle]

theorem cap_comp_cup_eq_diagBasis :
    (cap : (of 2 : TLCat R δ) ⟶ of 0) ≫ cup =
      diagBasis (of 2) (of 2) (TLDiagram.cap.comp TLDiagram.cup).matching := by
  rw [cap_eq_diagBasis, cup_eq_diagBasis,
    diagBasis_comp_diagBasis (X := of 2) (Y := of 0) (Z := of 2)]
  simp [TLDiagram.matching_comp]

@[reassoc]
theorem cap_comp_cup_comp_cap :
    (cap : (of 2 : TLCat R δ) ⟶ of 0) ≫ cup ≫ cap = δ • (cap : (of 2 : TLCat R δ) ⟶ of 0) := by
  rw [cup_comp_cap, Linear.comp_smul, Category.comp_id]

@[simp, reassoc]
theorem cup_comp_cap_comp_cup :
    (cup : (of 0 : TLCat R δ) ⟶ of 2) ≫ cap ≫ cup = δ • (cup : (of 0 : TLCat R δ) ⟶ of 2) := by
  rw [← Category.assoc, cup_comp_cap, Linear.smul_comp, Category.id_comp]

/-- The Temperley–Lieb generator `e₁ = cap ≫ cup` satisfies `e₁ ≫ e₁ = δ • e₁`. -/
theorem cap_comp_cup_comp_cap_comp_cup :
    ((cap : (of 2 : TLCat R δ) ⟶ of 0) ≫ cup) ≫ (cap ≫ cup) =
      δ • ((cap : (of 2 : TLCat R δ) ⟶ of 0) ≫ cup) := by
  rw [Category.assoc, ← Category.assoc cup cap cup, cup_comp_cap, Linear.smul_comp,
    Category.id_comp, Linear.comp_smul]

/-- Over a nontrivial ring, `cap ≫ cup` is linearly independent of `𝟙 (of 2)`: in particular it is
never a scalar multiple of `𝟙 (of 2)` for any `r : R`. -/
theorem cap_comp_cup_ne_smul_id [Nontrivial R] (r : R) :
    (cap : (of 2 : TLCat R δ) ⟶ of 0) ≫ cup ≠ r • 𝟙 (of 2 : TLCat R δ) := by
  intro h
  have hne : (TLDiagram.cap.comp TLDiagram.cup).matching ≠ PlanarMatching.nested 2 := by
    intro hm
    have h0 := congrFun (congrArg (fun x : PlanarMatching 4 => ⇑x.1.val) hm) 0
    simp only [TLDiagram.cap_comp_cup_matching_val, PlanarMatching.nested_val] at h0
    exact absurd h0 (by decide)
  have hc := DFunLike.congr_fun (congrArg Hom.coeff h)
    (TLDiagram.cap.comp TLDiagram.cup).matching
  rw [cap_comp_cup_eq_diagBasis, coeff_diagBasis, coeff_smul, coeff_id, Finsupp.coe_smul,
    Pi.smul_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne, smul_zero] at hc
  exact one_ne_zero hc

/-- Every endomorphism of the empty boundary `of 0` is a scalar multiple of `𝟙 (of 0)`. -/
theorem end_zero_eq_smul_id (f : (of 0 : TLCat R δ) ⟶ of 0) :
    f = f.coeff (PlanarMatching.nested 0) • 𝟙 (of 0 : TLCat R δ) := by
  refine hom_ext (Finsupp.ext fun x => ?_)
  obtain rfl : x = PlanarMatching.nested 0 := Subsingleton.elim (α := PlanarMatching 0) _ _
  simp

/-- **Endomorphisms of the empty boundary form the ground ring `R`.** -/
noncomputable def endZeroAlgEquiv : End (of 0 : TLCat R δ) ≃ₐ[R] R :=
  AlgEquiv.symm
    { Algebra.ofId R (End (of 0 : TLCat R δ)) with
      invFun := fun f => f.asHom.coeff (PlanarMatching.nested 0)
      left_inv := fun r => by
        simp [End.algebraMap_asHom]
      right_inv := fun f => End.ext <| by
        simpa [End.algebraMap_asHom] using (end_zero_eq_smul_id f.asHom).symm }

@[simp]
theorem endZeroAlgEquiv_apply (f : End (of 0 : TLCat R δ)) :
    endZeroAlgEquiv f = f.asHom.coeff (PlanarMatching.nested 0) := (rfl)

@[simp]
theorem endZeroAlgEquiv_symm_apply (r : R) :
    endZeroAlgEquiv.symm r = algebraMap R (End (of 0 : TLCat R δ)) r := (rfl)

theorem endZeroAlgEquiv_of_linearize_map (f : (TLDiagCat.of 0 : TLDiagCat) ⟶ .of 0) :
    endZeroAlgEquiv (End.of ((linearize R δ).map f)) = δ ^ f.diagram.circles := by
  have hm : f.diagram.matching = PlanarMatching.nested 0 :=
    Subsingleton.elim (α := PlanarMatching 0) _ _
  simp [linearize_map, hm, coeff_diagBasis (X := of 0) (Y := of 0)]

/-! ### Monomorphisms, epimorphisms, and non-generic `δ` -/

/-- Every planar-matching basis morphism out of the empty boundary `of 0` is a monomorphism, for
every commutative ring `R` and every loop value `δ : R`: gluing along `0` points closes no circle
and appends `y` injectively to each matching on `X.as + 0`. -/
theorem mono_diagBasis_zero_left {Y : TLCat R δ} (y : PlanarMatching (0 + Y.as)) :
    Mono (diagBasis (of 0) Y y) := by
  refine ⟨fun {X} f₁ f₂ h => ?_⟩
  let ι : PlanarMatching (X.as + 0) → PlanarMatching (X.as + Y.as) :=
    fun x => PlanarMatching.glueMiddle 0 (x.append y)
  have hι : Function.Injective ι := by
    intro x₁ x₂ hx
    simp only [ι, PlanarMatching.glueMiddle_zero, EmbeddingLike.apply_eq_iff_eq] at hx
    refine PlanarMatching.ext fun i => Fin.castAdd_injective (X.as + 0) (0 + Y.as) ?_
    have hi := congrFun (congrArg (fun z : PlanarMatching _ => ⇑z.1.val) hx)
      (Fin.castAdd (0 + Y.as) i)
    simpa only [PlanarMatching.append_val_castAdd] using hi
  have hmap (f : X ⟶ of 0) :
      (f ≫ diagBasis (of 0) Y y).coeff = Finsupp.mapDomain ι f.coeff :=
    LinearMap.congr_fun
      (f := (coeffLinearEquiv X Y).toLinearMap.comp
        (Linear.rightComp R X (diagBasis (of 0) Y y)))
      (g := (Finsupp.lmapDomain R R ι).comp (coeffLinearEquiv X (of 0)).toLinearMap)
      ((diagBasis X (of 0)).ext fun x => by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Linear.rightComp_apply,
          Finsupp.lmapDomain_apply]
        rw [diagBasis_comp_diagBasis (X := X) (Y := of 0) (Z := Y), coeffLinearEquiv_apply,
          coeffLinearEquiv_apply, coeff_smul, coeff_diagBasis, coeff_diagBasis]
        simp [ι]) f
  have hc := congrArg Hom.coeff h
  rw [hmap, hmap] at hc
  exact hom_ext (Finsupp.mapDomain_injective hι hc)

/-- Every planar-matching basis morphism into the empty boundary `of 0` is an epimorphism, for
every commutative ring `R` and every loop value `δ : R`. -/
theorem epi_diagBasis_zero_right {X : TLCat R δ} (x : PlanarMatching (X.as + 0)) :
    Epi (diagBasis X (of 0) x) := by
  refine ⟨fun {Z} g₁ g₂ h => ?_⟩
  let ι : PlanarMatching (0 + Z.as) → PlanarMatching (X.as + Z.as) :=
    fun z => PlanarMatching.glueMiddle 0 (x.append z)
  have hι : Function.Injective ι := by
    intro z₁ z₂ hz
    simp only [ι, PlanarMatching.glueMiddle_zero, EmbeddingLike.apply_eq_iff_eq] at hz
    refine PlanarMatching.ext fun j => Fin.natAdd_injective (0 + Z.as) (X.as + 0) ?_
    have hj := congrFun (congrArg (fun w : PlanarMatching _ => ⇑w.1.val) hz)
      (Fin.natAdd (X.as + 0) j)
    simpa only [PlanarMatching.append_val_natAdd] using hj
  have hmap (g : of 0 ⟶ Z) :
      (diagBasis X (of 0) x ≫ g).coeff = Finsupp.mapDomain ι g.coeff :=
    LinearMap.congr_fun
      (f := (coeffLinearEquiv X Z).toLinearMap.comp
        (Linear.leftComp R Z (diagBasis X (of 0) x)))
      (g := (Finsupp.lmapDomain R R ι).comp (coeffLinearEquiv (of 0) Z).toLinearMap)
      ((diagBasis (of 0) Z).ext fun z => by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Linear.leftComp_apply,
          Finsupp.lmapDomain_apply]
        rw [diagBasis_comp_diagBasis (X := X) (Y := of 0) (Z := Z), coeffLinearEquiv_apply,
          coeffLinearEquiv_apply, coeff_smul, coeff_diagBasis, coeff_diagBasis]
        simp [ι]) g
  have hc := congrArg Hom.coeff h
  rw [hmap, hmap] at hc
  exact hom_ext (Finsupp.mapDomain_injective hι hc)

/-- `cup` is unconditionally a monomorphism for every `R` and `δ`. -/
instance : Mono (cup : (of 0 : TLCat R δ) ⟶ of 2) :=
  mono_diagBasis_zero_left _

/-- `cap` is unconditionally an epimorphism for every `R` and `δ`. -/
instance : Epi (cap : (of 2 : TLCat R δ) ⟶ of 0) :=
  epi_diagBasis_zero_right _

/-- Over a nontrivial ring, `cap` is never a monomorphism (for any `δ : R`), since the nonzero
endomorphism `cap ≫ cup - δ • 𝟙 (of 2)` satisfies `(cap ≫ cup - δ • 𝟙 (of 2)) ≫ cap = 0`. -/
theorem not_mono_cap [Nontrivial R] : ¬ Mono (cap : (of 2 : TLCat R δ) ⟶ of 0) := by
  intro hmono
  have hkill :
      (cap ≫ cup - δ • 𝟙 (of 2 : TLCat R δ)) ≫ (cap : (of 2 : TLCat R δ) ⟶ of 0) = 0 ≫ cap := by
    simp [Preadditive.sub_comp]
  exact cap_comp_cup_ne_smul_id δ (sub_eq_zero.mp ((cancel_mono cap).mp hkill))

/-- Over a nontrivial ring, `cup` is never an epimorphism (for any `δ : R`), since
`cup ≫ (cap ≫ cup - δ • 𝟙 (of 2)) = 0`. -/
theorem not_epi_cup [Nontrivial R] : ¬ Epi (cup : (of 0 : TLCat R δ) ⟶ of 2) := by
  intro hepi
  have hkill :
      (cup : (of 0 : TLCat R δ) ⟶ of 2) ≫ (cap ≫ cup - δ • 𝟙 (of 2 : TLCat R δ)) = cup ≫ 0 := by
    simp [Preadditive.comp_sub]
  exact cap_comp_cup_ne_smul_id δ (sub_eq_zero.mp ((cancel_epi cup).mp hkill))

/-- A scalar endomorphism `r • 𝟙 (of 0)` of the empty boundary is a monomorphism if and only if
`r` is a non-zero-divisor in `R`. -/
theorem mono_smul_id_zero_iff (r : R) :
    Mono (r • 𝟙 (of 0 : TLCat R δ)) ↔ r ∈ nonZeroDivisors R := by
  rw [mem_nonZeroDivisors_iff_right]
  refine ⟨fun hmono s hsr => ?_, fun hr => ⟨fun {X} f₁ f₂ h => ?_⟩⟩
  · have hcomp :
        (s • 𝟙 (of 0 : TLCat R δ)) ≫ (r • 𝟙 (of 0 : TLCat R δ)) =
          0 ≫ (r • 𝟙 (of 0 : TLCat R δ)) := by
      simp [smul_smul, mul_comm r s, hsr]
    have hs := (cancel_mono (r • 𝟙 (of 0 : TLCat R δ))).mp hcomp
    simpa using DFunLike.congr_fun (congrArg Hom.coeff hs) (PlanarMatching.nested 0)
  · refine hom_ext (Finsupp.ext fun x => sub_eq_zero.mp (hr _ ?_))
    have hx := DFunLike.congr_fun (congrArg Hom.coeff h) x
    simp only [Linear.comp_smul, Category.comp_id, coeff_smul, Finsupp.coe_smul, Pi.smul_apply,
      smul_eq_mul] at hx
    calc (f₁.coeff x - f₂.coeff x) * r = r * f₁.coeff x - r * f₂.coeff x := by
          rw [sub_mul, mul_comm, mul_comm _ r]
      _ = 0 := sub_eq_zero.mpr hx

/-- A scalar endomorphism `r • 𝟙 (of 0)` of the empty boundary is an epimorphism if and only if
`r` is a non-zero-divisor in `R`. -/
theorem epi_smul_id_zero_iff (r : R) :
    Epi (r • 𝟙 (of 0 : TLCat R δ)) ↔ r ∈ nonZeroDivisors R := by
  rw [mem_nonZeroDivisors_iff_right]
  refine ⟨fun hepi s hsr => ?_, fun hr => ⟨fun {Z} g₁ g₂ h => ?_⟩⟩
  · have hcomp :
        (r • 𝟙 (of 0 : TLCat R δ)) ≫ (s • 𝟙 (of 0 : TLCat R δ)) =
          (r • 𝟙 (of 0 : TLCat R δ)) ≫ 0 := by
      simp [smul_smul, hsr]
    have hs := (cancel_epi (r • 𝟙 (of 0 : TLCat R δ))).mp hcomp
    simpa using DFunLike.congr_fun (congrArg Hom.coeff hs) (PlanarMatching.nested 0)
  · refine hom_ext (Finsupp.ext fun z => sub_eq_zero.mp (hr _ ?_))
    have hz := DFunLike.congr_fun (congrArg Hom.coeff h) z
    simp only [Linear.smul_comp, Category.id_comp, coeff_smul, Finsupp.coe_smul, Pi.smul_apply,
      smul_eq_mul] at hz
    calc (g₁.coeff z - g₂.coeff z) * r = r * g₁.coeff z - r * g₂.coeff z := by
          rw [sub_mul, mul_comm, mul_comm _ r]
      _ = 0 := sub_eq_zero.mpr hz

/-- A scalar endomorphism `r • 𝟙 (of 0)` of the empty boundary is an isomorphism if and only if
`r` is a unit in `R`. -/
theorem isIso_smul_id_zero_iff (r : R) :
    IsIso (r • 𝟙 (of 0 : TLCat R δ)) ↔ IsUnit r := by
  rw [← CategoryTheory.isUnit_iff_isIso (End.of (r • 𝟙 (of 0 : TLCat R δ)))]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using h.map (endZeroAlgEquiv (R := R) (δ := δ)).toMonoidHom
  · have hu := h.map (endZeroAlgEquiv (R := R) (δ := δ)).symm.toMonoidHom
    simpa [Algebra.algebraMap_eq_smul_one] using hu

/-- The image of `TLDiagCat.circle` in `TLCat R δ` is a monomorphism if and only if
`δ ∈ nonZeroDivisors R`. -/
theorem mono_linearize_circle_iff :
    Mono ((linearize R δ).map TLDiagCat.circle) ↔ δ ∈ nonZeroDivisors R := by
  rw [linearize_map_circle, mono_smul_id_zero_iff]

/-- The image of `TLDiagCat.circle` in `TLCat R δ` is an epimorphism if and only if
`δ ∈ nonZeroDivisors R`. -/
theorem epi_linearize_circle_iff :
    Epi ((linearize R δ).map TLDiagCat.circle) ↔ δ ∈ nonZeroDivisors R := by
  rw [linearize_map_circle, epi_smul_id_zero_iff]

/-- The image of `TLDiagCat.circle` in `TLCat R δ` is an isomorphism if and only if `IsUnit δ`. -/
theorem isIso_linearize_circle_iff :
    IsIso ((linearize R δ).map TLDiagCat.circle) ↔ IsUnit δ := by
  rw [linearize_map_circle, isIso_smul_id_zero_iff]

/-! ### Corner-dragging, rotation, and reflection linear equivalences -/

/-- **Dragging the bottom-right corner up**, lifted linearly to morphism modules of `TLCat R δ`. -/
noncomputable def dragRight (n m : ℕ) :
    ((of (n + 1) : TLCat R δ) ⟶ of m) ≃ₗ[R] ((of n : TLCat R δ) ⟶ of (m + 1)) :=
  (diagBasis (of (n + 1)) (of m)).equiv (diagBasis (of n) (of (m + 1)))
    (PlanarMatching.cast (Nat.add_right_comm n 1 m))

@[simp]
theorem dragRight_diagBasis (n m : ℕ) (x : PlanarMatching (n + 1 + m)) :
    dragRight (R := R) (δ := δ) n m (diagBasis (of (n + 1)) (of m) x) =
      diagBasis (of n) (of (m + 1)) (PlanarMatching.cast (Nat.add_right_comm n 1 m) x) := by
  simp [dragRight]

@[simp]
theorem dragRight_symm_diagBasis (n m : ℕ) (x : PlanarMatching (n + (m + 1))) :
    (dragRight (R := R) (δ := δ) n m).symm (diagBasis (of n) (of (m + 1)) x) =
      diagBasis (of (n + 1)) (of m) (PlanarMatching.cast (Nat.add_right_comm n 1 m).symm x) := by
  simp [dragRight]

@[simp]
theorem dragRight_linearize_map (n m : ℕ) (f : TLDiagCat.of (n + 1) ⟶ .of m) :
    dragRight (R := R) (δ := δ) n m ((linearize R δ).map f) =
      (linearize R δ).map (TLDiagCat.Hom.mk (TLDiagram.dragRight n m f.diagram)) := by
  rw [linearize_map, map_smul, dragRight_diagBasis]
  simp [linearize_map]

/-- **Dragging the bottom-left corner up**, lifted linearly to morphism modules of `TLCat R δ`. -/
noncomputable def dragLeft (n m : ℕ) :
    ((of (n + 1) : TLCat R δ) ⟶ of m) ≃ₗ[R] ((of n : TLCat R δ) ⟶ of (m + 1)) :=
  (diagBasis (of (n + 1)) (of m)).equiv (diagBasis (of n) (of (m + 1)))
    ((PlanarMatching.rotate (n + 1 + m)).symm.trans
      (PlanarMatching.cast (Nat.add_right_comm n 1 m)))

@[simp]
theorem dragLeft_diagBasis (n m : ℕ) (x : PlanarMatching (n + 1 + m)) :
    dragLeft (R := R) (δ := δ) n m (diagBasis (of (n + 1)) (of m) x) =
      diagBasis (of n) (of (m + 1))
        (PlanarMatching.cast (Nat.add_right_comm n 1 m)
          ((PlanarMatching.rotate (n + 1 + m)).symm x)) := by
  simp [dragLeft]

@[simp]
theorem dragLeft_symm_diagBasis (n m : ℕ) (x : PlanarMatching (n + (m + 1))) :
    (dragLeft (R := R) (δ := δ) n m).symm (diagBasis (of n) (of (m + 1)) x) =
      diagBasis (of (n + 1)) (of m)
        (PlanarMatching.rotate (n + 1 + m)
          (PlanarMatching.cast (Nat.add_right_comm n 1 m).symm x)) := by
  simp [dragLeft]

@[simp]
theorem dragLeft_linearize_map (n m : ℕ) (f : TLDiagCat.of (n + 1) ⟶ .of m) :
    dragLeft (R := R) (δ := δ) n m ((linearize R δ).map f) =
      (linearize R δ).map (TLDiagCat.Hom.mk (TLDiagram.dragLeft n m f.diagram)) := by
  rw [linearize_map, map_smul, dragLeft_diagBasis]
  simp [linearize_map]

/-- **Counterclockwise rotation** of boundary points, lifted linearly to a module automorphism of
`(of n : TLCat R δ) ⟶ of m`. -/
noncomputable def rotateHom (n m : ℕ) :
    ((of n : TLCat R δ) ⟶ of m) ≃ₗ[R] ((of n : TLCat R δ) ⟶ of m) :=
  (diagBasis (of n) (of m)).equiv (diagBasis (of n) (of m)) (PlanarMatching.rotate (n + m))

@[simp]
theorem rotateHom_diagBasis (n m : ℕ) (x : PlanarMatching (n + m)) :
    rotateHom (R := R) (δ := δ) n m (diagBasis (of n) (of m) x) =
      diagBasis (of n) (of m) (PlanarMatching.rotate (n + m) x) := by
  simp [rotateHom]

@[simp]
theorem rotateHom_symm_diagBasis (n m : ℕ) (x : PlanarMatching (n + m)) :
    (rotateHom (R := R) (δ := δ) n m).symm (diagBasis (of n) (of m) x) =
      diagBasis (of n) (of m) ((PlanarMatching.rotate (n + m)).symm x) := by
  simp [rotateHom]

@[simp]
theorem rotateHom_linearize_map (n m : ℕ) (f : TLDiagCat.of n ⟶ .of m) :
    rotateHom (R := R) (δ := δ) n m ((linearize R δ).map f) =
      (linearize R δ).map (TLDiagCat.Hom.mk (TLDiagram.rotate n m f.diagram)) := by
  rw [linearize_map, map_smul, rotateHom_diagBasis]
  simp [linearize_map]

/-- Rotating once counterclockwise and then dragging the bottom-left corner up equals dragging the
bottom-right corner up, as linear equivalences on morphism modules. -/
theorem rotateHom_trans_dragLeft (n m : ℕ) :
    (rotateHom (R := R) (δ := δ) (n + 1) m).trans (dragLeft n m) = dragRight n m := by
  rw [rotateHom, dragLeft, dragRight, Module.Basis.equiv_trans]
  congr 1
  ext x
  simp

@[simp]
theorem dragLeft_rotateHom (n m : ℕ) (f : (of (n + 1) : TLCat R δ) ⟶ of m) :
    dragLeft n m (rotateHom (n + 1) m f) = dragRight n m f :=
  LinearEquiv.congr_fun (rotateHom_trans_dragLeft n m) f

private theorem rotateHom_iterate_eq_equiv (n m k : ℕ) (f : (of n : TLCat R δ) ⟶ of m) :
    (rotateHom n m)^[k] f =
      (diagBasis (of n) (of m)).equiv (diagBasis (of n) (of m))
        (PlanarMatching.rotate (n + m) ^ k) f := by
  induction k with
  | zero =>
    rw [pow_zero, Equiv.Perm.one_def, Module.Basis.equiv_refl]
    rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have heq :
        ((diagBasis (of n : TLCat R δ) (of m)).equiv (diagBasis (of n : TLCat R δ) (of m))
          (PlanarMatching.rotate (n + m) ^ k)).trans (rotateHom n m) =
        (diagBasis (of n : TLCat R δ) (of m)).equiv (diagBasis (of n : TLCat R δ) (of m))
          (PlanarMatching.rotate (n + m) ^ (k + 1)) := by
      rw [rotateHom, Module.Basis.equiv_trans]
      congr 1
      refine Equiv.ext fun x => ?_
      simp [pow_succ', Equiv.Perm.mul_apply]
    exact LinearEquiv.congr_fun heq f

/-- Rotating `n + m` times around the boundary of `of n ⟶ of m` is the identity. -/
@[simp]
theorem rotateHom_iterate_self (n m : ℕ) (f : (of n : TLCat R δ) ⟶ of m) :
    (rotateHom n m)^[n + m] f = f := by
  rw [rotateHom_iterate_eq_equiv, PlanarMatching.rotate_pow_self, Equiv.Perm.one_def,
    Module.Basis.equiv_refl]
  rfl

theorem dragRight_id_one :
    dragRight 0 1 (𝟙 (of 1 : TLCat R δ)) = (cup : (of 0 : TLCat R δ) ⟶ of 2) := by
  rw [id_eq_diagBasis, dragRight_diagBasis, cup_eq_diagBasis]
  exact congrArg (diagBasis (of 0 : TLCat R δ) (of 2))
    (by simpa using congrArg TLDiagram.matching TLDiagram.dragRight_id_one)

theorem dragLeft_id_one :
    dragLeft 0 1 (𝟙 (of 1 : TLCat R δ)) = (cup : (of 0 : TLCat R δ) ⟶ of 2) := by
  rw [id_eq_diagBasis, dragLeft_diagBasis, cup_eq_diagBasis]
  exact congrArg (diagBasis (of 0 : TLCat R δ) (of 2))
    (by simpa using congrArg TLDiagram.matching TLDiagram.dragLeft_id_one)

theorem dragRight_symm_id_one :
    (dragRight 1 0).symm (𝟙 (of 1 : TLCat R δ)) = (cap : (of 2 : TLCat R δ) ⟶ of 0) := by
  rw [id_eq_diagBasis, dragRight_symm_diagBasis, cap_eq_diagBasis]
  exact congrArg (diagBasis (of 2 : TLCat R δ) (of 0))
    (by simpa using congrArg TLDiagram.matching TLDiagram.dragRight_symm_id_one)

/-- **Vertical reflection** (turning a diagram upside down), lifted linearly to morphism modules
`((of n : TLCat R δ) ⟶ of m) ≃ₗ[R] (of m ⟶ of n)`. -/
noncomputable def verticalReflectHom (n m : ℕ) :
    ((of n : TLCat R δ) ⟶ of m) ≃ₗ[R] ((of m : TLCat R δ) ⟶ of n) :=
  (diagBasis (of n) (of m)).equiv (diagBasis (of m) (of n))
    ((PlanarMatching.reflect (n + m)).trans (PlanarMatching.cast (Nat.add_comm n m)))

@[simp]
theorem verticalReflectHom_diagBasis (n m : ℕ) (x : PlanarMatching (n + m)) :
    verticalReflectHom (R := R) (δ := δ) n m (diagBasis (of n) (of m) x) =
      diagBasis (of m) (of n)
        (PlanarMatching.cast (Nat.add_comm n m) (PlanarMatching.reflect (n + m) x)) := by
  simp [verticalReflectHom]

@[simp]
theorem verticalReflectHom_linearize_map (n m : ℕ) (f : TLDiagCat.of n ⟶ .of m) :
    verticalReflectHom (R := R) (δ := δ) n m ((linearize R δ).map f) =
      (linearize R δ).map (TLDiagCat.Hom.mk (TLDiagram.verticalReflect n m f.diagram)) := by
  rw [linearize_map, map_smul, verticalReflectHom_diagBasis]
  simp [linearize_map]

theorem verticalReflectHom_trans_verticalReflectHom (n m : ℕ) :
    (verticalReflectHom (R := R) (δ := δ) n m).trans (verticalReflectHom m n) =
      LinearEquiv.refl R _ := by
  rw [verticalReflectHom, verticalReflectHom, Module.Basis.equiv_trans,
    ← Module.Basis.equiv_refl (diagBasis (of n) (of m))]
  congr 1
  refine Equiv.ext fun x => ?_
  have h := congrArg TLDiagram.matching
    (TLDiagram.verticalReflect_verticalReflect (⟨x, 0⟩ : TLDiagram n m))
  simpa only [TLDiagram.matching_verticalReflect, Equiv.trans_apply, Equiv.refl_apply] using h

@[simp]
theorem verticalReflectHom_verticalReflectHom (n m : ℕ) (f : (of n : TLCat R δ) ⟶ of m) :
    verticalReflectHom m n (verticalReflectHom n m f) = f :=
  LinearEquiv.congr_fun (verticalReflectHom_trans_verticalReflectHom n m) f

@[simp]
theorem verticalReflectHom_symm (n m : ℕ) :
    (verticalReflectHom (R := R) (δ := δ) n m).symm = verticalReflectHom m n :=
  LinearEquiv.ext fun f =>
    (LinearEquiv.symm_apply_eq _).mpr (verticalReflectHom_verticalReflectHom m n f).symm

@[simp]
theorem verticalReflectHom_id (n : ℕ) :
    verticalReflectHom n n (𝟙 (of n : TLCat R δ)) = 𝟙 (of n : TLCat R δ) := by
  rw [id_eq_diagBasis, verticalReflectHom_diagBasis]
  have h := congrArg TLDiagram.matching (TLDiagram.verticalReflect_id n)
  rw [TLDiagram.matching_verticalReflect, TLDiagram.matching_id] at h
  exact congrArg (diagBasis (of n : TLCat R δ) (of n)) h

@[simp]
theorem verticalReflectHom_cup :
    verticalReflectHom 0 2 (cup : (of 0 : TLCat R δ) ⟶ of 2) = cap := by
  rw [cup_eq_diagBasis, verticalReflectHom_diagBasis, cap_eq_diagBasis]
  have h := congrArg TLDiagram.matching TLDiagram.verticalReflect_cup
  rw [TLDiagram.matching_verticalReflect] at h
  exact congrArg (diagBasis (of 2 : TLCat R δ) (of 0)) h

@[simp]
theorem verticalReflectHom_cap :
    verticalReflectHom 2 0 (cap : (of 2 : TLCat R δ) ⟶ of 0) = cup := by
  rw [cap_eq_diagBasis, verticalReflectHom_diagBasis, cup_eq_diagBasis]
  have h := congrArg TLDiagram.matching TLDiagram.verticalReflect_cap
  rw [TLDiagram.matching_verticalReflect] at h
  exact congrArg (diagBasis (of 0 : TLCat R δ) (of 2)) h

/-- **Horizontal (left–right) reflection**, lifted linearly to a module involution of
`(of n : TLCat R δ) ⟶ of m`. -/
noncomputable def reflectHom (n m : ℕ) :
    ((of n : TLCat R δ) ⟶ of m) ≃ₗ[R] ((of n : TLCat R δ) ⟶ of m) :=
  (diagBasis (of n) (of m)).equiv (diagBasis (of n) (of m))
    ((PlanarMatching.reflect (n + m)).trans (PlanarMatching.rotate (n + m) ^ n))

@[simp]
theorem reflectHom_diagBasis (n m : ℕ) (x : PlanarMatching (n + m)) :
    reflectHom (R := R) (δ := δ) n m (diagBasis (of n) (of m) x) =
      diagBasis (of n) (of m)
        ((PlanarMatching.rotate (n + m) ^ n) (PlanarMatching.reflect (n + m) x)) := by
  simp [reflectHom]

@[simp]
theorem reflectHom_linearize_map (n m : ℕ) (f : TLDiagCat.of n ⟶ .of m) :
    reflectHom (R := R) (δ := δ) n m ((linearize R δ).map f) =
      (linearize R δ).map (TLDiagCat.Hom.mk (TLDiagram.reflect n m f.diagram)) := by
  rw [linearize_map, map_smul, reflectHom_diagBasis]
  simp [linearize_map]

theorem reflectHom_trans_reflectHom (n m : ℕ) :
    (reflectHom (R := R) (δ := δ) n m).trans (reflectHom n m) = LinearEquiv.refl R _ := by
  rw [reflectHom, Module.Basis.equiv_trans, ← Module.Basis.equiv_refl (diagBasis (of n) (of m))]
  congr 1
  refine Equiv.ext fun x => ?_
  have h := congrArg TLDiagram.matching (TLDiagram.reflect_reflect (⟨x, 0⟩ : TLDiagram n m))
  simpa only [TLDiagram.matching_reflect, Equiv.trans_apply, Equiv.refl_apply] using h

@[simp]
theorem reflectHom_reflectHom (n m : ℕ) (f : (of n : TLCat R δ) ⟶ of m) :
    reflectHom n m (reflectHom n m f) = f :=
  LinearEquiv.congr_fun (reflectHom_trans_reflectHom n m) f

@[simp]
theorem reflectHom_symm (n m : ℕ) :
    (reflectHom (R := R) (δ := δ) n m).symm = reflectHom n m :=
  LinearEquiv.ext fun f =>
    (LinearEquiv.symm_apply_eq _).mpr (reflectHom_reflectHom n m f).symm

theorem verticalReflectHom_trans_reflectHom (n m : ℕ) :
    (verticalReflectHom (R := R) (δ := δ) n m).trans (reflectHom m n) =
      (reflectHom n m).trans (verticalReflectHom n m) := by
  rw [verticalReflectHom, reflectHom, reflectHom, Module.Basis.equiv_trans,
    Module.Basis.equiv_trans]
  congr 1
  refine Equiv.ext fun x => ?_
  have h := congrArg TLDiagram.matching
    (TLDiagram.reflect_verticalReflect (⟨x, 0⟩ : TLDiagram n m))
  simpa only [TLDiagram.matching_reflect, TLDiagram.matching_verticalReflect,
    Equiv.trans_apply] using h

theorem reflectHom_verticalReflectHom (n m : ℕ) (f : (of n : TLCat R δ) ⟶ of m) :
    reflectHom m n (verticalReflectHom n m f) =
      verticalReflectHom n m (reflectHom n m f) :=
  LinearEquiv.congr_fun (verticalReflectHom_trans_reflectHom n m) f

theorem dragRight_trans_reflectHom (n m : ℕ) :
    (dragRight (R := R) (δ := δ) n m).trans (reflectHom n (m + 1)) =
      (reflectHom (n + 1) m).trans (dragLeft n m) := by
  rw [dragRight, reflectHom, reflectHom, dragLeft, Module.Basis.equiv_trans,
    Module.Basis.equiv_trans]
  congr 1
  refine Equiv.ext fun x => ?_
  have h := congrArg TLDiagram.matching
    (TLDiagram.reflect_dragRight (⟨x, 0⟩ : TLDiagram (n + 1) m))
  simpa only [TLDiagram.matching_reflect, TLDiagram.matching_dragRight,
    TLDiagram.matching_dragLeft, Equiv.trans_apply] using h

theorem reflectHom_dragRight (n m : ℕ) (f : (of (n + 1) : TLCat R δ) ⟶ of m) :
    reflectHom n (m + 1) (dragRight n m f) = dragLeft n m (reflectHom (n + 1) m f) :=
  LinearEquiv.congr_fun (dragRight_trans_reflectHom n m) f

/-! ### Base change along a ring homomorphism -/

section BaseChange

variable {S : Type v} [CommRing S] {δ' : S}

/-- **Base change of the Temperley–Lieb category** along a ring homomorphism `φ : R →+* S` sending
`δ` to `δ'`: preserves objects and applies `φ` to every planar-matching coefficient.

Marked `@[expose, implicit_reducible]` so `((mapRingHom φ hδ).obj X)` reduces in dependent morphism
types `(mapRingHom φ hδ).obj X ⟶ (mapRingHom φ hδ).obj Y` without `eqToHom`. -/
@[expose, implicit_reducible]
noncomputable def mapRingHom (φ : R →+* S) (hδ : φ δ = δ') : TLCat R δ ⥤ TLCat S δ' where
  obj X := of X.as
  map f := ⟨Finsupp.mapRange φ φ.map_zero f.coeff⟩
  map_id X := hom_ext <| by simp
  map_comp f g := hom_ext <| by
    simp only [coeff_comp]
    induction f.coeff using Finsupp.induction_linear with
    | zero => simp
    | add u₁ u₂ ih₁ ih₂ => simp [Finsupp.mapRange_add, ih₁, ih₂]
    | single x a =>
      induction g.coeff using Finsupp.induction_linear with
      | zero => simp
      | add v₁ v₂ ih₁ ih₂ => simp [Finsupp.mapRange_add, ih₁, ih₂]
      | single y b =>
        simp [compCoeff_single_single, hδ]

@[simp]
theorem mapRingHom_obj_as (φ : R →+* S) (hδ : φ δ = δ') (X : TLCat R δ) :
    ((mapRingHom φ hδ).obj X).as = X.as := (rfl)

@[simp]
theorem mapRingHom_obj_of (φ : R →+* S) (hδ : φ δ = δ') (n : ℕ) :
    (mapRingHom φ hδ).obj (of n) = of n := (rfl)

@[simp]
theorem coeff_mapRingHom_map (φ : R →+* S) (hδ : φ δ = δ') {X Y : TLCat R δ} (f : X ⟶ Y) :
    ((mapRingHom φ hδ).map f).coeff = Finsupp.mapRange φ φ.map_zero f.coeff := (rfl)

instance (φ : R →+* S) (hδ : φ δ = δ') : (mapRingHom φ hδ).Additive where
  map_add {_ _} f g := hom_ext (Finsupp.ext fun x => by simp)

@[simp]
theorem mapRingHom_map_diagBasis (φ : R →+* S) (hδ : φ δ = δ')
    {X Y : TLCat R δ} (x : PlanarMatching (X.as + Y.as)) :
    (mapRingHom φ hδ).map (diagBasis X Y x) =
      diagBasis ((mapRingHom φ hδ).obj X) ((mapRingHom φ hδ).obj Y) x :=
  hom_ext <| by simp

@[simp]
theorem mapRingHom_map_smul (φ : R →+* S) (hδ : φ δ = δ') {X Y : TLCat R δ}
    (r : R) (f : X ⟶ Y) :
    (mapRingHom φ hδ).map (r • f) = φ r • (mapRingHom φ hδ).map f :=
  hom_ext (Finsupp.ext fun x => by simp)

@[simp]
theorem mapRingHom_map_linearize_map (φ : R →+* S) (hδ : φ δ = δ')
    {X Y : TLDiagCat} (f : X ⟶ Y) :
    (mapRingHom φ hδ).map ((linearize R δ).map f) = (linearize S δ').map f := by
  rw [linearize_map, mapRingHom_map_smul, map_pow, hδ,
    mapRingHom_map_diagBasis φ hδ (X := of X.as) (Y := of Y.as) f.diagram.matching]
  rfl

@[simp]
theorem mapRingHom_map_cup (φ : R →+* S) (hδ : φ δ = δ') :
    (mapRingHom φ hδ).map (cup : (of 0 : TLCat R δ) ⟶ of 2) = cup :=
  mapRingHom_map_diagBasis φ hδ (X := of 0) (Y := of 2) TLDiagram.cup.matching

@[simp]
theorem mapRingHom_map_cap (φ : R →+* S) (hδ : φ δ = δ') :
    (mapRingHom φ hδ).map (cap : (of 2 : TLCat R δ) ⟶ of 0) = cap :=
  mapRingHom_map_diagBasis φ hδ (X := of 2) (Y := of 0) TLDiagram.cap.matching

/-- Base change along `RingHom.id R` is naturally isomorphic to the identity functor. -/
noncomputable def mapRingHomIdIso :
    mapRingHom (RingHom.id R) (rfl : RingHom.id R δ = δ) ≅ 𝟭 (TLCat R δ) :=
  NatIso.ofComponents (fun X => Iso.refl X) fun {X Y} f => by
    cases X; cases Y
    dsimp only [Functor.id_obj, Functor.id_map, Iso.refl_hom, mapRingHom]
    rw [Category.comp_id, Category.id_comp]
    exact hom_ext (Finsupp.ext fun _ => by simp)

@[simp]
theorem mapRingHomIdIso_hom_app (X : TLCat R δ) :
    (mapRingHomIdIso (R := R) (δ := δ)).hom.app X = 𝟙 X := (rfl)

@[simp]
theorem mapRingHomIdIso_inv_app (X : TLCat R δ) :
    (mapRingHomIdIso (R := R) (δ := δ)).inv.app X = 𝟙 X := (rfl)

/-- Composing two base-change functors is naturally isomorphic to base change along the composite
ring homomorphism. -/
noncomputable def mapRingHomCompIso {T : Type*} [CommRing T] {δ'' : T}
    (φ : R →+* S) (hδ : φ δ = δ') (ψ : S →+* T) (hδ' : ψ δ' = δ'') :
    mapRingHom φ hδ ⋙ mapRingHom ψ hδ' ≅
      mapRingHom (ψ.comp φ) (by rw [RingHom.comp_apply, hδ, hδ']) :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun f => by
    dsimp only [Functor.comp_obj, Functor.comp_map, Iso.refl_hom]
    rw [Category.comp_id, Category.id_comp]
    exact hom_ext (Finsupp.ext fun _ => by simp)

@[simp]
theorem mapRingHomCompIso_hom_app {T : Type*} [CommRing T] {δ'' : T}
    (φ : R →+* S) (hδ : φ δ = δ') (ψ : S →+* T) (hδ' : ψ δ' = δ'') (X : TLCat R δ) :
    (mapRingHomCompIso φ hδ ψ hδ').hom.app X = 𝟙 (of X.as) := (rfl)

@[simp]
theorem mapRingHomCompIso_inv_app {T : Type*} [CommRing T] {δ'' : T}
    (φ : R →+* S) (hδ : φ δ = δ') (ψ : S →+* T) (hδ' : ψ δ' = δ'') (X : TLCat R δ) :
    (mapRingHomCompIso φ hδ ψ hδ').inv.app X = 𝟙 (of X.as) := (rfl)

end BaseChange

end Category

end TLCat

end TauCeti

end

/-! ### Non-generic `δ` and instance-coherence checks -/

namespace TauCeti.TLCat

open CategoryTheory

-- At `δ = 0` over any nontrivial commutative ring, the closed circle vanishes while `cup` remains
-- a monomorphism and `cap` is not a monomorphism.
example {R : Type*} [CommRing R] [Nontrivial R] :
    (linearize R (0 : R)).map TLDiagCat.circle = 0 ∧
      Mono (cup : (of 0 : TLCat R (0 : R)) ⟶ of 2) ∧
      ¬ Mono (cap : (of 2 : TLCat R (0 : R)) ⟶ of 0) :=
  ⟨by simp, inferInstance, not_mono_cap⟩

-- At the zero-divisor `δ = 2` in `ZMod 6`, `cup ≫ cap` is nonzero yet fails to be a monomorphism,
-- annihilated by `3 • 𝟙 (of 0) ≠ 0`.
example :
    ((cup : (of 0 : TLCat (ZMod 6) 2) ⟶ of 2) ≫ cap) ≠ 0 ∧
      ¬ Mono ((cup : (of 0 : TLCat (ZMod 6) 2) ⟶ of 2) ≫ cap) := by
  refine ⟨fun h => ?_, ?_⟩
  · have h0 := DFunLike.congr_fun (congrArg Hom.coeff h) (PlanarMatching.nested 0)
    rw [cup_comp_cap] at h0
    simp only [coeff_smul, coeff_id, coeff_zero, Finsupp.coe_smul, Finsupp.coe_zero,
      Pi.smul_apply, Pi.zero_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h0
    exact absurd h0 (by decide)
  · rw [cup_comp_cap, mono_smul_id_zero_iff, mem_nonZeroDivisors_iff_right]
    push Not
    exact ⟨3, by decide, by decide⟩

-- Over `ℤ`, the `Linear ℤ (TLCat ℤ δ)` instance agrees definitionally with
-- `CategoryTheory.Linear.preadditiveIntLinear`.
example (δ : ℤ) :
    (inferInstance : CategoryTheory.Linear ℤ (TLCat ℤ δ)) =
      CategoryTheory.Linear.preadditiveIntLinear :=
  rfl

end TauCeti.TLCat

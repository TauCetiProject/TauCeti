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

## Main results

* `TauCeti.TLCat.diagBasis_comp_diagBasis`: **the loop rule** on basis matchings.
* `TauCeti.TLCat.finrank_hom_of_add_eq_two_mul`, `TauCeti.TLCat.finrank_end_of`: when
  `X.as + Y.as = 2 * k`, the module `X ⟶ Y` is free of rank `catalan k`; in particular `End (of n)`
  has rank `catalan n`.
* `TauCeti.TLCat.hom_eq_zero_of_not_even`, `TauCeti.TLCat.finrank_hom_of_odd`: when
  `X.as + Y.as` is odd, `X ⟶ Y` vanishes and has rank `0`.
* `TauCeti.TLCat.cup_comp_cap`: `cup ≫ cap = δ • 𝟙 (of 0)`.
* `TauCeti.TLCat.mono_diagBasis_zero_left`, `TauCeti.TLCat.epi_diagBasis_zero_right`: every basis
  morphism out of `of 0` is a monomorphism and every basis morphism into `of 0` is an epimorphism
  (in particular `Mono cup` and `Epi cap` for every `R` and `δ`), whereas `cap` is never a
  monomorphism (`TauCeti.TLCat.not_mono_cap`) and `cup` is never an epimorphism
  (`TauCeti.TLCat.not_epi_cup`) over a nontrivial ring.
* `TauCeti.TLCat.mono_smul_id_zero_iff`, `TauCeti.TLCat.epi_smul_id_zero_iff`,
  `TauCeti.TLCat.isIso_smul_id_zero_iff`: `r • 𝟙 (of 0)` is a monomorphism (or epimorphism) iff
  `r ∈ nonZeroDivisors R`, and an isomorphism iff `IsUnit r`.

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

/-- Induction on morphisms of `TLCat R δ` along the diagram basis: a property of morphisms
`X ⟶ Y` that holds on every basis morphism and is closed under `0`, addition and scalar
multiplication holds for every morphism. -/
@[elab_as_elim]
theorem hom_induction {motive : (X ⟶ Y) → Prop} (zero : motive 0)
    (add : ∀ f g, motive f → motive g → motive (f + g))
    (smul : ∀ (r : R) f, motive f → motive (r • f)) (basis : ∀ x, motive (diagBasis X Y x))
    (f : X ⟶ Y) : motive f := by
  have hf : f ∈ Submodule.span R (Set.range (diagBasis X Y)) := by
    rw [(diagBasis X Y).span_eq]
    exact Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem _ h => obtain ⟨x, rfl⟩ := h; exact basis x
  | zero => exact zero
  | add _ _ _ _ h₁ h₂ => exact add _ _ h₁ h₂
  | smul r _ _ h => exact smul r _ h

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
theorem finrank_hom_self [StrongRankCondition R] (X : TLCat R δ) :
    Module.finrank R (X ⟶ X) = catalan X.as :=
  finrank_hom_of_add_eq_two_mul (two_mul X.as).symm

/-- **Catalan rank of endomorphism algebras.** The endomorphism `R`-algebra `End (of n)` is free of
rank `catalan n`. -/
@[simp]
theorem finrank_end_of [StrongRankCondition R] (n : ℕ) :
    Module.finrank R (End (of n : TLCat R δ)) = catalan n :=
  (End.linearEquiv (R := R) (X := (of n : TLCat R δ))).finrank_eq.trans (finrank_hom_self (of n))

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

/-- Every basis morphism is the image of a circle-free diagram under linearization. -/
theorem diagBasis_eq_linearize_map (x : PlanarMatching (X.as + Y.as)) :
    diagBasis X Y x =
      (linearize R δ).map (TLDiagCat.Hom.mk ⟨x, 0⟩ : TLDiagCat.of X.as ⟶ TLDiagCat.of Y.as) := by
  simp only [linearize_map_mk, pow_zero, one_smul]

instance : (linearize R δ).EssSurj where
  mem_essImage Y := ⟨.of Y.as, ⟨Iso.refl Y⟩⟩

/-- The image of `TLDiagCat` morphisms under `linearize R δ` spans every morphism module of
`TLCat R δ` over `R`. -/
theorem span_range_linearize_map (X Y : TLDiagCat) :
    Submodule.span R (Set.range ((linearize R δ).map : (X ⟶ Y) → _)) = ⊤ := by
  cases X with | of n =>
  cases Y with | of m =>
  rw [eq_top_iff, ← (diagBasis (of n) (of m)).span_eq, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact Submodule.subset_span ⟨TLDiagCat.Hom.mk ⟨x, 0⟩, by simp⟩

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
  cases X with | of n =>
  cases Y with | of m =>
  cases f with | mk d =>
  cases d with | mk x c =>
  dsimp only at x ⊢
  rw [linearize_map_mk, Functor.map_smul, liftDiag_map_diagBasis F hF (X := of n) (Y := of m),
    ← liftDiag_map_mk_circles F hF]

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

/-- Over a nontrivial ring, `cap ≫ cup` is never a scalar multiple of `𝟙 (of 2)` for any
`r : R`. -/
theorem cap_comp_cup_ne_smul_id [Nontrivial R] (r : R) :
    (cap : (of 2 : TLCat R δ) ⟶ of 0) ≫ cup ≠ r • 𝟙 (of 2 : TLCat R δ) := by
  intro h
  have hne : PlanarMatching.nested 2 ≠ (TLDiagram.cap.comp TLDiagram.cup).matching := by
    intro hm
    have h0 := congrFun (congrArg (fun x : PlanarMatching 4 => ⇑x.val.val) hm) 0
    simp only [TLDiagram.cap_comp_cup_matching_val, PlanarMatching.nested_val] at h0
    exact absurd h0 (by decide)
  rw [cap_comp_cup_eq_diagBasis] at h
  generalize (TLDiagram.cap.comp TLDiagram.cup).matching = m at h hne
  have hc := DFunLike.congr_fun (congrArg Hom.coeff h) m
  simp [coeff_diagBasis (X := of 2) (Y := of 2), hne] at hc

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

/-- Under `endZeroAlgEquiv`, a linearized diagram on the empty boundary evaluates to `δ` raised to
its number of closed circles. -/
theorem endZeroAlgEquiv_linearize_map (f : (TLDiagCat.of 0 : TLDiagCat) ⟶ .of 0) :
    endZeroAlgEquiv (End.of ((linearize R δ).map f)) = δ ^ f.diagram.circles := by
  have hm : f.diagram.matching = PlanarMatching.nested 0 :=
    Subsingleton.elim (α := PlanarMatching 0) _ _
  simp [linearize_map, hm, coeff_diagBasis (X := of 0) (Y := of 0)]

/-! ### Monomorphisms, epimorphisms, and non-generic `δ` -/

/-- Postcomposing a morphism `f : X ⟶ of 0` with a basis morphism `diagBasis (of 0) Y y`
pushes forward its planar-matching coefficients along `x ↦ glueMiddle 0 (x.append y)`. -/
theorem coeff_comp_diagBasis_zero (f : X ⟶ of 0) (y : PlanarMatching (0 + Y.as)) :
    (f ≫ diagBasis (of 0) Y y).coeff =
      Finsupp.mapDomain (fun x : PlanarMatching (X.as + 0) =>
        PlanarMatching.glueMiddle 0 (x.append y)) f.coeff := by
  rw [coeff_comp, coeff_diagBasis]
  induction f.coeff using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ ih₁ ih₂ => simp [Finsupp.mapDomain_add, ih₁, ih₂]
  | single x a =>
    rw [compCoeff_single_single]
    simp

/-- Precomposing a morphism `g : of 0 ⟶ Z` with a basis morphism `diagBasis X (of 0) x`
pushes forward its planar-matching coefficients along `z ↦ glueMiddle 0 (x.append z)`. -/
theorem coeff_diagBasis_zero_comp (x : PlanarMatching (X.as + 0)) (g : of 0 ⟶ Z) :
    (diagBasis X (of 0) x ≫ g).coeff =
      Finsupp.mapDomain (fun z : PlanarMatching (0 + Z.as) =>
        PlanarMatching.glueMiddle 0 (x.append z)) g.coeff := by
  rw [coeff_comp, coeff_diagBasis]
  induction g.coeff using Finsupp.induction_linear with
  | zero => simp
  | add v₁ v₂ ih₁ ih₂ => simp [Finsupp.mapDomain_add, ih₁, ih₂]
  | single z b =>
    rw [compCoeff_single_single]
    simp

private theorem glueMiddle_zero_append_left_injective {n m : ℕ} (y : PlanarMatching (0 + m)) :
    Function.Injective (fun x : PlanarMatching (n + 0) =>
      PlanarMatching.glueMiddle 0 (x.append y)) := by
  intro x₁ x₂ hx
  simp only [PlanarMatching.glueMiddle_zero, EmbeddingLike.apply_eq_iff_eq] at hx
  refine PlanarMatching.ext fun i => Fin.castAdd_injective (n + 0) (0 + m) ?_
  have hi := congrFun (congrArg (fun z : PlanarMatching _ => ⇑z.val.val) hx)
    (Fin.castAdd (0 + m) i)
  simpa only [PlanarMatching.append_val_castAdd] using hi

private theorem glueMiddle_zero_append_right_injective {n m : ℕ} (x : PlanarMatching (n + 0)) :
    Function.Injective (fun z : PlanarMatching (0 + m) =>
      PlanarMatching.glueMiddle 0 (x.append z)) := by
  intro z₁ z₂ hz
  simp only [PlanarMatching.glueMiddle_zero, EmbeddingLike.apply_eq_iff_eq] at hz
  refine PlanarMatching.ext fun j => Fin.natAdd_injective (0 + m) (n + 0) ?_
  have hj := congrFun (congrArg (fun w : PlanarMatching _ => ⇑w.val.val) hz)
    (Fin.natAdd (n + 0) j)
  simpa only [PlanarMatching.append_val_natAdd] using hj

/-- Every planar-matching basis morphism out of the empty boundary `of 0` is a monomorphism, for
every commutative ring `R` and every loop value `δ : R`: gluing along `0` points closes no circle
and appends `y` injectively to each matching on `X.as + 0`. -/
theorem mono_diagBasis_zero_left {Y : TLCat R δ} (y : PlanarMatching (0 + Y.as)) :
    Mono (diagBasis (of 0) Y y) :=
  ⟨fun f₁ f₂ h => hom_ext <|
    Finsupp.mapDomain_injective (glueMiddle_zero_append_left_injective y) <| by
      rw [← coeff_comp_diagBasis_zero, ← coeff_comp_diagBasis_zero, h]⟩

/-- Every planar-matching basis morphism into the empty boundary `of 0` is an epimorphism, for
every commutative ring `R` and every loop value `δ : R`. -/
theorem epi_diagBasis_zero_right {X : TLCat R δ} (x : PlanarMatching (X.as + 0)) :
    Epi (diagBasis X (of 0) x) :=
  ⟨fun g₁ g₂ h => hom_ext <|
    Finsupp.mapDomain_injective (glueMiddle_zero_append_right_injective x) <| by
      rw [← coeff_diagBasis_zero_comp, ← coeff_diagBasis_zero_comp, h]⟩

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

private theorem eq_zero_of_smul_id_zero_eq_zero {s : R}
    (h : s • 𝟙 (of 0 : TLCat R δ) = 0) : s = 0 := by
  simpa using congrArg (fun f : (of 0 : TLCat R δ) ⟶ of 0 => f.coeff (PlanarMatching.nested 0)) h

private theorem smul_injective_of_mem_nonZeroDivisors {r : R} (hr : r ∈ nonZeroDivisors R)
    {X Y : TLCat R δ} : Function.Injective (fun f : X ⟶ Y => r • f) := by
  intro f₁ f₂ h
  refine hom_ext (Finsupp.ext fun x => sub_eq_zero.mp (mem_nonZeroDivisors_iff_left.mp hr _ ?_))
  have hx := DFunLike.congr_fun (congrArg Hom.coeff h) x
  simpa [mul_sub, sub_eq_zero] using hx

/-- A scalar endomorphism `r • 𝟙 (of 0)` of the empty boundary is a monomorphism if and only if
`r` is a non-zero-divisor in `R`. -/
theorem mono_smul_id_zero_iff (r : R) :
    Mono (r • 𝟙 (of 0 : TLCat R δ)) ↔ r ∈ nonZeroDivisors R :=
  ⟨fun _ => mem_nonZeroDivisors_iff_left.mpr fun s hsr =>
    eq_zero_of_smul_id_zero_eq_zero ((cancel_mono (r • 𝟙 (of 0 : TLCat R δ))).mp <| by
      simp [smul_smul, hsr]),
    fun hr => ⟨fun f₁ f₂ h => smul_injective_of_mem_nonZeroDivisors hr (by simpa using h)⟩⟩

/-- A scalar endomorphism `r • 𝟙 (of 0)` of the empty boundary is an epimorphism if and only if
`r` is a non-zero-divisor in `R`. -/
theorem epi_smul_id_zero_iff (r : R) :
    Epi (r • 𝟙 (of 0 : TLCat R δ)) ↔ r ∈ nonZeroDivisors R :=
  ⟨fun _ => mem_nonZeroDivisors_iff_right.mpr fun s hsr =>
    eq_zero_of_smul_id_zero_eq_zero ((cancel_epi (r • 𝟙 (of 0 : TLCat R δ))).mp <| by
      simp [smul_smul, hsr]),
    fun hr => ⟨fun g₁ g₂ h => smul_injective_of_mem_nonZeroDivisors hr (by simpa using h)⟩⟩

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
theorem mono_linearize_map_circle_iff :
    Mono ((linearize R δ).map TLDiagCat.circle) ↔ δ ∈ nonZeroDivisors R := by
  rw [linearize_map_circle, mono_smul_id_zero_iff]

/-- The image of `TLDiagCat.circle` in `TLCat R δ` is an epimorphism if and only if
`δ ∈ nonZeroDivisors R`. -/
theorem epi_linearize_map_circle_iff :
    Epi ((linearize R δ).map TLDiagCat.circle) ↔ δ ∈ nonZeroDivisors R := by
  rw [linearize_map_circle, epi_smul_id_zero_iff]

/-- The image of `TLDiagCat.circle` in `TLCat R δ` is an isomorphism if and only if `IsUnit δ`. -/
theorem isIso_linearize_map_circle_iff :
    IsIso ((linearize R δ).map TLDiagCat.circle) ↔ IsUnit δ := by
  rw [linearize_map_circle, isIso_smul_id_zero_iff]

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
  · have h0 : (2 : ZMod 6) = 0 := by
      simpa [cup_comp_cap] using congrArg
        (fun f : (of 0 : TLCat (ZMod 6) 2) ⟶ of 0 => f.coeff (PlanarMatching.nested 0)) h
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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.Algebra.TemperleyLieb.Category
public import TauCeti.Combinatorics.PlanarMatching.Monoidal

/-!
# The monoidal structure of the linear Temperley–Lieb category

The linear Temperley–Lieb category `TauCeti.TLCat R δ` is a strict monoidal `R`-linear category
under juxtaposition of diagrams. The tensor product of objects adds the numbers of boundary points,
`TLCat.of n ⊗ TLCat.of m = TLCat.of (n + m)`, the unit is the empty boundary `TLCat.of 0`, and the
tensor product of two basis morphisms places the second matching to the right of the first:

`diagBasis X Y x ⊗ₘ diagBasis X' Y' y = diagBasis (X ⊗ X') (Y ⊗ Y') (x ⊗ y)`,

where `x ⊗ y` is the matching of the tensor product `TauCeti.TLDiagram.tensor` of the circle-free
diagrams `x` and `y`. On general morphisms the tensor product is the bilinear extension of this
rule. The associators and unitors are the transports `eqToHom` along the equalities
`n + m + k = n + (m + k)`, `0 + n = n` and `n + 0 = n`, as in the diagram category
`TauCeti.TLDiagCat`.

The linearization functor `TauCeti.TLCat.linearize R δ : TLDiagCat ⥤ TLCat R δ` is strict monoidal:
it sends a tensor product of diagrams to the tensor product of their images, because juxtaposing
two diagrams adds their circle counts and `δ ^ (c + c') = δ ^ c * δ ^ c'`. Since its image spans
every morphism module, each axiom of the monoidal structure on `TLCat R δ` is the image of the
corresponding axiom on `TLDiagCat`, extended multilinearly.

The same argument makes the diagram-linearization universal property monoidal: if a monoidal
functor `F : TLDiagCat ⥤ D` into a monoidal `R`-linear category evaluates each closed circle to
`δ`, its `R`-linear extension `TauCeti.TLCat.liftDiag F hF : TLCat R δ ⥤ D` is monoidal, with the
structure morphisms of `F`, and its identification with `F` along `linearize R δ` is monoidal.
This is the step between monoidal functors out of the diagram category, which interpret a
self-duality, and monoidal functors out of `TLCat R δ`.

## Main definitions

* `TauCeti.TLCat.tensorCoeff`: juxtaposition of planar-matching coefficient vectors.
* `TauCeti.TLCat.instMonoidalCategory`: the monoidal structure on `TLCat R δ`.
* `TauCeti.TLCat.instMonoidalLinearize`: `linearize R δ` is a monoidal functor, with identity
  structure morphisms.
* `TauCeti.TLCat.instMonoidalLiftDiag`: `liftDiag F hF` is a monoidal functor when `F` is.

## Main results

* `TauCeti.TLCat.diagBasis_tensorHom_diagBasis`: the tensor product of two basis morphisms, and
  `TauCeti.TLCat.whiskerLeft_diagBasis`, `TauCeti.TLCat.diagBasis_whiskerRight` for whiskerings.
* `TauCeti.TLCat.linearize_map_tensorHom`: linearization preserves tensor products of morphisms.
* `TauCeti.TLCat.instMonoidalPreadditive`, `TauCeti.TLCat.instMonoidalLinear`: the tensor product
  is `R`-bilinear.
* `TauCeti.TLCat.associator_hom`, `TauCeti.TLCat.leftUnitor_hom`, `TauCeti.TLCat.rightUnitor_hom`
  and their inverses: the monoidal structure is strict.
* `TauCeti.TLCat.liftDiag_ε`, `TauCeti.TLCat.liftDiag_μ`: the structure morphisms of the
  extension, and the instance `NatTrans.IsMonoidal (linearizeLiftDiagIso F hF).hom`.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace TLCat

universe u

variable {R : Type u} [CommRing R] {δ : R}

/-! ### Juxtaposition of coefficient vectors -/

/-- Juxtaposition of planar-matching coefficient vectors, bilinear in both arguments: on basis
vectors `(x, y)` it produces the basis vector of the matching of the tensor product of the
circle-free diagrams `x : n → m` and `y : n' → m'`. -/
noncomputable def tensorCoeff {n m n' m' : ℕ} :
    (PlanarMatching (n + m) →₀ R) →ₗ[R] (PlanarMatching (n' + m') →₀ R) →ₗ[R]
      (PlanarMatching (n + n' + (m + m')) →₀ R) :=
  Finsupp.lsum R fun x => LinearMap.smulRight LinearMap.id
    (Finsupp.lmapDomain R R fun y => (TLDiagram.tensor ⟨x, 0⟩ ⟨y, 0⟩).matching)

/-- Juxtaposition on two basis vectors of planar-matching coefficients. -/
theorem tensorCoeff_single_single {n m n' m' : ℕ} (x : PlanarMatching (n + m))
    (y : PlanarMatching (n' + m')) (a b : R) :
    tensorCoeff (Finsupp.single x a) (Finsupp.single y b) =
      Finsupp.single (TLDiagram.tensor ⟨x, 0⟩ ⟨y, 0⟩).matching (a * b) := by
  simp [tensorCoeff, Finsupp.smul_single]

/-! ### The monoidal structure -/

noncomputable instance : MonoidalCategoryStruct (TLCat R δ) where
  tensorObj X Y := of (X.as + Y.as)
  whiskerLeft X _ _ f := ⟨tensorCoeff (𝟙 X : X ⟶ X).coeff f.coeff⟩
  whiskerRight f Y := ⟨tensorCoeff f.coeff (𝟙 Y : Y ⟶ Y).coeff⟩
  tensorHom f g := ⟨tensorCoeff f.coeff g.coeff⟩
  tensorUnit := of 0
  associator X Y Z := eqToIso (TLCat.ext (Nat.add_assoc X.as Y.as Z.as))
  leftUnitor X := eqToIso (TLCat.ext (Nat.zero_add X.as))
  rightUnitor X := eqToIso (TLCat.ext (Nat.add_zero X.as))

variable {X Y Z X' Y' Z' : TLCat R δ}

/-! The next two lemmas are proved by `rfl`, not `(rfl)`, so that `dsimp` and `simp` can rewrite
the numbers of points inside the indices of matching types, as for `TauCeti.TLDiagCat`. -/

/-- The tensor product of objects adds the numbers of boundary points. -/
@[simp]
theorem tensorObj_as (X Y : TLCat R δ) : (X ⊗ Y).as = X.as + Y.as := rfl

/-- The monoidal unit is the empty boundary. -/
@[simp]
theorem tensorUnit_as : (𝟙_ (TLCat R δ)).as = 0 := rfl

/-- The coefficients of a tensor product of morphisms are given by `tensorCoeff`. -/
theorem coeff_tensorHom (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ₘ g).coeff = tensorCoeff f.coeff g.coeff := (rfl)

/-- The associator is the transport along `X.as + Y.as + Z.as = X.as + (Y.as + Z.as)`. -/
theorem associator_hom (X Y Z : TLCat R δ) :
    (α_ X Y Z).hom = eqToHom (TLCat.ext (Nat.add_assoc X.as Y.as Z.as)) := (rfl)

theorem associator_inv (X Y Z : TLCat R δ) :
    (α_ X Y Z).inv = eqToHom (TLCat.ext (Nat.add_assoc X.as Y.as Z.as).symm) := (rfl)

/-- The left unitor is the transport along `0 + X.as = X.as`. -/
theorem leftUnitor_hom (X : TLCat R δ) :
    (λ_ X).hom = eqToHom (TLCat.ext (Nat.zero_add X.as)) := (rfl)

theorem leftUnitor_inv (X : TLCat R δ) :
    (λ_ X).inv = eqToHom (TLCat.ext (Nat.zero_add X.as).symm) := (rfl)

/-- The right unitor is the transport along `X.as + 0 = X.as`. -/
theorem rightUnitor_hom (X : TLCat R δ) :
    (ρ_ X).hom = eqToHom (TLCat.ext (Nat.add_zero X.as)) := (rfl)

theorem rightUnitor_inv (X : TLCat R δ) :
    (ρ_ X).inv = eqToHom (TLCat.ext (Nat.add_zero X.as).symm) := (rfl)

/-- **The juxtaposition rule.** The tensor product of two basis morphisms is the basis morphism of
the juxtaposed matching, with no scalar factor: juxtaposition closes no circle. -/
@[simp]
theorem diagBasis_tensorHom_diagBasis (x : PlanarMatching (X.as + Y.as))
    (y : PlanarMatching (X'.as + Y'.as)) :
    diagBasis X Y x ⊗ₘ diagBasis X' Y' y =
      diagBasis (X ⊗ X') (Y ⊗ Y') (TLDiagram.tensor ⟨x, 0⟩ ⟨y, 0⟩).matching :=
  hom_ext <| by
    rw [coeff_tensorHom, coeff_diagBasis, coeff_diagBasis, tensorCoeff_single_single, mul_one,
      coeff_diagBasis]

/-! The bilinearity of the tensor product, needed to construct the monoidal structure. Once it
exists, these follow from the `MonoidalPreadditive` and `MonoidalLinear` instances below (for
instance as `MonoidalPreadditive.add_tensor`). -/

private theorem zero_tensorHom (g : X' ⟶ Y') : (0 : X ⟶ Y) ⊗ₘ g = 0 :=
  hom_ext <| by simp [coeff_tensorHom]

private theorem tensorHom_zero (f : X ⟶ Y) : f ⊗ₘ (0 : X' ⟶ Y') = 0 :=
  hom_ext <| by simp [coeff_tensorHom]

private theorem add_tensorHom (f₁ f₂ : X ⟶ Y) (g : X' ⟶ Y') :
    (f₁ + f₂) ⊗ₘ g = f₁ ⊗ₘ g + f₂ ⊗ₘ g :=
  hom_ext <| by simp [coeff_tensorHom]

private theorem tensorHom_add (f : X ⟶ Y) (g₁ g₂ : X' ⟶ Y') :
    f ⊗ₘ (g₁ + g₂) = f ⊗ₘ g₁ + f ⊗ₘ g₂ :=
  hom_ext <| by simp [coeff_tensorHom]

private theorem smul_tensorHom (r : R) (f : X ⟶ Y) (g : X' ⟶ Y') :
    (r • f) ⊗ₘ g = r • (f ⊗ₘ g) :=
  hom_ext <| by simp [coeff_tensorHom]

private theorem tensorHom_smul (r : R) (f : X ⟶ Y) (g : X' ⟶ Y') :
    f ⊗ₘ (r • g) = r • (f ⊗ₘ g) :=
  hom_ext <| by simp [coeff_tensorHom]

/-- Every basis morphism is the image of a circle-free diagram under linearization. -/
private theorem diagBasis_eq_linearize_map (x : PlanarMatching (X.as + Y.as)) :
    diagBasis X Y x =
      (linearize R δ).map (TLDiagCat.Hom.mk ⟨x, 0⟩ : TLDiagCat.of X.as ⟶ TLDiagCat.of Y.as) := by
  simp

/-- **Linearization preserves tensor products of morphisms**: juxtaposition adds the circle counts
of two diagrams, and `δ ^ (c + c') = δ ^ c * δ ^ c'`. -/
@[simp]
theorem linearize_map_tensorHom {X Y X' Y' : TLDiagCat} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (linearize R δ).map (f ⊗ₘ g) = (linearize R δ).map f ⊗ₘ (linearize R δ).map g := by
  have h : (δ ^ f.diagram.circles •
        diagBasis (of X.as : TLCat R δ) (of Y.as) f.diagram.matching) ⊗ₘ
      (δ ^ g.diagram.circles • diagBasis (of X'.as : TLCat R δ) (of Y'.as) g.diagram.matching) =
      (δ ^ f.diagram.circles * δ ^ g.diagram.circles) •
        diagBasis (of X.as ⊗ of X'.as) (of Y.as ⊗ of Y'.as)
          (TLDiagram.tensor ⟨f.diagram.matching, 0⟩ ⟨g.diagram.matching, 0⟩).matching := by
    rw [smul_tensorHom, tensorHom_smul, diagBasis_tensorHom_diagBasis, smul_smul]
  rw [linearize_map, linearize_map, linearize_map]
  refine Eq.trans ?_ h.symm
  simp only [TLDiagCat.diagram_tensorHom, TLDiagram.circles_tensor, pow_add,
    TLDiagram.matching_tensor]
  -- The two sides differ only in writing the objects as `of (X.as + X'.as)` and
  -- `of X.as ⊗ of X'.as`, which are equal by definition of the tensor product of objects.
  rfl

/-! The axioms of the monoidal structure. Each side of each naturality axiom is linear in each
morphism, so it suffices to check them on basis morphisms, which are images of diagrams under
`linearize R δ`; there each axiom is the image of the same axiom in `TLDiagCat`. That image `h` is
stated between the objects `(linearize R δ).obj (TLDiagCat.of X.as)`, which are `X` by definition
of `linearize R δ` on objects, and the structure isomorphisms of `TLCat R δ` are the transports
`eqToHom` of `associator_hom`, `leftUnitor_hom` and `rightUnitor_hom`. -/

section Axioms

/- The bilinearity lemmas reduce the zero, sum and scalar cases of each basis induction below to
the inductive hypotheses. -/
attribute [local simp] zero_tensorHom tensorHom_zero add_tensorHom tensorHom_add smul_tensorHom
  tensorHom_smul

private theorem id_tensorHom_id' (X Y : TLCat R δ) : 𝟙 X ⊗ₘ 𝟙 Y = 𝟙 (X ⊗ Y) := by
  rw [id_eq_diagBasis, id_eq_diagBasis, diagBasis_tensorHom_diagBasis, id_eq_diagBasis,
    TLDiagram.mk_nested_zero, TLDiagram.mk_nested_zero, TLDiagram.id_tensor_id,
    TLDiagram.matching_id]
  dsimp only [tensorObj_as]

private theorem tensorHom_comp_tensorHom' {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : TLCat R δ} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
  induction f₁ using hom_induction with
  | basis x₁ =>
    induction f₂ using hom_induction with
    | basis x₂ =>
      induction g₁ using hom_induction with
      | basis y₁ =>
        induction g₂ using hom_induction with
        | basis y₂ =>
          have h := congrArg (linearize R δ).map (tensorHom_comp_tensorHom
            (TLDiagCat.Hom.mk ⟨x₁, 0⟩ : TLDiagCat.of _ ⟶ TLDiagCat.of _)
            (TLDiagCat.Hom.mk ⟨x₂, 0⟩ : TLDiagCat.of _ ⟶ TLDiagCat.of _)
            (TLDiagCat.Hom.mk ⟨y₁, 0⟩ : TLDiagCat.of _ ⟶ TLDiagCat.of _)
            (TLDiagCat.Hom.mk ⟨y₂, 0⟩ : TLDiagCat.of _ ⟶ TLDiagCat.of _))
          simp only [Functor.map_comp, linearize_map_tensorHom, ← diagBasis_eq_linearize_map] at h
          exact h
        | _ => simp_all
      | _ => simp_all
    | _ => simp_all
  | _ => simp_all

private theorem associator_naturality' {X₁ X₂ X₃ Y₁ Y₂ Y₃ : TLCat R δ} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) := by
  induction f₁ using hom_induction with
  | basis x₁ =>
    induction f₂ using hom_induction with
    | basis x₂ =>
      induction f₃ using hom_induction with
      | basis x₃ =>
        have h := congrArg (linearize R δ).map (associator_naturality
          (TLDiagCat.Hom.mk ⟨x₁, 0⟩ : TLDiagCat.of _ ⟶ TLDiagCat.of _)
          (TLDiagCat.Hom.mk ⟨x₂, 0⟩ : TLDiagCat.of _ ⟶ TLDiagCat.of _)
          (TLDiagCat.Hom.mk ⟨x₃, 0⟩ : TLDiagCat.of _ ⟶ TLDiagCat.of _))
        simp only [Functor.map_comp, linearize_map_tensorHom, ← diagBasis_eq_linearize_map,
          TLDiagCat.associator_hom, eqToHom_map] at h
        rw [associator_hom, associator_hom]
        exact h
      | _ => simp_all
    | _ => simp_all
  | _ => simp_all

private theorem leftUnitor_naturality' {X Y : TLCat R δ} (f : X ⟶ Y) :
    (𝟙 (𝟙_ (TLCat R δ)) ⊗ₘ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  induction f using hom_induction with
  | basis x =>
    have h := congrArg (linearize R δ).map (leftUnitor_naturality
      (TLDiagCat.Hom.mk ⟨x, 0⟩ : TLDiagCat.of _ ⟶ TLDiagCat.of _))
    simp only [← id_tensorHom, Functor.map_comp, linearize_map_tensorHom, (linearize R δ).map_id,
      ← diagBasis_eq_linearize_map, TLDiagCat.leftUnitor_hom, eqToHom_map] at h
    rw [leftUnitor_hom, leftUnitor_hom]
    exact h
  | _ => simp_all

private theorem rightUnitor_naturality' {X Y : TLCat R δ} (f : X ⟶ Y) :
    (f ⊗ₘ 𝟙 (𝟙_ (TLCat R δ))) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  induction f using hom_induction with
  | basis x =>
    have h := congrArg (linearize R δ).map (rightUnitor_naturality
      (TLDiagCat.Hom.mk ⟨x, 0⟩ : TLDiagCat.of _ ⟶ TLDiagCat.of _))
    simp only [← tensorHom_id, Functor.map_comp, linearize_map_tensorHom, (linearize R δ).map_id,
      ← diagBasis_eq_linearize_map, TLDiagCat.rightUnitor_hom, eqToHom_map] at h
    rw [rightUnitor_hom, rightUnitor_hom]
    exact h
  | _ => simp_all

private theorem pentagon' (W X Y Z : TLCat R δ) :
    ((α_ W X Y).hom ⊗ₘ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom ≫ (𝟙 W ⊗ₘ (α_ X Y Z).hom) =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  have h := congrArg (linearize R δ).map
    (pentagon (TLDiagCat.of W.as) (.of X.as) (.of Y.as) (.of Z.as))
  simp only [← tensorHom_id, ← id_tensorHom, Functor.map_comp, linearize_map_tensorHom,
    (linearize R δ).map_id, TLDiagCat.associator_hom, eqToHom_map] at h
  simp only [associator_hom]
  exact h

private theorem triangle' (X Y : TLCat R δ) :
    (α_ X (𝟙_ (TLCat R δ)) Y).hom ≫ (𝟙 X ⊗ₘ (λ_ Y).hom) = (ρ_ X).hom ⊗ₘ 𝟙 Y := by
  have h := congrArg (linearize R δ).map (triangle (TLDiagCat.of X.as) (.of Y.as))
  simp only [← tensorHom_id, ← id_tensorHom, Functor.map_comp, linearize_map_tensorHom,
    (linearize R δ).map_id, TLDiagCat.associator_hom, TLDiagCat.leftUnitor_hom,
    TLDiagCat.rightUnitor_hom, eqToHom_map] at h
  simp only [associator_hom, leftUnitor_hom, rightUnitor_hom]
  exact h

end Axioms

/-- **The linear Temperley–Lieb category is monoidal** under juxtaposition of diagrams. The
monoidal structure is strict: the tensor product of objects adds the numbers of points, and the
associators and unitors are transports along equalities of objects. -/
noncomputable instance instMonoidalCategory : MonoidalCategory (TLCat R δ) :=
  -- The axioms are passed through `by exact`: the body of an instance is exposed, so it cannot
  -- name the private lemmas above directly, while its proofs can.
  .ofTensorHom (by exact id_tensorHom_id') (fun _ _ _ _ => rfl) (fun _ _ => rfl)
    (by exact tensorHom_comp_tensorHom') (by exact associator_naturality')
    (by exact leftUnitor_naturality') (by exact rightUnitor_naturality') (by exact pentagon')
    (by exact triangle')

/-- The left whiskering `X ◁ diagBasis Y Z y` of a basis morphism is the basis morphism of the
matching of `y` with `X.as` straight strands on its left. -/
@[simp]
theorem whiskerLeft_diagBasis (X : TLCat R δ) (y : PlanarMatching (Y.as + Z.as)) :
    X ◁ diagBasis Y Z y =
      diagBasis (X ⊗ Y) (X ⊗ Z) ((TLDiagram.id X.as).tensor ⟨y, 0⟩).matching := by
  rw [← id_tensorHom, id_eq_diagBasis, diagBasis_tensorHom_diagBasis, TLDiagram.mk_nested_zero]

/-- The right whiskering `diagBasis X Y x ▷ Z` of a basis morphism is the basis morphism of the
matching of `x` with `Z.as` straight strands on its right. -/
@[simp]
theorem diagBasis_whiskerRight (x : PlanarMatching (X.as + Y.as)) (Z : TLCat R δ) :
    diagBasis X Y x ▷ Z =
      diagBasis (X ⊗ Z) (Y ⊗ Z) (TLDiagram.tensor ⟨x, 0⟩ (TLDiagram.id Z.as)).matching := by
  rw [← tensorHom_id, id_eq_diagBasis, diagBasis_tensorHom_diagBasis, TLDiagram.mk_nested_zero]

/-- The tensor product on `TLCat R δ` is additive in each variable. -/
instance instMonoidalPreadditive : MonoidalPreadditive (TLCat R δ) where
  whiskerLeft_zero := tensorHom_zero _
  zero_whiskerRight := zero_tensorHom _
  whiskerLeft_add _ _ := tensorHom_add _ _ _
  add_whiskerRight _ _ := add_tensorHom _ _ _

/-- The tensor product on `TLCat R δ` is `R`-bilinear. -/
instance instMonoidalLinear : MonoidalLinear R (TLCat R δ) where
  whiskerLeft_smul _ _ _ r f := tensorHom_smul r _ f
  smul_whiskerRight r _ _ f _ := smul_tensorHom r f _

/-! ### Linearization is a monoidal functor -/

/-- Linearization preserves left whiskerings. -/
@[simp]
theorem linearize_map_whiskerLeft (X : TLDiagCat) {Y Z : TLDiagCat} (f : Y ⟶ Z) :
    (linearize R δ).map (X ◁ f) = (linearize R δ).obj X ◁ (linearize R δ).map f := by
  rw [← id_tensorHom, linearize_map_tensorHom, (linearize R δ).map_id, id_tensorHom]

/-- Linearization preserves right whiskerings. -/
@[simp]
theorem linearize_map_whiskerRight {X Y : TLDiagCat} (f : X ⟶ Y) (Z : TLDiagCat) :
    (linearize R δ).map (f ▷ Z) = (linearize R δ).map f ▷ (linearize R δ).obj Z := by
  rw [← tensorHom_id, linearize_map_tensorHom, (linearize R δ).map_id, tensorHom_id]

/-- **Linearization is a strict monoidal functor**: the comparison morphisms
`(linearize R δ).obj X ⊗ (linearize R δ).obj Y ⟶ (linearize R δ).obj (X ⊗ Y)` and
`𝟙_ (TLCat R δ) ⟶ (linearize R δ).obj (𝟙_ TLDiagCat)` are identities. -/
noncomputable instance instMonoidalLinearize : (linearize R δ).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _
      μIso_hom_natural_left := fun _ _ => by simp
      μIso_hom_natural_right := fun _ _ => by simp
      associativity := fun _ _ _ => by
        simp [TLDiagCat.associator_hom, eqToHom_map, associator_hom]
      left_unitality := fun _ => by
        simp [TLDiagCat.leftUnitor_hom, eqToHom_map, leftUnitor_hom]
      right_unitality := fun _ => by
        rw [TLDiagCat.rightUnitor_hom, eqToHom_map, rightUnitor_hom]
        simp only [Iso.refl_hom, MonoidalCategory.whiskerLeft_id, Category.id_comp] }

/-- The unit comparison morphism of `linearize R δ` is the identity. -/
@[simp]
theorem linearize_ε : Functor.LaxMonoidal.ε (linearize R δ) = 𝟙 (𝟙_ (TLCat R δ)) := (rfl)

/-- The tensor comparison morphisms of `linearize R δ` are identities. -/
@[simp]
theorem linearize_μ (X Y : TLDiagCat) :
    Functor.LaxMonoidal.μ (linearize R δ) X Y =
      𝟙 ((linearize R δ).obj X ⊗ (linearize R δ).obj Y) := (rfl)

/-- The counit comparison morphism of `linearize R δ` is the identity. -/
@[simp]
theorem linearize_η : Functor.OplaxMonoidal.η (linearize R δ) = 𝟙 (𝟙_ (TLCat R δ)) := (rfl)

/-- The cotensor comparison morphisms of `linearize R δ` are identities. -/
@[simp]
theorem linearize_δ (X Y : TLDiagCat) :
    Functor.OplaxMonoidal.δ (linearize R δ) X Y =
      𝟙 ((linearize R δ).obj X ⊗ (linearize R δ).obj Y) := (rfl)

/-- Linearization sends the associator of `TLDiagCat` to the associator of `TLCat R δ`. -/
@[simp]
theorem linearize_map_associator_hom (X Y Z : TLDiagCat) :
    (linearize R δ).map (α_ X Y Z).hom =
      (α_ ((linearize R δ).obj X) ((linearize R δ).obj Y) ((linearize R δ).obj Z)).hom := by
  rw [TLDiagCat.associator_hom, eqToHom_map, associator_hom]

/-- Linearization sends the inverse associator of `TLDiagCat` to that of `TLCat R δ`. -/
@[simp]
theorem linearize_map_associator_inv (X Y Z : TLDiagCat) :
    (linearize R δ).map (α_ X Y Z).inv =
      (α_ ((linearize R δ).obj X) ((linearize R δ).obj Y) ((linearize R δ).obj Z)).inv := by
  rw [TLDiagCat.associator_inv, eqToHom_map, associator_inv]

/-! The unitor comparisons are not `@[simp]`: Mathlib's simp lemmas
`Functor.LaxMonoidal.left_unitality` and `Functor.LaxMonoidal.right_unitality` rewrite the unitor
of `(linearize R δ).obj X` back into an expression containing `(linearize R δ).map` of a unitor,
so simp would loop. -/

/-- Linearization sends the left unitor of `TLDiagCat` to the left unitor of `TLCat R δ`. -/
theorem linearize_map_leftUnitor_hom (X : TLDiagCat) :
    (linearize R δ).map (λ_ X).hom = (λ_ ((linearize R δ).obj X)).hom := by
  rw [TLDiagCat.leftUnitor_hom, eqToHom_map, leftUnitor_hom]

/-- Linearization sends the inverse left unitor of `TLDiagCat` to that of `TLCat R δ`. -/
theorem linearize_map_leftUnitor_inv (X : TLDiagCat) :
    (linearize R δ).map (λ_ X).inv = (λ_ ((linearize R δ).obj X)).inv := by
  rw [TLDiagCat.leftUnitor_inv, eqToHom_map, leftUnitor_inv]

/-- Linearization sends the right unitor of `TLDiagCat` to the right unitor of `TLCat R δ`. -/
theorem linearize_map_rightUnitor_hom (X : TLDiagCat) :
    (linearize R δ).map (ρ_ X).hom = (ρ_ ((linearize R δ).obj X)).hom := by
  rw [TLDiagCat.rightUnitor_hom, eqToHom_map, rightUnitor_hom]

/-- Linearization sends the inverse right unitor of `TLDiagCat` to that of `TLCat R δ`. -/
theorem linearize_map_rightUnitor_inv (X : TLDiagCat) :
    (linearize R δ).map (ρ_ X).inv = (ρ_ ((linearize R δ).obj X)).inv := by
  rw [TLDiagCat.rightUnitor_inv, eqToHom_map, rightUnitor_inv]

/-! ### The monoidal universal property -/

section LiftDiag

variable {D : Type*} [Category D] [Preadditive D] [CategoryTheory.Linear R D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear R D]
  (F : TLDiagCat ⥤ D) [F.Monoidal]
  (hF : ∀ {n m : ℕ} (x : PlanarMatching (n + m)) (c : ℕ),
    F.map (TLDiagCat.Hom.mk ⟨x, c + 1⟩ : .of n ⟶ .of m) =
      δ • F.map (TLDiagCat.Hom.mk ⟨x, c⟩ : .of n ⟶ .of m))

/-- **The extension of a monoidal functor is monoidal.** If `F : TLDiagCat ⥤ D` is a monoidal
functor into a monoidal `R`-linear category that evaluates each closed circle to a factor of `δ`,
then its `R`-linear extension `liftDiag F hF : TLCat R δ ⥤ D` is monoidal, with the structure
morphisms of `F`. -/
noncomputable instance instMonoidalLiftDiag : (liftDiag F hF).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Functor.Monoidal.εIso F
      μIso := fun X Y => Functor.Monoidal.μIso F (TLDiagCat.of X.as) (TLDiagCat.of Y.as)
      μIso_hom_natural_left := fun f X' => by
        induction f using hom_induction with
        | basis x =>
          have h := Functor.LaxMonoidal.μ_natural_left F
            (TLDiagCat.Hom.mk ⟨x, 0⟩ : TLDiagCat.of _ ⟶ TLDiagCat.of _) (TLDiagCat.of X'.as)
          rw [← liftDiag_map_linearize_map F hF, ← liftDiag_map_linearize_map F hF (_ ▷ _),
            linearize_map_whiskerRight, ← diagBasis_eq_linearize_map] at h
          exact h
        | _ => simp_all [Preadditive.add_comp, Preadditive.comp_add]
      μIso_hom_natural_right := fun X' f => by
        induction f using hom_induction with
        | basis x =>
          have h := Functor.LaxMonoidal.μ_natural_right F (TLDiagCat.of X'.as)
            (TLDiagCat.Hom.mk ⟨x, 0⟩ : TLDiagCat.of _ ⟶ TLDiagCat.of _)
          rw [← liftDiag_map_linearize_map F hF, ← liftDiag_map_linearize_map F hF (_ ◁ _),
            linearize_map_whiskerLeft, ← diagBasis_eq_linearize_map] at h
          exact h
        | _ => simp_all [Preadditive.add_comp, Preadditive.comp_add]
      associativity := fun X Y Z => by
        have h := Functor.LaxMonoidal.associativity F (TLDiagCat.of X.as) (TLDiagCat.of Y.as)
          (TLDiagCat.of Z.as)
        rw [← liftDiag_map_linearize_map F hF, linearize_map_associator_hom] at h
        exact h
      left_unitality := fun X => by
        have h := Functor.LaxMonoidal.left_unitality F (TLDiagCat.of X.as)
        rw [← liftDiag_map_linearize_map F hF, linearize_map_leftUnitor_hom] at h
        exact h
      right_unitality := fun X => by
        have h := Functor.LaxMonoidal.right_unitality F (TLDiagCat.of X.as)
        rw [← liftDiag_map_linearize_map F hF, linearize_map_rightUnitor_hom] at h
        exact h }

/-- The unit comparison morphism of `liftDiag F hF` is that of `F`. -/
@[simp]
theorem liftDiag_ε : Functor.LaxMonoidal.ε (liftDiag F hF) = Functor.LaxMonoidal.ε F := (rfl)

/-- The tensor comparison morphisms of `liftDiag F hF` are those of `F`. -/
@[simp]
theorem liftDiag_μ (X Y : TLCat R δ) :
    Functor.LaxMonoidal.μ (liftDiag F hF) X Y =
      Functor.LaxMonoidal.μ F (TLDiagCat.of X.as) (TLDiagCat.of Y.as) := (rfl)

/-- The identification of `linearize R δ ⋙ liftDiag F hF` with `F` is a monoidal natural
isomorphism. -/
instance : NatTrans.IsMonoidal (linearizeLiftDiagIso F hF).hom where
  unit := by
    simp only [Functor.comp_obj, Functor.LaxMonoidal.comp_ε, liftDiag_ε, linearize_ε,
      CategoryTheory.Functor.map_id, linearizeLiftDiagIso_hom_app]
    -- The object `(liftDiag F hF).obj (𝟙_ (TLCat R δ))` is `F.obj (𝟙_ TLDiagCat)` by definition,
    -- but only up to unfolding, which blocks `simp`; restate the goal over `F.obj`.
    change (Functor.LaxMonoidal.ε F ≫ 𝟙 _) ≫ 𝟙 (F.obj (𝟙_ TLDiagCat)) = _
    simp
  tensor X Y := by
    simp only [Functor.comp_obj, Functor.LaxMonoidal.comp_μ, liftDiag_μ, linearize_μ,
      CategoryTheory.Functor.map_id, linearizeLiftDiagIso_hom_app]
    -- As for `unit`, the objects coming from `(liftDiag F hF).obj ((linearize R δ).obj X)` are
    -- `F.obj X` by definition; restate the goal over `F.obj`.
    change (Functor.LaxMonoidal.μ F X Y ≫ 𝟙 (F.obj (X ⊗ Y))) ≫ 𝟙 (F.obj (X ⊗ Y)) =
      (𝟙 (F.obj X) ⊗ₘ 𝟙 (F.obj Y)) ≫ Functor.LaxMonoidal.μ F X Y
    simp

end LiftDiag

end TLCat

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.FullyFaithful
public import TauCeti.CategoryTheory.Monoidal.FSymbols.Model

/-!
# Linear reconstruction from a split simple family

The category underlying an F-symbol model is linearly equivalent to any category with the
corresponding split simple family. An object is realized as the biproduct of its basis vectors,
and a matrix entry acts by the corresponding scalar endomorphism. The entry formulas give the
linear functor's action on the summands used to build its tensor structure from fusion bases.

We use Mathlib's `biproduct.map`, `biproduct.lift`, `biproduct.desc`, `biproduct.lift_desc`, and
`biproductBiproductIso`. These give the same block decomposition as
`CategoryTheory.HomOrthogonal.matrixDecompositionLinearEquiv`, while retaining the model's native
basis types in arbitrary universes.

## References

* A. Kitaev, *Anyons in an exactly solved model and beyond*, Ann. Physics 321 (2006),
  Appendix E, §E.7.1, Definition E.17 and equation (257), for the graded model and multiplicity
  spaces. See §E.7.3, Definition E.25, for the tensor functor.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.FSymbols

universe u v w z

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {R : Type v} [CommRing R] {N : FusionRules ι} (P : FSymbols R N)
variable {C : Type w} [Category.{z} C] [Preadditive C] [Linear R C]
variable [HasFiniteBiproducts C] (S : ι → C)

namespace Reconstruction

/-- Realize a model object by one copy of `S a` for every basis vector of grade `a`.
This abbreviation retains the native basis carriers for the biproduct component API. -/
private abbrev rawObj (X : Model P) : C := ⨁ fun a ↦ ⨁ fun _ : X.basis a ↦ S a

/-- Realize a matrix morphism by its scalar entries on each grade. -/
private def map {X Y : Model P} (f : X ⟶ Y) : rawObj P S X ⟶ rawObj P S Y :=
  biproduct.map fun a ↦ biproduct.desc fun x ↦ biproduct.lift fun y ↦ f a x y • 𝟙 (S a)

@[simp]
private theorem map_id (X : Model P) : map P S (𝟙 X) = 𝟙 (rawObj P S X) := by
  ext b y a x : 4
  by_cases h : a = b
  · subst b
    by_cases hxy : x = y
    · subst y
      simp [rawObj, map, Category.assoc]
    · simp [rawObj, map, Category.assoc, hxy]
  · simp [rawObj, map, Category.assoc, h]

@[simp]
private theorem map_comp {X Y Z : Model P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map P S (f ≫ g) = map P S f ≫ map P S g := by
  ext b y a x : 4
  by_cases h : a = b
  · subst b
    simp [rawObj, map, Category.assoc, Matrix.mul_apply, biproduct.lift_desc_assoc,
      Linear.smul_comp, smul_smul, Finset.sum_smul, Preadditive.sum_comp]
  · simp [rawObj, map, Category.assoc, h]

/-- The realization functor from the F-symbol model to the category containing the family. -/
def functor : Model P ⥤ C where
  obj := rawObj P S
  map := map P S
  map_id := map_id P S
  map_comp := map_comp P S

/-- The inclusion of the copy of `S a` indexed by the basis vector `x`. -/
def incl (X : Model P) (a : ι) (x : X.basis a) : S a ⟶ (functor P S).obj X :=
  biproduct.ι (fun _ : X.basis a ↦ S a) x ≫
    biproduct.ι (fun a ↦ ⨁ fun _ : X.basis a ↦ S a) a

/-- The projection to the copy of `S a` indexed by the basis vector `x`. -/
def proj (X : Model P) (a : ι) (x : X.basis a) : (functor P S).obj X ⟶ S a :=
  biproduct.π (fun a ↦ ⨁ fun _ : X.basis a ↦ S a) a ≫
    biproduct.π (fun _ : X.basis a ↦ S a) x

/-- Maps between realized objects are determined by all their native matrix components. -/
@[ext]
theorem hom_ext {X Y : Model P}
    {f g : (functor P S).obj X ⟶ (functor P S).obj Y}
    (h : ∀ a b (x : X.basis a) (y : Y.basis b),
      incl P S X a x ≫ f ≫ proj P S Y b y =
        incl P S X a x ≫ g ≫ proj P S Y b y) : f = g := by
  -- Expose the nested biproducts in the types of the maps before applying extensionality.
  dsimp only [functor, rawObj] at f g
  apply biproduct.hom_ext (f := fun b ↦ ⨁ fun _ : Y.basis b ↦ S b)
  intro b
  apply biproduct.hom_ext (f := fun _ : Y.basis b ↦ S b)
  intro y
  apply biproduct.hom_ext' (f := fun a ↦ ⨁ fun _ : X.basis a ↦ S a)
  intro a
  apply biproduct.hom_ext' (f := fun _ : X.basis a ↦ S a)
  intro x
  -- Expose the biproduct carriers in composition instances so associativity matches.
  dsimp (config := { instances := true }) only [incl, proj, functor, rawObj] at h ⊢
  simpa only [Category.assoc] using h a b x y

private theorem hom_ext_of_entry {X Y : Model P}
    {f g : (functor P S).obj X ⟶ (functor P S).obj Y}
    (hoff : ∀ a b, a ≠ b → ∀ (x : X.basis a) (y : Y.basis b),
      incl P S X a x ≫ f ≫ proj P S Y b y =
        incl P S X a x ≫ g ≫ proj P S Y b y)
    (h : ∀ a (x : X.basis a) (y : Y.basis a),
      incl P S X a x ≫ f ≫ proj P S Y a y =
        incl P S X a x ≫ g ≫ proj P S Y a y) : f = g := by
  apply hom_ext P S
  intro a b x y
  by_cases hab : a = b
  · subst b
    exact h a x y
  · exact hoff a b hab x y

/-- The realized object is the iterated biproduct of the copies of `S a` in each grade. -/
theorem functor_obj (X : Model P) :
    (functor P S).obj X = ⨁ fun a ↦ ⨁ fun _ : X.basis a ↦ S a := (rfl)

/-- Realization sends each matrix entry to its scalar endomorphism. -/
@[reassoc (attr := simp)]
theorem functor_map_entry {X Y : Model P} (f : X ⟶ Y) (a : ι)
    (x : X.basis a) (y : Y.basis a) :
    incl P S X a x ≫ (functor P S).map f ≫ proj P S Y a y =
      f a x y • 𝟙 (S a) := by
  simp [incl, proj, functor, map, Category.assoc]

/-- Realization has zero components between distinct grades. -/
@[reassoc (attr := simp)]
theorem functor_map_entry_of_ne {X Y : Model P} (f : X ⟶ Y) {a b : ι}
    (h : a ≠ b) (x : X.basis a) (y : Y.basis b) :
    incl P S X a x ≫ (functor P S).map f ≫ proj P S Y b y = 0 := by
  simp [incl, proj, functor, map, Category.assoc, h]

/-- Inclusions and projections in a fixed grade are the coordinate Kronecker deltas. -/
@[reassoc (attr := simp)]
theorem incl_comp_proj (X : Model P) (a : ι) (x y : X.basis a) :
    incl P S X a x ≫ proj P S X a y =
      if x = y then 𝟙 (S a) else 0 := by
  have h := functor_map_entry P S (𝟙 X) a x y
  rw [(functor P S).map_id] at h
  simpa only [Category.id_comp, Model.id_apply, Matrix.one_apply,
    ite_smul, one_smul, zero_smul] using h

/-- Inclusions and projections from distinct grades have zero composite. -/
@[reassoc (attr := simp)]
theorem incl_comp_proj_of_ne (X : Model P) {a b : ι} (h : a ≠ b)
    (x : X.basis a) (y : X.basis b) :
    incl P S X a x ≫ proj P S X b y = 0 := by
  have h' := functor_map_entry_of_ne P S (𝟙 X) h x y
  rw [(functor P S).map_id] at h'
  simpa only [Category.id_comp] using h'

/-- The native basis inclusions and projections resolve the identity of a realized object. -/
@[simp]
theorem sum_proj_comp_incl (X : Model P) :
    ∑ a, ∑ x : X.basis a, proj P S X a x ≫ incl P S X a x =
      𝟙 ((functor P S).obj X) := by
  -- The additive structures in these sums depend on the realized object carriers.
  dsimp (config := { instances := true }) only [incl, proj, functor, rawObj]
  calc
    _ = ∑ a, biproduct.π (fun a ↦ ⨁ fun _ : X.basis a ↦ S a) a ≫
        (∑ x : X.basis a, biproduct.π (fun _ : X.basis a ↦ S a) x ≫
          biproduct.ι (fun _ : X.basis a ↦ S a) x) ≫
        biproduct.ι (fun a ↦ ⨁ fun _ : X.basis a ↦ S a) a := by
      simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
    _ = _ := by simp

/-- Realization acts on a basis inclusion by the corresponding row of its matrix. -/
@[reassoc]
theorem incl_comp_functor_map {X Y : Model P} (f : X ⟶ Y) (a : ι) (x : X.basis a) :
    incl P S X a x ≫ (functor P S).map f =
      ∑ y : Y.basis a, f a x y • incl P S Y a y := by
  -- The additive structures in these sums depend on the realized object carriers.
  dsimp (config := { instances := true }) only [incl, proj, functor, rawObj]
  simp [map, biproduct.lift_eq, Category.assoc, Preadditive.sum_comp,
    Linear.smul_comp]

/-- Realization acts on a basis projection by the corresponding column of its matrix. -/
@[reassoc]
theorem functor_map_comp_proj {X Y : Model P} (f : X ⟶ Y) (a : ι) (y : Y.basis a) :
    (functor P S).map f ≫ proj P S Y a y =
      ∑ x : X.basis a, f a x y • proj P S X a x := by
  -- The additive structures in these sums depend on the realized object carriers.
  dsimp (config := { instances := true }) only [incl, proj, functor, rawObj]
  simp [map, biproduct.desc_eq, Category.assoc, Preadditive.comp_sum,
    Preadditive.sum_comp, Linear.comp_smul]

instance : (functor P S).Additive where
  map_add {X Y} f g := by
    apply hom_ext_of_entry P S
    · intro a b hab x y
      simp [Preadditive.comp_add, Preadditive.add_comp, hab]
    · intro a x y
      simp [Preadditive.comp_add, Preadditive.add_comp, add_smul]

instance : (functor P S).Linear R where
  map_smul f r := by
    apply hom_ext_of_entry P S
    · intro a b hab x y
      simp [Linear.comp_smul, Linear.smul_comp, hab]
    · intro a x y
      simp [Linear.comp_smul, Linear.smul_comp, smul_smul]

/-- The realization of the model's simple object in grade `a` is `S a`. -/
def simpleIso (a : ι) : (functor P S).obj (Model.simple P a) ≅ S a where
  hom := proj P S (Model.simple P a) a default
  inv := incl P S (Model.simple P a) a default
  hom_inv_id := by
    apply hom_ext P S
    intro b c x y
    obtain rfl := Model.eq_of_simple_basis x
    obtain rfl := Model.eq_of_simple_basis y
    simp [Category.assoc, Subsingleton.elim x default, Subsingleton.elim y default]
  inv_hom_id := by
    rw [incl_comp_proj]
    exact ite_eq_left rfl

@[simp]
theorem simpleIso_hom (a : ι) :
    (simpleIso P S a).hom = proj P S (Model.simple P a) a default := (rfl)

@[simp]
theorem simpleIso_inv (a : ι) :
    (simpleIso P S a).inv = incl P S (Model.simple P a) a default := (rfl)

variable (hEnd : ∀ a, Function.Bijective (algebraMap R (End (S a))))
variable (hOrth : HomOrthogonal S)

private def coordinates (X Y : Model P) :
    ((functor P S).obj X ⟶ (functor P S).obj Y) → (X ⟶ Y) :=
  fun g a x y ↦ homPairingOfBijective (hEnd a) _ (incl P S X a x) (g ≫ proj P S Y a y)

private theorem coordinates_map {X Y : Model P} (f : X ⟶ Y) :
    coordinates P S hEnd X Y ((functor P S).map f) = f := by
  ext a x y
  apply (homPairingOfBijective_eq_iff _ _ _).2
  exact functor_map_entry P S f a x y

include hOrth in
private theorem map_coordinates {X Y : Model P} (g : (functor P S).obj X ⟶ (functor P S).obj Y) :
    (functor P S).map (coordinates P S hEnd X Y g) = g := by
  apply hom_ext_of_entry P S
  · intro a b hab x y
    rw [functor_map_entry_of_ne P S _ hab]
    exact (hOrth.eq_zero hab _).symm
  · intro a x y
    rw [functor_map_entry]
    exact homPairingOfBijective_smul_id _ _

/-- Realization is fully faithful when the family has scalar endomorphisms and is orthogonal.
The chosen preimage retains the model's native basis carriers. -/
def fullyFaithful : (functor P S).FullyFaithful :=
  { preimage := fun {X Y} g ↦ coordinates P S hEnd X Y g
    map_preimage := fun {_ _} g ↦ map_coordinates P S hEnd hOrth g
    preimage_map := fun {_ _} f ↦ coordinates_map P S hEnd f }

/-- The native matrix coordinates of a morphism between realized objects, given by the inverse of
`Functor.homLinearEquiv` on the caller's chosen basis carriers. Use `fullyFaithful` to supply
local `Full` and `Faithful` instances for the generic functor laws. -/
abbrev coordinatesLinearEquiv (X Y : Model P) :
    ((functor P S).obj X ⟶ (functor P S).obj Y) ≃ₗ[R] (X ⟶ Y) :=
  letI := (fullyFaithful P S hEnd hOrth).full
  letI := (fullyFaithful P S hEnd hOrth).faithful
  ((functor P S).homLinearEquiv R X Y).symm

/-- Evaluate a native matrix coordinate by pairing the corresponding inclusion and projection. -/
theorem coordinatesLinearEquiv_apply {X Y : Model P}
    (g : (functor P S).obj X ⟶ (functor P S).obj Y) (a : ι)
    (x : X.basis a) (y : Y.basis a) :
    coordinatesLinearEquiv P S hEnd hOrth X Y g a x y =
      homPairingOfBijective (hEnd a) _ (incl P S X a x) (g ≫ proj P S Y a y) := by
  let := (fullyFaithful P S hEnd hOrth).full
  symm
  apply (homPairingOfBijective_eq_iff _ _ _).2
  simpa only [coordinatesLinearEquiv, Functor.homLinearEquiv_symm_apply,
    Functor.map_preimage] using
    functor_map_entry P S ((functor P S).preimage g) a x y

/-- An entry of the coordinate matrix is characterized by the corresponding scalar component. -/
theorem coordinatesLinearEquiv_apply_smul_id {X Y : Model P}
    (g : (functor P S).obj X ⟶ (functor P S).obj Y) (a : ι)
    (x : X.basis a) (y : Y.basis a) :
    coordinatesLinearEquiv P S hEnd hOrth X Y g a x y • 𝟙 (S a) =
      incl P S X a x ≫ g ≫ proj P S Y a y := by
  rw [coordinatesLinearEquiv_apply]
  exact homPairingOfBijective_smul_id _ _

variable (hS : IsSplitSimpleFamily R S)

include hS in
private theorem essSurj : (functor P S).EssSurj where
  mem_essImage Y := by
    classical
    obtain ⟨κ, _, f, ⟨e⟩⟩ := hS.exists_iso_biproduct Y
    let X : Model P := ⟨fun a ↦ ULift.{u} {k : κ // f k = a}⟩
    let t : (Σ a, X.basis a) ≃ κ :=
      (Equiv.sigmaCongrRight fun _ ↦ Equiv.ulift).trans (Equiv.sigmaFiberEquiv f)
    refine ⟨X, ⟨?_ ≪≫ e.symm⟩⟩
    exact biproductBiproductIso X.basis (fun a _ ↦ S a) ≪≫
      biproduct.whiskerEquiv t (fun p ↦ eqToIso (congrArg S p.2.down.property))

/-- The `R`-linear equivalence realizing the F-symbol model in a category with a split simple
family. Its underlying functor sends each basis vector in grade `a` to a copy of `S a`. -/
def equivalence : Model P ≌ C := by
  letI := (fullyFaithful P S hS.bijective_algebraMap hS.homOrthogonal).full
  letI := (fullyFaithful P S hS.bijective_algebraMap hS.homOrthogonal).faithful
  letI := essSurj P S hS
  letI : (functor P S).IsEquivalence := {}
  exact (functor P S).asEquivalence

@[simp]
theorem equivalence_functor : (equivalence P S hS).functor = functor P S := (rfl)

instance : (equivalence P S hS).functor.Linear R := by
  rw [equivalence_functor]
  infer_instance

end Reconstruction

end TauCeti.FSymbols

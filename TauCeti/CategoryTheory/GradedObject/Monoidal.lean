/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import TauCeti.CategoryTheory.GradedObject.Bifunctor

/-!
# Exactness and reindexing for tensor products of graded objects

The tensor product of two graded objects `X` and `Y` has the coproduct of the `X i ⊗ Y j` with
`i + j = n` in degree `n` (`CategoryTheory.GradedObject.Monoidal.tensorObj`).  This file records
facts about these coproducts which are used to compare homology of tensor products of complexes.

* The map of coproducts over the fibres of a map induced by a morphism of graded objects is a
  map of colimits of discrete diagrams (`CategoryTheory.GradedObject.mapMap_eq_colimMap`).
* A family of monomorphisms induces a monomorphism on coproducts over the fibres of a map, when
  colimits of that shape preserve monomorphisms (`CategoryTheory.GradedObject.mono_mapMap`), and
  a family of epimorphisms induces an epimorphism (`CategoryTheory.GradedObject.epi_mapMap`).
  When these coproducts are exact, a family of exact sequences induces an exact sequence
  (`CategoryTheory.GradedObject.exact_mapMap`), and likewise a family of short exact sequences
  induces a short exact sequence (`CategoryTheory.GradedObject.shortExact_mapMap`).  In particular
  the tensor product of morphisms of graded objects is a monomorphism in a degree whose
  coproducts preserve monomorphisms as soon as each summand is
  (`CategoryTheory.GradedObject.Monoidal.mono_tensorHom`), for instance in a degree with finitely
  many summands, or for graded modules.  Tensoring with an identity is the map of coproducts
  induced by the whiskerings (`CategoryTheory.GradedObject.Monoidal.id_tensorHom_eq_mapMap`), so
  these facts apply to it.
* The inclusion of a summand `X i ⊗ Y j` into the tensor product is a split monomorphism in a
  category with zero morphisms (`CategoryTheory.GradedObject.Monoidal.isSplitMono_ιTensorObj`).
  It is an isomorphism when one factor vanishes outside a single degree
  (`CategoryTheory.GradedObject.Monoidal.isIso_ιTensorObj_of_isZero_right`,
  `CategoryTheory.GradedObject.Monoidal.isIso_ιTensorObj_of_isZero_left`).
* If `Y` vanishes in the degrees which are not of the form `q + 1`, for instance in degree `0` for
  graded objects indexed by `ℕ`, then the summands of `X ⊗ Y` in degree `m + 1` are those of `X`
  tensored with `Y` shifted down by one, in degree `m`
  (`CategoryTheory.GradedObject.Monoidal.tensorObjSuccIso`), and symmetrically for `X` when the
  indices commute (`CategoryTheory.GradedObject.Monoidal.succTensorObjIso`).  This identifies the
  degree shift of a connecting morphism between tensor products.
* For graded objects indexed by an additive monoid with antidiagonals, such as `ℕ`, whose tensor
  product exists in every degree (`HasTensor`) and whose summands in degree `n` have a biproduct,
  the tensor product in degree `n` is this biproduct indexed by `Finset.antidiagonal n`
  (`CategoryTheory.GradedObject.Monoidal.tensorObjIsoBiproduct`), naturally
  (`CategoryTheory.GradedObject.Monoidal.tensorHom_tensorObjIsoBiproduct_hom`); it is a special
  case of `CategoryTheory.GradedObject.mapBifunctorMapObjIsoBiproduct`.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.GradedObject

variable {I J C : Type*} [Category* C]

/-- The map of coproducts over the fibre of `p : I → J` over `j` induced by a morphism of graded
objects is the map of colimits of the corresponding discrete diagrams. -/
lemma mapMap_eq_colimMap {X Y : GradedObject I C} (φ : X ⟶ Y) (p : I → J) [X.HasMap p]
    [Y.HasMap p] (j : J) :
    mapMap φ p j = colimMap (Discrete.natTrans fun i ↦ φ i.as.val :
      Discrete.functor (X.mapObjFun p j) ⟶ Discrete.functor (Y.mapObjFun p j)) := by
  refine mapObj_ext _ _ _ _ fun i hi ↦ ?_
  rw [ι_mapMap]
  -- `ιMapObj` is the colimit inclusion `Sigma.ι` of the discrete diagram `mapObjFun`
  exact (ι_colimMap (Discrete.natTrans fun i ↦ φ i.as.val :
    Discrete.functor (X.mapObjFun p j) ⟶ Discrete.functor (Y.mapObjFun p j)) ⟨⟨i, hi⟩⟩).symm

/-- A morphism of graded objects which is a monomorphism in each degree induces a monomorphism on
the coproducts over the fibre of `p : I → J` over `j`, when colimits of that shape preserve
monomorphisms. -/
lemma mono_mapMap {X Y : GradedObject I C} (φ : X ⟶ Y) (p : I → J) [X.HasMap p]
    [Y.HasMap p] (j : J) [HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [(colim : (Discrete (p ⁻¹' {j}) ⥤ C) ⥤ C).PreservesMonomorphisms]
    [hφ : ∀ i, Mono (φ i)] : Mono (mapMap φ p j) := by
  let α : Discrete.functor (X.mapObjFun p j) ⟶ Discrete.functor (Y.mapObjFun p j) :=
    Discrete.natTrans fun i ↦ φ i.as.val
  have : ∀ i, Mono (α.app i) := fun i ↦ inferInstanceAs (Mono (φ i.as.val))
  have : Mono α := NatTrans.mono_of_mono_app _
  rw [mapMap_eq_colimMap, ← colim_map]
  exact CategoryTheory.Functor.map_mono colim α

/-- A morphism of graded objects which is an epimorphism in each degree induces an epimorphism on
the coproducts over the fibre of `p : I → J` over `j`. -/
lemma epi_mapMap {X Y : GradedObject I C} (φ : X ⟶ Y) (p : I → J) [X.HasMap p]
    [Y.HasMap p] (j : J) [∀ i, Epi (φ i)] : Epi (mapMap φ p j) where
  left_cancellation g₁ g₂ h := mapObj_ext _ _ _ _ fun i hi ↦ by
    rw [← cancel_epi (φ i), ← ι_mapMap_assoc φ p i j hi, h, ι_mapMap_assoc]

/-- A short complex of graded objects which is exact in each degree induces an exact sequence on
the coproducts over the fibre of `p : I → J` over `j`, when coproducts of that shape are exact. -/
lemma exact_mapMap [Abelian C] (S : ShortComplex (GradedObject I C)) (p : I → J)
    [S.X₁.HasMap p] [S.X₂.HasMap p] [S.X₃.HasMap p] (j : J)
    [HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasExactColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    (hS : ∀ i, (ShortComplex.mk (S.f i) (S.g i) (congr_fun S.zero i)).Exact) :
    (ShortComplex.mk (mapMap S.f p j) (mapMap S.g p j) (by
      rw [← Pi.comp_apply, ← mapMap_comp, S.zero]; ext; simp)).Exact := by
  -- the coproducts over the fibre are the colimits of the corresponding discrete diagrams, and
  -- `colim` is exact
  let T : ShortComplex (Discrete (p ⁻¹' {j}) ⥤ C) :=
    ShortComplex.mk (X₁ := Discrete.functor (S.X₁.mapObjFun p j))
      (X₂ := Discrete.functor (S.X₂.mapObjFun p j)) (X₃ := Discrete.functor (S.X₃.mapObjFun p j))
      (Discrete.natTrans fun i ↦ S.f i.as.val) (Discrete.natTrans fun i ↦ S.g i.as.val)
      (by ext i; exact congr_fun S.zero i.as.val)
  have hT : T.Exact := by
    have hP : JointlyReflectIsomorphisms fun i : Discrete (p ⁻¹' {j}) ↦ (evaluation _ C).obj i :=
      ⟨fun f h ↦ have : ∀ i, IsIso (f.app i) := h; NatIso.isIso_of_isIso_app f⟩
    rw [hP.exact_iff]
    exact fun i ↦ hS i.as.val
  exact colim.exact_mapShortComplex hT (colimit.isColimit _) (colimit.isColimit _)
    (colimit.isColimit _) (mapMap S.f p j) (mapMap S.g p j)
    (fun i ↦ ι_mapMap S.f p i.as.val j i.as.property) (fun i ↦ ι_mapMap S.g p i.as.val j
        i.as.property)

/-- A short complex of graded objects which is short exact in each degree induces a short exact
sequence on the coproducts over the fibre of `p : I → J` over `j`, when coproducts of that shape
are exact. -/
lemma shortExact_mapMap [Abelian C] (S : ShortComplex (GradedObject I C)) (p : I → J)
    [S.X₁.HasMap p] [S.X₂.HasMap p] [S.X₃.HasMap p] (j : J)
    [HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasExactColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    (hS : ∀ i, (ShortComplex.mk (S.f i) (S.g i) (congr_fun S.zero i)).ShortExact) :
    (ShortComplex.mk (mapMap S.f p j) (mapMap S.g p j) (by
      rw [← Pi.comp_apply, ← mapMap_comp, S.zero]; ext; simp)).ShortExact :=
  have (i : I) : Mono (S.f i) := (hS i).mono_f
  have (i : I) : Epi (S.g i) := (hS i).epi_g
  { exact := exact_mapMap S p j fun i ↦ (hS i).exact
    mono_f := mono_mapMap S.f p j
    epi_g := epi_mapMap S.g p j }

namespace Monoidal

/-- In a degree `n`, the tensor product of two morphisms of graded objects is a monomorphism as soon
as each of its summands `f i ⊗ g j` is, when coproducts over the pairs `i + j = n` preserve
monomorphisms; for instance when there are finitely many such pairs in a category with finite
biproducts, or in a category of modules. -/
lemma mono_tensorHom [AddMonoid I] [MonoidalCategory C] {X₁ X₂ Y₁ Y₂ : GradedObject I C}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] (n : I)
    [HasColimitsOfShape (Discrete ((fun x : I × I ↦ x.1 + x.2) ⁻¹' {n})) C]
    [(colim : (Discrete ((fun x : I × I ↦ x.1 + x.2) ⁻¹' {n}) ⥤ C) ⥤ C).PreservesMonomorphisms]
    [∀ i j, Mono (f i ⊗ₘ g j)] : Mono (tensorHom f g n) := by
  unfold tensorHom mapBifunctorMapMap
  refine mono_mapMap _ _ n (hφ := fun ⟨i, j⟩ ↦ ?_)
  -- Compute the component of the bifunctor map to identify it with the tensor product.
  rw [Pi.comp_apply]
  dsimp only [mapBifunctor, curriedTensor]
  rw [← MonoidalCategory.tensorHom_def]
  infer_instance

/-- Tensoring a morphism of graded objects with the identity of `X` is, in each degree, the map of
coproducts induced by the morphisms `X i ◁ g j`. -/
lemma id_tensorHom_eq_mapMap [AddMonoid I] [MonoidalCategory C] (X : GradedObject I C)
    {Y Y' : GradedObject I C} (g : Y ⟶ Y') [HasTensor X Y] [HasTensor X Y'] (n : I) :
    tensorHom (𝟙 X) g n =
      mapMap (((mapBifunctor (curriedTensor C) I I).obj X).map g) (fun x ↦ x.1 + x.2) n := by
  dsimp [tensorHom, mapBifunctorMapMap]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- The inclusion of the summand `X₁ i₁ ⊗ X₂ i₂` into the tensor product of graded objects in
degree `i₁ + i₂` is a split monomorphism in a category with zero morphisms, being a coprojection
into a coproduct. -/
instance isSplitMono_ιTensorObj [AddMonoid I] [MonoidalCategory C] [HasZeroMorphisms C]
    (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
    IsSplitMono (ιTensorObj X₁ X₂ i₁ i₂ i₁₂ h) := by
  unfold ιTensorObj ιMapBifunctorMapObj GradedObject.ιMapObj
  exact isSplitMono_sigma_ι _ _

/-- If `Y` vanishes outside degree `j`, the summand `X i ⊗ Y j` is all of the tensor product of
graded objects in degree `i + j`. -/
lemma isIso_ιTensorObj_of_isZero_right [AddMonoid I] [IsRightCancelAdd I] [MonoidalCategory C]
    [HasZeroMorphisms C] (X Y : GradedObject I C) [HasTensor X Y]
    [∀ i, (tensorLeft (X i)).PreservesZeroMorphisms] {j : I} (hY : ∀ j' ≠ j, IsZero (Y j'))
    (i n : I) (h : i + j = n) : IsIso (ιTensorObj X Y i j n h) := by
  classical
  refine ⟨tensorObjDesc fun i' j' h' ↦ if hj : j' = j then
      eqToHom (by subst hj; rw [add_right_cancel (h'.trans h.symm)]) else 0,
    by simp, tensorObj_ext _ _ fun i' j' h' ↦ ?_⟩
  by_cases hj : j' = j
  · subst hj
    obtain rfl : i' = i := add_right_cancel (h'.trans h.symm)
    simp
  · exact ((tensorLeft _).map_isZero (hY j' hj)).eq_of_src _ _

/-- If `X` vanishes outside degree `i`, the summand `X i ⊗ Y j` is all of the tensor product of
graded objects in degree `i + j`. -/
lemma isIso_ιTensorObj_of_isZero_left [AddMonoid I] [IsLeftCancelAdd I] [MonoidalCategory C]
    [HasZeroMorphisms C] (X Y : GradedObject I C) [HasTensor X Y]
    [∀ j, (tensorRight (Y j)).PreservesZeroMorphisms] {i : I} (hX : ∀ i' ≠ i, IsZero (X i'))
    (j n : I) (h : i + j = n) : IsIso (ιTensorObj X Y i j n h) := by
  classical
  refine ⟨tensorObjDesc fun i' j' h' ↦ if hi : i' = i then
      eqToHom (by subst hi; rw [add_left_cancel (h'.trans h.symm)]) else 0,
    by simp, tensorObj_ext _ _ fun i' j' h' ↦ ?_⟩
  by_cases hi : i' = i
  · subst hi
    obtain rfl : j' = j := add_left_cancel (h'.trans h.symm)
    simp
  · exact ((tensorRight _).map_isZero (hX i' hi)).eq_of_src _ _

section SuccRight

variable [AddRightCancelMonoid I] [One I] [HasZeroMorphisms C] [MonoidalCategory C]
  (X Y : GradedObject I C) [HasTensor X (fun q ↦ Y (q + 1))]

open Classical in
/-- The component of the inverse of `tensorObjSuccIso` on the summand `X p ⊗ Y q` of degree
`m + 1`: the inclusion of the same summand of degree `m` if `q` is of the form `q' + 1`, and zero
otherwise. -/
private def tensorObjSuccInvComponent (m p q : I) (h : p + q = m + 1) :
    X p ⊗ Y q ⟶ tensorObj X (fun q ↦ Y (q + 1)) m :=
  if hq : ∃ q', q' + 1 = q then
    eqToHom (by rw [hq.choose_spec]) ≫ ιTensorObj X (fun q ↦ Y (q + 1)) p hq.choose m
      (add_right_cancel (by rw [add_assoc, hq.choose_spec, h]))
  else 0

private lemma tensorObjSuccInvComponent_add_one (m p q : I) (h : p + (q + 1) = m + 1)
    (h' : p + q = m) :
    tensorObjSuccInvComponent X Y m p (q + 1) h = ιTensorObj X (fun q ↦ Y (q + 1)) p q m h' := by
  -- the chosen predecessor of `q + 1` is `q`, by cancellation
  have key (a : I) (ha : a + 1 = q + 1) (h₁ : X p ⊗ Y (q + 1) = X p ⊗ Y (a + 1))
      (h₂ : p + a = m) : eqToHom h₁ ≫ ιTensorObj X (fun q ↦ Y (q + 1)) p a m h₂ =
        ιTensorObj X (fun q ↦ Y (q + 1)) p q m h' := by
    obtain rfl := add_right_cancel ha
    simp
  rw [tensorObjSuccInvComponent]
  split_ifs with hq
  · exact key _ hq.choose_spec _ _
  · exact absurd ⟨q, rfl⟩ hq

variable [∀ p, (tensorLeft (X p)).PreservesZeroMorphisms]
  (hY : ∀ q, (∀ q', q' + 1 ≠ q) → IsZero (Y q)) [HasTensor X Y] (m : I)

/-- If `Y` vanishes in every degree which is not of the form `q + 1`, as for graded objects indexed
by `ℕ` with `Y 0 = 0`, then the tensor product of `X` with `Y` shifted down by one in degree `m`
is the tensor product of `X` and `Y` in degree `m + 1`: both are the coproduct of the
`X p ⊗ Y (q + 1)` with `p + q = m`. -/
def tensorObjSuccIso : tensorObj X (fun q ↦ Y (q + 1)) m ≅ tensorObj X Y (m + 1) where
  hom := tensorObjDesc fun p q h ↦ ιTensorObj X Y p (q + 1) (m + 1) (by rw [← add_assoc, h])
  inv := tensorObjDesc (tensorObjSuccInvComponent X Y m)
  hom_inv_id := by
    ext p q h
    simp [tensorObjSuccInvComponent_add_one _ _ _ _ _ _ h]
  inv_hom_id := by
    ext p q h
    by_cases hq : ∃ q', q' + 1 = q
    · obtain ⟨q, rfl⟩ := hq
      have h' : p + q = m := add_right_cancel (b := 1) (by rw [add_assoc, h])
      simp [tensorObjSuccInvComponent_add_one _ _ _ _ _ _ h']
    · exact ((tensorLeft _).map_isZero (hY q (not_exists.1 hq))).eq_of_src _ _

/-- `tensorObjSuccIso` sends the summand `X p ⊗ Y (q + 1)` of degree `m` to the same summand of
degree `m + 1`. -/
@[reassoc (attr := simp)]
lemma ι_tensorObjSuccIso_hom (p q : I) (h : p + q = m) :
    ιTensorObj X (fun q ↦ Y (q + 1)) p q m h ≫ (tensorObjSuccIso X Y hY m).hom =
      ιTensorObj X Y p (q + 1) (m + 1) (by rw [← add_assoc, h]) := by
  simp [tensorObjSuccIso]

/-- The inverse of `tensorObjSuccIso` sends the summand `X p ⊗ Y (q + 1)` of degree `m + 1` to the
same summand of degree `m`. -/
@[reassoc (attr := simp)]
lemma ι_tensorObjSuccIso_inv (p q : I) (h : p + (q + 1) = m + 1) :
    ιTensorObj X Y p (q + 1) (m + 1) h ≫ (tensorObjSuccIso X Y hY m).inv =
      ιTensorObj X (fun q ↦ Y (q + 1)) p q m
        (add_right_cancel (b := 1) (by rw [add_assoc, h])) := by
  have h' : p + q = m := add_right_cancel (b := 1) (by rw [add_assoc, h])
  simp [tensorObjSuccIso, tensorObjSuccInvComponent_add_one _ _ _ _ _ _ h']

end SuccRight

section SuccLeft

variable [AddCancelCommMonoid I] [One I] [HasZeroMorphisms C] [MonoidalCategory C]
  (X Y : GradedObject I C) [HasTensor (fun p ↦ X (p + 1)) Y]

/-- `(p + 1) + q = (p + q) + 1` in an additive commutative monoid. -/
private lemma succ_add_eq {p q m : I} (h : p + q = m) : p + 1 + q = m + 1 := by
  rw [add_right_comm, h]

/-- `p + q = m` if `(p + 1) + q = m + 1` in an additive cancellative commutative monoid. -/
private lemma add_eq_of_succ_add_eq {p q m : I} (h : p + 1 + q = m + 1) : p + q = m :=
  add_right_cancel (b := 1) (by rw [← h, add_right_comm])

open Classical in
/-- The component of the inverse of `succTensorObjIso` on the summand `X p ⊗ Y q` of degree
`m + 1`: the inclusion of the same summand of degree `m` if `p` is of the form `p' + 1`, and zero
otherwise. -/
private def succTensorObjInvComponent (m p q : I) (h : p + q = m + 1) :
    X p ⊗ Y q ⟶ tensorObj (fun p ↦ X (p + 1)) Y m :=
  if hp : ∃ p', p' + 1 = p then
    eqToHom (by rw [hp.choose_spec]) ≫ ιTensorObj (fun p ↦ X (p + 1)) Y hp.choose q m
      (add_eq_of_succ_add_eq (by rw [hp.choose_spec, h]))
  else 0

private lemma succTensorObjInvComponent_add_one (m p q : I) (h : p + 1 + q = m + 1)
    (h' : p + q = m) :
    succTensorObjInvComponent X Y m (p + 1) q h = ιTensorObj (fun p ↦ X (p + 1)) Y p q m h' := by
  -- the chosen predecessor of `p + 1` is `p`, by cancellation
  have key (a : I) (ha : a + 1 = p + 1) (h₁ : X (p + 1) ⊗ Y q = X (a + 1) ⊗ Y q)
      (h₂ : a + q = m) : eqToHom h₁ ≫ ιTensorObj (fun p ↦ X (p + 1)) Y a q m h₂ =
        ιTensorObj (fun p ↦ X (p + 1)) Y p q m h' := by
    obtain rfl := add_right_cancel ha
    simp
  rw [succTensorObjInvComponent]
  split_ifs with hp
  · exact key _ hp.choose_spec _ _
  · exact absurd ⟨p, rfl⟩ hp

variable [∀ q, (tensorRight (Y q)).PreservesZeroMorphisms]
  (hX : ∀ p, (∀ p', p' + 1 ≠ p) → IsZero (X p)) [HasTensor X Y] (m : I)

/-- If `X` vanishes in every degree which is not of the form `p + 1`, as for graded objects indexed
by `ℕ` with `X 0 = 0`, then the tensor product of `X` shifted down by one with `Y` in degree `m` is
the tensor product of `X` and `Y` in degree `m + 1`: both are the coproduct of the
`X (p + 1) ⊗ Y q` with `p + q = m`.  This is the counterpart of `tensorObjSuccIso` for the first
factor. -/
def succTensorObjIso : tensorObj (fun p ↦ X (p + 1)) Y m ≅ tensorObj X Y (m + 1) where
  hom := tensorObjDesc fun p q h ↦ ιTensorObj X Y (p + 1) q (m + 1) (succ_add_eq h)
  inv := tensorObjDesc (succTensorObjInvComponent X Y m)
  hom_inv_id := by
    ext p q h
    simp [succTensorObjInvComponent_add_one _ _ _ _ _ _ h]
  inv_hom_id := by
    ext p q h
    by_cases hp : ∃ p', p' + 1 = p
    · obtain ⟨p, rfl⟩ := hp
      simp [succTensorObjInvComponent_add_one _ _ _ _ _ _ (add_eq_of_succ_add_eq h)]
    · exact ((tensorRight _).map_isZero (hX p (not_exists.1 hp))).eq_of_src _ _

/-- `succTensorObjIso` sends the summand `X (p + 1) ⊗ Y q` of degree `m` to the same summand of
degree `m + 1`. -/
@[reassoc (attr := simp)]
lemma ι_succTensorObjIso_hom (p q : I) (h : p + q = m) :
    ιTensorObj (fun p ↦ X (p + 1)) Y p q m h ≫ (succTensorObjIso X Y hX m).hom =
      ιTensorObj X Y (p + 1) q (m + 1) (by rw [add_right_comm, h]) := by
  simp [succTensorObjIso]

/-- The inverse of `succTensorObjIso` sends the summand `X (p + 1) ⊗ Y q` of degree `m + 1` to the
same summand of degree `m`. -/
@[reassoc (attr := simp)]
lemma ι_succTensorObjIso_inv (p q : I) (h : p + 1 + q = m + 1) :
    ιTensorObj X Y (p + 1) q (m + 1) h ≫ (succTensorObjIso X Y hX m).inv =
      ιTensorObj (fun p ↦ X (p + 1)) Y p q m
        (add_right_cancel (b := 1) (by rw [← h, add_right_comm])) := by
  simp [succTensorObjIso, succTensorObjInvComponent_add_one _ _ _ _ _ _ (add_eq_of_succ_add_eq h)]

end SuccLeft

end Monoidal

namespace Monoidal

section Antidiagonal

variable {I : Type*} [AddMonoid I] [Finset.HasAntidiagonal I] [MonoidalCategory C]
  [HasZeroMorphisms C] (X Y : GradedObject I C) [HasTensor X Y] (n : I)
  [HasBiproduct fun x : Finset.antidiagonal n ↦ X x.val.1 ⊗ Y x.val.2]

-- The summands `X i ⊗ Y j` are by definition those of `curriedTensor C`.
private instance : HasBiproduct fun x : Finset.antidiagonal n ↦
    ((curriedTensor C).obj (X x.val.1)).obj (Y x.val.2) :=
  ‹HasBiproduct fun x : Finset.antidiagonal n ↦ X x.val.1 ⊗ Y x.val.2›

/-- For graded objects indexed by an additive monoid with antidiagonals, such as `ℕ`, whose tensor
product exists in every degree (`HasTensor X Y`), the tensor product in degree `n` is the biproduct
of the `X i ⊗ Y j` indexed by `Finset.antidiagonal n`, assuming this biproduct exists. -/
noncomputable def tensorObjIsoBiproduct :
    tensorObj X Y n ≅ ⨁ fun x : Finset.antidiagonal n ↦ X x.val.1 ⊗ Y x.val.2 :=
  mapBifunctorMapObjIsoBiproduct X Y (curriedTensor C) n

/-- `tensorObjIsoBiproduct` sends the summand `X i ⊗ Y j` to the corresponding summand of the
biproduct. -/
@[reassoc (attr := simp)]
lemma ι_tensorObjIsoBiproduct_hom (i j : I) (h : i + j = n) :
    ιTensorObj X Y i j n h ≫ (tensorObjIsoBiproduct X Y n).hom =
      biproduct.ι (fun x : Finset.antidiagonal n ↦ X x.val.1 ⊗ Y x.val.2)
        ⟨(i, j), Finset.mem_antidiagonal.2 h⟩ :=
  ι_mapBifunctorMapObjIsoBiproduct_hom X Y (curriedTensor C) n i j h

/-- The inverse of `tensorObjIsoBiproduct` sends each summand of the biproduct to the
corresponding summand of the tensor product. -/
@[reassoc (attr := simp)]
lemma ι_tensorObjIsoBiproduct_inv (x : Finset.antidiagonal n) :
    biproduct.ι (fun x : Finset.antidiagonal n ↦ X x.val.1 ⊗ Y x.val.2) x ≫
        (tensorObjIsoBiproduct X Y n).inv =
      ιTensorObj X Y x.val.1 x.val.2 n (Finset.mem_antidiagonal.1 x.property) :=
  ι_mapBifunctorMapObjIsoBiproduct_inv X Y (curriedTensor C) n x

variable {X Y} {X' Y' : GradedObject I C} [HasTensor X' Y']
  [HasBiproduct fun x : Finset.antidiagonal n ↦ X' x.val.1 ⊗ Y' x.val.2]

/-- **Naturality of `tensorObjIsoBiproduct`**: under these identifications, the tensor product of
morphisms `f` and `g` of graded objects is the map of biproducts given by the `f i ⊗ g j`. -/
@[reassoc]
lemma tensorHom_tensorObjIsoBiproduct_hom (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom f g n ≫ (tensorObjIsoBiproduct X' Y' n).hom =
      (tensorObjIsoBiproduct X Y n).hom ≫ biproduct.map fun x ↦ f x.val.1 ⊗ₘ g x.val.2 := by
  simp only [MonoidalCategory.tensorHom_def]
  -- `tensorHom` and `tensorObjIsoBiproduct` are by definition `mapBifunctorMapMap` and
  -- `mapBifunctorMapObjIsoBiproduct` of `curriedTensor C`
  exact mapBifunctorMapMap_mapBifunctorMapObjIsoBiproduct_hom (F := curriedTensor C) n f g

end Antidiagonal

end Monoidal

end CategoryTheory.GradedObject

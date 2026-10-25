/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.GradedObject
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Basic
public import TauCeti.CategoryTheory.Limits.Shapes.Products

/-!
# Compression of bounded complexes to periodic complexes

The `n`-periodic compression `Δₙ` folds an integer-indexed cochain complex `K` into a
`ZMod n`-indexed one:
`(Δₙ K)^r = ⨁_{i ≡ r mod n} K^i`, with differential induced by the differentials of `K`.
No signs are introduced. The coproduct over a residue class is Mathlib's
`CategoryTheory.GradedObject.mapObj` along the reduction `ℤ → ZMod n`, so the construction
`TauCeti.PeriodicComplex.compression` applies to every complex with these coproducts
(`TauCeti.PeriodicComplex.HasCompression`). A bounded complex has them in any category with zero
morphisms and finite coproducts, since only finitely many of its terms are nonzero.
The summand inclusions `TauCeti.PeriodicComplex.ιCompression` and the summand projections
`TauCeti.PeriodicComplex.πCompression` intertwine the differentials of `K` and of its compression.

Compression is functorial, additive, and carries homotopies to homotopies. Consequently the
compression functor on bounded complexes, `TauCeti.PeriodicComplex.compressionFunctor`, descends
to `TauCeti.PeriodicComplex.homotopyCompressionFunctor` from the bounded homotopy category to the
`n`-periodic homotopy category. For `n = 0`, when `ZMod 0` is integer indexing, every residue
class is a single degree.

The construction follows Mathlib's total complex of a bicomplex
(`Mathlib.Algebra.Homology.TotalComplex`), which also assembles a complex from coproducts
`GradedObject.mapObj` with differentials defined summand by summand.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3.
-/

public section

open CategoryTheory Limits

universe v u

namespace TauCeti

namespace PeriodicComplex

variable {C : Type u} [Category.{v} C]

section HasZeroMorphisms

variable [HasZeroMorphisms C] (n : ℕ)

/-- A cochain complex has an `n`-periodic compression when, for every residue class modulo `n`,
its terms in the degrees of that class have a coproduct. -/
abbrev HasCompression (K : CochainComplex C ℤ) : Prop :=
  GradedObject.HasMap K.X (fun i : ℤ ↦ (i : ZMod n))

variable (K L M : CochainComplex C ℤ) [HasCompression n K] [HasCompression n L]
  [HasCompression n M]

/-- The differential of the compression: on the summand of degree `i`, the differential of `K`
followed by the inclusion of the summand of degree `i + 1`, or zero if that summand does not
lie in the target. -/
private noncomputable def compressionDifferential (r s : ZMod n) :
    GradedObject.mapObj K.X (fun i : ℤ ↦ (i : ZMod n)) r ⟶
      GradedObject.mapObj K.X (fun i : ℤ ↦ (i : ZMod n)) s :=
  GradedObject.descMapObj _ _ fun i _ ↦
    K.d i (i + 1) ≫ GradedObject.ιMapObjOrZero K.X _ (i + 1) s

/-- The `n`-periodic compression of an integer-indexed cochain complex: its term of residue `r`
is the coproduct of the terms of `K` in the degrees congruent to `r` modulo `n`, and its
differential is induced by the differentials of `K`. -/
-- Implicitly reducible so that its terms unfold to the coproducts `GradedObject.mapObj` when
-- morphisms built on those coproducts are composed with its differentials.
@[implicit_reducible]
noncomputable def compression : HomologicalComplex C (ComplexShape.up (ZMod n)) where
  X := GradedObject.mapObj K.X (fun i : ℤ ↦ (i : ZMod n))
  d := compressionDifferential n K
  shape r s hrs := by
    ext i hi
    rw [compressionDifferential, GradedObject.ι_descMapObj, comp_zero,
      GradedObject.ιMapObjOrZero_eq_zero _ _ _ _ fun h ↦ hrs ?_, comp_zero]
    simp only [ComplexShape.up_Rel, ← hi, ← h, Int.cast_add, Int.cast_one]
  d_comp_d' r s t _ _ := by
    ext i hi
    by_cases hs : ((i + 1 : ℤ) : ZMod n) = s
    · simp [compressionDifferential, GradedObject.ιMapObjOrZero_eq _ _ _ _ hs]
    · simp [compressionDifferential, GradedObject.ιMapObjOrZero_eq_zero _ _ _ _ hs]

/-- The inclusion of the term of degree `i` into the term of its residue in the compression. -/
noncomputable def ιCompression (i : ℤ) (r : ZMod n) (hi : (i : ZMod n) = r) :
    K.X i ⟶ (compression n K).X r :=
  GradedObject.ιMapObj K.X _ i r hi

/-- A family of morphisms out of the terms in one residue class induces a morphism out of the
corresponding term of the compression. -/
noncomputable def compressionDesc {r : ZMod n} {A : C}
    (f : ∀ (i : ℤ) (_ : (i : ZMod n) = r), K.X i ⟶ A) :
    (compression n K).X r ⟶ A :=
  GradedObject.descMapObj K.X _ f

/-- The morphism induced by `compressionDesc` restricts to the prescribed morphism on each
summand. -/
@[reassoc (attr := simp)]
lemma ιCompression_compressionDesc {r : ZMod n} {A : C}
    (f : ∀ (i : ℤ) (_ : (i : ZMod n) = r), K.X i ⟶ A) (i : ℤ)
    (hi : (i : ZMod n) = r) :
    ιCompression n K i r hi ≫ compressionDesc n K f = f i hi :=
  GradedObject.ι_descMapObj K.X _ f i hi

variable {n K} in
/-- Morphisms out of a term of the compression agree when they agree on every summand. -/
@[ext]
lemma compression_hom_ext {r : ZMod n} {A : C} {f g : (compression n K).X r ⟶ A}
    (h : ∀ (i : ℤ) (hi : (i : ZMod n) = r), ιCompression n K i r hi ≫ f =
      ιCompression n K i r hi ≫ g) : f = g :=
  GradedObject.mapObj_ext _ _ _ _ h

/-- On the summand of degree `i`, the differential of the compression is the differential of
`K` into degree `i + 1`. -/
@[reassoc]
lemma ιCompression_d (i j : ℤ) (hij : i + 1 = j) (r s : ZMod n) (hi : (i : ZMod n) = r)
    (hj : (j : ZMod n) = s) :
    ιCompression n K i r hi ≫ (compression n K).d r s = K.d i j ≫ ιCompression n K j s hj := by
  subst hij
  simp [compression, ιCompression, compressionDifferential,
    GradedObject.ιMapObjOrZero_eq _ _ _ _ hj]

variable {K} in
/-- Identifying two equal integer degrees before including them into the compression does not
change the inclusion. -/
@[reassoc (attr := simp)]
lemma XIsoOfEq_hom_comp_ιCompression {i j : ℤ} (hij : i = j) (r : ZMod n)
    (hj : (j : ZMod n) = r) :
    (K.XIsoOfEq hij).hom ≫ ιCompression n K j r hj = ιCompression n K i r (hij ▸ hj) := by
  subst hij
  simp

/-- Composing the inclusion of a summand with the identification of two equal residue degrees of
the compression gives the inclusion into the other degree. -/
@[reassoc (attr := simp)]
lemma ιCompression_XIsoOfEq_hom (i : ℤ) {r s : ZMod n} (h : r = s) (hi : (i : ZMod n) = r) :
    ιCompression n K i r hi ≫ ((compression n K).XIsoOfEq h).hom =
      ιCompression n K i s (hi.trans h) := by
  subst h
  simp

/-- The projection of the term of residue `r` of the compression onto the term of degree `j`
of `K`; it is zero when `j` does not lie in the residue class `r`. -/
noncomputable def πCompression (r : ZMod n) (j : ℤ) :
    (compression n K).X r ⟶ K.X j :=
  compressionDesc n K fun i _ ↦ if h : i = j then eqToHom (congrArg K.X h) else 0

/-- The inclusion of the term of degree `j` of `K` into the term of residue `r` of the
compression; it is zero when `j` does not lie in the residue class `r`. -/
noncomputable def ιCompressionOrZero (j : ℤ) (r : ZMod n) :
    K.X j ⟶ (compression n K).X r :=
  GradedObject.ιMapObjOrZero K.X _ j r

/-- On a degree in the residue class `r`, `ιCompressionOrZero` is the summand inclusion. -/
@[simp]
lemma ιCompressionOrZero_eq (j : ℤ) (r : ZMod n) (h : (j : ZMod n) = r) :
    ιCompressionOrZero n K j r = ιCompression n K j r h :=
  GradedObject.ιMapObjOrZero_eq _ _ _ _ h

/-- On a degree outside the residue class `r`, `ιCompressionOrZero` is zero. -/
@[simp]
lemma ιCompressionOrZero_eq_zero (j : ℤ) (r : ZMod n) (h : (j : ZMod n) ≠ r) :
    ιCompressionOrZero n K j r = 0 :=
  GradedObject.ιMapObjOrZero_eq_zero _ _ _ _ h

/-- The projection onto the summand of degree `j` restricts to the identity on that summand and to
zero on the other summands. -/
@[reassoc (attr := simp)]
lemma ιCompression_πCompression (i : ℤ) (r : ZMod n) (hi : (i : ZMod n) = r) (j : ℤ) :
    ιCompression n K i r hi ≫ πCompression n K r j =
      if h : i = j then eqToHom (congrArg K.X h) else 0 :=
  ιCompression_compressionDesc n K _ i hi

/-- On a degree outside the residue class `r`, `πCompression` is zero. -/
@[simp]
lemma πCompression_eq_zero (r : ZMod n) (j : ℤ) (h : (j : ZMod n) ≠ r) :
    πCompression n K r j = 0 := by
  ext i hi
  have hij : i ≠ j := by
    rintro rfl
    exact h hi
  simp [hij]

/-- The term of degree `j` of `K` is a retract of the term of its residue in the compression. -/
@[reassoc]
lemma ιCompressionOrZero_πCompression (j : ℤ) (r : ZMod n) (hj : (j : ZMod n) = r) :
    ιCompressionOrZero n K j r ≫ πCompression n K r j = 𝟙 _ := by
  simp [ιCompressionOrZero_eq n K j r hj]

/-- The projections onto the summands of degrees `i` and `j = i + 1` intertwine the differentials
of the compression and of `K`. -/
@[reassoc]
lemma d_πCompression (r s : ZMod n) (hrs : r + 1 = s) (i j : ℤ) (hij : i + 1 = j) :
    (compression n K).d r s ≫ πCompression n K s j =
      πCompression n K r i ≫ K.d i j := by
  ext k hk
  have hk' : ((k + 1 : ℤ) : ZMod n) = s := by push_cast; rw [hk, hrs]
  rw [ιCompression_d_assoc n K k (k + 1) rfl r s hk hk',
    ιCompression_πCompression, ιCompression_πCompression_assoc]
  by_cases hki : k = i
  · subst hki hij
    simp
  · have hkj : k + 1 ≠ j := by omega
    simp [hki, hkj]

/-- The inclusions of the summands of degrees `i` and `j = i + 1` intertwine the differentials
of `K` and of the compression. -/
@[reassoc]
lemma ιCompressionOrZero_d (r s : ZMod n) (hrs : r + 1 = s) (i j : ℤ) (hij : i + 1 = j) :
    ιCompressionOrZero n K i r ≫ (compression n K).d r s =
      K.d i j ≫ ιCompressionOrZero n K j s := by
  by_cases hi : (i : ZMod n) = r
  · have hj : (j : ZMod n) = s := by rw [← hij, ← hrs, ← hi, Int.cast_add, Int.cast_one]
    rw [ιCompressionOrZero_eq n K i r hi, ιCompressionOrZero_eq n K j s hj]
    exact ιCompression_d n K i j hij r s hi hj
  · have hj : (j : ZMod n) ≠ s := fun hj ↦ hi (by
      rw [← hij, ← hrs] at hj
      push_cast at hj
      exact add_right_cancel hj)
    rw [ιCompressionOrZero_eq_zero n K i r hi, ιCompressionOrZero_eq_zero n K j s hj, zero_comp,
      comp_zero]

variable {K L M}

/-- The morphism of compressions induced by a morphism of cochain complexes. -/
noncomputable def compressionMap (f : K ⟶ L) : compression n K ⟶ compression n L where
  f := GradedObject.mapMap (X := K.X) (Y := L.X) f.f _
  comm' r s _ := by
    dsimp only [compression]
    ext i hi
    simp [compressionDifferential]

/-- A morphism of compressions acts on the summand of degree `i` by the component of the
original morphism. -/
@[reassoc (attr := simp)]
lemma ιCompression_compressionMap_f (f : K ⟶ L) (i : ℤ) (r : ZMod n) (hi : (i : ZMod n) = r) :
    ιCompression n K i r hi ≫ (compressionMap n f).f r = f.f i ≫ ιCompression n L i r hi :=
  GradedObject.ι_mapMap _ _ _ _ _

variable (K) in
@[simp]
lemma compressionMap_id : compressionMap n (𝟙 K) = 𝟙 _ := by
  ext r i hi
  simp

@[reassoc, simp]
lemma compressionMap_comp (f : K ⟶ L) (g : L ⟶ M) :
    compressionMap n (f ≫ g) = compressionMap n f ≫ compressionMap n g := by
  ext r i hi
  simp

variable (K L) in
@[simp]
lemma compressionMap_zero : compressionMap n (0 : K ⟶ L) = 0 := by
  ext r i hi
  simp

/-- An isomorphism of complexes induces an isomorphism of their compressions. -/
noncomputable def compressionMapIso (e : K ≅ L) : compression n K ≅ compression n L where
  hom := compressionMap n e.hom
  inv := compressionMap n e.inv
  hom_inv_id := by rw [← compressionMap_comp, e.hom_inv_id, compressionMap_id]
  inv_hom_id := by rw [← compressionMap_comp, e.inv_hom_id, compressionMap_id]

/-- The forward map of the compressed isomorphism is the compression of the forward map. -/
@[simp]
lemma compressionMapIso_hom (e : K ≅ L) :
    (compressionMapIso n e).hom = compressionMap n e.hom :=
  (rfl)

/-- The inverse map of the compressed isomorphism is the compression of the inverse map. -/
@[simp]
lemma compressionMapIso_inv (e : K ≅ L) :
    (compressionMapIso n e).inv = compressionMap n e.inv :=
  (rfl)

end HasZeroMorphisms

section Preadditive

variable [Preadditive C] (n : ℕ) {K L : CochainComplex C ℤ} [HasCompression n K]
  [HasCompression n L]

@[simp]
lemma compressionMap_add (f g : K ⟶ L) :
    compressionMap n (f + g) = compressionMap n f + compressionMap n g := by
  ext r i hi
  simp [Preadditive.comp_add, Preadditive.add_comp]

variable (K) in
/-- If every nonzero term of `K` in the residue class `r` has degree in `T`, the identity of the
term of residue `r` of the compression is the sum over `T` of the composites of the projections
and inclusions. -/
lemma sum_πCompression_ιCompressionOrZero (r : ZMod n) (T : Finset ℤ)
    (hT : ∀ i : ℤ, (i : ZMod n) = r → i ∉ T → IsZero (K.X i)) :
    ∑ j ∈ T, πCompression n K r j ≫ ιCompressionOrZero n K j r = 𝟙 _ := by
  ext i hi
  rw [Preadditive.comp_sum, Category.comp_id]
  by_cases hiT : i ∈ T
  · rw [Finset.sum_eq_single i (fun j _ hji ↦ by
        simp [ιCompression_πCompression_assoc, Ne.symm hji])
      (fun h ↦ absurd hiT h), ιCompression_πCompression_assoc, ιCompressionOrZero_eq n K i r hi]
    simp
  · exact (hT i hi hiT).eq_of_src _ _

variable {f g : K ⟶ L}

/-- The components of the compressed homotopy: on the summand of degree `i`, the homotopy into
degree `i - 1`, or zero if that summand does not lie in the target. -/
private noncomputable def compressionHomotopyHom (h : Homotopy f g) (r s : ZMod n) :
    (compression n K).X r ⟶ (compression n L).X s :=
  GradedObject.descMapObj _ _ fun i _ ↦
    h.hom i (i - 1) ≫ GradedObject.ιMapObjOrZero L.X _ (i - 1) s

@[reassoc]
private lemma ιCompression_compressionHomotopyHom (h : Homotopy f g) (i j : ℤ) (hij : j + 1 = i)
    (r s : ZMod n) (hi : (i : ZMod n) = r) (hj : (j : ZMod n) = s) :
    ιCompression n K i r hi ≫ compressionHomotopyHom n h r s =
      h.hom i j ≫ ιCompression n L j s hj := by
  obtain rfl : j = i - 1 := by omega
  simp [compression, compressionHomotopyHom, ιCompression,
    GradedObject.ιMapObjOrZero_eq _ _ _ _ hj]

/-- A homotopy between morphisms of cochain complexes induces a homotopy between the morphisms of
their compressions. -/
noncomputable def compressionHomotopy (h : Homotopy f g) :
    Homotopy (compressionMap n f) (compressionMap n g) where
  hom := compressionHomotopyHom n h
  zero r s hrs := by
    ext i hi
    have hs : ((i - 1 : ℤ) : ZMod n) ≠ s := fun hs ↦ hrs (by simp [← hi, ← hs])
    simp [compression, compressionHomotopyHom, ιCompression,
      GradedObject.ιMapObjOrZero_eq_zero _ _ _ _ hs]
  comm r := by
    have hr₁ : (ComplexShape.up (ZMod n)).Rel r (r + 1) := by rw [ComplexShape.up_Rel]
    have hr₀ : (ComplexShape.up (ZMod n)).Rel (r - 1) r := by
      rw [ComplexShape.up_Rel, sub_add_cancel]
    rw [dNext_eq _ hr₁, prevD_eq _ hr₀]
    ext i hi
    have hi₁ : ((i + 1 : ℤ) : ZMod n) = r + 1 := by simp [← hi]
    have hi₀ : ((i - 1 : ℤ) : ZMod n) = r - 1 := by simp [← hi]
    simp only [Preadditive.comp_add, ιCompression_compressionMap_f,
      ιCompression_d_assoc n K i (i + 1) rfl r (r + 1) hi hi₁,
      ιCompression_compressionHomotopyHom n h (i + 1) i rfl (r + 1) r hi₁ hi,
      ιCompression_compressionHomotopyHom_assoc n h i (i - 1) (sub_add_cancel i 1) r (r - 1) hi hi₀,
      ιCompression_d n L (i - 1) i (sub_add_cancel i 1) (r - 1) r hi₀ hi]
    have hi₂ : (ComplexShape.up ℤ).Rel i (i + 1) := by rw [ComplexShape.up_Rel]
    have hi₃ : (ComplexShape.up ℤ).Rel (i - 1) i := by rw [ComplexShape.up_Rel, sub_add_cancel]
    rw [h.comm i, dNext_eq _ hi₂, prevD_eq _ hi₃]
    simp only [Preadditive.add_comp, Category.assoc]

/-- On the summand of degree `i`, the compressed homotopy is the homotopy into degree `i - 1`. -/
@[reassoc]
lemma ιCompression_compressionHomotopy_hom (h : Homotopy f g) (i j : ℤ) (hij : j + 1 = i)
    (r s : ZMod n) (hi : (i : ZMod n) = r) (hj : (j : ZMod n) = s) :
    ιCompression n K i r hi ≫ (compressionHomotopy n h).hom r s =
      h.hom i j ≫ ιCompression n L j s hj :=
  ιCompression_compressionHomotopyHom n h i j hij r s hi hj

/-- Compressions of morphisms that agree in the homotopy category agree in the periodic homotopy
category. -/
lemma quotient_map_compressionMap_eq {f g : K ⟶ L}
    (h : (HomotopyCategory.quotient C _).map f = (HomotopyCategory.quotient C _).map g) :
    (HomotopyCategory.quotient C _).map (compressionMap n f) =
      (HomotopyCategory.quotient C _).map (compressionMap n g) :=
  HomotopyCategory.eq_of_homotopy _ _ (compressionHomotopy n (HomotopyCategory.homotopyOfEq _ _ h))

end Preadditive

section Bounded

variable [HasZeroMorphisms C] [HasFiniteCoproducts C] (n : ℕ)

/-- A bounded cochain complex has an `n`-periodic compression: each residue class meets its
support in finitely many degrees. -/
lemma hasCompression_of_bounded {K : CochainComplex C ℤ} (hK : CochainComplex.bounded C K) :
    HasCompression n K := fun r ↦ by
  obtain ⟨s, hs⟩ := (CochainComplex.bounded_iff_exists_finset_isZero_X C K).1 hK
  refine hasCoproduct_of_finite_setOf_not_isZero _
    ((s.finite_toSet.preimage Subtype.val_injective.injOn).subset fun i hi ↦ ?_)
  by_contra h
  exact hi (hs i h)

instance (K : CochainComplex.Bounded C) : HasCompression n K.obj :=
  hasCompression_of_bounded n K.property

/-- The `n`-periodic compression of bounded cochain complexes. -/
noncomputable def compressionFunctor :
    CochainComplex.Bounded C ⥤ HomologicalComplex C (ComplexShape.up (ZMod n)) where
  obj K := compression n K.obj
  map f := compressionMap n f.hom

/-- The compression functor sends a bounded complex to the compression of its underlying
complex. -/
@[simp]
lemma compressionFunctor_obj (K : CochainComplex.Bounded C) :
    (compressionFunctor n).obj K = compression n K.obj :=
  (rfl)

/-- The compression functor acts on a morphism by compressing the underlying chain map, after
transporting along the object equations. -/
@[simp]
lemma compressionFunctor_map {K L : CochainComplex.Bounded C} (f : K ⟶ L) :
    (compressionFunctor n).map f =
      eqToHom (compressionFunctor_obj n K) ≫ compressionMap n f.hom ≫
        eqToHom (compressionFunctor_obj n L).symm := by
  -- Unfold the map field and identify the transports along its definitional object equations
  -- with identities. Simplification alone cannot eliminate the opaque equality proofs.
  change compressionMap n f.hom = 𝟙 _ ≫ compressionMap n f.hom ≫ 𝟙 _
  simp

end Bounded

instance [Preadditive C] [HasFiniteCoproducts C] (n : ℕ) :
    (compressionFunctor (C := C) n).Additive where
  map_add {_ _ f g} := compressionMap_add n f.hom g.hom

section Homotopy

variable [Preadditive C] (n : ℕ)

/-- The compression of a morphism in the homotopy category, computed through any representing
chain map; see `quotientCompressionMap_eq`. -/
noncomputable def quotientCompressionMap {K L : CochainComplex C ℤ} [HasCompression n K]
    [HasCompression n L]
    (φ : (HomotopyCategory.quotient C _).obj K ⟶ (HomotopyCategory.quotient C _).obj L) :
    (HomotopyCategory.quotient C _).obj (compression n K) ⟶
      (HomotopyCategory.quotient C _).obj (compression n L) :=
  (HomotopyCategory.quotient C _).map
    (compressionMap n ((HomotopyCategory.quotient C _).preimage φ))

variable {K L M : CochainComplex C ℤ} [HasCompression n K] [HasCompression n L]
  [HasCompression n M]

/-- The compression of the class of a chain map is the class of its compression. -/
lemma quotientCompressionMap_eq (g : K ⟶ L)
    (φ : (HomotopyCategory.quotient C _).obj K ⟶ (HomotopyCategory.quotient C _).obj L)
    (hg : (HomotopyCategory.quotient C _).map g = φ) :
    quotientCompressionMap n φ = (HomotopyCategory.quotient C _).map (compressionMap n g) :=
  quotient_map_compressionMap_eq n (by simp [hg])

@[reassoc]
lemma quotientCompressionMap_comp
    (φ : (HomotopyCategory.quotient C _).obj K ⟶ (HomotopyCategory.quotient C _).obj L)
    (ψ : (HomotopyCategory.quotient C _).obj L ⟶ (HomotopyCategory.quotient C _).obj M) :
    quotientCompressionMap n (φ ≫ ψ) =
      quotientCompressionMap n φ ≫ quotientCompressionMap n ψ := by
  rw [quotientCompressionMap_eq n ((HomotopyCategory.quotient C _).preimage φ ≫
    (HomotopyCategory.quotient C _).preimage ψ) _ (by simp), compressionMap_comp,
    CategoryTheory.Functor.map_comp]
  rfl

variable (K) in
@[simp]
lemma quotientCompressionMap_id :
    quotientCompressionMap n (𝟙 ((HomotopyCategory.quotient C _).obj K)) = 𝟙 _ := by
  rw [quotientCompressionMap_eq n (𝟙 K) _ (by simp), compressionMap_id]
  exact CategoryTheory.Functor.map_id _ _

lemma quotientCompressionMap_add
    (φ ψ : (HomotopyCategory.quotient C _).obj K ⟶ (HomotopyCategory.quotient C _).obj L) :
    quotientCompressionMap n (φ + ψ) = quotientCompressionMap n φ + quotientCompressionMap n ψ := by
  rw [quotientCompressionMap_eq n ((HomotopyCategory.quotient C _).preimage φ +
    (HomotopyCategory.quotient C _).preimage ψ) _ (by simp), compressionMap_add,
    Functor.map_add]
  rfl

/-- The isomorphism of compressions induced by an isomorphism in the homotopy category. -/
noncomputable def quotientCompressionIso
    (e : (HomotopyCategory.quotient C _).obj K ≅ (HomotopyCategory.quotient C _).obj L) :
    (HomotopyCategory.quotient C _).obj (compression n K) ≅
      (HomotopyCategory.quotient C _).obj (compression n L) where
  hom := quotientCompressionMap n e.hom
  inv := quotientCompressionMap n e.inv
  hom_inv_id := by rw [← quotientCompressionMap_comp, e.hom_inv_id, quotientCompressionMap_id]
  inv_hom_id := by rw [← quotientCompressionMap_comp, e.inv_hom_id, quotientCompressionMap_id]

/-- The forward map of `quotientCompressionIso` compresses the forward map of the isomorphism. -/
@[simp]
lemma quotientCompressionIso_hom
    (e : (HomotopyCategory.quotient C _).obj K ≅ (HomotopyCategory.quotient C _).obj L) :
    (quotientCompressionIso n e).hom = quotientCompressionMap n e.hom :=
  (rfl)

/-- The inverse of `quotientCompressionIso` compresses the inverse of the isomorphism. -/
@[simp]
lemma quotientCompressionIso_inv
    (e : (HomotopyCategory.quotient C _).obj K ≅ (HomotopyCategory.quotient C _).obj L) :
    (quotientCompressionIso n e).inv = quotientCompressionMap n e.inv :=
  (rfl)

open HomotopyCategory.Bounded (rep quotient_obj_rep quotient_obj_rep_quotient_obj)

variable [HasFiniteCoproducts C]

instance (K : HomotopyCategory.Bounded C) : HasCompression n (rep K) :=
  hasCompression_of_bounded n (HomotopyCategory.Bounded.bounded_rep K)

/-- The `n`-periodic compression of bounded cochain complexes, descended to their homotopy
category. It sends the class of a bounded complex to the class of its compression. -/
noncomputable def homotopyCompressionFunctor :
    HomotopyCategory.Bounded C ⥤ HomotopyCategory C (ComplexShape.up (ZMod n)) where
  obj K := (HomotopyCategory.quotient C _).obj (compression n (rep K))
  map {K L} f := quotientCompressionMap n
    (eqToHom (quotient_obj_rep K) ≫ f.hom ≫ eqToHom (quotient_obj_rep L).symm)
  map_id K := by
    simp only [ObjectProperty.FullSubcategory.id_hom, Category.id_comp, eqToHom_trans,
      eqToHom_refl]
    exact quotientCompressionMap_id n _
  map_comp {K L M} f g := by
    refine Eq.trans ?_ (quotientCompressionMap_comp n _ _)
    simp

/-- The descended compression sends an object to the class of the compression of its underlying
complex. -/
lemma homotopyCompressionFunctor_obj (K : HomotopyCategory.Bounded C) :
    (homotopyCompressionFunctor n).obj K =
      (HomotopyCategory.quotient C _).obj (compression n (rep K)) :=
  (rfl)

/-- The descended compression acts on a morphism through any representing chain map, after
transporting along the object equations. -/
lemma homotopyCompressionFunctor_map {K L : HomotopyCategory.Bounded C} (f : K ⟶ L)
    (g : rep K ⟶ rep L)
    (hg : (HomotopyCategory.quotient C _).map g =
      eqToHom (quotient_obj_rep K) ≫ f.hom ≫ eqToHom (quotient_obj_rep L).symm) :
    (homotopyCompressionFunctor n).map f =
      eqToHom (homotopyCompressionFunctor_obj n K) ≫
        (HomotopyCategory.quotient C _).map (compressionMap n g) ≫
          eqToHom (homotopyCompressionFunctor_obj n L).symm := by
  -- Unfold the map field and identify the transports along its definitional object equations
  -- with identities. Simplification alone cannot eliminate the opaque equality proofs.
  change quotientCompressionMap n _ = 𝟙 _ ≫ _ ≫ 𝟙 _
  simpa using quotientCompressionMap_eq n g _ hg

instance : (homotopyCompressionFunctor (C := C) n).Additive where
  map_add {K L f g} := by
    refine Eq.trans (congrArg (quotientCompressionMap n) ?_) (quotientCompressionMap_add n _ _)
    -- Morphisms of the full subcategory are added as morphisms of the homotopy category.
    rw [← Preadditive.comp_add, ← Preadditive.add_comp]
    rfl

/-- The descended compression restricts along the quotient functor to the compression of bounded
cochain complexes. -/
noncomputable def quotientCompHomotopyCompressionFunctorIso :
    HomotopyCategory.Bounded.quotient C ⋙ homotopyCompressionFunctor n ≅
      compressionFunctor n ⋙ HomotopyCategory.quotient C _ :=
  NatIso.ofComponents (fun K ↦ quotientCompressionIso n
    (eqToIso (quotient_obj_rep_quotient_obj K))) (fun {K L} f ↦ by
      -- The naturality square, with its objects stated as classes of compressions.
      have key : quotientCompressionMap n (eqToHom (quotient_obj_rep _) ≫
          ((HomotopyCategory.Bounded.quotient C).map f).hom ≫
            eqToHom (quotient_obj_rep _).symm) ≫
          quotientCompressionMap n (eqToHom (quotient_obj_rep_quotient_obj L)) =
          quotientCompressionMap n (eqToHom (quotient_obj_rep_quotient_obj K)) ≫
            (HomotopyCategory.quotient C _).map (compressionMap n f.hom) := by
        rw [← quotientCompressionMap_comp, ← quotientCompressionMap_eq n f.hom _ rfl,
          ← quotientCompressionMap_comp]
        congr 1
        simp [HomotopyCategory.Bounded.quotient_map_hom]
      exact key)

/-- The component of `quotientCompHomotopyCompressionFunctorIso` at a bounded complex is the
compression of the identification of the class of its underlying complex, after transporting
along the object equations. -/
lemma quotientCompHomotopyCompressionFunctorIso_hom_app (K : CochainComplex.Bounded C) :
    (quotientCompHomotopyCompressionFunctorIso n).hom.app K =
      eqToHom (homotopyCompressionFunctor_obj n _) ≫
        quotientCompressionMap n (eqToHom (quotient_obj_rep_quotient_obj K)) ≫
          eqToHom (congrArg (HomotopyCategory.quotient C _).obj
            (compressionFunctor_obj n K)).symm := by
  -- Unfold the component and identify the transports along its definitional object equations
  -- with identities. Simplification alone cannot eliminate the opaque equality proofs.
  change quotientCompressionMap n _ = 𝟙 _ ≫ _ ≫ 𝟙 _
  simp

/-- The inverse component of `quotientCompHomotopyCompressionFunctorIso` at a bounded complex is
the compression of the inverse identification, after transporting along the object
equations. -/
lemma quotientCompHomotopyCompressionFunctorIso_inv_app (K : CochainComplex.Bounded C) :
    (quotientCompHomotopyCompressionFunctorIso n).inv.app K =
      eqToHom (congrArg (HomotopyCategory.quotient C _).obj (compressionFunctor_obj n K)) ≫
        quotientCompressionMap n (eqToHom (quotient_obj_rep_quotient_obj K).symm) ≫
          eqToHom (homotopyCompressionFunctor_obj n _).symm := by
  -- Unfold the component and identify the transports along its definitional object equations
  -- with identities. Simplification alone cannot eliminate the opaque equality proofs.
  change quotientCompressionMap n _ = 𝟙 _ ≫ _ ≫ 𝟙 _
  simp

end Homotopy

end PeriodicComplex

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Projections of the mapping cocone and short exact sequences

The mapping cocone `mappingCocone φ` of a morphism `φ : K ⟶ L` of cochain complexes is
`(mappingCone φ)⟦-1⟧`, and its projections `mappingCocone.fst φ : mappingCocone φ ⟶ K` and
`mappingCocone.snd φ` are built from those of the mapping cone. This file records the components
of these projections and their naturality with respect to the shifted mapping cone map induced by
a commutative square.

For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of cochain complexes in an abelian category,
the first map lifts to the mapping cocone of the second, and this lift `X₁ ⟶ mappingCocone S.g`
is a quasi-isomorphism. This is dual to Mathlib's `mappingCone.quasiIso_descShortComplex`, which
compares the mapping cone of the first map with the third term.

## Main results

* `CochainComplex.mappingCocone.fst_f`, `CochainComplex.mappingCocone.snd_v`: the components of
  the projections of the mapping cocone are those of the mapping cone.
* `CochainComplex.mappingCocone.shiftFunctor_map_mappingCone_map_comp_fst` and
  `CochainComplex.mappingCocone.shiftFunctor_map_mappingCone_map_f_snd_v`: the projections of
  the mapping cocone are natural in commutative squares.
* `CochainComplex.mappingCocone.quasiIso_lift_of_shortExact`: for a short exact sequence `S` of
  cochain complexes, the lift `S.X₁ ⟶ mappingCocone S.g` of `S.f` is a quasi-isomorphism.
-/

public section

open CategoryTheory Limits HomologicalComplex

namespace CochainComplex.mappingCocone

open HomComplex

section

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- The components of the first projection of the mapping cocone are those of the first
projection of the mapping cone. -/
lemma fst_f {K L : CochainComplex C ℤ} (φ : K ⟶ L) (p : ℤ) :
    (fst φ).f p = (mappingCone.fst φ).1.v (p + -1) p (by lia) := by
  simp [fst, Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia)]
  rfl

/-- The first projection of the mapping cocone is natural in commutative squares. -/
@[reassoc]
lemma shiftFunctor_map_mappingCone_map_comp_fst {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) :
    (mappingCone.map φ₁ φ₂ a b comm)⟦(-1 : ℤ)⟧' ≫ fst φ₂ = fst φ₁ ≫ a := by
  -- `mappingCocone φ` is `(mappingCone φ)⟦-1⟧` only up to unfolding, so the components are
  -- restated in matching types before rewriting.
  ext n : 1
  change ((mappingCone.map φ₁ φ₂ a b comm)⟦(-1 : ℤ)⟧').f n ≫ (fst φ₂).f n =
    (fst φ₁).f n ≫ a.f n
  rw [fst_f, fst_f, shiftFunctor_map_f']
  change (mappingCone.map φ₁ φ₂ a b comm).f (n + -1) ≫
      (mappingCone.fst φ₂).1.v (n + -1) n (by lia) =
    (mappingCone.fst φ₁).1.v (n + -1) n (by lia) ≫ a.f n
  apply mappingCone.ext_from φ₁ n (n + -1) (by lia) <;> simp [mappingCone.map]

/-- The components of the second projection of the mapping cocone are those of the second
projection of the mapping cone. -/
lemma snd_v {K L : CochainComplex C ℤ} (φ : K ⟶ L) (p : ℤ) :
    (snd φ).v p (p + -1) rfl = (mappingCone.snd φ).v (p + -1) (p + -1) (add_zero _) := by
  -- `snd φ` is a left shift of `mappingCone.snd φ`, but its source `mappingCocone φ` is
  -- `(mappingCone φ)⟦-1⟧` only up to unfolding, so it is restated before `leftShift_v` applies.
  change ((mappingCone.snd φ).leftShift (-1) (-1) (zero_add _)).v p (p + -1) rfl = _
  rw [Cochain.leftShift_v _ (-1) (-1) _ p (p + -1) rfl (p + -1) (add_zero _)]
  simp [Int.negOnePow_even 2 ⟨1, rfl⟩]

/-- The second projection of the mapping cocone is natural in commutative squares. -/
@[reassoc]
lemma shiftFunctor_map_mappingCone_map_f_snd_v {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)
    (p : ℤ) :
    ((mappingCone.map φ₁ φ₂ a b comm)⟦(-1 : ℤ)⟧').f p ≫ (snd φ₂).v p (p + -1) rfl =
      (snd φ₁).v p (p + -1) rfl ≫ b.f (p + -1) := by
  rw [snd_v, snd_v, shiftFunctor_map_f']
  -- As in `shiftFunctor_map_mappingCone_map_comp_fst`, the components are restated in matching
  -- types before applying the extensionality lemma for maps out of the mapping cone.
  change (mappingCone.map φ₁ φ₂ a b comm).f (p + -1) ≫
      (mappingCone.snd φ₂).v (p + -1) (p + -1) (add_zero _) =
    (mappingCone.snd φ₁).v (p + -1) (p + -1) (add_zero _) ≫ b.f (p + -1)
  apply mappingCone.ext_from φ₁ p (p + -1) (by lia) <;> simp [mappingCone.map]

/-- Two morphisms to a term of the mapping cocone are equal if their compositions with both
projections are. -/
lemma ext_to {K L : CochainComplex C ℤ} (φ : K ⟶ L) (p q : ℤ) (hpq : p + -1 = q) {A : C}
    {f g : A ⟶ (mappingCocone φ).X p}
    (h₁ : f ≫ (fst φ).f p = g ≫ (fst φ).f p)
    (h₂ : f ≫ (snd φ).v p q hpq = g ≫ (snd φ).v p q hpq) : f = g := by
  rw [← Category.comp_id f, ← Category.comp_id g, ← id_X φ p q hpq, Preadditive.comp_add,
    Preadditive.comp_add, reassoc_of% h₁, reassoc_of% h₂]

end

section Abelian

variable {C : Type*} [Category* C] [Abelian C]

/-- The mapping cocone of an identity morphism is acyclic, since it is contractible. -/
lemma acyclic_mappingCocone_id (L : CochainComplex C ℤ) : (mappingCocone (𝟙 L)).Acyclic :=
  fun i ↦ by
    rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
    have := ((mappingCone.homotopyToZeroOfId L).shift (-1)).homologyMap_eq i
    simp only [CategoryTheory.Functor.map_id, Functor.map_zero, homologyMap_id,
      homologyMap_zero] at this
    exact this

variable {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- The map `mappingCocone φ ⟶ mappingCocone (𝟙 L)` induced by the square from `φ` to `𝟙 L`;
it is `φ` on the first component and the identity on the second. -/
private noncomputable def toId : mappingCocone φ ⟶ mappingCocone (𝟙 L) :=
  (mappingCone.map φ (𝟙 L) φ (𝟙 L) (by simp))⟦(-1 : ℤ)⟧'

@[reassoc]
private lemma toId_comp_fst : toId φ ≫ fst (𝟙 L) = fst φ ≫ φ :=
  shiftFunctor_map_mappingCone_map_comp_fst _ _ _ _ _

@[reassoc]
private lemma toId_f_fst_f (p : ℤ) : (toId φ).f p ≫ (fst (𝟙 L)).f p = (fst φ).f p ≫ φ.f p :=
  HomologicalComplex.congr_hom (toId_comp_fst φ) p

@[reassoc]
private lemma toId_f_snd_v (p : ℤ) :
    (toId φ).f p ≫ (snd (𝟙 L)).v p (p + -1) rfl = (snd φ).v p (p + -1) rfl :=
  (shiftFunctor_map_mappingCone_map_f_snd_v _ _ _ _ _ p).trans (Category.comp_id _)

/-- The map to the mapping cocone of `𝟙 L` is a degreewise epimorphism when `φ` is. -/
private lemma epi_toId_f (p : ℤ) [Epi (φ.f p)] : Epi ((toId φ).f p) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A y
  obtain ⟨A', π, hπ, x, hx⟩ :=
    surjective_up_to_refinements_of_epi (φ.f p) (y ≫ (fst (𝟙 L)).f p)
  refine ⟨A', π, hπ, x ≫ (inl φ).v p p (add_zero p) +
    π ≫ y ≫ (snd (𝟙 L)).v p (p + -1) rfl ≫ (inr φ).1.v (p + -1) p (by lia), ?_⟩
  apply ext_to (𝟙 L) p (p + -1) rfl
  · simp [toId_f_fst_f, hx]
  · simp [toId_f_snd_v]

variable {S : ShortComplex (CochainComplex C ℤ)}

@[reassoc (attr := simp)]
private lemma lift_comp_toId : lift S.g S.f 0 (by simp) ≫ toId S.g = 0 := by
  ext p
  apply ext_to _ p (p + -1) rfl
  · rw [← HomologicalComplex.comp_f, Category.assoc, toId_comp_fst, lift_fst_assoc, S.zero]
    simp
  · simp [toId_f_snd_v]

/-- The lift of `S.f` to the mapping cocone of `S.g` is the kernel of the map to the mapping
cocone of `𝟙 S.X₃`, degreewise. -/
private lemma shortExact_lift_toId (hS : S.ShortExact) :
    (ShortComplex.mk _ _ (lift_comp_toId (S := S))).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p ↦ ?_
  have hSp := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS p
  have : Mono (S.f.f p) := hSp.mono_f
  have : Epi (S.g.f p) := hSp.epi_g
  refine .mk' ?_ (mono_of_mono_fac (lift_f_fst_f S.g S.f 0 (by simp) p)) (epi_toId_f S.g p)
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x (hx : x ≫ (toId S.g).f p = 0)
  have h₁ : (x ≫ (fst S.g).f p) ≫ S.g.f p = 0 := by
    simpa [toId_f_fst_f] using hx =≫ (fst (𝟙 S.X₃)).f p
  have h₂ : x ≫ (snd S.g).v p (p + -1) rfl = 0 := by
    simpa [toId_f_snd_v] using hx =≫ (snd (𝟙 S.X₃)).v p (p + -1) rfl
  obtain ⟨A', π, hπ, z, hz⟩ :=
    (ShortComplex.exact_iff_exact_up_to_refinements _).1 hSp.exact _ h₁
  refine ⟨A', π, hπ, z, (?_ : π ≫ x = z ≫ (lift S.g S.f 0 (by simp)).f p)⟩
  apply ext_to S.g p (p + -1) rfl
  · simpa using hz
  · simp [h₂]

/-- For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of cochain complexes, the lift
`X₁ ⟶ mappingCocone S.g` of `S.f` is a quasi-isomorphism. -/
theorem quasiIso_lift_of_shortExact (hS : S.ShortExact) :
    QuasiIso (lift S.g S.f 0 (by simp)) := by
  -- The proof does not compare connecting maps: the lift is the kernel of a degreewise
  -- epimorphism onto the mapping cocone of `𝟙 X₃`, which is contractible. We use the long exact
  -- homology sequence of the short exact sequence
  -- `X₁ ⟶ mappingCocone S.g ⟶ mappingCocone (𝟙 X₃)`, whose third term is acyclic.
  have hT := shortExact_lift_toId hS
  have hC := acyclic_mappingCocone_id S.X₃
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (homologyMap (lift S.g S.f 0 (by simp)) n) :=
    (hT.homology_exact₁ (n - 1) n (by simp)).mono_g
      (((hC (n - 1)).isZero_homology).eq_of_src _ _)
  have : Epi (homologyMap (lift S.g S.f 0 (by simp)) n) :=
    (hT.homology_exact₂ n).epi_f (((hC n).isZero_homology).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end Abelian

end CochainComplex.mappingCocone

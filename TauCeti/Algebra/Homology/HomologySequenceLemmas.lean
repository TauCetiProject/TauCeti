/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Lemmas on the homology sequence of a short exact sequence of complexes

Let `φ : S₁ ⟶ S₂` be a morphism between two short exact sequences of homological complexes in an
abelian category. Mathlib's `HomologicalComplex.HomologySequence.quasiIso_τ₃` shows that `φ.τ₃`
is a quasi-isomorphism when `φ.τ₁` and `φ.τ₂` are. This file proves the corresponding statement
for the middle map: `φ.τ₂` is a quasi-isomorphism when `φ.τ₁` and `φ.τ₃` are. This lets one
transfer a quasi-isomorphism to the middle terms of short exact sequences after comparing their
outer terms, as for the short exact sequences associated with maps of mapping cones.

It also proves that the connecting maps of a `3 × 3` diagram of complexes with short exact rows
and columns anticommute: the two composites of connecting maps from the homology of one corner to
that of the opposite corner differ by a sign. Both composites factor through the connecting maps of
two auxiliary short exact sequences, `ker (X₂₂ ⟶ X₃₃) ⟶ X₂₂ ⟶ X₃₃` and
`X₁₁ ⟶ X₁₂ ⊞ X₂₁ ⟶ ker (X₂₂ ⟶ X₃₃)`, and the sign is that of the first map `(f, -f)` of the
second one. This is the sign rule behind the compatibility of products with connecting maps in each
variable, such as for the cup product in Tate cohomology.

## Main results

* `HomologicalComplex.HomologySequence.mono_homologyMap_τ₂`,
  `HomologicalComplex.HomologySequence.epi_homologyMap_τ₂`,
  `HomologicalComplex.HomologySequence.isIso_homologyMap_τ₂`: sufficient conditions for `φ.τ₂`
  to induce a mono, epi or iso in a given degree.
* `HomologicalComplex.HomologySequence.quasiIso_τ₂`: if `φ.τ₁` and `φ.τ₃` are
  quasi-isomorphisms, so is `φ.τ₂`.
* `HomologicalComplex.HomologySequence.δ_comp_δ_eq_neg`: the connecting maps of a `3 × 3` diagram
  with short exact rows and columns anticommute.
-/

public section

open CategoryTheory ComposableArrows Abelian

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

namespace HomologicalComplex

namespace HomologySequence

include hS₁ hS₂

/-- The map `φ.τ₂` is injective on homology in degree `j` if `φ.τ₁` and `φ.τ₃` are injective in
degree `j` and `φ.τ₃` is surjective in the degrees preceding `j`. -/
lemma mono_homologyMap_τ₂ (j : ι)
    (h₁ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i))
    (h₂ : Mono (homologyMap φ.τ₁ j))
    (h₃ : Mono (homologyMap φ.τ₃ j)) :
    Mono (homologyMap φ.τ₂ j) := by
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    -- The exact sequence `H_i(X₃) ⟶ H_j(X₁) ⟶ H_j(X₂) ⟶ H_j(X₃)`.
    apply mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δ₀
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δ₀
    · exact h₁ i hij
    · exact h₂
    · exact h₃
  · have := hS₂.mono_f
    have := mono_homologyMap_of_mono_of_not_rel S₂.f j (by simpa using hj)
    exact mono_of_mono_of_mono_of_mono (mapComposableArrows₂ φ j)
      (composableArrows₂_exact hS₁ j) this h₂ h₃

/-- The map `φ.τ₂` is surjective on homology in degree `j` if `φ.τ₁` and `φ.τ₃` are surjective in
degree `j` and `φ.τ₁` is injective in the degrees following `j`. -/
lemma epi_homologyMap_τ₂ (j : ι)
    (h₁ : Epi (homologyMap φ.τ₁ j))
    (h₂ : Epi (homologyMap φ.τ₃ j))
    (h₃ : ∀ k, c.Rel j k → Mono (homologyMap φ.τ₁ k)) :
    Epi (homologyMap φ.τ₂ j) := by
  by_cases hj : ∃ k, c.Rel j k
  · obtain ⟨k, hjk⟩ := hj
    -- The exact sequence `H_j(X₁) ⟶ H_j(X₂) ⟶ H_j(X₃) ⟶ H_k(X₁)`.
    apply epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ j k hjk))
    · exact (composableArrows₅_exact hS₁ j k hjk).δlast.δlast
    · exact (composableArrows₅_exact hS₂ j k hjk).δlast.δlast
    · exact h₁
    · exact h₂
    · exact h₃ k hjk
  · have := hS₁.epi_g
    have := epi_homologyMap_of_epi_of_not_rel S₁.g j (by simpa using hj)
    exact epi_of_epi_of_epi_of_epi (mapComposableArrows₂ φ j)
      (composableArrows₂_exact hS₂ j) this h₁ h₂

/-- The map `φ.τ₂` is an isomorphism on homology in degree `j` if `φ.τ₁` and `φ.τ₃` are
isomorphisms in degree `j`, `φ.τ₃` is surjective in the degrees preceding `j`, and `φ.τ₁` is
injective in the degrees following `j`. -/
lemma isIso_homologyMap_τ₂ (j : ι)
    (h₁ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i))
    (h₂ : IsIso (homologyMap φ.τ₁ j))
    (h₃ : IsIso (homologyMap φ.τ₃ j))
    (h₄ : ∀ k, c.Rel j k → Mono (homologyMap φ.τ₁ k)) :
    IsIso (homologyMap φ.τ₂ j) := by
  have := mono_homologyMap_τ₂ φ hS₁ hS₂ j h₁ inferInstance inferInstance
  have := epi_homologyMap_τ₂ φ hS₁ hS₂ j inferInstance inferInstance h₄
  exact isIso_of_mono_of_epi _

/-- **Two out of three for the middle map.** In a morphism of short exact sequences of complexes,
if the outer maps `φ.τ₁` and `φ.τ₃` are quasi-isomorphisms, so is the middle map `φ.τ₂`. -/
lemma quasiIso_τ₂ (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_homologyMap_τ₂ φ hS₁ hS₂
  all_goals infer_instance

end HomologySequence

end HomologicalComplex


/-! ### Anticommutativity of the connecting maps of a `3 × 3` diagram -/

open Limits

namespace ThreeByThree

section

variable {A : Type*} [Category* A] [HasZeroMorphisms A] [HasKernels A]
  (D : ShortComplex (ShortComplex A))

/-- The kernel of the diagonal `X₂₂ ⟶ X₃₃` of a `3 × 3` diagram. -/
private noncomputable abbrev K : A := kernel (D.X₂.g ≫ D.g.τ₃)

/-- The inclusion of the kernel of the diagonal. -/
private noncomputable abbrev incl : K D ⟶ D.X₂.X₂ := kernel.ι (D.X₂.g ≫ D.g.τ₃)

end

section

variable {A : Type*} [Category* A] [Preadditive A] [Balanced A] [HasKernels A]
  (D : ShortComplex (ShortComplex A))

/-- The map from the kernel of the diagonal to `X₃₁`. -/
private noncomputable def toX₃₁ (h₃ : D.X₃.ShortExact) : K D ⟶ D.X₃.X₁ :=
  have := h₃.mono_f
  h₃.exact.lift (incl D ≫ D.g.τ₂) (by rw [Category.assoc, D.g.comm₂₃, kernel.condition])

private lemma toX₃₁_f (h₃ : D.X₃.ShortExact) : toX₃₁ D h₃ ≫ D.X₃.f = incl D ≫ D.g.τ₂ :=
  have := h₃.mono_f
  h₃.exact.lift_f _ _

/-- The map from the kernel of the diagonal to `X₁₃`. -/
private noncomputable def toX₁₃ (h₃' : (D.map ShortComplex.π₃).ShortExact) : K D ⟶ D.X₁.X₃ :=
  have := h₃'.mono_f
  h₃'.exact.lift (incl D ≫ D.X₂.g)
    ((Category.assoc _ _ _).trans (kernel.condition (D.X₂.g ≫ D.g.τ₃)))

private lemma toX₁₃_f (h₃' : (D.map ShortComplex.π₃).ShortExact) :
    toX₁₃ D h₃' ≫ D.f.τ₃ = incl D ≫ D.X₂.g :=
  have := h₃'.mono_f
  h₃'.exact.lift_f _ _

end

variable {A : Type*} [Category* A] [Abelian A] (D : ShortComplex (ShortComplex A))

/-- The morphism from the kernel sequence of the diagonal to the third row. -/
private noncomputable def diagSequenceToRow₃ (h₃ : D.X₃.ShortExact) :
    ShortComplex.kernelSequence (D.X₂.g ≫ D.g.τ₃) ⟶ D.X₃ where
  τ₁ := toX₃₁ D h₃
  τ₂ := D.g.τ₂
  τ₃ := 𝟙 _
  comm₁₂ := toX₃₁_f D h₃
  comm₂₃ := D.g.comm₂₃.trans (Category.comp_id _).symm

/-- The morphism from the kernel sequence of the diagonal to the third column. -/
private noncomputable def diagSequenceToCol₃ (h₃' : (D.map ShortComplex.π₃).ShortExact) :
    ShortComplex.kernelSequence (D.X₂.g ≫ D.g.τ₃) ⟶ D.map ShortComplex.π₃ where
  τ₁ := toX₁₃ D h₃'
  τ₂ := D.X₂.g
  τ₃ := 𝟙 _
  comm₁₂ := toX₁₃_f D h₃'
  comm₂₃ := (Category.comp_id _).symm

section

variable {A : Type*} [Category* A] [HasZeroMorphisms A] [HasBinaryBiproducts A] [HasKernels A]
  (D : ShortComplex (ShortComplex A))

/-- The map `X₁₂ ⊞ X₂₁ ⟶ ker (X₂₂ ⟶ X₃₃)` induced by the sum of the two maps to `X₂₂`. -/
private noncomputable def toK : D.X₁.X₂ ⊞ D.X₂.X₁ ⟶ K D :=
  kernel.lift _ (biprod.desc D.f.τ₂ D.X₂.f) (by
    ext
    · rw [biprod.inl_desc_assoc, ← Category.assoc, D.f.comm₂₃, Category.assoc,
        ← ShortComplex.comp_τ₃, D.zero, ShortComplex.zero_τ₃, comp_zero, comp_zero]
    · rw [biprod.inr_desc_assoc, ← Category.assoc, D.X₂.zero, zero_comp, comp_zero])

private lemma toK_incl : toK D ≫ incl D = biprod.desc D.f.τ₂ D.X₂.f := kernel.lift_ι _ _ _

end

/-- The short complex `X₁₁ ⟶ X₁₂ ⊞ X₂₁ ⟶ ker (X₂₂ ⟶ X₃₃)`, whose first map is `(f, -f)`. -/
private noncomputable abbrev crossSequence : ShortComplex A :=
  ShortComplex.mk (biprod.lift D.X₁.f (-D.f.τ₁)) (toK D) (by
    rw [← cancel_mono (incl D), Category.assoc, toK_incl, biprod.lift_desc, zero_comp,
      Preadditive.neg_comp, D.f.comm₁₂, add_neg_cancel])

variable {D}

private lemma crossSequence_shortExact (h₁ : D.X₁.ShortExact) (h₂ : D.X₂.ShortExact)
    (h₃ : D.X₃.ShortExact) (h₁' : (D.map ShortComplex.π₁).ShortExact)
    (h₂' : (D.map ShortComplex.π₂).ShortExact)
    (h₃' : (D.map ShortComplex.π₃).ShortExact) :
    (crossSequence D).ShortExact := by
  have := h₁.mono_f
  have := h₂.mono_f
  have : Epi D.g.τ₁ := h₁'.epi_g
  have : Mono D.f.τ₂ := h₂'.mono_f
  have : Mono D.f.τ₃ := h₃'.mono_f
  have : Mono (crossSequence D).f := mono_of_mono_fac (biprod.lift_fst D.X₁.f (-D.f.τ₁))
  have : Epi (crossSequence D).g := by
    rw [epi_iff_surjective_up_to_refinements]
    intro B y
    -- The image of `y` in `X₃₂` comes from `X₃₁`; lift it to `X₂₁` up to refinement.
    obtain ⟨B', π, _, a, ha⟩ := surjective_up_to_refinements_of_epi D.g.τ₁ (y ≫ toX₃₁ D h₃)
    -- The difference of `y` and the image of `a` in `X₂₂` comes from `X₁₂`.
    have hb : (π ≫ y ≫ incl D - a ≫ D.X₂.f) ≫ D.g.τ₂ = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, Category.assoc, ← toX₃₁_f D h₃, ← Category.assoc y,
        ← Category.assoc π, ha, Category.assoc, Category.assoc, D.g.comm₁₂, sub_self]
    have := h₂'.mono_f
    let b : B' ⟶ D.X₁.X₂ := h₂'.exact.lift _ hb
    have hb' : b ≫ D.f.τ₂ = π ≫ y ≫ incl D - a ≫ D.X₂.f := h₂'.exact.lift_f _ hb
    refine ⟨B', π, inferInstance, biprod.lift b a, ?_⟩
    rw [← cancel_mono (incl D), Category.assoc, Category.assoc, toK_incl, biprod.lift_desc, hb',
      sub_add_cancel]
  refine { exact := ?_ }
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro B x hx
  have hx' : x ≫ biprod.fst ≫ D.f.τ₂ + x ≫ biprod.snd ≫ D.X₂.f = 0 := by
    have e := hx =≫ incl D
    rwa [Category.assoc, toK_incl, zero_comp, biprod.desc_eq, Preadditive.comp_add] at e
  -- The first component of `x` comes from `X₁₁`.
  have hb : (x ≫ biprod.fst) ≫ D.X₁.g = 0 := by
    rw [← cancel_mono D.f.τ₃, Category.assoc, Category.assoc, ← D.f.comm₂₃, zero_comp,
      ← Category.assoc biprod.fst, ← Category.assoc x, eq_neg_of_add_eq_zero_left hx',
      Preadditive.neg_comp, Category.assoc, Category.assoc, D.X₂.zero, comp_zero, comp_zero,
      neg_zero]
  refine ⟨B, 𝟙 B, inferInstance, h₁.exact.lift _ hb, ?_⟩
  ext
  · rw [Category.id_comp, Category.assoc, biprod.lift_fst, h₁.exact.lift_f]
  · rw [Category.id_comp, Category.assoc, biprod.lift_snd, ← cancel_mono D.X₂.f]
    simp only [Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp, D.f.comm₁₂]
    rw [← Category.assoc (h₁.exact.lift _ hb), h₁.exact.lift_f, Category.assoc]
    exact eq_neg_of_add_eq_zero_right hx'

/-- The morphism from the cross sequence to the first row: the identity on `X₁₁` and the first
projection on `X₁₂ ⊞ X₂₁`. -/
private noncomputable def crossSequenceToRow₁ (h₃' : (D.map ShortComplex.π₃).ShortExact) :
    crossSequence D ⟶ D.X₁ where
  τ₁ := 𝟙 _
  τ₂ := biprod.fst
  τ₃ := toX₁₃ D h₃'
  comm₁₂ := by rw [Category.id_comp]; exact (biprod.lift_fst D.X₁.f (-D.f.τ₁)).symm
  comm₂₃ := by
    have : Mono D.f.τ₃ := h₃'.mono_f
    rw [← cancel_mono D.f.τ₃]
    simp only [Category.assoc, toX₁₃_f]
    ext
    · simp [← D.f.comm₂₃, ← Category.assoc, toK_incl]
    · simp [← Category.assoc, toK_incl]

/-- The morphism from the cross sequence to the first column: minus the identity on `X₁₁` and the
second projection on `X₁₂ ⊞ X₂₁`. -/
private noncomputable def crossSequenceToCol₁ (h₃ : D.X₃.ShortExact) :
    crossSequence D ⟶ D.map ShortComplex.π₁ where
  τ₁ := -𝟙 _
  τ₂ := biprod.snd
  τ₃ := toX₃₁ D h₃
  comm₁₂ := by
    dsimp only [ShortComplex.map, ShortComplex.π₁]
    rw [Preadditive.neg_comp, Category.id_comp, biprod.lift_snd]
  comm₂₃ := by
    dsimp only [ShortComplex.map, ShortComplex.π₁]
    have := h₃.mono_f
    rw [← cancel_mono D.X₃.f]
    simp only [Category.assoc, toX₃₁_f]
    ext
    · simp [← Category.assoc, toK_incl, ← ShortComplex.comp_τ₂, D.zero]
    · simp [← Category.assoc, toK_incl, D.g.comm₁₂]

end ThreeByThree

namespace HomologicalComplex.HomologySequence

open ThreeByThree in
/-- **The connecting maps of a `3 × 3` diagram anticommute.** Let `D` be a `3 × 3` diagram of
homological complexes in an abelian category, presented as a short complex `D.X₁ ⟶ D.X₂ ⟶ D.X₃`
of short complexes, all of whose rows `D.Xᵢ` and columns `D.map π_j` are short exact. Then the two
composites of connecting maps from the homology of the corner `X₃₃` to that of the corner `X₁₁`,
through the third row and the first column, and through the third column and the first row,
differ by a sign. -/
lemma δ_comp_δ_eq_neg (D : ShortComplex (ShortComplex (HomologicalComplex C c)))
    (h₁ : D.X₁.ShortExact) (h₂ : D.X₂.ShortExact) (h₃ : D.X₃.ShortExact)
    (h₁' : (D.map ShortComplex.π₁).ShortExact) (h₂' : (D.map ShortComplex.π₂).ShortExact)
    (h₃' : (D.map ShortComplex.π₃).ShortExact) (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    h₃.δ i j hij ≫ h₁'.δ j k hjk = -(h₃'.δ i j hij ≫ h₁.δ j k hjk) := by
  have : Epi (D.X₂.g ≫ D.g.τ₃) := by
    have := h₂.epi_g
    have : Epi D.g.τ₃ := h₃'.epi_g
    exact epi_comp _ _
  have hE := TauCeti.kernelSequence_shortExact (D.X₂.g ≫ D.g.τ₃)
  have hT := crossSequence_shortExact (A := HomologicalComplex C c) h₁ h₂ h₃ h₁' h₂' h₃'
  -- Give the auxiliary and column connecting maps the diagram's objects as endpoints, so rewriting
  -- does not need to unfold the chosen kernels and the column projection functors.
  let δE : D.X₃.X₃.homology i ⟶ (K D).homology j := hE.δ i j hij
  let δT : (K D).homology j ⟶ D.X₁.X₁.homology k := hT.δ j k hjk
  let δC₁ : D.X₃.X₁.homology j ⟶ D.X₁.X₁.homology k := h₁'.δ j k hjk
  let δC₃ : D.X₃.X₃.homology i ⟶ D.X₁.X₃.homology j := h₃'.δ i j hij
  -- The connecting maps of the third row and column factor through the one of the kernel sequence
  -- of the diagonal `X₂₂ ⟶ X₃₃`, and the connecting maps of the first row and column factor,
  -- with opposite signs, through the one of the cross sequence `X₁₁ ⟶ X₁₂ ⊞ X₂₁ ⟶ ker`.
  have eR₃ : δE ≫ homologyMap (toX₃₁ D h₃) j = homologyMap (𝟙 _) i ≫ h₃.δ i j hij :=
    δ_naturality (diagSequenceToRow₃ D h₃) hE h₃ i j hij
  have eC₃ : δE ≫ homologyMap (toX₁₃ D h₃') j = homologyMap (𝟙 _) i ≫ δC₃ :=
    δ_naturality (diagSequenceToCol₃ D h₃') hE h₃' i j hij
  have eR₁ : δT ≫ homologyMap (𝟙 _) k = homologyMap (toX₁₃ D h₃') j ≫ h₁.δ j k hjk :=
    δ_naturality (crossSequenceToRow₁ h₃') hT h₁ j k hjk
  have eC₁ : δT ≫ homologyMap (-𝟙 _) k = homologyMap (toX₃₁ D h₃) j ≫ δC₁ :=
    δ_naturality (crossSequenceToCol₁ h₃) hT h₁' j k hjk
  rw [homologyMap_id, Category.id_comp] at eR₃ eC₃
  rw [homologyMap_id, Category.comp_id] at eR₁
  rw [homologyMap_neg, homologyMap_id, Preadditive.comp_neg, Category.comp_id] at eC₁
  suffices h₃.δ i j hij ≫ δC₁ = -(δC₃ ≫ h₁.δ j k hjk) from this
  rw [← eR₃, ← eC₃, Category.assoc, Category.assoc, ← eC₁, ← eR₁,
    Preadditive.comp_neg]

end HomologicalComplex.HomologySequence

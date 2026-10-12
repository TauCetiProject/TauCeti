/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex
public import TauCeti.Algebra.Homology.HomologySequenceLemmas

/-!
# Short exact coefficient sequences and Čech acyclicity

The Čech complex preserves short exact sequences of presheaves when the coefficient category
has products and its products of the required sizes are exact. The exactness requirement is
automatic for finite families in an abelian category, and for arbitrary families of abelian
groups. Exactness is tested in the presheaf values before sheafification, only at the
objects specified below. For finite families, the exact-product hypothesis is supplied by
locally enabling `Abelian.hasFiniteBiproducts`.

Only the values at finite products of members matter: a sequence of presheaves that is short
exact after evaluation at each such product has a short exact sequence of Čech complexes
(`shortExact_map_cechComplexFunctor`). For an open cover, this asks for exactness only on the
finite intersections of members.

For a coefficient sequence that is short exact at the terminal object and at the finite
products of members, acyclicity of its middle and right terms implies acyclicity of its left term.
This is the coefficient-sequence descent used when iterating
Mayer-Vietoris sequences for Laurent covers: the middle term is the pair of restrictions and
the right term is the restriction to the intersection.

The comparison uses `HomologicalComplex.HomologySequence.quasiIso_τ₁` for the morphism of
short exact sequences induced by the augmentations.

Shifting dimension along such sequences gives Čech acyclicity from a resolution. If
`0 ⟶ P ⟶ K⁰ ⟶ K¹ ⟶ ⋯` is a sequence of presheaves which is exact at the terminal object and at the
finite products of members, and every `Kᵏ` is acyclic, then `P` is acyclic
(`quasiIso_cechAugmentation_of_resolution`). The resolution splits into sequences of presheaves
of cycles, short exact at those objects, and in each of them the augmented Čech complexes of the
left and right terms agree up to a shift of one degree, by the degreewise lemmas
`HomologicalComplex.HomologySequence.isIso_homologyMap_τ₁` and
`HomologicalComplex.HomologySequence.mono_homologyMap_τ₁`.

## Main results

* `TauCeti.CategoryTheory.preservesLimitsOfShape_cechComplexFunctor`: the Čech complex functor
  preserves every limit that exists in the coefficient category.
* `TauCeti.CategoryTheory.shortExact_map_cechComplexFunctor`: a sequence of presheaves short exact
  at the finite products of members has a short exact sequence of Čech complexes.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_shortExact`: for a coefficient sequence
  short exact at the terminal object and at finite products of members, acyclicity of the middle
  and right terms implies acyclicity of the left term.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_resolution`: a presheaf with a resolution by
  acyclic presheaves, exact at the terminal object and at the finite products of members, is
  acyclic.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Appendix A and Lemma 8.34(i).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v v' u u'

namespace TauCeti.CategoryTheory

section Preservation

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C)

/-- Evaluation of the Čech complex in degree `n` is the product of the evaluations at
`U (a 0) × ⋯ × U (a n)`. -/
private def cechEvalIso (n : ℕ) :
    cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) n ≅
      (Functor.whiskeringLeft (Discrete (Fin (n + 1) → ι)) Cᵒᵖ A).obj
        (Discrete.functor (fun a ↦ op (∏ᶜ fun j ↦ U (a j)))) ⋙ lim :=
  NatIso.ofComponents (fun P ↦
    let e : ((cechComplexFunctor U).obj P).X n ≅
        ∏ᶜ (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) := Iso.refl _
    e ≪≫ HasLimit.isoOfNatIso
      (F := Discrete.functor (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))))
      (G := Discrete.functor (fun a : Fin (n + 1) → ι ↦ op (∏ᶜ fun j ↦ U (a j))) ⋙ P)
      (Discrete.compNatIsoDiscrete _ P).symm) (fun α ↦ by
    apply limit.hom_ext
    intro a
    -- The Čech term and the product use definitionally equal diagrams with different
    -- chosen-limit instances; `erw` also normalizes those instances.
    erw [Iso.trans_hom, Iso.trans_hom, Iso.refl_hom, Iso.refl_hom,
      Category.id_comp, Category.id_comp]
    dsimp only [Functor.comp_map, HomologicalComplex.eval_map,
      Functor.whiskeringLeft_obj_obj, Functor.whiskeringLeft_obj_map]
    erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, Category.assoc, limMap_π,
      HasLimit.isoOfNatIso_hom_π_assoc]
    simp only [Discrete.compNatIsoDiscrete, Iso.symm_hom, Discrete.natIso_inv_app,
      Iso.refl_inv]
    erw [Category.comp_id, Category.id_comp]
    convert cechComplexFunctor_map_f_π U _ α n a.as using 1
    rfl)

/-- The Čech complex functor preserves every limit that exists in the coefficient category: in
each degree it is a product of evaluations, and limits commute with products and evaluations. -/
instance preservesLimitsOfShape_cechComplexFunctor (J : Type*) [Category J]
    [HasLimitsOfShape J A] : PreservesLimitsOfShape J (cechComplexFunctor (A := A) U) := by
  apply HomologicalComplex.preservesLimitsOfShape_of_eval
  intro n
  exact preservesLimitsOfShape_of_natIso (cechEvalIso U n).symm

/-- The Čech complex functor preserves finite limits. -/
instance preservesFiniteLimits_cechComplexFunctor [HasFiniteLimits A] :
    PreservesFiniteLimits (cechComplexFunctor (A := A) U) where
  preservesFiniteLimits _ _ _ := inferInstance

section FiniteColimits

variable [HasFiniteColimits A]
  [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → ι)) A]

/-- With exact products, the Čech complex functor preserves finite colimits. -/
instance preservesFiniteColimits_cechComplexFunctor : PreservesFiniteColimits (cechComplexFunctor
    (A := A) U) where
  preservesFiniteColimits J _ _ := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    exact preservesColimitsOfShape_of_natIso (cechEvalIso U n).symm

end FiniteColimits

end Preservation

/-! ### Resolutions and their cycles

A morphism `ε : P ⋙ single₀ ⟶ K` from a presheaf `P`, placed in degree `0`, to a presheaf of
cochain complexes `K` resolves `P` at an object `Y` when `ε.app Y` is a quasi-isomorphism, that is,
when `0 ⟶ P(Y) ⟶ K⁰(Y) ⟶ K¹(Y) ⟶ ⋯` is exact. The resolution splits into the sequences
`0 ⟶ P ⟶ K⁰ ⟶ Z¹ ⟶ 0` (`augmentationSC`) and `0 ⟶ Zᵏ ⟶ Kᵏ ⟶ Zᵏ⁺¹ ⟶ 0` (`cyclesSC`) of
presheaves of cycles `Zᵏ`, which are short exact at every object where `ε` is a
quasi-isomorphism. -/

section Resolution

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] [Abelian A]

variable (K : Cᵒᵖ ⥤ CochainComplex A ℕ)

/-- The inclusion `Zᵏ ⟶ Kᵏ` of the presheaf of cycles. -/
private def cyclesι (k : ℕ) :
    K ⋙ HomologicalComplex.cyclesFunctor A _ k ⟶ K ⋙ HomologicalComplex.eval A _ k where
  app Y := (K.obj Y).iCycles k
  naturality _ _ f := HomologicalComplex.cyclesMap_i (K.map f) k

/-- The map `Kᵏ ⟶ Zᵏ⁺¹` onto the presheaf of cycles of the next degree. -/
private def cyclesπ (k : ℕ) :
    K ⋙ HomologicalComplex.eval A _ k ⟶ K ⋙ HomologicalComplex.cyclesFunctor A _ (k + 1) where
  app Y := (K.obj Y).toCycles k (k + 1)
  naturality _ _ f := ((K.obj _).toCycles_cyclesMap (K.map f) k (k + 1)).symm

/-- The sequence `0 ⟶ Zᵏ ⟶ Kᵏ ⟶ Zᵏ⁺¹ ⟶ 0` of presheaves of cycles. -/
private def cyclesSC (k : ℕ) : ShortComplex (Cᵒᵖ ⥤ A) :=
  ShortComplex.mk (cyclesι K k) (cyclesπ K k) <|
    NatTrans.ext <| funext fun Y ↦ (K.obj Y).iCycles_toCycles k (k + 1)

/-- The sequence of cycles in degree `k` is short exact at every object `Y` at which `K` is exact
in degree `k + 1`. -/
private lemma cyclesSC_shortExact (k : ℕ) {Y : Cᵒᵖ} (hY : (K.obj Y).ExactAt (k + 1)) :
    ((cyclesSC K k).map ((evaluation Cᵒᵖ A).obj Y)).ShortExact :=
  have : Epi ((K.obj Y).toCycles k (k + 1)) :=
    HomologicalComplex.epi_toCycles_of_exactAt hY (by simp)
  { exact := (K.obj Y).exact_iCycles_toCycles k (k + 1) (by simp)
    mono_f := inferInstanceAs (Mono ((K.obj Y).iCycles k))
    epi_g := inferInstanceAs (Epi ((K.obj Y).toCycles k (k + 1))) }

variable {P : Cᵒᵖ ⥤ A} {K} (ε : P ⋙ CochainComplex.single₀ A ⟶ K)

/-- The augmentation `P ⟶ K⁰` of the resolution. -/
private def augmentationι : P ⟶ K ⋙ HomologicalComplex.eval A _ 0 where
  app Y := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj Y)).inv ≫ (ε.app Y).f 0
  naturality Y Y' f := by
    have h := congr_arg (fun g ↦ HomologicalComplex.Hom.f g 0) (ε.naturality f)
    simp only [Functor.comp_map, HomologicalComplex.comp_f,
      HomologicalComplex.single_map_f_self] at h
    simp only [Functor.comp_map, HomologicalComplex.eval_map, Category.assoc, ← h,
      Iso.inv_hom_id_assoc]

/-- The sequence `0 ⟶ P ⟶ K⁰ ⟶ Z¹ ⟶ 0` of the augmented resolution. -/
private def augmentationSC : ShortComplex (Cᵒᵖ ⥤ A) :=
  ShortComplex.mk (augmentationι ε) (cyclesπ K 0) <|
    NatTrans.ext <| funext fun Y ↦ (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (HomologicalComplex.single_f_toCycles (ε.app Y) 1)).trans comp_zero

/-- The augmented sequence is short exact at every object `Y` at which `ε` is a
quasi-isomorphism. -/
private lemma augmentationSC_shortExact {Y : Cᵒᵖ} (hY : QuasiIso (ε.app Y)) :
    ((augmentationSC ε).map ((evaluation Cᵒᵖ A).obj Y)).ShortExact := by
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj Y)
  -- in degree `0`, `ε.app Y` identifies `P(Y)` with the kernel of `K⁰(Y) ⟶ K¹(Y)`
  obtain ⟨hexact, hmono⟩ := (ShortComplex.quasiIso_iff_of_zeros _
    (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) _ _ _ _)
    (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) _ _ _ _)
    ((K.obj Y).shape 0 0 (by simp))).1
      ((CochainComplex.quasiIsoAt₀_iff (ε.app Y)).1 (hY.quasiIsoAt 0))
  have h₁ : (K.obj Y).ExactAt 1 := (quasiIsoAt_iff_exactAt (ε.app Y) 1
    (CochainComplex.exactAt_succ_single_obj _ 0)).1 (hY.quasiIsoAt 1)
  have : Epi ((K.obj Y).toCycles 0 1) :=
    HomologicalComplex.epi_toCycles_of_exactAt h₁ (by simp)
  -- compare with the sequence `P(Y) ⟶ K⁰(Y) ⟶ K¹(Y)` whose exactness is `hexact`
  let φ : (augmentationSC ε).map ((evaluation Cᵒᵖ A).obj Y) ⟶ ShortComplex.mk ((ε.app Y).f 0)
      ((K.obj Y).d 0 1) (HomologicalComplex.single_f_d (ε.app Y) 1) :=
    { τ₁ := e.inv
      τ₂ := 𝟙 _
      τ₃ := (K.obj Y).iCycles 1
      comm₁₂ := (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans (HomologicalComplex.toCycles_i _ _ _).symm }
  -- the instances are passed explicitly: the degree `0` term of `single₀ (P(Y))` is `P(Y)` only up
  -- to unfolding, so instance search cannot match the components of `φ`
  exact
    { exact := (@ShortComplex.exact_iff_of_epi_of_isIso_of_mono _ _ _ _ _ φ
        (inferInstanceAs (Epi e.inv)) (inferInstanceAs (IsIso (𝟙 _)))
        (inferInstanceAs (Mono ((K.obj Y).iCycles 1)))).2 hexact
      mono_f := @mono_comp _ _ _ _ _ e.inv inferInstance ((ε.app Y).f 0) hmono
      epi_g := inferInstanceAs (Epi ((K.obj Y).toCycles 0 1)) }

end Resolution

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C)
  [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → ι)) A]

/-- **The Čech complexes of a coefficient sequence that is short exact on the members.** If a
sequence of presheaves becomes short exact after evaluation at every finite product
`U (a 0) × ⋯ × U (a n)` of members of the family `U`, then its sequence of Čech complexes for `U`
is short exact. No exactness is required at other objects: for an open cover, only the
intersections of members matter. -/
theorem shortExact_map_cechComplexFunctor (S : ShortComplex (Cᵒᵖ ⥤ A))
    (hS : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      (S.map ((evaluation Cᵒᵖ A).obj (op (∏ᶜ fun j ↦ U (a j))))).ShortExact) :
    (S.map (cechComplexFunctor U)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  -- in degree `n`, the sequence of Čech complexes is the product of the evaluations of `S`
  have h := (ShortComplex.shortExact_of_forall_evaluation (S.map ((Functor.whiskeringLeft
    (Discrete (Fin (n + 1) → ι)) Cᵒᵖ A).obj (Discrete.functor fun a ↦ op (∏ᶜ fun j ↦ U (a j)))))
      fun a ↦ hS n a.as).map_of_exact lim
  exact ShortComplex.shortExact_of_iso (S.mapNatIso (cechEvalIso U n).symm) h

variable {T : C} (hT : IsTerminal T)

/-- The augmentation is a morphism from the coefficient sequence, concentrated in degree zero,
to its sequence of Čech complexes. -/
private def cechAugmentationShortComplexHom (S : ShortComplex (Cᵒᵖ ⥤ A)) :
    S.map ((evaluation Cᵒᵖ A).obj (op T) ⋙
      HomologicalComplex.single A (ComplexShape.up ℕ) 0) ⟶
        S.map (cechComplexFunctor U) where
  τ₁ := cechAugmentation U hT S.X₁
  τ₂ := cechAugmentation U hT S.X₂
  τ₃ := cechAugmentation U hT S.X₃
  comm₁₂ := cechAugmentation_naturality U hT S.X₁ S.f
  comm₂₃ := cechAugmentation_naturality U hT S.X₂ S.g

/-- **Čech acyclicity descends to the kernel of a locally short exact coefficient sequence.**
If a sequence of presheaves is short exact at the terminal object and at every finite product of
members of `U`, and `U` is acyclic for the middle and right presheaves, then `U` is acyclic for the
left presheaf as well. Exactness at other objects is not required. -/
theorem quasiIso_cechAugmentation_of_shortExact (S : ShortComplex (Cᵒᵖ ⥤ A))
    (hST : (S.map ((evaluation Cᵒᵖ A).obj (op T))).ShortExact)
    (hSU : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      (S.map ((evaluation Cᵒᵖ A).obj (op (∏ᶜ fun j ↦ U (a j))))).ShortExact)
    (h₂ : QuasiIso (cechAugmentation U hT S.X₂))
    (h₃ : QuasiIso (cechAugmentation U hT S.X₃)) :
    QuasiIso (cechAugmentation U hT S.X₁) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₁ (cechAugmentationShortComplexHom U hT S)
    (hST.map_of_exact (HomologicalComplex.single A (ComplexShape.up ℕ) 0))
    (shortExact_map_cechComplexFunctor U S hSU) h₂ h₃

/-! ### Acyclic resolutions

For a sequence of presheaves `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` that is short exact at `T` and at the finite
products of members, with `X₂` acyclic, the augmented Čech complexes of `X₁` and `X₃` agree up to a
shift by one degree. Along the short exact sequences of cycles of a resolution by acyclic
presheaves, this shows that the resolved presheaf is acyclic. -/

section Resolution

variable {S : ShortComplex (Cᵒᵖ ⥤ A)}
  (hST : (S.map ((evaluation Cᵒᵖ A).obj (op T))).ShortExact)
  (hSU : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
    (S.map ((evaluation Cᵒᵖ A).obj (op (∏ᶜ fun j ↦ U (a j))))).ShortExact)

include hST hSU

/-- The source and the target of the augmentation of `S` are short exact sequences of complexes. -/
private lemma shortExact_map_single_and_cechComplexFunctor :
    (S.map ((evaluation Cᵒᵖ A).obj (op T) ⋙
      HomologicalComplex.single A (ComplexShape.up ℕ) 0)).ShortExact ∧
      (S.map (cechComplexFunctor U)).ShortExact :=
  ⟨hST.map_of_exact (HomologicalComplex.single A (ComplexShape.up ℕ) 0),
    shortExact_map_cechComplexFunctor U S hSU⟩

/-- In degree `0`, the augmentation of `X₁` is injective on cohomology if that of `X₂` is an
isomorphism. -/
private lemma mono_homologyMap_cechAugmentation_X₁_zero
    (h₂ : QuasiIsoAt (cechAugmentation U hT S.X₂) 0) :
    Mono (HomologicalComplex.homologyMap (cechAugmentation U hT S.X₁) 0) := by
  let φ := cechAugmentationShortComplexHom U hT S
  have : QuasiIsoAt φ.τ₂ 0 := h₂
  have := (quasiIsoAt_iff_isIso_homologyMap φ.τ₂ 0).1 this
  obtain ⟨hS₁, hS₂⟩ := shortExact_map_single_and_cechComplexFunctor U hST hSU
  exact HomologicalComplex.HomologySequence.mono_homologyMap_τ₁ φ hS₁ hS₂ 0
    (fun _ hi ↦ absurd hi (by simp)) (fun _ hi ↦ absurd hi (by simp)) inferInstance

/-- In degree `0`, the augmentation of `X₁` is a quasi-isomorphism if that of `X₂` is, and that of
`X₃` is injective on cohomology. -/
private lemma quasiIsoAt_cechAugmentation_X₁_zero
    (h₂ : QuasiIsoAt (cechAugmentation U hT S.X₂) 0)
    (h₃ : Mono (HomologicalComplex.homologyMap (cechAugmentation U hT S.X₃) 0)) :
    QuasiIsoAt (cechAugmentation U hT S.X₁) 0 := by
  let φ := cechAugmentationShortComplexHom U hT S
  have : QuasiIsoAt φ.τ₂ 0 := h₂
  have := (quasiIsoAt_iff_isIso_homologyMap φ.τ₂ 0).1 this
  obtain ⟨hS₁, hS₂⟩ := shortExact_map_single_and_cechComplexFunctor U hST hSU
  exact (quasiIsoAt_iff_isIso_homologyMap _ 0).2 <|
    HomologicalComplex.HomologySequence.isIso_homologyMap_τ₁ φ hS₁ hS₂ 0
      (fun _ hi ↦ absurd hi (by simp)) (fun _ hi ↦ absurd hi (by simp)) inferInstance h₃

/-- **Dimension shifting.** If the augmentation of `X₂` is a quasi-isomorphism, then the
augmentation of `X₁` is a quasi-isomorphism in degree `n + 1` as soon as that of `X₃` is one in
degree `n`. -/
private lemma quasiIsoAt_cechAugmentation_X₁_succ (h₂ : QuasiIso (cechAugmentation U hT S.X₂))
    {n : ℕ} (h₃ : QuasiIsoAt (cechAugmentation U hT S.X₃) n) :
    QuasiIsoAt (cechAugmentation U hT S.X₁) (n + 1) := by
  let φ := cechAugmentationShortComplexHom U hT S
  have : QuasiIso φ.τ₂ := h₂
  have (i : ℕ) : IsIso (HomologicalComplex.homologyMap φ.τ₂ i) :=
    (quasiIsoAt_iff_isIso_homologyMap φ.τ₂ i).1 inferInstance
  have : QuasiIsoAt φ.τ₃ n := h₃
  have := (quasiIsoAt_iff_isIso_homologyMap φ.τ₃ n).1 this
  obtain ⟨hS₁, hS₂⟩ := shortExact_map_single_and_cechComplexFunctor U hST hSU
  refine (quasiIsoAt_iff_isIso_homologyMap _ (n + 1)).2 <|
    HomologicalComplex.HomologySequence.isIso_homologyMap_τ₁ φ hS₁ hS₂ (n + 1)
      (fun _ _ ↦ inferInstance) (fun i hi ↦ ?_) inferInstance ?_
  · obtain rfl : i = n := by simpa using hi
    infer_instance
  · -- the cohomology of a complex concentrated in degree `0` vanishes in degree `n + 1`
    exact mono_of_source_iso_zero _
      (CochainComplex.exactAt_succ_single_obj (S.X₃.obj (op T)) n).isZero_homology.isoZero

omit hST hSU

/-- **Čech acyclicity from an acyclic resolution.** Let `ε : P ⋙ single₀ ⟶ K` be a morphism from
a presheaf `P`, placed in degree `0`, to a presheaf of cochain complexes `K`, which is a
quasi-isomorphism at `T` and at every finite product of members of the family `U`: for an open
cover, the sequence `0 ⟶ P ⟶ K⁰ ⟶ K¹ ⟶ ⋯` is exact on the whole space and on every finite
intersection of members. If every presheaf `Kᵏ` is acyclic for `U`, then so is `P`. -/
theorem quasiIso_cechAugmentation_of_resolution {P : Cᵒᵖ ⥤ A} {K : Cᵒᵖ ⥤ CochainComplex A ℕ}
    (ε : P ⋙ CochainComplex.single₀ A ⟶ K) (hεT : QuasiIso (ε.app (op T)))
    (hεU : ∀ (n : ℕ) (a : Fin (n + 1) → ι), QuasiIso (ε.app (op (∏ᶜ fun j ↦ U (a j)))))
    (hK : ∀ k, QuasiIso (cechAugmentation U hT (K ⋙ HomologicalComplex.eval A _ k))) :
    QuasiIso (cechAugmentation U hT P) := by
  -- the sequences of cycles are short exact at `T` and at the finite products of members
  have hexact {Y : Cᵒᵖ} (hY : QuasiIso (ε.app Y)) (k : ℕ) : (K.obj Y).ExactAt (k + 1) :=
    (quasiIsoAt_iff_exactAt (ε.app Y) (k + 1) (CochainComplex.exactAt_succ_single_obj _ k)).1
      (hY.quasiIsoAt (k + 1))
  have hcT (k : ℕ) := cyclesSC_shortExact K k (hexact hεT k)
  have hcU (k n : ℕ) (a : Fin (n + 1) → ι) := cyclesSC_shortExact K k (hexact (hεU n a) k)
  have haT := augmentationSC_shortExact ε hεT
  have haU (n : ℕ) (a : Fin (n + 1) → ι) := augmentationSC_shortExact ε (hεU n a)
  -- dimension shifting: in each degree, `P` and every presheaf of cycles are acyclic
  have key (n : ℕ) : QuasiIsoAt (cechAugmentation U hT P) n ∧ ∀ k,
      QuasiIsoAt (cechAugmentation U hT (K ⋙ HomologicalComplex.cyclesFunctor A _ (k + 1))) n := by
    induction n with
    | zero =>
      have hmono (k : ℕ) := mono_homologyMap_cechAugmentation_X₁_zero U hT (hcT (k + 1))
        (hcU (k + 1)) ((hK (k + 1)).quasiIsoAt 0)
      exact ⟨quasiIsoAt_cechAugmentation_X₁_zero U hT haT haU ((hK 0).quasiIsoAt 0) (hmono 0),
        fun k ↦ quasiIsoAt_cechAugmentation_X₁_zero U hT (hcT (k + 1)) (hcU (k + 1))
          ((hK (k + 1)).quasiIsoAt 0) (hmono (k + 1))⟩
    | succ n ih =>
      exact ⟨quasiIsoAt_cechAugmentation_X₁_succ U hT haT haU (hK 0) (ih.2 0),
        fun k ↦ quasiIsoAt_cechAugmentation_X₁_succ U hT (hcT (k + 1)) (hcU (k + 1)) (hK (k + 1))
          (ih.2 (k + 1))⟩
  rw [quasiIso_iff]
  exact fun n ↦ (key n).1

end Resolution

end TauCeti.CategoryTheory

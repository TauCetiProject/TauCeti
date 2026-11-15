/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Exact.BaseChange
public import TauCeti.CategoryTheory.Exact.Biproduct
public import TauCeti.CategoryTheory.Exact.Opposite
public import TauCeti.CategoryTheory.Exact.Split
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq
public import Mathlib.Tactic.TFAE

/-!
# Bicartesian squares in exact categories

A pushout of an inflation in an exact category is also a pullback.  Dually, a pullback of a
deflation is also a pushout.  Thus the base-change squares supplied by Quillen's E2 and E2op
axioms are bicartesian.  This file proves Bühler's characterization of these squares: for a
commutative square whose top map is an inflation, being a pushout, being bicartesian, having a
conflation as its biproduct sequence, and extending to a morphism of conflations which is the
identity on the cokernels are all equivalent.

The proof uses the standard biproduct criterion for a commutative square.  For a square

```text
W --f--> X
|        |
g        h
v        v
Y --i--> Z,
```

Mathlib identifies the pushout property with `Z` being the cokernel in the sequence

```text
W --(f,-g)--> X ⊞ Y --(h,i)--> Z.
```

When `f` is an inflation, `(f,-g)` is an inflation as well: it factors as the split graph
inclusion `(1,-g)` followed by `f ⊞ 1`.  Its distinguished cokernel is uniquely isomorphic to
the pushout cokernel, so the displayed sequence is a conflation.  Its kernel property is exactly
the pullback property.  The statement for deflations follows by passing to the opposite exact
category.

Conversely, a morphism of conflations `φ : S ⟶ T` which is invertible on the cokernels has a
pushout as its left square; dually, one which is invertible on the kernels has a pullback as its
right square.  Since a pushout of an isomorphism is an isomorphism, this yields the short five
lemma for conflations: a morphism of conflations invertible on the kernels and the cokernels is
invertible in the middle.

## Main results

* `TauCeti.ExactStructure.conflation_shortComplex_of_isPushout_of_isInflation` packages a
  pushout of an inflation as its associated conflation.
* `TauCeti.ExactStructure.isPullback_of_isPushout_of_isInflation` proves that such a pushout is
  also a pullback.
* `TauCeti.ExactStructure.isPushout_of_isPullback_of_isDeflation` is the dual statement.
* `TauCeti.ExactStructure.bicartesianSq_of_isPushout_of_isInflation` and
  `TauCeti.ExactStructure.bicartesianSq_of_isPullback_of_isDeflation` bundle the conclusions as
  `CategoryTheory.BicartesianSq`.
* `TauCeti.ExactStructure.conflation_shortComplex_iff_isPushout` and
  `TauCeti.ExactStructure.conflation_shortComplex'_iff_isPullback`: the biproduct criterion as an
  equivalence along an inflation, respectively a deflation.
* `TauCeti.ExactStructure.isPushout_of_conflation_of_isIso₃` and
  `TauCeti.ExactStructure.isPullback_of_conflation_of_isIso₁`: a morphism of conflations which
  is invertible on the cokernels has a pushout as its left square, and one which is invertible on
  the kernels has a pullback as its right square.
* `TauCeti.ExactStructure.isIso₂_of_conflation_of_isIso₁₃`: the short five lemma.
* `TauCeti.ExactStructure.tfae_isPushout_of_isInflation` and
  `TauCeti.ExactStructure.tfae_isPullback_of_isDeflation`: the bicartesian characterization of
  pushouts along inflations and of pullbacks along deflations.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Proposition 2.12 and Corollary 3.2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace ConflationClass

variable [HasBinaryBiproducts C]

/-- A commutative square whose biproduct short complex `W ⟶ X ⊞ Y ⟶ Z` is a conflation is a
pushout square: the second map of a conflation is a cokernel of the first. -/
theorem isPushout_of_conflation_shortComplex (E : ConflationClass C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq f g h i) (hS : E.Conflation sq.shortComplex) :
    IsPushout f g h i :=
  IsPushout.of_isColimit' sq
    (sq.isColimitEquivIsColimitCokernelCofork.symm (E.isKernelCokernelPair _ hS).gIsCokernel)

/-- A commutative square whose biproduct short complex `W ⟶ X ⊞ Y ⟶ Z`, with maps `(f,g)` and
`(h,-i)`, is a conflation is a pullback square: the first map of a conflation is a kernel of the
second. -/
theorem isPullback_of_conflation_shortComplex' (E : ConflationClass C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq f g h i) (hS : E.Conflation sq.shortComplex') :
    IsPullback f g h i :=
  IsPullback.of_isLimit' sq
    (sq.isLimitEquivIsLimitKernelFork.symm (E.isKernelCokernelPair _ hS).fIsKernel)

end ConflationClass

namespace ExactStructure

variable [HasZeroObject C] [HasBinaryBiproducts C]

/-- The elementary triangular automorphism sending the graph of `-g` to the first biproduct
inclusion. -/
private noncomputable def graphIso {W Y : C} (g : W ⟶ Y) : W ⊞ Y ≅ W ⊞ Y where
  hom := biprod.desc (biprod.inl + g ≫ biprod.inr) biprod.inr
  inv := biprod.desc (biprod.inl - g ≫ biprod.inr) biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext <;> simp
    · apply biprod.hom_ext <;> simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext <;> simp
    · apply biprod.hom_ext <;> simp

/-- The graph map `(1, -g) : W ⟶ W ⊞ Y` is an inflation in every exact structure. -/
private theorem isInflation_graph (E : ExactStructure C) {W Y : C} (g : W ⟶ Y) :
    E.IsInflation (biprod.lift (𝟙 W) (-g)) := by
  apply E.isInflation_of_split_isInflation
  rw [split_isInflation_iff]
  exact ⟨Y, graphIso g, by simp [graphIso]⟩

/-- For a commutative square whose top map is an inflation, the first map `(f,-g)` of the
associated biproduct short complex is again an inflation. -/
private theorem isInflation_shortComplex_f (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq f g h i) (hf : E.IsInflation f) : E.IsInflation sq.shortComplex.f := by
  have hgraph : E.IsInflation (biprod.lift (𝟙 W) (-g)) := isInflation_graph E g
  have hsum : E.IsInflation (biprod.map f (𝟙 Y)) := E.isInflation_biprod_id hf Y
  have hfac : biprod.lift (𝟙 W) (-g) ≫ biprod.map f (𝟙 Y) =
      biprod.lift f (-g) := by
    apply biprod.hom_ext <;> simp
  -- Rewriting cannot key through the unexposed `IsInflation` abbreviation.
  change E.inflations (biprod.lift f (-g))
  rw [← hfac]
  exact E.isInflation_comp _ _ hgraph hsum

/-- The sign change on the second summand of a binary biproduct. -/
private noncomputable def biprodSignIso (X Y : C) : X ⊞ Y ≅ X ⊞ Y where
  hom := biprod.map (𝟙 X) (-𝟙 Y)
  inv := biprod.map (𝟙 X) (-𝟙 Y)
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

/-- Changing the sign of the lower-left map converts the cokernel convention for a square into
the kernel convention. -/
private noncomputable def shortComplexIso
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq f g h i) : sq.shortComplex ≅ sq.shortComplex' :=
  ShortComplex.isoMk (Iso.refl _) (biprodSignIso X Y) (Iso.refl _)
    (by
      dsimp [CommSq.shortComplex, CommSq.shortComplex', biprodSignIso]
      apply biprod.hom_ext <;> simp [Category.assoc])
    (by
      dsimp [CommSq.shortComplex, CommSq.shortComplex', biprodSignIso]
      apply biprod.hom_ext' <;> simp)

/-- The biproduct short complex associated to a pushout square of an inflation is a
conflation.

Its maps are `(f,-g) : W ⟶ X ⊞ Y` and `(h,i) : X ⊞ Y ⟶ Z`.  This is the
kernel--cokernel sequence underlying the bicartesian-square criterion. -/
theorem conflation_shortComplex_of_isPushout_of_isInflation (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (hf : E.IsInflation f) (hsq : IsPushout f g h i) :
    E.Conflation hsq.toCommSq.shortComplex := by
  let sq := hsq.toCommSq
  have hfirst : E.IsInflation sq.shortComplex.f := E.isInflation_shortComplex_f sq hf
  obtain ⟨Q, q, hq, hT⟩ :=
    (ConflationClass.isInflation_iff E.toConflationClass sq.shortComplex.f).mp hfirst
  let T := ShortComplex.mk sq.shortComplex.f q hq
  have hT' : E.Conflation T := by simpa [T] using hT
  have hpairT : IsKernelCokernelPair T := E.isKernelCokernelPair T hT'
  have hpushoutCokernel : IsColimit sq.cokernelCofork := hsq.isColimitCokernelCofork
  let e : Q ≅ Z :=
    IsColimit.coconePointUniqueUpToIso hpairT.gIsCokernel hpushoutCokernel
  have he : q ≫ e.hom = sq.shortComplex.g :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hpairT.gIsCokernel hpushoutCokernel
      WalkingParallelPair.one
  exact E.conflation_of_iso (S := T) (T := sq.shortComplex)
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e
      (by dsimp [T]; rw [Category.id_comp, Category.comp_id])
      (by dsimp [T]; rw [Category.id_comp]; exact he.symm)) hT'

/-- **A pushout square of an inflation in an exact category is a pullback square.** -/
theorem isPullback_of_isPushout_of_isInflation (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (hf : E.IsInflation f) (hsq : IsPushout f g h i) :
    IsPullback f g h i := by
  let sq := hsq.toCommSq
  have hconflation := E.conflation_shortComplex_of_isPushout_of_isInflation hf hsq
  have hpair := E.isKernelCokernelPair sq.shortComplex hconflation
  have hpair' : IsKernelCokernelPair sq.shortComplex' :=
    hpair.of_iso (shortComplexIso sq)
  exact IsPullback.of_isLimit' sq
    (sq.isLimitEquivIsLimitKernelFork.symm hpair'.fIsKernel)

/-- A pushout square of an inflation, bundled as a bicartesian square. -/
theorem bicartesianSq_of_isPushout_of_isInflation (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (hf : E.IsInflation f) (hsq : IsPushout f g h i) :
    BicartesianSq f g h i :=
  BicartesianSq.of_isPullback_isPushout
    (E.isPullback_of_isPushout_of_isInflation hf hsq) hsq

/-- **A pullback square of a deflation in an exact category is a pushout square.** -/
theorem isPushout_of_isPullback_of_isDeflation (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (hh : E.IsDeflation h) (hsq : IsPullback f g h i) :
    IsPushout f g h i := by
  have hop : IsPushout h.op i.op f.op g.op := hsq.op.flip
  have hhop : E.op.IsInflation h.op := by simpa using hh
  have hpull : IsPullback h.op i.op f.op g.op :=
    E.op.isPullback_of_isPushout_of_isInflation hhop hop
  simpa using hpull.unop.flip

/-- A pullback square of a deflation, bundled as a bicartesian square. -/
theorem bicartesianSq_of_isPullback_of_isDeflation (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (hh : E.IsDeflation h) (hsq : IsPullback f g h i) :
    BicartesianSq f g h i :=
  BicartesianSq.of_isPullback_isPushout hsq
    (E.isPushout_of_isPullback_of_isDeflation hh hsq)

/-! ### The bicartesian characterization -/

/-- The biproduct short complex `W ⟶ X ⊞ Y ⟶ Z`, with maps `(f,g)` and `(h,-i)`, of a pullback
square of a deflation `h` is a conflation. -/
theorem conflation_shortComplex'_of_isPullback_of_isDeflation (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (hh : E.IsDeflation h) (hsq : IsPullback f g h i) :
    E.Conflation hsq.toCommSq.shortComplex' := by
  have hfac : biprod.map h (𝟙 Y) ≫ biprod.desc (𝟙 Z) (-i) = biprod.desc h (-i) := by
    apply biprod.hom_ext' <;> simp
  have hg : E.IsDeflation (biprod.desc h (-i)) := by
    -- Rewriting cannot key through the unexposed `IsDeflation` abbreviation.
    change E.deflations (biprod.desc h (-i))
    rw [← hfac]
    exact E.isDeflation_comp _ _ (E.isDeflation_biprod_id hh Y)
      (E.isDeflation_of_split_isDeflation (split_isDeflation_biprod_desc_id_left (-i)))
  exact E.conflation_of_isLimit_of_isDeflation hsq.isLimitKernelFork hg

/-- For a commutative square whose top map `f` is an inflation, the biproduct short complex
`W ⟶ X ⊞ Y ⟶ Z` is a conflation exactly when the square is a pushout. -/
theorem conflation_shortComplex_iff_isPushout (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq f g h i) (hf : E.IsInflation f) :
    E.Conflation sq.shortComplex ↔ IsPushout f g h i :=
  ⟨E.isPushout_of_conflation_shortComplex sq,
    E.conflation_shortComplex_of_isPushout_of_isInflation hf⟩

/-- For a commutative square whose right map `h` is a deflation, the biproduct short complex
`W ⟶ X ⊞ Y ⟶ Z`, with maps `(f,g)` and `(h,-i)`, is a conflation exactly when the square is a
pullback. -/
theorem conflation_shortComplex'_iff_isPullback (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq f g h i) (hh : E.IsDeflation h) :
    E.Conflation sq.shortComplex' ↔ IsPullback f g h i :=
  ⟨E.isPullback_of_conflation_shortComplex' sq,
    E.conflation_shortComplex'_of_isPullback_of_isDeflation hh⟩

/-- **A morphism of conflations which is invertible on the cokernels has a pushout as its left
square.** If `φ : S ⟶ T` is a morphism of conflations with `φ.τ₃` an isomorphism, then the
square formed by `S.f`, `φ.τ₁`, `φ.τ₂` and `T.f` is a pushout. -/
theorem isPushout_of_conflation_of_isIso₃ (E : ExactStructure C) {S T : ShortComplex C}
    (φ : S ⟶ T) (hS : E.Conflation S) (hT : E.Conflation T) [IsIso φ.τ₃] :
    IsPushout S.f φ.τ₁ φ.τ₂ T.f := by
  -- Pull `S` back along `T.g ≫ (φ.τ₃)⁻¹` to a conflation `S.X₁ ⟶ P ⟶ T.X₂`. A cocone on the
  -- span `S.X₂ ⟵ S.X₁ ⟶ T.X₁` gives a map out of `P` vanishing on `S.X₁`, which descends along
  -- the deflation `P ⟶ T.X₂` to the required map out of `T.X₂`.
  have hpairT := E.isKernelCokernelPair T hT
  have := hpairT.mono_f
  have : HasPullback S.g (T.g ≫ inv φ.τ₃) :=
    E.hasPullbacks_deflations.hasPullback _ (E.isDeflation_g hS)
  have sq : IsPullback (pullback.fst S.g (T.g ≫ inv φ.τ₃)) (pullback.snd S.g (T.g ≫ inv φ.τ₃))
      S.g (T.g ≫ inv φ.τ₃) := IsPullback.of_hasPullback _ _
  set p₁ := pullback.fst S.g (T.g ≫ inv φ.τ₃)
  set p₂ := pullback.snd S.g (T.g ≫ inv φ.τ₃)
  have hB := E.conflation_baseChange hS sq
  rw [baseChange_def] at hB
  have hpairB := E.isKernelCokernelPair _ hB
  have := hpairB.epi_g
  -- The difference `p₂ - p₁ ≫ φ.τ₂ : P ⟶ T.X₂` lies in the kernel `T.X₁` of `T.g`.
  have hd : (p₂ - p₁ ≫ φ.τ₂) ≫ T.g = 0 := by
    have hw : p₁ ≫ S.g ≫ φ.τ₃ = p₂ ≫ T.g := by
      rw [← Category.assoc, sq.w]
      simp
    rw [Preadditive.sub_comp, Category.assoc, φ.comm₂₃, hw, sub_self]
  set δ := hpairT.lift _ hd
  have hδ : δ ≫ T.f = p₂ - p₁ ≫ φ.τ₂ := hpairT.lift_f _ hd
  have hιδ : baseChangeι S sq ≫ δ = -φ.τ₁ := by
    rw [← cancel_mono T.f, Category.assoc, hδ, Preadditive.neg_comp, φ.comm₁₂]
    simp
  -- The section `(𝟙, φ.τ₂) : S.X₂ ⟶ P` and the inclusion `(0, T.f) : T.X₁ ⟶ P`.
  have hσ : 𝟙 S.X₂ ≫ S.g = φ.τ₂ ≫ T.g ≫ inv φ.τ₃ := by
    rw [reassoc_of% φ.comm₂₃]
    simp
  have hσδ : sq.lift (𝟙 S.X₂) φ.τ₂ hσ ≫ δ = 0 := by
    rw [← cancel_mono T.f, Category.assoc, hδ]
    simp
  have ht : (0 : T.X₁ ⟶ S.X₂) ≫ S.g = T.f ≫ T.g ≫ inv φ.τ₃ := by simp
  have htδ : sq.lift 0 T.f ht ≫ δ = 𝟙 T.X₁ := by
    rw [← cancel_mono T.f, Category.assoc, hδ]
    simp
  refine IsPushout.of_isColimit' ⟨φ.comm₁₂.symm⟩ (PushoutCocone.IsColimit.mk _
    (fun s => hpairB.desc (p₁ ≫ s.inl + δ ≫ s.inr) ?_) (fun s => ?_) (fun s => ?_)
    (fun s m hm₁ hm₂ => ?_))
  · simp only [Preadditive.comp_add, baseChangeι_fst_assoc, reassoc_of% hιδ,
      Preadditive.neg_comp, s.condition, add_neg_cancel]
  · have h₂ : φ.τ₂ = sq.lift (𝟙 S.X₂) φ.τ₂ hσ ≫ p₂ := (sq.lift_snd _ _ _).symm
    rw [h₂, Category.assoc, hpairB.g_desc, Preadditive.comp_add, reassoc_of% hσδ,
      sq.lift_fst_assoc]
    simp
  · have h₂ : T.f = sq.lift 0 T.f ht ≫ p₂ := (sq.lift_snd _ _ _).symm
    rw [h₂, Category.assoc, hpairB.g_desc, Preadditive.comp_add, reassoc_of% htδ,
      sq.lift_fst_assoc]
    simp
  · rw [← cancel_epi p₂, hpairB.g_desc]
    have hp₂ : p₂ = δ ≫ T.f + p₁ ≫ φ.τ₂ := by rw [hδ]; abel
    rw [hp₂, Preadditive.add_comp, Category.assoc, Category.assoc, hm₁, hm₂, add_comm]

/-- **A morphism of conflations which is invertible on the kernels has a pullback as its right
square.** If `φ : S ⟶ T` is a morphism of conflations with `φ.τ₁` an isomorphism, then the
square formed by `φ.τ₂`, `S.g`, `T.g` and `φ.τ₃` is a pullback. -/
theorem isPullback_of_conflation_of_isIso₁ (E : ExactStructure C) {S T : ShortComplex C}
    (φ : S ⟶ T) (hS : E.Conflation S) (hT : E.Conflation T) [IsIso φ.τ₁] :
    IsPullback φ.τ₂ S.g T.g φ.τ₃ := by
  have : IsIso (ShortComplex.opMap φ).τ₃ := by
    rw [ShortComplex.opMap_τ₃]
    exact inferInstanceAs (IsIso (φ.τ₁).op)
  exact (E.op.isPushout_of_conflation_of_isIso₃ (ShortComplex.opMap φ)
    ((E.op_conflation_op_iff T).2 hT) ((E.op_conflation_op_iff S).2 hS)).unop.flip

/-- **The short five lemma in an exact category.** A morphism of conflations which is invertible
on the kernels and on the cokernels is invertible on the middle terms. -/
theorem isIso₂_of_conflation_of_isIso₁₃ (E : ExactStructure C) {S T : ShortComplex C}
    (φ : S ⟶ T) (hS : E.Conflation S) (hT : E.Conflation T) [IsIso φ.τ₁] [IsIso φ.τ₃] :
    IsIso φ.τ₂ :=
  (E.isPushout_of_conflation_of_isIso₃ φ hS hT).isIso_inl_of_isIso

/-- **The bicartesian characterization of pushouts along an inflation.** For a commutative square
whose top map `f` is an inflation, the following are equivalent:
1. the square is a pushout;
2. the biproduct short complex `W ⟶ X ⊞ Y ⟶ Z` is a conflation;
3. the square is bicartesian;
4. the bottom map `i` is an inflation with a cokernel `q`, and `f` has the cokernel `h ≫ q`; that
   is, the square is the left half of a morphism of conflations which is the identity on the
   cokernels. -/
theorem tfae_isPushout_of_isInflation (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq f g h i) (hf : E.IsInflation f) :
    List.TFAE [IsPushout f g h i, E.Conflation sq.shortComplex, BicartesianSq f g h i,
      ∃ (V : C) (p : X ⟶ V) (q : Z ⟶ V) (hp : f ≫ p = 0) (hq : i ≫ q = 0),
        E.Conflation (ShortComplex.mk f p hp) ∧ E.Conflation (ShortComplex.mk i q hq) ∧
          h ≫ q = p] := by
  tfae_have 1 ↔ 2 := (E.conflation_shortComplex_iff_isPushout sq hf).symm
  tfae_have 1 → 3 := E.bicartesianSq_of_isPushout_of_isInflation hf
  tfae_have 3 → 1 := BicartesianSq.toIsPushout
  tfae_have 1 → 4 := fun hsq => by
    obtain ⟨V, p, hp, hS⟩ := (ConflationClass.isInflation_iff E.toConflationClass f).mp hf
    have hT := E.conflation_cobaseChange hS (S := ShortComplex.mk f p hp) hsq
    rw [cobaseChange_def] at hT
    exact ⟨V, p, _, hp, _, hS, hT, inl_cobaseChangeπ (ShortComplex.mk f p hp) hsq⟩
  tfae_have 4 → 1 := fun ⟨V, p, q, hp, hq, hS, hT, hhq⟩ =>
    E.isPushout_of_conflation_of_isIso₃
      { τ₁ := g, τ₂ := h, τ₃ := 𝟙 V, comm₁₂ := sq.w.symm, comm₂₃ := by simp [hhq] } hS hT
  tfae_finish

/-- **The bicartesian characterization of pullbacks along a deflation.** For a commutative square
whose right map `h` is a deflation, the following are equivalent:
1. the square is a pullback;
2. the biproduct short complex `W ⟶ X ⊞ Y ⟶ Z`, with maps `(f,g)` and `(h,-i)`, is a conflation;
3. the square is bicartesian;
4. the left map `g` is a deflation with a kernel `k`, and `h` has the kernel `k ≫ f`; that is,
   the square is the right half of a morphism of conflations which is the identity on the
   kernels. -/
theorem tfae_isPullback_of_isDeflation (E : ExactStructure C)
    {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq f g h i) (hh : E.IsDeflation h) :
    List.TFAE [IsPullback f g h i, E.Conflation sq.shortComplex', BicartesianSq f g h i,
      ∃ (U : C) (k : U ⟶ W) (l : U ⟶ X) (hk : k ≫ g = 0) (hl : l ≫ h = 0),
        E.Conflation (ShortComplex.mk k g hk) ∧ E.Conflation (ShortComplex.mk l h hl) ∧
          k ≫ f = l] := by
  tfae_have 1 ↔ 2 := (E.conflation_shortComplex'_iff_isPullback sq hh).symm
  tfae_have 1 → 3 := E.bicartesianSq_of_isPullback_of_isDeflation hh
  tfae_have 3 → 1 := BicartesianSq.toIsPullback
  tfae_have 1 → 4 := fun hsq => by
    obtain ⟨U, l, hl, hT⟩ := (ConflationClass.isDeflation_iff E.toConflationClass h).mp hh
    have hS := E.conflation_baseChange hT (S := ShortComplex.mk l h hl) hsq
    rw [baseChange_def] at hS
    exact ⟨U, _, l, _, hl, hS, hT, baseChangeι_fst (ShortComplex.mk l h hl) hsq⟩
  tfae_have 4 → 1 := fun ⟨U, k, l, hk, hl, hS, hT, hkl⟩ =>
    E.isPullback_of_conflation_of_isIso₁
      { τ₁ := 𝟙 U, τ₂ := f, τ₃ := i, comm₁₂ := by simp [hkl], comm₂₃ := sq.w } hS hT
  tfae_finish

end ExactStructure

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Scheme
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic

/-!
# Scheme-theoretic torsor squares for homogeneous quotients

If the fppf quotient `G/N` is represented by a scheme `X`, the kernel pair of the
quotient projection is `G × N`, with maps `(g, n) ↦ g` and `(g, n) ↦ gn`.
This is a pullback of schemes, not just an assertion about geometric points. More generally,
a lift of `T ⟶ X` to `G` identifies its pullback of `G` with `T × N`. The lifts needed for
this comparison exist fppf locally by local surjectivity of the quotient sheaf projection.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H)

local notation "G" => Scheme.asOver (Spec (CommRingCat.of H)) (Spec (CommRingCat.of R))
local notation "N" =>
  Scheme.asOver (Spec (CommRingCat.of (quotient H I))) (Spec (CommRingCat.of R))

/-- The closed subgroup inclusion with its relative spectrum endpoints, so that multiplication
and the affine point equivalences use the same presentation of the ambient group. -/
private def subgroupIncl : N ⟶ G := (quotientSpecι H I).hom.hom

/-- Right multiplication on `Spec H` by its closed subgroup `Spec (H ⧸ I)`. -/
def quotientSpecRightMul : G ⊗ N ⟶ G :=
  fst G N * (snd G N ≫ subgroupIncl H I)

/-- The right multiplication map multiplies the first factor by the included second factor. -/
theorem quotientSpecRightMul_def :
    let i : N ⟶ G := (quotientSpecι H I).hom.hom
    quotientSpecRightMul H I = fst G N * (snd G N ≫ i) := (rfl)

private theorem comp_quotientSpecRightMul' {T : Over (Spec (CommRingCat.of R))} (t : T ⟶ G ⊗ N) :
    t ≫ quotientSpecRightMul H I = (t ≫ fst G N) * ((t ≫ snd G N) ≫ subgroupIncl H I) := by
  simp only [quotientSpecRightMul, MonObj.comp_mul, Category.assoc]

private theorem mapMulEquiv_comp_quotientSpecι {A : CommAlgCat.{u} R}
    (n : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    Spec.mapMulEquiv n ≫ subgroupIncl H I =
      Spec.mapMulEquiv (quotientPointsHom H I A n) := by
  rw [subgroupIncl, quotientSpecι_def]
  symm
  exact mapMulEquiv_mapDomain A (mkQuotient H I).hom n

variable {X : Over (Spec (CommRingCat.of R))}
  (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)

private theorem exists_quotientSpecRightMul_lift {A : CommAlgCat.{u} R}
    {g g' : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ G}
    (h : g ≫ representedQuotientProjection H I e = g' ≫ representedQuotientProjection H I e) :
    ∃ t : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ G ⊗ N,
      t ≫ fst G N = g ∧ t ≫ quotientSpecRightMul H I = g' := by
  obtain ⟨g, rfl⟩ := Spec.mapMulEquiv.surjective g
  obtain ⟨g', rfl⟩ := Spec.mapMulEquiv.surjective g'
  obtain ⟨n, hn⟩ := (mapMulEquiv_comp_representedQuotientProjection_eq_iff H I e g g').mp h
  refine ⟨lift (Spec.mapMulEquiv g) (Spec.mapMulEquiv n), lift_fst _ _, ?_⟩
  rw [comp_quotientSpecRightMul', lift_fst, lift_snd, mapMulEquiv_comp_quotientSpecι,
    ← map_mul, hn, mul_inv_cancel_left]

private theorem quotientSpecRightMul_comp_projection {A : CommAlgCat.{u} R}
    (t : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ G ⊗ N) :
    (t ≫ quotientSpecRightMul H I) ≫ representedQuotientProjection H I e =
      (t ≫ fst G N) ≫ representedQuotientProjection H I e := by
  obtain ⟨g, hg⟩ := Spec.mapMulEquiv.surjective (t ≫ fst G N)
  obtain ⟨n, hn⟩ := Spec.mapMulEquiv.surjective (t ≫ snd G N)
  rw [comp_quotientSpecRightMul', ← hg, ← hn, mapMulEquiv_comp_quotientSpecι, ← map_mul]
  exact mapMulEquiv_mul_comp_representedQuotientProjection H I e g
    ⟨quotientPointsHom H I A n, quotientPointsHom_mem_quotientPointsSubgroup H I A n⟩

/-- The right multiplication square for a represented homogeneous quotient is cartesian in
schemes over the base. No flatness or reducedness is required for the kernel pair. -/
theorem isPullback_representedQuotientProjection_rightMul :
    IsPullback (fst G N) (quotientSpecRightMul H I)
      (representedQuotientProjection H I e) (representedQuotientProjection H I e) := by
  let F := CommAlgCat.pointsSheafFunctor R ⋙
    sheafToPresheaf (CommAlgCat.fppfTopology R) (Type (u + 1))
  -- Full faithfulness on affine test schemes lets the pointwise coset criterion detect
  -- the scheme pullback, including on nonreduced test algebras.
  apply IsPullback.of_map_of_faithful F
  apply IsPullback.of_forall_isPullback_app
  intro A
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext ⟨t⟩
    exact congrArg ULift.up (quotientSpecRightMul_comp_projection H I e (A := A.unop.unop) t).symm
  · rintro ⟨s⟩ ⟨t⟩ ⟨h₁, h₂⟩
    have h₁' : s ≫ fst G N = t ≫ fst G N := congrArg ULift.down h₁
    have h₂' : s ≫ quotientSpecRightMul H I = t ≫ quotientSpecRightMul H I :=
      congrArg ULift.down h₂
    rw [comp_quotientSpecRightMul', comp_quotientSpecRightMul', h₁'] at h₂'
    have : Mono (subgroupIncl H I).left :=
      inferInstanceAs (Mono (quotientSpecι H I).hom.hom.left)
    have := Over.mono_of_mono_left (subgroupIncl H I)
    have hsnd : s ≫ snd G N = t ≫ snd G N :=
      (cancel_mono (subgroupIncl H I)).mp (mul_left_cancel h₂')
    exact congrArg ULift.up (CartesianMonoidalCategory.hom_ext s t h₁' hsnd)
  · rintro ⟨g⟩ ⟨g'⟩ hg
    obtain ⟨t, ht, ht'⟩ := exists_quotientSpecRightMul_lift H I e (A := A.unop.unop)
      (congrArg ULift.down hg)
    exact ⟨ULift.up t, congrArg ULift.up ht, congrArg ULift.up ht'⟩

/-- The pullback of a represented homogeneous quotient along a point `a : T ⟶ X`
with lift `s : T ⟶ G` is the trivial family `T × N ⟶ T`. Its map to `G` takes
`(t, n)` to `s(t)n`. -/
theorem isPullback_representedQuotientProjection_of_lift {T : Over (Spec (CommRingCat.of R))}
    {a : T ⟶ X} (s : T ⟶ G) (hs : s ≫ representedQuotientProjection H I e = a) :
    IsPullback (fst T N) ((s ⊗ₘ 𝟙 N) ≫ quotientSpecRightMul H I) a
      (representedQuotientProjection H I e) := by
  subst a
  have h : IsPullback (fst T N) (s ⊗ₘ 𝟙 N) s (fst G N) := by
    -- Compare the Cartesian monoidal products with the limit products used by the base-change
    -- lemma. Both comparisons are determined by the projections.
    let c (U : Over (Spec (CommRingCat.of R))) : LimitCone (pair U N) :=
      ⟨_, tensorProductIsBinaryProduct U N⟩
    let i (U : Over (Spec (CommRingCat.of R))) : U ⊗ N ≅ U ⨯ N := (limit.isoLimitCone (c U)).symm
    have hf (U : Over (Spec (CommRingCat.of R))) : (i U).hom ≫ Limits.prod.fst = fst U N :=
      limit.isoLimitCone_inv_π (c U) ⟨WalkingPair.left⟩
    have hg (U : Over (Spec (CommRingCat.of R))) : (i U).hom ≫ Limits.prod.snd = snd U N :=
      limit.isoLimitCone_inv_π (c U) ⟨WalkingPair.right⟩
    refine (IsPullback.of_prod_fst_with_id s N).of_iso' (i T) (.refl _) (i G) (.refl _) ?_ ?_ ?_ ?_
    · simpa using hf T
    · apply Limits.prod.hom_ext
      · simp only [Category.assoc, Limits.prod.map_fst, ← Category.assoc (i T).hom,
          hf, tensorHom_fst]
      · simp only [Category.assoc, Limits.prod.map_snd, Category.comp_id, hg, tensorHom_snd]
    · simp
    · simpa using hf G
  simpa only [Category.assoc] using
    (h.flip.paste_horiz (isPullback_representedQuotientProjection_rightMul H I e).flip).flip

end CommHopfAlgCat

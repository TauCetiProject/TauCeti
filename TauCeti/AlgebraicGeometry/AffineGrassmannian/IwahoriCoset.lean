/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.Preimage
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Iwahori cosets and the fibre over the positive-loop coset

For an affine group `G` and a closed subgroup `B`, let `I` be the inverse image of `B`
under evaluation at zero on positive loops. This file constructs the presheaf of literal
left cosets `LG/I`. Its subfunctor of cosets admitting a positive-loop representative is
naturally `G/B`: reduction gives one direction, and constant loops give the inverse.
The projection to literal positive-loop cosets has precisely this subfunctor as its
identity fibre. Translation describes the fibre over any loop coset as well.

All coefficient algebras are allowed, including nonreduced algebras. Laurent series use
the coefficientwise algebra structure `HahnSeries.instAlgebra`, as do the loop-group APIs.
These are pointwise coset statements, before sheafification.

The construction uses the preimage API of `LoopGroup.Preimage` and the homogeneous quotient
presheaf of `Fppf.Quotient.Homogeneous.Basic`. For the geometric interpretation see
Pappas–Rapoport, *Twisted loop groups and their affine flag varieties*, §1.b, and
Zhu, *An introduction to affine Grassmannians and the geometric Satake equivalence*, §1.4.
-/

public section

open CategoryTheory Opposite WithConv

universe u

noncomputable section

-- Match the coefficientwise algebra used by the loop-group functors.
attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti.AffineGrassmannian

open TauCeti.HopfAlgebra

variable {k : Type u} [CommRing k] (H : _root_.CommHopfAlgCat.{u} k) (J : HopfIdeal k H)

/-- The image in `LG(R)` of the inverse image of `B(R)` under reduction at zero. -/
noncomputable def iwahoriLoopSubgroup (R : CommAlgCat.{u} k) :
    Subgroup ((loopGroup k H).obj R) :=
  (positiveLoopPreimage H J R).map ((positiveLoopToLoop k H).app R).hom

/-- A loop belongs to the Iwahori subgroup exactly when it is the image of a positive
loop whose reduction belongs to the closed subgroup. -/
theorem mem_iwahoriLoopSubgroup_iff (R : CommAlgCat.{u} k)
    (g : (loopGroup k H).obj R) :
    g ∈ iwahoriLoopSubgroup H J R ↔
      ∃ a ∈ positiveLoopPreimage H J R, ((positiveLoopToLoop k H).app R).hom a = g :=
  Iff.rfl

/-- The literal left cosets of the Iwahori subgroup in the loop group. -/
abbrev IwahoriCoset (R : CommAlgCat.{u} k) :=
  (loopGroup k H).obj R ⧸ iwahoriLoopSubgroup H J R

/-- Inclusion into loops detects membership in the preimage subgroup. -/
@[simp]
theorem positiveLoopToLoop_mem_iwahoriLoopSubgroup (R : CommAlgCat.{u} k)
    (a : WithConv (H →ₐ[k] PowerSeries R)) :
    dsimp% ((positiveLoopToLoop k H).app R).hom a ∈ iwahoriLoopSubgroup H J R ↔
      a ∈ positiveLoopPreimage H J R :=
  Subgroup.mem_map_iff_mem (positiveLoopToLoop_app_injective k H R)

/-- Coefficient maps carry the Iwahori subgroup into the Iwahori subgroup. -/
theorem map_mem_iwahoriLoopSubgroup {R S : CommAlgCat.{u} k} (f : R ⟶ S)
    {a : (loopGroup k H).obj R} (ha : a ∈ iwahoriLoopSubgroup H J R) :
    (loopGroup k H).map f a ∈ iwahoriLoopSubgroup H J S := by
  obtain ⟨b, hb, rfl⟩ := ha
  have hn := congrArg (fun m ↦ m.hom b) ((positiveLoopToLoop k H).naturality f)
  exact ⟨(positiveLoopGroup k H).map f b,
    mapValue_mem_positiveLoopPreimage f.hom hb, hn⟩

/-- The presheaf of literal left Iwahori cosets on affine `k`-algebras. -/
noncomputable abbrev iwahoriCosetPresheaf : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ ⥤ Type u where
  obj R := IwahoriCoset H J R.unop.unop
  map f := ↾Quotient.map' ((loopGroup k H).map f.unop.unop) (fun a b hab ↦ by
    apply QuotientGroup.leftRel_apply.mpr
    simpa only [map_mul, map_inv] using
      map_mem_iwahoriLoopSubgroup H J f.unop.unop (QuotientGroup.leftRel_apply.mp hab))
  map_id R := by
    ext q
    induction q using Quotient.inductionOn' with | _ a =>
      exact congrArg QuotientGroup.mk (congrArg (fun m ↦ m.hom a) ((loopGroup k H).map_id _))
  map_comp f g := by
    ext q
    induction q using Quotient.inductionOn' with | _ a =>
      exact congrArg QuotientGroup.mk
        (congrArg (fun m ↦ m.hom a) ((loopGroup k H).map_comp f.unop.unop g.unop.unop))

/-- Positive representatives define the same coset exactly when their reductions do. -/
theorem mk_positiveLoopToLoop_eq_iff (R : CommAlgCat.{u} k)
    (a b : WithConv (H →ₐ[k] PowerSeries R)) :
    (QuotientGroup.mk (((positiveLoopToLoop k H).app R).hom a) : IwahoriCoset H J R) =
        QuotientGroup.mk (((positiveLoopToLoop k H).app R).hom b) ↔
      (QuotientGroup.mk (positiveLoopEvalZero k H R a) :
        WithConv (H →ₐ[k] R) ⧸ CommHopfAlgCat.quotientPointsSubgroup H J R) =
      QuotientGroup.mk (positiveLoopEvalZero k H R b) := by
  rw [QuotientGroup.eq, QuotientGroup.eq]
  have hm := map_mul ((positiveLoopToLoop k H).app R).hom (a⁻¹) b
  have hi := map_inv ((positiveLoopToLoop k H).app R).hom a
  have he := (Iff.of_eq (congrArg (fun x ↦ x ∈ iwahoriLoopSubgroup H J R)
    (hm.trans (congrArg (· * ((positiveLoopToLoop k H).app R).hom b) hi)))).symm.trans
      (positiveLoopToLoop_mem_iwahoriLoopSubgroup H J R (a⁻¹ * b))
  simp only [mem_positiveLoopPreimage, map_mul, map_inv] at he
  convert he using 1

/-- The cosets with a positive-loop representative form a subfunctor. -/
noncomputable def positiveIwahoriCosets : Subfunctor (iwahoriCosetPresheaf H J) where
  obj R := {q | ∃ a : WithConv (H →ₐ[k] PowerSeries R.unop.unop),
    QuotientGroup.mk (((positiveLoopToLoop k H).app R.unop.unop).hom a) = q}
  map f := by
    rintro q ⟨a, rfl⟩
    refine ⟨(positiveLoopGroup k H).map f.unop.unop a, ?_⟩
    exact congrArg (QuotientGroup.mk)
      (congrArg (fun m ↦ m.hom a) ((positiveLoopToLoop k H).naturality f.unop.unop))

/-- Membership in the positive-representative subfunctor is existence of a positive loop
representing the given coset. -/
theorem mem_positiveIwahoriCosets_iff (R : CommAlgCat.{u} k) (q : IwahoriCoset H J R) :
    q ∈ (positiveIwahoriCosets H J).obj (op (op R)) ↔
      ∃ a : WithConv (H →ₐ[k] PowerSeries R),
        QuotientGroup.mk (((positiveLoopToLoop k H).app R).hom a) = q := Iff.rfl

/-- Constant loops embed the literal homogeneous space into the Iwahori cosets. -/
noncomputable def constantIwahoriCoset (R : CommAlgCat.{u} k) :
    (WithConv (H →ₐ[k] R) ⧸ CommHopfAlgCat.quotientPointsSubgroup H J R) →
      IwahoriCoset H J R :=
  Quotient.map' (fun a ↦ ((positiveLoopToLoop k H).app R).hom (constantPositiveLoop k H R a))
    fun a b hab ↦ Quotient.exact' <|
      (mk_positiveLoopToLoop_eq_iff H J R _ _).mpr <| by
        simpa only [positiveLoopEvalZero_constantPositiveLoop] using Quotient.sound' hab

/-- The constant-coset map on representatives. -/
@[simp]
theorem constantIwahoriCoset_mk (R : CommAlgCat.{u} k) (a : WithConv (H →ₐ[k] R)) :
    constantIwahoriCoset H J R (QuotientGroup.mk a) =
      QuotientGroup.mk ((positiveLoopToLoop k H).app R
        (constantPositiveLoop k H R a)) := (rfl)

/-- A positive-loop coset is represented by the constant loop of its reduction. -/
theorem constantIwahoriCoset_reduction (R : CommAlgCat.{u} k)
    (a : WithConv (H →ₐ[k] PowerSeries R)) :
    constantIwahoriCoset H J R (QuotientGroup.mk (positiveLoopEvalZero k H R a)) =
      QuotientGroup.mk (((positiveLoopToLoop k H).app R).hom a) := by
  rw [constantIwahoriCoset_mk]
  apply (mk_positiveLoopToLoop_eq_iff H J R _ _).mpr
  rw [positiveLoopEvalZero_constantPositiveLoop]

/-- Constant loops give distinct Iwahori cosets for distinct `G/B` cosets. -/
theorem constantIwahoriCoset_injective (R : CommAlgCat.{u} k) :
    Function.Injective (constantIwahoriCoset H J R) := by
  intro a b
  induction a using Quotient.inductionOn' with | _ a =>
    induction b using Quotient.inductionOn' with | _ b =>
      intro hab
      simpa only [positiveLoopEvalZero_constantPositiveLoop] using
        (mk_positiveLoopToLoop_eq_iff H J R _ _).mp hab

/-- The image of constant cosets is precisely the cosets with a positive representative. -/
theorem range_constantIwahoriCoset (R : CommAlgCat.{u} k) :
    Set.range (constantIwahoriCoset H J R) = (positiveIwahoriCosets H J).obj (op (op R)) := by
  ext q
  rw [mem_positiveIwahoriCosets_iff]
  constructor
  · rintro ⟨a, rfl⟩
    induction a using Quotient.inductionOn' with | _ a =>
      exact ⟨constantPositiveLoop k H R a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨QuotientGroup.mk (positiveLoopEvalZero k H R a),
      constantIwahoriCoset_reduction H J R a⟩

/-- Reduction identifies the positive-representative cosets with the literal `G/B` cosets.
The displayed direction is induced by constant loops. -/
def positiveIwahoriCosetEquiv (R : CommAlgCat.{u} k) :
    (WithConv (H →ₐ[k] R) ⧸ CommHopfAlgCat.quotientPointsSubgroup H J R) ≃
      (positiveIwahoriCosets H J).obj (op (op R)) :=
  Equiv.ofBijective
    (fun q ↦ ⟨constantIwahoriCoset H J R q,
      (range_constantIwahoriCoset H J R).le ⟨q, rfl⟩⟩)
    ⟨fun _ _ h ↦ constantIwahoriCoset_injective H J R (congrArg Subtype.val h),
      fun q ↦ by
        obtain ⟨a, ha⟩ := (range_constantIwahoriCoset H J R).ge q.property
        exact ⟨a, Subtype.ext ha⟩⟩

/-- The inclusion of the positive-coset equivalence is the constant-coset map. -/
@[simp]
theorem coe_positiveIwahoriCosetEquiv (R : CommAlgCat.{u} k)
    (q : WithConv (H →ₐ[k] R) ⧸ CommHopfAlgCat.quotientPointsSubgroup H J R) :
    (positiveIwahoriCosetEquiv H J R q).val = constantIwahoriCoset H J R q := (rfl)

/-- The inverse equivalence is reduction of any positive representative. -/
@[simp]
theorem positiveIwahoriCosetEquiv_symm_positive (R : CommAlgCat.{u} k)
    (a : WithConv (H →ₐ[k] PowerSeries R)) :
    dsimp% (positiveIwahoriCosetEquiv H J R).symm
      ⟨QuotientGroup.mk (((positiveLoopToLoop k H).app R).hom a),
        (mem_positiveIwahoriCosets_iff H J R _).mpr ⟨a, rfl⟩⟩ =
        QuotientGroup.mk (positiveLoopEvalZero k H R a) := by
  apply (positiveIwahoriCosetEquiv H J R).symm_apply_eq.mpr
  apply Subtype.ext
  exact (constantIwahoriCoset_reduction H J R a).symm

/-- The Iwahori image is contained in the positive-loop image. -/
theorem iwahoriLoopSubgroup_le_positiveLoopRange (R : CommAlgCat.{u} k) :
    iwahoriLoopSubgroup H J R ≤ ((positiveLoopToLoop k H).app R).hom.range := by
  rintro _ ⟨a, _, rfl⟩
  exact ⟨a, rfl⟩

/-- Forgetting the Iwahori level gives a literal positive-loop coset. -/
def iwahoriCosetProjection (R : CommAlgCat.{u} k) :
    IwahoriCoset H J R →
      ((loopGroup k H).obj R ⧸ ((positiveLoopToLoop k H).app R).hom.range) :=
  Subgroup.quotientMapOfLE (iwahoriLoopSubgroup_le_positiveLoopRange H J R)

/-- The pointwise projection preserves representatives. -/
@[simp]
theorem iwahoriCosetProjection_mk (R : CommAlgCat.{u} k)
    (g : (loopGroup k H).obj R) :
    iwahoriCosetProjection H J R (QuotientGroup.mk g) = QuotientGroup.mk g := (rfl)

/-- The identity fibre of the literal coset projection consists exactly of the cosets
with a positive-loop representative. -/
theorem iwahoriCosetProjection_eq_one_iff (R : CommAlgCat.{u} k)
    (q : IwahoriCoset H J R) :
    iwahoriCosetProjection H J R q = QuotientGroup.mk 1 ↔
      q ∈ (positiveIwahoriCosets H J).obj (op (op R)) := by
  induction q using Quotient.inductionOn' with | _ g =>
    rw [iwahoriCosetProjection_mk, QuotientGroup.mk_eq_one_iff, mem_positiveIwahoriCosets_iff]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, ha⟩
      have h := iwahoriLoopSubgroup_le_positiveLoopRange H J R (QuotientGroup.eq.mp ha)
      have hi : ((positiveLoopToLoop k H).app R).hom a ∈
          ((positiveLoopToLoop k H).app R).hom.range := ⟨a, rfl⟩
      simpa using (((positiveLoopToLoop k H).app R).hom.range).mul_mem hi h

/-- Every homogeneous-space coset lies over the identity positive-loop coset. -/
@[simp]
theorem iwahoriCosetProjection_constant (R : CommAlgCat.{u} k)
    (q : WithConv (H →ₐ[k] R) ⧸ CommHopfAlgCat.quotientPointsSubgroup H J R) :
    iwahoriCosetProjection H J R (constantIwahoriCoset H J R q) = QuotientGroup.mk 1 :=
  (iwahoriCosetProjection_eq_one_iff H J R _).mpr
    ((range_constantIwahoriCoset H J R).le ⟨q, rfl⟩)

/-- Constant cosets commute with every coefficient map. The homogeneous-space map is the
existing map of `homogeneousQuotientPresheaf`. -/
theorem constantIwahoriCoset_naturality {R S : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ} (f : R ⟶ S)
    (q : (_root_.CommHopfAlgCat.homogeneousQuotientPresheaf H J).obj R) :
    (iwahoriCosetPresheaf H J).map f (constantIwahoriCoset H J R.unop.unop
      (_root_.CommHopfAlgCat.homogeneousQuotientPresheafObjEquiv H J R q)) =
      constantIwahoriCoset H J S.unop.unop
        (_root_.CommHopfAlgCat.homogeneousQuotientPresheafObjEquiv H J S
          ((_root_.CommHopfAlgCat.homogeneousQuotientPresheaf H J).map f q)) := by
  induction q using _root_.CommHopfAlgCat.homogeneousQuotientPresheaf_induction_on H J with
  | h a =>
    rw [_root_.CommHopfAlgCat.homogeneousQuotientPresheaf_map_mk,
      _root_.CommHopfAlgCat.homogeneousQuotientPresheafObjEquiv_mk,
      _root_.CommHopfAlgCat.homogeneousQuotientPresheafObjEquiv_mk]
    rw [constantIwahoriCoset_mk]
    dsimp only [iwahoriCosetPresheaf]
    have hn := congrArg (fun m ↦ m.hom (constantPositiveLoop k H R.unop.unop a))
      ((positiveLoopToLoop k H).naturality f.unop.unop)
    calc
      _ = QuotientGroup.mk (((positiveLoopToLoop k H).app S.unop.unop).hom
          ((positiveLoopGroup k H).map f.unop.unop
            (constantPositiveLoop k H R.unop.unop a))) := congrArg QuotientGroup.mk hn.symm
      _ = constantIwahoriCoset H J S.unop.unop (QuotientGroup.mk
          (positiveLoopEvalZero k H S.unop.unop
            ((positiveLoopGroup k H).map f.unop.unop
              (constantPositiveLoop k H R.unop.unop a)))) :=
        (constantIwahoriCoset_reduction H J S.unop.unop _).symm
      _ = _ := by
        congr 2
        exact (positiveLoopEvalZero_naturality f.unop.unop.hom _).trans
          (congrArg (AlgHom.mapValue f.unop.unop.hom)
            (positiveLoopEvalZero_constantPositiveLoop a))

/-- The subfunctor of positive representatives is naturally the existing homogeneous
quotient presheaf `G/B`. The lift only aligns the presheaves' value universes. -/
def positiveIwahoriCosetsIso :
    _root_.CommHopfAlgCat.homogeneousQuotientPresheaf H J ≅
      (positiveIwahoriCosets H J).toFunctor ⋙ uliftFunctor.{u + 1, u} :=
  NatIso.ofComponents (fun R ↦
    (((_root_.CommHopfAlgCat.homogeneousQuotientPresheafObjEquiv H J R).trans
      (positiveIwahoriCosetEquiv H J R.unop.unop)).trans
      Equiv.ulift.{u + 1, u}.symm).toIso) (by
    intro R S f
    ext q
    apply ULift.ext
    apply Subtype.ext
    exact (constantIwahoriCoset_naturality H J f q).symm)

/-- On representatives, the natural base-fibre identification is the constant-loop map. -/
@[simp]
theorem positiveIwahoriCosetsIso_hom_mk (R : ((CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ)
    (a : WithConv (H →ₐ[k] R.unop.unop)) :
    dsimp% ((positiveIwahoriCosetsIso H J).hom.app R
      (_root_.CommHopfAlgCat.homogeneousQuotientPresheafMk H J R a)).down.val =
        constantIwahoriCoset H J R.unop.unop (QuotientGroup.mk a) := by
  exact congrArg (constantIwahoriCoset H J R.unop.unop)
    (_root_.CommHopfAlgCat.homogeneousQuotientPresheafObjEquiv_mk H J R a)

/-- The projection is equivariant for left multiplication by loops. -/
theorem iwahoriCosetProjection_smul (R : CommAlgCat.{u} k)
    (g : (loopGroup k H).obj R) (q : IwahoriCoset H J R) :
    iwahoriCosetProjection H J R (g • q) = g • iwahoriCosetProjection H J R q := by
  induction q using Quotient.inductionOn' with | _ a => rfl

/-- A coset lies over `gL⁺G` exactly when translating it by `g⁻¹` gives a positive
representative. -/
theorem iwahoriCosetProjection_eq_mk_iff (R : CommAlgCat.{u} k)
    (g : (loopGroup k H).obj R) (q : IwahoriCoset H J R) :
    iwahoriCosetProjection H J R q = QuotientGroup.mk g ↔
      g⁻¹ • q ∈ (positiveIwahoriCosets H J).obj (op (op R)) := by
  rw [← iwahoriCosetProjection_eq_one_iff, iwahoriCosetProjection_smul]
  constructor
  · intro h
    rw [h, MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
  · intro h
    have he := congrArg (g • ·) h
    simpa using he

/-- The fibre over the coset of a specified loop is `G/B`, with trivialization given by
left multiplication by the inverse loop. -/
def iwahoriCosetFiberEquiv (R : CommAlgCat.{u} k) (g : (loopGroup k H).obj R) :
    {q : IwahoriCoset H J R // iwahoriCosetProjection H J R q = QuotientGroup.mk g} ≃
      (WithConv (H →ₐ[k] R) ⧸ CommHopfAlgCat.quotientPointsSubgroup H J R) where
  toFun q := (positiveIwahoriCosetEquiv H J R).symm
    ⟨g⁻¹ • q.val, (iwahoriCosetProjection_eq_mk_iff H J R g q.val).mp q.property⟩
  invFun a := ⟨g • constantIwahoriCoset H J R a, by
    rw [iwahoriCosetProjection_smul, iwahoriCosetProjection_constant,
      MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]⟩
  left_inv q := by
    apply Subtype.ext
    have he : constantIwahoriCoset H J R ((positiveIwahoriCosetEquiv H J R).symm
        ⟨g⁻¹ • q.val, (iwahoriCosetProjection_eq_mk_iff H J R g q.val).mp q.property⟩) =
        g⁻¹ • q.val :=
      congrArg Subtype.val ((positiveIwahoriCosetEquiv H J R).apply_symm_apply _)
    exact (congrArg (fun x : IwahoriCoset H J R ↦ g • x) he).trans (smul_inv_smul g q.val)
  right_inv a := by
    apply (positiveIwahoriCosetEquiv H J R).symm_apply_eq.mpr
    apply Subtype.ext
    have hs : g⁻¹ • (g • constantIwahoriCoset H J R a) = constantIwahoriCoset H J R a :=
      inv_smul_smul g _
    exact hs.trans (coe_positiveIwahoriCosetEquiv H J R a).symm

/-- Inverse fibre coordinates are constant loops translated on the left by `g`. -/
@[simp]
theorem iwahoriCosetFiberEquiv_symm_coe (R : CommAlgCat.{u} k)
    (g : (loopGroup k H).obj R)
    (a : WithConv (H →ₐ[k] R) ⧸ CommHopfAlgCat.quotientPointsSubgroup H J R) :
    ((iwahoriCosetFiberEquiv H J R g).symm a).val = g • constantIwahoriCoset H J R a := (rfl)

/-- The forward fibre coordinates use `g⁻¹`; this formula avoids unfolding the equivalence. -/
theorem constant_iwahoriCosetFiberEquiv (R : CommAlgCat.{u} k)
    (g : (loopGroup k H).obj R)
    (q : {q : IwahoriCoset H J R // iwahoriCosetProjection H J R q = QuotientGroup.mk g}) :
    constantIwahoriCoset H J R (iwahoriCosetFiberEquiv H J R g q) = g⁻¹ • q.val :=
  congrArg Subtype.val ((positiveIwahoriCosetEquiv H J R).apply_symm_apply _)

/-- Coefficient maps commute with the left loop action on cosets. -/
theorem iwahoriCosetPresheaf_map_smul {R S : CommAlgCat.{u} k} (f : R ⟶ S)
    (g : (loopGroup k H).obj R) (q : IwahoriCoset H J R) :
    (iwahoriCosetPresheaf H J).map f.op.op (g • q) =
      ((loopGroup k H).map f).hom g •
        ((iwahoriCosetPresheaf H J).map f.op.op q : IwahoriCoset H J S) := by
  induction q using Quotient.inductionOn' with | _ a =>
    exact congrArg QuotientGroup.mk (map_mul ((loopGroup k H).map f).hom g a)

/-- Coefficient extension maps the fibre over `gL⁺G` to the fibre over its image. -/
def iwahoriCosetFiberMap {R S : CommAlgCat.{u} k} (f : R ⟶ S)
    (g : (loopGroup k H).obj R)
    (q : {q : IwahoriCoset H J R // iwahoriCosetProjection H J R q = QuotientGroup.mk g}) :
    {q : IwahoriCoset H J S // iwahoriCosetProjection H J S q =
      QuotientGroup.mk (((loopGroup k H).map f).hom g)} :=
  ⟨(iwahoriCosetPresheaf H J).map f.op.op q.val, by
    apply (iwahoriCosetProjection_eq_mk_iff H J S _ _).mpr
    rw [← map_inv, ← iwahoriCosetPresheaf_map_smul]
    exact (positiveIwahoriCosets H J).map f.op.op
      ((iwahoriCosetProjection_eq_mk_iff H J R g q.val).mp q.property)⟩

/-- On underlying cosets, the fibre map is the coefficient map of the coset presheaf. -/
@[simp]
theorem iwahoriCosetFiberMap_coe {R S : CommAlgCat.{u} k} (f : R ⟶ S)
    (g : (loopGroup k H).obj R)
    (q : {q : IwahoriCoset H J R // iwahoriCosetProjection H J R q = QuotientGroup.mk g}) :
    (iwahoriCosetFiberMap H J f g q).val =
      (iwahoriCosetPresheaf H J).map f.op.op q.val := (rfl)

/-- The fibre trivializations commute with coefficient maps, using the existing
homogeneous quotient presheaf to map the `G/B` coordinate. -/
theorem iwahoriCosetFiberEquiv_naturality {R S : CommAlgCat.{u} k} (f : R ⟶ S)
    (g : (loopGroup k H).obj R)
    (q : (_root_.CommHopfAlgCat.homogeneousQuotientPresheaf H J).obj (op (op R))) :
    iwahoriCosetFiberMap H J f g ((iwahoriCosetFiberEquiv H J R g).symm
      (_root_.CommHopfAlgCat.homogeneousQuotientPresheafObjEquiv H J _ q)) =
    (iwahoriCosetFiberEquiv H J S (((loopGroup k H).map f).hom g)).symm
      (_root_.CommHopfAlgCat.homogeneousQuotientPresheafObjEquiv H J _
        ((_root_.CommHopfAlgCat.homogeneousQuotientPresheaf H J).map f.op.op q)) := by
  apply Subtype.ext
  rw [iwahoriCosetFiberMap_coe, iwahoriCosetFiberEquiv_symm_coe,
    iwahoriCosetFiberEquiv_symm_coe, iwahoriCosetPresheaf_map_smul]
  exact congrArg (fun a : IwahoriCoset H J S ↦ ((loopGroup k H).map f).hom g • a)
    (constantIwahoriCoset_naturality H J f.op.op q)

/-- Pairs of a loop and an Iwahori coset over its positive-loop coset are pairs of a loop
and a `G/B` coset. This is a trivialization over the loop group, before sheafification. -/
def iwahoriCosetPairsEquiv (R : CommAlgCat.{u} k) :
    {p : (loopGroup k H).obj R × IwahoriCoset H J R //
      iwahoriCosetProjection H J R p.2 = QuotientGroup.mk p.1} ≃
      (loopGroup k H).obj R ×
        (WithConv (H →ₐ[k] R) ⧸ CommHopfAlgCat.quotientPointsSubgroup H J R) :=
  (Equiv.subtypeProdEquivSigmaSubtype fun g q ↦
    iwahoriCosetProjection H J R q = QuotientGroup.mk g).trans
      (Equiv.sigmaEquivProdOfEquiv (iwahoriCosetFiberEquiv H J R))

/-- The inverse pair coordinates retain the loop and translate its constant-loop flag. -/
@[simp]
theorem iwahoriCosetPairsEquiv_symm_coe (R : CommAlgCat.{u} k)
    (p : (loopGroup k H).obj R ×
      (WithConv (H →ₐ[k] R) ⧸ CommHopfAlgCat.quotientPointsSubgroup H J R)) :
    dsimp% ((iwahoriCosetPairsEquiv H J R).symm p).val =
      (p.1, p.1 • constantIwahoriCoset H J R p.2) := (rfl)

/-- Forward pair coordinates retain the loop and translate the flag by its inverse. -/
theorem iwahoriCosetPairsEquiv_apply (R : CommAlgCat.{u} k)
    (p : {p : (loopGroup k H).obj R × IwahoriCoset H J R //
      iwahoriCosetProjection H J R p.2 = QuotientGroup.mk p.1}) :
    Prod.map id (constantIwahoriCoset H J R) (iwahoriCosetPairsEquiv H J R p) =
      (p.val.1, p.val.1⁻¹ • p.val.2) :=
  Prod.ext rfl (constant_iwahoriCosetFiberEquiv H J R p.val.1 ⟨p.val.2, p.property⟩)

/-- At the identity loop the fibre coordinates are the base-fibre coordinates. -/
@[simp]
theorem iwahoriCosetFiberEquiv_one_symm_coe (R : CommAlgCat.{u} k)
    (q : WithConv (H →ₐ[k] R) ⧸ CommHopfAlgCat.quotientPointsSubgroup H J R) :
    ((iwahoriCosetFiberEquiv H J R 1).symm q).val = constantIwahoriCoset H J R q := by
  rw [iwahoriCosetFiberEquiv_symm_coe, one_smul]

/-- For `B = G`, the Iwahori image is the entire positive-loop image. Thus the literal
projection forgets no additional level structure. -/
@[simp]
theorem iwahoriLoopSubgroup_bot (R : CommAlgCat.{u} k) :
    iwahoriLoopSubgroup H ⊥ R = ((positiveLoopToLoop k H).app R).hom.range := by
  rw [iwahoriLoopSubgroup, positiveLoopPreimage_bot]
  convert Subgroup.map_top ((positiveLoopToLoop k H).app R).hom using 1
  rfl

/-- For `B = G`, the positive-representative fibre has just one coset. -/
theorem positiveIwahoriCosets_bot_subsingleton (R : CommAlgCat.{u} k) :
    Subsingleton ((positiveIwahoriCosets H ⊥).obj (op (op R))) := by
  have hs : Subsingleton (WithConv (H →ₐ[k] R) ⧸
      CommHopfAlgCat.quotientPointsSubgroup H ⊥ R) := by
    rw [CommHopfAlgCat.quotientPointsSubgroup_bot]
    exact QuotientGroup.subsingleton_quotient_top
  exact (positiveIwahoriCosetEquiv H ⊥ R).surjective.subsingleton

/-- For the trivial subgroup, positive-representative cosets are naturally the points of `G`.
The Iwahori subgroup is then the first congruence subgroup. -/
def positiveIwahoriCosetsTrivialEquiv (R : CommAlgCat.{u} k) :
    (positiveIwahoriCosets H (HopfIdeal.augmentation k H)).obj (op (op R)) ≃
      WithConv (H →ₐ[k] R) :=
  (positiveIwahoriCosetEquiv H (HopfIdeal.augmentation k H) R).symm.trans
    ((Subgroup.quotientEquivOfEq (by
      ext a
      rw [CommHopfAlgCat.mem_quotientPointsSubgroup_augmentation_iff, Subgroup.mem_bot])).trans
        (QuotientGroup.quotientEquivSelf _))

/-- Coefficient extension on pairs consisting of a loop and a coset above its image. -/
def iwahoriCosetPairsMap {R S : CommAlgCat.{u} k} (f : R ⟶ S)
    (p : {p : (loopGroup k H).obj R × IwahoriCoset H J R //
      iwahoriCosetProjection H J R p.2 = QuotientGroup.mk p.1}) :
    {p : (loopGroup k H).obj S × IwahoriCoset H J S //
      iwahoriCosetProjection H J S p.2 = QuotientGroup.mk p.1} :=
  ⟨(((loopGroup k H).map f).hom p.val.1,
      (iwahoriCosetFiberMap H J f p.val.1 ⟨p.val.2, p.property⟩).val),
    (iwahoriCosetFiberMap H J f p.val.1 ⟨p.val.2, p.property⟩).property⟩

/-- On underlying pairs, coefficient extension maps the loop and the coset separately. -/
@[simp]
theorem iwahoriCosetPairsMap_coe {R S : CommAlgCat.{u} k} (f : R ⟶ S)
    (p : {p : (loopGroup k H).obj R × IwahoriCoset H J R //
      iwahoriCosetProjection H J R p.2 = QuotientGroup.mk p.1}) :
    (iwahoriCosetPairsMap H J f p).val =
      (((loopGroup k H).map f).hom p.val.1,
        (iwahoriCosetPresheaf H J).map f.op.op p.val.2) := (rfl)

/-- The pair trivialization commutes with coefficient extension. The inverse direction
expresses the map explicitly as left multiplication of constant-loop flags. -/
theorem iwahoriCosetPairsEquiv_naturality {R S : CommAlgCat.{u} k} (f : R ⟶ S)
    (g : (loopGroup k H).obj R)
    (q : (_root_.CommHopfAlgCat.homogeneousQuotientPresheaf H J).obj (op (op R))) :
    iwahoriCosetPairsMap H J f ((iwahoriCosetPairsEquiv H J R).symm
      (g, _root_.CommHopfAlgCat.homogeneousQuotientPresheafObjEquiv H J _ q)) =
      (iwahoriCosetPairsEquiv H J S).symm
        (((loopGroup k H).map f).hom g,
          _root_.CommHopfAlgCat.homogeneousQuotientPresheafObjEquiv H J _
            ((_root_.CommHopfAlgCat.homogeneousQuotientPresheaf H J).map f.op.op q)) := by
  apply Subtype.ext
  rw [iwahoriCosetPairsMap_coe, iwahoriCosetPairsEquiv_symm_coe,
    iwahoriCosetPairsEquiv_symm_coe]
  apply Prod.ext
  · rfl
  · have h := congrArg Subtype.val (iwahoriCosetFiberEquiv_naturality H J f g q)
    rw [iwahoriCosetFiberMap_coe, iwahoriCosetFiberEquiv_symm_coe,
      iwahoriCosetFiberEquiv_symm_coe] at h
    exact h

/-- Fiber coordinates of a translated positive representative are its reduction. -/
@[simp]
theorem iwahoriCosetFiberEquiv_symm_reduction (R : CommAlgCat.{u} k)
    (g : (loopGroup k H).obj R) (a : WithConv (H →ₐ[k] PowerSeries R)) :
    ((iwahoriCosetFiberEquiv H J R g).symm
      (QuotientGroup.mk (positiveLoopEvalZero k H R a))).val =
        QuotientGroup.mk (g * ((positiveLoopToLoop k H).app R).hom a) := by
  rw [iwahoriCosetFiberEquiv_symm_coe, constantIwahoriCoset_reduction,
    MulAction.Quotient.smul_mk, smul_eq_mul]

/-- With trivial `B`, the Iwahori image is the image of the first congruence subgroup. -/
theorem iwahoriLoopSubgroup_augmentation (R : CommAlgCat.{u} k) :
    iwahoriLoopSubgroup H (HopfIdeal.augmentation k H) R =
      (congruenceSubgroup k H (Ideal.span {(PowerSeries.X : PowerSeries R)})).map
        ((positiveLoopToLoop k H).app R).hom := by
  rw [iwahoriLoopSubgroup, positiveLoopPreimage_augmentation]

/-- For trivial `B`, the inverse base-fibre equivalence sends a group point to its
constant-loop coset. -/
@[simp]
theorem positiveIwahoriCosetsTrivialEquiv_symm_coe (R : CommAlgCat.{u} k)
    (a : WithConv (H →ₐ[k] R)) :
    ((positiveIwahoriCosetsTrivialEquiv H R).symm a).val =
      QuotientGroup.mk (((positiveLoopToLoop k H).app R).hom
        (constantPositiveLoop k H R a)) := (rfl)

end TauCeti.AffineGrassmannian

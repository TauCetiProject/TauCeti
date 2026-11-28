/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.Functor
public import TauCeti.CategoryTheory.DG.Opposite.Functor
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
import TauCeti.Data.Nat.Choose.Basic
import TauCeti.Data.Finset.Basic

/-!
# Opposites of differential graded nerves

Reversing a dg simplex reverses its vertices and its coherence indices. A coherence with `r`
interior vertices acquires the sign `(-1)^(r choose 2)`. The Koszul sign in opposite DG
composition makes this operation preserve the differential equation. Consequently the dg nerve
of the opposite DG category identifies with the opposite simplicial set of the dg nerve.

The construction uses `TauCeti.dgComp_op` for opposite composition and
`TauCeti.DGNerve.boundary_def` for the coherence equation. The simplex involution and the
simplicial opposite are Mathlib's `SimplexCategory.rev` and `SSet.op`.

The main comparison is `TauCeti.dgNerve.opIso`; `Simplex.op` and `Simplex.unop` describe its
components, and `CategoryTheory.EnrichedFunctor.mapDGNerve_opIso_hom` gives its naturality.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.6 and Remark 1.3.1.12.
-/

public section

open CategoryTheory Finset Opposite Simplicial

namespace TauCeti

namespace DGNerve

universe v u

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C] {n : ℕ}

/-- Signed reflection of dg coherence data, with the source and target interchanged. -/
noncomputable def Coherences.op {X : Fin (n + 1) → C} (f : Coherences R X) :
    Coherences R (fun i ↦ Opposite.op (X i.rev)) :=
  fun i j S d hij hS hd ↦ ((#S).choose 2 : ℤ).negOnePow •
    f j.rev i.rev (S.image Fin.rev) d (Fin.rev_le_rev.mpr hij)
      (by
        intro a ha
        obtain ⟨s, hs, rfl⟩ := mem_image.mp ha
        exact mem_Ioo.mpr ⟨Fin.rev_lt_rev.mpr (mem_Ioo.mp (hS hs)).2,
          Fin.rev_lt_rev.mpr (mem_Ioo.mp (hS hs)).1⟩)
      (by rwa [card_image_of_injective _ Fin.rev_injective])

/-- A reflected coherence is the original coherence on the reflected set, with its reversal
sign. -/
@[simp]
theorem Coherences.op_apply {X : Fin (n + 1) → C} (f : Coherences R X)
    (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (d : ℤ) (hij : i ≤ j)
    (hS : S ⊆ Ioo i j) (hd : d + #S = 0) :
    f.op i j S d hij hS hd = ((#S).choose 2 : ℤ).negOnePow •
      f j.rev i.rev (S.image Fin.rev) d (Fin.rev_le_rev.mpr hij)
        (by
          intro a ha
          obtain ⟨s, hs, rfl⟩ := mem_image.mp ha
          exact mem_Ioo.mpr ⟨Fin.rev_lt_rev.mpr (mem_Ioo.mp (hS hs)).2,
            Fin.rev_lt_rev.mpr (mem_Ioo.mp (hS hs)).1⟩)
        (by rwa [card_image_of_injective _ Fin.rev_injective]) := (rfl)

/-- Signed reflection commutes with the dg nerve boundary. -/
theorem boundary_op {X : Fin (n + 1) → C} (f : Coherences R X)
    (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (d : ℤ) (hij : i ≤ j)
    (hS : S ⊆ Ioo i j) (hd : d + #S = 0) :
    boundary R f.op i j S d hij hS hd = ((#S).choose 2 : ℤ).negOnePow •
      boundary R f j.rev i.rev (S.image Fin.rev) d (Fin.rev_le_rev.mpr hij)
        (by
          intro a ha
          obtain ⟨s, hs, rfl⟩ := mem_image.mp ha
          exact mem_Ioo.mpr ⟨Fin.rev_lt_rev.mpr (mem_Ioo.mp (hS hs)).2,
            Fin.rev_lt_rev.mpr (mem_Ioo.mp (hS hs)).1⟩)
        (by rwa [card_image_of_injective _ Fin.rev_injective]) := by
  have hcard (P : Fin (n + 1) → Prop) [DecidablePred P] :
      #{s ∈ S.image Fin.rev | P s} = #{s ∈ S | P s.rev} := by
    rw [filter_image, card_image_of_injective _ Fin.rev_injective]
  -- Pair each deletion and composition summand with its reflected interior vertex.
  rw [boundary_def, boundary_def, Finset.smul_sum]
  refine sum_bij (fun t _ ↦ ⟨t.val.rev, mem_image_of_mem Fin.rev t.property⟩)
    (fun _ _ ↦ mem_attach _ _) ?_ ?_ ?_
  · intro a _ b _ h
    exact Subtype.ext (Fin.rev_injective (congrArg Subtype.val h))
  · intro b _
    obtain ⟨a, ha, hab⟩ := mem_image.mp b.property
    exact ⟨⟨a, ha⟩, mem_attach _ _, Subtype.ext hab⟩
  intro t _
  dsimp only
  have hlo : {s ∈ S.image Fin.rev | s < t.val.rev} =
      {s ∈ S | t.val < s}.image Fin.rev := by simp [filter_image]
  have hhi : {s ∈ S.image Fin.rev | t.val.rev < s} =
      {s ∈ S | s < t.val}.image Fin.rev := by simp [filter_image]
  have hrank : #{s ∈ S.image Fin.rev | t.val.rev ≤ s} = #{s ∈ S | s ≤ t.val} := by
    simp [hcard]
  have hsplit := card_filter_lt_add_card_filter_gt_add_one t.property
  have hge' := card_filter_add_card_filter_not (s := S) (p := fun s ↦ s < t.val)
  have hle' := card_filter_add_card_filter_not (s := S) (p := fun s ↦ t.val < s)
  simp only [not_lt] at hge' hle'
  have hge : #{s ∈ S | t.val ≤ s} = #{s ∈ S | t.val < s} + 1 := by omega
  have hle : #{s ∈ S | s ≤ t.val} = #{s ∈ S | s < t.val} + 1 := by omega
  rw [hrank]
  simp only [Coherences.op, dgComp_op, dgComp_units_smul, units_smul_dgComp,
    smul_sub, smul_smul]
  -- The deletion and composition signs both differ by an even exponent.
  refine congrArg₂ (· - ·) ?_ ?_
  · refine congrArg₂ (· • ·) ?_ (f.congr (image_erase Fin.rev_injective _ _))
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, card_erase_of_mem t.property,
      hge, hle]
    have hc : #S = (#S - 1) + 1 := by have := card_pos.mpr ⟨t.val, t.property⟩; omega
    rw [hc, Nat.choose_succ_succ', Nat.choose_one_right]
    rw [Int.negOnePow_eq_iff]
    refine ⟨-(#{s ∈ S | s < t.val} : ℤ), ?_⟩
    push_cast
    omega
  · refine congrArg₂ (· • ·) ?_ (f.dgComp_congr hlo.symm hhi.symm)
    have hloCard := congrArg Finset.card hlo
    have hhiCard := congrArg Finset.card hhi
    simp only [card_image_of_injective _ Fin.rev_injective] at hloCard hhiCard
    simp only [← Int.negOnePow_add, neg_mul_neg, hloCard, hhiCard]
    rw [hge, hle, hsplit.symm, Nat.choose_succ_succ', Nat.choose_one_right,
      Nat.add_choose_two]
    rw [Int.negOnePow_eq_iff]
    refine ⟨-(#{s ∈ S | s < t.val} : ℤ), ?_⟩
    push_cast
    ring

/-- Reverse the vertices and coherences of a dg simplex into the opposite DG category. -/
-- The vertex formula must reduce because it determines the types of the coherences.
@[expose]
noncomputable def Simplex.op (x : Simplex R C n) : Simplex R Cᵒᵖ n where
  obj i := Opposite.op (x.obj i.rev)
  coh := x.coh.op
  coh_self i := by simp [Coherences.op]
  dgDifferential_coh i j S d hij hS hd := by
    simp only [Coherences.op]
    rw [dgDifferential_op, map_zsmul_unit, x.dgDifferential_coh, boundary_op]

/-- Reflection reverses the vertex order. -/
@[simp]
theorem Simplex.op_obj (x : Simplex R C n) (i : Fin (n + 1)) :
    x.op.obj i = Opposite.op (x.obj i.rev) := (rfl)

/-- A coherence with `r` interior vertices acquires the sign `(-1)^(r choose 2)`. -/
@[simp]
theorem Simplex.op_coh (x : Simplex R C n) (i j : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (d : ℤ) (hij : i ≤ j) (hS : S ⊆ Ioo i j)
    (hd : d + #S = 0) :
    x.op.coh i j S d hij hS hd = ((#S).choose 2 : ℤ).negOnePow •
      x.coh j.rev i.rev (S.image Fin.rev) d (Fin.rev_le_rev.mpr hij)
        (by
          intro a ha
          obtain ⟨s, hs, rfl⟩ := mem_image.mp ha
          exact mem_Ioo.mpr ⟨Fin.rev_lt_rev.mpr (mem_Ioo.mp (hS hs)).2,
            Fin.rev_lt_rev.mpr (mem_Ioo.mp (hS hs)).1⟩)
        (by rwa [card_image_of_injective _ Fin.rev_injective]) := (rfl)

private theorem signed_coh_heq (x : Simplex R C n) (a : ℤˣ)
    {i i' j j' : Fin (n + 1)} {S S' : Finset (Fin (n + 1))} {d : ℤ}
    (hi : i = i') (hj : j = j') (hS : S = S')
    {h₁ : i ≤ j} {h₂ : S ⊆ Ioo i j} {h₃ : d + #S = 0}
    {h₁' : i' ≤ j'} {h₂' : S' ⊆ Ioo i' j'} {h₃' : d + #S' = 0} :
    a • x.coh i j S d h₁ h₂ h₃ ≍ a • x.coh i' j' S' d h₁' h₂' h₃' := by
  subst hi hj hS
  rfl

/-- Reflection of dg simplices commutes with pullback by a simplex operator, with the operator
itself reflected. This includes operators that identify vertices. -/
theorem Simplex.op_map (x : Simplex R C n) {m : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (x.map α.toOrderHom).op = x.op.map (SimplexCategory.rev.map α).toOrderHom := by
  refine Simplex.ext (by ext i; simp) fun i j S d hij hS hd ↦ ?_
  dsimp only [Simplex.op, Coherences.op, Simplex.map]
  have himage : (S.image (SimplexCategory.rev.map α).toOrderHom).image Fin.rev =
      (S.image Fin.rev).image α.toOrderHom := by
    simp only [image_image, Function.comp_def, SimplexCategory.rev_map_apply, Fin.rev_rev]
    rfl
  have hc : (#(S.image (SimplexCategory.rev.map α).toOrderHom) = #S ∧
      S.image (SimplexCategory.rev.map α).toOrderHom ⊆
        Ioo ((SimplexCategory.rev.map α).toOrderHom i)
          ((SimplexCategory.rev.map α).toOrderHom j)) ↔
      (#((S.image Fin.rev).image α.toOrderHom) = #(S.image Fin.rev) ∧
        (S.image Fin.rev).image α.toOrderHom ⊆ Ioo (α.toOrderHom j.rev)
          (α.toOrderHom i.rev)) := by
    rw [← himage, card_image_of_injective _ Fin.rev_injective,
      card_image_of_injective _ Fin.rev_injective]
    simp only [image_subset_iff, SimplexCategory.rev_map_apply, mem_Ioo,
      Fin.rev_lt_rev]
    simp only [forall_mem_image, SimplexCategory.rev_map_apply, Fin.rev_rev]
    constructor
    · rintro ⟨hc, hs⟩
      exact ⟨hc, fun s hsS ↦ (hs s hsS).symm⟩
    · rintro ⟨hc, hs⟩
      exact ⟨hc, fun s hsS ↦ (hs hsS).symm⟩
  by_cases h : #(S.image (SimplexCategory.rev.map α).toOrderHom) = #S ∧
      S.image (SimplexCategory.rev.map α).toOrderHom ⊆
        Ioo ((SimplexCategory.rev.map α).toOrderHom i)
          ((SimplexCategory.rev.map α).toOrderHom j)
  · rw [Simplex.mapCoh_eq_coh _ _ (hc.mp h), Simplex.mapCoh_eq_coh _ _ h]
    simp only [Coherences.op, h.1, SimplexCategory.rev_map_apply]
    exact signed_coh_heq x _ (Fin.rev_rev _).symm (Fin.rev_rev _).symm himage.symm
  · rw [Simplex.mapCoh_eq_zero _ _ (not_iff_not.mpr hc |>.mp h),
      Simplex.mapCoh_eq_zero _ _ h]
    simp only [smul_zero]
    have he : (α.toOrderHom j.rev, α.toOrderHom i.rev) =
        ((α.toOrderHom j.rev).rev.rev, (α.toOrderHom i.rev).rev.rev) := by simp
    exact congr_arg_heq (fun z : Fin (n + 1) × Fin (n + 1) ↦
      (0 : DGHom R d (x.obj z.1) (x.obj z.2))) he

/-- Signed reflection from the nerve of the opposite category back to the original category. -/
-- Exposed for the same dependent vertex types as `Simplex.op`.
@[expose]
noncomputable def Simplex.unop (x : Simplex R Cᵒᵖ n) : Simplex R C n where
  obj i := (x.obj i.rev).unop
  coh i j S d hij hS hd := x.coh.op i j S d hij hS hd
  coh_self i := by
    simp only [Coherences.op, image_empty, card_empty, Nat.choose_zero_succ,
      Int.natCast_zero, Int.negOnePow_zero, one_smul, x.coh_self]
    exact dgId_op R (x.obj i.rev).unop
  dgDifferential_coh i j S d hij hS hd := by
    have h := x.op.dgDifferential_coh i j S d hij hS hd
    dsimp only [Simplex.op] at h
    convert h using 1
    rw [boundary_def (R := R) (C := C), boundary_def (R := R) (C := Cᵒᵖᵒᵖ)]
    refine sum_congr rfl fun t _ ↦ ?_
    congr 3
    symm
    rw [dgComp_op (R := R) (C := Cᵒᵖ), dgComp_op (R := R) (C := C),
      smul_smul]
    simp [mul_comm]

/-- The inverse reflection also reverses the vertex order. -/
@[simp]
theorem Simplex.unop_obj (x : Simplex R Cᵒᵖ n) (i : Fin (n + 1)) :
    x.unop.obj i = (x.obj i.rev).unop := (rfl)

/-- The inverse reflection uses the same sign on every coherence. -/
@[simp]
theorem Simplex.unop_coh (x : Simplex R Cᵒᵖ n) (i j : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (d : ℤ) (hij : i ≤ j) (hS : S ⊆ Ioo i j)
    (hd : d + #S = 0) :
    x.unop.coh i j S d hij hS hd = ((#S).choose 2 : ℤ).negOnePow •
      x.coh j.rev i.rev (S.image Fin.rev) d (Fin.rev_le_rev.mpr hij)
        (by
          intro a ha
          obtain ⟨s, hs, rfl⟩ := mem_image.mp ha
          exact mem_Ioo.mpr ⟨Fin.rev_lt_rev.mpr (mem_Ioo.mp (hS hs)).2,
            Fin.rev_lt_rev.mpr (mem_Ioo.mp (hS hs)).1⟩)
        (by rwa [card_image_of_injective _ Fin.rev_injective]) := (rfl)

/-- Reflecting a simplex and then reflecting it back is the identity. -/
@[simp]
theorem Simplex.unop_op (x : Simplex R C n) : x.op.unop = x := by
  refine Simplex.ext (by ext i; simp) fun i j S d hij hS hd ↦ ?_
  dsimp only [Simplex.op, Simplex.unop, Coherences.op]
  simp only [card_image_of_injective _ Fin.rev_injective, smul_smul,
    Int.units_mul_self, one_smul]
  exact x.coh_heq (Fin.rev_rev _) (Fin.rev_rev _) (by simp [image_image, Function.comp_def])

/-- Reflecting back and then taking the opposite returns the original simplex. -/
@[simp]
theorem Simplex.op_unop (x : Simplex R Cᵒᵖ n) : x.unop.op = x := by
  refine Simplex.ext (by ext i; simp) fun i j S d hij hS hd ↦ ?_
  dsimp only [Simplex.op, Simplex.unop, Coherences.op]
  simp only [card_image_of_injective _ Fin.rev_injective, smul_smul,
    Int.units_mul_self, one_smul]
  exact x.coh_heq (Fin.rev_rev _) (Fin.rev_rev _) (by simp [image_image, Function.comp_def])

/-- Signed reflection is a bijection between dg simplices in a category and its opposite. -/
noncomputable def Simplex.opEquiv : Simplex R C n ≃ Simplex R Cᵒᵖ n where
  toFun := Simplex.op
  invFun := Simplex.unop
  left_inv := Simplex.unop_op
  right_inv := Simplex.op_unop

/-- The reflection equivalence acts by taking the opposite simplex. -/
@[simp]
theorem Simplex.opEquiv_apply (x : Simplex R C n) : Simplex.opEquiv x = x.op := (rfl)

/-- The inverse reflection equivalence acts by taking the unopposite simplex. -/
@[simp]
theorem Simplex.opEquiv_symm_apply (x : Simplex R Cᵒᵖ n) :
    Simplex.opEquiv.symm x = x.unop := (rfl)

/-- Reflection takes the constant vertex of an object to the vertex of the opposite object. -/
@[simp]
theorem Simplex.op_vertex (X : C) : (Simplex.vertex (R := R) X).op =
    Simplex.vertex (Opposite.op X) := by
  apply Simplex.ext_zero
  simp

/-- Reflection reverses a closed edge and retains its underlying degree-zero morphism. -/
@[simp]
theorem Simplex.op_edge {X Y : C} (f : dgCycles R X Y) :
    (Simplex.edge f).op = Simplex.edge (X := Opposite.op Y) (Y := Opposite.op X)
      ⟨f.val, by simpa only [mem_dgCycles, dgDifferential_op] using f.property⟩ := by
  rw [Simplex.eq_edge (Simplex.edge f).op]
  congr 1
  apply Subtype.ext
  simp only [Simplex.op_coh, card_empty, Nat.choose_zero_succ, Nat.cast_zero,
    Int.negOnePow_zero, one_smul, image_empty]
  exact Simplex.edge_coh_zero_one f

end DGNerve

namespace dgNerve

variable (R : Type v) [CommRing R] (C : Type u) [DGCategory R C]

/-- The differential graded nerve commutes with taking opposites, by signed vertex reflection. -/
noncomputable def opIso : (dgNerve R C).op ≅ dgNerve R Cᵒᵖ :=
  NatIso.ofComponents
    (fun Δ ↦ Equiv.toIso (SSet.opObjEquiv.trans DGNerve.Simplex.opEquiv)) (by
      intro Δ Δ' α
      ext x
      -- Evaluate the opposite simplicial map before removing the component-function wrappers.
      change (SSet.opObjEquiv ((dgNerve R C).op.map α x)).op =
        (dgNerve R Cᵒᵖ).map α (SSet.opObjEquiv x).op
      rw [SSet.op_map]
      -- Both components are the signed reflection bijection of dg simplices.
      change ((SSet.opObjEquiv x).map
        (SimplexCategory.rev.map α.unop).toOrderHom).op =
        (SSet.opObjEquiv x).op.map α.unop.toOrderHom
      simpa only [SimplexCategory.rev_map_rev_map] using
        (SSet.opObjEquiv x).op_map (SimplexCategory.rev.map α.unop))

/-- The forward comparison reflects the dg simplex underlying an opposite simplex. -/
@[simp]
theorem opIso_hom_app {Δ : SimplexCategoryᵒᵖ} (x : (dgNerve R C).op.obj Δ) :
    (opIso R C).hom.app Δ x = (SSet.opObjEquiv x).op := (rfl)

/-- The inverse comparison reflects a simplex back into the original DG category. -/
@[simp]
theorem opIso_inv_app {Δ : SimplexCategoryᵒᵖ} (x : (dgNerve R Cᵒᵖ).obj Δ) :
    (opIso R C).inv.app Δ x = SSet.opObjEquiv.symm x.unop := (rfl)

end dgNerve

end TauCeti

namespace CategoryTheory.EnrichedFunctor

open TauCeti TauCeti.DGNerve

universe v u₁ u₂

variable {R : Type v} [CommRing R] {C : Type u₁} {D : Type u₂}
  [DGCategory R C] [DGCategory R D]
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)

/-- A DG functor commutes with signed reflection of dg simplices. -/
theorem mapDGNerveSimplex_op {n : ℕ} (x : Simplex R C n) :
    F.op.mapDGNerveSimplex x.op = (F.mapDGNerveSimplex x).op := by
  refine Simplex.ext rfl fun i j S d hij hS hd ↦ heq_of_eq ?_
  simp only [mapDGNerveSimplex_coh, Simplex.op, Coherences.op, op_dgMap,
    map_zsmul_unit]
  -- The opposite functor and both simplex constructions have the same vertex formula.
  rfl

end CategoryTheory.EnrichedFunctor

namespace CategoryTheory.EnrichedFunctor

open TauCeti

universe v u

variable {R : Type v} [CommRing R] {C D : Type u} [DGCategory R C] [DGCategory R D]
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)

/-- The simplicial opposite comparison is natural for DG functors. -/
theorem mapDGNerve_opIso_hom :
    SSet.opFunctor.map F.mapDGNerve ≫ (dgNerve.opIso R D).hom =
      (dgNerve.opIso R C).hom ≫ F.op.mapDGNerve := by
  ext Δ x
  -- Evaluate composition of the two component functions before using the comparison API.
  change (dgNerve.opIso R D).hom.app Δ
      ((SSet.opFunctor.map F.mapDGNerve).app Δ x) =
    F.op.mapDGNerve.app Δ ((dgNerve.opIso R C).hom.app Δ x)
  rw [dgNerve.opIso_hom_app, dgNerve.opIso_hom_app]
  rw [SSet.opFunctor_map F.mapDGNerve, F.mapDGNerve_app]
  -- Unfold the exposed dg-nerve object type when matching the opposite component.
  erw [F.op.mapDGNerve_app]
  -- The opposite-object equivalence cancels its inverse in the left composite.
  change (F.mapDGNerveSimplex (SSet.opObjEquiv x)).op =
    F.op.mapDGNerveSimplex (SSet.opObjEquiv x).op
  exact (F.mapDGNerveSimplex_op (SSet.opObjEquiv x)).symm

end CategoryTheory.EnrichedFunctor

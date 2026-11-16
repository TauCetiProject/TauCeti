/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Triangulated.Basic
public import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.CategoryTheory.Triangulated.Dense

/-!
# Classification of dense triangulated subcategories via `K₀`

This file establishes Thomason's classification of strictly full dense triangulated subcategories
of an essentially small pretriangulated category `C` in terms of subgroups of its triangulated
Grothendieck group `TauCeti.TriangulatedK0 C`.

For a strictly full dense triangulated subcategory `A` of `C`, the quotient map
`TauCeti.StableClasses.mk A` is additive on distinguished triangles, so it factors through a
surjective homomorphism `TauCeti.StableClasses.fromK0 A hdense` from `TriangulatedK0 C` to
`StableClasses A` whose kernel is precisely `(TriangulatedK0.map A.ι).range`
(`TauCeti.StableClasses.ker_fromK0`). This identifies `TauCeti.StableClasses A` with the quotient
`TriangulatedK0 C ⧸ (TriangulatedK0.map A.ι).range` (`TauCeti.StableClasses.equivQuotientK0`).

Combining this kernel identification with the zero-class criterion
`TauCeti.StableClasses.mk_eq_zero_iff` yields Thomason's `K₀`-membership criterion
(`TauCeti.DenseClasses.membership_iff`): an object `X` belongs to `A` if and only if
`TriangulatedK0.of X ∈ (TriangulatedK0.map A.ι).range`. Conversely, every subgroup `H` of
`TriangulatedK0 C` cuts out a strictly full dense triangulated subcategory
`TauCeti.DenseClasses.ofSubgroup H`, giving an order isomorphism
`TauCeti.DenseClasses.orderIso` (and unique characterization `TauCeti.DenseClasses.classification`)
between strictly full dense triangulated subcategories of `C` and subgroups of `TriangulatedK0 C`.
Applying the same stable-class construction to the kernel subcategory inside `A` shows that the
inclusion map `TriangulatedK0.map A.ι` is injective (`TauCeti.DenseClasses.map_injective`).

## Main definitions

* `TauCeti.StableClasses.fromK0`: the canonical homomorphism `TriangulatedK0 C →+ StableClasses A`
  for a dense strictly full triangulated subcategory `A`.
* `TauCeti.StableClasses.equivQuotientK0`: the isomorphism
  `StableClasses A ≃+ TriangulatedK0 C ⧸ (TriangulatedK0.map A.ι).range`.
* `TauCeti.DenseClasses.ofSubgroup`: the strictly full dense triangulated subcategory of objects
  whose `K₀`-class lies in a subgroup `H ≤ TriangulatedK0 C`.
* `TauCeti.DenseClasses.orderIso`: the inclusion-preserving bijection between strictly full dense
  triangulated subcategories of `C` and subgroups of `TriangulatedK0 C`.

## Main results

* `TauCeti.StableClasses.ker_fromK0`: `(fromK0 A hdense).ker = (TriangulatedK0.map A.ι).range`.
* `TauCeti.DenseClasses.membership_iff`: for a strictly full dense triangulated subcategory `A`,
  `A X ↔ TriangulatedK0.of X ∈ (TriangulatedK0.map A.ι).range`.
* `TauCeti.DenseClasses.classification`: every subgroup `H` of `TriangulatedK0 C` determines a
  unique strictly full dense triangulated subcategory whose membership is detected by `H`.
* `TauCeti.DenseClasses.map_injective`: for a strictly full dense triangulated subcategory `A`,
  `TriangulatedK0.map A.ι : TriangulatedK0 A.FullSubcategory →+ TriangulatedK0 C` is injective.

## References

* R. W. Thomason, *The classification of triangulated subcategories*, Compositio Math. **105**
  (1997), no. 1, 1–27, Theorem 2.1, Lemma 2.2, and Corollary 2.3.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe w w' v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [EssentiallySmall.{w} C]

namespace StableClasses

/-- **Comparison homomorphism from triangulated `K₀` to stable classes** (Thomason 1997,
Lemma 2.2): when `A` is a strictly full dense triangulated subcategory of `C`, the stable class map
`X ↦ mk A X` descends to a homomorphism `TriangulatedK0 C →+ StableClasses A`. -/
noncomputable def fromK0 (A : ObjectProperty C) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    (hdense : A.retractClosure = ⊤) : TriangulatedK0 C →+ StableClasses A :=
  let _ : AddCommGroup (StableClasses A) := addCommGroup A hdense
  TriangulatedK0.lift
    { obj := mk A
      map_distTriang := fun _ hT =>
        mk_distTriang hT (by rw [hdense]; trivial) (by rw [hdense]; trivial) }

/-- `TauCeti.StableClasses.fromK0` sends the `K₀`-class of an object to its stable class. -/
@[simp]
theorem fromK0_of (A : ObjectProperty C) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    (hdense : A.retractClosure = ⊤) (X : C) :
    fromK0 A hdense (TriangulatedK0.of X) = mk A X :=
  let _ : AddCommGroup (StableClasses A) := addCommGroup A hdense
  TriangulatedK0.lift_of _ X

/-- The comparison homomorphism `TauCeti.StableClasses.fromK0` is surjective. -/
theorem fromK0_surjective (A : ObjectProperty C) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    (hdense : A.retractClosure = ⊤) : Function.Surjective (fromK0 A hdense) := fun x => by
  induction x using induction_on with | h X =>
  exact ⟨TriangulatedK0.of X, fromK0_of A hdense X⟩

/-- The comparison homomorphism `TauCeti.StableClasses.fromK0` vanishes on the image of
`TriangulatedK0.map A.ι`. -/
@[simp]
theorem fromK0_comp_map_ι (A : ObjectProperty C) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    [EssentiallySmall.{w'} A.FullSubcategory] (hdense : A.retractClosure = ⊤) :
    (fromK0 A hdense).comp (TriangulatedK0.map A.ι) = 0 := by
  ext X
  simp [mk_eq_zero_of_prop X.property]

/-- **Kernel of `TauCeti.StableClasses.fromK0`**: an element of `TriangulatedK0 C` has zero stable
class modulo a strictly full dense triangulated subcategory `A` if and only if it lies in the range
of `TriangulatedK0.map A.ι`. -/
theorem ker_fromK0 (A : ObjectProperty C) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    [EssentiallySmall.{w'} A.FullSubcategory] (hdense : A.retractClosure = ⊤) :
    (fromK0 A hdense).ker = (TriangulatedK0.map A.ι).range := by
  ext x
  obtain ⟨X, rfl⟩ := TriangulatedK0.of_surjective x
  refine ⟨fun hx => ?_, fun ⟨y, hy⟩ => ?_⟩
  · rw [AddMonoidHom.mem_ker, fromK0_of, mk_eq_zero_iff] at hx
    exact ⟨TriangulatedK0.of ⟨X, hx⟩, TriangulatedK0.map_of A.ι ⟨X, hx⟩⟩
  · rw [AddMonoidHom.mem_ker, ← hy, ← AddMonoidHom.comp_apply, fromK0_comp_map_ι,
      AddMonoidHom.zero_apply]

/-- **Quotient identification of stable classes** (Thomason 1997, Lemma 2.2): for a strictly full
dense triangulated subcategory `A` of `C`, the group of stable classes `TauCeti.StableClasses A` is
canonically isomorphic to `TriangulatedK0 C ⧸ (TriangulatedK0.map A.ι).range`. -/
noncomputable def equivQuotientK0 (A : ObjectProperty C) [A.IsTriangulated]
    [A.IsClosedUnderIsomorphisms] [EssentiallySmall.{w'} A.FullSubcategory]
    (hdense : A.retractClosure = ⊤) :
    StableClasses A ≃+ TriangulatedK0 C ⧸ (TriangulatedK0.map A.ι).range :=
  let toFun : StableClasses A →+ TriangulatedK0 C ⧸ (TriangulatedK0.map A.ι).range :=
    lift A (fun X => QuotientAddGroup.mk (TriangulatedK0.of X))
      (fun _ _ e => by rw [TriangulatedK0.of_congr e])
      (fun X Y => by rw [TriangulatedK0.of_biprod, QuotientAddGroup.mk_add])
      (fun X hX => (QuotientAddGroup.eq_zero_iff _).2
        ⟨TriangulatedK0.of ⟨X, hX⟩, TriangulatedK0.map_of A.ι ⟨X, hX⟩⟩)
  let invFun : TriangulatedK0 C ⧸ (TriangulatedK0.map A.ι).range →+ StableClasses A :=
    QuotientAddGroup.lift (TriangulatedK0.map A.ι).range (fromK0 A hdense)
      (ker_fromK0 A hdense).ge
  { toFun := toFun
    invFun := invFun
    left_inv := fun x => by
      induction x using induction_on with | h X =>
      simp [toFun, invFun]
    right_inv := fun q => by
      induction q using QuotientAddGroup.induction_on with | H x =>
      obtain ⟨X, rfl⟩ := TriangulatedK0.of_surjective x
      simp [toFun, invFun]
    map_add' := toFun.map_add }

/-- `TauCeti.StableClasses.equivQuotientK0` sends the stable class of `X` to the coset of
`TriangulatedK0.of X`. -/
@[simp]
theorem equivQuotientK0_mk (A : ObjectProperty C) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    [EssentiallySmall.{w'} A.FullSubcategory] (hdense : A.retractClosure = ⊤) (X : C) :
    equivQuotientK0 A hdense (mk A X) = QuotientAddGroup.mk (TriangulatedK0.of X) :=
  lift_mk ..

/-- The inverse of `TauCeti.StableClasses.equivQuotientK0` sends the coset of `x` to
`fromK0 A hdense x`. -/
@[simp]
theorem equivQuotientK0_symm_mk (A : ObjectProperty C) [A.IsTriangulated]
    [A.IsClosedUnderIsomorphisms] [EssentiallySmall.{w'} A.FullSubcategory]
    (hdense : A.retractClosure = ⊤) (x : TriangulatedK0 C) :
    (equivQuotientK0 A hdense).symm (QuotientAddGroup.mk x) = fromK0 A hdense x :=
  (rfl)

end StableClasses

namespace DenseClasses

/-- **Thomason's `K₀`-membership criterion** (Thomason 1997, Theorem 2.1 and Corollary 2.3): an
object belongs to a strictly full dense triangulated subcategory `A` if and only if its class in
`TriangulatedK0 C` lies in the range of `TriangulatedK0.map A.ι`. -/
theorem membership_iff (A : ObjectProperty C) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    [EssentiallySmall.{w'} A.FullSubcategory] (hdense : A.retractClosure = ⊤) (X : C) :
    A X ↔ TriangulatedK0.of X ∈ (TriangulatedK0.map A.ι).range := by
  rw [← StableClasses.ker_fromK0 A hdense, AddMonoidHom.mem_ker, StableClasses.fromK0_of,
    StableClasses.mk_eq_zero_iff]

/-- The object property of objects of `C` whose class in `TriangulatedK0 C` lies in a subgroup
`H`. -/
def ofSubgroup (H : AddSubgroup (TriangulatedK0 C)) : ObjectProperty C :=
  fun X => TriangulatedK0.of X ∈ H

/-- Membership in `TauCeti.DenseClasses.ofSubgroup H`. -/
@[simp]
theorem ofSubgroup_apply (H : AddSubgroup (TriangulatedK0 C)) (X : C) :
    ofSubgroup H X ↔ TriangulatedK0.of X ∈ H :=
  Iff.rfl

instance (H : AddSubgroup (TriangulatedK0 C)) : (ofSubgroup H).IsClosedUnderIsomorphisms where
  of_iso e hX := by
    rw [ofSubgroup_apply, ← TriangulatedK0.of_congr e]
    exact hX

instance (H : AddSubgroup (TriangulatedK0 C)) : (ofSubgroup H).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, by simp⟩
  isStableUnderShiftBy n := ⟨fun X hX => by
    dsimp only [ObjectProperty.shift]
    rw [ofSubgroup_apply, TriangulatedK0.of_shift]
    exact H.zsmul_mem hX _⟩
  ext₂' T hT h₁ h₃ := (ofSubgroup H).le_isoClosure _ (by
    rw [ofSubgroup_apply, TriangulatedK0.of_distTriang hT]
    exact H.add_mem h₁ h₃)

/-- Every subcategory `TauCeti.DenseClasses.ofSubgroup H` is dense in `C`: each object `X` is a
retract of `X ⊞ X⟦1⟧`, whose `K₀`-class vanishes. -/
theorem retractClosure_ofSubgroup (H : AddSubgroup (TriangulatedK0 C)) :
    (ofSubgroup H).retractClosure = ⊤ :=
  eq_top_iff.2 fun X _ =>
    ⟨X ⊞ X⟦(1 : ℤ)⟧, by
      rw [ofSubgroup_apply, TriangulatedK0.of_biprod, TriangulatedK0.of_shift_one, add_neg_cancel]
      exact H.zero_mem,
      ⟨{ i := biprod.inl, r := biprod.fst, retract := biprod.inl_fst }⟩⟩

/-- The image of `K₀` of `TauCeti.DenseClasses.ofSubgroup H` in `TriangulatedK0 C` recovers `H`. -/
@[simp]
theorem range_map_ι_ofSubgroup (H : AddSubgroup (TriangulatedK0 C))
    [EssentiallySmall.{w'} (ofSubgroup H).FullSubcategory] :
    (TriangulatedK0.map (ofSubgroup H).ι).range = H := by
  ext x
  obtain ⟨X, rfl⟩ := TriangulatedK0.of_surjective x
  rw [TriangulatedK0.mem_range_map_ι_iff]
  exact ⟨fun ⟨_, hY, hXY⟩ => hXY ▸ hY, fun hX => ⟨X, hX, rfl⟩⟩

/-- Recovering a strictly full dense triangulated subcategory from the range of its `K₀`-inclusion.
-/
theorem ofSubgroup_range_map_ι (A : ObjectProperty C) [A.IsTriangulated]
    [A.IsClosedUnderIsomorphisms] [EssentiallySmall.{w'} A.FullSubcategory]
    (hdense : A.retractClosure = ⊤) :
    ofSubgroup (TriangulatedK0.map A.ι).range = A := by
  ext X
  exact (membership_iff A hdense X).symm

/-- **Thomason's classification of dense triangulated subcategories** (Thomason 1997, Theorem 2.1):
every subgroup `H` of `TriangulatedK0 C` determines a unique strictly full dense triangulated
subcategory whose membership is detected by `H`. -/
theorem classification (H : AddSubgroup (TriangulatedK0 C)) :
    ∃! A : ObjectProperty C,
      A.IsTriangulated ∧ A.IsClosedUnderIsomorphisms ∧ A.retractClosure = ⊤ ∧
        ∀ X : C, A X ↔ TriangulatedK0.of X ∈ H := by
  refine ⟨ofSubgroup H, ⟨inferInstance, inferInstance, retractClosure_ofSubgroup H,
    ofSubgroup_apply H⟩, ?_⟩
  rintro A ⟨_, _, _, hA⟩
  ext X
  exact hA X

/-- **Thomason's classification as an order isomorphism** (Thomason 1997, Theorem 2.1): strictly
full dense triangulated subcategories of `C`, ordered by inclusion, correspond order-isomorphically
to subgroups of `TriangulatedK0 C`. -/
noncomputable def orderIso :
    {A : ObjectProperty C // A.IsTriangulated ∧ A.IsClosedUnderIsomorphisms ∧
      A.retractClosure = ⊤} ≃o AddSubgroup (TriangulatedK0 C) where
  toFun A :=
    have _ := A.2.1
    (TriangulatedK0.map A.1.ι).range
  invFun H := ⟨ofSubgroup H, inferInstance, inferInstance, retractClosure_ofSubgroup H⟩
  left_inv A := by
    rcases A with ⟨A, htri, hiso, hdense⟩
    exact Subtype.ext (ofSubgroup_range_map_ι A hdense)
  right_inv H := range_map_ι_ofSubgroup H
  map_rel_iff' {A B} := by
    rcases A with ⟨A, hAtri, hAiso, hAdense⟩
    rcases B with ⟨B, hBtri, hBiso, hBdense⟩
    dsimp only [Equiv.coe_fn_mk]
    constructor
    · intro h X hX
      exact (membership_iff B hBdense X).2 (h ((membership_iff A hAdense X).1 hX))
    · intro h x hx
      rw [TriangulatedK0.mem_range_map_ι_iff] at hx ⊢
      obtain ⟨X, hAX, rfl⟩ := hx
      exact ⟨X, h X hAX, rfl⟩

/-- `TauCeti.DenseClasses.orderIso` sends a strictly full dense triangulated subcategory `A` to the
range of `TriangulatedK0.map A.ι`. -/
@[simp]
theorem orderIso_apply (A : ObjectProperty C) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    (hdense : A.retractClosure = ⊤) :
    orderIso ⟨A, ‹_›, ‹_›, hdense⟩ = (TriangulatedK0.map A.ι).range :=
  (rfl)

/-- The inverse of `TauCeti.DenseClasses.orderIso` sends a subgroup `H` to
`TauCeti.DenseClasses.ofSubgroup H`. -/
@[simp]
theorem orderIso_symm_apply_coe (H : AddSubgroup (TriangulatedK0 C)) :
    ((orderIso (C := C)).symm H : ObjectProperty C) = ofSubgroup H :=
  (rfl)

/-- **Injectivity on `K₀` of a dense triangulated inclusion** (Thomason 1997, Corollary 2.3): for a
strictly full dense triangulated subcategory `A` of `C`, the induced homomorphism
`TriangulatedK0.map A.ι : TriangulatedK0 A.FullSubcategory →+ TriangulatedK0 C` is injective. -/
theorem map_injective (A : ObjectProperty C) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    [EssentiallySmall.{w'} A.FullSubcategory] (hdense : A.retractClosure = ⊤) :
    Function.Injective (TriangulatedK0.map A.ι) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨⟨X, hX⟩, rfl⟩ := TriangulatedK0.of_surjective a
  simp only [TriangulatedK0.map_of, ObjectProperty.ι_obj] at ha
  let B : ObjectProperty C := fun Y =>
    ∃ hY : A Y, (TriangulatedK0.of (⟨Y, hY⟩ : A.FullSubcategory) :
      TriangulatedK0 A.FullSubcategory) = 0
  have : B.IsClosedUnderIsomorphisms :=
    { of_iso := fun {Y Z} e ⟨hY, hY0⟩ =>
        ⟨A.prop_of_iso e hY, (TriangulatedK0.of_congr (A.isoMk e)).symm.trans hY0⟩ }
  have hshift : ∀ (n : ℤ) {Y : C} (hY : A Y),
      (TriangulatedK0.of (⟨Y⟦n⟧, A.le_shift n Y hY⟩ : A.FullSubcategory) :
        TriangulatedK0 A.FullSubcategory) =
      (n.negOnePow : ℤ) • TriangulatedK0.of (⟨Y, hY⟩ : A.FullSubcategory) := fun n Y hY => by
    rw [← TriangulatedK0.of_congr (A.isoMk ((A.ι.commShiftIso n).app ⟨Y, hY⟩)),
      TriangulatedK0.of_shift]
  have : B.IsTriangulated :=
    { exists_zero := ⟨0, isZero_zero C, A.prop_zero, TriangulatedK0.of_eq_zero_of_isZero
        ((IsZero.iff_id_eq_zero _).2 (by ext))⟩
      isStableUnderShiftBy := fun n => ⟨fun Y ⟨hY, hY0⟩ =>
        ⟨A.le_shift n Y hY, by rw [hshift n hY, hY0, smul_zero]⟩⟩
      ext₂' := fun T hT ⟨h₁, h₁0⟩ ⟨h₃, h₃0⟩ => by
        have h₂ : A T.obj₂ := A.ext_of_isTriangulatedClosed₂ T hT h₁ h₃
        refine B.le_isoClosure _ ⟨h₂, ?_⟩
        rw [TriangulatedK0.of_fullSubcategory_distTriang A hT h₁ h₂ h₃, h₁0, h₃0, add_zero] }
  have hBdense : B.retractClosure = ⊤ := eq_top_iff.2 fun Y _ => by
    have hW : A (Y ⊞ Y⟦(1 : ℤ)⟧) :=
      A.prop_biprod_shift_one_of_retractClosure (by rw [hdense]; trivial)
    set W := Y ⊞ Y⟦(1 : ℤ)⟧
    have hW₁ : A (W⟦(1 : ℤ)⟧) := A.le_shift (1 : ℤ) W hW
    have hWW₁ : A (W ⊞ W⟦(1 : ℤ)⟧) := A.prop_biprod_of_isClosedUnderBinaryProducts hW hW₁
    have hsum :
        (TriangulatedK0.of (⟨W ⊞ W⟦(1 : ℤ)⟧, hWW₁⟩ : A.FullSubcategory) :
          TriangulatedK0 A.FullSubcategory) =
          TriangulatedK0.of ⟨W, hW⟩ + TriangulatedK0.of ⟨W⟦(1 : ℤ)⟧, hW₁⟩ :=
      TriangulatedK0.of_fullSubcategory_distTriang A
        (binaryBiproductTriangle_distinguished W (W⟦(1 : ℤ)⟧)) hW hWW₁ hW₁
    have hBWW₁ : B (W ⊞ W⟦(1 : ℤ)⟧) := by
      refine ⟨hWW₁, ?_⟩
      rw [hsum, hshift (1 : ℤ) hW, Int.negOnePow_one, Units.val_neg, Units.val_one, neg_one_zsmul,
        add_neg_cancel]
    exact ⟨W ⊞ W⟦(1 : ℤ)⟧, hBWW₁, ⟨{
      i := biprod.inl ≫ biprod.inl
      r := biprod.fst ≫ biprod.fst
      retract := by rw [Category.assoc, biprod.inl_fst_assoc, biprod.inl_fst] }⟩⟩
  have hmk0 : StableClasses.mk B X = 0 := by
    rw [← StableClasses.fromK0_of B hBdense X, ha, map_zero]
  obtain ⟨_, h0⟩ := (StableClasses.mk_eq_zero_iff (A := B)).1 hmk0
  exact h0

end DenseClasses

end TauCeti

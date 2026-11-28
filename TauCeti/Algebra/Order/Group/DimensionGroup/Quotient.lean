/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.Algebra.Order.Group.DimensionGroup.Basic
public import TauCeti.Algebra.Order.Group.DimensionGroup.OrderIdeal
import Mathlib.Order.Atoms
import Mathlib.Tactic.Abel

/-!
# Quotients of ordered abelian groups by order ideals

For an order ideal `I` of a preordered abelian group `G`, the quotient group `G ⧸ I` carries a
natural translation-invariant partial order defined by `[x] ≤ [y] ↔ ∃ h ∈ I, x ≤ y + h`. Order
connectedness of `I` gives antisymmetry on `G ⧸ I`. Directly from the quotient order, every
nonnegative class lifts to a nonnegative representative (`Quotient.exists_nonneg_mk_eq`), and upward
directedness of `G` passes to `G ⧸ I` by surjectivity (`Quotient.isDirectedOrder`). Upward
directedness of `I` lets quotient inequalities be witnessed by nonnegative elements of `I`
(`Quotient.exists_nonneg_le_of_mk_le_mk`), so Riesz interpolation and unperforation descend
(`Quotient.hasRieszInterpolation`, `Quotient.isUnperforated`, `Quotient.isDimensionGroup`).

We also establish the universal property of `G ⧸ I` (`Quotient.lift`), positive surjectivity and
kernel exactness, the isomorphism criterion (`Quotient.liftOrderAddMonoidIso`), and the order
isomorphism between order ideals of `G ⧸ I` and order ideals of `G` containing `I`
(`orderIdealQuotientOrderIso`).

## Main definitions

* `TauCeti.OrderIdeal.instHasQuotient`: the quotient `G ⧸ I` by an order ideal `I`.
* `TauCeti.OrderIdeal.Quotient.partialOrder`, `TauCeti.OrderIdeal.Quotient.isOrderedAddMonoid`:
  the quotient partial order on `G ⧸ I`.
* `TauCeti.OrderIdeal.Quotient.mk`: the canonical monotone homomorphism `G →+o G ⧸ I`.
* `TauCeti.OrderIdeal.Quotient.lift` and `TauCeti.OrderIdeal.Quotient.liftOrderAddMonoidIso`:
  universal property of `G ⧸ I` and the first isomorphism theorem for ordered abelian groups.
* `TauCeti.OrderIdeal.orderIdealQuotientOrderIso`: order isomorphism
  `OrderIdeal (G ⧸ I) ≃o Set.Ici I`.

## Main results

* `TauCeti.OrderIdeal.Quotient.exists_nonneg_mk_eq`: every nonnegative element of `G ⧸ I` lifts
  to a nonnegative element of `G`.
* `TauCeti.OrderIdeal.Quotient.hasRieszInterpolation`,
  `TauCeti.OrderIdeal.Quotient.isUnperforated`,
  `TauCeti.OrderIdeal.Quotient.isDimensionGroup`: permanence of dimension-group axioms under
  quotients by order ideals.
* `TauCeti.OrderIdeal.isSimpleOrder_quotient_iff`: `G ⧸ I` has exactly two distinct order ideals
  iff `I` is maximal among proper order ideals (`IsCoatom I`).

## References

* K. R. Goodearl, *Partially ordered abelian groups with interpolation*, Mathematical Surveys
  and Monographs 20, AMS, 1986, Chapters 1–2.
* M. Rørdam, *Classification of nuclear C⋆-algebras*, Encyclopaedia of Mathematical Sciences
  126, Springer, 2002, §§1.4–1.5.
-/

public section

namespace TauCeti

namespace OrderIdeal

section QuotientDef

variable {G : Type*} [AddCommGroup G] [LE G]

/-- The equivalence relation `x ≈ y ↔ -x + y ∈ I` associated to an order ideal `I`, chosen to
be definitionally equal to the `AddSubgroup` quotient relation. -/
@[expose] def quotientRel (I : OrderIdeal G) : Setoid G :=
  QuotientAddGroup.leftRel I.toAddSubgroup

theorem quotientRel_iff {I : OrderIdeal G} {x y : G} :
    I.quotientRel x y ↔ x - y ∈ I := by
  rw [← Quotient.eq (r := I.quotientRel)]
  exact QuotientAddGroup.eq_iff_sub_mem

/-- The quotient `G ⧸ I` of an ordered abelian group `G` by an order ideal `I`. -/
instance instHasQuotient : HasQuotient G (OrderIdeal G) :=
  ⟨fun I ↦ Quotient I.quotientRel⟩

end QuotientDef

namespace Quotient

section AddCommGroup

variable {G : Type*} [AddCommGroup G] [LE G]

/-- The quotient abelian group structure on `G ⧸ I`, inherited from `G ⧸ I.toAddSubgroup`. -/
instance addCommGroup (I : OrderIdeal G) : AddCommGroup (G ⧸ I) :=
  inferInstanceAs <| AddCommGroup (G ⧸ I.toAddSubgroup)

end AddCommGroup

section Order

variable {G : Type*} [AddCommGroup G] [Preorder G] [IsOrderedAddMonoid G]

/-- The quotient order relation on `G ⧸ I`, defined by `[x] ≤ [y] ↔ ∃ h ∈ I, x ≤ y + h`. -/
instance le (I : OrderIdeal G) : LE (G ⧸ I) where
  le := Quotient.lift₂ (fun x y ↦ ∃ h ∈ I, x ≤ y + h) fun x₁ y₁ x₂ y₂ hx hy ↦
      propext <| by
    have hx' : x₁ - x₂ ∈ I := quotientRel_iff.1 hx
    have hy' : y₁ - y₂ ∈ I := quotientRel_iff.1 hy
    constructor <;> rintro ⟨h, hhI, hle⟩
    · refine ⟨(y₁ - y₂) + h + (x₂ - x₁),
        add_mem (add_mem hy' hhI) (neg_sub x₁ x₂ ▸ neg_mem hx'), ?_⟩
      exact le_of_eq_of_le (by abel) ((add_le_add_right hle (x₂ - x₁)).trans_eq (by abel))
    · refine ⟨(y₂ - y₁) + h + (x₁ - x₂),
        add_mem (add_mem (neg_sub y₁ y₂ ▸ neg_mem hy') hhI) hx', ?_⟩
      exact le_of_eq_of_le (by abel) ((add_le_add_right hle (x₁ - x₂)).trans_eq (by abel))

/-- The quotient partial order on `G ⧸ I`; antisymmetry follows from order-connectedness of
`I`. -/
instance partialOrder (I : OrderIdeal G) : PartialOrder (G ⧸ I) where
  le := (· ≤ ·)
  le_refl a := by
    induction a using Quotient.inductionOn with | _ x =>
    exact ⟨0, zero_mem I, by simp⟩
  le_trans a b c hab hbc := by
    induction a using Quotient.inductionOn with | _ x =>
    induction b using Quotient.inductionOn with | _ y =>
    induction c using Quotient.inductionOn with | _ z =>
    obtain ⟨h₁, hh₁, hxy⟩ := hab
    obtain ⟨h₂, hh₂, hyz⟩ := hbc
    exact ⟨h₁ + h₂, add_mem hh₁ hh₂,
      hxy.trans ((add_le_add_left hyz h₁).trans_eq (by abel))⟩
  le_antisymm a b hab hba := by
    induction a using Quotient.inductionOn with | _ x =>
    induction b using Quotient.inductionOn with | _ y =>
    obtain ⟨h₁, hh₁, hxy⟩ := hab
    obtain ⟨h₂, hh₂, hyx⟩ := hba
    have hlo : -h₂ ≤ x - y := by
      rw [neg_le_sub_iff_le_add', add_comm]
      exact hyx
    have hhi : x - y ≤ h₁ := sub_le_iff_le_add'.2 hxy
    have hsub : x - y ∈ I := I.mem_of_le_of_le (neg_mem hh₂) hh₁ hlo hhi
    exact Quotient.sound (quotientRel_iff.2 hsub)

/-- Translation invariance of the quotient partial order on `G ⧸ I`. -/
instance isOrderedAddMonoid (I : OrderIdeal G) : IsOrderedAddMonoid (G ⧸ I) where
  add_le_add_left a b hab c := by
    induction a using Quotient.inductionOn with | _ x =>
    induction b using Quotient.inductionOn with | _ y =>
    induction c using Quotient.inductionOn with | _ z =>
    obtain ⟨h, hh, hxy⟩ := hab
    have heq : y + h + z = y + z + h := by abel
    exact ⟨h, hh, (add_le_add hxy le_rfl).trans_eq heq⟩

/-- The canonical monotone quotient homomorphism `G →+o G ⧸ I`. -/
def mk (I : OrderIdeal G) : G →+o G ⧸ I where
  toAddMonoidHom := QuotientAddGroup.mk' I.toAddSubgroup
  monotone' _ _ hxy := ⟨0, zero_mem I, by simpa using hxy⟩

theorem mk_apply (I : OrderIdeal G) (x : G) :
    mk I x = QuotientAddGroup.mk' I.toAddSubgroup x := by
  rfl

theorem mk_surjective (I : OrderIdeal G) : Function.Surjective (mk I) :=
  QuotientAddGroup.mk'_surjective I.toAddSubgroup

@[elab_as_elim]
theorem induction_on {I : OrderIdeal G} {p : G ⧸ I → Prop} (q : G ⧸ I)
    (h : ∀ x : G, p (mk I x)) : p q := by
  obtain ⟨x, rfl⟩ := mk_surjective I q
  exact h x

theorem mk_eq_mk_iff {I : OrderIdeal G} {x y : G} : mk I x = mk I y ↔ x - y ∈ I := by
  rw [mk_apply, mk_apply]
  exact QuotientAddGroup.eq_iff_sub_mem

@[simp]
theorem mk_eq_zero_iff {I : OrderIdeal G} {x : G} : mk I x = 0 ↔ x ∈ I := by
  simpa [map_zero] using (mk_eq_mk_iff (I := I) (x := x) (y := 0))

/-- Adding an element of `I` does not change the quotient class `mk I x`. -/
@[simp]
theorem mk_add_of_mem {I : OrderIdeal G} {x h : G} (hh : h ∈ I) : mk I (x + h) = mk I x := by
  rw [map_add, mk_eq_zero_iff.2 hh, add_zero]

theorem ker_mk (I : OrderIdeal G) : (mk I).toAddMonoidHom.ker = I.toAddSubgroup := by
  exact QuotientAddGroup.ker_mk' I.toAddSubgroup

/-- Characterization of the quotient order in terms of representatives. -/
theorem mk_le_mk_iff {I : OrderIdeal G} {x y : G} :
    mk I x ≤ mk I y ↔ ∃ h ∈ I, x ≤ y + h := by
  exact Iff.rfl

/-- Characterization of nonnegativity in `G ⧸ I`. -/
theorem mk_nonneg_iff {I : OrderIdeal G} {x : G} :
    0 ≤ mk I x ↔ ∃ h ∈ I, 0 ≤ x + h := by
  simpa [map_zero] using (mk_le_mk_iff (I := I) (x := 0) (y := x))

/-- Every nonnegative element of `G ⧸ I` lifts to a nonnegative element of `G`. -/
theorem exists_nonneg_mk_eq (I : OrderIdeal G) {q : G ⧸ I} (hq : 0 ≤ q) :
    ∃ g : G, 0 ≤ g ∧ mk I g = q := by
  induction q using induction_on with | _ x =>
  obtain ⟨h, hhI, hx⟩ := mk_nonneg_iff.1 hq
  exact ⟨x + h, hx, mk_add_of_mem hhI⟩

/-- Using directedness of `I`, an inequality `mk I x ≤ mk I y` is witnessed by a *nonnegative*
element `h ∈ I` with `x ≤ y + h`. -/
theorem exists_nonneg_le_of_mk_le_mk {I : OrderIdeal G} {x y : G} (hxy : mk I x ≤ mk I y) :
    ∃ h ∈ I, 0 ≤ h ∧ x ≤ y + h := by
  obtain ⟨h, hhI, hle⟩ := mk_le_mk_iff.1 hxy
  obtain ⟨h', hh'I, hh'0, hhh'⟩ := I.exists_nonneg_le hhI
  exact ⟨h', hh'I, hh'0, hle.trans (add_le_add le_rfl hhh')⟩

end Order

section UniversalProperty

variable {G H : Type*} [AddCommGroup G] [Preorder G] [IsOrderedAddMonoid G]
  [AddMonoid H] [Preorder H]

omit [IsOrderedAddMonoid G] in
private def liftHom (I : OrderIdeal G) (f : G →+o H) (hf : ∀ x ∈ I, f x = 0) :
    (G ⧸ I) →+ H :=
  QuotientAddGroup.lift I.toAddSubgroup f.toAddMonoidHom hf

private theorem liftHom_mk (I : OrderIdeal G) (f : G →+o H) (hf : ∀ x ∈ I, f x = 0) (x : G) :
    liftHom I f hf (mk I x) = f x :=
  rfl

/-- Universal property of `G ⧸ I`: a monotone homomorphism `f : G →+o H` vanishing on `I`
factors uniquely through `mk I` as a monotone homomorphism `(G ⧸ I) →+o H`. -/
def lift (I : OrderIdeal G) (f : G →+o H) (hf : ∀ x ∈ I, f x = 0) :
    (G ⧸ I) →+o H where
  toAddMonoidHom := liftHom I f hf
  monotone' a b hab := by
    induction a using induction_on with | _ x =>
    induction b using induction_on with | _ y =>
    obtain ⟨h, hhI, hxy⟩ := mk_le_mk_iff.1 hab
    simp only [AddMonoidHom.toFun_eq_coe, liftHom_mk]
    exact (OrderHomClass.mono f hxy).trans_eq (by rw [map_add, hf h hhI, add_zero])

@[simp]
theorem lift_mk (I : OrderIdeal G) (f : G →+o H) (hf : ∀ x ∈ I, f x = 0) (x : G) :
    lift I f hf (mk I x) = f x := by
  rfl

/-- Two monotone homomorphisms out of `G ⧸ I` agree when their compositions with `mk I` agree. -/
@[ext 1100]
theorem hom_ext {I : OrderIdeal G} ⦃f g : (G ⧸ I) →+o H⦄
    (h : f.comp (mk I) = g.comp (mk I)) : f = g := by
  ext q
  induction q using induction_on with | _ x =>
  exact congrArg (fun φ : G →+o H ↦ φ x) h

/-- `Quotient.lift` is injective whenever nonnegative elements in the image of `f` lift to
nonnegative elements in the corresponding coset modulo `I`. -/
theorem lift_injective (I : OrderIdeal G) (f : G →+o H) (hf : ∀ x ∈ I, f x = 0)
    (hlift : ∀ g : G, 0 ≤ f g → ∃ h ∈ I, 0 ≤ g + h) :
    Function.Injective (lift I f hf) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  induction q using induction_on with | _ x =>
  rw [lift_mk] at hq
  have h0le : 0 ≤ mk I x := mk_nonneg_iff.2 (hlift x (hq ▸ le_rfl))
  have hfnx : f (-x) = 0 := by
    calc f (-x) = 0 + f (-x) := (zero_add (f (-x))).symm
      _ = f x + f (-x) := by rw [hq]
      _ = f (x + -x) := (map_add f x (-x)).symm
      _ = 0 := by rw [add_neg_cancel, map_zero]
  have hle0 : mk I x ≤ 0 := by
    rw [← neg_nonneg, ← map_neg]
    exact mk_nonneg_iff.2 (hlift (-x) (hfnx ▸ le_rfl))
  exact le_antisymm hle0 h0le

/-- `Quotient.lift` is surjective when `f` is surjective. -/
theorem lift_surjective (I : OrderIdeal G) (f : G →+o H) (hf : ∀ x ∈ I, f x = 0)
    (hsurj : Function.Surjective f) : Function.Surjective (lift I f hf) :=
  QuotientAddGroup.lift_surjective_of_surjective _ f.toAddMonoidHom hsurj hf

/-- Canonical map between quotients `G ⧸ I →+o G ⧸ J` for `I ≤ J`. -/
def factor {I J : OrderIdeal G} (hIJ : I ≤ J) : (G ⧸ I) →+o (G ⧸ J) :=
  lift I (mk J) fun _ hx ↦ mk_eq_zero_iff.2 (hIJ hx)

@[simp]
theorem factor_mk {I J : OrderIdeal G} (hIJ : I ≤ J) (x : G) :
    factor hIJ (mk I x) = mk J x :=
  lift_mk I (mk J) _ x

@[simp]
theorem factor_comp_mk {I J : OrderIdeal G} (hIJ : I ≤ J) :
    (factor hIJ).comp (mk I) = mk J := by
  ext x
  simp

end UniversalProperty

section LiftOrderAddMonoidIso

variable {G H : Type*} [AddCommGroup G] [Preorder G] [IsOrderedAddMonoid G]
  [AddCommGroup H] [Preorder H] [IsOrderedAddMonoid H]

/-- First isomorphism theorem for order ideals: if `f : G →+o H` is surjective, vanishes on `I`,
and lifts nonnegative elements within every prescribed coset modulo `I` (`0 ≤ f g` implies
`0 ≤ g + h` for some `h ∈ I`, which together with `hf` forces `ker f = I`), then `lift` is an
ordered additive isomorphism `(G ⧸ I) ≃+o H`. -/
noncomputable def liftOrderAddMonoidIso (I : OrderIdeal G) (f : G →+o H)
    (hf : ∀ x ∈ I, f x = 0) (hsurj : Function.Surjective f)
    (hlift : ∀ g : G, 0 ≤ f g → ∃ h ∈ I, 0 ≤ g + h) :
    (G ⧸ I) ≃+o H :=
  let e := AddEquiv.ofBijective (lift I f hf).toAddMonoidHom
    ⟨lift_injective I f hf hlift, lift_surjective I f hf hsurj⟩
  have he_mk (z : G) : e.toFun (mk I z) = f z :=
    (AddEquiv.ofBijective_apply _ _ _).trans (lift_mk I f hf z)
  OrderAddMonoidIso.mk e fun {a b} ↦ by
    induction a using induction_on with | _ x =>
    induction b using induction_on with | _ y =>
    refine ⟨fun hle ↦ ?_, fun hle ↦ OrderHomClass.mono (lift I f hf) hle⟩
    rw [he_mk, he_mk] at hle
    obtain ⟨h, hhI, hpos⟩ := hlift (y - x) (map_sub f y x ▸ sub_nonneg.2 hle)
    exact mk_le_mk_iff.2 ⟨h, hhI, by
      rw [← sub_nonneg]
      exact hpos.trans_eq (by abel)⟩

theorem liftOrderAddMonoidIso_apply (I : OrderIdeal G) (f : G →+o H)
    (hf : ∀ x ∈ I, f x = 0) (hsurj : Function.Surjective f)
    (hlift : ∀ g : G, 0 ≤ f g → ∃ h ∈ I, 0 ≤ g + h) (q : G ⧸ I) :
    liftOrderAddMonoidIso I f hf hsurj hlift q = lift I f hf q := by
  rfl

@[simp]
theorem liftOrderAddMonoidIso_mk (I : OrderIdeal G) (f : G →+o H)
    (hf : ∀ x ∈ I, f x = 0) (hsurj : Function.Surjective f)
    (hlift : ∀ g : G, 0 ≤ f g → ∃ h ∈ I, 0 ≤ g + h) (x : G) :
    liftOrderAddMonoidIso I f hf hsurj hlift (mk I x) = f x :=
  lift_mk I f hf x

end LiftOrderAddMonoidIso

section Permanence

variable {G : Type*} [AddCommGroup G] [Preorder G] [IsOrderedAddMonoid G]

/-- Taking the quotient by an order ideal preserves upward directedness. -/
instance isDirectedOrder (I : OrderIdeal G) [IsDirectedOrder G] : IsDirectedOrder (G ⧸ I) where
  directed a b := by
    induction a using induction_on with | _ x =>
    induction b using induction_on with | _ y =>
    obtain ⟨c, hxc, hyc⟩ := exists_ge_ge x y
    exact ⟨mk I c, OrderHomClass.mono (mk I) hxc, OrderHomClass.mono (mk I) hyc⟩

/-- Taking the quotient by an order ideal preserves Riesz interpolation. -/
theorem hasRieszInterpolation (I : OrderIdeal G) (h : HasRieszInterpolation G) :
    HasRieszInterpolation (G ⧸ I) := by
  rw [hasRieszInterpolation_iff]
  intro a₁ a₂ b₁ b₂ h₁₁ h₁₂ h₂₁ h₂₂
  induction a₁ using induction_on with | _ x₁ =>
  induction a₂ using induction_on with | _ x₂ =>
  induction b₁ using induction_on with | _ y₁ =>
  induction b₂ using induction_on with | _ y₂ =>
  obtain ⟨h₁₁', hh₁₁, le₁₁⟩ := mk_le_mk_iff.1 h₁₁
  obtain ⟨h₁₂', hh₁₂, le₁₂⟩ := mk_le_mk_iff.1 h₁₂
  obtain ⟨h₂₁', hh₂₁, le₂₁⟩ := mk_le_mk_iff.1 h₂₁
  obtain ⟨h₂₂', hh₂₂, le₂₂⟩ := mk_le_mk_iff.1 h₂₂
  obtain ⟨H₁, hH₁, hh₁₁H₁, hh₁₂H₁⟩ := I.directedOn h₁₁' hh₁₁ h₁₂' hh₁₂
  obtain ⟨H₂, hH₂, hh₂₁H₂, hh₂₂H₂⟩ := I.directedOn h₂₁' hh₂₁ h₂₂' hh₂₂
  obtain ⟨H, hH, hH₁H, hH₂H⟩ := I.directedOn H₁ hH₁ H₂ hH₂
  have leH₁₁ : x₁ ≤ y₁ + H := le₁₁.trans (add_le_add_right (hh₁₁H₁.trans hH₁H) y₁)
  have leH₁₂ : x₁ ≤ y₂ + H := le₁₂.trans (add_le_add_right (hh₁₂H₁.trans hH₁H) y₂)
  have leH₂₁ : x₂ ≤ y₁ + H := le₂₁.trans (add_le_add_right (hh₂₁H₂.trans hH₂H) y₁)
  have leH₂₂ : x₂ ≤ y₂ + H := le₂₂.trans (add_le_add_right (hh₂₂H₂.trans hH₂H) y₂)
  obtain ⟨c, hx₁c, hx₂c, hcy₁, hcy₂⟩ :=
    h.exists_ge_ge_le_le leH₁₁ leH₁₂ leH₂₁ leH₂₂
  refine ⟨mk I c, OrderHomClass.mono (mk I) hx₁c, OrderHomClass.mono (mk I) hx₂c, ?_, ?_⟩
  · exact (OrderHomClass.mono (mk I) hcy₁).trans_eq (mk_add_of_mem hH)
  · exact (OrderHomClass.mono (mk I) hcy₂).trans_eq (mk_add_of_mem hH)

/-- Taking the quotient by an order ideal preserves unperforation. -/
theorem isUnperforated (I : OrderIdeal G) (h : IsUnperforated G) : IsUnperforated (G ⧸ I) := by
  rw [isUnperforated_iff]
  intro n hn q hq
  induction q using induction_on with | _ g =>
  rw [← map_nsmul] at hq
  obtain ⟨h', hh'I, hh'0, hle⟩ := exists_nonneg_le_of_mk_le_mk hq
  have hnle : 0 ≤ n • (g + h') := by
    rw [nsmul_add]
    exact hle.trans (add_le_add le_rfl (le_self_nsmul hh'0 hn))
  have hg : 0 ≤ g + h' := h.nonneg_of_nsmul_nonneg hn hnle
  exact mk_nonneg_iff.2 ⟨h', hh'I, hg⟩

end Permanence

section DimensionGroup

/-- The quotient of a dimension group by an order ideal is again a dimension group. -/
theorem isDimensionGroup {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    (I : OrderIdeal G) (h : IsDimensionGroup G) :
    IsDimensionGroup (G ⧸ I) where
  isDirectedOrder := by
    have := h.isDirectedOrder
    infer_instance
  isUnperforated := isUnperforated I h.isUnperforated
  hasRieszInterpolation := hasRieszInterpolation I h.hasRieszInterpolation

end DimensionGroup

end Quotient

section IdealCorrespondence

variable {G : Type*} [AddCommGroup G] [Preorder G] [IsOrderedAddMonoid G]

private theorem Quotient.mem_comap_mk {I : OrderIdeal G} {K : OrderIdeal (G ⧸ I)} {x : G} :
    x ∈ K.toAddSubgroup.comap (Quotient.mk I).toAddMonoidHom ↔ Quotient.mk I x ∈ K := by
  simp [AddSubgroup.mem_comap]

/-- Preimage of an order ideal of `G ⧸ I` along `Quotient.mk I`. -/
def Quotient.comapIdeal (I : OrderIdeal G) (K : OrderIdeal (G ⧸ I)) : OrderIdeal G :=
  ofDirected (K.toAddSubgroup.comap (Quotient.mk I).toAddMonoidHom)
    (fun _ hx ↦ by
      obtain ⟨q, hqK, h0q, hxq⟩ := K.exists_nonneg_le hx
      obtain ⟨z, hz0, rfl⟩ := Quotient.exists_nonneg_mk_eq I h0q
      obtain ⟨h, hhI, hh0, hxz⟩ := Quotient.exists_nonneg_le_of_mk_le_mk hxq
      refine ⟨z + h, Quotient.mem_comap_mk.2 ?_, add_nonneg hz0 hh0, hxz⟩
      simpa [Quotient.mk_add_of_mem hhI] using hqK)
    (isHereditary_def.2 fun _ _ ha hab hb ↦
      K.isHereditary.mem_of_le ((map_zero (Quotient.mk I)).symm.trans_le
        (OrderHomClass.mono (Quotient.mk I) ha)) (OrderHomClass.mono (Quotient.mk I) hab) hb)

@[simp]
theorem Quotient.mem_comapIdeal {I : OrderIdeal G} {K : OrderIdeal (G ⧸ I)} {x : G} :
    x ∈ Quotient.comapIdeal I K ↔ Quotient.mk I x ∈ K := by
  rw [comapIdeal, mem_ofDirected]
  exact mem_comap_mk

theorem Quotient.le_comapIdeal (I : OrderIdeal G) (K : OrderIdeal (G ⧸ I)) :
    I ≤ Quotient.comapIdeal I K := by
  intro x hx
  simp [Quotient.mk_eq_zero_iff.2 hx]

/-- Image of an order ideal `J ≥ I` of `G` in the quotient `G ⧸ I`. -/
def Quotient.mapIdeal {I J : OrderIdeal G} (hIJ : I ≤ J) : OrderIdeal (G ⧸ I) where
  toAddSubgroup := J.toAddSubgroup.map (Quotient.mk I).toAddMonoidHom
  directedOn' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hzJ, hxz, hyz⟩ := J.directedOn x hx y hy
    exact ⟨Quotient.mk I z, ⟨z, hzJ, rfl⟩, OrderHomClass.mono (Quotient.mk I) hxz,
      OrderHomClass.mono (Quotient.mk I) hyz⟩
  isHereditary' := isHereditary_def.2 fun q b hq0 hqb hb ↦ by
    obtain ⟨a, ha0, rfl⟩ := Quotient.exists_nonneg_mk_eq I hq0
    obtain ⟨c, hcJ, rfl⟩ := hb
    obtain ⟨h, hhI, _, hac⟩ := Quotient.exists_nonneg_le_of_mk_le_mk hqb
    exact ⟨a, J.isHereditary.mem_of_le ha0 hac (add_mem hcJ (hIJ hhI)), rfl⟩

@[simp]
theorem Quotient.mem_mapIdeal {I J : OrderIdeal G} (hIJ : I ≤ J) {q : G ⧸ I} :
    q ∈ Quotient.mapIdeal hIJ ↔ ∃ x ∈ J, Quotient.mk I x = q := by
  exact Iff.rfl

/-- **Ideal correspondence theorem**: order ideals of `G ⧸ I` correspond order-isomorphically to
order ideals of `G` containing `I`. -/
def orderIdealQuotientOrderIso (I : OrderIdeal G) :
    OrderIdeal (G ⧸ I) ≃o Set.Ici I where
  toFun K := ⟨Quotient.comapIdeal I K, Quotient.le_comapIdeal I K⟩
  invFun J := Quotient.mapIdeal J.property
  left_inv K := by
    ext q
    induction q using Quotient.induction_on with | _ x =>
    simp only [Quotient.mem_mapIdeal, Quotient.mem_comapIdeal]
    exact ⟨fun ⟨_, hyK, hyx⟩ ↦ hyx ▸ hyK, fun hxK ↦ ⟨x, hxK, rfl⟩⟩
  right_inv J := by
    ext x
    simp only [Quotient.mem_comapIdeal, Quotient.mem_mapIdeal]
    refine ⟨fun ⟨y, hyJ, hyx⟩ ↦ ?_, fun hxJ ↦ ⟨x, hxJ, rfl⟩⟩
    have hsub : x - y ∈ I := Quotient.mk_eq_mk_iff.1 hyx.symm
    have hx : x = y + (x - y) := by abel
    rw [hx]
    exact add_mem hyJ (J.property hsub)
  map_rel_iff' {K₁ K₂} := by
    refine ⟨fun h q hq ↦ ?_,
      fun h x hx ↦ Quotient.mem_comapIdeal.2 (h (Quotient.mem_comapIdeal.1 hx))⟩
    induction q using Quotient.induction_on with | _ x =>
    exact Quotient.mem_comapIdeal.1 (h (Quotient.mem_comapIdeal.2 hq))

@[simp]
theorem orderIdealQuotientOrderIso_apply_coe (I : OrderIdeal G) (K : OrderIdeal (G ⧸ I)) :
    (orderIdealQuotientOrderIso I K : OrderIdeal G) = Quotient.comapIdeal I K := by
  rfl

@[simp]
theorem orderIdealQuotientOrderIso_symm_apply (I : OrderIdeal G) (J : Set.Ici I) :
    (orderIdealQuotientOrderIso I).symm J = Quotient.mapIdeal J.property := by
  rfl

/-- In a preordered abelian group, the quotient `G ⧸ I` has `OrderIdeal (G ⧸ I)` simple (i.e.,
exactly two distinct order ideals `⊥` and `⊤`) iff `I` is maximal among proper order ideals
(`IsCoatom I`). -/
theorem isSimpleOrder_quotient_iff (I : OrderIdeal G) :
    IsSimpleOrder (OrderIdeal (G ⧸ I)) ↔ IsCoatom I :=
  (orderIdealQuotientOrderIso I).isSimpleOrder_iff.trans Set.isSimpleOrder_Ici_iff_isCoatom

end IdealCorrespondence

end OrderIdeal

end TauCeti

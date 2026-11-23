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

For an order ideal `I` of a partially ordered abelian group `G`, the quotient group `G ⧸ I`
carries a natural translation-invariant partial order defined by
`[x] ≤ [y] ↔ ∃ h ∈ I, x ≤ y + h`. Order
connectedness of `I` gives antisymmetry, and upward directedness of `I` ensures that the quotient
order lifts nonnegative elements (`Quotient.exists_nonneg_mk_eq`) and inherits directedness,
Riesz interpolation, unperforation, and hence the dimension-group property
(`Quotient.isDimensionGroup`).

We also establish the universal property of `G ⧸ I` (`Quotient.lift`), positive surjectivity and
kernel exactness, the isomorphism criterion (`Quotient.liftOrderIso`), and the order isomorphism
between order ideals of `G ⧸ I` and order ideals of `G` containing `I`
(`orderIdealQuotientOrderIso`).

## Main definitions

* `TauCeti.OrderIdeal.instHasQuotient`: the quotient `G ⧸ I` by an order ideal `I`.
* `TauCeti.OrderIdeal.Quotient.partialOrder`, `TauCeti.OrderIdeal.Quotient.isOrderedAddMonoid`:
  the quotient partial order on `G ⧸ I`.
* `TauCeti.OrderIdeal.Quotient.mk`: the canonical monotone homomorphism `G →+o G ⧸ I`.
* `TauCeti.OrderIdeal.Quotient.lift` and `TauCeti.OrderIdeal.Quotient.liftOrderIso`: universal
  property of `G ⧸ I` and the first isomorphism theorem for ordered abelian groups.
* `TauCeti.OrderIdeal.orderIdealQuotientOrderIso`: order isomorphism
  `OrderIdeal (G ⧸ I) ≃o Set.Ici I`.

## Main results

* `TauCeti.OrderIdeal.Quotient.exists_nonneg_mk_eq`: every nonnegative element of `G ⧸ I` lifts
  to a nonnegative element of `G`.
* `TauCeti.OrderIdeal.Quotient.hasRieszInterpolation`,
  `TauCeti.OrderIdeal.Quotient.isUnperforated`,
  `TauCeti.OrderIdeal.Quotient.isDimensionGroup`: permanence of dimension-group axioms under
  quotients by order ideals.
* `TauCeti.OrderIdeal.isSimpleOrder_quotient_iff`: `G ⧸ I` has only trivial order ideals iff `I`
  is maximal proper (`IsCoatom I`).

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

variable {G : Type*} [AddCommGroup G] [PartialOrder G]

/-- The equivalence relation `x ≈ y ↔ -x + y ∈ I` associated to an order ideal `I`, chosen to
be definitionally equal to the `AddSubgroup` quotient relation. -/
@[expose] def quotientRel (I : OrderIdeal G) : Setoid G :=
  QuotientAddGroup.leftRel I.toAddSubgroup

/-- The quotient `G ⧸ I` of a partially ordered abelian group `G` by an order ideal `I`. -/
instance instHasQuotient : HasQuotient G (OrderIdeal G) :=
  ⟨fun I ↦ Quotient I.quotientRel⟩

end QuotientDef

namespace Quotient

section Order

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

instance addCommGroup (I : OrderIdeal G) : AddCommGroup (G ⧸ I) :=
  inferInstanceAs <| AddCommGroup (G ⧸ I.toAddSubgroup)

instance le (I : OrderIdeal G) : LE (G ⧸ I) where
  le := Quotient.lift₂ (fun x y ↦ ∃ h ∈ I, x ≤ y + h) fun x₁ y₁ x₂ y₂ hx hy ↦
      propext <| by
    have hx' : x₁ - x₂ ∈ I := by
      have hxrel : (QuotientAddGroup.leftRel I.toAddSubgroup).r x₁ x₂ := hx
      rw [QuotientAddGroup.leftRel_apply] at hxrel
      simpa [sub_eq_add_neg, neg_add_rev, add_comm] using neg_mem hxrel
    have hy' : y₁ - y₂ ∈ I := by
      have hyrel : (QuotientAddGroup.leftRel I.toAddSubgroup).r y₁ y₂ := hy
      rw [QuotientAddGroup.leftRel_apply] at hyrel
      simpa [sub_eq_add_neg, neg_add_rev, add_comm] using neg_mem hyrel
    constructor <;> rintro ⟨h, hhI, hle⟩
    · refine ⟨(y₁ - y₂) + h + (x₂ - x₁),
        add_mem (add_mem hy' hhI) (neg_sub x₁ x₂ ▸ neg_mem hx'), ?_⟩
      exact le_of_eq_of_le (by abel) ((add_le_add_right hle (x₂ - x₁)).trans_eq (by abel))
    · refine ⟨(y₂ - y₁) + h + (x₁ - x₂),
        add_mem (add_mem (neg_sub y₁ y₂ ▸ neg_mem hy') hhI) hx', ?_⟩
      exact le_of_eq_of_le (by abel) ((add_le_add_right hle (x₁ - x₂)).trans_eq (by abel))

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
    have hsub : x - y ∈ I := I.convex (neg_mem hh₂) hh₁ hlo hhi
    change (QuotientAddGroup.mk x : G ⧸ I.toAddSubgroup) = QuotientAddGroup.mk y
    rw [QuotientAddGroup.eq]
    change -x + y ∈ I
    simpa [sub_eq_add_neg, add_comm] using neg_mem hsub

instance isOrderedAddMonoid (I : OrderIdeal G) : IsOrderedAddMonoid (G ⧸ I) where
  add_le_add_left a b hab c := by
    induction a using Quotient.inductionOn with | _ x =>
    induction b using Quotient.inductionOn with | _ y =>
    induction c using Quotient.inductionOn with | _ z =>
    obtain ⟨h, hh, hxy⟩ := hab
    exact ⟨h, hh,
      (add_le_add hxy le_rfl).trans_eq (by rw [add_assoc, add_comm h z, ← add_assoc])⟩

/-- The canonical monotone quotient homomorphism `G →+o G ⧸ I`. -/
@[expose] def mk (I : OrderIdeal G) : G →+o G ⧸ I where
  toAddMonoidHom := QuotientAddGroup.mk' I.toAddSubgroup
  monotone' _ _ hxy := ⟨0, zero_mem I, by simpa using hxy⟩

theorem mk_surjective (I : OrderIdeal G) : Function.Surjective (mk I) :=
  QuotientAddGroup.mk'_surjective I.toAddSubgroup

@[elab_as_elim]
theorem inductionOn {I : OrderIdeal G} {p : G ⧸ I → Prop} (q : G ⧸ I)
    (h : ∀ x : G, p (mk I x)) : p q := by
  obtain ⟨x, rfl⟩ := mk_surjective I q
  exact h x

theorem mk_eq_mk_iff {I : OrderIdeal G} {x y : G} : mk I x = mk I y ↔ x - y ∈ I := by
  change (QuotientAddGroup.mk x : G ⧸ I.toAddSubgroup) = QuotientAddGroup.mk y ↔ x - y ∈ I
  rw [QuotientAddGroup.eq]
  change -x + y ∈ I ↔ x - y ∈ I
  rw [← neg_mem_iff, neg_add_rev, neg_neg, sub_eq_add_neg, add_comm]

@[simp]
theorem mk_eq_zero_iff {I : OrderIdeal G} {x : G} : mk I x = 0 ↔ x ∈ I := by
  simpa [map_zero] using (mk_eq_mk_iff (I := I) (x := x) (y := 0))

theorem ker_mk (I : OrderIdeal G) : (mk I).toAddMonoidHom.ker = I.toAddSubgroup := by
  ext x
  simp

/-- Characterization of the quotient order in terms of representatives. -/
theorem mk_le_mk_iff {I : OrderIdeal G} {x y : G} :
    mk I x ≤ mk I y ↔ ∃ h ∈ I, x ≤ y + h :=
  Iff.rfl

/-- Characterization of nonnegativity in `G ⧸ I`. -/
theorem mk_nonneg_iff {I : OrderIdeal G} {x : G} :
    0 ≤ mk I x ↔ ∃ h ∈ I, 0 ≤ x + h := by
  simpa [map_zero] using (mk_le_mk_iff (I := I) (x := 0) (y := x))

/-- Every nonnegative element of `G ⧸ I` lifts to a nonnegative element of `G`. -/
theorem exists_nonneg_mk_eq (I : OrderIdeal G) {q : G ⧸ I} (hq : 0 ≤ q) :
    ∃ g : G, 0 ≤ g ∧ mk I g = q := by
  induction q using inductionOn with | _ x =>
  obtain ⟨h, hhI, hx⟩ := mk_nonneg_iff.1 hq
  refine ⟨x + h, hx, ?_⟩
  rw [map_add, mk_eq_zero_iff.2 hhI, add_zero]

/-- Using directedness of `I`, an inequality `mk I x ≤ mk I y` is witnessed by a *nonnegative*
element `h ∈ I` with `x ≤ y + h`. -/
theorem exists_nonneg_le_of_mk_le_mk {I : OrderIdeal G} {x y : G} (hxy : mk I x ≤ mk I y) :
    ∃ h ∈ I, 0 ≤ h ∧ x ≤ y + h := by
  obtain ⟨h, hhI, hle⟩ := mk_le_mk_iff.1 hxy
  obtain ⟨h', hh'I, hh'0, hhh'⟩ := I.exists_nonneg_le hhI
  exact ⟨h', hh'I, hh'0, hle.trans (add_le_add le_rfl hhh')⟩

end Order

section UniversalProperty

variable {G H : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
  [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]

/-- Universal property of `G ⧸ I`: a monotone homomorphism `f : G →+o H` vanishing on `I`
factors uniquely through `mk I` as a monotone homomorphism `(G ⧸ I) →+o H`. -/
@[expose] def lift (I : OrderIdeal G) (f : G →+o H) (hf : ∀ x ∈ I, f x = 0) :
    (G ⧸ I) →+o H where
  toAddMonoidHom := QuotientAddGroup.lift I.toAddSubgroup f.toAddMonoidHom hf
  monotone' a b hab := by
    induction a using inductionOn with | _ x =>
    induction b using inductionOn with | _ y =>
    obtain ⟨h, hhI, hxy⟩ := mk_le_mk_iff.1 hab
    have hle : f x ≤ f (y + h) := OrderHomClass.mono f hxy
    change QuotientAddGroup.lift I.toAddSubgroup f.toAddMonoidHom hf
        (QuotientAddGroup.mk' I.toAddSubgroup x) ≤
      QuotientAddGroup.lift I.toAddSubgroup f.toAddMonoidHom hf
        (QuotientAddGroup.mk' I.toAddSubgroup y)
    simpa [hf h hhI] using hle

omit [IsOrderedAddMonoid H] in
@[simp]
theorem lift_mk (I : OrderIdeal G) (f : G →+o H) (hf : ∀ x ∈ I, f x = 0) (x : G) :
    lift I f hf (mk I x) = f x :=
  rfl

omit [IsOrderedAddMonoid H] in
theorem hom_ext {I : OrderIdeal G} {f g : (G ⧸ I) →+o H}
    (h : f.comp (mk I) = g.comp (mk I)) : f = g := by
  ext q
  induction q using inductionOn with | _ x =>
  exact congrArg (fun φ : G →+o H ↦ φ x) h

/-- First isomorphism theorem for order ideals: if `f : G →+o H` is surjective, vanishes on `I`,
and lifts nonnegative elements (`0 ≤ f g` implies `0 ≤ g + h` for some `h ∈ I`), then `lift`
is an ordered additive isomorphism `(G ⧸ I) ≃+o H`. -/
noncomputable def liftOrderIso (I : OrderIdeal G) (f : G →+o H) (hf : ∀ x ∈ I, f x = 0)
    (hsurj : Function.Surjective f) (hlift : ∀ g : G, 0 ≤ f g → ∃ h ∈ I, 0 ≤ g + h) :
    (G ⧸ I) ≃+o H :=
  have hinj : Function.Injective (lift I f hf) := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    induction q using inductionOn with | _ x =>
    rw [lift_mk] at hq
    obtain ⟨h₁, hh₁, hpos⟩ := hlift x (hq ▸ le_rfl)
    obtain ⟨h₂, hh₂, hneg⟩ := hlift (-x) (by simp [hq])
    have hxlo : -h₁ ≤ x := neg_le_iff_add_nonneg.2 hpos
    have hxhi : x ≤ h₂ := by
      have := add_le_add_right hneg x
      simpa using this
    exact mk_eq_zero_iff.2 (I.convex (neg_mem hh₁) hh₂ hxlo hxhi)
  have hsurj' : Function.Surjective (lift I f hf) := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨mk I x, lift_mk I f hf x⟩
  { AddEquiv.ofBijective (lift I f hf).toAddMonoidHom ⟨hinj, hsurj'⟩ with
    map_le_map_iff' {a b} := by
      induction a using inductionOn with | _ x =>
      induction b using inductionOn with | _ y =>
      refine ⟨fun hle ↦ ?_, fun hle ↦ OrderHomClass.mono (lift I f hf) hle⟩
      change f x ≤ f y at hle
      obtain ⟨h, hhI, hpos⟩ := hlift (y - x) (map_sub f y x ▸ sub_nonneg.2 hle)
      exact mk_le_mk_iff.2 ⟨h, hhI, by
        rw [← sub_nonneg]
        exact hpos.trans_eq (by abel)⟩ }

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

section Permanence

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- Taking the quotient by an order ideal preserves upward directedness. -/
instance isDirectedOrder (I : OrderIdeal G) [IsDirectedOrder G] : IsDirectedOrder (G ⧸ I) where
  directed a b := by
    induction a using inductionOn with | _ x =>
    induction b using inductionOn with | _ y =>
    obtain ⟨c, hxc, hyc⟩ := exists_ge_ge x y
    exact ⟨mk I c, OrderHomClass.mono (mk I) hxc, OrderHomClass.mono (mk I) hyc⟩

/-- Taking the quotient by an order ideal preserves Riesz interpolation. -/
theorem hasRieszInterpolation (I : OrderIdeal G) (h : HasRieszInterpolation G) :
    HasRieszInterpolation (G ⧸ I) := by
  rw [hasRieszInterpolation_iff]
  intro a₁ a₂ b₁ b₂ h₁₁ h₁₂ h₂₁ h₂₂
  induction a₁ using inductionOn with | _ x₁ =>
  induction a₂ using inductionOn with | _ x₂ =>
  induction b₁ using inductionOn with | _ y₁ =>
  induction b₂ using inductionOn with | _ y₂ =>
  obtain ⟨h₁₁', hh₁₁, hh₁₁0, le₁₁⟩ := exists_nonneg_le_of_mk_le_mk h₁₁
  obtain ⟨h₁₂', hh₁₂, hh₁₂0, le₁₂⟩ := exists_nonneg_le_of_mk_le_mk h₁₂
  obtain ⟨h₂₁', hh₂₁, hh₂₁0, le₂₁⟩ := exists_nonneg_le_of_mk_le_mk h₂₁
  obtain ⟨h₂₂', hh₂₂, hh₂₂0, le₂₂⟩ := exists_nonneg_le_of_mk_le_mk h₂₂
  let H : G := h₁₁' + h₁₂' + h₂₁' + h₂₂'
  have hH : H ∈ I := add_mem (add_mem (add_mem hh₁₁ hh₁₂) hh₂₁) hh₂₂
  have leH₁₁ : x₁ ≤ y₁ + H := le₁₁.trans (add_le_add le_rfl
    (le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
      (le_add_of_le_of_nonneg le_rfl hh₁₂0) hh₂₁0) hh₂₂0))
  have leH₁₂ : x₁ ≤ y₂ + H := le₁₂.trans (add_le_add le_rfl
    (le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
      (le_add_of_nonneg_left hh₁₁0) hh₂₁0) hh₂₂0))
  have leH₂₁ : x₂ ≤ y₁ + H := le₂₁.trans (add_le_add le_rfl
    (le_add_of_le_of_nonneg (le_add_of_nonneg_left (add_nonneg hh₁₁0 hh₁₂0)) hh₂₂0))
  have leH₂₂ : x₂ ≤ y₂ + H := le₂₂.trans (add_le_add le_rfl
    (le_add_of_nonneg_left (add_nonneg (add_nonneg hh₁₁0 hh₁₂0) hh₂₁0)))
  obtain ⟨c, hx₁c, hx₂c, hcy₁, hcy₂⟩ :=
    h.exists_ge_ge_le_le leH₁₁ leH₁₂ leH₂₁ leH₂₂
  refine ⟨mk I c, OrderHomClass.mono (mk I) hx₁c, OrderHomClass.mono (mk I) hx₂c, ?_, ?_⟩
  · exact (OrderHomClass.mono (mk I) hcy₁).trans_eq (by
      rw [map_add, mk_eq_zero_iff.2 hH, add_zero])
  · exact (OrderHomClass.mono (mk I) hcy₂).trans_eq (by
      rw [map_add, mk_eq_zero_iff.2 hH, add_zero])

/-- Taking the quotient by an order ideal preserves unperforation. -/
theorem isUnperforated (I : OrderIdeal G) (h : IsUnperforated G) : IsUnperforated (G ⧸ I) := by
  rw [isUnperforated_iff]
  intro n hn q hq
  induction q using inductionOn with | _ g =>
  rw [← map_nsmul] at hq
  obtain ⟨h', hh'I, hh'0, hle⟩ := exists_nonneg_le_of_mk_le_mk hq
  have hnle : 0 ≤ n • (g + h') := by
    rw [nsmul_add]
    exact hle.trans (add_le_add le_rfl (le_self_nsmul hh'0 hn))
  have hg : 0 ≤ g + h' := h.nonneg_of_nsmul_nonneg hn hnle
  exact mk_nonneg_iff.2 ⟨h', hh'I, hg⟩

/-- The quotient of a dimension group by an order ideal is again a dimension group. -/
theorem isDimensionGroup (I : OrderIdeal G) (h : IsDimensionGroup G) :
    IsDimensionGroup (G ⧸ I) where
  isDirectedOrder := @isDirectedOrder G _ _ _ I h.isDirectedOrder
  isUnperforated := isUnperforated I h.isUnperforated
  hasRieszInterpolation := hasRieszInterpolation I h.hasRieszInterpolation

end Permanence

end Quotient

section IdealCorrespondence

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- Preimage of an order ideal of `G ⧸ I` along `Quotient.mk I`. -/
def Quotient.comapIdeal (I : OrderIdeal G) (K : OrderIdeal (G ⧸ I)) : OrderIdeal G where
  toAddSubgroup := K.toAddSubgroup.comap (Quotient.mk I).toAddMonoidHom
  directedOn' x hx y hy := by
    obtain ⟨q, hqK, hxq, hyq⟩ := K.directedOn (Quotient.mk I x) hx (Quotient.mk I y) hy
    induction q using Quotient.inductionOn with | _ z =>
    obtain ⟨h₁, hh₁I, hh₁0, hxz⟩ := Quotient.exists_nonneg_le_of_mk_le_mk hxq
    obtain ⟨h₂, hh₂I, hh₂0, hyz⟩ := Quotient.exists_nonneg_le_of_mk_le_mk hyq
    refine ⟨z + (h₁ + h₂), ?_, ?_, ?_⟩
    · change Quotient.mk I (z + (h₁ + h₂)) ∈ K
      simpa [map_add, Quotient.mk_eq_zero_iff.2 (add_mem hh₁I hh₂I)] using hqK
    · exact hxz.trans (add_le_add le_rfl (le_add_of_nonneg_right hh₂0))
    · exact hyz.trans (add_le_add le_rfl (le_add_of_nonneg_left hh₁0))
  isHereditary' := isHereditary_def.2 fun _ _ ha hab hb ↦
    K.mem_of_nonneg_of_le ((map_zero (Quotient.mk I)).symm.trans_le
      (OrderHomClass.mono (Quotient.mk I) ha)) (OrderHomClass.mono (Quotient.mk I) hab) hb

@[simp]
theorem Quotient.mem_comapIdeal {I : OrderIdeal G} {K : OrderIdeal (G ⧸ I)} {x : G} :
    x ∈ Quotient.comapIdeal I K ↔ Quotient.mk I x ∈ K :=
  Iff.rfl

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
    exact ⟨a, J.mem_of_nonneg_of_le ha0 hac (add_mem hcJ (hIJ hhI)), rfl⟩

@[simp]
theorem Quotient.mem_mapIdeal {I J : OrderIdeal G} (hIJ : I ≤ J) {q : G ⧸ I} :
    q ∈ Quotient.mapIdeal hIJ ↔ ∃ x ∈ J, Quotient.mk I x = q :=
  Iff.rfl

/-- **Ideal correspondence theorem**: order ideals of `G ⧸ I` correspond order-isomorphically to
order ideals of `G` containing `I`. -/
def orderIdealQuotientOrderIso (I : OrderIdeal G) :
    OrderIdeal (G ⧸ I) ≃o Set.Ici I where
  toFun K := ⟨Quotient.comapIdeal I K, Quotient.le_comapIdeal I K⟩
  invFun J := Quotient.mapIdeal J.property
  left_inv K := by
    ext q
    induction q using Quotient.inductionOn with | _ x =>
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
    refine ⟨fun h q hq ↦ ?_, fun h x hx ↦ h hx⟩
    induction q using Quotient.inductionOn with | _ x =>
    exact h hq

/-- In a directed ordered abelian group, the quotient `G ⧸ I` has no nontrivial proper order
ideals iff `I` is maximal among proper order ideals (`IsCoatom I`). -/
theorem isSimpleOrder_quotient_iff (I : OrderIdeal G) [IsDirectedOrder G] :
    IsSimpleOrder (OrderIdeal (G ⧸ I)) ↔ IsCoatom I := by
  let heq : OrderIdeal (G ⧸ I) ≃o Set.Ici I := orderIdealQuotientOrderIso I
  have hbot_val : (heq (⊥ : OrderIdeal (G ⧸ I)) : OrderIdeal G) = I := by
    ext x; simp [heq]
  have htop_val : (heq (⊤ : OrderIdeal (G ⧸ I)) : OrderIdeal G) = ⊤ := by
    ext x; simp [heq]
  refine ⟨fun hsimple ↦ ⟨fun htop ↦ ?_, fun J hIJ ↦ ?_⟩, fun hcoat ↦ ?_⟩
  · obtain ⟨K₁, K₂, hne⟩ := hsimple.exists_pair_ne
    apply hne
    apply heq.injective
    apply Subtype.ext
    have h₁ : (heq K₁ : OrderIdeal G) = ⊤ := top_unique (htop ▸ (heq K₁).property)
    have h₂ : (heq K₂ : OrderIdeal G) = ⊤ := top_unique (htop ▸ (heq K₂).property)
    exact h₁.trans h₂.symm
  · rcases eq_bot_or_eq_top (Quotient.mapIdeal hIJ.le) with hbot | htop
    · exfalso
      have hleft : (heq (Quotient.mapIdeal hIJ.le) : OrderIdeal G) = J :=
        congrArg Subtype.val (heq.right_inv ⟨J, hIJ.le⟩)
      exact hIJ.ne' (hleft.symm.trans ((congrArg (fun K ↦ (heq K : OrderIdeal G)) hbot).trans
        hbot_val))
    · have hleft : (heq (Quotient.mapIdeal hIJ.le) : OrderIdeal G) = J :=
        congrArg Subtype.val (heq.right_inv ⟨J, hIJ.le⟩)
      exact hleft.symm.trans ((congrArg (fun K ↦ (heq K : OrderIdeal G)) htop).trans htop_val)
  · refine
      { exists_pair_ne := ⟨⊥, ⊤, fun hbot ↦ hcoat.1 ?_⟩
        eq_bot_or_eq_top := fun K ↦ ?_ }
    · exact hbot_val.symm.trans ((congrArg (fun K ↦ (heq K : OrderIdeal G)) hbot).trans htop_val)
    · have hIK : I ≤ (heq K : OrderIdeal G) := (heq K).property
      rcases eq_or_lt_of_le hIK with hEq | hLt
      · left
        exact heq.injective (Subtype.ext (hEq.symm.trans hbot_val.symm))
      · right
        exact heq.injective (Subtype.ext ((hcoat.2 _ hLt).trans htop_val.symm))

end IdealCorrespondence

end OrderIdeal

end TauCeti

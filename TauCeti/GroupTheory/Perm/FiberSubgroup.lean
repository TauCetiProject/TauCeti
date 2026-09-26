/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.Fintype.Pi
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.GroupTheory.Perm.Basic

/-!
# Permutations preserving the fibers of a map

Given `f : α → ι`, the permutations `σ` of `α` with `f (σ a) = f a` for every `a` form a subgroup
of `Equiv.Perm α`, here called `TauCeti.fiberSubgroup f`.  This file records that subgroup, the
transpositions it contains, the behaviour of the construction under conjugation and pairing two
maps, the criteria for it to be trivial and for it to be a point stabilizer, and the isomorphism
restricting a fiber-preserving permutation to each fiber,

`fiberSubgroup f ≃* ∀ i, Equiv.Perm {a // f a = i}`,

together with the two formulas reading that isomorphism, and its inverse, through a family of
equivalences `{a // f a = i} ≃ β i` of the fibers, which is how a concrete description of the
fibers is fed into it.

For finite `α` the cosets of `fiberSubgroup f` are the rearrangements of `f`: the coset of `g`
records the map `f ∘ g⁻¹`, and this identifies `Equiv.Perm α ⧸ fiberSubgroup f`, equivariantly,
with the maps `α → ι` having fibers of the same sizes as those of `f`
(`TauCeti.quotientFiberSubgroupEquiv`).  When the fibers of `f` are the rows of a tabloid this is
the description of the tabloids as the row-colourings of `α`, and the fixed points of a
permutation `π` on the cosets are the rearrangements `c` with `c ∘ π = c`
(`TauCeti.card_fixedPoints_quotient_fiberSubgroup`).

Mathlib already studies these permutations, but through the domain action of `Equiv.Perm α` on
`α → ι`: `DomMulAct.stabilizerMulEquiv` is the same isomorphism stated on
`(MulAction.stabilizer (Equiv.Perm α)ᵈᵐᵃ f)ᵐᵒᵖ`.  The `ᵈᵐᵃ`/`ᵐᵒᵖ` wrapping makes it awkward to use
where the object of interest is a subgroup of `Equiv.Perm α` itself, as it is for the row and
column groups of a Young tableau; `fiberSubgroup` is that subgroup.  The two presentations are
identified by `fiberSubgroupMulEquivStabilizer`, and the isomorphism above is Mathlib's
`DomMulAct.stabilizerMulEquiv` transported along it.
-/

public section

namespace TauCeti

variable {α ι κ : Type*}

/-- The subgroup of permutations of `α` that preserve every fiber of `f : α → ι`, that is, those
moving each point within its own fiber. -/
def fiberSubgroup (f : α → ι) : Subgroup (Equiv.Perm α) where
  carrier := {σ | ∀ a, f (σ a) = f a}
  mul_mem' hσ hτ a := (hσ _).trans (hτ a)
  one_mem' _ := rfl
  inv_mem' {σ} hσ a := by
    have h := hσ (σ⁻¹ a)
    rwa [Equiv.Perm.inv_def, Equiv.apply_symm_apply, eq_comm] at h

@[simp]
theorem mem_fiberSubgroup {f : α → ι} {σ : Equiv.Perm α} :
    σ ∈ fiberSubgroup f ↔ ∀ a, f (σ a) = f a :=
  Iff.rfl

/-- The transposition of two points lying in a common fiber of `f` preserves every fiber of `f`:
it moves each of the two points to the other, inside their shared fiber, and fixes the rest. -/
theorem swap_mem_fiberSubgroup [DecidableEq α] {f : α → ι} {x y : α} (h : f x = f y) :
    Equiv.swap x y ∈ fiberSubgroup f := by
  rw [mem_fiberSubgroup]
  intro a
  rcases eq_or_ne a x with rfl | hax
  · rw [Equiv.swap_apply_left, h]
  · rcases eq_or_ne a y with rfl | hay
    · rw [Equiv.swap_apply_right, h]
    · rw [Equiv.swap_apply_of_ne_of_ne hax hay]

/-- Conjugation by `e` transports the subgroup preserving the fibers of `f` to the subgroup
preserving the fibers of `g` when `e` identifies their fiber equivalence relations. -/
theorem fiberSubgroup_map_conj {f : α → ι} {g : α → κ} (e : Equiv.Perm α)
    (h : ∀ a b, f a = f b ↔ g (e a) = g (e b)) :
    (fiberSubgroup f).map (MulAut.conj e).toMonoidHom = fiberSubgroup g := by
  ext σ
  rw [Subgroup.mem_map_equiv, mem_fiberSubgroup, mem_fiberSubgroup]
  constructor
  · intro hσ a
    have hfa : f (e.symm (σ a)) = f (e.symm a) := by
      simpa only [MulAut.conj_symm_apply, Equiv.Perm.coe_mul, Function.comp_apply,
        Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using hσ (e.symm a)
    have ha := (h (e.symm (σ a)) (e.symm a)).mp hfa
    simpa only [MulAut.conj_symm_apply, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using ha
  · intro hσ a
    apply (h _ _).mpr
    simpa only [MulAut.conj_symm_apply, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using hσ (e a)

/-- Composing with an injective map does not change the fibers of `f`, hence neither the
permutations preserving them. -/
theorem fiberSubgroup_comp_of_injective {g : ι → κ} (hg : Function.Injective g) (f : α → ι) :
    fiberSubgroup (g ∘ f) = fiberSubgroup f := by
  ext σ
  simp only [mem_fiberSubgroup, Function.comp_apply, hg.eq_iff]

/-- Preserving the fibers of two maps at once is preserving the fibers of the paired map. -/
theorem fiberSubgroup_inf (f : α → ι) (g : α → κ) :
    fiberSubgroup f ⊓ fiberSubgroup g = fiberSubgroup fun a => (f a, g a) := by
  ext σ
  simp [Subgroup.mem_inf, Prod.ext_iff, forall_and]

/-- **A map whose fibers are `{a}` and at most one other makes the fiber subgroup a point
stabilizer.**  If `f` separates `a` from every other point and identifies all the others with one
another, then a permutation preserves the fibers of `f` exactly when it fixes `a`: the fiber `{a}`
can only be mapped to itself, and its complement -- a second fiber when it is nonempty, and empty
when `α = {a}` -- then takes care of itself. -/
theorem fiberSubgroup_eq_stabilizer {f : α → ι} {a : α} (hsep : ∀ x, x ≠ a → f x ≠ f a)
    (hrest : ∀ x y, x ≠ a → y ≠ a → f x = f y) :
    fiberSubgroup f = MulAction.stabilizer (Equiv.Perm α) a := by
  ext σ
  rw [mem_fiberSubgroup, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  constructor
  · intro hσ
    by_contra hne
    exact hsep (σ a) hne (hσ a)
  · intro hσ x
    rcases eq_or_ne x a with rfl | hx
    · rw [hσ]
    · exact hrest _ _ (fun h => hx (σ.injective (h.trans hσ.symm))) hx

/-- Only the identity preserves the fibers of an injective map, its fibers being singletons. -/
theorem fiberSubgroup_eq_bot_of_injective {f : α → ι} (hf : Function.Injective f) :
    fiberSubgroup f = ⊥ :=
  eq_bot_iff.mpr fun _ hσ => Subgroup.mem_bot.mpr (Equiv.ext fun a => hf (hσ a))

/-- If the identity is the only permutation preserving the fibers of `f`, then `f` is injective:
two points in a common fiber would be exchanged by a nontrivial fiber-preserving transposition. -/
theorem injective_of_fiberSubgroup_eq_bot {f : α → ι}
    (h : fiberSubgroup f = ⊥) : Function.Injective f := by
  classical
  intro a b hab
  by_contra hne
  have hswap : Equiv.swap a b ∈ fiberSubgroup f := swap_mem_fiberSubgroup hab
  rw [h, Subgroup.mem_bot, Equiv.Perm.one_def] at hswap
  exact hne (Equiv.swap_eq_refl_iff.mp hswap)

/-- The fibers of `f` are preserved only by the identity exactly when `f` is injective. -/
theorem fiberSubgroup_eq_bot_iff {f : α → ι} :
    fiberSubgroup f = ⊥ ↔ Function.Injective f :=
  ⟨injective_of_fiberSubgroup_eq_bot, fiberSubgroup_eq_bot_of_injective⟩

/-- The permutations preserving the fibers of `f` are the stabilizer of `f` for the domain action
of `Equiv.Perm α` on `α → ι`, read as a subgroup of `Equiv.Perm α` itself: the `ᵈᵐᵃ` and `ᵐᵒᵖ`
synonyms reverse multiplication twice, so `σ ↦ DomMulAct.mk σ` is an isomorphism. -/
def fiberSubgroupMulEquivStabilizer (f : α → ι) :
    fiberSubgroup f ≃* (MulAction.stabilizer (Equiv.Perm α)ᵈᵐᵃ f)ᵐᵒᵖ where
  toFun σ := MulOpposite.op ⟨DomMulAct.mk (σ : Equiv.Perm α),
    DomMulAct.mem_stabilizer_iff.mpr (funext (mem_fiberSubgroup.mp σ.2))⟩
  invFun g := ⟨DomMulAct.mk.symm (g.unop : (Equiv.Perm α)ᵈᵐᵃ),
    mem_fiberSubgroup.mpr (congrFun (DomMulAct.mem_stabilizer_iff.mp g.unop.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Read in `(Equiv.Perm α)ᵈᵐᵃ`, the stabilizer element attached to a fiber-preserving permutation
is that permutation. -/
-- This is the defining equation of `fiberSubgroupMulEquivStabilizer`: its `toFun` is literally
-- `fun σ => MulOpposite.op ⟨DomMulAct.mk σ, _⟩`, so after `unop` and the subtype coercion the two
-- sides are the same term and `rfl` proves it.  The definition is deliberately not `@[expose]`d, so
-- the pre-bump `simp [fiberSubgroupMulEquivStabilizer]` has nothing to unfold; the parentheses in
-- `(rfl)` keep the definitional step inside this module, leaving this lemma and
-- `fiberSubgroupMulEquivStabilizer_symm_apply_coe` as the whole interface for importers.
@[simp]
theorem fiberSubgroupMulEquivStabilizer_apply_unop_coe (f : α → ι) (σ : fiberSubgroup f) :
    ((fiberSubgroupMulEquivStabilizer f σ).unop : (Equiv.Perm α)ᵈᵐᵃ) =
      DomMulAct.mk (σ : Equiv.Perm α) := (rfl)

/-- Read in `Equiv.Perm α`, the fiber-preserving permutation attached to an element of the
stabilizer is that element. -/
@[simp]
theorem fiberSubgroupMulEquivStabilizer_symm_apply_coe (f : α → ι)
    (g : (MulAction.stabilizer (Equiv.Perm α)ᵈᵐᵃ f)ᵐᵒᵖ) :
    (((fiberSubgroupMulEquivStabilizer f).symm g : fiberSubgroup f) : Equiv.Perm α) =
      DomMulAct.mk.symm (g.unop : (Equiv.Perm α)ᵈᵐᵃ) := by
  conv_rhs => rw [← (fiberSubgroupMulEquivStabilizer f).apply_symm_apply g]
  rw [fiberSubgroupMulEquivStabilizer_apply_unop_coe, Equiv.symm_apply_apply]

/-- Restricting a fiber-preserving permutation of `α` to each fiber of `f` is an isomorphism onto
the product of the permutation groups of the fibers.

This is Mathlib's `DomMulAct.stabilizerMulEquiv` transported along
`fiberSubgroupMulEquivStabilizer`. -/
def fiberSubgroupMulEquivPiPerm (f : α → ι) :
    fiberSubgroup f ≃* ∀ i, Equiv.Perm {a // f a = i} :=
  (fiberSubgroupMulEquivStabilizer f).trans (DomMulAct.stabilizerMulEquiv f)

@[simp]
theorem fiberSubgroupMulEquivPiPerm_apply_coe (f : α → ι) (σ : fiberSubgroup f) (i : ι)
    (a : {a // f a = i}) : (fiberSubgroupMulEquivPiPerm f σ i a : α) = (σ : Equiv.Perm α) a := by
  obtain ⟨a, ha⟩ := a
  rw [fiberSubgroupMulEquivPiPerm, MulEquiv.trans_apply,
    DomMulAct.stabilizerMulEquiv_apply _ ha, fiberSubgroupMulEquivStabilizer_apply_unop_coe,
    Equiv.symm_apply_apply]

/-- The fiber-preserving permutation assembled from a family of permutations of the fibers of `f`
moves each point by the permutation of its own fiber. -/
@[simp]
theorem fiberSubgroupMulEquivPiPerm_symm_apply (f : α → ι)
    (σ : ∀ i, Equiv.Perm {a // f a = i}) (a : α) :
    ((fiberSubgroupMulEquivPiPerm f).symm σ : Equiv.Perm α) a = (σ (f a) ⟨a, rfl⟩ : α) := by
  conv_rhs => rw [← (fiberSubgroupMulEquivPiPerm f).apply_symm_apply σ]
  rw [fiberSubgroupMulEquivPiPerm_apply_coe]

section Transport

variable {β : ι → Type*}

/-- Reading `fiberSubgroupMulEquivPiPerm f` through equivalences `e i : {a // f a = i} ≃ β i` of
the fibers of `f`: the `i`-th component takes the point of `β i` matching `a` to the one matching
`σ a`.  Specialising this to a concrete family of fibers gives the component formula for the
transported isomorphism. -/
theorem fiberSubgroupMulEquivPiPerm_trans_piCongrRight_apply (f : α → ι)
    (e : ∀ i, {a // f a = i} ≃ β i) (σ : fiberSubgroup f) (i : ι) (a : {a // f a = i}) :
    (fiberSubgroupMulEquivPiPerm f).trans
        (MulEquiv.piCongrRight fun i => (e i).permCongrHom) σ i (e i a) =
      e i ⟨(σ : Equiv.Perm α) a, (mem_fiberSubgroup.mp σ.2 a).trans a.2⟩ := by
  rw [MulEquiv.trans_apply, MulEquiv.piCongrRight_apply, Equiv.permCongrHom_coe,
    Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact congrArg (e i) (Subtype.ext (fiberSubgroupMulEquivPiPerm_apply_coe f σ i a))

/-- Reading the inverse of `fiberSubgroupMulEquivPiPerm f` through equivalences
`e i : {a // f a = i} ≃ β i` of the fibers of `f`: the assembled permutation moves each point by
the permutation of its own fiber, read through `e`. -/
theorem fiberSubgroupMulEquivPiPerm_trans_piCongrRight_symm_apply (f : α → ι)
    (e : ∀ i, {a // f a = i} ≃ β i) (σ : ∀ i, Equiv.Perm (β i)) (a : α) :
    ((((fiberSubgroupMulEquivPiPerm f).trans
        (MulEquiv.piCongrRight fun i => (e i).permCongrHom)).symm σ : Equiv.Perm α) a : α) =
      ((e (f a)).symm (σ (f a) (e (f a) ⟨a, rfl⟩)) : α) := by
  rw [MulEquiv.symm_trans_apply, fiberSubgroupMulEquivPiPerm_symm_apply,
    MulEquiv.piCongrRight_symm, MulEquiv.piCongrRight_apply, Equiv.permCongrHom_symm,
    Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_symm]

end Transport

section Quotient

open Finset

variable [Fintype α]

/-- Local decidable equality for computing fiber cardinalities without an API constraint. -/
noncomputable local instance instDecidableEqFiberColour : DecidableEq ι := Classical.decEq ι

/-- **The cosets of the fiber subgroup of `f` are the rearrangements of `f`.**  The coset of `g`
in `Equiv.Perm α ⧸ fiberSubgroup f` is sent to the map `f ∘ g⁻¹`
(`TauCeti.quotientFiberSubgroupEquiv_mk`), and every map with fibers of the same sizes as those of
`f` arises in exactly one way.  The equivalence intertwines the left action of `Equiv.Perm α` on
the cosets with its action `c ↦ c ∘ π⁻¹` on maps (`TauCeti.quotientFiberSubgroupEquiv_smul`). -/
noncomputable def quotientFiberSubgroupEquiv (f : α → ι) :
    Equiv.Perm α ⧸ fiberSubgroup f ≃ {c : α → ι // ∀ i, #{a | c a = i} = #{a | f a = i}} :=
  Equiv.ofBijective
    (Quotient.lift (fun g : Equiv.Perm α => ⟨f ∘ ⇑g⁻¹, card_filter_comp_perm f g⁻¹⟩)
      fun g h hgh => Subtype.ext <| funext fun a => by
        have hk := mem_fiberSubgroup.mp (QuotientGroup.leftRel_apply.mp hgh)
        simpa only [Equiv.Perm.coe_inv, Function.comp_apply, Equiv.Perm.mul_apply,
          Equiv.apply_symm_apply] using hk (h⁻¹ a))
    ⟨fun p q => Quotient.inductionOn₂ p q fun g h hgh => by
      refine Quotient.sound (QuotientGroup.leftRel_apply.mpr (mem_fiberSubgroup.mpr fun a => ?_))
      have := congrFun (congrArg Subtype.val hgh) (h a)
      simpa only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, Quotient.lift_mk, Function.comp_apply,
        Equiv.symm_apply_apply] using this,
    fun c => by
      have hcard : ∀ i, Fintype.card {a // c.1 a = i} = Fintype.card {a // f a = i} := fun i => by
        rw [Fintype.card_subtype, Fintype.card_subtype, c.2 i]
      -- Matching the fibers of `c` with those of `f` produces `e` with `f ∘ e = c`.
      let e : Equiv.Perm α := Equiv.ofFiberEquiv fun i => Fintype.equivOfCardEq (hcard i)
      refine ⟨Quotient.mk _ e⁻¹, Subtype.ext (funext fun a => ?_)⟩
      exact (inv_inv e).symm ▸ Equiv.ofFiberEquiv_map _ a⟩

/-- The coset of `g` is sent to the rearrangement `f ∘ g⁻¹` of `f`. -/
@[simp]
theorem quotientFiberSubgroupEquiv_mk (f : α → ι) (g : Equiv.Perm α) :
    (quotientFiberSubgroupEquiv f (g : Equiv.Perm α ⧸ fiberSubgroup f) : α → ι) = f ∘ ⇑g⁻¹ :=
  (rfl)

/-- **The rearrangement equivalence is equivariant**: moving a coset by `π` precomposes the
corresponding rearrangement with `π⁻¹`. -/
@[simp]
theorem quotientFiberSubgroupEquiv_smul (f : α → ι) (π : Equiv.Perm α)
    (q : Equiv.Perm α ⧸ fiberSubgroup f) :
    (quotientFiberSubgroupEquiv f (π • q) : α → ι) = quotientFiberSubgroupEquiv f q ∘ ⇑π⁻¹ :=
  QuotientGroup.induction_on q fun g => by
    rw [MulAction.Quotient.smul_mk, quotientFiberSubgroupEquiv_mk, quotientFiberSubgroupEquiv_mk,
      smul_eq_mul, mul_inv_rev, Equiv.Perm.coe_mul, Function.comp_assoc]

/-- A coset is fixed by `π` exactly when the corresponding rearrangement of `f` is invariant
under `π`. -/
@[simp]
theorem smul_eq_self_iff_quotientFiberSubgroupEquiv (f : α → ι) (π : Equiv.Perm α)
    (q : Equiv.Perm α ⧸ fiberSubgroup f) :
    π • q = q ↔ (quotientFiberSubgroupEquiv f q : α → ι) ∘ ⇑π = quotientFiberSubgroupEquiv f q := by
  rw [← (quotientFiberSubgroupEquiv f).apply_eq_iff_eq, Subtype.ext_iff,
    quotientFiberSubgroupEquiv_smul]
  constructor
  · intro h
    conv_lhs => rw [← h]
    rw [Function.comp_assoc, Equiv.Perm.coe_inv, Equiv.symm_comp_self, Function.comp_id]
  · intro h
    conv_lhs => rw [← h]
    rw [Function.comp_assoc, Equiv.Perm.coe_inv, Equiv.self_comp_symm, Function.comp_id]

/-- **The fixed cosets of `π` count the `π`-invariant rearrangements of `f`**: the number of cosets
of the fiber subgroup of `f` fixed by `π` is the number of maps `c : α → ι` with fibers of the same
sizes as those of `f` and with `c ∘ π = c`.  For the rows of a tabloid this is the value at `π` of
the permutation character on the tabloids. -/
theorem card_fixedPoints_quotient_fiberSubgroup [Fintype ι] (f : α → ι)
    (π : Equiv.Perm α) :
    Nat.card {q : Equiv.Perm α ⧸ fiberSubgroup f // π • q = q} =
      #{c : α → ι | c ∘ π = c ∧ ∀ i, #{a | c a = i} = #{a | f a = i}} := by
  classical
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (((quotientFiberSubgroupEquiv f).subtypeEquiv
    (q := fun c : {c : α → ι // ∀ i, #{a | c a = i} = #{a | f a = i}} => c.1 ∘ π = c.1)
    fun q =>
      smul_eq_self_iff_quotientFiberSubgroupEquiv f π q).trans ?_)
  exact (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun c : α → ι => c ∘ π = c)).trans
    (Equiv.subtypeEquivRight fun _ => and_comm)

end Quotient

end TauCeti

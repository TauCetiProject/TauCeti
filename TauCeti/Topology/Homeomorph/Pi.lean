/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Defs
public import TauCeti.Data.Finset.Sum

/-!
# Homeomorphisms of products of subspaces, of products of pairs and of products over sums

Four equivalences are homeomorphisms for the product topologies:

* `Homeomorph.Set.univPi`: the subspace `Set.pi univ s` of a product is the product of the
  subspaces `s i`, upgrading `Equiv.Set.univPi`;
* `Homeomorph.arrowProdHomeomorphProdArrow`: a product of pairs is a pair of products,
  `(∀ i, X i × Y i) ≃ₜ (∀ i, X i) × (∀ i, Y i)`, upgrading `Equiv.arrowProdEquivProdArrow`;
* `Homeomorph.piFinsetSum`: a product over a finite `s ⊆ ι ⊕ ι'` is the pair of the products over
  `s.toLeft` and `s.toRight`, upgrading `Equiv.piFinsetSum`;
* `Homeomorph.piFinsetSumSdiff`: a product over the difference `t \ s` of finite sets of `ι ⊕ ι'`
  is the pair of the products over `t.toLeft \ s.toLeft` and `t.toRight \ s.toRight`, the splitting
  `Homeomorph.piFinsetSum` at `t \ s` up to `Finset.toLeft_sdiff` and `Finset.toRight_sdiff`.
-/

public section

open Set

namespace Homeomorph

variable {ι : Type*}

section univPi

variable {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (s : ∀ i, Set (X i))

/-- The subspace `Set.pi univ s` of a product is homeomorphic to the product of the subspaces
`s i`. -/
def Set.univPi : Set.pi .univ s ≃ₜ ∀ i, s i where
  toEquiv := Equiv.Set.univPi s
  continuous_toFun := continuous_pi fun i ↦
    ((continuous_apply i).comp continuous_subtypeVal).subtype_mk _
  continuous_invFun :=
    (continuous_pi fun i ↦ continuous_subtypeVal.comp (continuous_apply i)).subtype_mk _

/-- The underlying equivalence of `Homeomorph.Set.univPi` is `Equiv.Set.univPi`. -/
@[simp]
theorem Set.toEquiv_univPi : (Set.univPi s).toEquiv = Equiv.Set.univPi s :=
  (rfl)

/-- The `i`-th component of the image of a point of `Set.pi univ s` is its `i`-th coordinate. -/
@[simp]
theorem Set.coe_univPi_apply (z : Set.pi .univ s) (i : ι) :
    (Set.univPi s z i : X i) = (z : ∀ i, X i) i :=
  (rfl)

/-- The inverse of `Homeomorph.Set.univPi` assembles the coordinates into a point of the
product. -/
@[simp]
theorem Set.coe_univPi_symm_apply (z : ∀ i, s i) :
    ((Set.univPi s).symm z : ∀ i, X i) = fun i ↦ (z i : X i) :=
  (rfl)

end univPi

section arrowProd

variable (X Y : ι → Type*) [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]

/-- A product of pairs is homeomorphic to the pair of the products of the components. -/
def arrowProdHomeomorphProdArrow : (∀ i, X i × Y i) ≃ₜ (∀ i, X i) × ∀ i, Y i where
  toEquiv := Equiv.arrowProdEquivProdArrow ι X Y
  continuous_toFun := (continuous_pi fun i ↦ continuous_fst.comp (continuous_apply i)).prodMk
    (continuous_pi fun i ↦ continuous_snd.comp (continuous_apply i))
  continuous_invFun := continuous_pi fun i ↦
    ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)

/-- The underlying equivalence of `Homeomorph.arrowProdHomeomorphProdArrow` is
`Equiv.arrowProdEquivProdArrow`. -/
@[simp]
theorem toEquiv_arrowProdHomeomorphProdArrow :
    (arrowProdHomeomorphProdArrow X Y).toEquiv = Equiv.arrowProdEquivProdArrow ι X Y :=
  (rfl)

/-- `Homeomorph.arrowProdHomeomorphProdArrow` splits a product of pairs into its two
components. -/
@[simp]
theorem arrowProdHomeomorphProdArrow_apply (z : ∀ i, X i × Y i) :
    arrowProdHomeomorphProdArrow X Y z = (fun i ↦ (z i).1, fun i ↦ (z i).2) :=
  (rfl)

/-- The inverse of `Homeomorph.arrowProdHomeomorphProdArrow` pairs the two components. -/
@[simp]
theorem arrowProdHomeomorphProdArrow_symm_apply (z : (∀ i, X i) × ∀ i, Y i) :
    (arrowProdHomeomorphProdArrow X Y).symm z = fun i ↦ (z.1 i, z.2 i) :=
  (rfl)

end arrowProd

section piFinsetSum

variable {ι' : Type*} (X : ι ⊕ ι' → Type*) [∀ i, TopologicalSpace (X i)] (s : Finset (ι ⊕ ι'))

/-- A product over a finite `s ⊆ ι ⊕ ι'` is homeomorphic to the pair of the products over its left
part `s.toLeft` and its right part `s.toRight`. This is `Equiv.piFinsetSum` as a homeomorphism,
the finite-set analogue of `Homeomorph.sumPiEquivProdPi`. -/
def piFinsetSum :
    (∀ i : s, X i) ≃ₜ (∀ a : s.toLeft, X (.inl a)) × ∀ b : s.toRight, X (.inr b) where
  toEquiv := Equiv.piFinsetSum X s
  continuous_toFun := (continuous_pi fun _ ↦ continuous_apply _).prodMk
    (continuous_pi fun _ ↦ continuous_apply _)
  continuous_invFun := continuous_pi fun ⟨i, _⟩ ↦ by
    cases i
    exacts [(continuous_apply _).comp (f := Prod.fst) continuous_fst,
      (continuous_apply _).comp (f := Prod.snd) continuous_snd]

/-- The underlying equivalence of `Homeomorph.piFinsetSum` is `Equiv.piFinsetSum`. -/
@[simp]
theorem toEquiv_piFinsetSum : (piFinsetSum X s).toEquiv = Equiv.piFinsetSum X s :=
  (rfl)

/-- `Homeomorph.piFinsetSum` acts as `Equiv.piFinsetSum`. -/
@[simp]
theorem coe_piFinsetSum : ⇑(piFinsetSum X s) = Equiv.piFinsetSum X s :=
  (rfl)

/-- The inverse of `Homeomorph.piFinsetSum` acts as the inverse of `Equiv.piFinsetSum`. -/
@[simp]
theorem coe_piFinsetSum_symm : ⇑(piFinsetSum X s).symm = (Equiv.piFinsetSum X s).symm :=
  (rfl)

end piFinsetSum

section piFinsetSumSdiff

variable {ι' : Type*} [DecidableEq ι] [DecidableEq ι'] (X : ι ⊕ ι' → Type*)
  [∀ i, TopologicalSpace (X i)] (s t : Finset (ι ⊕ ι'))

/-- A product over the difference `t \ s` of finite sets of `ι ⊕ ι'` is homeomorphic to the pair of
the products over the differences `t.toLeft \ s.toLeft` and `t.toRight \ s.toRight` of their left
and right parts. This is `Homeomorph.piFinsetSum` at `t \ s` up to the equalities
`Finset.toLeft_sdiff` and `Finset.toRight_sdiff`; it is defined directly, so that an index keeps its
value and only the proof of its membership changes, and its evaluation lemmas hold by definition. -/
def piFinsetSumSdiff :
    (∀ i : ↥(t \ s), X i) ≃ₜ
      (∀ a : ↥(t.toLeft \ s.toLeft), X (.inl a)) × ∀ b : ↥(t.toRight \ s.toRight), X (.inr b) where
  toFun f :=
    (fun a ↦ f ⟨.inl a, by rw [← Finset.mem_toLeft, Finset.toLeft_sdiff]; exact a.property⟩,
      fun b ↦ f ⟨.inr b, by rw [← Finset.mem_toRight, Finset.toRight_sdiff]; exact b.property⟩)
  invFun p := fun
    | ⟨.inl a, h⟩ => p.1 ⟨a, by rw [← Finset.toLeft_sdiff]; exact Finset.mem_toLeft.2 h⟩
    | ⟨.inr b, h⟩ => p.2 ⟨b, by rw [← Finset.toRight_sdiff]; exact Finset.mem_toRight.2 h⟩
  left_inv f := funext fun ⟨i, _⟩ ↦ by cases i <;> rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_pi fun _ ↦ continuous_apply _).prodMk
    (continuous_pi fun _ ↦ continuous_apply _)
  continuous_invFun := continuous_pi fun ⟨i, _⟩ ↦ by
    cases i
    exacts [(continuous_apply _).comp (f := Prod.fst) continuous_fst,
      (continuous_apply _).comp (f := Prod.snd) continuous_snd]

/-- The left part of the image of a family under `Homeomorph.piFinsetSumSdiff` is its restriction
to `t.toLeft \ s.toLeft`. -/
@[simp]
theorem piFinsetSumSdiff_apply_fst (f : ∀ i : ↥(t \ s), X i) (a : ↥(t.toLeft \ s.toLeft)) :
    (piFinsetSumSdiff X s t f).1 a =
      f ⟨.inl a, by rw [← Finset.mem_toLeft, Finset.toLeft_sdiff]; exact a.property⟩ :=
  (rfl)

/-- The right part of the image of a family under `Homeomorph.piFinsetSumSdiff` is its restriction
to `t.toRight \ s.toRight`. -/
@[simp]
theorem piFinsetSumSdiff_apply_snd (f : ∀ i : ↥(t \ s), X i) (b : ↥(t.toRight \ s.toRight)) :
    (piFinsetSumSdiff X s t f).2 b =
      f ⟨.inr b, by rw [← Finset.mem_toRight, Finset.toRight_sdiff]; exact b.property⟩ :=
  (rfl)

/-- The inverse of `Homeomorph.piFinsetSumSdiff` reads the left family at a left-tagged index. -/
@[simp]
theorem piFinsetSumSdiff_symm_apply_inl
    (p : (∀ a : ↥(t.toLeft \ s.toLeft), X (.inl a)) × ∀ b : ↥(t.toRight \ s.toRight), X (.inr b))
    (a : ι) (h : .inl a ∈ t \ s) :
    (piFinsetSumSdiff X s t).symm p ⟨.inl a, h⟩ =
      p.1 ⟨a, by rw [← Finset.toLeft_sdiff]; exact Finset.mem_toLeft.2 h⟩ :=
  (rfl)

/-- The inverse of `Homeomorph.piFinsetSumSdiff` reads the right family at a right-tagged index. -/
@[simp]
theorem piFinsetSumSdiff_symm_apply_inr
    (p : (∀ a : ↥(t.toLeft \ s.toLeft), X (.inl a)) × ∀ b : ↥(t.toRight \ s.toRight), X (.inr b))
    (b : ι') (h : .inr b ∈ t \ s) :
    (piFinsetSumSdiff X s t).symm p ⟨.inr b, h⟩ =
      p.2 ⟨b, by rw [← Finset.toRight_sdiff]; exact Finset.mem_toRight.2 h⟩ :=
  (rfl)

end piFinsetSumSdiff

end Homeomorph

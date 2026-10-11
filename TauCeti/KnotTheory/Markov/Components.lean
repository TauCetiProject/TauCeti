/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Markov.Basic
import TauCeti.GroupTheory.Perm.Splice

/-!
# Transporting braid-closure components through Markov moves

Conjugation relabels components by the conjugating braid's permutation. Stabilization
includes each old strand and inserts the new strand into the component of the old last
strand. These explicit bijections transport per-component data; an equality of component
counts alone does not specify that transport.

For framed closures the coefficients are relative to the Seifert framing. Transporting
these coefficients preserves them on each corresponding component, for either sign of
stabilization. They are independent of the blackboard framing, which stabilization changes.

Reference: J. Birman, *Braids, Links, and Mapping Class Groups*, Theorem 2.3, for Markov
moves; R. Gompf and A. Stipsicz, *4-Manifolds and Kirby Calculus*, Section 4.5, for integer
framing coefficients relative to the Seifert framing.
-/

public section

noncomputable section

namespace TauCeti

open BraidGroup Equiv.Perm

namespace MarkovBraid

variable {n : ℕ}

/-- Conjugation carries each component along the conjugating braid's strand permutation. -/
def conjComponentsEquiv (b c : BraidGroup (n + 1)) :
    (⟨n, b⟩ : MarkovBraid).Components ≃ (⟨n, c * b * c⁻¹⟩ : MarkovBraid).Components :=
  Quotient.congr (permHom (n + 1) c) fun x y => by
    -- Read the quotient setoids as their cycle relations to use the conjugation theorem.
    change (permHom (n + 1) b).SameCycle x y ↔
      (permHom (n + 1) (c * b * c⁻¹)).SameCycle
        (permHom (n + 1) c x) (permHom (n + 1) c y)
    simp

/-- The component bijection for conjugation applies the conjugating strand permutation. -/
@[simp] theorem conjComponentsEquiv_mk (b c : BraidGroup (n + 1)) (i : Fin (n + 1)) :
    conjComponentsEquiv b c (Quotient.mk _ i) = Quotient.mk _ (permHom (n + 1) c i) := (rfl)

/-- The inverse conjugation correspondence follows the inverse strand permutation. -/
@[simp] theorem conjComponentsEquiv_symm_mk (b c : BraidGroup (n + 1))
    (i : Fin (n + 1)) :
    (conjComponentsEquiv b c).symm (Quotient.mk _ i) =
      Quotient.mk _ ((permHom (n + 1) c).symm i) := by
  apply (conjComponentsEquiv b c).injective
  rw [Equiv.apply_symm_apply, conjComponentsEquiv_mk]
  simp

-- Preserve the named `Semiconj` type: an extracted lambda proof prevents rewriting the
-- orbit equivalence at the transparency level used by `rw`.
private theorem semiconj_permHom_strandIncl (b : BraidGroup (n + 1)) :
    Function.Semiconj Fin.castSucc (permHom (n + 1) b) (permHom (n + 2) (strandIncl b)) :=
  fun i => (permHom_strandIncl_castSucc b i).symm

private def spliceComponentsEquiv (b : BraidGroup (n + 1)) :
    (⟨n, b⟩ : MarkovBraid).Components ≃ Quotient (SameCycle.setoid
      (permHom (n + 2) (strandIncl b) * Equiv.swap (Fin.castSucc (Fin.last n))
        (Fin.last (n + 1)))) :=
  orbitQuotientEquivSplice (permHom (n + 1) b) (permHom (n + 2) (strandIncl b))
    Fin.castSucc (Fin.last (n + 1)) (Fin.last n) (Fin.castSucc_injective _)
    (fun i => (Fin.castSucc_lt_last i).ne)
    (fun _ hy => Fin.eq_castSucc_of_ne_last hy)
    (semiconj_permHom_strandIncl b)

/-- Positive stabilization preserves components by including the old strands. -/
def stabilizeComponentsEquiv (b : BraidGroup (n + 1)) :
    (⟨n, b⟩ : MarkovBraid).Components ≃
      (⟨n + 1, strandIncl b * sigma (Fin.last n)⟩ : MarkovBraid).Components :=
  (spliceComponentsEquiv b).trans (Quotient.congrRight fun _ _ => by
    rw [map_mul, permHom_sigma_last])

/-- Negative stabilization has the same component correspondence as positive stabilization. -/
def stabilizeInvComponentsEquiv (b : BraidGroup (n + 1)) :
    (⟨n, b⟩ : MarkovBraid).Components ≃
      (⟨n + 1, strandIncl b * (sigma (Fin.last n))⁻¹⟩ : MarkovBraid).Components :=
  (spliceComponentsEquiv b).trans (Quotient.congrRight fun _ _ => by
    rw [map_mul, map_inv, permHom_sigma_last, Equiv.swap_inv])

/-- Positive stabilization sends each old strand to its inclusion. -/
@[simp] theorem stabilizeComponentsEquiv_mk (b : BraidGroup (n + 1)) (i : Fin (n + 1)) :
    stabilizeComponentsEquiv b (Quotient.mk _ i) = Quotient.mk _ (Fin.castSucc i) := by
  unfold stabilizeComponentsEquiv spliceComponentsEquiv
  rw [Equiv.trans_apply, orbitQuotientEquivSplice_mk]
  rfl

/-- Negative stabilization sends each old strand to its inclusion. -/
@[simp] theorem stabilizeInvComponentsEquiv_mk (b : BraidGroup (n + 1)) (i : Fin (n + 1)) :
    stabilizeInvComponentsEquiv b (Quotient.mk _ i) = Quotient.mk _ (Fin.castSucc i) := by
  unfold stabilizeInvComponentsEquiv spliceComponentsEquiv
  rw [Equiv.trans_apply, orbitQuotientEquivSplice_mk]
  rfl

/-- The inverse positive-stabilization correspondence recovers the component of an old strand. -/
@[simp] theorem stabilizeComponentsEquiv_symm_mk (b : BraidGroup (n + 1)) (i : Fin (n + 1)) :
    (stabilizeComponentsEquiv b).symm (Quotient.mk _ (Fin.castSucc i)) = Quotient.mk _ i := by
  rw [← stabilizeComponentsEquiv_mk b i]
  exact Equiv.symm_apply_apply _ _

/-- The inverse negative-stabilization correspondence recovers the component of an old strand. -/
@[simp] theorem stabilizeInvComponentsEquiv_symm_mk (b : BraidGroup (n + 1)) (i : Fin (n + 1)) :
    (stabilizeInvComponentsEquiv b).symm (Quotient.mk _ (Fin.castSucc i)) = Quotient.mk _ i := by
  rw [← stabilizeInvComponentsEquiv_mk b i]
  exact Equiv.symm_apply_apply _ _

/-- Under positive stabilization the new strand joins the old last strand's component. -/
@[simp] theorem stabilizeComponentsEquiv_symm_mk_last (b : BraidGroup (n + 1)) :
    (stabilizeComponentsEquiv b).symm (Quotient.mk _ (Fin.last (n + 1))) =
      Quotient.mk _ (Fin.last n) := by
  unfold stabilizeComponentsEquiv spliceComponentsEquiv
  rw [Equiv.symm_trans_apply]
  exact orbitQuotientEquivSplice_symm_mk_new _ _ _ _ _ _ _ _ _

/-- Under negative stabilization the new strand joins the old last strand's component. -/
@[simp] theorem stabilizeInvComponentsEquiv_symm_mk_last (b : BraidGroup (n + 1)) :
    (stabilizeInvComponentsEquiv b).symm (Quotient.mk _ (Fin.last (n + 1))) =
      Quotient.mk _ (Fin.last n) := by
  unfold stabilizeInvComponentsEquiv spliceComponentsEquiv
  rw [Equiv.symm_trans_apply]
  exact orbitQuotientEquivSplice_symm_mk_new _ _ _ _ _ _ _ _ _

end MarkovBraid

namespace FramedMarkovBraid

-- The constructors expose their strand counts, which index the types of their framing arguments.

/-- Conjugate a framed braid closure, carrying its Seifert-relative coefficients along the
conjugating strand permutation. -/
abbrev conj (β : FramedMarkovBraid) (c : BraidGroup (β.forgetFraming.predStrands + 1)) :
    FramedMarkovBraid where
  forgetFraming := ⟨β.forgetFraming.predStrands, c * β.forgetFraming.braid * c⁻¹⟩
  framing := β.framing ∘ (MarkovBraid.conjComponentsEquiv β.forgetFraming.braid c).symm

/-- Forgetting the framing of conjugation gives ordinary braid conjugation. -/
@[simp] theorem forgetFraming_conj (β : FramedMarkovBraid)
    (c : BraidGroup (β.forgetFraming.predStrands + 1)) :
    (β.conj c).forgetFraming =
      ⟨β.forgetFraming.predStrands, c * β.forgetFraming.braid * c⁻¹⟩ := (rfl)

/-- Conjugation reads the old framing at the inverse image of the strand. -/
@[simp↓] theorem framing_conj_mk (β : FramedMarkovBraid)
    (c : BraidGroup (β.forgetFraming.predStrands + 1))
    (i : Fin (β.forgetFraming.predStrands + 1)) :
    (β.conj c).framing (Quotient.mk _ i) =
      β.framing (Quotient.mk _ ((permHom _ c).symm i)) := by
  unfold conj
  exact congrArg β.framing
    (MarkovBraid.conjComponentsEquiv_symm_mk β.forgetFraming.braid c i)

/-- Conjugation preserves the coefficient on each corresponding component. -/
@[simp↓] theorem framing_conj_componentsEquiv (β : FramedMarkovBraid)
    (c : BraidGroup (β.forgetFraming.predStrands + 1)) (q : β.forgetFraming.Components) :
    (β.conj c).framing (MarkovBraid.conjComponentsEquiv β.forgetFraming.braid c q) =
      β.framing q := by
  unfold conj
  exact congrArg β.framing (Equiv.symm_apply_apply _ _)

/-- Positively stabilize a framed closure, preserving the Seifert-relative framing of every
component. The new strand joins the component of the old last strand. -/
abbrev stabilize (β : FramedMarkovBraid) : FramedMarkovBraid where
  forgetFraming := ⟨β.forgetFraming.predStrands + 1,
    strandIncl β.forgetFraming.braid * sigma (Fin.last β.forgetFraming.predStrands)⟩
  framing := β.framing ∘ (MarkovBraid.stabilizeComponentsEquiv β.forgetFraming.braid).symm

/-- Negatively stabilize a framed closure, preserving its Seifert-relative coefficients. -/
abbrev stabilizeInv (β : FramedMarkovBraid) : FramedMarkovBraid where
  forgetFraming := ⟨β.forgetFraming.predStrands + 1,
    strandIncl β.forgetFraming.braid * (sigma (Fin.last β.forgetFraming.predStrands))⁻¹⟩
  framing := β.framing ∘ (MarkovBraid.stabilizeInvComponentsEquiv β.forgetFraming.braid).symm

/-- Forgetting framing gives positive stabilization of the underlying braid. -/
@[simp] theorem forgetFraming_stabilize (β : FramedMarkovBraid) :
    β.stabilize.forgetFraming = ⟨β.forgetFraming.predStrands + 1,
      strandIncl β.forgetFraming.braid * sigma (Fin.last β.forgetFraming.predStrands)⟩ := (rfl)

/-- Forgetting framing gives negative stabilization of the underlying braid. -/
@[simp] theorem forgetFraming_stabilizeInv (β : FramedMarkovBraid) :
    β.stabilizeInv.forgetFraming = ⟨β.forgetFraming.predStrands + 1,
      strandIncl β.forgetFraming.braid * (sigma (Fin.last β.forgetFraming.predStrands))⁻¹⟩ := (rfl)

/-- Positive stabilization preserves the coefficient on each corresponding component. -/
@[simp↓] theorem framing_stabilize_componentsEquiv (β : FramedMarkovBraid)
    (q : β.forgetFraming.Components) :
    β.stabilize.framing (MarkovBraid.stabilizeComponentsEquiv β.forgetFraming.braid q) =
      β.framing q := by
  unfold stabilize
  exact congrArg β.framing (Equiv.symm_apply_apply _ _)

/-- Negative stabilization preserves the coefficient on each corresponding component. -/
@[simp↓] theorem framing_stabilizeInv_componentsEquiv (β : FramedMarkovBraid)
    (q : β.forgetFraming.Components) :
    β.stabilizeInv.framing (MarkovBraid.stabilizeInvComponentsEquiv β.forgetFraming.braid q) =
      β.framing q := by
  unfold stabilizeInv
  exact congrArg β.framing (Equiv.symm_apply_apply _ _)

/-- Positive stabilization retains the framing coefficient at every old strand. -/
@[simp↓] theorem framing_stabilize_mk (β : FramedMarkovBraid)
    (i : Fin (β.forgetFraming.predStrands + 1)) :
    β.stabilize.framing (Quotient.mk _ (Fin.castSucc i)) = β.framing (Quotient.mk _ i) := by
  unfold stabilize
  exact congrArg β.framing
    (MarkovBraid.stabilizeComponentsEquiv_symm_mk β.forgetFraming.braid i)

/-- Negative stabilization retains the framing coefficient at every old strand. -/
@[simp↓] theorem framing_stabilizeInv_mk (β : FramedMarkovBraid)
    (i : Fin (β.forgetFraming.predStrands + 1)) :
    β.stabilizeInv.framing (Quotient.mk _ (Fin.castSucc i)) = β.framing (Quotient.mk _ i) := by
  unfold stabilizeInv
  exact congrArg β.framing
    (MarkovBraid.stabilizeInvComponentsEquiv_symm_mk β.forgetFraming.braid i)

/-- The new strand in positive stabilization has the old last strand's framing coefficient. -/
@[simp↓] theorem framing_stabilize_mk_last (β : FramedMarkovBraid) :
    β.stabilize.framing (Quotient.mk _ (Fin.last (β.forgetFraming.predStrands + 1))) =
      β.framing (Quotient.mk _ (Fin.last β.forgetFraming.predStrands)) := by
  unfold stabilize
  exact congrArg β.framing
    (MarkovBraid.stabilizeComponentsEquiv_symm_mk_last β.forgetFraming.braid)

/-- The new strand in negative stabilization has the old last strand's framing coefficient. -/
@[simp↓] theorem framing_stabilizeInv_mk_last (β : FramedMarkovBraid) :
    β.stabilizeInv.framing (Quotient.mk _ (Fin.last (β.forgetFraming.predStrands + 1))) =
      β.framing (Quotient.mk _ (Fin.last β.forgetFraming.predStrands)) := by
  unfold stabilizeInv
  exact congrArg β.framing
    (MarkovBraid.stabilizeInvComponentsEquiv_symm_mk_last β.forgetFraming.braid)

end FramedMarkovBraid

end TauCeti

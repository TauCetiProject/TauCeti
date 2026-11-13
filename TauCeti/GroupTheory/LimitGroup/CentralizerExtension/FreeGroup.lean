/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic
public import TauCeti.GroupTheory.FreeGroup.Centralizer
public import Mathlib.GroupTheory.PresentedGroup

/-!
# Extending the centralizer of a basis element of a free group

Let `F` be the free group on a set `X` and `a ∈ X`. The centralizer of `a` in `F` is the cyclic
group `⟨a⟩`, so the extension of the centralizer of `a` by `ℤ` is
`F(a, ℤ) = F ∗_{⟨a⟩} (⟨a⟩ × ⟨t⟩)`, the group with generators `X` and a new letter `t` and the single
relator `[a, t]`. This is the basic example of an extension of a centralizer. As an illustration
of the retractions `t ↦ a ^ k` onto `F`: for a basis element `b ≠ a`, they send `[b, t]` to
`[b, a ^ k]`, which is nontrivial for every `k ≠ 0`. That every finite family of nonidentity
elements survives under a single such retraction is the general discrimination theorem
`TauCeti.LimitGroup.CentralizerExt.isDiscriminatedBy`.

## Main definitions

* `TauCeti.LimitGroup.CentralizerExt.freeGroupOfEquivPresentedGroup`: the isomorphism of `F(a, ℤ)`
  with the presented group `⟨X, t | [a, t] = 1⟩`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.retraction_commutatorElement_ne_one`: the retraction
  `t ↦ a ^ k` keeps `[b, t]` nontrivial for every basis element `b ≠ a` and every `k ≠ 0`.

## References

* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Subgroups of fully residually
  free groups: algorithmic problems*, Contemp. Math. 360 (2004), §5.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
-/

public section

open scoped commutatorElement

namespace TauCeti.LimitGroup.CentralizerExt

variable {α : Type*}

/-- In `⟨X, t | [a, t] = 1⟩`, with `t` written `none`, the generators `a` and `t` commute. -/
private theorem commute_of_some_of_none (a : α) :
    Commute (PresentedGroup.of (some a) :
      PresentedGroup ({⁅FreeGroup.of (some a), FreeGroup.of none⁆} : Set (FreeGroup (Option α))))
      (PresentedGroup.of none) :=
  commutatorElement_eq_one_iff_commute.1 <| by
    rw [PresentedGroup.of, PresentedGroup.of, ← map_commutatorElement]
    exact PresentedGroup.one_of_mem (Set.mem_singleton _)

/-- The homomorphism `F(a, ℤ) →* ⟨X, t | [a, t] = 1⟩` that is the identity on `X` and sends the new
letter to `t`. It exists because `C_F(a) = ⟨a⟩` commutes with `t`. -/
private def toPresentedGroup (a : α) : CentralizerExt (FreeGroup.of a) 1 →*
    PresentedGroup ({⁅FreeGroup.of (some a), FreeGroup.of none⁆} : Set (FreeGroup (Option α))) :=
  lift (FreeGroup.lift fun x => PresentedGroup.of (some x)) (fun _ => PresentedGroup.of none)
    (fun _ _ => .refl _) fun c hc _ => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1
        (FreeGroup.mem_zpowers_of_of_commute (Subgroup.mem_centralizer_singleton_iff.1 hc))
      simpa using (commute_of_some_of_none a).zpow_left k

/-- The inverse of `toPresentedGroup`: the relator `[a, t]` holds in `F(a, ℤ)` because `t`
commutes with `C_F(a) ∋ a`. -/
private def ofPresentedGroup (a : α) :
    PresentedGroup ({⁅FreeGroup.of (some a), FreeGroup.of none⁆} : Set (FreeGroup (Option α))) →*
      CentralizerExt (FreeGroup.of a) 1 :=
  PresentedGroup.toGroup (f := fun x => x.elim (t 0) fun y => of (FreeGroup.of y)) fun r hr => by
    rw [Set.mem_singleton_iff.1 hr, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    simpa using commute_of_t (Subgroup.mem_centralizer_singleton_iff.2 rfl) 0

/-- The extension of the centralizer of a basis element `a` of the free group `F` on `X` by `ℤ` is
the group `⟨X, t | [a, t] = 1⟩`, with the new letter `t` written `none` in the generating set
`Option X`. -/
def freeGroupOfEquivPresentedGroup (a : α) : CentralizerExt (FreeGroup.of a) 1 ≃*
    PresentedGroup ({⁅FreeGroup.of (some a), FreeGroup.of none⁆} : Set (FreeGroup (Option α))) :=
  (toPresentedGroup a).toMulEquiv (ofPresentedGroup a)
    (hom_ext (FreeGroup.ext_hom _ _ fun x => by simp [toPresentedGroup, ofPresentedGroup])
      fun i => by simp [toPresentedGroup, ofPresentedGroup, Subsingleton.elim i 0])
    (PresentedGroup.ext fun x => by cases x <;> simp [toPresentedGroup, ofPresentedGroup])

/-- `freeGroupOfEquivPresentedGroup` on an element `g` of `F`: the class of `g`, written in the
alphabet `Option X`. -/
theorem freeGroupOfEquivPresentedGroup_of (a : α) (g : FreeGroup α) :
    freeGroupOfEquivPresentedGroup a (of g) = PresentedGroup.mk _ (FreeGroup.map some g) := by
  have h : (FreeGroup.lift fun x => PresentedGroup.of (some x)) = (PresentedGroup.mk
      ({⁅FreeGroup.of (some a), FreeGroup.of none⁆} : Set (FreeGroup (Option α)))).comp
      (FreeGroup.map some) :=
    FreeGroup.ext_hom _ _ fun x => by simp [PresentedGroup.of]
  simpa [freeGroupOfEquivPresentedGroup, toPresentedGroup] using DFunLike.congr_fun h g

@[simp] theorem freeGroupOfEquivPresentedGroup_of_of (a x : α) :
    freeGroupOfEquivPresentedGroup a (of (FreeGroup.of x)) = PresentedGroup.of (some x) := by
  simp [freeGroupOfEquivPresentedGroup, toPresentedGroup]

@[simp] theorem freeGroupOfEquivPresentedGroup_t (a : α) (i : Fin 1) :
    freeGroupOfEquivPresentedGroup a (t i) = PresentedGroup.of none := by
  simp [freeGroupOfEquivPresentedGroup, toPresentedGroup]

@[simp] theorem freeGroupOfEquivPresentedGroup_symm_of_some (a x : α) :
    (freeGroupOfEquivPresentedGroup a).symm (PresentedGroup.of (some x)) =
      of (FreeGroup.of x) := by
  simp [freeGroupOfEquivPresentedGroup, ofPresentedGroup]

@[simp] theorem freeGroupOfEquivPresentedGroup_symm_of_none (a : α) :
    (freeGroupOfEquivPresentedGroup a).symm (PresentedGroup.of none) = t 0 := by
  simp [freeGroupOfEquivPresentedGroup, ofPresentedGroup]

/-- In `F(a, ℤ) = ⟨X, t | [a, t] = 1⟩`, the retraction `t ↦ a ^ k` sends `[b, t]` to `[b, a ^ k]`,
which is nontrivial for every basis element `b ≠ a` and every `k ≠ 0`. -/
theorem retraction_commutatorElement_ne_one {a b : α} (hab : a ≠ b) {k : ℤ} (hk : k ≠ 0) :
    retraction (u := FreeGroup.of a) (n := 1) (fun _ => k)
      ⁅(of (FreeGroup.of b) : CentralizerExt (FreeGroup.of a) 1), t 0⁆ ≠ 1 := by
  rw [map_commutatorElement, retraction_of, retraction_t, Ne, commutatorElement_eq_one_iff_commute,
    ← zpow_one (FreeGroup.of b), FreeGroup.commute_of_zpow_of_zpow_iff hab.symm]
  simp [hk]

end TauCeti.LimitGroup.CentralizerExt

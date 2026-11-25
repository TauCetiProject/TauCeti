/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.BranchTuple.Hurwitz.Fiber
public import TauCeti.GroupTheory.SpecificGroups.Braid.Block
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Group
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Algebraic gluing of Hurwitz fibres

Concatenating branch tuples models gluing marked covers. Independent braids act on the two
blocks through `BraidGroup.blockSum`. A fixed prefix gives an equivariant map along
`BraidGroup.shiftHom`, which supplies the gluing maps used for stabilization. Concatenation
preserves the class condition, and a full-monodromy suffix still generates the group after
any prefix is added. The ordered boundary products multiply in block order and the generated
subgroups form a join.

## References

* J. S. Ellenberg, A. Venkatesh, C. Westerland, *Homological stability for Hurwitz spaces and the
  Cohen–Lenstra conjecture over function fields*, Ann. of Math. 183 (2016), §2.6.
-/

public section

namespace TauCeti

open BraidGroup

variable {G : Type*} [Group G] {m n : ℕ}

namespace BranchTuple

/-- A Hurwitz move in the right block leaves the prefix unchanged. -/
private theorem hurwitzMove_append (t : BranchTuple m G) (s : BranchTuple n G) (i : Fin (n - 1)) :
    hurwitzMove (⟨m + i, by have := i.isLt; omega⟩ : Fin (m + n - 1)) (Fin.append t s) =
      Fin.append t (hurwitzMove i s) := by
  have h₀ : strand (⟨m + i, by have := i.isLt; omega⟩ : Fin (m + n - 1)) =
      Fin.natAdd m (strand i) := Fin.ext (by simp)
  have h₁ : strandSucc (⟨m + i, by have := i.isLt; omega⟩ : Fin (m + n - 1)) =
      Fin.natAdd m (strandSucc i) := Fin.ext (by simp; omega)
  funext k
  induction k using Fin.addCases with
  | left k =>
    rw [hurwitzMove_apply_of_ne]
    · simp
    · intro h
      have hv := congrArg Fin.val h
      simp only [val_strand, Fin.val_castAdd] at hv
      have := k.isLt
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [val_strandSucc, Fin.val_castAdd] at hv
      have := k.isLt
      omega
  | right k =>
    simp only [hurwitzMove_apply, h₀, h₁, Fin.append_right, Fin.natAdd_inj]

/-- Concatenation with an arbitrary fixed prefix intertwines the suffix braid action with the
block inclusion. -/
theorem hurwitzAction_shift (t : BranchTuple m G) (s : BranchTuple n G) (b : BraidGroup n) :
    hurwitzAction (shiftHom m n b) (Fin.append t s) = Fin.append t (hurwitzAction b s) := by
  symm
  apply apply_hurwitzAction_of_apply_hurwitzMove
    (hurwitzAction.comp (shiftHom m n))
  intro i u
  rw [MonoidHom.comp_apply, shiftHom_sigma, hurwitzAction_sigma, hurwitzMove_append]

private theorem hurwitzMove_append_left (t : BranchTuple m G) (s : BranchTuple n G)
    (i : Fin (m - 1)) :
    hurwitzMove (⟨i, by have := i.isLt; omega⟩ : Fin (m + n - 1)) (Fin.append t s) =
      Fin.append (hurwitzMove i t) s := by
  have h₀ : strand (⟨i, by have := i.isLt; omega⟩ : Fin (m + n - 1)) =
      Fin.castAdd n (strand i) := Fin.ext (by simp)
  have h₁ : strandSucc (⟨i, by have := i.isLt; omega⟩ : Fin (m + n - 1)) =
      Fin.castAdd n (strandSucc i) := Fin.ext (by simp)
  funext k
  induction k using Fin.addCases with
  | left k =>
    simp only [hurwitzMove_apply, h₀, h₁, Fin.append_left, Fin.castAdd_inj]
  | right k =>
    rw [hurwitzMove_apply_of_ne]
    · simp
    · intro h
      have hv := congrArg Fin.val h
      simp only [val_strand, Fin.val_natAdd] at hv
      have := i.isLt
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [val_strandSucc, Fin.val_natAdd] at hv
      have := i.isLt
      omega

/-- Acting on the prefix uses the inclusion on the first block of strands. -/
theorem hurwitzAction_appendHom (t : BranchTuple m G) (s : BranchTuple n G)
    (b : BraidGroup m) :
    hurwitzAction (appendHom m n b) (Fin.append t s) = Fin.append (hurwitzAction b t) s := by
  symm
  apply apply_hurwitzAction_of_apply_hurwitzMove
    (hurwitzAction.comp (appendHom m n)) (F := fun u ↦ Fin.append u s)
  intro i u
  rw [MonoidHom.comp_apply, appendHom_sigma, hurwitzAction_sigma, hurwitzMove_append_left]

/-- Independent braids on the two blocks act on their concatenation through the block sum. -/
theorem hurwitzAction_blockSum (t : BranchTuple m G) (s : BranchTuple n G)
    (b : BraidGroup m) (d : BraidGroup n) :
    hurwitzAction (blockSum m n (b, d)) (Fin.append t s) =
      Fin.append (hurwitzAction b t) (hurwitzAction d s) := by
  rw [blockSum_apply, map_mul, Equiv.Perm.mul_apply, hurwitzAction_shift,
    hurwitzAction_appendHom]

end BranchTuple

namespace HurwitzFiber

open BranchTuple

variable {c : ConjClasses G} {prefixFull full : Bool}

/-- Prepend a tuple in the same conjugacy class to a fibre point. The generation condition is
inherited from the suffix alone. -/
def prepend (t : HurwitzFiber c prefixFull m) (s : HurwitzFiber c full n) :
    HurwitzFiber c full (m + n) where
  tuple := Fin.append t.tuple s.tuple
  mem := Fin.addCases (by simpa using t.mem) (by simpa using s.mem)
  gen h := by simp [s.gen h]

/-- Concatenation on fibres is concatenation of the underlying tuples. -/
@[simp]
theorem prepend_tuple (t : HurwitzFiber c prefixFull m) (s : HurwitzFiber c full n) :
    (prepend t s).tuple = Fin.append t.tuple s.tuple := (rfl)

/-- The suffix action on fibre concatenation is carried by the right block inclusion. -/
theorem prepend_smul (t : HurwitzFiber c prefixFull m) (s : HurwitzFiber c full n)
    (b : BraidGroup n) : prepend t (b • s) = shiftHom m n b • prepend t s := by
  apply tuple_injective
  simp only [prepend_tuple, tuple_smul, hurwitzAction_shift]

/-- Fibre concatenation commutes with simultaneous conjugation of both inputs. -/
theorem prepend_conjAct_smul (x : ConjAct G) (t : HurwitzFiber c prefixFull m)
    (s : HurwitzFiber c full n) : prepend (x • t) (x • s) = x • prepend t s := by
  apply tuple_injective
  simp only [prepend_tuple, tuple_conjAct_smul, conjAct_smul_eq, smul_eq_comp, Fin.comp_append]

/-- Independent actions on the two fibre points act on their concatenation via the block sum. -/
theorem prepend_blockSum_smul (t : HurwitzFiber c prefixFull m) (s : HurwitzFiber c full n)
    (b : BraidGroup m) (d : BraidGroup n) :
    prepend (b • t) (d • s) = blockSum m n (b, d) • prepend t s := by
  apply tuple_injective
  simp only [prepend_tuple, tuple_smul, hurwitzAction_blockSum]

/-- Prepend a constant block of `m` elements of the conjugacy class. -/
def glue (m : ℕ) (g : c.carrier) (s : HurwitzFiber c full n) : HurwitzFiber c full (m + n) :=
  prepend ⟨fun _ ↦ g, fun _ ↦ g.property, Bool.false_ne_true.elim⟩ s

/-- The tuple obtained by constant-block gluing. -/
@[simp]
theorem glue_tuple (g : c.carrier) (s : HurwitzFiber c full n) :
    (glue m g s).tuple = Fin.append (fun _ ↦ (g : G)) s.tuple := (rfl)

/-- Constant-block gluing is equivariant for suffix braids. -/
theorem glue_smul (g : c.carrier) (s : HurwitzFiber c full n) (b : BraidGroup n) :
    glue m g (b • s) = shiftHom m n b • glue m g s := by
  exact prepend_smul _ s b

/-- Constant-block gluing transports conjugation of the suffix by conjugating the prefix back. -/
theorem glue_conjAct_smul (h : G) (g : c.carrier) (s : HurwitzFiber c full n) :
    glue m g (ConjAct.toConjAct h • s) = ConjAct.toConjAct h •
      glue m ⟨h⁻¹ * (g : G) * h, ConjClasses.conj_inv_mem_carrier g.property h⟩ s := by
  apply tuple_injective
  simp only [glue_tuple, tuple_conjAct_smul, conjAct_smul_eq, smul_eq_comp, Fin.comp_append]
  congr 1
  funext i
  simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    ConjAct.ofConjAct_toConjAct]
  group

/-- A constant block multiplies the boundary on the left by the corresponding power. -/
@[simp↓]
theorem product_glue (g : c.carrier) (s : HurwitzFiber c full n) :
    product (glue m g s).tuple = (g : G) ^ m * product s.tuple := by
  simp [glue_tuple, product_def, List.ofFn_const]

end HurwitzFiber

end TauCeti

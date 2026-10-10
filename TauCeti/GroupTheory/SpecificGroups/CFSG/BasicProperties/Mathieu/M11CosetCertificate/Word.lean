/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.CyclicRelators
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic.FinCases

/-! Signed words and exact evaluation for the M11 coset certificate. -/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations

open Sporadic

/-- Signed words in the exact M11 generators. -/
abbrev Word := PresentationWord (Fin m11Presentation.generatorCount)

/-- The index of the first M11 generator. -/
@[expose]
def genA : Fin m11Presentation.generatorCount := ⟨0, by
  simp [GroupPresentation.generatorCount]⟩

/-- The index of the second M11 generator. -/
@[expose]
def genB : Fin m11Presentation.generatorCount := ⟨1, by
  simp [GroupPresentation.generatorCount]⟩

/-- Decode the certificate alphabet `[a,b,A,B]`. -/
@[expose]
def decode (w : List (Fin 4)) : Word :=
  w.map fun i ↦ (if i.val % 2 = 0 then genA else genB, decide (i.val < 2))

/-- Evaluate a signed word in the exact presented group. -/
@[expose]
def eval (w : Word) : m11Presentation.Group :=
  PresentedGroup.mk m11Presentation.relatorSet (FreeGroup.mk w)

private theorem eval_append (u v : Word) : eval (u ++ v) = eval u * eval v := by
  simp only [eval, ← FreeGroup.mul_mk, map_mul]

theorem eval_replicate (w : Word) (n : ℕ) :
    eval ((List.replicate n w).flatten) = eval w ^ n := by
  simp only [eval, ← FreeGroup.pow_mk, map_pow]

/-- Inverse words evaluate to inverse group elements. -/
theorem eval_invRev (w : Word) : eval (FreeGroup.invRev w) = (eval w)⁻¹ := by
  simp only [eval, ← FreeGroup.inv_mk, map_inv]

/-- Every rotation of an exact closed word is closed. -/
theorem eval_rotate_eq_one {w : Word} (hw : eval w = 1) (n : ℕ) :
    eval (w.rotate n) = 1 := by
  rw [eval, ← m11Presentation.prod_toTableWord]
  simpa only [PresentationWord.toTableWord, List.map_rotate] using
    List.prod_rotate_eq_one_of_prod_eq_one
      ((m11Presentation.prod_toTableWord w).trans hw) n

/-- Rotate a signed word, optionally inverting it first. -/
@[expose]
def variant (w : Word) (invert : Bool) (shift : ℕ) : Word :=
  (if invert then FreeGroup.invRev w else w).rotate shift

theorem variant_eq_one {u v : Word} (hu : eval u = 1)
    (invert : Bool) (shift : ℕ) (hv : v = variant u invert shift) :
    eval v = 1 := by
  rw [hv, variant]
  apply eval_rotate_eq_one
  cases invert with
  | false => exact hu
  | true =>
    change eval (FreeGroup.invRev u) = 1
    rw [eval_invRev, hu, inv_one]

theorem product_eq_one {u v : Word} (hu : eval u = 1) (hv : eval v = 1) :
    eval (u ++ v) = 1 := by
  rw [eval_append, hu, hv, mul_one]

theorem reduced_conjugate_eq_one {w core : Word} (q : Word) (hw : eval w = 1)
    (hred : FreeGroup.reduce w =
      FreeGroup.reduce (q ++ core ++ FreeGroup.invRev q)) : eval core = 1 := by
  have heq := congrArg (PresentedGroup.mk m11Presentation.relatorSet)
    (FreeGroup.reduce.exact hred)
  change eval w = eval (q ++ core ++ FreeGroup.invRev q) at heq
  rw [eval_append, eval_append, eval_invRev] at heq
  exact conj_eq_one_iff.mp (heq.symm.trans hw)

/-- The first cyclically reduced relation of the exact M11 presentation. -/
abbrev original0 : Word := decode [1, 2, 2, 2, 1, 2, 1, 1, 1]
/-- The second cyclically reduced relation of the exact M11 presentation. -/
abbrev original1 : Word := decode [1, 0, 3, 2, 3, 2, 1, 0, 3, 0]

theorem original0_eq_one : eval original0 = 1 := by
  apply m11Presentation.cyclicRelators_eq_one
  simp only [GroupPresentation.cyclicRelators, GroupPresentation.relators_def,
    m11Presentation_transcribed, List.map_cons, List.map_nil,
    Relator.toWord_mul, Relator.toWord_pow, Relator.toWord_inv, Relator.toWord_gen]
  decide +kernel

theorem original1_eq_one : eval original1 = 1 := by
  apply m11Presentation.cyclicRelators_eq_one
  simp only [GroupPresentation.cyclicRelators, GroupPresentation.relators_def,
    m11Presentation_transcribed, List.map_cons, List.map_nil,
    Relator.toWord_mul, Relator.toWord_pow, Relator.toWord_inv, Relator.toWord_gen]
  decide +kernel

/-- The first generator of the exact M11 presentation. -/
@[expose]
def a : m11Presentation.Group := PresentedGroup.of genA

/-- The second generator of the exact M11 presentation. -/
@[expose]
def b : m11Presentation.Group := PresentedGroup.of genB

/-- The cyclic subgroup generator. -/
@[expose]
def x : m11Presentation.Group := a * b⁻¹

/-- The subgroup word `[a,B]` evaluates to the cyclic subgroup generator. -/
theorem eval_abinv : eval (decode [0, 3]) = x := by
  have h : decode [0, 3] = [(genA, true)] ++ FreeGroup.invRev [(genB, true)] := by
    decide +kernel
  rw [h, eval_append, eval_invRev]
  rfl

/-- The inverse subgroup word evaluates to the inverse cyclic subgroup generator. -/
theorem eval_bainv : eval (decode [1, 2]) = x⁻¹ := by
  have h : decode [1, 2] = FreeGroup.invRev (decode [0, 3]) := by decide +kernel
  rw [h, eval_invRev, eval_abinv]

/-- Identify the concrete four-letter alphabet with the presentation's doubled alphabet. -/
@[expose]
def toTableLetter : Fin 4 → Fin (m11Presentation.generatorCount + m11Presentation.generatorCount) :=
  Fin.cast (by simp [GroupPresentation.generatorCount])

/-- Every letter of the doubled presentation alphabet has a concrete code. -/
theorem toTableLetter_surjective : Function.Surjective toTableLetter := by
  intro i
  refine ⟨⟨i.val, ?_⟩, ?_⟩
  · simpa [GroupPresentation.generatorCount] using i.isLt
  · apply Fin.ext
    rfl

/-- Decoding then encoding preserves the concrete word up to the alphabet identification. -/
theorem toTableWord_decode (w : List (Fin 4)) :
    (decode w).toTableWord = w.map toTableLetter := by
  simp only [decode, PresentationWord.toTableWord, List.map_map]
  congr 1
  funext i
  apply Fin.ext
  fin_cases i <;> simp [toTableLetter, genA, genB, GroupPresentation.generatorCount]

/-- Interpret the concrete alphabet in the exact presentation group. -/
@[expose]
def letterValue (i : Fin 4) : m11Presentation.Group :=
  m11Presentation.tableGenerators (toTableLetter i)

/-- The concrete letter values generate the exact presentation group. -/
theorem closure_range_letterValue : Subgroup.closure (Set.range letterValue) = ⊤ := by
  have h : Set.range letterValue = Set.range m11Presentation.tableGenerators := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨toTableLetter i, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, rfl⟩ := toTableLetter_surjective i
      exact ⟨j, rfl⟩
  rw [h, m11Presentation.closure_range_tableGenerators]

/-- Concrete table-word evaluation agrees with exact signed-word evaluation. -/
theorem prod_letterValue (w : List (Fin 4)) :
    (w.map letterValue).prod = eval (decode w) := by
  calc
    (w.map letterValue).prod =
        ((decode w).toTableWord.map m11Presentation.tableGenerators).prod := by
      rw [toTableWord_decode, List.map_map]
      rfl
    _ = eval (decode w) := m11Presentation.prod_toTableWord _

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations

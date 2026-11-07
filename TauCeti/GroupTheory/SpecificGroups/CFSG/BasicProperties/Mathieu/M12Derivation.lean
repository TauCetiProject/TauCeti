/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.WordDerivation
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu

/-!
# Exact M12 relations for checked word derivations

The alphabet `[a,b,A,B]` decodes to the original two presentation generators and
their inverses. The three initial relations are proved directly from the transcribed
presentation. `PresentationWord` derivation rules then apply through its quotient
homomorphism. No additional relation from the permutation image is assumed.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M12Derivation

/-- Signed words in the original two generators of the M12 presentation. -/
abbrev Word := PresentationWord (Fin m12Presentation.generatorCount)

/-- Decode `[a,b,A,B]`, with capital letters denoting inverses. -/
@[expose]
def decode (w : List (Fin 4)) : Word :=
  w.map fun i ↦
    (⟨i.val % 2, by simpa [GroupPresentation.generatorCount] using Nat.mod_lt i.val (by decide)⟩,
      decide (i.val < 2))

/-- Evaluate in the exact presented group, through its canonical quotient map. -/
@[expose]
def eval (w : Word) : m12Presentation.Group :=
  PresentationWord.eval (PresentedGroup.mk m12Presentation.relatorSet) w

/-- The original relator `(B a)³`. -/
@[expose]
def original0 : Word := decode [3, 0, 3, 0, 3, 0]

/-- The original relator `a⁵ b⁶`; neither factor is separately assumed to be one. -/
@[expose]
def original1 : Word := decode [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1]

/-- The original relator `a b² a B a² b a² b²`. -/
@[expose]
def original2 : Word := decode [0, 1, 1, 0, 3, 0, 0, 1, 0, 0, 1, 1]

private theorem eval_eq_one_of_mem {w : Word} (hw : w ∈ m12Presentation.relators) :
    eval w = 1 := by
  apply PresentedGroup.one_of_mem
  obtain ⟨r, hr, rfl⟩ := (m12Presentation.mem_relators_iff w).mp hw
  exact (m12Presentation.mem_relatorSet_iff _).mpr
    ⟨r, hr, r.toWord_toFreeGroup.symm⟩

/-- The first initial word is a relation in the exact presented group. -/
theorem original0_eq_one : eval original0 = 1 := by
  apply eval_eq_one_of_mem
  simp only [GroupPresentation.relators_def, m12Presentation_transcribed,
    List.map_cons, List.map_nil, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_inv, Relator.toWord_gen]
  decide +kernel

/-- The second initial word is a relation in the exact presented group. -/
theorem original1_eq_one : eval original1 = 1 := by
  apply eval_eq_one_of_mem
  simp only [GroupPresentation.relators_def, m12Presentation_transcribed,
    List.map_cons, List.map_nil, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_inv, Relator.toWord_gen]
  decide +kernel

/-- The third initial word is a relation in the exact presented group. -/
theorem original2_eq_one : eval original2 = 1 := by
  apply eval_eq_one_of_mem
  simp only [GroupPresentation.relators_def, m12Presentation_transcribed,
    List.map_cons, List.map_nil, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_inv, Relator.toWord_gen]
  decide +kernel

end TauCeti.Sporadic.Mathieu.M12Derivation

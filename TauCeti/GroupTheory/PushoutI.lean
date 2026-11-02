/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PushoutI

/-!
# Reduced words in amalgamated products

A word in the free product of the factors of an amalgamated product `Monoid.PushoutI φ` is
*reduced* (`Monoid.PushoutI.Reduced`) when none of its letters lies in the image of the
amalgamated group. Mathlib's normal form theorem shows that a nonempty reduced word does not
evaluate into the amalgamated group (`Monoid.PushoutI.Reduced.eq_empty_of_mem_range`). This file
records the existence half: when every map `φ i` is injective, every element of the amalgamated
product is an element of the amalgamated group followed by the product of a reduced word.
-/

public section

namespace Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- Every element of an amalgamated product of groups along injective maps is `base φ h` times
the product of a reduced word. -/
theorem exists_reduced_eq_base_mul_ofCoprodI_prod (hφ : ∀ i, Function.Injective (φ i))
    (x : PushoutI φ) :
    ∃ (h : H) (w : CoprodI.Word G), Reduced φ w ∧ x = base φ h * ofCoprodI w.prod := by
  classical
  obtain ⟨d⟩ := NormalWord.transversal_nonempty φ hφ
  set w := NormalWord.equiv (d := d) x
  refine ⟨w.head, w.toWord, fun ⟨i, g⟩ hg hr => ?_,
    ((NormalWord.equiv (d := d)).symm_apply_apply x).symm⟩
  -- A letter of a normal word lies in the transversal, which meets the image of `φ i` only in `1`.
  have hc := d.compl i
  exact w.ne_one _ hg <| congrArg Subtype.val <|
    (hc.equiv_snd_eq_self_of_mem_of_one_mem (MonoidHom.range _).one_mem
      (w.normalized i g hg)).symm.trans (hc.equiv_snd_eq_one_of_mem_of_one_mem (d.one_mem i) hr)

end Monoid.PushoutI

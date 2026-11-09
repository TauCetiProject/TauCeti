/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Tits.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.HalfFrobenius

/-!
# Character pullback at the Tits index

The represented Tits Steinberg map is the exceptional F₄ endomorphism itself. On the represented
weight torus its character pullback is the native datum Steinberg map at the Tits index. The
index's exponent is one, so this uses the special-isogeny character computation directly, not a
Ree index with an invalid parameter. The torus coordinates are the fundamental-weight coordinates
of the index's own rank-four lattice.

This is a comparison of the represented point endomorphism with its root-datum shadow, not a
comparison of ambient group schemes or a simplicity theorem. The exceptional-map convention is
that of Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 28; the separate Tits
candidate convention follows Carter, *Simple Groups of Lie Type*, §14.
-/

public section

namespace TauCeti.TitsLieIndex

noncomputable section

variable (d : TitsLieIndex)

/-- The represented weight torus in the Tits index's fundamental-weight coordinates. -/
def weightTorus : (Fin d.1.rank → d.1.Closureˣ) →* d.AmbientGroup :=
  (F4ShortRoot.PrimeField.weightTorusPoints d.1.Closure).comp
    (MonoidHom.pi fun i => Pi.evalMonoidHom _ (finCongr d.rank_eq_four.symm i))

/-- Evaluation uses the rank identification and no permutation of the torus coordinates. -/
theorem weightTorus_apply (s : Fin d.1.rank → d.1.Closureˣ) :
    d.weightTorus s = F4ShortRoot.PrimeField.weightTorusPoints d.1.Closure
      (fun i => s (finCongr d.rank_eq_four.symm i)) :=
  (rfl)

/-- The represented Tits Steinberg map has the weight map of the native datum Steinberg map
as character pullback; its exponent-one specialization retains the exceptional map. -/
theorem isCharacterMap_steinberg :
    IsCharacterMap d.weightTorus d.steinberg d.toSuzukiReeIndex.datumSteinberg.weightMap := by
  have h := F4ShortRoot.PrimeField.isCharacterMap_specialIsogeny d.1.Closure
  -- The lattice depends on the rank; use the index eliminator before identifying coordinates.
  obtain rfl := d.eq_of
  rw [weightTorus, steinberg_def]
  simp only [toSuzukiReeIndex, SuzukiReeIndex.datumSteinberg_tits,
    SuzukiReeIndex.datumSpecialIsogeny_weightMap_tits]
  exact h

end

end TauCeti.TitsLieIndex

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.McKay.Basic
public import TauCeti.RepresentationTheory.SU2.Standard

/-!
# The McKay correspondence for finite subgroups of `SU(2)`

Specializing `TauCeti.exists_isMcKayLabelling` to `TauCeti.SU2.stdFDRep H` gives the McKay
correspondence for every nontrivial finite subgroup `H` of `SU(2)`
(`TauCeti.SU2.exists_isMcKayLabelling`).
-/

public section

namespace TauCeti.SU2

/-- **The McKay correspondence for finite nontrivial subgroups of `SU(2)`.** -/
theorem exists_isMcKayLabelling (H : Subgroup SU2) [Finite H] [Nontrivial H] :
    ∃ (t : AffineDynkinType) (e : SimpleFDRepClasses ℂ H ≃ Fin t.nodes),
      t.Valid ∧ IsMcKayLabelling (stdFDRep H) t e :=
  TauCeti.exists_isMcKayLabelling (stdFDRep H) (finrank_stdFDRep H) (ρ_stdFDRep_injective H)
    (det_ρ_stdFDRep H)

end TauCeti.SU2

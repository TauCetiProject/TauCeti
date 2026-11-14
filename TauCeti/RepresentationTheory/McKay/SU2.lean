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

Specializing `TauCeti.exists_isMcKayLabelling` (`TauCeti.RepresentationTheory.McKay.Basic`) to the
tautological two-dimensional complex representation `TauCeti.SU2.stdFDRep H`
(`TauCeti.RepresentationTheory.SU2.Standard`) gives the McKay correspondence for every nontrivial
finite subgroup `H` of `SU(2)`.

## Main results

* `TauCeti.SU2.exists_isMcKayLabelling`: every nontrivial finite subgroup `H : Subgroup SU2` admits
  a McKay labelling by a valid affine simply-laced Dynkin diagram relative to `SU2.stdFDRep H`.

## References

* J. McKay, *Graphs, singularities, and finite groups*, Proc. Symp. Pure Math. **37** (1980),
  183–186.
* R. Steinberg, *Finite subgroups of `SU₂`, Dynkin diagrams and affine Coxeter elements*, Pacific J.
  Math. **118** (1985), 587–598.
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

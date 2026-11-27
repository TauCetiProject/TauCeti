/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Basic

import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Affine
import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Zariski
import TauCeti.AlgebraicGeometry.Sites.StackQuasiCompact

/-!
# Fpqc descent of quasi-coherent modules

The pseudofunctor of quasi-coherent modules is a stack for the fpqc topology. Thus its canonical
functor to descent data along any fpqc covering family is an equivalence of categories, by
`CategoryTheory.Pseudofunctor.isEquivalence_toDescentData`.

The proof uses `TauCeti.AlgebraicGeometry.isStack_propQCTopology_iff` to reduce to Zariski
descent and faithfully flat descent between affine schemes, both established in the preceding
modules.

## Main declarations

* `TauCeti.AlgebraicGeometry.Descent.qcohPseudofunctor_isStack_fpqcTopology`: the stack property
  for quasi-coherent modules in the fpqc topology.

## References

* The Stacks Project, Proposition 35.5.2 (023T), descent of quasi-coherent modules along fpqc
  coverings.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Descent

universe u

/-- Quasi-coherent modules satisfy effective descent for the fpqc topology. -/
instance qcohPseudofunctor_isStack_fpqcTopology :
    qcohPseudofunctor.{u}.IsStack Scheme.fpqcTopology := by
  have : IsZariskiLocalAtSource @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)
  rw [Scheme.fpqcTopology_eq_propQCTopology,
    TauCeti.AlgebraicGeometry.isStack_propQCTopology_iff (P := @Flat)]
  refine ⟨ZariskiGlue.isStack_zariskiTopology, fun f hf hs ↦ ?_⟩
  have := hf
  have := hs
  rw [← Presieve.ofArrows_pUnit.{0}, Pseudofunctor.isStackFor_ofArrows_iff]
  exact isEquivalence_toDescentData_specMap f

end TauCeti.AlgebraicGeometry.Descent

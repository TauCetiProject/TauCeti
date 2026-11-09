/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Basic
public import TauCeti.FieldTheory.GaloisCohomology.Congr

/-!
# Transporting the cohomological Brauer group along a field isomorphism

A field isomorphism induces an additive equivalence between the cohomological Brauer groups.
The construction uses the existing identification of separable closures and their absolute
Galois groups, followed by change of groups and coefficients in continuous cohomology. In
particular, it allows the Brauer groups of archimedean completions to be compared with those
of the real and complex fields without changing the cohomology carrier.

This API supplies an additive identification using a chosen lift to separable closures. It does
not supply functoriality lemmas comparing the lifts chosen for different field isomorphisms.
For a supplied identification `a := brCongr e`, use `a.symm` for its inverse and `a.trans b`
for successive identifications. Their cancellation and application laws are
`AddEquiv.symm_apply_apply`, `AddEquiv.apply_symm_apply`, and `AddEquiv.trans_apply`.
The archimedean invariant is independent of this identification, as recorded by
`TauCeti.ClassFieldTheory.infiniteInvMap_eq_realInv_comp` in the archimedean module.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

/-- An isomorphism of fields supplies an additive equivalence of their cohomological Brauer
groups, using a chosen identification of separable closures. -/
def brCongr {K L : Type*} [Field K] [Field L] (e : K ≃+* L) : Br K ≃+ Br L :=
  (unitsRepH2Equiv K).symm.trans (e.unitsH2Congr.trans (unitsRepH2Equiv L))

/-- The cohomological Brauer-group identification is the field transport on explicit unit-valued
second Galois cohomology, read through the canonical cohomology comparison. -/
theorem brCongr_unitsRepH2Equiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (x : ContCohomology.H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    brCongr e (unitsRepH2Equiv K x) = unitsRepH2Equiv L (e.unitsH2Congr x) := by
  simp [brCongr]

end TauCeti.ClassFieldTheory

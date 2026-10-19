/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Congr

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
def brCongr {K L : Type*} [Field K] [Field L] (e : K ≃+* L) : Br K ≃+ Br L := by
  let φ : AbsoluteGaloisGroup L ≃ₜ* AbsoluteGaloisGroup K := e.absoluteGaloisGroupCongr
  let c : UnitsCoeff L ≃+ UnitsCoeff K :=
    (Units.mapEquiv e.separableClosureCongr.toMulEquiv).toAdditive
  have hc (g : AbsoluteGaloisGroup L) (x : UnitsCoeff K) :
      c.symm (φ g • x) = g • c.symm x := by
    apply c.injective
    rw [c.apply_symm_apply]
    apply Additive.toMul.injective
    apply Units.ext
    -- The coefficient actions are evaluation by field automorphisms; taking values exposes
    -- the conjugation formula supplied by the absolute-Galois-group equivalence.
    change (φ g) (x.toMul : SeparableClosure K) =
      e.separableClosureCongr (g (e.separableClosureCongr.symm (x.toMul : SeparableClosure K)))
    exact e.absoluteGaloisGroupCongr_apply g _
  exact (unitsRepH2Equiv K).symm.trans
    ((ContCohomology.explicitMap2Equiv (AbsoluteGaloisGroup K) (UnitsCoeff K)
      (AbsoluteGaloisGroup L) (UnitsCoeff L) φ c.symm
      continuous_of_discreteTopology continuous_of_discreteTopology hc).trans
        (unitsRepH2Equiv L))

end TauCeti.ClassFieldTheory

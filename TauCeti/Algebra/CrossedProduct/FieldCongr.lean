/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Inflation
public import TauCeti.FieldTheory.GaloisCohomology.Congr

/-!
# Finite cocycle inflation and field isomorphisms

Finite cocycles on normal subextensions of the chosen separable closures can be transported
along compatible coefficient and automorphism maps. Inflation commutes with a field
isomorphism when those coefficient maps agree with its chosen separable-closure identification.
The cocycle over the target field is constructed with `TwoCocycle.comap`; no compatibility
of its inflated class is assumed.

The resulting cocycle and cohomology identities give the finite-generator equations for
comparing Brauer/cohomology identifications across isomorphic presentations of a field.

## References

* J.-P. Serre, *Local Fields*, Chapter X, §5.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, §4.4.
-/

public noncomputable section

namespace TauCeti.TwoCocycle

open ContCohomology

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] (e : K ≃+* L)
  (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [Normal K E]
  (F : IntermediateField L (SeparableClosure L)) [FiniteDimensional L F] [Normal L F]
  (ι : E →+* F) (π : (F ≃ₐ[L] F) →* (E ≃ₐ[K] E))
  (hι : ∀ x : E, e.separableClosureCongr.symm (E.val x) = F.val (ι x))
  (hπ : ∀ g x, ι (π g x) = g (ι x))

include hι hπ

/-- Transporting an inflated finite cocycle is the inflation of its transport between the
identified finite normal subextensions. -/
theorem unitsCocyclesCongr_inflateZ2 (c : TwoCocycle K E) :
    e.unitsCocyclesCongr (c.inflateZ2 E) = (c.comap π ι hπ).inflateZ2 F := by
  apply Subtype.ext
  funext p
  rcases p with ⟨g, h⟩
  rw [e.unitsCocyclesCongr_apply]
  apply Additive.toMul.injective
  apply Units.ext
  simp only [RingEquiv.unitsCoeffCongr_apply, coe_inflateZ2, inflate_toFun,
    toMul_ofMul, Units.coe_map, comap_toFun]
  rw [← e.restrictNormalHom_congr E F ι π hι hπ g,
    ← e.restrictNormalHom_congr E F ι π hι hπ h]
  exact hι _

/-- Field transport on explicit second Galois cohomology commutes with inflation of finite
cocycles along compatible maps of the finite subextensions. -/
theorem unitsH2Congr_inflateH2 (c : TwoCocycle K E) :
    e.unitsH2Congr (c.inflateH2 E) = (c.comap π ι hπ).inflateH2 F := by
  rw [inflateH2_def, inflateH2_def]
  exact (e.unitsH2Congr_mk (c.inflateZ2 E)).trans
    (congrArg (H2pi (AbsoluteGaloisGroup L) (UnitsCoeff L))
      (unitsCocyclesCongr_inflateZ2 e E F ι π hι hπ c))

end TauCeti.TwoCocycle

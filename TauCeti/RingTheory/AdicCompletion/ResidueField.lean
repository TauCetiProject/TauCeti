/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Residue field of the completion of a local ring

Let `R` be a Noetherian local ring with maximal ideal `𝔪` and `𝔪`-adic completion `R̂`. The
canonical map `R → R̂` induces an isomorphism on residue fields
(`AdicCompletion.residueField_map_bijective`).
This file packages it as the `R`-algebra equivalence `TauCeti.AdicCompletion.residueFieldEquiv`.

## Main results

* `TauCeti.AdicCompletion.residueFieldEquiv`: the `R`-algebra equivalence
  `ResidueField R ≃ₐ[R] ResidueField R̂` induced by `R → R̂`.
* `TauCeti.AdicCompletion.residueFieldEquiv_apply`: `residueFieldEquiv` agrees with
  `IsLocalRing.ResidueField.map` of `algebraMap R R̂`.
-/

public section

open IsLocalRing

namespace TauCeti.AdicCompletion

section

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The `R`-algebra equivalence `ResidueField R ≃ₐ[R] ResidueField R̂` induced by `R → R̂`. -/
noncomputable def residueFieldEquiv (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ResidueField R ≃ₐ[R] ResidueField (AdicCompletion (maximalIdeal R) R) :=
  have : IsLocalHom (Algebra.ofId R (AdicCompletion (maximalIdeal R) R)) :=
    ⟨IsLocalHom.map_nonunit (f := algebraMap R (AdicCompletion (maximalIdeal R) R))⟩
  AlgEquiv.ofBijective
    (ResidueField.mapAlgHom (Algebra.ofId R (AdicCompletion (maximalIdeal R) R)))
    (_root_.AdicCompletion.residueField_map_bijective R)

/-- `residueFieldEquiv` agrees with `ResidueField.map` of the canonical map `R → R̂`. -/
@[simp]
theorem residueFieldEquiv_apply (x : ResidueField R) :
    residueFieldEquiv R x =
      ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) x :=
  AlgEquiv.ofBijective_apply _ _ x

end

end TauCeti.AdicCompletion

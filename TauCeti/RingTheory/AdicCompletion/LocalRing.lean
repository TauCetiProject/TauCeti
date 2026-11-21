/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import TauCeti.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.RegularLocalRing.Flat

/-!
# Dimension and regularity of the completion of a local ring

Let `R` be a Noetherian local ring with maximal ideal `𝔪` and let `R̂` be its `𝔪`-adic completion.
Then `R̂` is a Noetherian local ring, flat over `R`, with maximal ideal `𝔪 R̂` and the same residue
field. This file shows that `R̂` has the same Krull dimension as `R`, and that `R̂` is regular if
and only if `R` is. Together with Mathlib's `AdicCompletion.spanFinrank_maximalIdeal_eq`, these
are among the invariants of a local ring that are unchanged by completion.

Descent of regularity from `R̂` to `R` lets regularity be tested on complete local rings, where the
Cohen structure theorem presents them as quotients of power series rings over a field or, in mixed
characteristic, over a complete discrete valuation ring.

## Main results

* `TauCeti.AdicCompletion.residueFieldAlgEquiv`: the canonical `R`-algebra isomorphism
  `ResidueField R ≃ₐ[R] ResidueField R̂`.
* `TauCeti.AdicCompletion.ringKrullDim_eq`: `R̂` and `R` have the same Krull dimension.
* `TauCeti.AdicCompletion.isRegularLocalRing_iff`: `R̂` is regular if and only if `R` is.

## References

* [Stacks Project, Lemma 15.44.1](https://stacks.math.columbia.edu/tag/07NV), the dimension of
  the completion.
* [Stacks Project, Lemma 15.44.4](https://stacks.math.columbia.edu/tag/07NY), regularity of the
  completion.
-/

public section

open IsLocalRing

namespace TauCeti.AdicCompletion

section

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

variable (R) in
/-- The canonical `R`-algebra isomorphism between the residue field of a Noetherian local ring and
the residue field of its maximal-ideal completion, induced by `algebraMap`. -/
noncomputable def residueFieldAlgEquiv :
    ResidueField R ≃ₐ[R] ResidueField (_root_.AdicCompletion (maximalIdeal R) R) :=
  { RingEquiv.ofBijective
      (ResidueField.map (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R)))
      (_root_.AdicCompletion.residueField_map_bijective R) with
    commutes' r := by
      simp [IsScalarTower.algebraMap_apply R (_root_.AdicCompletion (maximalIdeal R) R)
        (ResidueField (_root_.AdicCompletion (maximalIdeal R) R)),
        ResidueField.algebraMap_eq] }

theorem residueFieldAlgEquiv_apply (x : ResidueField R) :
    residueFieldAlgEquiv R x =
      ResidueField.map (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R)) x :=
  (rfl)

@[simp]
theorem residueFieldAlgEquiv_residue (r : R) :
    residueFieldAlgEquiv R (residue R r) =
      residue (_root_.AdicCompletion (maximalIdeal R) R) (algebraMap R _ r) :=
  (rfl)

@[simp]
theorem residueFieldAlgEquiv_symm_residue (r : R) :
    (residueFieldAlgEquiv R).symm
      (residue (_root_.AdicCompletion (maximalIdeal R) R) (algebraMap R _ r)) =
      residue R r :=
  (residueFieldAlgEquiv R).symm_apply_eq.mpr (residueFieldAlgEquiv_residue r).symm

/-- The completion of a Noetherian local ring at its maximal ideal has the same Krull dimension as
the ring. -/
@[stacks 07NV]
theorem ringKrullDim_eq :
    ringKrullDim (_root_.AdicCompletion (maximalIdeal R) R) = ringKrullDim R :=
  ringKrullDim_eq_of_hasGoingDown_of_map_maximalIdeal_eq
    _root_.AdicCompletion.maximalIdeal_eq_map.symm

/-- The completion of a Noetherian local ring at its maximal ideal is regular if and only if the
ring is. -/
@[stacks 07NY]
theorem isRegularLocalRing_iff :
    IsRegularLocalRing (_root_.AdicCompletion (maximalIdeal R) R) ↔ IsRegularLocalRing R :=
  isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq
    _root_.AdicCompletion.maximalIdeal_eq_map.symm

end

/-- The completion of a regular local ring at its maximal ideal is regular. -/
instance {R : Type*} [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (_root_.AdicCompletion (maximalIdeal R) R) :=
  isRegularLocalRing_iff.mpr ‹_›

end TauCeti.AdicCompletion

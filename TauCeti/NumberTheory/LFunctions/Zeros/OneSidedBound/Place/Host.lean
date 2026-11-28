/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.HostField
public import TauCeti.NumberTheory.NumberField.Cyclotomic.InfinitePlace.Basic

/-!
# Cyclotomic labels of the places of the prime-sum host

The fixed complex inclusion of the host labels its infinite places by the units modulo
the tower level. A label also determines the representative embedding that extends the
fixed inclusion of the imaginary quadratic base. Thus a subset of the labels can specify
infinite places and their embeddings without an extra choice of basepoint.

The normalization follows `New.Parameters.placeMulEquiv` in
`New/Reduction/Data/FieldsAndPlaces.lean` of [lsernau/grh-lean](https://github.com/lsernau/grh-lean)
at `72fead1`. We use
`NumberField.InfinitePlace.equivUnitsZMod` to label the places relative to the inclusion.
-/

public noncomputable section

open IsCyclotomicExtension NumberField

namespace TauCeti.OneSidedBound.Parameters

variable (P : Parameters) (s : ℕ)

/-- The infinite places of the host, labeled relative to the fixed inclusion into `ℂ`. -/
def hostPlaceEquiv : InfinitePlace (P.hostField s) ≃ (ZMod (P.q₁ s))ˣ :=
  (InfinitePlace.mk (P.hostField s).val.toRingHom).equivUnitsZMod
    (InfinitePlace.isUnramified_iff.mpr (.inr (IsTotallyComplex.isComplex _)))
    (P.irreducible_cyclotomic_baseField s)

/-- The complex embedding for a cyclotomic place label, extending the inclusion of the
quadratic base. -/
def hostEmbedding (u : (ZMod (P.q₁ s))ˣ) : P.hostField s →ₐ[P.baseField] ℂ :=
  (P.hostField s).val.comp
    ((autEquivPow (P.hostField s) (P.irreducible_cyclotomic_baseField s)).symm u).toAlgHom

/-- The embedding for a label induces precisely the infinite place assigned to that label. -/
@[simp] theorem mk_hostEmbedding (u : (ZMod (P.q₁ s))ˣ) :
    InfinitePlace.mk (P.hostEmbedding s u) = (P.hostPlaceEquiv s).symm u := by
  rw [hostPlaceEquiv, InfinitePlace.equivUnitsZMod_symm_apply_mk, hostEmbedding]
  rfl

/-- The reference inclusion is the embedding for the unit label `1`. -/
@[simp] theorem hostEmbedding_one : P.hostEmbedding s 1 = (P.hostField s).val := by
  apply AlgHom.ext
  intro x
  simp [hostEmbedding]

/-- The embedding for a label raises the image of the cyclotomic generator to that power. -/
@[simp] theorem hostEmbedding_hostRoot (u : (ZMod (P.q₁ s))ˣ) :
    P.hostEmbedding s u (P.hostRoot s) = (P.hostRoot s : ℂ) ^ (u : ZMod (P.q₁ s)).val := by
  simp only [hostEmbedding, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    autEquivPow_apply_of_pow_eq_one _ (P.irreducible_cyclotomic_baseField s) _
      (P.isPrimitiveRoot_hostRoot s).pow_eq_one, MulEquiv.apply_symm_apply, map_pow]
  rfl

end TauCeti.OneSidedBound.Parameters

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Equiv

/-!
# Ramification under field isomorphisms

The ramification index depends on the extension, not on its presentation as a field carrier:
transporting a place of the upstairs field along an isomorphism over the downstairs field does not
change the place below it, its ramification index, or the separability of its residue extension.
This allows an extension to be placed in a finite Galois overfield without changing its
ramification behaviour.
-/

public section

namespace TauCeti.Place

variable {k F L L' : Type*} [Field k] [Field F] [Field L] [Field L']
variable [Algebra k F] [Algebra k L] [Algebra k L'] [Algebra F L] [Algebra F L']
variable [IsScalarTower k F L] [IsScalarTower k F L']

/-- An isomorphism `e : L ≃ₐ[F] L'` over the base field fixes the constants `k` of the tower
`k → F → L`. This is the compatibility hypothesis needed to transport places of `L` to places of
`L'` along `e` with `TauCeti.Place.equivOfRingEquiv`. -/
theorem _root_.AlgEquiv.toRingEquiv_algebraMap_of_isScalarTower (e : L ≃ₐ[F] L') (c : k) :
    e.toRingEquiv (algebraMap k L c) = algebraMap k L' (RingEquiv.refl k c) :=
  (e.restrictScalars k).commutes c

/-- **The ramification index is invariant under an isomorphism of the upstairs field** over the
base field: transporting a place of `L` along `e : L ≃ₐ[F] L'` does not change its ramification
index over `F`. -/
@[simp]
theorem ramificationIdx_equivOfRingEquiv (e : L ≃ₐ[F] L') (Q : Place k L) :
    ramificationIdx F (equivOfRingEquiv (RingEquiv.refl k) e.toRingEquiv
      e.toRingEquiv_algebraMap_of_isScalarTower Q) = ramificationIdx F Q := by
  rw [ramificationIdx_def, ramificationIdx_def]
  congr 1
  ext c
  rw [Valuation.comap_apply, Valuation.comap_apply, valuation_equivOfRingEquiv]
  exact congrArg Q.valuation (e.symm.commutes c)

variable [Algebra.IsIntegral F L] [Algebra.IsIntegral F L']

/-- Transporting a place of `L` along `e : L ≃ₐ[F] L'` does not change the place of `F` below
it. -/
@[simp]
theorem restrict_equivOfRingEquiv (e : L ≃ₐ[F] L') (Q : Place k L) :
    (equivOfRingEquiv (RingEquiv.refl k) e.toRingEquiv e.toRingEquiv_algebraMap_of_isScalarTower
      Q).restrict k F = Q.restrict k F := by
  apply integers_injective
  ext x
  rw [mem_integers_restrict_iff, mem_integers_restrict_iff, mem_integers_iff,
    mem_integers_iff, valuation_equivOfRingEquiv]
  simp

/-- **Separability of the residue extension is invariant under an isomorphism of the upstairs
field** over the base field: transporting a place of `L` along `e : L ≃ₐ[F] L'` does not change
whether its residue extension over the place below it in `F` is separable. -/
theorem isSeparable_residueField_equivOfRingEquiv_iff (e : L ≃ₐ[F] L') (Q : Place k L) :
    Algebra.IsSeparable
        ((equivOfRingEquiv (RingEquiv.refl k) e.toRingEquiv
          e.toRingEquiv_algebraMap_of_isScalarTower Q).restrict k F).ResidueField
        (equivOfRingEquiv (RingEquiv.refl k) e.toRingEquiv
          e.toRingEquiv_algebraMap_of_isScalarTower Q).ResidueField ↔
      Algebra.IsSeparable (Q.restrict k F).ResidueField Q.ResidueField := by
  set h := AlgEquiv.toRingEquiv_algebraMap_of_isScalarTower (k := k) e
  set Q' := equivOfRingEquiv (RingEquiv.refl k) e.toRingEquiv h Q
  have hres : Q.restrict k F = Q'.restrict k F := (restrict_equivOfRingEquiv e Q).symm
  -- Identify the residue fields below by the equality of places, and those above by `e`.
  have cast_residue (P₁ P₂ : Place k F) (hP : P₁ = P₂) (x : P₁.integers) (y : P₂.integers)
      (hxy : (x : F) = y) :
      RingEquiv.cast (R := fun P : Place k F ↦ P.ResidueField) hP
          (IsLocalRing.residue P₁.integers x) = IsLocalRing.residue P₂.integers y := by
    subst hP
    rw [Subtype.ext hxy]
    rfl
  refine (Algebra.IsSeparable.iff_of_equiv_equiv
    (RingEquiv.cast (R := fun P : Place k F ↦ P.ResidueField) hres)
    (IsLocalRing.ResidueField.mapEquiv (integersEquivOfRingEquiv _ _ h Q)) ?_).symm
  ext x
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    cast_residue _ _ hres x ⟨x, hres ▸ x.2⟩ rfl, IsLocalRing.ResidueField.algebraMap_residue,
    IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  refine congrArg (IsLocalRing.residue Q'.integers) (Subtype.ext ?_)
  simp [Q']

end TauCeti.Place

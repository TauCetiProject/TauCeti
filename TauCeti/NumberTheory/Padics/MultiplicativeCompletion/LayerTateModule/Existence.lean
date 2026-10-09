/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.LayerTateModule.Basic
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Cohomology
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction

/-!
# Existence of the Tate module of a finite layer

Let `L/K` be a finite Galois extension of `p`-adic fields. The Tate module of the layer
(`TauCeti.LayerTateModule`) exists: it is the splitting module of the class `u` of the class
module, carried to `A(L)` along local reciprocity. Tate's hypotheses for `u` on the
`p`-subgroups of `Gal(L/K)` are NSW (3.6.4) at `G_K`, whose input is `scd_p G_K = 2`
(`TauCeti.isZero_groupCohomology_one_res_padicCompletionUnits`,
`TauCeti.natCard_groupCohomology_two_res_padicCompletionUnits`); the restriction of `u` generates
on each `p`-subgroup because `u` has the full `p`-part of `#Gal(L/K)` as its order
(`groupCohomology.zmultiples_map_subtype_eq_top`).

## Main statements

* `TauCeti.nonempty_layerTateModule`: the Tate module of a finite Galois layer of `p`-adic fields
  exists.

## Implementation notes

Local reciprocity and Mathlib's representations are stated for fields in `Type`. For fields in
an arbitrary universe the layer is first moved to its copy `Shrink L / Shrink K` in `Type`, and
the Tate module of the copy is carried back along the induced isomorphisms of Galois groups and
of `A(L)` (`TauCeti.padicCompletionUnitsCongr`, `TauCeti.LayerTateModule.nonempty_of_equiv`).

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.6.4), (5.6.5)
  and the proof of (7.4.1).
-/

public section

namespace TauCeti

open CategoryTheory Limits

variable (p : ℕ) [Fact p.Prime]

universe u

/-- **Existence of the Tate module, for fields in `Type`.** -/
private theorem nonempty_layerTateModule_of_type (L K : Type) [Field L] [Field K] [Algebra K L]
    [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K] [Module.Finite ℚ_[p] K]
    [IsScalarTower ℚ_[p] K L] [IsGalois K L] [FiniteDimensional K L] :
    Nonempty (LayerTateModule p L K) := by
  -- The local-field structures of `K` and `L`.
  let _ := finiteExtensionValuativeRel ℚ_[p] K
  let _ := finiteExtensionNormedFieldTopology ℚ_[p] K
  have := finiteExtension_isNonarchimedeanLocalField ℚ_[p] K
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  let _ := finiteExtensionValuativeRel ℚ_[p] L
  let _ := finiteExtensionNormedFieldTopology ℚ_[p] L
  have := finiteExtension_isNonarchimedeanLocalField ℚ_[p] L
  have := finiteExtension_valuativeExtension ℚ_[p] L
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  let A := Rep.of (padicCompletionUnitsRepresentation p L K)
  obtain ⟨u, hu, hcard⟩ := exists_zmultiples_eq_top_groupCohomology_two_padicCompletionUnits p K L
  have : Finite (groupCohomology A 2) :=
    Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hord : addOrderOf u = p ^ padicValNat p (Nat.card (L ≃ₐ[K] L)) := by
    rw [← hcard, ← Nat.card_zmultiples, hu, AddSubgroup.card_top]
  refine LayerTateModule.nonempty_of_tateHypotheses u
    (fun S _ ↦ isZero_groupCohomology_one_res_padicCompletionUnits p K L S) (fun S hS x ↦ ?_)
    (natCard_groupCohomology_two_res_padicCompletionUnits p K L)
  have hgen := groupCohomology.zmultiples_map_subtype_eq_top hord.symm.dvd hS
    (natCard_groupCohomology_two_res_padicCompletionUnits p K L S hS)
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 (hgen ▸ AddSubgroup.mem_top x)
  exact ⟨m, by rw [Int.cast_smul_eq_zsmul, hm]⟩

/-- **Existence of the Tate module of a finite layer** (NSW (5.6.5) and the proof of (7.4.1)). For
a finite Galois extension `L/K` of `p`-adic fields there is a finitely generated
`ℤ_p[Gal(L/K)]`-module of projective dimension at most one which is an extension of the
augmentation ideal by `A(L)`. -/
theorem nonempty_layerTateModule (L K : Type u) [Field L] [Field K] [Algebra K L]
    [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K] [Module.Finite ℚ_[p] K]
    [IsScalarTower ℚ_[p] K L] [IsGalois K L] [FiniteDimensional K L] :
    Nonempty (LayerTateModule p L K) := by
  -- The copy `L' / K'` of the layer in `Type`.
  have : Small.{0} L := Module.Finite.small.{0} ℚ_[p] L
  have : Small.{0} K := Module.Finite.small.{0} ℚ_[p] K
  let eL : Shrink.{0} L ≃+* L := (Shrink.algEquiv ℚ_[p] L).toRingEquiv
  let eK : Shrink.{0} K ≃+* K := (Shrink.algEquiv ℚ_[p] K).toRingEquiv
  let _ : Algebra (Shrink.{0} K) (Shrink.{0} L) :=
    ((eL.symm : L →+* Shrink.{0} L).comp ((algebraMap K L).comp eK)).toAlgebra
  have halg (k : Shrink.{0} K) :
      algebraMap (Shrink.{0} K) (Shrink.{0} L) k = eL.symm (algebraMap K L (eK k)) :=
    rfl
  have hst : IsScalarTower ℚ_[p] (Shrink.{0} K) (Shrink.{0} L) := .of_algebraMap_eq fun a ↦ by
    rw [halg]
    -- `eK` is the ring equivalence underlying `Shrink.algEquiv ℚ_[p] K`.
    change _ = eL.symm (algebraMap K L ((Shrink.algEquiv ℚ_[p] K) (algebraMap ℚ_[p] _ a)))
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply, RingEquiv.eq_symm_apply]
    exact ((Shrink.algEquiv ℚ_[p] L).commutes a)
  have hL : Module.Finite ℚ_[p] (Shrink.{0} L) :=
    .equiv (Shrink.algEquiv ℚ_[p] L).symm.toLinearEquiv
  have hK : Module.Finite ℚ_[p] (Shrink.{0} K) :=
    .equiv (Shrink.algEquiv ℚ_[p] K).symm.toLinearEquiv
  have hG : IsGalois (Shrink.{0} K) (Shrink.{0} L) :=
    IsGalois.of_equiv_equiv (f := eK.symm) (g := eL.symm) (RingHom.ext fun k ↦ by
      simp [halg])
  -- The isomorphism of Galois groups, by conjugation with `eL`.
  have hfix (σ : L ≃ₐ[K] L) (k : Shrink.{0} K) :
      eL.symm (σ (eL (algebraMap (Shrink.{0} K) (Shrink.{0} L) k))) =
        algebraMap (Shrink.{0} K) (Shrink.{0} L) k := by
    rw [halg, RingEquiv.apply_symm_apply, AlgEquiv.commutes]
  have hfix' (σ' : Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L) (k : K) :
      eL (σ' (eL.symm (algebraMap K L k))) = algebraMap K L k := by
    have hk : eL.symm (algebraMap K L k) =
        algebraMap (Shrink.{0} K) (Shrink.{0} L) (eK.symm k) := by
      rw [halg, RingEquiv.apply_symm_apply]
    rw [hk, AlgEquiv.commutes, ← hk, RingEquiv.apply_symm_apply]
  let φ : (L ≃ₐ[K] L) ≃* (Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L) :=
    { toFun σ := AlgEquiv.ofRingEquiv (f := (eL.trans σ.toRingEquiv).trans eL.symm) (hfix σ)
      invFun σ' := AlgEquiv.ofRingEquiv (f := (eL.symm.trans σ'.toRingEquiv).trans eL) (hfix' σ')
      left_inv σ := AlgEquiv.ext fun y ↦ by
        -- `AlgEquiv.ofRingEquiv` applies its ring equivalence, a conjugate by `eL`.
        change eL (eL.symm (σ (eL (eL.symm y)))) = σ y
        simp
      right_inv σ' := AlgEquiv.ext fun y ↦ by
        -- `AlgEquiv.ofRingEquiv` applies its ring equivalence, a conjugate by `eL`.
        change eL.symm (eL (σ' (eL.symm (eL y)))) = σ' y
        simp
      map_mul' σ τ := AlgEquiv.ext fun y ↦ by
        -- `AlgEquiv.ofRingEquiv` applies its ring equivalence, a conjugate by `eL`.
        change eL.symm ((σ * τ) (eL y)) = eL.symm (σ (eL (eL.symm (τ (eL y)))))
        simp [AlgEquiv.mul_apply] }
  have : Finite (Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L) := .of_equiv _ φ.toEquiv
  have hfd : FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) :=
    IsGalois.finiteDimensional_of_finite _ _
  obtain ⟨Y⟩ := @nonempty_layerTateModule_of_type p _ (Shrink.{0} L) (Shrink.{0} K) _ _ _ _ hL _ hK
    hst hG hfd
  exact LayerTateModule.nonempty_of_equiv φ (padicCompletionUnitsCongr p eL.symm)
    (padicCompletionUnitsCongr_smul p eL.symm)
    (fun σ x ↦ padicCompletionUnitsCongr_aut p K eL.symm σ (φ σ) (fun y ↦ by
      -- `φ σ` is the conjugate of `σ` by `eL`.
      change eL.symm (σ (eL (eL.symm y))) = eL.symm (σ y)
      simp) x) Y

end TauCeti

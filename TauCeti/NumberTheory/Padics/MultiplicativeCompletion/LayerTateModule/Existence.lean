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

* `TauCeti.LayerTateModule.nonempty_of_equiv`: a Tate module transports along an isomorphism of
  layers.
* `TauCeti.nonempty_layerTateModule`: the Tate module of a finite Galois layer of `p`-adic fields
  exists.

## Implementation notes

Local reciprocity and Mathlib's representations are stated for fields in `Type`. For fields in
an arbitrary universe the layer is first moved to its copy `Shrink L / Shrink K` in `Type`, and
the Tate module of the copy is carried back along the induced isomorphisms of Galois groups and
of `A(L)` (`TauCeti.padicCompletionUnitsCongr`).

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.6.4), (5.6.5)
  and the proof of (7.4.1).
-/

public section

namespace TauCeti

open CategoryTheory Limits

variable (p : ℕ) [Fact p.Prime]

universe u

namespace LayerTateModule

variable {p}

/-- **Transport of the Tate module along an isomorphism of layers.** Let `L/K` and `L'/K'` be
layers, `L', K'` in `Type`, with an isomorphism `φ` of their automorphism groups and a
`ℤ_p`-linear isomorphism `A(L) ≃ A(L')` intertwining the actions of `σ` and `φ σ`. Then a Tate
module of `L'/K'` gives one of `L/K`: its carrier, lifted to the universe of `L`, is a module over
`ℤ_p[Gal(L/K)]` through the induced isomorphism of group algebras. -/
theorem nonempty_of_equiv {L K : Type u} [Field L] [Field K] [Algebra K L]
    {L' K' : Type} [Field L'] [Field K'] [Algebra K' L']
    (φ : (L ≃ₐ[K] L) ≃* (L' ≃ₐ[K'] L'))
    (c : ↑(padicCompletionUnits p L) ≃* ↑(padicCompletionUnits p L'))
    (hsmul : ∀ (a : ℤ_[p]) (x : Additive ↑(padicCompletionUnits p L)),
      Additive.ofMul (c (a • x).toMul) = a • Additive.ofMul (c x.toMul))
    (haut : ∀ σ x, c (padicCompletionUnitsAut p L K σ x) =
      padicCompletionUnitsAut p L' K' (φ σ) (c x))
    (Y : LayerTateModule p L' K') : Nonempty (LayerTateModule p L K) := by
  let R := MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)
  let R' := MonoidAlgebra ℤ_[p] (L' ≃ₐ[K'] L')
  let Φ : R ≃+* R' := MonoidAlgebra.mapDomainRingEquiv ℤ_[p] φ
  have : RingHomInvPair (Φ : R →+* R') (Φ.symm : R' →+* R) := .of_ringEquiv Φ
  have : RingHomInvPair (Φ.symm : R' →+* R) (Φ : R →+* R') := .of_ringEquiv_symm Φ
  -- `A(L) ≃ A(L')` is `Φ`-semilinear.
  have hc (r : R) (x : Additive ↑(padicCompletionUnits p L)) :
      Additive.ofMul (c (r • x).toMul) = Φ r • Additive.ofMul (c x.toMul) := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r s hr hs =>
      rw [add_smul, toMul_add, map_mul, ofMul_mul, hr, hs, map_add, add_smul]
    | single σ a =>
      obtain ⟨x, rfl⟩ : ∃ y, Additive.ofMul y = x := ⟨x.toMul, rfl⟩
      rw [MonoidAlgebra.mapDomainRingEquiv_single, padicCompletionUnits_single_smul, hsmul,
        toMul_ofMul, toMul_ofMul, haut, padicCompletionUnits_single_smul]
  let cS : Additive ↑(padicCompletionUnits p L) ≃ₛₗ[(Φ : R →+* R')]
      Additive ↑(padicCompletionUnits p L') :=
    { c.toAdditive with map_smul' := hc }
  -- The carrier, lifted to the universe of `L`, as an `R`-module through `Φ`.
  let _ : Module R (ULift.{u} Y.carrier) := Module.compHom _ (Φ : R →+* R')
  let eY : ULift.{u} Y.carrier ≃ₛₗ[(Φ : R →+* R')] Y.carrier :=
    { toFun := ULift.down
      invFun := ULift.up
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv _ := rfl
      right_inv _ := rfl }
  -- `Φ` identifies the augmentation ideals.
  have hI : Submodule.map (Φ.toSemilinearEquiv : R →ₛₗ[(Φ : R →+* R')] R')
      (RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L))) =
      RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L' ≃ₐ[K'] L')) := by
    ext y
    rw [Submodule.mem_map_equiv, RingHom.mem_ker, RingHom.mem_ker,
      ← MonoidAlgebra.augmentation_mapDomainRingEquiv ℤ_[p] φ]
    exact Iff.of_eq (congrArg (· = 0) (congrArg _ (Φ.apply_symm_apply y)))
  let eI := Φ.toSemilinearEquiv.ofSubmodules _ _ hI
  obtain ⟨n, f', hf', hker'⟩ := Y.projdim
  let PΦ : (Fin n → R) ≃ₛₗ[(Φ : R →+* R')] (Fin n → R') :=
    { toFun v i := Φ (v i)
      invFun v i := Φ.symm (v i)
      map_add' _ _ := funext fun _ ↦ map_add Φ _ _
      map_smul' _ _ := funext fun _ ↦ map_mul Φ _ _
      left_inv _ := funext fun _ ↦ Φ.symm_apply_apply _
      right_inv _ := funext fun _ ↦ Φ.apply_symm_apply _ }
  let ι : Additive ↑(padicCompletionUnits p L) →ₗ[R] ULift.{u} Y.carrier :=
    eY.symm.toLinearMap.comp (Y.ι.comp cS.toLinearMap)
  let π : ULift.{u} Y.carrier →ₗ[R] RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L)) :=
    eI.symm.toLinearMap.comp (Y.π.comp eY.toLinearMap)
  let f : (Fin n → R) →ₗ[R] ULift.{u} Y.carrier :=
    eY.symm.toLinearMap.comp (f'.comp PΦ.toLinearMap)
  have hf : Function.Surjective f :=
    eY.symm.surjective.comp (hf'.comp PΦ.surjective)
  have hker : (LinearMap.ker f).map (PΦ : (Fin n → R) →ₛₗ[(Φ : R →+* R')] (Fin n → R')) =
      LinearMap.ker f' := by
    ext v
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
    -- Unfold the local definitions of `f` and of the inverse of `PΦ`.
    change eY.symm (f' (PΦ (PΦ.symm v))) = 0 ↔ _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.map_eq_zero_iff]
  have : Module.Projective R (LinearMap.ker f) :=
    .of_equiv (σ := (Φ.symm : R' →+* R)) (σ' := (Φ : R →+* R'))
      (PΦ.ofSubmodules _ _ hker).symm
  have hιπ : Function.Exact ι π := by
    intro y
    -- Unfold the local definitions of `ι` and `π`.
    change eI.symm (Y.π (eY y)) = 0 ↔ ∃ x, eY.symm (Y.ι (cS x)) = y
    rw [LinearEquiv.map_eq_zero_iff, ← LinearMap.mem_ker, Y.exact, LinearMap.mem_range]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨cS.symm x, by rw [LinearEquiv.apply_symm_apply, hx, LinearEquiv.symm_apply_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨cS x, (eY.apply_symm_apply _).symm⟩
  exact ⟨{
    carrier := ULift.{u} Y.carrier
    ι := ι
    π := π
    ι_injective := eY.symm.injective.comp (Y.ι_injective.comp cS.injective)
    π_surjective := eI.symm.surjective.comp (Y.π_surjective.comp eY.surjective)
    exact := LinearMap.exact_iff.mp hιπ
    finite := .of_surjective f hf
    projdim := ⟨n, f, hf, this⟩ }⟩

end LayerTateModule

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

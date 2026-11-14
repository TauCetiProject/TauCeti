/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.Algebra.AlgebraicGroup.Connected.GroupScheme
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Components
import TauCeti.Algebra.AlgebraicGroup.Reductive.CompleteReducibility
import TauCeti.Algebra.AlgebraicGroup.Representation.Coinvariants
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Hom
import TauCeti.Algebra.AlgebraicGroup.Representation.Translation
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.ColinearSection
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Exact
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Fixed
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Weight
import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Linear reductivity via the identity component

Let `H` be a finite-type commutative Hopf algebra over a field `k`, representing an affine group
`G` of finite type without any connectedness or reducedness assumption. After extension to an
algebraic closure `K = AlgebraicClosure k`, the group sits in an exact sequence with normal
connected subgroup `(G_K)°` and finite constant component quotient `π₀(G_K)`. This file
characterizes linear reductivity of `G` in terms of `(G_K)°` and the order of `π₀(G_K)`:

* Over an algebraically closed field `k`, `G` is linearly reductive if and only if `G°` is linearly
  reductive and `(Nat.card π₀(G) : k) ≠ 0`.
* Over an arbitrary field `k`, `G` is linearly reductive if and only if `(G_K)°` is linearly
  reductive over `K` and `(Nat.card π₀(G_K) : k) ≠ 0`.
* Over a field `k` of characteristic zero, the component-order condition is automatic and `(G_K)°`
  is smooth by Cartier's theorem, so `G` is linearly reductive if and only if `(G_K)°` is
  reductive (Milne, *Algebraic Groups*, Corollary 22.43).

This reduces linear reductivity of disconnected affine groups to the connected case, both in
characteristic zero and in positive characteristic.

## Main declarations

* `TauCeti.linearlyReductiveCommHopfAlgProperty.of_colinear_section`: linear reductivity descends
  along a morphism of commutative Hopf algebras admitting a unital left-colinear linear section.
* `TauCeti.linearlyReductiveCommHopfAlgProperty.natCast_card_connectedComponents_ne_zero`: over an
  algebraically closed field, the number of connected components of a linearly reductive
  finite-type affine group is nonzero in `k`.
* `TauCeti.linearlyReductiveCommHopfAlgProperty.identityComponent`: linear reductivity passes from
  a finite-type affine group over an algebraically closed field to its identity component.
* `TauCeti.linearlyReductiveCommHopfAlgProperty.of_identityComponent`: linear reductivity of the
  identity component together with invertible component-group order implies linear reductivity.
* `TauCeti.linearlyReductiveCommHopfAlgProperty_iff_identityComponent_of_isAlgClosed` and
  `TauCeti.linearlyReductiveCommHopfAlgProperty_iff_identityComponent`: the full characterization
  over an algebraically closed field and over an arbitrary field.
* `TauCeti.linearlyReductiveCommHopfAlgProperty_iff_identityComponent_of_charZero` and
  `TauCeti.linearlyReductiveCommHopfAlgProperty_iff_reductive_identityComponent`: in characteristic
  zero, linear reductivity is equivalent to linear reductivity, and hence to reductivity, of the
  geometric identity component.

## References

* M. Nagata, *Complete reducibility of rational representations of a matric group*,
  J. Math. Kyoto Univ. **1** (1961), 87–99.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.g and Corollary 22.43.
-/

public section

open scoped TensorProduct
open CategoryTheory WithConv

namespace TauCeti

universe u v

/-- Linear reductivity descends along a morphism of commutative Hopf algebras over a field `k`
admitting a unital `k`-linear map `σ` that intertwines `(q ⊗ id) ∘ Δ_C ∘ σ = (id ⊗ σ) ∘ Δ_D`. -/
theorem linearlyReductiveCommHopfAlgProperty.of_colinear_section {k : Type u} [Field k]
    {C D : CommHopfAlgCat.{v} k}
    (q : C ⟶ D) (σ : D →ₗ[k] C) (hσ1 : σ 1 = 1)
    (hσ : ∀ x : D,
      ((q.hom.toCoalgHom : C →ₗ[k] D).rTensor C) (Coalgebra.comul (R := k) (σ x)) =
        σ.lTensor D (Coalgebra.comul (R := k) x))
    (hC : linearlyReductiveCommHopfAlgProperty k C) :
    linearlyReductiveCommHopfAlgProperty k D := by
  rw [linearlyReductiveCommHopfAlgProperty_iff] at hC ⊢
  rw [Coalgebra.isLinearlyReductive_iff_forall_fixedMap_surjective_of_surjective]
  intro M N f hf
  exact Comodule.Hom.fixedMap_surjective_of_colinear_section q.hom σ hσ1 hσ hC f.hom hf

section IsAlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, the number of connected components of a linearly reductive
finite-type affine group is nonzero in the base field. -/
theorem linearlyReductiveCommHopfAlgProperty.natCast_card_connectedComponents_ne_zero
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : linearlyReductiveCommHopfAlgProperty k H.obj) :
    (Nat.card (ConnectedComponents (PrimeSpectrum H)) : k) ≠ 0 := by
  have hcomp := linearlyReductiveCommHopfAlgProperty.of_injective
    (FiniteTypeCommHopfAlgCat.componentCoordinateHom H)
    (FiniteTypeCommHopfAlgCat.componentCoordinateHom_injective H) hH
  exact (ConstantGroup.linearlyReductiveCommHopfAlgProperty_coordinateRing_iff k
    (ConnectedComponents (PrimeSpectrum H))).mp hcomp

section IdentityComponentSection

/-- The exposed quotient bialgebra morphism onto the identity component. -/
private noncomputable abbrev identityComponentBialgHom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    H →ₐc[k] FiniteTypeCommHopfAlgCat.identityComponent H :=
  FiniteTypeCommHopfAlgCat.toBialgHom
    (FiniteTypeCommHopfAlgCat.mkQuotient H
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)))

/-- The canonical idempotent of `H` attached to a connected component of `Spec H`, expressed as the
image of the corresponding constant-group delta function. -/
private noncomputable def componentDeltaIdempotent (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (C : ConnectedComponents (PrimeSpectrum H)) : H :=
  FiniteTypeCommHopfAlgCat.componentCoordinateBialgHom H
    (ConstantGroup.delta k (ConnectedComponents (PrimeSpectrum H)) C)

private theorem componentDeltaIdempotent_eq (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (C : ConnectedComponents (PrimeSpectrum H)) :
    componentDeltaIdempotent H C = PrimeSpectrum.connectedComponentsIdempotent C := by
  classical
  rw [componentDeltaIdempotent, FiniteTypeCommHopfAlgCat.componentCoordinateBialgHom_apply,
    ← FiniteTypeCommHopfAlgCat.componentCoordinateMap_indicator H C]
  congr 1
  apply (ConstantGroup.functionAlgEquiv k (ConnectedComponents (PrimeSpectrum H))).injective
  rw [ConstantGroup.functionAlgEquiv_delta, AlgEquiv.apply_symm_apply]

private theorem componentDeltaIdempotent_one (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    componentDeltaIdempotent H 1 =
      PrimeSpectrum.connectedComponentIdempotent (R := H) (Bialgebra.augmentationPoint k H) := by
  rw [componentDeltaIdempotent_eq, ← FiniteTypeCommHopfAlgCat.rationalKernelPoint_one_component H]
  exact PrimeSpectrum.connectedComponentsIdempotent_mk (Bialgebra.augmentationPoint k H)

private theorem mulRight_componentDeltaIdempotent_one_mem_ker
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) {x : H}
    (hx : x ∈
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal.restrictScalars k) :
    x ∈ LinearMap.ker (LinearMap.mulRight k (componentDeltaIdempotent H 1)) := by
  have hx_ideal : x ∈ (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal := hx
  rw [HopfAlgebra.identityComponentHopfIdeal_toIdeal_eq_span,
    ← componentDeltaIdempotent_one H, Ideal.mem_span_singleton] at hx_ideal
  obtain ⟨a, rfl⟩ := hx_ideal
  have hidem : IsIdempotentElem (componentDeltaIdempotent H 1) := by
    rw [componentDeltaIdempotent_one]
    exact PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent _
  rw [LinearMap.mem_ker, LinearMap.mulRight_apply, mul_right_comm, sub_mul, one_mul,
    hidem.eq, sub_self, zero_mul]

/-- Right multiplication by the identity-component idempotent descends from `H` to a `k`-linear
section `identityComponent H →ₗ[k] H`. -/
private noncomputable def identityComponentIdempotentSection
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    FiniteTypeCommHopfAlgCat.identityComponent H →ₗ[k] H :=
  ((HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal.restrictScalars k).liftQ
    (LinearMap.mulRight k (componentDeltaIdempotent H 1))
    (fun _ hx ↦ mulRight_componentDeltaIdempotent_one_mem_ker H hx)

private theorem identityComponentIdempotentSection_mk (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (a : H) :
    identityComponentIdempotentSection H (identityComponentBialgHom H a) =
      a * componentDeltaIdempotent H 1 := by
  let p := (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal.restrictScalars k
  have hmk : (identityComponentBialgHom H a : H ⧸ p) = Submodule.Quotient.mk (p := p) a := by
    -- Unfold the full-subcategory morphism wrapper to use `CommHopfAlgCat.mkQuotient_apply`.
    change (CommHopfAlgCat.mkQuotient H.obj _).hom a = _
    rw [CommHopfAlgCat.mkQuotient_apply]
    rfl
  -- Align the quotient carrier with `H ⧸ p` before applying `Submodule.liftQ_apply`.
  change p.liftQ (LinearMap.mulRight k (componentDeltaIdempotent H 1)) _
    (identityComponentBialgHom H a : H ⧸ p) = _
  rw [hmk, Submodule.liftQ_apply, LinearMap.mulRight_apply]

private theorem comul_componentDeltaIdempotent_one (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    [Fintype (ConnectedComponents (PrimeSpectrum H))] :
    Coalgebra.comul (R := k) (componentDeltaIdempotent H 1) =
      ∑ C : ConnectedComponents (PrimeSpectrum H),
        componentDeltaIdempotent H C ⊗ₜ[k] componentDeltaIdempotent H C⁻¹ := by
  let ι := FiniteTypeCommHopfAlgCat.componentCoordinateBialgHom H
  have hmap := (CoalgHomClass.map_comp_comul_apply ι
    (ConstantGroup.delta k (ConnectedComponents (PrimeSpectrum H)) 1)).symm
  rw [componentDeltaIdempotent, hmap, ConstantGroup.comul_delta, map_sum]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  rw [mul_one, TensorProduct.map_tmul]
  rfl

private theorem rTensor_identityComponentBialgHom_comul_idempotent
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    ((identityComponentBialgHom H).toLinearMap.rTensor H)
      (Coalgebra.comul (R := k) (componentDeltaIdempotent H 1)) =
      (1 : FiniteTypeCommHopfAlgCat.identityComponent H) ⊗ₜ[k] componentDeltaIdempotent H 1 := by
  classical
  let _ : Fintype (ConnectedComponents (PrimeSpectrum H)) := Fintype.ofFinite _
  let q := identityComponentBialgHom H
  have hq1 : q (componentDeltaIdempotent H 1) = 1 := by
    have hmem : 1 - componentDeltaIdempotent H 1 ∈
        HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) := by
      rw [← HopfIdeal.mem_toIdeal, HopfAlgebra.identityComponentHopfIdeal_toIdeal_eq_span,
        ← componentDeltaIdempotent_one H]
      exact Ideal.subset_span rfl
    have hzero : q (1 - componentDeltaIdempotent H 1) = 0 :=
      (FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff H _ _).mpr hmem
    rw [map_sub, map_one, sub_eq_zero] at hzero
    exact hzero.symm
  have hqne {C : ConnectedComponents (PrimeSpectrum H)} (hC : C ≠ 1) :
      q (componentDeltaIdempotent H C) = 0 := by
    have hortho : componentDeltaIdempotent H C * componentDeltaIdempotent H 1 = 0 := by
      rw [componentDeltaIdempotent_eq, componentDeltaIdempotent_eq]
      exact PrimeSpectrum.orthogonalIdempotents_connectedComponentsIdempotent.ortho hC
    calc
      q (componentDeltaIdempotent H C) =
          q (componentDeltaIdempotent H C) * q (componentDeltaIdempotent H 1) := by
        rw [hq1, mul_one]
      _ = q (componentDeltaIdempotent H C * componentDeltaIdempotent H 1) := (map_mul q _ _).symm
      _ = 0 := by rw [hortho, map_zero]
  rw [comul_componentDeltaIdempotent_one H, map_sum, Finset.sum_eq_single 1]
  · rw [inv_one, LinearMap.rTensor_tmul]
    exact congrArg (fun z ↦ z ⊗ₜ[k] componentDeltaIdempotent H 1) hq1
  · intro C _ hC
    rw [LinearMap.rTensor_tmul]
    have h0 : q.toLinearMap (componentDeltaIdempotent H C) = 0 := hqne hC
    rw [h0, TensorProduct.zero_tmul]
  · simp

private theorem rTensor_identityComponentBialgHom_comul_idempotentSection
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : FiniteTypeCommHopfAlgCat.identityComponent H) :
    ((identityComponentBialgHom H).toLinearMap.rTensor H)
      (Coalgebra.comul (R := k) (identityComponentIdempotentSection H x)) =
      (identityComponentIdempotentSection H).lTensor (FiniteTypeCommHopfAlgCat.identityComponent H)
        (Coalgebra.comul (R := k) x) := by
  let q := identityComponentBialgHom H
  obtain ⟨a, ha⟩ := CommHopfAlgCat.mkQuotient_surjective H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) x
  have hqa : q a = x := ha
  rw [← hqa, identityComponentIdempotentSection_mk]
  let Φ : H →ₐ[k] FiniteTypeCommHopfAlgCat.identityComponent H ⊗[k] H :=
    (Algebra.TensorProduct.map q.toAlgHom (AlgHom.id k H)).comp (Bialgebra.comulAlgHom k H)
  have hΦ (b : H) : Φ b = (q.toLinearMap.rTensor H) (Coalgebra.comul (R := k) b) := by
    simp only [Φ, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, LinearMap.rTensor_def]
    induction Coalgebra.comul (R := k) b using TensorProduct.inductionOn with
    | tmul u v => rfl
    | add u v hu hv => simp [hu, hv]
  have hmul (w : FiniteTypeCommHopfAlgCat.identityComponent H ⊗[k] H) :
      w * ((1 : FiniteTypeCommHopfAlgCat.identityComponent H) ⊗ₜ[k] componentDeltaIdempotent H 1) =
        (LinearMap.mulRight k (componentDeltaIdempotent H 1)).lTensor
          (FiniteTypeCommHopfAlgCat.identityComponent H) w := by
    induction w using TensorProduct.inductionOn with
    | tmul u v => simp
    | add u v hu hv => simp [add_mul, hu, hv]
  calc
    (q.toLinearMap.rTensor H) (Coalgebra.comul (R := k) (a * componentDeltaIdempotent H 1)) =
        Φ a * Φ (componentDeltaIdempotent H 1) := by
      rw [← hΦ, map_mul]
    _ = (LinearMap.mulRight k (componentDeltaIdempotent H 1)).lTensor
          (FiniteTypeCommHopfAlgCat.identityComponent H)
          ((q.toLinearMap.rTensor H) (Coalgebra.comul (R := k) a)) := by
      rw [hΦ (componentDeltaIdempotent H 1),
        rTensor_identityComponentBialgHom_comul_idempotent H, hmul, hΦ a]
    _ = (identityComponentIdempotentSection H).lTensor
          (FiniteTypeCommHopfAlgCat.identityComponent H) (Coalgebra.comul (R := k) (q a)) := by
      have hqcomul : Coalgebra.comul (R := k) (q a) =
          TensorProduct.map q.toLinearMap q.toLinearMap (Coalgebra.comul (R := k) a) :=
        (CoalgHomClass.map_comp_comul_apply q a).symm
      rw [hqcomul]
      induction Coalgebra.comul (R := k) a using TensorProduct.inductionOn with
      | tmul u v =>
        simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
          LinearMap.mulRight_apply]
        have hqv : q.toLinearMap v = identityComponentBialgHom H v := rfl
        rw [hqv, identityComponentIdempotentSection_mk]
      | add u v hu hv => simp only [map_add, hu, hv]

private theorem rightTranslationAlgHom_idempotent_one
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (u : WithConv (H →ₐ[k] k)) {C : ConnectedComponents (PrimeSpectrum H)}
    (hu : FiniteTypeCommHopfAlgCat.rationalComponentMap H u = C⁻¹) :
    HopfAlgebra.rightTranslationAlgHom u (componentDeltaIdempotent H 1) =
      componentDeltaIdempotent H C := by
  classical
  let _ : Fintype (ConnectedComponents (PrimeSpectrum H)) := Fintype.ofFinite _
  have heval (D : ConnectedComponents (PrimeSpectrum H)) :
      u.ofConv (componentDeltaIdempotent H D⁻¹) = if D = C then 1 else 0 := by
    have h := AlgHom.congr_fun (FiniteTypeCommHopfAlgCat.eval_componentCoordinateMap H u)
      (ConstantGroup.delta k (ConnectedComponents (PrimeSpectrum H)) D⁻¹)
    rw [AlgHom.comp_apply, hu, ConstantGroup.eval_apply,
      ConstantGroup.functionAlgEquiv_delta, Pi.single_apply] at h
    simpa [componentDeltaIdempotent, inv_inj, eq_comm] using h
  rw [HopfAlgebra.rightTranslationAlgHom_apply, comul_componentDeltaIdempotent_one H,
    map_sum, map_sum, Finset.sum_eq_single C]
  · simp [heval C]
  · intro D _ hDC
    simp [heval D, hDC]
  · simp

private theorem sum_rightTranslationAlgHom_idempotentSection_one
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    [Fintype (ConnectedComponents (PrimeSpectrum H))]
    (g : ConnectedComponents (PrimeSpectrum H) → WithConv (H →ₐ[k] k))
    (hg : ∀ C, FiniteTypeCommHopfAlgCat.rationalComponentMap H (g C) = C) :
    (∑ C : ConnectedComponents (PrimeSpectrum H),
        (HopfAlgebra.rightTranslationAlgHom (g C)⁻¹).toLinearMap ∘ₗ
          identityComponentIdempotentSection H) 1 = 1 := by
  have hmk1 : identityComponentIdempotentSection H 1 = componentDeltaIdempotent H 1 := by
    simpa only [map_one, one_mul] using identityComponentIdempotentSection_mk H 1
  have hsum : ∑ C : ConnectedComponents (PrimeSpectrum H), componentDeltaIdempotent H C = 1 := by
    simp_rw [componentDeltaIdempotent_eq]
    exact PrimeSpectrum.completeOrthogonalIdempotents_connectedComponentsIdempotent.complete
  rw [LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, hmk1, AlgHom.toLinearMap_apply]
  have hterm (C : ConnectedComponents (PrimeSpectrum H)) :
      HopfAlgebra.rightTranslationAlgHom (g C)⁻¹ (componentDeltaIdempotent H 1) =
        componentDeltaIdempotent H C :=
    rightTranslationAlgHom_idempotent_one H (g C)⁻¹ (by rw [map_inv, hg C])
  simp_rw [hterm]
  exact hsum

/-- Summing right translates of `identityComponentIdempotentSection` over coset representatives of
`π₀` yields a unital left `(identityComponent H)`-colinear section `identityComponent H →ₗ[k] H`. -/
private theorem exists_unital_colinear_section (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    ∃ σ : FiniteTypeCommHopfAlgCat.identityComponent H →ₗ[k] H,
      σ 1 = 1 ∧
      ∀ x : FiniteTypeCommHopfAlgCat.identityComponent H,
        ((identityComponentBialgHom H).toLinearMap.rTensor H)
          (Coalgebra.comul (R := k) (σ x)) =
          σ.lTensor (FiniteTypeCommHopfAlgCat.identityComponent H)
            (Coalgebra.comul (R := k) x) := by
  classical
  let _ : Fintype (ConnectedComponents (PrimeSpectrum H)) := Fintype.ofFinite _
  let H₀ := FiniteTypeCommHopfAlgCat.identityComponent H
  let g : ConnectedComponents (PrimeSpectrum H) → WithConv (H →ₐ[k] k) := fun C ↦
    Classical.choose (FiniteTypeCommHopfAlgCat.rationalComponentMap_surjective H C)
  have hg (C : ConnectedComponents (PrimeSpectrum H)) :
      FiniteTypeCommHopfAlgCat.rationalComponentMap H (g C) = C :=
    Classical.choose_spec (FiniteTypeCommHopfAlgCat.rationalComponentMap_surjective H C)
  let σ : H₀ →ₗ[k] H :=
    ∑ C : ConnectedComponents (PrimeSpectrum H),
      (HopfAlgebra.rightTranslationAlgHom (g C)⁻¹).toLinearMap ∘ₗ
        identityComponentIdempotentSection H
  refine ⟨σ, sum_rightTranslationAlgHom_idempotentSection_one H g hg, fun x ↦ ?_⟩
  let q := (identityComponentBialgHom H).toLinearMap
  have hlsum (z : H₀ ⊗[k] H₀) :
      σ.lTensor H₀ z =
        ∑ C : ConnectedComponents (PrimeSpectrum H),
          ((HopfAlgebra.rightTranslationAlgHom (g C)⁻¹).toLinearMap ∘ₗ
            identityComponentIdempotentSection H).lTensor H₀ z := by
    induction z using TensorProduct.inductionOn with
    | tmul u v => simp [σ, LinearMap.sum_apply, TensorProduct.tmul_sum]
    | add u v hu hv => simp [hu, hv, Finset.sum_add_distrib]
  rw [LinearMap.sum_apply, map_sum, map_sum, hlsum]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  let τ := (HopfAlgebra.rightTranslationAlgHom (g C)⁻¹).toLinearMap
  calc
    (q.rTensor H)
          (Coalgebra.comul (R := k)
            (HopfAlgebra.rightTranslationAlgHom (g C)⁻¹
              (identityComponentIdempotentSection H x))) =
        (q.rTensor H)
          (τ.lTensor H (Coalgebra.comul (R := k) (identityComponentIdempotentSection H x))) := by
      rw [HopfAlgebra.comul_rightTranslationAlgHom]
    _ = τ.lTensor H₀
          ((q.rTensor H)
            (Coalgebra.comul (R := k) (identityComponentIdempotentSection H x))) := by
      rw [LinearMap.lTensor_rTensor_comm]
    _ = (τ ∘ₗ identityComponentIdempotentSection H).lTensor H₀ (Coalgebra.comul (R := k) x) := by
      rw [rTensor_identityComponentBialgHom_comul_idempotentSection H x,
        LinearMap.lTensor_comp, LinearMap.comp_apply]

/-- **Linear reductivity passes to the identity component.** Over an algebraically closed field,
if a finite-type affine group is linearly reductive, then its identity component is linearly
reductive, with no reducedness hypothesis. -/
theorem linearlyReductiveCommHopfAlgProperty.identityComponent
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : linearlyReductiveCommHopfAlgProperty k H.obj) :
    linearlyReductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.identityComponent H).obj := by
  obtain ⟨σ, hσ1, hσ⟩ := exists_unital_colinear_section H
  exact linearlyReductiveCommHopfAlgProperty.of_colinear_section
    (FiniteTypeCommHopfAlgCat.mkQuotient H
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))).hom σ hσ1 hσ hH

end IdentityComponentSection

section Converse

/-- Averaging a vector fixed by the identity component over coset representatives of `π₀` produces
a vector fixed by the whole affine group. -/
private theorem average_mem_fixedSubcomodule_of_identityComponent_fixed
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M]
    (g : ConnectedComponents (PrimeSpectrum H) → WithConv (H →ₐ[k] k))
    (hg : ∀ C, FiniteTypeCommHopfAlgCat.rationalComponentMap H (g C) = C)
    [Fintype (ConnectedComponents (PrimeSpectrum H))]
    {m₀ : M}
    (hm₀ : TensorProduct.map LinearMap.id
      (Ideal.Quotient.mkₐ k
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal).toLinearMap
      (Comodule.coact (R := k) (C := H) m₀) =
        m₀ ⊗ₜ[k] (1 : H ⧸ (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal)) :
    ((Nat.card (ConnectedComponents (PrimeSpectrum H)) : k)⁻¹ •
        ∑ C : ConnectedComponents (PrimeSpectrum H),
          Comodule.basePointsRepresentation (H := H) M (g C) m₀) ∈
      Comodule.fixedSubcomodule k H M := by
  let _ : Module.Free k M := Module.Free.of_divisionRing k M
  let π₀ := ConnectedComponents (PrimeSpectrum H)
  let m : M := (Nat.card π₀ : k)⁻¹ • ∑ C : π₀, Comodule.basePointsRepresentation (H := H) M (g C) m₀
  rw [Comodule.mem_fixedSubcomodule, Comodule.coact_eq_tmul_iff_forall_matrixCoefficient]
  intro ψ
  have hcoinv : Comodule.matrixCoefficient (R := k) (C := H) ψ m₀ ∈
      (FiniteTypeCommHopfAlgCat.componentCoordinateMap H).range := by
    rw [← FiniteTypeCommHopfAlgCat.coinvariants_identityComponentHopfIdeal_eq_range H]
    exact (HopfAlgebra.identityComponentHopfIdeal (k := k)
      (H := H)).matrixCoefficient_mem_coinvariants_of_quotient_coact_eq_tmul_one M ψ m₀ hm₀
  obtain ⟨a, ha⟩ := hcoinv
  let ι := FiniteTypeCommHopfAlgCat.componentCoordinateBialgHom H
  have ha' : ι a = Comodule.matrixCoefficient (R := k) (C := H) ψ m₀ :=
    (FiniteTypeCommHopfAlgCat.componentCoordinateBialgHom_apply H a).trans ha
  have hmap (C : π₀) : BialgHom.mapDomain ι (g C) = ConstantGroup.toPoints k π₀ C := by
    apply WithConv.ofConv_injective
    ext x
    have hev := AlgHom.congr_fun (FiniteTypeCommHopfAlgCat.eval_componentCoordinateMap H (g C)) x
    rw [AlgHom.comp_apply, hg C] at hev
    simpa [BialgHom.mapDomain_apply, ι] using hev
  have hsum_range : Comodule.matrixCoefficient (R := k) (C := H) ψ m ∈
      Set.range (algebraMap k H) := by
    have hcoeff : Comodule.matrixCoefficient (R := k) (C := H) ψ m =
        (Nat.card π₀ : k)⁻¹ •
          ι (∑ C : π₀, HopfAlgebra.rightTranslationAlgHom (ConstantGroup.toPoints k π₀ C) a) := by
      rw [← Comodule.matrixCoefficientLinear_apply, map_smul, map_sum, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun C _ ↦ ?_
      rw [Comodule.matrixCoefficientLinear_apply,
        ← HopfAlgebra.rightTranslationAlgHom_matrixCoefficient, ← ha']
      have htr := AlgHom.congr_fun (BialgHom.comp_rightTranslationAlgHom ι (g C)) a
      simpa only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, hmap C] using htr.symm
    obtain ⟨r, hr⟩ := ConstantGroup.sum_rightTranslationAlgHom_toPoints_mem_range (R := k) a
    refine ⟨(Nat.card π₀ : k)⁻¹ * r, ?_⟩
    rw [hcoeff, ← hr, AlgHomClass.commutes ι r, map_mul, Algebra.smul_def]
  obtain ⟨s, hs⟩ := hsum_range
  have hs_eq : s = ψ m := by
    have hε := congrArg (Bialgebra.counitAlgHom k H) hs
    simpa only [AlgHom.commutes, Algebra.algebraMap_self_apply,
      Bialgebra.counitAlgHom_apply, Comodule.counit_matrixCoefficient] using hε
  rw [← hs, hs_eq, Algebra.smul_def, mul_one]

/-- When the identity component is linearly reductive, any `H`-invariant element in the image of a
comodule morphism lifts to a preimage fixed by the restricted coaction of `identityComponent H`. -/
private theorem exists_identityComponent_fixed_preimage
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH₀ : linearlyReductiveCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.identityComponent H).obj)
    {M N : Type u} [AddCommGroup M] [Module k M] [Comodule k H M]
    [AddCommGroup N] [Module k N] [Comodule k H N]
    (φ : Comodule.Hom k H M N) {n : N} (hn : n ∈ Comodule.fixedSubcomodule k H N)
    (hrange : n ∈ LinearMap.range φ.toLinearMap) :
    ∃ m₀ : M, φ m₀ = n ∧
      TensorProduct.map LinearMap.id
        (Ideal.Quotient.mkₐ k
          (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal).toLinearMap
        (Comodule.coact (R := k) (C := H) m₀) =
          m₀ ⊗ₜ[k]
            (1 : H ⧸ (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal) := by
  let H₀ := FiniteTypeCommHopfAlgCat.identityComponent H
  let q := identityComponentBialgHom H
  let _ : Comodule k H₀ M := Comodule.Corestrict q.toCoalgHom
  let _ : Comodule k H₀ N := Comodule.Corestrict q.toCoalgHom
  have hq1 : q.toCoalgHom 1 = 1 := map_one q
  have hn₀ : n ∈ Comodule.fixedSubcomodule k H₀ N := by
    rw [Comodule.mem_fixedSubcomodule, Comodule.corestrict_coact_apply,
      Comodule.mem_fixedSubcomodule.mp hn]
    simp [hq1]
  obtain ⟨m₀, hm₀, hφm₀⟩ :=
    (Comodule.corestrictHom q.toCoalgHom φ).exists_fixed_preimage_of_isLinearlyReductive
      ((linearlyReductiveCommHopfAlgProperty_iff k H₀.obj).mp hH₀) hn₀ hrange
  -- `corestrictHom` acts on elements as the original `Comodule.Hom`.
  change φ m₀ = n at hφm₀
  refine ⟨m₀, hφm₀, ?_⟩
  have h := Comodule.mem_fixedSubcomodule.mp hm₀
  rw [Comodule.corestrict_coact_apply] at h
  have hq_lin : q.toCoalgHom.toLinearMap =
      (Ideal.Quotient.mkₐ k
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal).toLinearMap :=
    CommHopfAlgCat.mkQuotient_toLinearMap H.obj _
  rwa [hq_lin] at h

/-- **Linear reductivity from the identity component and component order.** Over an algebraically
closed field, if the identity component of a finite-type affine group is linearly reductive and the
number of connected components is nonzero in `k`, then the group is linearly reductive. -/
theorem linearlyReductiveCommHopfAlgProperty.of_identityComponent
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH₀ : linearlyReductiveCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.identityComponent H).obj)
    (hcard : (Nat.card (ConnectedComponents (PrimeSpectrum H)) : k) ≠ 0) :
    linearlyReductiveCommHopfAlgProperty k H.obj := by
  let _ : Fintype (ConnectedComponents (PrimeSpectrum H)) := Fintype.ofFinite _
  let g : ConnectedComponents (PrimeSpectrum H) → WithConv (H →ₐ[k] k) := fun C ↦
    Classical.choose (FiniteTypeCommHopfAlgCat.rationalComponentMap_surjective H C)
  have hg (C : ConnectedComponents (PrimeSpectrum H)) :
      FiniteTypeCommHopfAlgCat.rationalComponentMap H (g C) = C :=
    Classical.choose_spec (FiniteTypeCommHopfAlgCat.rationalComponentMap_surjective H C)
  rw [linearlyReductiveCommHopfAlgProperty_iff,
    Coalgebra.isLinearlyReductive_iff_forall_fixedMap_surjective_of_surjective]
  intro M N f hf n
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  let φ : Comodule.Hom k H M N := ConcreteCategory.hom f.hom
  obtain ⟨y₀, hy₀⟩ := hf n.1
  obtain ⟨m₀, hφm₀, hm₀_quot⟩ := exists_identityComponent_fixed_preimage hH₀ φ n.2 ⟨y₀, hy₀⟩
  let m : M := (Nat.card (ConnectedComponents (PrimeSpectrum H)) : k)⁻¹ •
    ∑ C : ConnectedComponents (PrimeSpectrum H),
      Comodule.basePointsRepresentation (H := H) M (g C) m₀
  have hm : m ∈ Comodule.fixedSubcomodule k H M :=
    average_mem_fixedSubcomodule_of_identityComponent_fixed H g hg hm₀_quot
  have hφm : φ m = n.1 := by
    have hnC (C : ConnectedComponents (PrimeSpectrum H)) :
        φ (Comodule.basePointsRepresentation (H := H) M (g C) m₀) = n.1 := by
      rw [φ.map_basePointsRepresentation, hφm₀]
      exact Comodule.basePointsRepresentation_eq_of_coact_eq_tmul_one n.1
        (Comodule.mem_fixedSubcomodule.mp n.2) (g C)
    calc
      φ m = (Nat.card (ConnectedComponents (PrimeSpectrum H)) : k)⁻¹ •
          ∑ C : ConnectedComponents (PrimeSpectrum H),
            φ (Comodule.basePointsRepresentation (H := H) M (g C) m₀) := by
        rw [← φ.coe_toLinearMap, map_smul, map_sum]
      _ = n.1 := by
        simp only [hnC, Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
          ← Nat.cast_smul_eq_nsmul k, inv_smul_smul₀ hcard]
  exact ⟨⟨m, hm⟩, Subtype.ext ((φ.fixedMap_apply ⟨m, hm⟩).trans hφm)⟩

end Converse

/-- Over an algebraically closed field `k`, a finite-type affine group is linearly reductive if and
only if its identity component is linearly reductive and the order of its component group is
nonzero in `k`. No reducedness hypothesis is needed. -/
theorem linearlyReductiveCommHopfAlgProperty_iff_identityComponent_of_isAlgClosed
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    linearlyReductiveCommHopfAlgProperty k H.obj ↔
      linearlyReductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.identityComponent H).obj ∧
        (Nat.card (ConnectedComponents (PrimeSpectrum H)) : k) ≠ 0 :=
  ⟨fun hH ↦ ⟨hH.identityComponent, hH.natCast_card_connectedComponents_ne_zero⟩,
    fun ⟨hH₀, hcard⟩ ↦ linearlyReductiveCommHopfAlgProperty.of_identityComponent hH₀ hcard⟩

end IsAlgClosed

section ArbitraryField

variable {k : Type u} [Field k]

/-- Over an arbitrary field `k`, a finite-type affine group is linearly reductive if and only if
its geometric identity component over `AlgebraicClosure k` is linearly reductive and the number of
geometric connected components is nonzero in `k`. -/
theorem linearlyReductiveCommHopfAlgProperty_iff_identityComponent
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    linearlyReductiveCommHopfAlgProperty k H.obj ↔
      linearlyReductiveCommHopfAlgProperty (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.identityComponent
          ((FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).obj H)).obj ∧
      (Nat.card (ConnectedComponents (PrimeSpectrum
        ((FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).obj H))) : k) ≠
          0 := by
  let Hbar := (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).obj H
  have hcast :
      (Nat.card (ConnectedComponents (PrimeSpectrum Hbar)) : AlgebraicClosure k) ≠ 0 ↔
        (Nat.card (ConnectedComponents (PrimeSpectrum Hbar)) : k) ≠ 0 := by
    rw [← map_natCast (algebraMap k (AlgebraicClosure k))]
    exact map_ne_zero_iff (algebraMap k (AlgebraicClosure k))
      (algebraMap k (AlgebraicClosure k)).injective
  exact (linearlyReductiveCommHopfAlgProperty_baseChange_iff (AlgebraicClosure k) H.obj).symm.trans
    ((linearlyReductiveCommHopfAlgProperty_iff_identityComponent_of_isAlgClosed Hbar).trans
      (and_congr_right' hcast))

/-- In characteristic zero, a finite-type affine group over a field `k` is linearly reductive if
and only if its geometric identity component over `AlgebraicClosure k` is linearly reductive. -/
theorem linearlyReductiveCommHopfAlgProperty_iff_identityComponent_of_charZero
    [CharZero k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    linearlyReductiveCommHopfAlgProperty k H.obj ↔
      linearlyReductiveCommHopfAlgProperty (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.identityComponent
          ((FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).obj H)).obj := by
  let Hbar := (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).obj H
  let _ : Finite (ConnectedComponents (PrimeSpectrum Hbar)) :=
    FiniteTypeCommHopfAlgCat.instFiniteConnectedComponents Hbar
  have : Nonempty (ConnectedComponents (PrimeSpectrum Hbar)) :=
    ⟨ConnectedComponents.mk (Bialgebra.augmentationPoint (AlgebraicClosure k) Hbar)⟩
  have hcard : (Nat.card (ConnectedComponents (PrimeSpectrum Hbar)) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  exact (linearlyReductiveCommHopfAlgProperty_iff_identityComponent H).trans (and_iff_left hcard)

/-- **Milne, *Algebraic Groups*, Corollary 22.43.** Over a field `k` of characteristic zero, an
affine group of finite type (not necessarily connected) is linearly reductive if and only if its
geometric identity component over `AlgebraicClosure k` is reductive. -/
theorem linearlyReductiveCommHopfAlgProperty_iff_reductive_identityComponent
    [CharZero k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    linearlyReductiveCommHopfAlgProperty k H.obj ↔
      reductiveCommHopfAlgProperty (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.identityComponent
          ((FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).obj H)) :=
  (linearlyReductiveCommHopfAlgProperty_iff_identityComponent_of_charZero H).trans
    (reductiveCommHopfAlgProperty_iff_linearlyReductive _
      (FiniteTypeCommHopfAlgCat.geometricallyConnected_identityComponent _)).symm

end ArbitraryField

end TauCeti

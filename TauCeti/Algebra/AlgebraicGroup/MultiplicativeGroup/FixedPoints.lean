/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.FixedPoints.Involution
public import TauCeti.Algebra.AlgebraicGroup.FixedPoints.Smooth
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
import TauCeti.Algebra.Polynomial.Laurent.Smooth

/-!
# Fixed points of inversion on the multiplicative group

Under `CommHopfAlgCat.antipodeAction` on `𝔾ₘ = Spec R[T;T⁻¹]` (`[Coalgebra.IsCocomm R R[T;T⁻¹]]`),
the fixed-point closed subgroup scheme is `μ₂`: its `A`-points are `{ u : Aˣ | u ^ 2 = 1 }`, and
for `IsUnit (2 : R)` it is smooth over `R` yet has disconnected spectrum when `[Nontrivial R]`.

## Main declarations

* `TauCeti.MultiplicativeGroup.smoothCommHopfAlgProperty_fixedPoints_antipodeAction`: smoothness of
  `(𝔾ₘ)^{ℤ/2}` over `R` when `IsUnit (2 : R)`.
* `TauCeti.MultiplicativeGroup.image_pointsMulEquiv_fixedPoints_antipodeAction`: on `A`-points,
  `(𝔾ₘ)^{ℤ/2}` cuts out `{ u : Aˣ | u ^ 2 = 1 }`.
* `TauCeti.MultiplicativeGroup.not_connectedSpace_primeSpectrum_fixedPoints_antipodeAction`,
  `TauCeti.MultiplicativeGroup.not_geometricallyConnected_fixedPoints_antipodeAction`: for
  `[Nontrivial R]` with `IsUnit (2 : R)` (and over any field `k` with `(2 : k) ≠ 0`), `(𝔾ₘ)^{ℤ/2}`
  has disconnected spectrum and is not geometrically connected.
-/

public section

open CategoryTheory WithConv _root_.CommHopfAlgCat TauCeti.CommHopfAlgCat
open scoped LaurentPolynomial

namespace TauCeti.MultiplicativeGroup

universe u w

section CommRing

variable {R : Type u} [CommRing R]

private noncomputable abbrev invFixed (R : Type u) [CommRing R] :=
  fixedPoints fun θ ↦ (antipodeAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) θ).asIso.hom

private noncomputable abbrev mkInvFixed (R : Type u) [CommRing R] :=
  mkFixedPoints fun θ ↦ (antipodeAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) θ).asIso.hom

/-- When `2` is invertible in `R`, `(𝔾ₘ)^{ℤ/2}` under inversion is smooth over `R`. -/
theorem smoothCommHopfAlgProperty_fixedPoints_antipodeAction (h2 : IsUnit (2 : R)) :
    smoothCommHopfAlgProperty R
      (fixedPoints fun θ ↦ (antipodeAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) θ).asIso.hom) := by
  have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 :=
    (Nat.card_congr (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2))).trans
      (Nat.card_zmod 2)
  exact smoothCommHopfAlgProperty_fixedPoints
    ((smoothCommHopfAlgProperty_iff _).mpr (inferInstanceAs (Algebra.Smooth R R[T;T⁻¹])))
    (antipodeAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹])) (by rwa [hcard, Nat.cast_two])

/-- Under `pointsMulEquiv`, inversion-fixed `A`-points of `𝔾ₘ` are `{ u : Aˣ | u ^ 2 = 1 }`. -/
theorem image_pointsMulEquiv_fixedPoints_antipodeAction (A : Type w) [CommRing A] [Algebra R A] :
    pointsMulEquiv (R := R) (A := A) ''
        Set.range (BialgHom.mapDomain (A := A)
          (mkFixedPoints fun θ ↦
            (antipodeAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) θ).asIso.hom).hom) =
      {u : Aˣ | u ^ 2 = 1} := by
  rw [range_mapDomain_mkFixedPoints_antipodeAction]; ext u
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  refine ⟨by rintro ⟨g, hg, rfl⟩; rw [sq, ← inv_eq_iff_mul_eq_one, ← map_inv, hg], fun hu ↦ ?_⟩
  refine ⟨(pointsMulEquiv (R := R) (A := A)).symm u, ?_,
    (pointsMulEquiv (R := R) (A := A)).apply_symm_apply u⟩
  apply (pointsMulEquiv (R := R) (A := A)).injective
  rw [map_inv, MulEquiv.apply_symm_apply, inv_eq_iff_mul_eq_one, ← sq]; exact hu

private theorem mkFixedPoints_antipodeAction_T_mul_self :
    ((mkInvFixed R).hom (LaurentPolynomial.T 1)) *
      ((mkInvFixed R).hom (LaurentPolynomial.T 1)) = 1 := by
  let f := fun θ ↦ (antipodeAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) θ).asIso.hom
  have hcomp := congrArg (fun m ↦ m.hom (LaurentPolynomial.T 1)) (comp_mkFixedPoints f (.ofAdd 1))
  dsimp only [f] at hcomp
  rw [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply, antipodeAction_ofAdd_one,
    antipodeEnd_hom, HopfAlgebra.antipodeBialgHom_apply, LaurentPolynomial.antipode_T] at hcomp
  nth_rw 1 [← hcomp]
  rw [← map_mul, ← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero, map_one]

private theorem exists_algHom_fixedPoints_antipodeAction_apply_T (u : Rˣ) (hu : u ^ 2 = 1) :
    ∃ φ : (invFixed R : Type u) →ₐ[R] R,
      φ ((mkInvFixed R).hom (LaurentPolynomial.T 1)) = (u : R) := by
  have hu' : u ∈ pointsMulEquiv (R := R) (A := R) ''
      Set.range (BialgHom.mapDomain (A := R) (mkInvFixed R).hom) := by
    rw [image_pointsMulEquiv_fixedPoints_antipodeAction]; exact Set.mem_ofPred_eq.mpr hu
  rcases hu' with ⟨_, ⟨p, rfl⟩, hpu⟩
  refine ⟨p.ofConv, ?_⟩
  have hp : BialgHom.mapDomain (A := R) _ p = (pointsMulEquiv (R := R) (A := R)).symm u :=
    (MulEquiv.eq_symm_apply _).mpr hpu
  simpa [BialgHom.mapDomain_apply_apply] using
    congrArg (fun m : WithConv (R[T;T⁻¹] →ₐ[R] R) ↦ m.ofConv (LaurentPolynomial.T 1)) hp

private theorem exists_nontrivial_idempotent_fixedPoints_antipodeAction [Nontrivial R]
    (h2 : IsUnit (2 : R)) :
    ∃ e : invFixed R, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  let t : invFixed R := (mkInvFixed R).hom (LaurentPolynomial.T 1)
  let c : R := ((h2.unit⁻¹ : Rˣ) : R)
  have hc2 : c * 2 = 1 := by rw [← h2.unit_spec, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rcases exists_algHom_fixedPoints_antipodeAction_apply_T (1 : Rˣ) (one_pow 2) with ⟨φ₁, hφ₁⟩
  rcases exists_algHom_fixedPoints_antipodeAction_apply_T (-1 : Rˣ) (by simp) with ⟨φ₂, hφ₂⟩
  refine ⟨c • (1 + t), isIdempotentElem_iff.mpr ?_, fun he0 ↦ ?_, fun he1 ↦ ?_⟩
  · have h1t : (1 + t) * (1 + t) = (2 : R) • (1 + t) := by
      rw [Algebra.smul_def, map_ofNat]
      linear_combination mkFixedPoints_antipodeAction_T_mul_self (R := R)
    rw [smul_mul_smul_comm, h1t, ← mul_smul, mul_assoc, hc2, mul_one]
  · have h1 := congrArg φ₁ he0
    rw [map_smul, map_add, map_one, map_zero, hφ₁, Units.val_one, smul_eq_mul,
      one_add_one_eq_two, hc2] at h1
    exact one_ne_zero h1
  · have h2' := congrArg φ₂ he1
    rw [map_smul, map_add, map_one, hφ₂, Units.val_neg, Units.val_one, add_neg_cancel,
      smul_zero] at h2'
    exact zero_ne_one h2'

/-- Over a nontrivial commutative ring `R` in which `2` is invertible, the fixed-point coordinate
ring of `𝔾ₘ` under inversion has disconnected prime spectrum. -/
theorem not_connectedSpace_primeSpectrum_fixedPoints_antipodeAction [Nontrivial R]
    (h2 : IsUnit (2 : R)) :
    ¬ ConnectedSpace (PrimeSpectrum
        (fixedPoints fun θ ↦
          (antipodeAction (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) θ).asIso.hom)) := by
  intro hconn
  obtain ⟨e, he, he0, he1⟩ := exists_nontrivial_idempotent_fixedPoints_antipodeAction h2
  exact he.eq_zero_or_eq_one_of_preconnectedSpace.elim he0 he1

end CommRing

/-- Over any field `k` with `(2 : k) ≠ 0`, `(𝔾ₘ)^{ℤ/2}` under inversion is not geometrically
connected. -/
theorem not_geometricallyConnected_fixedPoints_antipodeAction {k : Type u} [Field k]
    (h2 : (2 : k) ≠ 0) :
    ¬ geometricallyConnectedCommHopfAlgProperty k
        (fixedPoints fun θ ↦ (antipodeAction (_root_.CommHopfAlgCat.of k k[T;T⁻¹]) θ).asIso.hom) :=
  fun hconn ↦
    not_connectedSpace_primeSpectrum_fixedPoints_antipodeAction h2.isUnit hconn.connectedSpace

end TauCeti.MultiplicativeGroup

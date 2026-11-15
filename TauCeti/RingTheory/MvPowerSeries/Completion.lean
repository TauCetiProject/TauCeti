/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Completion
public import Mathlib.RingTheory.MvPowerSeries.Equiv

import TauCeti.RingTheory.AdicCompletion.Filtered
import TauCeti.RingTheory.FilteredAlgebra.Map
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Polynomial completion as multivariate power series

The completion of a multivariate polynomial ring `R[X_i : i ∈ σ]` along the ideal of variables is
the power series ring `R⟦X_i : i ∈ σ⟧`, for a commutative coefficient ring `R` and a finite set of
variables, so in particular for coefficient rings that are monoid algebras.

## Main definitions and results

* `TauCeti.principalCompletionEquiv`: the ring isomorphism from the completion of the polynomial
  ring along the ideal-power filtration of the ideal of variables to `MvPowerSeries σ R`.
* `TauCeti.projection_principalCompletionEquiv_symm`: at order `k`, the inverse is total-degree
  truncation at `k + 1` followed by the quotient map.
* `TauCeti.principalCompletionEquiv_toCompletion`: the equivalence restricts to the inclusion of
  polynomials into power series.
* `RingHom.principalCompletionMap`: a change of coefficients `R →+* S` extends to the completions;
  `TauCeti.principalCompletionEquiv_map` says that it corresponds to `MvPowerSeries.map`.

The equivalence is the composite of Mathlib's `MvPowerSeries.toAdicCompletionAlgEquiv` with the
comparison `AdicCompletion.algFiltrationCompletionEquiv` between adic and filtered completions.

Adapted from `yuma-mizuno-lean/Mei`, commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`,
`Mei/RingTheory/MvPowerSeries/Completion.lean` (Apache 2.0). The equivalence is stated for rings
rather than algebras over the polynomial ring.
-/

public section

namespace TauCeti

variable (σ R : Type*) [Finite σ] [CommRing R]

-- The ideal-power filtration of the ideal of variables of the polynomial ring.
local notation "𝔉" => Ideal.algFiltration (MvPolynomial.idealOfVars σ R)

/-- The completion of a polynomial ring along the ideal of variables is its power series ring. -/
noncomputable def principalCompletionEquiv : (𝔉).completion ≃+* MvPowerSeries σ R :=
  (AdicCompletion.algFiltrationCompletionEquiv (MvPolynomial.idealOfVars σ R)).symm.trans
    (MvPowerSeries.toAdicCompletionAlgEquiv σ R : MvPowerSeries σ R ≃+* _).symm

/-- At order `k`, the inverse equivalence is total-degree truncation at `k + 1` followed by the
quotient map. -/
@[simp]
theorem projection_principalCompletionEquiv_symm (k : ℕ) (p : MvPowerSeries σ R) :
    (𝔉).projection k ((principalCompletionEquiv σ R).symm p) =
      Ideal.Quotient.mk ((𝔉).ideal (k + 1)) (p.truncTotal (k + 1)) := by
  simp only [principalCompletionEquiv, RingEquiv.symm_trans_apply, RingEquiv.symm_symm,
    AdicCompletion.projection_algFiltrationCompletionEquiv, AlgEquiv.coe_toRingEquiv,
    MvPowerSeries.toAdicCompletionAlgEquiv_apply]
  rw [← AdicCompletion.factor_eval_eq_evalₐ _ _ (le_of_eq (Ideal.mul_top _))]
  simp only [AdicCompletion.eval_apply, MvPowerSeries.toAdicCompletion_apply_eq_mk_truncTotal]
  simp

/-- Completing a polynomial and then passing to power series is the usual inclusion. -/
@[simp]
theorem principalCompletionEquiv_toCompletion (p : MvPolynomial σ R) :
    principalCompletionEquiv σ R ((𝔉).toCompletion p) = p := by
  apply (principalCompletionEquiv σ R).symm.injective
  rw [RingEquiv.symm_apply_apply]
  simp only [principalCompletionEquiv, RingEquiv.symm_trans_apply, RingEquiv.symm_symm,
    AlgEquiv.coe_toRingEquiv, MvPowerSeries.toAdicCompletionAlgEquiv_apply,
    MvPowerSeries.toAdicCompletion_coe, AdicCompletion.algFiltrationCompletionEquiv_of]

/-- Truncating the power series associated to a completed polynomial recovers its finite-order
projection. -/
@[simp]
theorem mk_truncTotal_principalCompletionEquiv (k : ℕ) (x : (𝔉).completion) :
    Ideal.Quotient.mk ((𝔉).ideal (k + 1)) ((principalCompletionEquiv σ R x).truncTotal (k + 1)) =
      (𝔉).projection k x := by
  rw [← projection_principalCompletionEquiv_symm, RingEquiv.symm_apply_apply]

/-- A polynomial representing the order-`k` projection has the same coefficients as the associated
power series in every total degree at most `k`. -/
theorem coeff_principalCompletionEquiv_eq_of_projection_eq (x : (𝔉).completion) (k : ℕ)
    (p : MvPolynomial σ R)
    (hp : Ideal.Quotient.mk ((𝔉).ideal (k + 1)) p = (𝔉).projection k x)
    (n : σ →₀ ℕ) (hn : n.degree ≤ k) :
    MvPowerSeries.coeff n (principalCompletionEquiv σ R x) = p.coeff n := by
  rw [← mk_truncTotal_principalCompletionEquiv] at hp
  have hmem := Ideal.Quotient.eq.mp hp
  rw [Ideal.algFiltration_ideal, MvPolynomial.mem_pow_idealOfVars_iff'] at hmem
  have he := hmem n (Nat.lt_succ_of_le hn)
  symm
  simpa only [MvPolynomial.coeff_sub, MvPowerSeries.coeff_truncTotal _
    (Nat.lt_succ_of_le hn), sub_eq_zero] using he

end TauCeti

namespace RingHom

open TauCeti

variable {σ R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

local notation "𝔉[" R "]" => Ideal.algFiltration (MvPolynomial.idealOfVars σ R)

/-- A change of coefficients extends to the completions of the polynomial rings along the ideal of
variables, with the same cutoff at every order. -/
noncomputable def principalCompletionMap (φ : R →+* S) :
    (𝔉[R]).completion →+* (𝔉[S]).completion :=
  (𝔉[R]).mapCompletion (𝔉[S]) (MvPolynomial.map φ) _root_.id monotone_id fun k => by
    rw [Ideal.algFiltration_ideal, Ideal.algFiltration_ideal]
    exact MvPolynomial.pow_idealOfVars_le_comap_map φ (k + 1)

/-- At each order, the change of coefficients is computed on any polynomial representative. -/
theorem projection_principalCompletionMap (φ : R →+* S) (k : ℕ) (x : (𝔉[R]).completion)
    (p : MvPolynomial σ R)
    (hp : Ideal.Quotient.mk ((𝔉[R]).ideal (k + 1)) p = (𝔉[R]).projection k x) :
    (𝔉[S]).projection k (φ.principalCompletionMap x) =
      Ideal.Quotient.mk ((𝔉[S]).ideal (k + 1)) (MvPolynomial.map φ p) := by
  rw [principalCompletionMap, AlgFiltration.projection_mapCompletion]
  simp only [id_eq, ← hp, Ideal.quotientMap_mk]

/-- The change of coefficients commutes with the canonical inclusion of the polynomial ring. -/
@[simp]
theorem principalCompletionMap_toCompletion (φ : R →+* S) (p : MvPolynomial σ R) :
    φ.principalCompletionMap ((𝔉[R]).toCompletion p) = (𝔉[S]).toCompletion (MvPolynomial.map φ p) :=
  AlgFiltration.mapCompletion_toCompletion _ _ _ _ _ _ p

/-- The identity change of coefficients is the identity of the completion. -/
@[simp]
theorem principalCompletionMap_id :
    (RingHom.id R).principalCompletionMap (σ := σ) = RingHom.id (𝔉[R]).completion := by
  have hmap : MvPolynomial.map (RingHom.id R) = RingHom.id (MvPolynomial σ R) :=
    RingHom.ext MvPolynomial.map_id
  unfold principalCompletionMap
  simpa only [hmap] using (𝔉[R]).mapCompletion_id

/-- Changes of coefficients compose. -/
theorem principalCompletionMap_comp (φ : R →+* S) (ψ : S →+* T) :
    (ψ.comp φ).principalCompletionMap (σ := σ) =
      ψ.principalCompletionMap.comp φ.principalCompletionMap := by
  have hmap : MvPolynomial.map (σ := σ) (ψ.comp φ) =
      (MvPolynomial.map ψ).comp (MvPolynomial.map φ) :=
    RingHom.ext fun p => (MvPolynomial.map_map φ ψ p).symm
  unfold principalCompletionMap
  simp only [hmap]
  rw [← AlgFiltration.mapCompletion_comp]
  simp only [Function.id_comp]

end RingHom

namespace TauCeti

variable {σ R S : Type*} [Finite σ] [CommRing R] [CommRing S]

/-- The change of coefficients commutes with the power series description of the completion. -/
@[simp]
theorem principalCompletionEquiv_map (φ : R →+* S)
    (x : (Ideal.algFiltration (MvPolynomial.idealOfVars σ R)).completion) :
    principalCompletionEquiv σ S (φ.principalCompletionMap x) =
      MvPowerSeries.map φ (principalCompletionEquiv σ R x) := by
  obtain ⟨p, rfl⟩ := (principalCompletionEquiv σ R).symm.surjective x
  rw [RingEquiv.apply_symm_apply]
  apply (principalCompletionEquiv σ S).symm.injective
  rw [RingEquiv.symm_apply_apply]
  refine (Ideal.algFiltration (MvPolynomial.idealOfVars σ S)).completion_ext fun k => ?_
  rw [projection_principalCompletionEquiv_symm,
    RingHom.projection_principalCompletionMap φ k _ (p.truncTotal (k + 1))
      (projection_principalCompletionEquiv_symm σ R k p).symm]
  congr 1
  ext e
  by_cases he : e.degree < k + 1 <;>
    simp [MvPolynomial.coeff_map, MvPowerSeries.coeff_truncTotal_eq_ite, he]

end TauCeti

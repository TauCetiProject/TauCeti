/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
import TauCeti.LinearAlgebra.Basis.Semilinear

/-!
# The determinant of a commuting scalar action

Let `V` be a module over a commutative ring `E` with a commuting action of a semiring `k`. Each
`a ∈ k` acts on `V` by an `E`-linear map, so `a ↦ det_E(a | V)` is a monoid homomorphism
`k →* E`. This is the shape of the reflex norm of a CM type, `N_{k,Φ}(a) = det_E(a | V)`.

## Main definitions

* `TauCeti.smulDet E k V`: the monoid homomorphism `a ↦ det_E(a | V)`.

## Main results

* `TauCeti.smulDet_congr`: it depends only on the isomorphism class of `V`.
* `TauCeti.smulDet_eq_symm_apply_of_map_smul`: a `σ`-semilinear isomorphism `V' ≃ V` changes it by
  `σ⁻¹`.
* `TauCeti.smulDet_eq_pow_of_smul_eq`: if `a` acts on a free module as `c ∈ E`, then
  `det_E(a | V) = c ^ dim_E V`.
-/

public section

namespace TauCeti

variable (E : Type*) [CommRing E] (k : Type*) [Semiring k] (V : Type*) [AddCommGroup V]
  [Module E V] [Module k V] [SMulCommClass E k V]

/-- **The determinant of the scalar action.** For an `E`-module `V` with a commuting action of a
semiring `k`, the map `a ↦ det_E(a | V)`. -/
noncomputable def smulDet : k →* E :=
  haveI : SMulCommClass k E V := .symm E k V
  LinearMap.det.comp (DistribMulAction.toModuleEnd E V)

theorem smulDet_apply (a : k) :
    haveI : SMulCommClass k E V := .symm E k V
    smulDet E k V a = LinearMap.det (DistribSMul.toLinearMap E V a) :=
  (rfl)

variable {E k V}

/-- If `a ∈ k` acts on a free `E`-module `V` as `c ∈ E`, then `det_E(a | V) = c ^ dim_E V`. -/
theorem smulDet_eq_pow_of_smul_eq [Module.Free E V] {a : k} {c : E}
    (h : ∀ v : V, a • v = c • v) :
    smulDet E k V a = c ^ Module.finrank E V := by
  have : SMulCommClass k E V := .symm E k V
  have hc : DistribSMul.toLinearMap E V a = c • LinearMap.id := LinearMap.ext h
  rw [smulDet_apply, hc, LinearMap.det_smul, LinearMap.det_id, mul_one]

/-- **Independence of the module.** Isomorphic `E`-modules with commuting `k`-actions have the same
determinant of the scalar action: a `k`-linear isomorphism `V ≃ W` intertwining the actions of `E`
gives `det_E(a | V) = det_E(a | W)`. -/
theorem smulDet_congr {W : Type*} [AddCommGroup W] [Module E W] [Module k W]
    [SMulCommClass E k W] (e : V ≃ₗ[k] W) (he : ∀ (c : E) (v : V), e (c • v) = c • e v) :
    smulDet E k V = smulDet E k W := by
  have : SMulCommClass k E V := .symm E k V
  have : SMulCommClass k E W := .symm E k W
  -- `e` is also `E`-linear.
  let eE : V ≃ₗ[E] W := { e.toAddEquiv with map_smul' := he }
  ext a
  rw [smulDet_apply, smulDet_apply, ← LinearMap.det_conj _ eE]
  congr 1
  ext w
  simp [eE, e.map_smul]

/-- **A semilinear twist changes the determinant of the scalar action by `σ⁻¹`.** If a
`k`-linear isomorphism `e : V' ≃ V` satisfies `e (c • v) = σ c • e v` for a ring automorphism
`σ` of `E`, then `det_E(a | V') = σ⁻¹(det_E(a | V))` for every `a ∈ k`. -/
theorem smulDet_eq_symm_apply_of_map_smul {V' : Type*} [AddCommGroup V'] [Module E V']
    [Module k V'] [SMulCommClass E k V'] (σ : E ≃+* E) (e : V' ≃ₗ[k] V)
    (he : ∀ (c : E) (v : V'), e (c • v) = σ c • e v) (a : k) :
    smulDet E k V' a = σ.symm (smulDet E k V a) := by
  have : SMulCommClass k E V := .symm E k V
  have : SMulCommClass k E V' := .symm E k V'
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  -- `e⁻¹` is `σ⁻¹`-semilinear over `E`.
  let eE : V ≃ₛₗ[(σ.symm : E →+* E)] V' :=
    { e.symm.toAddEquiv with
      map_smul' c v := e.injective (by simp [he]) }
  -- `eE` is `k`-linear, since `e` is.
  have hk (a : k) (v : V) : eE (a • v) = a • eE v := e.symm.map_smul a v
  rw [smulDet_apply, smulDet_apply]
  by_cases H : ∃ s : Finset V, Nonempty (Module.Basis s E V)
  · classical
    obtain ⟨s, ⟨b⟩⟩ := H
    let b' := b.mapₛₗ eE
    have hb' (j : s) : b' j = eE (b j) := b.mapₛₗ_apply eE j
    -- `eE` applies `σ⁻¹` to the coordinates in `b` and reads the result in `b'`.
    have hb (v : V) (i : s) : b'.repr (eE v) i = σ.symm (b.repr v i) := by
      have h : eE v = b.semilinearMap σ.symm b' v :=
        LinearMap.congr_fun (b.ext (f₁ := (eE : V →ₛₗ[(σ.symm : E →+* E)] V')) fun j ↦ by
          simp [hb']) v
      simp [h]
    rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b', RingEquiv.map_det]
    congr 1
    ext i j
    simp [LinearMap.toMatrix_apply, hb', ← hk, hb]
  · have H' : ¬∃ s : Finset V', Nonempty (Module.Basis s E V') := fun ⟨s, ⟨b⟩⟩ ↦ by
      classical
      exact H ⟨_, ⟨(b.mapₛₗ eE.symm).reindexFinsetRange⟩⟩
    classical
    simp [LinearMap.coe_det, H, H']

end TauCeti

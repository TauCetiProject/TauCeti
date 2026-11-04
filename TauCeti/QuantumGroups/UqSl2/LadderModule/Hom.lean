/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.LadderModule.Basic
public import TauCeti.RingTheory.Semisimple.Schur

/-!
# Intertwiners and Schur scalars between signed ladder modules

At a generic quantum parameter `q`, the signed ladder modules `L_m^ε` of `U_q(sl₂)` are pairwise
non-isomorphic simple modules whose endomorphism algebras are canonically `ℂ`. In calculations with
parameterized families of ladder modules (such as iterated Clebsch–Gordan channels), the source and
target weights or signs are often equal only propositionally rather than definitionally. This file
provides the parameter-transport isomorphism `LadderModule.congr` and the Schur scalar
`LadderModule.homScalar` for arbitrary `UqSl2 q`-linear maps `L_m^ε →ₗ[UqSl2 q] L_n^δ`.

The scalar `homScalar φ` is defined for all parameters as the `v₀`-coordinate of `φ v₀`. At a
generic parameter:

* `hom_eq_zero_of_ne`: every intertwiner `L_m^ε →ₗ[UqSl2 q] L_n^δ` with `m ≠ n` or `ε ≠ δ` is zero;
* `apply_vec_eq_homScalar_smul`: for every `φ : L_m^ε →ₗ[UqSl2 q] L_n^δ` and every integer `k`,
  `φ v_k = homScalar φ • v_k` unconditionally;
* `homScalar_injective`: `homScalar` is injective for every pair of ladder modules, and when
  `m = n` and `ε = δ` every intertwiner is `homScalar φ • (congr hm hε).toLinearMap`;
* `homScalar_comp`: `homScalar (ψ ∘ₗ φ) = homScalar ψ * homScalar φ` for any composable pair of
  intertwiners between signed ladder modules.

## Main definitions

* `TauCeti.UqSl2.LadderModule.congr`: the `UqSl2 q`-linear isomorphism `L_m^ε ≃ₗ[UqSl2 q] L_n^δ`
  attached to `m = n` and `ε = δ`, sending `v_k` to `v_k`.
* `TauCeti.UqSl2.LadderModule.homScalar`: the `ℂ`-linear Schur scalar functional
  `(L_m^ε →ₗ[UqSl2 q] L_n^δ) →ₗ[ℂ] ℂ`.

## Main results

* `TauCeti.UqSl2.LadderModule.hom_eq_zero_of_ne`: Schur vanishing for distinct weights or signs.
* `TauCeti.UqSl2.LadderModule.apply_vec_eq_homScalar_smul`: every intertwiner acts on the ladder
  vectors `v_k` (`k : ℤ`) by `homScalar φ`.
* `TauCeti.UqSl2.LadderModule.eq_homScalar_smul_congr`: when `m = n` and `ε = δ`, every intertwiner
  is `homScalar φ` times `congr`.
* `TauCeti.UqSl2.LadderModule.homScalar_injective`: intertwiners between ladder modules are
  determined by their Schur scalar.
* `TauCeti.UqSl2.LadderModule.homScalar_comp`: functoriality of `homScalar` under composition.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Section VI.3.
-/

public noncomputable section

open Module

namespace TauCeti.UqSl2.LadderModule

variable {q : ℂ} {m n p : ℕ} {ε δ ζ : ℤˣ}

/-! ### Parameter congruence of ladder modules -/

/-- Underlying complex-linear equivalence `L_m^ε ≃ₗ[ℂ] L_n^δ` induced by `m = n` and `ε = δ`. -/
private def congrLinearEquiv (hm : m = n) (_hε : ε = δ) :
    LadderModule q m ε ≃ₗ[ℂ] LadderModule q n δ :=
  (basis q m ε).equiv (basis q n δ) (finCongr (congrArg (· + 1) hm))

private theorem congrLinearEquiv_vec (hm : m = n) (hε : ε = δ) (j : ℤ) :
    congrLinearEquiv (q := q) hm hε (vec q m ε j) = vec q n δ j := by
  subst hm hε
  by_cases hj : 0 ≤ j ∧ j ≤ m
  · obtain ⟨i, rfl⟩ : ∃ i : Fin (m + 1), (i : ℤ) = j := ⟨⟨j.toNat, by omega⟩, by simp; omega⟩
    simp [congrLinearEquiv, vec_coe]
  · rw [vec_eq_zero_iff.mpr (by omega), map_zero]

private theorem congrLinearEquiv_refl :
    congrLinearEquiv (q := q) (rfl : m = m) (rfl : ε = ε) =
      LinearEquiv.refl ℂ (LadderModule q m ε) := by
  apply LinearEquiv.toLinearMap_injective
  exact (basis q m ε).ext fun i => by simp [congrLinearEquiv]

section Module

variable [Fact (q ≠ 0)]

/-- Forward `UqSl2 q`-linear map of `LadderModule.congr`. -/
private def congrHom (hm : m = n) (hε : ε = δ) :
    LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ :=
  homOfVec (congrLinearEquiv hm hε).toLinearMap
    (fun j _ => by subst hm hε; simp [congrLinearEquiv_vec])
    (fun j _ => by subst hm hε; simp [congrLinearEquiv_vec])
    (fun j _ => by subst hm hε; simp [congrLinearEquiv_vec])

@[simp]
private theorem congrHom_apply (hm : m = n) (hε : ε = δ) (x : LadderModule q m ε) :
    congrHom hm hε x = congrLinearEquiv hm hε x := by
  simp [congrHom]

/-- Equal highest weights and equal signs induce a canonical `UqSl2 q`-linear isomorphism
`L_m^ε ≃ₗ[UqSl2 q] L_n^δ` preserving every ladder vector `v_j`. -/
def congr (hm : m = n) (hε : ε = δ) :
    LadderModule q m ε ≃ₗ[UqSl2 q] LadderModule q n δ :=
  LinearEquiv.ofLinearMap (congrHom hm hε) (congrHom hm.symm hε.symm)
    (LinearMap.ext fun x => by subst hm hε; simp [congrLinearEquiv_refl])
    (LinearMap.ext fun x => by subst hm hε; simp [congrLinearEquiv_refl])

/-- `congr` preserves the integer-indexed ladder vectors `v_j`. -/
@[simp]
theorem congr_vec (hm : m = n) (hε : ε = δ) (j : ℤ) :
    congr (q := q) hm hε (vec q m ε j) = vec q n δ j := by
  simp [congr, congrLinearEquiv_vec]

/-- `congr` reindexes the ladder basis along `finCongr`. -/
@[simp]
theorem congr_basis (hm : m = n) (hε : ε = δ) (i : Fin (m + 1)) :
    congr (q := q) hm hε (basis q m ε i) = basis q n δ (finCongr (congrArg (· + 1) hm) i) := by
  simp [congr, congrLinearEquiv]

/-- Inverting `congr` reverses the parameter equalities. -/
@[simp]
theorem congr_symm (hm : m = n) (hε : ε = δ) :
    (congr (q := q) hm hε).symm = congr hm.symm hε.symm :=
  (rfl)

/-- `congr` with reflexive equalities is the identity equivalence. -/
@[simp]
theorem congr_refl :
    congr (q := q) (rfl : m = m) (rfl : ε = ε) =
      LinearEquiv.refl (UqSl2 q) (LadderModule q m ε) := by
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext fun x => ?_
  simp [congr, congrLinearEquiv_refl]

/-- `congr` composes along transitivity of parameter equalities. -/
theorem congr_trans (hm₁ : m = n) (hε₁ : ε = δ) (hm₂ : n = p) (hε₂ : δ = ζ) :
    (congr (q := q) hm₁ hε₁).trans (congr hm₂ hε₂) =
      congr (hm₁.trans hm₂) (hε₁.trans hε₂) := by
  subst hm₁ hε₁ hm₂ hε₂
  simp

/-! ### Schur vanishing and the Schur scalar -/

/-- At a generic parameter, every `UqSl2 q`-linear map between ladder modules with different
highest weights or different signs is zero. -/
theorem hom_eq_zero_of_ne (hq : IsGenericQuantumParameter q) (h : m ≠ n ∨ ε ≠ δ)
    (φ : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) : φ = 0 := by
  have := isSimpleModule (m := m) (ε := ε) hq
  have := isSimpleModule (m := n) (ε := δ) hq
  apply hom_eq_zero_of_isEmpty_linearEquiv
  rw [← not_nonempty_iff, nonempty_linearEquiv_iff hq]
  tauto

/-- At a generic parameter, every `UqSl2 q`-linear map between ladder modules of different highest
weights is zero. -/
theorem hom_eq_zero_of_ne_left (hq : IsGenericQuantumParameter q) (hm : m ≠ n)
    (φ : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) : φ = 0 :=
  hom_eq_zero_of_ne hq (.inl hm) φ

/-- At a generic parameter, every `UqSl2 q`-linear map between ladder modules of different signs
is zero. -/
theorem hom_eq_zero_of_ne_right (hq : IsGenericQuantumParameter q) (hε : ε ≠ δ)
    (φ : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) : φ = 0 :=
  hom_eq_zero_of_ne hq (.inr hε) φ

/-- The `ℂ`-linear Schur scalar functional `(L_m^ε →ₗ[UqSl2 q] L_n^δ) →ₗ[ℂ] ℂ`, defined as the
`v₀`-coordinate of `φ v₀` in the ladder basis of `L_n^δ`.

At a generic parameter, `φ v_k = homScalar φ • v_k` for every integer `k`
(`apply_vec_eq_homScalar_smul`); in particular `homScalar φ = 0` whenever `(m, ε) ≠ (n, δ)`. -/
def homScalar : (LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) →ₗ[ℂ] ℂ where
  toFun φ := (basis q n δ).repr (φ (vec q m ε 0)) 0
  map_add' φ ψ := by simp
  map_smul' c φ := by simp

/-- `homScalar φ` extracts the `v₀`-coordinate of `φ v₀` in the ladder basis. -/
theorem homScalar_apply (φ : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) :
    homScalar φ = (basis q n δ).repr (φ (vec q m ε 0)) 0 :=
  (rfl)

/-- The identity intertwiner has Schur scalar `1`. -/
@[simp]
theorem homScalar_id :
    homScalar (LinearMap.id : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q m ε) = 1 := by
  simp [homScalar_apply]

/-- The parameter-transport isomorphism `congr` has Schur scalar `1`. -/
@[simp]
theorem homScalar_congr (hm : m = n) (hε : ε = δ) :
    homScalar (congr (q := q) hm hε).toLinearMap = 1 := by
  simp [homScalar_apply]

/-- On endomorphisms of `L_m^ε`, `homScalar` agrees with the canonical Schur algebra equivalence
`endAlgEquivSelfOfIsSimpleModule`. -/
theorem homScalar_end (hq : IsGenericQuantumParameter q)
    (φ : Module.End (UqSl2 q) (LadderModule q m ε)) :
    homScalar φ =
      have := isSimpleModule (m := m) (ε := ε) hq
      endAlgEquivSelfOfIsSimpleModule (k := ℂ) φ := by
  have := isSimpleModule (m := m) (ε := ε) hq
  rw [homScalar_apply, ← endAlgEquivSelfOfIsSimpleModule_smul (k := ℂ) φ (vec q m ε 0),
    map_smul, Finsupp.smul_apply, basis_repr_vec]
  simp

/-- At a generic parameter, every `UqSl2 q`-endomorphism of `L_m^ε` acts as scalar multiplication
by its `homScalar`. -/
theorem end_apply_eq_homScalar_smul (hq : IsGenericQuantumParameter q)
    (φ : Module.End (UqSl2 q) (LadderModule q m ε)) (x : LadderModule q m ε) :
    φ x = homScalar φ • x := by
  have := isSimpleModule (m := m) (ε := ε) hq
  rw [homScalar_end hq φ, endAlgEquivSelfOfIsSimpleModule_smul]

/-- At a generic parameter, when `m = n` and `ε = δ`, every `UqSl2 q`-linear map
`L_m^ε →ₗ[UqSl2 q] L_n^δ` acts as `homScalar φ` composed with `congr hm hε`. -/
theorem apply_eq_homScalar_smul_congr (hq : IsGenericQuantumParameter q)
    (hm : m = n) (hε : ε = δ) (φ : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ)
    (x : LadderModule q m ε) :
    φ x = homScalar φ • congr hm hε x := by
  subst hm hε
  simpa using end_apply_eq_homScalar_smul hq φ x

/-- At a generic parameter, when `m = n` and `ε = δ`, every `UqSl2 q`-linear map
`L_m^ε →ₗ[UqSl2 q] L_n^δ` equals `homScalar φ • (congr hm hε).toLinearMap`. -/
theorem eq_homScalar_smul_congr (hq : IsGenericQuantumParameter q)
    (hm : m = n) (hε : ε = δ) (φ : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) :
    φ = homScalar φ • (congr hm hε).toLinearMap :=
  LinearMap.ext (apply_eq_homScalar_smul_congr hq hm hε φ)

/-- At a generic parameter, the Schur scalar vanishes whenever the weights or signs differ. -/
theorem homScalar_eq_zero_of_ne (hq : IsGenericQuantumParameter q) (h : m ≠ n ∨ ε ≠ δ)
    (φ : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) :
    homScalar φ = 0 := by
  rw [hom_eq_zero_of_ne hq h φ, map_zero]

/-- At a generic parameter, every `UqSl2 q`-linear map `φ : L_m^ε →ₗ[UqSl2 q] L_n^δ` acts on the
ladder vectors by `φ v_k = homScalar φ • v_k` for every integer `k`, whether or not `(m, ε)` and
`(n, δ)` agree. -/
theorem apply_vec_eq_homScalar_smul (hq : IsGenericQuantumParameter q)
    (φ : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) (k : ℤ) :
    φ (vec q m ε k) = homScalar φ • vec q n δ k := by
  by_cases h : m = n ∧ ε = δ
  · rw [apply_eq_homScalar_smul_congr hq h.1 h.2, congr_vec]
  · have hne : m ≠ n ∨ ε ≠ δ := by tauto
    rw [hom_eq_zero_of_ne hq hne φ, map_zero, LinearMap.zero_apply, zero_smul]

/-- At a generic parameter, `UqSl2 q`-linear maps between signed ladder modules are determined by
their Schur scalar. -/
theorem homScalar_injective (hq : IsGenericQuantumParameter q) :
    Function.Injective (homScalar (q := q) (m := m) (ε := ε) (n := n) (δ := δ)) := by
  intro φ ψ h
  refine hom_ext hq ?_
  rw [apply_vec_eq_homScalar_smul hq, apply_vec_eq_homScalar_smul hq, h]

/-- At a generic parameter, an intertwiner between signed ladder modules vanishes iff its Schur
scalar vanishes. -/
@[simp]
theorem homScalar_eq_zero_iff (hq : IsGenericQuantumParameter q)
    {φ : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ} :
    homScalar φ = 0 ↔ φ = 0 :=
  map_eq_zero_iff homScalar (homScalar_injective hq)

/-- If `φ v₀ = c • v₀`, then `homScalar φ = c`. -/
theorem homScalar_eq_of_apply_vec_zero
    {φ : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ} {c : ℂ}
    (h : φ (vec q m ε 0) = c • vec q n δ 0) :
    homScalar φ = c := by
  simp [homScalar_apply, h]

/-- At a generic parameter, `homScalar` sends composition of intertwiners to multiplication of
scalars, unconditionally for any three signed ladder modules. -/
@[simp]
theorem homScalar_comp (hq : IsGenericQuantumParameter q)
    (ψ : LadderModule q n δ →ₗ[UqSl2 q] LadderModule q p ζ)
    (φ : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) :
    homScalar (ψ.comp φ) = homScalar ψ * homScalar φ := by
  apply homScalar_eq_of_apply_vec_zero
  rw [LinearMap.comp_apply, apply_vec_eq_homScalar_smul hq φ,
    LinearMapClass.map_smul_of_tower, apply_vec_eq_homScalar_smul hq ψ, smul_smul, mul_comm]

end Module

end TauCeti.UqSl2.LadderModule

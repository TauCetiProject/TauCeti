/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem

import TauCeti.LinearAlgebra.RootSystem.PairingInvariance

/-!
# Pairing invariance between an integral root datum and a Killing root system

For a finite-dimensional characteristic-zero Killing Lie algebra `L` with splitting Cartan
subalgebra `H`, this file transports root relations from `P : RootPairing ι ℤ X Y` along a bijection
`e : ι ≃ H.root` matching integer Cartan pairings to weights, coroots, and root spaces on `H`.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule Module Set

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
  {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {P : RootPairing ι ℤ X Y}
  (e : ι ≃ H.root) (he : ∀ i j, (rootSystem H).pairingIn ℤ (e i) (e j) = P.pairing i j)

include he

/-- A Cartan-matching `e : ι ≃ H.root` identifies coroot evaluations of weights with `P.pairing`. -/
theorem coe_root_coroot_eq_pairing (i j : ι) :
    (e i : Weight K H L) (coroot (e j : Weight K H L)) = (P.pairing i j : K) := by
  rw [← rootSystem_pairing_apply, ← (rootSystem H).algebraMap_pairingIn ℤ, he, eq_intCast]

/-- A Cartan-matching `e : ι ≃ H.root` intertwines self-reflection with negation of roots. -/
theorem map_reflectionPerm_self_eq_neg (a : ι) : e (P.reflectionPerm a a) = -e a :=
  let _ : Finite ι := Finite.of_equiv _ e.symm
  (RootPairing.map_reflectionPerm_of_pairingIn e
    (RootPairing.pairingIn_eq_of_pairingIn_eq_pairing he) a a).trans
    (rootSystem_reflectionPerm_self_eq_neg (e a))

/-- A Cartan-matching `e : ι ≃ H.root` carries root sums in `P` to weight sums on `H`. -/
theorem coe_weight_eq_add_of_root_eq_add {i j k : ι} (hk : P.root k = P.root i + P.root j) :
    ((e k : Weight K H L) : H → K) = ((e i : Weight K H L) : H → K) + (e j : Weight K H L) := by
  let _ : Finite ι := Finite.of_equiv _ e.symm
  have hkH := (RootPairing.root_eq_add_iff_of_pairingIn e
    (RootPairing.pairingIn_eq_of_pairingIn_eq_pairing he) k i j).mpr hk
  ext z; simpa [rootSystem_root_apply, Weight.toLinear_apply] using DFunLike.congr_fun hkH z

/-- A Cartan-matching `e : ι ≃ H.root` carries opposite roots in `P` to opposite weights on `H`. -/
theorem weight_eq_neg_of_root_add_eq_zero {i j : ι} (h0 : P.root i + P.root j = 0) :
    (e j : Weight K H L) = -(e i : Weight K H L) := by
  let _ : Finite ι := Finite.of_equiv _ e.symm
  have hH := (RootPairing.root_add_eq_zero_iff_of_pairingIn e
    (RootPairing.pairingIn_eq_of_pairingIn_eq_pairing he) i j).mpr h0
  ext z; simp only [Weight.coe_neg, Pi.neg_apply]
  exact eq_neg_of_add_eq_zero_right
    (by simpa [rootSystem_root_apply, Weight.toLinear_apply] using DFunLike.congr_fun hH z)

/-- Non-root nonzero sums in `P` correspond to trivial root spaces on `H`. -/
theorem rootSpace_add_eq_bot_of_notMem {i j : ι}
    (hnot : P.root i + P.root j ∉ range P.root) (hne : P.root i + P.root j ≠ 0) :
    rootSpace H (((e i : Weight K H L) : H → K) + (e j : Weight K H L)) = ⊥ := by
  let _ : Finite ι := Finite.of_equiv _ e.symm
  by_contra hbot
  let heIn := RootPairing.pairingIn_eq_of_pairingIn_eq_pairing he
  let χ : Weight K H L := ⟨((e i : Weight K H L) : H → K) + (e j : Weight K H L), hbot⟩
  have hχ : χ.IsNonZero := fun h0 ↦ hne <|
    (RootPairing.root_add_eq_zero_iff_of_pairingIn e heIn i j).mp <| by
      ext z; simpa [χ, rootSystem_root_apply, Weight.toLinear_apply] using congrFun h0 z
  exact hnot <| (RootPairing.root_add_mem_range_iff_of_pairingIn e heIn i j).mp
    ⟨⟨χ, by simpa [LieSubalgebra.root] using hχ⟩,
      by ext z; simp [χ, rootSystem_root_apply, Weight.toLinear_apply]⟩

/-- Any `γ : Y →ₗ[ℤ] H` intertwining root evaluations along `e` maps `P.coroot` to `coroot`. -/
theorem map_coroot_eq_rootSystem_coroot (γ : Y →ₗ[ℤ] H)
    (hγ_pair : ∀ y i, (e i : Weight K H L) (γ y) = (P.toLinearMap (P.root i) y : K)) (i : ι) :
    γ (P.coroot i) = (rootSystem H).coroot (e i) := by
  have hsub (α : Dual K H) : α (γ (P.coroot i) - (rootSystem H).coroot (e i)) = 0 := by
    have hmem : α ∈ Submodule.span K (range (rootSystem H).root) := by
      simp [RootPairing.IsRootSystem.span_root_eq_top]
    induction hmem using Submodule.span_induction with
    | mem _ hf =>
      obtain ⟨r, rfl⟩ := hf; obtain ⟨j, rfl⟩ := e.surjective r
      rw [map_sub, sub_eq_zero, rootSystem_root_apply, Weight.toLinear_apply,
        Weight.toLinear_apply, hγ_pair, rootSystem_coroot_apply, P.root_coroot_eq_pairing,
        coe_root_coroot_eq_pairing e he]
    | zero => simp
    | add _ _ _ _ hf hg => simp only [LinearMap.add_apply, hf, hg, add_zero]
    | smul _ _ _ hf => simp only [LinearMap.smul_apply, hf, smul_zero]
  exact sub_eq_zero.mp <| (rootSystem H).toPerfPair.flip.bijective.injective <| by
    ext α; simpa using hsub α

end TauCeti

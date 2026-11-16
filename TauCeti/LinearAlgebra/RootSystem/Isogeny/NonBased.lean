/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Based
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A

/-!
# The non-based `A₁` reflection isogeny

On `typeASimplyConnectedRootDatum 1`, `a1ReflectionIsogeny c` composes the simple reflection with
`smulId _ c`: its weight and coweight maps are `-((c : ℕ) • LinearMap.id)`, its exponent is `c`,
and its square is `smulId _ (c ^ 2)` (mirroring `(Int(n) ∘ Frob_p)^2 = Frob_{p^2}` on `SL₂`).
Every `Aut`-conjugate equals itself (`conj_ofEquiv_a1ReflectionIsogeny`) and, relative to every
base `b`, is neither based (`not_isBased_a1ReflectionIsogeny`, `a1ReflectionIsogeny_ne_of_isBased`,
`not_isBased_conj_ofEquiv_a1ReflectionIsogeny`, `conj_ofEquiv_a1ReflectionIsogeny_ne_of_isBased`)
nor a positive scaling (`a1ReflectionIsogeny_ne_smulId`,
`conj_ofEquiv_a1ReflectionIsogeny_ne_smulId`).

## References

* R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, Mem. Amer. Math. Soc. **80** (1968),
  §11.
* Schémas en groupes (SGA 3), Exposé XXI, §6.8.
* G. Malle and D. Testerman, *Linear Algebraic Groups and Finite Groups of Lie Type*, Cambridge
  Univ. Press (2011), §21.1 and Example 22.3.
-/

public section

namespace TauCeti.DynkinType

open RootPairingIsogeny (ofEquiv smulId)

/-- **The reflection-times-scaling endo-isogeny `s₀ ∘ (c • id)`** of
`typeASimplyConnectedRootDatum 1`. -/
def a1ReflectionIsogeny (c : ℕ+) :
    RootPairingIsogeny (typeASimplyConnectedRootDatum 1) (typeASimplyConnectedRootDatum 1) :=
  ofEquiv (RootPairing.Equiv.reflection (typeASimplyConnectedRootDatum 1) (typeASimpleIndex 1 0)) *
    smulId (typeASimplyConnectedRootDatum 1) c

/-- Unfolding formula for `a1ReflectionIsogeny c`. -/
theorem a1ReflectionIsogeny_def (c : ℕ+) : a1ReflectionIsogeny c =
    ofEquiv (RootPairing.Equiv.reflection (typeASimplyConnectedRootDatum 1)
      (typeASimpleIndex 1 0)) * smulId (typeASimplyConnectedRootDatum 1) c := (rfl)

/-- The weight map of `a1ReflectionIsogeny c` is `-((c : ℕ) • LinearMap.id)`. -/
@[simp] theorem a1ReflectionIsogeny_weightMap (c : ℕ+) :
    (a1ReflectionIsogeny c).weightMap = -((c : ℕ) • LinearMap.id) := by
  rw [a1ReflectionIsogeny_def, RootPairingIsogeny.weightMap_mul,
    RootPairingIsogeny.ofEquiv_weightMap, reflection_typeASimplyConnectedRootDatum_one_weightMap,
    RootPairingIsogeny.smulId_weightMap]; ext x; simp

/-- The coweight map of `a1ReflectionIsogeny c` is `-((c : ℕ) • LinearMap.id)`. -/
@[simp] theorem a1ReflectionIsogeny_coweightMap (c : ℕ+) :
    (a1ReflectionIsogeny c).coweightMap = -((c : ℕ) • LinearMap.id) := by
  rw [a1ReflectionIsogeny_def, RootPairingIsogeny.coweightMap_mul,
    RootPairingIsogeny.ofEquiv_coweightMap,
    reflection_typeASimplyConnectedRootDatum_one_coweightMap,
    RootPairingIsogeny.smulId_coweightMap]; ext y; simp

/-- The index bijection of `a1ReflectionIsogeny c` is the simple reflection at node `0`. -/
@[simp] theorem a1ReflectionIsogeny_indexEquiv (c : ℕ+) : (a1ReflectionIsogeny c).indexEquiv =
    (typeASimplyConnectedRootDatum 1).reflectionPerm (typeASimpleIndex 1 0) := by
  rw [a1ReflectionIsogeny_def, RootPairingIsogeny.indexEquiv_mul,
    RootPairingIsogeny.smulId_indexEquiv, Equiv.refl_trans, RootPairingIsogeny.ofEquiv_indexEquiv,
    RootPairing.Equiv.reflection_indexEquiv]

/-- Every root-rescaling exponent of `a1ReflectionIsogeny c` equals `c`. -/
@[simp] theorem a1ReflectionIsogeny_exponent (c : ℕ+) (i : Fin (1 * (1 + 1))) :
    (a1ReflectionIsogeny c).exponent i = c := by
  rw [a1ReflectionIsogeny_def, RootPairingIsogeny.exponent_mul,
    RootPairingIsogeny.smulId_exponent, RootPairingIsogeny.ofEquiv_exponent, mul_one]

/-- **Composing `a1ReflectionIsogeny c` with itself gives `smulId _ (c ^ 2)`.** -/
@[simp] theorem a1ReflectionIsogeny_mul_self (c : ℕ+) :
    a1ReflectionIsogeny c * a1ReflectionIsogeny c =
      smulId (typeASimplyConnectedRootDatum 1) (c ^ 2) := by
  let P := typeASimplyConnectedRootDatum 1
  let s := RootPairing.Equiv.reflection P (typeASimpleIndex 1 0)
  have hss : ofEquiv s * ofEquiv s = 1 := by
    rw [← RootPairingIsogeny.ofEquivHom_apply, ← map_mul,
      mul_eq_one_iff_eq_inv.mpr (RootPairing.Equiv.reflection_inv P _).symm, map_one]
  rw [a1ReflectionIsogeny_def, mul_assoc, ← mul_assoc (smulId P c),
    (RootPairingIsogeny.commute_smulId P (ofEquiv s) c).eq, mul_assoc, ← mul_assoc (ofEquiv s), hss]
  simp [P, RootPairingIsogeny.smulId_mul_smulId, sq]

/-- Every power of `a1ReflectionIsogeny c` squares to `smulId _ ((c ^ 2) ^ n)`. -/
theorem a1ReflectionIsogeny_pow_mul_self (c : ℕ+) (n : ℕ) :
    a1ReflectionIsogeny c ^ n * a1ReflectionIsogeny c ^ n =
      smulId (typeASimplyConnectedRootDatum 1) ((c ^ 2) ^ n) :=
  RootPairingIsogeny.pow_mul_self_eq_smulId _ (a1ReflectionIsogeny_mul_self c) n

/-- **`a1ReflectionIsogeny c` is not based** with respect to any base `b`. -/
@[simp] theorem not_isBased_a1ReflectionIsogeny (b : (typeASimplyConnectedRootDatum 1).Base)
    (c : ℕ+) : ¬ (a1ReflectionIsogeny c).IsBased b := fun hBased => by
  let P := typeASimplyConnectedRootDatum 1
  obtain ⟨γ, hγpos⟩ : ∃ γ : Fin (1 * (1 + 1)), γ ∈ posRoots P b := by
    by_cases h0 : typeASimpleIndex 1 0 ∈ posRoots P b
    · exact ⟨typeASimpleIndex 1 0, h0⟩
    · exact ⟨P.reflectionPerm (typeASimpleIndex 1 0) (typeASimpleIndex 1 0),
        (reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b _).mpr
          ((not_mem_posRoots_iff_mem_negRoots P b _).mp h0)⟩
  have himg := hBased.indexEquiv_mem_posRoots hγpos
  rw [a1ReflectionIsogeny_indexEquiv, reflectionPerm_typeASimpleIndex_one_zero] at himg
  exact reflectionPerm_self_notMem_posRoots P b hγpos himg

/-- **`a1ReflectionIsogeny c` does not equal any based endo-isogeny.** -/
theorem a1ReflectionIsogeny_ne_of_isBased (b : (typeASimplyConnectedRootDatum 1).Base) (c : ℕ+)
    {f : RootPairingIsogeny (typeASimplyConnectedRootDatum 1) (typeASimplyConnectedRootDatum 1)}
    (hf : f.IsBased b) : a1ReflectionIsogeny c ≠ f :=
  fun heq => not_isBased_a1ReflectionIsogeny b c (heq ▸ hf)

/-- **`a1ReflectionIsogeny c` does not equal any positive scaling `smulId _ d`.** -/
theorem a1ReflectionIsogeny_ne_smulId (c d : ℕ+) :
    a1ReflectionIsogeny c ≠ smulId (typeASimplyConnectedRootDatum 1) d :=
  a1ReflectionIsogeny_ne_of_isBased (typeASimplyConnectedBase 1) c
    (RootPairingIsogeny.isBased_smulId _ (typeASimplyConnectedBase 1) d)

/-- **`a1ReflectionIsogeny c` is invariant under conjugation by every automorphism.** -/
@[simp] theorem conj_ofEquiv_a1ReflectionIsogeny
    (g : RootPairing.Aut (typeASimplyConnectedRootDatum 1)) (c : ℕ+) :
    ofEquiv g * a1ReflectionIsogeny c * ofEquiv g⁻¹ = a1ReflectionIsogeny c := by
  let P := typeASimplyConnectedRootDatum 1
  let s := RootPairing.Equiv.reflection P (typeASimpleIndex 1 0)
  have hgs : ofEquiv g * ofEquiv s * ofEquiv g⁻¹ = ofEquiv s := by
    rw [← RootPairingIsogeny.ofEquivHom_apply, ← RootPairingIsogeny.ofEquivHom_apply,
      ← RootPairingIsogeny.ofEquivHom_apply, ← map_mul, ← map_mul,
      aut_typeASimplyConnectedRootDatum_one_mul_comm g s, mul_inv_cancel_right]
  rw [a1ReflectionIsogeny_def, mul_assoc, mul_assoc,
    (RootPairingIsogeny.commute_smulId P (ofEquiv g⁻¹) c).eq, ← mul_assoc, ← mul_assoc, hgs]

/-- **No `Aut`-conjugate of `a1ReflectionIsogeny c` is based** with respect to any base `b`. -/
theorem not_isBased_conj_ofEquiv_a1ReflectionIsogeny (b : (typeASimplyConnectedRootDatum 1).Base)
    (g : RootPairing.Aut (typeASimplyConnectedRootDatum 1)) (c : ℕ+) :
    ¬ (ofEquiv g * a1ReflectionIsogeny c * ofEquiv g⁻¹).IsBased b := by
  rw [conj_ofEquiv_a1ReflectionIsogeny]; exact not_isBased_a1ReflectionIsogeny b c

/-- **No `Aut`-conjugate of `a1ReflectionIsogeny c` equals any based endo-isogeny.** -/
theorem conj_ofEquiv_a1ReflectionIsogeny_ne_of_isBased (b : (typeASimplyConnectedRootDatum 1).Base)
    (g : RootPairing.Aut (typeASimplyConnectedRootDatum 1)) (c : ℕ+)
    {f : RootPairingIsogeny (typeASimplyConnectedRootDatum 1) (typeASimplyConnectedRootDatum 1)}
    (hf : f.IsBased b) : ofEquiv g * a1ReflectionIsogeny c * ofEquiv g⁻¹ ≠ f :=
  fun heq => not_isBased_conj_ofEquiv_a1ReflectionIsogeny b g c (heq ▸ hf)

/-- **No `Aut`-conjugate of `a1ReflectionIsogeny c` equals any positive scaling `smulId _ d`.** -/
theorem conj_ofEquiv_a1ReflectionIsogeny_ne_smulId
    (g : RootPairing.Aut (typeASimplyConnectedRootDatum 1)) (c d : ℕ+) :
    ofEquiv g * a1ReflectionIsogeny c * ofEquiv g⁻¹ ≠ smulId (typeASimplyConnectedRootDatum 1) d :=
  conj_ofEquiv_a1ReflectionIsogeny_ne_of_isBased (typeASimplyConnectedBase 1) g c
    (RootPairingIsogeny.isBased_smulId _ (typeASimplyConnectedBase 1) d)

end TauCeti.DynkinType

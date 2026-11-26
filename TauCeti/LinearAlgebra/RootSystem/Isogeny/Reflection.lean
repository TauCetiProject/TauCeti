/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Basic

import Mathlib.Tactic.Module

/-!
# Weyl-reflection compatibility of root-pairing isogenies

An isogeny `f : P ⟶ Q` of root pairings intertwines the Weyl reflections on weight space and the
Weyl coreflections on coweight space (`weightMap_reflection`, `coweightMap_coreflection`) over any
commutative ring. When `Q` is reduced over a characteristic-zero domain, `f.indexEquiv` intertwines
the root reflection permutations, `f.exponent` is invariant on Weyl orbits, and `f.indexEquiv`
preserves opposite root pairs (`indexEquiv_reflectionPerm`, `exponent_reflectionPerm`,
`root_indexEquiv_eq_neg_iff`, `root_indexEquiv_add_eq_zero_iff`).

## References

* Schémas en groupes (SGA 3), Exposé XXI, 6.8; R. Steinberg, *Memoirs AMS* 80 (1968), §11.
-/

public section

namespace TauCeti.RootPairingIsogeny

section ReflectionMap

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}

/-- **The weight map of a root-pairing isogeny intertwines Weyl reflections.** -/
theorem weightMap_reflection (f : RootPairingIsogeny P Q) (i : ι) (x : M) :
    f.weightMap (P.reflection i x) = Q.reflection (f.indexEquiv i) (f.weightMap x) := by
  simp only [RootPairing.reflection_apply, LinearMap.flip_apply, map_sub, map_smul,
    f.weight_coweight_transpose, f.root_weightMap, f.coroot_coweightMap]
  module

/-- **The coweight map of a root-pairing isogeny intertwines Weyl coreflections.** -/
theorem coweightMap_coreflection (f : RootPairingIsogeny P Q) (i : ι) (y : N₂) :
    f.coweightMap (Q.coreflection (f.indexEquiv i) y) = P.coreflection i (f.coweightMap y) := by
  simp only [RootPairing.coreflection_apply, map_sub, map_smul, LinearMap.smul_apply,
    ← f.weight_coweight_transpose, f.root_weightMap, f.coroot_coweightMap]
  module

end ReflectionMap

section Reflection

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} [Q.IsReduced]

private theorem indexEquiv_reflectionPerm_and_exponent (f : RootPairingIsogeny P Q) (i j : ι) :
    f.indexEquiv (P.reflectionPerm i j) = Q.reflectionPerm (f.indexEquiv i) (f.indexEquiv j) ∧
      f.exponent (P.reflectionPerm i j) = f.exponent j := by
  have : Module.IsReflexive R M₂ := .of_isPerfPair Q.toLinearMap
  have : HasUniqueDiv M₂ := .of_isTorsionFree R M₂
  set k₁ := f.indexEquiv (P.reflectionPerm i j)
  set k₂ := Q.reflectionPerm (f.indexEquiv i) (f.indexEquiv j)
  have hw : (f.exponent (P.reflectionPerm i j) : R) • Q.root k₁ =
      (f.exponent j : R) • Q.root k₂ := by
    rw [← f.root_weightMap, P.root_reflectionPerm, f.weightMap_reflection, f.root_weightMap,
      map_smul, Q.root_reflectionPerm]
  have he₁ := f.exponent_pos (P.reflectionPerm i j)
  have he₂ := f.exponent_pos j
  have hdep : ¬LinearIndependent R ![Q.root k₁, Q.root k₂] :=
    mt LinearIndependent.pair_iff.mp <| not_forall.mpr ⟨(f.exponent (P.reflectionPerm i j) : R),
      not_forall.mpr ⟨-(f.exponent j : R), not_imp.mpr ⟨by rw [neg_smul, hw, add_neg_cancel],
        fun ⟨h0, _⟩ => absurd h0 (by exact_mod_cast he₁.ne')⟩⟩⟩
  rcases (by simpa only [RootPairing.IsReduced.linearIndependent_iff, not_and_or, not_not]
      using hdep : k₁ = k₂ ∨ Q.root k₁ = -Q.root k₂) with hk | hneg
  · exact ⟨hk, smul_left_injective ℤ (Q.ne_zero k₂)
      (by simpa [hk, Int.cast_smul_eq_zsmul] using hw)⟩
  · have : -f.exponent (P.reflectionPerm i j) = f.exponent j :=
      smul_left_injective ℤ (Q.ne_zero k₂)
        (by simpa [hneg, Int.cast_smul_eq_zsmul, smul_neg, neg_smul] using hw)
    omega

/-- **The index bijection of a root-pairing isogeny intertwines Weyl reflections.** -/
@[simp] theorem indexEquiv_reflectionPerm (f : RootPairingIsogeny P Q) (i j : ι) :
    f.indexEquiv (P.reflectionPerm i j) = Q.reflectionPerm (f.indexEquiv i) (f.indexEquiv j) :=
  (indexEquiv_reflectionPerm_and_exponent f i j).1

/-- **The rescaling exponent of a root-pairing isogeny is constant on Weyl orbits.** -/
@[simp] theorem exponent_reflectionPerm (f : RootPairingIsogeny P Q) (i j : ι) :
    f.exponent (P.reflectionPerm i j) = f.exponent j :=
  (indexEquiv_reflectionPerm_and_exponent f i j).2

/-- **The index bijection of a root-pairing isogeny preserves opposite root pairs.** -/
theorem root_indexEquiv_eq_neg_iff (f : RootPairingIsogeny P Q) (i j : ι) :
    Q.root (f.indexEquiv i) = -Q.root (f.indexEquiv j) ↔ P.root i = -P.root j := by
  rw [RootPairing.root_eq_neg_iff, RootPairing.root_eq_neg_iff, ← f.indexEquiv_reflectionPerm,
    f.indexEquiv.injective.eq_iff]

/-- Two image roots sum to zero if and only if the source roots sum to zero. -/
theorem root_indexEquiv_add_eq_zero_iff (f : RootPairingIsogeny P Q) (i j : ι) :
    Q.root (f.indexEquiv i) + Q.root (f.indexEquiv j) = 0 ↔ P.root i + P.root j = 0 := by
  rw [add_eq_zero_iff_eq_neg, add_eq_zero_iff_eq_neg, f.root_indexEquiv_eq_neg_iff]

end Reflection

end TauCeti.RootPairingIsogeny

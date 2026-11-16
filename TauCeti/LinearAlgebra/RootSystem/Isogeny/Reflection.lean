/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Power

/-!
# Weyl reflections and involutive index permutations of root-pairing isogenies

An isogeny `f : P ⟶ Q` of root pairings intertwines Weyl reflections via `f.indexEquiv` and has
Weyl-invariant `f.exponent` when `Q` is reduced over a characteristic-zero domain
(`indexEquiv_reflectionPerm`, `exponent_reflectionPerm`, `root_indexEquiv_add_eq_zero_iff`). If
`f * f = smulId P c`, `f.indexEquiv` is an involution and complementary exponents multiply to `c`
(`indexEquiv_apply_apply`, `exponent_mul_exponent_indexEquiv`), with transport along `P = Q` via
`ofEq` and `ofEq_mul_self`.

## References

* Schémas en groupes (SGA 3), Exposé XXI, 6.8; R. Steinberg, *Memoirs AMS* 80 (1968), §11.
-/

public section

namespace TauCeti.RootPairingIsogeny

/-- Transport an endo-isogeny along `P = Q`, keeping maps, `indexEquiv`, and `exponent`
definitionally unchanged. -/
@[expose] def ofEq {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] {P Q : RootPairing ι R M N} (h : P = Q) (f : RootPairingIsogeny Q Q) :
    RootPairingIsogeny P P :=
  ⟨f.1, f.2, f.3, f.4, f.5, f.6, f.7, f.8, f.9, h ▸ f.10, h ▸ f.11, h ▸ f.12⟩

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
    calc (f.exponent (P.reflectionPerm i j) : R) • Q.root k₁
        = f.weightMap (P.root j - P.pairing j i • P.root i) := by
          rw [← f.root_weightMap, P.root_reflectionPerm, P.reflection_apply_root]
      _ = (f.exponent j : R) • Q.root (f.indexEquiv j) -
            ((f.exponent j : R) * Q.pairing (f.indexEquiv j) (f.indexEquiv i)) •
              Q.root (f.indexEquiv i) := by
          rw [map_sub, map_smul, f.root_weightMap, f.root_weightMap, smul_smul,
            mul_comm (P.pairing j i), f.exponent_mul_pairing j i]
      _ = (f.exponent j : R) • Q.root k₂ := by
          rw [Q.root_reflectionPerm, Q.reflection_apply_root, smul_sub, smul_smul]
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

section ScalingSquare

variable {ι M N : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
  [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]
  (P : RootPairing ι ℤ M N) {f : RootPairingIsogeny P P} {c : ℕ+}

/-- Transporting `g * g = smulId Q c` along `P = Q` yields `ofEq h g * ofEq h g = smulId P c`. -/
theorem ofEq_mul_self {Q : RootPairing ι ℤ M N} (h : P = Q) {g : RootPairingIsogeny Q Q}
    (hg : g * g = smulId Q c) : ofEq h g * ofEq h g = smulId P c := by
  subst h; exact hg

/-- **An endo-isogeny whose square is a scaling induces an involution on root indices.** -/
theorem indexEquiv_apply_apply (h : f * f = smulId P c) (i : ι) :
    f.indexEquiv (f.indexEquiv i) = i := by simpa using congrArg (fun g => g.indexEquiv i) h

/-- The inverse of the index permutation of an endo-isogeny whose square is a scaling is itself. -/
theorem indexEquiv_symm (h : f * f = smulId P c) : f.indexEquiv.symm = f.indexEquiv :=
  Equiv.ext fun i => f.indexEquiv.symm_apply_eq.2 (indexEquiv_apply_apply P h i).symm

/-- **Complementary exponents multiply to the scaling factor.** -/
theorem exponent_mul_exponent_indexEquiv (h : f * f = smulId P c) (i : ι) :
    f.exponent i * f.exponent (f.indexEquiv i) = c := by
  simpa using congrArg (fun g => g.exponent i) h

/-- Evaluating `weightMap` at `P.root (f.indexEquiv i)` rescales `P.root i` by
`f.exponent (f.indexEquiv i)`. -/
theorem weightMap_root_indexEquiv (h : f * f = smulId P c) (i : ι) :
    f.weightMap (P.root (f.indexEquiv i)) = f.exponent (f.indexEquiv i) • P.root i := by
  rw [f.root_weightMap, indexEquiv_apply_apply P h, Int.cast_id]

/-- Evaluating `coweightMap` at `P.coroot i` rescales `P.coroot (f.indexEquiv i)` by
`f.exponent (f.indexEquiv i)`. -/
theorem coweightMap_coroot (h : f * f = smulId P c) (i : ι) :
    f.coweightMap (P.coroot i) = f.exponent (f.indexEquiv i) • P.coroot (f.indexEquiv i) := by
  simpa only [indexEquiv_apply_apply P h, Int.cast_id] using f.coroot_coweightMap (f.indexEquiv i)

end ScalingSquare

end TauCeti.RootPairingIsogeny

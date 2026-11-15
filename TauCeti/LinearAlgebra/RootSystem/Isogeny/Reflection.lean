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

An isogeny `f : P ⟶ Q` of root pairings does not preserve Cartan integers when its exponents vary
with root length, yet its index bijection still intertwines all Weyl reflections, and its exponent
function is constant along every Weyl orbit. Writing out `f.weightMap` on the reflected root
`P.root j - P.pairing j i • P.root i` and eliminating `P.pairing j i` through
`TauCeti.RootPairingIsogeny.exponent_mul_pairing` yields

```text
exponent (P.reflectionPerm i j) • Q.root (indexEquiv (P.reflectionPerm i j)) =
  exponent j • Q.root (Q.reflectionPerm (indexEquiv i) (indexEquiv j)).
```

When `Q` is reduced over a characteristic-zero domain and all exponents are positive, the two
indices must coincide and their exponents must agree. In particular, `indexEquiv` commutes with
root negation `i ↦ reflectionPerm i i`, so opposite root pairs correspond under `indexEquiv`, and
the exponent of an isogeny depends only on the Weyl orbit of a root.

For an endo-isogeny `f` of a finite free `ℤ`-root pairing satisfying `f * f = smulId P c`, reading
the index and exponent components of the square identity shows that `f.indexEquiv` is an involution
and that `f.exponent i * f.exponent (f.indexEquiv i) = c` for every root index `i`.

## Main results

* `TauCeti.RootPairingIsogeny.indexEquiv_reflectionPerm`: the index bijection of an isogeny into a
  reduced root pairing over a characteristic-zero domain intertwines `reflectionPerm`.
* `TauCeti.RootPairingIsogeny.exponent_reflectionPerm`: the rescaling exponent is invariant under
  every Weyl reflection.
* `TauCeti.RootPairingIsogeny.root_indexEquiv_eq_neg_iff` and
  `TauCeti.RootPairingIsogeny.root_indexEquiv_add_eq_zero_iff`: `indexEquiv` preserves opposite root
  pairs.
* `TauCeti.RootPairingIsogeny.indexEquiv_apply_apply` and
  `TauCeti.RootPairingIsogeny.exponent_mul_exponent_indexEquiv`: for `f * f = smulId P c`, the
  index permutation is involutive and complementary exponents multiply to `c`.

## References

* Schémas en groupes (SGA 3), Exposé XXI, 6.8.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
-/

public section

namespace TauCeti.RootPairingIsogeny

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
  have hw : (f.exponent (P.reflectionPerm i j) : R) •
      Q.root (f.indexEquiv (P.reflectionPerm i j)) =
      (f.exponent j : R) • Q.root (Q.reflectionPerm (f.indexEquiv i) (f.indexEquiv j)) := by
    calc (f.exponent (P.reflectionPerm i j) : R) • Q.root (f.indexEquiv (P.reflectionPerm i j))
        = f.weightMap (P.root (P.reflectionPerm i j)) := (f.root_weightMap _).symm
      _ = f.weightMap (P.root j - P.pairing j i • P.root i) := by
          rw [P.root_reflectionPerm, P.reflection_apply_root]
      _ = (f.exponent j : R) • Q.root (f.indexEquiv j) -
            (P.pairing j i * (f.exponent i : R)) • Q.root (f.indexEquiv i) := by
          rw [map_sub, map_smul, f.root_weightMap, f.root_weightMap, smul_smul]
      _ = (f.exponent j : R) • Q.root (f.indexEquiv j) -
            ((f.exponent j : R) * Q.pairing (f.indexEquiv j) (f.indexEquiv i)) •
              Q.root (f.indexEquiv i) := by
          rw [mul_comm (P.pairing j i), f.exponent_mul_pairing j i]
      _ = (f.exponent j : R) • Q.root (Q.reflectionPerm (f.indexEquiv i) (f.indexEquiv j)) := by
          rw [Q.root_reflectionPerm, Q.reflection_apply_root, smul_sub, smul_smul]
  set k₁ := f.indexEquiv (P.reflectionPerm i j)
  set k₂ := Q.reflectionPerm (f.indexEquiv i) (f.indexEquiv j)
  have he₁ : 0 < f.exponent (P.reflectionPerm i j) := f.exponent_pos _
  have he₂ : 0 < f.exponent j := f.exponent_pos _
  have hdep : ¬LinearIndependent R ![Q.root k₁, Q.root k₂] := by
    simpa only [LinearIndependent.pair_iff, not_forall] using
      ⟨(f.exponent (P.reflectionPerm i j) : R), -(f.exponent j : R),
        by rw [neg_smul, hw, add_neg_cancel],
        fun ⟨h0, _⟩ => absurd h0 (by exact_mod_cast he₁.ne')⟩
  have hor : k₁ = k₂ ∨ Q.root k₁ = -Q.root k₂ := by
    simpa only [RootPairing.IsReduced.linearIndependent_iff, not_and_or, not_not] using hdep
  rcases hor with hk | hneg
  · refine ⟨hk, smul_left_injective ℤ (Q.ne_zero k₂) ?_⟩
    simpa only [hk, Int.cast_smul_eq_zsmul] using hw
  · exfalso
    have hcontra : -f.exponent (P.reflectionPerm i j) = f.exponent j := by
      apply smul_left_injective ℤ (Q.ne_zero k₂)
      simpa only [hneg, Int.cast_smul_eq_zsmul, smul_neg, neg_smul] using hw
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

/-- **An endo-isogeny whose square is a scaling induces an involution on root indices.** -/
theorem indexEquiv_apply_apply (h : f * f = smulId P c) (i : ι) :
    f.indexEquiv (f.indexEquiv i) = i := by
  simpa only [indexEquiv_mul, smulId_indexEquiv, Equiv.trans_apply, Equiv.refl_apply] using
    congrArg (fun g => g.indexEquiv i) h

/-- The inverse of the index permutation of an endo-isogeny whose square is a scaling is itself. -/
theorem indexEquiv_symm (h : f * f = smulId P c) : f.indexEquiv.symm = f.indexEquiv := by
  ext i
  exact f.indexEquiv.symm_apply_eq.2 (indexEquiv_apply_apply P h i).symm

/-- **Complementary exponents multiply to the scaling factor.** When `f * f = smulId P c`, the
exponents at `i` and `f.indexEquiv i` have product `c`. -/
theorem exponent_mul_exponent_indexEquiv (h : f * f = smulId P c) (i : ι) :
    f.exponent i * f.exponent (f.indexEquiv i) = c := by
  simpa only [exponent_mul, smulId_exponent] using congrArg (fun g => g.exponent i) h

/-- Evaluating `weightMap` at the partner root `P.root (f.indexEquiv i)` rescales `P.root i` by
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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.EvensNorm
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic
import TauCeti.FieldTheory.GaloisCohomology.Corestriction.Exact
import TauCeti.FieldTheory.GaloisCohomology.MuTwo.CupNorm
import TauCeti.FieldTheory.GaloisCohomology.MuTwo.KummerCharacter
import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Transfer

/-!
# The quadratic character of `K(√d)/K` is the Kummer class of `d`

Let `K` be a field in which `2` is invertible and let `L = K(x)` be a quadratic extension with
`x ∉ K` and `x² = d ∈ Kˣ`. A `K`-embedding `σ : L → Kˢ` cuts out the index-two open subgroup
`G_L` of `G_K`, and the class `χ_{L/K} = TauCeti.galoisCharacter K L σ hL ∈ H¹(G_K, 𝔽₂)` of the
character with kernel `G_L` is the **Kummer class** `(d)`
(`TauCeti.galoisCharacter_eq_kummerClass`). Indeed `g ∈ G_K` fixes `σ(L)` exactly when it fixes
the generator `σ(x)`, a square root of `d`, and the Kummer class of `d` is the class of the
character `g ↦ [g σ(x) ≠ σ(x)]` (`TauCeti.kummerClass_eq_homClass`).

This reads two index-two statements about `χ_{L/K}` in terms of Kummer classes over `K`:

* the kernel of restriction `H²(G_K, 𝔽₂) → H²(G_L, 𝔽₂)` is `(d) ∪ H¹(G_K, 𝔽₂)`
  (`TauCeti.galoisRes2_eq_zero_iff`);
* the Evens norm of a restricted class is `N^{Ev}(res y) = y ∪ y + (d) ∪ y`
  (`TauCeti.galoisEvens2_galoisRes1`).

The second determines the norm on the classes that come from `K`. On the Kummer class of `b ∈ Kˣ`,
where `(b) ∪ (b) = (-1) ∪ (b)`, it gives `N^{Ev}((b)) = (-d) ∪ (b)`
(`TauCeti.galoisEvens2_kummerClass_algebraMap`). The other Evens identity,
`res N^{Ev}(z) = z ∪ σ·z`, determines `N^{Ev}(z)` only modulo the kernel `(d) ∪ H¹(G_K, 𝔽₂)` of
restriction; the formula above computes `N^{Ev}` exactly on the restricted classes.

## Main results

* `TauCeti.galoisCharacter_eq_kummerClass`: `χ_{K(√d)/K} = (d)`.
* `TauCeti.galoisRes2_eq_zero_iff`: a class in `H²(G_K, 𝔽₂)` restricts to zero over `K(√d)` exactly
  when it is `(d) ∪ y` for some `y ∈ H¹(G_K, 𝔽₂)`.
* `TauCeti.galoisEvens2_galoisRes1`: `N^{Ev}(res y) = y ∪ y + (d) ∪ y`.
* `TauCeti.galoisEvens2_kummerClass_algebraMap`: `N^{Ev}((b)) = (-d) ∪ (b)` for `b ∈ Kˣ`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1) and
  Chapter I, §§5–6.
* J. Kr. Arason, *Cohomologische Invarianten quadratischer Formen*, J. Algebra **36** (1975),
  448–491.
* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer. Math.
  Soc. **108** (1963), 54–65.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology

universe u

section Universe

variable {K : Type u} [Field K] [Invertible (2 : K)] {L : Type u} [Field L] [Algebra K L]
  [FiniteDimensional K L] (σ : L →ₐ[K] SeparableClosure K) (hL : Module.finrank K L = 2)
  {d : Kˣ} {x : L}

/-- **The quadratic character of `K(√d)/K` is the Kummer class of `d`.** If `L = K(x)` with
`x ∉ K` and `x² = d`, the class `χ_{L/K}` of the character of `G_K` with kernel `G_L` is
`(d) ∈ H¹(G_K, 𝔽₂)`. -/
theorem galoisCharacter_eq_kummerClass (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L (d : K)) :
    galoisCharacter K L σ hL = kummerClass d := by
  have hr : σ x ^ 2 = algebraMap K (SeparableClosure K) d := by
    rw [← map_pow, hx2, AlgHom.commutes]
  rw [galoisCharacter_def, OpenSubgroup.indexTwoCharacterClass_def, ← homClass_def,
    kummerClass_eq_homClass d (σ x) hr]
  -- Both characters are `g ↦ rootSign (σ x) g`.
  congr 1
  refine MonoidHom.ext fun g => Multiplicative.toAdd.injective ?_
  rw [toAdd_kummerCharacter, toAdd_indexTwoCharacter_galoisSubgroup_eq_rootSign σ _ hx]

/-- **The kernel of restriction to `K(√d)` in degree two is `(d) ∪ H¹(G_K, 𝔽₂)`.** If
`L = K(x)` with `x ∉ K` and `x² = d`, a class `z ∈ H²(G_K, 𝔽₂)` restricts to zero over `L`
exactly when `z = (d) ∪ y` for some `y ∈ H¹(G_K, 𝔽₂)`. -/
theorem galoisRes2_eq_zero_iff (hL : Module.finrank K L = 2)
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L (d : K))
    (z : continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K))) :
    galoisRes K L σ 2 z = 0 ↔
      ∃ y : continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup K)),
        z = (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass d) y := by
  rw [galoisRes_eq_zero_iff K L σ hL, galoisCharacter_eq_kummerClass σ hL hx hx2]

/-- **The Evens norm of a restricted class.** If `L = K(x)` with `x ∉ K` and `x² = d`, then for
every `y ∈ H¹(G_K, 𝔽₂)`,

```text
N^{Ev}(res y) = y ∪ y + (d) ∪ y.
``` -/
theorem galoisEvens2_galoisRes1 (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L (d : K))
    (y : continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup K))) :
    galoisEvens K L σ hL (galoisRes K L σ 1 y) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 y y +
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass d) y := by
  rw [galoisEvens_galoisRes, galoisCharacter_eq_kummerClass σ hL hx hx2]

end Universe

/-! ### The norm of a Kummer class from the base -/

section TypeZero

variable {K : Type} [Field K] [Invertible (2 : K)] {L : Type} [Field L] [Algebra K L]
  [FiniteDimensional K L] [Invertible (2 : L)] (σ : L →ₐ[K] SeparableClosure K)
  (hL : Module.finrank K L = 2) {d : Kˣ} {x : L}

/-- **The Evens norm of the Kummer class of an element of the base.** If `L = K(x)` with `x ∉ K`
and `x² = d`, then for `b ∈ Kˣ`, viewed in `L`, `N^{Ev}((b)) = (-d) ∪ (b)`. This is stated for
`K : Type`, the universe of the comparison of cup products of Kummer classes with quaternion
symbols (`TauCeti.cup_kummerClass_eq_cup_kummerClass_iff_quaternionClass_eq`). -/
theorem galoisEvens2_kummerClass_algebraMap (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L (d : K)) (b : Kˣ) :
    galoisEvens K L σ hL (kummerClass (Units.map (algebraMap K L).toMonoidHom b)) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass (-d))
        (kummerClass b) := by
  -- `(b) ∪ (b) = (-1) ∪ (b)`, read off the quaternion relation `[(b, b)] = [(b, -1)]`.
  have hself : (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass b)
      (kummerClass b) =
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass (-1))
          (kummerClass b) :=
    (cup_kummerClass_eq_cup_kummerClass_iff_quaternionClass_eq b b (-1) b).2 <| by
      rw [BrauerGroup.quaternionClass_self, BrauerGroup.quaternionClass_comm]
  have hd : -d = -1 * d := (neg_one_mul d).symm
  rw [← galoisRes_kummerClass, galoisEvens2_galoisRes1 σ hL hx hx2, hself, hd, kummerClass_mul,
    map_add, LinearMap.add_apply]

end TypeZero

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.AlgebraicTopology.Singular.Coefficients.Bockstein
public import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
public import TauCeti.AlgebraicTopology.Singular.Coefficients.ZModCoefficientSequence

import TauCeti.Algebra.Category.ModuleCat.AB
import TauCeti.Algebra.Module.Torsion.Int

/-!
# Integral singular homology from homology with prime field coefficients

The singular homology of a space `X` with coefficients in `ℤ/m` can be formed with the integer
module `ℤ/m` as coefficients in `ModuleCat ℤ`, which is how it appears in the coefficient long
exact sequence of `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/m ⟶ 0`, or with a ring `k ≅ ℤ/m`, such as the field `𝔽_p` for a
prime `m = p`, as coefficients in `ModuleCat k`. Restriction of scalars along `ℤ → k` preserves
coproducts and homology, so one vanishes exactly when the other does
(`TopCat.isZero_singularHomology_zmod_iff_of_ringEquiv`).

The coefficient long exact sequence

`⋯ ⟶ Hₙ₊₁(X; ℤ/m) ⟶ Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ/m) ⟶ ⋯`,

whose middle map is multiplication by `m`
(`TopCat.singularHomologyFunctor_map_zmodCoefficientSequence_f_app`) and whose next map is the
reduction `ρ : Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ/m)` (`TopCat.singularHomologyReductionMod`), shows:

* a class reduces to zero exactly when it is `m` times a class
  (`TopCat.ker_singularHomologyReductionMod`);
* the reduction is onto in degree `n + 1` exactly when multiplication by `m` is injective on
  `Hₙ(X; ℤ)` (`TopCat.surjective_singularHomologyReductionMod_succ_iff`);
* if `Hₙ(X; ℤ/m) = 0`, multiplication by `m` on `Hₙ(X; ℤ)` is onto
  (`TopCat.surjective_lsmul_singularHomology_of_isZero_zmod`);
* if `Hₙ₊₁(X; ℤ/m) = 0`, multiplication by `m` on `Hₙ(X; ℤ)` is injective
  (`TopCat.injective_lsmul_singularHomology_of_isZero_zmod`).

Letting `m` run through the primes, integral homology is controlled by homology with coefficients
in the prime fields. If `Hₙ₊₁(X; 𝔽_p) = 0` for every prime `p`, then `Hₙ(X; ℤ)` is torsion-free
(`TopCat.isTorsionFree_singularHomology_of_forall_isZero_zmod`), hence free when it is finitely
generated. If `Hₙ(X; 𝔽_p) = 0` for every prime `p` and `Hₙ(X; ℤ)` is finitely generated, then
`Hₙ(X; ℤ) = 0` (`TopCat.isZero_singularHomology_of_forall_isZero_zmod`). For instance, if a compact
manifold has vanishing odd-degree homology over every prime field, its integral homology vanishes
in odd degrees and is free in even degrees. Finite generation is essential for the second
statement: a Moore space with first integral homology the divisible torsion group `ℚ / ℤ` has
vanishing first homology over every prime field.

## Main results

* `TopCat.isZero_singularHomology_zmod_iff_of_ringEquiv`: homology with coefficients in the integer
  module `ℤ/m` vanishes exactly when homology over a ring `k ≅ ℤ/m` does.
* `TopCat.singularHomologyReductionMod`: the reduction `Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ/m)` modulo `m`.
* `TopCat.ker_singularHomologyReductionMod`,
  `TopCat.surjective_singularHomologyReductionMod_succ_iff`: its kernel is `m Hₙ(X; ℤ)`, and it is
  onto in degree `n + 1` exactly when multiplication by `m` on `Hₙ(X; ℤ)` is injective.
* `TopCat.surjective_lsmul_singularHomology_of_isZero_zmod`,
  `TopCat.injective_lsmul_singularHomology_of_isZero_zmod`: vanishing of mod-`m` homology makes
  multiplication by `m` on integral homology onto, respectively injective one degree lower.
* `TopCat.isTorsionFree_singularHomology_of_forall_isZero_zmod`: integral homology is torsion-free
  in the degree just below a degree in which homology over every prime field vanishes.
* `TopCat.isZero_singularHomology_of_forall_isZero_zmod`: finitely generated integral homology
  vanishes in a degree in which homology over every prime field vanishes.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.A (change of coefficients and the universal coefficient theorem) and Section 3.E
  (Bockstein homomorphisms).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe u

namespace TopCat

/-- Singular homology with coefficients in the integer module `ℤ/m` vanishes exactly when singular
homology with coefficients in a ring `k ≅ ℤ/m`, as a module over itself, does. For `k = ZMod m`
and a space in the lowest universe this compares `ℤ/m` and `ZMod m` themselves rather than their
lifts. -/
theorem isZero_singularHomology_zmod_iff_of_ringEquiv (X : TopCat.{u}) (m : ℕ) {k : Type u}
    [CommRing k] (e : k ≃+* ZMod m) (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X) := by
  -- `ℤ/m` and `k` are isomorphic abelian groups, and `k` as an integer module is `k` with its
  -- scalars restricted along `ℤ → k`, which preserves coproducts and homology
  rw [Iso.isZero_iff (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).mapIso
      (AddEquiv.ulift.trans e.symm.toAddEquiv).toIntLinearEquiv.toModuleIso).app X),
    Iso.isZero_iff (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).mapIso
      (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := k) k).symm).app X ≪≫
      ((Functor.singularHomologyFunctorObjCompIso
        (ModuleCat.restrictScalars.{u} (algebraMap ℤ k)) (ModuleCat.of k k) n).app X).symm),
    ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  -- restriction of scalars does not change the underlying abelian group
  rfl

/-- The **reduction modulo `m`** `Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ/m)`, induced by the coefficient map
`ℤ ⟶ ℤ/m`. -/
abbrev singularHomologyReductionMod (X : TopCat.{u}) (m n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X ⟶
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X :=
  ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map
    (TauCeti.zmodCoefficientSequence.{u} m).g).app X

/-- **The kernel of the reduction modulo `m`**: an integral homology class reduces to zero modulo
`m` exactly when it is `m` times a class. -/
theorem ker_singularHomologyReductionMod (X : TopCat.{u}) (m : ℕ) [NeZero m] (n : ℕ) :
    LinearMap.ker (X.singularHomologyReductionMod m n).hom =
      LinearMap.range (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) m) := by
  rw [← X.singularHomologyFunctor_map_zmodCoefficientSequence_f_app]
  exact ((X.singularHomology_exact_coefficient₂
    (TauCeti.zmodCoefficientSequence_shortExact.{u} m) n).moduleCat_range_eq_ker).symm

/-- The reduction modulo `m` is onto in degree `n + 1` exactly when multiplication by `m` is
injective on `Hₙ(X; ℤ)`. -/
theorem surjective_singularHomologyReductionMod_succ_iff (X : TopCat.{u}) (m : ℕ) [NeZero m]
    (n : ℕ) :
    Function.Surjective (X.singularHomologyReductionMod m (n + 1)) ↔
      Function.Injective (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) m) := by
  have hS := TauCeti.zmodCoefficientSequence_shortExact.{u} m
  -- both conditions say that the Bockstein homomorphism vanishes
  rw [← ModuleCat.epi_iff_surjective,
    (X.singularHomology_exact_coefficient₃ hS (n + 1) n).epi_f_iff,
    ← (X.singularHomology_exact_coefficient₁ hS (n + 1) n).mono_g_iff, ModuleCat.mono_iff_injective,
    ← X.singularHomologyFunctor_map_zmodCoefficientSequence_f_app]

/-- If the singular homology of `X` with coefficients in `ℤ/m` vanishes in degree `n`, then
multiplication by `m` on the integral homology `Hₙ(X; ℤ)` is onto. -/
theorem surjective_lsmul_singularHomology_of_isZero_zmod (X : TopCat.{u}) (m : ℕ) [NeZero m]
    (n : ℕ) (h : IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X)) :
    Function.Surjective (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) m) :=
  -- every class reduces to zero, hence is `m` times a class
  LinearMap.range_eq_top.1 ((X.ker_singularHomologyReductionMod m n).symm.trans
    (LinearMap.ker_eq_top.2
      (LinearMap.ext fun _ ↦ (ModuleCat.isZero_iff_subsingleton.1 h).elim _ _)))

/-- If the singular homology of `X` with coefficients in `ℤ/m` vanishes in degree `n + 1`, then
multiplication by `m` on the integral homology `Hₙ(X; ℤ)` is injective. -/
theorem injective_lsmul_singularHomology_of_isZero_zmod (X : TopCat.{u}) (m : ℕ) [NeZero m]
    (n : ℕ) (h : IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj X)) :
    Function.Injective (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) m) :=
  -- the reduction modulo `m` onto a zero group is onto
  (X.surjective_singularHomologyReductionMod_succ_iff m n).1 fun _ ↦
    ⟨0, (ModuleCat.isZero_iff_subsingleton.1 h).elim _ _⟩

/-- **Integral homology is torsion-free one degree below vanishing prime field homology.** If
`Hₙ₊₁(X; 𝔽_p) = 0` for every prime `p`, with `𝔽_p` taken as the integer module `ℤ/p`, then
`Hₙ(X; ℤ)` is torsion-free. -/
theorem isTorsionFree_singularHomology_of_forall_isZero_zmod (X : TopCat.{u}) (n : ℕ)
    (h : ∀ p : ℕ, p.Prime → IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod p)))).obj X)) :
    Module.IsTorsionFree ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) := by
  have := TauCeti.hasUniqueDiv_of_forall_prime fun p hp x y hxy ↦ by
    have : NeZero p := ⟨hp.ne_zero⟩
    exact X.injective_lsmul_singularHomology_of_isZero_zmod p n (h p hp)
      (by simpa only [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul] using hxy)
  -- the integer module structure of homology is that of the underlying abelian group
  convert Module.isTorsionFree_int_iff_hasUniqueDiv.2 this
  exact Subsingleton.elim _ _

/-- **Finitely generated integral homology vanishes with prime field homology.** If `Hₙ(X; ℤ)`
is finitely generated and `Hₙ(X; 𝔽_p) = 0` for every prime `p`, with `𝔽_p` taken as the integer
module `ℤ/p`, then `Hₙ(X; ℤ) = 0`. -/
theorem isZero_singularHomology_of_forall_isZero_zmod (X : TopCat.{u}) (n : ℕ)
    [Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X)]
    (h : ∀ p : ℕ, p.Prime → IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod p)))).obj X)) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) := by
  -- Nakayama's lemma over `ℤ`: a finitely generated abelian group on which every prime acts
  -- surjectively is zero
  have := TauCeti.subsingleton_of_forall_prime_surjective fun p hp ↦ by
    have : NeZero p := ⟨hp.ne_zero⟩
    exact fun x ↦ (X.surjective_lsmul_singularHomology_of_isZero_zmod p n (h p hp) x).imp
      fun y hy ↦ by simpa only [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul] using hy
  exact ModuleCat.isZero_of_subsingleton _

end TopCat

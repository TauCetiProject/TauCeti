/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.CategoryTheory.Monoidal.Tor
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Adjunction.Limits
import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
import TauCeti.CategoryTheory.Abelian.LeftDerived
import TauCeti.CategoryTheory.Abelian.Projective.Dimension

/-!
# Projective dimension under extension and surjective restriction of scalars

Let `f : P →+* R` be a homomorphism of commutative rings. Restricting scalars of `R ⊗[P] X` back to
`P` recovers the tensor product of `X` over `P` with `R`
(`ModuleCat.extendScalarsCompRestrictScalarsIso`). Because restriction of scalars is exact and
faithful, the `n`-th left derived functor of `ModuleCat.extendScalars f` at `X` vanishes if and
only if `Tor_n^P(R, X)` vanishes (`ModuleCat.isZero_leftDerived_extendScalars_iff`).

Extension of scalars is right exact and preserves projective modules, so vanishing of
`Tor_{i+1}^P(R, X)` below degree `n` transports projective-dimension bounds `< n` from `X` to
`R ⊗[P] X` (`ModuleCat.hasProjectiveDimensionLT_extendScalars_of_isZero_Tor`). In particular, if
`f : P →+* R` is flat then `Tor_{i+1}^P(R, X) = 0` for every `X`, while if `f` is surjective then
restriction of scalars is full (`RingHom.full_restrictScalars`), so the counit `R ⊗[P] M ≅ M`
transfers projective-dimension bounds from a `P`-restricted `R`-module `M` to `M` over `R` whenever
`Tor_{i+1}^P(R, M) = 0` (`ModuleCat.hasProjectiveDimensionLT_of_surjective_of_isZero_Tor`).

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Exercise 4.1.2 and Section 4.3 (change of
  rings for projective dimension).
-/

public section

namespace ModuleCat

open CategoryTheory Limits

universe u

variable {P R : Type u} [CommRing P] [CommRing R] (f : P →+* R)

/-- The `n`-th left derived functor of extension of scalars along `f : P →+* R` vanishes at a
`P`-module `X` if and only if `Tor_n^P(R, X)` vanishes. -/
theorem isZero_leftDerived_extendScalars_iff (X : ModuleCat.{u} P) (n : ℕ) :
    IsZero (((extendScalars.{u, u, u} f).leftDerived n).obj X) ↔
      IsZero (((Tor (ModuleCat.{u} P) n).obj ((restrictScalars f).obj (of R R))).obj X) := by
  rw [← (extendScalars.{u, u, u} f).isZero_comp_leftDerived_iff (restrictScalars.{u} f), Tor_obj]
  exact ((NatIso.leftDerived (extendScalarsCompRestrictScalarsIso f) n).app X).isZero_iff

/-- **Projective dimension under extension of scalars.** If `X` is a `P`-module of projective
dimension `< n` and `Tor_{i+1}^P(R, X) = 0` for every `i` with `i + 1 < n`, then `R ⊗[P] X` has
projective dimension `< n` over `R`. -/
theorem hasProjectiveDimensionLT_extendScalars_of_isZero_Tor (X : ModuleCat.{u} P) (n : ℕ)
    [HasProjectiveDimensionLT X n]
    (h : ∀ i, i + 1 < n →
      IsZero (((Tor (ModuleCat.{u} P) (i + 1)).obj ((restrictScalars f).obj (of R R))).obj X)) :
    HasProjectiveDimensionLT ((extendScalars.{u, u, u} f).obj X) n := by
  have : PreservesColimitsOfSize.{0, 0} (extendScalars.{u, u, u} f) :=
    (extendRestrictScalarsAdj.{u, u, u} f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (extendScalars.{u, u, u} f) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have := Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (extendRestrictScalarsAdj.{u, u, u} f)
  exact (extendScalars.{u, u, u} f).hasProjectiveDimensionLT_obj_of_isZero_leftDerived X n
    fun i hi ↦ (isZero_leftDerived_extendScalars_iff f X (i + 1)).mpr (h i hi)

/-- If `X` has projective dimension `≤ d` over `P` and `Tor_{i+1}^P(R, X) = 0` for every `i < d`,
then `R ⊗[P] X` has projective dimension `≤ d` over `R`. -/
theorem hasProjectiveDimensionLE_extendScalars_of_isZero_Tor (X : ModuleCat.{u} P) (d : ℕ)
    [HasProjectiveDimensionLE X d]
    (h : ∀ i < d,
      IsZero (((Tor (ModuleCat.{u} P) (i + 1)).obj ((restrictScalars f).obj (of R R))).obj X)) :
    HasProjectiveDimensionLE ((extendScalars.{u, u, u} f).obj X) d :=
  hasProjectiveDimensionLT_extendScalars_of_isZero_Tor f X (d + 1) fun i hi ↦
    h i (Nat.lt_of_succ_lt_succ hi)

/-- If `Tor_{i+1}^P(R, X) = 0` for every `i`, then the projective dimension of `R ⊗[P] X` over `R`
is at most the projective dimension of `X` over `P`. -/
theorem projectiveDimension_extendScalars_le_of_isZero_Tor (X : ModuleCat.{u} P)
    (h : ∀ i,
      IsZero (((Tor (ModuleCat.{u} P) (i + 1)).obj ((restrictScalars f).obj (of R R))).obj X)) :
    projectiveDimension ((extendScalars.{u, u, u} f).obj X) ≤ projectiveDimension X :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun n _ ↦
    hasProjectiveDimensionLT_extendScalars_of_isZero_Tor f X n fun i _ ↦ h i

section Surjective

variable {f}

/-- **Projective dimension along a surjective ring homomorphism.** Let `f : P →+* R` be surjective
and let `M` be an `R`-module whose restriction of scalars to `P` has projective dimension `< n`.
If `Tor_{i+1}^P(R, M) = 0` for every `i` with `i + 1 < n`, then `M` has projective dimension `< n`
over `R`. -/
theorem hasProjectiveDimensionLT_of_surjective_of_isZero_Tor (hf : Function.Surjective f)
    (M : ModuleCat.{u} R) (n : ℕ) [HasProjectiveDimensionLT ((restrictScalars f).obj M) n]
    (h : ∀ i, i + 1 < n → IsZero (((Tor (ModuleCat.{u} P) (i + 1)).obj
      ((restrictScalars f).obj (of R R))).obj ((restrictScalars f).obj M))) :
    HasProjectiveDimensionLT M n := by
  have := f.full_restrictScalars hf
  exact (extendRestrictScalarsAdj.{u, u, u} f).hasProjectiveDimensionLT_of_isZero_leftDerived M n
    fun i hi ↦ (isZero_leftDerived_extendScalars_iff f _ (i + 1)).mpr (h i hi)

/-- If `f : P →+* R` is surjective, `M` has projective dimension `≤ d` over `P`, and
`Tor_{i+1}^P(R, M) = 0` for every `i < d`, then `M` has projective dimension `≤ d` over `R`. -/
theorem hasProjectiveDimensionLE_of_surjective_of_isZero_Tor (hf : Function.Surjective f)
    (M : ModuleCat.{u} R) (d : ℕ) [HasProjectiveDimensionLE ((restrictScalars f).obj M) d]
    (h : ∀ i < d, IsZero (((Tor (ModuleCat.{u} P) (i + 1)).obj
      ((restrictScalars f).obj (of R R))).obj ((restrictScalars f).obj M))) :
    HasProjectiveDimensionLE M d :=
  hasProjectiveDimensionLT_of_surjective_of_isZero_Tor hf M (d + 1) fun i hi ↦
    h i (Nat.lt_of_succ_lt_succ hi)

/-- If `f : P →+* R` is surjective and `Tor_{i+1}^P(R, M) = 0` for every `i`, then the projective
dimension of `M` over `R` is at most its projective dimension as a `P`-module. -/
theorem projectiveDimension_le_restrictScalars_of_surjective_of_isZero_Tor
    (hf : Function.Surjective f) (M : ModuleCat.{u} R)
    (h : ∀ i, IsZero (((Tor (ModuleCat.{u} P) (i + 1)).obj
      ((restrictScalars f).obj (of R R))).obj ((restrictScalars f).obj M))) :
    projectiveDimension M ≤ projectiveDimension ((restrictScalars f).obj M) :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun n _ ↦
    hasProjectiveDimensionLT_of_surjective_of_isZero_Tor hf M n fun i _ ↦ h i

end Surjective

end ModuleCat

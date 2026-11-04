/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.Norm.Transitivity
public import TauCeti.RingTheory.Localization.FiniteFree
public import TauCeti.RingTheory.Norm.NonZeroDivisors

/-!
# Norms on total quotient rings

For a finite free commutative algebra `S` over `R`, the algebra norm extends uniquely to a
multiplicative map from the total quotient ring of `S` to that of `R`. On fractions it is
`Norm(x / y) = Norm(x) / Norm(y)`. Neither ring need be a domain: regular denominators have
regular norms, which is precisely what makes this construction possible.

`Algebra.fractionNorm` does not require a chosen algebra structure between the total quotient
rings. If compatible algebra structures are supplied, it agrees with the ordinary determinant
norm on the localized finite free algebra. It preserves zero for a nontrivial source algebra,
and successive extensions compose in a finite free tower.

In particular this constructs norms on total quotient rings for finite abelian covers: use
`R = NovikovSeries A K (N.comp K.subtype)` and `S = NovikovSeries A H N`, whose finite free
structure is supplied by the coset-monomial basis. This construction alone does not assert that
a nonzero field component stays nonzero under the norm.

## References

* V. Turaev, *Introduction to Combinatorial Torsions*, Birkhäuser 2001, Chapter I.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002), §2.
-/

public section

noncomputable section

open scoped nonZeroDivisors

namespace Algebra

variable (R S QR QS : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S]
  [CommRing QR] [Algebra R QR] [IsFractionRing R QR]
  [CommRing QS] [Algebra S QS] [IsFractionRing S QS]

/-- The unique multiplicative extension of the algebra norm to total quotient rings.
Regular denominators have regular norms; no domain hypothesis is needed. -/
def fractionNorm : QS →* QR :=
  (IsLocalization.toLocalizationMap S⁰ QS).lift
    (g := (algebraMap R QR).toMonoidHom.comp (norm R))
    (fun y => IsLocalization.map_units QR
      ⟨norm R (y : S), norm_mem_nonZeroDivisors_iff.mpr y.property⟩)

/-- The extended norm agrees with the algebra norm on the original algebra. -/
@[simp]
theorem fractionNorm_algebraMap (x : S) :
    fractionNorm R S QR QS (algebraMap S QS x) = algebraMap R QR (norm R x) :=
  Submonoid.LocalizationMap.lift_eq _ _ x

/-- The norm of a fraction is the fraction of the norms, including regular denominators
which need not be units before localization. -/
theorem fractionNorm_mk' (x : S) (y : S⁰) :
    fractionNorm R S QR QS (IsLocalization.mk' QS x y) =
      IsLocalization.mk' QR (norm R x)
        ⟨norm R (y : S), norm_mem_nonZeroDivisors_iff.mpr y.property⟩ := by
  apply (Submonoid.LocalizationMap.lift_mk'_spec
    (IsLocalization.toLocalizationMap S⁰ QS)
    (g := (algebraMap R QR).toMonoidHom.comp (norm R)) _ x _ y).2
  exact (IsLocalization.mk'_spec' QR _
    (⟨norm R (y : S), norm_mem_nonZeroDivisors_iff.mpr y.property⟩ : R⁰)).symm

/-- Multiplication by the norm of a regular denominator clears that denominator. -/
theorem fractionNorm_mul_norm_denominator (z : QS) (x : S) (y : S⁰)
    (hz : z * algebraMap S QS y = algebraMap S QS x) :
    fractionNorm R S QR QS z * algebraMap R QR (norm R (y : S)) =
      algebraMap R QR (norm R x) := by
  simpa only [map_mul, fractionNorm_algebraMap] using congrArg (fractionNorm R S QR QS) hz

/-- Agreement on the original algebra characterizes the extension among multiplicative maps. -/
theorem fractionNorm_unique (f : QS →* QR)
    (hf : ∀ x : S, f (algebraMap S QS x) = algebraMap R QR (norm R x)) :
    fractionNorm R S QR QS = f :=
  Submonoid.LocalizationMap.lift_unique _ _ hf

/-- For a nontrivial finite free algebra the extended norm preserves zero. The nontriviality
hypothesis excludes the rank-zero algebra, whose determinant norm is constantly one. -/
@[simp]
theorem fractionNorm_zero [Nontrivial S] : fractionNorm R S QR QS 0 = 0 := by
  simpa only [map_zero, norm_zero] using fractionNorm_algebraMap R S QR QS (0 : S)

/-- Changing the models of the total quotient rings commutes with the extended norm.
The two coefficient-compatible maps can in particular be the canonical localization
equivalences; thus the construction is independent of those models. -/
theorem fractionNorm_naturality (QR' QS' : Type*)
    [CommRing QR'] [Algebra R QR'] [IsFractionRing R QR']
    [CommRing QS'] [Algebra S QS'] [IsFractionRing S QS']
    (f : QR →ₐ[R] QR') (g : QS →ₐ[S] QS') :
    f.toMonoidHom.comp (fractionNorm R S QR QS) =
      (fractionNorm R S QR' QS').comp g.toMonoidHom := by
  apply (IsLocalization.toLocalizationMap S⁰ QS).epic_of_localizationMap
  ext x
  simp [IsLocalization.toLocalizationMap_toMonoidHom]

section Determinant

variable [Algebra QR QS] [Algebra R QS] [IsScalarTower R QR QS] [IsScalarTower R S QS]

/-- With compatible algebra structures on the total quotient rings, the multiplicative
extension is the ordinary determinant norm of the localized algebra. -/
theorem fractionNorm_eq_norm : fractionNorm R S QR QS = norm QR := by
  have : IsLocalization (algebraMapSubmonoid S R⁰) QS :=
    (IsFractionRing.isLocalization_algebraMapSubmonoid_iff R QS).mpr inferInstance
  exact fractionNorm_unique R S QR QS (norm QR) fun x =>
    norm_localization R (Rₘ := QR) (Sₘ := QS) R⁰ x

end Determinant

/-- Norm extensions compose in finite free towers, without choosing algebra structures
between the total quotient rings. -/
theorem fractionNorm_trans (T QT : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Module.Free S T] [Module.Finite S T]
    [Module.Free R T] [Module.Finite R T]
    [CommRing QT] [Algebra T QT] [IsFractionRing T QT] :
    (fractionNorm R S QR QS).comp (fractionNorm S T QS QT) = fractionNorm R T QR QT := by
  symm
  apply fractionNorm_unique
  intro x
  simp only [MonoidHom.comp_apply, fractionNorm_algebraMap, norm_norm]

end Algebra

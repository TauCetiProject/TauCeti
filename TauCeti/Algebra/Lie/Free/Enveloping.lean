/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Free.LowerCentral
public import TauCeti.Algebra.Lie.Presentation.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Cofinality
public import TauCeti.Algebra.Lie.UniversalEnveloping.Truncation

import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Injective

/-!
# Augmentation powers and the lower central series of a free Lie algebra

Let `F` be the free Lie algebra on a type `S` over a commutative ring `R`, graded by word length,
and let `J` be the augmentation ideal of its universal enveloping algebra `U(F)`. Since the free
generators have length one, the total-degree filtration of `U(F)` is exactly the filtration by the
powers of `J`: an element of `U(F)` lies in `J ^ N` exactly when its components of length below
`N` vanish.

When the canonical map `ι : F → U(F)` is injective, the Lie elements that `ι` sends into
`J ^ (c + 1)` are exactly the `c`-th term of the lower central series. Equivalently, the induced
map `F ⧸ lowerCentralSeries c → U(F) ⧸ J ^ (c + 1)` from the free nilpotent Lie algebra of class
at most `c` to the truncated enveloping algebra is injective. This is the uniqueness half of the
universal Baker–Campbell–Hausdorff element of class `c`: an element of `U(F) ⧸ J ^ (c + 1)` has
at most one preimage in the free nilpotent quotient. The image of that quotient consists of
nilpotent elements (`TauCeti.UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι`), so
when `R` is a `ℚ`-algebra the exponential `exp x` and the logarithm `log (1 + x)` of such an
element `x` are finite sums.

Injectivity of `ι` holds whenever `F` is free as an `R`-module
(`TauCeti.UniversalEnvelopingAlgebra.ι_injective`), in particular over every field, and also over
every commutative `ℚ`-algebra `R` via PBW symmetrization
(`TauCeti.UniversalEnvelopingAlgebra.ι_injective_of_algebra_rat`).

## Main results

* `TauCeti.FreeLieAlgebra.degreeFiltration_eq_augmentation_pow`: the word-length filtration of
  `U(F)` is the filtration by powers of the augmentation ideal.
* `TauCeti.FreeLieAlgebra.quotientEquivAlgOfEq_truncatedLieToU`: comparison between
  `truncatedLieToU` and `lowerCentralQuotientι`.
* `TauCeti.FreeLieAlgebra.mem_augmentation_pow_iff`: membership in `J ^ N` is the vanishing of
  every component of length below `N`.
* `TauCeti.FreeLieAlgebra.comap_augmentation_pow_ι` and
  `TauCeti.FreeLieAlgebra.comap_augmentation_pow_ι_of_algebra_rat`: if `ι` is injective (in
  particular over any commutative `ℚ`-algebra `R`), the preimage of `J ^ (c + 1)` is the
  `c`-th term of the lower central series.
* `TauCeti.FreeLieAlgebra.lowerCentralQuotientι_injective` and
  `TauCeti.FreeLieAlgebra.lowerCentralQuotientι_injective_of_algebra_rat`: if `ι` is injective (in
  particular over any commutative `ℚ`-algebra `R`), so is the induced map
  `TauCeti.UniversalEnvelopingAlgebra.lowerCentralQuotientι` from `F ⧸ lowerCentralSeries c` to
  `U(F) ⧸ J ^ (c + 1)`.

## Attribution

Adapted from `Mei/Algebra/Lie/Free/Enveloping.lean` and
`Mei/Algebra/Lie/UniversalEnveloping/GradedEmbedding.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0). Original copyright and author credit
are retained.
-/

public section

namespace TauCeti.FreeLieAlgebra

variable (R : Type*) [CommRing R] (S : Type*)

-- The canonical map `ι` is a Lie homomorphism into the commutator Lie algebra of `U(F)`.
attribute [local instance 100] LieRing.ofAssociativeRing

local notation "F" => _root_.FreeLieAlgebra R S
local notation "U" => _root_.UniversalEnvelopingAlgebra R F
local notation "J" => HopfIdeal.toIdeal (HopfIdeal.augmentation R U)
local notation "ℒ" => homogeneousSubmodule R S
local notation "𝓕" => UniversalEnvelopingAlgebra.degreeFiltration ℒ
  PositiveDegrees.naturals.degree (PositiveDegrees.naturals.eq_bot_of_degree_neg ℒ)

/-- The word-length filtration of the enveloping algebra of a free Lie algebra is the filtration
by powers of the augmentation ideal. -/
theorem degreeFiltration_eq_augmentation_pow (k : ℕ) : (𝓕).ideal k = J ^ k :=
  UniversalEnvelopingAlgebra.degreeFiltration_eq_augmentation_pow ℒ
    PositiveDegrees.naturals.degree (PositiveDegrees.naturals.eq_bot_of_degree_nonpos ℒ)
    (_root_.FreeLieAlgebra.of R) (fun _ => 1) (lieSpan_range_of_eq_top R S)
    (fun s => by simpa using word_mem_homogeneousSubmodule R (FreeMagma.of s))
    (fun _ => by simp [PositiveDegrees.naturals_degree]) k

/-- `truncatedLieToU` for `PositiveDegrees.naturals` agrees with `lowerCentralQuotientι` across the
identifications of degree ideals with lower central terms and filtration ideals with augmentation
powers. -/
theorem quotientEquivAlgOfEq_truncatedLieToU (c : ℕ)
    (z : PositiveDegrees.naturals.truncatedLie ℒ c) :
    Ideal.quotientEquivAlgOfEq R (degreeFiltration_eq_augmentation_pow R S (c + 1))
        (UniversalEnvelopingAlgebra.truncatedLieToU PositiveDegrees.naturals ℒ c z) =
      UniversalEnvelopingAlgebra.lowerCentralQuotientι R F c
        (((PositiveDegrees.naturals.degreeIdeal ℒ c).quotEquivOfEq _
          (naturals_degreeIdeal_eq_lowerCentralSeries R S c)) z) := by
  obtain ⟨x, rfl⟩ := (PositiveDegrees.naturals.degreeIdeal ℒ c).surjective_mkQ z
  simp [LieIdeal.mkQ_apply, LieIdeal.quotEquivOfEq_mk]

/-- An element of the enveloping algebra of a free Lie algebra lies in the `N`-th power of the
augmentation ideal exactly when its components of word length below `N` vanish. -/
theorem mem_augmentation_pow_iff {a : U} {N : ℕ} :
    a ∈ J ^ N ↔ ∀ n : ℕ, n < N →
      (DirectSum.decompose (UniversalEnvelopingAlgebra.homogeneousSubmodule ℒ) a n : U) = 0 := by
  rw [← degreeFiltration_eq_augmentation_pow,
    UniversalEnvelopingAlgebra.mem_degreeFiltration_ideal_iff]
  simp [PositiveDegrees.naturals_degree]

/-- If the canonical map into the enveloping algebra is injective, the Lie elements it sends into
the `(c + 1)`-st power of the augmentation ideal are exactly the `c`-th term of the lower central
series. -/
theorem comap_augmentation_pow_ι
    (hι : Function.Injective (_root_.UniversalEnvelopingAlgebra.ι R : F → U)) (c : ℕ) :
    ((J ^ (c + 1)).restrictScalars R).comap
        (_root_.UniversalEnvelopingAlgebra.ι R : F →ₗ⁅R⁆ U).toLinearMap =
      (LieModule.lowerCentralSeries R F F c).toSubmodule := by
  rw [← degreeFiltration_eq_augmentation_pow,
    UniversalEnvelopingAlgebra.comap_degreeFiltration_ι ℒ _ _ hι,
    ← PositiveDegrees.degreeSubmodule_eq_degreeTail,
    ← PositiveDegrees.degreeIdeal_toSubmodule,
    naturals_degreeIdeal_eq_lowerCentralSeries]

/-- If the canonical map into the enveloping algebra is injective, the free nilpotent Lie algebra
of class at most `c` embeds in the truncated enveloping algebra `U(F) ⧸ J ^ (c + 1)`. -/
theorem lowerCentralQuotientι_injective
    (hι : Function.Injective (_root_.UniversalEnvelopingAlgebra.ι R : F → U)) (c : ℕ) :
    Function.Injective (UniversalEnvelopingAlgebra.lowerCentralQuotientι R F c) :=
  (UniversalEnvelopingAlgebra.lowerCentralQuotientι_injective_iff R F c).mpr
    (comap_augmentation_pow_ι R S hι c).le

section Rational

variable (R : Type*) [CommRing R] [Algebra ℚ R] (S : Type*)

/-- Over a commutative `ℚ`-algebra `R`, the preimage of the `(c + 1)`-st power of the
augmentation ideal under `ι R` is the `c`-th term of the lower central series. -/
theorem comap_augmentation_pow_ι_of_algebra_rat (c : ℕ) :
    (((HopfIdeal.augmentation R
          (_root_.UniversalEnvelopingAlgebra R (_root_.FreeLieAlgebra R S))).toIdeal ^
        (c + 1)).restrictScalars R).comap
      (_root_.UniversalEnvelopingAlgebra.ι R : _root_.FreeLieAlgebra R S →ₗ⁅R⁆
        _root_.UniversalEnvelopingAlgebra R (_root_.FreeLieAlgebra R S)).toLinearMap =
      (LieModule.lowerCentralSeries R (_root_.FreeLieAlgebra R S)
        (_root_.FreeLieAlgebra R S) c).toSubmodule :=
  comap_augmentation_pow_ι R S
    (UniversalEnvelopingAlgebra.ι_injective_of_algebra_rat R (_root_.FreeLieAlgebra R S)) c

/-- Over a commutative `ℚ`-algebra `R`, the free nilpotent Lie algebra of class at most `c`
embeds into the truncated enveloping algebra modulo the `(c + 1)`-st augmentation power. -/
theorem lowerCentralQuotientι_injective_of_algebra_rat (c : ℕ) :
    Function.Injective
      (UniversalEnvelopingAlgebra.lowerCentralQuotientι R (_root_.FreeLieAlgebra R S) c) :=
  lowerCentralQuotientι_injective R S
    (UniversalEnvelopingAlgebra.ι_injective_of_algebra_rat R (_root_.FreeLieAlgebra R S)) c

end Rational

end TauCeti.FreeLieAlgebra

/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Free.LowerCentral
public import TauCeti.Algebra.Lie.Presentation.Basic
public import TauCeti.Algebra.Lie.Quotient
public import TauCeti.Algebra.Lie.UniversalEnveloping.Cofinality

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
nilpotent elements, so their exponentials and logarithms are finite sums.

Injectivity of `ι` holds whenever `F` is free as an `R`-module
(`TauCeti.UniversalEnvelopingAlgebra.ι_injective`), in particular over every field.

## Main definitions

* `TauCeti.FreeLieAlgebra.quotientEnvelopingMap`: the Lie homomorphism
  `F ⧸ lowerCentralSeries c → U(F) ⧸ J ^ (c + 1)` induced by `ι`.

## Main results

* `TauCeti.FreeLieAlgebra.degreeFiltration_eq_augmentation_pow`: the word-length filtration of
  `U(F)` is the filtration by powers of the augmentation ideal.
* `TauCeti.FreeLieAlgebra.mem_augmentation_pow_iff`: membership in `J ^ N` is the vanishing of
  every component of length below `N`.
* `TauCeti.FreeLieAlgebra.comap_augmentation_pow_ι`: if `ι` is injective, the preimage of
  `J ^ (c + 1)` is the `c`-th term of the lower central series.
* `TauCeti.FreeLieAlgebra.quotientEnvelopingMap_injective`: if `ι` is injective, so is
  `quotientEnvelopingMap`.

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
local notation "δ" => Nat.castAddMonoidHom ℤ
local notation "𝓕" => UniversalEnvelopingAlgebra.degreeFiltration ℒ δ
  (fun n hn => absurd hn (not_lt.mpr (Int.natCast_nonneg n)))

/-- The word-length filtration of the enveloping algebra of a free Lie algebra is the filtration
by powers of the augmentation ideal. -/
theorem degreeFiltration_eq_augmentation_pow (k : ℕ) : (𝓕).ideal k = J ^ k := by
  have hpos : ∀ n, δ n ≤ 0 → ℒ n = ⊥ := fun n hn => by
    obtain rfl : n = 0 := by simpa using hn
    exact homogeneousSubmodule_zero R S
  refine le_antisymm ?_
    (UniversalEnvelopingAlgebra.augmentation_pow_le_degreeFiltration ℒ δ hpos k)
  rcases k with _ | k
  · simp
  · have h := UniversalEnvelopingAlgebra.degreeFiltration_le_augmentation_pow ℒ δ
      (fun n hn => absurd hn (not_lt.mpr (Int.natCast_nonneg n))) (_root_.FreeLieAlgebra.of R)
      (fun _ => 1) (lieSpan_range_of_eq_top R S)
      (fun s => by simpa using word_mem_homogeneousSubmodule R (FreeMagma.of s)) 1
      (fun _ => by simp) (k + 1)
    rwa [Nat.add_sub_cancel, one_mul] at h

/-- An element of the enveloping algebra of a free Lie algebra lies in the `N`-th power of the
augmentation ideal exactly when its components of word length below `N` vanish. -/
theorem mem_augmentation_pow_iff {a : U} {N : ℕ} :
    a ∈ J ^ N ↔ ∀ n : ℕ, n < N →
      (DirectSum.decompose (UniversalEnvelopingAlgebra.homogeneousSubmodule ℒ) a n : U) = 0 := by
  rw [← degreeFiltration_eq_augmentation_pow,
    UniversalEnvelopingAlgebra.mem_degreeFiltration_ideal_iff]
  simp

/-- If the canonical map into the enveloping algebra is injective, the Lie elements it sends into
the `(c + 1)`-st power of the augmentation ideal are exactly the `c`-th term of the lower central
series. -/
theorem comap_augmentation_pow_ι
    (hι : Function.Injective (_root_.UniversalEnvelopingAlgebra.ι R : F → U)) (c : ℕ) :
    ((J ^ (c + 1)).restrictScalars R).comap
        (_root_.UniversalEnvelopingAlgebra.ι R : F →ₗ⁅R⁆ U).toLinearMap =
      (LieModule.lowerCentralSeries R F F c).toSubmodule := by
  rw [← degreeFiltration_eq_augmentation_pow,
    UniversalEnvelopingAlgebra.comap_degreeFiltration_ι ℒ δ _ hι,
    lowerCentralSeries_toSubmodule_eq_iSup, DirectSum.degreeTail_def]
  refine iSup_congr fun n => iSup_congr_Prop ?_ fun _ => rfl
  simp only [Nat.coe_castAddMonoidHom]
  omega

/-- The Lie homomorphism `F ⧸ lowerCentralSeries c → U(F) ⧸ J ^ (c + 1)` induced by the canonical
map into the enveloping algebra, from the free nilpotent Lie algebra of class at most `c` to the
truncated enveloping algebra. -/
noncomputable def quotientEnvelopingMap (c : ℕ) :
    (F ⧸ LieModule.lowerCentralSeries R F F c) →ₗ⁅R⁆ U ⧸ J ^ (c + 1) :=
  LieIdeal.liftQ _ ((Ideal.Quotient.mkₐ R (J ^ (c + 1))).toLieHom.comp
      (_root_.UniversalEnvelopingAlgebra.ι R)) fun x hx => by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using
      UniversalEnvelopingAlgebra.ι_mem_augmentation_toIdeal_pow_of_mem_lowerCentralSeries R F hx

/-- The class of `x` maps to the class of its image under the canonical map. -/
@[simp]
theorem quotientEnvelopingMap_mk (c : ℕ) (x : F) :
    quotientEnvelopingMap R S c (LieSubmodule.Quotient.mk x) =
      Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι R x) := by
  simp [quotientEnvelopingMap]

/-- Every element in the image of `quotientEnvelopingMap` is nilpotent. -/
theorem isNilpotent_quotientEnvelopingMap (c : ℕ)
    (z : F ⧸ LieModule.lowerCentralSeries R F F c) :
    IsNilpotent (quotientEnvelopingMap R S c z) := by
  obtain ⟨z, rfl⟩ := LieIdeal.surjective_mkQ _ z
  refine ⟨c + 1, ?_⟩
  rw [LieIdeal.mkQ_apply, quotientEnvelopingMap_mk, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (HopfIdeal.mem_toIdeal.mpr
    (UniversalEnvelopingAlgebra.ι_mem_augmentation R F z)) _

/-- The maps `quotientEnvelopingMap` commute with the transitions to smaller nilpotency
classes. -/
theorem quotientEnvelopingMap_factor {c d : ℕ} (h : c ≤ d)
    (z : F ⧸ LieModule.lowerCentralSeries R F F d) :
    quotientEnvelopingMap R S c
        (LieIdeal.factor (LieModule.antitone_lowerCentralSeries R F F h) z) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))
        (quotientEnvelopingMap R S d z) := by
  obtain ⟨z, rfl⟩ := LieIdeal.surjective_mkQ _ z
  simp [LieIdeal.mkQ_apply, LieIdeal.factor_apply]

/-- If the canonical map into the enveloping algebra is injective, the free nilpotent Lie algebra
of class at most `c` embeds in the truncated enveloping algebra `U(F) ⧸ J ^ (c + 1)`. -/
theorem quotientEnvelopingMap_injective
    (hι : Function.Injective (_root_.UniversalEnvelopingAlgebra.ι R : F → U)) (c : ℕ) :
    Function.Injective (quotientEnvelopingMap R S c) := by
  refine LieIdeal.liftQ_injective _ _ _ fun x hx => ?_
  have hmem := SetLike.ext_iff.mp (comap_augmentation_pow_ι R S hι c) x
  simp only [Submodule.mem_comap, Submodule.restrictScalars_mem, LieHom.coe_toLinearMap,
    LieSubmodule.mem_toSubmodule] at hmem
  exact hmem.mp (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hx)

end TauCeti.FreeLieAlgebra

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.NumberField.FractionalIdeal
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.NumberTheory.NumberField.FractionalIdeal
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# Torsion of `K ⧸ R` by an ideal

Let `A` be an `R`-algebra, `N` an `R`-submodule of `A` and `I` an ideal of `R`. The class of
`x ∈ A` in `A ⧸ N` is killed by `I` exactly when `x a ∈ N` for every `a ∈ I`, that is when `x`
lies in the ideal quotient `N / I` (with `I` carried into `A` by `algebraMap`). So the
`I`-torsion of `A ⧸ N` is the image of `N / I`, and its size is the index of `N` in `N / I`.

For a domain `R` with fraction field `K` and `I ≠ 0`, taking `N = R` gives `1 / I = I⁻¹`: the
`I`-torsion of `K ⧸ R` is `I⁻¹ ⧸ R`, and it has `[I⁻¹ : R]` elements. For the ring of integers
`𝓞_E` of a number field `E` this index is `N(𝓞_E) / N(I⁻¹) = N(I)`
(`NumberField.relIndex_fractionalIdeal_eq_absNorm_div_absNorm`). For `I = 0` the torsion is all of
`E ⧸ 𝓞_E`, which is infinite because it contains the `P ^ k`-torsion for a maximal ideal `P` and
every `k`; so `Nat.card` gives `0 = N(0)` there too.

## Main results

* `Submodule.comap_mkQ_torsionBySet`: the classes in `A ⧸ N` killed by `I` are those of `N / I`.
* `Submodule.natCard_torsionBySet_quotient`: the `I`-torsion of `A ⧸ N` has `[N / I : N]`
  elements.
* `FractionalIdeal.comap_mkQ_torsionBySet_eq_inv`: the classes in `K ⧸ R` killed by `I ≠ 0` are
  those of `I⁻¹`.
* `FractionalIdeal.natCard_torsionBySet_quotient_one`: the `I`-torsion of `K ⧸ R` has
  `[I⁻¹ : R]` elements.
* `NumberField.natCard_torsionBySet_quotient_one`: the `I`-torsion of `E ⧸ 𝓞_E` has `N(I)`
  elements.
-/

public section

open scoped nonZeroDivisors

namespace Submodule

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **The `I`-torsion of `A ⧸ N`.** The class of `x` in `A ⧸ N` is killed by the ideal `I`
exactly when `x ∈ N / I`, the ideal quotient, with `I` carried into `A` by `algebraMap`. -/
theorem comap_mkQ_torsionBySet (N : Submodule R A) (I : Ideal R) :
    (torsionBySet R (A ⧸ N) I).comap N.mkQ = N / Submodule.map (Algebra.linearMap R A) I := by
  ext x
  rw [mem_comap, mkQ_apply, mem_torsionBySet_iff, mem_div_iff_forall_mul_mem]
  constructor
  · rintro h _ ⟨a, ha, rfl⟩
    rw [Algebra.linearMap_apply, mul_comm, ← Algebra.smul_def, ← Quotient.mk_eq_zero,
      Quotient.mk_smul]
    exact h ⟨a, ha⟩
  · rintro h ⟨a, ha⟩
    rw [← Quotient.mk_smul, Quotient.mk_eq_zero, Algebra.smul_def, mul_comm]
    exact h _ ⟨a, ha, rfl⟩

/-- **The size of the `I`-torsion of `A ⧸ N`** is the index of `N` in the ideal quotient
`N / I` (`Submodule.comap_mkQ_torsionBySet`). -/
theorem natCard_torsionBySet_quotient (N : Submodule R A) (I : Ideal R) :
    Nat.card (torsionBySet R (A ⧸ N) I) =
      N.toAddSubgroup.relIndex (N / Submodule.map (Algebra.linearMap R A) I).toAddSubgroup := by
  have hP := comap_mkQ_torsionBySet N I
  set P := N / Submodule.map (Algebra.linearMap R A) I
  -- the torsion is the image of `P` in `A ⧸ N`, that is `P ⧸ (N ∩ P)`
  have hrange : LinearMap.range (N.mkQ ∘ₗ P.subtype) = torsionBySet R (A ⧸ N) I := by
    rw [LinearMap.range_comp, range_subtype, ← hP, map_comap_eq_of_surjective N.mkQ_surjective]
  have hker : LinearMap.ker (N.mkQ ∘ₗ P.subtype) = N.comap P.subtype := by
    rw [LinearMap.ker_comp, ker_mkQ]
  rw [← hrange, ← Nat.card_congr (N.mkQ ∘ₗ P.subtype).quotKerEquivRange.toEquiv, hker,
    ← cardQuot_apply, cardQuot_eq_relIndex_map_subtype, map_comap_subtype]
  -- `(P ⊓ N).toAddSubgroup` is `P.toAddSubgroup ⊓ N.toAddSubgroup` by definition
  exact AddSubgroup.inf_relIndex_left (H := P.toAddSubgroup) (K := N.toAddSubgroup)

end Submodule

namespace FractionalIdeal

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The `I`-torsion of `K ⧸ R` is `I⁻¹ ⧸ R`.** For a nonzero ideal `I` of a domain `R` with
fraction field `K`, the class of `x` in `K ⧸ R` is killed by `I` exactly when `x ∈ I⁻¹`. -/
theorem comap_mkQ_torsionBySet_eq_inv {I : Ideal R} (hI : I ≠ ⊥) :
    (Submodule.torsionBySet R (K ⧸ (1 : Submodule R K)) I).comap (1 : Submodule R K).mkQ =
      ((I : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) := by
  rw [Submodule.comap_mkQ_torsionBySet, inv_eq, coeToSubmodule_div (coeIdeal_ne_zero.mpr hI),
    coeToSubmodule_one, coeToSubmodule_coeIdeal]
  rfl

/-- **The `I`-torsion of `K ⧸ R` has `[I⁻¹ : R]` elements**, for a nonzero ideal `I` of a domain
`R` with fraction field `K`. -/
theorem natCard_torsionBySet_quotient_one {I : Ideal R} (hI : I ≠ ⊥) :
    Nat.card (Submodule.torsionBySet R (K ⧸ (1 : Submodule R K)) I) =
      (1 : Submodule R K).toAddSubgroup.relIndex
        (((I : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K).toAddSubgroup := by
  rw [Submodule.natCard_torsionBySet_quotient, ← comap_mkQ_torsionBySet_eq_inv hI,
    Submodule.comap_mkQ_torsionBySet]

end FractionalIdeal

namespace NumberField

variable {E : Type*} [Field E] [NumberField E]

/-- For a nonzero ideal `I`, the `I`-torsion of `E ⧸ 𝓞_E` is `I⁻¹ ⧸ 𝓞_E`, whose index is
`N(𝓞_E) / N(I⁻¹) = N(I)`. -/
private theorem natCard_torsionBySet_quotient_one_of_ne_bot {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) :
    Nat.card (Submodule.torsionBySet (𝓞 E) (E ⧸ (1 : Submodule (𝓞 E) E)) I) =
      Ideal.absNorm I := by
  have hI' : (I : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hI
  have hle : ((1 : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) ≤
      ((Units.mk0 _ (inv_ne_zero hI')) : FractionalIdeal (𝓞 E)⁰ E) := by
    simpa using FractionalIdeal.inv_anti_mono hI' FractionalIdeal.coeIdeal_le_one
  have h := relIndex_fractionalIdeal_eq_absNorm_div_absNorm hle
  rw [Units.val_one, Units.val_mk0, FractionalIdeal.coeToSubmodule_one, map_one, map_inv₀,
    FractionalIdeal.coeIdeal_absNorm, one_div, inv_inv] at h
  rw [FractionalIdeal.natCard_torsionBySet_quotient_one hI]
  exact_mod_cast h

/-- `E ⧸ 𝓞_E` is infinite: it contains the `P ^ k`-torsion, with `N(P) ^ k` elements, for a
maximal ideal `P` and every `k`. -/
private theorem natCard_torsionBySet_quotient_one_bot :
    Nat.card (Submodule.torsionBySet (𝓞 E) (E ⧸ (1 : Submodule (𝓞 E) E))
      ((⊥ : Ideal (𝓞 E)) : Set (𝓞 E))) = 0 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have h1 : 1 < Ideal.absNorm P := by
    have := Ideal.absNorm_eq_zero_iff.not.mpr hP0
    have := Ideal.absNorm_eq_one_iff.not.mpr hP.ne_top
    omega
  rw [Nat.card_eq_zero]
  refine .inr (not_finite_iff_infinite.mp fun hfin ↦ ?_)
  set N := Nat.card (Submodule.torsionBySet (𝓞 E) (E ⧸ (1 : Submodule (𝓞 E) E))
    ((⊥ : Ideal (𝓞 E)) : Set (𝓞 E)))
  have hle := Submodule.torsionBySet_le_torsionBySet_of_subset (R := 𝓞 E)
    (M := E ⧸ (1 : Submodule (𝓞 E) E)) (SetLike.coe_subset_coe.mpr (bot_le (a := P ^ N)))
  have hcard := Nat.card_le_card_of_injective _ (Submodule.inclusion_injective hle)
  rw [natCard_torsionBySet_quotient_one_of_ne_bot (pow_ne_zero N hP0), map_pow] at hcard
  exact (Nat.lt_pow_self h1).not_ge hcard

/-- **The `I`-torsion of `E ⧸ 𝓞_E` has `N(I)` elements**, for an ideal `I` of the ring of
integers of a number field `E`. For `I ≠ 0` it is `I⁻¹ ⧸ 𝓞_E`
(`FractionalIdeal.natCard_torsionBySet_quotient_one`), whose index is
`N(𝓞_E) / N(I⁻¹) = N(I)` (`NumberField.relIndex_fractionalIdeal_eq_absNorm_div_absNorm`). For
`I = 0` both sides are `0`: the whole of `E ⧸ 𝓞_E` is infinite. -/
theorem natCard_torsionBySet_quotient_one (I : Ideal (𝓞 E)) :
    Nat.card (Submodule.torsionBySet (𝓞 E) (E ⧸ (1 : Submodule (𝓞 E) E)) I) =
      Ideal.absNorm I := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · rw [Ideal.absNorm_bot, natCard_torsionBySet_quotient_one_bot]
  · exact natCard_torsionBySet_quotient_one_of_ne_bot hI

end NumberField

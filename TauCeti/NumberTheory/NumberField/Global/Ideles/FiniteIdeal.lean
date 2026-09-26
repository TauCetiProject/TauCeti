/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup

/-!
# Fractional ideals of ideles

This file relates the fractional ideal of an idele's finite component to its valuations at
finite places. It also gives a norm-one idele representative of every ideal class.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  IsDedekindDomain.FiniteAdeleRing NumberField NumberField.InfinitePlace
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The fractional ideal of an idele's finite component is trivial exactly when the idele is a
unit at every finite place. -/
-- The finite-adele and coordinate simp lemmas already prove this equivalence.
theorem toFractionalIdeal_toFiniteIdele_eq_one_iff {x : IdeleGroup R K} :
    toFractionalIdeal (IdeleGroup.toFiniteIdele R K x) = 1 ↔
      ∀ v : HeightOneSpectrum R, Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
  simp only [toFractionalIdeal_eq_one_iff, adicOrd_eq_zero_iff, IdeleGroup.coe_toFiniteIdele,
    HeightOneSpectrum.coe_ideleFiniteCoord]

end TauCeti.GlobalNumberFields

namespace ClassGroup

open TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- Every ideal class is the class of the finite part of an idele of norm one. -/
theorem exists_ideleNorm_eq_one_and_toClassGroup_eq (c : ClassGroup (𝓞 K)) :
    ∃ b : IdeleGroup (𝓞 K) K, ideleNorm b = 1 ∧
      FiniteAdeleRing.toClassGroup (𝓞 K) K (IdeleGroup.toFiniteIdele (𝓞 K) K b) = c := by
  obtain ⟨f, hf⟩ := FiniteAdeleRing.toClassGroup_surjective (R := 𝓞 K) (K := K) c
  -- Correct the norm at one infinite place, which does not change the finite part.
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain ⟨x, hx⟩ := exists_infiniteCompletionNormalizedAbsValue_eq w
    ((ideleNorm (IdeleGroup.ofFiniteIdele (𝓞 K) K f))⁻¹ : NNReal).coe_nonneg
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact Units.ne_zero _ (by exact_mod_cast hx.symm)
  refine ⟨IdeleGroup.ofFiniteIdele (𝓞 K) K f * IdeleGroup.ofCompletion (𝓞 K) K w (Units.mk0 x hx0),
    ?_, ?_⟩
  · ext
    rw [map_mul, Units.val_mul, NNReal.coe_mul, coe_ideleNorm_ofCompletion, Units.val_mk0, hx]
    simp
  · rw [map_mul, map_mul, IdeleGroup.toFiniteIdele_ofFiniteIdele,
      IdeleGroup.toFiniteIdele_ofCompletion, map_one, mul_one, hf]

end ClassGroup

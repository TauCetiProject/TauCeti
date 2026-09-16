/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.RingTheory.Unramified.Locus
public import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.NumberTheory.RamificationInertia.Splitting
import TauCeti.RingTheory.Ideal.PrimesOver

/-!
# Complete splitting and unramifiedness in composita and Galois closures

Let `M / K` be a finite Galois extension of number fields with group `G`, let `E` be an
intermediate field, and let `𝔭` be a prime of `𝓞 K`. Say that `𝔭` *splits completely* in `E`
when it has `[E : K]` primes above it in `𝓞 E`. This file proves

* `𝔭` splits completely in `E` exactly when every decomposition group `D(Q) ≤ G`, for `Q` a prime
  of `𝓞 M` above `𝔭`, fixes `E` pointwise;
* `𝔭` is unramified in `E` exactly when every inertia group `I(Q)` fixes `E` pointwise.

Both conditions are about the fixing subgroup of `E`, and the Galois correspondence turns a join
of fields into a meet of fixing subgroups. So both properties pass to composita: `𝔭` splits
completely (or is unramified) in `E₁ ⊔ E₂` exactly when it does in `E₁` and in `E₂`, and likewise
for an arbitrary join. Conjugating `E` by `σ ∈ G` conjugates its fixing subgroup, while the
decomposition and inertia groups over `𝔭` are permuted among themselves by the same conjugation;
so neither property changes. As the normal closure of `E` in `M` is the join of the conjugates of
`E`, the prime `𝔭` splits completely (or is unramified) in `E` exactly when it does in the normal
closure. When `M` is itself the normal closure of `E`, this compares `E` with `M` directly.

The decomposition-group criterion rests on the local degree formula
`e(Q ∩ E / 𝔭) f(Q ∩ E / 𝔭) = [D(Q) : D(Q) ∩ Gal(M/E)]`, together with the non-Galois count
criterion "`[E : K]` primes above `𝔭` exactly when `e = f = 1` at each". The inertia-group
criterion rests likewise on `e(Q ∩ E / 𝔭) = [I(Q) : I(Q) ∩ Gal(M/E)]`.

## Main results

* `Ideal.ncard_primesOver_eq_finrank_iff_forall_stabilizer_le`: `𝔭` splits completely in `E`
  iff every decomposition group above `𝔭` lies in `Gal(M/E)`.
* `Ideal.ncard_primesOver_eq_finrank_iff_forall_stabilizer_eq_bot`: `𝔭` splits completely in `M`
  iff every decomposition group above `𝔭` is trivial.
* `Ideal.ncard_primesOver_sup_eq_finrank_iff`, `Ideal.ncard_primesOver_iSup_eq_finrank_iff`:
  complete splitting in a compositum.
* `Ideal.ncard_primesOver_map_eq_finrank_iff`: complete splitting in a conjugate field.
* `Ideal.ncard_primesOver_normalClosure_eq_finrank_iff`: `𝔭` splits completely in `E` iff it
  splits completely in the normal closure of `E`.
* `Ideal.ncard_primesOver_eq_finrank_iff_of_normalClosure_eq_top`: the same, when `M` is the
  normal closure of `E`.
* `Ideal.isUnramifiedIn_iff_forall_inertia_le`: `𝔭` is unramified in `E` iff every inertia group
  above `𝔭` lies in `Gal(M/E)`.
* `Ideal.isUnramifiedIn_sup_iff`, `Ideal.isUnramifiedIn_iSup_iff`,
  `Ideal.isUnramifiedIn_map_iff`, `Ideal.isUnramifiedIn_normalClosure_iff`: the same four
  consequences for unramifiedness.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9, Exercise 4.
-/

public section

open IntermediateField Module

open scoped NumberField Pointwise

namespace Ideal

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

/-! ### Complete splitting -/

/-- **Complete splitting through decomposition groups.** For `M / K` Galois and `E` an
intermediate field, a prime `p` of `𝓞 K` has `[E : K]` primes above it in `𝓞 E` exactly when the
decomposition group of every prime of `𝓞 M` above `p` fixes `E` pointwise. -/
theorem ncard_primesOver_eq_finrank_iff_forall_stabilizer_le (p : Ideal (𝓞 K)) [p.IsPrime]
    (E : IntermediateField K M) :
    (p.primesOver (𝓞 E)).ncard = finrank K E ↔
      ∀ Q ∈ p.primesOver (𝓞 M), MulAction.stabilizer (M ≃ₐ[K] M) Q ≤ E.fixingSubgroup := by
  obtain ⟨H, rfl⟩ : ∃ H, fixedField H = E := ⟨_, IsGalois.fixedField_fixingSubgroup E⟩
  rw [fixingSubgroup_fixedField, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 (fixedField H)),
    TauCeti.RamificationInertia.ncard_primesOver_eq_finrank_iff_forall]
  -- at each prime, `e = f = 1` says the index `[D(Q) : D(Q) ∩ H]` is one
  simp_rw [← mul_eq_one, ← Subgroup.relIndex_eq_one]
  refine ⟨fun h Q hQ ↦ ?_, fun h P hP ↦ ?_⟩
  · have := hQ.1
    rw [← ramificationIdx_mul_inertiaDeg_under_fixedField_eq_relIndex]
    exact h _ (under_mem_primesOver hQ)
  · obtain ⟨Q, hQ, rfl⟩ := exists_mem_primesOver_under_eq (B := 𝓞 M) hP
    have := hQ.1
    rw [ramificationIdx_mul_inertiaDeg_under_fixedField_eq_relIndex]
    exact h Q hQ

/-- **Complete splitting in a Galois extension.** For `M / K` Galois, a prime `p` of `𝓞 K` has
`[M : K]` primes above it exactly when the decomposition group of every prime above it is
trivial. -/
theorem ncard_primesOver_eq_finrank_iff_forall_stabilizer_eq_bot (p : Ideal (𝓞 K))
    [p.IsPrime] :
    (p.primesOver (𝓞 M)).ncard = finrank K M ↔
      ∀ Q ∈ p.primesOver (𝓞 M), MulAction.stabilizer (M ≃ₐ[K] M) Q = ⊥ := by
  rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 M) M,
    TauCeti.RamificationInertia.ncard_primesOver_eq_finrank_iff_forall]
  refine forall₂_congr fun Q ⟨_, _⟩ ↦ ?_
  -- the decomposition group of `Q` has order `e * f`
  rw [← mul_eq_one, ← Subgroup.card_eq_one, Ideal.card_stabilizer_eq p Q,
    Ideal.ramificationIdxIn_eq_ramificationIdx p Q (M ≃ₐ[K] M),
    Ideal.inertiaDegIn_eq_inertiaDeg p Q (M ≃ₐ[K] M)]

/-- **Complete splitting in a compositum.** A prime `p` of `𝓞 K` splits completely in `E₁ ⊔ E₂`
exactly when it splits completely in `E₁` and in `E₂`. -/
theorem ncard_primesOver_sup_eq_finrank_iff (p : Ideal (𝓞 K)) [p.IsPrime]
    (E₁ E₂ : IntermediateField K M) :
    (p.primesOver (𝓞 ↥(E₁ ⊔ E₂))).ncard = finrank K ↥(E₁ ⊔ E₂) ↔
      (p.primesOver (𝓞 E₁)).ncard = finrank K E₁ ∧
        (p.primesOver (𝓞 E₂)).ncard = finrank K E₂ := by
  simp only [ncard_primesOver_eq_finrank_iff_forall_stabilizer_le, fixingSubgroup_sup,
    le_inf_iff, ← forall_and]

/-- **Complete splitting in an arbitrary compositum.** A prime `p` of `𝓞 K` splits completely in
`⨆ i, E i` exactly when it splits completely in every `E i`. -/
theorem ncard_primesOver_iSup_eq_finrank_iff (p : Ideal (𝓞 K)) [p.IsPrime]
    {ι : Sort*} (E : ι → IntermediateField K M) :
    (p.primesOver (𝓞 ↥(⨆ i, E i))).ncard = finrank K ↥(⨆ i, E i) ↔
      ∀ i, (p.primesOver (𝓞 (E i))).ncard = finrank K (E i) := by
  simp only [ncard_primesOver_eq_finrank_iff_forall_stabilizer_le, fixingSubgroup_iSup,
    le_iInf_iff]
  exact ⟨fun h i Q hQ ↦ h Q hQ i, fun h Q hQ i ↦ h i Q hQ⟩

/-- **Complete splitting in a conjugate field.** A prime `p` of `𝓞 K` splits completely in
`σ E` exactly when it splits completely in `E`. -/
theorem ncard_primesOver_map_eq_finrank_iff (p : Ideal (𝓞 K)) [p.IsPrime]
    (E : IntermediateField K M) (σ : M ≃ₐ[K] M) :
    (p.primesOver (𝓞 ↥(E.map (σ : M →ₐ[K] M)))).ncard = finrank K ↥(E.map (σ : M →ₐ[K] M)) ↔
      (p.primesOver (𝓞 E)).ncard = finrank K E := by
  obtain ⟨H, rfl⟩ : ∃ H, fixedField H = E := ⟨_, IsGalois.fixedField_fixingSubgroup E⟩
  rw [← H.fixedField_map_conj σ, ncard_primesOver_eq_finrank_iff_forall_stabilizer_le,
    ncard_primesOver_eq_finrank_iff_forall_stabilizer_le, fixingSubgroup_fixedField,
    fixingSubgroup_fixedField]
  -- `D(σ • Q) = σ D(Q) σ⁻¹`, and `σ` permutes the primes above `p`
  refine ⟨fun h Q hQ ↦ ?_, fun h Q hQ ↦ ?_⟩
  · have := h _ (smul_mem_primesOver σ hQ)
    rwa [MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
      Subgroup.map_le_map_iff_of_injective (MulAut.conj σ).injective] at this
  · rw [← smul_inv_smul σ Q, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact Subgroup.map_mono (h _ (smul_mem_primesOver σ⁻¹ hQ))

/-- **Complete splitting in the normal closure.** A prime `p` of `𝓞 K` splits completely in an
intermediate field `E` of `M / K` exactly when it splits completely in the normal closure of `E`
in `M`. -/
theorem ncard_primesOver_normalClosure_eq_finrank_iff (p : Ideal (𝓞 K)) [p.IsPrime]
    (E : IntermediateField K M) :
    (p.primesOver (𝓞 (normalClosure K E M))).ncard = finrank K (normalClosure K E M) ↔
      (p.primesOver (𝓞 E)).ncard = finrank K E := by
  rw [normalClosure_def'' E, ncard_primesOver_iSup_eq_finrank_iff]
  simp only [ncard_primesOver_map_eq_finrank_iff, forall_const]

/-- **Complete splitting in a field and in its Galois closure.** If `M` is the normal closure of
the intermediate field `E`, a prime `p` of `𝓞 K` splits completely in `E` exactly when it splits
completely in `M`. -/
theorem ncard_primesOver_eq_finrank_iff_of_normalClosure_eq_top (p : Ideal (𝓞 K)) [p.IsPrime]
    {E : IntermediateField K M} (hE : normalClosure K E M = ⊤) :
    (p.primesOver (𝓞 E)).ncard = finrank K E ↔
      (p.primesOver (𝓞 M)).ncard = finrank K M := by
  rw [← ncard_primesOver_normalClosure_eq_finrank_iff,
    ncard_primesOver_eq_finrank_iff_forall_stabilizer_le, hE, fixingSubgroup_top,
    ncard_primesOver_eq_finrank_iff_forall_stabilizer_eq_bot]
  simp only [le_bot_iff]

/-! ### Unramifiedness -/

/-- **Unramifiedness through inertia groups.** For `M / K` Galois and `E` an intermediate field,
a prime `p` of `𝓞 K` is unramified in `E` exactly when the inertia group of every prime of `𝓞 M`
above `p` fixes `E` pointwise. -/
theorem isUnramifiedIn_iff_forall_inertia_le (p : Ideal (𝓞 K)) (E : IntermediateField K M) :
    Algebra.IsUnramifiedIn (𝓞 E) p ↔
      ∀ Q ∈ p.primesOver (𝓞 M), Q.inertia (M ≃ₐ[K] M) ≤ E.fixingSubgroup := by
  obtain ⟨H, rfl⟩ : ∃ H, fixedField H = E := ⟨_, IsGalois.fixedField_fixingSubgroup E⟩
  rw [fixingSubgroup_fixedField, Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  -- at each prime, `e = 1` says the index `[I(Q) : I(Q) ∩ H]` is one
  simp_rw [← Subgroup.relIndex_eq_one]
  refine ⟨fun h Q hQ ↦ ?_, fun h P _ hP ↦ ?_⟩
  · have := hQ.1
    rw [← ramificationIdx_under_fixedField_eq_relIndex]
    exact h _ (under_mem_primesOver hQ).2
  · obtain ⟨Q, hQ, rfl⟩ := exists_mem_primesOver_under_eq (B := 𝓞 M) (p := p) ⟨inferInstance, hP⟩
    have := hQ.1
    rw [ramificationIdx_under_fixedField_eq_relIndex]
    exact h Q hQ

/-- **Unramifiedness in a compositum.** A prime `p` of `𝓞 K` is unramified in `E₁ ⊔ E₂` exactly
when it is unramified in `E₁` and in `E₂`. -/
theorem isUnramifiedIn_sup_iff (p : Ideal (𝓞 K)) (E₁ E₂ : IntermediateField K M) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E₁ ⊔ E₂)) p ↔
      Algebra.IsUnramifiedIn (𝓞 E₁) p ∧ Algebra.IsUnramifiedIn (𝓞 E₂) p := by
  simp only [isUnramifiedIn_iff_forall_inertia_le, fixingSubgroup_sup, le_inf_iff, ← forall_and]

/-- **Unramifiedness in an arbitrary compositum.** A prime `p` of `𝓞 K` is unramified in
`⨆ i, E i` exactly when it is unramified in every `E i`. -/
theorem isUnramifiedIn_iSup_iff (p : Ideal (𝓞 K)) {ι : Sort*} (E : ι → IntermediateField K M) :
    Algebra.IsUnramifiedIn (𝓞 ↥(⨆ i, E i)) p ↔ ∀ i, Algebra.IsUnramifiedIn (𝓞 (E i)) p := by
  simp only [isUnramifiedIn_iff_forall_inertia_le, fixingSubgroup_iSup, le_iInf_iff]
  exact ⟨fun h i Q hQ ↦ h Q hQ i, fun h Q hQ i ↦ h i Q hQ⟩

/-- **Unramifiedness in a conjugate field.** A prime `p` of `𝓞 K` is unramified in `σ E` exactly
when it is unramified in `E`. -/
theorem isUnramifiedIn_map_iff (p : Ideal (𝓞 K)) (E : IntermediateField K M) (σ : M ≃ₐ[K] M) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E.map (σ : M →ₐ[K] M))) p ↔ Algebra.IsUnramifiedIn (𝓞 E) p := by
  obtain ⟨H, rfl⟩ : ∃ H, fixedField H = E := ⟨_, IsGalois.fixedField_fixingSubgroup E⟩
  rw [← H.fixedField_map_conj σ, isUnramifiedIn_iff_forall_inertia_le,
    isUnramifiedIn_iff_forall_inertia_le, fixingSubgroup_fixedField, fixingSubgroup_fixedField]
  -- `I(σ • Q) = σ I(Q) σ⁻¹`, and `σ` permutes the primes above `p`
  refine ⟨fun h Q hQ ↦ ?_, fun h Q hQ ↦ ?_⟩
  · have := h _ (smul_mem_primesOver σ hQ)
    rwa [Ideal.inertia_smul,
      Subgroup.map_le_map_iff_of_injective (MulAut.conj σ).injective] at this
  · rw [← smul_inv_smul σ Q, Ideal.inertia_smul]
    exact Subgroup.map_mono (h _ (smul_mem_primesOver σ⁻¹ hQ))

/-- **Unramifiedness in the normal closure.** A prime `p` of `𝓞 K` is unramified in an
intermediate field `E` of `M / K` exactly when it is unramified in the normal closure of `E`
in `M`. -/
theorem isUnramifiedIn_normalClosure_iff (p : Ideal (𝓞 K)) (E : IntermediateField K M) :
    Algebra.IsUnramifiedIn (𝓞 (normalClosure K E M)) p ↔ Algebra.IsUnramifiedIn (𝓞 E) p := by
  rw [normalClosure_def'' E, isUnramifiedIn_iSup_iff]
  simp only [isUnramifiedIn_map_iff, forall_const]

end Ideal

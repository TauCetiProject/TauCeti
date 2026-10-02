/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Basic
import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia

/-!
# The double coset law for special subgroups

Let `M / K` be a finite Galois extension of number fields with group `G`, let `Q` be a prime of
`𝓞 M` above a prime `p` of `𝓞 K`, with decomposition group `D`, and let `H` be a subgroup of `G`
with fixed field `E = M ^ H`. The double coset law (`Ideal.doubleCosetQuotientEquivPrimesOver`)
indexes the primes of `𝓞 E` above `p` by `H \ G / D`, the class of `σ` naming `σ Q ∩ 𝓞 E`.
This file reads the law off at the subgroups where the double cosets are explicit.

* **One prime.** `p` has a single prime above it in `E` exactly when `H D = G`, since then
  `H \ G / D` is the identity class alone. This covers `H = G`, where `E = K`, and the case
  `D = G` of a prime `p` with a single prime above it in `M`, for instance an inert prime: then
  `p` has a single prime above it in every subfield.
* **`H = 1`.** Then `E = M` and `1 \ G / D` is `G / D`, so the law recovers the Galois count
  `g = [G : D]` of the primes of `𝓞 M` above `p`.
* **`H = D`.** Then `E` is the decomposition field of `Q`. The double cosets `D \ G / D` are not
  a singleton in general, and only the identity double coset is special: it names
  `Q ∩ 𝓞 E`, which has ramification index `1` and residue degree `1` over `p`, and `Q` is the
  only prime of `𝓞 M` above it. Both facts come out of the double coset law itself:
  `e · f = [D : H ∩ D]` is `1` for `H = D`, and the primes of `𝓞 M` with the same contraction
  to `𝓞 E` as `Q` form the `D`-orbit of `Q`, which is `{Q}`. These are the double-coset
  counterparts of the Hilbert-theory statements
  `TauCeti.IsDecompositionField.ramificationIdx_under_eq_one`,
  `TauCeti.IsDecompositionField.inertiaDeg_under_eq_one` and
  `IsDecompositionField.primesOver_eq_singleton`, which are stated for an abstract
  decomposition field and a maximal ideal; here `Q` is only assumed prime.

## Main results

* `Ideal.doubleCosetQuotientEquivPrimesOver_mk_one`: the identity double coset names
  `Q ∩ 𝓞 E`.
* `Ideal.card_primesOver_fixedField_eq_one_iff`: a single prime above `p` in `E` exactly when
  `H D = G`.
* `Ideal.card_primesOver_fixedField_top` and
  `Ideal.card_primesOver_fixedField_eq_one_of_stabilizer_eq_top`: the cases `H = G` and `D = G`.
* `Ideal.card_primesOver_fixedField_bot_eq_index`: for `H = 1` the count is `[G : D]`.
* `Ideal.ramificationIdx_doubleCosetQuotientEquivPrimesOver_stabilizer_mk_one`,
  `Ideal.inertiaDeg_doubleCosetQuotientEquivPrimesOver_stabilizer_mk_one` and
  `Ideal.primesOver_doubleCosetQuotientEquivPrimesOver_stabilizer_mk_one`: for `H = D`, the
  prime named by the identity double coset has `e = f = 1` over `p`, and `Q` is the only prime
  above it.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
* G. J. Janusz, *Algebraic Number Fields*, Chapter I.
-/

public section

open IntermediateField MulAction NumberField

open scoped NumberField Pointwise

namespace Ideal

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (p : Ideal (𝓞 K)) (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver p]

/-- The double coset law sends the identity double coset of `H \ G / D` to the contraction
`Q ∩ 𝓞 (M ^ H)`. -/
theorem doubleCosetQuotientEquivPrimesOver_mk_one (H : Subgroup (M ≃ₐ[K] M)) :
    (doubleCosetQuotientEquivPrimesOver p Q H (DoubleCoset.mk H _ 1) :
        Ideal (𝓞 ↥(fixedField H))) = Q.under (𝓞 ↥(fixedField H)) := by
  rw [doubleCosetQuotientEquivPrimesOver_mk, one_smul]

/-- **A single prime above `p` in a subfield.** For a subgroup `H` of `G = Gal(M/K)` and the
decomposition group `D` of a prime `Q` of `𝓞 M` above `p`, there is exactly one prime of
`𝓞 (M ^ H)` above `p` if and only if `H D = G`. -/
theorem card_primesOver_fixedField_eq_one_iff (H : Subgroup (M ≃ₐ[K] M)) :
    Nat.card (p.primesOver (𝓞 ↥(fixedField H))) = 1 ↔
      (H : Set (M ≃ₐ[K] M)) * (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M)) = Set.univ := by
  rw [← card_doubleCosetQuotient_eq_card_primesOver p Q H, Nat.card_eq_one_iff_unique,
    TauCeti.subsingleton_doubleCosetQuotient_iff]
  exact and_iff_left ⟨DoubleCoset.mk H _ 1⟩

/-- **A prime with a single prime above it in `M` has a single prime above it in every
subfield.** If the decomposition group of `Q` is the whole Galois group, as for an inert prime,
then `p` has exactly one prime above it in `M ^ H` for every subgroup `H`. -/
theorem card_primesOver_fixedField_eq_one_of_stabilizer_eq_top
    (hD : stabilizer (M ≃ₐ[K] M) Q = ⊤) (H : Subgroup (M ≃ₐ[K] M)) :
    Nat.card (p.primesOver (𝓞 ↥(fixedField H))) = 1 :=
  (card_primesOver_fixedField_eq_one_iff p Q H).2 <| Set.eq_univ_of_forall fun σ ↦
    Set.mem_mul.2 ⟨1, one_mem H, σ, hD ▸ Subgroup.mem_top σ, one_mul σ⟩

/-- **The double coset law for `H = 1` is the Galois count.** The fixed field of the trivial
subgroup is `M` itself, and the primes of its ring of integers above `p` are counted by the
index `[G : D]` of the decomposition group of `Q`. -/
theorem card_primesOver_fixedField_bot_eq_index :
    Nat.card (p.primesOver (𝓞 ↥(fixedField (⊥ : Subgroup (M ≃ₐ[K] M))))) =
      (stabilizer (M ≃ₐ[K] M) Q).index := by
  rw [← card_doubleCosetQuotient_eq_card_primesOver p Q ⊥, DoubleCoset.left_bot_eq_left_quot,
    Subgroup.index_eq_card]

/-- **The double coset law for `H = G`.** The fixed field of the whole Galois group is `K`, and
a prime `p` of `𝓞 K` has exactly one prime above it there. -/
theorem card_primesOver_fixedField_top [p.IsPrime] :
    Nat.card (p.primesOver (𝓞 ↥(fixedField (⊤ : Subgroup (M ≃ₐ[K] M))))) = 1 := by
  obtain ⟨⟨R, _, _⟩⟩ := p.nonempty_primesOver (S := 𝓞 M)
  exact (card_primesOver_fixedField_eq_one_iff p R ⊤).2 <| Set.eq_univ_of_forall fun σ ↦
    Set.mem_mul.2 ⟨σ, Subgroup.mem_top σ, 1, one_mem _, mul_one σ⟩

/-- The contraction of `Q` to the decomposition field has `e · f = [D : D] = 1` over the base. -/
private theorem ramificationIdx_mul_inertiaDeg_under_fixedField_stabilizer :
    (Q.under (𝓞 ↥(fixedField (stabilizer (M ≃ₐ[K] M) Q)))).ramificationIdx (𝓞 K)
        * (Q.under (𝓞 ↥(fixedField (stabilizer (M ≃ₐ[K] M) Q)))).inertiaDeg (𝓞 K) = 1 := by
  rw [ramificationIdx_mul_inertiaDeg_under_fixedField_eq_relIndex, Subgroup.relIndex_self]

/-- **The identity double coset of `D \ G / D` names an unramified prime.** For `D` the
decomposition group of `Q`, the prime of the decomposition field `M ^ D` named by the identity
double coset, namely `Q ∩ 𝓞 (M ^ D)`, has ramification index `1` over `p`. -/
theorem ramificationIdx_doubleCosetQuotientEquivPrimesOver_stabilizer_mk_one :
    (doubleCosetQuotientEquivPrimesOver p Q (stabilizer (M ≃ₐ[K] M) Q) (DoubleCoset.mk _ _ 1) :
        Ideal (𝓞 ↥(fixedField (stabilizer (M ≃ₐ[K] M) Q)))).ramificationIdx (𝓞 K) = 1 := by
  rw [doubleCosetQuotientEquivPrimesOver_mk_one]
  exact (mul_eq_one.1 (ramificationIdx_mul_inertiaDeg_under_fixedField_stabilizer Q)).1

/-- **The identity double coset of `D \ G / D` names a prime of residue degree one.** For `D`
the decomposition group of `Q`, the prime of the decomposition field `M ^ D` named by the
identity double coset, namely `Q ∩ 𝓞 (M ^ D)`, has residue degree `1` over `p`. -/
theorem inertiaDeg_doubleCosetQuotientEquivPrimesOver_stabilizer_mk_one :
    (doubleCosetQuotientEquivPrimesOver p Q (stabilizer (M ≃ₐ[K] M) Q) (DoubleCoset.mk _ _ 1) :
        Ideal (𝓞 ↥(fixedField (stabilizer (M ≃ₐ[K] M) Q)))).inertiaDeg (𝓞 K) = 1 := by
  rw [doubleCosetQuotientEquivPrimesOver_mk_one]
  exact (mul_eq_one.1 (ramificationIdx_mul_inertiaDeg_under_fixedField_stabilizer Q)).2

/-- **`Q` is the only prime above the prime named by the identity double coset of
`D \ G / D`.** For `D` the decomposition group of `Q`, the only prime of `𝓞 M` above
`Q ∩ 𝓞 (M ^ D)` is `Q` itself. -/
theorem primesOver_doubleCosetQuotientEquivPrimesOver_stabilizer_mk_one :
    (doubleCosetQuotientEquivPrimesOver p Q (stabilizer (M ≃ₐ[K] M) Q) (DoubleCoset.mk _ _ 1) :
        Ideal (𝓞 ↥(fixedField (stabilizer (M ≃ₐ[K] M) Q)))).primesOver (𝓞 M) = {Q} := by
  rw [doubleCosetQuotientEquivPrimesOver_mk_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rintro R ⟨_, hR⟩
  -- A prime with the same contraction as `Q` is a `D`-translate of `Q`, hence `Q` itself.
  obtain ⟨d, rfl⟩ := mem_orbit_iff.1 ((under_fixedField_eq_iff_mem_orbit R Q _).1 hR.over.symm)
  rw [Subgroup.smul_def]
  exact mem_stabilizer_iff.1 d.2

end Ideal

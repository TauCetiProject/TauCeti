/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.Candidates
public import TauCeti.NumberTheory.NumberField.Index.Discriminant
import TauCeti.NumberTheory.NumberField.Units.Normalization
import TauCeti.NumberTheory.NumberField.Units.PrimeDegree

/-!
# Elimination certificates for fundamental units

A certificate eliminates each polynomial in `unitCandidates K B` either by excluding real roots
in `(1, B)` or by excluding it as the minimal polynomial of an integral primitive element of `K`.
The field test can be discharged by the index–discriminant formula. These are proofs of the tests,
not Boolean assertions about an unchecked root-finding procedure.

In a number field of prime degree and unit rank one, a certificate excludes every unit in the
selected real interval. With `B = w u > 1`, normalization then proves that `u` generates the units
modulo torsion. The certificate does not depend on a choice of real place: the root test excludes
all real roots in the interval, and soundness can be applied at any real place.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, §5.7, for unit search.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2, for the index–discriminant formula.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.Units Polynomial
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- Every candidate polynomial is excluded either by its real roots in `(1, B)` or as a minimal
polynomial of an integral primitive element of `K`. -/
def UnitCandidateEliminationCertificate (K : Type*) [Field K] [NumberField K] (B : ℝ) : Prop :=
  ∀ f ∈ unitCandidates K B,
    (∀ x ∈ Set.Ioo (1 : ℝ) B, aeval x f ≠ 0) ∨
      ∀ θ : IntegralPrimitiveElement K, minpoly ℤ θ.1 ≠ f

/-- The two possible proofs carried by an elimination certificate for each candidate. -/
@[simp]
theorem unitCandidateEliminationCertificate_iff (B : ℝ) :
    UnitCandidateEliminationCertificate K B ↔
      ∀ f ∈ unitCandidates K B,
        (∀ x ∈ Set.Ioo (1 : ℝ) B, aeval x f ≠ 0) ∨
          ∀ θ : IntegralPrimitiveElement K, minpoly ℤ θ.1 ≠ f :=
  (Iff.rfl)

namespace UnitCandidateEliminationCertificate

/-- Construct a certificate using real-root exclusions and the obstruction that a primitive
minimal polynomial must have discriminant equal to the field discriminant times a positive
integer square. -/
theorem of_discr {B : ℝ}
    (h : ∀ f ∈ unitCandidates K B,
      (∀ x ∈ Set.Ioo (1 : ℝ) B, aeval x f ≠ 0) ∨
        ∀ n : ℕ, 0 < n → f.discr ≠ (n : ℤ) ^ 2 * NumberField.discr K) :
    UnitCandidateEliminationCertificate K B := by
  rw [unitCandidateEliminationCertificate_iff]
  intro f hf
  rcases h f hf with hroot | hdiscr
  · exact Or.inl hroot
  · refine Or.inr fun θ heq => ?_
    exact hdiscr θ.index θ.index_pos
      (heq ▸ θ.discr_minpoly_eq_index_sq_mul_discr)

/-- A certificate excludes all units with real image strictly between `1` and `B`, provided the
unit rank is one and the field degree is prime. -/
theorem no_unit_between_real {B : ℝ} (h : UnitCandidateEliminationCertificate K B)
    (hr : rank K = 1) (hp : Nat.Prime (Module.finrank ℚ K))
    {w : InfinitePlace K} (hw : w.IsReal) :
    ¬ ∃ v : (𝓞 K)ˣ,
      1 < w.embedding_of_isReal hw (v : K) ∧ w.embedding_of_isReal hw (v : K) < B := by
  intro ⟨v, hlo, hhi⟩
  have hmem := minpoly_mem_unitCandidates hr hp hw v hlo hhi.le
  rcases (unitCandidateEliminationCertificate_iff B).mp h _ hmem with hroot | hfield
  · apply hroot _ ⟨hlo, hhi⟩
    exact minpoly.aeval_algHom ℤ
      ((w.embedding_of_isReal hw).comp (algebraMap (𝓞 K) K)).toIntAlgHom (v : 𝓞 K)
  · have hnot : v ∉ torsion K := by
      intro hv
      have hone := (NumberField.Units.mem_torsion (x := v)).mp hv w
      have hval : w v = w.embedding_of_isReal hw (v : K) := by
        rw [← norm_embedding_of_isReal hw, Real.norm_eq_abs,
          abs_of_pos (zero_lt_one.trans hlo)]
      exact (ne_of_gt hlo) (hval ▸ hone)
    exact hfield ⟨v, adjoin_eq_top_of_finrank_prime hp hnot⟩ rfl

/-- **Soundness of unit-candidate elimination.** A unit expanding at a real place generates
modulo torsion if every candidate below its absolute value has been eliminated. -/
theorem sound {u : (𝓞 K)ˣ} {w : InfinitePlace K}
    (h : UnitCandidateEliminationCertificate K (w u))
    (hr : rank K = 1) (hp : Nat.Prime (Module.finrank ℚ K)) (hw : w.IsReal) (hu : 1 < w u) :
    Subgroup.closure {u} ⊔ torsion K = ⊤ :=
  (generates_mod_torsion_iff_no_unit_between_real hr u w hw hu).mpr
    (h.no_unit_between_real hr hp hw)

end UnitCandidateEliminationCertificate

end TauCeti.NumberField.Units

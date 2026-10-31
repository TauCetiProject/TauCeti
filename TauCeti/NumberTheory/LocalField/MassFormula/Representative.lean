/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Orbit
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Sums over representatives of the isomorphism classes

Serre's mass formula has two forms: the sum of `q ^ (-c(L))` over the totally ramified extensions
`L ∈ σ_K(n)` of a local field `K` inside a fixed separable closure, which equals `n`, and the sum of
`1 / (#Aut_K(M) · q ^ c(M))` over a set of representatives `M` of their `K`-isomorphism classes,
which equals `1`. This file passes from the first to the second.

Following Serre, a set of representatives is a predicate rather than a quotient:
`IsRepresentativeSet n R` says that `R ⊆ σ_K(n)` and that every member of `σ_K(n)` is
`K`-isomorphic to exactly one member of `R`. Such sets exist. A sum over `σ_K(n)` of a function
that is constant on `K`-isomorphism classes splits along the classes. By the orbit count
`TauCeti.ncard_isomorphic_mul_natCard_algEquiv`, the class of `M` has `n / #Aut_K(M)` members, so
the sum equals the sum over `R` of `n / #Aut_K(M)` times the value at `M`. The wild exponent is such
a function, so the two forms of the mass formula are equivalent.

## Main definitions

* `TauCeti.IsRepresentativeSet n R`: `R` is a set of representatives of the `K`-isomorphism
  classes of `σ_K(n)`.

## Main results

* `TauCeti.exists_isRepresentativeSet`: sets of representatives exist.

In the namespace `TauCeti.IsRepresentativeSet`:

* `tsum_eq_tsum_div_natCard_algEquiv_mul`: a sum over `σ_K(n)` of an isomorphism-invariant
  function, regrouped along isomorphism classes.
* `mul_tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_wildExponent`:
  `n · ∑_{M ∈ R} 1 / (#Aut_K(M) · q ^ c(M)) = ∑_{L ∈ σ_K(n)} q ^ (-c(L))`.
* `tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_wildExponent_eq_one_iff`: for
  `0 < n`, the second form of the mass formula holds for `R` exactly when the first does.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Théorème 2 and
  Remarque 3°.
-/

public section

open ValuativeRel
open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A set `R` of subextensions of `SeparableClosure K` is a *set of representatives* of the
`K`-isomorphism classes of `σ_K(n)` when `R ⊆ σ_K(n)` and every member of `σ_K(n)` is
`K`-isomorphic to exactly one member of `R`. -/
def IsRepresentativeSet (n : ℕ) (R : Set (IntermediateField K (SeparableClosure K))) : Prop :=
  R ⊆ totallyRamifiedOfDegree K n ∧
    ∀ L ∈ totallyRamifiedOfDegree K n, ∃! M, M ∈ R ∧ Nonempty (L ≃ₐ[K] M)

theorem isRepresentativeSet_iff {n : ℕ} {R : Set (IntermediateField K (SeparableClosure K))} :
    IsRepresentativeSet n R ↔ R ⊆ totallyRamifiedOfDegree K n ∧
      ∀ L ∈ totallyRamifiedOfDegree K n, ∃! M, M ∈ R ∧ Nonempty (L ≃ₐ[K] M) :=
  Iff.rfl

variable (K) in
/-- Every `σ_K(n)` has a set of representatives of its `K`-isomorphism classes. -/
theorem exists_isRepresentativeSet (n : ℕ) :
    ∃ R : Set (IntermediateField K (SeparableClosure K)), IsRepresentativeSet n R := by
  let s : Setoid (totallyRamifiedOfDegree K n) :=
    { r := fun L M ↦ Nonempty (L.1 ≃ₐ[K] M.1)
      iseqv := ⟨fun L ↦ ⟨.refl⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩ }
  -- Choose one member of each class.
  refine ⟨Set.range fun c : Quotient s ↦ (c.out : IntermediateField K (SeparableClosure K)),
    ?_, fun L hL ↦ ⟨(Quotient.mk s ⟨L, hL⟩).out,
      ⟨⟨_, rfl⟩, Setoid.symm' s (Quotient.mk_out (s := s) ⟨L, hL⟩)⟩, ?_⟩⟩
  · rintro _ ⟨c, rfl⟩
    exact c.out.2
  · rintro _ ⟨⟨c, rfl⟩, he⟩
    -- A representative isomorphic to `L` is the one chosen in the class of `L`.
    have : c = Quotient.mk s ⟨L, hL⟩ := by
      rw [← Quotient.out_eq c]
      exact Quotient.sound (Setoid.symm' s he)
    rw [this]

namespace IsRepresentativeSet

variable {n : ℕ} {R : Set (IntermediateField K (SeparableClosure K))}

theorem subset (hR : IsRepresentativeSet n R) : R ⊆ totallyRamifiedOfDegree K n :=
  hR.1

theorem existsUnique {L : IntermediateField K (SeparableClosure K)} (hR : IsRepresentativeSet n R)
    (hL : L ∈ totallyRamifiedOfDegree K n) : ∃! M, M ∈ R ∧ Nonempty (L ≃ₐ[K] M) :=
  hR.2 L hL

/-- A sum over `σ_K(n)` of a function that is constant on `K`-isomorphism classes, regrouped along
the classes: the class of a representative `M` has `n / #Aut_K(M)` members. -/
theorem tsum_eq_tsum_div_natCard_algEquiv_mul (hR : IsRepresentativeSet n R)
    (f : IntermediateField K (SeparableClosure K) → ℝ≥0∞)
    (hf : ∀ {L M : IntermediateField K (SeparableClosure K)}, (L ≃ₐ[K] M) → f L = f M) :
    ∑' L : totallyRamifiedOfDegree K n, f L =
      ∑' M : R, (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) * f M := by
  classical
  -- The isomorphism class of `M` inside `σ_K(n)`.
  let C (M : IntermediateField K (SeparableClosure K)) :
      Set (IntermediateField K (SeparableClosure K)) :=
    {L | L ∈ totallyRamifiedOfDegree K n ∧ Nonempty (M ≃ₐ[K] L)}
  -- Every member of `σ_K(n)` lies in the class of exactly one representative.
  have hU : totallyRamifiedOfDegree K n = ⋃ M ∈ R, C M := by
    ext L
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨fun hL ↦ ?_, fun ⟨_, _, hL, _⟩ ↦ hL⟩
    obtain ⟨M, ⟨hM, ⟨e⟩⟩, -⟩ := hR.existsUnique hL
    exact ⟨M, hM, hL, ⟨e.symm⟩⟩
  have hdisj : R.PairwiseDisjoint C := by
    rintro M hM M' hM' hne
    refine Set.disjoint_left.2 ?_
    rintro L ⟨hL, ⟨e⟩⟩ ⟨-, ⟨e'⟩⟩
    obtain ⟨_, -, huniq⟩ := hR.existsUnique hL
    exact hne ((huniq M ⟨hM, ⟨e.symm⟩⟩).trans (huniq M' ⟨hM', ⟨e'.symm⟩⟩).symm)
  rw [hU, ENNReal.tsum_biUnion hdisj]
  refine tsum_congr fun M ↦ ?_
  have hcard := ncard_isomorphic_mul_natCard_algEquiv (hR.subset M.2)
  have hAut : Nat.card (M ≃ₐ[K] M) ≠ 0 := by
    have := (mem_totallyRamifiedOfDegree_iff.1 (hR.subset M.2)).2.finite
    exact Nat.card_ne_zero.2 ⟨⟨.refl⟩, inferInstance⟩
  -- The class is finite: its size times `#Aut_K(M)` is `n`, and `n ≠ 0` as `σ_K(0) = ∅`.
  have hfin : (C M).Finite := Set.finite_of_ncard_ne_zero fun h ↦ by
    have hn : n = 0 := hcard ▸ mul_eq_zero_of_left h _
    simpa [hn, totallyRamifiedOfDegree_zero] using hR.subset M.2
  -- `f` is constant on the class of `M`, which has `n / #Aut_K(M)` members.
  rw [tsum_congr fun L : C M ↦ hf (Classical.choice L.2.2).symm, ENNReal.tsum_set_const,
    ← hfin.cast_ncard_eq]
  congr 1
  exact (ENNReal.eq_div_iff (by exact_mod_cast hAut) (ENNReal.natCast_ne_top _)).2
    (by exact_mod_cast (mul_comm _ _).trans hcard)

/-- The two sums of Serre's mass formula, related along isomorphism classes:
`n · ∑_{M ∈ R} 1 / (#Aut_K(M) · q ^ c(M)) = ∑_{L ∈ σ_K(n)} q ^ (-c(L))`. -/
theorem mul_tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_wildExponent
    (hR : IsRepresentativeSet n R) :
    (n : ℝ≥0∞) * ∑' M : R, 1 / ((Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) *
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ M.1.wildExponent) =
      ∑' L : totallyRamifiedOfDegree K n,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent := by
  rw [hR.tsum_eq_tsum_div_natCard_algEquiv_mul
    (fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.wildExponent) fun e ↦ by
    rw [IntermediateField.wildExponent_eq_of_algEquiv e], ← ENNReal.tsum_mul_left]
  refine tsum_congr fun M ↦ ?_
  rw [one_div, ENNReal.mul_inv (.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
    (.inl (ENNReal.natCast_ne_top _)), ← mul_assoc]
  simp only [div_eq_mul_inv, one_mul]

/-- For `0 < n`, Serre's mass formula over a set of representatives,
`∑_{M ∈ R} 1 / (#Aut_K(M) · q ^ c(M)) = 1`, is equivalent to the mass formula over `σ_K(n)`,
`∑_{L ∈ σ_K(n)} q ^ (-c(L)) = n`. -/
theorem tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_wildExponent_eq_one_iff
    (hR : IsRepresentativeSet n R) (hn : 0 < n) :
    ∑' M : R, 1 / ((Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) *
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ M.1.wildExponent) = 1 ↔
      ∑' L : totallyRamifiedOfDegree K n,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent = n := by
  rw [← hR.mul_tsum_one_div_natCard_algEquiv_mul_natCard_residueField_pow_wildExponent]
  conv_rhs => rhs; rw [← mul_one (n : ℝ≥0∞)]
  exact (ENNReal.mul_right_inj (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top _)).symm

end IsRepresentativeSet

end TauCeti

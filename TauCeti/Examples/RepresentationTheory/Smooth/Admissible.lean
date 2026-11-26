/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Admissible
public import TauCeti.Examples.RepresentationTheory.Smooth.Dual.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic
import TauCeti.RepresentationTheory.OfMulAction
import TauCeti.RepresentationTheory.Smooth.FinitelyGenerated

/-!
# Examples of admissible representations

The zero representation is admissible, and so is a trivial representation on a finitely generated
module. For a compact group, here the trivial group, the trivial action on `ℚ^(ℕ)` is smooth but
not admissible: its invariants under the whole group are the whole infinite-dimensional module.

For `G = ℤ_p`, written multiplicatively, the permutation representation `ℚ[ℤ_p ⧸ p^n ℤ_p]` is
admissible, being smooth and finite-dimensional, and its `ℤ_p`-invariants are one-dimensional, as
`ℤ_p` permutes the cosets transitively. For `G = ℚ_p`, the permutation representation
`ℚ[ℚ_p ⧸ ℤ_p]` is smooth and finitely generated, but not admissible: the compact open subgroup
`ℤ_p` acts trivially on it, so its `ℤ_p`-invariants are the whole infinite-dimensional space. The
compactness of `ℤ_p` in `ℚ_p` is `TauCeti.Examples.SmoothDual.isCompact_padicIntOpenSubgroup`.

Admissibility quantifies over compact open subgroups. In `ℚ_p^ℕ` with the product topology every
open subgroup contains a whole coordinate line `ℚ_p`, so no open subgroup is compact, and the
trivial action of `ℚ_p^ℕ` on `ℚ^(ℕ)` is admissible.
-/

public section

open Representation MulAction

namespace TauCeti

example {A G : Type*} [CommRing A] [Group G] [TopologicalSpace G] (ρ : Representation A G PUnit) :
    IsAdmissible ρ :=
  inferInstance

example {A G : Type*} [CommRing A] [Group G] [TopologicalSpace G] :
    IsAdmissible (trivial A G (Fin 3 → A)) :=
  inferInstance

/-- The trivial action of the trivial group on `ℚ^(ℕ)` is smooth but not admissible. -/
example : IsSmooth (trivial ℚ Unit (ℕ →₀ ℚ)) ∧ ¬IsAdmissible (trivial ℚ Unit (ℕ →₀ ℚ)) := by
  refine ⟨inferInstance, fun h ↦ ?_⟩
  rw [isAdmissible_iff_finite_of_isTrivial ⟨⊤, isCompact_univ⟩] at h
  have := Module.Finite.finite_basis (Finsupp.basisSingleOne (R := ℚ) (ι := ℕ))
  exact not_finite ℕ

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- **`ℚ[ℤ_p ⧸ p^n ℤ_p]` is admissible**, with one-dimensional `ℤ_p`-invariants. -/
example (n : ℕ) :
    IsAdmissible (ofMulAction ℚ (Multiplicative ℤ_[p])
        (Multiplicative ℤ_[p] ⧸ (padicIntLevel p n).toSubgroup)) ∧
      Module.finrank ℚ (ofMulAction ℚ (Multiplicative ℤ_[p])
        (Multiplicative ℤ_[p] ⧸ (padicIntLevel p n).toSubgroup)).invariants = 1 := by
  have : (padicIntLevel p n).toSubgroup.FiniteIndex :=
    ⟨by rw [index_padicIntLevel]; exact pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  refine ⟨inferInstance, ?_⟩
  rw [Module.finrank_eq_nat_card_basis (invariantOrbitSumBasis ℚ _ _)]
  have := (pretransitive_iff_subsingleton_quotient (Multiplicative ℤ_[p])
    (Multiplicative ℤ_[p] ⧸ (padicIntLevel p n).toSubgroup)).1 inferInstance
  have : Nonempty (orbitRel.Quotient (Multiplicative ℤ_[p])
    (Multiplicative ℤ_[p] ⧸ (padicIntLevel p n).toSubgroup)) := ⟨⟦1⟧⟩
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩

open Examples.SmoothDual in
/-- **`ℚ[ℚ_p ⧸ ℤ_p]` is smooth and finitely generated, but not admissible**: the compact open
subgroup `ℤ_p` acts trivially on it, and `ℚ_p ⧸ ℤ_p` is infinite. -/
example : IsSmooth (ofMulAction ℚ (Multiplicative ℚ_[p]) (PadicQuotient p)) ∧
    Module.Finite (MonoidAlgebra ℚ (Multiplicative ℚ_[p]))
      (ofMulAction ℚ (Multiplicative ℚ_[p]) (PadicQuotient p)).asModule ∧
    ¬IsAdmissible (ofMulAction ℚ (Multiplicative ℚ_[p]) (PadicQuotient p)) := by
  refine ⟨inferInstance, inferInstance, fun h ↦ ?_⟩
  have hfin := h.finite_invariants (padicIntOpenSubgroup p) (isCompact_padicIntOpenSubgroup p)
  have htop : invariants ((ofMulAction ℚ (Multiplicative ℚ_[p]) (PadicQuotient p)).comp
      (padicIntOpenSubgroup p : Subgroup (Multiplicative ℚ_[p])).subtype) = ⊤ := by
    rw [ofMulAction_comp_subtype, eq_top_iff]
    exact fun v _ ↦ mem_invariants_ofMulAction_iff.2 fun u x ↦
      congrArg v.coeff (smul_eq_of_mem_padicIntOpenSubgroup p u.property x)
  rw [htop] at hfin
  exact not_finite_monoidAlgebra_padicQuotient p (Module.Finite.equiv (LinearEquiv.ofTop ⊤ rfl))

/-- **`ℚ_p^ℕ` has no compact open subgroup**, so the trivial action of `ℚ_p^ℕ` on `ℚ^(ℕ)` is
admissible. An open subgroup contains a whole coordinate line `ℚ_p`, since a basic neighbourhood of
`0` in the product topology constrains finitely many coordinates, and `ℚ_p` is not compact. -/
example : (∀ U : OpenSubgroup (Multiplicative (ℕ → ℚ_[p])),
      ¬IsCompact (U : Set (Multiplicative (ℕ → ℚ_[p])))) ∧
    IsAdmissible (trivial ℚ (Multiplicative (ℕ → ℚ_[p])) (ℕ →₀ ℚ)) := by
  have hG (U : OpenSubgroup (Multiplicative (ℕ → ℚ_[p]))) :
      ¬IsCompact (U : Set (Multiplicative (ℕ → ℚ_[p]))) := by
    intro hc
    have hU : Multiplicative.ofAdd ⁻¹' (U : Set (Multiplicative (ℕ → ℚ_[p]))) ∈
        nhds (0 : ℕ → ℚ_[p]) :=
      continuous_ofAdd.continuousAt.preimage_mem_nhds (by rw [ofAdd_zero]; exact U.mem_nhds_one)
    rw [nhds_pi, Filter.mem_pi'] at hU
    obtain ⟨I, t, ht, hsub⟩ := hU
    obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset I
    -- The coordinate line `j` lies in `U`.
    have hline (a : ℚ_[p]) : (Pi.single j a : ℕ → ℚ_[p]) ∈
        Multiplicative.ofAdd ⁻¹' (U : Set (Multiplicative (ℕ → ℚ_[p]))) :=
      hsub fun i hi ↦ by
        rw [Pi.single_eq_of_ne (ne_of_mem_of_not_mem hi hj)]
        exact mem_of_mem_nhds (ht i)
    have : IsCompact (Set.univ : Set ℚ_[p]) :=
      (hc.image (f := fun x : Multiplicative (ℕ → ℚ_[p]) ↦ x.toAdd j)
        ((continuous_apply j).comp continuous_toAdd)).of_isClosed_subset isClosed_univ
        fun a _ ↦ ⟨Multiplicative.ofAdd (Pi.single j a), hline a, by simp⟩
    exact noncompact_univ ℚ_[p] this
  exact ⟨hG, IsAdmissible.of_forall_not_isCompact hG⟩

end Padic

end TauCeti

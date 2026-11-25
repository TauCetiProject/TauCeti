/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Admissible
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Basic
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
`ℤ_p` acts trivially on it, so its `ℤ_p`-invariants are the whole infinite-dimensional space.

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

/-- `p^n ℤ_p` is an open subgroup of `ℤ_p`, written multiplicatively. -/
example (n : ℕ) : ∃ U : OpenSubgroup (Multiplicative ℤ_[p]),
    ∀ x, x ∈ U ↔ x.toAdd ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
  let f := (PadicInt.toZModPow (p := p) n).toAddMonoidHom.toMultiplicative
  have h : (f.ker : Set (Multiplicative ℤ_[p])) =
      Multiplicative.toAdd ⁻¹' Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-n : ℤ)) := by
    ext x
    rw [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, Metric.mem_closedBall,
      dist_zero_right, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker]
    exact toAdd_eq_zero.symm
  have hopen : IsOpen (f.ker : Set (Multiplicative ℤ_[p])) := by
    rw [h]
    exact continuous_toAdd.isOpen_preimage _
      (IsUltrametricDist.isOpen_closedBall _
        (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _).ne')
  refine ⟨⟨f.ker, hopen⟩, fun x ↦ ?_⟩
  change x ∈ f.ker ↔ _
  rw [MonoidHom.mem_ker, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  exact toAdd_eq_zero.symm

/-- **`ℚ[ℤ_p ⧸ p^n ℤ_p]` is admissible**, with one-dimensional `ℤ_p`-invariants. -/
example (n : ℕ) (U : OpenSubgroup (Multiplicative ℤ_[p]))
    (hU : ∀ x, x ∈ U ↔ x.toAdd ∈ Ideal.span {(p : ℤ_[p]) ^ n}) :
    IsAdmissible (ofMulAction ℚ (Multiplicative ℤ_[p]) (Multiplicative ℤ_[p] ⧸ (U : Subgroup _))) ∧
      Module.finrank ℚ (ofMulAction ℚ (Multiplicative ℤ_[p])
        (Multiplicative ℤ_[p] ⧸ (U : Subgroup _))).invariants = 1 := by
  -- `U` contains the kernel of the reduction `ℤ_p → ℤ/p^n`, so it has finite index.
  let f := (PadicInt.toZModPow (p := p) n).toAddMonoidHom.toMultiplicative
  have hle : f.ker ≤ U := fun x hx ↦ by
    rw [OpenSubgroup.mem_toSubgroup, hU, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    exact toAdd_eq_zero.2 (MonoidHom.mem_ker.1 hx)
  have : (U : Subgroup (Multiplicative ℤ_[p])).FiniteIndex := Subgroup.finiteIndex_of_le hle
  refine ⟨IsAdmissible.of_finite, ?_⟩
  rw [Module.finrank_eq_nat_card_basis (invariantOrbitSumBasis ℚ _ _)]
  have := (pretransitive_iff_subsingleton_quotient (Multiplicative ℤ_[p])
    (Multiplicative ℤ_[p] ⧸ (U : Subgroup _))).1 inferInstance
  have : Nonempty (orbitRel.Quotient (Multiplicative ℤ_[p])
    (Multiplicative ℤ_[p] ⧸ (U : Subgroup _))) := ⟨⟦1⟧⟩
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩

/-- `ℤ_p` is a compact open subgroup of `ℚ_p`, written multiplicatively. -/
example : ∃ U : OpenSubgroup (Multiplicative ℚ_[p]),
    (∀ x, x ∈ U ↔ ‖x.toAdd‖ ≤ 1) ∧ IsCompact (U : Set (Multiplicative ℚ_[p])) :=
  ⟨⟨AddSubgroup.toSubgroup (IsUltrametricDist.closedBall_openAddSubgroup ℚ_[p] one_pos),
      (IsUltrametricDist.closedBall_openAddSubgroup ℚ_[p] one_pos).isOpen⟩,
    fun x ↦ by
      change Multiplicative.toAdd x ∈ Metric.closedBall (0 : ℚ_[p]) 1 ↔ _
      rw [Metric.mem_closedBall, dist_zero_right], isCompact_closedBall (0 : ℚ_[p]) 1⟩

/-- **`ℚ[ℚ_p ⧸ ℤ_p]` is smooth and finitely generated, but not admissible.** -/
example (U : OpenSubgroup (Multiplicative ℚ_[p])) (hU : ∀ x, x ∈ U ↔ ‖x.toAdd‖ ≤ 1) :
    IsSmooth (ofMulAction ℚ (Multiplicative ℚ_[p])
        (Multiplicative ℚ_[p] ⧸ (U : Subgroup _))) ∧
      Module.Finite (MonoidAlgebra ℚ (Multiplicative ℚ_[p])) (ofMulAction ℚ (Multiplicative ℚ_[p])
        (Multiplicative ℚ_[p] ⧸ (U : Subgroup _))).asModule ∧
      ¬IsAdmissible (ofMulAction ℚ (Multiplicative ℚ_[p])
        (Multiplicative ℚ_[p] ⧸ (U : Subgroup _))) := by
  set X := Multiplicative ℚ_[p] ⧸ (U : Subgroup (Multiplicative ℚ_[p]))
  refine ⟨inferInstance, inferInstance, fun h ↦ ?_⟩
  have hc : IsCompact (U : Set (Multiplicative ℚ_[p])) := by
    have : (U : Set (Multiplicative ℚ_[p])) =
        Multiplicative.toAdd ⁻¹' Metric.closedBall (0 : ℚ_[p]) 1 := by
      ext x
      rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, ← hU]
      rfl
    rw [this]
    exact isCompact_closedBall (0 : ℚ_[p]) 1
  have hfin := h.finite_invariants U hc
  -- `ℤ_p` acts trivially on `ℚ_p ⧸ ℤ_p`, as `ℚ_p` is commutative.
  have htop : invariants ((ofMulAction ℚ (Multiplicative ℚ_[p]) X).comp
      (U : Subgroup (Multiplicative ℚ_[p])).subtype) = ⊤ := by
    rw [ofMulAction_comp_subtype, eq_top_iff]
    refine fun v _ ↦ mem_invariants_ofMulAction_iff.2 fun u x ↦ ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, mul_comm,
        QuotientGroup.mk_mul_of_mem _ u.property]
  rw [htop] at hfin
  have : Module.Finite ℚ (X →₀ ℚ) :=
    Module.Finite.equiv ((LinearEquiv.ofTop ⊤ rfl).trans (MonoidAlgebra.coeffLinearEquiv ℚ))
  rcases Module.finite_finsupp_self_iff.1 this with h | h
  · exact not_subsingleton ℚ h
  -- In a finite quotient `g ^ m ∈ ℤ_p` for `m` the index, which fails for `g = (p m)⁻¹`.
  have hm : (U : Subgroup (Multiplicative ℚ_[p])).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmem := Subgroup.pow_index_mem (U : Subgroup (Multiplicative ℚ_[p]))
    (Multiplicative.ofAdd ((p * (U : Subgroup (Multiplicative ℚ_[p])).index : ℚ_[p])⁻¹))
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_inv, ← mul_assoc, mul_comm _ (p : ℚ_[p])⁻¹,
    mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm), mul_one, OpenSubgroup.mem_toSubgroup, hU,
    toAdd_ofAdd, norm_inv, Padic.norm_p, inv_inv] at hmem
  exact absurd hmem (not_le.2 (by exact_mod_cast (Fact.out : p.Prime).one_lt))

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
      U.mem_nhds_one
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

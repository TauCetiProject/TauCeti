/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet.Sum

/-!
# Finiteness of labelled Galois sets of a given size

The point stabilizers of a labelled Galois set `ρ : TauCeti.GaloisSet K n` have fixed fields of
degree at most `n` over `K` (`TauCeti.GaloisSet.finrank_fixedField_stabilizer_le`). Conversely,
every subextension of `SeparableClosure K` of degree `m` with `0 < m ≤ n` is the fixed field of a
point stabilizer of some Galois set of size `n`: a transitive Galois set on `m` labels, padded by
`n - m` fixed labels (`TauCeti.GaloisSet.exists_fixedField_stabilizer_eq`).

So there are finitely many labelled Galois sets of size `n` exactly when `SeparableClosure K` has
finitely many subextensions of each degree `m` with `0 < m ≤ n` (`TauCeti.finite_galoisSet_iff`).
When there are, all point stabilizers of all Galois sets of size `n` contain the fixing subgroup
of the compositum of these finitely many subextensions, an open subgroup of finite index, and a
Galois set is determined by its values on the cosets of that subgroup.

This is the field-theoretic half of the finiteness dichotomy for Galois sets over a local field:
there the subextensions of a given degree `m > 0` are finite in number unless `K` has equal
characteristic `p` and `p ∣ m` (`TauCeti.infinite_setOf_finrank_eq_iff`), which is why the étale
mass is a sum in `ℝ≥0∞`.
-/

public section

noncomputable section

namespace TauCeti

universe u

variable {K : Type u} [Field K] {n : ℕ}

namespace GaloisSet

/-- The fixed field of a point stabilizer of a Galois set of size `n` has degree at most `n`, the
size of the set. -/
theorem finrank_fixedField_stabilizer_le (ρ : GaloisSet K n) (i : Fin n) :
    letI := ρ.mulAction
    Module.finrank K (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) i)) ≤ n := by
  let := ρ.mulAction
  rw [ρ.finrank_fixedField_stabilizer]
  exact (Finite.card_subtype_le _).trans (Nat.card_fin n).le

/-- Every subextension of `SeparableClosure K` of degree `m` with `0 < m ≤ n` is the fixed field
of a point stabilizer of some labelled Galois set of size `n`. -/
theorem exists_fixedField_stabilizer_eq (L : IntermediateField K (SeparableClosure K))
    (hpos : 0 < Module.finrank K L) (hle : Module.finrank K L ≤ n) :
    ∃ (ρ : GaloisSet K n) (i : Fin n),
      letI := ρ.mulAction
      IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i) = L := by
  set m := Module.finrank K L
  -- A transitive Galois set of size `m` in which the label `0` has stabilizer fixed field `L`.
  obtain ⟨⟨τ, -, hτ⟩⟩ := (Nat.card_ne_zero.1
    ((natCard_isTransitive_fixedField_stabilizer_eq L rfl ⟨0, hpos⟩).trans_ne
      (m - 1).factorial_ne_zero)).1
  -- Pad it with `n - m` fixed labels.
  let e : Fin m ⊕ Fin (n - m) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  refine ⟨sum τ (trivial K (n - m)) e, e (Sum.inl ⟨0, hpos⟩), ?_⟩
  rw [stabilizer_sum_inl]
  exact hτ

end GaloisSet

/-- **Finiteness of labelled Galois sets.** There are finitely many labelled Galois sets of size `n`
over `K` exactly when `SeparableClosure K` has finitely many subextensions of each degree `m` with
`0 < m ≤ n`. -/
theorem finite_galoisSet_iff :
    Finite (GaloisSet K n) ↔ ∀ m, 0 < m → m ≤ n →
      {L : IntermediateField K (SeparableClosure K) | Module.finrank K L = m}.Finite := by
  constructor
  · -- Every such subextension is the fixed field of a point stabilizer.
    intro h m hm hmn
    refine (Set.finite_range fun p : GaloisSet K n × Fin n ↦
      letI := p.1.mulAction
      IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) p.2)).subset ?_
    rintro L (hL : Module.finrank K L = m)
    obtain ⟨ρ, i, hρ⟩ := GaloisSet.exists_fixedField_stabilizer_eq L (hL ▸ hm) (hL ▸ hmn)
    exact ⟨(ρ, i), hρ⟩
  · intro h
    -- The subextensions of degree at most `n` form a finite set `S` of finite subextensions.
    let S : Set (IntermediateField K (SeparableClosure K)) :=
      {L | 0 < Module.finrank K L ∧ Module.finrank K L ≤ n}
    have hS : S.Finite := ((Set.finite_Icc 1 n).biUnion fun m hm ↦ h m hm.1 hm.2).subset
      fun L hL ↦ Set.mem_biUnion (x := Module.finrank K L) hL rfl
    have := hS.to_subtype
    have (L : S) : FiniteDimensional K L.val := Module.finite_of_finrank_pos L.property.1
    -- The fixing subgroup `H` of their compositum has finite index.
    let H := (⨆ L : S, L.val).fixingSubgroup
    have : H.FiniteIndex :=
      ⟨by rw [← IntermediateField.finrank_eq_fixingSubgroup_index]; exact Module.finrank_pos.ne'⟩
    -- Every element of `H` fixes every label of every Galois set of size `n`, since every point
    -- stabilizer is the fixing subgroup of a member of `S`.
    have hH (ρ : GaloisSet K n) (σ : Gal(SeparableClosure K/K)) (hσ : σ ∈ H) : ρ.val σ = 1 := by
      let := ρ.mulAction
      refine Equiv.ext fun i ↦ ?_
      have := ρ.finiteDimensional_fixedField_stabilizer i
      have hσi := IntermediateField.fixingSubgroup_le (le_iSup (fun L : S ↦ L.val)
        ⟨_, Module.finrank_pos, ρ.finrank_fixedField_stabilizer_le i⟩) hσ
      rw [ρ.fixingSubgroup_fixedField_stabilizer, MulAction.mem_stabilizer_iff,
        GaloisSet.smul_def] at hσi
      rw [Equiv.Perm.one_apply]
      exact hσi
    -- So a Galois set is determined by its values on representatives of the cosets of `H`.
    refine Finite.of_injective (fun ρ : GaloisSet K n ↦ fun c : Gal(SeparableClosure K/K) ⧸ H ↦
      ρ.val c.out) fun ρ τ hρτ ↦ GaloisSet.ext fun σ i ↦ ?_
    obtain ⟨g, hg⟩ := QuotientGroup.mk_out_eq_mul H σ
    have hσ := congrFun hρτ (σ : Gal(SeparableClosure K/K) ⧸ H)
    simp only [hg, map_mul, hH ρ g g.property, hH τ g g.property, mul_one] at hσ
    exact DFunLike.congr_fun hσ i

end TauCeti

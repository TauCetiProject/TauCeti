/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Lifting
import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentralSeries

/-!
# The peripheral product identity

Let `F` be a free pro-`p` group of rank `r` with basis `x_0, …, x_{r-1}` and cusp
`z = (x_0 ⋯ x_{r-1})⁻¹`. For every unit `u ∈ ℤ_pˣ` there are conjugators `c_0, …, c_{r-1}` and `d`
in `F`, with `c_0 = 1`, such that

`(c_0⁻¹ x_0 ^ u c_0) ⋯ (c_{r-1}⁻¹ x_{r-1} ^ u c_{r-1}) · (d⁻¹ z ^ u d) = 1`,

where `^ u` is the `p`-adic power; that is, the peripheral defect of `(c, d)` is trivial. The
identity is what makes the continuous endomorphism `x_i ↦ c_i⁻¹ x_i ^ u c_i` carry the cusp `z`
to the conjugate `d⁻¹ z ^ u d` of its `u`-th power.

The proof passes to the limit in the approximate solutions supplied by
`TauCeti.Peripheral.exists_mem_level_succ`. The sets of normalized conjugators, with `c_0 = 1`,
whose defect lies in `γ_{n+1}(F)` form a decreasing sequence of nonempty closed subsets of the
compact space `F ^ r × F`, so they have a common point. Its defect lies in every term of the
closed lower central series, whose intersection is trivial because `F` is pro-`p`. Imposing
`c_0 = 1` at every level is what keeps the normalization in the limit.

## Main results

* `TauCeti.Peripheral.exists_defect_eq_one`: for every unit `u`, the basis of a free pro-`p`
  group admits normalized conjugators whose peripheral defect is trivial.

## References

* Y. Ihara, "Braids, Galois groups, and some arithmetic functions", Proc. ICM Kyoto 1990,
  99–120, for the peripheral automorphisms `x ↦ x ^ λ`, `y ↦ f⁻¹ y ^ λ f` of free pro-`p` groups
  of rank two, which Ihara obtains from the Galois action on the fundamental group of the
  thrice-punctured line.
-/

public section

namespace TauCeti

namespace Peripheral

variable {p r : ℕ} [Fact p.Prime] {F : Type*} [Group F] [TopologicalSpace F]
  [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F]

/-- **The peripheral product identity.** For every unit `u ∈ ℤ_pˣ`, the basis `x = basis e` of a
free pro-`p` group admits conjugators `c` on the basis, with `c 0 = 1` in positive rank, and `d`
on the cusp such that `(∏_i (c i)⁻¹ * x i ^ u * c i) * (d⁻¹ * cusp x ^ u * d) = 1`, the product
taken in order and `^ u` the `p`-adic power. -/
theorem exists_defect_eq_one (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) (u : ℤ_[p]ˣ) :
    ∃ (c : Fin r → F) (d : F), (∀ h0 : 0 < r, c ⟨0, h0⟩ = 1) ∧
      defect hF (basis e) (u : ℤ_[p]) c d = 1 := by
  let _ : T2Space F := e.toHomeomorph.isEmbedding.t2Space
  -- The normalized conjugators at level `n + 1`.
  let N : Set ((Fin r → F) × F) := {cd | ∀ h0 : 0 < r, cd.1 ⟨0, h0⟩ = 1}
  let T : ℕ → Set ((Fin r → F) × F) := fun n ↦ level hF (basis e) (u : ℤ_[p]) (n + 1) ∩ N
  have hN : IsClosed N := by
    simp only [N, Set.ofPred_forall]
    exact isClosed_iInter fun h0 ↦ isClosed_eq (by fun_prop) continuous_const
  have hT : ∀ n, IsClosed (T n) := fun n ↦ (isClosed_level hF _ _ _).inter hN
  -- Each level is nonempty: start from the trivial conjugators and apply the correction step,
  -- which leaves the first conjugator unchanged.
  have hTn : ∀ n, (T n).Nonempty := by
    intro n
    induction n with
    | zero => exact ⟨(1, 1), by simp, fun _ ↦ rfl⟩
    | succ n ih =>
      obtain ⟨⟨c, d⟩, hcd, hc0⟩ := ih
      obtain ⟨c', d', -, -, hc'0, hlev⟩ :=
        exists_mem_level_succ hF e u (n + 1) (Nat.le_add_left 1 n) c d hcd
      exact ⟨_, hlev, fun h0 ↦ (congrArg₂ (· * ·) (hc0 h0) (hc'0 h0)).trans (mul_one 1)⟩
  obtain ⟨⟨c, d⟩, hcd⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T
    (fun n ↦ Set.inter_subset_inter_left _ (level_antitone hF _ _ (Nat.le_succ _))) hTn
    (hT 0).isCompact hT
  simp only [Set.mem_iInter] at hcd
  refine ⟨c, d, (hcd 0).2, ?_⟩
  -- The defect lies in every term of the closed lower central series, whose intersection is
  -- trivial.
  rw [← Subgroup.mem_bot, ← hF.iInf_closedLowerCentralSeries_eq_bot Fact.out, Subgroup.mem_iInf]
  exact fun n ↦ (mem_level_iff ..).mp <| level_antitone hF _ _ (Nat.le_succ n) (hcd n).1

end Peripheral

end TauCeti

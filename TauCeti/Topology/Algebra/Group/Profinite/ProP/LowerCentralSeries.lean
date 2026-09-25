/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.FiniteGeneration

/-!
# The lower `p`-series of a profinite group

The lower `p`-series `λ_k = TauCeti.pLowerCentralSeries p G k` of a topological group is defined
and studied for arbitrary topological groups in `TauCeti.Topology.Algebra.Group.LowerCentralSeries`.
This file adds what holds for a profinite group `G` and a prime `p`.

For a profinite group and a prime `p`, the first term `λ_1` is the pro-`p` Frattini subgroup
`TauCeti.proPFrattini p G`. Primality matters: for `p = 4` and the cyclic group of order two,
fourth powers and commutators are trivial, so `λ_1` is trivial, while the pro-`4` Frattini
subgroup is the whole group.

For a topologically finitely generated profinite group and a prime `p`, every `λ_k` is open, hence
of finite index, and in a topologically finitely generated pro-`p` group the quotients `G ⧸ λ_k`
are finite `p`-groups; in particular the graded pieces `gr_k(G) = λ_k ⧸ λ_{k+1}` are finite.
Without finite generation the terms need not be open: an infinite product of copies of `ℤ ⧸ p`
has `λ_1 = 1`, so `gr_0(G) = G` is infinite.

## Main results

* `TauCeti.pLowerCentralSeries_one_eq_proPFrattini`: for a prime `p`, `λ_1` is the pro-`p`
  Frattini subgroup of a profinite group.
* `TauCeti.IsTopologicallyFinitelyGenerated.isOpen_pLowerCentralSeries`: for a prime `p`, in a
  topologically finitely generated profinite group every `λ_k` is open, so
  `TauCeti.IsTopologicallyFinitelyGenerated.finite_quotient_pLowerCentralSeries`,
  `TauCeti.IsTopologicallyFinitelyGenerated.finite_gradedPiece` and, for a pro-`p` group,
  `TauCeti.IsProP.isPGroup_quotient_pLowerCentralSeries`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, Section 1.2.
-/

public section

namespace TauCeti

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- For a profinite group and a prime `p`, the first term of the lower `p`-series is the pro-`p`
Frattini subgroup. -/
theorem pLowerCentralSeries_one_eq_proPFrattini (hp : p.Prime) :
    pLowerCentralSeries p G 1 = proPFrattini p G := by
  rw [pLowerCentralSeries_one, proPFrattini_eq_topologicalClosure hp]

/-- **Openness of the lower `p`-series.** For a prime `p`, in a topologically finitely generated
profinite group every term of the lower `p`-series is open. -/
theorem IsTopologicallyFinitelyGenerated.isOpen_pLowerCentralSeries
    (hG : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) (k : ℕ) :
    IsOpen (pLowerCentralSeries p G k : Set G) := by
  induction k with
  | zero => rw [pLowerCentralSeries_zero, coe_top]; exact isOpen_univ
  | succ k ih =>
    let U : OpenSubgroup G := ⟨pLowerCentralSeries p G k, ih⟩
    have : CompactSpace U.toSubgroup :=
      isCompact_iff_compactSpace.mp (isClosed_pLowerCentralSeries k).isCompact
    have hopen : IsOpen (proPFrattini p U.toSubgroup : Set U.toSubgroup) :=
      (hG.of_openSubgroup U).isOpen_proPFrattini p
    -- The Frattini subgroup of `λ_k` maps into `λ_{k+1}`.
    have hle : (proPFrattini p U.toSubgroup).map U.toSubgroup.subtype ≤
        pLowerCentralSeries p G (k + 1) := by
      rw [proPFrattini_eq_topologicalClosure hp, pLowerCentralSeries_succ, pLowerCentralStep_def]
      refine (U.toSubgroup.subtype.map_topologicalClosure_le continuous_subtype_val _).trans
        (topologicalClosure_mono ?_)
      rw [Subgroup.map_sup, MonoidHom.map_closure, commutator_def, map_commutator]
      refine sup_le (le_sup_of_le_left ((Subgroup.closure_le _).mpr ?_))
        (le_sup_of_le_right (commutator_mono (map_subtype_le _) le_top))
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact Subgroup.subset_closure ⟨x, x.2, (Subgroup.coe_pow _ x p).symm⟩
    refine isOpen_mono hle ?_
    rw [coe_map, coe_subtype]
    exact ih.isOpenMap_subtype_val _ hopen

/-- For a prime `p`, in a topologically finitely generated profinite group every quotient
`G ⧸ λ_k` is finite. -/
theorem IsTopologicallyFinitelyGenerated.finite_quotient_pLowerCentralSeries
    (hG : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) (k : ℕ) :
    Finite (G ⧸ pLowerCentralSeries p G k) :=
  quotient_finite_of_isOpen _ (hG.isOpen_pLowerCentralSeries hp k)

/-- For a prime `p`, in a topologically finitely generated profinite group every graded piece
`gr_k(G) = λ_k ⧸ λ_{k+1}` of the lower `p`-series is finite. -/
theorem IsTopologicallyFinitelyGenerated.finite_gradedPiece
    (hG : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) (k : ℕ) :
    Finite (gradedPiece p G k) :=
  have := hG.finite_quotient_pLowerCentralSeries hp (k + 1)
  Finite.of_injective _ (gradedPieceInclusion_injective k)

/-- For a prime `p`, in a topologically finitely generated pro-`p` group every quotient `G ⧸ λ_k`
is a finite `p`-group. -/
theorem IsProP.isPGroup_quotient_pLowerCentralSeries (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) (k : ℕ) :
    IsPGroup p (G ⧸ pLowerCentralSeries p G k) :=
  isProP_iff.mp hG ⟨⟨pLowerCentralSeries p G k, hfg.isOpen_pLowerCentralSeries hp k⟩,
    inferInstance⟩

end TauCeti

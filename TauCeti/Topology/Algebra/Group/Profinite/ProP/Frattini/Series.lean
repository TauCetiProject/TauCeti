/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.FrattiniSeries
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentralSeries

/-!
# The Frattini series of a profinite group

The Frattini series `Φ_k = TauCeti.proPFrattiniSeries p G k` of a topological group is defined and
studied for arbitrary topological groups in `TauCeti.Topology.Algebra.Group.FrattiniSeries`. This
file adds what holds for a profinite group `G` and a prime `p`.

For a prime `p` and a closed subgroup `H` of a profinite group, one step of the recursion is the
honest Frattini subgroup of `H`, transported to the ambient group along the inclusion
(`TauCeti.proPFrattiniStep_eq_map_proPFrattini`), so `Φ_{k+1} = Φ(Φ_k)`; in particular
`Φ_1 = proPFrattini p G`.

The Frattini series and the lower `p`-series `λ_k = TauCeti.pLowerCentralSeries p G k`
**interleave**: the two steps differ only in that the Frattini step takes commutators inside the
subgroup while the lower `p`-series step takes them against the whole group, so `Φ_k ≤ λ_k` always;
and in a topologically finitely generated pro-`p` group every `Φ_k` is open, so conversely every
`Φ_k` contains a `λ_j`. The two series are therefore cofinal in one another, and both are
neighbourhood bases of `1`; the arguments that run level by level along one of them run equally
along the other.

Cofinality of the Frattini series among the open normal subgroups of a pro-`p` group needs no
finite generation, because `Φ_k ≤ λ_k` and the lower `p`-series is already cofinal. So the `Φ_k`
have trivial intersection in any pro-`p` group and such a group is the inverse limit of its
quotients `G ⧸ Φ_k`. With finite generation the quotients are finite `p`-groups. Without finite
generation the terms need not be open: an infinite product of copies of `ℤ ⧸ p` has `Φ_1 = 1`.

## Main results

* `TauCeti.proPFrattiniStep_eq_map_proPFrattini` and
  `TauCeti.proPFrattiniSeries_succ_eq_map_proPFrattini`: for a prime `p` and a closed subgroup of
  a profinite group the step is the pro-`p` Frattini subgroup of that subgroup, so the series is
  the iterated Frattini subgroup; `TauCeti.proPFrattiniSeries_one` is the case `Φ_1 = Φ(G)`, in
  simp-normal form `TauCeti.proPFrattiniStep_top_eq_proPFrattini`.
* `TauCeti.IsProP.exists_pLowerCentralSeries_le_proPFrattiniSeries`: together with
  `TauCeti.proPFrattiniSeries_le_pLowerCentralSeries` this is the interleaving of the Frattini
  series with the lower `p`-series.
* `TauCeti.IsTopologicallyFinitelyGenerated.isOpen_proPFrattiniSeries`: in a topologically
  finitely generated profinite group every `Φ_k` is open, so
  `TauCeti.IsTopologicallyFinitelyGenerated.finite_quotient_proPFrattiniSeries` and, for a pro-`p`
  group, `TauCeti.IsProP.isPGroup_quotient_proPFrattiniSeries`.
* `TauCeti.IsProP.exists_proPFrattiniSeries_le`: in a pro-`p` group every open normal subgroup
  contains a term of the Frattini series, so `TauCeti.IsProP.iInf_proPFrattiniSeries_eq_bot`.
* `TauCeti.IsProP.existsUnique_forall_mk_eq_proPFrattiniSeries`: a pro-`p` group is the inverse
  limit of its quotients `G ⧸ Φ_k`.
* `TauCeti.IsProP.hasAntitoneBasis_nhds_one_proPFrattiniSeries`: in a topologically finitely
  generated pro-`p` group the Frattini series is a neighbourhood basis of `1`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8, Proposition 2.8.13.
* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, Section 1.2.
-/

public section

namespace TauCeti

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **One step of the Frattini series is the pro-`p` Frattini subgroup.** For a prime `p` and a
closed subgroup `H` of a profinite group, `proPFrattiniStep p H` is the pro-`p` Frattini subgroup
of `H`, viewed inside the ambient group along the inclusion. -/
theorem proPFrattiniStep_eq_map_proPFrattini (hp : p.Prime) {H : Subgroup G}
    (hH : IsClosed (H : Set G)) :
    proPFrattiniStep p H = (proPFrattini p H).map H.subtype := by
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  -- The `p`-th powers of `H`, computed in `H` and transported, are the `p`-th powers of `H`.
  have himage : ⇑H.subtype '' (Set.range fun x : H ↦ x ^ p) = (· ^ p) '' (H : Set G) := by
    rw [← Set.range_comp]
    refine Set.ext fun x ↦ ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, by simp⟩
  rw [proPFrattini_eq_topologicalClosure hp,
    H.subtype.map_topologicalClosure continuous_subtype_val _
      (isClosed_topologicalClosure _).isCompact,
    Subgroup.map_sup, MonoidHom.map_closure, himage, H.map_subtype_commutator,
    proPFrattiniStep_def]

/-- **The Frattini series is the iterated pro-`p` Frattini subgroup.** For a prime `p` and a
profinite group, `Φ_{k+1}` is the pro-`p` Frattini subgroup of `Φ_k`, viewed inside the ambient
group along the inclusion. -/
theorem proPFrattiniSeries_succ_eq_map_proPFrattini (hp : p.Prime) (k : ℕ) :
    proPFrattiniSeries p G (k + 1) =
      (proPFrattini p (proPFrattiniSeries p G k)).map (proPFrattiniSeries p G k).subtype := by
  rw [proPFrattiniSeries_succ,
    proPFrattiniStep_eq_map_proPFrattini hp (isClosed_proPFrattiniSeries k)]

/-- The Frattini step at the whole group of a profinite group is its pro-`p` Frattini subgroup.
This is the simp-normal form of `TauCeti.proPFrattiniSeries_one`: `TauCeti.proPFrattiniSeries_succ`
and `TauCeti.proPFrattiniSeries_zero` rewrite `Φ_1` to `proPFrattiniStep p ⊤`, and this lemma
carries it on to `proPFrattini p G`. -/
@[simp]
theorem proPFrattiniStep_top_eq_proPFrattini (hp : p.Prime) :
    proPFrattiniStep p (⊤ : Subgroup G) = proPFrattini p G := by
  -- At the whole group the two steps are the same closure: `⁅⊤, ⊤⁆` on both sides.
  rw [← pLowerCentralSeries_one_eq_proPFrattini hp, pLowerCentralSeries_succ,
    pLowerCentralSeries_zero, proPFrattiniStep_def, pLowerCentralStep_def]

/-- The first term of the Frattini series of a profinite group is its pro-`p` Frattini
subgroup. -/
theorem proPFrattiniSeries_one (hp : p.Prime) :
    proPFrattiniSeries p G 1 = proPFrattini p G := by
  rw [proPFrattiniSeries_succ, proPFrattiniSeries_zero, proPFrattiniStep_top_eq_proPFrattini hp]

/-- **Openness of the Frattini series.** For a prime `p`, in a topologically finitely generated
profinite group every term of the Frattini series is open. -/
theorem IsTopologicallyFinitelyGenerated.isOpen_proPFrattiniSeries
    (hG : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) (k : ℕ) :
    IsOpen (proPFrattiniSeries p G k : Set G) := by
  induction k with
  | zero => rw [proPFrattiniSeries_zero, coe_top]; exact isOpen_univ
  | succ k ih =>
    rw [proPFrattiniSeries_succ_eq_map_proPFrattini hp]
    exact hG.isOpen_map_subtype_proPFrattini p ⟨_, ih⟩

/-- For a prime `p`, in a topologically finitely generated profinite group every quotient
`G ⧸ Φ_k` is finite. -/
theorem IsTopologicallyFinitelyGenerated.finite_quotient_proPFrattiniSeries
    (hG : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) (k : ℕ) :
    Finite (G ⧸ proPFrattiniSeries p G k) :=
  quotient_finite_of_isOpen _ (hG.isOpen_proPFrattiniSeries hp k)

/-- For a prime `p`, in a topologically finitely generated pro-`p` group every quotient `G ⧸ Φ_k`
is a finite `p`-group. -/
theorem IsProP.isPGroup_quotient_proPFrattiniSeries (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) (k : ℕ) :
    IsPGroup p (G ⧸ proPFrattiniSeries p G k) :=
  isProP_iff.mp hG ⟨⟨proPFrattiniSeries p G k, hfg.isOpen_proPFrattiniSeries hp k⟩,
    inferInstance⟩

/-! ### Cofinality of the Frattini series in a pro-`p` group -/

open Filter Topology

omit [TotallyDisconnectedSpace G] in
/-- **Cofinality of the Frattini series.** In a compact pro-`p` group every open normal subgroup
contains a term of the Frattini series. No finite generation is needed. -/
theorem IsProP.exists_proPFrattiniSeries_le (hG : IsProP p G) (hp : p.Prime)
    (U : OpenNormalSubgroup G) : ∃ k, proPFrattiniSeries p G k ≤ U.toSubgroup := by
  obtain ⟨k, hk⟩ := hG.exists_pLowerCentralSeries_le hp U
  exact ⟨k, (proPFrattiniSeries_le_pLowerCentralSeries k).trans hk⟩

/-- In a pro-`p` group the terms of the Frattini series have trivial intersection. -/
theorem IsProP.iInf_proPFrattiniSeries_eq_bot (hG : IsProP p G) (hp : p.Prime) :
    ⨅ k, proPFrattiniSeries p G k = ⊥ := by
  refine le_bot_iff.mp ?_
  rw [← hG.iInf_pLowerCentralSeries_eq_bot hp]
  exact le_iInf fun k ↦ iInf_le_of_le k (proPFrattiniSeries_le_pLowerCentralSeries k)

/-- **The interleaving of the two series.** For a prime `p`, in a topologically finitely generated
pro-`p` group every term of the Frattini series contains a term of the lower `p`-series. Together
with `TauCeti.proPFrattiniSeries_le_pLowerCentralSeries` this makes the two series cofinal in one
another. -/
theorem IsProP.exists_pLowerCentralSeries_le_proPFrattiniSeries (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) (k : ℕ) :
    ∃ j, pLowerCentralSeries p G j ≤ proPFrattiniSeries p G k :=
  hG.exists_pLowerCentralSeries_le hp
    ⟨⟨proPFrattiniSeries p G k, hfg.isOpen_proPFrattiniSeries hp k⟩, inferInstance⟩

/-- **A pro-`p` group is the inverse limit of its quotients by the Frattini series.** A sequence
of cosets of the `Φ_k`, compatible along the quotient maps, is realized by a unique element. -/
theorem IsProP.existsUnique_forall_mk_eq_proPFrattiniSeries (hG : IsProP p G) (hp : p.Prime)
    (x : ∀ k, G ⧸ proPFrattiniSeries p G k)
    (hcompat : ∀ (k : ℕ) (g : G), (g : G ⧸ proPFrattiniSeries p G (k + 1)) = x (k + 1) →
      (g : G ⧸ proPFrattiniSeries p G k) = x k) :
    ∃! g : G, ∀ k, (g : G ⧸ proPFrattiniSeries p G k) = x k :=
  existsUnique_forall_mk_eq_of_iInf_eq_bot isClosed_proPFrattiniSeries
    (hG.iInf_proPFrattiniSeries_eq_bot hp) x hcompat

/-- **The Frattini series is a neighbourhood basis of `1`** in a topologically finitely generated
pro-`p` group. -/
theorem IsProP.hasAntitoneBasis_nhds_one_proPFrattiniSeries (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) :
    (𝓝 (1 : G)).HasAntitoneBasis fun k ↦ (proPFrattiniSeries p G k : Set G) :=
  hasAntitoneBasis_nhds_one_of_iInf_eq_bot proPFrattiniSeries_antitone
    (hfg.isOpen_proPFrattiniSeries hp) (hG.iInf_proPFrattiniSeries_eq_bot hp)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClosedSubgroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.TraceShortExact
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence

/-!
# Cohomological dimension of an open subgroup

Let `G` be a profinite group and `U` an open subgroup. If `cd_p G < ∞`, then `cd_p U = cd_p G`
(Serre, *Galois Cohomology*, Ch. I, §3.3, Prop. 14; NSW (3.3.5)).

The inequality `cd_p U ≤ cd_p G` holds for every closed subgroup
(`TauCeti.cohomologicalDimensionAt_le_of_isClosed`). The reverse inequality is where openness is
used. For a discrete `p`-primary torsion `G`-module `M`, the trace `Coind_U^G M → M` is surjective
because `U` is open, with `p`-primary torsion kernel `K`
(`TauCeti.DiscreteCoind.traceShortExact`). If `cd_p G ≤ n + 1` then `Hⁿ⁺²(G, K)` vanishes, so the
long exact sequence makes `Hⁿ⁺¹(G, Coind_U^G M) → Hⁿ⁺¹(G, M)` surjective, and Shapiro's lemma
identifies its source with `Hⁿ⁺¹(U, M)`. Hence `cd_p U ≤ n` forces `cd_p G ≤ n`, one degree at a
time, and `cd_p G ≤ cd_p U` follows by descending from any finite bound on `cd_p G`.

Finiteness of `cd_p G` is essential: `ℤ/p` has `cd_p = ∞` while its open subgroup `1` has
`cd_p = 0`. The theorem is stated for a profinite group `G`; for a pro-`p` group it says that an
open subgroup of a pro-`p` group of finite cohomological dimension has the same cohomological
dimension, which is how the cohomological dimension of an open subgroup of a Demushkin group or of
a free pro-`p` group is read off.

## Main results

* `TauCeti.CohomologicalDimensionLE.of_isOpen`: for `U` open in a profinite group `G` with
  `cd_p G ≤ n` for some `n`, the vanishing predicate `cd_p U ≤ m` implies `cd_p G ≤ m`.
* `TauCeti.cohomologicalDimensionAt_le_of_isOpen_of_ne_top`: **`cd_p G ≤ cd_p U`** for `U` open in
  a profinite group `G` with `cd_p G ≠ ∞`.
* `TauCeti.cohomologicalDimensionAt_eq_of_isOpen_of_ne_top`: **`cd_p U = cd_p G`** for `U` open in
  a profinite group `G` with `cd_p G ≠ ∞`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.3, Prop. 14.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.5).
-/

public section

namespace TauCeti

open ContCohomology _root_.TauCeti.ContinuousCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] {U : Subgroup G}

/-- **The descent step.** For `U` open in a profinite group `G`, if `cd_p G ≤ n + 1` and
`cd_p U ≤ n`, then `cd_p G ≤ n`, as vanishing predicates: `Hⁿ⁺¹(G, M)` is a quotient of
`Hⁿ⁺¹(G, Coind_U^G M) ≅ Hⁿ⁺¹(U, M)` by the trace short exact sequence, whose kernel has vanishing
`Hⁿ⁺²`. -/
theorem CohomologicalDimensionLE.of_isOpen_succ {n : ℕ} (h : CohomologicalDimensionLE.{u} p U n)
    (hU : IsOpen (U : Set G)) (hG : CohomologicalDimensionLE.{u} p G (n + 1)) :
    CohomologicalDimensionLE.{u} p G n := by
  have hUc : IsClosed (U : Set G) := U.isClosed_of_isOpen hU
  have : CompactSpace U := isCompact_iff_compactSpace.mp hUc.isCompact
  have : Finite (G ⧸ U) := U.quotient_finite_of_isOpen hU
  have : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  rw [cohomologicalDimensionLE_iff_forall_subsingleton_succ] at h ⊢
  intro M _ _ _ _ _ hM
  -- `Hⁿ⁺¹(G, Coind_U^G M) ≅ Hⁿ⁺¹(U, M)` vanishes by Shapiro's lemma and `cd_p U ≤ n`
  have : Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G (DiscreteCoind G U M))) :=
    (subsingleton_continuousCohomology_discreteCoind_iff U hUc M (n + 1)).2 (h M hM)
  -- `Hⁿ⁺²(G, K)` vanishes for the `p`-primary torsion kernel `K` of the trace, by `cd_p G ≤ n + 1`
  have : Subsingleton
      (continuousCohomology (n + 1 + 1) (ofDiscreteModule ℤ G (DiscreteCoind.traceKer G U M))) :=
    cohomologicalDimensionLE_iff.1 hG _ (DiscreteCoind.isPPrimaryTorsion_traceKer G U M hM)
      (n + 1 + 1) (by omega)
  exact ((DiscreteCoind.traceShortExact G U M hU).coeffMap_proj_surjective
    (n := n + 1)).subsingleton

/-- **Cohomological dimension descends from an open subgroup.** For `U` open in a profinite group
`G` with `cd_p G ≤ n` for some `n`, the vanishing predicate `cd_p U ≤ m` implies `cd_p G ≤ m`, by
iterating the descent step `TauCeti.CohomologicalDimensionLE.of_isOpen_succ` down from `n`. -/
theorem CohomologicalDimensionLE.of_isOpen {m n : ℕ} (h : CohomologicalDimensionLE.{u} p U m)
    (hU : IsOpen (U : Set G)) (hG : CohomologicalDimensionLE.{u} p G n) :
    CohomologicalDimensionLE.{u} p G m := by
  induction n with
  | zero => exact hG.mono (Nat.zero_le m)
  | succ n ih =>
    rcases le_or_gt (n + 1) m with hle | hlt
    · exact hG.mono hle
    · exact ih ((h.mono (Nat.lt_succ_iff.1 hlt)).of_isOpen_succ hU hG)

/-- **`cd_p G ≤ cd_p U` for an open subgroup `U` of a profinite group `G` with `cd_p G < ∞`.** -/
theorem cohomologicalDimensionAt_le_of_isOpen_of_ne_top (hU : IsOpen (U : Set G))
    (hG : cohomologicalDimensionAt.{u} p G ≠ ⊤) :
    cohomologicalDimensionAt.{u} p G ≤ cohomologicalDimensionAt.{u} p U := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hG
  induction hcd : cohomologicalDimensionAt.{u} p U using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
    exact (cohomologicalDimensionAt_le_iff p G m).2
      (((cohomologicalDimensionAt_le_iff p U m).1 hcd.le).of_isOpen hU
        ((cohomologicalDimensionAt_le_iff p G n).1 hn.ge))

/-- **`cd_p U = cd_p G` for an open subgroup `U` of a profinite group `G` with `cd_p G < ∞`**
(Serre, *Galois Cohomology*, Ch. I, §3.3, Prop. 14). The inequality `cd_p U ≤ cd_p G` holds for
every closed subgroup; the reverse one uses openness and the finiteness of `cd_p G`. -/
theorem cohomologicalDimensionAt_eq_of_isOpen_of_ne_top (hU : IsOpen (U : Set G))
    (hG : cohomologicalDimensionAt.{u} p G ≠ ⊤) :
    cohomologicalDimensionAt.{u} p U = cohomologicalDimensionAt.{u} p G :=
  le_antisymm (cohomologicalDimensionAt_le_of_isClosed (U.isClosed_of_isOpen hU))
    (cohomologicalDimensionAt_le_of_isOpen_of_ne_top hU hG)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Bifurcation.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.PointConfigurationCount

/-!
# Invariance of the weighted count through points under local bifurcations

Taubes's invariant of a class `A` counts configurations of embedded pseudoholomorphic curves
through fixed generic points (`TauCeti.pointConfigurationCount`). Along a generic path of almost
complex structures, with the points held fixed, the curves through the points change only by
local bifurcations: the curves taking part in one bifurcation are close to each other, so they
pass through the same points. This file proves that the count through the points is unchanged by
such bifurcations, transferring the invariance of the count without points proved in
`TauCeti.Geometry.Symplectic.JHolomorphic.Bifurcation.Basic`.

The transfer rests on the inclusion–exclusion formula of
`TauCeti.Geometry.Symplectic.JHolomorphic.PointConfigurationCount`. Write `s_T` for the
candidates of `s` whose images avoid a set `T` of points. A configuration of `s` lies in `s_T`
exactly when its images avoid `T`, and the alternating sum `∑ (-1) ^ |T|` over the sets `T`
avoided by the images is `1` when the images cover all the points and `0` otherwise. Hence,
when the configurations of `s` in class `A` are finite in number
(`TauCeti.pointConfigurationCount_eq_sum_neg_one_pow`),

`N^P_s(A) = ∑_{T ⊆ P} (-1) ^ |T| N_{s_T}(A)`,

where `N^P` is the count through the points `P` and `N` the count without points. Consequently:

* **Point-refined local counts.** Replacing a cluster `K` by a cluster `K'` with the same
  compatibility with `s` does not change the count through the points in class `A` if, for every
  set `T` of points, the members of `K` and of `K'` avoiding `T` have the same local counts
  (`TauCeti.pointConfigurationCount_union_eq_union`).
* **Clusters through common points.** If every member of `K` and of `K'` passes through the same
  set of points, and replacing `K` by `K'` leaves the count without points unchanged over every
  subfamily of `s`, then it leaves the count through the points unchanged
  (`TauCeti.pointConfigurationCount_union_eq_union_of_forall_eq`).

The second criterion applies to each bifurcation of
`TauCeti.Geometry.Symplectic.JHolomorphic.Bifurcation.Basic`, whose hypotheses pass to every
subfamily: ordinary birth and death of two curves through the same points
(`TauCeti.pointConfigurationCount_insert_insert_of_weight_eq_neg`), replacement of a cluster of
tori on a ray (`TauCeti.pointConfigurationCount_union_eq_union_of_coeff_rayTorusWeightSeries_eq`),
birth and death of tori (`TauCeti.pointConfigurationCount_insert_insert_of_eq_torusWeight_not`),
period doubling
(`TauCeti.pointConfigurationCount_insert_eq_insert_insert_of_eq_torusWeight_castSucc`,
`TauCeti.pointConfigurationCount_insert_eq_insert_insert_of_eq_torusWeight_succ`) and a change
of index of a torus below its double cover
(`TauCeti.pointConfigurationCount_insert_eq_insert_of_area_lt_two_mul`). For generic points, the
tori of index zero pass through none of them, so the torus statements apply with empty point sets.

As in the count without points, the candidates, their classes, point incidences and weights, and
the description of a bifurcation as the replacement of one cluster by another, are inputs here.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* D. McDuff, *Lectures on Gromov invariants for symplectic 4-manifolds*, arXiv:dg-ga/9606005.
-/

public section

namespace TauCeti

variable {ι H P R : Type*}

/-! ### Replacing a cluster -/

section Cluster

variable {r : ι → ι → Prop} {pts : ι → Finset P} {s K K' : Set ι}

/-- The members of a family `K` all passing through the points `Q` avoid `T` together. -/
private theorem sep_disjoint_eq_sep {Q T : Finset P} (hK : ∀ c ∈ K, pts c = Q) :
    {c ∈ K | Disjoint (pts c) T} = {c ∈ K | Disjoint Q T} := by
  ext c
  exact and_congr_right fun hc ↦ by rw [hK c hc]

variable [CommRing R] {w : ι → ℕ → R}

/-- **Replacing a cluster, through the points.** Let `K` and `K'` be two clusters of candidates,
disjoint from `s`, with the same compatibility with `s`: a candidate `d ∈ s` is compatible with a
member of `K`, or of `K'`, exactly when `d ∈ U`. Suppose that the configurations of `K ∪ s` and of
`K' ∪ s` in class `A` are finite in number. If for every set `T` of points, the members of `K`
and of `K'` avoiding `T` have the same local counts in every class `B ≠ 0` for which the members
of `U` avoiding `T` have a configuration in class `A - B`, then replacing `K` by `K'` does not
change the count through the points in class `A`. -/
theorem pointConfigurationCount_union_eq_union [AddCommGroup H] {cls : ι → H} {U : Set ι} {A : H}
    (hKs : Disjoint K s) (hK's : Disjoint K' s) (hU : ∀ k ∈ K, ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U)
    (hU' : ∀ k ∈ K', ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U)
    (hfin : (compatibleConfigurations r cls (K ∪ s) A).Finite)
    (hfin' : (compatibleConfigurations r cls (K' ∪ s) A).Finite)
    (hK : ∀ (T : Finset P), ∀ B ≠ 0,
      (compatibleConfigurations r cls {d ∈ U | Disjoint (pts d) T} (A - B)).Nonempty →
        configurationCount r cls w {k ∈ K | Disjoint (pts k) T} B =
          configurationCount r cls w {k ∈ K' | Disjoint (pts k) T} B) :
    pointConfigurationCount r cls pts w (K ∪ s) A =
      pointConfigurationCount r cls pts w (K' ∪ s) A := by
  cases finite_or_infinite P
  swap
  · rw [pointConfigurationCount_eq_zero_of_infinite, pointConfigurationCount_eq_zero_of_infinite]
  have := Fintype.ofFinite P
  rw [pointConfigurationCount_eq_sum_neg_one_pow hfin,
    pointConfigurationCount_eq_sum_neg_one_pow hfin']
  refine Finset.sum_congr rfl fun T _ ↦ congrArg _ ?_
  -- Restricted to the candidates avoiding `T`, the clusters still have the same compatibility
  -- with the remaining candidates.
  have hcomp {L : Set ι} (hL : ∀ k ∈ L, ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U) :
      ∀ k ∈ {k ∈ L | Disjoint (pts k) T}, ∀ d ∈ {d ∈ s | Disjoint (pts d) T},
        r k d ∧ r d k ↔ d ∈ {d ∈ U ∩ s | Disjoint (pts d) T} :=
    fun k hk d hd ↦ (hL k hk.1 d hd.1).trans ⟨fun h ↦ ⟨⟨h, hd.1⟩, hd.2⟩, fun h ↦ h.1.1⟩
  have hsub {L : Set ι} : {c ∈ L | Disjoint (pts c) T} ∪ {c ∈ s | Disjoint (pts c) T} ⊆ L ∪ s :=
    Set.union_subset_union (Set.sep_subset _ _) (Set.sep_subset _ _)
  have hUT : {d ∈ U ∩ s | Disjoint (pts d) T} ⊆ {d ∈ U | Disjoint (pts d) T} :=
    fun d hd ↦ ⟨hd.1.1, hd.2⟩
  simp only [Set.mem_union, Set.sep_union]
  exact configurationCount_union_eq_union (U := {d ∈ U ∩ s | Disjoint (pts d) T})
    (hKs.mono (Set.sep_subset _ _) (Set.sep_subset _ _))
    (hK's.mono (Set.sep_subset _ _) (Set.sep_subset _ _)) (fun d hd ↦ ⟨hd.1.2, hd.2⟩)
    (hcomp hU) (hcomp hU') (hfin.subset (compatibleConfigurations_mono hsub))
    (hfin'.subset (compatibleConfigurations_mono hsub)) fun B hB hn ↦
      hK T B hB (hn.mono (compatibleConfigurations_mono hUT))

/-- **Replacing a cluster through common points.** Let `K` and `K'` be two families of candidates
all of whose members pass through the same set `Q` of points. Suppose that the configurations of
`K ∪ s` and of `K' ∪ s` in class `A` are finite in number, and that replacing `K` by `K'` does not
change the count without points in class `A` over `K ∪ t`, for every subfamily `t ⊆ s`. Then it
does not change the count through the points in class `A`. -/
theorem pointConfigurationCount_union_eq_union_of_forall_eq [AddCommMonoid H] {cls : ι → H}
    {A : H} {Q : Finset P} (hK : ∀ c ∈ K, pts c = Q) (hK' : ∀ c ∈ K', pts c = Q)
    (hfin : (compatibleConfigurations r cls (K ∪ s) A).Finite)
    (hfin' : (compatibleConfigurations r cls (K' ∪ s) A).Finite)
    (h : ∀ t ⊆ s, configurationCount r cls w (K ∪ t) A = configurationCount r cls w (K' ∪ t) A) :
    pointConfigurationCount r cls pts w (K ∪ s) A =
      pointConfigurationCount r cls pts w (K' ∪ s) A := by
  cases finite_or_infinite P
  swap
  · rw [pointConfigurationCount_eq_zero_of_infinite, pointConfigurationCount_eq_zero_of_infinite]
  have := Fintype.ofFinite P
  rw [pointConfigurationCount_eq_sum_neg_one_pow hfin,
    pointConfigurationCount_eq_sum_neg_one_pow hfin']
  refine Finset.sum_congr rfl fun T _ ↦ congrArg _ ?_
  simp only [Set.mem_union, Set.sep_union]
  rw [sep_disjoint_eq_sep hK, sep_disjoint_eq_sep hK']
  by_cases hQ : Disjoint Q T
  · simp only [hQ, and_true]
    exact h _ (Set.sep_subset _ _)
  · simp [hQ]

/-- Adding two candidates `c` and `d` through the same points transfers from the count without
points to the count through the points, provided it holds over every subfamily. -/
private theorem pointConfigurationCount_insert_insert_eq [AddCommMonoid H] {cls : ι → H} {A : H}
    {c d : ι} (hpts : pts d = pts c)
    (hfin : (compatibleConfigurations r cls (insert c (insert d s)) A).Finite)
    (h : ∀ t ⊆ s, configurationCount r cls w (insert c (insert d t)) A =
      configurationCount r cls w t A) :
    pointConfigurationCount r cls pts w (insert c (insert d s)) A =
      pointConfigurationCount r cls pts w s A := by
  have hunion (t : Set ι) : insert c (insert d t) = ({c, d} : Set ι) ∪ t := by
    rw [Set.insert_union, Set.singleton_union]
  rw [hunion] at hfin ⊢
  conv_rhs => rw [← Set.empty_union s]
  refine pointConfigurationCount_union_eq_union_of_forall_eq (Q := pts c)
    (by rintro e (rfl | rfl) <;> simp [hpts]) (fun _ h ↦ h.elim) hfin
    (hfin.subset (compatibleConfigurations_mono (by simp))) fun t ht ↦ ?_
  rw [← hunion, Set.empty_union]
  exact h t ht

end Cluster

/-! ### Ordinary birth and death -/

section BirthDeath

variable [AddCommGroup H] [CommRing R] {r : ι → ι → Prop} {cls : ι → H}
  {pts : ι → Finset P} {w : ι → ℕ → R} {s : Set ι} {A : H} {c d : ι}

/-- **Ordinary birth and death through the points.** Let `c` and `d` be two incompatible
candidates outside `s` of the same class, through the same points, with the same compatibility
with the candidates of `s` and opposite weights `w d k = -w c k` for `k ≠ 0`. If the
configurations of `s ∪ {c, d}` in class `A` are finite in number, then adding `c` and `d` to `s`
does not change the count through the points in class `A`. -/
theorem pointConfigurationCount_insert_insert_of_weight_eq_neg (hcd : c ≠ d) (hc : c ∉ s)
    (hd : d ∉ s) (hr : ¬(r c d ∧ r d c)) (hcls : cls d = cls c) (hpts : pts d = pts c)
    (hcomp : ∀ e ∈ s, r d e ∧ r e d ↔ r c e ∧ r e c) (hw : ∀ k ≠ 0, w d k = -w c k)
    (hfin : (compatibleConfigurations r cls (insert c (insert d s)) A).Finite) :
    pointConfigurationCount r cls pts w (insert c (insert d s)) A =
      pointConfigurationCount r cls pts w s A :=
  pointConfigurationCount_insert_insert_eq hpts hfin fun t ht ↦
    configurationCount_insert_insert_of_weight_eq_neg hcd (fun h ↦ hc (ht h))
      (fun h ↦ hd (ht h)) hr hcls (fun e he ↦ hcomp e (ht he)) hw
      (hfin.subset (compatibleConfigurations_mono (by gcongr)))

end BirthDeath

/-! ### Tori -/

section Ray

variable [AddCommGroup H] {r : ι → ι → Prop} {cls : ι → H} {pts : ι → Finset P}
  {w : ι → ℕ → ℤ} {s U : Set ι} {A A₀ : H} {ω : H →+ ℝ} {m : ι → ℕ+} {σ : ι → Bool}
  {i : ι → Fin 4} {Q : Finset P}

/-- **Replacing a cluster of tori through the points.** Let `K` and `K'` be finite families of
pairwise compatible tori, disjoint from `s`, on the ray of a class `A₀`, all passing through the
same set `Q` of points, the torus `c` having class `m c • A₀` and the four-twist weights
`w c = w_(σ c, i c)`. Suppose that a candidate `d ∈ s` is compatible with a torus of `K`, or of
`K'`, exactly when `d ∈ U`. If the candidates have positive area `ω`, with finitely many of area
at most `ω A`, and the ray series `∏ f_(σ c, i c)(t ^ m c)` of `K` and `K'` have the same
coefficients up to area `ω A`, then replacing `K` by `K'` does not change the count through the
points in class `A`. -/
theorem pointConfigurationCount_union_eq_union_of_coeff_rayTorusWeightSeries_eq
    {K K' : Finset ι} (hKs : Disjoint (K : Set ι) s) (hK's : Disjoint (K' : Set ι) s)
    (hU : ∀ k ∈ K, ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U)
    (hU' : ∀ k ∈ K', ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U)
    (hK : (K : Set ι).Pairwise r) (hK' : (K' : Set ι).Pairwise r)
    (hcls : ∀ c ∈ (↑K ∪ ↑K' : Set ι), cls c = (m c : ℕ) • A₀)
    (hw : ∀ c ∈ (↑K ∪ ↑K' : Set ι), w c = torusWeight (σ c) (i c))
    (hpts : ∀ c ∈ (↑K ∪ ↑K' : Set ι), pts c = Q)
    (hpos : ∀ c ∈ (↑K ∪ ↑K' : Set ι) ∪ s, 0 < ω (cls c))
    (hfin : {c ∈ (↑K ∪ ↑K' : Set ι) ∪ s | ω (cls c) ≤ ω A}.Finite)
    (hseries : ∀ j : ℕ, ω (j • A₀) ≤ ω A →
      PowerSeries.coeff j (rayTorusWeightSeries K m σ i) =
        PowerSeries.coeff j (rayTorusWeightSeries K' m σ i)) :
    pointConfigurationCount r cls pts w (↑K ∪ s) A =
      pointConfigurationCount r cls pts w (↑K' ∪ s) A := by
  have hsub : (↑K ∪ s : Set ι) ⊆ (↑K ∪ ↑K') ∪ s :=
    Set.union_subset_union_left _ Set.subset_union_left
  have hsub' : (↑K' ∪ s : Set ι) ⊆ (↑K ∪ ↑K') ∪ s :=
    Set.union_subset_union_left _ Set.subset_union_right
  refine pointConfigurationCount_union_eq_union_of_forall_eq
    (fun c hc ↦ hpts c (Or.inl hc)) (fun c hc ↦ hpts c (Or.inr hc))
    (finite_compatibleConfigurations (fun c hc ↦ hpos c (hsub hc))
      (hfin.subset fun c hc ↦ ⟨hsub hc.1, hc.2⟩))
    (finite_compatibleConfigurations (fun c hc ↦ hpos c (hsub' hc))
      (hfin.subset fun c hc ↦ ⟨hsub' hc.1, hc.2⟩)) fun t ht ↦ ?_
  have hmono : (↑K ∪ ↑K' : Set ι) ∪ t ⊆ (↑K ∪ ↑K') ∪ s := Set.union_subset_union_right _ ht
  exact configurationCount_union_eq_union_of_coeff_rayTorusWeightSeries_eq (U := U ∩ t)
    (hKs.mono_right ht) (hK's.mono_right ht) Set.inter_subset_right
    (fun k hk d hd ↦ (hU k hk d (ht hd)).trans (and_iff_left hd).symm)
    (fun k hk d hd ↦ (hU' k hk d (ht hd)).trans (and_iff_left hd).symm) hK hK' hcls hw
    (fun c hc ↦ hpos c (hmono hc)) (hfin.subset fun c hc ↦ ⟨hmono hc.1, hc.2⟩) hseries

/-- **Birth and death of tori through the points.** Let `c` and `d` be two compatible tori outside
`s` of the same class, through the same points, with the same compatibility with the candidates
of `s`, with the same index and opposite determinant signs: `w c = w_(σ, j)` and
`w d = w_(!σ, j)`. If the candidates have positive area `ω`, with finitely many of area at most
`ω A`, then adding `c` and `d` to `s` does not change the count through the points in class
`A`. -/
theorem pointConfigurationCount_insert_insert_of_eq_torusWeight_not {c d : ι} (hc : c ∉ s)
    (hd : d ∉ s) (hr : r c d ∧ r d c) (hcls : cls d = cls c) (hpts : pts d = pts c)
    (hcomp : ∀ e ∈ s, r d e ∧ r e d ↔ r c e ∧ r e c) {σ₀ : Bool} {j : Fin 4}
    (hwc : w c = torusWeight σ₀ j) (hwd : w d = torusWeight (!σ₀) j)
    (hpos : ∀ e ∈ insert c (insert d s), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert d s) | ω (cls e) ≤ ω A}.Finite) :
    pointConfigurationCount r cls pts w (insert c (insert d s)) A =
      pointConfigurationCount r cls pts w s A :=
  pointConfigurationCount_insert_insert_eq hpts (finite_compatibleConfigurations hpos hfin)
    fun t ht ↦
    have hmono : insert c (insert d t) ⊆ insert c (insert d s) := by gcongr
    configurationCount_insert_insert_of_eq_torusWeight_not (fun h ↦ hc (ht h))
      (fun h ↦ hd (ht h)) hr hcls (fun e he ↦ hcomp e (ht he)) hwc hwd
      (fun e he ↦ hpos e (hmono he)) (hfin.subset fun e he ↦ ⟨hmono he.1, he.2⟩)

/-- Replacing a torus `c` by two tori `c'` and `d` through the same points transfers from the
count without points to the count through the points, provided it holds over every subfamily. -/
private theorem pointConfigurationCount_insert_eq_insert_insert {c c' d : ι}
    (hpts' : pts c' = pts c) (hptsd : pts d = pts c)
    (hpos : ∀ e ∈ insert c (insert c' (insert d s)), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert c' (insert d s)) | ω (cls e) ≤ ω A}.Finite)
    (h : ∀ t ⊆ s, configurationCount r cls w (insert c t) A =
      configurationCount r cls w (insert c' (insert d t)) A) :
    pointConfigurationCount r cls pts w (insert c s) A =
      pointConfigurationCount r cls pts w (insert c' (insert d s)) A := by
  have hunion (t : Set ι) : insert c' (insert d t) = ({c', d} : Set ι) ∪ t := by
    rw [Set.insert_union, Set.singleton_union]
  have hconf := finite_compatibleConfigurations (r := r) hpos hfin
  rw [← Set.singleton_union, hunion]
  refine pointConfigurationCount_union_eq_union_of_forall_eq (Q := pts c) (by simp)
    (by rintro e (rfl | rfl) <;> simp [hpts', hptsd])
    (hconf.subset (compatibleConfigurations_mono ?_))
    (hconf.subset (compatibleConfigurations_mono ?_)) fun t ht ↦ ?_
  · rw [Set.singleton_union]
    gcongr
    exact (Set.subset_insert _ _).trans (Set.subset_insert _ _)
  · rw [← hunion]
    exact Set.subset_insert _ _
  · rw [Set.singleton_union, ← hunion]
    exact h t ht

/-- **Period doubling through the points.** Let `c` be a torus outside `s` of label `(σ, j)`,
`j ∈ {0, 1, 2}`, and let `c'` and `d` be compatible tori outside `s`: `c'` of the class of `c` and
label `(σ, j + 1)`, and `d` of twice that class and label `(σ, j % 2)`, all three through the same
points and with the same compatibility with the candidates of `s`. If the candidates have
positive area `ω`, with finitely many of area at most `ω A`, then replacing `c` by `c'` and `d`
does not change the count through the points in class `A`. -/
theorem pointConfigurationCount_insert_eq_insert_insert_of_eq_torusWeight_castSucc {c c' d : ι}
    (hc : c ∉ s) (hc' : c' ∉ s) (hd : d ∉ s) (hr : r c' d ∧ r d c') (hcls' : cls c' = cls c)
    (hclsd : cls d = 2 • cls c) (hpts' : pts c' = pts c) (hptsd : pts d = pts c)
    (hcomp' : ∀ e ∈ s, r c' e ∧ r e c' ↔ r c e ∧ r e c)
    (hcompd : ∀ e ∈ s, r d e ∧ r e d ↔ r c e ∧ r e c) {σ₀ : Bool} {j : Fin 3}
    (hwc : w c = torusWeight σ₀ j.castSucc) (hwc' : w c' = torusWeight σ₀ j.succ)
    (hwd : w d = torusWeight σ₀ (j % 2).castSucc)
    (hpos : ∀ e ∈ insert c (insert c' (insert d s)), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert c' (insert d s)) | ω (cls e) ≤ ω A}.Finite) :
    pointConfigurationCount r cls pts w (insert c s) A =
      pointConfigurationCount r cls pts w (insert c' (insert d s)) A :=
  pointConfigurationCount_insert_eq_insert_insert hpts' hptsd hpos hfin fun t ht ↦
    have hmono : insert c (insert c' (insert d t)) ⊆ insert c (insert c' (insert d s)) := by
      gcongr
    configurationCount_insert_eq_insert_insert_of_eq_torusWeight_castSucc (fun h ↦ hc (ht h))
      (fun h ↦ hc' (ht h)) (fun h ↦ hd (ht h)) hr hcls' hclsd (fun e he ↦ hcomp' e (ht he))
      (fun e he ↦ hcompd e (ht he)) hwc hwc' hwd (fun e he ↦ hpos e (hmono he))
      (hfin.subset fun e he ↦ ⟨hmono he.1, he.2⟩)

/-- **Period doubling through the points**, in the other direction. Let `c` be a torus outside `s`
of label `(σ, j + 1)`, `j ∈ {0, 1, 2}`, and let `c'` and `d` be compatible tori outside `s`: `c'`
of the class of `c` and label `(σ, j)`, and `d` of twice that class and label `(!σ, j % 2)`, all
three through the same points and with the same compatibility with the candidates of `s`. If the
candidates have positive area `ω`, with finitely many of area at most `ω A`, then replacing `c`
by `c'` and `d` does not change the count through the points in class `A`. -/
theorem pointConfigurationCount_insert_eq_insert_insert_of_eq_torusWeight_succ {c c' d : ι}
    (hc : c ∉ s) (hc' : c' ∉ s) (hd : d ∉ s) (hr : r c' d ∧ r d c') (hcls' : cls c' = cls c)
    (hclsd : cls d = 2 • cls c) (hpts' : pts c' = pts c) (hptsd : pts d = pts c)
    (hcomp' : ∀ e ∈ s, r c' e ∧ r e c' ↔ r c e ∧ r e c)
    (hcompd : ∀ e ∈ s, r d e ∧ r e d ↔ r c e ∧ r e c) {σ₀ : Bool} {j : Fin 3}
    (hwc : w c = torusWeight σ₀ j.succ) (hwc' : w c' = torusWeight σ₀ j.castSucc)
    (hwd : w d = torusWeight (!σ₀) (j % 2).castSucc)
    (hpos : ∀ e ∈ insert c (insert c' (insert d s)), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert c' (insert d s)) | ω (cls e) ≤ ω A}.Finite) :
    pointConfigurationCount r cls pts w (insert c s) A =
      pointConfigurationCount r cls pts w (insert c' (insert d s)) A :=
  pointConfigurationCount_insert_eq_insert_insert hpts' hptsd hpos hfin fun t ht ↦
    have hmono : insert c (insert c' (insert d t)) ⊆ insert c (insert c' (insert d s)) := by
      gcongr
    configurationCount_insert_eq_insert_insert_of_eq_torusWeight_succ (fun h ↦ hc (ht h))
      (fun h ↦ hc' (ht h)) (fun h ↦ hd (ht h)) hr hcls' hclsd (fun e he ↦ hcomp' e (ht he))
      (fun e he ↦ hcompd e (ht he)) hwc hwc' hwd (fun e he ↦ hpos e (hmono he))
      (hfin.subset fun e he ↦ ⟨hmono he.1, he.2⟩)

/-- **Changing the index of a torus below its double cover, through the points.** Let `c` and `c'`
be tori outside `s` of the same class, through the same points, with the same determinant sign
`σ`, with any indices `j` and `j'`, and with the same compatibility with the candidates of `s`. If
the candidates have positive area `ω`, with finitely many of area at most `ω A`, and `ω A` is less
than the area of the double cover of `c`, then replacing `c` by `c'` does not change the count
through the points in class `A`. -/
theorem pointConfigurationCount_insert_eq_insert_of_area_lt_two_mul {c c' : ι} (hc : c ∉ s)
    (hc' : c' ∉ s) (hcls' : cls c' = cls c) (hpts' : pts c' = pts c)
    (hcomp' : ∀ e ∈ s, r c' e ∧ r e c' ↔ r c e ∧ r e c)
    {σ₀ : Bool} {j j' : Fin 4} (hwc : w c = torusWeight σ₀ j) (hwc' : w c' = torusWeight σ₀ j')
    (hpos : ∀ e ∈ insert c (insert c' s), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert c' s) | ω (cls e) ≤ ω A}.Finite) (hA : ω A < 2 * ω (cls c)) :
    pointConfigurationCount r cls pts w (insert c s) A =
      pointConfigurationCount r cls pts w (insert c' s) A := by
  have hconf := finite_compatibleConfigurations (r := r) hpos hfin
  rw [← Set.singleton_union, ← Set.singleton_union]
  refine pointConfigurationCount_union_eq_union_of_forall_eq (Q := pts c) (by simp)
    (by simp [hpts']) (hconf.subset (compatibleConfigurations_mono ?_))
    (hconf.subset (compatibleConfigurations_mono ?_)) fun t ht ↦ ?_
  · rw [Set.singleton_union]
    gcongr
    exact Set.subset_insert _ _
  · rw [Set.singleton_union]
    exact Set.subset_insert _ _
  · have hmono : insert c (insert c' t) ⊆ insert c (insert c' s) := by gcongr
    rw [Set.singleton_union, Set.singleton_union]
    exact configurationCount_insert_eq_insert_of_area_lt_two_mul (fun h ↦ hc (ht h))
      (fun h ↦ hc' (ht h)) hcls' (fun e he ↦ hcomp' e (ht he)) hwc hwc'
      (fun e he ↦ hpos e (hmono he)) (hfin.subset fun e he ↦ ⟨hmono he.1, he.2⟩) hA

end Ray

end TauCeti

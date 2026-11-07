/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Groupoid.Average
public import TauCeti.Geometry.Manifold.Groupoid.Cutoff
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Invariant smooth partitions of unity on proper étale groupoids

A smooth cutoff averages an ordinary smooth partition of unity to one whose functions take
equal values at the endpoints of every arrow. The average preserves subordination to saturated
covers and fixes invariant partitions. Applied to the existence of ordinary partitions and
smooth cutoffs, this gives invariant smooth partitions on proper étale presentations.
This extends the action-presentation construction `SmoothPartitionOfUnity.cutoffAverage`
to native groupoids without choosing global group labels.

All arrows are counted, including ineffective isotropy. Local finiteness follows from the
compactness of the arrows with source in a compact set and target in the cutoff support,
so no compact-support assumption on the original partition is needed. Such partitions glue
invariant local bundle and metric data on the object manifold.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2.

The cutoff construction is `TauCeti.Quiver.exists_isCutoff_contMDiff`; averaging uses
`TauCeti.Quiver.IsCutoff.average` and its support and smoothness theorems.
-/

public noncomputable section

open CategoryTheory Function Set Topology
open scoped Manifold ContDiff

namespace SmoothPartitionOfUnity

variable {ι E E' H H' C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace C] [ChartedSpace H C] [T2Space C] {s : Set C} {c : C → ℝ}

section Quiver

variable [Quiver C] [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [T2Space (Quiver.Total C)] [LocallyCompactSpace C]

variable (f : SmoothPartitionOfUnity ι I C s) (hc : TauCeti.Quiver.IsCutoff c)
  (hcs : CMDiff ∞ c)
  (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
  (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
  (hstable : ∀ ⦃x y : C⦄, (x ⟶ y) → x ∈ s → y ∈ s)

/-- The cutoff average of a smooth partition on a set preserved by all arrows. For a groupoid,
its functions are invariant under every arrow (`groupoidAverage_target_eq_source`). -/
def groupoidAverage : SmoothPartitionOfUnity ι I C s where
  toFun i := ⟨hc.average (f i), hc.contMDiff_average hcs hs ht (f i).contMDiff⟩
  locallyFinite' x := by
    obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
    have hT : IsCompact (Quiver.Total.right ''
        (Quiver.Total.left ⁻¹' K ∩ Quiver.Total.right ⁻¹' tsupport c)) :=
      (hc.isCompact_preimage_inter hK).image ht.continuous
    refine ⟨K, hxK, (f.locallyFinite.finite_nonempty_inter_compact hT).subset ?_⟩
    rintro i ⟨y, hy, hyK⟩
    obtain ⟨a, ⟨hac, haf⟩, hay⟩ := hc.support_average_subset (f i) hy
    exact ⟨a.right, haf, a,
      ⟨by simpa only [mem_preimage, hay] using hyK, subset_tsupport c hac⟩, rfl⟩
  nonneg' i x := by
    simp only [ContMDiffMap.coeFn_mk, TauCeti.Quiver.IsCutoff.average_apply, smul_eq_mul]
    exact finsum_nonneg fun a ↦ mul_nonneg (hc.nonneg _) (f.nonneg i a.1)
  sum_eq_one' x hx := by
    simp only [ContMDiffMap.coeFn_mk]
    rw [hc.finsum_average (fun i y ↦ f i y) (fun y ↦ f.locallyFinite.point_finite y) x]
    calc
      hc.average (fun y ↦ ∑ᶠ i, f i y) x = ∑ᶠ a : Σ y, x ⟶ y, c a.1 := by
        rw [TauCeti.Quiver.IsCutoff.average_apply]
        exact finsum_congr fun a ↦ by rw [f.sum_eq_one (hstable a.2 hx)]; simp
      _ = 1 := by
        simpa only [Quiver.Total.finsum_mem_preimage_left_singleton] using hc.finsum_eq_one x
  sum_le_one' x := by
    simp only [ContMDiffMap.coeFn_mk]
    rw [hc.finsum_average (fun i y ↦ f i y) (fun y ↦ f.locallyFinite.point_finite y) x]
    calc
      hc.average (fun y ↦ ∑ᶠ i, f i y) x ≤ ∑ᶠ a : Σ y, x ⟶ y, c a.1 := by
        simp only [TauCeti.Quiver.IsCutoff.average_apply, smul_eq_mul]
        exact finsum_le_finsum
          ((hc.hasFiniteSupport x).subset fun _ ha ↦ left_ne_zero_of_mul ha)
          (hc.hasFiniteSupport x) fun a ↦
            mul_le_of_le_one_right (hc.nonneg _) (f.sum_le_one a.1)
      _ = 1 := by
        simpa only [Quiver.Total.finsum_mem_preimage_left_singleton] using hc.finsum_eq_one x

/-- Each function of the averaged partition is the cutoff average of the corresponding
function of the original partition. -/
@[simp]
theorem groupoidAverage_apply (i : ι) (x : C) :
    f.groupoidAverage hc hcs hs ht hstable i x = hc.average (f i) x := (rfl)

/-- Averaging fixes an invariant smooth partition. -/
theorem groupoidAverage_eq_self
    (hf : ∀ i ⦃x y : C⦄, (x ⟶ y) → f i y = f i x) :
    f.groupoidAverage hc hcs hs ht hstable = f := by
  apply DFunLike.ext
  intro i
  apply ContMDiffMap.ext
  intro x
  exact congrFun (hc.average_eq_self (f i) (hf i)) x

end Quiver

section Groupoid

variable [Category C] [IsGroupoid C] [TopologicalSpace (Quiver.Total C)]
  [ChartedSpace H' (Quiver.Total C)] [T2Space (Quiver.Total C)] [LocallyCompactSpace C]
  (f : SmoothPartitionOfUnity ι I C s) (hc : TauCeti.Quiver.IsCutoff c)
  (hcs : CMDiff ∞ c)
  (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
  (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
  (hstable : ∀ ⦃x y : C⦄, (x ⟶ y) → x ∈ s → y ∈ s)

/-- Every averaged partition function takes equal values at the endpoints of an arrow. -/
theorem groupoidAverage_target_eq_source (i : ι) {x y : C} (g : x ⟶ y) :
    f.groupoidAverage hc hcs hs ht hstable i y = f.groupoidAverage hc hcs hs ht hstable i x :=
  hc.average_target_eq_source (f i) g

variable {f hc hcs hs ht hstable}

/-- Averaging preserves subordination to a saturated cover. -/
theorem IsSubordinate.groupoidAverage {U : ι → Set C} (hf : f.IsSubordinate U)
    (hU : ∀ i ⦃x y : C⦄, (x ⟶ y) → x ∈ U i → y ∈ U i) :
    (f.groupoidAverage hc hcs hs ht hstable).IsSubordinate U := by
  intro i x hx
  obtain ⟨a, ⟨-, ha⟩, rfl⟩ := hc.tsupport_average_subset hs.contMDiff.continuous ht.continuous
    (f i) hx
  exact hU i (inv a.hom) (hf i ha)

end Groupoid

variable [Groupoid C] [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [T2Space (Quiver.Total C)]

/-- A closed saturated set in a proper étale presentation admits invariant smooth partitions
of unity subordinate to any saturated open cover. -/
theorem exists_isSubordinate_groupoid_invariant [FiniteDimensional ℝ E] [IsManifold I ∞ C]
    [SigmaCompactSpace C] (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hclosed : IsClosed s) (hstable : ∀ ⦃x y : C⦄, (x ⟶ y) → x ∈ s → y ∈ s)
    (U : ι → Set C) (ho : ∀ i, IsOpen (U i)) (hcover : s ⊆ ⋃ i, U i)
    (hU : ∀ i ⦃x y : C⦄, (x ⟶ y) → x ∈ U i → y ∈ U i) :
    ∃ f : SmoothPartitionOfUnity ι I C s,
      f.IsSubordinate U ∧ ∀ i ⦃x y : C⦄, (x ⟶ y) → f i y = f i x := by
  let : LocallyCompactSpace C := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨c, hc, hcs⟩ := TauCeti.Quiver.exists_isCutoff_contMDiff (I := I) hp hs ht
  obtain ⟨f, hf⟩ := exists_isSubordinate I hclosed U ho hcover
  exact ⟨f.groupoidAverage hc hcs hs ht.contMDiff hstable,
    hf.groupoidAverage (hc := hc) (hcs := hcs) (hs := hs) (ht := ht.contMDiff)
      (hstable := hstable) hU,
    fun i _ _ g ↦ f.groupoidAverage_target_eq_source hc hcs hs ht.contMDiff hstable i g⟩

end SmoothPartitionOfUnity

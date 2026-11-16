/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.LocallyFinite
public import TauCeti.Topology.Homotopy.Extension.Proper.DeformationRetract
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import TauCeti.Topology.CWComplex.Classical.Skeleton.Induction
import TauCeti.Topology.Homotopy.Extension.Ball

/-!
# Proper homotopy extension for strongly locally finite CW complexes

For a subcomplex `E` of an infinite-dimensional CW complex `C`, the cell-by-cell skeletal cylinder
retraction `r : I × C → I × C` onto `{0} × C ∪ I × E` need not be proper under local finiteness
alone; Farrell, Taylor, and Wagoner show that **strong local finiteness**
(`Topology.CWComplex.StronglyLocallyFinite`) makes `r` proper.

On any Hausdorff relative CW complex `(C, D)`, `r` can be built so that its values on each closed
`n`-cell stay inside the cell together with the image of its boundary under the lower-skeleton
retraction (`TauCeti.exists_retraction_cylinderExtensionDomain_base`), hence preserving every
closed-cell-saturated subset `S ⊆ X` — in particular every subcomplex `F` of `C`. When `C` admits a
locally finite cover by finite subcomplexes `(F k)`, any compact `K ⊆ C` meets only finitely many
`F k`, so `r⁻¹(I × K)` is closed inside a finite union of compact cylinders `I × F k`, proving
`IsProperMap r` (`Topology.RelCWComplex.Subcomplex.hasProperHomotopyExtensionProperty`).

## Main results

* `TauCeti.exists_retraction_cylinderExtensionDomain_base`: skeletal cylinder retraction onto
  `{0} × C ∪ I × D` preserving every closed-cell-saturated subset of `X`.
* `Topology.RelCWComplex.Subcomplex.hasProperHomotopyExtensionProperty`,
  `Topology.RelCWComplex.Subcomplex.hasProperHomotopyExtensionProperty_of_finiteDimensional`,
  `Topology.RelCWComplex.Subcomplex.hasProperHomotopyExtensionProperty_univ`,
  `TauCeti.hasProperHomotopyExtensionProperty_skeletonLT`: **proper homotopy extension for
  subcomplexes and skeletons** of strongly locally finite (or finite-dimensional locally finite)
  Hausdorff CW complexes.
* `Topology.RelCWComplex.Subcomplex.exists_proper_strong_deformation_retraction_iff`: a subcomplex
  is a proper strong deformation retract of `C` iff its inclusion is a proper homotopy equivalence.

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, Theorem 1.6.
* D. H. Baues, A. Quintero, *Infinite Homotopy Theory*, Kluwer Academic Publishers (2001),
  Chapter I, Proposition 3.8.
-/

public section

noncomputable section

open Filter Metric Set Topology Topology.RelCWComplex unitInterval

universe u

namespace TauCeti

section RelativeRetraction

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

/-- Single skeletal step of the cylinder retraction: given `G` on `I × skeletonLT C n` fixing time
`0` and landing in `cylinderExtensionDomain (Subtype.val ⁻¹' D)`, extend `G` over
`I × skeletonLT C (n + 1)` so that every `n`-cell-saturated subset preserved by `G` remains
preserved. -/
private theorem exists_retraction_step (n : ℕ)
    (G : C(I × (skeletonLT C n : Set X), I × C))
    (hG₀ : ∀ x, G (0, x) = (0, ⟨x, (skeletonLT C n).subset_complex x.2⟩))
    (hG_dom : ∀ p, G p ∈ cylinderExtensionDomain (Subtype.val ⁻¹' D : Set C)) :
    ∃ F : C(I × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X), I × C),
      (∀ t (x : X) (hx : x ∈ (skeletonLT C n : Set X)),
        F (t, ⟨x, skeletonLT_mono (by exact_mod_cast n.le_succ) hx⟩) = G (t, ⟨x, hx⟩)) ∧
      (∀ x, F (0, x) = (0, ⟨x, (skeletonLT C ((n + 1 : ℕ) : ℕ∞)).subset_complex x.2⟩)) ∧
      (∀ p, F p ∈ cylinderExtensionDomain (Subtype.val ⁻¹' D : Set C)) ∧
      ∀ {S : Set X},
        (∀ j : cell C n, (openCell n j ∩ S).Nonempty → closedCell n j ⊆ S) →
        (∀ t (x : (skeletonLT C n : Set X)), (x : X) ∈ S → ((G (t, x)).2 : X) ∈ S) →
        ∀ t (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)),
          (x : X) ∈ S → ((F (t, x)).2 : X) ∈ S := by
  let fCell (j : cell C n) : C(closedBall (0 : Fin n → ℝ) 1, I × C) :=
    ⟨fun y ↦ (0, ⟨map n j y, closedCell_subset_complex n j ⟨y, y.2, rfl⟩⟩),
      continuous_const.prodMk ((continuous_map_closedBall j).subtype_mk _)⟩
  let HCell (j : cell C n) :
      C(I × (Subtype.val ⁻¹' sphere (0 : Fin n → ℝ) 1 : Set (closedBall (0 : Fin n → ℝ) 1)),
        I × C) :=
    G.comp ⟨fun q ↦ (q.1, ⟨map n j q.2.1, cellFrontier_subset_skeletonLT n j ⟨q.2.1, q.2.2, rfl⟩⟩),
      continuous_fst.prodMk
        (((continuous_map_closedBall j).comp
          (continuous_subtype_val.comp continuous_snd)).subtype_mk _)⟩
  have hext (j : cell C n) : ∃ K : C(I × closedBall (0 : Fin n → ℝ) 1, I × C),
      (∀ y, K (0, y) = fCell j y) ∧
      (∀ t (y : closedBall (0 : Fin n → ℝ) 1) (hy : (y : Fin n → ℝ) ∈ sphere 0 1),
        K (t, y) = G (t, ⟨map n j y, cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩⟩)) ∧
      ∀ p, K p ∈ range (fCell j) ∪ range (HCell j) := by
    obtain ⟨K', hK'₀, hK's⟩ := (hasHomotopyExtensionProperty_sphere_closedBall
      (E := Fin n → ℝ)).exists_extension_of_isClosed
      (isClosed_sphere.preimage continuous_subtype_val) (Y := ↥(range (fCell j) ∪ range (HCell j)))
      ⟨fun w ↦ ⟨fCell j w, .inl (mem_range_self w)⟩, by fun_prop⟩
      ⟨fun q ↦ ⟨HCell j q, .inr (mem_range_self q)⟩, by fun_prop⟩ fun _ ↦ Subtype.ext (hG₀ _)
    exact ⟨⟨fun p ↦ (K' p).1, continuous_subtype_val.comp K'.continuous⟩,
      fun y ↦ congrArg Subtype.val (hK'₀ y), fun t y hy ↦ congrArg Subtype.val (hK's t ⟨y, hy⟩),
      fun p ↦ (K' p).2⟩
  choose K hK₀ hKs hKr using hext
  obtain ⟨F, hFG, hFK⟩ := exists_continuousMap_prod_skeletonLT_succ G K hKs
  refine ⟨F, hFG, fun x ↦ ?_, fun ⟨t, x⟩ ↦ ?_, fun {S} hSn hGS t x hxS ↦ ?_⟩
  · obtain hx | ⟨j, y, hy, hxy⟩ := mem_skeletonLT_or_exists_map x.2
    · exact (hFG 0 x hx).trans (hG₀ ⟨x, hx⟩)
    · obtain rfl : x = ⟨map n j y, map_mem_skeletonLT_succ j hy.le⟩ := Subtype.ext hxy.symm
      exact (hFK j 0 ⟨y, mem_closedBall_zero_iff.2 hy.le⟩).trans (hK₀ j _)
  · obtain hx | ⟨j, y, hy, hxy⟩ := mem_skeletonLT_or_exists_map x.2
    · exact hFG t x hx ▸ hG_dom _
    · obtain rfl : x = ⟨map n j y, map_mem_skeletonLT_succ j hy.le⟩ := Subtype.ext hxy.symm
      rw [hFK j t ⟨y, mem_closedBall_zero_iff.2 hy.le⟩]
      exact (hKr j _).elim (fun ⟨_, hw⟩ ↦ hw ▸ zero_mem_cylinderExtensionDomain _)
        fun ⟨_, hq⟩ ↦ hq ▸ hG_dom _
  · obtain hx | ⟨j, y, hy, hxy⟩ := mem_skeletonLT_or_exists_map x.2
    · exact hFG t x hx ▸ hGS t ⟨x, hx⟩ hxS
    · have hclosedS : closedCell n j ⊆ S := hSn j ⟨x, ⟨y, mem_ball_zero_iff.2 hy, hxy⟩, hxS⟩
      obtain rfl : x = ⟨map n j y, map_mem_skeletonLT_succ j hy.le⟩ := Subtype.ext hxy.symm
      rw [hFK j t ⟨y, mem_closedBall_zero_iff.2 hy.le⟩]
      exact (hKr j _).elim (fun ⟨w, hw⟩ ↦ hw ▸ hclosedS ⟨w, w.2, rfl⟩) fun ⟨q, hq⟩ ↦
        hq ▸ hGS q.1 _ (hclosedS (cellFrontier_subset_closedCell n j ⟨q.2.1, q.2.2, rfl⟩))

/-- Recursive sequence of skeletal cylinder retractions on `I × skeletonLT C (0 + j)`. -/
private def retractionSeq : (j : ℕ) →
    {G : C(I × (skeletonLT C ((0 + j : ℕ) : ℕ∞) : Set X), I × C) //
      (∀ x, G (0, x) = (0, ⟨x, (skeletonLT C _).subset_complex x.2⟩)) ∧
      ∀ p, G p ∈ cylinderExtensionDomain (Subtype.val ⁻¹' D : Set C)}
  | 0 =>
    ⟨⟨fun p ↦ (p.1, ⟨p.2, (skeletonLT C _).subset_complex p.2.2⟩),
        continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd |>.subtype_mk _)⟩,
      fun _ ↦ rfl,
      fun p ↦ mem_cylinderExtensionDomain_of_mem <| by
        have hx : (p.2 : X) ∈ (skeletonLT C (0 : ℕ∞) : Set X) := p.2.2
        rwa [skeletonLT_zero_eq_base] at hx⟩
  | j + 1 =>
    let prev := retractionSeq j
    let step := exists_retraction_step (0 + j) prev.1 prev.2.1 prev.2.2
    ⟨step.choose, step.choose_spec.2.1, step.choose_spec.2.2.1⟩

private lemma retractionSeq_succ_apply (j : ℕ) (t : I) (x : X)
    (hx : x ∈ (skeletonLT C ((0 + j : ℕ) : ℕ∞) : Set X)) :
    (retractionSeq (C := C) (j + 1)).1
        (t, ⟨x, skeletonLT_mono (by exact_mod_cast (0 + j).le_succ) hx⟩) =
      (retractionSeq (C := C) j).1 (t, ⟨x, hx⟩) := by
  rw [retractionSeq]
  exact (exists_retraction_step (0 + j) (retractionSeq j).1 (retractionSeq j).2.1
    (retractionSeq j).2.2).choose_spec.1 t x hx

private lemma retractionSeq_preserves {S : Set X}
    (hS : ∀ (n : ℕ) (i : cell C n), (openCell n i ∩ S).Nonempty → closedCell n i ⊆ S) :
    ∀ (j : ℕ) (t : I) (x : (skeletonLT C ((0 + j : ℕ) : ℕ∞) : Set X)),
      (x : X) ∈ S → (((retractionSeq (C := C) j).1 (t, x)).2 : X) ∈ S
  | 0, _, _, hxS => hxS
  | j + 1, t, x, hxS => by
    rw [retractionSeq]
    exact (exists_retraction_step (0 + j) (retractionSeq j).1 (retractionSeq j).2.1
      (retractionSeq j).2.2).choose_spec.2.2.2 (hS (0 + j)) (retractionSeq_preserves hS j) t x hxS

/-- **Skeletal cylinder retraction preserving cell-saturated subsets.** For any Hausdorff relative
CW complex `(C, D)`, there is a continuous retraction `r : I × C → I × C` onto
`{0} × C ∪ I × (Subtype.val ⁻¹' D)` such that `r` preserves every subset `S ⊆ X` which contains
`closedCell n i` whenever it meets `openCell n i`. -/
theorem exists_retraction_cylinderExtensionDomain_base :
    ∃ r : C(I × C, I × C),
      (∀ p, r p ∈ cylinderExtensionDomain (Subtype.val ⁻¹' D : Set C)) ∧
      (∀ p ∈ cylinderExtensionDomain (Subtype.val ⁻¹' D : Set C), r p = p) ∧
      ∀ {S : Set X},
        (∀ (n : ℕ) (i : cell C n), (openCell n i ∩ S).Nonempty → closedCell n i ⊆ S) →
        ∀ (t : I) (x : C), (x : X) ∈ S → ((r (t, x)).2 : X) ∈ S := by
  obtain ⟨r, hr_apply⟩ := exists_continuousMap_prod_complex_of_skeletonLT
    (fun j ↦ (retractionSeq (C := C) j).1) retractionSeq_succ_apply
  refine ⟨r, fun ⟨t, x⟩ ↦ ?_, fun ⟨t, x⟩ hp ↦ ?_, fun {S} hS t x hxS ↦ ?_⟩
  · obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add 0 x.2
    exact hr_apply j t x hj ▸ (retractionSeq (C := C) j).2.2 (t, ⟨x, hj⟩)
  · rcases mem_cylinderExtensionDomain_iff.1 hp with rfl | hxD
    · obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add 0 x.2
      exact (hr_apply j 0 x hj).trans ((retractionSeq (C := C) j).2.1 ⟨x, hj⟩)
    · exact hr_apply 0 t x ((skeletonLT C ((0 + 0 : ℕ) : ℕ∞)).base_subset hxD)
  · obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add 0 x.2
    exact hr_apply j t x hj ▸ retractionSeq_preserves hS j t ⟨x, hj⟩ hxS

end RelativeRetraction

section StronglyLocallyFinite

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-- **Farrell–Taylor–Wagoner proper cofibration theorem.** Every subcomplex `E` of a strongly
locally finite Hausdorff CW complex `C` has the proper homotopy extension property inside `C`. -/
@[alias_in Topology.CWComplex.Subcomplex]
theorem _root_.Topology.RelCWComplex.Subcomplex.hasProperHomotopyExtensionProperty
    [CWComplex.StronglyLocallyFinite C] (E : CWComplex.Subcomplex C) :
    HasProperHomotopyExtensionProperty (Subtype.val ⁻¹' (E : Set X) : Set C) := by
  rw [hasProperHomotopyExtensionProperty_iff_exists_retraction
    (E.closed.preimage continuous_subtype_val)]
  obtain ⟨r, hr_dom, hr_fix, hr_sat⟩ :=
    @exists_retraction_cylinderExtensionDomain_base X _ _ C E E.relCWComplex
  have hr_sub (F : CWComplex.Subcomplex C) (t : I) (x : C) (hx : (x : X) ∈ F) :
      ((r (t, x)).2 : X) ∈ F :=
    hr_sat (fun n i ⟨z, hzo, hzF⟩ ↦ by
      rw [E.openCell_relCWComplex] at hzo
      rw [E.closedCell_relCWComplex]
      exact F.closedCell_subset_of_mem ((F.mem_I_iff_of_mem_openCell hzo).2 hzF)) t x hx
  have hsnd : IsProperMap fun p : I × C ↦ (r p).2 := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨r.continuous.snd, fun K hK ↦ ?_⟩
    obtain ⟨ι, F, hF_fin, hF_cov, hF_lf⟩ :=
      CWComplex.StronglyLocallyFinite.exists_locallyFinite_finite_subcomplex (C := C)
    have hfin := hF_lf.finite_nonempty_inter_compact hK
    have hL_comp : IsCompact (⋃ k ∈ hfin.toFinset, (Subtype.val ⁻¹' (F k : Set X) : Set C)) :=
      hfin.toFinset.isCompact_biUnion fun k _ ↦ by
        have := hF_fin k
        exact RelCWComplex.isClosed.isProperMap_subtypeVal.isCompact_preimage
          CWComplex.isCompact_of_finite
    refine (isCompact_univ.prod hL_comp).of_isClosed_subset
      (hK.isClosed.preimage r.continuous.snd) fun ⟨t, x⟩ hxK ↦ ⟨trivial, ?_⟩
    obtain ⟨k, hxk⟩ := mem_iUnion.1 (hF_cov.symm.subset x.2)
    exact mem_biUnion (x := k) (hfin.mem_toFinset.2 ⟨(r (t, x)).2, hr_sub (F k) t x hxk, hxK⟩) hxk
  exact ⟨r, hsnd.prodMk_of_t2_left r.continuous.fst, hr_dom, hr_fix⟩

/-- On a finite-dimensional locally finite Hausdorff CW complex, every subcomplex has the proper
homotopy extension property. -/
@[alias_in Topology.CWComplex.Subcomplex]
theorem
    _root_.Topology.RelCWComplex.Subcomplex.hasProperHomotopyExtensionProperty_of_finiteDimensional
    [CWComplex.LocallyFinite C] [CWComplex.FiniteDimensional C] (E : CWComplex.Subcomplex C) :
    HasProperHomotopyExtensionProperty (Subtype.val ⁻¹' (E : Set X) : Set C) := by
  have := CWComplex.LocallyFinite.stronglyLocallyFinite_of_finiteDimensional (C := C)
  exact E.hasProperHomotopyExtensionProperty

/-- Every skeleton of a strongly locally finite Hausdorff CW complex has the proper homotopy
extension property inside the complex. -/
theorem hasProperHomotopyExtensionProperty_skeletonLT [CWComplex.StronglyLocallyFinite C]
    (n : ℕ∞) :
    HasProperHomotopyExtensionProperty
      (Subtype.val ⁻¹' (CWComplex.skeletonLT C n : Set X) : Set C) :=
  (CWComplex.skeletonLT C n).hasProperHomotopyExtensionProperty

/-- When `W` carries a strongly locally finite CW structure on `univ`, every subcomplex `E` has the
proper homotopy extension property as a subset of `W`. -/
@[alias_in Topology.CWComplex.Subcomplex]
theorem _root_.Topology.RelCWComplex.Subcomplex.hasProperHomotopyExtensionProperty_univ
    {W : Type u} [TopologicalSpace W] [T2Space W] [CWComplex (univ : Set W)]
    [CWComplex.StronglyLocallyFinite (univ : Set W)]
    (E : CWComplex.Subcomplex (univ : Set W)) :
    HasProperHomotopyExtensionProperty (E : Set W) := by
  have h := E.hasProperHomotopyExtensionProperty.image (Homeomorph.Set.univ W)
  rwa [Homeomorph.Set.univ_apply, image_preimage_eq_range_inter, Subtype.range_coe, univ_inter] at h

/-- **Proper strong deformation retraction onto a subcomplex.** In a strongly locally finite
Hausdorff CW complex `C`, a subcomplex `E` is a proper strong deformation retract of `C` if and only
if the inclusion of `E` into `C` is a proper homotopy equivalence. -/
@[alias_in Topology.CWComplex.Subcomplex]
theorem _root_.Topology.RelCWComplex.Subcomplex.exists_proper_strong_deformation_retraction_iff
    [CWComplex.StronglyLocallyFinite C] (E : CWComplex.Subcomplex C) :
    (∃ r : C(C, Subtype.val ⁻¹' (E : Set X)), IsProperMap r ∧
      (∀ a : Subtype.val ⁻¹' (E : Set X), r (a : C) = a) ∧
      ∃ H : (ContinuousMap.id C).HomotopyRel
        ((ContinuousMap.subtypeVal (Subtype.val ⁻¹' (E : Set X) : Set C)).comp r)
        (Subtype.val ⁻¹' (E : Set X) : Set C), IsProperMap H) ↔
      (ContinuousMap.subtypeVal
        (Subtype.val ⁻¹' (E : Set X) : Set C)).HasProperHomotopyInverse :=
  E.hasProperHomotopyExtensionProperty.exists_proper_strong_deformation_retraction_iff

end StronglyLocallyFinite

end TauCeti

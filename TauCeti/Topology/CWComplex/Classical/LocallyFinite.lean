/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyFinite
public import TauCeti.Topology.CWComplex.Classical.CompactSupport
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Locally finite and strongly locally finite CW complexes

In proper homotopy theory, infinite-dimensional locally finite CW complexes need not admit locally
finite covers by finite subcomplexes. Farrell, Taylor, and Wagoner single out the class on which
proper cellular homotopy theory works:

* A CW complex `C` is *locally finite* (`Topology.CWComplex.LocallyFinite`) when the preimages in
  `C` of its closed cells `closedCell n i` form a locally finite family. Every locally finite
  Hausdorff CW complex is locally compact
  (`Topology.CWComplex.LocallyFinite.weaklyLocallyCompactSpace`).
* A Hausdorff CW complex `C` is *strongly locally finite*
  (`Topology.CWComplex.StronglyLocallyFinite`) when `C` is covered by a family of finite
  subcomplexes whose preimages in `C` form a locally finite family.

Using the recursive finite subcomplex `Topology.CWComplex.cellSubcomplex n i` from
`TauCeti.Topology.CWComplex.Classical.CompactSupport`, whose lower-dimensional cells at each stage
meet `cellFrontier n i` (`Topology.CWComplex.mem_cellSubcomplex_iff`), local finiteness propagates
inductively up dimension: on finite-dimensional Hausdorff CW complexes, local finiteness and strong
local finiteness coincide (`Topology.CWComplex.stronglyLocallyFinite_iff_locallyFinite`).

## Main declarations

* `Topology.CWComplex.LocallyFinite`,
  `Topology.CWComplex.LocallyFinite.finite_nonempty_inter_closedCell`,
  `Topology.CWComplex.LocallyFinite.weaklyLocallyCompactSpace`,
  `Topology.CWComplex.LocallyFinite.subcomplex`: local finiteness of closed cells, local
  compactness, and inheritance by subcomplexes.
* `Topology.CWComplex.StronglyLocallyFinite`,
  `Topology.CWComplex.StronglyLocallyFinite.subcomplex`,
  `Topology.CWComplex.StronglyLocallyFinite.locallyFinite`,
  `Topology.CWComplex.LocallyFinite.stronglyLocallyFinite_of_finiteDimensional`,
  `Topology.CWComplex.stronglyLocallyFinite_iff_locallyFinite`: strong local finiteness and its
  equivalence with local finiteness in finite dimension.

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, Section 1.
* R. Fritsch, R. A. Piccinini, *Cellular Structures in Topology*, Cambridge University Press (1990),
  Theorem 1.5.14.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Appendix,
  Proposition A.1.
-/

public section

noncomputable section

open Filter Set

universe u

namespace Topology.CWComplex

section LocallyFinite

variable {X : Type u} [TopologicalSpace X]

/-- A CW complex `C` is *locally finite* when the preimages in `C` of its closed cells form a
locally finite family of subsets of `C`. -/
class LocallyFinite (C : Set X) [CWComplex C] : Prop where
  /-- Every point of `C` has a neighborhood in `C` meeting only finitely many closed cells. -/
  locallyFinite_closedCell :
    _root_.LocallyFinite fun p : Σ n, cell C n ↦ (Subtype.val ⁻¹' closedCell p.1 p.2 : Set C)

/-- A Hausdorff CW complex `C` is *strongly locally finite* when it is covered by a family of finite
subcomplexes whose preimages in `C` form a locally finite family. -/
class StronglyLocallyFinite [T2Space X] (C : Set X) [CWComplex C] : Prop where
  /-- Existence of a locally finite cover of `C` by finite subcomplexes. -/
  exists_locallyFinite_finite_subcomplex :
    ∃ (ι : Type u) (E : ι → Subcomplex C),
      (∀ i, Finite (E i : Set X)) ∧ (⋃ i, (E i : Set X)) = C ∧
        _root_.LocallyFinite fun i ↦ (Subtype.val ⁻¹' (E i : Set X) : Set C)

/-- Every finite CW complex is locally finite. -/
instance LocallyFinite.of_finite (C : Set X) [CWComplex C] [Finite C] : LocallyFinite C where
  locallyFinite_closedCell := by
    have := RelCWComplex.finite_cells_of_finite (C := C)
    exact locallyFinite_of_finite _

/-- Every finite Hausdorff CW complex is strongly locally finite. -/
instance StronglyLocallyFinite.of_finite [T2Space X] (C : Set X) [CWComplex C] [Finite C] :
    StronglyLocallyFinite C where
  exists_locallyFinite_finite_subcomplex :=
    ⟨PUnit.{u + 1}, fun _ ↦ ⊤, fun _ ↦ RelCWComplex.Subcomplex.finite_subcomplex_of_finite ⊤,
      by simp [iUnion_const], locallyFinite_of_finite _⟩

variable [T2Space X] {C : Set X} [CWComplex C]

/-- In a locally finite Hausdorff CW complex, every compact subset of `X` meets only finitely many
closed cells. -/
theorem LocallyFinite.finite_nonempty_inter_closedCell [LocallyFinite C] {K : Set X}
    (hK : IsCompact K) :
    {p : Σ n, cell C n | (closedCell p.1 p.2 ∩ K).Nonempty}.Finite :=
  ((LocallyFinite.locallyFinite_closedCell (C := C)).finite_nonempty_inter_compact
    (RelCWComplex.isClosed.isProperMap_subtypeVal.isCompact_preimage hK)).subset
    fun p ⟨x, hxc, hxK⟩ ↦ ⟨⟨x, RelCWComplex.closedCell_subset_complex p.1 p.2 hxc⟩, hxc, hxK⟩

/-- **A locally finite Hausdorff CW complex is locally compact.** -/
instance LocallyFinite.weaklyLocallyCompactSpace [LocallyFinite C] :
    WeaklyLocallyCompactSpace C where
  exists_compact_mem_nhds x := by
    obtain ⟨V, hVx, hVfin⟩ := LocallyFinite.locallyFinite_closedCell (C := C) x
    refine ⟨⋃ p ∈ hVfin.toFinset, (Subtype.val ⁻¹' closedCell p.1 p.2 : Set C),
      hVfin.toFinset.isCompact_biUnion fun p _ ↦
        RelCWComplex.isClosed.isProperMap_subtypeVal.isCompact_preimage
          RelCWComplex.isCompact_closedCell,
      Filter.mem_of_superset hVx fun y hyV ↦ ?_⟩
    obtain ⟨n, i, hyi⟩ := mem_iUnion₂.1 ((CWComplex.union (C := C)).symm.subset y.property)
    exact mem_biUnion (x := (⟨n, i⟩ : Σ m, cell C m)) (hVfin.mem_toFinset.2 ⟨y, hyi, hyV⟩) hyi

/-- Every subcomplex of a locally finite Hausdorff CW complex is locally finite. -/
instance LocallyFinite.subcomplex [LocallyFinite C] (E : Subcomplex C) :
    LocallyFinite (E : Set X) where
  locallyFinite_closedCell := by
    convert ((LocallyFinite.locallyFinite_closedCell (C := C)).preimage_continuous
      (continuous_inclusion E.subset_complex)).comp_injective
      (Function.injective_id.sigma_map fun n ↦
        (Subtype.val_injective : Function.Injective (Subtype.val : cell (E : Set X) n → cell C n)))
      using 1
    ext ⟨n, i⟩ ⟨x, hxE⟩
    simp only [Function.comp_apply, Sigma.map_mk, id_eq, mem_preimage,
      RelCWComplex.Subcomplex.closedCell_eq, inclusion_mk]

/-- Every subcomplex of a strongly locally finite Hausdorff CW complex is strongly locally
finite. -/
instance StronglyLocallyFinite.subcomplex [StronglyLocallyFinite C] (E : Subcomplex C) :
    StronglyLocallyFinite (E : Set X) where
  exists_locallyFinite_finite_subcomplex := by
    obtain ⟨ι, F, hF_fin, hF_cov, hF_lf⟩ :=
      StronglyLocallyFinite.exists_locallyFinite_finite_subcomplex (C := C)
    let G : ι → Subcomplex (E : Set X) := fun k ↦ .ofLE (inf_le_left : E ⊓ F k ≤ E)
    refine ⟨ι, G, fun k ↦ ?_, ?_, ?_⟩
    · refine Subcomplex.finite_iff_finite_cells.2 <|
        ((Subcomplex.finite_iff_finite_cells.1 (hF_fin k)).preimage
          (Function.injective_id.sigma_map fun _ ↦ Subtype.val_injective).injOn).subset
          fun ⟨n, j⟩ hj ↦ ?_
      simp only [G, RelCWComplex.Subcomplex.ofLE_I, mem_preimage, RelCWComplex.Subcomplex.inf_I,
        mem_inter_iff] at hj
      exact hj.2
    · ext x
      simp only [G, mem_iUnion, RelCWComplex.Subcomplex.coe_ofLE, RelCWComplex.Subcomplex.coe_inf,
        mem_inter_iff]
      exact ⟨fun ⟨_, hxE, _⟩ ↦ hxE, fun hxE ↦
        let ⟨k, hxk⟩ := mem_iUnion.1 (hF_cov.symm.subset (E.subset_complex hxE))
        ⟨k, hxE, hxk⟩⟩
    · convert hF_lf.preimage_continuous (continuous_inclusion E.subset_complex) using 1
      ext k ⟨x, hxE⟩
      simp only [G, mem_preimage, RelCWComplex.Subcomplex.coe_ofLE, RelCWComplex.Subcomplex.coe_inf,
        mem_inter_iff, inclusion_mk, hxE, true_and]

/-- **Every strongly locally finite Hausdorff CW complex is locally finite.** -/
instance StronglyLocallyFinite.locallyFinite [StronglyLocallyFinite C] : LocallyFinite C where
  locallyFinite_closedCell x := by
    obtain ⟨ι, E, hE_fin, hE_cov, hE_lf⟩ :=
      StronglyLocallyFinite.exists_locallyFinite_finite_subcomplex (C := C)
    obtain ⟨V, hVx, hV_fin⟩ := hE_lf x
    obtain ⟨W, hWV, hW_open, hxW⟩ := mem_nhds_iff.1 hVx
    obtain ⟨U, hU_open, rfl⟩ := isOpen_induced_iff.1 hW_open
    refine ⟨Subtype.val ⁻¹' U, hW_open.mem_nhds hxW,
      (hV_fin.biUnion fun k _ ↦ Subcomplex.finite_iff_finite_cells.1 (hE_fin k)).subset
        fun ⟨n, j⟩ ⟨z, hzc, hzU⟩ ↦ ?_⟩
    have hne : (closedCell n j ∩ U).Nonempty := ⟨z.val, hzc, hzU⟩
    rw [← RelCWComplex.closure_openCell_eq_closedCell,
      closure_inter_open_nonempty_iff hU_open] at hne
    obtain ⟨y, hyo, hyU⟩ := hne
    have hyC : y ∈ C := RelCWComplex.openCell_subset_complex n j hyo
    obtain ⟨k, hyk⟩ := mem_iUnion.1 (hE_cov.symm.subset hyC)
    exact mem_biUnion (⟨⟨y, hyC⟩, hyk, hWV hyU⟩ :
      k ∈ {k | ((Subtype.val ⁻¹' (E k : Set X) : Set C) ∩ V).Nonempty})
      ((E k).mem_I_iff_of_mem_openCell hyo |>.2 hyk)

/-- In a locally finite Hausdorff CW complex, a compact subset of `X` meets `cellSubcomplex n i` for
only finitely many `n`-cells `i` in each fixed dimension `n`. -/
private theorem finite_nonempty_inter_cellSubcomplex [LocallyFinite C] (n : ℕ) :
    ∀ {K : Set X}, IsCompact K →
      {i : cell C n | ((cellSubcomplex n i : Set X) ∩ K).Nonempty}.Finite := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro K hK
    have hinj : (Sigma.mk n : cell C n → Σ k, cell C k).Injective := sigma_mk_injective
    have hclosed_fin : {i : cell C n | (closedCell n i ∩ K).Nonempty}.Finite :=
      (LocallyFinite.finite_nonempty_inter_closedCell (C := C) hK).preimage hinj.injOn
    have hH_fin : (⋃ m : Fin n,
        ⋃ j ∈ {j : cell C m.val | ((cellSubcomplex m.val j : Set X) ∩ K).Nonempty},
        {i : cell C n | (closedCell n i ∩ closedCell m.val j).Nonempty}).Finite :=
      finite_iUnion fun m ↦ (ih m.val m.isLt hK).biUnion fun j _ ↦
        (LocallyFinite.finite_nonempty_inter_closedCell (C := C)
          (RelCWComplex.isCompact_closedCell (n := m.val) (i := j))).preimage hinj.injOn
    refine (hH_fin.union hclosed_fin).subset fun i ⟨x, hxi, hxK⟩ ↦ ?_
    rcases mem_cellSubcomplex_iff.1 hxi with htop | ⟨m, hmn, j, ⟨y, hyf, hyo⟩, hxj⟩
    · exact .inr ⟨x, htop, hxK⟩
    · exact .inl <| mem_iUnion.2 ⟨⟨m, hmn⟩, mem_biUnion ⟨x, hxj, hxK⟩
        ⟨y, RelCWComplex.cellFrontier_subset_closedCell n i hyf,
          RelCWComplex.openCell_subset_closedCell m j hyo⟩⟩

/-- **Every finite-dimensional locally finite Hausdorff CW complex is strongly locally finite.** -/
theorem LocallyFinite.stronglyLocallyFinite_of_finiteDimensional [LocallyFinite C]
    [FiniteDimensional C] : StronglyLocallyFinite C where
  exists_locallyFinite_finite_subcomplex := by
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅))
    refine ⟨Σ n, cell C n, fun p ↦ cellSubcomplex p.1 p.2,
      fun p ↦ finite_cellSubcomplex p.1 p.2, ?_, fun x ↦ ?_⟩
    · exact Subset.antisymm (iUnion_subset fun p ↦ (cellSubcomplex p.1 p.2).subset_complex)
        ((CWComplex.union (C := C)).superset.trans (iUnion₂_subset fun n i ↦
          (closedCell_subset_cellSubcomplex n i).trans
            (subset_iUnion (fun p : Σ m, cell C m ↦ (cellSubcomplex p.1 p.2 : Set X)) ⟨n, i⟩)))
    · obtain ⟨K, hKc, hKx⟩ := exists_compact_mem_nhds x
      have hKX : IsCompact ((Subtype.val : C → X) '' K) := hKc.image continuous_subtypeVal
      refine ⟨K, hKx, (finite_iUnion fun m : Fin N ↦
        (finite_nonempty_inter_cellSubcomplex m.val hKX).image (Sigma.mk m.val)).subset
        fun ⟨n, i⟩ ⟨z, hzc, hzK⟩ ↦ ?_⟩
      have hn : n < N := by_contra fun h ↦ (hN n (Nat.le_of_not_lt h)).false i
      exact mem_iUnion.2 ⟨⟨n, hn⟩, i, ⟨z.val, hzc, mem_image_of_mem Subtype.val hzK⟩, rfl⟩

/-- **On finite-dimensional Hausdorff CW complexes, strong local finiteness and local finiteness
coincide.** -/
theorem stronglyLocallyFinite_iff_locallyFinite [FiniteDimensional C] :
    StronglyLocallyFinite C ↔ LocallyFinite C :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ LocallyFinite.stronglyLocallyFinite_of_finiteDimensional⟩

end LocallyFinite

end Topology.CWComplex

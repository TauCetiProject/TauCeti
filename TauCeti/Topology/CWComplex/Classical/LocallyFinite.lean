/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyFinite
public import TauCeti.Topology.CWComplex.Classical.CompactSupport
public import TauCeti.Topology.CWComplex.Classical.Finite
public import TauCeti.Topology.CWComplex.Classical.Subcomplex
public import TauCeti.Topology.Maps.Proper.Basic

/-!
# Locally finite and strongly locally finite CW complexes

In proper homotopy theory, the weak topology of an arbitrary CW complex does not automatically make
cylinders and skeletal retractions proper: infinite-dimensional locally finite CW complexes can fail
to admit locally finite covers by finite subcomplexes. Farrell, Taylor, and Wagoner single out the
exact class on which proper cellular homotopy theory works:

* A CW complex `C` is *locally finite* (`Topology.CWComplex.LocallyFinite`) when the family of
  preimages in `C` of its closed cells `(closedCell n i)` is locally finite in `C`. Every locally
  finite Hausdorff CW complex is locally compact
  (`Topology.CWComplex.LocallyFinite.weaklyLocallyCompactSpace`).
* A CW complex `C` is *strongly locally finite* (`Topology.CWComplex.StronglyLocallyFinite`) when
  `C` is covered by a family of finite subcomplexes whose preimages in `C` form a locally finite
  family.

To connect the two notions, we construct for every cell `(n, i)` of a Hausdorff CW complex `C` a
finite subcomplex `Topology.CWComplex.cellSubcomplex n i` containing `closedCell n i` (from which it
also follows that every compact subset of `C` lies in a finite subcomplex,
`Topology.CWComplex.exists_finite_subcomplex_of_isCompact`). Because the lower-dimensional cells
used at each stage meet `closedCell n i`, local finiteness of closed cells propagates inductively up
dimension: every finite-dimensional locally finite Hausdorff CW complex is strongly locally finite
(`Topology.CWComplex.LocallyFinite.stronglyLocallyFinite_of_finiteDimensional`), and on
finite-dimensional Hausdorff CW complexes the two conditions coincide
(`Topology.CWComplex.stronglyLocallyFinite_iff_locallyFinite`).

## Main declarations

* `Topology.RelCWComplex.Subcomplex.adjoinCell`: adjoining a single cell whose cell frontier lies in
  a subcomplex `E`.
* `Topology.CWComplex.cellSubcomplex`: a finite subcomplex containing `closedCell n i`.
* `Topology.CWComplex.exists_finite_subcomplex_of_isCompact`: every compact subset of a Hausdorff CW
  complex lies in a finite subcomplex.
* `Topology.CWComplex.LocallyFinite`: local finiteness of closed cells in `C`.
* `Topology.CWComplex.LocallyFinite.weaklyLocallyCompactSpace`: a locally finite Hausdorff CW
  complex is locally compact.
* `Topology.CWComplex.StronglyLocallyFinite`: existence of a locally finite cover of `C` by finite
  subcomplexes.
* `Topology.CWComplex.StronglyLocallyFinite.locallyFinite`: every strongly locally finite Hausdorff
  CW complex is locally finite.
* `Topology.CWComplex.LocallyFinite.stronglyLocallyFinite_of_finiteDimensional`,
  `Topology.CWComplex.stronglyLocallyFinite_iff_locallyFinite`: **on finite-dimensional Hausdorff CW
  complexes, local finiteness and strong local finiteness are equivalent.**

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

namespace Topology.RelCWComplex.Subcomplex

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

/-- The bottom subcomplex `⊥` of a relative CW complex is finite. -/
@[alias_in CWComplex.Subcomplex]
instance finite_bot : Finite (((⊥ : Subcomplex C) : Set X)) := by
  have : FiniteDimensional (((⊥ : Subcomplex C) : Set X)) :=
    ⟨Eventually.of_forall fun _ ↦ Subtype.isEmpty_false⟩
  have : FiniteType (((⊥ : Subcomplex C) : Set X)) :=
    ⟨fun n ↦ (finite_empty : ((⊥ : Subcomplex C).I n).Finite).to_subtype⟩
  exact finite_of_finiteDimensional_finiteType _

/-- The union `E₁ ⊔ E₂` of two finite subcomplexes is finite. -/
@[alias_in CWComplex.Subcomplex]
theorem finite_sup {E₁ E₂ : Subcomplex C}
    (h₁ : Finite (E₁ : Set X)) (h₂ : Finite (E₂ : Set X)) :
    Finite (((E₁ ⊔ E₂ : Subcomplex C) : Set X)) := by
  have : FiniteDimensional (((E₁ ⊔ E₂ : Subcomplex C) : Set X)) := by
    refine ⟨?_⟩
    filter_upwards [h₁.eventually_isEmpty_cell, h₂.eventually_isEmpty_cell] with n hn₁ hn₂
    exact ⟨fun ⟨i, hi⟩ ↦ hi.elim (fun h ↦ hn₁.false ⟨i, h⟩) (fun h ↦ hn₂.false ⟨i, h⟩)⟩
  have : FiniteType (((E₁ ⊔ E₂ : Subcomplex C) : Set X)) := by
    refine ⟨fun n ↦ ?_⟩
    have := h₁.finite_cell n
    have := h₂.finite_cell n
    exact ((Set.toFinite (E₁.I n)).union (Set.toFinite (E₂.I n))).to_subtype
  exact finite_of_finiteDimensional_finiteType _

omit [T2Space X] in
/-- The carrier of a `Finset.sup` of subcomplexes is the union of the base `D` with the carriers of
the indexed subcomplexes. -/
@[simp, norm_cast, alias_in CWComplex.Subcomplex]
theorem coe_finsetSup {α : Type*} (s : Finset α) (f : α → Subcomplex C) :
    ((s.sup f : Subcomplex C) : Set X) = D ∪ ⋃ a ∈ s, (f a : Set X) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s _ha ih =>
    ext x
    simp only [Finset.sup_insert, coe_sup, ih, mem_union, mem_iUnion, Finset.mem_insert,
      SetLike.mem_coe]
    exact ⟨fun h ↦ h.elim (fun hfa ↦ .inr ⟨a, .inl rfl, hfa⟩)
        (fun h' ↦ h'.elim .inl fun ⟨b, hb, hfb⟩ ↦ .inr ⟨b, .inr hb, hfb⟩),
      fun h ↦ h.elim (.inr ∘ .inl) fun ⟨b, hb, hfb⟩ ↦
        hb.elim (fun hba ↦ .inl (hba ▸ hfb)) fun hbs ↦ .inr (.inr ⟨b, hbs, hfb⟩)⟩

/-- A `Finset.sup` of finite subcomplexes is finite. -/
@[alias_in CWComplex.Subcomplex]
theorem finite_finsetSup {α : Type*} (s : Finset α)
    (f : α → Subcomplex C) (hf : ∀ a ∈ s, Finite (f a : Set X)) :
    Finite (((s.sup f : Subcomplex C) : Set X)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sup_empty]
    exact finite_bot
  | insert a s _ha ih =>
    rw [Finset.sup_insert]
    exact finite_sup (hf a (Finset.mem_insert_self a s))
      (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))

/-- Adjoining a single `n`-cell `i` whose cell frontier already lies in `E` produces a subcomplex
with carrier `(E : Set X) ∪ closedCell n i`. -/
@[alias_in CWComplex.Subcomplex]
def adjoinCell (E : Subcomplex C) (n : ℕ) (i : cell C n)
    (hi : cellFrontier n i ⊆ E) : Subcomplex C where
  carrier := (E : Set X) ∪ closedCell n i
  I k := if h : k = n then E.I k ∪ {h ▸ i} else E.I k
  closed' := E.closed.union isClosed_closedCell
  union' := by
    let J : ∀ k, Set (cell C k) := fun k ↦ if h : k = n then E.I k ∪ {h ▸ i} else E.I k
    have hsubE : (E : Set X) ⊆ D ∪ ⋃ (k : ℕ) (j : ↥(J k)), openCell k j.1 := by
      rw [← E.union]
      refine union_subset_union_right D (iUnion₂_subset fun k ⟨l, hlE⟩ ↦ ?_)
      have hl' : l ∈ J k := by
        dsimp only [J]
        split_ifs <;> simp [hlE]
      exact subset_iUnion₂ (s := fun k (j : ↥(J k)) ↦ openCell k j.1) k ⟨l, hl'⟩
    refine Subset.antisymm
      (union_subset (E.base_subset.trans subset_union_left) (iUnion₂_subset fun k ⟨l, hl⟩ ↦ ?_))
      (union_subset hsubE ?_)
    · by_cases hkn : k = n
      · subst hkn
        rcases (by simpa [J] using hl : l = i ∨ l ∈ E.I k) with rfl | hlE
        · exact (openCell_subset_closedCell k l).trans subset_union_right
        · exact (E.openCell_subset_of_mem hlE).trans subset_union_left
      · exact (E.openCell_subset_of_mem (by simpa [J, hkn] using hl)).trans subset_union_left
    · rw [← cellFrontier_union_openCell_eq_closedCell]
      refine union_subset (hi.trans hsubE) (subset_union_of_subset_right ?_ D)
      exact subset_iUnion₂ (s := fun k (j : ↥(J k)) ↦ openCell k j.1) n ⟨i, by simp [J]⟩

/-- The carrier of `E.adjoinCell n i hi` is `(E : Set X) ∪ closedCell n i`. -/
@[simp, norm_cast, alias_in CWComplex.Subcomplex]
theorem coe_adjoinCell (E : Subcomplex C) (n : ℕ) (i : cell C n)
    (hi : cellFrontier n i ⊆ E) :
    (E.adjoinCell n i hi : Set X) = (E : Set X) ∪ closedCell n i :=
  (rfl)

/-- Membership in `E.adjoinCell n i hi` is membership in `E` or in `closedCell n i`. -/
@[simp, alias_in CWComplex.Subcomplex]
theorem mem_adjoinCell {E : Subcomplex C} {n : ℕ} {i : cell C n}
    {hi : cellFrontier n i ⊆ E} {x : X} :
    x ∈ E.adjoinCell n i hi ↔ x ∈ E ∨ x ∈ closedCell n i :=
  .rfl

/-- The `k`-cells of `E.adjoinCell n i hi` are those of `E` together with `i` when `k = n`. -/
@[simp, alias_in CWComplex.Subcomplex]
theorem adjoinCell_I (E : Subcomplex C) (n : ℕ) (i : cell C n)
    (hi : cellFrontier n i ⊆ E) (k : ℕ) :
    (E.adjoinCell n i hi).I k = if h : k = n then E.I k ∪ {h ▸ i} else E.I k :=
  (rfl)

/-- Adjoining a single cell to a finite subcomplex yields a finite subcomplex. -/
@[alias_in CWComplex.Subcomplex]
theorem finite_adjoinCell {E : Subcomplex C} (hE : Finite (E : Set X))
    (n : ℕ) (i : cell C n) (hi : cellFrontier n i ⊆ E) :
    Finite (E.adjoinCell n i hi : Set X) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hE.eventually_isEmpty_cell
  have : FiniteDimensional (E.adjoinCell n i hi : Set X) := by
    refine ⟨eventually_atTop.2 ⟨max N (n + 1), fun m hm ↦ ?_⟩⟩
    have hmn : m ≠ n := Nat.ne_of_gt (Nat.lt_of_succ_le (le_of_max_le_right hm))
    have hmN : IsEmpty (E.I m) := hN m (le_of_max_le_left hm)
    refine ⟨fun ⟨j, hj⟩ ↦ hmN.false ⟨j, ?_⟩⟩
    simpa [adjoinCell_I, hmn] using hj
  have : FiniteType (E.adjoinCell n i hi : Set X) := by
    refine ⟨fun k ↦ ?_⟩
    have hk : ((E.adjoinCell n i hi).I k).Finite := by
      rw [adjoinCell_I]
      have := hE.finite_cell k
      have hkE : (E.I k).Finite := Set.toFinite (E.I k)
      split_ifs with h
      · exact hkE.union (finite_singleton _)
      · exact hkE
    exact hk.to_subtype
  exact finite_of_finiteDimensional_finiteType _

end Topology.RelCWComplex.Subcomplex

namespace Topology.CWComplex

section FiniteSubcomplex

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-- Finite set of `m`-cells (`m < n`) whose open cells meet `cellFrontier n i` and together cover
`cellFrontier n i`. -/
private def frontierCells (n : ℕ) (i : cell C n) (m : ℕ) : Finset (cell C m) :=
  open Classical in
  ((cellFrontier_subset_finite_openCell (C := C) n i).choose m).filter
    fun j ↦ (cellFrontier n i ∩ openCell m j).Nonempty

omit [T2Space X] in
private lemma cellFrontier_subset_iUnion_frontierCells (n : ℕ) (i : cell C n) :
    cellFrontier n i ⊆ ⋃ (m : Fin n) (j ∈ frontierCells n i m.1), openCell m.1 j := by
  intro x hx
  have hx' := (cellFrontier_subset_finite_openCell (C := C) n i).choose_spec hx
  simp only [mem_iUnion, exists_prop] at hx' ⊢
  obtain ⟨m, hmn, j, hj, hxj⟩ := hx'
  refine ⟨⟨m, hmn⟩, j, ?_, hxj⟩
  classical
  exact Finset.mem_filter.2 ⟨hj, ⟨x, hx, hxj⟩⟩

omit [T2Space X] in
private lemma nonempty_closedCell_inter_of_mem_frontierCells {n m : ℕ} {i : cell C n}
    {j : cell C m} (hj : j ∈ frontierCells n i m) :
    (closedCell m j ∩ closedCell n i).Nonempty := by
  classical
  obtain ⟨x, hxf, hxo⟩ := (Finset.mem_filter.1 hj).2
  exact ⟨x, RelCWComplex.openCell_subset_closedCell m j hxo,
    RelCWComplex.cellFrontier_subset_closedCell n i hxf⟩

/-- Bundled finite subcomplex containing `closedCell n i`, constructed recursively along cell
dimension so that every cell used at step `n` meets `closedCell n i`. -/
private def cellSubcomplexAux :
    ∀ (n : ℕ) (i : cell C n), {E : Subcomplex C // Finite (E : Set X) ∧ closedCell n i ⊆ E}
  | n, i =>
    open Classical in
    let prev : ∀ m : Fin n, (j : cell C m.1) →
        {E : Subcomplex C // Finite (E : Set X) ∧ closedCell m.1 j ⊆ E} :=
      fun m j ↦ cellSubcomplexAux m.1 j
    let B : Subcomplex C :=
      (Finset.univ : Finset (Fin n)).sup fun m ↦
        (frontierCells n i m.1).sup fun j ↦ (prev m j).1
    have hB_fin : Finite (B : Set X) :=
      Subcomplex.finite_finsetSup _ _ fun m _ ↦
        Subcomplex.finite_finsetSup _ _ fun j _ ↦ (prev m j).2.1
    have hB_fr : cellFrontier n i ⊆ B := by
      refine (cellFrontier_subset_iUnion_frontierCells n i).trans (iUnion_subset fun m ↦ ?_)
      refine iUnion₂_subset fun j hj ↦ ?_
      have hle₁ : (prev m j).1 ≤ (frontierCells n i m.1).sup fun k ↦ (prev m k).1 :=
        Finset.le_sup (f := fun k ↦ (prev m k).1) hj
      have hle₂ : ((frontierCells n i m.1).sup fun k ↦ (prev m k).1) ≤ B :=
        Finset.le_sup (f := fun m : Fin n ↦ (frontierCells n i m.1).sup fun k ↦ (prev m k).1)
          (Finset.mem_univ m)
      exact (RelCWComplex.openCell_subset_closedCell m.1 j).trans
        ((prev m j).2.2.trans (hle₁.trans hle₂))
    ⟨B.adjoinCell n i hB_fr, RelCWComplex.Subcomplex.finite_adjoinCell hB_fin n i hB_fr,
      subset_union_right⟩
termination_by n _ => n
decreasing_by exact m.2

/-- A finite subcomplex of `C` containing `closedCell n i`, built recursively from the lower
dimensional cells meeting `cellFrontier n i`. -/
def cellSubcomplex (n : ℕ) (i : cell C n) : Subcomplex C :=
  (cellSubcomplexAux n i).1

/-- For each cell `(n, i)`, the subcomplex `cellSubcomplex n i` is finite. -/
instance finite_cellSubcomplex (n : ℕ) (i : cell C n) : Finite (cellSubcomplex n i : Set X) :=
  (cellSubcomplexAux n i).2.1

/-- The closed cell `closedCell n i` is contained in `cellSubcomplex n i`. -/
theorem closedCell_subset_cellSubcomplex (n : ℕ) (i : cell C n) :
    closedCell n i ⊆ cellSubcomplex n i :=
  (cellSubcomplexAux n i).2.2

private lemma coe_cellSubcomplex_eq (n : ℕ) (i : cell C n) :
    (cellSubcomplex n i : Set X) =
      (⋃ (m : Fin n) (j ∈ frontierCells n i m.1), (cellSubcomplex m.1 j : Set X)) ∪
        closedCell n i := by
  unfold cellSubcomplex
  rw [cellSubcomplexAux]
  simp only [RelCWComplex.Subcomplex.coe_adjoinCell, RelCWComplex.Subcomplex.coe_finsetSup,
    empty_union, Finset.mem_univ, iUnion_true]

/-- **Every compact subset of a Hausdorff CW complex is contained in a finite subcomplex.** No
local-finiteness or dimension bound is required on `C`. -/
theorem exists_finite_subcomplex_of_isCompact {K : Set X} (hK : IsCompact K) (hKC : K ⊆ C) :
    ∃ E : Subcomplex C, Finite (E : Set X) ∧ K ⊆ E := by
  classical
  have hfin := TauCeti.finite_setOf_nonempty_inter_openCell_of_isCompact (C := C) hK
  let E : Subcomplex C := hfin.toFinset.sup fun p ↦ cellSubcomplex p.1 p.2
  refine ⟨E, Subcomplex.finite_finsetSup _ _ fun p _ ↦ finite_cellSubcomplex p.1 p.2,
    fun x hx ↦ ?_⟩
  have hxC : x ∈ ⋃ (n : ℕ) (i : cell C n), openCell n i := by
    rw [iUnion_openCell_eq_complex]
    exact hKC hx
  obtain ⟨n, i, hxi⟩ := mem_iUnion₂.1 hxC
  have hmem : (⟨n, i⟩ : Σ m, cell C m) ∈ hfin.toFinset :=
    hfin.mem_toFinset.2 ⟨x, hx, hxi⟩
  have hle : cellSubcomplex n i ≤ E :=
    Finset.le_sup (f := fun p : Σ m, cell C m ↦ cellSubcomplex p.1 p.2) hmem
  exact hle (closedCell_subset_cellSubcomplex n i
    (RelCWComplex.openCell_subset_closedCell n i hxi))

end FiniteSubcomplex

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
    {p : Σ n, cell C n | (closedCell p.1 p.2 ∩ K).Nonempty}.Finite := by
  have hKC : IsCompact (Subtype.val ⁻¹' K : Set C) :=
    RelCWComplex.isClosed.isProperMap_subtypeVal.isCompact_preimage hK
  refine ((LocallyFinite.locallyFinite_closedCell (C := C)).finite_nonempty_inter_compact
    hKC).subset fun p ⟨x, hxc, hxK⟩ ↦ ?_
  exact ⟨⟨x, RelCWComplex.closedCell_subset_complex p.1 p.2 hxc⟩, hxc, hxK⟩

/-- **A locally finite Hausdorff CW complex is locally compact.** -/
instance LocallyFinite.weaklyLocallyCompactSpace [LocallyFinite C] :
    WeaklyLocallyCompactSpace C where
  exists_compact_mem_nhds x := by
    -- A neighborhood in `C` meeting only finitely many closed cells lies in their compact union.
    obtain ⟨V, hVx, hVfin⟩ := LocallyFinite.locallyFinite_closedCell (C := C) x
    let K : Set C := ⋃ p ∈ hVfin.toFinset, (Subtype.val ⁻¹' closedCell p.1 p.2 : Set C)
    have hK_comp : IsCompact K := by
      refine hVfin.toFinset.isCompact_biUnion fun p _ ↦ ?_
      exact RelCWComplex.isClosed.isProperMap_subtypeVal.isCompact_preimage
        RelCWComplex.isCompact_closedCell
    refine ⟨K, hK_comp, Filter.mem_of_superset hVx fun y hyV ↦ ?_⟩
    have hyC : (y : X) ∈ ⋃ (n : ℕ) (i : cell C n), closedCell n i := by
      rw [CWComplex.union]
      exact y.2
    obtain ⟨n, i, hyi⟩ := mem_iUnion₂.1 hyC
    have hp : (⟨n, i⟩ : Σ m, cell C m) ∈ hVfin.toFinset :=
      hVfin.mem_toFinset.2 ⟨y, hyi, hyV⟩
    exact mem_biUnion hp hyi

/-- Every subcomplex of a locally finite Hausdorff CW complex is locally finite. -/
instance LocallyFinite.subcomplex [LocallyFinite C] (E : Subcomplex C) :
    LocallyFinite (E : Set X) where
  locallyFinite_closedCell := by
    have hpre := (LocallyFinite.locallyFinite_closedCell (C := C)).preimage_continuous
      (ContinuousMap.inclusion E.subset_complex).continuous
    refine hpre.comp_injective
      (g := fun p : Σ n, cell (E : Set X) n ↦ (⟨p.1, p.2.1⟩ : Σ n, cell C n)) ?_
    rintro ⟨n₁, i₁, _⟩ ⟨n₂, i₂, _⟩ h
    obtain rfl : n₁ = n₂ := congrArg Sigma.fst h
    obtain rfl : i₁ = i₂ := eq_of_heq (Sigma.ext_iff.1 h).2
    rfl

/-- Every subcomplex of a strongly locally finite Hausdorff CW complex is strongly locally
finite. -/
instance StronglyLocallyFinite.subcomplex [StronglyLocallyFinite C] (E : Subcomplex C) :
    StronglyLocallyFinite (E : Set X) where
  exists_locallyFinite_finite_subcomplex := by
    obtain ⟨ι, F, hF_fin, hF_cov, hF_lf⟩ :=
      StronglyLocallyFinite.exists_locallyFinite_finite_subcomplex (C := C)
    let G : ι → Subcomplex (E : Set X) :=
      fun k ↦ RelCWComplex.Subcomplex.ofLE (inf_le_left : E ⊓ F k ≤ E)
    refine ⟨ι, G, fun k ↦ ?_, ?_, ?_⟩
    · have hk := hF_fin k
      obtain ⟨N, hN⟩ := eventually_atTop.1 hk.eventually_isEmpty_cell
      have : FiniteDimensional (G k : Set X) := by
        refine ⟨eventually_atTop.2 ⟨N, fun m hm ↦ ⟨fun ⟨⟨j, _⟩, hj⟩ ↦ ?_⟩⟩⟩
        exact (hN m hm).false ⟨j, by simpa [G] using hj⟩
      have : FiniteType (G k : Set X) := by
        refine ⟨fun n ↦ ?_⟩
        have hFn : ((F k).I n).Finite := by
          have := hk.finite_cell n
          exact Set.toFinite ((F k).I n)
        exact (hFn.preimage Subtype.val_injective.injOn).subset
          (fun x hx ↦ by simpa [G] using hx) |>.to_subtype
      exact finite_of_finiteDimensional_finiteType _
    · ext x
      simp only [G, mem_iUnion, RelCWComplex.Subcomplex.coe_ofLE, RelCWComplex.Subcomplex.coe_inf,
        mem_inter_iff]
      refine ⟨fun ⟨_, hxE, _⟩ ↦ hxE, fun hxE ↦ ?_⟩
      have hxC : x ∈ ⋃ k, (F k : Set X) := hF_cov.symm ▸ E.subset_complex hxE
      obtain ⟨k, hxk⟩ := mem_iUnion.1 hxC
      exact ⟨k, hxE, hxk⟩
    · convert hF_lf.preimage_continuous
        (ContinuousMap.inclusion E.subset_complex).continuous using 1
      ext k ⟨x, hxE⟩
      simp [G, ContinuousMap.inclusion, hxE]

/-- **Every strongly locally finite Hausdorff CW complex is locally finite.** -/
instance StronglyLocallyFinite.locallyFinite [StronglyLocallyFinite C] : LocallyFinite C where
  locallyFinite_closedCell x := by
    -- Any open neighborhood meeting `closedCell n j` meets its dense `openCell n j`, which belongs
    -- to one of the finitely many covering subcomplexes `E k` meeting that neighborhood.
    obtain ⟨ι, E, hE_fin, hE_cov, hE_lf⟩ :=
      StronglyLocallyFinite.exists_locallyFinite_finite_subcomplex (C := C)
    obtain ⟨V, hVx, hV_fin⟩ := hE_lf x
    obtain ⟨W, hWV, hW_open, hxW⟩ := mem_nhds_iff.1 hVx
    obtain ⟨U, hU_open, rfl⟩ := isOpen_induced_iff.1 hW_open
    have hcell_fin : ∀ k, {p : Σ n, cell C n | p.2 ∈ (E k).I p.1}.Finite := fun k ↦ by
      have : Finite (E k : Set X) := hE_fin k
      have := RelCWComplex.finite_cells_of_finite (C := (E k : Set X))
      refine (finite_range fun q : Σ n, cell (E k : Set X) n ↦
        (⟨q.1, q.2.1⟩ : Σ n, cell C n)).subset ?_
      rintro ⟨n, j⟩ hj
      exact ⟨⟨n, ⟨j, hj⟩⟩, rfl⟩
    refine ⟨Subtype.val ⁻¹' U, hW_open.mem_nhds hxW,
      (hV_fin.biUnion fun k _ ↦ hcell_fin k).subset fun ⟨n, j⟩ ⟨z, hzc, hzU⟩ ↦ ?_⟩
    have hne : (closedCell n j ∩ U).Nonempty := ⟨z.1, hzc, hzU⟩
    rw [← RelCWComplex.closure_openCell_eq_closedCell,
      closure_inter_open_nonempty_iff hU_open] at hne
    obtain ⟨y, hyo, hyU⟩ := hne
    have hyC : y ∈ C := RelCWComplex.openCell_subset_complex n j hyo
    obtain ⟨k, hyk⟩ := mem_iUnion.1 (hE_cov.symm ▸ hyC)
    have hkV : k ∈ {k | ((Subtype.val ⁻¹' (E k : Set X) : Set C) ∩ V).Nonempty} :=
      ⟨⟨y, hyC⟩, hyk, hWV hyU⟩
    exact mem_biUnion hkV ((E k).mem_I_iff_of_mem_openCell hyo |>.2 hyk)

/-- In a locally finite Hausdorff CW complex, a compact subset of `X` meets `cellSubcomplex n i` for
only finitely many `n`-cells `i` in each fixed dimension `n`. -/
private theorem finite_nonempty_inter_cellSubcomplex [LocallyFinite C] (n : ℕ) :
    ∀ {K : Set X}, IsCompact K →
      {i : cell C n | ((cellSubcomplex n i : Set X) ∩ K).Nonempty}.Finite := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro K hK
    have hclosed_fin : {i : cell C n | (closedCell n i ∩ K).Nonempty}.Finite := by
      refine ((LocallyFinite.finite_nonempty_inter_closedCell (C := C) hK).preimage
        (f := fun i : cell C n ↦ (⟨n, i⟩ : Σ m, cell C m)) ?_)
      intro i₁ _ i₂ _ h
      exact eq_of_heq (Sigma.ext_iff.1 h).2
    let H : Set (cell C n) :=
      ⋃ m : Fin n, ⋃ j ∈ {j : cell C m.1 | ((cellSubcomplex m.1 j : Set X) ∩ K).Nonempty},
        {i : cell C n | (closedCell n i ∩ closedCell m.1 j).Nonempty}
    have hH_fin : H.Finite := by
      refine finite_iUnion fun m ↦ (ih m.1 m.2 hK).biUnion fun j _ ↦ ?_
      refine ((LocallyFinite.finite_nonempty_inter_closedCell (C := C)
        (RelCWComplex.isCompact_closedCell (n := m.1) (i := j))).preimage
        (f := fun i : cell C n ↦ (⟨n, i⟩ : Σ k, cell C k)) ?_)
      intro i₁ _ i₂ _ h
      exact eq_of_heq (Sigma.ext_iff.1 h).2
    refine (hH_fin.union hclosed_fin).subset fun i hi ↦ ?_
    simp only [mem_ofPred_eq] at hi
    rw [coe_cellSubcomplex_eq, union_inter_distrib_right, union_nonempty] at hi
    rcases hi with hlow | htop
    · simp only [iUnion_inter, nonempty_iUnion] at hlow
      obtain ⟨m, j, hj_fr, hjK⟩ := hlow
      refine Or.inl (mem_iUnion.2 ⟨m, mem_biUnion hjK ?_⟩)
      simp only [mem_ofPred_eq]
      rw [inter_comm]
      exact nonempty_closedCell_inter_of_mem_frontierCells hj_fr
    · exact Or.inr htop

/-- **Every finite-dimensional locally finite Hausdorff CW complex is strongly locally finite.** -/
theorem LocallyFinite.stronglyLocallyFinite_of_finiteDimensional [LocallyFinite C]
    [FiniteDimensional C] : StronglyLocallyFinite C where
  exists_locallyFinite_finite_subcomplex := by
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅))
    refine ⟨Σ n, cell C n, fun p ↦ cellSubcomplex p.1 p.2,
      fun p ↦ finite_cellSubcomplex p.1 p.2, ?_, fun x ↦ ?_⟩
    · refine Subset.antisymm (iUnion_subset fun p ↦ (cellSubcomplex p.1 p.2).subset_complex) ?_
      exact (CWComplex.union (C := C)).superset.trans (iUnion₂_subset fun n i ↦
        (closedCell_subset_cellSubcomplex n i).trans
          (subset_iUnion (fun p : Σ m, cell C m ↦ (cellSubcomplex p.1 p.2 : Set X)) ⟨n, i⟩))
    · obtain ⟨K, hKc, hKx⟩ := exists_compact_mem_nhds x
      have hKX : IsCompact ((Subtype.val : C → X) '' K) := hKc.image continuous_subtype_val
      let S : Set (Σ n, cell C n) :=
        ⋃ m : Fin N, (fun i : cell C m.1 ↦ (⟨m.1, i⟩ : Σ n, cell C n)) ''
          {i : cell C m.1 | ((cellSubcomplex m.1 i : Set X) ∩ Subtype.val '' K).Nonempty}
      have hS_fin : S.Finite :=
        finite_iUnion fun m ↦ (finite_nonempty_inter_cellSubcomplex m.1 hKX).image _
      refine ⟨K, hKx, hS_fin.subset fun ⟨n, i⟩ ⟨z, hzc, hzK⟩ ↦ ?_⟩
      have hn : n < N := by_contra fun h ↦ (hN n (Nat.le_of_not_lt h)).false i
      exact mem_iUnion.2 ⟨⟨n, hn⟩, i, ⟨z.1, hzc, mem_image_of_mem Subtype.val hzK⟩, rfl⟩

/-- **On finite-dimensional Hausdorff CW complexes, strong local finiteness and local finiteness
coincide.** -/
theorem stronglyLocallyFinite_iff_locallyFinite [FiniteDimensional C] :
    StronglyLocallyFinite C ↔ LocallyFinite C :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ LocallyFinite.stronglyLocallyFinite_of_finiteDimensional⟩

end LocallyFinite

end Topology.CWComplex

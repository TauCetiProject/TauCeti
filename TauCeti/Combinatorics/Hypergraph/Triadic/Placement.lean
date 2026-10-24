/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic
public import TauCeti.Combinatorics.Hypergraph.Colored.Counting
public import TauCeti.Combinatorics.Hypergraph.PairColor.Density
public import TauCeti.Combinatorics.Hypergraph.Polyad.Density
public import TauCeti.Data.Fintype.CardEmbedding
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Placements of colored patterns into triadic complexes

Fix a triadic complex `C` on `V` and a colored three-uniform pattern `F` on `Fin F.k`. To predict
the number of induced copies of `F` in a coloring of the triples of `V`, an induced copy is
recorded by the data it determines in `C`:

* a placement `φ : PatternPlacement3 C F`, assigning to each pattern vertex a vertex cell of `C`
  (cells may repeat);
* a route `ψ : PairColorPlacement3 φ`, assigning to each canonically oriented pattern pair
  `i < j` a pair color of `C`, such that for every pattern triple `i < j < l` the induced polyad
  `ψ.polyad i j l` is one of the selected polyads of `C`.

`placementInjectionCount φ` counts the injections of the pattern vertices respecting the assigned
cells. Since vertex cells are disjoint, it is the product over the cells `A` of the falling
factorials `(#A).descFactorial m_A`, where `m_A` is the number of pattern vertices assigned to
`A`; for a transversal placement, with pairwise distinct cells, it is the product of the cell
sizes.

`H.placedInducedCopyCount φ ψ` counts the labelled induced copies of `F` in `H` that realize the
placement `φ` and the route `ψ`. When the selected polyads of `C` decompose the injective triples,
every induced copy realizes exactly one placement and route, so these placed counts sum to the
induced count `H.inducedCopyCount F`.

`H.expectedInducedCountAt φ ψ` is the corresponding prediction: the injection count, times the
pair-color density of every canonical pattern pair over its assigned cells, times the relative
density over the induced polyad of the pattern color of every canonical pattern triple. Its sum
over all placements and routes is the prediction `H.expectedInducedCount C F` of the induced
count which an induced counting lemma compares with `H.inducedCopyCount F`.

## Main definitions

* `TauCeti.PatternPlacement3`: an assignment of the pattern vertices to vertex cells.
* `TauCeti.PairColorPlacement3`: a route, assigning pair colors to canonical pattern pairs.
* `TauCeti.placementInjectionCount`: the number of cell-respecting injections of a placement.
* `TauCeti.Colored3Graph.placedInducedCopyCount`: the induced copies realizing a placement and a
  route.
* `TauCeti.Colored3Graph.expectedInducedCountAt`, `TauCeti.Colored3Graph.expectedInducedCount`:
  the local and global predictions of the induced count.

## Main results

* `TauCeti.placementInjectionCount_eq_prod_descFactorial`: the injection count is a product of
  falling factorials of the cell sizes.
* `TauCeti.placementInjectionCount_eq_prod_of_transversal`: at a transversal placement it is the
  product of the cell sizes.
* `TauCeti.Colored3Graph.inducedCopyCount_eq_sum_placedInducedCopyCount`: over a polyad
  decomposition, the induced count is the sum of the placed counts.
* `TauCeti.Colored3Graph.expectedInducedCountAt_le_placementInjectionCount`: the local prediction
  lies between zero and the injection count.

## References

* B. Nagle, V. Rödl and M. Schacht, *The counting lemma for regular k-uniform hypergraphs*,
  Random Structures Algorithms 28 (2006).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: counting lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset Function

namespace TauCeti

variable {κ V : Type*} [Fintype V] [DecidableEq V]

/-! ### Placements -/

/-- A placement of the vertices of a pattern `F` into the vertex cells of a triadic complex `C`.
Distinct pattern vertices may be assigned the same cell. -/
@[ext]
structure PatternPlacement3 (C : TriadicComplex3 V) (F : FiniteColored3Pattern κ) where
  /-- The vertex cell assigned to each pattern vertex. -/
  vertexCell : Fin F.k → Finset V
  /-- Every assigned cell is a vertex cell of the complex. -/
  vertexCell_mem : ∀ i, vertexCell i ∈ C.skeleton.vertexPart.parts

namespace PatternPlacement3

variable {C : TriadicComplex3 V} {F : FiniteColored3Pattern κ}

/-- There are finitely many placements of a pattern, as they are determined by their cell
assignments. -/
instance : Fintype (PatternPlacement3 C F) :=
  Fintype.ofEquiv {c : Fin F.k → Finset V // ∀ i, c i ∈ C.skeleton.vertexPart.parts}
    { toFun c := ⟨c.1, c.2⟩
      invFun φ := ⟨φ.vertexCell, φ.vertexCell_mem⟩ }

/-- A placement is transversal when it assigns pairwise distinct cells. -/
def Transversal (φ : PatternPlacement3 C F) : Prop :=
  Injective φ.vertexCell

/-- Unfolded form of `PatternPlacement3.Transversal`. -/
theorem transversal_iff (φ : PatternPlacement3 C F) : φ.Transversal ↔ Injective φ.vertexCell :=
  Iff.rfl

end PatternPlacement3

variable {C : TriadicComplex3 V} {F : FiniteColored3Pattern κ}

/-- The number of injections of the pattern vertices into `V` sending every pattern vertex into
its assigned cell. -/
noncomputable def placementInjectionCount (φ : PatternPlacement3 C F) : ℕ :=
  Nat.card {f : Fin F.k ↪ V // ∀ i, f i ∈ φ.vertexCell i}

/-- The injection count of a placement counts the cell-respecting injections. -/
theorem placementInjectionCount_def (φ : PatternPlacement3 C F) :
    placementInjectionCount φ = Nat.card {f : Fin F.k ↪ V // ∀ i, f i ∈ φ.vertexCell i} :=
  (rfl)

/-- **The falling-factorial formula.** The cell-respecting injections of a placement are counted
cell by cell: a cell `A` to which `m` pattern vertices are assigned contributes
`(#A).descFactorial m`, which vanishes when `A` has fewer than `m` vertices. Unused cells
contribute one. -/
theorem placementInjectionCount_eq_prod_descFactorial (φ : PatternPlacement3 C F) :
    placementInjectionCount φ = ∏ A ∈ C.skeleton.vertexPart.parts,
      (#A).descFactorial (occCount φ.vertexCell A) := by
  rw [placementInjectionCount_def]
  exact Nat.card_embedding_mem_eq_prod_descFactorial _ φ.vertexCell_mem
    C.skeleton.vertexPart.disjoint

/-- At a transversal placement, the injection count is the product of the assigned cell sizes. -/
theorem placementInjectionCount_eq_prod_of_transversal {φ : PatternPlacement3 C F}
    (hφ : φ.Transversal) : placementInjectionCount φ = ∏ i, #(φ.vertexCell i) := by
  rw [placementInjectionCount_def]
  exact Nat.card_embedding_mem_eq_prod_of_injective hφ φ.vertexCell_mem
    C.skeleton.vertexPart.disjoint

/-- The injection count never exceeds the product of the assigned cell sizes. -/
theorem placementInjectionCount_le_prod (φ : PatternPlacement3 C F) :
    placementInjectionCount φ ≤ ∏ i, #(φ.vertexCell i) := by
  rw [placementInjectionCount_def]
  exact Nat.card_embedding_mem_le_prod _

/-! ### Routes -/

/-- A route over a placement `φ`: a pair color of the complex for each canonically oriented
pattern pair `i < j`, such that for every pattern triple `i < j < l` the polyad formed by the
assigned cells and pair colors is a selected polyad of the complex. -/
@[ext]
structure PairColorPlacement3 (φ : PatternPlacement3 C F) where
  /-- The pair color assigned to each canonically oriented pattern pair. -/
  pairColor : {p : Fin F.k × Fin F.k // p.1 < p.2} → Fin C.pairColorCount
  /-- The polyad of every canonically ordered pattern triple is selected by the complex. -/
  ofData_mem : ∀ (i j l : Fin F.k) (hij : i < j) (hjl : j < l),
    Polyad3.ofData (φ.vertexCell i) (φ.vertexCell j) (φ.vertexCell l)
      (φ.vertexCell_mem i) (φ.vertexCell_mem j) (φ.vertexCell_mem l)
      (pairColor ⟨(i, j), hij⟩) (pairColor ⟨(i, l), hij.trans hjl⟩) (pairColor ⟨(j, l), hjl⟩)
      ∈ C.polyads

namespace PairColorPlacement3

variable {φ : PatternPlacement3 C F}

/-- There are finitely many routes over a placement. -/
noncomputable instance : Fintype (PairColorPlacement3 φ) :=
  Fintype.ofInjective _ fun _ _ ↦ PairColorPlacement3.ext

/-- The polyad that a route induces on the canonically ordered pattern triple `i < j < l`. -/
def polyad (ψ : PairColorPlacement3 φ) (i j l : Fin F.k) (hij : i < j) (hjl : j < l) :
    Polyad3 C.skeleton :=
  Polyad3.ofData (φ.vertexCell i) (φ.vertexCell j) (φ.vertexCell l)
    (φ.vertexCell_mem i) (φ.vertexCell_mem j) (φ.vertexCell_mem l)
    (ψ.pairColor ⟨(i, j), hij⟩) (ψ.pairColor ⟨(i, l), hij.trans hjl⟩)
    (ψ.pairColor ⟨(j, l), hjl⟩)

/-- Every polyad induced by a route is selected by the complex. -/
theorem polyad_mem (ψ : PairColorPlacement3 φ) (i j l : Fin F.k) (hij : i < j) (hjl : j < l) :
    ψ.polyad i j l hij hjl ∈ C.polyads :=
  ψ.ofData_mem i j l hij hjl

variable (ψ : PairColorPlacement3 φ) (i j l : Fin F.k) (hij : i < j) (hjl : j < l)

@[simp]
theorem polyad_c₀ : (ψ.polyad i j l hij hjl).c₀ = φ.vertexCell i :=
  Polyad3.ofData_c₀ ..

@[simp]
theorem polyad_c₁ : (ψ.polyad i j l hij hjl).c₁ = φ.vertexCell j :=
  Polyad3.ofData_c₁ ..

@[simp]
theorem polyad_c₂ : (ψ.polyad i j l hij hjl).c₂ = φ.vertexCell l :=
  Polyad3.ofData_c₂ ..

@[simp]
theorem polyad_color₀₁ : (ψ.polyad i j l hij hjl).color₀₁ = ψ.pairColor ⟨(i, j), hij⟩ :=
  Polyad3.ofData_color₀₁ ..

@[simp]
theorem polyad_color₀₂ :
    (ψ.polyad i j l hij hjl).color₀₂ = ψ.pairColor ⟨(i, l), hij.trans hjl⟩ :=
  Polyad3.ofData_color₀₂ ..

@[simp]
theorem polyad_color₁₂ : (ψ.polyad i j l hij hjl).color₁₂ = ψ.pairColor ⟨(j, l), hjl⟩ :=
  Polyad3.ofData_color₁₂ ..

end PairColorPlacement3

/-! ### Placed induced copies -/

namespace Colored3Graph

variable (H : Colored3Graph κ V)

/-- The induced copies of the pattern `F` in `H` that realize the placement `φ` and the route
`ψ`: every pattern vertex lands in its assigned cell, and every canonically oriented pattern pair
lands on a pair of its assigned color. -/
noncomputable def placedInducedCopies (φ : PatternPlacement3 C F) (ψ : PairColorPlacement3 φ) :
    Finset (Fin F.k ↪ V) := by
  classical
  exact (H.inducedCopies F).filter fun f ↦ (∀ i, f i ∈ φ.vertexCell i) ∧
    ∀ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
      C.skeleton.pairColors.colorOfPair (f p.1.1) (f p.1.2) = some (ψ.pairColor p)

variable {H} in
/-- Membership in the placed induced copies. -/
@[simp]
theorem mem_placedInducedCopies {φ : PatternPlacement3 C F} {ψ : PairColorPlacement3 φ}
    {f : Fin F.k ↪ V} :
    f ∈ H.placedInducedCopies φ ψ ↔ H.IsInducedCopy F f ∧ (∀ i, f i ∈ φ.vertexCell i) ∧
      ∀ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
        C.skeleton.pairColors.colorOfPair (f p.1.1) (f p.1.2) = some (ψ.pairColor p) := by
  classical
  simp [placedInducedCopies]

/-- The number of labelled induced copies of `F` in `H` realizing the placement `φ` and the
route `ψ`. -/
noncomputable def placedInducedCopyCount (φ : PatternPlacement3 C F)
    (ψ : PairColorPlacement3 φ) : ℕ :=
  #(H.placedInducedCopies φ ψ)

theorem placedInducedCopyCount_def (φ : PatternPlacement3 C F) (ψ : PairColorPlacement3 φ) :
    H.placedInducedCopyCount φ ψ = #(H.placedInducedCopies φ ψ) :=
  (rfl)

/-- A placed count is at most the injection count of its placement. -/
theorem placedInducedCopyCount_le_placementInjectionCount (φ : PatternPlacement3 C F)
    (ψ : PairColorPlacement3 φ) : H.placedInducedCopyCount φ ψ ≤ placementInjectionCount φ := by
  classical
  rw [placedInducedCopyCount_def, placementInjectionCount_def, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  exact card_le_card fun f hf ↦ mem_filter.2 ⟨mem_univ _, (mem_placedInducedCopies.1 hf).2.1⟩

/-- The placement whose cells are the vertex cells containing the images of an embedding. -/
private noncomputable def placementOf (f : Fin F.k ↪ V) : PatternPlacement3 C F where
  vertexCell i := C.skeleton.vertexPart.part (f i)
  vertexCell_mem _ := C.skeleton.vertexPart.part_mem.2 (mem_univ _)

/-- Over a polyad decomposition, the route recording the pair colors of an embedding. Its polyads
are the polyads of the images of the pattern triples. -/
private noncomputable def routeOf (hC : C.IsPolyadDecomposition) (f : Fin F.k ↪ V) :
    PairColorPlacement3 (placementOf (C := C) f) where
  pairColor p := C.skeleton.pairColors.color ⟨(f p.1.1, f p.1.2), f.injective.ne p.2.ne⟩
  ofData_mem i j l hij hjl := by
    have hinj : Injective ![i, j, l] := by
      intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [hij.ne, hjl.ne, (hij.trans hjl).ne, hij.ne', hjl.ne', (hij.trans hjl).ne']
    -- The polyad formed by the cells and colors of `f` is the polyad of the image triple.
    convert (C.isPolyadDecomposition_iff_ofTriple_mem.1 hC) ⟨f ∘ ![i, j, l], f.injective.comp hinj⟩
      using 1
    refine Polyad3.ext_data ?_ ?_ ?_ ?_ ?_ ?_
    · simp [placementOf]
    · simp [placementOf]
    · simp [placementOf]
    · rw [Polyad3.ofData_color₀₁, Polyad3.ofTriple_color₀₁]
      exact congrArg _ (Subtype.ext (by simp))
    · rw [Polyad3.ofData_color₀₂, Polyad3.ofTriple_color₀₂]
      exact congrArg _ (Subtype.ext (by simp))
    · rw [Polyad3.ofData_color₁₂, Polyad3.ofTriple_color₁₂]
      exact congrArg _ (Subtype.ext (by simp))

/-- **Placed counts decompose the induced count.** When the selected polyads of `C` decompose the
injective triples, every induced copy of `F` in `H` realizes exactly one placement and route, so
the induced count is the sum of the placed counts. -/
theorem inducedCopyCount_eq_sum_placedInducedCopyCount (hC : C.IsPolyadDecomposition) :
    H.inducedCopyCount F =
      ∑ φ : PatternPlacement3 C F, ∑ ψ : PairColorPlacement3 φ, H.placedInducedCopyCount φ ψ := by
  classical
  have hcover : H.inducedCopies F = (univ : Finset (Σ φ : PatternPlacement3 C F,
      PairColorPlacement3 φ)).biUnion fun σ ↦ H.placedInducedCopies σ.1 σ.2 := by
    ext f
    simp only [mem_biUnion, mem_univ, true_and, mem_placedInducedCopies, mem_inducedCopies]
    refine ⟨fun hf ↦ ⟨⟨placementOf f, routeOf hC f⟩, hf, fun i ↦ ?_, fun p ↦ ?_⟩,
      fun ⟨_, hf, _⟩ ↦ hf⟩
    · exact C.skeleton.vertexPart.mem_part (mem_univ _)
    · exact C.skeleton.pairColors.colorOfPair_of_ne _
  have hdisj : (Set.univ : Set (Σ φ : PatternPlacement3 C F,
      PairColorPlacement3 φ)).PairwiseDisjoint fun σ ↦ H.placedInducedCopies σ.1 σ.2 := by
    rintro ⟨φ, ψ⟩ - ⟨φ', ψ'⟩ - hne
    refine disjoint_left.2 fun f hf hf' ↦ hne ?_
    obtain ⟨-, hφ, hψ⟩ := mem_placedInducedCopies.1 hf
    obtain ⟨-, hφ', hψ'⟩ := mem_placedInducedCopies.1 hf'
    -- The cells are the parts containing the images, and the colors are those of the image pairs.
    obtain rfl : φ = φ' := PatternPlacement3.ext <| funext fun i ↦
      C.skeleton.vertexPart.eq_of_mem_parts (φ.vertexCell_mem i) (φ'.vertexCell_mem i) (hφ i)
        (hφ' i)
    obtain rfl : ψ = ψ' := PairColorPlacement3.ext <| funext fun p ↦
      Option.some_injective _ ((hψ p).symm.trans (hψ' p))
    rfl
  simp only [inducedCopyCount_def, placedInducedCopyCount_def]
  rw [hcover, card_biUnion (by simpa using hdisj), Fintype.sum_sigma]

/-! ### The prediction -/

variable [DecidableEq κ]

/-- The predicted number of induced copies of `F` realizing the placement `φ` and the route `ψ`:
the number of cell-respecting injections, times the density of the assigned pair color over the
assigned cells for every canonically oriented pattern pair, times the relative density in `H` of
the pattern color over the induced polyad for every canonically ordered pattern triple. -/
noncomputable def expectedInducedCountAt (φ : PatternPlacement3 C F)
    (ψ : PairColorPlacement3 φ) : ℝ :=
  (placementInjectionCount φ : ℝ) *
    (∏ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
      (pairColorDensity C.skeleton.pairColors (ψ.pairColor p)
        (φ.vertexCell p.1.1) (φ.vertexCell p.1.2) : ℝ)) *
    ∏ t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2},
      (H.relativeDensity (F.tripleColor t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2)
        (ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2) : ℝ)

theorem expectedInducedCountAt_def (φ : PatternPlacement3 C F) (ψ : PairColorPlacement3 φ) :
    H.expectedInducedCountAt φ ψ = (placementInjectionCount φ : ℝ) *
      (∏ p : {p : Fin F.k × Fin F.k // p.1 < p.2},
        (pairColorDensity C.skeleton.pairColors (ψ.pairColor p)
          (φ.vertexCell p.1.1) (φ.vertexCell p.1.2) : ℝ)) *
      ∏ t : {t : Fin F.k × Fin F.k × Fin F.k // t.1 < t.2.1 ∧ t.2.1 < t.2.2},
        (H.relativeDensity (F.tripleColor t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2)
          (ψ.polyad t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2) : ℝ) :=
  (rfl)

/-- Local predictions are nonnegative. -/
theorem expectedInducedCountAt_nonneg (φ : PatternPlacement3 C F) (ψ : PairColorPlacement3 φ) :
    0 ≤ H.expectedInducedCountAt φ ψ := by
  rw [expectedInducedCountAt_def]
  refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun p _ ↦ ?_))
    (prod_nonneg fun t _ ↦ ?_)
  · exact_mod_cast pairColorDensity_nonneg _ _ _ _
  · exact_mod_cast H.relativeDensity_nonneg _ _

/-- A local prediction is at most the injection count of its placement, since every density
factor is at most one. -/
theorem expectedInducedCountAt_le_placementInjectionCount (φ : PatternPlacement3 C F)
    (ψ : PairColorPlacement3 φ) : H.expectedInducedCountAt φ ψ ≤ placementInjectionCount φ := by
  rw [expectedInducedCountAt_def, mul_assoc]
  refine mul_le_of_le_one_right (Nat.cast_nonneg _) ((mul_le_of_le_one_left
    (prod_nonneg fun t _ ↦ ?_) (prod_le_one₀ (fun p _ ↦ ?_) fun p _ ↦ ?_)).trans
    (prod_le_one₀ (fun t _ ↦ ?_) fun t _ ↦ ?_))
  · exact_mod_cast H.relativeDensity_nonneg _ _
  · exact_mod_cast pairColorDensity_nonneg _ _ _ _
  · exact_mod_cast pairColorDensity_le_one _ _ _ _
  · exact_mod_cast H.relativeDensity_nonneg _ _
  · exact_mod_cast H.relativeDensity_le_one _ _

variable (C F) in
/-- The predicted number of induced copies of `F` in `H` over the triadic complex `C`: the sum of
the local predictions over all placements and routes. -/
noncomputable def expectedInducedCount : ℝ :=
  ∑ φ : PatternPlacement3 C F, ∑ ψ : PairColorPlacement3 φ, H.expectedInducedCountAt φ ψ

variable (C F) in
theorem expectedInducedCount_def :
    H.expectedInducedCount C F =
      ∑ φ : PatternPlacement3 C F, ∑ ψ : PairColorPlacement3 φ, H.expectedInducedCountAt φ ψ :=
  (rfl)

variable (C F) in
/-- The predicted induced count is nonnegative. -/
theorem expectedInducedCount_nonneg : 0 ≤ H.expectedInducedCount C F :=
  sum_nonneg fun φ _ ↦ sum_nonneg fun ψ _ ↦ H.expectedInducedCountAt_nonneg φ ψ

end Colored3Graph

end TauCeti

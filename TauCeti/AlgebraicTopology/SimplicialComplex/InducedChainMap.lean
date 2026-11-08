/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.ChainComplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Maps

/-!
# Chain maps induced by simplicial maps

A tuple `[v₀, ..., vₙ]` of vertices of a simplicial complex with linearly ordered vertices
determines an ordered simplicial `n`-chain `TauCeti.OrderedSimplicialChain.tupleChain`. It is
`0` when the tuple repeats a vertex, and otherwise it is the cell spanned by the tuple, with the
sign of the permutation sorting the tuple into increasing order. Its boundary is the alternating
sum of the chains of the tuples obtained by deleting one entry, for every tuple spanning a face,
including tuples that repeat a vertex.

An arbitrary simplicial map `f : K → L` therefore induces a chain map of ordered simplicial chain
complexes, sending an increasingly enumerated cell `[v₀, ..., vₙ]` to the chain of
`[f v₀, ..., f vₙ]`. A cell on which `f` is not injective goes to `0`, and a cell on which `f`
reverses the vertex order picks up the sign of the reordering. The map is functorial, so
simplicial maps that are not monotone, such as simplicial approximations, can be computed on
ordered chains.

## Main definitions

* `TauCeti.OrderedSimplicialChain.tupleChain`: the ordered chain of a vertex tuple.
* `TauCeti.OrderedSimplicialChain.map`: the map on ordered chains induced by a simplicial map.
* `TauCeti.orderedSimplicialChainComplexMap`: the induced map of ordered chain complexes.

## Main results

* `TauCeti.OrderedSimplicialChain.tupleChain_comp_perm`: permuting a tuple multiplies its chain
  by the sign of the permutation.
* `TauCeti.OrderedSimplicialChain.boundary_tupleChain`: the boundary of the chain of a tuple is
  the alternating sum of the chains of its deleted-entry tuples.
* `TauCeti.orderedSimplicialChainComplexMap_id`, `TauCeti.orderedSimplicialChainComplexMap_comp`:
  functoriality of the induced chain maps.

## Implementation notes

The coefficient of a cell in the chain of a tuple is the determinant of the `0`/`1` incidence
matrix between the tuple and the increasing enumeration of the cell. This single formula is the
sign of the sorting permutation on tuples of distinct vertices and vanishes on tuples with
repeated vertices, so the boundary formula follows from the Laplace expansion along an adjoined
column of ones, without a case analysis on the shape of the tuple.

## References

* J. R. Munkres, *Elements of Algebraic Topology*, §§5 and 12 (oriented simplices and the chain
  map of a simplicial map).
* A. Hatcher, *Algebraic Topology*, Section 2.1.
-/

public section

noncomputable section

open CategoryTheory Finsupp

universe u v

open AbstractSimplicialComplex

namespace TauCeti

namespace OrderedSimplicialChain

variable {ι : Type u} [LinearOrder ι] {K : AbstractSimplicialComplex ι} {n : ℕ}

section Tuple

/-- The `0`/`1` incidence matrix between a vertex tuple and the increasing enumeration of a
cell. -/
private def incidence {m : ℕ} (g : Fin m → ι) (c : RealizationCell K n) :
    Matrix (Fin m) (Fin (n + 1)) ℤ :=
  Matrix.of fun i k ↦ if g i = c.vertexEmbedding k then 1 else 0

private theorem incidence_comp_perm (g : Fin (n + 1) → ι) (σ : Equiv.Perm (Fin (n + 1)))
    (c : RealizationCell K n) :
    incidence (g ∘ σ) c = (incidence g c).submatrix σ id := by
  ext i k
  simp [incidence]

private theorem injective_of_det_incidence_ne_zero {g : Fin (n + 1) → ι}
    {c : RealizationCell K n} (h : (incidence g c).det ≠ 0) : Function.Injective g := by
  intro i j hij
  by_contra hne
  exact h (Matrix.det_zero_of_row_eq hne (funext fun k ↦ by simp [incidence, hij]))

/-- A tuple with nonzero incidence determinant against a cell enumerates exactly the vertices of
that cell. -/
private theorem image_eq_of_det_incidence_ne_zero {g : Fin (n + 1) → ι}
    {c : RealizationCell K n} (h : (incidence g c).det ≠ 0) : Finset.univ.image g = c.1.1 := by
  have hmem : ∀ i, g i ∈ c.1.1 := fun i ↦ by
    by_contra hi
    refine h (Matrix.det_eq_zero_of_row_eq_zero i fun k ↦ ?_)
    have hk : g i ≠ c.vertexEmbedding k := fun hk ↦ hi (hk ▸ c.vertexEmbedding_mem k)
    simp [incidence, hk]
  refine Finset.eq_of_subset_of_card_le (fun x hx ↦ ?_) ?_
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i
  · rw [c.2, Finset.card_image_of_injective _ (injective_of_det_incidence_ne_zero h),
      Finset.card_univ, Fintype.card_fin]

omit [LinearOrder ι] in
/-- Cells with the same vertex set are equal. -/
private theorem eq_of_val_eq {c d : RealizationCell K n} (h : c.1.1 = d.1.1) : c = d :=
  Subtype.ext (Subtype.ext h)

private theorem det_incidence_vertexEmbedding (c d : RealizationCell K n) :
    (incidence c.vertexEmbedding d).det = if c = d then 1 else 0 := by
  split_ifs with hcd
  · subst hcd
    have h1 : incidence c.vertexEmbedding c = 1 := by
      ext i k
      simp [incidence, Matrix.one_apply, c.vertexEmbedding.injective.eq_iff]
    rw [h1, Matrix.det_one]
  · by_contra h
    exact hcd (eq_of_val_eq ((c.image_vertexEmbedding).symm.trans
      (image_eq_of_det_incidence_ne_zero h)))

variable (R : Type v) [Ring R]

/-- The ordered simplicial chain of a tuple `[g 0, ..., g n]` of vertices. It is `0` when the
tuple repeats a vertex or does not span a face; otherwise it is the cell spanned by the tuple,
multiplied by the sign of the permutation that sorts the tuple increasingly
(`tupleChain_vertexEmbedding_comp`). -/
def tupleChain (g : Fin (n + 1) → ι) : OrderedSimplicialChain K R n :=
  ofSupportFinite (fun c ↦ ((incidence g c).det : R)) <| by
    refine Set.Subsingleton.finite fun c hc d hd ↦ eq_of_val_eq ?_
    have hc' : (incidence g c).det ≠ 0 := fun h ↦ hc (by simp [h])
    have hd' : (incidence g d).det ≠ 0 := fun h ↦ hd (by simp [h])
    exact (image_eq_of_det_incidence_ne_zero hc').symm.trans
      (image_eq_of_det_incidence_ne_zero hd')

variable {R}

private theorem tupleChain_apply (g : Fin (n + 1) → ι) (c : RealizationCell K n) :
    tupleChain R g c = ((incidence g c).det : R) :=
  (rfl)

/-- The chain of the increasing enumeration of a cell is that cell. -/
@[simp]
theorem tupleChain_vertexEmbedding (c : RealizationCell K n) :
    tupleChain R c.vertexEmbedding = single c 1 := by
  ext d
  rw [tupleChain_apply, det_incidence_vertexEmbedding, single_apply]
  split_ifs <;> simp

/-- **Permuting a vertex tuple multiplies its chain by the sign of the permutation.** -/
theorem tupleChain_comp_perm (g : Fin (n + 1) → ι) (σ : Equiv.Perm (Fin (n + 1))) :
    tupleChain (K := K) R (g ∘ σ) = Equiv.Perm.sign σ • tupleChain R g := by
  ext c
  rw [Units.smul_def, Finsupp.smul_apply, tupleChain_apply, tupleChain_apply, incidence_comp_perm,
    Matrix.det_permute, Int.cast_id, Int.cast_mul, zsmul_eq_mul]

/-- The chain of a permuted increasing enumeration of a cell is that cell with the sign of the
permutation. -/
theorem tupleChain_vertexEmbedding_comp (c : RealizationCell K n)
    (σ : Equiv.Perm (Fin (n + 1))) :
    tupleChain R (c.vertexEmbedding ∘ σ) = Equiv.Perm.sign σ • single c 1 := by
  rw [tupleChain_comp_perm, tupleChain_vertexEmbedding]

/-- The chain of a tuple with a repeated vertex vanishes. -/
theorem tupleChain_eq_zero_of_not_injective {g : Fin (n + 1) → ι} (hg : ¬Function.Injective g) :
    tupleChain (K := K) R g = 0 := by
  ext c
  rw [tupleChain_apply, Finsupp.zero_apply]
  by_contra h
  exact hg (injective_of_det_incidence_ne_zero fun h' ↦ h (by rw [h', Int.cast_zero]))

/-- The chain of a tuple whose vertices do not span a face vanishes. -/
theorem tupleChain_eq_zero_of_image_notMem {g : Fin (n + 1) → ι} (hg : Finset.univ.image g ∉ K) :
    tupleChain (K := K) R g = 0 := by
  ext c
  rw [tupleChain_apply, Finsupp.zero_apply]
  by_contra h
  exact hg ((image_eq_of_det_incidence_ne_zero fun h' ↦ h (by rw [h', Int.cast_zero])) ▸ c.1.2)

/-- The integer matrix obtained by adjoining a column of ones to the incidence matrix of a
tuple of `n + 2` vertices against an `n`-cell. Its Laplace expansion along the column of ones
is the coefficient of the alternating deleted-entry sum. -/
private def boundaryIncidence (g : Fin (n + 2) → ι) (d : RealizationCell K n) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ :=
  Matrix.of fun i ↦ (Fin.cons 1 fun k ↦ incidence g d i k : Fin (n + 2) → ℤ)

private theorem det_boundaryIncidence (g : Fin (n + 2) → ι) (d : RealizationCell K n) :
    (boundaryIncidence g d).det =
      ∑ j : Fin (n + 2), (-1) ^ (j : ℕ) * (incidence (g ∘ j.succAbove) d).det := by
  rw [Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h : (boundaryIncidence g d).submatrix j.succAbove Fin.succ =
      incidence (g ∘ j.succAbove) d := by
    ext a k
    simp [boundaryIncidence, incidence]
  rw [h]
  simp [boundaryIncidence]

private theorem det_boundaryIncidence_comp_perm (g : Fin (n + 2) → ι)
    (σ : Equiv.Perm (Fin (n + 2))) (d : RealizationCell K n) :
    (boundaryIncidence (g ∘ σ) d).det = Equiv.Perm.sign σ * (boundaryIncidence g d).det := by
  have h : boundaryIncidence (g ∘ σ) d = (boundaryIncidence g d).submatrix σ id := by
    ext i k
    simp [boundaryIncidence, incidence]
  rw [h, Matrix.det_permute, Int.cast_id]

private theorem det_boundaryIncidence_of_not_injective {g : Fin (n + 2) → ι}
    (hg : ¬Function.Injective g) (d : RealizationCell K n) :
    (boundaryIncidence g d).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, g i = g j ∧ i ≠ j := by
    simpa [Function.Injective] using hg
  exact Matrix.det_zero_of_row_eq hne (funext fun k ↦ by simp [boundaryIncidence, incidence, hij])

private theorem sum_tupleChain_comp_succAbove_apply (g : Fin (n + 2) → ι)
    (d : RealizationCell K n) :
    (∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) • tupleChain R (g ∘ j.succAbove)) d =
      ((boundaryIncidence g d).det : R) := by
  simp [det_boundaryIncidence, Finset.sum_apply', tupleChain_apply]

/-- **The boundary of the chain of a vertex tuple.** For a tuple of vertices spanning a face,
the boundary of its chain is the alternating sum of the chains of the tuples obtained by
deleting one entry. Both sides vanish when the tuple repeats a vertex. -/
theorem boundary_tupleChain {g : Fin (n + 2) → ι} (hg : Finset.univ.image g ∈ K) :
    boundary R n (tupleChain (K := K) R g) =
      ∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) • tupleChain R (g ∘ j.succAbove) := by
  by_cases hinj : Function.Injective g
  · -- Reduce to the increasing enumeration of a cell, where this is the definition of the
    -- boundary; both sides change by the sign of the sorting permutation.
    obtain ⟨c, σ, rfl⟩ := RealizationCell.exists_eq_vertexEmbedding_comp hinj hg
    have hc : boundary R n (single c 1) = ∑ j : Fin (n + 2),
        (-1 : R) ^ (j : ℕ) • tupleChain R (c.vertexEmbedding ∘ j.succAbove) := by
      rw [boundary_single]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← RealizationCell.vertexEmbedding_face, tupleChain_vertexEmbedding]
    ext d
    rw [tupleChain_vertexEmbedding_comp, Units.smul_def, map_zsmul, hc, Finsupp.smul_apply,
      sum_tupleChain_comp_succAbove_apply, sum_tupleChain_comp_succAbove_apply,
      det_boundaryIncidence_comp_perm, Int.cast_mul, zsmul_eq_mul]
  · ext d
    rw [tupleChain_eq_zero_of_not_injective hinj, map_zero, sum_tupleChain_comp_succAbove_apply,
      det_boundaryIncidence_of_not_injective hinj, Finsupp.zero_apply, Int.cast_zero]

end Tuple

section Map

variable {κ τ : Type*} [LinearOrder κ] [LinearOrder τ]
  {L : AbstractSimplicialComplex κ} {P : AbstractSimplicialComplex τ}
  (R : Type v) [Ring R]
  (f : PreAbstractSimplicialComplex.SimplicialMap
    K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)

/-- A simplicial map sends a vertex tuple spanning a face to a vertex tuple spanning a face. -/
private theorem image_comp_mem {m : ℕ} {g : Fin m → ι} (hg : Finset.univ.image g ∈ K) :
    Finset.univ.image (f ∘ g) ∈ L := by
  rw [← Finset.image_image]
  exact f.map_face hg

/-- The map on ordered chains induced by a simplicial map. A cell with increasing vertices
`[v₀, ..., vₙ]` goes to the chain of the tuple `[f v₀, ..., f vₙ]`: it vanishes when `f`
identifies two vertices of the cell, and otherwise it is the image cell with the sign of the
permutation sorting the image vertices. -/
def map (n : ℕ) : OrderedSimplicialChain K R n →ₗ[R] OrderedSimplicialChain L R n :=
  linearCombination R fun c ↦ tupleChain R (f ∘ c.vertexEmbedding)

variable {R}

/-- A multiple of a cell goes to that multiple of the chain of the image of its increasing
vertex enumeration. -/
@[simp]
theorem map_single (c : RealizationCell K n) (r : R) :
    map R f n (single c r) = r • tupleChain R (f ∘ c.vertexEmbedding) :=
  linearCombination_single R r c

/-- The induced map sends the chain of a vertex tuple to the chain of its image tuple. -/
theorem map_tupleChain {g : Fin (n + 1) → ι} (hg : Finset.univ.image g ∈ K) :
    map R f n (tupleChain R g) = tupleChain R (f ∘ g) := by
  by_cases hinj : Function.Injective g
  · obtain ⟨c, σ, rfl⟩ := RealizationCell.exists_eq_vertexEmbedding_comp hinj hg
    rw [tupleChain_vertexEmbedding_comp, Units.smul_def, map_zsmul, map_single, one_smul,
      ← Function.comp_assoc, tupleChain_comp_perm, Units.smul_def]
  · rw [tupleChain_eq_zero_of_not_injective hinj, map_zero,
      tupleChain_eq_zero_of_not_injective fun h ↦ hinj h.of_comp]

/-- The identity simplicial map induces the identity on ordered chains. -/
@[simp]
theorem map_id (n : ℕ) :
    map R (PreAbstractSimplicialComplex.SimplicialMap.id K.toPreAbstractSimplicialComplex) n =
      LinearMap.id := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp

/-- The map induced by a composite of simplicial maps is the composite of the induced maps. -/
theorem map_comp
    (g : PreAbstractSimplicialComplex.SimplicialMap
      L.toPreAbstractSimplicialComplex P.toPreAbstractSimplicialComplex) (n : ℕ) :
    map R (g.comp f) n = map R g n ∘ₗ map R f n := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  have hc : Finset.univ.image c.vertexEmbedding ∈ K := c.image_vertexEmbedding ▸ c.1.2
  simp only [LinearMap.comp_apply, lsingle_apply, map_single, one_smul,
    map_tupleChain g (image_comp_mem f hc),
    PreAbstractSimplicialComplex.SimplicialMap.coe_comp, Function.comp_assoc]

/-- The induced maps commute with the alternating boundary. -/
theorem boundary_comp_map (n : ℕ) :
    boundary R n ∘ₗ map R f (n + 1) = map R f n ∘ₗ boundary R n := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  have hc : Finset.univ.image c.vertexEmbedding ∈ K := c.image_vertexEmbedding ▸ c.1.2
  simp only [LinearMap.comp_apply, lsingle_apply, map_single, one_smul,
    boundary_tupleChain (image_comp_mem f hc), boundary_single, map_sum, map_smul,
    RealizationCell.vertexEmbedding_face, Function.comp_assoc]

end Map

end OrderedSimplicialChain

variable {ι κ τ : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder τ]
  {K : AbstractSimplicialComplex ι} {L : AbstractSimplicialComplex κ}
  {P : AbstractSimplicialComplex τ}
  (R : Type v) [Ring R]
  (f : PreAbstractSimplicialComplex.SimplicialMap
    K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)

/-- The map of ordered simplicial chain complexes induced by a simplicial map. It sends an
oriented simplex to the oriented image simplex, with the sign of the reordering of its vertices,
and to `0` when the simplicial map collapses it. -/
def orderedSimplicialChainComplexMap :
    orderedSimplicialChainComplex K R ⟶ orderedSimplicialChainComplex L R where
  f n := eqToHom (orderedSimplicialChainComplex_X R n) ≫
    ModuleCat.ofHom (OrderedSimplicialChain.map R f n) ≫
      eqToHom (orderedSimplicialChainComplex_X R n).symm
  comm' i j h := by
    subst i
    simp only [orderedSimplicialChainComplex_d, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    congr 1
    simp only [← Category.assoc]
    congr 1
    exact ModuleCat.hom_ext (OrderedSimplicialChain.boundary_comp_map f j)

/-- The degreewise map is the linear extension of the map on cells. -/
@[simp]
theorem orderedSimplicialChainComplexMap_f (n : ℕ) :
    (orderedSimplicialChainComplexMap R f).f n =
      eqToHom (orderedSimplicialChainComplex_X R n) ≫
        ModuleCat.ofHom (OrderedSimplicialChain.map R f n) ≫
          eqToHom (orderedSimplicialChainComplex_X R n).symm :=
  (rfl)

/-- The identity simplicial map induces the identity chain map. -/
@[simp]
theorem orderedSimplicialChainComplexMap_id :
    orderedSimplicialChainComplexMap R
        (PreAbstractSimplicialComplex.SimplicialMap.id K.toPreAbstractSimplicialComplex) =
      𝟙 _ := by
  ext n : 1
  simp [OrderedSimplicialChain.map_id]

/-- Composing simplicial maps composes their induced chain maps. -/
theorem orderedSimplicialChainComplexMap_comp
    (g : PreAbstractSimplicialComplex.SimplicialMap
      L.toPreAbstractSimplicialComplex P.toPreAbstractSimplicialComplex) :
    orderedSimplicialChainComplexMap R (g.comp f) =
      orderedSimplicialChainComplexMap R f ≫ orderedSimplicialChainComplexMap R g := by
  ext n : 1
  simp only [orderedSimplicialChainComplexMap_f, HomologicalComplex.comp_f,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  congr 1
  rw [← Category.assoc, cancel_mono, ← ModuleCat.ofHom_comp]
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_ofHom]
  exact OrderedSimplicialChain.map_comp f g n

end TauCeti

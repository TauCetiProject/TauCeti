/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.AdjunctionModel
public import TauCeti.Topology.Homotopy.Extension.Tower
import Mathlib.CategoryTheory.Functor.OfSequence
import TauCeti.Topology.Category.TopCat.ClosedEmbedding
import TauCeti.Topology.Category.TopCat.DisjointOpens
import TauCeti.Logic.Equiv.Sum
import TauCeti.Topology.CWComplex.Abstract.Hausdorff
import TauCeti.Topology.CWComplex.Classical.SequentialColimit

/-!
# CW models of towers of cell attachments

Let a space `X` be the union of an increasing sequence of subsets `Z 0 ⊆ Z 1 ⊆ ⋯`, carrying the
topology coherent with them, each `Z k` having the homotopy extension property in `Z (k + 1)`.
Suppose that each `Z (k + 1)` is obtained from `Z k`, up to homotopy, by attaching disks: there
are maps `a k i : ∂Dⁿ⁽ᵏ ⁱ⁾ → Z k` and a homotopy equivalence
`Φ k : Z k ∪_{a k} ⨆ᵢ Dⁿ⁽ᵏ ⁱ⁾ ≃ₕ Z (k + 1)` which is the inclusion on `Z k`. If `Z 0` is
homotopy equivalent to a Hausdorff CW complex `W₀`, then `X` is homotopy equivalent to a Hausdorff
CW complex whose `m`-cells are the `m`-cells of `W₀` together with one `m`-cell for each pair
`(k, i)` with `n k i = m` (`TauCeti.exists_cwComplex_homotopyEquiv_of_isCoherentWith`).

Each stage may attach infinitely many cells, of any dimensions, and a later stage may attach cells
of lower dimension than an earlier one. This is the situation of a proper Morse function bounded
below: its sublevels at an increasing sequence of regular values exhaust the manifold, their
inclusions are closed cofibrations, and crossing the critical levels between two of them attaches
one cell for each critical point, of dimension its index (Milnor, *Morse Theory*, Theorem 3.5).

## Proof

The CW models `W k ≃ₕ Z k` are built by induction. Given `W k`, the attaching maps `a k i` are
moved by cellular approximation into the skeleta of `W k`, and attaching the disks along them gives
a CW complex `W (k + 1)` containing `W k` as a subcomplex, with a homotopy equivalence to
`Z (k + 1)` which restricts exactly to that of `W k`
(`ContinuousMap.HomotopyEquiv.exists_homotopyEquiv_sigmaDiskAdjunction`). The model of `X` is the
colimit `W` of the tower of closed embeddings `W 0 → W 1 → ⋯` in `TopCat`.

* `W` is Hausdorff because each `W k → W (k + 1)` is a relative CW complex, so each `W k → W`
  extends disjoint open sets (`TauCeti.TopCat.t2Space_of_isColimit`).
* Each `W k → W (k + 1)` is a closed embedding carrying cells onto cells, so `W` is a CW complex
  (`TauCeti.cwComplexOfIsColimit`), whose cells are those of `W 0` and the attached cells
  (`TauCeti.cwComplexOfIsColimitCellEquiv`).
* The homotopy equivalences `W k ≃ₕ Z k` commute strictly with the inclusions, so they induce a
  map `W → X`, which is a homotopy equivalence because both sides are unions of towers of
  cofibrations (`TauCeti.hasHomotopyExtensionProperty_preimage_range_ι` and
  `TauCeti.exists_homotopyEquiv_of_isCoherentWith`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and its proof, where a manifold is assembled from the cells attached at its
  critical levels.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Cambridge
  University Press, 2002, Proposition 0.18 and Section 4.1, Theorem 4.8, for the homotopy
  invariance of attachments and cellular approximation, and the Appendix for the weak topology
  of a union of cell complexes.
-/

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex
open scoped ContinuousMap

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {Z : ℕ → Set X} {ι : ℕ → Type u} {n : ∀ k, ι k → ℕ}

/-! The construction, private to this file. -/

namespace TowerModel

/-- The space obtained by attaching the disks `Dⁿⁱ` to `Y` along the maps `b i`. -/
abbrev Adj {Y : Type u} [TopologicalSpace Y] {κ : Type u} {m : κ → ℕ}
    (b : ∀ i, C(TopCat.diskBoundary.{u} (m i), Y)) : TopCat.{u} :=
  letI := sigmaDiskRelCWComplex m
  relCWAdjunctionSpace (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (m i))))
    (sigmaDiskAttachingMap b)

/-- The inclusion of `Y` into `Y ∪_b ⨆ᵢ Dⁿⁱ`. -/
abbrev adjInr {Y : Type u} [TopologicalSpace Y] {κ : Type u} {m : κ → ℕ}
    (b : ∀ i, C(TopCat.diskBoundary.{u} (m i), Y)) : TopCat.of Y ⟶ Adj b :=
  letI := sigmaDiskRelCWComplex m
  pushout.inr (relCWBaseInclusion (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (m i)))))
    (TopCat.ofHom (sigmaDiskAttachingMap b))

/-- A CW model of a space `Y`: a Hausdorff CW complex with a homotopy equivalence to `Y`. -/
structure Stage (Y : Type u) [TopologicalSpace Y] where
  /-- The CW complex. -/
  W : TopCat.{u}
  t2 : T2Space W
  cw : CWComplex (univ : Set W)
  /-- The homotopy equivalence with `Y`. -/
  h : W ≃ₕ Y

attribute [instance] Stage.t2 Stage.cw

section Next

variable {Y Y' : Type u} [TopologicalSpace Y] [TopologicalSpace Y'] {κ : Type u} {m : κ → ℕ}
  (s : Stage Y) (a : ∀ i, C(TopCat.diskBoundary.{u} (m i), Y))

theorem Stage.exists_next :
    ∃ (b : ∀ i, C(TopCat.diskBoundary.{u} (m i), s.W)),
      (∀ i x, b i x ∈ (skeletonLT (univ : Set s.W) (m i) : Set s.W)) ∧
      ∃ Ψ : Adj b ≃ₕ Adj a, ∀ w : s.W, Ψ (adjInr b w) = adjInr a (s.h w) := by
  obtain ⟨b, hb, -, Ψ, hΨ⟩ := s.h.exists_homotopyEquiv_sigmaDiskAdjunction a
  exact ⟨b, hb, Ψ, hΨ⟩

/-- The attaching maps of the next stage, moved into the skeleta of `s.W`. -/
def Stage.nextAttach : ∀ i, C(TopCat.diskBoundary.{u} (m i), s.W) := (s.exists_next a).choose

theorem Stage.nextAttach_mem (i : κ) (x : TopCat.diskBoundary.{u} (m i)) :
    s.nextAttach a i x ∈ (skeletonLT (univ : Set s.W) (m i) : Set s.W) :=
  (s.exists_next a).choose_spec.1 i x

/-- The comparison of the attachment to `s.W` with the attachment to `Y`. -/
def Stage.nextEquiv : Adj (s.nextAttach a) ≃ₕ Adj a := (s.exists_next a).choose_spec.2.choose

theorem Stage.nextEquiv_adjInr (w : s.W) :
    s.nextEquiv a (adjInr (s.nextAttach a) w) = adjInr a (s.h w) :=
  (s.exists_next a).choose_spec.2.choose_spec w

/-- The next stage: the CW complex obtained by attaching cells to `s.W`, modelling a space `Y'`
homotopy equivalent to the attachment `Y ∪_a ⨆ᵢ Dⁿⁱ`. -/
def Stage.next (Φ : Adj a ≃ₕ Y') : Stage Y' where
  W := Adj (s.nextAttach a)
  t2 := by
    let := sigmaDiskRelCWComplex m
    infer_instance
  cw := sigmaDiskAdjunctionCWComplex m (s.nextAttach a) (nextAttach_mem s a)
  h := (s.nextEquiv a).trans Φ

end Next


variable (s₀ : Stage (Z 0)) (a : ∀ k i, C(TopCat.diskBoundary.{u} (n k i), Z k))
  (Φ : ∀ k, Adj (a k) ≃ₕ Z (k + 1))

/-- The stages of the CW model of the tower. -/
def stage : ∀ k, Stage (Z k)
  | 0 => s₀
  | k + 1 => (stage k).next (a k) (Φ k)

/-- The inclusion of each stage into the next. -/
def incl (k : ℕ) : (stage s₀ a Φ k).W ⟶ (stage s₀ a Φ (k + 1)).W :=
  adjInr ((stage s₀ a Φ k).nextAttach (a k))

theorem isClosedEmbedding_incl (k : ℕ) : IsClosedEmbedding (incl s₀ a Φ k) := by
  let := sigmaDiskRelCWComplex (n k)
  exact isClosedEmbedding_pushout_inr_relCWBaseInclusion _

theorem extendsDisjointOpens_incl (k : ℕ) : TopCat.extendsDisjointOpens (incl s₀ a Φ k) := by
  let := sigmaDiskRelCWComplex (n k)
  exact (relCWAdjunctionSpaceRelativeCWComplex _ _).extendsDisjointOpens

/-- The tower of stages, as a functor `ℕ ⥤ TopCat`. -/
def tower : ℕ ⥤ TopCat.{u} := Functor.ofSequence (incl s₀ a Φ)

theorem tower_map_succ (k : ℕ) : (tower s₀ a Φ).map (homOfLE k.le_succ) = incl s₀ a Φ k :=
  Functor.ofSequence_map_homOfLE_succ _ k

theorem isClosedEmbedding_tower_map_succ (k : ℕ) :
    IsClosedEmbedding ((tower s₀ a Φ).map (homOfLE k.le_succ)) := by
  rw [tower_map_succ]
  exact isClosedEmbedding_incl s₀ a Φ k

instance (k : ℕ) : CWComplex (univ : Set ((tower s₀ a Φ).obj k)) := (stage s₀ a Φ k).cw

instance (k : ℕ) : T2Space ((tower s₀ a Φ).obj k) := (stage s₀ a Φ k).t2

/-- The cells of the next stage are the cells of a stage together with the attached cells. -/
def cellEquiv (k m : ℕ) :
    cell (univ : Set ((tower s₀ a Φ).obj (k + 1))) m ≃
      cell (univ : Set ((tower s₀ a Φ).obj k)) m ⊕ {i : ι k // n k i = m} :=
  letI := sigmaDiskRelCWComplex (n k)
  sigmaDiskAdjunctionCWComplexCellEquiv (n k) _ ((stage s₀ a Φ k).nextAttach_mem (a k)) m

/-- The cells of a stage, as cells of the next stage. -/
def cellIncl (k m : ℕ) :
    cell (univ : Set ((tower s₀ a Φ).obj k)) m → cell (univ : Set ((tower s₀ a Φ).obj (k + 1))) m :=
  (cellEquiv s₀ a Φ k m).symm ∘ Sum.inl

theorem coe_map_cellIncl (k m : ℕ) (j : cell (univ : Set ((tower s₀ a Φ).obj k)) m) :
    ⇑(map m (cellIncl s₀ a Φ k m j)) = (tower s₀ a Φ).map (homOfLE k.le_succ) ∘ map m j := by
  let := sigmaDiskRelCWComplex (n k)
  rw [tower_map_succ]
  exact funext <| sigmaDiskAdjunctionCWComplex_map_inl (n k) _
    ((stage s₀ a Φ k).nextAttach_mem (a k)) m j

/-- The colimit of the tower of stages. -/
abbrev L : TopCat.{u} := colimit (tower s₀ a Φ)

/-- The inclusion of a stage into the colimit. -/
abbrev ιL (k : ℕ) : (stage s₀ a Φ k).W ⟶ L s₀ a Φ := colimit.ι (tower s₀ a Φ) k

/-- The inclusion of the first stage into the colimit, as a transfinite composition of the
inclusions of the stages. -/
def towerTransfiniteComposition (P : MorphismProperty TopCat.{u})
    (hP : ∀ k, P (incl s₀ a Φ k)) : P.TransfiniteCompositionOfShape ℕ (ιL s₀ a Φ 0) where
  F := tower s₀ a Φ
  isoBot := Iso.refl _
  incl := (colimit.cocone _).ι
  isColimit := colimit.isColimit _
  map_mem k _ := by
    have h := hP k
    rw [← tower_map_succ] at h
    exact h

instance : T2Space (L s₀ a Φ) :=
  TopCat.t2Space_of_isColimit (colimit.isColimit _) fun k ↦
    (towerTransfiniteComposition s₀ a Φ TopCat.extendsDisjointOpens fun k ↦
      extendsDisjointOpens_incl s₀ a Φ k).mem_incl_app k

/-- The CW structure on the colimit, whose cells are those of the stages. -/
@[instance_reducible]
def cw : CWComplex (univ : Set (L s₀ a Φ)) :=
  cwComplexOfIsColimit (isClosedEmbedding_tower_map_succ s₀ a Φ) (coe_map_cellIncl s₀ a Φ)
    (colimit.isColimit _)

/-- The cells of the colimit are the cells of the first stage and the attached cells. -/
def cwCellEquiv (m : ℕ) :
    @cell (L s₀ a Φ) _ univ ∅ (@CWComplex.instRelCWComplex _ _ _ (cw s₀ a Φ)) m ≃
      (s₀.cw.cell m ⊕ Σ k, {i : ι k // n k i = m}) :=
  (cwComplexOfIsColimitCellEquiv (isClosedEmbedding_tower_map_succ s₀ a Φ)
    (coe_map_cellIncl s₀ a Φ) (colimit.isColimit _) m).trans <|
  Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaCongrRight fun k ↦
    (cellEquiv s₀ a Φ k m).complRangeSymmInl)

variable (hΦ : ∀ k (z : Z k), (Φ k (adjInr (a k) z) : X) = z)
include hΦ

theorem h_incl (k : ℕ) (w : (stage s₀ a Φ k).W) :
    ((stage s₀ a Φ (k + 1)).h (incl s₀ a Φ k w) : X) = (stage s₀ a Φ k).h w := by
  -- The equivalence of the next stage is `nextEquiv` followed by `Φ k`, by definition.
  change (Φ k (Stage.nextEquiv _ (a k) (adjInr _ w)) : X) = _
  rw [Stage.nextEquiv_adjInr]
  exact hΦ k _

/-- The map from the colimit to `X` induced by the homotopy equivalences of the stages. -/
def toX : L s₀ a Φ ⟶ TopCat.of X :=
  colimit.desc (tower s₀ a Φ)
    { pt := TopCat.of X
      ι := NatTrans.ofSequence
        (fun k ↦ TopCat.ofHom ⟨fun w ↦ ((stage s₀ a Φ k).h w : X),
          continuous_subtype_val.comp (stage s₀ a Φ k).h.toFun.continuous⟩)
        fun k ↦ by
          rw [tower_map_succ]
          ext w
          exact h_incl s₀ a Φ hΦ k w }

theorem toX_ιL (k : ℕ) (w : (stage s₀ a Φ k).W) :
    toX s₀ a Φ hΦ (ιL s₀ a Φ k w) = ((stage s₀ a Φ k).h w : X) := by
  -- Read the left side as a composite, to apply `colimit.ι_desc`.
  change (colimit.ι (tower s₀ a Φ) k ≫ toX s₀ a Φ hΦ) w = _
  rw [toX, colimit.ι_desc]
  rfl

theorem monotone_Z : Monotone Z :=
  monotone_nat_of_le_succ fun k z hz ↦ by
    have h : (Φ k (adjInr (a k) ⟨z, hz⟩) : X) = z := hΦ k ⟨z, hz⟩
    exact h ▸ (Φ k (adjInr (a k) ⟨z, hz⟩)).2

theorem exists_homotopyEquiv (hZX : ⋃ k, Z k = univ) (hZc : IsCoherentWith (range Z))
    (hZH : ∀ k, HasHomotopyExtensionProperty ((↑) ⁻¹' Z k : Set (Z (k + 1)))) :
    Nonempty (L s₀ a Φ ≃ₕ X) := by
  have hc := colimit.isColimit (tower s₀ a Φ)
  have hemb := TopCat.isClosedEmbedding_ι_of_isColimit_of_succ
    (isClosedEmbedding_tower_map_succ s₀ a Φ) hc
  -- Each stage is homeomorphic to its image in the colimit.
  let e (k : ℕ) : (stage s₀ a Φ k).W ≃ₜ (range (ιL s₀ a Φ k) : Set (L s₀ a Φ)) :=
    (hemb k).isEmbedding.toHomeomorph
  obtain ⟨h, -, -⟩ := exists_homotopyEquiv_of_isCoherentWith (TopCat.monotone_range_ι _)
    (monotone_Z a Φ hΦ) (TopCat.iUnion_range_ι_of_isColimit hc) hZX
    (TopCat.isCoherentWith_range_ι_of_isColimit hc) hZc
    (hasHomotopyExtensionProperty_preimage_range_ι (isClosedEmbedding_tower_map_succ s₀ a Φ)
      (coe_map_cellIncl s₀ a Φ) hc) hZH (toX s₀ a Φ hΦ).hom
    (fun k ↦ (e k).symm.toHomotopyEquiv.trans (stage s₀ a Φ k).h) fun k ↦ by
      rintro ⟨_, w, rfl⟩
      -- The composite inverts `ιL s₀ a Φ k` on its range and then applies the model of `Z k`.
      exact (congrArg (fun v ↦ ((stage s₀ a Φ k).h v : X))
        ((hemb k).isEmbedding.toHomeomorph_symm_apply w)).trans (toX_ιL s₀ a Φ hΦ k w).symm
  exact ⟨h⟩

end TowerModel

/-- **CW models of towers of cell attachments.** Let `X` be the union of an increasing sequence
`Z 0 ⊆ Z 1 ⊆ ⋯`, carrying the topology coherent with it, each `Z k` having the homotopy extension
property in `Z (k + 1)`. Suppose that `Z (k + 1)` is homotopy equivalent to the space
`Z k ∪_{a k} ⨆ᵢ Dⁿ⁽ᵏ ⁱ⁾` obtained by attaching disks to `Z k` along maps `a k i`, by a homotopy
equivalence `Φ k` which is the inclusion on `Z k`, and that `Z 0` is homotopy equivalent to a
Hausdorff CW complex `W₀`. Then `X` is homotopy equivalent to a Hausdorff CW complex whose
`m`-cells are the `m`-cells of `W₀` together with the indices `(k, i)` with `n k i = m`. -/
public theorem exists_cwComplex_homotopyEquiv_of_isCoherentWith
    (hZX : ⋃ k, Z k = univ) (hZc : IsCoherentWith (range Z))
    (hZH : ∀ k, HasHomotopyExtensionProperty ((↑) ⁻¹' Z k : Set (Z (k + 1))))
    {W₀ : Type u} [TopologicalSpace W₀] [T2Space W₀] [CWComplex (univ : Set W₀)]
    (h₀ : W₀ ≃ₕ Z 0) (a : ∀ k i, C(TopCat.diskBoundary.{u} (n k i), Z k))
    (Φ : ∀ k, (letI := sigmaDiskRelCWComplex (n k)
      relCWAdjunctionSpace (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n k i))))
        (sigmaDiskAttachingMap (a k))) ≃ₕ Z (k + 1))
    (hΦ : ∀ k (z : Z k), letI := sigmaDiskRelCWComplex (n k)
      (Φ k (pushout.inr (relCWBaseInclusion
        (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (n k i)))))
          (TopCat.ofHom (sigmaDiskAttachingMap (a k))) z) : X) = z) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      Nonempty (W ≃ₕ X) ∧ ∀ m, Nonempty (cell (univ : Set W) m ≃
        (cell (univ : Set W₀) m ⊕ Σ k, {i : ι k // n k i = m})) := by
  let s₀ : TowerModel.Stage (Z 0) := ⟨TopCat.of W₀, ‹_›, ‹_›, h₀⟩
  obtain ⟨e⟩ := TowerModel.exists_homotopyEquiv s₀ a Φ hΦ hZX hZc hZH
  exact ⟨TowerModel.L s₀ a Φ, inferInstance, inferInstance, TowerModel.cw s₀ a Φ, ⟨e⟩,
    fun m ↦ ⟨TowerModel.cwCellEquiv s₀ a Φ m⟩⟩

end TauCeti

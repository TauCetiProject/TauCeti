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
import TauCeti.Topology.CWComplex.Abstract.Hausdorff
import TauCeti.Topology.CWComplex.Classical.Tower.Union
import TauCeti.Topology.Homotopy.Extension.Pushout

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
* `W` is the union of the images of the stages, which form a tower of CW complexes with the
  topology coherent with them, so it is a CW complex (`TauCeti.cwSubcomplexTowerUnion`), whose
  cells are those of `W 0` and the attached cells.
* The homotopy equivalences `W k ≃ₕ Z k` commute strictly with the inclusions, so they induce a
  map `W → X`, which is a homotopy equivalence because both sides are unions of towers of
  cofibrations (`TauCeti.exists_homotopyEquiv_of_isCoherentWith`).

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

section Univ

variable {Y : Type u} [TopologicalSpace Y]

theorem exists_cwComplex_univ {C : Set Y} (h : CWComplex C) (hC : C = univ) :
    ∃ h' : CWComplex (univ : Set Y), ∀ m, Nonempty (h'.cell m ≃ h.cell m) := by
  subst hC
  exact ⟨h, fun m ↦ ⟨Equiv.refl _⟩⟩

end Univ

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

theorem hasHomotopyExtensionProperty_range_incl (k : ℕ) :
    HasHomotopyExtensionProperty (range (incl s₀ a Φ k)) := by
  let := sigmaDiskRelCWComplex (n k)
  exact (IsPushout.of_hasPushout _ _).hasHomotopyExtensionProperty_range_inr
    (isEmbedding_relCWBaseInclusion _) (hasHomotopyExtensionProperty_range_relCWBaseInclusion _)

/-- The tower of stages, as a functor `ℕ ⥤ TopCat`. -/
def tower : ℕ ⥤ TopCat.{u} := Functor.ofSequence (incl s₀ a Φ)

theorem tower_map_succ (k : ℕ) :
    (tower s₀ a Φ).map (homOfLE (Nat.le_add_right k 1)) = incl s₀ a Φ k :=
  Functor.ofSequence_map_homOfLE_succ _ k

/-- The colimit of the tower of stages. -/
abbrev L : TopCat.{u} := colimit (tower s₀ a Φ)

/-- The inclusion of a stage into the colimit. -/
abbrev ιL (k : ℕ) : (stage s₀ a Φ k).W ⟶ L s₀ a Φ := colimit.ι (tower s₀ a Φ) k

@[reassoc]
theorem incl_ιL (k : ℕ) : incl s₀ a Φ k ≫ ιL s₀ a Φ (k + 1) = ιL s₀ a Φ k := by
  rw [← tower_map_succ]
  exact colimit.w _ _

theorem ιL_incl_apply (k : ℕ) (w : (stage s₀ a Φ k).W) :
    ιL s₀ a Φ (k + 1) (incl s₀ a Φ k w) = ιL s₀ a Φ k w :=
  ConcreteCategory.congr_hom (incl_ιL s₀ a Φ k) w

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

theorem isClosedEmbedding_ιL (k : ℕ) : IsClosedEmbedding (ιL s₀ a Φ k) :=
  (TopCat.isClosedEmbedding_iff _).1 <|
    (towerTransfiniteComposition s₀ a Φ TopCat.isClosedEmbedding fun k ↦
      (TopCat.isClosedEmbedding_iff _).2 (isClosedEmbedding_incl s₀ a Φ k)).mem_incl_app k

instance : T2Space (L s₀ a Φ) :=
  have (k : ℕ) : T2Space ((tower s₀ a Φ).obj k) := (stage s₀ a Φ k).t2
  TopCat.t2Space_of_isColimit (colimit.isColimit _) fun k ↦
    (towerTransfiniteComposition s₀ a Φ TopCat.extendsDisjointOpens fun k ↦
      extendsDisjointOpens_incl s₀ a Φ k).mem_incl_app k

theorem exists_ιL_eq (y : L s₀ a Φ) : ∃ k w, ιL s₀ a Φ k w = y :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) (colimit.isColimit _)) y

/-- The CW structure of a stage, carried to its image in the colimit. -/
@[instance_reducible]
def stageCW (k : ℕ) : CWComplex (range (ιL s₀ a Φ k)) :=
  letI := (isClosedEmbedding_ιL s₀ a Φ k).relCWComplex (C := univ) (D := ∅) image_univ
    (image_empty _)
  RelCWComplex.toCWComplex _

/-- The cells of a stage, read in its image in the colimit, are the cells of the stage. -/
def stageCWCellEquiv (k m : ℕ) :
    (stageCW s₀ a Φ k).cell m ≃ cell (univ : Set (stage s₀ a Φ k).W) m :=
  (isClosedEmbedding_ιL s₀ a Φ k).relCWComplexCellEquiv image_univ (image_empty _) m

theorem coe_map_stageCW (k m : ℕ) (j : (stageCW s₀ a Φ k).cell m) :
    ⇑((stageCW s₀ a Φ k).map m j) = ιL s₀ a Φ k ∘ map m (stageCWCellEquiv s₀ a Φ k m j) :=
  IsClosedEmbedding.coe_map_relCWComplex _ image_univ (image_empty _) m j

/-- The cells of a stage, as cells of the next stage. -/
def cellIncl (k m : ℕ) : (stageCW s₀ a Φ k).cell m → (stageCW s₀ a Φ (k + 1)).cell m :=
  letI := sigmaDiskRelCWComplex (n k)
  fun j ↦ (stageCWCellEquiv s₀ a Φ (k + 1) m).symm
    ((sigmaDiskAdjunctionCWComplexCellEquiv (n k) ((stage s₀ a Φ k).nextAttach (a k))
      ((stage s₀ a Φ k).nextAttach_mem (a k)) m).symm (.inl (stageCWCellEquiv s₀ a Φ k m j)))

theorem map_cellIncl (k m : ℕ) (j : (stageCW s₀ a Φ k).cell m) :
    ⇑((stageCW s₀ a Φ (k + 1)).map m (cellIncl s₀ a Φ k m j)) =
      ⇑((stageCW s₀ a Φ k).map m j) := by
  let := sigmaDiskRelCWComplex (n k)
  have hj : stageCWCellEquiv s₀ a Φ (k + 1) m (cellIncl s₀ a Φ k m j) =
      (sigmaDiskAdjunctionCWComplexCellEquiv (n k) ((stage s₀ a Φ k).nextAttach (a k))
        ((stage s₀ a Φ k).nextAttach_mem (a k)) m).symm (.inl (stageCWCellEquiv s₀ a Φ k m j)) :=
    Equiv.apply_symm_apply _ _
  funext x
  rw [coe_map_stageCW, coe_map_stageCW, Function.comp_apply, Function.comp_apply, hj]
  exact (congrArg (ιL s₀ a Φ (k + 1)) (sigmaDiskAdjunctionCWComplex_map_inl (n k)
    ((stage s₀ a Φ k).nextAttach (a k)) ((stage s₀ a Φ k).nextAttach_mem (a k)) m
      (stageCWCellEquiv s₀ a Φ k m j) x)).trans
      (ιL_incl_apply s₀ a Φ k _)

/-- The cells of a stage which do not come from the previous stage are the attached cells. -/
def newCellEquiv (k m : ℕ) :
    {c : (stageCW s₀ a Φ (k + 1)).cell m // c ∉ range (cellIncl s₀ a Φ k m)} ≃
      {i : ι k // n k i = m} :=
  letI := sigmaDiskRelCWComplex (n k)
  let E := stageCWCellEquiv s₀ a Φ k m
  let e := (stageCWCellEquiv s₀ a Φ (k + 1) m).trans
    (sigmaDiskAdjunctionCWComplexCellEquiv (n k) ((stage s₀ a Φ k).nextAttach (a k))
      ((stage s₀ a Φ k).nextAttach_mem (a k)) m)
  have he (j : (stageCW s₀ a Φ k).cell m) : cellIncl s₀ a Φ k m j = e.symm (.inl (E j)) := rfl
  (Equiv.subtypeEquiv e fun c ↦ by
    rcases h : e c with j | i
    · simp only [Sum.isRight_inl, Bool.false_eq_true, iff_false, not_not]
      exact ⟨E.symm j, by rw [he, E.apply_symm_apply, e.symm_apply_eq, h]⟩
    · simp only [Sum.isRight_inr, iff_true]
      rintro ⟨j, rfl⟩
      rw [he, e.apply_symm_apply] at h
      cases h).trans Equiv.sumIsRight

theorem isClosed_of_forall_isClosed_inter (A : Set (L s₀ a Φ))
    (hA : ∀ k, IsClosed (A ∩ range (ιL s₀ a Φ k))) : IsClosed A := by
  rw [_root_.TopCat.isClosed_iff_of_isColimit _ (colimit.isColimit _)]
  intro k
  have h : ιL s₀ a Φ k ⁻¹' A = ιL s₀ a Φ k ⁻¹' (A ∩ range (ιL s₀ a Φ k)) := by
    ext w
    simp
  exact h ▸ (hA k).preimage (ιL s₀ a Φ k).hom.continuous

theorem iUnion_range_ιL : ⋃ k, range (ιL s₀ a Φ k) = univ :=
  eq_univ_of_forall fun y ↦ by
    obtain ⟨k, w, hw⟩ := exists_ιL_eq s₀ a Φ y
    exact mem_iUnion.2 ⟨k, w, hw⟩

/-- The CW structure on the colimit: the union of the tower of the stages. -/
@[instance_reducible]
def unionCW : CWComplex (⋃ k, range (ιL s₀ a Φ k)) :=
  letI := stageCW s₀ a Φ
  cwSubcomplexTowerUnion (ι := cellIncl s₀ a Φ) (map_cellIncl s₀ a Φ)
    fun A _ hA ↦ isClosed_of_forall_isClosed_inter s₀ a Φ A hA

/-- The cells of the colimit are the cells of the first stage and the attached cells. -/
def unionCWCellEquiv (m : ℕ) :
    (unionCW s₀ a Φ).cell m ≃ (s₀.cw.cell m ⊕ Σ k, {i : ι k // n k i = m}) :=
  letI := stageCW s₀ a Φ
  (cwSubcomplexTowerUnionCellEquiv (ι := cellIncl s₀ a Φ) (map_cellIncl s₀ a Φ)
    (fun A _ hA ↦ isClosed_of_forall_isClosed_inter s₀ a Φ A hA) m).trans <|
  (Equiv.sigmaNatSucc _).trans <| Equiv.sumCongr
    ((Equiv.subtypeUnivEquiv fun i ↦ isNewTowerCell_zero (cellIncl s₀ a Φ) i).trans
      (stageCWCellEquiv s₀ a Φ 0 m))
    (Equiv.sigmaCongrRight fun k ↦
      (Equiv.subtypeEquivRight fun i ↦ isNewTowerCell_succ_iff (cellIncl s₀ a Φ) i).trans
        (newCellEquiv s₀ a Φ k m))

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
  let A (k : ℕ) : Set (L s₀ a Φ) := range (ιL s₀ a Φ k)
  have hA : Monotone A := monotone_nat_of_le_succ fun k ↦ by
    rintro _ ⟨w, rfl⟩
    exact ⟨incl s₀ a Φ k w, ιL_incl_apply s₀ a Φ k w⟩
  have hAc : IsCoherentWith (range A) := IsCoherentWith.of_isClosed fun t ht ↦
    isClosed_of_forall_isClosed_inter s₀ a Φ t fun k ↦ by
      rw [inter_comm, ← Subtype.image_preimage_coe]
      exact (isClosedEmbedding_ιL s₀ a Φ k).isClosed_range.isClosedMap_subtype_val _
        (ht _ (mem_range_self k))
  -- Each stage is homeomorphic to its image in the colimit.
  let e (k : ℕ) : (stage s₀ a Φ k).W ≃ₜ A k :=
    (isClosedEmbedding_ιL s₀ a Φ k).isEmbedding.toHomeomorph
  have hAH (k : ℕ) : HasHomotopyExtensionProperty ((↑) ⁻¹' A k : Set (A (k + 1))) := by
    convert (hasHomotopyExtensionProperty_range_incl s₀ a Φ k).image (e (k + 1)) using 1
    ext ⟨_, w, rfl⟩
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨incl s₀ a Φ k v, ⟨v, rfl⟩, Subtype.ext ?_⟩
      exact (ιL_incl_apply s₀ a Φ k v).trans hv
    · rintro ⟨_, ⟨v, rfl⟩, hv⟩
      exact ⟨v, (ιL_incl_apply s₀ a Φ k v).symm.trans (congrArg Subtype.val hv)⟩
  obtain ⟨h, -, -⟩ := exists_homotopyEquiv_of_isCoherentWith hA (monotone_Z a Φ hΦ)
    (iUnion_range_ιL s₀ a Φ) hZX hAc hZc hAH hZH (toX s₀ a Φ hΦ).hom
    (fun k ↦ (e k).symm.toHomotopyEquiv.trans (stage s₀ a Φ k).h) fun k ↦ by
      rintro ⟨_, w, rfl⟩
      have hw : (e k).symm ⟨ιL s₀ a Φ k w, w, rfl⟩ = w :=
        (isClosedEmbedding_ιL s₀ a Φ k).isEmbedding.toHomeomorph_symm_apply w
      -- Unfold the composite homotopy equivalence on the stage.
      change ((stage s₀ a Φ k).h ((e k).symm _) : X) = toX s₀ a Φ hΦ (ιL s₀ a Φ k w)
      rw [hw, toX_ιL]
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
  obtain ⟨cw, hcw⟩ := TowerModel.exists_cwComplex_univ (TowerModel.unionCW s₀ a Φ)
    (TowerModel.iUnion_range_ιL s₀ a Φ)
  obtain ⟨e⟩ := TowerModel.exists_homotopyEquiv s₀ a Φ hΦ hZX hZc hZH
  exact ⟨TowerModel.L s₀ a Φ, inferInstance, inferInstance, cw, ⟨e⟩,
    fun m ↦ ⟨(hcw m).some.trans (TowerModel.unionCWCellEquiv s₀ a Φ m)⟩⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import TauCeti.Topology.CWComplex.Classical.Copy
public import TauCeti.Topology.CWComplex.Classical.Image
public import TauCeti.Topology.CWComplex.Classical.TowerUnion
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.Category.TopCat.DisjointOpens
public import TauCeti.Topology.Homotopy.Extension.Tower

/-!
# The colimit of a tower of CW complexes

Let `W 0 → W 1 → W 2 → ⋯` be a sequence of CW complexes along closed embeddings
`j k : W k → W (k + 1)`, such that every cell of `W k` is a cell of `W (k + 1)` whose characteristic
map is that of `W k` followed by `j k`. The colimit of the sequence in `TopCat` is then a CW
complex whose `n`-cells are the `n`-cells of `W 0` together with, for each `k`, the `n`-cells of
`W (k + 1)` not coming from `W k`, with their characteristic maps
(`TauCeti.exists_cwComplex_of_isColimit`). Cells may be added in any order of dimensions, and no
separation axiom is needed.

If moreover the `W k` are Hausdorff and the images of the `j k` have the homotopy extension
property, the colimit is a model for any space exhausted compatibly by spaces of the homotopy
types of the `W k`. Let `Y` be the union of an increasing sequence of subsets `A 0 ⊆ A 1 ⊆ ⋯`,
each with the homotopy extension property in the next, carrying the topology coherent with them,
and let `h k : W k ≃ₕ A k` be homotopy equivalences commuting strictly with the inclusions. Then
`Y` is homotopy equivalent to the colimit, a Hausdorff CW complex containing every `W k` as a
closed subspace, by a homotopy equivalence restricting to `h k` on `W k`
(`TauCeti.exists_cwComplex_homotopyEquiv_of_tower`).

This is the last step of Milnor's construction of a CW model, with one cell for each critical
point, of a manifold exhausted by the regular sublevels `M_{a_k} = {f ≤ a_k}` of a proper Morse
function bounded below. The sublevels are linked by closed cofibrations
(`TauCeti.hasHomotopyExtensionProperty_range_sublevelInclusion`), the manifold carries the topology
coherent with them since the open sets `{f < a_k}` cover it (`Topology.IsCoherentWith.of_nhds`),
and a CW model of `M_{a_k}` extends across the band `f⁻¹[a_k, a_{k+1}]` to a CW model of
`M_{a_{k+1}}` with one new cell for each critical point in the band.

The proofs read everything inside the colimit `X`.

* Each `W k` embeds as a closed subspace of `X`, since the bonding maps are closed embeddings
  (`TauCeti.TopCat.isClosedEmbedding_ι_of_isColimit`), and its image carries the CW structure of
  `W k` (`Topology.IsClosedEmbedding.relCWComplex`), with characteristic maps normalized to depend
  only on their values (`Topology.CWComplex.copy`). The images then form a tower of CW complexes
  in `X`, whose union is a CW complex with the new cells of all stages
  (`TauCeti.cwSubcomplexTowerUnion`), because `X` carries the final topology of the stages.
* `X` is Hausdorff, since an embedding whose image has the homotopy extension property extends
  disjoint open sets (`TauCeti.TopCat.extendsDisjointOpens_of_hasHomotopyExtensionProperty` and
  `TauCeti.TopCat.t2Space_of_isColimit_nat`).
* The maps `h k` induce a map `X → Y` which is a homotopy equivalence on every stage, hence a
  homotopy equivalence (`TauCeti.exists_homotopyEquiv_of_isCoherentWith`).

## Main results

* `TauCeti.exists_cwComplex_of_isColimit`: the colimit of a tower of CW complexes along closed
  embeddings is a CW complex whose cells are the new cells of the stages.
* `TauCeti.exists_cwComplex_homotopyEquiv_of_tower`: a space exhausted by a tower of cofibrations
  with compatible CW models is homotopy equivalent to the colimit of the models.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5, whose proof builds a CW model of a manifold one critical level at a time and
  passes to the union of the stages.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 and the Appendix, for CW complexes as unions of their stages with the weak topology.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex
open scoped ContinuousMap

universe u

namespace TauCeti

section ColimitMaps

variable {W : ℕ → Type u} [∀ k, TopologicalSpace (W k)] (j : ∀ k, C(W k, W (k + 1)))
  {c : Cocone (Functor.ofSequence fun k ↦ _root_.TopCat.ofHom (j k))}

/-- The maps to a colimit of a sequence are compatible with the bonding maps. -/
private theorem ι_app_succ_apply (k : ℕ) (w : W k) : c.ι.app (k + 1) (j k w) = c.ι.app k w := by
  have := ConcreteCategory.congr_hom (c.w (homOfLE k.le_succ)) w
  rwa [Functor.ofSequence_map_homOfLE_succ] at this

/-- The maps to a colimit of a sequence along closed embeddings are closed embeddings. -/
private theorem isClosedEmbedding_ι_app (hj : ∀ k, IsClosedEmbedding (j k)) (hc : IsColimit c)
    (k : ℕ) : IsClosedEmbedding (c.ι.app k) :=
  TopCat.isClosedEmbedding_ι_of_isColimit (fun _ _ ↦
    TopCat.isClosedEmbedding_map_of_isWellOrderContinuous _ fun n _ ↦ by
      have hF : (Functor.ofSequence fun k ↦ _root_.TopCat.ofHom (j k)).map
          (homOfLE (Order.le_succ n)) = _root_.TopCat.ofHom (j n) :=
        Functor.ofSequence_map_homOfLE_succ _ n
      rw [hF]
      exact hj n) hc k

end ColimitMaps

variable {W : ℕ → Type u} [∀ k, TopologicalSpace (W k)] [∀ k, CWComplex (univ : Set (W k))]

/-- **The colimit of a tower of CW complexes.** Let `W 0 → W 1 → ⋯` be CW complexes along closed
embeddings `j k`, with maps `ι k n` labelling the `n`-cells of `W k` among those of `W (k + 1)`,
whose characteristic maps are those of `W k` followed by `j k`. Then the colimit of the sequence in
`TopCat` is a CW complex whose `n`-cells are the `n`-cells of `W 0` together with the `n`-cells of
the stages `W (k + 1)` outside the range of `ι k n`, with their characteristic maps followed by the
maps to the colimit. -/
theorem exists_cwComplex_of_isColimit (j : ∀ k, C(W k, W (k + 1)))
    (hj : ∀ k, IsClosedEmbedding (j k))
    (ι : ∀ k n, cell (univ : Set (W k)) n → cell (univ : Set (W (k + 1))) n)
    (hι : ∀ k n i x, map n (ι k n i) x = j k (map n i x))
    {c : Cocone (Functor.ofSequence fun k ↦ _root_.TopCat.ofHom (j k))} (hc : IsColimit c) :
    ∃ _ : CWComplex (univ : Set c.pt), ∀ n,
      ∃ e : cell (univ : Set c.pt) n ≃ cell (univ : Set (W 0)) n ⊕ (Σ k, ↥(range (ι k n))ᶜ),
        (∀ i x, map n (e.symm (.inl i)) x = c.ι.app 0 (map n i x)) ∧
        ∀ k i x, map n (e.symm (.inr ⟨k, i⟩)) x = c.ι.app (k + 1) (map n i.1 x) := by
  classical
  let e (k : ℕ) : C(W k, c.pt) := ConcreteCategory.hom (c.ι.app k)
  have hej (k : ℕ) (w : W k) : e (k + 1) (j k w) = e k w := ι_app_succ_apply j k w
  have he (k : ℕ) : IsClosedEmbedding (e k) := isClosedEmbedding_ι_app j hj hc k
  -- The images `V k` of the stages exhaust the colimit, which carries the topology coherent with
  -- them.
  let V (k : ℕ) : Set c.pt := range (e k)
  have hVX : ⋃ k, V k = univ := TopCat.iUnion_range_ι_of_isColimit hc
  have hVc : IsCoherentWith (range V) := TopCat.isCoherentWith_range_ι_of_isColimit hc
  -- The CW structure of `W k` read on `V k`, with characteristic maps `InjOn.toPartialEquiv` of
  -- their values, so that the cells of `V k` reappear in `V (k + 1)` with the same characteristic
  -- maps.
  have hinj (k n : ℕ) (i : cell (univ : Set (W k)) n) : InjOn (e k ∘ map n i) (ball 0 1) :=
    (he k).injective.comp_injOn (source_eq n i ▸ (map n i).injOn)
  let hVim (k : ℕ) : CWComplex (V k) :=
    letI := (he k).relCWComplex (C := (univ : Set (W k))) (D := ∅) (C' := V k) (D' := ∅)
      image_univ (image_empty _)
    RelCWComplex.toCWComplex (V k)
  let φ (k n : ℕ) (i : cell (V k) n) : PartialEquiv (Fin n → ℝ) c.pt :=
    (hinj k n ((he k).relCWComplexCellEquiv image_univ (image_empty _) n i)).toPartialEquiv _ _
  have hφ (k n : ℕ) (i : cell (V k) n) : EqOn (φ k n i) (map n i) (closedBall 0 1) :=
    fun x _ ↦ by simp [φ]
  let hVcw (k : ℕ) : CWComplex (V k) :=
    @CWComplex.copy _ _ (V k) (hVim k) (V k) rfl (φ k) (fun _ _ ↦ rfl) (hφ k)
  -- The cells of `V k`, now for the copied structure, are those of `W k`.
  let cellEq (k n : ℕ) : cell (V k) n ≃ cell (univ : Set (W k)) n :=
    (@CWComplex.copyCellEquiv _ _ (V k) (hVim k) (V k) rfl (φ k) (fun _ _ ↦ rfl) (hφ k) n).trans
      ((he k).relCWComplexCellEquiv image_univ (image_empty _) n)
  have hmap (k n : ℕ) (i : cell (V k) n) :
      map n i = (hinj k n (cellEq k n i)).toPartialEquiv _ _ :=
    @CWComplex.map_copy _ _ (V k) (hVim k) (V k) rfl (φ k) (fun _ _ ↦ rfl) (hφ k) n i
  let ι' (k n : ℕ) (i : cell (V k) n) : cell (V (k + 1)) n :=
    (cellEq (k + 1) n).symm (ι k n (cellEq k n i))
  have hι' (k n : ℕ) (i : cell (V k) n) : map n (ι' k n i) = map n i := by
    rw [hmap, hmap]
    congr 1
    funext x
    simp [ι', hι, hej]
  -- The union of the tower `V`, which is the whole colimit.
  let hU : CWComplex (⋃ k, V k) := cwSubcomplexTowerUnion hι' fun B _ hB ↦
    hVc.isClosed_of_forall_isClosed_inter (by rintro _ ⟨k, rfl⟩; exact hB k)
  let hX : CWComplex (univ : Set c.pt) :=
    CWComplex.copy univ hVX.symm (fun n i ↦ map n i) (fun n i ↦ source_eq n i)
      fun _ _ ↦ eqOn_refl _ _
  -- The new cells of the stages.
  have hnew (k n : ℕ) (i : cell (V (k + 1)) n) :
      IsNewTowerCell ι' (k + 1) i ↔ cellEq (k + 1) n i ∈ (range (ι k n))ᶜ := by
    rw [isNewTowerCell_succ_iff, mem_compl_iff, not_iff_not]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨cellEq k n a, by simp [ι']⟩
    · rintro ⟨b, hb⟩
      exact ⟨(cellEq k n).symm b, by simp [ι', hb]⟩
  let cellNew (n : ℕ) :
      TowerNewCell ι' n ≃ cell (univ : Set (W 0)) n ⊕ (Σ k, ↥(range (ι k n))ᶜ) :=
    (Equiv.sigmaNatSucc fun k ↦ {i : cell (V k) n // IsNewTowerCell ι' k i}).trans
      (Equiv.sumCongr ((Equiv.subtypeUnivEquiv (isNewTowerCell_zero ι')).trans (cellEq 0 n))
        (Equiv.sigmaCongrRight fun k ↦ (cellEq (k + 1) n).subtypeEquiv (hnew k n)))
  let cellX (n : ℕ) :
      cell (univ : Set c.pt) n ≃ cell (univ : Set (W 0)) n ⊕ (Σ k, ↥(range (ι k n))ᶜ) :=
    ((CWComplex.copyCellEquiv univ hVX.symm _ _ _ n).trans
      (cwSubcomplexTowerUnionCellEquiv hι' _ n)).trans (cellNew n)
  -- The characteristic map of a cell of the colimit is that of the new cell it comes from.
  have hmapX (n : ℕ) (c' : TowerNewCell ι' n) (x : Fin n → ℝ) :
      map n ((cellX n).symm (cellNew n c')) x = e c'.1 (map n (cellEq c'.1 n c'.2.1) x) := by
    have hc : (cellX n).symm (cellNew n c') = (CWComplex.copyCellEquiv univ hVX.symm _ _ _ n).symm
        ((cwSubcomplexTowerUnionCellEquiv hι' _ n).symm c') := by
      simp [cellX]
    simp only [hc, CWComplex.map_copy, Equiv.apply_symm_apply,
      map_cwSubcomplexTowerUnionCellEquiv_symm]
    simp [hmap]
  refine ⟨hX, fun n ↦ ⟨cellX n, fun i x ↦ ?_, fun k i x ↦ ?_⟩⟩
  · have hc : cellNew n ⟨0, (cellEq 0 n).symm i, isNewTowerCell_zero ι' _⟩ = .inl i := by
      simp [cellNew, Equiv.sigmaNatSucc]
    rw [← hc, hmapX]
    dsimp only
    -- What remains is the definition of `e` as the maps of the colimit cocone.
    rw [Equiv.apply_symm_apply]
    rfl
  · have hi : IsNewTowerCell ι' (k + 1) ((cellEq (k + 1) n).symm i.1) := (hnew k n _).2 (by simp)
    have hc : cellNew n ⟨k + 1, (cellEq (k + 1) n).symm i.1, hi⟩ = .inr ⟨k, i⟩ := by
      simp [cellNew, Equiv.sigmaNatSucc]
    rw [← hc, hmapX]
    dsimp only
    -- What remains is the definition of `e` as the maps of the colimit cocone.
    rw [Equiv.apply_symm_apply]
    rfl

variable [∀ k, T2Space (W k)] {Y : Type u} [TopologicalSpace Y] {A : ℕ → Set Y}

/-- **The CW model of a tower.** Let `Y` be the union of an increasing sequence of subsets `A k`,
each with the homotopy extension property in the next, carrying the topology coherent with them.
Let `W 0 → W 1 → ⋯` be Hausdorff CW complexes along closed embeddings `j k` whose images have the
homotopy extension property, with maps `ι k n` labelling the `n`-cells of `W k` among those of
`W (k + 1)`, whose characteristic maps are those of `W k` followed by `j k`. Let
`h k : W k ≃ₕ A k` be homotopy equivalences commuting with the inclusions.

Then there are a Hausdorff CW complex `X` with closed embeddings `e k : W k → X` compatible with
the `j k`, and a homotopy equivalence `H : X ≃ₕ Y` with `H ∘ e k = h k`, such that for every `n`
the `n`-cells of `X` are the `n`-cells of `W 0` together with the `n`-cells of the stages
`W (k + 1)` outside the range of `ι k n`, with their characteristic maps followed by `e`. -/
theorem exists_cwComplex_homotopyEquiv_of_tower (hA : Monotone A) (hAY : ⋃ k, A k = univ)
    (hAc : IsCoherentWith (range A))
    (hAH : ∀ k, HasHomotopyExtensionProperty ((↑) ⁻¹' A k : Set (A (k + 1))))
    (j : ∀ k, C(W k, W (k + 1))) (hj : ∀ k, IsClosedEmbedding (j k))
    (hjH : ∀ k, HasHomotopyExtensionProperty (range (j k)))
    (ι : ∀ k n, cell (univ : Set (W k)) n → cell (univ : Set (W (k + 1))) n)
    (hι : ∀ k n i x, map n (ι k n i) x = j k (map n i x)) (h : ∀ k, W k ≃ₕ A k)
    (hh : ∀ k w, (h (k + 1) (j k w) : Y) = h k w) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X))
      (e : ∀ k, C(W k, X)) (H : X ≃ₕ Y),
      (∀ k, IsClosedEmbedding (e k)) ∧ (∀ k w, e (k + 1) (j k w) = e k w) ∧
      (∀ k w, (H (e k w) : Y) = h k w) ∧
      ∀ n, ∃ c : cell (univ : Set X) n ≃ cell (univ : Set (W 0)) n ⊕ (Σ k, ↥(range (ι k n))ᶜ),
        (∀ i x, map n (c.symm (.inl i)) x = e 0 (map n i x)) ∧
        ∀ k i x, map n (c.symm (.inr ⟨k, i⟩)) x = e (k + 1) (map n i.1 x) := by
  -- `X` is the colimit of the sequence of the `W k` in `TopCat`, with the maps `e k : W k → X`.
  let F : ℕ ⥤ _root_.TopCat.{u} := Functor.ofSequence fun k ↦ _root_.TopCat.ofHom (j k)
  have hFmap (k : ℕ) : F.map (homOfLE k.le_succ) = _root_.TopCat.ofHom (j k) :=
    Functor.ofSequence_map_homOfLE_succ _ k
  have : ∀ k, T2Space (F.obj k) := fun k ↦ (inferInstance : T2Space (W k))
  let c := colimit.cocone F
  have hc : IsColimit c := colimit.isColimit F
  obtain ⟨hX, hcell⟩ := exists_cwComplex_of_isColimit j hj ι hι hc
  let e (k : ℕ) : C(W k, c.pt) := (c.ι.app k).hom
  have hej (k : ℕ) (w : W k) : e (k + 1) (j k w) = e k w := ι_app_succ_apply j k w
  have he (k : ℕ) : IsClosedEmbedding (e k) := isClosedEmbedding_ι_app j hj hc k
  have hT2 : T2Space c.pt := TopCat.t2Space_of_isColimit_nat (fun k ↦ by
    rw [hFmap]
    exact TopCat.extendsDisjointOpens_of_hasHomotopyExtensionProperty _ (hj k).isInducing (hjH k))
    hc
  -- The images `V k` of the stages form an increasing sequence exhausting `X`, which carries the
  -- topology coherent with it.
  let V (k : ℕ) : Set c.pt := range (e k)
  have hV : Monotone V := monotone_nat_of_le_succ fun k ↦ by
    rintro _ ⟨w, rfl⟩
    exact ⟨j k w, hej k w⟩
  have hVX : ⋃ k, V k = univ := TopCat.iUnion_range_ι_of_isColimit hc
  have hVc : IsCoherentWith (range V) := TopCat.isCoherentWith_range_ι_of_isColimit hc
  -- Each stage `W k` is homeomorphic to its image, and `V k` is a cofibration in `V (k + 1)`.
  let Φ (k : ℕ) : W k ≃ₜ V k := (he k).isEmbedding.toHomeomorph
  have hVH (k : ℕ) : HasHomotopyExtensionProperty ((↑) ⁻¹' V k : Set (V (k + 1))) := by
    convert (hjH k).image (Φ (k + 1)) using 1
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨j k w, ⟨w, rfl⟩, Subtype.ext ((hej k w).trans hw)⟩
    · rintro ⟨_, ⟨w, rfl⟩, hw⟩
      exact ⟨w, (hej k w).symm.trans (congrArg Subtype.val hw)⟩
  -- The map `X → Y` induced by the `h k`, which restricts to a homotopy equivalence on each stage.
  let s : Cocone F :=
    { pt := _root_.TopCat.of Y
      ι := NatTrans.ofSequence
        (fun k ↦ _root_.TopCat.ofHom (ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩
          (h k).toFun))
        fun k ↦ by
          ext w
          rw [hFmap]
          exact hh k w }
  let g : C(c.pt, Y) := (hc.desc s).hom
  have hg (k : ℕ) (w : W k) : g (e k w) = h k w := ConcreteCategory.congr_hom (hc.fac s k) w
  let eV (k : ℕ) : V k ≃ₕ A k := (Φ k).symm.toHomotopyEquiv.trans (h k)
  have heV (k : ℕ) (a : V k) : (eV k a : Y) = g a := by
    obtain ⟨w, rfl⟩ := (Φ k).surjective a
    -- By definition, `eV k` applies `(Φ k).symm` and then `h k`.
    change ((h k) ((Φ k).symm (Φ k w)) : Y) = g (Φ k w)
    rw [Homeomorph.symm_apply_apply]
    exact (hg k w).symm
  obtain ⟨H, hH, -⟩ :=
    exists_homotopyEquiv_of_isCoherentWith hV hA hVX hAY hVc hAc hVH hAH g eV heV
  exact ⟨c.pt, inferInstance, hT2, hX, e, H, he, hej, fun k w ↦ by rw [hH, hg], hcell⟩

end TauCeti

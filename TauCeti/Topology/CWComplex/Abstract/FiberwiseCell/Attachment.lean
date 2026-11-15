/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk.LinearIsometry
public import TauCeti.AlgebraicTopology.Disk.Reattachment
public import TauCeti.Topology.Category.TopCat.Pushout
public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Basic
import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Topology
import TauCeti.Topology.Category.TopCat.OpenEmbedding
import TauCeti.Topology.Homotopy.Homotopic.Rel

/-!
# Attaching families of cells over a parameter space

Let `A` be a subspace of a space `Y`, and let `α i : P × ∂D^{k i} → A` be continuous families of
attaching maps, parametrized by a space `P`. Attaching, over each `p ∈ P`, one disc `D^{k i}` along
each `α i p` gives the *fiberwise adjunction space*

`(P × A) ∪_α ⨆ᵢ (P × D^{k i})`,

the pushout in `TopCat` of `(p, s) ↦ (p, α i (p, s))` along the inclusions
`P × ∂D^{k i} → P × D^{k i}` (`TauCeti.fiberwiseCellAttachment`). It lies over `P`
(`TauCeti.fiberwiseCellAttachmentProj`), and its points over `p` are those of the attachment
`A ∪_{α p} ⨆ᵢ D^{k i}`.
Characteristic families `χ i : P × D^{k i} → Y` restricting to `α i` on the boundary spheres induce
the comparison map `(P × A) ∪_α ⨆ᵢ (P × D^{k i}) → P × Y` over `P`
(`TauCeti.fiberwiseCellComparison`). These are the families of cell attachments met when the charts
of a Morse function at a critical level vary continuously with a parameter.

Two families `χ₀` and `χ₁` of characteristic maps are compared as in Milnor's Lemma 3.6, now over
`P`. Given self-maps `h i` of `P × D^{k i}` over `P` preserving `P × ∂D^{k i}`, and homotopies
`K i : χ₁ i ≃ χ₀ i ∘ (p, h i)` keeping `P × ∂D^{k i}` in `A`, the *fiberwise reattachment map*
(`TauCeti.fiberwiseCellReattachment`)

`E : (P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i}) → (P × A) ∪_{α₀} ⨆ᵢ (P × D^{k i})`

is the identity on `P × A`, sends `(p, x)` in the `i`-th disc with `‖x‖ ≤ 1/2` to the point
`(p, h i (p, 2x))` of the `i`-th disc, and sends `(p, x)` with `1/2 ≤ ‖x‖` to the point
`(p, K i (2 - 2‖x‖, (p, x/‖x‖)))` of `P × A`. It lies over `P`, and `Φ₀ ∘ E` is homotopic to `Φ₁`
relative to `P × A` through maps over `P` (`TauCeti.fiberwiseCellReattachmentHomotopy`), for the
comparison maps `Φ₀` and `Φ₁`. If `Φ₀` has a left inverse `g₀` over `P`, then `E` is homotopic to
`g₀ ∘ Φ₁` relative to `P × A` over `P`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_of_leftInverse`). Hence the relative
homotopy class of `E` over `P` does not depend on the chosen `h` and `K`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_fiberwiseCellReattachment`), and
reattachment maps compose up to homotopy relative to `P × A` over `P`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment`).

When the self-maps `h i (p, ·)` are linear isometries `g i p`, no left inverse is needed to invert
`E`. The reverse homotopies `K' i (t, (p, w)) = K i (1 - t, (p, (g i p)⁻¹ w))` are homotopies
`χ₀ i ≃ χ₁ i ∘ (g i p)⁻¹`, and the reattachment map `E'` along them is a homotopy inverse of `E`
relative to `P × A`, by homotopies over `P`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment_id`). On
each cell, `E' ∘ E` is the cell shrunk to the disc of radius `1/4`, followed by a collar along which
the boundary homotopy is run forwards and then backwards; the radial homotopy
`TauCeti.TopCat.reattachmentFoldPath` folds the collar away.
So `E` is a fibre homotopy equivalence over `P`
(`TauCeti.fiberwiseCellReattachmentFiberHomotopyEquiv`). In particular, two families of cell
attachments whose characteristic families are homotopic as maps of pairs up to a continuous family
of linear isometries of the discs are fibre homotopy equivalent relative to `P × A`, compatibly
with their comparison maps
(`TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellAttachment_of_homotopy`).

All of these constructions are natural in the parameter space: along a continuous map
`g : P' → P`, the attachments of the restricted families map to the original ones over `g`
(`TauCeti.fiberwiseCellAttachmentMap`), compatibly with the comparison maps and with the
reattachment maps (`TauCeti.fiberwiseCellReattachment_comp_fiberwiseCellAttachmentMap`) and with
the homotopies (`TauCeti.fiberwiseCellReattachmentHomotopy_fiberwiseCellAttachmentMap`). In
particular, for the inclusion of a subspace `P' ⊆ P`, restricting the data to `P'` gives the same
construction over `P'`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 3.6 and Remark 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits Set Metric unitInterval

universe u

namespace TauCeti

variable {P Y : Type u} [TopologicalSpace P] [TopologicalSpace Y] {A : Set Y} {ι : Type u}
  {k : ι → ℕ}

section Attachment

/-- The coproduct of the maps `(p, s) ↦ (p, α i (p, s))` from `P × ∂D^{k i}` to `P × A`. -/
def fiberwiseAttachingMap (α : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A)) :
    (∐ fun i ↦ TopCat.of (P × TopCat.diskBoundary.{u} (k i))) ⟶ TopCat.of (P × A) :=
  Sigma.desc fun i ↦ TopCat.ofHom (ContinuousMap.fst.prodMk (α i))

variable (P k) in
/-- The coproduct of the inclusions `P × ∂D^{k i} → P × D^{k i}`. -/
def fiberwiseBoundaryInclusion :
    (∐ fun i ↦ TopCat.of (P × TopCat.diskBoundary.{u} (k i))) ⟶
      ∐ fun i ↦ TopCat.of (P × TopCat.disk.{u} (k i)) :=
  Limits.Sigma.map fun i ↦
    TopCat.ofHom ((ContinuousMap.id P).prodMap (TopCat.diskBoundaryInclusion (k i)).hom)

/-- The **fiberwise adjunction space** `(P × A) ∪_α ⨆ᵢ (P × D^{k i})` of a family of attaching maps
`α i : P × ∂D^{k i} → A`: over each `p`, one disc `D^{k i}` is attached to `A` along each
`α i (p, ·)`. It is the pushout in `TopCat` of `TauCeti.fiberwiseAttachingMap α` along
`TauCeti.fiberwiseBoundaryInclusion` (`TauCeti.isPushout_fiberwiseCellAttachment`). -/
def fiberwiseCellAttachment (α : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A)) : TopCat.{u} :=
  pushout (fiberwiseAttachingMap α) (fiberwiseBoundaryInclusion P k)

/-- The inclusion of `P × A` into the fiberwise adjunction space. -/
def fiberwiseCellAttachmentIncl (α : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A)) :
    TopCat.of (P × A) ⟶ fiberwiseCellAttachment α :=
  pushout.inl _ _

/-- The family over `P` of characteristic maps `P × D^{k i} → (P × A) ∪_α ⨆ᵢ (P × D^{k i})` of the
cells attached along `α i`. -/
def fiberwiseCellAttachmentCell (α : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A)) (i : ι) :
    TopCat.of (P × TopCat.disk.{u} (k i)) ⟶ fiberwiseCellAttachment α :=
  Sigma.ι (fun i ↦ TopCat.of (P × TopCat.disk.{u} (k i))) i ≫ pushout.inr _ _

variable (α : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))

/-- The fiberwise adjunction space is the pushout of the attaching maps along the boundary
inclusions, with the inclusion of `P × A` and the characteristic maps of the cells as its legs. -/
theorem isPushout_fiberwiseCellAttachment :
    IsPushout (fiberwiseAttachingMap α) (fiberwiseBoundaryInclusion P k)
      (fiberwiseCellAttachmentIncl α) (Sigma.desc (fiberwiseCellAttachmentCell α)) := by
  have h : Sigma.desc (fiberwiseCellAttachmentCell α) =
      (pushout.inr _ _ : _ ⟶ fiberwiseCellAttachment α) :=
    Sigma.hom_ext _ _ fun i ↦ by rw [Sigma.ι_comp_desc, fiberwiseCellAttachmentCell]
  rw [h]
  exact IsPushout.of_hasPushout _ _

/-- On the `i`-th summand, the coproduct of the attaching maps is `(p, s) ↦ (p, α i (p, s))`. -/
@[simp]
theorem fiberwiseAttachingMap_ι (i : ι) (x : P × TopCat.diskBoundary.{u} (k i)) :
    fiberwiseAttachingMap α
        (Sigma.ι (fun i ↦ TopCat.of (P × TopCat.diskBoundary.{u} (k i))) i x) =
      (x.1, α i x) := by
  rw [← ConcreteCategory.comp_apply, fiberwiseAttachingMap, Sigma.ι_comp_desc]
  rfl

/-- On the `i`-th summand, the coproduct of the boundary inclusions is the inclusion
`P × ∂D^{k i} → P × D^{k i}`. -/
@[simp]
theorem fiberwiseBoundaryInclusion_ι (i : ι) (x : P × TopCat.diskBoundary.{u} (k i)) :
    fiberwiseBoundaryInclusion P k
        (Sigma.ι (fun i ↦ TopCat.of (P × TopCat.diskBoundary.{u} (k i))) i x) =
      Sigma.ι (fun i ↦ TopCat.of (P × TopCat.disk.{u} (k i))) i
        (x.1, TopCat.diskBoundaryInclusion (k i) x.2) := by
  rw [fiberwiseBoundaryInclusion, Sigma.ι_map_apply]
  rfl

/-- On the boundary spheres, the characteristic maps of the cells are the attaching maps followed by
the inclusion of `P × A`. -/
theorem fiberwiseCellAttachmentCell_diskBoundaryInclusion (i : ι) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    fiberwiseCellAttachmentCell α i (p, TopCat.diskBoundaryInclusion (k i) s) =
      fiberwiseCellAttachmentIncl α (p, α i (p, s)) := by
  have h := (isPushout_fiberwiseCellAttachment α).w_apply
    (Sigma.ι (fun i ↦ TopCat.of (P × TopCat.diskBoundary.{u} (k i))) i (p, s))
  rw [fiberwiseAttachingMap_ι, fiberwiseBoundaryInclusion_ι, ← ConcreteCategory.comp_apply,
    Sigma.ι_comp_desc] at h
  exact h.symm

/-- A map on `P × A` and maps on the families of discs which agree along the attaching maps induce
a map out of the fiberwise adjunction space. -/
def fiberwiseCellAttachmentDesc {Z : TopCat.{u}} (g : TopCat.of (P × A) ⟶ Z)
    (G : ∀ i, TopCat.of (P × TopCat.disk.{u} (k i)) ⟶ Z)
    (hG : ∀ i p s, G i (p, TopCat.diskBoundaryInclusion (k i) s) = g (p, α i (p, s))) :
    fiberwiseCellAttachment α ⟶ Z :=
  (isPushout_fiberwiseCellAttachment α).desc g (Sigma.desc G) (Sigma.hom_ext _ _ fun i ↦ by
    ext ⟨p, s⟩
    simp only [ConcreteCategory.comp_apply]
    rw [fiberwiseAttachingMap_ι, fiberwiseBoundaryInclusion_ι, ← ConcreteCategory.comp_apply,
      Sigma.ι_comp_desc]
    exact (hG i p s).symm)

section Desc

variable {Z : TopCat.{u}} (g : TopCat.of (P × A) ⟶ Z)
  (G : ∀ i, TopCat.of (P × TopCat.disk.{u} (k i)) ⟶ Z)
  (hG : ∀ i p s, G i (p, TopCat.diskBoundaryInclusion (k i) s) = g (p, α i (p, s)))

@[reassoc (attr := simp)]
theorem fiberwiseCellAttachmentIncl_desc :
    fiberwiseCellAttachmentIncl α ≫ fiberwiseCellAttachmentDesc α g G hG = g :=
  IsPushout.inl_desc _ _ _ _

@[reassoc (attr := simp)]
theorem fiberwiseCellAttachmentCell_desc (i : ι) :
    fiberwiseCellAttachmentCell α i ≫ fiberwiseCellAttachmentDesc α g G hG = G i := by
  rw [fiberwiseCellAttachmentDesc, ← Sigma.ι_comp_desc (fiberwiseCellAttachmentCell α) i,
    Category.assoc, IsPushout.inr_desc, Sigma.ι_comp_desc]

@[simp]
theorem fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentIncl (x : P × A) :
    fiberwiseCellAttachmentDesc α g G hG (fiberwiseCellAttachmentIncl α x) = g x :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentIncl_desc α g G hG) x

@[simp]
theorem fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentCell (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseCellAttachmentDesc α g G hG (fiberwiseCellAttachmentCell α i x) = G i x :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentCell_desc α g G hG i) x

end Desc

/-- Continuous maps out of the fiberwise adjunction space agree as soon as they agree on `P × A`
and on the cells. -/
theorem fiberwiseCellAttachment_continuousMap_ext {W : Type u} [TopologicalSpace W]
    {g g' : C(fiberwiseCellAttachment α, W)}
    (h₀ : ∀ x, g (fiberwiseCellAttachmentIncl α x) = g' (fiberwiseCellAttachmentIncl α x))
    (h : ∀ i x, g (fiberwiseCellAttachmentCell α i x) = g' (fiberwiseCellAttachmentCell α i x)) :
    g = g' := by
  refine (isPushout_fiberwiseCellAttachment α).continuousMap_ext h₀ fun z ↦ ?_
  obtain ⟨i, x, rfl⟩ := TopCat.exists_sigma_ι_eq _ z
  rw [← ConcreteCategory.comp_apply, Sigma.ι_comp_desc]
  exact h i x

/-- Maps out of the fiberwise adjunction space are determined by their restrictions to `P × A` and
to the cells. -/
theorem fiberwiseCellAttachment_hom_ext {Z : TopCat.{u}} {g g' : fiberwiseCellAttachment α ⟶ Z}
    (h₀ : ∀ x, g (fiberwiseCellAttachmentIncl α x) = g' (fiberwiseCellAttachmentIncl α x))
    (h : ∀ i x, g (fiberwiseCellAttachmentCell α i x) = g' (fiberwiseCellAttachmentCell α i x)) :
    g = g' :=
  TopCat.hom_ext (fiberwiseCellAttachment_continuousMap_ext α h₀ h)

/-- Every point of the fiberwise adjunction space lies in `P × A` or in a cell. -/
theorem range_fiberwiseCellAttachmentIncl_union_iUnion_range_fiberwiseCellAttachmentCell :
    range (fiberwiseCellAttachmentIncl α) ∪ ⋃ i, range (fiberwiseCellAttachmentCell α i) =
      univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  by_cases hy : y ∈ range (fiberwiseCellAttachmentIncl α)
  · exact Or.inl hy
  rw [← mem_compl_iff,
    ← TopCat.image_compl_range_of_isPushout (isPushout_fiberwiseCellAttachment α)] at hy
  obtain ⟨z, -, rfl⟩ := hy
  obtain ⟨i, x, rfl⟩ := TopCat.exists_sigma_ι_eq _ z
  refine Or.inr (mem_iUnion.2 ⟨i, x, ?_⟩)
  rw [← ConcreteCategory.comp_apply, Sigma.ι_comp_desc]

section CylinderDesc

variable {W : Type u} [TopologicalSpace W]

/-- The map `I × ((P × A) ∪_α ⨆ᵢ (P × D^{k i})) → W` glued from `L : I × (P × A) → W` and maps
`C i : I × (P × D^{k i}) → W` that agree along the attaching maps: the form of
`TauCeti.fiberwiseCellAttachmentDesc` for homotopies out of the fiberwise adjunction space. -/
def fiberwiseCellAttachmentCylinderDesc (L : C(I × (P × A), W))
    (C : ∀ i, C(I × (P × TopCat.disk.{u} (k i)), W))
    (hC : ∀ i t p s, C i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) = L (t, (p, α i (p, s)))) :
    C(I × fiberwiseCellAttachment α, W) :=
  (isPushout_fiberwiseCellAttachment α).cylinderDesc L
    (TopCat.sigmaCylinderDesc (F := fun i ↦ TopCat.of (P × TopCat.disk.{u} (k i))) C) fun t b ↦ by
      obtain ⟨i, x, rfl⟩ := TopCat.exists_sigma_ι_eq _ b
      rw [fiberwiseAttachingMap_ι, fiberwiseBoundaryInclusion_ι, TopCat.sigmaCylinderDesc_ι]
      exact (hC i t x.1 x.2).symm

variable (L : C(I × (P × A), W)) (C : ∀ i, C(I × (P × TopCat.disk.{u} (k i)), W))
  (hC : ∀ i t p s, C i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) = L (t, (p, α i (p, s))))

@[simp]
theorem fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl (t : I) (x : P × A) :
    fiberwiseCellAttachmentCylinderDesc α L C hC (t, fiberwiseCellAttachmentIncl α x) = L (t, x) :=
  (isPushout_fiberwiseCellAttachment α).cylinderDesc_inl L _ _ t x

@[simp]
theorem fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell (t : I) (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseCellAttachmentCylinderDesc α L C hC (t, fiberwiseCellAttachmentCell α i x) =
      C i (t, x) := by
  rw [← Sigma.ι_comp_desc (fiberwiseCellAttachmentCell α) i, ConcreteCategory.comp_apply]
  exact ((isPushout_fiberwiseCellAttachment α).cylinderDesc_inr L _ _ t _).trans
    (TopCat.sigmaCylinderDesc_ι (F := fun i ↦ TopCat.of (P × TopCat.disk.{u} (k i))) C t i x)

end CylinderDesc

/-- The projection of the fiberwise adjunction space `(P × A) ∪_α ⨆ᵢ (P × D^{k i})` to the parameter
space `P`. -/
def fiberwiseCellAttachmentProj : fiberwiseCellAttachment α ⟶ TopCat.of P :=
  fiberwiseCellAttachmentDesc α (TopCat.ofHom (ContinuousMap.fst : C(P × A, P)))
    (fun i ↦ TopCat.ofHom (ContinuousMap.fst : C(P × TopCat.disk.{u} (k i), P)))
    fun _ _ _ ↦ rfl

@[simp]
theorem fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl (x : P × A) :
    fiberwiseCellAttachmentProj α (fiberwiseCellAttachmentIncl α x) = x.1 :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentIncl_desc α _ _ _) x

@[simp]
theorem fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseCellAttachmentProj α (fiberwiseCellAttachmentCell α i x) = x.1 :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentCell_desc α _ _ _ i) x

/-- A property of the points of the fiberwise adjunction space holds as soon as it holds at the
points of `P × A` and of the cells. -/
@[elab_as_elim]
theorem fiberwiseCellAttachment_induction {motive : fiberwiseCellAttachment α → Prop}
    (h₀ : ∀ x : P × A, motive (fiberwiseCellAttachmentIncl α x))
    (h : ∀ i (x : P × TopCat.disk.{u} (k i)), motive (fiberwiseCellAttachmentCell α i x))
    (y : fiberwiseCellAttachment α) : motive y := by
  obtain ⟨x, rfl⟩ | hy :=
    (range_fiberwiseCellAttachmentIncl_union_iUnion_range_fiberwiseCellAttachmentCell α).symm ▸
      mem_univ y
  · exact h₀ x
  · obtain ⟨i, x, rfl⟩ := mem_iUnion.1 hy
    exact h i x

section Comparison

variable (χ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ : ∀ i p s, χ i (p, TopCat.diskBoundaryInclusion (k i) s) = α i (p, s))

/-- The **comparison map** `(P × A) ∪_α ⨆ᵢ (P × D^{k i}) → P × Y` over `P` of a family of
characteristic maps `χ i : P × D^{k i} → Y` restricting to the attaching maps `α i` on the boundary
spheres: it is the inclusion on `P × A` and `(p, x) ↦ (p, χ i (p, x))` on the `i`-th cell. -/
def fiberwiseCellComparison : fiberwiseCellAttachment α ⟶ TopCat.of (P × Y) :=
  fiberwiseCellAttachmentDesc α
    (TopCat.ofHom ((ContinuousMap.id P).prodMap ⟨Subtype.val, continuous_subtype_val⟩))
    (fun i ↦ TopCat.ofHom (ContinuousMap.fst.prodMk (χ i))) fun i p s ↦ Prod.ext rfl (hχ i p s)

@[simp]
theorem fiberwiseCellComparison_fiberwiseCellAttachmentIncl (x : P × A) :
    fiberwiseCellComparison α χ hχ (fiberwiseCellAttachmentIncl α x) = (x.1, (x.2 : Y)) :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentIncl_desc α _ _ _) x

@[simp]
theorem fiberwiseCellComparison_fiberwiseCellAttachmentCell (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseCellComparison α χ hχ (fiberwiseCellAttachmentCell α i x) = (x.1, χ i x) :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentCell_desc α _ _ _ i) x

/-- The comparison map lies over `P`. -/
@[simp]
theorem fst_fiberwiseCellComparison (y : fiberwiseCellAttachment α) :
    (fiberwiseCellComparison α χ hχ y).1 = fiberwiseCellAttachmentProj α y :=
  fiberwiseCellAttachment_induction α
    (fun x ↦ by rw [fiberwiseCellComparison_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl])
    (fun i x ↦ by rw [fiberwiseCellComparison_fiberwiseCellAttachmentCell,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]) y

end Comparison

end Attachment

section Reattachment

variable (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (χ₀ χ₁ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (h : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hh : ∀ i p, MapsTo (fun w ↦ h i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))))
  (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)

/-- The reattachment map on the `i`-th family of discs: `(p, x) ↦ (p, h i (p, 2x))` into the `i`-th
cell on the disc of radius `1/2`, glued to `K i` read in the annulus coordinates of the annulus
`1/2 ≤ ‖x‖`. The pieces agree on the seam `‖x‖ = 1/2` because `K i (1, ·) = χ₀ i ∘ (p, h i)` and
`h i (p, ·)` preserves the boundary sphere. -/
private def fiberwiseCellReattachmentFun (i : ι) :
    C(P × TopCat.disk.{u} (k i), fiberwiseCellAttachment α₀) :=
  TopCat.discGlue (by norm_num : (0 : ℝ) < 1 / 2)
    ⟨fun q ↦ fiberwiseCellAttachmentCell α₀ i (q.1, h i (q.1, TopCat.reattachmentRadial
        (ULift.up ⟨q.2.1, closedBall_subset_closedBall (by norm_num) q.2.2⟩))),
      (fiberwiseCellAttachmentCell α₀ i).hom.continuous.comp (continuous_fst.prodMk
        ((h i).continuous.comp (continuous_fst.prodMk (TopCat.continuous_reattachmentRadial.comp
          (continuous_uliftUp.comp ((continuous_subtype_val.comp continuous_snd).subtype_mk _))))))⟩
    ⟨fun q ↦ fiberwiseCellAttachmentIncl α₀
        (q.1, ⟨K i (σ q.2.1, (q.1, TopCat.diskBoundaryInclusion (k i) q.2.2)), hK i _ _ _⟩),
      (fiberwiseCellAttachmentIncl α₀).hom.continuous.comp (continuous_fst.prodMk
        (((K i).continuous.comp ((continuous_symm.comp (continuous_fst.comp continuous_snd)).prodMk
          (continuous_fst.prodMk ((TopCat.diskBoundaryInclusion (k i)).hom.continuous.comp
            (continuous_snd.comp continuous_snd))))).subtype_mk fun q ↦ hK i _ _ _))⟩
    fun p θ ↦ by
      obtain ⟨s, hs⟩ := hh i p ⟨θ, rfl⟩
      have hs' : h i (p, TopCat.diskBoundaryInclusion (k i) θ) =
          TopCat.diskBoundaryInclusion (k i) s := hs.symm
      -- At the seam `K i (1, ·) = χ₀ i ∘ (p, h i)`, and `h i (p, ·)` lands on the boundary sphere.
      have hseam : (⟨K i (σ 0, (p, TopCat.diskBoundaryInclusion (k i) θ)), hK i _ p θ⟩ : A) =
          α₀ i (p, s) := by
        refine Subtype.ext ?_
        dsimp only
        rw [symm_zero, ContinuousMap.Homotopy.apply_one, ContinuousMap.comp_apply,
          ContinuousMap.prod_eval, ContinuousMap.fst_apply, hs']
        exact hχ₀ i p s
      simp only [ContinuousMap.coe_mk, TopCat.reattachmentRadial_half_smul]
      rw [hseam, hs', fiberwiseCellAttachmentCell_diskBoundaryInclusion]

private theorem fiberwiseCellReattachmentFun_of_norm_le (i : ι) (p : P)
    {w : TopCat.disk.{u} (k i)} (hw : ‖w.down.1‖ ≤ 1 / 2) :
    fiberwiseCellReattachmentFun α₀ χ₀ χ₁ hχ₀ h hh K hK i (p, w) =
      fiberwiseCellAttachmentCell α₀ i (p, h i (p, TopCat.reattachmentRadial w)) := by
  rw [fiberwiseCellReattachmentFun, TopCat.discGlue_apply_of_norm_le _ _ _ _ _ hw]
  rfl

private theorem fiberwiseCellReattachmentFun_of_le_norm (i : ι) (p : P)
    {w : TopCat.disk.{u} (k i)} (hw : 1 / 2 ≤ ‖w.down.1‖) :
    fiberwiseCellReattachmentFun α₀ χ₀ χ₁ hχ₀ h hh K hK i (p, w) =
      fiberwiseCellAttachmentIncl α₀ (p, ⟨K i (TopCat.reattachmentTime w,
        (p, TopCat.diskBoundaryInclusion (k i) (TopCat.annulusDir (by norm_num) ⟨w, hw⟩))),
        hK i _ _ _⟩) := by
  rw [fiberwiseCellReattachmentFun, TopCat.discGlue_apply_of_le_norm _ _ _ _ _ hw,
    TopCat.reattachmentTime_def]
  rfl

include hχ₁ in
/-- On the boundary spheres, the reattachment map is the attaching map `α₁ i`. -/
private theorem fiberwiseCellReattachmentFun_diskBoundaryInclusion (i : ι) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    fiberwiseCellReattachmentFun α₀ χ₀ χ₁ hχ₀ h hh K hK i
        (p, TopCat.diskBoundaryInclusion (k i) s) =
      fiberwiseCellAttachmentIncl α₀ (p, α₁ i (p, s)) := by
  have hw : 1 / 2 ≤ ‖(TopCat.diskBoundaryInclusion (k i) s).down.1‖ := by
    rw [TopCat.norm_diskBoundaryInclusion]
    norm_num
  rw [fiberwiseCellReattachmentFun_of_le_norm (hw := hw)]
  refine congrArg _ (Prod.ext rfl (Subtype.ext ?_))
  simp only [TopCat.annulusDir_diskBoundaryInclusion, TopCat.reattachmentTime_diskBoundaryInclusion,
    ContinuousMap.Homotopy.apply_zero]
  exact hχ₁ i p s

/-- **The fiberwise reattachment map**
`E : (P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i}) → (P × A) ∪_{α₀} ⨆ᵢ (P × D^{k i})` of a family over `P` of
self-maps `h i` of the disc pairs `(D^{k i}, ∂D^{k i})` and of homotopies
`K i : χ₁ i ≃ χ₀ i ∘ (p, h i)` of families of characteristic maps keeping the boundary spheres in
`A`. It is the identity on `P × A`; on the `i`-th family of discs it sends `(p, x)` to the point
`(p, h i (p, 2x))` of the `i`-th cell when `‖x‖ ≤ 1/2`, and to the point
`(p, K i (2 - 2‖x‖, (p, x/‖x‖)))` of `P × A` when `1/2 ≤ ‖x‖`. -/
def fiberwiseCellReattachment : fiberwiseCellAttachment α₁ ⟶ fiberwiseCellAttachment α₀ :=
  fiberwiseCellAttachmentDesc α₁ (fiberwiseCellAttachmentIncl α₀)
    (fun i ↦ TopCat.ofHom (fiberwiseCellReattachmentFun α₀ χ₀ χ₁ hχ₀ h hh K hK i))
    fun i p s ↦ fiberwiseCellReattachmentFun_diskBoundaryInclusion α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK i
      p s

/-- The fiberwise reattachment map is the identity on `P × A`. -/
@[simp]
theorem fiberwiseCellReattachment_fiberwiseCellAttachmentIncl (x : P × A) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK (fiberwiseCellAttachmentIncl α₁ x) =
      fiberwiseCellAttachmentIncl α₀ x :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentIncl_desc α₁ _ _ _) x

private theorem fiberwiseCellReattachment_fiberwiseCellAttachmentCell (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK (fiberwiseCellAttachmentCell α₁ i x) =
      fiberwiseCellReattachmentFun α₀ χ₀ χ₁ hχ₀ h hh K hK i x :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentCell_desc α₁ _ _ _ i) x

/-- On the disc of radius `1/2` of the `i`-th cell over `p`, the fiberwise reattachment map is
`x ↦ h i (p, 2x)`, read in the `i`-th cell over `p`. -/
theorem fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (i : ι) (p : P)
    {w v : TopCat.disk.{u} (k i)} (hw : ‖w.down.1‖ ≤ 1 / 2) (hv : v.down.1 = (2 : ℝ) • w.down.1) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK
        (fiberwiseCellAttachmentCell α₁ i (p, w)) =
      fiberwiseCellAttachmentCell α₀ i (p, h i (p, v)) := by
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell,
    fiberwiseCellReattachmentFun_of_norm_le (hw := hw)]
  exact congrArg (fun v ↦ fiberwiseCellAttachmentCell α₀ i (p, h i (p, v)))
    (ULift.ext (Subtype.ext (hv ▸ TopCat.coe_reattachmentRadial_of_norm_le hw)))

/-- Outside the disc of radius `1/2` of the `i`-th cell over `p`, the fiberwise reattachment map is
`x ↦ K i (2 - 2‖x‖, (p, x/‖x‖))`, read in `P × A`. -/
theorem fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (i : ι) (p : P)
    {w : TopCat.disk.{u} (k i)} (hw : 1 / 2 ≤ ‖w.down.1‖) {t : I}
    (ht : (t : ℝ) = 2 - 2 * ‖w.down.1‖) {s : TopCat.diskBoundary.{u} (k i)}
    (hs : s.down.1 = ‖w.down.1‖⁻¹ • w.down.1) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK
        (fiberwiseCellAttachmentCell α₁ i (p, w)) =
      fiberwiseCellAttachmentIncl α₀ (p, ⟨K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)),
        hK i t p s⟩) := by
  have ht' : TopCat.reattachmentTime w = t :=
    Subtype.ext ((TopCat.coe_reattachmentTime_of_le_norm hw).trans ht.symm)
  have hs' : TopCat.annulusDir (by norm_num) ⟨w, hw⟩ = s :=
    ULift.ext (Subtype.ext ((TopCat.coe_annulusDir _ _).trans hs.symm))
  subst ht' hs'
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell,
    fiberwiseCellReattachmentFun_of_le_norm (hw := hw)]

/-- The fiberwise reattachment map lies over `P`. -/
@[simp]
theorem fiberwiseCellAttachmentProj_fiberwiseCellReattachment (y : fiberwiseCellAttachment α₁) :
    fiberwiseCellAttachmentProj α₀ (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK y) =
      fiberwiseCellAttachmentProj α₁ y := by
  refine fiberwiseCellAttachment_induction α₁
    (fun x ↦ by rw [fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl]) (fun i x ↦ ?_) y
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell,
    fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]
  rcases le_total ‖x.2.down.1‖ (1 / 2) with hw | hw
  · rw [fiberwiseCellReattachmentFun_of_norm_le (hw := hw),
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]
  · rw [fiberwiseCellReattachmentFun_of_le_norm (hw := hw),
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl]

/-- On the `i`-th cell, the fiberwise reattachment map followed by the comparison map `Φ₀` is `K i`
read along the disc-to-cylinder map `x ↦ (reattachmentTime x, reattachmentRadial x)`. -/
private theorem fiberwiseCellComparison_fiberwiseCellReattachment_fiberwiseCellAttachmentCell
    (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    fiberwiseCellComparison α₀ χ₀ hχ₀ (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK
        (fiberwiseCellAttachmentCell α₁ i (p, w))) =
      (p, K i (TopCat.reattachmentTime w, (p, TopCat.reattachmentRadial w))) := by
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell]
  by_cases hw : 1 / 2 ≤ ‖w.down.1‖
  · rw [fiberwiseCellReattachmentFun_of_le_norm (hw := hw),
      fiberwiseCellComparison_fiberwiseCellAttachmentIncl, TopCat.reattachmentRadial_of_le_norm hw]
  · rw [fiberwiseCellReattachmentFun_of_norm_le (hw := (not_le.1 hw).le),
      fiberwiseCellComparison_fiberwiseCellAttachmentCell,
      TopCat.reattachmentTime_of_norm_le (not_le.1 hw).le, ContinuousMap.Homotopy.apply_one,
      ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.fst_apply]

/-- The homotopy on the cylinder over the `i`-th family of discs:
`(t, (p, x)) ↦ (p, K i (π (x, t)))` for the straight-line homotopy
`π = TauCeti.TopCat.reattachmentPath` in the cylinder `I × D^{k i}` from
`x ↦ (reattachmentTime x, reattachmentRadial x)` to `x ↦ (0, x)`. -/
private def fiberwiseCellReattachmentCylinder (i : ι) :
    C(I × (P × TopCat.disk.{u} (k i)), P × Y) :=
  ⟨fun q ↦ (q.2.1, K i ((TopCat.reattachmentPath (q.2.2, q.1)).1,
      (q.2.1, (TopCat.reattachmentPath (q.2.2, q.1)).2))),
    (continuous_fst.comp continuous_snd).prodMk ((K i).continuous.comp
      ((continuous_fst.comp (TopCat.continuous_reattachmentPath.comp
        ((continuous_snd.comp continuous_snd).prodMk continuous_fst))).prodMk
      ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp
        (TopCat.continuous_reattachmentPath.comp
          ((continuous_snd.comp continuous_snd).prodMk continuous_fst))))))⟩

private theorem fiberwiseCellReattachmentCylinder_apply (i : ι) (t : I)
    (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseCellReattachmentCylinder χ₀ χ₁ h K i (t, x) =
      (x.1, K i ((TopCat.reattachmentPath (x.2, t)).1,
        (x.1, (TopCat.reattachmentPath (x.2, t)).2))) :=
  rfl

include hχ₁ in
/-- The map `I × ((P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i})) → P × Y` underlying
`TauCeti.fiberwiseCellReattachmentHomotopy`: the inclusion on `I × (P × A)`, and
`TauCeti.fiberwiseCellReattachmentCylinder` on the cylinders over the cells. -/
private def fiberwiseCellReattachmentCylinderMap : C(I × fiberwiseCellAttachment α₁, P × Y) :=
  fiberwiseCellAttachmentCylinderDesc α₁
    (((ContinuousMap.id P).prodMap ⟨Subtype.val, continuous_subtype_val⟩).comp ContinuousMap.snd)
    (fiberwiseCellReattachmentCylinder χ₀ χ₁ h K) fun i t p s ↦ by
      rw [fiberwiseCellReattachmentCylinder_apply, TopCat.reattachmentPath_diskBoundaryInclusion,
        ContinuousMap.Homotopy.apply_zero]
      exact Prod.ext rfl (hχ₁ i p s)

private theorem fiberwiseCellReattachmentCylinderMap_fiberwiseCellAttachmentIncl (t : I)
    (x : P × A) :
    fiberwiseCellReattachmentCylinderMap α₁ χ₀ χ₁ hχ₁ h K (t, fiberwiseCellAttachmentIncl α₁ x) =
      (x.1, (x.2 : Y)) :=
  fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ _ _ t x

private theorem fiberwiseCellReattachmentCylinderMap_fiberwiseCellAttachmentCell (t : I) (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseCellReattachmentCylinderMap α₁ χ₀ χ₁ hχ₁ h K (t, fiberwiseCellAttachmentCell α₁ i x) =
      (x.1, K i ((TopCat.reattachmentPath (x.2, t)).1,
        (x.1, (TopCat.reattachmentPath (x.2, t)).2))) :=
  fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell α₁ _ _ _ t i x

/-- **`Φ₀ ∘ E` is homotopic to `Φ₁` over `P`, relative to `P × A`.** The homotopy from the fiberwise
reattachment map followed by the comparison map `Φ₀` to the comparison map `Φ₁`. It fixes the
points of `P × A`, lies over `P` at all times
(`TauCeti.fst_fiberwiseCellReattachmentHomotopy`), and on the `i`-th cell it is `K i` read along
the straight-line homotopy `TauCeti.TopCat.reattachmentPath` in the cylinder `I × D^{k i}`. -/
def fiberwiseCellReattachmentHomotopy :
    (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫
        fiberwiseCellComparison α₀ χ₀ hχ₀).hom.HomotopyRel
      (fiberwiseCellComparison α₁ χ₁ hχ₁).hom (range (fiberwiseCellAttachmentIncl α₁)) where
  toFun := fiberwiseCellReattachmentCylinderMap α₁ χ₀ χ₁ hχ₁ h K
  continuous_toFun := (fiberwiseCellReattachmentCylinderMap α₁ χ₀ χ₁ hχ₁ h K).continuous
  -- At time `0`, on the `i`-th cell the cylinder path is
  -- `x ↦ (reattachmentTime x, reattachmentRadial x)`, along which `K i` is `Φ₀ ∘ E`.
  map_zero_left y := by
    rw [TopCat.hom_comp, ContinuousMap.comp_apply]
    refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · rw [fiberwiseCellReattachmentCylinderMap_fiberwiseCellAttachmentIncl,
        fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
        fiberwiseCellComparison_fiberwiseCellAttachmentIncl]
    · rw [fiberwiseCellReattachmentCylinderMap_fiberwiseCellAttachmentCell,
        fiberwiseCellComparison_fiberwiseCellReattachment_fiberwiseCellAttachmentCell,
        TopCat.reattachmentPath_zero]
  -- At time `1` the cylinder path is `x ↦ (0, x)`, along which `K i` is `χ₁ i`.
  map_one_left y := by
    refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · rw [fiberwiseCellReattachmentCylinderMap_fiberwiseCellAttachmentIncl,
        fiberwiseCellComparison_fiberwiseCellAttachmentIncl]
    · rw [fiberwiseCellReattachmentCylinderMap_fiberwiseCellAttachmentCell,
        fiberwiseCellComparison_fiberwiseCellAttachmentCell, TopCat.reattachmentPath_one,
        ContinuousMap.Homotopy.apply_zero]
  -- On `P × A` the homotopy is constant.
  prop' t y hy := by
    obtain ⟨x, rfl⟩ := hy
    refine (fiberwiseCellReattachmentCylinderMap_fiberwiseCellAttachmentIncl α₁ χ₀ χ₁ hχ₁ h K t
      x).trans ?_
    rw [TopCat.hom_comp, ContinuousMap.comp_apply,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellComparison_fiberwiseCellAttachmentIncl]

@[simp]
theorem fiberwiseCellReattachmentHomotopy_fiberwiseCellAttachmentIncl (t : I) (x : P × A) :
    fiberwiseCellReattachmentHomotopy α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK
        (t, fiberwiseCellAttachmentIncl α₁ x) = (x.1, (x.2 : Y)) :=
  fiberwiseCellReattachmentCylinderMap_fiberwiseCellAttachmentIncl α₁ χ₀ χ₁ hχ₁ h K t x

@[simp]
theorem fiberwiseCellReattachmentHomotopy_fiberwiseCellAttachmentCell (t : I) (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseCellReattachmentHomotopy α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK
        (t, fiberwiseCellAttachmentCell α₁ i x) =
      (x.1, K i ((TopCat.reattachmentPath (x.2, t)).1,
        (x.1, (TopCat.reattachmentPath (x.2, t)).2))) :=
  fiberwiseCellReattachmentCylinderMap_fiberwiseCellAttachmentCell α₁ χ₀ χ₁ hχ₁ h K t i x

/-- The homotopy from `Φ₀ ∘ E` to `Φ₁` lies over `P` at all times. -/
@[simp]
theorem fst_fiberwiseCellReattachmentHomotopy (t : I) (y : fiberwiseCellAttachment α₁) :
    (fiberwiseCellReattachmentHomotopy α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK (t, y)).1 =
      fiberwiseCellAttachmentProj α₁ y := by
  refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
  · rw [fiberwiseCellReattachmentHomotopy_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl]
  · rw [fiberwiseCellReattachmentHomotopy_fiberwiseCellAttachmentCell,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]

end Reattachment

section LeftInverse

variable (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (χ₀ χ₁ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (h h' : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hh : ∀ i p, MapsTo (fun w ↦ h i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (hh' : ∀ i p, MapsTo (fun w ↦ h' i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))))
  (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (K' : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h' i))))
  (hK' : ∀ i t p s, K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (g₀ : C(P × Y, fiberwiseCellAttachment α₀))
  (hg₀ : Function.LeftInverse g₀ (fiberwiseCellComparison α₀ χ₀ hχ₀))
  (hg₀P : ∀ y, fiberwiseCellAttachmentProj α₀ (g₀ y) = y.1)

include hg₀ hg₀P in
/-- **The fiberwise reattachment map is homotopic to `g₀ ∘ Φ₁`.** For a left inverse `g₀` over `P`
of the comparison map `Φ₀`, the fiberwise reattachment map is homotopic to `g₀ ∘ Φ₁` relative to
`P × A`, by a homotopy over `P`: it is `g₀` applied to
`TauCeti.fiberwiseCellReattachmentHomotopy`. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_of_leftInverse :
    ∃ G : (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK).hom.HomotopyRel
        (g₀.comp (fiberwiseCellComparison α₁ χ₁ hχ₁).hom)
        (range (fiberwiseCellAttachmentIncl α₁)),
      ∀ t y, fiberwiseCellAttachmentProj α₀ (G (t, y)) = fiberwiseCellAttachmentProj α₁ y := by
  have hE : g₀.comp (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫
      fiberwiseCellComparison α₀ χ₀ hχ₀).hom =
        (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK).hom :=
    ContinuousMap.ext fun _ ↦ hg₀ _
  exact ⟨((fiberwiseCellReattachmentHomotopy α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK).compContinuousMap
    g₀).cast hE rfl, fun t y ↦ (hg₀P _).trans (fst_fiberwiseCellReattachmentHomotopy ..)⟩

include hg₀ hg₀P in
/-- **The fiberwise reattachment map does not depend on the homotopies.** Two fiberwise
reattachment maps between the same attachments, built from any families of self-maps of the disc
pairs and of homotopies of the same characteristic maps, are homotopic relative to `P × A`, by a
homotopy over `P`, provided the comparison map `Φ₀` has a left inverse `g₀` over `P`. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_fiberwiseCellReattachment :
    ∃ G : (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK).hom.HomotopyRel
        (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h' hh' K' hK').hom
        (range (fiberwiseCellAttachmentIncl α₁)),
      ∀ t y, fiberwiseCellAttachmentProj α₀ (G (t, y)) = fiberwiseCellAttachmentProj α₁ y := by
  obtain ⟨G, hG⟩ := exists_homotopyRel_fiberwiseCellReattachment_of_leftInverse
    α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK g₀ hg₀ hg₀P
  obtain ⟨G', hG'⟩ := exists_homotopyRel_fiberwiseCellReattachment_of_leftInverse
    α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h' hh' K' hK' g₀ hg₀ hg₀P
  refine ⟨G.trans G'.symm, fun t y ↦ ?_⟩
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · exact hG _ y
  · exact hG' _ y

end LeftInverse

section Composition

variable (α₀ α₁ α₂ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (χ₀ χ₁ χ₂ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (hχ₂ : ∀ i p s, χ₂ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₂ i (p, s))
  (h₀₁ h₁₂ h₀₂ : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hh₀₁ : ∀ i p, MapsTo (fun w ↦ h₀₁ i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (hh₁₂ : ∀ i p, MapsTo (fun w ↦ h₁₂ i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (hh₀₂ : ∀ i p, MapsTo (fun w ↦ h₀₂ i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (K₀₁ : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h₀₁ i))))
  (hK₀₁ : ∀ i t p s, K₀₁ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (K₁₂ : ∀ i, (χ₂ i).Homotopy ((χ₁ i).comp (ContinuousMap.fst.prodMk (h₁₂ i))))
  (hK₁₂ : ∀ i t p s, K₁₂ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (K₀₂ : ∀ i, (χ₂ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h₀₂ i))))
  (hK₀₂ : ∀ i t p s, K₀₂ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (g₀ : C(P × Y, fiberwiseCellAttachment α₀))
  (hg₀ : Function.LeftInverse g₀ (fiberwiseCellComparison α₀ χ₀ hχ₀))
  (hg₀P : ∀ y, fiberwiseCellAttachmentProj α₀ (g₀ y) = y.1)

include hg₀ hg₀P in
/-- **Fiberwise reattachment maps compose up to homotopy.** For three families of characteristic
maps and fiberwise reattachment maps `E₀₁`, `E₁₂`, `E₀₂` between their attachments, `E₀₁ ∘ E₁₂`
is homotopic to `E₀₂` relative to `P × A`, by a homotopy over `P`, provided the comparison map
`Φ₀` has a left inverse `g₀` over `P`. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment :
    ∃ G : (fiberwiseCellReattachment α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂ K₁₂ hK₁₂ ≫
        fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁ hh₀₁ K₀₁ hK₀₁).hom.HomotopyRel
        (fiberwiseCellReattachment α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂ hh₀₂ K₀₂ hK₀₂).hom
        (range (fiberwiseCellAttachmentIncl α₂)),
      ∀ t y, fiberwiseCellAttachmentProj α₀ (G (t, y)) = fiberwiseCellAttachmentProj α₂ y := by
  -- `E₀₁ ∘ E₁₂ ≃ g₀ ∘ Φ₁ ∘ E₁₂ ≃ g₀ ∘ Φ₂ ≃ E₀₂`.
  set E₁₂ := fiberwiseCellReattachment α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂ K₁₂ hK₁₂
  obtain ⟨G₁, hG₁⟩ := exists_homotopyRel_fiberwiseCellReattachment_of_leftInverse
    α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h₀₁ hh₀₁ K₀₁ hK₀₁ g₀ hg₀ hg₀P
  obtain ⟨G₃, hG₃⟩ := exists_homotopyRel_fiberwiseCellReattachment_of_leftInverse
    α₀ α₂ χ₀ χ₂ hχ₀ hχ₂ h₀₂ hh₀₂ K₀₂ hK₀₂ g₀ hg₀ hg₀P
  have hmono : range (fiberwiseCellAttachmentIncl α₂) ⊆
      E₁₂.hom ⁻¹' range (fiberwiseCellAttachmentIncl α₁) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, (fiberwiseCellReattachment_fiberwiseCellAttachmentIncl ..).symm⟩
  let F₁ := (G₁.precomp E₁₂.hom).mono hmono
  let F₂ := ((fiberwiseCellReattachmentHomotopy α₁ α₂ χ₁ χ₂ hχ₁ hχ₂ h₁₂ hh₁₂ K₁₂
    hK₁₂).compContinuousMap g₀).cast
    (by rw [TopCat.hom_comp, ContinuousMap.comp_assoc] :
      g₀.comp (E₁₂ ≫ fiberwiseCellComparison α₁ χ₁ hχ₁).hom =
        (g₀.comp (fiberwiseCellComparison α₁ χ₁ hχ₁).hom).comp E₁₂.hom) rfl
  refine ⟨(F₁.trans (F₂.trans G₃.symm)).cast (TopCat.hom_comp _ _).symm rfl, fun t y ↦ ?_⟩
  simp only [ContinuousMap.HomotopyRel.cast_apply, ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · rw [ContinuousMap.HomotopyRel.mono_apply, ContinuousMap.HomotopyRel.precomp_apply, hG₁]
    exact fiberwiseCellAttachmentProj_fiberwiseCellReattachment ..
  · exact (hg₀P _).trans (fst_fiberwiseCellReattachmentHomotopy ..)
  · exact hG₃ _ y

end Composition

section Inverse

/-! ### The reversed reattachment map

When the self-maps `h i (p, ·)` of the discs are linear isometries, reversing the homotopies
`K i : χ₁ i ≃ χ₀ i ∘ h i` through the inverse isometries gives homotopies `χ₀ i ≃ χ₁ i ∘ h⁻¹ i`,
and hence a fiberwise reattachment map in the opposite direction. It is a homotopy inverse of the
first, relative to `P × A` and over `P`, with no further hypothesis on the attachments. -/

private theorem two_smul_mem_closedBall_one {n : ℕ}
    (z : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) :
    (2 : ℝ) • (z : EuclideanSpace ℝ (Fin n)) ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_two]
  linarith [mem_closedBall_zero_iff.1 z.2]

variable (α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))

/-- The `i`-th cell of the attachment along `α₁` with a collar attached along a homotopy
`H : I × (P × ∂D^{k i}) → A` starting at `α₁ i`: it sends `(p, x)` to the point `(p, 2x)` of the
cell for `‖x‖ ≤ 1/2`, and to the point `(p, H (2‖x‖ - 1, (p, x/‖x‖)))` of `P × A` for
`1/2 ≤ ‖x‖`. -/
private def collarCell (i : ι) (H : C(I × (P × TopCat.diskBoundary.{u} (k i)), A))
    (hH : ∀ p s, H (0, (p, s)) = α₁ i (p, s)) :
    C(P × TopCat.disk.{u} (k i), fiberwiseCellAttachment α₁) :=
  TopCat.discGlue (by norm_num : (0 : ℝ) < 1 / 2)
    ⟨fun q ↦ fiberwiseCellAttachmentCell α₁ i
        (q.1, ULift.up ⟨(2 : ℝ) • q.2.1, two_smul_mem_closedBall_one q.2⟩),
      (fiberwiseCellAttachmentCell α₁ i).hom.continuous.comp (continuous_fst.prodMk
        (continuous_uliftUp.comp (((continuous_subtype_val.comp continuous_snd).const_smul
          (2 : ℝ)).subtype_mk fun q ↦ two_smul_mem_closedBall_one q.2)))⟩
    ⟨fun q ↦ fiberwiseCellAttachmentIncl α₁ (q.1, H (q.2.1, (q.1, q.2.2))),
      (fiberwiseCellAttachmentIncl α₁).hom.continuous.comp (continuous_fst.prodMk
        (H.continuous.comp ((continuous_fst.comp continuous_snd).prodMk
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))))⟩
    fun p θ ↦ by
      simp only [ContinuousMap.coe_mk]
      rw [hH, ← fiberwiseCellAttachmentCell_diskBoundaryInclusion]
      refine congrArg (fun w ↦ fiberwiseCellAttachmentCell α₁ i (p, w)) (ULift.ext (Subtype.ext ?_))
      refine (TopCat.coe_diskBoundaryInclusion_apply_down _ θ).trans ?_
      dsimp only
      rw [smul_smul]
      norm_num

variable {α₁}

private theorem collarCell_of_norm_le {i : ι} {H : C(I × (P × TopCat.diskBoundary.{u} (k i)), A)}
    (hH : ∀ p s, H (0, (p, s)) = α₁ i (p, s)) (p : P) {z w : TopCat.disk.{u} (k i)}
    (hz : ‖z.down.1‖ ≤ 1 / 2) (hw : w.down.1 = (2 : ℝ) • z.down.1) :
    collarCell α₁ i H hH (p, z) = fiberwiseCellAttachmentCell α₁ i (p, w) := by
  rw [collarCell, TopCat.discGlue_apply_of_norm_le _ _ _ _ _ hz]
  exact congrArg (fun w ↦ fiberwiseCellAttachmentCell α₁ i (p, w))
    (ULift.ext (Subtype.ext hw.symm))

private theorem collarCell_of_le_norm {i : ι} {H : C(I × (P × TopCat.diskBoundary.{u} (k i)), A)}
    (hH : ∀ p s, H (0, (p, s)) = α₁ i (p, s)) (p : P) {z : TopCat.disk.{u} (k i)}
    (hz : 1 / 2 ≤ ‖z.down.1‖) {t : I} (ht : (t : ℝ) = 2 * ‖z.down.1‖ - 1)
    {θ : TopCat.diskBoundary.{u} (k i)} (hθ : θ.down.1 = ‖z.down.1‖⁻¹ • z.down.1) :
    collarCell α₁ i H hH (p, z) = fiberwiseCellAttachmentIncl α₁ (p, H (t, (p, θ))) := by
  rw [collarCell, TopCat.discGlue_apply_of_le_norm _ _ _ _ _ hz]
  have ht' : TopCat.annulusParam (1 / 2) z = t := by
    refine Subtype.ext ?_
    have := TopCat.add_one_sub_mul_annulusParam (by norm_num : (1 / 2 : ℝ) ≤ 1) hz
    rw [ht]
    linarith
  have hθ' : TopCat.annulusDir (by norm_num : (0 : ℝ) < 1 / 2) ⟨z, hz⟩ = θ :=
    ULift.ext (Subtype.ext ((TopCat.coe_annulusDir _ _).trans hθ.symm))
  simp only [ContinuousMap.coe_mk, ht', hθ']

private theorem collarCell_of_eq_half_smul {i : ι}
    {H : C(I × (P × TopCat.diskBoundary.{u} (k i)), A)} (hH : ∀ p s, H (0, (p, s)) = α₁ i (p, s))
    (p : P) {z w : TopCat.disk.{u} (k i)} (hz : z.down.1 = (1 / 2 : ℝ) • w.down.1) :
    collarCell α₁ i H hH (p, z) = fiberwiseCellAttachmentCell α₁ i (p, w) := by
  refine collarCell_of_norm_le hH p ?_ (by rw [hz, smul_smul]; norm_num)
  rw [hz, norm_smul, Real.norm_of_nonneg (by norm_num)]
  linarith [mem_closedBall_zero_iff.1 w.down.2]

private theorem fiberwiseCellAttachmentProj_collarCell {i : ι}
    {H : C(I × (P × TopCat.diskBoundary.{u} (k i)), A)} (hH : ∀ p s, H (0, (p, s)) = α₁ i (p, s))
    (q : P × TopCat.disk.{u} (k i)) :
    fiberwiseCellAttachmentProj α₁ (collarCell α₁ i H hH q) = q.1 := by
  obtain ⟨p, z⟩ := q
  rcases le_total ‖z.down.1‖ (1 / 2) with hz | hz
  · rw [collarCell_of_norm_le hH p hz (TopCat.coe_reattachmentRadial_of_norm_le hz),
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]
  · rw [collarCell_of_le_norm hH p hz (t := σ (TopCat.reattachmentTime z))
      (by rw [coe_symm_eq, TopCat.coe_reattachmentTime_of_le_norm hz]; ring)
      (TopCat.coe_annulusDir (by norm_num) ⟨z, hz⟩),
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl]

variable (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (χ₀ χ₁ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (g : ∀ i, P → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)))
  (h h' : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hg : ∀ i p w, (h i (p, w)).down.1 = g i p w.down.1)
  (hg' : ∀ i p w, (h' i (p, w)).down.1 = (g i p).symm w.down.1)
  (hh : ∀ i p, MapsTo (fun w ↦ h i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (hh' : ∀ i p, MapsTo (fun w ↦ h' i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))))
  (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (K' : ∀ i, (χ₀ i).Homotopy ((χ₁ i).comp (ContinuousMap.fst.prodMk (h' i))))
  (hK' : ∀ i t p s, K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (hKK' : ∀ i t p w, K' i (t, (p, w)) = K i (σ t, (p, h' i (p, w))))

/-- The restriction of `K i` to the boundary spheres, as a homotopy in `A` starting at `α₁ i`. -/
private def reattachmentBoundaryHomotopy (i : ι) :
    C(I × (P × TopCat.diskBoundary.{u} (k i)), A) :=
  ⟨fun q ↦ ⟨K i (q.1, (q.2.1, TopCat.diskBoundaryInclusion (k i) q.2.2)), hK i _ _ _⟩,
    ((K i).continuous.comp (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
      ((TopCat.diskBoundaryInclusion (k i)).hom.continuous.comp
        (continuous_snd.comp continuous_snd))))).subtype_mk _⟩

private theorem coe_reattachmentBoundaryHomotopy_apply (i : ι) (t : I) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    (reattachmentBoundaryHomotopy χ₀ χ₁ h K hK i (t, (p, s)) : Y) =
      K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) :=
  rfl

include hχ₁ in
private theorem reattachmentBoundaryHomotopy_zero (i : ι) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    reattachmentBoundaryHomotopy χ₀ χ₁ h K hK i (0, (p, s)) = α₁ i (p, s) :=
  Subtype.ext <| by rw [coe_reattachmentBoundaryHomotopy_apply, (K i).apply_zero, hχ₁]

include hg hg' in
/-- For `‖x‖ ≤ 1/4`, the composite of the reattachment maps along `K` and `K'` sends the point `x`
of the `i`-th cell to the point `4x`: `E` sends it to `h (2x)` and `E'` to `h⁻¹ (2 h (2x))`. -/
private theorem collarCell_of_norm_le_quarter (i : ι) (p : P) {x z : TopCat.disk.{u} (k i)}
    (hx : ‖x.down.1‖ ≤ 1 / 4) (hz : z.down.1 = (2 : ℝ) • x.down.1) :
    collarCell α₁ i (reattachmentBoundaryHomotopy χ₀ χ₁ h K hK i)
        (reattachmentBoundaryHomotopy_zero α₁ χ₀ χ₁ hχ₁ h K hK i) (p, z) =
      fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK'
        (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK
          (fiberwiseCellAttachmentCell α₁ i (p, x))) := by
  have hx₂ : ‖x.down.1‖ ≤ 1 / 2 := by linarith
  set y := h i (p, TopCat.reattachmentRadial x)
  have hy : y.down.1 = g i p ((2 : ℝ) • x.down.1) := by
    rw [hg, TopCat.coe_reattachmentRadial_of_norm_le hx₂]
  have hy₂ : ‖y.down.1‖ ≤ 1 / 2 := by
    rw [hy, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_two]
    linarith
  have hz₂ : ‖z.down.1‖ ≤ 1 / 2 := by
    rw [hz, norm_smul, Real.norm_two]
    linarith
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hx₂)
      (hv := TopCat.coe_reattachmentRadial_of_norm_le hx₂),
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hy₂)
      (hv := TopCat.coe_reattachmentRadial_of_norm_le hy₂),
    collarCell_of_norm_le _ p hz₂ (TopCat.coe_reattachmentRadial_of_norm_le hz₂)]
  refine congrArg (fun w ↦ fiberwiseCellAttachmentCell α₁ i (p, w)) (ULift.ext (Subtype.ext ?_))
  simp [hg', TopCat.coe_reattachmentRadial_of_norm_le hy₂, hy, ← map_smul,
    TopCat.coe_reattachmentRadial_of_norm_le hz₂, hz]

include hg hg' hKK' in
/-- For `1/4 ≤ ‖x‖ ≤ 1/2`, the composite of the reattachment maps along `K` and `K'` sends the point
`x` of the `i`-th cell to the point `K i (4‖x‖ - 1, x/‖x‖)` of `A`: `E` sends it to `h (2x)`, and
`E'` reads `K'` at time `2 - 4‖x‖`, which is `K` at time `4‖x‖ - 1`. -/
private theorem collarCell_of_quarter_le_norm_le_half (i : ι) (p : P)
    {x z : TopCat.disk.{u} (k i)} (hx₁ : 1 / 4 ≤ ‖x.down.1‖) (hx₂ : ‖x.down.1‖ ≤ 1 / 2)
    (hz : z.down.1 = (2 : ℝ) • x.down.1) :
    collarCell α₁ i (reattachmentBoundaryHomotopy χ₀ χ₁ h K hK i)
        (reattachmentBoundaryHomotopy_zero α₁ χ₀ χ₁ hχ₁ h K hK i) (p, z) =
      fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK'
        (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK
          (fiberwiseCellAttachmentCell α₁ i (p, x))) := by
  set y := h i (p, TopCat.reattachmentRadial x)
  have hy : y.down.1 = g i p ((2 : ℝ) • x.down.1) := by
    rw [hg, TopCat.coe_reattachmentRadial_of_norm_le hx₂]
  have hny : ‖y.down.1‖ = ‖z.down.1‖ := by rw [hy, LinearIsometryEquiv.norm_map, hz]
  have hz₂ : 1 / 2 ≤ ‖z.down.1‖ := by
    rw [hz, norm_smul, Real.norm_two]
    linarith
  have hy₂ : 1 / 2 ≤ ‖y.down.1‖ := hny ▸ hz₂
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hx₂)
      (hv := TopCat.coe_reattachmentRadial_of_norm_le hx₂),
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hy₂)
      (ht := TopCat.coe_reattachmentTime_of_le_norm hy₂)
      (hs := TopCat.coe_annulusDir (by norm_num) ⟨y, hy₂⟩),
    collarCell_of_le_norm _ p hz₂ (t := σ (TopCat.reattachmentTime y))
      (by rw [coe_symm_eq, TopCat.coe_reattachmentTime_of_le_norm hy₂, hny]; ring)
      (TopCat.coe_annulusDir (by norm_num) ⟨z, hz₂⟩)]
  refine congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₁ (p, a)) (Subtype.ext ?_)
  rw [coe_reattachmentBoundaryHomotopy_apply]
  refine Eq.trans ?_ (hKK' i _ p _).symm
  refine congrArg (fun w ↦ K i (_, (p, w))) (ULift.ext (Subtype.ext ?_))
  simp [hg', TopCat.coe_diskBoundaryInclusion_apply_down, TopCat.coe_annulusDir, hy, hz, norm_smul]

/-- For `1/2 ≤ ‖x‖`, the composite of the reattachment maps along `K` and `K'` sends the point `x`
of the `i`-th cell to the point `K i (2 - 2‖x‖, x/‖x‖)` of `A`: `E` sends it there, and `E'` is the
identity on `P × A`. -/
private theorem collarCell_of_half_le_norm (i : ι) (p : P) {x z : TopCat.disk.{u} (k i)}
    (hx : 1 / 2 ≤ ‖x.down.1‖)
    (hz : z.down.1 = ((3 / 2 - ‖x.down.1‖) / ‖x.down.1‖) • x.down.1) :
    collarCell α₁ i (reattachmentBoundaryHomotopy χ₀ χ₁ h K hK i)
        (reattachmentBoundaryHomotopy_zero α₁ χ₀ χ₁ hχ₁ h K hK i) (p, z) =
      fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK'
        (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK
          (fiberwiseCellAttachmentCell α₁ i (p, x))) := by
  have hx₀ : 0 < ‖x.down.1‖ := by linarith
  have h₃ : 0 < 3 / 2 - ‖x.down.1‖ := by linarith [mem_closedBall_zero_iff.1 x.down.2]
  have hnz : ‖z.down.1‖ = 3 / 2 - ‖x.down.1‖ := by
    rw [hz, norm_smul, Real.norm_of_nonneg (div_nonneg h₃.le hx₀.le), div_mul_cancel₀ _ hx₀.ne']
  have hz₂ : 1 / 2 ≤ ‖z.down.1‖ := by rw [hnz]; linarith [mem_closedBall_zero_iff.1 x.down.2]
  have hθ : (TopCat.annulusDir (by norm_num) ⟨x, hx⟩).down.1 = ‖z.down.1‖⁻¹ • z.down.1 := by
    have hc : (3 / 2 - ‖x.down.1‖)⁻¹ * ((3 / 2 - ‖x.down.1‖) / ‖x.down.1‖) = ‖x.down.1‖⁻¹ := by
      rw [mul_div_assoc', inv_mul_cancel₀ h₃.ne', one_div]
    rw [TopCat.coe_annulusDir, hnz, hz, smul_smul, hc]
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hx)
      (ht := TopCat.coe_reattachmentTime_of_le_norm hx)
      (hs := TopCat.coe_annulusDir (by norm_num) ⟨x, hx⟩),
    fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
    collarCell_of_le_norm _ p hz₂ (t := TopCat.reattachmentTime x)
      (by rw [TopCat.coe_reattachmentTime_of_le_norm hx, hnz]; ring)
      hθ]
  exact congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₁ (p, a))
    (Subtype.ext (coe_reattachmentBoundaryHomotopy_apply χ₀ χ₁ h K hK i _ p _).symm)

include hg hg' hKK' in
/-- At time `0` the fold path, read in the cell with a collar along `K i`, is the composite of the
reattachment map along `K` and the reattachment map along `K'`. -/
private theorem collarCell_reattachmentFoldPath_zero (i : ι) (p : P) (x : TopCat.disk.{u} (k i)) :
    collarCell α₁ i (reattachmentBoundaryHomotopy χ₀ χ₁ h K hK i)
        (reattachmentBoundaryHomotopy_zero α₁ χ₀ χ₁ hχ₁ h K hK i)
        (p, TopCat.reattachmentFoldPath (0, x)) =
      fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK'
        (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK
          (fiberwiseCellAttachmentCell α₁ i (p, x))) := by
  rcases le_total ‖x.down.1‖ (1 / 2) with hx | hx
  · have hz := TopCat.coe_reattachmentFoldPath_zero_of_norm_le hx
    rcases le_total ‖x.down.1‖ (1 / 4) with hx' | hx'
    · exact collarCell_of_norm_le_quarter α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ g h h' hg hg' hh hh' K hK K' hK' i p
        hx' hz
    · exact collarCell_of_quarter_le_norm_le_half α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ g h h' hg hg' hh hh' K hK K'
        hK' hKK' i p hx' hx hz
  · exact collarCell_of_half_le_norm α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h h' hh hh' K hK K' hK' i p hx
      (TopCat.coe_reattachmentFoldPath_zero_of_le_norm hx)

/-- The fold path read in the cell with a collar along `K i`, on the `i`-th family of discs: a
homotopy from the composite of the reattachment maps along `K` and `K'` at time `0` to the identity
at time `1`. -/
private def reattachmentInvCylinder (i : ι) :
    C(I × (P × TopCat.disk.{u} (k i)), fiberwiseCellAttachment α₁) :=
  (collarCell α₁ i (reattachmentBoundaryHomotopy χ₀ χ₁ h K hK i)
      (reattachmentBoundaryHomotopy_zero α₁ χ₀ χ₁ hχ₁ h K hK i)).comp
    ⟨fun q ↦ (q.2.1, TopCat.reattachmentFoldPath (q.1, q.2.2)),
      (continuous_fst.comp continuous_snd).prodMk (TopCat.continuous_reattachmentFoldPath.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))⟩

private theorem reattachmentInvCylinder_apply (i : ι) (t : I) (x : P × TopCat.disk.{u} (k i)) :
    reattachmentInvCylinder α₁ χ₀ χ₁ hχ₁ h K hK i (t, x) =
      collarCell α₁ i (reattachmentBoundaryHomotopy χ₀ χ₁ h K hK i)
        (reattachmentBoundaryHomotopy_zero α₁ χ₀ χ₁ hχ₁ h K hK i)
        (x.1, TopCat.reattachmentFoldPath (t, x.2)) :=
  rfl

/-- The collar homotopy is constant on the boundary spheres, at the attaching maps. -/
private theorem reattachmentInvCylinder_diskBoundaryInclusion (i : ι) (t : I) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    reattachmentInvCylinder α₁ χ₀ χ₁ hχ₁ h K hK i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
      fiberwiseCellAttachmentIncl α₁ (p, α₁ i (p, s)) := by
  rw [reattachmentInvCylinder_apply,
    collarCell_of_eq_half_smul _ p (TopCat.coe_reattachmentFoldPath_diskBoundaryInclusion t s),
    fiberwiseCellAttachmentCell_diskBoundaryInclusion]

include hg hg' hKK' in
/-- The homotopy from the composite of the reattachment maps along `K` and `K'` to the identity,
relative to `P × A` and over `P`. -/
private theorem exists_homotopyRel_fiberwiseCellReattachment_comp_id :
    ∃ G : (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫
        fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK').hom.HomotopyRel
        (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₁)),
      ∀ t y, fiberwiseCellAttachmentProj α₁ (G (t, y)) = fiberwiseCellAttachmentProj α₁ y := by
  set E := fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK
  set E' := fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK'
  let L : C(I × (P × A), fiberwiseCellAttachment α₁) :=
    (fiberwiseCellAttachmentIncl α₁).hom.comp ContinuousMap.snd
  let F := fiberwiseCellAttachmentCylinderDesc α₁ L
    (reattachmentInvCylinder α₁ χ₀ χ₁ hχ₁ h K hK)
    (reattachmentInvCylinder_diskBoundaryInclusion α₁ χ₀ χ₁ hχ₁ h K hK)
  have hFincl (t : I) (x : P × A) : F (t, fiberwiseCellAttachmentIncl α₁ x) =
      fiberwiseCellAttachmentIncl α₁ x :=
    fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ _ _ t x
  have hFcell (t : I) (i : ι) (x : P × TopCat.disk.{u} (k i)) :
      F (t, fiberwiseCellAttachmentCell α₁ i x) =
        reattachmentInvCylinder α₁ χ₀ χ₁ hχ₁ h K hK i (t, x) :=
    fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell α₁ _ _ _ t i x
  have hEE' (x : P × A) : (E ≫ E') (fiberwiseCellAttachmentIncl α₁ x) =
      fiberwiseCellAttachmentIncl α₁ x := by
    rw [ConcreteCategory.comp_apply, fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]
  refine ⟨
    { toFun := F
      continuous_toFun := F.continuous
      map_zero_left := fun y ↦ ?_
      map_one_left := fun y ↦ ?_
      prop' := fun t y hy ↦ ?_ }, fun t y ↦ ?_⟩
  · refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · rw [hFincl]
      exact (hEE' x).symm
    · rw [hFcell, reattachmentInvCylinder_apply]
      exact collarCell_reattachmentFoldPath_zero α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ g h h' hg hg' hh hh' K hK K'
        hK' hKK' i x.1 x.2
  · refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact hFincl 1 x
    · rw [hFcell, reattachmentInvCylinder_apply,
        collarCell_of_eq_half_smul _ x.1 (TopCat.coe_reattachmentFoldPath_one x.2)]
      rfl
  · obtain ⟨x, rfl⟩ := hy
    exact (hFincl t x).trans (hEE' x).symm
  · refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact congrArg _ (hFincl t x)
    · refine (congrArg _ (hFcell t i x)).trans ?_
      rw [reattachmentInvCylinder_apply, fiberwiseCellAttachmentProj_collarCell,
        fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]

include hg hg' hKK' in
/-- **Reattaching along a homotopy and along its reverse are mutually inverse.** Let the self-maps
`h i (p, ·)` of the discs be the linear isometries `g i p`, let `h' i (p, ·)` be their inverses,
and let `K' i (t, (p, w)) = K i (1 - t, (p, h' i (p, w)))` be the reverse of the homotopy
`K i : χ₁ i ≃ χ₀ i ∘ h i`, a homotopy `χ₀ i ≃ χ₁ i ∘ h' i`. Then the fiberwise reattachment maps
`E` along `K` and `E'` along `K'` are mutually inverse up to homotopy relative to `P × A`, by
homotopies over `P`. No left inverse of a comparison map is needed. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment_id :
    (∃ G : (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫
        fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK').hom.HomotopyRel
        (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₁)),
      ∀ t y, fiberwiseCellAttachmentProj α₁ (G (t, y)) = fiberwiseCellAttachmentProj α₁ y) ∧
    ∃ G : (fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK' ≫
        fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK).hom.HomotopyRel
        (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₀)),
      ∀ t y, fiberwiseCellAttachmentProj α₀ (G (t, y)) = fiberwiseCellAttachmentProj α₀ y := by
  -- `K` is in turn the reverse of `K'`, through the isometries `(g i p)⁻¹`.
  have hK'K (i : ι) (t : I) (p : P) (w : TopCat.disk.{u} (k i)) :
      K i (t, (p, w)) = K' i (σ t, (p, h i (p, w))) := by
    rw [hKK', symm_symm]
    exact congrArg (fun w ↦ K i (t, (p, w)))
      (ULift.ext (Subtype.ext (by rw [hg', hg, LinearIsometryEquiv.symm_apply_apply]))).symm
  exact ⟨exists_homotopyRel_fiberwiseCellReattachment_comp_id α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ g h h' hg hg'
    hh hh' K hK K' hK' hKK', exists_homotopyRel_fiberwiseCellReattachment_comp_id α₁ α₀ χ₁ χ₀ hχ₁
      hχ₀ (fun i p ↦ (g i p).symm) h' h hg' hg hh' hh K' hK' K hK hK'K⟩

/-- **The fiberwise reattachment map as a fibre homotopy equivalence over `P`.** When the self-maps
`h i (p, ·)` of the discs are the linear isometries `g i p`, the fiberwise reattachment map along
`K` is a fibre homotopy equivalence over `P`, with inverse the reattachment map along the reverse
homotopies `K'`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment_id`). -/
def fiberwiseCellReattachmentFiberHomotopyEquiv :
    FiberHomotopyEquiv (fiberwiseCellAttachmentProj α₁).hom
      (fiberwiseCellAttachmentProj α₀).hom where
  toFun := (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK).hom
  invFun := (fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK').hom
  comp_toFun := ContinuousMap.ext fun _ ↦ fiberwiseCellAttachmentProj_fiberwiseCellReattachment ..
  comp_invFun := ContinuousMap.ext fun _ ↦ fiberwiseCellAttachmentProj_fiberwiseCellReattachment ..
  left_inv := by
    obtain ⟨G, hG⟩ :=
      (exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment_id
        α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ g h h' hg hg' hh hh' K hK K' hK' hKK').1
    exact ⟨{ toHomotopy := G.toHomotopy, prop' := fun t ↦ ContinuousMap.ext (hG t) }⟩
  right_inv := by
    obtain ⟨G, hG⟩ :=
      (exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment_id
        α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ g h h' hg hg' hh hh' K hK K' hK' hKK').2
    exact ⟨{ toHomotopy := G.toHomotopy, prop' := fun t ↦ ContinuousMap.ext (hG t) }⟩

@[simp]
theorem fiberwiseCellReattachmentFiberHomotopyEquiv_toFun :
    (fiberwiseCellReattachmentFiberHomotopyEquiv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ g h h' hg hg' hh hh' K hK K'
      hK' hKK').toFun = (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK).hom :=
  (rfl)

@[simp]
theorem fiberwiseCellReattachmentFiberHomotopyEquiv_invFun :
    (fiberwiseCellReattachmentFiberHomotopyEquiv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ g h h' hg hg' hh hh' K hK K'
      hK' hKK').invFun = (fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK').hom :=
  (rfl)

end Inverse

section IsometryFamily

variable (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (χ₀ χ₁ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (g : ∀ i, P → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)))
  (hg : ∀ i, Continuous fun p ↦
    (g i p : EuclideanSpace ℝ (Fin (k i)) →L[ℝ] EuclideanSpace ℝ (Fin (k i))))
  (K : ∀ i, (χ₁ i).Homotopy
    ((χ₀ i).comp (ContinuousMap.fst.prodMk (diskMapFamily (g i) (hg i)))))
  (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)

/-- The disk maps of the inverses `(g i p)⁻¹`, given their continuity in the operator norm. -/
private abbrev diskMapFamilyInv
    (hg' : ∀ i, Continuous fun p ↦
      ((g i p).symm : EuclideanSpace ℝ (Fin (k i)) →L[ℝ] EuclideanSpace ℝ (Fin (k i)))) (i : ι) :
    C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)) :=
  diskMapFamily (fun p ↦ (g i p).symm) (hg' i)

private theorem comp_diskMapFamily_comp_diskMapFamilyInv
    (hg' : ∀ i, Continuous fun p ↦
      ((g i p).symm : EuclideanSpace ℝ (Fin (k i)) →L[ℝ] EuclideanSpace ℝ (Fin (k i)))) (i : ι) :
    ((χ₀ i).comp (ContinuousMap.fst.prodMk (diskMapFamily (g i) (hg i)))).comp
      (ContinuousMap.fst.prodMk (diskMapFamilyInv g hg' i)) = χ₀ i := by
  ext q
  have hw : diskMapFamily (g i) (hg i) (q.1, diskMapFamilyInv g hg' i q) = q.2 := by
    refine ULift.ext (Subtype.ext ?_)
    rw [diskMapFamily_apply, LinearIsometryEquiv.coe_diskMap_apply_down,
      diskMapFamily_apply, LinearIsometryEquiv.coe_diskMap_apply_down]
    exact (g i q.1).apply_symm_apply _
  simp only [ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.fst_apply, hw]

/-- The reverse `(t, (p, w)) ↦ K i (1 - t, (p, (g i p)⁻¹ w))` of the homotopy `K i`: a homotopy
`χ₀ i ≃ χ₁ i ∘ (g i)⁻¹`. -/
private def reverseHomotopy
    (hg' : ∀ i, Continuous fun p ↦
      ((g i p).symm : EuclideanSpace ℝ (Fin (k i)) →L[ℝ] EuclideanSpace ℝ (Fin (k i)))) (i : ι) :
    (χ₀ i).Homotopy ((χ₁ i).comp (ContinuousMap.fst.prodMk (diskMapFamilyInv g hg' i))) :=
  ((K i).symm.compContinuousMap (ContinuousMap.fst.prodMk (diskMapFamilyInv g hg' i))).cast
    (comp_diskMapFamily_comp_diskMapFamilyInv χ₀ g hg hg' i) rfl

include hK in
/-- The reverse homotopies keep the boundary spheres in `A`. -/
private theorem reverseHomotopy_mem
    (hg' : ∀ i, Continuous fun p ↦
      ((g i p).symm : EuclideanSpace ℝ (Fin (k i)) →L[ℝ] EuclideanSpace ℝ (Fin (k i)))) (i : ι)
    (t : I) (p : P) (s : TopCat.diskBoundary.{u} (k i)) :
    reverseHomotopy χ₀ χ₁ g hg K hg' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A := by
  have e : reverseHomotopy χ₀ χ₁ g hg K hg' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
      K i (σ t, (p, (g i p).symm.diskMap (TopCat.diskBoundaryInclusion (k i) s))) :=
    congrArg (fun w ↦ K i (σ t, (p, w))) (diskMapFamily_apply _ _ _)
  rw [e, LinearIsometryEquiv.diskMap_diskBoundaryInclusion]
  exact hK i (σ t) p _

include hK in
/-- **Cell attachments with characteristic maps homotopic up to isometries are fibre homotopy
equivalent.** Let `g i p` be linear isometries of `ℝ^{k i}`, continuous in `p` in the operator
norm, and let `K i : χ₁ i ≃ χ₀ i ∘ (p, g i p)` be homotopies of
families of characteristic maps keeping the boundary spheres in `A`. Then there is a fibre homotopy
equivalence over `P` from the attachment along `α₁` to the attachment along `α₀` which is the
identity on `P × A` in both directions, whose composite with the comparison map `Φ₀` is homotopic
to `Φ₁`, and whose two composites are homotopic to the identities, all by homotopies relative to
`P × A` which stay over `P`. It is the fiberwise reattachment map along `K`, with inverse the
reattachment map along the reverse homotopies `(t, (p, w)) ↦ K i (1 - t, (p, (g i p)⁻¹ w))`. -/
theorem exists_fiberHomotopyEquiv_fiberwiseCellAttachment_of_homotopy :
    ∃ Ψ : FiberHomotopyEquiv (fiberwiseCellAttachmentProj α₁).hom
        (fiberwiseCellAttachmentProj α₀).hom,
      (∀ x, Ψ.toFun (fiberwiseCellAttachmentIncl α₁ x) = fiberwiseCellAttachmentIncl α₀ x) ∧
      (∀ x, Ψ.invFun (fiberwiseCellAttachmentIncl α₀ x) = fiberwiseCellAttachmentIncl α₁ x) ∧
      (∃ G : ((fiberwiseCellComparison α₀ χ₀ hχ₀).hom.comp Ψ.toFun).HomotopyRel
          (fiberwiseCellComparison α₁ χ₁ hχ₁).hom (range (fiberwiseCellAttachmentIncl α₁)),
        ∀ t y, (G (t, y)).1 = fiberwiseCellAttachmentProj α₁ y) ∧
      (∃ G : (Ψ.invFun.comp Ψ.toFun).HomotopyRel (ContinuousMap.id _)
          (range (fiberwiseCellAttachmentIncl α₁)),
        ∀ t y, fiberwiseCellAttachmentProj α₁ (G (t, y)) = fiberwiseCellAttachmentProj α₁ y) ∧
      ∃ G : (Ψ.toFun.comp Ψ.invFun).HomotopyRel (ContinuousMap.id _)
          (range (fiberwiseCellAttachmentIncl α₀)),
        ∀ t y, fiberwiseCellAttachmentProj α₀ (G (t, y)) = fiberwiseCellAttachmentProj α₀ y := by
  -- The inverse isometries are continuous in the operator norm, as the isometry group is a
  -- topological group.
  have hg' (i : ι) : Continuous fun p ↦
      ((g i p).symm : EuclideanSpace ℝ (Fin (k i)) →L[ℝ] EuclideanSpace ℝ (Fin (k i))) := by
    open scoped TauCeti.LinearIsometryEquivOperatorNorm in
    exact LinearIsometryEquiv.continuous_operatorNorm_iff.1
      (LinearIsometryEquiv.continuous_operatorNorm_iff.2 (hg i)).inv
  let h' := diskMapFamilyInv g hg'
  have hh (i : ι) := mapsTo_diskMapFamily_range_diskBoundaryInclusion (g i) (hg i)
  have hh' (i : ι) := mapsTo_diskMapFamily_range_diskBoundaryInclusion _ (hg' i)
  have hgh (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
      (diskMapFamily (g i) (hg i) (p, w)).down.1 = g i p w.down.1 := by
    rw [diskMapFamily_apply, LinearIsometryEquiv.coe_diskMap_apply_down]
  have hgh' (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
      (h' i (p, w)).down.1 = (g i p).symm w.down.1 := by
    rw [diskMapFamily_apply, LinearIsometryEquiv.coe_diskMap_apply_down]
  have hK' := reverseHomotopy_mem χ₀ χ₁ g hg K hK hg'
  refine ⟨fiberwiseCellReattachmentFiberHomotopyEquiv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ g _ h' hgh hgh' hh hh' K
    hK _ hK' fun _ _ _ _ ↦ rfl, ?_⟩
  -- The forward and backward maps of the equivalence are, by definition, the reattachment maps
  -- along `K` and its reverse.
  exact ⟨fun _ ↦ fiberwiseCellReattachment_fiberwiseCellAttachmentIncl ..,
    fun _ ↦ fiberwiseCellReattachment_fiberwiseCellAttachmentIncl ..,
    ⟨fiberwiseCellReattachmentHomotopy .., fun _ _ ↦ fst_fiberwiseCellReattachmentHomotopy ..⟩,
    exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment_id α₀ α₁ χ₀ χ₁ hχ₀
      hχ₁ g _ h' hgh hgh' hh hh' K hK _ hK' fun _ _ _ _ ↦ rfl⟩

end IsometryFamily

section BaseChange

variable {P' : Type u} [TopologicalSpace P'] (g : C(P', P))

section Map

variable (α : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (α' : ∀ i, C(P' × TopCat.diskBoundary.{u} (k i), A)) (hα : ∀ i p s, α' i (p, s) = α i (g p, s))

/-- The map of fiberwise adjunction spaces over a map `g : P' → P` of parameter spaces, for
families of attaching maps `α' i (p, s) = α i (g p, s)` restricted along `g`: it is `g × id` on
`P' × A` and on each family of discs. For the inclusion of a subspace `P' ⊆ P`, it includes the
attachment of the restricted families into the attachment over `P`. -/
def fiberwiseCellAttachmentMap : fiberwiseCellAttachment α' ⟶ fiberwiseCellAttachment α :=
  fiberwiseCellAttachmentDesc α'
    (TopCat.ofHom (g.prodMap (ContinuousMap.id A)) ≫ fiberwiseCellAttachmentIncl α)
    (fun i ↦ TopCat.ofHom (g.prodMap (ContinuousMap.id _)) ≫ fiberwiseCellAttachmentCell α i)
    fun i p s ↦ by
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hα]
      exact fiberwiseCellAttachmentCell_diskBoundaryInclusion α i (g p) s

@[simp]
theorem fiberwiseCellAttachmentMap_fiberwiseCellAttachmentIncl (x : P' × A) :
    fiberwiseCellAttachmentMap g α α' hα (fiberwiseCellAttachmentIncl α' x) =
      fiberwiseCellAttachmentIncl α (g x.1, x.2) :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentIncl_desc α' _ _ _) x

@[simp]
theorem fiberwiseCellAttachmentMap_fiberwiseCellAttachmentCell (i : ι)
    (x : P' × TopCat.disk.{u} (k i)) :
    fiberwiseCellAttachmentMap g α α' hα (fiberwiseCellAttachmentCell α' i x) =
      fiberwiseCellAttachmentCell α i (g x.1, x.2) :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentCell_desc α' _ _ _ i) x

/-- The map of fiberwise adjunction spaces lies over `g`. -/
@[simp]
theorem fiberwiseCellAttachmentProj_fiberwiseCellAttachmentMap (y : fiberwiseCellAttachment α') :
    fiberwiseCellAttachmentProj α (fiberwiseCellAttachmentMap g α α' hα y) =
      g (fiberwiseCellAttachmentProj α' y) :=
  fiberwiseCellAttachment_induction α'
    (fun x ↦ by rw [fiberwiseCellAttachmentMap_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl])
    (fun i x ↦ by rw [fiberwiseCellAttachmentMap_fiberwiseCellAttachmentCell,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]) y

/-- The map of fiberwise adjunction spaces over the identity of `P` is the identity. -/
@[simp]
theorem fiberwiseCellAttachmentMap_id
    (hα : ∀ i p s, α i (p, s) = α i (ContinuousMap.id P p, s)) :
    fiberwiseCellAttachmentMap (ContinuousMap.id P) α α hα = 𝟙 _ := by
  refine fiberwiseCellAttachment_hom_ext α (fun x ↦ ?_) fun i x ↦ ?_
  · rw [fiberwiseCellAttachmentMap_fiberwiseCellAttachmentIncl, ContinuousMap.id_apply,
      ConcreteCategory.id_apply]
  · rw [fiberwiseCellAttachmentMap_fiberwiseCellAttachmentCell, ContinuousMap.id_apply,
      ConcreteCategory.id_apply]

/-- Maps of fiberwise adjunction spaces compose along composites of parameter maps. -/
@[reassoc (attr := simp)]
theorem fiberwiseCellAttachmentMap_comp {P'' : Type u} [TopologicalSpace P''] (g' : C(P'', P'))
    (α'' : ∀ i, C(P'' × TopCat.diskBoundary.{u} (k i), A))
    (hα' : ∀ i p s, α'' i (p, s) = α' i (g' p, s)) :
    fiberwiseCellAttachmentMap g' α' α'' hα' ≫ fiberwiseCellAttachmentMap g α α' hα =
      fiberwiseCellAttachmentMap (g.comp g') α α''
        (fun i p s ↦ (hα' i p s).trans (hα i (g' p) s)) := by
  refine fiberwiseCellAttachment_hom_ext α'' (fun x ↦ ?_) fun i x ↦ ?_
  · rw [ConcreteCategory.comp_apply, fiberwiseCellAttachmentMap_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentMap_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentMap_fiberwiseCellAttachmentIncl, ContinuousMap.comp_apply]
  · rw [ConcreteCategory.comp_apply, fiberwiseCellAttachmentMap_fiberwiseCellAttachmentCell,
      fiberwiseCellAttachmentMap_fiberwiseCellAttachmentCell,
      fiberwiseCellAttachmentMap_fiberwiseCellAttachmentCell, ContinuousMap.comp_apply]

/-- The map of fiberwise adjunction spaces over `g` intertwines the comparison maps of
characteristic families `χ' i (p, x) = χ i (g p, x)` restricted along `g`. -/
theorem fiberwiseCellComparison_fiberwiseCellAttachmentMap
    (χ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
    (hχ : ∀ i p s, χ i (p, TopCat.diskBoundaryInclusion (k i) s) = α i (p, s))
    (χ' : ∀ i, C(P' × TopCat.disk.{u} (k i), Y))
    (hχ' : ∀ i p s, χ' i (p, TopCat.diskBoundaryInclusion (k i) s) = α' i (p, s))
    (hχχ' : ∀ i p x, χ' i (p, x) = χ i (g p, x)) (y : fiberwiseCellAttachment α') :
    fiberwiseCellComparison α χ hχ (fiberwiseCellAttachmentMap g α α' hα y) =
      (g (fiberwiseCellComparison α' χ' hχ' y).1, (fiberwiseCellComparison α' χ' hχ' y).2) :=
  fiberwiseCellAttachment_induction α'
    (fun x ↦ by rw [fiberwiseCellAttachmentMap_fiberwiseCellAttachmentIncl,
      fiberwiseCellComparison_fiberwiseCellAttachmentIncl,
      fiberwiseCellComparison_fiberwiseCellAttachmentIncl])
    (fun i x ↦ by rw [fiberwiseCellAttachmentMap_fiberwiseCellAttachmentCell,
      fiberwiseCellComparison_fiberwiseCellAttachmentCell,
      fiberwiseCellComparison_fiberwiseCellAttachmentCell, hχχ']) y

end Map

variable (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (χ₀ χ₁ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (h : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hh : ∀ i p, MapsTo (fun w ↦ h i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))))
  (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (α₀' α₁' : ∀ i, C(P' × TopCat.diskBoundary.{u} (k i), A))
  (χ₀' χ₁' : ∀ i, C(P' × TopCat.disk.{u} (k i), Y))
  (hχ₀' : ∀ i p s, χ₀' i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀' i (p, s))
  (hχ₁' : ∀ i p s, χ₁' i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁' i (p, s))
  (h' : ∀ i, C(P' × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hh' : ∀ i p, MapsTo (fun w ↦ h' i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (K' : ∀ i, (χ₁' i).Homotopy ((χ₀' i).comp (ContinuousMap.fst.prodMk (h' i))))
  (hK' : ∀ i t p s, K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (hα₀ : ∀ i p s, α₀' i (p, s) = α₀ i (g p, s)) (hα₁ : ∀ i p s, α₁' i (p, s) = α₁ i (g p, s))

/-- **The fiberwise reattachment map is natural in the parameter space.** Let `g : P' → P` be
continuous, and restrict along `g` the data of a fiberwise reattachment map over `P`: the attaching
maps, the self-maps `h' i (p, x) = h i (g p, x)` of the discs and the homotopies
`K' i (t, (p, x)) = K i (t, (g p, x))`. Then the reattachment map over `P'` of the restricted data,
followed by the map of fiberwise adjunction spaces over `g`, is the map over `g` followed by the
reattachment map over `P`. -/
theorem fiberwiseCellReattachment_comp_fiberwiseCellAttachmentMap
    (hh'h : ∀ i p x, h' i (p, x) = h i (g p, x))
    (hK'K : ∀ i t p x, K' i (t, (p, x)) = K i (t, (g p, x))) :
    fiberwiseCellReattachment α₀' α₁' χ₀' χ₁' hχ₀' hχ₁' h' hh' K' hK' ≫
        fiberwiseCellAttachmentMap g α₀ α₀' hα₀ =
      fiberwiseCellAttachmentMap g α₁ α₁' hα₁ ≫
        fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK := by
  refine fiberwiseCellAttachment_hom_ext α₁' (fun x ↦ ?_) fun i x ↦ ?_
  · rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentMap_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentMap_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]
  obtain ⟨p, w⟩ := x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    fiberwiseCellAttachmentMap_fiberwiseCellAttachmentCell]
  rcases le_total ‖w.down.1‖ (1 / 2) with hw | hw
  · have hv := TopCat.coe_reattachmentRadial_of_norm_le hw
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hw) (hv := hv),
      fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hw) (hv := hv),
      fiberwiseCellAttachmentMap_fiberwiseCellAttachmentCell, hh'h]
  · obtain ⟨s, hs⟩ : ∃ s : TopCat.diskBoundary.{u} (k i), s.down.1 = ‖w.down.1‖⁻¹ • w.down.1 :=
      ⟨TopCat.annulusDir (by norm_num) ⟨w, hw⟩, TopCat.coe_annulusDir _ _⟩
    obtain ⟨t, ht⟩ : ∃ t : I, (t : ℝ) = 2 - 2 * ‖w.down.1‖ :=
      ⟨TopCat.reattachmentTime w, TopCat.coe_reattachmentTime_of_le_norm hw⟩
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hw) (ht := ht)
        (hs := hs),
      fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hw) (ht := ht)
        (hs := hs),
      fiberwiseCellAttachmentMap_fiberwiseCellAttachmentIncl]
    exact congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₀ (g p, a)) (Subtype.ext (hK'K i t p _))

/-- **The homotopy `Φ₀ ∘ E ≃ Φ₁` is natural in the parameter space.** For data restricted along a
continuous map `g : P' → P`, with `K' i (t, (p, x)) = K i (t, (g p, x))`, the homotopy over `P`
read on the image of the map of fiberwise adjunction spaces over `g` is the homotopy over `P'`
followed by `g × id`. -/
theorem fiberwiseCellReattachmentHomotopy_fiberwiseCellAttachmentMap
    (hK'K : ∀ i t p x, K' i (t, (p, x)) = K i (t, (g p, x))) (t : I)
    (y : fiberwiseCellAttachment α₁') :
    fiberwiseCellReattachmentHomotopy α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK
        (t, fiberwiseCellAttachmentMap g α₁ α₁' hα₁ y) =
      (g (fiberwiseCellReattachmentHomotopy α₀' α₁' χ₀' χ₁' hχ₀' hχ₁' h' hh' K' hK' (t, y)).1,
        (fiberwiseCellReattachmentHomotopy α₀' α₁' χ₀' χ₁' hχ₀' hχ₁' h' hh' K' hK' (t, y)).2) := by
  refine fiberwiseCellAttachment_induction α₁' (fun x ↦ ?_) (fun i x ↦ ?_) y
  · rw [fiberwiseCellAttachmentMap_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachmentHomotopy_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachmentHomotopy_fiberwiseCellAttachmentIncl]
  · rw [fiberwiseCellAttachmentMap_fiberwiseCellAttachmentCell,
      fiberwiseCellReattachmentHomotopy_fiberwiseCellAttachmentCell,
      fiberwiseCellReattachmentHomotopy_fiberwiseCellAttachmentCell, hK'K]

end BaseChange

end TauCeti

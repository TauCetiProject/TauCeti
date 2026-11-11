/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk.Reattachment
public import TauCeti.Topology.Category.TopCat.Pushout
import TauCeti.Topology.Category.TopCat.OpenEmbedding

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
comparison maps `Φ₀` and `Φ₁`.

When each `h i (p, ·)` is a linear isometry `e i p` of the disc, as for the polar factors in
Milnor's comparison of two charts, `E` is a homotopy equivalence over `P` relative to `P × A`. Its
inverse (`TauCeti.fiberwiseCellReattachmentInv`) is the reattachment map of the inverse isometries
`(e i p)⁻¹` and of the reversed homotopies `(t, (p, x)) ↦ K i (1 - t, (p, (e i p)⁻¹ x))`, and both
composites are homotopic to the identity relative to `P × A` through maps over `P`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachmentInv`,
`TauCeti.exists_homotopyRel_fiberwiseCellReattachmentInv_comp_fiberwiseCellReattachment`). On the
`i`-th cell, `E` followed by its inverse is `x ↦ 4x` on the disc of radius `1/4`, while on the
annulus `1/4 ≤ ‖x‖` it runs out along `K i` and back. Contracting this out-and-back track, and then
undoing the radial push of radius `1/4`, gives the homotopy. The construction uses no left inverse
of the comparison map `Φ₀`.

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

section Inverse

/-- The time `(1 - u) · min (3s) ((3 - 3s) / 2)`: for fixed `u` a tent in `s`, vanishing at both
ends, peaking at `s = 1/3`, and vanishing identically at `u = 1`. -/
private def reattachmentLoopTime (u s : I) : I :=
  projIcc 0 1 zero_le_one ((1 - (u : ℝ)) * min (3 * (s : ℝ)) ((3 - 3 * (s : ℝ)) / 2))

private theorem continuous_reattachmentLoopTime :
    Continuous fun q : I × I ↦ reattachmentLoopTime q.1 q.2 :=
  continuous_projIcc.comp ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).min
      ((continuous_const.sub (continuous_const.mul
        (continuous_subtype_val.comp continuous_snd))).div_const _)))

private theorem coe_reattachmentLoopTime (u s : I) :
    (reattachmentLoopTime u s : ℝ) = (1 - (u : ℝ)) * min (3 * (s : ℝ)) ((3 - 3 * (s : ℝ)) / 2) := by
  have hu₀ : 0 ≤ (u : ℝ) := u.2.1
  have hu₁ : (u : ℝ) ≤ 1 := u.2.2
  have hs₀ : 0 ≤ (s : ℝ) := s.2.1
  have hs₁ : (s : ℝ) ≤ 1 := s.2.2
  have hm₀ : 0 ≤ min (3 * (s : ℝ)) ((3 - 3 * (s : ℝ)) / 2) := le_min (by linarith) (by linarith)
  have hm₁ : min (3 * (s : ℝ)) ((3 - 3 * (s : ℝ)) / 2) ≤ 1 := by
    rcases le_or_gt (s : ℝ) (1 / 3) with h | h
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  have h₀ : 0 ≤ (1 - (u : ℝ)) * min (3 * (s : ℝ)) ((3 - 3 * (s : ℝ)) / 2) :=
    mul_nonneg (by linarith) hm₀
  have h₁ : (1 - (u : ℝ)) * min (3 * (s : ℝ)) ((3 - 3 * (s : ℝ)) / 2) ≤ 1 :=
    (mul_le_of_le_one_left hm₀ (by linarith)).trans hm₁
  rw [reattachmentLoopTime, projIcc_of_mem _ ⟨h₀, h₁⟩]

private theorem reattachmentLoopTime_zero_right (u : I) : reattachmentLoopTime u 0 = 0 :=
  Subtype.ext (by rw [coe_reattachmentLoopTime]; norm_num)

private theorem reattachmentLoopTime_one_right (u : I) : reattachmentLoopTime u 1 = 0 :=
  Subtype.ext (by rw [coe_reattachmentLoopTime]; norm_num)

private theorem reattachmentLoopTime_one_left (s : I) : reattachmentLoopTime 1 s = 0 :=
  Subtype.ext (by rw [coe_reattachmentLoopTime]; norm_num)

/-- At `u = 0` and a point `w` of the annulus `1/4 ≤ ‖w‖`, the time is the tent `4‖w‖ - 1` on
`‖w‖ ≤ 1/2` and `2 - 2‖w‖` on `1/2 ≤ ‖w‖`, that is, `min (4‖w‖ - 1) (2 - 2‖w‖)`. -/
private theorem coe_reattachmentLoopTime_zero_annulusParam {n : ℕ} {w : TopCat.disk.{u} n}
    (hw : 1 / 4 ≤ ‖w.down.1‖) :
    (reattachmentLoopTime 0 (TopCat.annulusParam (1 / 4) w) : ℝ) =
      min (4 * ‖w.down.1‖ - 1) (2 - 2 * ‖w.down.1‖) := by
  have h := TopCat.add_one_sub_mul_annulusParam (by norm_num : (1 / 4 : ℝ) ≤ 1) hw
  rw [coe_reattachmentLoopTime, Icc.coe_zero, sub_zero, one_mul]
  congr 1 <;> linarith

variable (α : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))

/-- The inclusion of the ball of radius `1/4` into the disk. -/
private def quarterBallInclusion (n : ℕ) :
    C(closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 4), TopCat.disk.{u} n) :=
  ⟨fun v ↦ (ULift.up ⟨v.1, closedBall_subset_closedBall (by norm_num) v.2⟩ : TopCat.disk.{u} n),
    continuous_uliftUp.comp (continuous_subtype_val.subtype_mk _)⟩

@[simp]
private theorem coe_quarterBallInclusion_apply_down {n : ℕ}
    (v : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 4)) :
    ((quarterBallInclusion.{u} n v).down : EuclideanSpace ℝ (Fin n)) = v :=
  rfl

/-- The radial push of radius `1/4` at time `1` of the point `(1/4) θ` of the disk is `θ`. -/
private theorem diskRadialPush_one_quarterBallInclusion {n : ℕ} (θ : TopCat.diskBoundary.{u} n) :
    TopCat.diskRadialPush.{u} n (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, quarterBallInclusion n
      ⟨(1 / 4 : ℝ) • θ.down.1, TopCat.smul_diskBoundary_mem_closedBall (by norm_num) θ⟩) =
      TopCat.diskBoundaryInclusion n θ := by
  have hθ := TopCat.smul_diskBoundary_mem_closedBall.{u} (by norm_num : (0 : ℝ) ≤ 1 / 4) θ
  have hx : ‖((quarterBallInclusion.{u} n ⟨(1 / 4 : ℝ) • θ.down.1, hθ⟩).down :
      EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 4 := by
    rw [coe_quarterBallInclusion_apply_down]
    exact mem_closedBall_zero_iff.1 hθ
  refine ULift.ext (Subtype.ext ?_)
  rw [TopCat.coe_diskRadialPush_one_of_norm_le _ hx, TopCat.coe_diskBoundaryInclusion_apply_down,
    coe_quarterBallInclusion_apply_down, smul_smul]
  norm_num

/-- The inner piece of `TauCeti.reattachmentLoop`: `(p, v) ↦ (p, 4v)` in the `i`-th cell, written
with the radial push of radius `1/4`. -/
private def reattachmentLoopInner (i : ι) :
    C((I × P) × closedBall (0 : EuclideanSpace ℝ (Fin (k i))) (1 / 4), fiberwiseCellAttachment α) :=
  ⟨fun q ↦ fiberwiseCellAttachmentCell α i (q.1.2, TopCat.diskRadialPush (k i)
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, quarterBallInclusion (k i) q.2)),
    (fiberwiseCellAttachmentCell α i).hom.continuous.comp
      ((continuous_snd.comp continuous_fst).prodMk
      ((TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4)).continuous.comp
        (continuous_const.prodMk ((quarterBallInclusion (k i)).continuous.comp continuous_snd))))⟩

variable {α} in
/-- The outer piece of `TauCeti.reattachmentLoop`: `(s, θ)` goes along the track `H` of `θ` for the
time `reattachmentLoopTime u s`, read in `P × A`. -/
private def reattachmentLoopOuter (i : ι) (H : C(I × (P × TopCat.diskBoundary.{u} (k i)), A)) :
    C((I × P) × (I × TopCat.diskBoundary.{u} (k i)), fiberwiseCellAttachment α) :=
  ⟨fun q ↦ fiberwiseCellAttachmentIncl α
      (q.1.2, H (reattachmentLoopTime q.1.1 q.2.1, (q.1.2, q.2.2))),
    (fiberwiseCellAttachmentIncl α).hom.continuous.comp ((continuous_snd.comp continuous_fst).prodMk
      (H.continuous.comp ((continuous_reattachmentLoopTime.comp
        ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))).prodMk
        ((continuous_snd.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd)))))⟩

/-- **The loop homotopy on a cell.** For a track `H : I × (P × ∂D^{k i}) → A` starting at the
attaching map `α i`, this is the map `I × (P × D^{k i}) → (P × A) ∪_α ⨆ᵢ (P × D^{k i})` sending
`(u, (p, w))` to the point `(p, 4w)` of the `i`-th cell when `‖w‖ ≤ 1/4`, and, when
`‖w‖ = 1/4 + 3s/4` with `s ∈ [0, 1]`, to the point `(p, H((1 - u) τ(s), (p, w/‖w‖)))` of `P × A`,
where `τ(s) = min (3s) ((3 - 3s)/2)`. At `u = 1` it is the `i`-th cell composed with the radial
push of radius `1/4`. -/
private def reattachmentLoop (i : ι) (H : C(I × (P × TopCat.diskBoundary.{u} (k i)), A))
    (hH : ∀ p s, H (0, (p, s)) = α i (p, s)) :
    C(I × (P × TopCat.disk.{u} (k i)), fiberwiseCellAttachment α) :=
  (TopCat.discGlue (by norm_num : (0 : ℝ) < 1 / 4) (reattachmentLoopInner α i)
    (reattachmentLoopOuter i H) fun q θ ↦ by
      simp only [reattachmentLoopOuter, reattachmentLoopInner, ContinuousMap.coe_mk,
        reattachmentLoopTime_zero_right, hH, diskRadialPush_one_quarterBallInclusion]
      exact (fiberwiseCellAttachmentCell_diskBoundaryInclusion α i q.2 θ).symm).comp
    ⟨fun q ↦ ((q.1, q.2.1), q.2.2),
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd)⟩

variable {α}

section Loop

variable {i : ι} {H : C(I × (P × TopCat.diskBoundary.{u} (k i)), A)}
  {hH : ∀ p s, H (0, (p, s)) = α i (p, s)}

private theorem reattachmentLoop_of_norm_le (t : I) (p : P) {w : TopCat.disk.{u} (k i)}
    (hw : ‖w.down.1‖ ≤ 1 / 4) :
    reattachmentLoop α i H hH (t, (p, w)) = fiberwiseCellAttachmentCell α i
      (p, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, w)) := by
  rw [reattachmentLoop, ContinuousMap.comp_apply]
  exact TopCat.discGlue_apply_of_norm_le _ _ _ _ (t, p) hw

private theorem reattachmentLoop_of_le_norm (t : I) (p : P) {w : TopCat.disk.{u} (k i)}
    (hw : 1 / 4 ≤ ‖w.down.1‖) :
    reattachmentLoop α i H hH (t, (p, w)) = fiberwiseCellAttachmentIncl α
      (p, H (reattachmentLoopTime t (TopCat.annulusParam (1 / 4) w),
        (p, TopCat.annulusDir (by norm_num) ⟨w, hw⟩))) := by
  rw [reattachmentLoop, ContinuousMap.comp_apply]
  exact TopCat.discGlue_apply_of_le_norm _ _ _ _ (t, p) hw

/-- On the boundary spheres the loop homotopy is the attaching map at all times. -/
private theorem reattachmentLoop_diskBoundaryInclusion (t : I) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    reattachmentLoop α i H hH (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
      fiberwiseCellAttachmentIncl α (p, α i (p, s)) := by
  have hw : 1 / 4 ≤ ‖(TopCat.diskBoundaryInclusion (k i) s).down.1‖ := by
    rw [TopCat.norm_diskBoundaryInclusion]
    norm_num
  rw [reattachmentLoop_of_le_norm t p hw, TopCat.annulusDir_diskBoundaryInclusion,
    TopCat.annulusParam_of_norm_eq_one (by norm_num) (TopCat.norm_diskBoundaryInclusion s),
    reattachmentLoopTime_one_right, hH]

/-- At time `1` the loop homotopy is the `i`-th cell composed with the radial push of radius
`1/4`. -/
private theorem reattachmentLoop_one (p : P) (w : TopCat.disk.{u} (k i)) :
    reattachmentLoop α i H hH (1, (p, w)) = fiberwiseCellAttachmentCell α i
      (p, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, w)) := by
  rcases le_total ‖w.down.1‖ (1 / 4) with hw | hw
  · exact reattachmentLoop_of_norm_le 1 p hw
  · rw [reattachmentLoop_of_le_norm 1 p hw, reattachmentLoopTime_one_left, hH,
      ← fiberwiseCellAttachmentCell_diskBoundaryInclusion, TopCat.diskBoundaryInclusion_annulusDir]

/-- The loop homotopy lies over `P`. -/
private theorem fiberwiseCellAttachmentProj_reattachmentLoop (t : I) (p : P)
    (w : TopCat.disk.{u} (k i)) :
    fiberwiseCellAttachmentProj α (reattachmentLoop α i H hH (t, (p, w))) = p := by
  rcases le_total ‖w.down.1‖ (1 / 4) with hw | hw
  · rw [reattachmentLoop_of_norm_le t p hw, fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]
  · rw [reattachmentLoop_of_le_norm t p hw, fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl]

end Loop

/-- **The loop homotopy followed by the radial unpush.** For a track `H` of the attaching map
`α i`, a homotopy over `P` from the loop homotopy at time `0` to the `i`-th cell, constant on the
boundary spheres. -/
private theorem exists_reattachmentLoopCylinder (i : ι)
    (H : C(I × (P × TopCat.diskBoundary.{u} (k i)), A)) (hH : ∀ p s, H (0, (p, s)) = α i (p, s)) :
    ∃ C : C(I × (P × TopCat.disk.{u} (k i)), fiberwiseCellAttachment α),
      (∀ x, C (0, x) = reattachmentLoop α i H hH (0, x)) ∧
      (∀ x, C (1, x) = fiberwiseCellAttachmentCell α i x) ∧
      (∀ t p s, C (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
        fiberwiseCellAttachmentIncl α (p, α i (p, s))) ∧
      ∀ t x, fiberwiseCellAttachmentProj α (C (t, x)) = x.1 := by
  have hr : (0 : ℝ) ≤ 1 / 4 := by norm_num
  let F₀ : C(P × TopCat.disk.{u} (k i), fiberwiseCellAttachment α) :=
    ⟨fun x ↦ reattachmentLoop α i H hH (0, x),
      (reattachmentLoop α i H hH).continuous.comp (continuous_const.prodMk continuous_id)⟩
  let F₁ : C(P × TopCat.disk.{u} (k i), fiberwiseCellAttachment α) :=
    ⟨fun x ↦ fiberwiseCellAttachmentCell α i (x.1, TopCat.diskRadialPush (k i) hr (1, x.2)),
      (fiberwiseCellAttachmentCell α i).hom.continuous.comp (continuous_fst.prodMk
        ((TopCat.diskRadialPush (k i) hr).continuous.comp
          (continuous_const.prodMk continuous_snd)))⟩
  let Θ₁ : F₀.Homotopy F₁ :=
    { toFun := reattachmentLoop α i H hH
      continuous_toFun := (reattachmentLoop α i H hH).continuous
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun x ↦ reattachmentLoop_one x.1 x.2 }
  let Θ₂ : F₁.Homotopy (fiberwiseCellAttachmentCell α i).hom :=
    { toFun := fun q ↦ fiberwiseCellAttachmentCell α i
        (q.2.1, TopCat.diskRadialPush (k i) hr (σ q.1, q.2.2))
      continuous_toFun := (fiberwiseCellAttachmentCell α i).hom.continuous.comp
        ((continuous_fst.comp continuous_snd).prodMk
          ((TopCat.diskRadialPush (k i) hr).continuous.comp
            ((continuous_symm.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))))
      map_zero_left := fun x ↦ by simp [F₁]
      map_one_left := fun x ↦ by simp [TopCat.diskRadialPush_zero] }
  refine ⟨(Θ₁.trans Θ₂).toContinuousMap, fun x ↦ (Θ₁.trans Θ₂).apply_zero x,
    fun x ↦ (Θ₁.trans Θ₂).apply_one x, fun t p s ↦ ?_, fun t x ↦ ?_⟩
  · rw [ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact reattachmentLoop_diskBoundaryInclusion (hH := hH) _ p s
    · -- Unfold the local homotopy `Θ₂`: the cell composed with the reversed radial push.
      change fiberwiseCellAttachmentCell α i (p, TopCat.diskRadialPush (k i) hr (_, _)) = _
      rw [TopCat.diskRadialPush_diskBoundaryInclusion (by norm_num) (by norm_num),
        fiberwiseCellAttachmentCell_diskBoundaryInclusion]
  · rw [ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact fiberwiseCellAttachmentProj_reattachmentLoop (hH := hH) _ x.1 x.2
    · exact fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell α i _


section Composite

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
  (K' : ∀ i, (χ₀ i).Homotopy ((χ₁ i).comp (ContinuousMap.fst.prodMk (h' i))))
  (hK' : ∀ i t p s, K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (e : ∀ i, P → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)))
  (he : ∀ i p w, ((h i (p, w)).down : EuclideanSpace ℝ (Fin (k i))) = e i p w.down)
  (he' : ∀ i p w, ((h' i (p, w)).down : EuclideanSpace ℝ (Fin (k i))) = (e i p).symm w.down)
  (hKK' : ∀ i t x, K' i (t, x) = K i (σ t, (x.1, h' i x)))

/-- The track `(t, (p, s)) ↦ K i (t, (p, s))` of the boundary spheres in `A`. -/
private def reattachmentTrack (i : ι) : C(I × (P × TopCat.diskBoundary.{u} (k i)), A) :=
  ⟨fun q ↦ ⟨K i (q.1, (q.2.1, TopCat.diskBoundaryInclusion (k i) q.2.2)), hK i _ _ _⟩,
    ((K i).continuous.comp (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
      ((TopCat.diskBoundaryInclusion (k i)).hom.continuous.comp
        (continuous_snd.comp continuous_snd))))).subtype_mk _⟩

private theorem reattachmentTrack_apply (i : ι) (q : I × (P × TopCat.diskBoundary.{u} (k i))) :
    reattachmentTrack χ₀ χ₁ h K hK i q =
      ⟨K i (q.1, (q.2.1, TopCat.diskBoundaryInclusion (k i) q.2.2)), hK i _ _ _⟩ :=
  rfl

include hχ₁ in
private theorem reattachmentTrack_zero (i : ι) (p : P) (s : TopCat.diskBoundary.{u} (k i)) :
    reattachmentTrack χ₀ χ₁ h K hK i (0, (p, s)) = α₁ i (p, s) :=
  Subtype.ext ((K i).apply_zero _ |>.trans (hχ₁ i p s))

include he he' hKK' in
/-- On the `i`-th cell, the composite of the two reattachment maps is the loop homotopy at time
`0`, built on the track of the boundary spheres along `K i`. -/
private theorem fiberwiseCellReattachment_fiberwiseCellReattachment_fiberwiseCellAttachmentCell
    (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK'
        (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK
          (fiberwiseCellAttachmentCell α₁ i (p, w))) =
      reattachmentLoop α₁ i (reattachmentTrack χ₀ χ₁ h K hK i)
        (reattachmentTrack_zero α₁ χ₀ χ₁ hχ₁ h K hK i) (0, (p, w)) := by
  -- the norm of `h i (p, v)` is that of `v`
  have hnorm : ∀ v : TopCat.disk.{u} (k i), ‖(h i (p, v)).down.1‖ = ‖v.down.1‖ := fun v ↦ by
    rw [he, LinearIsometryEquiv.norm_map]
  rcases le_total ‖w.down.1‖ (1 / 2) with hw₂ | hw₂
  · rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K
      hK i p hw₂ (TopCat.coe_reattachmentRadial_of_norm_le hw₂)]
    have hv : ‖(h i (p, TopCat.reattachmentRadial w)).down.1‖ = 2 * ‖w.down.1‖ := by
      rw [hnorm, TopCat.coe_reattachmentRadial_of_norm_le hw₂, norm_smul, Real.norm_two]
    rcases le_total ‖w.down.1‖ (1 / 4) with hw₄ | hw₄
    · -- On the ball of radius `1/4` the composite is `x ↦ 4x`.
      have hv₂ : ‖(h i (p, TopCat.reattachmentRadial w)).down.1‖ ≤ 1 / 2 := by
        rw [hv]
        linarith
      rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h'
        hh' K' hK' i p hv₂ (TopCat.coe_reattachmentRadial_of_norm_le hv₂),
        reattachmentLoop_of_norm_le 0 p hw₄]
      congr 2
      refine ULift.ext (Subtype.ext ?_)
      rw [he', TopCat.coe_reattachmentRadial_of_norm_le hv₂, he, map_smul,
        LinearIsometryEquiv.symm_apply_apply, TopCat.coe_reattachmentRadial_of_norm_le hw₂,
        TopCat.coe_diskRadialPush_one_of_norm_le _ hw₄, smul_smul]
      norm_num
    · -- On the annulus `1/4 ≤ ‖x‖ ≤ 1/2` the composite runs out along `K i` and back.
      have hv₂ : 1 / 2 ≤ ‖(h i (p, TopCat.reattachmentRadial w)).down.1‖ := by
        rw [hv]
        linarith
      have hw₀ : 0 < ‖w.down.1‖ := by linarith
      have ht := coe_reattachmentLoopTime_zero_annulusParam hw₄
      rw [min_eq_left (by linarith)] at ht
      rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h'
        hh' K' hK' i p hv₂ (t := σ (reattachmentLoopTime 0 (TopCat.annulusParam (1 / 4) w)))
        (by rw [coe_symm_eq, ht, hv]; ring) (s := TopCat.annulusDir (by norm_num) ⟨_, hv₂⟩)
        (TopCat.coe_annulusDir _ _), reattachmentLoop_of_le_norm 0 p hw₄]
      congr 2
      rw [reattachmentTrack_apply, Subtype.mk.injEq, hKK', symm_symm]
      congr 3
      refine ULift.ext (Subtype.ext ?_)
      rw [he', TopCat.coe_diskBoundaryInclusion_apply_down, TopCat.coe_annulusDir, map_smul, hv, he,
        LinearIsometryEquiv.symm_apply_apply, TopCat.coe_reattachmentRadial_of_norm_le hw₂,
        TopCat.coe_diskBoundaryInclusion_apply_down, TopCat.coe_annulusDir, smul_smul]
      congr 1
      field_simp
  · -- On the annulus `1/2 ≤ ‖x‖` the composite runs back along `K i`.
    have ht := coe_reattachmentLoopTime_zero_annulusParam (by linarith : 1 / 4 ≤ ‖w.down.1‖)
    rw [min_eq_right (by linarith)] at ht
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K
      hK i p hw₂ (t := reattachmentLoopTime 0 (TopCat.annulusParam (1 / 4) w)) ht
      (s := TopCat.annulusDir (by norm_num : (0 : ℝ) < 1 / 4) ⟨w, by linarith⟩)
      (TopCat.coe_annulusDir _ _),
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      reattachmentLoop_of_le_norm 0 p (by linarith), reattachmentTrack_apply]

include he he' hKK' in
/-- **Reattaching back along the reversed homotopy undoes a reattachment, over `P` and relative to
`P × A`.** Let `h i (p, ·)` act on the disc by linear isometries `e i p`, let `h' i (p, ·)` act by
their inverses, and let `K' i (t, (p, x)) = K i (1 - t, (p, h' i (p, x)))`. Then the fiberwise
reattachment map of `(h, K)` followed by that of `(h', K')` is homotopic to the identity relative to
`P × A`, through maps over `P`. -/
private theorem exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment :
    ∃ G : (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫
        fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK').hom.HomotopyRel
        (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₁)),
      ∀ t y, fiberwiseCellAttachmentProj α₁ (G (t, y)) = fiberwiseCellAttachmentProj α₁ y := by
  choose C hC₀ hC₁ hCb hCp using fun i ↦ exists_reattachmentLoopCylinder (α := α₁) i
    (reattachmentTrack χ₀ χ₁ h K hK i) (reattachmentTrack_zero α₁ χ₀ χ₁ hχ₁ h K hK i)
  have hE : ∀ x, (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫
      fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK').hom
        (fiberwiseCellAttachmentIncl α₁ x) = fiberwiseCellAttachmentIncl α₁ x := fun x ↦ by
    rw [TopCat.hom_comp, ContinuousMap.comp_apply,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]
  refine ⟨{ toFun := fiberwiseCellAttachmentCylinderDesc α₁
              ((fiberwiseCellAttachmentIncl α₁).hom.comp ContinuousMap.snd) C hCb
            continuous_toFun := (fiberwiseCellAttachmentCylinderDesc α₁ _ C hCb).continuous
            map_zero_left := fun y ↦ ?_
            map_one_left := fun y ↦ ?_
            prop' := ?_ }, fun t y ↦ ?_⟩
  · refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ C hCb 0 x).trans
        (hE x).symm
    · refine (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell α₁ _ C hCb 0 i
        x).trans ?_
      rw [hC₀, TopCat.hom_comp, ContinuousMap.comp_apply,
        fiberwiseCellReattachment_fiberwiseCellReattachment_fiberwiseCellAttachmentCell α₀ α₁ χ₀ χ₁
          hχ₀ hχ₁ h h' hh hh' K hK K' hK' e he he' hKK' i x.1 x.2]
  · refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ C hCb 1 x
    · exact (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell α₁ _ C hCb 1 i
        x).trans (hC₁ i x)
  · rintro t _ ⟨x, rfl⟩
    exact (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ C hCb t x).trans
      (hE x).symm
  · refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact congrArg (fiberwiseCellAttachmentProj α₁)
        (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ C hCb t x)
    · exact (congrArg (fiberwiseCellAttachmentProj α₁)
        (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell α₁ _ C hCb t i x)).trans
        ((hCp i t x).trans (fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell α₁ i x).symm)

end Composite

section Inv

variable (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (χ₀ χ₁ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (h : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hh : ∀ i p, MapsTo (fun w ↦ h i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))))
  (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (e : ∀ i, P → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)))
  (he : ∀ i p w, ((h i (p, w)).down : EuclideanSpace ℝ (Fin (k i))) = e i p w.down)

include h he in
/-- The family `(p, w) ↦ (e i p)⁻¹ w` of inverse isometries of the disc. It is continuous because
`(e i p)⁻¹ v = Σⱼ ⟪e i p bⱼ, v⟫ bⱼ` for the standard basis `(bⱼ)`, and `e i p bⱼ = h i (p, bⱼ)`
depends continuously on `p`. -/
private def fiberwiseDiskInv (i : ι) : C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)) where
  toFun x := (ULift.up ⟨(e i x.1).symm x.2.down.1, by
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.1 x.2.down.2⟩ : TopCat.disk.{u} (k i))
  continuous_toFun := by
    let b := EuclideanSpace.basisFun (Fin (k i)) ℝ
    have hb : ∀ j, b j ∈ closedBall (0 : EuclideanSpace ℝ (Fin (k i))) 1 :=
      fun j ↦ mem_closedBall_zero_iff.2 (b.orthonormal.1 j).le
    -- `p ↦ e i p bⱼ` is continuous, being `p ↦ h i (p, bⱼ)`.
    have hcont : ∀ j, Continuous fun p ↦ e i p (b j) := fun j ↦ by
      have hfun : (fun p ↦ e i p (b j)) = fun p ↦
          ((h i (p, (ULift.up ⟨b j, hb j⟩ : TopCat.disk.{u} (k i)))).down :
            EuclideanSpace ℝ (Fin (k i))) :=
        funext fun p ↦ (he i p (ULift.up ⟨b j, hb j⟩ : TopCat.disk.{u} (k i))).symm
      rw [hfun]
      exact continuous_subtype_val.comp (continuous_uliftDown.comp
        ((h i).continuous.comp (continuous_id.prodMk continuous_const)))
    have key : (fun x : P × TopCat.disk.{u} (k i) ↦ (e i x.1).symm x.2.down.1) =
        fun x ↦ ∑ j, inner ℝ (e i x.1 (b j)) x.2.down.1 • b j := by
      funext x
      conv_lhs => rw [← b.sum_repr' ((e i x.1).symm x.2.down.1)]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← LinearIsometryEquiv.inner_map_map (e i x.1), LinearIsometryEquiv.apply_symm_apply]
    refine continuous_uliftUp.comp (Continuous.subtype_mk ?_ _)
    rw [key]
    exact continuous_finsetSum _ fun j _ ↦ (Continuous.inner (𝕜 := ℝ)
      ((hcont j).comp continuous_fst)
      (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_snd))).smul
        continuous_const

private theorem coe_fiberwiseDiskInv_apply_down (i : ι) (x : P × TopCat.disk.{u} (k i)) :
    ((fiberwiseDiskInv h e he i x).down : EuclideanSpace ℝ (Fin (k i))) = (e i x.1).symm x.2.down :=
  rfl

private theorem apply_fiberwiseDiskInv (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    h i (p, fiberwiseDiskInv h e he i (p, w)) = w :=
  ULift.ext (Subtype.ext (by rw [he, coe_fiberwiseDiskInv_apply_down,
    LinearIsometryEquiv.apply_symm_apply]))

private theorem fiberwiseDiskInv_apply (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    fiberwiseDiskInv h e he i (p, h i (p, w)) = w :=
  ULift.ext (Subtype.ext (by rw [coe_fiberwiseDiskInv_apply_down, he,
    LinearIsometryEquiv.symm_apply_apply]))

private theorem mapsTo_fiberwiseDiskInv (i : ι) (p : P) :
    MapsTo (fun w ↦ fiberwiseDiskInv h e he i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))) := by
  rintro _ ⟨s, rfl⟩
  rw [mem_range_diskBoundaryInclusion_iff, coe_fiberwiseDiskInv_apply_down,
    LinearIsometryEquiv.norm_map]
  exact TopCat.norm_diskBoundaryInclusion s

/-- The reversed homotopy `(t, (p, x)) ↦ K i (1 - t, (p, (e i p)⁻¹ x))` from `χ₀ i` to
`χ₁ i ∘ (p, (e i p)⁻¹)`. -/
private def fiberwiseReattachmentInvHomotopy (i : ι) :
    (χ₀ i).Homotopy ((χ₁ i).comp (ContinuousMap.fst.prodMk (fiberwiseDiskInv h e he i))) where
  toFun q := K i (σ q.1, (q.2.1, fiberwiseDiskInv h e he i q.2))
  continuous_toFun := (K i).continuous.comp ((continuous_symm.comp continuous_fst).prodMk
    ((continuous_fst.comp continuous_snd).prodMk
      ((fiberwiseDiskInv h e he i).continuous.comp continuous_snd)))
  map_zero_left x := by
    rw [symm_zero, (K i).apply_one, ContinuousMap.comp_apply, ContinuousMap.prod_eval,
      ContinuousMap.fst_apply, apply_fiberwiseDiskInv]
  map_one_left x := by
    rw [symm_one, (K i).apply_zero, ContinuousMap.comp_apply, ContinuousMap.prod_eval,
      ContinuousMap.fst_apply]

private theorem fiberwiseReattachmentInvHomotopy_apply (i : ι) (t : I)
    (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseReattachmentInvHomotopy χ₀ χ₁ h K e he i (t, x) =
      K i (σ t, (x.1, fiberwiseDiskInv h e he i x)) :=
  rfl

include hK in
private theorem fiberwiseReattachmentInvHomotopy_mem (i : ι) (t : I) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    fiberwiseReattachmentInvHomotopy χ₀ χ₁ h K e he i
      (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A := by
  obtain ⟨s', hs'⟩ := mapsTo_fiberwiseDiskInv h e he i p ⟨s, rfl⟩
  rw [fiberwiseReattachmentInvHomotopy_apply]
  simp only at hs'
  rw [← hs']
  exact hK i _ p s'

/-- **The inverse of a fiberwise reattachment map** along isometries of the discs. When `h i (p, ·)`
is a linear isometry `e i p` of the disc for every `p`, this is the fiberwise reattachment map
`(P × A) ∪_{α₀} ⨆ᵢ (P × D^{k i}) → (P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i})` of the inverse isometries
`(e i p)⁻¹` and the reversed homotopies `(t, (p, x)) ↦ K i (1 - t, (p, (e i p)⁻¹ x))` from `χ₀ i`
to `χ₁ i ∘ (p, (e i p)⁻¹)`. It is a homotopy inverse of `TauCeti.fiberwiseCellReattachment` over
`P`, relative to `P × A`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachmentInv`,
`TauCeti.exists_homotopyRel_fiberwiseCellReattachmentInv_comp_fiberwiseCellReattachment`). -/
def fiberwiseCellReattachmentInv : fiberwiseCellAttachment α₀ ⟶ fiberwiseCellAttachment α₁ :=
  fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ (fiberwiseDiskInv h e he)
    (mapsTo_fiberwiseDiskInv h e he) (fiberwiseReattachmentInvHomotopy χ₀ χ₁ h K e he)
    (fiberwiseReattachmentInvHomotopy_mem χ₀ χ₁ h K hK e he)

/-- The inverse of a fiberwise reattachment map is the identity on `P × A`. -/
@[simp]
theorem fiberwiseCellReattachmentInv_fiberwiseCellAttachmentIncl (x : P × A) :
    fiberwiseCellReattachmentInv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he
        (fiberwiseCellAttachmentIncl α₀ x) = fiberwiseCellAttachmentIncl α₁ x :=
  fiberwiseCellReattachment_fiberwiseCellAttachmentIncl _ _ _ _ _ _ _ _ _ _ x

/-- The inverse of a fiberwise reattachment map lies over `P`. -/
@[simp]
theorem fiberwiseCellAttachmentProj_fiberwiseCellReattachmentInv
    (y : fiberwiseCellAttachment α₀) :
    fiberwiseCellAttachmentProj α₁
        (fiberwiseCellReattachmentInv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he y) =
      fiberwiseCellAttachmentProj α₀ y :=
  fiberwiseCellAttachmentProj_fiberwiseCellReattachment _ _ _ _ _ _ _ _ _ _ y

/-- On the disc of radius `1/2` of the `i`-th cell over `p`, the inverse of a fiberwise
reattachment map is `x ↦ (e i p)⁻¹ (2x)`, read in the `i`-th cell over `p`. -/
theorem fiberwiseCellReattachmentInv_fiberwiseCellAttachmentCell_of_norm_le (i : ι) (p : P)
    {w v : TopCat.disk.{u} (k i)} (hw : ‖w.down.1‖ ≤ 1 / 2)
    (hv : v.down.1 = (e i p).symm ((2 : ℝ) • w.down.1)) :
    fiberwiseCellReattachmentInv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he
        (fiberwiseCellAttachmentCell α₀ i (p, w)) =
      fiberwiseCellAttachmentCell α₁ i (p, v) := by
  rw [fiberwiseCellReattachmentInv, fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le
    _ _ _ _ _ _ _ _ _ _ i p hw (TopCat.coe_reattachmentRadial_of_norm_le hw)]
  refine congrArg (fun v ↦ fiberwiseCellAttachmentCell α₁ i (p, v)) (ULift.ext (Subtype.ext ?_))
  rw [coe_fiberwiseDiskInv_apply_down, TopCat.coe_reattachmentRadial_of_norm_le hw, hv]

/-- Outside the disc of radius `1/2` of the `i`-th cell over `p`, the inverse of a fiberwise
reattachment map is `x ↦ K i (2‖x‖ - 1, (p, (e i p)⁻¹ (x/‖x‖)))`, read in `P × A`. -/
theorem fiberwiseCellReattachmentInv_fiberwiseCellAttachmentCell_of_le_norm (i : ι) (p : P)
    {w : TopCat.disk.{u} (k i)} (hw : 1 / 2 ≤ ‖w.down.1‖) {t : I}
    (ht : (t : ℝ) = 2 * ‖w.down.1‖ - 1) {s : TopCat.diskBoundary.{u} (k i)}
    (hs : s.down.1 = (e i p).symm (‖w.down.1‖⁻¹ • w.down.1)) :
    fiberwiseCellReattachmentInv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he
        (fiberwiseCellAttachmentCell α₀ i (p, w)) =
      fiberwiseCellAttachmentIncl α₁ (p, ⟨K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)),
        hK i t p s⟩) := by
  rw [fiberwiseCellReattachmentInv, fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm
    _ _ _ _ _ _ _ _ _ _ i p hw (t := σ t) (by rw [coe_symm_eq, ht]; ring)
    (s := TopCat.annulusDir (by norm_num : (0 : ℝ) < 1 / 2) ⟨w, hw⟩) (TopCat.coe_annulusDir _ _)]
  refine congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₁ (p, a)) (Subtype.ext ?_)
  rw [Subtype.coe_mk, fiberwiseReattachmentInvHomotopy_apply, symm_symm]
  refine congrArg (fun v ↦ K i (t, (p, v))) (ULift.ext (Subtype.ext ?_))
  rw [coe_fiberwiseDiskInv_apply_down, TopCat.coe_diskBoundaryInclusion_apply_down,
    TopCat.coe_annulusDir, TopCat.coe_diskBoundaryInclusion_apply_down, hs]

include he in
/-- **`E` followed by its inverse is homotopic to the identity over `P`, relative to `P × A`.** -/
theorem exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachmentInv :
    ∃ G : (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫
        fiberwiseCellReattachmentInv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he).hom.HomotopyRel
        (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₁)),
      ∀ t y, fiberwiseCellAttachmentProj α₁ (G (t, y)) = fiberwiseCellAttachmentProj α₁ y :=
  exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁
    h (fiberwiseDiskInv h e he) hh (mapsTo_fiberwiseDiskInv h e he) K hK
    (fiberwiseReattachmentInvHomotopy χ₀ χ₁ h K e he)
    (fiberwiseReattachmentInvHomotopy_mem χ₀ χ₁ h K hK e he) e he
    (fun i p w ↦ coe_fiberwiseDiskInv_apply_down h e he i (p, w))
    (fiberwiseReattachmentInvHomotopy_apply χ₀ χ₁ h K e he)

include he in
/-- **The inverse followed by `E` is homotopic to the identity over `P`, relative to `P × A`.** -/
theorem exists_homotopyRel_fiberwiseCellReattachmentInv_comp_fiberwiseCellReattachment :
    ∃ G : (fiberwiseCellReattachmentInv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he ≫
        fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK).hom.HomotopyRel
        (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₀)),
      ∀ t y, fiberwiseCellAttachmentProj α₀ (G (t, y)) = fiberwiseCellAttachmentProj α₀ y :=
  exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀
    (fiberwiseDiskInv h e he) h (mapsTo_fiberwiseDiskInv h e he) hh
    (fiberwiseReattachmentInvHomotopy χ₀ χ₁ h K e he)
    (fiberwiseReattachmentInvHomotopy_mem χ₀ χ₁ h K hK e he) K hK (fun i p ↦ (e i p).symm)
    (fun i p w ↦ coe_fiberwiseDiskInv_apply_down h e he i (p, w))
    (fun i p w ↦ by rw [LinearIsometryEquiv.symm_symm]; exact he i p w)
    fun i t x ↦ by rw [fiberwiseReattachmentInvHomotopy_apply, symm_symm, fiberwiseDiskInv_apply]

end Inv

end Inverse

end TauCeti

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

When the maps `h i (p, ·)` are invertible, with inverses continuous in `p` and preserving the
boundary spheres, `E` is a homotopy equivalence over `P` relative to `P × A`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp`), with no hypothesis on the
comparison maps. Indeed `E` factors as the reattachment along `K` which does not move the discs,
followed by the homeomorphism reparametrizing the discs by `h`
(`TauCeti.fiberwiseCellAttachmentIso`), and a reattachment which does not move the discs is
inverted by the reattachment along the reverse homotopy: on a cell their composite runs along `K`
on the boundary sphere and back again, and contracting this excursion gives a homotopy to the
identity over `P`, relative to `P × A`.

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

section Inverse

/-! ### Reattaching along a homotopy and back

When the self-maps of the discs are the identity, reattaching along a homotopy `K` of families of
characteristic maps and then along the reverse homotopy gives a map of the fiberwise adjunction
space which is homotopic to the identity, over `P` and relative to `P × A`. On a cell it is
`x ↦ 4x` on the disc of radius `1/4`, and on the annulus `1/4 ≤ ‖x‖` it runs along `K` on the
boundary sphere forward and then back, at the times `4‖x‖ - 1` and `2 - 2‖x‖`. Capping these
times by `1 - u` contracts the excursion along `K`, and the radial push of the disc of radius `1/4`
then undoes the rescaling `x ↦ 4x`.
-/

variable (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (χ₀ χ₁ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk ContinuousMap.snd)))
  (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)

variable (k) in
/-- The second projection `P × D^{k i} → D^{k i}` preserves the boundary spheres. -/
private theorem mapsTo_snd (i : ι) (p : P) :
    MapsTo
      (fun w ↦ (ContinuousMap.snd : C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i))) (p, w))
      (range (TopCat.diskBoundaryInclusion (k i))) (range (TopCat.diskBoundaryInclusion (k i))) :=
  fun _ hw ↦ hw

/-- The time `min (3s, (3 - 3s)/2, 1 - u)` along the homotopy at which the point of radial
parameter `s` of the annulus `1/4 ≤ ‖x‖` is read, at stage `u` of the contraction. -/
private def undoTime (u s : I) : I :=
  projIcc 0 1 zero_le_one (min (min (3 * (s : ℝ)) ((3 - 3 * s) / 2)) (1 - u))

private theorem continuous_undoTime : Continuous fun q : I × I ↦ undoTime q.1 q.2 :=
  continuous_projIcc.comp (by fun_prop)

private theorem coe_undoTime (u s : I) :
    (undoTime u s : ℝ) = min (min (3 * (s : ℝ)) ((3 - 3 * s) / 2)) (1 - u) := by
  have h₀ : 0 ≤ min (min (3 * (s : ℝ)) ((3 - 3 * s) / 2)) (1 - u) :=
    le_min (le_min (by linarith [s.2.1]) (by linarith [s.2.2])) (by linarith [u.2.2])
  have h₁ : min (min (3 * (s : ℝ)) ((3 - 3 * s) / 2)) (1 - u) ≤ 1 :=
    (min_le_right _ _).trans (by linarith [u.2.1])
  rw [undoTime, coe_projIcc, min_eq_right h₁, max_eq_right h₀]

private theorem undoTime_zero_right (u : I) : undoTime u 0 = 0 :=
  Subtype.ext ((coe_undoTime u 0).trans (by
    rw [Icc.coe_zero, mul_zero, sub_zero, min_eq_left (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    exact min_eq_left (by linarith [u.2.2])))

/-- On the disc of radius `1/4`, the factor `4` keeps a point in the unit disc. -/
private theorem four_smul_mem_closedBall {n : ℕ}
    (v : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 4)) :
    (4 : ℝ) • (v : EuclideanSpace ℝ (Fin n)) ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (by norm_num)]
  linarith [mem_closedBall_zero_iff.1 v.2]

include hχ₁ in
/-- On the `i`-th family of discs, stage `u` of the contraction: `x ↦ 4x` into the `i`-th cell on
the disc of radius `1/4`, and on the annulus the homotopy `K i` on the boundary sphere read at the
time `TauCeti.undoTime`. -/
private def undoCell (i : ι) : C((I × P) × TopCat.disk.{u} (k i), fiberwiseCellAttachment α₁) :=
  TopCat.discGlue (by norm_num : (0 : ℝ) < 1 / 4)
    ⟨fun q ↦ fiberwiseCellAttachmentCell α₁ i
        (q.1.2, ULift.up ⟨(4 : ℝ) • (q.2 : EuclideanSpace ℝ (Fin (k i))),
          four_smul_mem_closedBall q.2⟩),
      (fiberwiseCellAttachmentCell α₁ i).hom.continuous.comp (by fun_prop)⟩
    ⟨fun q ↦ fiberwiseCellAttachmentIncl α₁
        (q.1.2, ⟨K i (undoTime q.1.1 q.2.1, (q.1.2, TopCat.diskBoundaryInclusion (k i) q.2.2)),
          hK i _ _ _⟩),
      (fiberwiseCellAttachmentIncl α₁).hom.continuous.comp (continuous_snd.comp continuous_fst
        |>.prodMk (((K i).continuous.comp ((continuous_undoTime.comp
          ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))).prodMk
          ((continuous_snd.comp continuous_fst).prodMk
            ((TopCat.diskBoundaryInclusion (k i)).hom.continuous.comp
              (continuous_snd.comp continuous_snd))))).subtype_mk _))⟩
    fun q θ ↦ by
      -- On the seam the time vanishes, and `K i` starts at `χ₁ i`, which is `α₁ i` on the sphere.
      have hθ : (ULift.up ⟨(4 : ℝ) • (1 / 4 : ℝ) • θ.down.1, four_smul_mem_closedBall
          ⟨(1 / 4 : ℝ) • θ.down.1, TopCat.smul_diskBoundary_mem_closedBall (by norm_num) θ⟩⟩ :
            TopCat.disk.{u} (k i)) = TopCat.diskBoundaryInclusion (k i) θ :=
        ULift.ext (Subtype.ext (by
          simp only [smul_smul, TopCat.coe_diskBoundaryInclusion_apply_down]
          norm_num))
      simp only [ContinuousMap.coe_mk, undoTime_zero_right, ContinuousMap.Homotopy.apply_zero,
        hχ₁]
      rw [hθ, fiberwiseCellAttachmentCell_diskBoundaryInclusion]

private theorem undoCell_of_norm_le (i : ι) (u : I) (p : P) {w v : TopCat.disk.{u} (k i)}
    (hw : ‖w.down.1‖ ≤ 1 / 4) (hv : v.down.1 = (4 : ℝ) • w.down.1) :
    undoCell α₁ χ₀ χ₁ hχ₁ K hK i ((u, p), w) = fiberwiseCellAttachmentCell α₁ i (p, v) := by
  rw [undoCell, TopCat.discGlue_apply_of_norm_le _ _ _ _ _ hw]
  exact congrArg (fun v ↦ fiberwiseCellAttachmentCell α₁ i (p, v))
    (ULift.ext (Subtype.ext hv.symm))

private theorem undoCell_of_le_norm (i : ι) (u : I) (p : P) {w : TopCat.disk.{u} (k i)}
    (hw : 1 / 4 ≤ ‖w.down.1‖) {t : I}
    (ht : (t : ℝ) = min (min (4 * ‖w.down.1‖ - 1) (2 - 2 * ‖w.down.1‖)) (1 - u))
    {s : TopCat.diskBoundary.{u} (k i)} (hs : s.down.1 = ‖w.down.1‖⁻¹ • w.down.1) :
    undoCell α₁ χ₀ χ₁ hχ₁ K hK i ((u, p), w) =
      fiberwiseCellAttachmentIncl α₁
        (p, ⟨K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)), hK i t p s⟩) := by
  have ha := TopCat.add_one_sub_mul_annulusParam (by norm_num : (1 / 4 : ℝ) ≤ 1) hw
  have ht' : undoTime u (TopCat.annulusParam (1 / 4) w) = t := by
    refine Subtype.ext ((coe_undoTime _ _).trans (ht ▸ ?_))
    have h₁ : (3 - 3 * (TopCat.annulusParam (1 / 4) w : ℝ)) / 2 = 2 - 2 * ‖w.down.1‖ := by
      linarith
    have h₂ : 3 * (TopCat.annulusParam (1 / 4) w : ℝ) = 4 * ‖w.down.1‖ - 1 := by linarith
    rw [h₁, h₂]
  have hs' : TopCat.annulusDir (by norm_num) ⟨w, hw⟩ = s :=
    ULift.ext (Subtype.ext ((TopCat.coe_annulusDir _ _).trans hs.symm))
  rw [undoCell, TopCat.discGlue_apply_of_le_norm _ _ _ _ _ hw]
  simp only [ContinuousMap.coe_mk, ht', hs']


include hχ₁ in
/-- At every stage of the contraction, the boundary sphere of the `i`-th family of discs goes to
its attaching map. -/
private theorem undoCell_diskBoundaryInclusion (i : ι) (u : I) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    undoCell α₁ χ₀ χ₁ hχ₁ K hK i ((u, p), TopCat.diskBoundaryInclusion (k i) s) =
      fiberwiseCellAttachmentIncl α₁ (p, α₁ i (p, s)) := by
  rw [undoCell_of_le_norm α₁ χ₀ χ₁ hχ₁ K hK i u p (t := 0) (s := s)
    (by rw [TopCat.norm_diskBoundaryInclusion]; norm_num)
    (by rw [TopCat.norm_diskBoundaryInclusion, Icc.coe_zero]; norm_num [u.2.2])
    (by rw [TopCat.norm_diskBoundaryInclusion, inv_one, one_smul]; rfl)]
  exact congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₁ (p, a))
    (Subtype.ext ((K i).apply_zero _ |>.trans (hχ₁ i p s)))

/-- Every stage of the contraction lies over `P`. -/
private theorem fiberwiseCellAttachmentProj_undoCell (i : ι) (u : I) (p : P)
    (w : TopCat.disk.{u} (k i)) :
    fiberwiseCellAttachmentProj α₁ (undoCell α₁ χ₀ χ₁ hχ₁ K hK i ((u, p), w)) = p := by
  rcases le_total ‖w.down.1‖ (1 / 4) with hw | hw
  · rw [undoCell, TopCat.discGlue_apply_of_norm_le _ _ _ _ _ hw]
    exact fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell α₁ i _
  · rw [undoCell, TopCat.discGlue_apply_of_le_norm _ _ _ _ _ hw]
    exact fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl α₁ _

include hχ₁ in
/-- The contraction `I × ((P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i})) → (P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i})`: the
identity on `P × A`, and `TauCeti.undoCell` on the cylinders over the cells. -/
private def undoHomotopyFun : C(I × fiberwiseCellAttachment α₁, fiberwiseCellAttachment α₁) :=
  fiberwiseCellAttachmentCylinderDesc α₁
    ((fiberwiseCellAttachmentIncl α₁).hom.comp ContinuousMap.snd)
    (fun i ↦ (undoCell α₁ χ₀ χ₁ hχ₁ K hK i).comp ⟨fun q ↦ ((q.1, q.2.1), q.2.2), by fun_prop⟩)
    fun i t p s ↦ undoCell_diskBoundaryInclusion α₁ χ₀ χ₁ hχ₁ K hK i t p s

private theorem undoHomotopyFun_fiberwiseCellAttachmentIncl (t : I) (x : P × A) :
    undoHomotopyFun α₁ χ₀ χ₁ hχ₁ K hK (t, fiberwiseCellAttachmentIncl α₁ x) =
      fiberwiseCellAttachmentIncl α₁ x :=
  fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ _ _ t x

private theorem undoHomotopyFun_fiberwiseCellAttachmentCell (t : I) (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    undoHomotopyFun α₁ χ₀ χ₁ hχ₁ K hK (t, fiberwiseCellAttachmentCell α₁ i x) =
      undoCell α₁ χ₀ χ₁ hχ₁ K hK i ((t, x.1), x.2) :=
  fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell α₁ _ _ _ t i x

/-- The radial push of every cell at the end of its homotopy: `x ↦ 4x` on the disc of radius
`1/4`, with the annulus `1/4 ≤ ‖x‖` pushed onto the boundary sphere. -/
private def radialPushMap : fiberwiseCellAttachment α₁ ⟶ fiberwiseCellAttachment α₁ :=
  fiberwiseCellAttachmentDesc α₁ (fiberwiseCellAttachmentIncl α₁)
    (fun i ↦ TopCat.ofHom ⟨fun x ↦ fiberwiseCellAttachmentCell α₁ i
        (x.1, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, x.2)),
      (fiberwiseCellAttachmentCell α₁ i).hom.continuous.comp (continuous_fst.prodMk
        ((TopCat.diskRadialPush (k i) _).continuous.comp
          (continuous_const.prodMk continuous_snd)))⟩)
    fun i p s ↦ (congrArg (fun w ↦ fiberwiseCellAttachmentCell α₁ i (p, w))
      (TopCat.diskRadialPush_diskBoundaryInclusion (by norm_num) (by norm_num) 1 s)).trans
      (fiberwiseCellAttachmentCell_diskBoundaryInclusion α₁ i p s)

private theorem radialPushMap_fiberwiseCellAttachmentCell (i : ι) (p : P)
    (w : TopCat.disk.{u} (k i)) :
    radialPushMap α₁ (fiberwiseCellAttachmentCell α₁ i (p, w)) =
      fiberwiseCellAttachmentCell α₁ i
        (p, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, w)) :=
  fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentCell α₁ _ _ _ i (p, w)

/-- The radial push of the cells, undone along the radial push homotopy of the discs. -/
private def pushHomotopyFun : C(I × fiberwiseCellAttachment α₁, fiberwiseCellAttachment α₁) :=
  fiberwiseCellAttachmentCylinderDesc α₁
    ((fiberwiseCellAttachmentIncl α₁).hom.comp ContinuousMap.snd)
    (fun i ↦ ⟨fun q ↦ fiberwiseCellAttachmentCell α₁ i
        (q.2.1, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (σ q.1, q.2.2)),
      (fiberwiseCellAttachmentCell α₁ i).hom.continuous.comp ((continuous_fst.comp continuous_snd)
        |>.prodMk ((TopCat.diskRadialPush (k i) _).continuous.comp
          ((continuous_symm.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))))⟩)
    fun i t p s ↦ by
      rw [ContinuousMap.coe_mk,
        TopCat.diskRadialPush_diskBoundaryInclusion (by norm_num) (by norm_num),
        fiberwiseCellAttachmentCell_diskBoundaryInclusion]
      rfl

private theorem pushHomotopyFun_fiberwiseCellAttachmentIncl (t : I) (x : P × A) :
    pushHomotopyFun α₁ (t, fiberwiseCellAttachmentIncl α₁ x) = fiberwiseCellAttachmentIncl α₁ x :=
  fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ _ _ t x

private theorem pushHomotopyFun_fiberwiseCellAttachmentCell (t : I) (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    pushHomotopyFun α₁ (t, fiberwiseCellAttachmentCell α₁ i x) =
      fiberwiseCellAttachmentCell α₁ i
        (x.1, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (σ t, x.2)) :=
  fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell α₁ _ _ _ t i x

/-- The radial push of the cells is homotopic to the identity, relative to `P × A`. -/
private def pushHomotopy :
    (radialPushMap α₁).hom.HomotopyRel (ContinuousMap.id _)
      (range (fiberwiseCellAttachmentIncl α₁)) where
  toFun := pushHomotopyFun α₁
  continuous_toFun := (pushHomotopyFun α₁).continuous
  map_zero_left y := by
    refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · rw [pushHomotopyFun_fiberwiseCellAttachmentIncl]
      exact (fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentIncl α₁ _ _ _ x).symm
    · rw [pushHomotopyFun_fiberwiseCellAttachmentCell, symm_zero]
      exact (radialPushMap_fiberwiseCellAttachmentCell α₁ i x.1 x.2).symm
  map_one_left y := by
    refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact pushHomotopyFun_fiberwiseCellAttachmentIncl α₁ 1 x
    · rw [pushHomotopyFun_fiberwiseCellAttachmentCell, symm_one, TopCat.diskRadialPush_zero]
      rfl
  prop' t y hy := by
    obtain ⟨x, rfl⟩ := hy
    exact (pushHomotopyFun_fiberwiseCellAttachmentIncl α₁ t x).trans
      (fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentIncl α₁ _ _ _ x).symm

private theorem fiberwiseCellAttachmentProj_pushHomotopy (t : I)
    (y : fiberwiseCellAttachment α₁) :
    fiberwiseCellAttachmentProj α₁ (pushHomotopy α₁ (t, y)) = fiberwiseCellAttachmentProj α₁ y := by
  refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
  · exact congrArg _ (pushHomotopyFun_fiberwiseCellAttachmentIncl α₁ t x)
  · refine (congrArg _ (pushHomotopyFun_fiberwiseCellAttachmentCell α₁ t i x)).trans ?_
    rw [fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]


variable (K' : ∀ i, (χ₀ i).Homotopy ((χ₁ i).comp (ContinuousMap.fst.prodMk ContinuousMap.snd)))
  (hK' : ∀ i t p s, K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (hKK' : ∀ i t p s, K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
    K i (σ t, (p, TopCat.diskBoundaryInclusion (k i) s)))

include hKK' in
/-- At the start of the contraction, `TauCeti.undoCell` is the reattachment map along `K` followed
by the reattachment map along the reverse homotopy `K'`, on the `i`-th cell. -/
private theorem undoCell_zero (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    undoCell α₁ χ₀ χ₁ hχ₁ K hK i ((0, p), w) =
      fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ (fun _ ↦ ContinuousMap.snd)
        (mapsTo_snd k) K' hK'
        (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ (fun _ ↦ ContinuousMap.snd)
          (mapsTo_snd k) K hK (fiberwiseCellAttachmentCell α₁ i (p, w))) := by
  have hw₁ : ‖w.down.1‖ ≤ 1 := mem_closedBall_zero_iff.1 w.down.2
  set v := TopCat.reattachmentRadial w
  rcases le_total ‖w.down.1‖ (1 / 2) with hw | hw
  · -- The first reattachment map sends `w` to the point `v = 2w` of the `i`-th cell.
    have hv : v.down.1 = (2 : ℝ) • w.down.1 := TopCat.coe_reattachmentRadial_of_norm_le hw
    have hvn : ‖v.down.1‖ = 2 * ‖w.down.1‖ := by
      rw [hv, norm_smul, Real.norm_of_nonneg zero_le_two]
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hw) (hv := hv)]
    simp only [ContinuousMap.snd_apply]
    rcases le_total ‖w.down.1‖ (1 / 4) with hw' | hw'
    · -- On the disc of radius `1/4` both maps are `w ↦ 4w`.
      have hv' : (TopCat.reattachmentRadial v).down.1 = (2 : ℝ) • v.down.1 :=
        TopCat.coe_reattachmentRadial_of_norm_le (by rw [hvn]; linarith)
      rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (w := v)
        (hw := by rw [hvn]; linarith) (hv := hv'),
        undoCell_of_norm_le α₁ χ₀ χ₁ hχ₁ K hK i 0 p hw' (by rw [hv', hv, smul_smul]; norm_num)]
      simp only [ContinuousMap.snd_apply]
    · -- On the annulus `1/4 ≤ ‖w‖ ≤ 1/2` the reverse homotopy is read at time `2 - 4‖w‖`.
      have hvn' : 1 / 2 ≤ ‖v.down.1‖ := by rw [hvn]; linarith
      have hw₀ : 0 < ‖w.down.1‖ := by linarith
      obtain ⟨t, ht⟩ : ∃ t : I, (t : ℝ) = 2 - 2 * ‖v.down.1‖ :=
        ⟨TopCat.reattachmentTime v, TopCat.coe_reattachmentTime_of_le_norm hvn'⟩
      obtain ⟨s, hs⟩ : ∃ s : TopCat.diskBoundary.{u} (k i), s.down.1 = ‖v.down.1‖⁻¹ • v.down.1 :=
        ⟨TopCat.annulusDir (by norm_num) ⟨v, hvn'⟩, TopCat.coe_annulusDir _ _⟩
      rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (w := v) (hw := hvn')
        (ht := ht) (hs := hs), undoCell_of_le_norm α₁ χ₀ χ₁ hχ₁ K hK i 0 p hw' (t := σ t) (s := s)
        (by
          rw [coe_symm_eq, ht, hvn, Icc.coe_zero, sub_zero,
            min_eq_left (show 4 * ‖w.down.1‖ - 1 ≤ 2 - 2 * ‖w.down.1‖ by linarith),
            min_eq_left (show 4 * ‖w.down.1‖ - 1 ≤ 1 by linarith)]
          ring)
        (by rw [hs, hvn, hv, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ two_ne_zero,
          mul_one])]
      exact congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₁ (p, a))
        (Subtype.ext (hKK' i t p s).symm)
  · -- On the annulus `1/2 ≤ ‖w‖` the homotopy is read at time `2 - 2‖w‖`, and the second
    -- reattachment map fixes `P × A`.
    obtain ⟨t, ht⟩ : ∃ t : I, (t : ℝ) = 2 - 2 * ‖w.down.1‖ :=
      ⟨TopCat.reattachmentTime w, TopCat.coe_reattachmentTime_of_le_norm hw⟩
    obtain ⟨s, hs⟩ : ∃ s : TopCat.diskBoundary.{u} (k i), s.down.1 = ‖w.down.1‖⁻¹ • w.down.1 :=
      ⟨TopCat.annulusDir (by norm_num) ⟨w, hw⟩, TopCat.coe_annulusDir _ _⟩
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hw) (ht := ht)
      (hs := hs), fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      undoCell_of_le_norm α₁ χ₀ χ₁ hχ₁ K hK i 0 p (by linarith) (t := t) (s := s)
        (by
          rw [ht, Icc.coe_zero, sub_zero,
            min_eq_right (show 2 - 2 * ‖w.down.1‖ ≤ 4 * ‖w.down.1‖ - 1 by linarith),
            min_eq_left (show 2 - 2 * ‖w.down.1‖ ≤ 1 by linarith)]) hs]

/-- At the end of the contraction, `TauCeti.undoCell` is the radial push of the `i`-th cell. -/
private theorem undoCell_one (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    undoCell α₁ χ₀ χ₁ hχ₁ K hK i ((1, p), w) =
      radialPushMap α₁ (fiberwiseCellAttachmentCell α₁ i (p, w)) := by
  have hw₁ : ‖w.down.1‖ ≤ 1 := mem_closedBall_zero_iff.1 w.down.2
  rw [radialPushMap_fiberwiseCellAttachmentCell]
  rcases le_total ‖w.down.1‖ (1 / 4) with hw | hw
  · exact undoCell_of_norm_le α₁ χ₀ χ₁ hχ₁ K hK i 1 p hw (by
      rw [TopCat.coe_diskRadialPush_one_of_norm_le _ hw]; norm_num)
  · have hpush : TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, w) =
        TopCat.diskBoundaryInclusion (k i) (TopCat.annulusDir (by norm_num) ⟨w, hw⟩) :=
      (TopCat.diskBoundaryInclusion_annulusDir _ ⟨w, hw⟩).symm
    rw [undoCell_of_le_norm α₁ χ₀ χ₁ hχ₁ K hK i 1 p hw (t := 0)
      (s := TopCat.annulusDir (by norm_num) ⟨w, hw⟩)
      (by rw [Icc.coe_one, sub_self, Icc.coe_zero, min_eq_right (le_min (by linarith)
        (by linarith))]) (TopCat.coe_annulusDir _ _),
      hpush, fiberwiseCellAttachmentCell_diskBoundaryInclusion]
    exact congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₁ (p, a))
      (Subtype.ext ((K i).apply_zero _ |>.trans (hχ₁ i p _)))

include hKK' in
/-- The contraction of the excursion along `K`, from the reattachment map along `K` followed by
the reattachment map along its reverse to the radial push of the cells, relative to `P × A`. -/
private def undoHomotopy :
    (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ (fun _ ↦ ContinuousMap.snd)
        (mapsTo_snd k) K hK ≫
      fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ (fun _ ↦ ContinuousMap.snd)
        (mapsTo_snd k) K' hK').hom.HomotopyRel (radialPushMap α₁).hom
      (range (fiberwiseCellAttachmentIncl α₁)) where
  toFun := undoHomotopyFun α₁ χ₀ χ₁ hχ₁ K hK
  continuous_toFun := (undoHomotopyFun α₁ χ₀ χ₁ hχ₁ K hK).continuous
  map_zero_left y := by
    refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · rw [undoHomotopyFun_fiberwiseCellAttachmentIncl, TopCat.hom_comp, ContinuousMap.comp_apply,
        fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
        fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]
    · rw [undoHomotopyFun_fiberwiseCellAttachmentCell,
        undoCell_zero α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ K hK K' hK' hKK']
      rfl
  map_one_left y := by
    refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · rw [undoHomotopyFun_fiberwiseCellAttachmentIncl]
      exact (fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentIncl α₁ _ _ _ x).symm
    · rw [undoHomotopyFun_fiberwiseCellAttachmentCell, undoCell_one]
  prop' t y hy := by
    obtain ⟨x, rfl⟩ := hy
    rw [ContinuousMap.coe_mk, undoHomotopyFun_fiberwiseCellAttachmentIncl, TopCat.hom_comp,
      ContinuousMap.comp_apply, fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]

include hKK' in
/-- **Reattaching along a homotopy and back is homotopic to the identity, over `P`.** Let
`K i : χ₁ i ≃ χ₀ i` be homotopies of families of characteristic maps keeping the boundary spheres
in `A`, and let `K' i : χ₀ i ≃ χ₁ i` agree on the boundary spheres with the reverse of `K i`. The
fiberwise reattachment map along `K` (with the identity of the discs), followed by the fiberwise
reattachment map along `K'`, is homotopic to the identity of
`(P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i})`, relative to `P × A`, through maps over `P`. -/
private theorem exists_homotopyRel_reattachment_comp_symm :
    ∃ F : (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ (fun _ ↦ ContinuousMap.snd)
          (mapsTo_snd k) K hK ≫
        fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ (fun _ ↦ ContinuousMap.snd)
          (mapsTo_snd k) K' hK').hom.HomotopyRel (ContinuousMap.id _)
        (range (fiberwiseCellAttachmentIncl α₁)),
      ∀ t y, fiberwiseCellAttachmentProj α₁ (F (t, y)) = fiberwiseCellAttachmentProj α₁ y := by
  refine ⟨(undoHomotopy α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ K hK K' hK' hKK').trans (pushHomotopy α₁),
    fun t y ↦ ?_⟩
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact congrArg _ (undoHomotopyFun_fiberwiseCellAttachmentIncl α₁ χ₀ χ₁ hχ₁ K hK _ x)
    · refine (congrArg _
        (undoHomotopyFun_fiberwiseCellAttachmentCell α₁ χ₀ χ₁ hχ₁ K hK _ i x)).trans ?_
      rw [fiberwiseCellAttachmentProj_undoCell,
        fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]
  · exact fiberwiseCellAttachmentProj_pushHomotopy α₁ _ y

end Inverse

section Iso

variable (α α' : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (h h' : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hh : ∀ i p, MapsTo (fun w ↦ h i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (hh' : ∀ i p, MapsTo (fun w ↦ h' i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (hh'h : ∀ i p w, h' i (p, h i (p, w)) = w) (hhh' : ∀ i p w, h i (p, h' i (p, w)) = w)
  (hα : ∀ i p s s', h i (p, TopCat.diskBoundaryInclusion (k i) s) =
    TopCat.diskBoundaryInclusion (k i) s' → α' i (p, s) = α i (p, s'))

/-- **Reparametrizing the discs of a fiberwise adjunction space.** Let `h i (p, ·)` be self-maps of
the disc pairs `(D^{k i}, ∂D^{k i})`, continuous in `p`, with inverses `h' i (p, ·)` which also
preserve the boundary spheres, and let `α' i (p, s) = α i (p, h i (p, s))` on the boundary spheres.
This is the homeomorphism `(P × A) ∪_{α'} ⨆ᵢ (P × D^{k i}) ≅ (P × A) ∪_α ⨆ᵢ (P × D^{k i})` which is
the identity on `P × A` and `(p, x) ↦ (p, h i (p, x))` on the `i`-th family of discs. It lies over
`P` (`TauCeti.fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIso_hom`). -/
def fiberwiseCellAttachmentIso : fiberwiseCellAttachment α' ≅ fiberwiseCellAttachment α where
  hom := fiberwiseCellAttachmentDesc α' (fiberwiseCellAttachmentIncl α)
    (fun i ↦ TopCat.ofHom (ContinuousMap.fst.prodMk (h i)) ≫ fiberwiseCellAttachmentCell α i)
    fun i p s ↦ by
      obtain ⟨s', hs'⟩ := hh i p ⟨s, rfl⟩
      refine (congrArg (fun w ↦ fiberwiseCellAttachmentCell α i (p, w)) hs'.symm).trans ?_
      rw [fiberwiseCellAttachmentCell_diskBoundaryInclusion, hα i p s s' hs'.symm]
  inv := fiberwiseCellAttachmentDesc α (fiberwiseCellAttachmentIncl α')
    (fun i ↦ TopCat.ofHom (ContinuousMap.fst.prodMk (h' i)) ≫ fiberwiseCellAttachmentCell α' i)
    fun i p s ↦ by
      obtain ⟨s', hs'⟩ := hh' i p ⟨s, rfl⟩
      refine (congrArg (fun w ↦ fiberwiseCellAttachmentCell α' i (p, w)) hs'.symm).trans ?_
      rw [fiberwiseCellAttachmentCell_diskBoundaryInclusion,
        hα i p s' s (by rw [hs']; exact hhh' i p _)]
  hom_inv_id := fiberwiseCellAttachment_hom_ext α'
    (fun x ↦ by
      rw [ConcreteCategory.comp_apply, fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentIncl,
        fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentIncl, ConcreteCategory.id_apply])
    fun i x ↦ by
      rw [ConcreteCategory.comp_apply, fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentCell,
        ConcreteCategory.comp_apply, fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentCell,
        ConcreteCategory.id_apply]
      exact congrArg (fun w ↦ fiberwiseCellAttachmentCell α' i (x.1, w)) (hh'h i x.1 x.2)
  inv_hom_id := fiberwiseCellAttachment_hom_ext α
    (fun x ↦ by
      rw [ConcreteCategory.comp_apply, fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentIncl,
        fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentIncl, ConcreteCategory.id_apply])
    fun i x ↦ by
      rw [ConcreteCategory.comp_apply, fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentCell,
        ConcreteCategory.comp_apply, fiberwiseCellAttachmentDesc_fiberwiseCellAttachmentCell,
        ConcreteCategory.id_apply]
      exact congrArg (fun w ↦ fiberwiseCellAttachmentCell α i (x.1, w)) (hhh' i x.1 x.2)

@[simp]
theorem fiberwiseCellAttachmentIso_hom_fiberwiseCellAttachmentIncl (x : P × A) :
    (fiberwiseCellAttachmentIso α α' h h' hh hh' hh'h hhh' hα).hom
        (fiberwiseCellAttachmentIncl α' x) = fiberwiseCellAttachmentIncl α x :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentIncl_desc α' _ _ _) x

@[simp]
theorem fiberwiseCellAttachmentIso_hom_fiberwiseCellAttachmentCell (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    (fiberwiseCellAttachmentIso α α' h h' hh hh' hh'h hhh' hα).hom
        (fiberwiseCellAttachmentCell α' i x) = fiberwiseCellAttachmentCell α i (x.1, h i x) :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentCell_desc α' _ _ _ i) x

@[simp]
theorem fiberwiseCellAttachmentIso_inv_fiberwiseCellAttachmentIncl (x : P × A) :
    (fiberwiseCellAttachmentIso α α' h h' hh hh' hh'h hhh' hα).inv
        (fiberwiseCellAttachmentIncl α x) = fiberwiseCellAttachmentIncl α' x :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentIncl_desc α _ _ _) x

@[simp]
theorem fiberwiseCellAttachmentIso_inv_fiberwiseCellAttachmentCell (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    (fiberwiseCellAttachmentIso α α' h h' hh hh' hh'h hhh' hα).inv
        (fiberwiseCellAttachmentCell α i x) = fiberwiseCellAttachmentCell α' i (x.1, h' i x) :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentCell_desc α _ _ _ i) x

/-- The reparametrization of the discs lies over `P`. -/
@[simp]
theorem fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIso_hom
    (y : fiberwiseCellAttachment α') :
    fiberwiseCellAttachmentProj α
        ((fiberwiseCellAttachmentIso α α' h h' hh hh' hh'h hhh' hα).hom y) =
      fiberwiseCellAttachmentProj α' y :=
  fiberwiseCellAttachment_induction α'
    (fun x ↦ by rw [fiberwiseCellAttachmentIso_hom_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl])
    (fun i x ↦ by rw [fiberwiseCellAttachmentIso_hom_fiberwiseCellAttachmentCell,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]) y

/-- The inverse of the reparametrization of the discs lies over `P`. -/
@[simp]
theorem fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIso_inv
    (y : fiberwiseCellAttachment α) :
    fiberwiseCellAttachmentProj α'
        ((fiberwiseCellAttachmentIso α α' h h' hh hh' hh'h hhh' hα).inv y) =
      fiberwiseCellAttachmentProj α y :=
  fiberwiseCellAttachment_induction α
    (fun x ↦ by rw [fiberwiseCellAttachmentIso_inv_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl])
    (fun i x ↦ by rw [fiberwiseCellAttachmentIso_inv_fiberwiseCellAttachmentCell,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]) y

end Iso

section HomotopyEquiv

variable (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (χ₀ χ₁ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (h : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hh : ∀ i p, MapsTo (fun w ↦ h i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))))
  (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)

/-- The end `(p, s) ↦ K i (1, (p, s))` of the homotopies on the boundary spheres: the attaching
maps `α₀ i (p, h i (p, s))` of the characteristic families `χ₀ i ∘ (p, h i)`. -/
private def endAttachingMap (i : ι) : C(P × TopCat.diskBoundary.{u} (k i), A) :=
  ⟨fun x ↦ ⟨K i (1, (x.1, TopCat.diskBoundaryInclusion (k i) x.2)), hK i 1 x.1 x.2⟩,
    ((K i).continuous.comp (continuous_const.prodMk (continuous_fst.prodMk
      ((TopCat.diskBoundaryInclusion (k i)).hom.continuous.comp continuous_snd)))).subtype_mk _⟩

private theorem comp_diskBoundaryInclusion_eq_endAttachingMap (i : ι) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))) (p, TopCat.diskBoundaryInclusion (k i) s) =
      endAttachingMap χ₀ χ₁ h K hK i (p, s) :=
  ((K i).apply_one _).symm

/-- `K i`, read as a homotopy from `χ₁ i` to `χ₀ i ∘ (p, h i)` composed with the identity of the
discs. -/
private def castHomotopy (i : ι) :
    (χ₁ i).Homotopy (((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))).comp
      (ContinuousMap.fst.prodMk ContinuousMap.snd)) :=
  (K i).cast rfl (ContinuousMap.ext fun _ ↦ rfl)

/-- The reverse of `K i`, read as a homotopy from `χ₀ i ∘ (p, h i)` to `χ₁ i` composed with the
identity of the discs. -/
private def symmHomotopy (i : ι) :
    ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))).Homotopy
      ((χ₁ i).comp (ContinuousMap.fst.prodMk ContinuousMap.snd)) :=
  (K i).symm.cast rfl (ContinuousMap.ext fun _ ↦ rfl)

include hK in
private theorem castHomotopy_mem (i : ι) (t : I) (p : P) (s : TopCat.diskBoundary.{u} (k i)) :
    castHomotopy χ₀ χ₁ h K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A :=
  hK i t p s

include hK in
private theorem symmHomotopy_mem (i : ι) (t : I) (p : P) (s : TopCat.diskBoundary.{u} (k i)) :
    symmHomotopy χ₀ χ₁ h K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A :=
  hK i (σ t) p s

include hχ₀ in
private theorem endAttachingMap_eq (i : ι) (p : P) (s s' : TopCat.diskBoundary.{u} (k i))
    (hs : h i (p, TopCat.diskBoundaryInclusion (k i) s) = TopCat.diskBoundaryInclusion (k i) s') :
    endAttachingMap χ₀ χ₁ h K hK i (p, s) = α₀ i (p, s') :=
  Subtype.ext (((K i).apply_one _).trans (by
    rw [ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.fst_apply, hs, hχ₀]))

/-- The reattachment map along `K` and `h` is the reattachment map along `K` with the identity of
the discs, into the attachment along the end of `K`, followed by the reparametrization of the
discs by `h`. -/
private theorem fiberwiseCellReattachment_eq_comp_fiberwiseCellAttachmentIso
    (h' : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
    (hh' : ∀ i p, MapsTo (fun w ↦ h' i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))))
    (hh'h : ∀ i p w, h' i (p, h i (p, w)) = w) (hhh' : ∀ i p w, h i (p, h' i (p, w)) = w) :
    fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK =
      fiberwiseCellReattachment (endAttachingMap χ₀ χ₁ h K hK) α₁
          (fun i ↦ (χ₀ i).comp (ContinuousMap.fst.prodMk (h i))) χ₁
          (comp_diskBoundaryInclusion_eq_endAttachingMap χ₀ χ₁ h K hK) hχ₁
          (fun _ ↦ ContinuousMap.snd) (mapsTo_snd k) (castHomotopy χ₀ χ₁ h K)
          (castHomotopy_mem χ₀ χ₁ h K hK) ≫
        (fiberwiseCellAttachmentIso α₀ (endAttachingMap χ₀ χ₁ h K hK) h h' hh hh' hh'h hhh'
          (endAttachingMap_eq α₀ χ₀ χ₁ hχ₀ h K hK)).hom := by
  refine fiberwiseCellAttachment_hom_ext α₁ (fun x ↦ ?_) fun i x ↦ ?_
  · rw [ConcreteCategory.comp_apply, fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellAttachmentIso_hom_fiberwiseCellAttachmentIncl]
  obtain ⟨p, w⟩ := x
  rw [ConcreteCategory.comp_apply]
  rcases le_total ‖w.down.1‖ (1 / 2) with hw | hw
  · have hv := TopCat.coe_reattachmentRadial_of_norm_le hw
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hw) (hv := hv),
      fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hw) (hv := hv),
      fiberwiseCellAttachmentIso_hom_fiberwiseCellAttachmentCell]
    simp only [ContinuousMap.snd_apply]
  · obtain ⟨s, hs⟩ : ∃ s : TopCat.diskBoundary.{u} (k i), s.down.1 = ‖w.down.1‖⁻¹ • w.down.1 :=
      ⟨TopCat.annulusDir (by norm_num) ⟨w, hw⟩, TopCat.coe_annulusDir _ _⟩
    obtain ⟨t, ht⟩ : ∃ t : I, (t : ℝ) = 2 - 2 * ‖w.down.1‖ :=
      ⟨TopCat.reattachmentTime w, TopCat.coe_reattachmentTime_of_le_norm hw⟩
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hw) (ht := ht)
        (hs := hs),
      fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hw) (ht := ht)
        (hs := hs),
      fiberwiseCellAttachmentIso_hom_fiberwiseCellAttachmentIncl]
    rfl

/-- A homotopy from a self-map `g` of `X` to the identity, conjugated by an isomorphism
`J : X ≅ X'`: it is `(t, y) ↦ J (F (t, J⁻¹ y))`. -/
private def homotopyRelConj {X X' : TopCat.{u}} (J : X ≅ X') {g : X ⟶ X} {S : Set X}
    (F : g.hom.HomotopyRel (ContinuousMap.id X) S) {S' : Set X'} (hS : MapsTo J.inv S' S) :
    (J.inv ≫ g ≫ J.hom).hom.HomotopyRel (ContinuousMap.id X') S' where
  toFun x := J.hom (F (x.1, J.inv x.2))
  continuous_toFun := J.hom.hom.continuous.comp
    (F.continuous.comp (continuous_fst.prodMk (J.inv.hom.continuous.comp continuous_snd)))
  map_zero_left y := by
    rw [ContinuousMap.HomotopyWith.apply_zero]
    rfl
  map_one_left y := by
    rw [ContinuousMap.HomotopyWith.apply_one, ContinuousMap.id_apply, ContinuousMap.id_apply,
      Iso.inv_hom_id_apply]
  prop' t y hy := by
    rw [ContinuousMap.coe_mk, F.eq_fst t (hS hy)]
    rfl

/-- **The fiberwise reattachment map is a homotopy equivalence over `P`, relative to `P × A`.**
Let `E : (P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i}) → (P × A) ∪_{α₀} ⨆ᵢ (P × D^{k i})` be the fiberwise
reattachment map of a family of homotopies `K i : χ₁ i ≃ χ₀ i ∘ (p, h i)` keeping the boundary
spheres in `A`, where the self-maps `h i (p, ·)` of the disc pairs are invertible, with inverses
`h' i (p, ·)` continuous in `p` and preserving the boundary spheres. Then `E` has a homotopy
inverse `E'` over `P` which is the identity on `P × A`, and both composites are homotopic to the
identities relative to `P × A`, through maps over `P`. The inverse is the reparametrization of the
discs by `h'` followed by the reattachment map along the reverse of `K`. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_comp
    (h' : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
    (hh' : ∀ i p, MapsTo (fun w ↦ h' i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))))
    (hh'h : ∀ i p w, h' i (p, h i (p, w)) = w) (hhh' : ∀ i p w, h i (p, h' i (p, w)) = w) :
    ∃ E' : fiberwiseCellAttachment α₀ ⟶ fiberwiseCellAttachment α₁,
      fiberwiseCellAttachmentIncl α₀ ≫ E' = fiberwiseCellAttachmentIncl α₁ ∧
      (∀ y, fiberwiseCellAttachmentProj α₁ (E' y) = fiberwiseCellAttachmentProj α₀ y) ∧
      (∃ F : (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫ E').hom.HomotopyRel
          (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₁)),
        ∀ t y, fiberwiseCellAttachmentProj α₁ (F (t, y)) = fiberwiseCellAttachmentProj α₁ y) ∧
      (∃ F : (E' ≫ fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK).hom.HomotopyRel
          (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₀)),
        ∀ t y, fiberwiseCellAttachmentProj α₀ (F (t, y)) = fiberwiseCellAttachmentProj α₀ y) := by
  -- Write `E = E₀ ≫ J`, where `E₀` reattaches along `K` without moving the discs, into the
  -- attachment along the end `α` of `K`, and `J` reparametrizes the discs by `h`.
  set α := endAttachingMap χ₀ χ₁ h K hK
  set χ := fun i ↦ (χ₀ i).comp (ContinuousMap.fst.prodMk (h i))
  have hχ := comp_diskBoundaryInclusion_eq_endAttachingMap χ₀ χ₁ h K hK
  have hKc := castHomotopy_mem χ₀ χ₁ h K hK
  have hKs := symmHomotopy_mem χ₀ χ₁ h K hK
  set J := fiberwiseCellAttachmentIso α₀ α h h' hh hh' hh'h hhh'
    (endAttachingMap_eq α₀ χ₀ χ₁ hχ₀ h K hK)
  set E₀ := fiberwiseCellReattachment α α₁ χ χ₁ hχ hχ₁ (fun _ ↦ ContinuousMap.snd) (mapsTo_snd k)
    (castHomotopy χ₀ χ₁ h K) hKc
  set E₁ := fiberwiseCellReattachment α₁ α χ₁ χ hχ₁ hχ (fun _ ↦ ContinuousMap.snd) (mapsTo_snd k)
    (symmHomotopy χ₀ χ₁ h K) hKs
  have hE := fiberwiseCellReattachment_eq_comp_fiberwiseCellAttachmentIso α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh
    K hK h' hh' hh'h hhh'
  obtain ⟨F₁, hF₁⟩ := exists_homotopyRel_reattachment_comp_symm
    α α₁ χ χ₁ hχ hχ₁ (castHomotopy χ₀ χ₁ h K) hKc (symmHomotopy χ₀ χ₁ h K) hKs
    fun _ _ _ _ ↦ rfl
  obtain ⟨F₀, hF₀⟩ := exists_homotopyRel_reattachment_comp_symm
    α₁ α χ₁ χ hχ₁ hχ (symmHomotopy χ₀ χ₁ h K) hKs (castHomotopy χ₀ χ₁ h K) hKc
    fun i t p s ↦ by
      simp only [castHomotopy, symmHomotopy, ContinuousMap.Homotopy.cast_apply,
        ContinuousMap.Homotopy.symm_apply, symm_symm]
  refine ⟨J.inv ≫ E₁, ?_, fun y ↦ ?_, ⟨F₁.cast ?_ rfl, fun t y ↦ hF₁ t y⟩, ?_⟩
  · ext x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      fiberwiseCellAttachmentIso_inv_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]
  · rw [ConcreteCategory.comp_apply, fiberwiseCellAttachmentProj_fiberwiseCellReattachment,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIso_inv]
  · -- `E ≫ E' = E₀ ≫ J ≫ J⁻¹ ≫ E₁ = E₀ ≫ E₁`.
    rw [hE, Category.assoc, Iso.hom_inv_id_assoc]
  -- `E' ≫ E = J⁻¹ ≫ (E₁ ≫ E₀) ≫ J`, and `E₁ ≫ E₀` is homotopic to the identity.
  have hS : MapsTo J.inv (range (fiberwiseCellAttachmentIncl α₀))
      (range (fiberwiseCellAttachmentIncl α)) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, (fiberwiseCellAttachmentIso_inv_fiberwiseCellAttachmentIncl ..).symm⟩
  -- After reassociating, the two sides differ only by unfolding the local abbreviations `α`, `χ`.
  refine ⟨(homotopyRelConj J F₀ hS).cast (by rw [hE]; simp only [Category.assoc]; rfl) rfl,
    fun t y ↦ ?_⟩
  exact ((fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIso_hom ..).trans (hF₀ t _)).trans
    (fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIso_inv ..)

end HomotopyEquiv

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

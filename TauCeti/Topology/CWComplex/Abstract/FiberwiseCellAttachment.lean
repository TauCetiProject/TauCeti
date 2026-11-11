/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk.Reattachment
public import TauCeti.Topology.Category.TopCat.Pushout
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

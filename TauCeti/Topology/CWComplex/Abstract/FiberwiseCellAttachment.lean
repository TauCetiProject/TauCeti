/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk.LinearIsometry
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

When each `h i (p, ·)` is the disc map of a linear isometry `g i p` of `ℝ^{k i}`, as for the polar
factors of changes of Morse charts, `E` is a homotopy equivalence over `P` relative to `P × A`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp`), with no hypothesis on `Y` or on the
characteristic families. Its homotopy inverse is the fiberwise reattachment map `E'` of the
reversed homotopies `(t, (p, x)) ↦ K i (1 - t, (p, (g i p)⁻¹ x))`. On the `i`-th cell, `E' ∘ E`
sends `x` to `4x` when `‖x‖ ≤ 1/4`, and on the annulus `1/4 ≤ ‖x‖` reads `K i` out along the
radius and back again, so shrinking this loop to its starting point and then pushing the disc of
radius `1/4` back out to the whole disc joins it to the identity, keeping `P × A` fixed
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment`). Unlike
the comparison of a single pair of Morse charts, which inverts the reattachment map through left
inverses of the comparison maps given by Milnor's cell attachment theorem, this needs no left
inverse of a comparison map, so it applies to families of charts.

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
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 0.18 (attaching
  along homotopic maps gives homotopy equivalent spaces relative to the base).
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

/-! ### The homotopy inverse of a fiberwise reattachment map -/

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

/-- The time at which the loop homotopy reads `K i` at stage `u`, at the point of radial parameter
`s` of the annulus `1/4 ≤ ‖x‖ ≤ 1` (so `‖x‖ = 1/4 + 3s/4`): the tent `min (3s) (3(1 - s)/2)`,
rising from `0` at `‖x‖ = 1/4` to `1` at `‖x‖ = 1/2` and falling back to `0` at `‖x‖ = 1`, cut
off at `1 - u`. -/
private def reattachmentLoopTime (u s : I) : I :=
  projIcc 0 1 zero_le_one (min (min (3 * (s : ℝ)) (3 / 2 * (1 - s))) (1 - u))

private theorem continuous_reattachmentLoopTime :
    Continuous fun q : I × I ↦ reattachmentLoopTime q.1 q.2 :=
  continuous_projIcc.comp (by fun_prop)

private theorem reattachmentLoopTime_zero_right (u : I) : reattachmentLoopTime u 0 = 0 :=
  projIcc_of_le_left _ (min_le_of_left_le (min_le_of_left_le (by simp)))

private theorem reattachmentLoopTime_one_right (u : I) : reattachmentLoopTime u 1 = 0 :=
  projIcc_of_le_left _ (min_le_of_left_le (min_le_of_right_le (by simp)))

private theorem reattachmentLoopTime_one_left (s : I) : reattachmentLoopTime 1 s = 0 :=
  projIcc_of_le_left _ (min_le_of_right_le (by simp))

/-- At stage `0` the loop homotopy reads `K i` along the whole tent. -/
private theorem coe_reattachmentLoopTime_zero_left (s : I) :
    (reattachmentLoopTime 0 s : ℝ) = min (3 * (s : ℝ)) (3 / 2 * (1 - s)) := by
  have h₀ : 0 ≤ min (3 * (s : ℝ)) (3 / 2 * (1 - s)) :=
    le_min (by linarith [s.2.1]) (by linarith [s.2.2])
  have h₁ : min (3 * (s : ℝ)) (3 / 2 * (1 - s)) ≤ 1 := by
    rcases le_total (s : ℝ) (1 / 3) with hs | hs
    · exact min_le_of_left_le (by linarith)
    · exact min_le_of_right_le (by linarith)
  rw [reattachmentLoopTime, coe_projIcc, Set.Icc.coe_zero, sub_zero, min_eq_left h₁,
    min_eq_right h₁, max_eq_right h₀]

/-- The inner piece of the loop homotopy on the `i`-th family of discs: `x ↦ 4x`, read in the
`i`-th cell, on the disc of radius `1/4`. -/
private def reattachmentLoopInner (i : ι) :
    C((I × P) × closedBall (0 : EuclideanSpace ℝ (Fin (k i))) (1 / 4),
      fiberwiseCellAttachment α₁) :=
  ⟨fun q ↦ fiberwiseCellAttachmentCell α₁ i (q.1.2,
      ULift.up ⟨(4 : ℝ) • (q.2 : EuclideanSpace ℝ (Fin (k i))), mem_closedBall_zero_iff.2 (by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
        linarith [mem_closedBall_zero_iff.1 q.2.2])⟩),
    (fiberwiseCellAttachmentCell α₁ i).hom.continuous.comp ((continuous_snd.comp
      continuous_fst).prodMk (continuous_uliftUp.comp
        (((continuous_subtype_val.comp continuous_snd).const_smul (4 : ℝ)).subtype_mk _)))⟩

/-- The outer piece of the loop homotopy on the `i`-th family of discs, in the annulus coordinates
`(s, θ)` of `1/4 ≤ ‖x‖ ≤ 1`: the point `K i (reattachmentLoopTime u s, (p, θ))` of `P × A`. -/
private def reattachmentLoopOuter (i : ι) :
    C((I × P) × (I × TopCat.diskBoundary.{u} (k i)), fiberwiseCellAttachment α₁) :=
  ⟨fun q ↦ fiberwiseCellAttachmentIncl α₁ (q.1.2, ⟨K i (reattachmentLoopTime q.1.1 q.2.1,
      (q.1.2, TopCat.diskBoundaryInclusion (k i) q.2.2)), hK i _ _ _⟩),
    (fiberwiseCellAttachmentIncl α₁).hom.continuous.comp ((continuous_snd.comp
      continuous_fst).prodMk (((K i).continuous.comp ((continuous_reattachmentLoopTime.comp
        ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))).prodMk
          ((continuous_snd.comp continuous_fst).prodMk ((TopCat.diskBoundaryInclusion
            (k i)).hom.continuous.comp (continuous_snd.comp continuous_snd))))).subtype_mk _))⟩

include hχ₁ in
/-- On the seam `‖x‖ = 1/4` the two pieces of the loop homotopy agree: both are the point `θ` of
the boundary sphere of the `i`-th cell. -/
private theorem reattachmentLoopOuter_zero (i : ι) (q : I × P)
    (θ : TopCat.diskBoundary.{u} (k i)) :
    reattachmentLoopOuter α₁ χ₀ χ₁ h K hK i (q, 0, θ) =
      reattachmentLoopInner α₁ i (q, ⟨(1 / 4 : ℝ) • θ.down.1,
        TopCat.smul_diskBoundary_mem_closedBall (by norm_num) θ⟩) := by
  have hθ : reattachmentLoopInner α₁ i (q, ⟨(1 / 4 : ℝ) • θ.down.1,
      TopCat.smul_diskBoundary_mem_closedBall (by norm_num) θ⟩) =
      fiberwiseCellAttachmentCell α₁ i (q.2, TopCat.diskBoundaryInclusion (k i) θ) :=
    congrArg (fun v ↦ fiberwiseCellAttachmentCell α₁ i (q.2, v)) (ULift.ext (Subtype.ext (by
      norm_num [smul_smul, TopCat.coe_diskBoundaryInclusion_apply_down])))
  rw [hθ, fiberwiseCellAttachmentCell_diskBoundaryInclusion]
  simp only [reattachmentLoopOuter, ContinuousMap.coe_mk, reattachmentLoopTime_zero_right,
    ContinuousMap.Homotopy.apply_zero, hχ₁, Subtype.coe_eta]

/-- The homotopy on the cylinder over the `i`-th family of discs that shrinks the loop in which a
reattachment map followed by its reversal reads `K i`: `x ↦ 4x` on the disc of radius `1/4`, and
on the annulus `1/4 ≤ ‖x‖` the point `K i (reattachmentLoopTime u s, (p, θ))` in annulus
coordinates. -/
private def reattachmentLoopCell (i : ι) :
    C(I × (P × TopCat.disk.{u} (k i)), fiberwiseCellAttachment α₁) :=
  (TopCat.discGlue (by norm_num : (0 : ℝ) < 1 / 4) (reattachmentLoopInner α₁ i)
      (reattachmentLoopOuter α₁ χ₀ χ₁ h K hK i)
      (reattachmentLoopOuter_zero α₁ χ₀ χ₁ hχ₁ h K hK i)).comp
    ⟨fun q ↦ ((q.1, q.2.1), q.2.2), by fun_prop⟩

private theorem reattachmentLoopCell_of_norm_le (i : ι) (u : I) (p : P)
    {w v : TopCat.disk.{u} (k i)} (hw : ‖w.down.1‖ ≤ 1 / 4) (hv : v.down.1 = (4 : ℝ) • w.down.1) :
    reattachmentLoopCell α₁ χ₀ χ₁ hχ₁ h K hK i (u, (p, w)) =
      fiberwiseCellAttachmentCell α₁ i (p, v) := by
  simp only [reattachmentLoopCell, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [TopCat.discGlue_apply_of_norm_le _ _ _ _ _ hw]
  exact congrArg (fun v ↦ fiberwiseCellAttachmentCell α₁ i (p, v))
    (ULift.ext (Subtype.ext hv.symm))

private theorem reattachmentLoopCell_of_le_norm (i : ι) (u : I) (p : P)
    {w : TopCat.disk.{u} (k i)} (hw : 1 / 4 ≤ ‖w.down.1‖) :
    reattachmentLoopCell α₁ χ₀ χ₁ hχ₁ h K hK i (u, (p, w)) =
      fiberwiseCellAttachmentIncl α₁ (p, ⟨K i (reattachmentLoopTime u
        (TopCat.annulusParam (1 / 4) w), (p, TopCat.diskBoundaryInclusion (k i)
          (TopCat.annulusDir (by norm_num) ⟨w, hw⟩))), hK i _ _ _⟩) := by
  simp only [reattachmentLoopCell, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [TopCat.discGlue_apply_of_le_norm _ _ _ _ _ hw]
  rfl

/-- The loop homotopy on the whole fiberwise adjunction space: constant on `P × A`, and
`TauCeti.reattachmentLoopCell` on the cylinders over the cells. -/
private def reattachmentLoopMap : C(I × fiberwiseCellAttachment α₁, fiberwiseCellAttachment α₁) :=
  fiberwiseCellAttachmentCylinderDesc α₁
    ((fiberwiseCellAttachmentIncl α₁).hom.comp ContinuousMap.snd)
    (reattachmentLoopCell α₁ χ₀ χ₁ hχ₁ h K hK) fun i t p s ↦ by
      have hw : 1 / 4 ≤ ‖(TopCat.diskBoundaryInclusion (k i) s).down.1‖ := by
        rw [TopCat.norm_diskBoundaryInclusion]
        norm_num
      rw [reattachmentLoopCell_of_le_norm (hw := hw)]
      simp only [TopCat.annulusParam_of_norm_eq_one (by norm_num : (1 / 4 : ℝ) < 1)
        (TopCat.norm_diskBoundaryInclusion s), reattachmentLoopTime_one_right,
        TopCat.annulusDir_diskBoundaryInclusion, ContinuousMap.Homotopy.apply_zero, hχ₁,
        Subtype.coe_eta, ContinuousMap.comp_apply, ContinuousMap.snd_apply]

/-- The radial homotopy on the cylinder over the `i`-th family of discs, from the push
`x ↦ x / max (1/4) ‖x‖` at time `0` to the identity at time `1`, read in the `i`-th cell. -/
private def reattachmentPushCell (i : ι) :
    C(I × (P × TopCat.disk.{u} (k i)), fiberwiseCellAttachment α₁) :=
  ⟨fun q ↦ fiberwiseCellAttachmentCell α₁ i
      (q.2.1, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (σ q.1, q.2.2)),
    (fiberwiseCellAttachmentCell α₁ i).hom.continuous.comp ((continuous_fst.comp
      continuous_snd).prodMk ((TopCat.diskRadialPush (k i) _).continuous.comp
        ((continuous_symm.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))))⟩

/-- The radial homotopy on the whole fiberwise adjunction space: constant on `P × A`, and
`TauCeti.reattachmentPushCell` on the cylinders over the cells. -/
private def reattachmentPushMap : C(I × fiberwiseCellAttachment α₁, fiberwiseCellAttachment α₁) :=
  fiberwiseCellAttachmentCylinderDesc α₁
    ((fiberwiseCellAttachmentIncl α₁).hom.comp ContinuousMap.snd)
    (reattachmentPushCell α₁) fun i t p s ↦ by
      simp only [reattachmentPushCell, ContinuousMap.coe_mk,
        TopCat.diskRadialPush_diskBoundaryInclusion (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)]
      exact fiberwiseCellAttachmentCell_diskBoundaryInclusion α₁ i p s

private theorem reattachmentLoopMap_fiberwiseCellAttachmentIncl (t : I) (x : P × A) :
    reattachmentLoopMap α₁ χ₀ χ₁ hχ₁ h K hK (t, fiberwiseCellAttachmentIncl α₁ x) =
      fiberwiseCellAttachmentIncl α₁ x :=
  fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ _ _ t x

private theorem reattachmentLoopMap_fiberwiseCellAttachmentCell (t : I) (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    reattachmentLoopMap α₁ χ₀ χ₁ hχ₁ h K hK (t, fiberwiseCellAttachmentCell α₁ i x) =
      reattachmentLoopCell α₁ χ₀ χ₁ hχ₁ h K hK i (t, x) :=
  fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell α₁ _ _ _ t i x

private theorem reattachmentPushMap_fiberwiseCellAttachmentIncl (t : I) (x : P × A) :
    reattachmentPushMap α₁ (t, fiberwiseCellAttachmentIncl α₁ x) =
      fiberwiseCellAttachmentIncl α₁ x :=
  fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ _ _ t x

private theorem reattachmentPushMap_fiberwiseCellAttachmentCell (t : I) (i : ι)
    (x : P × TopCat.disk.{u} (k i)) :
    reattachmentPushMap α₁ (t, fiberwiseCellAttachmentCell α₁ i x) =
      fiberwiseCellAttachmentCell α₁ i
        (x.1, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (σ t, x.2)) :=
  fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell α₁ _ _ _ t i x

private theorem fiberwiseCellAttachmentProj_reattachmentLoopMap (t : I)
    (y : fiberwiseCellAttachment α₁) :
    fiberwiseCellAttachmentProj α₁ (reattachmentLoopMap α₁ χ₀ χ₁ hχ₁ h K hK (t, y)) =
      fiberwiseCellAttachmentProj α₁ y := by
  refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
  · rw [reattachmentLoopMap_fiberwiseCellAttachmentIncl]
  rw [reattachmentLoopMap_fiberwiseCellAttachmentCell,
    fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]
  obtain ⟨p, w⟩ := x
  rcases le_total ‖w.down.1‖ (1 / 4) with hw | hw
  · obtain ⟨v, hv⟩ : ∃ v : TopCat.disk.{u} (k i), v.down.1 = (4 : ℝ) • w.down.1 :=
      ⟨TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, w), by
        rw [TopCat.coe_diskRadialPush_one_of_norm_le _ hw]
        norm_num⟩
    rw [reattachmentLoopCell_of_norm_le (hw := hw) (hv := hv),
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]
  · rw [reattachmentLoopCell_of_le_norm (hw := hw),
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl]

private theorem fiberwiseCellAttachmentProj_reattachmentPushMap (t : I)
    (y : fiberwiseCellAttachment α₁) :
    fiberwiseCellAttachmentProj α₁ (reattachmentPushMap α₁ (t, y)) =
      fiberwiseCellAttachmentProj α₁ y := by
  refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
  · rw [reattachmentPushMap_fiberwiseCellAttachmentIncl]
  · rw [reattachmentPushMap_fiberwiseCellAttachmentCell,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]

/-- At stage `1` the loop has shrunk to the attaching sphere, and the loop homotopy is the radial
push `x ↦ x / max (1/4) ‖x‖`, read in the `i`-th cell. -/
private theorem reattachmentLoopCell_one_left (i : ι) (x : P × TopCat.disk.{u} (k i)) :
    reattachmentLoopCell α₁ χ₀ χ₁ hχ₁ h K hK i (1, x) = reattachmentPushCell α₁ i (0, x) := by
  obtain ⟨p, w⟩ := x
  simp only [reattachmentPushCell, ContinuousMap.coe_mk, symm_zero]
  rcases le_total ‖w.down.1‖ (1 / 4) with hw | hw
  · refine reattachmentLoopCell_of_norm_le α₁ χ₀ χ₁ hχ₁ h K hK i 1 p hw ?_
    rw [TopCat.coe_diskRadialPush_one_of_norm_le _ hw]
    norm_num
  · rw [reattachmentLoopCell_of_le_norm (hw := hw), ← TopCat.diskBoundaryInclusion_annulusDir
      (by norm_num : (0 : ℝ) < 1 / 4) ⟨w, hw⟩, fiberwiseCellAttachmentCell_diskBoundaryInclusion]
    simp only [reattachmentLoopTime_one_left, ContinuousMap.Homotopy.apply_zero, hχ₁,
      Subtype.coe_eta]

/-- The second stage of the homotopy from `E' ∘ E` to the identity: the radial homotopy from the
push `x ↦ x / max (1/4) ‖x‖` of the cells to the identity, relative to `P × A`. -/
private def reattachmentPushHomotopy :
    ((reattachmentPushMap α₁).curry 0).HomotopyRel (ContinuousMap.id _)
      (range (fiberwiseCellAttachmentIncl α₁)) where
  toFun := reattachmentPushMap α₁
  continuous_toFun := (reattachmentPushMap α₁).continuous
  map_zero_left _ := rfl
  map_one_left y := by
    refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact reattachmentPushMap_fiberwiseCellAttachmentIncl α₁ 1 x
    · rw [reattachmentPushMap_fiberwiseCellAttachmentCell, symm_one, TopCat.diskRadialPush_zero]
      rfl
  prop' t y hy := by
    obtain ⟨x, rfl⟩ := hy
    exact (reattachmentPushMap_fiberwiseCellAttachmentIncl α₁ t x).trans
      (reattachmentPushMap_fiberwiseCellAttachmentIncl α₁ 0 x).symm

variable (g : ∀ i, P → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)))
  (hg : ∀ i p w, h i (p, w) = (g i p).diskMap w)
  (hg' : ∀ i p w, h' i (p, w) = (g i p).symm.diskMap w)
  (hK'K : ∀ i t p w, K' i (t, (p, w)) = K i (σ t, (p, h' i (p, w))))

include hg hg' hK'K in
/-- At stage `0` the loop homotopy is the fiberwise reattachment map `E` followed by its reversal
`E'`. On the `i`-th cell over `p`, `E' ∘ E` sends `x` to the point `g⁻¹ (2 g (2x)) = 4x` of the cell
when `‖x‖ ≤ 1/4`; to `K i (4‖x‖ - 1, (p, x/‖x‖))` when `1/4 ≤ ‖x‖ ≤ 1/2`, where `E'` reads the
reversal of `K i`; and to `K i (2 - 2‖x‖, (p, x/‖x‖))` when `1/2 ≤ ‖x‖`, where `E` reads `K i`. -/
private theorem reattachmentLoopCell_zero_left (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    reattachmentLoopCell α₁ χ₀ χ₁ hχ₁ h K hK i (0, (p, w)) =
      fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK'
        (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK
          (fiberwiseCellAttachmentCell α₁ i (p, w))) := by
  rcases le_total ‖w.down.1‖ (1 / 2) with hw₂ | hw₂
  swap
  · -- Outside the disc of radius `1/2`, `E` reads `K i` and `E'` is the identity on `P × A`.
    have hw₄ : 1 / 4 ≤ ‖w.down.1‖ := by linarith
    have ht : reattachmentLoopTime 0 (TopCat.annulusParam (1 / 4) w) =
        TopCat.reattachmentTime w := by
      have hs := TopCat.add_one_sub_mul_annulusParam (by norm_num : (1 / 4 : ℝ) ≤ 1) hw₄
      refine Subtype.ext ?_
      rw [coe_reattachmentLoopTime_zero_left, TopCat.coe_reattachmentTime_of_le_norm hw₂,
        min_eq_right (by linarith)]
      linarith
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hw₂)
        (ht := TopCat.coe_reattachmentTime_of_le_norm hw₂)
        (hs := TopCat.coe_annulusDir (by norm_num : (0 : ℝ) < 1 / 4) ⟨w, hw₄⟩),
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      reattachmentLoopCell_of_le_norm (hw := hw₄)]
    simp only [ht]
  -- On the disc of radius `1/2`, `E` sends `x` to the point `y = g (2x)` of the `i`-th cell.
  set y := h i (p, TopCat.reattachmentRadial w) with hy
  have hyw : y.down.1 = g i p ((2 : ℝ) • w.down.1) := by
    rw [hy, hg, LinearIsometryEquiv.coe_diskMap_apply_down,
      TopCat.coe_reattachmentRadial_of_norm_le hw₂]
  have hny : ‖y.down.1‖ = 2 * ‖w.down.1‖ := by
    rw [hyw, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_two]
  have hgy : (g i p).symm y.down.1 = (2 : ℝ) • w.down.1 := by
    rw [hyw, LinearIsometryEquiv.symm_apply_apply]
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hw₂)
    (hv := TopCat.coe_reattachmentRadial_of_norm_le hw₂)]
  rcases le_total ‖w.down.1‖ (1 / 4) with hw₄ | hw₄
  · -- On the disc of radius `1/4`, `E'` sends `y` to the point `g⁻¹ (2y) = 4x` of the cell.
    have hy₂ : ‖y.down.1‖ ≤ 1 / 2 := by
      rw [hny]
      linarith
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hy₂)
      (hv := TopCat.coe_reattachmentRadial_of_norm_le hy₂)]
    refine reattachmentLoopCell_of_norm_le α₁ χ₀ χ₁ hχ₁ h K hK i 0 p hw₄ ?_
    rw [hg', LinearIsometryEquiv.coe_diskMap_apply_down,
      TopCat.coe_reattachmentRadial_of_norm_le hy₂, map_smul, hgy, smul_smul]
    norm_num
  -- On the annulus `1/4 ≤ ‖x‖ ≤ 1/2`, `E'` reads the reversal of `K i` in the direction of `x`.
  have hy₂ : 1 / 2 ≤ ‖y.down.1‖ := by
    rw [hny]
    linarith
  have ht : reattachmentLoopTime 0 (TopCat.annulusParam (1 / 4) w) =
      σ (TopCat.reattachmentTime y) := by
    have hs := TopCat.add_one_sub_mul_annulusParam (by norm_num : (1 / 4 : ℝ) ≤ 1) hw₄
    refine Subtype.ext ?_
    rw [coe_reattachmentLoopTime_zero_left, coe_symm_eq, TopCat.coe_reattachmentTime_of_le_norm hy₂,
      hny, min_eq_left (by linarith)]
    linarith
  have hθ : TopCat.diskBoundaryInclusion (k i) (TopCat.annulusDir (by norm_num) ⟨w, hw₄⟩) =
      h' i (p, TopCat.diskBoundaryInclusion (k i) (TopCat.annulusDir (by norm_num) ⟨y, hy₂⟩)) := by
    have hw0 : ‖w.down.1‖ ≠ 0 := by linarith
    refine ULift.ext (Subtype.ext ?_)
    rw [hg', LinearIsometryEquiv.coe_diskMap_apply_down,
      TopCat.coe_diskBoundaryInclusion_apply_down, TopCat.coe_diskBoundaryInclusion_apply_down,
      TopCat.coe_annulusDir, TopCat.coe_annulusDir, map_smul, hgy, hny, smul_smul]
    congr 1
    field_simp
  rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hy₂)
      (ht := TopCat.coe_reattachmentTime_of_le_norm hy₂)
      (hs := TopCat.coe_annulusDir (by norm_num : (0 : ℝ) < 1 / 2) ⟨y, hy₂⟩),
    reattachmentLoopCell_of_le_norm (hw := hw₄)]
  simp only [hK'K, ht, hθ]

include hg hg' hK'K in
/-- The first stage of the homotopy from `E' ∘ E` to the identity: shrinking the loop in which `E'`
reads the reversal of the homotopies `K i` after `E` reads them, relative to `P × A`. -/
private def reattachmentLoopHomotopy :
    (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫
        fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK').hom.HomotopyRel
      ((reattachmentPushMap α₁).curry 0) (range (fiberwiseCellAttachmentIncl α₁)) where
  toFun := reattachmentLoopMap α₁ χ₀ χ₁ hχ₁ h K hK
  continuous_toFun := (reattachmentLoopMap α₁ χ₀ χ₁ hχ₁ h K hK).continuous
  map_zero_left y := by
    rw [TopCat.hom_comp, ContinuousMap.comp_apply]
    refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · rw [reattachmentLoopMap_fiberwiseCellAttachmentIncl,
        fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
        fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]
    · rw [reattachmentLoopMap_fiberwiseCellAttachmentCell]
      exact reattachmentLoopCell_zero_left α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h h' hh hh' K hK K' hK' g hg hg'
        hK'K i x.1 x.2
  map_one_left y := by
    refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact (reattachmentLoopMap_fiberwiseCellAttachmentIncl α₁ χ₀ χ₁ hχ₁ h K hK 1 x).trans
        (reattachmentPushMap_fiberwiseCellAttachmentIncl α₁ 0 x).symm
    · exact (reattachmentLoopMap_fiberwiseCellAttachmentCell α₁ χ₀ χ₁ hχ₁ h K hK 1 i x).trans
        ((reattachmentLoopCell_one_left α₁ χ₀ χ₁ hχ₁ h K hK i x).trans
          (reattachmentPushMap_fiberwiseCellAttachmentCell α₁ 0 i x).symm)
  prop' t y hy := by
    obtain ⟨x, rfl⟩ := hy
    refine (reattachmentLoopMap_fiberwiseCellAttachmentIncl α₁ χ₀ χ₁ hχ₁ h K hK t x).trans ?_
    rw [TopCat.hom_comp, ContinuousMap.comp_apply,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]

include hg hg' hK'K in
/-- **Reattaching along an orthogonal family and back is homotopic to the identity, over `P` and
relative to `P × A`.** Let `h i (p, ·)` and `h' i (p, ·)` be the disc maps of a linear isometry
`g i p` of `ℝ^{k i}` and of its inverse, and let `K' i (t, (p, x)) = K i (1 - t, (p, h' i (p, x)))`
reverse the homotopies `K i : χ₁ i ≃ χ₀ i ∘ (p, h i)`. Then the fiberwise reattachment map
`E` of the `K i` followed by the fiberwise reattachment map `E'` of the `K' i` is homotopic to the
identity relative to `P × A`, through maps over `P`. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment :
    ∃ H : (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫
        fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK').hom.HomotopyRel
          (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₁)),
      ∀ t y, fiberwiseCellAttachmentProj α₁ (H (t, y)) = fiberwiseCellAttachmentProj α₁ y := by
  refine ⟨(reattachmentLoopHomotopy α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h h' hh hh' K hK K' hK' g hg hg'
    hK'K).trans (reattachmentPushHomotopy α₁), fun t y ↦ ?_⟩
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · exact fiberwiseCellAttachmentProj_reattachmentLoopMap α₁ χ₀ χ₁ hχ₁ h K hK _ y
  · exact fiberwiseCellAttachmentProj_reattachmentPushMap α₁ _ y

include hg in
/-- **A fiberwise reattachment map along an orthogonal family is a homotopy equivalence over `P`
relative to `P × A`.** Let `h i (p, ·)` be the disc map of a linear isometry `g i p` of `ℝ^{k i}`,
such as the polar factor of a change of Morse chart, and let `K i : χ₁ i ≃ χ₀ i ∘ (p, h i)` be
homotopies keeping `P × ∂D^{k i}` in `A`. Then the fiberwise reattachment map
`E : (P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i}) → (P × A) ∪_{α₀} ⨆ᵢ (P × D^{k i})` has a homotopy inverse
`E'` over `P` which is the identity on `P × A`, and both composites are homotopic to the identities
relative to `P × A` through maps over `P`. The inverse is the fiberwise reattachment map of the
reversed homotopies `(t, (p, x)) ↦ K i (1 - t, (p, (g i p)⁻¹ x))`. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_comp :
    ∃ E' : fiberwiseCellAttachment α₀ ⟶ fiberwiseCellAttachment α₁,
      fiberwiseCellAttachmentIncl α₀ ≫ E' = fiberwiseCellAttachmentIncl α₁ ∧
      (∀ y, fiberwiseCellAttachmentProj α₁ (E' y) = fiberwiseCellAttachmentProj α₀ y) ∧
      (∃ H : (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫ E').hom.HomotopyRel
          (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₁)),
        ∀ t y, fiberwiseCellAttachmentProj α₁ (H (t, y)) = fiberwiseCellAttachmentProj α₁ y) ∧
      ∃ H : (E' ≫ fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK).hom.HomotopyRel
          (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₀)),
        ∀ t y, fiberwiseCellAttachmentProj α₀ (H (t, y)) = fiberwiseCellAttachmentProj α₀ y := by
  -- The disc maps of the inverse isometries form a continuous family.
  let h' (i : ι) : C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)) :=
    ⟨fun q ↦ (g i q.1).symm.diskMap q.2,
      TopCat.continuous_diskMap_symm ((h i).continuous.congr fun q ↦ hg i q.1 q.2)⟩
  have hg' (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
      h' i (p, w) = (g i p).symm.diskMap w :=
    rfl
  have hhh' (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) : h i (p, h' i (p, w)) = w :=
    ULift.ext (Subtype.ext (by
      rw [hg, LinearIsometryEquiv.coe_diskMap_apply_down, hg',
        LinearIsometryEquiv.coe_diskMap_apply_down, LinearIsometryEquiv.apply_symm_apply]))
  have hh'h (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) : h' i (p, h i (p, w)) = w :=
    ULift.ext (Subtype.ext (by
      rw [hg', LinearIsometryEquiv.coe_diskMap_apply_down, hg,
        LinearIsometryEquiv.coe_diskMap_apply_down, LinearIsometryEquiv.symm_apply_apply]))
  have hh' (i : ι) (p : P) : MapsTo (fun w ↦ h' i (p, w))
      (range (TopCat.diskBoundaryInclusion (k i))) (range (TopCat.diskBoundaryInclusion (k i))) :=
    fun _ hw ↦ (g i p).symm.mapsTo_diskMap_range_diskBoundaryInclusion hw
  -- The reversed homotopies `K' i : χ₀ i ≃ χ₁ i ∘ (p, h' i)`.
  let K' (i : ι) : (χ₀ i).Homotopy ((χ₁ i).comp (ContinuousMap.fst.prodMk (h' i))) :=
    { toFun q := K i (σ q.1, (q.2.1, h' i q.2))
      continuous_toFun := (K i).continuous.comp ((continuous_symm.comp continuous_fst).prodMk
        ((continuous_fst.comp continuous_snd).prodMk ((h' i).continuous.comp continuous_snd)))
      map_zero_left x := by
        simp only [symm_zero, ContinuousMap.Homotopy.apply_one, ContinuousMap.comp_apply,
          ContinuousMap.prod_eval, ContinuousMap.fst_apply, hhh', Prod.mk.eta]
      map_one_left x := by
        simp only [symm_one, ContinuousMap.Homotopy.apply_zero, ContinuousMap.comp_apply,
          ContinuousMap.prod_eval, ContinuousMap.fst_apply] }
  have hK'K (i : ι) (t : I) (p : P) (w : TopCat.disk.{u} (k i)) :
      K' i (t, (p, w)) = K i (σ t, (p, h' i (p, w))) :=
    rfl
  have hK' (i : ι) (t : I) (p : P) (s : TopCat.diskBoundary.{u} (k i)) :
      K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A := by
    obtain ⟨s', hs'⟩ := hh' i p ⟨s, rfl⟩
    have hs'' : TopCat.diskBoundaryInclusion (k i) s' =
        h' i (p, TopCat.diskBoundaryInclusion (k i) s) := hs'
    rw [hK'K, ← hs'']
    exact hK i _ p s'
  have hKK' (i : ι) (t : I) (p : P) (w : TopCat.disk.{u} (k i)) :
      K i (t, (p, w)) = K' i (σ t, (p, h i (p, w))) := by
    rw [hK'K, symm_symm, hh'h]
  refine ⟨fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK', ?_,
    fiberwiseCellAttachmentProj_fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK',
    exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀
      hχ₁ h h' hh hh' K hK K' hK' g hg hg' hK'K,
    exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁
      hχ₀ h' h hh' hh K' hK' K hK (fun i p ↦ (g i p).symm) hg' (fun i p w ↦ by
        rw [LinearIsometryEquiv.symm_symm]
        exact hg i p w) hKK'⟩
  ext x
  rw [ConcreteCategory.comp_apply]
  exact fiberwiseCellReattachment_fiberwiseCellAttachmentIncl α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK' x

end Inverse

end TauCeti

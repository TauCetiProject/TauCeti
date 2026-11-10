/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk.Annulus
import TauCeti.Topology.Homotopy.Homotopic.Rel
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import TauCeti.Topology.Category.TopCat.Pushout

/-!
# Attaching cells fibrewise over a parameter space, and reattaching them along homotopies

Let `P` be a parameter space and `Z` a space. A family of attaching maps
`αᵢ : P × ∂D^{k i} → Z` attaches, for each parameter `p`, one `k i`-disc to `Z` along each
`αᵢ (p, ·)`. Doing this for all parameters at once gives the **fibrewise adjunction space**

`(P × Z) ∪_α ⨆ᵢ (P × D^{k i})`,

the pushout in `TopCat` of `(p, s) ↦ (p, αᵢ (p, s))` along the inclusions
`P × ∂D^{k i} → P × D^{k i}` (`TauCeti.fiberwiseCellAttachment`). It lies over `P`
(`TauCeti.fiberwiseCellAttachmentProj`), and its points over `p` are those of
`Z ∪_{α (p, ·)} ⨆ᵢ D^{k i}`.
When `Z` maps to a space `X` by `e` and the attaching maps extend to characteristic maps
`χᵢ : P × D^{k i} → X`, the inclusion of `P × Z` and the characteristic maps induce the
comparison map `Φ : (P × Z) ∪_α ⨆ᵢ (P × D^{k i}) → P × X` over `P`
(`TauCeti.fiberwiseCellComparison`).

Milnor compares the cells attached by two families of attaching maps `α₀`, `α₁` along a homotopy.
Let `hᵢ` be a family of self-maps of the disc pairs `(D^{k i}, ∂D^{k i})`, with restrictions
`hbᵢ` to the boundary spheres, and let `Hᵢ` be a homotopy from `α₁ᵢ` to `α₀ᵢ ∘ hbᵢ`, all
depending continuously on `p`. The **reattachment map**

`E : (P × Z) ∪_{α₁} ⨆ᵢ (P × D^{k i}) → (P × Z) ∪_{α₀} ⨆ᵢ (P × D^{k i})`

(`TauCeti.fiberwiseCellReattachment`) is the identity on `P × Z`, sends the point `(p, x)` of the
`i`-th cell with `‖x‖ ≤ 1/2` to the point `(p, hᵢ (p, 2x))` of the `i`-th cell, and sends a point
with `1/2 ≤ ‖x‖` to the point `(p, Hᵢ (2 - 2‖x‖, (p, x/‖x‖)))` of `P × Z`. It is a map over `P`.

If the homotopy `Hᵢ` is the restriction to the boundary spheres of a homotopy `Kᵢ` from the
characteristic map `χ₁ᵢ` to `χ₀ᵢ ∘ hᵢ`, then `Φ₀ ∘ E` is homotopic to `Φ₁` relative to `P × Z` by a
homotopy over `P`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellComparison`). If
`Φ₀` has a left inverse `g₀` over `P`, it follows that `E` is homotopic to `g₀ ∘ Φ₁` relative to
`P × Z` over `P`, so that the relative homotopy class of `E` over `P` does not depend on the
homotopies, and that reattachment maps compose up to homotopy relative to `P × Z` over `P`.
All constructions are natural in the parameter space: along a map `u : P' → P`, the attachment
for the data pulled back to `P'` maps to the attachment for the data on `P`
(`TauCeti.fiberwiseCellAttachmentMap`), functorially in `u`, lying over `u`, and compatibly with
the comparison maps and the reattachment maps.

For a one-point parameter space this is Milnor's comparison of the cells attached across a
critical level of a Morse function by two choices of normal-form charts, with `Z` the sublevel
below the critical level and `X` the sublevel above it. Families over a compact parameter space
compare such choices continuously in a parameter.

## Main definitions

* `TauCeti.fiberwiseCellAttachment`: the fibrewise adjunction space
  `(P × Z) ∪_α ⨆ᵢ (P × D^{k i})`.
* `TauCeti.fiberwiseCellAttachmentProj`: its projection to `P`.
* `TauCeti.fiberwiseCellComparison`: the comparison map to `P × X` of a family of characteristic
  maps.
* `TauCeti.fiberwiseCellReattachment`: the reattachment map along a family of homotopies of
  attaching maps.
* `TauCeti.fiberwiseCellAttachmentMap`: the map of attachments induced by a map of parameter
  spaces.

## Main results

* `TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellComparison`:
  `Φ₀ ∘ E` is homotopic to `Φ₁` relative to `P × Z`, over `P`.
* `TauCeti.exists_homotopyRel_fiberwiseCellReattachment_of_leftInverse`: for a left inverse `g₀`
  of `Φ₀` over `P`, `E` is homotopic to `g₀ ∘ Φ₁` relative to `P × Z`, over `P`.
* `TauCeti.exists_homotopyRel_fiberwiseCellReattachment_fiberwiseCellReattachment`: two
  reattachment maps between the same attachments, whose homotopies extend to homotopies of the
  same characteristic maps, are homotopic relative to `P × Z`, over `P`, provided `Φ₀` has a left
  inverse over `P`.
* `TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment`:
  reattachment maps whose homotopies extend to homotopies of characteristic maps compose up to
  homotopy relative to `P × Z`, over `P`, provided `Φ₀` has a left inverse over `P`.
* `TauCeti.fiberwiseCellAttachmentMap_id`, `TauCeti.fiberwiseCellAttachmentMap_comp`: the maps
  induced by maps of parameter spaces are functorial.
* `TauCeti.fiberwiseCellReattachment_comp_fiberwiseCellAttachmentMap`: reattachment maps commute
  with the maps induced by a map of parameter spaces.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 3.6 and Remark 3.3.
-/

public section

noncomputable section

open Function Set Metric Topology CategoryTheory CategoryTheory.Limits unitInterval

universe u

namespace TauCeti

variable {P Z : Type u} [TopologicalSpace P] [TopologicalSpace Z] {ι : Type u} {k : ι → ℕ}

section Attachment

/-- The fibrewise attaching map `⨆ᵢ (P × ∂D^{k i}) → P × Z`, `(p, s) ↦ (p, αᵢ (p, s))`, of a family
of attaching maps `αᵢ : P × ∂D^{k i} → Z`. -/
def fiberwiseAttachingMap (α : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), Z)) :
    (∐ fun i ↦ TopCat.of (P × TopCat.diskBoundary.{u} (k i))) ⟶ TopCat.of (P × Z) :=
  Sigma.desc fun i ↦ TopCat.ofHom (ContinuousMap.fst.prodMk (α i))

/-- The inclusion `⨆ᵢ (P × ∂D^{k i}) → ⨆ᵢ (P × D^{k i})` of the boundaries of the cells over `P`. -/
def fiberwiseBoundaryInclusion (P : Type u) [TopologicalSpace P] (k : ι → ℕ) :
    (∐ fun i ↦ TopCat.of (P × TopCat.diskBoundary.{u} (k i))) ⟶
      ∐ fun i ↦ TopCat.of (P × TopCat.disk.{u} (k i)) :=
  Limits.Sigma.map fun i ↦ TopCat.ofHom
    ((ContinuousMap.id P).prodMap (TopCat.diskBoundaryInclusion.{u} (k i)).hom)

/-- The **fibrewise adjunction space** `(P × Z) ∪_α ⨆ᵢ (P × D^{k i})` of a family of attaching maps
`αᵢ : P × ∂D^{k i} → Z`: for each parameter `p`, one `k i`-disc is attached to `Z` along
`αᵢ (p, ·)`. It is the pushout in `TopCat` of the fibrewise attaching map along the inclusion of
the boundaries of the cells (`TauCeti.isPushout_fiberwiseCellAttachment`). -/
def fiberwiseCellAttachment (α : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), Z)) : TopCat.{u} :=
  pushout (fiberwiseAttachingMap α) (fiberwiseBoundaryInclusion P k)

variable (α : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), Z))

/-- The inclusion of `P × Z` into the fibrewise adjunction space. -/
def fiberwiseCellAttachmentIncl : TopCat.of (P × Z) ⟶ fiberwiseCellAttachment α :=
  pushout.inl _ _

/-- The characteristic map `P × D^{k i} → (P × Z) ∪_α ⨆ᵢ (P × D^{k i})` of the `i`-th cells. -/
def fiberwiseCellAttachmentCell (i : ι) :
    TopCat.of (P × TopCat.disk.{u} (k i)) ⟶ fiberwiseCellAttachment α :=
  Sigma.ι (fun i ↦ TopCat.of (P × TopCat.disk.{u} (k i))) i ≫ pushout.inr _ _

/-- The fibrewise adjunction space is the pushout of the fibrewise attaching map along the
inclusion of the boundaries of the cells, with the inclusion of `P × Z` and the characteristic
maps of the cells as its legs. -/
theorem isPushout_fiberwiseCellAttachment :
    IsPushout (fiberwiseAttachingMap α) (fiberwiseBoundaryInclusion P k)
      (fiberwiseCellAttachmentIncl α) (Sigma.desc (fiberwiseCellAttachmentCell α)) := by
  have h : Sigma.desc (fiberwiseCellAttachmentCell α) =
      (pushout.inr _ _ : _ ⟶ fiberwiseCellAttachment α) :=
    Sigma.hom_ext _ _ fun i ↦ by rw [Sigma.ι_comp_desc, fiberwiseCellAttachmentCell]
  rw [h]
  exact IsPushout.of_hasPushout _ _

/-- On the boundary sphere, the characteristic map of a cell is the attaching map followed by the
inclusion of `P × Z`. -/
theorem fiberwiseCellAttachmentIncl_apply_attaching (i : ι) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    fiberwiseCellAttachmentIncl α (p, α i (p, s)) =
      fiberwiseCellAttachmentCell α i (p, TopCat.diskBoundaryInclusion (k i) s) := by
  have := (isPushout_fiberwiseCellAttachment α).w_apply
    (Sigma.ι (fun i ↦ TopCat.of (P × TopCat.diskBoundary.{u} (k i))) i (p, s))
  simpa [fiberwiseAttachingMap, fiberwiseBoundaryInclusion, Sigma.ι_map_apply,
    fiberwiseCellAttachmentIncl] using this

/-- A map on `P × Z` and maps on the cells `P × D^{k i}` which agree along the attaching maps
induce a map out of the fibrewise adjunction space. -/
def fiberwiseCellAttachmentDesc {W : TopCat.{u}} (g : TopCat.of (P × Z) ⟶ W)
    (G : ∀ i, TopCat.of (P × TopCat.disk.{u} (k i)) ⟶ W)
    (hG : ∀ i p s, g (p, α i (p, s)) = G i (p, TopCat.diskBoundaryInclusion (k i) s)) :
    fiberwiseCellAttachment α ⟶ W :=
  (isPushout_fiberwiseCellAttachment α).desc g (Sigma.desc G) <| Sigma.hom_ext _ _ fun i ↦ by
    ext ⟨p, s⟩
    simpa [fiberwiseAttachingMap, fiberwiseBoundaryInclusion, Sigma.ι_map_apply] using hG i p s

variable {α} {W : TopCat.{u}} (g : TopCat.of (P × Z) ⟶ W)
  (G : ∀ i, TopCat.of (P × TopCat.disk.{u} (k i)) ⟶ W)
  (hG : ∀ i p s, g (p, α i (p, s)) = G i (p, TopCat.diskBoundaryInclusion (k i) s))

/-- The induced map out of the fibrewise adjunction space restricts to `g` on `P × Z`. -/
@[reassoc (attr := simp)]
theorem fiberwiseCellAttachmentIncl_desc :
    fiberwiseCellAttachmentIncl α ≫ fiberwiseCellAttachmentDesc α g G hG = g :=
  IsPushout.inl_desc _ _ _ _

/-- The induced map out of the fibrewise adjunction space restricts to `G i` on the `i`-th
cells. -/
@[reassoc (attr := simp)]
theorem fiberwiseCellAttachmentCell_desc (i : ι) :
    fiberwiseCellAttachmentCell α i ≫ fiberwiseCellAttachmentDesc α g G hG = G i := by
  rw [fiberwiseCellAttachmentDesc, ← Sigma.ι_comp_desc (fiberwiseCellAttachmentCell α) i,
    Category.assoc, IsPushout.inr_desc, Sigma.ι_comp_desc]

/-- The induced map out of the fibrewise adjunction space sends a point of `P × Z` to its value
under `g`. -/
@[simp]
theorem fiberwiseCellAttachmentDesc_incl (x : P × Z) :
    fiberwiseCellAttachmentDesc α g G hG (fiberwiseCellAttachmentIncl α x) = g x := by
  rw [← ConcreteCategory.comp_apply, fiberwiseCellAttachmentIncl_desc]

/-- The induced map out of the fibrewise adjunction space sends a point of the `i`-th cells to
its value under `G i`. -/
@[simp]
theorem fiberwiseCellAttachmentDesc_cell (i : ι) (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseCellAttachmentDesc α g G hG (fiberwiseCellAttachmentCell α i x) = G i x := by
  rw [← ConcreteCategory.comp_apply, fiberwiseCellAttachmentCell_desc]

variable (α) in
/-- Maps out of the fibrewise adjunction space are determined by their restrictions to `P × Z`
and to the cells. -/
theorem fiberwiseCellAttachment_hom_ext {f f' : fiberwiseCellAttachment α ⟶ W}
    (h₀ : fiberwiseCellAttachmentIncl α ≫ f = fiberwiseCellAttachmentIncl α ≫ f')
    (h : ∀ i, fiberwiseCellAttachmentCell α i ≫ f = fiberwiseCellAttachmentCell α i ≫ f') :
    f = f' :=
  (isPushout_fiberwiseCellAttachment α).hom_ext h₀ (Sigma.hom_ext _ _ fun i ↦ by
    simpa using h i)

variable (α) in
/-- Maps out of the fibrewise adjunction space are determined by their values on `P × Z` and on
the cells. -/
theorem fiberwiseCellAttachment_ext {f f' : fiberwiseCellAttachment α ⟶ W}
    (h₀ : ∀ x, f (fiberwiseCellAttachmentIncl α x) = f' (fiberwiseCellAttachmentIncl α x))
    (h : ∀ i x, f (fiberwiseCellAttachmentCell α i x) = f' (fiberwiseCellAttachmentCell α i x)) :
    f = f' :=
  fiberwiseCellAttachment_hom_ext α (by ext x; exact h₀ x) fun i ↦ by ext x; exact h i x

section ProdDesc

variable {V : Type u} [TopologicalSpace V] (L : C(I × (P × Z), V))
  (C : ∀ i, C(I × (P × TopCat.disk.{u} (k i)), V))
  (hC : ∀ i t p s, L (t, (p, α i (p, s))) = C i (t, (p, TopCat.diskBoundaryInclusion (k i) s)))

variable (α) in
include hC in
/-- The map `I × ((P × Z) ∪_α ⨆ᵢ (P × D^{k i})) → V` glued from a map `L : I × (P × Z) → V` and maps
`C i : I × (P × D^{k i}) → V` which agree along the attaching maps: the form of
`TauCeti.fiberwiseCellAttachmentDesc` for homotopies, given by
`CategoryTheory.IsPushout.cylinderDesc`. -/
def fiberwiseCellAttachmentProdDesc : C(I × fiberwiseCellAttachment α, V) :=
  (isPushout_fiberwiseCellAttachment α).cylinderDesc L (TopCat.sigmaCylinderDesc C)
    fun t b ↦ by
      obtain ⟨i, ⟨p, s⟩, rfl⟩ :
          ∃ i s, Sigma.ι (fun i ↦ TopCat.of (P × TopCat.diskBoundary.{u} (k i))) i s = b :=
        let ⟨⟨i⟩, s, hs⟩ := Concrete.colimit_exists_rep _ b; ⟨i, s, hs⟩
      simp only [fiberwiseAttachingMap, fiberwiseBoundaryInclusion, Sigma.ι_map_apply]
      rw [TopCat.sigmaCylinderDesc_ι]
      simpa using hC i t p s

/-- On the cylinder over `P × Z`, the glued map is `L`. -/
@[simp]
theorem fiberwiseCellAttachmentProdDesc_incl (t : I) (x : P × Z) :
    fiberwiseCellAttachmentProdDesc α L C hC (t, fiberwiseCellAttachmentIncl α x) = L (t, x) :=
  (isPushout_fiberwiseCellAttachment α).cylinderDesc_inl L _ _ t x

/-- On the cylinder over the `i`-th cells, the glued map is `C i`. -/
@[simp]
theorem fiberwiseCellAttachmentProdDesc_cell (t : I) (i : ι) (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseCellAttachmentProdDesc α L C hC (t, fiberwiseCellAttachmentCell α i x) =
      C i (t, x) := by
  rw [← Sigma.ι_comp_desc (fiberwiseCellAttachmentCell α) i, ConcreteCategory.comp_apply]
  exact ((isPushout_fiberwiseCellAttachment α).cylinderDesc_inr L _ _ t _).trans
    (TopCat.sigmaCylinderDesc_ι (X := fun i ↦ TopCat.of (P × TopCat.disk.{u} (k i))) C t i x)

/-- A slice of the glued map is the map out of the fibrewise adjunction space which agrees with the
corresponding slices of `L` on `P × Z` and of the `C i` on the cells: the form of
`CategoryTheory.IsPushout.cylinderDesc_apply_eq` for the fibrewise adjunction space. -/
theorem fiberwiseCellAttachmentProdDesc_apply_eq (t : I) {w : C(fiberwiseCellAttachment α, V)}
    (h₀ : ∀ x, L (t, x) = w (fiberwiseCellAttachmentIncl α x))
    (h₁ : ∀ i x, C i (t, x) = w (fiberwiseCellAttachmentCell α i x))
    (a : fiberwiseCellAttachment α) : fiberwiseCellAttachmentProdDesc α L C hC (t, a) = w a :=
  (isPushout_fiberwiseCellAttachment α).cylinderDesc_apply_eq _ _ _ t h₀ (fun z ↦ by
    obtain ⟨⟨i⟩, x, rfl⟩ := Concrete.colimit_exists_rep _ z
    rw [TopCat.sigmaCylinderDesc_ι, ← ConcreteCategory.comp_apply, Sigma.ι_comp_desc]
    exact h₁ i x) a

end ProdDesc

variable (α) in
/-- The projection of the fibrewise adjunction space `(P × Z) ∪_α ⨆ᵢ (P × D^{k i})` to the
parameter space `P`. -/
def fiberwiseCellAttachmentProj : fiberwiseCellAttachment α ⟶ TopCat.of P :=
  fiberwiseCellAttachmentDesc α (TopCat.ofHom ContinuousMap.fst)
    (fun _ ↦ TopCat.ofHom ContinuousMap.fst) fun _ _ _ ↦ rfl

/-- A point `(p, z)` of `P × Z` lies over `p`. -/
@[simp]
theorem fiberwiseCellAttachmentProj_incl (x : P × Z) :
    fiberwiseCellAttachmentProj α (fiberwiseCellAttachmentIncl α x) = x.1 :=
  fiberwiseCellAttachmentDesc_incl _ _ _ x

/-- A point `(p, w)` of the `i`-th cells lies over `p`. -/
@[simp]
theorem fiberwiseCellAttachmentProj_cell (i : ι) (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseCellAttachmentProj α (fiberwiseCellAttachmentCell α i x) = x.1 :=
  fiberwiseCellAttachmentDesc_cell _ _ _ i x

end Attachment

section Comparison

variable {X : Type u} [TopologicalSpace X] (α : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), Z))
  (e : C(Z, X)) (χ : ∀ i, C(P × TopCat.disk.{u} (k i), X))
  (hχ : ∀ i p s, χ i (p, TopCat.diskBoundaryInclusion (k i) s) = e (α i (p, s)))

/-- The comparison map `(P × Z) ∪_α ⨆ᵢ (P × D^{k i}) → P × X` of a family of characteristic maps
`χᵢ : P × D^{k i} → X` extending the attaching maps `αᵢ` followed by `e : Z → X`. It is induced by
`(p, z) ↦ (p, e z)` on `P × Z` and by `(p, w) ↦ (p, χᵢ (p, w))` on the `i`-th cells, so it is a map
over `P`. -/
def fiberwiseCellComparison : fiberwiseCellAttachment α ⟶ TopCat.of (P × X) :=
  fiberwiseCellAttachmentDesc α (TopCat.ofHom ((ContinuousMap.id P).prodMap e))
    (fun i ↦ TopCat.ofHom (ContinuousMap.fst.prodMk (χ i))) fun i p s ↦ by
      simp [hχ i p s]

variable {α e χ}

/-- The comparison map sends a point `(p, z)` of `P × Z` to `(p, e z)`. -/
@[simp]
theorem fiberwiseCellComparison_incl (x : P × Z) :
    fiberwiseCellComparison α e χ hχ (fiberwiseCellAttachmentIncl α x) = (x.1, e x.2) :=
  fiberwiseCellAttachmentDesc_incl _ _ _ x

/-- The comparison map sends a point `(p, w)` of the `i`-th cells to `(p, χᵢ (p, w))`. -/
@[simp]
theorem fiberwiseCellComparison_cell (i : ι) (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseCellComparison α e χ hχ (fiberwiseCellAttachmentCell α i x) = (x.1, χ i x) :=
  fiberwiseCellAttachmentDesc_cell _ _ _ i x

/-- The comparison map is a map over `P`. -/
@[simp]
theorem fst_fiberwiseCellComparison (x : fiberwiseCellAttachment α) :
    (fiberwiseCellComparison α e χ hχ x).1 = fiberwiseCellAttachmentProj α x := by
  refine ConcreteCategory.congr_hom (?_ : fiberwiseCellComparison α e χ hχ ≫
    TopCat.ofHom ContinuousMap.fst = fiberwiseCellAttachmentProj α) x
  refine fiberwiseCellAttachment_ext α (fun y ↦ ?_) fun i y ↦ ?_
  · rw [ConcreteCategory.comp_apply, fiberwiseCellComparison_incl, fiberwiseCellAttachmentProj_incl]
    rfl
  · rw [ConcreteCategory.comp_apply, fiberwiseCellComparison_cell, fiberwiseCellAttachmentProj_cell]
    rfl

end Comparison

section Reattachment

variable (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), Z))
  (h : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hb : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), TopCat.diskBoundary.{u} (k i)))
  (hh : ∀ i p s, h i (p, TopCat.diskBoundaryInclusion (k i) s) =
    TopCat.diskBoundaryInclusion (k i) (hb i (p, s)))
  (H : ∀ i, (α₁ i).Homotopy ((α₀ i).comp (ContinuousMap.fst.prodMk (hb i))))

/-- The reattachment map on the `i`-th cells: `(p, x) ↦ (p, hᵢ (p, 2x))` in the `i`-th cells on
the ball of radius `1/2`, glued to `(p, x) ↦ (p, Hᵢ (2 - 2‖x‖, (p, x/‖x‖)))` in `P × Z` on the
annulus `1/2 ≤ ‖x‖`. The point `2x` is the end of the radial push with radius `1/2`. -/
private def fiberwiseCellReattachmentFun (i : ι) :
    C(P × TopCat.disk.{u} (k i), fiberwiseCellAttachment α₀) :=
  TopCat.discGlue (by norm_num : (0 : ℝ) < 1 / 2)
    ⟨fun q ↦ fiberwiseCellAttachmentCell α₀ i (q.1, h i (q.1,
        TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (1, ULift.up ⟨q.2.1, closedBall_subset_closedBall (by norm_num) q.2.2⟩))),
      (fiberwiseCellAttachmentCell α₀ i).hom.continuous.comp
        (continuous_fst.prodMk ((h i).continuous.comp
          (continuous_fst.prodMk ((TopCat.diskRadialPush (k i) _).continuous.comp
            (continuous_const.prodMk (continuous_uliftUp.comp
              ((continuous_subtype_val.comp continuous_snd).subtype_mk _)))))))⟩
    ⟨fun q ↦ fiberwiseCellAttachmentIncl α₀ (q.1, H i (σ q.2.1, (q.1, q.2.2))), by fun_prop⟩
    fun p θ ↦ by
      -- At the seam, `Hᵢ (1, ·) = α₀ᵢ ∘ hbᵢ` and `hᵢ` restricts to `hbᵢ` on the boundary sphere.
      have h2 := TopCat.diskRadialPush_one_smul_diskBoundary (k := k i) (d := 1 / 2)
        (by norm_num) θ (closedBall_subset_closedBall (by norm_num)
          (TopCat.smul_diskBoundary_mem_closedBall (by norm_num) θ))
      simp only [ContinuousMap.coe_mk, symm_zero, ContinuousMap.Homotopy.apply_one,
        ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.fst_apply, h2, hh]
      exact fiberwiseCellAttachmentIncl_apply_attaching α₀ i p _

private theorem fiberwiseCellReattachmentFun_of_norm_le (i : ι) (p : P)
    {w : TopCat.disk.{u} (k i)} (hw : ‖w.down.1‖ ≤ 1 / 2) :
    fiberwiseCellReattachmentFun α₀ α₁ h hb hh H i (p, w) =
      fiberwiseCellAttachmentCell α₀ i
        (p, h i (p, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 2) (1, w))) := by
  rw [fiberwiseCellReattachmentFun, TopCat.discGlue_apply_of_norm_le _ _ _ _ _ hw]
  rfl

private theorem fiberwiseCellReattachmentFun_of_le_norm (i : ι) (p : P)
    {w : TopCat.disk.{u} (k i)} (hw : 1 / 2 ≤ ‖w.down.1‖) :
    fiberwiseCellReattachmentFun α₀ α₁ h hb hh H i (p, w) =
      fiberwiseCellAttachmentIncl α₀
        (p, H i (σ (TopCat.annulusParam (1 / 2) w),
          (p, TopCat.annulusDir (by norm_num) ⟨w, hw⟩))) := by
  rw [fiberwiseCellReattachmentFun, TopCat.discGlue_apply_of_le_norm _ _ _ _ _ hw]
  rfl

/-- On the boundary sphere of the `i`-th cells the reattachment map is the attaching map `α₁ᵢ`. -/
private theorem fiberwiseCellReattachmentFun_diskBoundaryInclusion (i : ι) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    fiberwiseCellReattachmentFun α₀ α₁ h hb hh H i (p, TopCat.diskBoundaryInclusion (k i) s) =
      fiberwiseCellAttachmentIncl α₀ (p, α₁ i (p, s)) := by
  have hw : 1 / 2 ≤ ‖(TopCat.diskBoundaryInclusion (k i) s).down.1‖ := by
    rw [TopCat.norm_diskBoundaryInclusion]; norm_num
  rw [fiberwiseCellReattachmentFun_of_le_norm (hw := hw),
    TopCat.annulusParam_of_norm_eq_one (by norm_num) (TopCat.norm_diskBoundaryInclusion s),
    TopCat.annulusDir_diskBoundaryInclusion, symm_one, ContinuousMap.Homotopy.apply_zero]

/-- **The reattachment map** `E : (P × Z) ∪_{α₁} ⨆ᵢ (P × D^{k i}) → (P × Z) ∪_{α₀} ⨆ᵢ (P × D^{k i})`
of a family of self-maps `hᵢ` of the disc pairs, restricting to `hbᵢ` on the boundary spheres, and
of a family of homotopies `Hᵢ` from `α₁ᵢ` to `α₀ᵢ ∘ hbᵢ`, all over `P`. It is the identity on
`P × Z`; on the `i`-th cells it sends `(p, x)` to the point `(p, hᵢ (p, 2x))` of the `i`-th cells
when `‖x‖ ≤ 1/2`, and to the point `(p, Hᵢ (2 - 2‖x‖, (p, x/‖x‖)))` of `P × Z` when
`1/2 ≤ ‖x‖`. -/
def fiberwiseCellReattachment : fiberwiseCellAttachment α₁ ⟶ fiberwiseCellAttachment α₀ :=
  fiberwiseCellAttachmentDesc α₁ (fiberwiseCellAttachmentIncl α₀)
    (fun i ↦ TopCat.ofHom (fiberwiseCellReattachmentFun α₀ α₁ h hb hh H i)) fun i p s ↦
      (fiberwiseCellReattachmentFun_diskBoundaryInclusion α₀ α₁ h hb hh H i p s).symm

private theorem fiberwiseCellReattachment_cell (i : ι) (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseCellReattachment α₀ α₁ h hb hh H (fiberwiseCellAttachmentCell α₁ i x) =
      fiberwiseCellReattachmentFun α₀ α₁ h hb hh H i x :=
  fiberwiseCellAttachmentDesc_cell _ _ _ i x

/-- The reattachment map is the identity on `P × Z`. -/
@[reassoc (attr := simp)]
theorem fiberwiseCellAttachmentIncl_comp_fiberwiseCellReattachment :
    fiberwiseCellAttachmentIncl α₁ ≫ fiberwiseCellReattachment α₀ α₁ h hb hh H =
      fiberwiseCellAttachmentIncl α₀ :=
  fiberwiseCellAttachmentIncl_desc _ _ _

/-- The reattachment map sends a point of `P × Z` to itself. -/
@[simp]
theorem fiberwiseCellReattachment_incl (x : P × Z) :
    fiberwiseCellReattachment α₀ α₁ h hb hh H (fiberwiseCellAttachmentIncl α₁ x) =
      fiberwiseCellAttachmentIncl α₀ x :=
  fiberwiseCellAttachmentDesc_incl _ _ _ x

/-- On the ball of radius `1/2` of the `i`-th cells, the reattachment map is
`(p, x) ↦ (p, hᵢ (p, 2x))`, read in the `i`-th cells. -/
theorem fiberwiseCellReattachment_cell_of_norm_le (i : ι) (p : P)
    {w v : TopCat.disk.{u} (k i)} (hw : ‖w.down.1‖ ≤ 1 / 2) (hv : v.down.1 = (2 : ℝ) • w.down.1) :
    fiberwiseCellReattachment α₀ α₁ h hb hh H (fiberwiseCellAttachmentCell α₁ i (p, w)) =
      fiberwiseCellAttachmentCell α₀ i (p, h i (p, v)) := by
  rw [fiberwiseCellReattachment_cell, fiberwiseCellReattachmentFun_of_norm_le (hw := hw),
    TopCat.diskRadialPush_one_of_norm_le _ hw (by rw [hv]; norm_num)]

/-- On the annulus `1/2 ≤ ‖x‖` of the `i`-th cells, the reattachment map is
`(p, x) ↦ (p, Hᵢ (2 - 2‖x‖, (p, x/‖x‖)))`, read in `P × Z`. -/
theorem fiberwiseCellReattachment_cell_of_le_norm (i : ι) (p : P)
    {w : TopCat.disk.{u} (k i)} (hw : 1 / 2 ≤ ‖w.down.1‖) {t : I}
    (ht : (t : ℝ) = 2 - 2 * ‖w.down.1‖) {s : TopCat.diskBoundary.{u} (k i)}
    (hs : s.down.1 = ‖w.down.1‖⁻¹ • w.down.1) :
    fiberwiseCellReattachment α₀ α₁ h hb hh H (fiberwiseCellAttachmentCell α₁ i (p, w)) =
      fiberwiseCellAttachmentIncl α₀ (p, H i (t, (p, s))) := by
  have ht' : σ (TopCat.annulusParam (1 / 2) w) = t := by
    have := TopCat.one_sub_mul_symm_annulusParam (by norm_num : (1 / 2 : ℝ) ≤ 1) hw
    exact Subtype.ext (by linarith)
  have hs' : TopCat.annulusDir (by norm_num) ⟨w, hw⟩ = s :=
    ULift.ext (Subtype.ext ((TopCat.coe_annulusDir _ _).trans hs.symm))
  rw [fiberwiseCellReattachment_cell, fiberwiseCellReattachmentFun_of_le_norm (hw := hw), ht', hs']

/-- The reattachment map is a map over `P`. -/
@[simp]
theorem fiberwiseCellAttachmentProj_fiberwiseCellReattachment (x : fiberwiseCellAttachment α₁) :
    fiberwiseCellAttachmentProj α₀ (fiberwiseCellReattachment α₀ α₁ h hb hh H x) =
      fiberwiseCellAttachmentProj α₁ x := by
  have : fiberwiseCellReattachment α₀ α₁ h hb hh H ≫ fiberwiseCellAttachmentProj α₀ =
      fiberwiseCellAttachmentProj α₁ := by
    refine fiberwiseCellAttachment_ext α₁ (fun y ↦ ?_) fun i ⟨p, w⟩ ↦ ?_
    · rw [ConcreteCategory.comp_apply, fiberwiseCellReattachment_incl,
        fiberwiseCellAttachmentProj_incl, fiberwiseCellAttachmentProj_incl]
    rw [ConcreteCategory.comp_apply, fiberwiseCellAttachmentProj_cell]
    rcases le_total ‖w.down.1‖ (1 / 2) with hw | hw
    · rw [fiberwiseCellReattachment_cell, fiberwiseCellReattachmentFun_of_norm_le (hw := hw),
        fiberwiseCellAttachmentProj_cell]
    · rw [fiberwiseCellReattachment_cell, fiberwiseCellReattachmentFun_of_le_norm (hw := hw),
        fiberwiseCellAttachmentProj_incl]
  exact ConcreteCategory.congr_hom this x

end Reattachment

section Comparison

variable {X : Type u} [TopologicalSpace X] (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), Z))
  (h : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hb : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), TopCat.diskBoundary.{u} (k i)))
  (hh : ∀ i p s, h i (p, TopCat.diskBoundaryInclusion (k i) s) =
    TopCat.diskBoundaryInclusion (k i) (hb i (p, s)))
  (H : ∀ i, (α₁ i).Homotopy ((α₀ i).comp (ContinuousMap.fst.prodMk (hb i))))
  (e : C(Z, X)) (χ₀ χ₁ : ∀ i, C(P × TopCat.disk.{u} (k i), X))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = e (α₀ i (p, s)))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = e (α₁ i (p, s)))

/-- **`Φ₀ ∘ E` is homotopic to `Φ₁` relative to `P × Z`, over `P`.** Let the homotopies `Hᵢ` of
attaching maps be the restrictions to the boundary spheres of homotopies `Kᵢ` from the
characteristic maps `χ₁ᵢ` to `χ₀ᵢ ∘ hᵢ`. Then the reattachment map followed by the comparison map
`Φ₀` is homotopic to the comparison map `Φ₁`, by a homotopy fixing `P × Z` and lying over `P`. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellComparison
    (K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))))
    (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) = e (H i (t, (p, s)))) :
    ∃ G : (fiberwiseCellReattachment α₀ α₁ h hb hh H ≫
        fiberwiseCellComparison α₀ e χ₀ hχ₀).hom.HomotopyRel
        (fiberwiseCellComparison α₁ e χ₁ hχ₁).hom (range (fiberwiseCellAttachmentIncl α₁)),
      ∀ t x, (G (t, x)).1 = fiberwiseCellAttachmentProj α₁ x := by
  have hd : (0 : ℝ) ≤ 1 / 2 := by norm_num
  -- The homotopy is constant on `P × Z`. On the `i`-th cells it is `Kᵢ` read along the
  -- straight-line homotopy in the cylinder, which fixes the boundary sphere.
  let L : C(I × (P × Z), P × X) := ⟨fun q ↦ (q.2.1, e q.2.2), by fun_prop⟩
  let C (i : ι) : C(I × (P × TopCat.disk.{u} (k i)), P × X) :=
    ⟨fun q ↦ (q.2.1, K i ((TopCat.diskCylinderPath (k i) hd (q.2.2, q.1)).1,
        (q.2.1, (TopCat.diskCylinderPath (k i) hd (q.2.2, q.1)).2))), by fun_prop⟩
  have hL (t : I) (x : P × Z) : L (t, x) = (x.1, e x.2) := rfl
  have hC (t : I) (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
      C i (t, (p, w)) = (p, K i ((TopCat.diskCylinderPath (k i) hd (w, t)).1,
        (p, (TopCat.diskCylinderPath (k i) hd (w, t)).2))) := rfl
  let G := fiberwiseCellAttachmentProdDesc α₁ L C fun i t p s ↦ by
    rw [hL, hC, TopCat.diskCylinderPath_diskBoundaryInclusion (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num), ContinuousMap.Homotopy.apply_zero, hχ₁]
  have hG₀ (t : I) (x : P × Z) : G (t, fiberwiseCellAttachmentIncl α₁ x) = (x.1, e x.2) :=
    fiberwiseCellAttachmentProdDesc_incl ..
  have hG₁ (t : I) (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
      G (t, fiberwiseCellAttachmentCell α₁ i (p, w)) =
        (p, K i ((TopCat.diskCylinderPath (k i) hd (w, t)).1,
          (p, (TopCat.diskCylinderPath (k i) hd (w, t)).2))) :=
    fiberwiseCellAttachmentProdDesc_cell ..
  refine ⟨{ toFun := G
            continuous_toFun := G.continuous
            map_zero_left := fiberwiseCellAttachmentProdDesc_apply_eq _ _ _ 0 (fun x ↦ ?_)
              fun i ⟨p, w⟩ ↦ ?_
            map_one_left := fiberwiseCellAttachmentProdDesc_apply_eq _ _ _ 1 (fun x ↦ ?_)
              fun i ⟨p, w⟩ ↦ ?_
            prop' t a ha := ?_ }, fun t a ↦ ?_⟩
  -- At time `0` the cylinder path is `w ↦ (1 - s, w / max (1/2) ‖w‖)`, along which `Kᵢ` is
  -- `Φ₀ ∘ E` on both pieces of `E`.
  · rw [hL, TopCat.hom_comp, ContinuousMap.comp_apply, fiberwiseCellReattachment_incl,
      fiberwiseCellComparison_incl]
  · rw [hC, TopCat.diskCylinderPath_zero, TopCat.hom_comp, ContinuousMap.comp_apply,
      fiberwiseCellReattachment_cell]
    rcases le_total ‖w.down.1‖ (1 / 2) with hw | hw
    · rw [fiberwiseCellReattachmentFun_of_norm_le (hw := hw), fiberwiseCellComparison_cell,
        TopCat.annulusParam_of_norm_le (by norm_num) hw, symm_zero,
        ContinuousMap.Homotopy.apply_one]
      rfl
    · rw [fiberwiseCellReattachmentFun_of_le_norm (hw := hw), fiberwiseCellComparison_incl,
        ← TopCat.diskBoundaryInclusion_annulusDir (by norm_num : (0 : ℝ) < 1 / 2) ⟨w, hw⟩, hK]
  -- At time `1` the cylinder path is `w ↦ (0, w)`, along which `Kᵢ` is `χ₁ᵢ`.
  · rw [hL, fiberwiseCellComparison_incl]
  · rw [hC, TopCat.diskCylinderPath_one, fiberwiseCellComparison_cell,
      ContinuousMap.Homotopy.apply_zero]
  -- On `P × Z` the homotopy is constant: its underlying map is `G`, which is `hG₀` there.
  · obtain ⟨x, rfl⟩ := ha
    refine (hG₀ t x).trans ?_
    rw [TopCat.hom_comp, ContinuousMap.comp_apply, fiberwiseCellReattachment_incl,
      fiberwiseCellComparison_incl]
  -- The homotopy lies over `P`.
  · exact ConcreteCategory.congr_hom (fiberwiseCellAttachment_ext α₁
      (f := TopCat.ofHom (ContinuousMap.fst.comp (G.curry t)))
      (f' := fiberwiseCellAttachmentProj α₁)
      (fun x ↦ (congrArg Prod.fst (hG₀ t x)).trans (fiberwiseCellAttachmentProj_incl x).symm)
      fun i x ↦ (congrArg Prod.fst (hG₁ t i x.1 x.2)).trans
        (fiberwiseCellAttachmentProj_cell i x).symm) a

/-- **The reattachment map is homotopic to `g₀ ∘ Φ₁`.** For a left inverse `g₀` of the comparison
map `Φ₀` which is a map over `P`, the reattachment map is homotopic to `g₀ ∘ Φ₁` relative to
`P × Z`, by a homotopy over `P`. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_of_leftInverse
    (K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))))
    (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) = e (H i (t, (p, s))))
    (g₀ : C(P × X, fiberwiseCellAttachment α₀))
    (hg₀ : LeftInverse g₀ (fiberwiseCellComparison α₀ e χ₀ hχ₀))
    (hg₀P : ∀ y, fiberwiseCellAttachmentProj α₀ (g₀ y) = y.1) :
    ∃ G : (fiberwiseCellReattachment α₀ α₁ h hb hh H).hom.HomotopyRel
        (g₀.comp (fiberwiseCellComparison α₁ e χ₁ hχ₁).hom)
        (range (fiberwiseCellAttachmentIncl α₁)),
      ∀ t x, fiberwiseCellAttachmentProj α₀ (G (t, x)) = fiberwiseCellAttachmentProj α₁ x := by
  obtain ⟨G, hG⟩ := exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellComparison
    α₀ α₁ h hb hh H e χ₀ χ₁ hχ₀ hχ₁ K hK
  have hE : g₀.comp (fiberwiseCellReattachment α₀ α₁ h hb hh H ≫
      fiberwiseCellComparison α₀ e χ₀ hχ₀).hom = (fiberwiseCellReattachment α₀ α₁ h hb hh H).hom :=
    ContinuousMap.ext fun a ↦ hg₀ _
  exact ⟨(G.compContinuousMap g₀).cast hE rfl, fun t x ↦ (hg₀P _).trans (hG t x)⟩

/-- **The reattachment map does not depend on the homotopies.** Two reattachment maps between the
same attachments, built from any families of self-maps of the disc pairs and of homotopies of
characteristic maps, are homotopic relative to `P × Z`, by a homotopy over `P`, provided the
comparison map `Φ₀` has a left inverse over `P`. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_fiberwiseCellReattachment
    (K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))))
    (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) = e (H i (t, (p, s))))
    (h' : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
    (hb' : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), TopCat.diskBoundary.{u} (k i)))
    (hh' : ∀ i p s, h' i (p, TopCat.diskBoundaryInclusion (k i) s) =
      TopCat.diskBoundaryInclusion (k i) (hb' i (p, s)))
    (H' : ∀ i, (α₁ i).Homotopy ((α₀ i).comp (ContinuousMap.fst.prodMk (hb' i))))
    (K' : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h' i))))
    (hK' : ∀ i t p s, K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) = e (H' i (t, (p, s))))
    (g₀ : C(P × X, fiberwiseCellAttachment α₀))
    (hg₀ : LeftInverse g₀ (fiberwiseCellComparison α₀ e χ₀ hχ₀))
    (hg₀P : ∀ y, fiberwiseCellAttachmentProj α₀ (g₀ y) = y.1) :
    ∃ G : (fiberwiseCellReattachment α₀ α₁ h hb hh H).hom.HomotopyRel
        (fiberwiseCellReattachment α₀ α₁ h' hb' hh' H').hom
        (range (fiberwiseCellAttachmentIncl α₁)),
      ∀ t x, fiberwiseCellAttachmentProj α₀ (G (t, x)) = fiberwiseCellAttachmentProj α₁ x := by
  -- At time `0`, `K` restricts to `H` on the boundary spheres, so `χ₁` extends `α₁`.
  have hχ₁ (i p s) : χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = e (α₁ i (p, s)) := by
    rw [← (K i).apply_zero, hK, (H i).apply_zero]
  obtain ⟨G, hG⟩ := exists_homotopyRel_fiberwiseCellReattachment_of_leftInverse
    α₀ α₁ h hb hh H e χ₀ χ₁ hχ₀ hχ₁ K hK g₀ hg₀ hg₀P
  obtain ⟨G', hG'⟩ := exists_homotopyRel_fiberwiseCellReattachment_of_leftInverse
    α₀ α₁ h' hb' hh' H' e χ₀ χ₁ hχ₀ hχ₁ K' hK' g₀ hg₀ hg₀P
  refine ⟨G.trans G'.symm, fun t x ↦ ?_⟩
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · exact hG _ x
  · exact hG' _ x

end Comparison

section Composition

variable {X : Type u} [TopologicalSpace X] (α₀ α₁ α₂ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), Z))
  (e : C(Z, X)) (χ₀ χ₁ χ₂ : ∀ i, C(P × TopCat.disk.{u} (k i), X))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = e (α₀ i (p, s)))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = e (α₁ i (p, s)))
  (hχ₂ : ∀ i p s, χ₂ i (p, TopCat.diskBoundaryInclusion (k i) s) = e (α₂ i (p, s)))
  (h₀₁ h₁₂ h₀₂ : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hb₀₁ hb₁₂ hb₀₂ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), TopCat.diskBoundary.{u} (k i)))
  (hh₀₁ : ∀ i p s, h₀₁ i (p, TopCat.diskBoundaryInclusion (k i) s) =
    TopCat.diskBoundaryInclusion (k i) (hb₀₁ i (p, s)))
  (hh₁₂ : ∀ i p s, h₁₂ i (p, TopCat.diskBoundaryInclusion (k i) s) =
    TopCat.diskBoundaryInclusion (k i) (hb₁₂ i (p, s)))
  (hh₀₂ : ∀ i p s, h₀₂ i (p, TopCat.diskBoundaryInclusion (k i) s) =
    TopCat.diskBoundaryInclusion (k i) (hb₀₂ i (p, s)))
  (H₀₁ : ∀ i, (α₁ i).Homotopy ((α₀ i).comp (ContinuousMap.fst.prodMk (hb₀₁ i))))
  (H₁₂ : ∀ i, (α₂ i).Homotopy ((α₁ i).comp (ContinuousMap.fst.prodMk (hb₁₂ i))))
  (H₀₂ : ∀ i, (α₂ i).Homotopy ((α₀ i).comp (ContinuousMap.fst.prodMk (hb₀₂ i))))

/-- **Reattachment maps compose up to homotopy.** For three families of attaching maps and
reattachment maps `E₀₁`, `E₁₂`, `E₀₂` between their attachments, `E₀₁ ∘ E₁₂` is homotopic to
`E₀₂` relative to `P × Z`, by a homotopy over `P`, provided the comparison map `Φ₀` has a left
inverse over `P`. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment
    (K₀₁ : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h₀₁ i))))
    (hK₀₁ : ∀ i t p s, K₀₁ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
      e (H₀₁ i (t, (p, s))))
    (K₁₂ : ∀ i, (χ₂ i).Homotopy ((χ₁ i).comp (ContinuousMap.fst.prodMk (h₁₂ i))))
    (hK₁₂ : ∀ i t p s, K₁₂ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
      e (H₁₂ i (t, (p, s))))
    (K₀₂ : ∀ i, (χ₂ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h₀₂ i))))
    (hK₀₂ : ∀ i t p s, K₀₂ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
      e (H₀₂ i (t, (p, s))))
    (g₀ : C(P × X, fiberwiseCellAttachment α₀))
    (hg₀ : LeftInverse g₀ (fiberwiseCellComparison α₀ e χ₀ hχ₀))
    (hg₀P : ∀ y, fiberwiseCellAttachmentProj α₀ (g₀ y) = y.1) :
    ∃ G : (fiberwiseCellReattachment α₁ α₂ h₁₂ hb₁₂ hh₁₂ H₁₂ ≫
        fiberwiseCellReattachment α₀ α₁ h₀₁ hb₀₁ hh₀₁ H₀₁).hom.HomotopyRel
        (fiberwiseCellReattachment α₀ α₂ h₀₂ hb₀₂ hh₀₂ H₀₂).hom
        (range (fiberwiseCellAttachmentIncl α₂)),
      ∀ t x, fiberwiseCellAttachmentProj α₀ (G (t, x)) = fiberwiseCellAttachmentProj α₂ x := by
  -- At time `0`, `K₀₁` and `K₁₂` restrict to `H₀₁` and `H₁₂` on the boundary spheres, so `χ₁` and
  -- `χ₂` extend `α₁` and `α₂`.
  have hχ₁ (i p s) : χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = e (α₁ i (p, s)) := by
    rw [← (K₀₁ i).apply_zero, hK₀₁, (H₀₁ i).apply_zero]
  have hχ₂ (i p s) : χ₂ i (p, TopCat.diskBoundaryInclusion (k i) s) = e (α₂ i (p, s)) := by
    rw [← (K₁₂ i).apply_zero, hK₁₂, (H₁₂ i).apply_zero]
  -- `E₀₁ ∘ E₁₂ ≃ g₀ ∘ Φ₁ ∘ E₁₂ ≃ g₀ ∘ Φ₂ ≃ E₀₂`.
  set E₁₂ := fiberwiseCellReattachment α₁ α₂ h₁₂ hb₁₂ hh₁₂ H₁₂
  obtain ⟨G₁, hG₁⟩ := exists_homotopyRel_fiberwiseCellReattachment_of_leftInverse
    α₀ α₁ h₀₁ hb₀₁ hh₀₁ H₀₁ e χ₀ χ₁ hχ₀ hχ₁ K₀₁ hK₀₁ g₀ hg₀ hg₀P
  obtain ⟨G₂, hG₂⟩ := exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellComparison
    α₁ α₂ h₁₂ hb₁₂ hh₁₂ H₁₂ e χ₁ χ₂ hχ₁ hχ₂ K₁₂ hK₁₂
  obtain ⟨G₃, hG₃⟩ := exists_homotopyRel_fiberwiseCellReattachment_of_leftInverse
    α₀ α₂ h₀₂ hb₀₂ hh₀₂ H₀₂ e χ₀ χ₂ hχ₀ hχ₂ K₀₂ hK₀₂ g₀ hg₀ hg₀P
  have hmono : range (fiberwiseCellAttachmentIncl α₂) ⊆
      E₁₂.hom ⁻¹' range (fiberwiseCellAttachmentIncl α₁) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, (fiberwiseCellReattachment_incl α₁ α₂ h₁₂ hb₁₂ hh₁₂ H₁₂ x).symm⟩
  let F₁ := (G₁.precomp E₁₂.hom).mono hmono
  let F₂ := (G₂.compContinuousMap g₀).cast
    (by rw [TopCat.hom_comp, ContinuousMap.comp_assoc] :
      g₀.comp (E₁₂ ≫ fiberwiseCellComparison α₁ e χ₁ hχ₁).hom =
        (g₀.comp (fiberwiseCellComparison α₁ e χ₁ hχ₁).hom).comp E₁₂.hom) rfl
  refine ⟨(F₁.trans (F₂.trans G₃.symm)).cast (TopCat.hom_comp _ _).symm rfl, fun t x ↦ ?_⟩
  simp only [ContinuousMap.HomotopyRel.cast_apply, ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · rw [ContinuousMap.HomotopyRel.mono_apply, ContinuousMap.HomotopyRel.precomp_apply, hG₁]
    exact fiberwiseCellAttachmentProj_fiberwiseCellReattachment α₁ α₂ h₁₂ hb₁₂ hh₁₂ H₁₂ x
  · exact (hg₀P _).trans (hG₂ _ x)
  · exact hG₃ _ x

end Composition

section BaseChange

variable {P' : Type u} [TopologicalSpace P'] (u : C(P', P))
  {α : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), Z)}
  {α' : ∀ i, C(P' × TopCat.diskBoundary.{u} (k i), Z)} (hα : ∀ i p s, α' i (p, s) = α i (u p, s))

/-- The map `(P' × Z) ∪_{α'} ⨆ᵢ (P' × D^{k i}) → (P × Z) ∪_α ⨆ᵢ (P × D^{k i})` induced by a map
`u : P' → P` of parameter spaces, when the attaching maps `α'` are those of `α` pulled back along
`u`. It is `u × id` on `P' × Z` and on each family of cells, and it lies over `u`
(`TauCeti.fiberwiseCellAttachmentProj_fiberwiseCellAttachmentMap`). -/
def fiberwiseCellAttachmentMap : fiberwiseCellAttachment α' ⟶ fiberwiseCellAttachment α :=
  fiberwiseCellAttachmentDesc α'
    (TopCat.ofHom (u.prodMap (ContinuousMap.id Z)) ≫ fiberwiseCellAttachmentIncl α)
    (fun i ↦ TopCat.ofHom (u.prodMap (ContinuousMap.id _)) ≫ fiberwiseCellAttachmentCell α i)
    fun i p s ↦ by
      simp only [ConcreteCategory.comp_apply, TopCat.hom_ofHom, ContinuousMap.prodMap_apply,
        Prod.map, ContinuousMap.id_apply, hα]
      exact fiberwiseCellAttachmentIncl_apply_attaching α i (u p) s

/-- The map induced by `u` sends a point `(p, z)` of `P' × Z` to `(u p, z)`. -/
@[simp]
theorem fiberwiseCellAttachmentMap_incl (x : P' × Z) :
    fiberwiseCellAttachmentMap u hα (fiberwiseCellAttachmentIncl α' x) =
      fiberwiseCellAttachmentIncl α (u x.1, x.2) :=
  fiberwiseCellAttachmentDesc_incl _ _ _ x

/-- The map induced by `u` sends a point `(p, w)` of the `i`-th cells to `(u p, w)`. -/
@[simp]
theorem fiberwiseCellAttachmentMap_cell (i : ι) (x : P' × TopCat.disk.{u} (k i)) :
    fiberwiseCellAttachmentMap u hα (fiberwiseCellAttachmentCell α' i x) =
      fiberwiseCellAttachmentCell α i (u x.1, x.2) :=
  fiberwiseCellAttachmentDesc_cell _ _ _ i x

/-- The map induced by the identity of `P` is the identity. -/
@[simp]
theorem fiberwiseCellAttachmentMap_id :
    fiberwiseCellAttachmentMap (ContinuousMap.id P) (α := α) (α' := α) (fun _ _ _ ↦ rfl) =
      𝟙 (fiberwiseCellAttachment α) :=
  fiberwiseCellAttachment_ext α (fun x ↦ fiberwiseCellAttachmentMap_incl _ _ x)
    fun i x ↦ fiberwiseCellAttachmentMap_cell _ _ i x

/-- The maps induced by `v : P'' → P'` and `u : P' → P` compose to the map induced by `u ∘ v`. -/
@[reassoc]
theorem fiberwiseCellAttachmentMap_comp {P'' : Type u} [TopologicalSpace P''] (v : C(P'', P'))
    {α'' : ∀ i, C(P'' × TopCat.diskBoundary.{u} (k i), Z)}
    (hα' : ∀ i p s, α'' i (p, s) = α' i (v p, s)) :
    fiberwiseCellAttachmentMap v hα' ≫ fiberwiseCellAttachmentMap u hα =
      fiberwiseCellAttachmentMap (u.comp v) fun i p s ↦ (hα' i p s).trans (hα i (v p) s) := by
  refine fiberwiseCellAttachment_ext α'' (fun x ↦ ?_) fun i x ↦ ?_
  · rw [ConcreteCategory.comp_apply, fiberwiseCellAttachmentMap_incl,
      fiberwiseCellAttachmentMap_incl, fiberwiseCellAttachmentMap_incl]
    rfl
  · rw [ConcreteCategory.comp_apply, fiberwiseCellAttachmentMap_cell,
      fiberwiseCellAttachmentMap_cell, fiberwiseCellAttachmentMap_cell]
    rfl

/-- The map induced by `u` lies over `u`. -/
@[simp]
theorem fiberwiseCellAttachmentProj_fiberwiseCellAttachmentMap (x : fiberwiseCellAttachment α') :
    fiberwiseCellAttachmentProj α (fiberwiseCellAttachmentMap u hα x) =
      u (fiberwiseCellAttachmentProj α' x) := by
  refine ConcreteCategory.congr_hom (?_ : fiberwiseCellAttachmentMap u hα ≫
    fiberwiseCellAttachmentProj α = fiberwiseCellAttachmentProj α' ≫ TopCat.ofHom u) x
  refine fiberwiseCellAttachment_ext α' (fun y ↦ ?_) fun i y ↦ ?_
  · rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, fiberwiseCellAttachmentMap_incl,
      fiberwiseCellAttachmentProj_incl, fiberwiseCellAttachmentProj_incl]
    rfl
  · rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, fiberwiseCellAttachmentMap_cell,
      fiberwiseCellAttachmentProj_cell, fiberwiseCellAttachmentProj_cell]
    rfl

/-- The comparison maps commute with the maps induced by `u`, when the characteristic maps over
`P'` are those over `P` pulled back along `u`. -/
theorem fiberwiseCellComparison_fiberwiseCellAttachmentMap {X : Type u} [TopologicalSpace X]
    (e : C(Z, X)) {χ : ∀ i, C(P × TopCat.disk.{u} (k i), X)}
    {χ' : ∀ i, C(P' × TopCat.disk.{u} (k i), X)}
    (hχ : ∀ i p s, χ i (p, TopCat.diskBoundaryInclusion (k i) s) = e (α i (p, s)))
    (hχ' : ∀ i p s, χ' i (p, TopCat.diskBoundaryInclusion (k i) s) = e (α' i (p, s)))
    (hχχ' : ∀ i p w, χ' i (p, w) = χ i (u p, w)) (x : fiberwiseCellAttachment α') :
    fiberwiseCellComparison α e χ hχ (fiberwiseCellAttachmentMap u hα x) =
      (u (fiberwiseCellComparison α' e χ' hχ' x).1, (fiberwiseCellComparison α' e χ' hχ' x).2) := by
  refine ConcreteCategory.congr_hom (?_ : fiberwiseCellAttachmentMap u hα ≫
    fiberwiseCellComparison α e χ hχ = fiberwiseCellComparison α' e χ' hχ' ≫
      TopCat.ofHom (u.prodMap (ContinuousMap.id X))) x
  refine fiberwiseCellAttachment_ext α' (fun y ↦ ?_) fun i y ↦ ?_
  · rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, fiberwiseCellAttachmentMap_incl,
      fiberwiseCellComparison_incl, fiberwiseCellComparison_incl]
    rfl
  · rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, fiberwiseCellAttachmentMap_cell,
      fiberwiseCellComparison_cell, fiberwiseCellComparison_cell, hχχ']
    rfl

/-- **Reattachment maps commute with restriction of the parameter space.** If the data over `P'`
are those over `P` pulled back along `u : P' → P`, the reattachment map over `P'` followed by the
map induced by `u` is the map induced by `u` followed by the reattachment map over `P`. -/
theorem fiberwiseCellReattachment_comp_fiberwiseCellAttachmentMap
    {α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), Z)}
    {α₀' α₁' : ∀ i, C(P' × TopCat.diskBoundary.{u} (k i), Z)}
    (hα₀ : ∀ i p s, α₀' i (p, s) = α₀ i (u p, s)) (hα₁ : ∀ i p s, α₁' i (p, s) = α₁ i (u p, s))
    {h : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i))}
    {hb : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), TopCat.diskBoundary.{u} (k i))}
    (hh : ∀ i p s, h i (p, TopCat.diskBoundaryInclusion (k i) s) =
      TopCat.diskBoundaryInclusion (k i) (hb i (p, s)))
    (H : ∀ i, (α₁ i).Homotopy ((α₀ i).comp (ContinuousMap.fst.prodMk (hb i))))
    {h' : ∀ i, C(P' × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i))}
    {hb' : ∀ i, C(P' × TopCat.diskBoundary.{u} (k i), TopCat.diskBoundary.{u} (k i))}
    (hh' : ∀ i p s, h' i (p, TopCat.diskBoundaryInclusion (k i) s) =
      TopCat.diskBoundaryInclusion (k i) (hb' i (p, s)))
    (H' : ∀ i, (α₁' i).Homotopy ((α₀' i).comp (ContinuousMap.fst.prodMk (hb' i))))
    (hhh' : ∀ i p w, h' i (p, w) = h i (u p, w))
    (hHH' : ∀ i t p s, H' i (t, (p, s)) = H i (t, (u p, s))) :
    fiberwiseCellReattachment α₀' α₁' h' hb' hh' H' ≫ fiberwiseCellAttachmentMap u hα₀ =
      fiberwiseCellAttachmentMap u hα₁ ≫ fiberwiseCellReattachment α₀ α₁ h hb hh H := by
  refine fiberwiseCellAttachment_ext α₁' (fun y ↦ ?_) fun i ⟨p, w⟩ ↦ ?_
  · rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, fiberwiseCellReattachment_incl,
      fiberwiseCellAttachmentMap_incl, fiberwiseCellAttachmentMap_incl,
      fiberwiseCellReattachment_incl]
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, fiberwiseCellAttachmentMap_cell,
    fiberwiseCellReattachment_cell, fiberwiseCellReattachment_cell]
  rcases le_total ‖w.down.1‖ (1 / 2) with hw | hw
  · rw [fiberwiseCellReattachmentFun_of_norm_le (hw := hw),
      fiberwiseCellReattachmentFun_of_norm_le (hw := hw), fiberwiseCellAttachmentMap_cell, hhh']
  · rw [fiberwiseCellReattachmentFun_of_le_norm (hw := hw),
      fiberwiseCellReattachmentFun_of_le_norm (hw := hw), fiberwiseCellAttachmentMap_incl, hHH']

end BaseChange

end TauCeti

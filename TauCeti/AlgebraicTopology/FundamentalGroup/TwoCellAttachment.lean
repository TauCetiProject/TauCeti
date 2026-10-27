/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.Path
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import Mathlib.Topology.CompactOpen
import TauCeti.AlgebraicTopology.FundamentalGroupoid.CoverGeneration
import TauCeti.Topology.Homotopy.Path
import TauCeti.Topology.UnitInterval.OpenSquare

/-!
# Attaching 2-cells along loops

Let `γ : ι → Path x x` be a family of loops at a point `x` of a space `X`. The space
`TauCeti.TwoCellAttachment γ` is obtained from `X` by attaching one 2-cell along each loop `γ i`.
The 2-cell is the square `I × I`, attached along its boundary: the edge `{0} × I` is glued to `X`
along `γ i`, and the other three edges are collapsed to `x`. A map of the square into a space `Y`
with this boundary behaviour is exactly a homotopy, relative to the endpoints, from the image of
`γ i` to the constant path, so the square is a 2-cell bounding the loop `γ i`.

This is the operation that builds the presentation complex of a group presentation from a wedge
of circles, and it is how the relators of a presentation are realized topologically: the loops
`γ i` become nullhomotopic, and a map out of `X` extends over the attached cells exactly when it
makes every loop `γ i` nullhomotopic.

The space is the quotient of `X ⊕ Σ _ : ι, I × I` which glues the boundary of each square to
`X`; the quotient presentation is private, and the space is used through the inclusion `incl γ`
of `X`, the characteristic maps `cell γ i` of the cells, and the universal property `lift`.

Attaching 2-cells does not create new loops: the inclusion of `X` induces a surjection on
fundamental groups. The open square of each cell is embedded as an open, simply connected subset,
the open cell, and `X` is embedded as a closed subspace. Every loop is first pushed off the
centres of the cells through the open cells (`Path.exists_range_subset_homotopic`), and then
retracted onto `X` along the radial deformation of each punctured cell onto its boundary
(`unitInterval.radialPush`).

## Main definitions

* `TauCeti.TwoCellAttachment γ`: the space obtained from `X` by attaching a 2-cell along each
  loop `γ i`.
* `TauCeti.TwoCellAttachment.incl`: the inclusion of `X`.
* `TauCeti.TwoCellAttachment.cell`: the characteristic map of the `i`-th cell.
* `TauCeti.TwoCellAttachment.cellHomotopy`: the `i`-th cell, as a nullhomotopy of the image of
  `γ i`.
* `TauCeti.TwoCellAttachment.lift`: the universal property, which extends a map out of `X`
  together with nullhomotopies of the images of the loops.

## Main results

* `TauCeti.TwoCellAttachment.isQuotientMap_sumElim`: the space is a quotient of
  `X ⊕ Σ _ : ι, I × I`.
* `TauCeti.TwoCellAttachment.instPathConnectedSpace`: the space is path connected when `X` is.
* `TauCeti.TwoCellAttachment.hom_ext`: maps out of the space are determined on `X` and the cells.
* `TauCeti.TwoCellAttachment.exists_comp_incl_eq_iff`: a map out of `X` extends over the attached
  cells exactly when it makes every loop `γ i` nullhomotopic.
* `TauCeti.TwoCellAttachment.map_incl_fromPath`: the inclusion kills the class of every loop
  `γ i` in the fundamental group.
* `TauCeti.TwoCellAttachment.cell_eq_cell_iff`, `TauCeti.TwoCellAttachment.incl_ne_cell`: a point
  of the open square of a cell is identified with no other point.
* `TauCeti.TwoCellAttachment.isOpenEmbedding_restrict_cell`,
  `TauCeti.TwoCellAttachment.isSimplyConnected_image_cell`: the open cells are open, embedded and
  simply connected.
* `TauCeti.TwoCellAttachment.cell_eq_incl_iff`: the points of a cell which are points of `X`.
* `TauCeti.TwoCellAttachment.isClosedEmbedding_incl`: `X` is a closed subspace.
* `TauCeti.TwoCellAttachment.surjective_map_incl`: the inclusion of `X` induces a surjection on
  fundamental groups.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 for attaching cells, and Section 1.2, Proposition 1.26 for the effect of attaching
  2-cells on the fundamental group.
-/

public section

noncomputable section

namespace TauCeti

open Set Topology unitInterval

universe u v w

variable {X : Type u} [TopologicalSpace X] {x : X} {ι : Type v}

/-- The normal form of a point of `X ⊕ Σ _ : ι, I × I` for attaching 2-cells along the loops `γ`:
a point `(s, t)` on the boundary of the `i`-th square is sent to the point of `X` it is glued to,
which is `γ i t` on the edge `s = 0` and `x` on the other three edges, and every other point to
itself. Two points have the same normal form exactly when the attachment identifies them. -/
private def cellNormalize (γ : ι → Path x x) (a : X ⊕ Σ _ : ι, I × I) : X ⊕ Σ _ : ι, I × I :=
  open Classical in
  a.elim .inl fun q =>
    if q.2.1 = 0 then .inl (γ q.1 q.2.2)
    else if q.2.1 = 1 ∨ q.2.2 = 0 ∨ q.2.2 = 1 then .inl x
    else .inr q

private lemma cellNormalize_cellNormalize (γ : ι → Path x x) (a : X ⊕ Σ _ : ι, I × I) :
    cellNormalize γ (cellNormalize γ a) = cellNormalize γ a := by
  rcases a with y | q
  · rfl
  · simp only [cellNormalize, Sum.elim_inr]
    split_ifs with h₀ h₁ <;> simp_all

/-- The space obtained from `X` by attaching a 2-cell along each loop `γ i`: the square `I × I`,
with the edge `{0} × I` glued to `X` along `γ i` and the other three edges collapsed to `x`. It
carries the quotient topology.

The presentation as a quotient is private: points come from `TauCeti.TwoCellAttachment.incl`
and `TauCeti.TwoCellAttachment.cell`, maps out of the space from
`TauCeti.TwoCellAttachment.lift`, and statements about all of its points from
`TauCeti.TwoCellAttachment.ind`. -/
def TwoCellAttachment (γ : ι → Path x x) : Type max u v :=
  Quotient (Setoid.ker (cellNormalize γ))

namespace TwoCellAttachment

variable (γ : ι → Path x x)

/-! The topology is transported from the private quotient; the instance is `@[no_expose]`, which
is what lets its body name the private constant. -/

@[no_expose] instance : TopologicalSpace (TwoCellAttachment γ) :=
  inferInstanceAs (TopologicalSpace (Quotient (Setoid.ker (cellNormalize γ))))

/-- The inclusion of `X` into the space with the 2-cells attached. -/
def incl : C(X, TwoCellAttachment γ) :=
  ⟨fun y => Quotient.mk _ (.inl y), continuous_quot_mk.comp continuous_inl⟩

/-- The characteristic map of the `i`-th attached cell, the square `I × I`. -/
def cell (i : ι) : C(I × I, TwoCellAttachment γ) :=
  ⟨fun p => Quotient.mk _ (.inr ⟨i, p⟩),
    continuous_quot_mk.comp (continuous_inr.comp continuous_sigmaMk)⟩

variable {γ}

/-- The quotient map onto the space with the cells attached. -/
private def mk (γ : ι → Path x x) (a : X ⊕ Σ _ : ι, I × I) : TwoCellAttachment γ :=
  Quotient.mk _ a

private lemma mk_cellNormalize (a : X ⊕ Σ _ : ι, I × I) :
    mk γ (cellNormalize γ a) = mk γ a :=
  Quotient.sound (cellNormalize_cellNormalize γ a)

private lemma mk_inl (y : X) : mk γ (.inl y) = incl γ y :=
  (rfl)

private lemma mk_inr (i : ι) (q : I × I) : mk γ (.inr ⟨i, q⟩) = cell γ i q :=
  (rfl)

/-- The edge `{0} × I` of the `i`-th cell is glued to `X` along the loop `γ i`. -/
@[simp]
lemma cell_apply_zero (i : ι) (t : I) : cell γ i (0, t) = incl γ (γ i t) := by
  rw [← mk_inr, ← mk_cellNormalize]
  simp [cellNormalize, mk_inl]

/-- The edge `{1} × I` of the `i`-th cell is collapsed to the base point. -/
@[simp]
lemma cell_apply_one (i : ι) (t : I) : cell γ i (1, t) = incl γ x := by
  rw [← mk_inr, ← mk_cellNormalize]
  simp [cellNormalize, mk_inl]

/-- The edge `I × {0}` of the `i`-th cell is collapsed to the base point. -/
@[simp]
lemma cell_source (i : ι) (s : I) : cell γ i (s, 0) = incl γ x := by
  rw [← mk_inr, ← mk_cellNormalize]
  by_cases hs : s = 0
  · simp [cellNormalize, mk_inl, hs]
  · simp [cellNormalize, mk_inl, hs]

/-- The edge `I × {1}` of the `i`-th cell is collapsed to the base point. -/
@[simp]
lemma cell_target (i : ι) (s : I) : cell γ i (s, 1) = incl γ x := by
  rw [← mk_inr, ← mk_cellNormalize]
  by_cases hs : s = 0
  · simp [cellNormalize, mk_inl, hs]
  · simp [cellNormalize, mk_inl, hs]

/-- Every point of the space comes from `X` or from one of the attached cells. -/
@[elab_as_elim]
lemma ind {p : TwoCellAttachment γ → Prop} (incl : ∀ y, p (incl γ y))
    (cell : ∀ i q, p (cell γ i q)) (z : TwoCellAttachment γ) : p z := by
  induction z using Quotient.ind with
  | _ a => cases a with
    | inl y => exact incl y
    | inr q => exact cell q.1 q.2

/-- **The space is a quotient of `X ⊕ Σ _ : ι, I × I`**, by the inclusion of `X` and the
characteristic maps of the cells. -/
theorem isQuotientMap_sumElim :
    IsQuotientMap (Sum.elim (incl γ) fun q : Σ _ : ι, I × I => cell γ q.1 q.2) := by
  have h : (Sum.elim (incl γ) fun q : Σ _ : ι, I × I => cell γ q.1 q.2) =
      Quotient.mk (Setoid.ker (cellNormalize γ)) := by
    funext a
    cases a <;> rfl
  rw [h]
  exact isQuotientMap_quot_mk

/-- **Attaching 2-cells to a path-connected space gives a path-connected space**: every point of
a cell is joined inside the cell to its edge `{1} × I`, which is collapsed to the base point. -/
instance instPathConnectedSpace [PathConnectedSpace X] :
    PathConnectedSpace (TwoCellAttachment γ) := by
  have h (z : TwoCellAttachment γ) : Joined (incl γ x) z := by
    induction z using ind with
    | incl y => exact (PathConnectedSpace.joined x y).map (incl γ).continuous
    | cell i q =>
      -- The horizontal segment from `(1, q.2)` to `q` inside the square.
      let p : Path ((1 : I), q.2) q :=
        { toFun r := (Set.Icc.convexComb 1 q.1 r, q.2)
          continuous_toFun := by fun_prop
          source' := by simp
          target' := by simp }
      rw [← cell_apply_one i q.2]
      exact ⟨p.map (cell γ i).continuous⟩
  exact ⟨⟨incl γ x⟩, fun v w => (h v).symm.trans (h w)⟩

section Lift

variable {Y : Type w} [TopologicalSpace Y]

/-- **The universal property of attaching 2-cells.** A map `f` out of `X`, together with a
nullhomotopy `H i` of the image under `f` of each loop `γ i`, extends over the attached cells: the
`i`-th cell is sent to `Y` by `H i`. -/
def lift (f : C(X, Y)) (H : ∀ i, Path.Homotopy ((γ i).map f.continuous) (Path.refl (f x))) :
    C(TwoCellAttachment γ, Y) :=
  ⟨Quotient.lift (Sum.elim f fun q => H q.1 q.2) fun a b hab => by
      -- The map out of `X ⊕ Σ _ : ι, I × I` is constant along the normal form, so it is
      -- constant on the fibres of the normal form.
      have key (c : X ⊕ Σ _ : ι, I × I) : Sum.elim f (fun q => H q.1 q.2) (cellNormalize γ c) =
          Sum.elim f (fun q => H q.1 q.2) c := by
        rcases c with y | ⟨i, s, t⟩
        · rfl
        · simp only [cellNormalize, Sum.elim_inr]
          split_ifs with h₀ h₁
          · simp [h₀]
          · rcases h₁ with h₁ | h₁ | h₁ <;> simp [h₁]
          · rfl
      exact (key a).symm.trans ((congrArg _ hab).trans (key b)),
    Continuous.quotient_lift
      (f.continuous.sumElim (continuous_sigma fun i => (H i).continuous)) _⟩

@[simp]
lemma lift_incl (f : C(X, Y)) (H : ∀ i, Path.Homotopy ((γ i).map f.continuous) (Path.refl (f x)))
    (y : X) : lift f H (incl γ y) = f y := (rfl)

@[simp]
lemma lift_cell (f : C(X, Y)) (H : ∀ i, Path.Homotopy ((γ i).map f.continuous) (Path.refl (f x)))
    (i : ι) (q : I × I) : lift f H (cell γ i q) = H i q := (rfl)

@[simp]
lemma lift_comp_incl (f : C(X, Y))
    (H : ∀ i, Path.Homotopy ((γ i).map f.continuous) (Path.refl (f x))) :
    (lift f H).comp (incl γ) = f := (rfl)

/-- **Extensionality for maps out of the space.** Two maps which agree on `X` and on every
attached cell are equal. -/
@[ext]
theorem hom_ext {f g : C(TwoCellAttachment γ, Y)} (h : f.comp (incl γ) = g.comp (incl γ))
    (hcell : ∀ i, f.comp (cell γ i) = g.comp (cell γ i)) : f = g := by
  refine ContinuousMap.ext fun z => ?_
  induction z using ind with
  | incl y => exact DFunLike.congr_fun h y
  | cell i q => exact DFunLike.congr_fun (hcell i) q

end Lift

/-! ### The attached cells as nullhomotopies -/

/-- The `i`-th attached cell is a nullhomotopy, relative to the endpoints, of the image of the
loop `γ i` in the space. -/
def cellHomotopy (i : ι) :
    Path.Homotopy ((γ i).map (incl γ).continuous) (Path.refl (incl γ x)) where
  toContinuousMap := cell γ i
  map_zero_left t := by simp
  map_one_left t := by simp
  prop' s t ht := by
    rcases ht with rfl | rfl <;> simp

@[simp]
lemma cellHomotopy_apply (i : ι) (q : I × I) : cellHomotopy (γ := γ) i q = cell γ i q := (rfl)

/-- Every loop `γ i` becomes nullhomotopic in the space with the 2-cells attached. -/
theorem homotopic_map_incl (i : ι) :
    ((γ i).map (incl γ).continuous).Homotopic (Path.refl (incl γ x)) :=
  ⟨cellHomotopy i⟩

/-- **The attached cells kill the loops.** The class of every loop `γ i` is sent to `1` in the
fundamental group of the space with the 2-cells attached. -/
@[simp]
theorem map_incl_fromPath (i : ι) :
    FundamentalGroup.map (incl γ) x
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ i))) = 1 := by
  rw [TauCeti.FundamentalGroup.map_fromPath]
  exact congrArg CategoryTheory.End.of (Quotient.sound (homotopic_map_incl i))

variable {Y : Type w} [TopologicalSpace Y]

/-- **Maps extend over the attached cells exactly when they kill the loops.** A map out of `X`
is the restriction of a map out of the space with the 2-cells attached if and only if the image
of every loop `γ i` is nullhomotopic relative to its endpoints. -/
theorem exists_comp_incl_eq_iff (f : C(X, Y)) :
    (∃ g : C(TwoCellAttachment γ, Y), g.comp (incl γ) = f) ↔
      ∀ i, ((γ i).map f.continuous).Homotopic (Path.refl (f x)) := by
  constructor
  · rintro ⟨g, rfl⟩ i
    have hrefl : (Path.refl (incl γ x)).map g.continuous = Path.refl (g (incl γ x)) := by
      ext
      simp
    have h := (homotopic_map_incl (γ := γ) i).map g
    rw [Path.map_map, hrefl] at h
    -- `h` is the goal up to unfolding `ContinuousMap.coe_comp` in the endpoints.
    exact h
  · intro h
    exact ⟨lift f fun i => (h i).some, lift_comp_incl _ _⟩

/-! ### The open cells -/

section OpenCell

variable {i : ι} {q : I × I}

/-- A point of the open square is its own normal form. -/
private lemma cellNormalize_inr_of_mem (hq : q ∈ Ioo 0 1 ×ˢ Ioo 0 1) :
    cellNormalize γ (.inr ⟨i, q⟩) = .inr ⟨i, q⟩ := by
  obtain ⟨⟨h₀, h₁⟩, h₂, h₃⟩ := hq
  simp [cellNormalize, h₀.ne', h₁.ne, h₂.ne', h₃.ne]

/-- Only a point of a square can have that point as its normal form. -/
private lemma eq_of_cellNormalize_eq_inr {a : X ⊕ Σ _ : ι, I × I}
    (h : cellNormalize γ a = .inr ⟨i, q⟩) : a = .inr ⟨i, q⟩ := by
  rcases a with y | ⟨j, q'⟩
  · simp [cellNormalize] at h
  · simp only [cellNormalize, Sum.elim_inr] at h
    split_ifs at h with h₀ h₁
    simp_all

/-- A point of the open square of a cell is identified with no other point. -/
private lemma mk_eq_cell_iff (hq : q ∈ Ioo 0 1 ×ˢ Ioo 0 1) {a : X ⊕ Σ _ : ι, I × I} :
    mk γ a = cell γ i q ↔ a = .inr ⟨i, q⟩ := by
  refine ⟨fun h => eq_of_cellNormalize_eq_inr (γ := γ) ?_, fun h => h ▸ rfl⟩
  rw [← cellNormalize_inr_of_mem hq]
  exact Quotient.exact h

private lemma sumElim_eq_mk (a : X ⊕ Σ _ : ι, I × I) :
    Sum.elim (incl γ) (fun q : Σ _ : ι, I × I => cell γ q.1 q.2) a = mk γ a := by
  rcases a with _ | _ <;> rfl

/-- A point of `X` is not a point of the open square of a cell. -/
theorem incl_ne_cell (hq : q ∈ Ioo 0 1 ×ˢ Ioo 0 1) (y : X) : incl γ y ≠ cell γ i q := by
  rw [← mk_inl, Ne, mk_eq_cell_iff hq]
  simp

/-- A point of a cell agrees with a point of the open square of a cell only when they are the same
point of the same cell. -/
theorem cell_eq_cell_iff (hq : q ∈ Ioo 0 1 ×ˢ Ioo 0 1) {j : ι} {q' : I × I} :
    cell γ j q' = cell γ i q ↔ j = i ∧ q' = q := by
  rw [← mk_inr, mk_eq_cell_iff hq]
  simp

/-- The image of an open subset of the open square of a cell is open. -/
theorem isOpen_image_cell {V : Set (I × I)} (hV : IsOpen V) (hVq : V ⊆ Ioo 0 1 ×ˢ Ioo 0 1) :
    IsOpen (cell γ i '' V) := by
  rw [← isQuotientMap_sumElim.isOpen_preimage]
  have h : Sum.elim (incl γ) (fun q : Σ _ : ι, I × I => cell γ q.1 q.2) ⁻¹' (cell γ i '' V) =
      Sum.inr '' (Sigma.mk i '' V) := by
    ext a
    simp only [mem_preimage, sumElim_eq_mk]
    constructor
    · rintro ⟨q, hq, h⟩
      exact ⟨⟨i, q⟩, ⟨q, hq, rfl⟩, ((mk_eq_cell_iff (hVq hq)).1 h.symm).symm⟩
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, rfl⟩
  rw [h]
  exact isOpenMap_inr _ (isOpenMap_sigmaMk _ hV)

/-- **The open cells.** The characteristic map of a cell restricts to an open embedding of the
open square. -/
theorem isOpenEmbedding_restrict_cell :
    IsOpenEmbedding ((Ioo 0 1 ×ˢ Ioo 0 1 : Set (I × I)).domRestrict (cell γ i)) := by
  have hT : IsOpen (Ioo 0 1 ×ˢ Ioo 0 1 : Set (I × I)) := isOpen_Ioo.prod isOpen_Ioo
  refine .of_continuous_injective_isOpenMap ((cell γ i).continuous.comp continuous_subtype_val)
    (fun q q' h => Subtype.ext ((cell_eq_cell_iff q'.2).1 h).2) fun V hV => ?_
  rw [domRestrict_eq, image_comp]
  exact isOpen_image_cell (hT.isOpenMap_subtype_val V hV) (Subtype.coe_image_subset _ _)

/-- The open cells are simply connected. -/
theorem isSimplyConnected_image_cell :
    IsSimplyConnected (cell γ i '' (Ioo 0 1 ×ˢ Ioo 0 1)) := by
  rw [← range_domRestrict, ← image_univ,
    isOpenEmbedding_restrict_cell.isEmbedding.isSimplyConnected_image,
    ← IsEmbedding.subtypeVal.isSimplyConnected_image, Subtype.coe_image_univ]
  exact unitInterval.isSimplyConnected_Ioo_prod_Ioo

/-- A point on an edge of a square is a point of `X`. -/
theorem cell_mem_range_incl (hq : q ∉ Ioo 0 1 ×ˢ Ioo 0 1) : cell γ i q ∈ range (incl γ) := by
  obtain ⟨s, t⟩ := q
  rcases unitInterval.notMem_Ioo_prod_Ioo_iff.1 hq with rfl | rfl | rfl | rfl
  exacts [⟨_, (cell_apply_zero i t).symm⟩, ⟨_, (cell_apply_one i t).symm⟩,
    ⟨_, (cell_source i s).symm⟩, ⟨_, (cell_target i s).symm⟩]

end OpenCell

/-! ### `X` is a closed subspace -/

/-- The inclusion of `X` is injective. -/
theorem incl_injective : Function.Injective (incl γ) := fun _ _ h =>
  Sum.inl_injective (Quotient.exact h)

/-- A point of a cell is the point `y` of `X` exactly when it lies on the edge `{0} × I` over
`γ i ⁻¹' {y}`, or on one of the other three edges and `y = x`. -/
theorem cell_eq_incl_iff {i : ι} {q : I × I} {y : X} :
    cell γ i q = incl γ y ↔ (q.1 = 0 ∧ γ i q.2 = y) ∨ (y = x ∧ (q.1 = 1 ∨ q.2 = 0 ∨ q.2 = 1)) := by
  obtain ⟨s, t⟩ := q
  constructor
  · intro h
    have hq : (s, t) ∉ (Ioo 0 1 ×ˢ Ioo 0 1 : Set (I × I)) := fun hq =>
      incl_ne_cell hq y h.symm
    rcases unitInterval.notMem_Ioo_prod_Ioo_iff.1 hq with rfl | rfl | rfl | rfl
    · exact .inl ⟨rfl, incl_injective ((cell_apply_zero i t).symm.trans h)⟩
    all_goals exact .inr ⟨incl_injective (h.symm.trans (by simp)), by simp⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩) <;> simp

/-- **`X` is a closed subspace.** The inclusion of `X` into the space with the 2-cells attached is
a closed embedding. -/
theorem isClosedEmbedding_incl : IsClosedEmbedding (incl γ) := by
  refine .of_continuous_injective_isClosedMap (incl γ).continuous incl_injective fun A hA => ?_
  rw [← isQuotientMap_sumElim.isClosed_preimage, isClosed_sum_iff, isClosed_sigma_iff]
  refine ⟨?_, fun i => ?_⟩
  · convert hA using 1
    ext y
    simp [incl_injective.eq_iff]
  · have h : Sigma.mk i ⁻¹' (Sum.inr ⁻¹'
        (Sum.elim (incl γ) (fun q : Σ _ : ι, I × I => cell γ q.1 q.2) ⁻¹' (incl γ '' A))) =
        ({q : I × I | q.1 = 0} ∩ (fun q : I × I => γ i q.2) ⁻¹' A) ∪
          {q | x ∈ A ∧ (q.1 = 1 ∨ q.2 = 0 ∨ q.2 = 1)} := by
      ext q
      simp only [mem_preimage, Sum.elim_inr, mem_image, mem_union, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨y, hy, h⟩
        rcases cell_eq_incl_iff.1 h.symm with ⟨h₀, rfl⟩ | ⟨rfl, hq⟩
        exacts [.inl ⟨h₀, hy⟩, .inr ⟨hy, hq⟩]
      · rintro (⟨h₀, hA⟩ | ⟨hx, h⟩)
        exacts [⟨_, hA, (cell_eq_incl_iff.2 (.inl ⟨h₀, rfl⟩)).symm⟩,
          ⟨_, hx, (cell_eq_incl_iff.2 (.inr ⟨rfl, h⟩)).symm⟩]
    rw [h]
    refine ((isClosed_eq continuous_fst continuous_const).inter
      (hA.preimage ((γ i).continuous.comp continuous_snd))).union ?_
    by_cases hx : x ∈ A
    · simp only [hx, true_and, ofPred_or]
      exact (isClosed_eq continuous_fst continuous_const).union
        ((isClosed_eq continuous_snd continuous_const).union
          (isClosed_eq continuous_snd continuous_const))
    · simp [hx]

/-! ### Attaching 2-cells induces a surjection on fundamental groups -/

section Surjective

open unitInterval

variable (γ) in
/-- The centres of the attached cells. -/
private abbrev centres : Set (TwoCellAttachment γ) :=
  range fun i => cell γ i squareCentre

private lemma isClosed_centres : IsClosed (centres γ) := by
  rw [← isQuotientMap_sumElim.isClosed_preimage, isClosed_sum_iff, isClosed_sigma_iff]
  refine ⟨?_, fun j => ?_⟩
  · convert isClosed_empty
    ext y
    simpa using fun i => (incl_ne_cell squareCentre_mem_Ioo_prod_Ioo y (i := i)).symm
  · convert isClosed_singleton (x := squareCentre)
    ext q
    simp only [mem_preimage, Sum.elim_inr, mem_range, mem_singleton_iff]
    constructor
    · rintro ⟨i, h⟩
      exact ((cell_eq_cell_iff squareCentre_mem_Ioo_prod_Ioo).1 h.symm).2
    · rintro rfl
      exact ⟨j, rfl⟩

/-- The radial deformation of the cells, at time `t`, on `X ⊕ Σ _ : ι, I × I`. -/
private def deformSum (t : I) : X ⊕ (Σ _ : ι, I × I) → X ⊕ (Σ _ : ι, I × I) :=
  Sum.map id fun q => ⟨q.1, radialPush t q.2⟩

/-- The radial deformation fixes the normal forms of the points of the edges of the cells. -/
private lemma mk_deformSum_cellNormalize (t : I) (a : X ⊕ Σ _ : ι, I × I) :
    mk γ (deformSum t (cellNormalize γ a)) = mk γ (deformSum t a) := by
  rcases a with y | ⟨i, q⟩
  · rfl
  by_cases hq : q ∈ (Ioo 0 1 ×ˢ Ioo 0 1 : Set (I × I))
  · rw [cellNormalize_inr_of_mem hq]
  · have h : deformSum t (cellNormalize γ (.inr ⟨i, q⟩)) = cellNormalize γ (.inr ⟨i, q⟩) := by
      simp only [cellNormalize, Sum.elim_inr]
      split_ifs <;> simp [deformSum, radialPush_of_notMem hq]
    rw [h, mk_cellNormalize]
    simp [deformSum, radialPush_of_notMem hq]

/-- The radial deformation of the cells, at time `t`: points of `X` are fixed, and each cell is
deformed by `unitInterval.radialPush t`. -/
private def deform (t : I) : TwoCellAttachment γ → TwoCellAttachment γ :=
  Quotient.lift (fun a => mk γ (deformSum t a)) fun a b hab => by
    rw [← mk_deformSum_cellNormalize, ← mk_deformSum_cellNormalize t b]
    exact congrArg (fun a => mk γ (deformSum t a)) hab

private lemma deform_mk (t : I) (a : X ⊕ Σ _ : ι, I × I) :
    deform t (mk γ a) = mk γ (deformSum t a) := (rfl)

private lemma deform_incl (t : I) (y : X) : deform t (incl γ y) = incl γ y := (rfl)

private lemma deform_cell (t : I) (i : ι) (q : I × I) :
    deform t (cell γ i q) = cell γ i (radialPush t q) := (rfl)

private lemma deform_zero (z : TwoCellAttachment γ) : deform 0 z = z := by
  induction z using ind with
  | incl y => rfl
  | cell i q => rw [deform_cell, radialPush_zero]

/-- At time `1` the radial deformation sends every point other than the centres into `X`. -/
private lemma deform_one_mem_range_incl {z : TwoCellAttachment γ} (hz : z ∉ centres γ) :
    deform 1 z ∈ range (incl γ) := by
  induction z using ind with
  | incl y => exact ⟨y, rfl⟩
  | cell i q =>
    rw [deform_cell]
    exact cell_mem_range_incl (radialPush_one_notMem fun h => hz ⟨i, h ▸ rfl⟩)

/-- The radial deformation is continuous on the complement of the centres. -/
private lemma continuous_deform :
    Continuous fun p : I × ↥(centres γ)ᶜ => deform p.1 p.2.1 := by
  have hf := (isQuotientMap_sumElim (γ := γ)).restrictPreimage_isOpen isClosed_centres.isOpen_compl
  refine hf.continuous_lift_prod_right ?_
  simp only [restrictPreimage_coe, sumElim_eq_mk, deform_mk]
  refine (continuous_quot_mk : Continuous (mk γ)).comp ?_
  -- The deformation is continuous at every point of the preimage of the complement of the
  -- centres: on `X` it is the identity, and on a cell it is the radial deformation away from the
  -- centre.
  set P := Sum.elim (incl γ) (fun q : Σ _ : ι, I × I => cell γ q.1 q.2) ⁻¹' (centres γ)ᶜ
  have hopen : IsOpen ((univ : Set I) ×ˢ P) :=
    isOpen_univ.prod (isClosed_centres.isOpen_compl.preimage isQuotientMap_sumElim.continuous)
  have hcont : ContinuousOn (fun p : I × (X ⊕ Σ _ : ι, I × I) => deformSum p.1 p.2)
      ((univ : Set I) ×ˢ P) := by
    refine (hopen.continuousOn_iff).2 ?_
    rintro ⟨t, y | ⟨i, q⟩⟩ ⟨-, ha⟩
    · have he : IsOpenEmbedding (Prod.map id Sum.inl : I × X → I × (X ⊕ Σ _ : ι, I × I)) :=
        IsOpenEmbedding.id.prodMap IsOpenEmbedding.inl
      refine (he.continuousAt_iff (x := (t, y))).1 ?_
      exact (continuous_inl.comp continuous_snd).continuousAt
    · have he : IsOpenEmbedding (Prod.map id (Sum.inr ∘ Sigma.mk (β := fun _ : ι => I × I) i) :
          I × (I × I) → I × (X ⊕ Σ _ : ι, I × I)) :=
        IsOpenEmbedding.id.prodMap (IsOpenEmbedding.inr.comp IsOpenEmbedding.sigmaMk)
      refine (he.continuousAt_iff (x := (t, q))).1 ?_
      have hq : q ≠ squareCentre := fun h => ha ⟨i, h ▸ rfl⟩
      exact (continuous_inr.comp continuous_sigmaMk).continuousAt.comp
        (continuousAt_radialPush hq)
  exact hcont.comp_continuous (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    fun p => ⟨trivial, p.2.2⟩

/-- At time `1` the radial deformation retracts the complement of the centres onto `X`. -/
private def retraction : C(↥(centres γ)ᶜ, X) :=
  ⟨fun z => isClosedEmbedding_incl.isEmbedding.toHomeomorph.symm
      ⟨deform 1 z.1, deform_one_mem_range_incl z.2⟩,
    isClosedEmbedding_incl.isEmbedding.toHomeomorph.symm.continuous.comp
      ((continuous_deform.comp (continuous_const.prodMk continuous_id)).subtype_mk _)⟩

private lemma incl_retraction (z : ↥(centres γ)ᶜ) : incl γ (retraction z) = deform 1 z.1 :=
  congrArg Subtype.val
    (isClosedEmbedding_incl.isEmbedding.toHomeomorph.apply_symm_apply ⟨deform 1 z.1, _⟩)

private lemma retraction_incl (y : X) (hy : incl γ y ∈ (centres γ)ᶜ) :
    retraction ⟨incl γ y, hy⟩ = y :=
  incl_injective (incl_retraction _)

/-- The open cells with their centres removed are path connected. -/
private lemma image_cell_inter_compl_centres (i : ι) :
    cell γ i '' (Ioo 0 1 ×ˢ Ioo 0 1) ∩ (centres γ)ᶜ =
      cell γ i '' (Ioo 0 1 ×ˢ Ioo 0 1 \ {squareCentre}) := by
  ext z
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hz⟩
    exact ⟨q, ⟨hq, fun h => hz ⟨i, (congrArg (cell γ i) h).symm⟩⟩, rfl⟩
  · rintro ⟨q, ⟨hq, hqc⟩, rfl⟩
    refine ⟨⟨q, hq, rfl⟩, ?_⟩
    rintro ⟨j, h⟩
    exact hqc ((cell_eq_cell_iff hq).1 h).2.symm

/-- **Attaching 2-cells induces a surjection on fundamental groups.** Every loop in the space with
the 2-cells attached is homotopic to a loop in `X`. -/
theorem surjective_map_incl : Function.Surjective (FundamentalGroup.map (incl γ) x) := by
  have hT : IsOpen (Ioo 0 1 ×ˢ Ioo 0 1 : Set (I × I)) := isOpen_Ioo.prod isOpen_Ioo
  have hxU : incl γ x ∈ (centres γ)ᶜ := fun ⟨i, h⟩ =>
    incl_ne_cell squareCentre_mem_Ioo_prod_Ioo x h.symm
  intro g
  obtain ⟨p, rfl⟩ : ∃ p : Path (incl γ x) (incl γ x),
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) = g :=
    ⟨Quotient.out (FundamentalGroup.toPath g), FundamentalGroup.fromPath_mk_out g⟩
  -- Push the loop off the centres, through the simply connected open cells.
  obtain ⟨δ, hδ, hpδ⟩ := Path.exists_range_subset_homotopic
    (W := fun i => cell γ i '' (Ioo 0 1 ×ˢ Ioo 0 1))
    (fun z => by
      by_cases hz : z ∈ (centres γ)ᶜ
      · exact .inl (isClosed_centres.isOpen_compl.mem_nhds hz)
      · obtain ⟨i, rfl⟩ := not_not.1 hz
        exact .inr ⟨i, (isOpen_image_cell hT subset_rfl).mem_nhds
          ⟨_, squareCentre_mem_Ioo_prod_Ioo, rfl⟩⟩)
    (fun i => isSimplyConnected_image_cell)
    (fun i => by
      rw [image_cell_inter_compl_centres]
      exact (isPathConnected_Ioo_prod_Ioo_diff_singleton squareCentre_mem_Ioo_prod_Ioo).image
        (cell γ i).continuous)
    (fun i j hij => by
      rintro _ ⟨⟨q, hq, rfl⟩, ⟨q', hq', h⟩⟩
      exact absurd ((cell_eq_cell_iff hq).1 h).1 (Ne.symm hij))
    hxU hxU p
  -- Retract the pushed-off loop onto `X`.
  let ε : Path x x :=
    { toFun := fun t => retraction ⟨δ t, hδ (mem_range_self t)⟩
      continuous_toFun := retraction.continuous.comp (δ.continuous.subtype_mk _)
      source' := (congrArg retraction (Subtype.ext δ.source)).trans (retraction_incl x hxU)
      target' := (congrArg retraction (Subtype.ext δ.target)).trans (retraction_incl x hxU) }
  refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ε), ?_⟩
  rw [TauCeti.FundamentalGroup.map_fromPath]
  refine congrArg CategoryTheory.End.of (Quotient.sound ?_)
  refine (Path.homotopic_of_continuous_square (fun q => deform q.1 (δ q.2))
    ((continuous_deform (γ := γ)).comp (continuous_fst.prodMk
      ((δ.continuous.comp continuous_snd).subtype_mk fun q => hδ (mem_range_self q.2))))
    (fun t => deform_zero _) (fun t => (incl_retraction ⟨δ t, hδ (mem_range_self t)⟩).symm)
    (fun t => by rw [δ.source, deform_incl]) (fun t => by rw [δ.target, deform_incl])).symm.trans
    hpδ.symm

end Surjective

end TwoCellAttachment

end TauCeti

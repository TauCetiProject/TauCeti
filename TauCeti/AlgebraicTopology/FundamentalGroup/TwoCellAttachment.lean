/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Homotopy.Path
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic

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
* `TauCeti.TwoCellAttachment.hom_ext`: maps out of the space are determined on `X` and the cells.
* `TauCeti.TwoCellAttachment.exists_comp_incl_eq_iff`: a map out of `X` extends over the attached
  cells exactly when it makes every loop `γ i` nullhomotopic.
* `TauCeti.TwoCellAttachment.map_incl_fromPath`: the inclusion kills the class of every loop
  `γ i` in the fundamental group.

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

end TwoCellAttachment

end TauCeti

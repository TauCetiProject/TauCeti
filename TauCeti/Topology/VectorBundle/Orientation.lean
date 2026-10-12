/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.LinearAlgebra.Orientation

/-!
# Orientations of real vector bundles

An orientation of a real vector bundle `E → B` with finite-dimensional model fibre `F` is a choice
of an orientation of every fibre `E b` that varies continuously with `b`. Continuity is read in
local trivializations: a linear trivialization `e` identifies the fibre over each point of its base
set with `F`, so it reads a family of fibre orientations as a family of orientations of the single
space `F` (`Bundle.Trivialization.mapOrientation`), and the family is continuous when these
readings are locally constant.

A `TauCeti.VectorBundleOrientation F E ι` asks for this in the preferred trivialization at every
point. When `ι` has cardinality the rank of the bundle, the coordinate changes between
trivializations of the atlas have continuous, nowhere-vanishing determinants, so local constancy
in one trivialization of the atlas implies it in every other
(`Bundle.Trivialization.eventually_mapOrientation_eq_of_eventually`): an orientation is locally
constant in every trivialization of the atlas
(`TauCeti.VectorBundleOrientation.eventually_mapOrientation_eq`), and conversely it suffices to
check local constancy in any chosen trivializations of the atlas
(`TauCeti.VectorBundleOrientation.ofEventually`).

An orientation of a plane bundle (`ι = Fin 2`) is the data on which the Euler class of the bundle
in `H²(B; ℤ)` depends, the opposite orientation giving the opposite class. Over a preconnected
base an orientation is determined by its value at a single point: two orientations either agree
or are opposite (`TauCeti.VectorBundleOrientation.eq_or_eq_neg`). The trivial bundle `B × F`
carries the constant orientations (`TauCeti.VectorBundleOrientation.trivial`), and over a
preconnected base these are all of its orientations
(`TauCeti.VectorBundleOrientation.eq_trivial`).

## Main definitions

* `Bundle.Trivialization.mapOrientation`: an orientation of a fibre, read in a trivialization as
  an orientation of the model fibre.
* `TauCeti.VectorBundleOrientation F E ι`: an orientation of the vector bundle `E`.
* `TauCeti.VectorBundleOrientation.ofEventually`: an orientation from local constancy in chosen
  trivializations of the atlas.
* `TauCeti.VectorBundleOrientation.trivial`: the constant orientations of a trivial bundle.

## Main results

* `TauCeti.VectorBundleOrientation.eventually_mapOrientation_eq`: an orientation is locally
  constant when read in any trivialization of the atlas.
* `TauCeti.VectorBundleOrientation.eq_or_eq_neg`: over a preconnected base, two orientations of
  a bundle are equal or opposite.
* `TauCeti.VectorBundleOrientation.eq_trivial`: over a preconnected base, every orientation of a
  trivial bundle is constant.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (oriented vector bundles and the Euler class).
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped Topology

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] (ι : Type*)

namespace Bundle.Trivialization

/-- An orientation of the fibre over a point `b` of the base set of a linear trivialization `e`,
read as an orientation of the model fibre: its transport along the linear equivalence `E b ≃ F`
given by `e`. -/
def mapOrientation (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    Orientation ℝ (E b) ι ≃ Orientation ℝ F ι :=
  Orientation.map ι (e.linearEquivAt ℝ b hb)

variable {ι}

-- Keep this lemma for explicit rewriting: a simp attribute unfolds the left-hand side of
-- `mapOrientation_neg`, making that simp lemma fail the `simpNF` linter.
theorem mapOrientation_apply (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) (o : Orientation ℝ (E b) ι) :
    e.mapOrientation ι hb o = Orientation.map ι (e.linearEquivAt ℝ b hb) o :=
  (rfl)

@[simp]
theorem mapOrientation_neg (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) (o : Orientation ℝ (E b) ι) :
    e.mapOrientation ι hb (-o) = -e.mapOrientation ι hb o :=
  Module.Ray.map_neg _ o

/-- Reading a fibre orientation in a second trivialization applies the coordinate change to its
reading in the first. -/
theorem mapOrientation_eq_map_coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear ℝ]
    [e'.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet)
    (o : Orientation ℝ (E b) ι) :
    e'.mapOrientation ι hb' o =
      Orientation.map ι (e.coordChangeL ℝ e' b).toLinearEquiv (e.mapOrientation ι hb o) := by
  have hcomp : (e.linearEquivAt ℝ b hb).trans (e.coordChangeL ℝ e' b).toLinearEquiv =
      e'.linearEquivAt ℝ b hb' := by
    rw [coe_coordChangeL' e e' ⟨hb, hb'⟩]
    calc
      _ = ((e.linearEquivAt ℝ b hb).trans (e.linearEquivAt ℝ b hb).symm).trans
          (e'.linearEquivAt ℝ b hb') := (LinearEquiv.trans_assoc _ _ _).symm
      _ = _ := by rw [LinearEquiv.self_trans_symm, LinearEquiv.refl_trans]
  simp only [mapOrientation_apply, ← Orientation.map_trans, hcomp]

variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] [Fintype ι]
  [FiniteDimensional ℝ F]

/-- If a family of fibre orientations is locally constant near `b` when read in one trivialization
of the atlas, then it is locally constant near `b` when read in any other, provided `ι` has
cardinality the rank of the bundle: the coordinate change has continuous nonvanishing
determinant, whose sign is therefore locally constant. -/
theorem eventually_mapOrientation_eq_of_eventually (hι : Fintype.card ι = finrank ℝ F)
    (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    {o : ∀ b, Orientation ℝ (E b) ι} {b : B} (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet)
    (h : ∀ᶠ x in 𝓝 b, ∀ hx : x ∈ e.baseSet,
      e.mapOrientation ι hx (o x) = e.mapOrientation ι hb (o b)) :
    ∀ᶠ x in 𝓝 b, ∀ hx : x ∈ e'.baseSet,
      e'.mapOrientation ι hx (o x) = e'.mapOrientation ι hb' (o b) := by
  have hmem : e.baseSet ∩ e'.baseSet ∈ 𝓝 b :=
    (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨hb, hb'⟩
  -- The determinant of the coordinate change is continuous at `b` and nonzero there, so its
  -- product with its value at `b` stays positive near `b`.
  set d : B → ℝ := fun x ↦ (e.coordChangeL ℝ e' x : F →L[ℝ] F).det
  have hdc : ContinuousAt d b :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      ((continuousOn_coordChange ℝ e e').continuousAt hmem)
  have hdb : d b ≠ 0 := by
    have := (LinearEquiv.det (e.coordChangeL ℝ e' b).toLinearEquiv).ne_zero
    rwa [LinearEquiv.coe_det] at this
  have hpos : ∀ᶠ x in 𝓝 b, 0 < d x * d b :=
    (hdc.mul continuousAt_const).eventually (lt_mem_nhds (mul_self_pos.2 hdb))
  filter_upwards [h, hmem, hpos] with x hx hxs hxpos hx'
  rw [mapOrientation_eq_map_coordChangeL e e' hxs.1 hx', hx hxs.1,
    mapOrientation_eq_map_coordChangeL e e' hb hb', Orientation.map_eq_map_iff_det_mul_pos _ _ _ hι]
  exact hxpos

end Bundle.Trivialization

namespace TauCeti

variable (F E) [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- An orientation of the real vector bundle `E` with model fibre `F`, indexed by `ι`: an
orientation of every fibre, such that near each point `b` the orientations of the fibres, read in
the preferred trivialization at `b`, all agree with that of the fibre over `b`. This is meaningful
when `ι` has cardinality the rank of the bundle; it is the condition that the fibre orientations
vary continuously with the base point. -/
structure VectorBundleOrientation where
  /-- The orientation of the fibre over each point. -/
  toFun : ∀ b, Orientation ℝ (E b) ι
  /-- The fibre orientations are locally constant in the preferred trivializations. -/
  eventually_mapOrientation_eq' : ∀ b, ∀ᶠ x in 𝓝 b,
    ∀ hx : x ∈ (trivializationAt F E b).baseSet,
      (trivializationAt F E b).mapOrientation ι hx (toFun x) =
        (trivializationAt F E b).mapOrientation ι (FiberBundle.mem_baseSet_trivializationAt' b)
          (toFun b)

namespace VectorBundleOrientation

variable {F E ι}

instance : DFunLike (VectorBundleOrientation F E ι) B (fun b ↦ Orientation ℝ (E b) ι) where
  coe := toFun
  coe_injective o o' h := by cases o; cases o'; congr

@[simp]
theorem coe_mk (o : ∀ b, Orientation ℝ (E b) ι) (ho) :
    ⇑(⟨o, ho⟩ : VectorBundleOrientation F E ι) = o :=
  rfl

@[ext]
theorem ext {o o' : VectorBundleOrientation F E ι} (h : ∀ b, o b = o' b) : o = o' :=
  DFunLike.ext _ _ h

/-- The opposite orientation, reversing the orientation of every fibre. -/
instance : Neg (VectorBundleOrientation F E ι) where
  neg o := ⟨fun b ↦ -o.toFun b, fun b ↦ (o.eventually_mapOrientation_eq' b).mono fun _ hx hx' ↦ by
    rw [Trivialization.mapOrientation_neg, Trivialization.mapOrientation_neg, hx hx']⟩

@[simp]
theorem neg_apply (o : VectorBundleOrientation F E ι) (b : B) : (-o) b = -o b :=
  (rfl)

protected theorem neg_neg (o : VectorBundleOrientation F E ι) : - -o = o := by
  ext b
  rw [neg_apply, neg_apply]
  -- `rw [neg_neg]` does not find the pattern: the negation on `Orientation` reached through
  -- `InvolutiveNeg` is only reducibly, not syntactically, the one in the goal.
  exact _root_.neg_neg (o b)

instance : InvolutiveNeg (VectorBundleOrientation F E ι) where
  neg_neg := VectorBundleOrientation.neg_neg

/-- Over a nonempty base, an orientation differs from the opposite orientation. -/
theorem ne_neg [Nonempty B] (o : VectorBundleOrientation F E ι) : o ≠ -o := fun h ↦
  Module.Ray.ne_neg_self (o (Classical.arbitrary B)) congr($h (Classical.arbitrary B))

variable (B) in
/-- The constant orientation `o` of the fibres of the trivial bundle `B × F`. -/
def trivial (o : Orientation ℝ F ι) : VectorBundleOrientation F (Bundle.Trivial B F) ι where
  toFun _ := o
  eventually_mapOrientation_eq' b := Eventually.of_forall fun x hx ↦ by
    have h (y : B) (hy : y ∈ (trivializationAt F (Bundle.Trivial B F) b).baseSet) :
        (trivializationAt F (Bundle.Trivial B F) b).linearEquivAt ℝ y hy =
          LinearEquiv.refl ℝ F := by
      ext v
      simp [Trivialization.linearEquivAt_apply]
    rw [Trivialization.mapOrientation_apply, Trivialization.mapOrientation_apply, h, h]

@[simp]
theorem trivial_apply (o : Orientation ℝ F ι) (b : B) : trivial B o b = o :=
  (rfl)

@[simp]
theorem neg_trivial (o : Orientation ℝ F ι) : -trivial B o = trivial B (-o) :=
  ext fun _ ↦ (rfl)

/-- The set of points where two orientations agree is open. -/
theorem isOpen_setOf_eq (o o' : VectorBundleOrientation F E ι) :
    IsOpen {b | o b = o' b} := by
  refine isOpen_iff_mem_nhds.2 fun b hb ↦ ?_
  have hmem := (trivializationAt F E b).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' b)
  filter_upwards [o.eventually_mapOrientation_eq' b, o'.eventually_mapOrientation_eq' b, hmem]
    with x hx hx' hxs
  exact (Trivialization.mapOrientation ι _ hxs).injective <| by
    calc
      _ = _ := hx hxs
      _ = _ := congrArg ((trivializationAt F E b).mapOrientation ι
        (FiberBundle.mem_baseSet_trivializationAt' b)) hb
      _ = _ := (hx' hxs).symm

variable [Fintype ι] [FiniteDimensional ℝ F]

/-- An orientation is locally constant when read in any trivialization of the atlas. -/
theorem eventually_mapOrientation_eq (hι : Fintype.card ι = finrank ℝ F)
    (o : VectorBundleOrientation F E ι) (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    {b : B} (hb : b ∈ e.baseSet) :
    ∀ᶠ x in 𝓝 b, ∀ hx : x ∈ e.baseSet, e.mapOrientation ι hx (o x) = e.mapOrientation ι hb (o b) :=
  (trivializationAt F E b).eventually_mapOrientation_eq_of_eventually hι e
    (FiberBundle.mem_baseSet_trivializationAt' b) hb (o.eventually_mapOrientation_eq' b)

/-- An orientation of the bundle from fibre orientations that are locally constant near each
point `b` when read in some trivialization `e b` of the atlas whose base set contains `b`. -/
def ofEventually (hι : Fintype.card ι = finrank ℝ F) (o : ∀ b, Orientation ℝ (E b) ι)
    (e : B → Trivialization F (π F E)) [∀ b, MemTrivializationAtlas (e b)]
    (he : ∀ b, b ∈ (e b).baseSet)
    (ho : ∀ b, ∀ᶠ x in 𝓝 b, ∀ hx : x ∈ (e b).baseSet,
      (e b).mapOrientation ι hx (o x) = (e b).mapOrientation ι (he b) (o b)) :
    VectorBundleOrientation F E ι where
  toFun := o
  eventually_mapOrientation_eq' b :=
    (e b).eventually_mapOrientation_eq_of_eventually hι (trivializationAt F E b) (he b)
      (FiberBundle.mem_baseSet_trivializationAt' b) (ho b)

@[simp]
theorem coe_ofEventually (hι : Fintype.card ι = finrank ℝ F) (o : ∀ b, Orientation ℝ (E b) ι)
    (e : B → Trivialization F (π F E)) [∀ b, MemTrivializationAtlas (e b)]
    (he : ∀ b, b ∈ (e b).baseSet) (ho) : ⇑(ofEventually hι o e he ho) = o :=
  (rfl)

/-- Over a preconnected base, two orientations of a bundle of rank `card ι` either agree or are
opposite. -/
theorem eq_or_eq_neg [PreconnectedSpace B] (hι : Fintype.card ι = finrank ℝ F)
    (o o' : VectorBundleOrientation F E ι) : o = o' ∨ o = -o' := by
  -- Read in a trivialization, the fibre orientations are orientations of `F`, whose rank is
  -- `card ι`, so they are equal or opposite.
  have hfib (b : B) : o b = o' b ∨ o b = -o' b := by
    have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) b
    have hinj := ((trivializationAt F E b).mapOrientation ι hb).injective
    rcases Orientation.eq_or_eq_neg (((trivializationAt F E b).mapOrientation ι hb) (o b))
      (((trivializationAt F E b).mapOrientation ι hb) (o' b)) hι with h | h
    · exact .inl (hinj h)
    · exact .inr (hinj (by rwa [Trivialization.mapOrientation_neg]))
  have hcompl : {b | o b = o' b}ᶜ = {b | o b = (-o') b} := by
    ext b
    simp only [mem_compl_iff, mem_ofPred_eq, neg_apply]
    exact ⟨(hfib b).resolve_left, fun h h' ↦ Module.Ray.ne_neg_self (o' b) (h'.symm.trans h)⟩
  have hclopen : IsClopen {b | o b = o' b} :=
    ⟨isOpen_compl_iff.1 (hcompl ▸ isOpen_setOf_eq o (-o')),
      isOpen_setOf_eq o o'⟩
  rcases isClopen_iff.1 hclopen with h | h
  · right
    ext b
    exact (hfib b).resolve_left fun h' ↦ (h.subset h' : b ∈ (∅ : Set B))
  · left
    ext b
    exact (h.symm.subset (mem_univ b) : o b = o' b)

/-- Over a preconnected base, an orientation of a trivial bundle of rank `card ι` is the constant
orientation given by its value at any point. -/
theorem eq_trivial [PreconnectedSpace B] (hι : Fintype.card ι = finrank ℝ F)
    (o : VectorBundleOrientation F (Bundle.Trivial B F) ι) (b : B) : o = trivial B (o b) := by
  refine (eq_or_eq_neg hι o (trivial B (o b))).resolve_right fun h ↦ ?_
  have hb : o b = -o b := by simpa using congr($h b)
  exact Module.Ray.ne_neg_self (o b) hb

end VectorBundleOrientation

end TauCeti

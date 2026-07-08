/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# `J`-holomorphic maps for a constant almost complex structure

This file adds the first map-level definition for the analytic Heegaard Floer roadmap:
a map between real normed spaces, each carrying a single *fixed* almost complex structure,
is holomorphic at a point when it has a Frechet derivative there and that derivative commutes
with the two structures.

## Scope: the constant-structure (flat) model only

The predicates here are named `IsConstJHolomorphic*` on purpose. They fix one almost complex
structure `J` on the source `V` and one `J'` on the target `W`, both constant across the whole
space, and ask that `df ∘ J = J' ∘ df`. This is ordinary several-variable holomorphy read in
linear complex coordinates -- the integrable, flat model -- not a genuine `J`-holomorphic curve.

A genuine `J`-holomorphic curve `u : Σ → M` into an almost complex manifold satisfies
`du ∘ j = J(u(z)) ∘ du`, with the target structure `J` *varying* along the map, evaluated at the
image point `u(z)`. The constant-structure predicate cannot express that: its target structure
`J'` does not depend on the point. This whole `IsConstJHolomorphic*` family, and the downstream
Neg/Transport/Congruence/Prod/Line/energy calculus built on it, therefore lives entirely in the
flat model.

The `Const` prefix is a deliberate reservation. The plain name `IsJHolomorphic` is left free for
the eventual varying-structure curve definition (roadmap `HeegaardFloer/README.md`, Lane F2.1's
`J`-holomorphic maps and the manifold/bundle layer built on them), so that layer does not
silently collide with -- or get mistaken for -- the flat model recorded here. Those later
versions should still use this file as their local model on coordinate charts and tangent
fibers, matching the same Cauchy--Riemann
convention. This settles the design choice raised in
`https://github.com/TauCetiProject/TauCeti/issues/797`, Task 1: rename (rather than
point-parametrize `J'`), and document the scope.

## Main declarations

* `IsConstJHolomorphicAt`: a map has a complex-linear Frechet derivative at a point.
* `IsConstJHolomorphicWithinAt`: a map has a complex-linear Frechet derivative within a set.
* `IsConstJHolomorphicOn` and `IsConstJHolomorphic`: setwise and global versions.

It also records the immediate differentiability and continuity consequences of these predicates.

The Cauchy--Riemann equation `df ∘ J = J' ∘ df` is real-linear in `df`, so a continuous
real-linear map is holomorphic in this sense exactly when it is complex-linear, and such maps are
closed under pointwise sums, differences, and real scalar multiples:

* `isConstJHolomorphicAt_continuousLinearMap_iff` and
  `isConstJHolomorphic_continuousLinearMap_iff`: a continuous real-linear map is
  `IsConstJHolomorphic` iff it is complex-linear.
* `IsConstJHolomorphicAt.add`, `IsConstJHolomorphicAt.neg`, `IsConstJHolomorphicAt.sub`,
  `IsConstJHolomorphicAt.const_smul` and their within-set, setwise, and global analogues.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: the Cauchy--Riemann equation is `df ∘ J = J' ∘ df`.
-/

@[expose] public section

namespace TauCeti

variable {V W X : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

section JHolomorphic

/-- A map is `J`-holomorphic at a point if its Frechet derivative exists there and
intertwines the source and target almost complex structures. -/
def IsConstJHolomorphicAt (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) (x : V) : Prop :=
  ∃ f' : V →L[ℝ] W, HasFDerivAt f f' x ∧ IsComplexLinearMap J J' f'.toLinearMap

/-- A map is `J`-holomorphic within a set at a point if its Frechet derivative within the
set exists there and intertwines the source and target almost complex structures. -/
def IsConstJHolomorphicWithinAt (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) (s : Set V) (x : V) : Prop :=
  ∃ f' : V →L[ℝ] W, HasFDerivWithinAt f f' s x ∧ IsComplexLinearMap J J' f'.toLinearMap

/-- A map is `J`-holomorphic on a set if it is `J`-holomorphic within that set at every
point of the set. -/
def IsConstJHolomorphicOn (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) (s : Set V) : Prop :=
  ∀ x ∈ s, IsConstJHolomorphicWithinAt J J' f s x

/-- A globally `J`-holomorphic map is `J`-holomorphic at every point. -/
def IsConstJHolomorphic (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) : Prop :=
  ∀ x, IsConstJHolomorphicAt J J' f x

/-- Restate pointwise `J`-holomorphicity as existence of a complex-linear Frechet
derivative. -/
lemma isConstJHolomorphicAt_iff (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) (x : V) :
    IsConstJHolomorphicAt J J' f x ↔
      ∃ f' : V →L[ℝ] W, HasFDerivAt f f' x ∧ IsComplexLinearMap J J' f'.toLinearMap :=
  Iff.rfl

/-- Restate within-set `J`-holomorphicity as existence of a complex-linear Frechet
derivative within the set. -/
lemma isConstJHolomorphicWithinAt_iff (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (f : V → W) (s : Set V) (x : V) :
    IsConstJHolomorphicWithinAt J J' f s x ↔
      ∃ f' : V →L[ℝ] W,
        HasFDerivWithinAt f f' s x ∧ IsComplexLinearMap J J' f'.toLinearMap :=
  Iff.rfl

/-- Restate setwise `J`-holomorphicity as the within-set derivative condition at each
point of the set. -/
lemma isConstJHolomorphicOn_iff (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) (s : Set V) :
    IsConstJHolomorphicOn J J' f s ↔
      ∀ x ∈ s, ∃ f' : V →L[ℝ] W,
        HasFDerivWithinAt f f' s x ∧ IsComplexLinearMap J J' f'.toLinearMap :=
  Iff.rfl

/-- Restate global `J`-holomorphicity as the pointwise derivative condition at every point. -/
lemma isConstJHolomorphic_iff (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) :
    IsConstJHolomorphic J J' f ↔
      ∀ x, ∃ f' : V →L[ℝ] W, HasFDerivAt f f' x ∧
        IsComplexLinearMap J J' f'.toLinearMap :=
  Iff.rfl

/-- On the whole space, setwise `J`-holomorphicity is the same as global
`J`-holomorphicity. -/
@[simp]
lemma isConstJHolomorphicOn_univ (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) :
    IsConstJHolomorphicOn J J' f Set.univ ↔ IsConstJHolomorphic J J' f := by
  simp [IsConstJHolomorphicOn, IsConstJHolomorphicWithinAt, IsConstJHolomorphic,
    IsConstJHolomorphicAt, hasFDerivWithinAt_univ]

/-- The continuous-linear derivative witnessing `J`-holomorphicity at a point. -/
lemma IsConstJHolomorphicAt.hasFDerivAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsConstJHolomorphicAt J J' f x) :
    HasFDerivAt f hf.choose x :=
  hf.choose_spec.1

/-- The chosen derivative at a `J`-holomorphic point is complex-linear. -/
lemma IsConstJHolomorphicAt.derivative_isComplexLinear {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsConstJHolomorphicAt J J' f x) :
    IsComplexLinearMap J J' hf.choose.toLinearMap :=
  hf.choose_spec.2

/-- A `J`-holomorphic map is differentiable at the point. -/
lemma IsConstJHolomorphicAt.differentiableAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsConstJHolomorphicAt J J' f x) :
    DifferentiableAt ℝ f x :=
  hf.hasFDerivAt.differentiableAt

/-- A pointwise `J`-holomorphic map is continuous at the point. -/
lemma IsConstJHolomorphicAt.continuousAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsConstJHolomorphicAt J J' f x) :
    ContinuousAt f x :=
  hf.hasFDerivAt.continuousAt

/-- A pointwise `J`-holomorphic map is continuous within any source set at the point. -/
lemma IsConstJHolomorphicAt.continuousWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicAt J J' f x) :
    ContinuousWithinAt f s x :=
  hf.continuousAt.continuousWithinAt

/-- The Frechet derivative of a `J`-holomorphic map is complex-linear. -/
lemma IsConstJHolomorphicAt.fderiv_isComplexLinear {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsConstJHolomorphicAt J J' f x) :
    IsComplexLinearMap J J' (fderiv ℝ f x).toLinearMap := by
  simpa [hf.hasFDerivAt.fderiv] using hf.derivative_isComplexLinear

/-- The Frechet derivative of a `J`-holomorphic map commutes with the almost complex
structures pointwise. -/
lemma IsConstJHolomorphicAt.fderiv_apply_commute {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x v : V}
    (hf : IsConstJHolomorphicAt J J' f x) :
    fderiv ℝ f x (J v) = J' (fderiv ℝ f x v) :=
  (isComplexLinearMap_iff_apply J J' (fderiv ℝ f x).toLinearMap).mp
    hf.fderiv_isComplexLinear v

/-- A pointwise `J`-holomorphic map is `J`-holomorphic within any set. -/
lemma IsConstJHolomorphicAt.isConstJHolomorphicWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicAt J J' f x) :
    IsConstJHolomorphicWithinAt J J' f s x :=
  ⟨hf.choose, hf.hasFDerivAt.hasFDerivWithinAt, hf.derivative_isComplexLinear⟩

/-- The continuous-linear derivative witnessing `J`-holomorphicity within a set. -/
lemma IsConstJHolomorphicWithinAt.hasFDerivWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicWithinAt J J' f s x) :
    HasFDerivWithinAt f hf.choose s x :=
  hf.choose_spec.1

/-- The chosen within-set derivative is complex-linear. -/
lemma IsConstJHolomorphicWithinAt.derivative_isComplexLinear {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicWithinAt J J' f s x) :
    IsComplexLinearMap J J' hf.choose.toLinearMap :=
  hf.choose_spec.2

/-- A map that is `J`-holomorphic within a set is differentiable within that set. -/
lemma IsConstJHolomorphicWithinAt.differentiableWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicWithinAt J J' f s x) :
    DifferentiableWithinAt ℝ f s x :=
  hf.hasFDerivWithinAt.differentiableWithinAt

/-- A map that is `J`-holomorphic within a set is continuous within that set at the point. -/
lemma IsConstJHolomorphicWithinAt.continuousWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicWithinAt J J' f s x) :
    ContinuousWithinAt f s x :=
  hf.hasFDerivWithinAt.continuousWithinAt

/-- The within-set Frechet derivative is complex-linear when the set has unique derivatives. -/
lemma IsConstJHolomorphicWithinAt.fderivWithin_isComplexLinear {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicWithinAt J J' f s x) (hs : UniqueDiffWithinAt ℝ s x) :
    IsComplexLinearMap J J' (fderivWithin ℝ f s x).toLinearMap := by
  simpa [hf.hasFDerivWithinAt.fderivWithin hs] using hf.derivative_isComplexLinear

/-- The within-set Frechet derivative commutes with the almost complex structures pointwise. -/
lemma IsConstJHolomorphicWithinAt.fderivWithin_apply_commute {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x v : V}
    (hf : IsConstJHolomorphicWithinAt J J' f s x) (hs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ f s x (J v) = J' (fderivWithin ℝ f s x v) :=
  (isComplexLinearMap_iff_apply J J' (fderivWithin ℝ f s x).toLinearMap).mp
    (hf.fderivWithin_isComplexLinear hs) v

/-- A within-set `J`-holomorphic map is pointwise `J`-holomorphic when the set is a
neighborhood of the point. -/
lemma IsConstJHolomorphicWithinAt.isConstJHolomorphicAt_of_mem_nhds {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicWithinAt J J' f s x) (hs : s ∈ nhds x) :
    IsConstJHolomorphicAt J J' f x :=
  ⟨hf.choose, (hasFDerivWithinAt_of_mem_nhds hs).mp hf.hasFDerivWithinAt,
    hf.derivative_isComplexLinear⟩

/-- A map that is `J`-holomorphic within a neighborhood of the point is continuous at the
point. -/
lemma IsConstJHolomorphicWithinAt.continuousAt_of_mem_nhds {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicWithinAt J J' f s x) (hs : s ∈ nhds x) :
    ContinuousAt f x :=
  hf.continuousWithinAt.continuousAt hs

/-- A map that is `J`-holomorphic within a neighborhood of the point is differentiable at the
point. -/
lemma IsConstJHolomorphicWithinAt.differentiableAt_of_mem_nhds {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicWithinAt J J' f s x) (hs : s ∈ nhds x) :
    DifferentiableAt ℝ f x :=
  (hf.isConstJHolomorphicAt_of_mem_nhds hs).differentiableAt

/-- A map that is `J`-holomorphic within a set is continuous within every smaller source set at
the point. -/
lemma IsConstJHolomorphicWithinAt.continuousWithinAt_mono {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s t : Set V} {x : V}
    (hf : IsConstJHolomorphicWithinAt J J' f s x) (hts : t ⊆ s) :
    ContinuousWithinAt f t x :=
  hf.continuousWithinAt.mono hts

/-- A constant map is `J`-holomorphic at every point. -/
@[simp]
lemma isConstJHolomorphicAt_const (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (c : W) (x : V) : IsConstJHolomorphicAt J J' (fun _ : V => c) x :=
  ⟨0, hasFDerivAt_const c x, by simp⟩

/-- The identity map is `J`-holomorphic for any fixed almost complex structure `J`. -/
@[simp]
lemma isConstJHolomorphicAt_id (J : AlmostComplexStructure V) (x : V) :
    IsConstJHolomorphicAt J J id x :=
  ⟨ContinuousLinearMap.id ℝ V, hasFDerivAt_id x, by simp⟩

/-- Eta-expanded form of `isConstJHolomorphicAt_id`. -/
@[simp]
lemma isConstJHolomorphicAt_id' (J : AlmostComplexStructure V) (x : V) :
    IsConstJHolomorphicAt J J (fun y : V => y) x :=
  isConstJHolomorphicAt_id J x

/-- Chain rule for pointwise `J`-holomorphic maps. -/
lemma IsConstJHolomorphicAt.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X}
    {f : V → W} {g : W → X} {x : V}
    (hg : IsConstJHolomorphicAt J' J'' g (f x)) (hf : IsConstJHolomorphicAt J J' f x) :
    IsConstJHolomorphicAt J J'' (g ∘ f) x := by
  refine ⟨hg.choose.comp hf.choose, hg.hasFDerivAt.comp x hf.hasFDerivAt, ?_⟩
  exact IsComplexLinearMap.comp hg.derivative_isComplexLinear hf.derivative_isComplexLinear

/-- A constant map is `J`-holomorphic within every set at every point. -/
@[simp]
lemma isConstJHolomorphicWithinAt_const (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (c : W) (s : Set V) (x : V) :
    IsConstJHolomorphicWithinAt J J' (fun _ : V => c) s x :=
  (isConstJHolomorphicAt_const J J' c x).isConstJHolomorphicWithinAt

/-- The identity map is `J`-holomorphic within every set at every point. -/
@[simp]
lemma isConstJHolomorphicWithinAt_id (J : AlmostComplexStructure V) (s : Set V) (x : V) :
    IsConstJHolomorphicWithinAt J J id s x :=
  (isConstJHolomorphicAt_id J x).isConstJHolomorphicWithinAt

/-- Eta-expanded form of `isConstJHolomorphicWithinAt_id`. -/
@[simp]
lemma isConstJHolomorphicWithinAt_id' (J : AlmostComplexStructure V) (s : Set V) (x : V) :
    IsConstJHolomorphicWithinAt J J (fun y : V => y) s x :=
  isConstJHolomorphicWithinAt_id J s x

/-- A constant map is `J`-holomorphic on every set. -/
@[simp]
lemma isConstJHolomorphicOn_const (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (c : W) (s : Set V) : IsConstJHolomorphicOn J J' (fun _ : V => c) s :=
  fun x _ => isConstJHolomorphicWithinAt_const J J' c s x

/-- The identity map is `J`-holomorphic on every set. -/
@[simp]
lemma isConstJHolomorphicOn_id (J : AlmostComplexStructure V) (s : Set V) :
    IsConstJHolomorphicOn J J id s :=
  fun x _ => isConstJHolomorphicWithinAt_id J s x

/-- Eta-expanded form of `isConstJHolomorphicOn_id`. -/
@[simp]
lemma isConstJHolomorphicOn_id' (J : AlmostComplexStructure V) (s : Set V) :
    IsConstJHolomorphicOn J J (fun y : V => y) s :=
  isConstJHolomorphicOn_id J s

/-- Chain rule for within-set `J`-holomorphic maps. -/
lemma IsConstJHolomorphicWithinAt.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X}
    {f : V → W} {g : W → X} {s : Set V} {t : Set W} {x : V}
    (hg : IsConstJHolomorphicWithinAt J' J'' g t (f x))
    (hf : IsConstJHolomorphicWithinAt J J' f s x) (hst : Set.MapsTo f s t) :
    IsConstJHolomorphicWithinAt J J'' (g ∘ f) s x := by
  refine ⟨hg.choose.comp hf.choose, hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt hst, ?_⟩
  exact IsComplexLinearMap.comp hg.derivative_isComplexLinear hf.derivative_isComplexLinear

/-- Chain rule for setwise `J`-holomorphic maps. -/
lemma IsConstJHolomorphicOn.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X}
    {f : V → W} {g : W → X} {s : Set V} {t : Set W}
    (hg : IsConstJHolomorphicOn J' J'' g t) (hf : IsConstJHolomorphicOn J J' f s)
    (hst : Set.MapsTo f s t) :
    IsConstJHolomorphicOn J J'' (g ∘ f) s :=
  fun x hx => (hg (f x) (hst hx)).comp (hf x hx) hst

/-- Restrict the domain set of a setwise `J`-holomorphic map. -/
lemma IsConstJHolomorphicOn.mono {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
    {f : V → W} {s t : Set V} (hf : IsConstJHolomorphicOn J J' f t) (hst : s ⊆ t) :
    IsConstJHolomorphicOn J J' f s :=
  fun x hx =>
    let hfx := hf x (hst hx)
    ⟨hfx.choose, hfx.hasFDerivWithinAt.mono hst, hfx.derivative_isComplexLinear⟩

/-- A map that is `J`-holomorphic on a set is differentiable on that set. -/
lemma IsConstJHolomorphicOn.differentiableOn {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V}
    (hf : IsConstJHolomorphicOn J J' f s) :
    DifferentiableOn ℝ f s :=
  fun x hx => (hf x hx).differentiableWithinAt

/-- A map that is `J`-holomorphic on a set is differentiable within that set at each of its
points. -/
lemma IsConstJHolomorphicOn.differentiableWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicOn J J' f s) (hx : x ∈ s) :
    DifferentiableWithinAt ℝ f s x :=
  (hf x hx).differentiableWithinAt

/-- A map that is `J`-holomorphic on a set is continuous on that set. -/
lemma IsConstJHolomorphicOn.continuousOn {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V}
    (hf : IsConstJHolomorphicOn J J' f s) :
    ContinuousOn f s :=
  fun x hx => (hf x hx).continuousWithinAt

/-- A map that is `J`-holomorphic on a set is continuous within that set at each of its points. -/
lemma IsConstJHolomorphicOn.continuousWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicOn J J' f s) (hx : x ∈ s) :
    ContinuousWithinAt f s x :=
  (hf x hx).continuousWithinAt

/-- A map that is `J`-holomorphic on a neighborhood of a point is differentiable at that point. -/
lemma IsConstJHolomorphicOn.differentiableAt_of_mem_nhds {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicOn J J' f s) (hs : s ∈ nhds x) :
    DifferentiableAt ℝ f x :=
  (hf x (mem_of_mem_nhds hs)).differentiableAt_of_mem_nhds hs

/-- A map that is `J`-holomorphic on a neighborhood of a point is continuous at that point. -/
lemma IsConstJHolomorphicOn.continuousAt_of_mem_nhds {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicOn J J' f s) (hs : s ∈ nhds x) :
    ContinuousAt f x :=
  (hf x (mem_of_mem_nhds hs)).continuousAt_of_mem_nhds hs

/-- A map that is `J`-holomorphic on an open set is pointwise differentiable at each point of
that set. -/
lemma IsConstJHolomorphicOn.differentiableAt_of_isOpen {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicOn J J' f s) (hs : IsOpen s) (hx : x ∈ s) :
    DifferentiableAt ℝ f x :=
  hf.differentiableAt_of_mem_nhds (hs.mem_nhds hx)

/-- A map that is `J`-holomorphic on an open set is continuous at each point of that set. -/
lemma IsConstJHolomorphicOn.continuousAt_of_isOpen {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicOn J J' f s) (hs : IsOpen s) (hx : x ∈ s) :
    ContinuousAt f x :=
  hf.continuousAt_of_mem_nhds (hs.mem_nhds hx)

/-- A globally `J`-holomorphic map is `J`-holomorphic on every set. -/
lemma IsConstJHolomorphic.isConstJHolomorphicOn {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W}
    (hf : IsConstJHolomorphic J J' f) (s : Set V) :
    IsConstJHolomorphicOn J J' f s :=
  fun x _ => (hf x).isConstJHolomorphicWithinAt

/-- A globally `J`-holomorphic map is differentiable. -/
lemma IsConstJHolomorphic.differentiable {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W}
    (hf : IsConstJHolomorphic J J' f) :
    Differentiable ℝ f :=
  fun x => (hf x).differentiableAt

/-- A globally `J`-holomorphic map is differentiable at every point. -/
lemma IsConstJHolomorphic.differentiableAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W}
    (hf : IsConstJHolomorphic J J' f) (x : V) :
    DifferentiableAt ℝ f x :=
  (hf x).differentiableAt

/-- A globally `J`-holomorphic map is continuous. -/
lemma IsConstJHolomorphic.continuous {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W}
    (hf : IsConstJHolomorphic J J' f) :
    Continuous f :=
  continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt

/-- A globally `J`-holomorphic map is continuous at every point. -/
lemma IsConstJHolomorphic.continuousAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W}
    (hf : IsConstJHolomorphic J J' f) (x : V) :
    ContinuousAt f x :=
  (hf x).continuousAt

/-- A globally `J`-holomorphic map is differentiable on every source set. -/
lemma IsConstJHolomorphic.differentiableOn {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W}
    (hf : IsConstJHolomorphic J J' f) (s : Set V) :
    DifferentiableOn ℝ f s :=
  (hf.isConstJHolomorphicOn s).differentiableOn

/-- A globally `J`-holomorphic map is continuous on every source set. -/
lemma IsConstJHolomorphic.continuousOn {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W}
    (hf : IsConstJHolomorphic J J' f) (s : Set V) :
    ContinuousOn f s :=
  (hf.isConstJHolomorphicOn s).continuousOn

/-- A constant map is globally `J`-holomorphic. -/
@[simp]
lemma isConstJHolomorphic_const (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (c : W) : IsConstJHolomorphic J J' (fun _ : V => c) :=
  fun x => isConstJHolomorphicAt_const J J' c x

/-- The identity map is globally `J`-holomorphic. -/
@[simp]
lemma isConstJHolomorphic_id (J : AlmostComplexStructure V) : IsConstJHolomorphic J J id :=
  fun x => isConstJHolomorphicAt_id J x

/-- Eta-expanded form of `isConstJHolomorphic_id`. -/
@[simp]
lemma isConstJHolomorphic_id' (J : AlmostComplexStructure V) :
    IsConstJHolomorphic J J (fun y : V => y) :=
  isConstJHolomorphic_id J

/-- Chain rule for global `J`-holomorphic maps. -/
lemma IsConstJHolomorphic.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X}
    {f : V → W} {g : W → X}
    (hg : IsConstJHolomorphic J' J'' g) (hf : IsConstJHolomorphic J J' f) :
    IsConstJHolomorphic J J'' (g ∘ f) :=
  fun x => (hg (f x)).comp (hf x)

end JHolomorphic

section LinearStructure

variable {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}

/-- A continuous real-linear map is `J`-holomorphic at a point iff it is complex-linear: its
derivative is the map itself, so the Cauchy--Riemann condition becomes complex-linearity. -/
lemma isConstJHolomorphicAt_continuousLinearMap_iff (F : V →L[ℝ] W) (x : V) :
    IsConstJHolomorphicAt J J' (⇑F) x ↔ IsComplexLinearMap J J' F.toLinearMap := by
  refine ⟨fun hF => ?_, fun h => ⟨F, F.hasFDerivAt, h⟩⟩
  obtain ⟨f', hf', hcl⟩ := hF
  rwa [hf'.unique F.hasFDerivAt] at hcl

/-- A continuous real-linear map is globally `J`-holomorphic iff it is complex-linear. -/
lemma isConstJHolomorphic_continuousLinearMap_iff (F : V →L[ℝ] W) :
    IsConstJHolomorphic J J' (⇑F) ↔ IsComplexLinearMap J J' F.toLinearMap :=
  ⟨fun h => (isConstJHolomorphicAt_continuousLinearMap_iff F 0).mp (h 0),
    fun h x => (isConstJHolomorphicAt_continuousLinearMap_iff F x).mpr h⟩

/-- The pointwise sum of two `J`-holomorphic maps is `J`-holomorphic. -/
lemma IsConstJHolomorphicAt.add {f g : V → W} {x : V}
    (hf : IsConstJHolomorphicAt J J' f x) (hg : IsConstJHolomorphicAt J J' g x) :
    IsConstJHolomorphicAt J J' (f + g) x := by
  refine ⟨hf.choose + hg.choose, hf.hasFDerivAt.add hg.hasFDerivAt, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_add]
  exact hf.derivative_isComplexLinear.add hg.derivative_isComplexLinear

/-- The pointwise negation of a `J`-holomorphic map is `J`-holomorphic. -/
lemma IsConstJHolomorphicAt.neg {f : V → W} {x : V} (hf : IsConstJHolomorphicAt J J' f x) :
    IsConstJHolomorphicAt J J' (-f) x := by
  refine ⟨-hf.choose, hf.hasFDerivAt.neg, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_neg]
  exact hf.derivative_isComplexLinear.neg

/-- The pointwise difference of two `J`-holomorphic maps is `J`-holomorphic. -/
lemma IsConstJHolomorphicAt.sub {f g : V → W} {x : V}
    (hf : IsConstJHolomorphicAt J J' f x) (hg : IsConstJHolomorphicAt J J' g x) :
    IsConstJHolomorphicAt J J' (f - g) x := by
  refine ⟨hf.choose - hg.choose, hf.hasFDerivAt.sub hg.hasFDerivAt, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_sub]
  exact hf.derivative_isComplexLinear.sub hg.derivative_isComplexLinear

/-- A real scalar multiple of a `J`-holomorphic map is `J`-holomorphic. -/
lemma IsConstJHolomorphicAt.const_smul {f : V → W} {x : V} (hf : IsConstJHolomorphicAt J J' f x)
    (c : ℝ) : IsConstJHolomorphicAt J J' (c • f) x := by
  refine ⟨c • hf.choose, hf.hasFDerivAt.const_smul c, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_smul]
  exact hf.derivative_isComplexLinear.smul c

/-- The pointwise sum of two maps `J`-holomorphic within a set is `J`-holomorphic within it. -/
lemma IsConstJHolomorphicWithinAt.add {f g : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicWithinAt J J' f s x) (hg : IsConstJHolomorphicWithinAt J J' g s x) :
    IsConstJHolomorphicWithinAt J J' (f + g) s x := by
  refine ⟨hf.choose + hg.choose, hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_add]
  exact hf.derivative_isComplexLinear.add hg.derivative_isComplexLinear

/-- The pointwise negation of a map `J`-holomorphic within a set is `J`-holomorphic within it. -/
lemma IsConstJHolomorphicWithinAt.neg {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicWithinAt J J' f s x) :
    IsConstJHolomorphicWithinAt J J' (-f) s x := by
  refine ⟨-hf.choose, hf.hasFDerivWithinAt.neg, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_neg]
  exact hf.derivative_isComplexLinear.neg

/-- The pointwise difference of two maps `J`-holomorphic within a set is `J`-holomorphic
within it. -/
lemma IsConstJHolomorphicWithinAt.sub {f g : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicWithinAt J J' f s x) (hg : IsConstJHolomorphicWithinAt J J' g s x) :
    IsConstJHolomorphicWithinAt J J' (f - g) s x := by
  refine ⟨hf.choose - hg.choose, hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_sub]
  exact hf.derivative_isComplexLinear.sub hg.derivative_isComplexLinear

/-- A real scalar multiple of a map `J`-holomorphic within a set is `J`-holomorphic within
it. -/
lemma IsConstJHolomorphicWithinAt.const_smul {f : V → W} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicWithinAt J J' f s x) (c : ℝ) :
    IsConstJHolomorphicWithinAt J J' (c • f) s x := by
  refine ⟨c • hf.choose, hf.hasFDerivWithinAt.const_smul c, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_smul]
  exact hf.derivative_isComplexLinear.smul c

/-- The pointwise sum of two maps `J`-holomorphic on a set is `J`-holomorphic on it. -/
lemma IsConstJHolomorphicOn.add {f g : V → W} {s : Set V}
    (hf : IsConstJHolomorphicOn J J' f s) (hg : IsConstJHolomorphicOn J J' g s) :
    IsConstJHolomorphicOn J J' (f + g) s :=
  fun x hx => (hf x hx).add (hg x hx)

/-- The pointwise negation of a map `J`-holomorphic on a set is `J`-holomorphic on it. -/
lemma IsConstJHolomorphicOn.neg {f : V → W} {s : Set V} (hf : IsConstJHolomorphicOn J J' f s) :
    IsConstJHolomorphicOn J J' (-f) s :=
  fun x hx => (hf x hx).neg

/-- The pointwise difference of two maps `J`-holomorphic on a set is `J`-holomorphic on it. -/
lemma IsConstJHolomorphicOn.sub {f g : V → W} {s : Set V}
    (hf : IsConstJHolomorphicOn J J' f s) (hg : IsConstJHolomorphicOn J J' g s) :
    IsConstJHolomorphicOn J J' (f - g) s :=
  fun x hx => (hf x hx).sub (hg x hx)

/-- A real scalar multiple of a map `J`-holomorphic on a set is `J`-holomorphic on it. -/
lemma IsConstJHolomorphicOn.const_smul {f : V → W} {s : Set V} (hf : IsConstJHolomorphicOn J J' f s)
    (c : ℝ) : IsConstJHolomorphicOn J J' (c • f) s :=
  fun x hx => (hf x hx).const_smul c

/-- The pointwise sum of two globally `J`-holomorphic maps is `J`-holomorphic. -/
lemma IsConstJHolomorphic.add {f g : V → W}
    (hf : IsConstJHolomorphic J J' f) (hg : IsConstJHolomorphic J J' g) :
    IsConstJHolomorphic J J' (f + g) :=
  fun x => (hf x).add (hg x)

/-- The pointwise negation of a globally `J`-holomorphic map is `J`-holomorphic. -/
lemma IsConstJHolomorphic.neg {f : V → W} (hf : IsConstJHolomorphic J J' f) :
    IsConstJHolomorphic J J' (-f) :=
  fun x => (hf x).neg

/-- The pointwise difference of two globally `J`-holomorphic maps is `J`-holomorphic. -/
lemma IsConstJHolomorphic.sub {f g : V → W}
    (hf : IsConstJHolomorphic J J' f) (hg : IsConstJHolomorphic J J' g) :
    IsConstJHolomorphic J J' (f - g) :=
  fun x => (hf x).sub (hg x)

/-- A real scalar multiple of a globally `J`-holomorphic map is `J`-holomorphic. -/
lemma IsConstJHolomorphic.const_smul {f : V → W} (hf : IsConstJHolomorphic J J' f) (c : ℝ) :
    IsConstJHolomorphic J J' (c • f) :=
  fun x => (hf x).const_smul c

end LinearStructure

end TauCeti

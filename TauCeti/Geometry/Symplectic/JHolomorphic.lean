/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# `J`-holomorphic maps between real normed spaces

This file adds the first map-level definition for the analytic Heegaard Floer roadmap:
a map between real normed spaces with fixed pointwise almost complex structures is
`J`-holomorphic at a point when it has a Frechet derivative there and that derivative
commutes with the two almost complex structures.

The definitions are deliberately linear and local. Later manifold and bundle versions should
use this as the model on coordinate charts and tangent fibers, rather than introducing a
different Cauchy--Riemann convention.

## Main declarations

* `IsJHolomorphicAt`: a map has a complex-linear Frechet derivative at a point.
* `IsJHolomorphicWithinAt`: a map has a complex-linear Frechet derivative within a set.
* `IsJHolomorphicOn` and `IsJHolomorphic`: setwise and global versions.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: the Cauchy--Riemann equation is `df ∘ J = J' ∘ df`.
-/

namespace TauCeti

variable {V W X : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

section JHolomorphic

/-- A map is `J`-holomorphic at a point if its Frechet derivative exists there and
intertwines the source and target almost complex structures. -/
def IsJHolomorphicAt (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) (x : V) : Prop :=
  ∃ f' : V →L[ℝ] W, HasFDerivAt f f' x ∧ IsComplexLinearMap J J' f'.toLinearMap

/-- A map is `J`-holomorphic within a set at a point if its Frechet derivative within the
set exists there and intertwines the source and target almost complex structures. -/
def IsJHolomorphicWithinAt (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) (s : Set V) (x : V) : Prop :=
  ∃ f' : V →L[ℝ] W, HasFDerivWithinAt f f' s x ∧ IsComplexLinearMap J J' f'.toLinearMap

/-- A map is `J`-holomorphic on a set if it is `J`-holomorphic within that set at every
point of the set. -/
def IsJHolomorphicOn (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) (s : Set V) : Prop :=
  ∀ x ∈ s, IsJHolomorphicWithinAt J J' f s x

/-- A globally `J`-holomorphic map is `J`-holomorphic at every point. -/
def IsJHolomorphic (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) : Prop :=
  ∀ x, IsJHolomorphicAt J J' f x

/-- Restate pointwise `J`-holomorphicity as existence of a complex-linear Frechet
derivative. -/
lemma isJHolomorphicAt_iff (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) (x : V) :
    IsJHolomorphicAt J J' f x ↔
      ∃ f' : V →L[ℝ] W, HasFDerivAt f f' x ∧ IsComplexLinearMap J J' f'.toLinearMap :=
  Iff.rfl

/-- Restate within-set `J`-holomorphicity as existence of a complex-linear Frechet
derivative within the set. -/
lemma isJHolomorphicWithinAt_iff (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (f : V → W) (s : Set V) (x : V) :
    IsJHolomorphicWithinAt J J' f s x ↔
      ∃ f' : V →L[ℝ] W,
        HasFDerivWithinAt f f' s x ∧ IsComplexLinearMap J J' f'.toLinearMap :=
  Iff.rfl

/-- Restate setwise `J`-holomorphicity as the within-set derivative condition at each
point of the set. -/
lemma isJHolomorphicOn_iff (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) (s : Set V) :
    IsJHolomorphicOn J J' f s ↔
      ∀ x ∈ s, ∃ f' : V →L[ℝ] W,
        HasFDerivWithinAt f f' s x ∧ IsComplexLinearMap J J' f'.toLinearMap :=
  Iff.rfl

/-- Restate global `J`-holomorphicity as the pointwise derivative condition at every point. -/
lemma isJHolomorphic_iff (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) :
    IsJHolomorphic J J' f ↔
      ∀ x, ∃ f' : V →L[ℝ] W, HasFDerivAt f f' x ∧
        IsComplexLinearMap J J' f'.toLinearMap :=
  Iff.rfl

/-- On the whole space, setwise `J`-holomorphicity is the same as global
`J`-holomorphicity. -/
@[simp]
lemma isJHolomorphicOn_univ (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) :
    IsJHolomorphicOn J J' f Set.univ ↔ IsJHolomorphic J J' f := by
  simp [IsJHolomorphicOn, IsJHolomorphicWithinAt, IsJHolomorphic, IsJHolomorphicAt,
    hasFDerivWithinAt_univ]

/-- The continuous-linear derivative witnessing `J`-holomorphicity at a point. -/
lemma IsJHolomorphicAt.hasFDerivAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsJHolomorphicAt J J' f x) :
    HasFDerivAt f hf.choose x :=
  hf.choose_spec.1

/-- The chosen derivative at a `J`-holomorphic point is complex-linear. -/
lemma IsJHolomorphicAt.derivative_isComplexLinear {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsJHolomorphicAt J J' f x) :
    IsComplexLinearMap J J' hf.choose.toLinearMap :=
  hf.choose_spec.2

/-- A `J`-holomorphic map is differentiable at the point. -/
lemma IsJHolomorphicAt.differentiableAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsJHolomorphicAt J J' f x) :
    DifferentiableAt ℝ f x :=
  hf.hasFDerivAt.differentiableAt

/-- The Frechet derivative of a `J`-holomorphic map is complex-linear. -/
lemma IsJHolomorphicAt.fderiv_isComplexLinear {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsJHolomorphicAt J J' f x) :
    IsComplexLinearMap J J' (fderiv ℝ f x).toLinearMap := by
  simpa [hf.hasFDerivAt.fderiv] using hf.derivative_isComplexLinear

/-- The Frechet derivative of a `J`-holomorphic map commutes with the almost complex
structures pointwise. -/
lemma IsJHolomorphicAt.fderiv_apply_commute {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x v : V}
    (hf : IsJHolomorphicAt J J' f x) :
    fderiv ℝ f x (J v) = J' (fderiv ℝ f x v) :=
  (isComplexLinearMap_iff_apply J J' (fderiv ℝ f x).toLinearMap).mp
    hf.fderiv_isComplexLinear v

/-- A pointwise `J`-holomorphic map is `J`-holomorphic within any set. -/
lemma IsJHolomorphicAt.isJHolomorphicWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsJHolomorphicAt J J' f x) :
    IsJHolomorphicWithinAt J J' f s x :=
  ⟨hf.choose, hf.hasFDerivAt.hasFDerivWithinAt, hf.derivative_isComplexLinear⟩

/-- The continuous-linear derivative witnessing `J`-holomorphicity within a set. -/
lemma IsJHolomorphicWithinAt.hasFDerivWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsJHolomorphicWithinAt J J' f s x) :
    HasFDerivWithinAt f hf.choose s x :=
  hf.choose_spec.1

/-- The chosen within-set derivative is complex-linear. -/
lemma IsJHolomorphicWithinAt.derivative_isComplexLinear {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsJHolomorphicWithinAt J J' f s x) :
    IsComplexLinearMap J J' hf.choose.toLinearMap :=
  hf.choose_spec.2

/-- A map that is `J`-holomorphic within a set is differentiable within that set. -/
lemma IsJHolomorphicWithinAt.differentiableWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsJHolomorphicWithinAt J J' f s x) :
    DifferentiableWithinAt ℝ f s x :=
  hf.hasFDerivWithinAt.differentiableWithinAt

/-- The within-set Frechet derivative is complex-linear when the set has unique derivatives. -/
lemma IsJHolomorphicWithinAt.fderivWithin_isComplexLinear {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsJHolomorphicWithinAt J J' f s x) (hs : UniqueDiffWithinAt ℝ s x) :
    IsComplexLinearMap J J' (fderivWithin ℝ f s x).toLinearMap := by
  simpa [hf.hasFDerivWithinAt.fderivWithin hs] using hf.derivative_isComplexLinear

/-- The within-set Frechet derivative commutes with the almost complex structures pointwise. -/
lemma IsJHolomorphicWithinAt.fderivWithin_apply_commute {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x v : V}
    (hf : IsJHolomorphicWithinAt J J' f s x) (hs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ f s x (J v) = J' (fderivWithin ℝ f s x v) :=
  (isComplexLinearMap_iff_apply J J' (fderivWithin ℝ f s x).toLinearMap).mp
    (hf.fderivWithin_isComplexLinear hs) v

/-- A within-set `J`-holomorphic map is pointwise `J`-holomorphic when the set is a
neighborhood of the point. -/
lemma IsJHolomorphicWithinAt.isJHolomorphicAt_of_mem_nhds {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsJHolomorphicWithinAt J J' f s x) (hs : s ∈ nhds x) :
    IsJHolomorphicAt J J' f x :=
  ⟨hf.choose, (hasFDerivWithinAt_of_mem_nhds hs).mp hf.hasFDerivWithinAt,
    hf.derivative_isComplexLinear⟩

/-- A constant map is `J`-holomorphic at every point. -/
@[simp]
lemma isJHolomorphicAt_const (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (c : W) (x : V) : IsJHolomorphicAt J J' (fun _ : V => c) x :=
  ⟨0, hasFDerivAt_const c x, by simp⟩

/-- The identity map is `J`-holomorphic for any fixed almost complex structure `J`. -/
@[simp]
lemma isJHolomorphicAt_id (J : AlmostComplexStructure V) (x : V) :
    IsJHolomorphicAt J J id x :=
  ⟨ContinuousLinearMap.id ℝ V, hasFDerivAt_id x, by simp⟩

/-- Chain rule for pointwise `J`-holomorphic maps. -/
lemma IsJHolomorphicAt.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X}
    {f : V → W} {g : W → X} {x : V}
    (hg : IsJHolomorphicAt J' J'' g (f x)) (hf : IsJHolomorphicAt J J' f x) :
    IsJHolomorphicAt J J'' (g ∘ f) x := by
  refine ⟨hg.choose.comp hf.choose, hg.hasFDerivAt.comp x hf.hasFDerivAt, ?_⟩
  exact IsComplexLinearMap.comp hg.derivative_isComplexLinear hf.derivative_isComplexLinear

/-- A constant map is `J`-holomorphic within every set at every point. -/
@[simp]
lemma isJHolomorphicWithinAt_const (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (c : W) (s : Set V) (x : V) :
    IsJHolomorphicWithinAt J J' (fun _ : V => c) s x :=
  (isJHolomorphicAt_const J J' c x).isJHolomorphicWithinAt

/-- The identity map is `J`-holomorphic within every set at every point. -/
@[simp]
lemma isJHolomorphicWithinAt_id (J : AlmostComplexStructure V) (s : Set V) (x : V) :
    IsJHolomorphicWithinAt J J id s x :=
  (isJHolomorphicAt_id J x).isJHolomorphicWithinAt

/-- A constant map is `J`-holomorphic on every set. -/
@[simp]
lemma isJHolomorphicOn_const (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (c : W) (s : Set V) : IsJHolomorphicOn J J' (fun _ : V => c) s :=
  fun x _ => isJHolomorphicWithinAt_const J J' c s x

/-- The identity map is `J`-holomorphic on every set. -/
@[simp]
lemma isJHolomorphicOn_id (J : AlmostComplexStructure V) (s : Set V) :
    IsJHolomorphicOn J J id s :=
  fun x _ => isJHolomorphicWithinAt_id J s x

/-- Chain rule for within-set `J`-holomorphic maps. -/
lemma IsJHolomorphicWithinAt.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X}
    {f : V → W} {g : W → X} {s : Set V} {t : Set W} {x : V}
    (hg : IsJHolomorphicWithinAt J' J'' g t (f x))
    (hf : IsJHolomorphicWithinAt J J' f s x) (hst : Set.MapsTo f s t) :
    IsJHolomorphicWithinAt J J'' (g ∘ f) s x := by
  refine ⟨hg.choose.comp hf.choose, hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt hst, ?_⟩
  exact IsComplexLinearMap.comp hg.derivative_isComplexLinear hf.derivative_isComplexLinear

/-- Chain rule for setwise `J`-holomorphic maps. -/
lemma IsJHolomorphicOn.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X}
    {f : V → W} {g : W → X} {s : Set V} {t : Set W}
    (hg : IsJHolomorphicOn J' J'' g t) (hf : IsJHolomorphicOn J J' f s)
    (hst : Set.MapsTo f s t) :
    IsJHolomorphicOn J J'' (g ∘ f) s :=
  fun x hx => (hg (f x) (hst hx)).comp (hf x hx) hst

/-- Restrict the domain set of a setwise `J`-holomorphic map. -/
lemma IsJHolomorphicOn.mono {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
    {f : V → W} {s t : Set V} (hf : IsJHolomorphicOn J J' f t) (hst : s ⊆ t) :
    IsJHolomorphicOn J J' f s :=
  fun x hx =>
    let hfx := hf x (hst hx)
    ⟨hfx.choose, hfx.hasFDerivWithinAt.mono hst, hfx.derivative_isComplexLinear⟩

/-- A globally `J`-holomorphic map is `J`-holomorphic on every set. -/
lemma IsJHolomorphic.isJHolomorphicOn {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W}
    (hf : IsJHolomorphic J J' f) (s : Set V) :
    IsJHolomorphicOn J J' f s :=
  fun x _ => (hf x).isJHolomorphicWithinAt

/-- A constant map is globally `J`-holomorphic. -/
@[simp]
lemma isJHolomorphic_const (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (c : W) : IsJHolomorphic J J' (fun _ : V => c) :=
  fun x => isJHolomorphicAt_const J J' c x

/-- The identity map is globally `J`-holomorphic. -/
@[simp]
lemma isJHolomorphic_id (J : AlmostComplexStructure V) : IsJHolomorphic J J id :=
  fun x => isJHolomorphicAt_id J x

/-- Chain rule for global `J`-holomorphic maps. -/
lemma IsJHolomorphic.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X}
    {f : V → W} {g : W → X}
    (hg : IsJHolomorphic J' J'' g) (hf : IsJHolomorphic J J' f) :
    IsJHolomorphic J J'' (g ∘ f) :=
  fun x => (hg (f x)).comp (hf x)

end JHolomorphic

end TauCeti

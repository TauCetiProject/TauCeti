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

* `IsComplexLinearMap`: a continuous real-linear map intertwines two almost complex
  structures.
* `IsJHolomorphicAt`: a map has a complex-linear Frechet derivative at a point.
* `IsJHolomorphicOn` and `IsJHolomorphic`: setwise and global versions.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: the Cauchy--Riemann equation is `df ∘ J = J' ∘ df`.
-/

namespace TauCeti

variable {V W X : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A continuous real-linear map is complex-linear with respect to two fixed pointwise
almost complex structures if it intertwines them. -/
def IsComplexLinearMap (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (F : V →L[ℝ] W) : Prop :=
  F.toLinearMap.comp J.toLinearMap = J'.toLinearMap.comp F.toLinearMap

lemma isComplexLinear_iff_apply (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (F : V →L[ℝ] W) :
    IsComplexLinearMap J J' F ↔ ∀ v, F (J v) = J' (F v) :=
  LinearMap.ext_iff

/-- The zero map is complex-linear for any source and target almost complex structures. -/
lemma isComplexLinear_zero (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W) :
    IsComplexLinearMap J J' (0 : V →L[ℝ] W) := by
  rw [isComplexLinear_iff_apply]
  intro v
  simp

/-- The identity map is complex-linear with respect to the same almost complex structure. -/
lemma isComplexLinear_id (J : AlmostComplexStructure V) :
    IsComplexLinearMap J J (ContinuousLinearMap.id ℝ V) := by
  rw [isComplexLinear_iff_apply]
  intro v
  rfl

/-- Complex-linear continuous maps are closed under composition. -/
lemma IsComplexLinearMap.comp {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
    {J'' : AlmostComplexStructure X} {F : V →L[ℝ] W} {G : W →L[ℝ] X}
    (hG : IsComplexLinearMap J' J'' G) (hF : IsComplexLinearMap J J' F) :
    IsComplexLinearMap J J'' (G.comp F) := by
  rw [isComplexLinear_iff_apply] at hF hG ⊢
  intro v
  calc
    G (F (J v)) = G (J' (F v)) := by rw [hF v]
    _ = J'' (G (F v)) := hG (F v)

section JHolomorphic

/-- A map is `J`-holomorphic at a point if its Frechet derivative exists there and
intertwines the source and target almost complex structures. -/
def IsJHolomorphicAt (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) (x : V) : Prop :=
  ∃ f' : V →L[ℝ] W, HasFDerivAt f f' x ∧ IsComplexLinearMap J J' f'

/-- A map is `J`-holomorphic on a set if it is `J`-holomorphic at every point of the set. -/
def IsJHolomorphicOn (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) (s : Set V) : Prop :=
  ∀ x ∈ s, IsJHolomorphicAt J J' f x

/-- A globally `J`-holomorphic map is `J`-holomorphic at every point. -/
def IsJHolomorphic (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) : Prop :=
  ∀ x, IsJHolomorphicAt J J' f x

lemma isJHolomorphicOn_univ (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) :
    IsJHolomorphicOn J J' f Set.univ ↔ IsJHolomorphic J J' f := by
  simp [IsJHolomorphicOn, IsJHolomorphic]

lemma IsJHolomorphicAt.hasFDerivAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsJHolomorphicAt J J' f x) :
    HasFDerivAt f hf.choose x :=
  hf.choose_spec.1

lemma IsJHolomorphicAt.derivative_isComplexLinear {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsJHolomorphicAt J J' f x) :
    IsComplexLinearMap J J' hf.choose :=
  hf.choose_spec.2

lemma IsJHolomorphicAt.differentiableAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsJHolomorphicAt J J' f x) :
    DifferentiableAt ℝ f x :=
  hf.hasFDerivAt.differentiableAt

lemma IsJHolomorphicAt.fderiv_isComplexLinear {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsJHolomorphicAt J J' f x) :
    IsComplexLinearMap J J' (fderiv ℝ f x) := by
  simpa [hf.hasFDerivAt.fderiv] using hf.derivative_isComplexLinear

lemma IsJHolomorphicAt.fderiv_apply_commute {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x v : V}
    (hf : IsJHolomorphicAt J J' f x) :
    fderiv ℝ f x (J v) = J' (fderiv ℝ f x v) :=
  (isComplexLinear_iff_apply J J' (fderiv ℝ f x)).mp hf.fderiv_isComplexLinear v

/-- A constant map is `J`-holomorphic at every point. -/
lemma isJHolomorphicAt_const (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (c : W) (x : V) : IsJHolomorphicAt J J' (fun _ : V => c) x :=
  ⟨0, hasFDerivAt_const c x, isComplexLinear_zero J J'⟩

/-- The identity map is `J`-holomorphic for any fixed almost complex structure `J`. -/
lemma isJHolomorphicAt_id (J : AlmostComplexStructure V) (x : V) :
    IsJHolomorphicAt J J id x :=
  ⟨ContinuousLinearMap.id ℝ V, hasFDerivAt_id x, isComplexLinear_id J⟩

lemma IsJHolomorphicAt.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X}
    {f : V → W} {g : W → X} {x : V}
    (hg : IsJHolomorphicAt J' J'' g (f x)) (hf : IsJHolomorphicAt J J' f x) :
    IsJHolomorphicAt J J'' (g ∘ f) x := by
  refine ⟨hg.choose.comp hf.choose, hg.hasFDerivAt.comp x hf.hasFDerivAt, ?_⟩
  exact IsComplexLinearMap.comp hg.derivative_isComplexLinear hf.derivative_isComplexLinear

lemma IsJHolomorphicOn.mono {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
    {f : V → W} {s t : Set V} (hf : IsJHolomorphicOn J J' f t) (hst : s ⊆ t) :
    IsJHolomorphicOn J J' f s :=
  fun x hx => hf x (hst hx)

lemma IsJHolomorphic.isJHolomorphicOn {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W}
    (hf : IsJHolomorphic J J' f) (s : Set V) :
    IsJHolomorphicOn J J' f s :=
  fun x _ => hf x

lemma isJHolomorphic_const (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (c : W) : IsJHolomorphic J J' (fun _ : V => c) :=
  fun x => isJHolomorphicAt_const J J' c x

lemma isJHolomorphic_id (J : AlmostComplexStructure V) : IsJHolomorphic J J id :=
  fun x => isJHolomorphicAt_id J x

lemma IsJHolomorphic.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X}
    {f : V → W} {g : W → X}
    (hg : IsJHolomorphic J' J'' g) (hf : IsJHolomorphic J J' f) :
    IsJHolomorphic J J'' (g ∘ f) :=
  fun x => (hg (f x)).comp (hf x)

end JHolomorphic

end TauCeti

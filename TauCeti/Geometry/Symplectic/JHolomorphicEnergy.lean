/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.JHolomorphic
public import TauCeti.Geometry.Symplectic.Prod

/-!
# Directional energy for `J`-holomorphic maps

This file adds the pointwise energy-density ingredient for the analytic Heegaard Floer
roadmap. Given a compatible pair `(ω, J)` on the target, the directional energy of a real-linear
map `F` in a tangent direction `v` is
```
ω (F v) (J (F v)).
```
Equivalently, it is the diagonal value of the compatible metric `g = ω(·, J ·)` on the image
of `v`. This is deliberately infinitesimal: no integration, domains, Sobolev spaces, or manifold
bundles are introduced here. Later curve-energy definitions can integrate this pointwise density
once the required measure-theoretic and manifold infrastructure exists.

## Main declarations

* `TauCeti.SymplecticForm.directionalEnergy`: the target-compatible metric energy of a
  linear map in one source direction.
* `TauCeti.SymplecticForm.Compatible.directionalEnergy_nonneg` and
  `directionalEnergy_eq_zero_iff`: positivity and zero-detection for compatible targets.
* `TauCeti.SymplecticForm.directionalEnergy_apply_sourceJ_of_isComplexLinearMap`: a
  complex-linear map has the same directional energy in `v` and `J v` source directions.
* `TauCeti.jHolomorphicDirectionalEnergyAt`: the same density for the Frechet derivative of a
  map at a point.
* `TauCeti.IsJHolomorphicAt.directionalEnergy_apply_sourceJ`: the corresponding statement for
  a `J`-holomorphic map.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: compatible triples use the metric `g(v,w) = ω(v,Jw)`, and a complex-linear
derivative is isometric on the two real directions paired by the source almost complex
structure.
-/

public section

namespace TauCeti

variable {E V W X : Type*}

namespace SymplecticForm

section Linear

variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]
variable {ω : SymplecticForm W} {J : AlmostComplexStructure W}

/-- The directional energy of a real-linear map into a target with almost complex structure.

For a compatible pair `(ω, J)` this is the diagonal of the associated metric
`g = ω(·, J ·)` evaluated on `F v`. -/
@[expose] def directionalEnergy (ω : SymplecticForm W) (J : AlmostComplexStructure W)
    (F : V →ₗ[ℝ] W) (v : V) : ℝ :=
  ω (F v) (J (F v))

@[simp]
lemma directionalEnergy_apply (ω : SymplecticForm W) (J : AlmostComplexStructure W)
    (F : V →ₗ[ℝ] W) (v : V) :
    ω.directionalEnergy J F v = ω (F v) (J (F v)) :=
  rfl

/-- Directional energy is the diagonal of the associated bilinear form. -/
lemma directionalEnergy_eq_associatedBilinForm (ω : SymplecticForm W)
    (J : AlmostComplexStructure W) (F : V →ₗ[ℝ] W) (v : V) :
    ω.directionalEnergy J F v = ω.associatedBilinForm J (F v) (F v) :=
  rfl

@[simp]
lemma directionalEnergy_zero_map (ω : SymplecticForm W) (J : AlmostComplexStructure W)
    (v : V) :
    ω.directionalEnergy J (0 : V →ₗ[ℝ] W) v = 0 := by
  simp [directionalEnergy]

@[simp]
lemma directionalEnergy_zero_vector (ω : SymplecticForm W) (J : AlmostComplexStructure W)
    (F : V →ₗ[ℝ] W) :
    ω.directionalEnergy J F (0 : V) = 0 := by
  simp [directionalEnergy]

/-- Directional energy is nonnegative for a compatible target. -/
lemma Compatible.directionalEnergy_nonneg (hω : ω.Compatible J) (F : V →ₗ[ℝ] W) (v : V) :
    0 ≤ ω.directionalEnergy J F v :=
  hω.symplecticForm_apply_apply_self_nonneg (F v)

/-- A nonzero image vector has positive directional energy for a compatible target. -/
lemma Compatible.directionalEnergy_pos (hω : ω.Compatible J) {F : V →ₗ[ℝ] W} {v : V}
    (hv : F v ≠ 0) :
    0 < ω.directionalEnergy J F v :=
  hω.associated_pos hv

/-- For a compatible target, directional energy vanishes exactly when the image direction is
zero. -/
lemma Compatible.directionalEnergy_eq_zero_iff (hω : ω.Compatible J) (F : V →ₗ[ℝ] W)
    (v : V) :
    ω.directionalEnergy J F v = 0 ↔ F v = 0 := by
  simpa [directionalEnergy_eq_associatedBilinForm] using hω.associatedBilinForm_self_eq_zero
    (v := F v)

/-- A direction in the kernel has zero directional energy. -/
lemma directionalEnergy_eq_zero_of_apply_eq_zero (ω : SymplecticForm W)
    (J : AlmostComplexStructure W) {F : V →ₗ[ℝ] W} {v : V} (hv : F v = 0) :
    ω.directionalEnergy J F v = 0 := by
  simp [directionalEnergy, hv]

/-- For a compatible target, zero directional energy means the direction lies in the kernel. -/
lemma Compatible.apply_eq_zero_of_directionalEnergy_eq_zero (hω : ω.Compatible J)
    {F : V →ₗ[ℝ] W} {v : V} (hv : ω.directionalEnergy J F v = 0) :
    F v = 0 :=
  (hω.directionalEnergy_eq_zero_iff F v).mp hv

variable {J₀ : AlmostComplexStructure V}

/-- A complex-linear map has equal target energy on the two source directions `v` and `J₀ v`.

This is the pointwise linear-algebra identity behind the usual energy density of a
`J`-holomorphic curve: the two real coordinate directions paired by the source complex
structure contribute equally to the compatible target metric. -/
lemma directionalEnergy_apply_sourceJ_of_isComplexLinearMap {F : V →ₗ[ℝ] W}
    (hF : IsComplexLinearMap J₀ J F) (hω : ω.Compatible J) (v : V) :
    ω.directionalEnergy J F (J₀ v) = ω.directionalEnergy J F v := by
  have happly := (isComplexLinearMap_iff_apply J₀ J F).mp hF v
  simpa [directionalEnergy, happly] using hω.associatedBilinForm_invariant (F v) (F v)

variable [AddCommGroup X] [Module ℝ X]
variable {ω₁ : SymplecticForm W} {ω₂ : SymplecticForm X}
variable {J₁ : AlmostComplexStructure W} {J₂ : AlmostComplexStructure X}

/-- Directional energy into a product compatible target is the sum of the directional energies
of the two components. -/
@[simp]
lemma prod_directionalEnergy (F : V →ₗ[ℝ] W) (G : V →ₗ[ℝ] X) (v : V) :
    (ω₁.prod ω₂).directionalEnergy (J₁.prod J₂) (F.prod G) v =
      ω₁.directionalEnergy J₁ F v + ω₂.directionalEnergy J₂ G v :=
  rfl

/-- Directional energy of a product map on a product source splits into the two component
energies. -/
@[simp]
lemma prodMap_directionalEnergy (F : V →ₗ[ℝ] W) (G : E →ₗ[ℝ] X) (p : V × E) :
    (ω₁.prod ω₂).directionalEnergy (J₁.prod J₂) (F.prodMap G) p =
      ω₁.directionalEnergy J₁ F p.1 + ω₂.directionalEnergy J₂ G p.2 :=
  rfl

end Linear

end SymplecticForm

section MapEnergy

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {ω : SymplecticForm W} {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
variable {f : V → W} {s : Set V} {x v : V}

/-- Directional energy of the Frechet derivative of a map at a point.

This is an infinitesimal energy density. It is not an integrated curve energy. -/
@[expose] noncomputable def jHolomorphicDirectionalEnergyAt (ω : SymplecticForm W)
    (J' : AlmostComplexStructure W) (f : V → W) (x v : V) : ℝ :=
  ω.directionalEnergy J' (fderiv ℝ f x).toLinearMap v

@[simp]
lemma jHolomorphicDirectionalEnergyAt_apply (ω : SymplecticForm W)
    (J' : AlmostComplexStructure W) (f : V → W) (x v : V) :
    jHolomorphicDirectionalEnergyAt ω J' f x v =
      ω ((fderiv ℝ f x) v) (J' ((fderiv ℝ f x) v)) :=
  rfl

/-- Directional energy of the within-set Frechet derivative of a map at a point. -/
@[expose] noncomputable def jHolomorphicDirectionalEnergyWithinAt (ω : SymplecticForm W)
    (J' : AlmostComplexStructure W) (f : V → W) (s : Set V) (x v : V) : ℝ :=
  ω.directionalEnergy J' (fderivWithin ℝ f s x).toLinearMap v

@[simp]
lemma jHolomorphicDirectionalEnergyWithinAt_apply (ω : SymplecticForm W)
    (J' : AlmostComplexStructure W) (f : V → W) (s : Set V) (x v : V) :
    jHolomorphicDirectionalEnergyWithinAt ω J' f s x v =
      ω ((fderivWithin ℝ f s x) v) (J' ((fderivWithin ℝ f s x) v)) :=
  rfl

namespace IsJHolomorphicAt

/-- A `J`-holomorphic map has equal target energy on the two source directions `v` and `J v`. -/
lemma directionalEnergy_apply_sourceJ (hf : IsJHolomorphicAt J J' f x)
    (hω : ω.Compatible J') (v : V) :
    jHolomorphicDirectionalEnergyAt ω J' f x (J v) =
      jHolomorphicDirectionalEnergyAt ω J' f x v :=
  SymplecticForm.directionalEnergy_apply_sourceJ_of_isComplexLinearMap
    hf.fderiv_isComplexLinear hω v

/-- The Frechet derivative of a `J`-holomorphic map has nonnegative directional energy in a
compatible target. -/
lemma directionalEnergy_nonneg (_hf : IsJHolomorphicAt J J' f x) (hω : ω.Compatible J')
    (v : V) :
    0 ≤ jHolomorphicDirectionalEnergyAt ω J' f x v :=
  hω.directionalEnergy_nonneg (fderiv ℝ f x).toLinearMap v

end IsJHolomorphicAt

namespace IsJHolomorphicWithinAt

/-- A within-set `J`-holomorphic map has equal target energy on `v` and `J v` whenever the
within-set derivative is unique. -/
lemma directionalEnergyWithin_apply_sourceJ (hf : IsJHolomorphicWithinAt J J' f s x)
    (hs : UniqueDiffWithinAt ℝ s x) (hω : ω.Compatible J') (v : V) :
    jHolomorphicDirectionalEnergyWithinAt ω J' f s x (J v) =
      jHolomorphicDirectionalEnergyWithinAt ω J' f s x v :=
  SymplecticForm.directionalEnergy_apply_sourceJ_of_isComplexLinearMap
    (hf.fderivWithin_isComplexLinear hs) hω v

/-- The within-set Frechet derivative of a `J`-holomorphic map has nonnegative directional energy
in a compatible target. -/
lemma directionalEnergyWithin_nonneg (_hf : IsJHolomorphicWithinAt J J' f s x)
    (hω : ω.Compatible J') (v : V) :
    0 ≤ jHolomorphicDirectionalEnergyWithinAt ω J' f s x v :=
  hω.directionalEnergy_nonneg (fderivWithin ℝ f s x).toLinearMap v

end IsJHolomorphicWithinAt

end MapEnergy

end TauCeti

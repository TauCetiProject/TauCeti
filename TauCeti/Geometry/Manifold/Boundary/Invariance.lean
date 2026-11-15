/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain

/-!
# Half-space charts send frontier points to the boundary hyperplane

Let `A` be a subset of a finite-dimensional real normed space `E`, and let `φ` be a homeomorphism
from an open subset of `A` onto an open subset of the half-space model `EuclideanHalfSpace m × V`,
where `m + dim V = dim E`. A point `y` of the source of `φ` which is not an interior point of `A`
in `E` is sent to the boundary hyperplane: the zeroth coordinate of `φ y` vanishes
(`OpenPartialHomeomorph.coe_fst_apply_zero_eq_zero_of_notMem_interior`).

This is the topological invariance of the boundary of the half-space, in the form needed when an
arbitrary chart of a subset with nonempty frontier, such as a closed ball, takes values in a
half-space model. Otherwise `φ.symm`, restricted to the open set of points of the target with
positive zeroth coordinate, would be a continuous injection of an open subset of
`ℝᵐ × V` into `E` whose image contains `y` and lies in `A`. By invariance of domain
(`IsOpen.image_of_continuousOn_of_injOn`) that image is open in `E`, so `y` would be an interior
point of `A`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Theorem 2B.3 (invariance
  of domain).
-/

public section

open Set Module

namespace OpenPartialHomeomorph

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {m : ℕ} [NeZero m]
  {A : Set E}

/-- **Invariance of the boundary of the half-space.** Let `φ` be a chart of a subset `A` of `E`
with values in the half-space model `EuclideanHalfSpace m × V`, where `m + dim V = dim E`. Then
`φ` sends every point of its source that is not an interior point of `A` to the boundary
hyperplane, where the zeroth coordinate vanishes. -/
theorem coe_fst_apply_zero_eq_zero_of_notMem_interior
    (φ : OpenPartialHomeomorph A (EuclideanHalfSpace m × V))
    (hdim : finrank ℝ E = m + finrank ℝ V) {y : A} (hy : y ∈ φ.source)
    (hyA : (y : E) ∉ interior A) : (φ y).1.1 0 = 0 := by
  by_contra hne
  have hpos : 0 < (φ y).1.1 0 := lt_of_le_of_ne (φ y).1.2 (Ne.symm hne)
  -- Read the target of `φ` in `ℝᵐ × V` through the model `𝓡∂ m` and its continuous inverse.
  set I := modelWithCornersEuclideanHalfSpace m
  let j : EuclideanSpace ℝ (Fin m) × V → EuclideanHalfSpace m × V := Prod.map I.symm id
  have hj : Continuous j := I.continuous_symm.prodMap continuous_id
  set U : Set (EuclideanSpace ℝ (Fin m) × V) := j ⁻¹' φ.target ∩ {p | 0 < p.1 0}
  have hU : IsOpen U :=
    (hj.isOpen_preimage _ φ.open_target).inter
      (isOpen_lt continuous_const ((PiLp.continuous_apply 2 _ 0).comp continuous_fst))
  let f : EuclideanSpace ℝ (Fin m) × V → E := fun p => (φ.symm (j p) : E)
  have hf : ContinuousOn f U :=
    continuous_subtype_val.comp_continuousOn
      (φ.continuousOn_symm.comp hj.continuousOn fun _ hp => hp.1)
  -- On points of positive zeroth coordinate, `j` is injective, so `f` is injective on `U`.
  have hjI {p : EuclideanSpace ℝ (Fin m) × V} (hp : 0 < p.1 0) : I (j p).1 = p.1 :=
    I.right_inv (by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact hp.le)
  have hinj : InjOn f U := by
    intro p hp q hq hpq
    have hjpq : j p = j q := φ.symm.injOn (φ.symm_source ▸ hp.1) (φ.symm_source ▸ hq.1)
      (Subtype.ext hpq)
    have h2 : (j p).2 = (j q).2 := congrArg Prod.snd hjpq
    exact Prod.ext (by rw [← hjI hp.2, ← hjI hq.2, hjpq]) h2
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin m) × V) = finrank ℝ E := by
    rw [hdim, finrank_prod, finrank_euclideanSpace_fin]
  have hopen : IsOpen (f '' U) := hU.image_of_continuousOn_of_injOn hf hinj hfin
  -- The point `y` is the image of the reading of `φ y`, and the image of `f` lies in `A`.
  set p₀ : EuclideanSpace ℝ (Fin m) × V := (I (φ y).1, (φ y).2)
  have hjp₀ : j p₀ = φ y := Prod.ext (I.left_inv _) rfl
  have hp₀ : p₀ ∈ U := ⟨by rw [mem_preimage, hjp₀]; exact φ.map_source hy, hpos⟩
  have hfp₀ : f p₀ = y := by
    simp only [f, hjp₀, φ.left_inv hy]
  refine hyA (interior_maximal ?_ hopen ⟨p₀, hp₀, hfp₀⟩)
  rintro _ ⟨p, -, rfl⟩
  exact (φ.symm (j p)).2

end OpenPartialHomeomorph

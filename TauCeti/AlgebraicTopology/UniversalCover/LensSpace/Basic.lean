/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Topology.Covering.Quotient
public import TauCeti.Geometry.Sphere.LinearIsometry

/-!
# Lens spaces

Let `m` be a positive integer and let `ℓ₀, …, ℓₖ` be residues modulo `m` that are units. The cyclic
group `ℤ/m` acts on the unit sphere `S²ᵏ⁺¹ ⊆ ℂᵏ⁺¹` with a generator rotating the `i`-th
coordinate by the angle `2πℓᵢ/m`:

  `(z₀, …, zₖ) ↦ (e^{2πiℓ₀/m} z₀, …, e^{2πiℓₖ/m} zₖ)`.

The action is free because each `ℓᵢ` is a unit modulo `m`, and its orbit space is the **lens
space** `L(m; ℓ₀, …, ℓₖ)`. The three-dimensional lens space `L(p, q)` is
`TauCeti.LensSpace p ![1, q]`.

The rotations are linear isometries of `ℂᵏ⁺¹` viewed as a real inner product space, so the
acting group is realised as a subgroup `TauCeti.lensGroup m ℓ` of the linear isometry group,
which acts on the unit sphere through `LinearIsometryEquiv.instMulActionUnitSphere`. It is
the image of the homomorphism `TauCeti.lensRotation m ℓ` out of `ℤ/m`, written
multiplicatively, which is injective when there is at least one coordinate, as there is for
`ℂᵏ⁺¹`. A finite group acts properly discontinuously, so the projection from the sphere
is a quotient covering map. This file develops the topology of the quotient; its manifold
structure is in `TauCeti.Geometry.Manifold.Instances.LensSpace`, and its fundamental group in
`TauCeti.AlgebraicTopology.UniversalCover.LensSpace.FundamentalGroup`.

Requiring `ℓᵢ` to be a unit of `ZMod m` builds the coprimality condition into the type, and it
ensures that the prescribed action of `ℤ/m` is faithful and free. For `m = 1` the acting group is
trivial and the lens space is a copy of the sphere.

## Main definitions

* `TauCeti.lensRotation`: the representation of `ℤ/m` on `ℂᵏ` by the weighted coordinate
  rotations.
* `TauCeti.lensGroup`: its image, a finite group of linear isometries acting freely on the unit
  sphere.
* `TauCeti.LensSpace`: the lens space `L(m; ℓ₀, …, ℓₖ)`, the orbit space of the unit sphere of
  `ℂᵏ⁺¹`.
* `TauCeti.LensSpace.mk`: the projection from the sphere.
* `TauCeti.LensSpace.inductionOn`, `TauCeti.LensSpace.lift`, and `TauCeti.LensSpace.lift_unique`:
  elimination principles for the quotient.

## Main results

* `TauCeti.lensRotation_injective`: the representation is faithful when there is at least one
  coordinate (`[NeZero k]`), so `TauCeti.lensGroupEquiv` identifies the lens group with `ℤ/m`.
* `TauCeti.lensGroup_isCancelSMul`: the lens group acts freely on the unit sphere.
* `TauCeti.LensSpace.mk_eq_mk_iff`: two unit vectors have the same image exactly when a rotation
  carries one to the other; `TauCeti.LensSpace.mk_lensRotation_smul` is the invariance of the
  projection under a rotation.
* `TauCeti.LensSpace.isQuotientCoveringMap_mk`: the projection from the sphere is a quotient
  covering map with group the lens group.
* A lens space is compact, Hausdorff and path-connected.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Example 2.43 (lens spaces
  as quotients of odd-dimensional spheres).
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9, §9G, Example 1: surgery on
  the unknot with coefficient `b/a` gives the lens space `L(b, a)`; the three-dimensional lens
  spaces are thus the manifolds obtained by Dehn surgery on the unknot.
* The quotient API (`mk`, `mk_eq_mk_iff`, `isQuotientCoveringMap_mk`, and the compactness and
  path-connectedness instances) is adapted from the real projective space formalization in
  `TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic`.
-/

public section

open Metric Module

namespace TauCeti

noncomputable section

section Rotation

variable (m : ℕ) [NeZero m] {k : ℕ} (ℓ : Fin k → (ZMod m)ˣ)

/-- The weighted rotation representation of `ℤ/m` on `ℂᵏ`, as real linear isometries: the residue
`a` rotates the `i`-th coordinate by the angle `2π ℓᵢ a / m`. -/
def lensRotation :
    Multiplicative (ZMod m) →* (EuclideanSpace ℂ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin k)) where
  toFun a := LinearIsometryEquiv.piLpCongrRight 2 fun i =>
    rotation (ZMod.toCircle ((ℓ i : ZMod m) * a.toAdd))
  map_one' := by
    ext x i
    simp
  map_mul' a b := by
    ext x i
    simp [mul_add, AddChar.map_add_eq_mul]

/-- The `i`-th coordinate of a rotated vector is the `i`-th coordinate of the vector multiplied
by the root of unity `e^{2πi ℓᵢ a / m}`. -/
@[simp]
theorem lensRotation_apply (a : Multiplicative (ZMod m)) (x : EuclideanSpace ℂ (Fin k))
    (i : Fin k) :
    lensRotation m ℓ a x i = ZMod.toCircle ((ℓ i : ZMod m) * a.toAdd) * x i := by
  simp [lensRotation]

/-- A rotation fixes a nonzero coordinate only if it is the identity: the weight of the
coordinate is a unit modulo `m`, so the rotation angle `2π ℓᵢ a / m` is a multiple of `2π` only
for `a = 0`. -/
theorem lensRotation_apply_eq_self_iff (a : Multiplicative (ZMod m))
    {x : EuclideanSpace ℂ (Fin k)} {i : Fin k} (hi : x i ≠ 0) :
    lensRotation m ℓ a x i = x i ↔ a = 1 := by
  rw [lensRotation_apply, mul_eq_right₀ hi, Circle.coe_eq_one,
    ZMod.injective_toCircle.eq_iff' (AddChar.map_zero_eq_one _), Units.mul_right_eq_zero,
    toAdd_eq_zero]

/-- The weighted rotation representation of `ℤ/m` is faithful once there is a coordinate. -/
theorem lensRotation_injective [NeZero k] : Function.Injective (lensRotation m ℓ) := by
  refine (injective_iff_map_eq_one _).mpr fun a ha => ?_
  refine (lensRotation_apply_eq_self_iff m ℓ a (x := EuclideanSpace.single 0 1) (i := 0)
    (by simp)).mp ?_
  rw [ha, LinearIsometryEquiv.coe_one, id_eq]

/-- The **lens group**: the cyclic group of linear isometries of `ℂᵏ` generated by the rotation
`(zᵢ) ↦ (e^{2πiℓᵢ/m} zᵢ)`, the image of `TauCeti.lensRotation`. -/
def lensGroup : Subgroup (EuclideanSpace ℂ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin k)) :=
  (lensRotation m ℓ).range

/-- The elements of the lens group are the rotations by residues modulo `m`. -/
@[simp]
theorem mem_lensGroup_iff {g : EuclideanSpace ℂ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin k)} :
    g ∈ lensGroup m ℓ ↔ ∃ a, lensRotation m ℓ a = g :=
  MonoidHom.mem_range

/-- The lens group is the cyclic group `ℤ/m`. -/
def lensGroupEquiv [NeZero k] : Multiplicative (ZMod m) ≃* lensGroup m ℓ :=
  MonoidHom.ofInjective (lensRotation_injective m ℓ)

@[simp]
theorem coe_lensGroupEquiv_apply [NeZero k] (a : Multiplicative (ZMod m)) :
    (lensGroupEquiv m ℓ a : EuclideanSpace ℂ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin k)) =
      lensRotation m ℓ a :=
  (rfl)

/-- The lens group is finite, as the image of `ℤ/m`. -/
instance : Finite (lensGroup m ℓ) :=
  Set.finite_range (lensRotation m ℓ) |>.to_subtype

/-- The lens group acts on the unit sphere by isometries. -/
instance : IsIsometricSMul (lensGroup m ℓ) (sphere (0 : EuclideanSpace ℂ (Fin k)) 1) :=
  ⟨fun g => g.1.isometry_unitSphereEquiv⟩

/-- **The lens group acts freely on the unit sphere**: a nontrivial rotation moves every unit
vector, because each weight is a unit modulo `m` and a unit vector has a nonzero coordinate. -/
instance lensGroup_isCancelSMul :
    IsCancelSMul (lensGroup m ℓ) (sphere (0 : EuclideanSpace ℂ (Fin k)) 1) := by
  refine isCancelSMul_iff_eq_one_of_smul_eq.mpr fun ⟨_, a, rfl⟩ x hx => ?_
  obtain ⟨i, hi⟩ : ∃ i, (x : EuclideanSpace ℂ (Fin k)) i ≠ 0 := by
    by_contra! h
    have hx0 : (x : EuclideanSpace ℂ (Fin k)) = 0 := PiLp.ext h
    simpa [hx0] using x.2
  have h := congrArg
    (fun y : sphere (0 : EuclideanSpace ℂ (Fin k)) 1 => (y : EuclideanSpace ℂ (Fin k)) i) hx
  simp only [Subgroup.smul_def, LinearIsometryEquiv.coe_smul_unitSphere] at h
  obtain rfl := (lensRotation_apply_eq_self_iff m ℓ a hi).mp h
  exact Subtype.ext (map_one _)

end Rotation

/-- The **lens space** `L(m; ℓ₀, …, ℓₖ)`: the orbit space of the unit sphere `S²ᵏ⁺¹ ⊆ ℂᵏ⁺¹`
under the free action of `ℤ/m` whose generator rotates the `i`-th coordinate by `2πℓᵢ/m`. It is a
closed analytic manifold of dimension `2k + 1`
(`TauCeti.Geometry.Manifold.Instances.LensSpace`). The three-dimensional lens space `L(p, q)` is
`LensSpace p ![1, q]`. -/
@[expose] def LensSpace (m : ℕ) [NeZero m] {k : ℕ} (ℓ : Fin (k + 1) → (ZMod m)ˣ) : Type :=
  MulAction.orbitRel.Quotient (lensGroup m ℓ) (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1)

namespace LensSpace

variable (m : ℕ) [NeZero m] {k : ℕ} (ℓ : Fin (k + 1) → (ZMod m)ˣ)

/-- The quotient topology on a lens space. -/
instance instTopologicalSpace : TopologicalSpace (LensSpace m ℓ) :=
  inferInstanceAs (TopologicalSpace (MulAction.orbitRel.Quotient (lensGroup m ℓ)
    (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1)))

/-- A lens space is compact, as a quotient of the compact sphere. -/
instance instCompactSpace : CompactSpace (LensSpace m ℓ) :=
  inferInstanceAs (CompactSpace (Quotient (MulAction.orbitRel (lensGroup m ℓ)
    (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1))))

/-- A lens space is Hausdorff, as the quotient of a compact Hausdorff space by a finite group. -/
instance instT2Space : T2Space (LensSpace m ℓ) :=
  inferInstanceAs (T2Space (Quotient (MulAction.orbitRel (lensGroup m ℓ)
    (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1))))

/-- The projection from the unit sphere of `ℂᵏ⁺¹` to the lens space. -/
def mk : sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1 → LensSpace m ℓ :=
  Quotient.mk (MulAction.orbitRel (lensGroup m ℓ) (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1))

/-- The projection from the sphere is the quotient map of the orbit relation of the lens group. -/
theorem mk_def : mk m ℓ = Quotient.mk
    (MulAction.orbitRel (lensGroup m ℓ) (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1)) :=
  (rfl)

/-- Every point of a lens space is the image of a unit vector. -/
theorem mk_surjective : Function.Surjective (mk m ℓ) :=
  Quotient.mk_surjective

/-- To prove a property of every point of a lens space, it suffices to prove it on the image of
every unit vector. -/
@[elab_as_elim]
protected theorem inductionOn {motive : LensSpace m ℓ → Prop} (x : LensSpace m ℓ)
    (h : ∀ y : sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1, motive (mk m ℓ y)) :
    motive x :=
  Quotient.inductionOn' x h

/-- Two unit vectors have the same image in the lens space exactly when a rotation by a residue
modulo `m` carries one to the other. -/
@[simp]
theorem mk_eq_mk_iff (x y : sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1) :
    mk m ℓ x = mk m ℓ y ↔ ∃ a : Multiplicative (ZMod m), lensRotation m ℓ a y = x := by
  unfold mk LensSpace
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨_, a, rfl⟩, h⟩
    exact ⟨a, by simpa [Subgroup.smul_def] using congrArg Subtype.val h⟩
  · rintro ⟨a, h⟩
    exact ⟨⟨_, a, rfl⟩, Subtype.ext (by simpa [Subgroup.smul_def] using h)⟩

/-- Rotating a unit vector does not change its image in the lens space. -/
@[simp]
theorem mk_lensRotation_smul (a : Multiplicative (ZMod m))
    (x : sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1) :
    mk m ℓ (lensRotation m ℓ a • x) = mk m ℓ x :=
  Quotient.sound ⟨⟨_, a, rfl⟩, rfl⟩

/-- A function on the unit sphere that is invariant under the rotations descends to the lens
space. -/
protected def lift {α : Sort*} (f : sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1 → α)
    (h : ∀ (a : Multiplicative (ZMod m)) x, f (lensRotation m ℓ a • x) = f x) :
    LensSpace m ℓ → α :=
  Quotient.lift f fun _ y hxy => by
    obtain ⟨⟨_, a, rfl⟩, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hxy)
    exact h a y

/-- Lifting an invariant function and applying it to a representative recovers the original
function. -/
@[simp]
protected theorem lift_mk {α : Sort*} (f : sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1 → α)
    (h : ∀ (a : Multiplicative (ZMod m)) x, f (lensRotation m ℓ a • x) = f x)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1) :
    LensSpace.lift m ℓ f h (mk m ℓ x) = f x :=
  (rfl)

/-- A function out of a lens space agreeing with an invariant function on representatives is its
lift. -/
protected theorem lift_unique {α : Sort*} (f : sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1 → α)
    (h : ∀ (a : Multiplicative (ZMod m)) x, f (lensRotation m ℓ a • x) = f x)
    (g : LensSpace m ℓ → α) (hg : ∀ x, g (mk m ℓ x) = f x) :
    g = LensSpace.lift m ℓ f h := by
  funext x
  exact LensSpace.inductionOn m ℓ x fun y => (hg y).trans (LensSpace.lift_mk m ℓ f h y).symm

/-- **The projection from the sphere to a lens space is a quotient covering map**, with fibres the
orbits of the lens group. -/
theorem isQuotientCoveringMap_mk : IsQuotientCoveringMap (mk m ℓ) (lensGroup m ℓ) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- The projection from the sphere to a lens space is a covering map. -/
theorem isCoveringMap_mk : IsCoveringMap (mk m ℓ) :=
  (isQuotientCoveringMap_mk m ℓ).isCoveringMap

/-- The projection from the sphere to a lens space is continuous. -/
theorem continuous_mk : Continuous (mk m ℓ) :=
  (isCoveringMap_mk m ℓ).continuous

/-- A lens space is path-connected, as a quotient of the path-connected sphere. -/
instance instPathConnectedSpace : PathConnectedSpace (LensSpace m ℓ) := by
  have : PathConnectedSpace (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1) := by
    refine isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere ?_ 0 zero_le_one)
    rw [← finrank_eq_rank, finrank_real_of_complex, finrank_euclideanSpace_fin, Nat.one_lt_cast]
    omega
  exact inferInstanceAs (PathConnectedSpace (Quotient (MulAction.orbitRel (lensGroup m ℓ)
    (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1))))

end LensSpace

end

end TauCeti

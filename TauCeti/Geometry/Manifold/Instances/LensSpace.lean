/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Instances.Quotient

/-!
# Lens spaces

Let `m` be a positive integer and let `ℓ₀, …, ℓₖ` be residues modulo `m` that are units. The cyclic
group `ℤ/m` acts on the unit sphere `S²ᵏ⁺¹ ⊆ ℂᵏ⁺¹` with a generator rotating the `i`-th
coordinate by the angle `2πℓᵢ/m`:

  `(z₀, …, zₖ) ↦ (e^{2πiℓ₀/m} z₀, …, e^{2πiℓₖ/m} zₖ)`.

The action is free because each `ℓᵢ` is a unit modulo `m`, so the orbit space is a closed smooth
manifold of dimension `2k + 1`: the **lens space** `L(m; ℓ₀, …, ℓₖ)`. The three-dimensional lens
space `L(p, q)` is `TauCeti.LensSpace p ![1, q]`.

The rotations are linear isometries of `ℂᵏ⁺¹` viewed as a real inner product space, so the
acting group is realised as a subgroup `TauCeti.lensGroup m ℓ` of the linear isometry group,
which acts on the unit sphere through `LinearIsometryEquiv.instMulActionUnitSphere`. It is
the image of the injective homomorphism `TauCeti.lensRotation m ℓ` out of `ℤ/m`, written
multiplicatively. A finite group acts properly discontinuously, and the rotations are analytic on
the sphere, so the orbit space is an analytic manifold by `TauCeti.instIsManifoldQuotient`, and the
projection from the sphere is a quotient covering map and an analytic local diffeomorphism.

Requiring `ℓᵢ` to be a unit of `ZMod m` builds the coprimality condition into the type: a weight
not coprime to `m` would give an action that is not free, whose orbit space is not a manifold. For
`m = 1` the acting group is trivial and the lens space is a copy of the sphere.

As for Mathlib's spheres (`EuclideanSpace.instChartedSpaceSphere`), the manifold structure is
stated for any `n` with `Fact (finrank ℝ (EuclideanSpace ℂ (Fin (k + 1))) = n + 1)`, and the
instance `TauCeti.factFinrankEuclideanSpaceComplex` supplies `n = 2k + 1`. This lets instance
search find the structure for a concrete model such as `𝓡 3`, where it could not solve
`2 * k + 1 = 3` for `k`.

## Main definitions

* `TauCeti.lensRotation`: the representation of `ℤ/m` on `ℂᵏ` by the weighted coordinate
  rotations.
* `TauCeti.lensGroup`: its image, a finite group of linear isometries acting freely on the unit
  sphere.
* `TauCeti.LensSpace`: the lens space `L(m; ℓ₀, …, ℓₖ)`, the orbit space of the unit sphere of
  `ℂᵏ⁺¹`.
* `TauCeti.LensSpace.mk`: the projection from the sphere.

## Main results

* `TauCeti.lensRotation_injective`: the representation is faithful, so
  `TauCeti.lensGroupEquiv` identifies the lens group with `ℤ/m`.
* `TauCeti.lensGroup_isCancelSMul`: the lens group acts freely on the unit sphere.
* `TauCeti.LensSpace.instIsManifold`: the lens space is an analytic manifold modelled on
  `ℝ²ᵏ⁺¹`; it is also compact, Hausdorff and path-connected.
* `TauCeti.LensSpace.isQuotientCoveringMap_mk` and `TauCeti.LensSpace.isLocalDiffeomorph_mk`:
  the projection from the sphere is a quotient covering map with group the lens group, and an
  analytic local diffeomorphism.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Example 2.43 (lens spaces
  as quotients of odd-dimensional spheres).
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9, §9G, Example 1: surgery on
  the unknot with coefficient `b/a` gives the lens space `L(b, a)`; the three-dimensional lens
  spaces are thus the manifolds obtained by Dehn surgery on the unknot.
-/

public section

open Metric Module
open scoped Manifold ContDiff

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
theorem mem_lensGroup_iff {e : EuclideanSpace ℂ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin k)} :
    e ∈ lensGroup m ℓ ↔ ∃ a, lensRotation m ℓ a = e :=
  Iff.rfl

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

/-- The unit sphere of `ℂᵏ⁺¹` is a real manifold of dimension `2k + 1`. -/
instance factFinrankEuclideanSpaceComplex (k : ℕ) :
    Fact (finrank ℝ (EuclideanSpace ℂ (Fin (k + 1))) = 2 * k + 1 + 1) :=
  ⟨by rw [finrank_real_of_complex, finrank_euclideanSpace_fin]; ring⟩

section Smooth

variable (m : ℕ) [NeZero m] {k : ℕ} (ℓ : Fin (k + 1) → (ZMod m)ˣ) {n : ℕ}
  [Fact (finrank ℝ (EuclideanSpace ℂ (Fin (k + 1))) = n + 1)]

/-- The lens group acts on the unit sphere of `ℂᵏ⁺¹` by analytic diffeomorphisms. -/
instance : ContMDiffConstSMul (𝓡 n) ω (lensGroup m ℓ)
    (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1) :=
  IsScalarTower.contMDiffConstSMul
    (EuclideanSpace ℂ (Fin (k + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (k + 1)))

end Smooth

/-- The **lens space** `L(m; ℓ₀, …, ℓₖ)`: the orbit space of the unit sphere `S²ᵏ⁺¹ ⊆ ℂᵏ⁺¹`
under the free action of `ℤ/m` whose generator rotates the `i`-th coordinate by `2πℓᵢ/m`. It is a
closed analytic manifold of dimension `2k + 1`. The three-dimensional lens space `L(p, q)` is
`LensSpace p ![1, q]`. -/
def LensSpace (m : ℕ) [NeZero m] {k : ℕ} (ℓ : Fin (k + 1) → (ZMod m)ˣ) : Type :=
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

section Manifold

variable {n : ℕ} [Fact (finrank ℝ (EuclideanSpace ℂ (Fin (k + 1))) = n + 1)]

/-- The charts of a lens space, pushed forward from the sphere along the orbit projection. -/
instance instChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) (LensSpace m ℓ) :=
  inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin n))
    (MulAction.orbitRel.Quotient (lensGroup m ℓ) (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1)))

/-- **A lens space is an analytic manifold** of dimension `2k + 1`. -/
instance instIsManifold : IsManifold (𝓡 n) ω (LensSpace m ℓ) :=
  inferInstanceAs (IsManifold (𝓡 n) ω (MulAction.orbitRel.Quotient (lensGroup m ℓ)
    (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1)))

end Manifold

/-- The projection from the unit sphere of `ℂᵏ⁺¹` to the lens space. -/
def mk : sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1 → LensSpace m ℓ :=
  Quotient.mk (MulAction.orbitRel (lensGroup m ℓ) (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1))

/-- Every point of a lens space is the image of a unit vector. -/
theorem mk_surjective : Function.Surjective (mk m ℓ) :=
  Quotient.mk_surjective

/-- Two unit vectors have the same image in the lens space exactly when a rotation by a residue
modulo `m` carries one to the other. -/
theorem mk_eq_mk_iff (x y : sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1) :
    mk m ℓ x = mk m ℓ y ↔ ∃ a : Multiplicative (ZMod m), lensRotation m ℓ a y = x := by
  unfold mk LensSpace
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨_, a, rfl⟩, h⟩
    exact ⟨a, by simpa [Subgroup.smul_def] using congrArg Subtype.val h⟩
  · rintro ⟨a, h⟩
    exact ⟨⟨_, a, rfl⟩, Subtype.ext (by simpa [Subgroup.smul_def] using h)⟩

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

/-- The projection from the sphere to a lens space is an analytic local diffeomorphism. -/
theorem isLocalDiffeomorph_mk {n : ℕ} [Fact (finrank ℝ (EuclideanSpace ℂ (Fin (k + 1))) = n + 1)] :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ω (mk m ℓ) :=
  isLocalDiffeomorph_quotientMk

/-- A lens space is path-connected, as a quotient of the path-connected sphere. -/
instance instPathConnectedSpace : PathConnectedSpace (LensSpace m ℓ) := by
  have : PathConnectedSpace (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1) := by
    refine isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere ?_ 0 zero_le_one)
    rw [← finrank_eq_rank, (factFinrankEuclideanSpaceComplex k).out, Nat.one_lt_cast]
    omega
  exact inferInstanceAs (PathConnectedSpace (Quotient (MulAction.orbitRel (lensGroup m ℓ)
    (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1))))

end LensSpace

end

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
public import TauCeti.LinearAlgebra.IntegralLattice.Norm
import Mathlib.LinearAlgebra.RootSystem.OfBilinear
public import TauCeti.LinearAlgebra.Reflection

/-!
# Reflections in roots of integral lattices

A lattice vector of norm two defines a lattice isometry by
`sₓ(y) = y - B(x, y) • x`. Integrality of the pairing ensures that this reflection preserves
the integral carrier, and its involutivity makes carrier preservation an equality.
These isometries are the generators used to compare root Weyl groups with lattice
automorphism groups.

The construction works for indefinite and degenerate lattices as well as positive definite
ones. We give its ambient and integral action, involutivity, fixed-vector criterion, and
transport under lattice isometries. In particular, conjugation carries a root reflection
to the reflection in the image root.

The underlying linear equivalence is Mathlib's `Module.reflection`; preservation of the
bilinear form uses `LinearMap.IsReflective.isOrthogonal_reflection`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §8.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]
variable {L : IntegralLattice V} {M : IntegralLattice W}

/-- Reflection in an integral vector of norm two, as an automorphism of the lattice. -/
noncomputable def rootReflection (x : L) (hx : L.integralNorm x = 2) : Isometry L L := by
  have hxx : L.integralForm x x = 2 := by simpa only [integralNorm_apply] using hx
  have hreflective : LinearMap.IsReflective L.integralForm x :=
    LinearMap.IsReflective.of_dvd_two L.integralForm (hxx ▸ dvd_rfl)
  have hcoroot : LinearMap.IsReflective.coroot L.integralForm hreflective =
      L.integralForm x := by
    ext y
    have h := LinearMap.IsReflective.apply_self_mul_coroot_apply
      L.integralForm hreflective (y := y)
    rw [hxx] at h
    linarith
  refine Isometry.ofCarrierEquiv (Module.reflection hxx) ?_
  intro y z
  simpa only [Module.reflection_apply, hcoroot, LinearEquiv.toFun_eq_coe] using
    LinearMap.IsReflective.isOrthogonal_reflection L.integralForm hreflective
      (LinearMap.BilinForm.isSymm_iff.mp L.isSymm_integralForm) y z

/-- The carrier equivalence is the integral module reflection in the root. -/
theorem rootReflection_carrierEquiv (x : L) (hx : L.integralNorm x = 2) :
    (rootReflection x hx).carrierEquiv =
      Module.reflection (x := x) (f := L.integralForm x)
        (by simpa only [integralNorm_apply] using hx) := by
  -- Unfold the comparison constructor to use the carrier-extension round trip.
  simp only [rootReflection, Isometry.carrierEquiv_ofCarrierEquiv]

/-- On the rational ambient space, reflection in a root has no denominator. -/
-- Like `Module.reflection_apply`, this stays explicit so that `simp` retains the reflection
-- until a specialized rule such as `rootReflection_apply_self` can apply.
theorem rootReflection_apply (x : L) (hx : L.integralNorm x = 2) (y : V) :
    rootReflection x hx y = y - L.form x y • (x : V) := by
  have hxx : L.form x x = 2 := by
    rw [← L.norm_apply, ← L.integralNorm_cast, hx]
    norm_num
  have hlinear := LinearEquiv.eq_extendOfIsLattice
    (rootReflection x hx).carrierEquiv (Module.reflection hxx) (by
      intro z
      simp only [rootReflection_carrierEquiv, Module.reflection_apply, Submodule.coe_sub,
        SetLike.val_smul, ← L.integralForm_cast, Int.cast_smul_eq_zsmul])
  rw [← Isometry.ofCarrierEquiv_carrierEquiv (rootReflection x hx),
    Isometry.ofCarrierEquiv_apply, ← hlinear, Module.reflection_apply]

/-- On the integral carrier, the reflection uses the integral pairing as its coefficient. -/
@[simp]
theorem rootReflection_carrierEquiv_apply (x : L) (hx : L.integralNorm x = 2) (y : L) :
    (rootReflection x hx).carrierEquiv y = y - L.integralForm x y • x := by
  rw [rootReflection_carrierEquiv, Module.reflection_apply]

/-- Every root reflection has determinant minus one. -/
@[simp]
theorem det_rootReflection (x : L) (hx : L.integralNorm x = 2) :
    Isometry.det L (rootReflection x hx) = -1 := by
  rw [Isometry.det_apply, rootReflection_carrierEquiv, Module.det_reflection]

/-- Reflection sends its defining root to its negative. -/
@[simp]
theorem rootReflection_apply_self (x : L) (hx : L.integralNorm x = 2) :
    rootReflection x hx x = -(x : V) := by
  have hxx : L.integralForm x x = 2 := by simpa only [integralNorm_apply] using hx
  simpa only [← Isometry.coe_carrierEquiv_apply, rootReflection_carrierEquiv,
    Submodule.coe_neg] using congrArg Subtype.val (Module.reflection_apply_self hxx)

/-- Reflection in a root is an involution in the lattice isometry group. -/
@[simp]
theorem rootReflection_mul_self (x : L) (hx : L.integralNorm x = 2) :
    rootReflection x hx * rootReflection x hx = 1 := by
  have hxx : L.integralForm x x = 2 := by simpa only [integralNorm_apply] using hx
  apply Isometry.carrierEquiv_injective
  ext y
  simp only [Isometry.mul_def, Isometry.carrierEquiv_trans, LinearEquiv.trans_apply,
    rootReflection_carrierEquiv, Isometry.one_def, Isometry.carrierEquiv_refl,
    LinearEquiv.refl_apply]
  exact congrArg Subtype.val (Module.involutive_reflection hxx y)

/-- The inverse of a root reflection is itself. -/
@[simp]
theorem rootReflection_inv (x : L) (hx : L.integralNorm x = 2) :
    (rootReflection x hx)⁻¹ = rootReflection x hx :=
  inv_eq_of_mul_eq_one_right (rootReflection_mul_self x hx)

/-- Opposite roots define the same reflection. -/
@[simp]
theorem rootReflection_neg (x : L) (hx : L.integralNorm x = 2) :
    rootReflection (-x) (by simpa using hx) = rootReflection x hx := by
  ext y
  simp [rootReflection_apply]

/-- A root reflection fixes exactly the vectors orthogonal to its root. -/
@[simp]
theorem rootReflection_apply_eq_self_iff (x : L) (hx : L.integralNorm x = 2) (y : V) :
    rootReflection x hx y = y ↔ L.form x y = 0 := by
  have hx0 : (x : V) ≠ 0 := by
    intro h
    have := L.integralNorm_cast x
    simp [hx, h, L.norm_apply] at this
  simp [rootReflection_apply, sub_eq_self, smul_eq_zero, hx0]

/-- Lattice isometries intertwine the reflections in a root and in its image. -/
theorem Isometry.map_rootReflection (e : Isometry L M) (x : L)
    (hx : L.integralNorm x = 2) (y : V) :
    e (rootReflection x hx y) =
      rootReflection (e.carrierEquiv x) (by simpa using hx) (e y) := by
  simp only [rootReflection_apply, map_sub, map_smul,
    Isometry.coe_carrierEquiv_apply, Isometry.map_app]

/-- Conjugation by a lattice automorphism carries root reflections to root reflections. -/
theorem Isometry.mul_rootReflection_mul_inv (e : Isometry L L) (x : L)
    (hx : L.integralNorm x = 2) :
    e * rootReflection x hx * e⁻¹ =
      rootReflection (e.carrierEquiv x) (by simpa using hx) := by
  ext y
  simp only [Isometry.mul_apply, Isometry.inv_apply, e.map_rootReflection x hx,
    Isometry.apply_symm_apply]

end TauCeti.IntegralLattice

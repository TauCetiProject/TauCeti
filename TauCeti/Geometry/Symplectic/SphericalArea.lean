/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Spherical
import TauCeti.AlgebraicTopology.UniversalCover.Circle.HigherHomotopy
import TauCeti.Topology.Homotopy.HomotopyGroup.Product

/-!
# Spherical areas of `S² × Tᵏ`

Gromov's proof of the nonsqueezing theorem embeds a ball into a product `S²(a) × T²ⁿ⁻²` of a
sphere of area `a` with a torus, and counts holomorphic spheres in the class of the slice
`S² × {y}`. Compactness of these spheres rests on an *area gap*: the area of every spherical class
is an integer multiple of `a`, so a holomorphic sphere, whose area is positive, has area at least
`a`, and a sphere of area `a` cannot bubble.

This file proves the topological part of the area gap, for any homomorphism `ω` from the second
integral homology group, such as integration of a closed two-form. Since the torus has trivial
second homotopy group, the spherical classes of `S² × Tᵏ` are the integer multiples of the class
`[S² × {y}]` of a slice (`TauCeti.sphericalClasses_sphere_prod_eq_zmultiples`), so:

* the value of `ω` on a spherical class is an integer multiple of `a = ω [S² × {y}]`
  (`TauCeti.exists_apply_eq_zsmul_apply_sphereSliceClass`);
* if `a > 0`, every positive value of `ω` on a spherical class is at least `a`
  (`TauCeti.apply_sphereSliceClass_le`).

Both statements are proved for `Sⁿ⁺¹ × Y` with `Y` path-connected and `πₙ₊₁(Y)` trivial. For a
product `Tᵏ` of circles these hypotheses are found by instance resolution
(`AddCircle.subsingleton_homotopyGroup` and `HomotopyGroup.subsingleton_pi`), so they apply to
`S² × Tᵏ` directly.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. **82** (1985),
  307–347, §0.3.A.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, second edition,
  Section 9.3, the proof of the nonsqueezing theorem.
-/

public section

open CategoryTheory AlgebraicTopology Metric

namespace TauCeti

variable {Y : Type} [TopologicalSpace Y] {G : Type*} [AddCommGroup G]

/-- **Spherical areas of `Sⁿ⁺¹ × Y` are multiples of the area of a slice.** If `Y` is
path-connected and `πₙ₊₁(Y, y)` is trivial, the value of a homomorphism `ω` on a spherical class
of `Sⁿ⁺¹ × Y` is an integer multiple of its value on the class of the slice `Sⁿ⁺¹ × {y}`. -/
theorem exists_apply_eq_zsmul_apply_sphereSliceClass [PathConnectedSpace Y] {y : Y}
    {n : ℕ} [Subsingleton (HomotopyGroup (Fin (n + 1)) Y y)]
    (ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 × Y)) →+ G)
    {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 × Y))}
    (hc : c ∈ sphericalClasses (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 × Y) n) :
    ∃ k : ℤ, ω c = k • ω (sphereSliceClass Y y n) := by
  rw [sphericalClasses_sphere_prod_eq_zmultiples y n] at hc
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hc
  exact ⟨k, map_zsmul ω k _⟩

/-- **The area gap of `Sⁿ⁺¹ × Y`.** If `Y` is path-connected and `πₙ₊₁(Y, y)` is trivial, and the
homomorphism `ω` is positive on the class of the slice `Sⁿ⁺¹ × {y}`, then every positive value of
`ω` on a spherical class of `Sⁿ⁺¹ × Y` is at least its value on the slice. -/
theorem apply_sphereSliceClass_le [PartialOrder G] [IsOrderedAddMonoid G]
    [PathConnectedSpace Y] {y : Y} {n : ℕ} [Subsingleton (HomotopyGroup (Fin (n + 1)) Y y)]
    (ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 × Y)) →+ G)
    (ha : 0 < ω (sphereSliceClass Y y n))
    {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 × Y))}
    (hc : c ∈ sphericalClasses (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 × Y) n)
    (hpos : 0 < ω c) : ω (sphereSliceClass Y y n) ≤ ω c := by
  obtain ⟨k, hk⟩ := exists_apply_eq_zsmul_apply_sphereSliceClass (y := y) ω hc
  rw [hk] at hpos ⊢
  -- `0 < k • a` with `a > 0` forces `k ≥ 1`.
  have hk0 : (0 : ℤ) < k := (zsmul_lt_zsmul_iff_left ha).1 (by rwa [zero_zsmul])
  have hk1 : 1 ≤ k := by omega
  simpa using zsmul_le_zsmul_left ha.le hk1

/-- The area gap applies to `S² × Tᵏ` for every product `Tᵏ` of circles: instance resolution
finds that the torus is path-connected and has trivial second homotopy group. -/
example {ι : Type} {p : ι → ℝ} {y : ∀ i, AddCircle (p i)}
    (ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ∀ i, AddCircle (p i))) →+ ℝ)
    (ha : 0 < ω (sphereSliceClass _ y 1))
    {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ∀ i, AddCircle (p i)))}
    (hc : c ∈ sphericalClasses (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ∀ i, AddCircle (p i)) 1)
    (hpos : 0 < ω c) : ω (sphereSliceClass _ y 1) ≤ ω c :=
  apply_sphereSliceClass_le ω ha hc hpos

end TauCeti

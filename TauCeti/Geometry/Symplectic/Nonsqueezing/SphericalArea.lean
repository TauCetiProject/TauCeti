/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Spherical
import TauCeti.AlgebraicTopology.UniversalCover.Torus.HigherHomotopy

/-!
# Spherical areas of `S² × Tᵏ`

Gromov's proof of the nonsqueezing theorem embeds a ball into a product `S²(a) × T²ⁿ⁻²` of a
sphere of area `a` with a torus, and counts holomorphic spheres in the class of the slice
`S² × {y}`. Compactness of these spheres rests on an *area gap*: the area of every spherical class
is an integer multiple of `a`, so a holomorphic sphere, whose area is positive, has area at least
`a`, and a sphere of area `a` cannot bubble.

The topological part of the area gap holds for any homomorphism `ω` from the second integral
homology group, such as integration of a closed two-form, and is proved for `Sⁿ⁺¹ × Y` with `Y`
path-connected and `πₙ₊₁(Y)` trivial in
`TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Spherical`:

* the value of `ω` on a spherical class is an integer multiple of `a = ω [S² × {y}]`
  (`TauCeti.exists_apply_eq_zsmul_apply_sphereSliceClass`);
* if `a > 0`, every positive value of `ω` on a spherical class is at least `a`
  (`TauCeti.apply_sphereSliceClass_le`).

For a product `Tᵏ` of circles both hypotheses are found by instance resolution, the second by
`AddCircle.subsingleton_homotopyGroup_pi`, so these statements apply to `S² × Tᵏ` directly. The
example below checks this.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. **82** (1985),
  307–347, §0.3.A.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, second edition,
  Section 9.3, the proof of the nonsqueezing theorem.
-/

open CategoryTheory AlgebraicTopology Metric

namespace TauCeti

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

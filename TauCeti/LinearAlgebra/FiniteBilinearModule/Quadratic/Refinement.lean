/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic.Basic
import TauCeti.Algebra.Group.Pow

/-!
# The quadratic refinement of a symmetric pairing of odd order

On a finite abelian group `A` of odd order `n`, a symmetric pairing `b : A × A → ℚ/ℤ` has exactly
one quadratic refinement, the map

```text
q(x) = ((n + 1) / 2) · b(x, x).
```

Indeed every quadratic map `q` with polar form `b` satisfies `2q(x) = b(x, x)` and `n q(x) = 0`,
so `q(x) = (n + 1) q(x) = ((n + 1) / 2) · b(x, x)`. Consequently a bilinear isometry between finite
quadratic modules of odd order preserves the quadratic maps, and finite quadratic modules of odd
order are classified by their bilinear modules alone.

## Main declarations

* `TauCeti.FiniteBilinearModule.quadraticRefinement`: the quadratic refinement
  `x ↦ ((n + 1) / 2) · b(x, x)` of a finite bilinear module of odd order `n`.
* `TauCeti.FiniteQuadraticModule.quadratic_eq_nsmul_pairing_self_of_odd` and
  `TauCeti.FiniteQuadraticModule.eq_quadraticRefinement`: every finite quadratic module of odd
  order is the quadratic refinement of its bilinear module.
* `TauCeti.FiniteQuadraticModule.map_quadratic_of_odd` and
  `TauCeti.FiniteQuadraticModule.isometryOfBilinearIsometryOfOdd`: a bilinear isometry between
  finite quadratic modules of odd order is a quadratic isometry.
* `TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd`: finite quadratic
  modules of odd order are isometric exactly when their bilinear modules are.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.8.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti

universe u v

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule.{u})

/-- **The quadratic refinement of a symmetric pairing of odd order.** On a finite abelian group
of odd order `n`, the quadratic map `x ↦ ((n + 1) / 2) • b(x, x)` has polar form `b`, since
`(n + 1) • b(x, y) = b(x, y)`. It is the only finite quadratic module structure with pairing `b`
(`TauCeti.FiniteQuadraticModule.eq_quadraticRefinement`).

Exposed so that its bilinear module is `A` by definition, and bilinear isometries into or out of
`A` are bilinear isometries of the refinement. -/
@[expose] noncomputable def quadraticRefinement (hA : Odd (Nat.card A)) :
    FiniteQuadraticModule where
  toFiniteBilinearModule := A
  quadratic := LinearMap.BilinMap.toQuadraticMap (((Nat.card A + 1) / 2) • A.toBilin)
  polar_eq_pairing' x y := by
    have hn : Nat.card A • A.pairing x y = 0 := by
      rw [← pairing_nsmul_left, card_nsmul_eq_zero', pairing_zero_left]
    rw [LinearMap.BilinMap.polar_toQuadraticMap]
    simp only [LinearMap.smul_apply, toBilin_apply]
    rw [A.pairing_comm y x, ← smul_add, ← two_nsmul, nsmul_two_nsmul_of_odd hA hn]

/-- The bilinear module of the quadratic refinement of `A` is `A`. -/
@[simp]
theorem quadraticRefinement_toFiniteBilinearModule (hA : Odd (Nat.card A)) :
    (A.quadraticRefinement hA).toFiniteBilinearModule = A :=
  (rfl)

/-- The quadratic refinement of a pairing `b` on a group of odd order `n` is
`x ↦ ((n + 1) / 2) • b(x, x)`. -/
@[simp]
theorem quadraticRefinement_quadratic (hA : Odd (Nat.card A)) (x : A) :
    (A.quadraticRefinement hA).quadratic x = ((Nat.card A + 1) / 2) • A.pairing x x :=
  (LinearMap.BilinMap.toQuadraticMap_apply _ x).trans <| by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, toBilin_apply]

end FiniteBilinearModule

namespace FiniteQuadraticModule

variable {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}

/-- On a finite quadratic module of odd order `n`, the quadratic map is determined by the pairing:
`q(x) = ((n + 1) / 2) • b(x, x)`. -/
theorem quadratic_eq_nsmul_pairing_self_of_odd (hA : Odd (Nat.card A)) (x : A) :
    A.quadratic x = ((Nat.card A + 1) / 2) • A.toFiniteBilinearModule.pairing x x := by
  rw [← polar_eq_pairing, QuadraticMap.polar_self,
    nsmul_two_nsmul_of_odd hA (A.natCard_nsmul_quadratic_of_odd hA x)]

/-- **Uniqueness of the quadratic refinement in odd order.** A finite quadratic module of odd
order is the quadratic refinement of its bilinear module. -/
theorem eq_quadraticRefinement (A : FiniteQuadraticModule.{u}) (hA : Odd (Nat.card A)) :
    A = A.toFiniteBilinearModule.quadraticRefinement hA := by
  obtain ⟨B, q, hq⟩ := A
  congr 1
  ext x
  exact (quadratic_eq_nsmul_pairing_self_of_odd (A := ⟨B, q, hq⟩) hA x).trans
    (B.quadraticRefinement_quadratic hA x).symm

/-- A bilinear isometry between finite quadratic modules of odd order preserves the quadratic
maps. -/
theorem map_quadratic_of_odd (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule)
    (x : A) : B.quadratic (f x) = A.quadratic x := by
  have hB : Nat.card B = Nat.card A := (Nat.card_congr f.toAddEquiv.toEquiv).symm
  rw [quadratic_eq_nsmul_pairing_self_of_odd (hB ▸ hA), quadratic_eq_nsmul_pairing_self_of_odd hA,
    hB, f.map_pairing]

/-- A bilinear isometry between finite quadratic modules of odd order, as a quadratic isometry. -/
def isometryOfBilinearIsometryOfOdd (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    Isometry A B where
  toLinearEquiv := f.toAddEquiv.toIntLinearEquiv
  map_app' := map_quadratic_of_odd hA f

/-- The quadratic isometry `isometryOfBilinearIsometryOfOdd hA f` acts as `f`. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_apply (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule)
    (x : A) : isometryOfBilinearIsometryOfOdd hA f x = f x :=
  (rfl)

/-- Forgetting the quadratic maps of `isometryOfBilinearIsometryOfOdd hA f` recovers `f`. -/
@[simp]
theorem toFiniteBilinearModule_isometryOfBilinearIsometryOfOdd (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    (isometryOfBilinearIsometryOfOdd hA f).toFiniteBilinearModule = f :=
  -- Both sides have the additive equivalence `f.toAddEquiv`, repackaged as a `ℤ`-linear one.
  FiniteBilinearModule.Isometry.toAddEquiv_injective
    (Isometry.toFiniteBilinearModule_toAddEquiv _)

/-- Finite quadratic modules of odd order are isometric exactly when their bilinear modules are.
In odd order no Gauss-sum condition is needed, unlike Nikulin's comparison theorem
`TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_and_gaussSign_eq`. -/
theorem nonempty_isometry_iff_bilinear_isometry_of_odd (hA : Odd (Nat.card A)) :
    Nonempty (Isometry A B) ↔
      Nonempty (FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :=
  ⟨fun ⟨f⟩ ↦ ⟨f.toFiniteBilinearModule⟩, fun ⟨f⟩ ↦ ⟨isometryOfBilinearIsometryOfOdd hA f⟩⟩

end FiniteQuadraticModule

end TauCeti

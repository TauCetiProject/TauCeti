/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.Algebra.Homology.DG.Algebra.Defs
import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Curved differential graded algebras

A curved differential graded algebra over a commutative ring `R` is an internally `ℤ`-graded
`R`-algebra `A` together with an `R`-linear map `d` of degree `+1` satisfying the graded Leibniz
rule, and a *curvature* `w ∈ A²` which measures the failure of `d` to square to zero:

`d (d a) = a * w - w * a` and `d w = 0`.

The square of `d` is thus the commutator with the curvature, with the sign fixed by the
**right-module convention**: a right curved module `M` over `A` has `d (d m) = m • w`. The
commutator equation is what makes this square compatible with the graded Leibniz rule
`d (m • a) = d m • a + (-1) ^ |m| • (m • d a)`: applying `d` twice to `m • a` gives
`d (d m) • a + m • d (d a) = m • (w * a) + m • d (d a)`, and this is `(m • a) • w` in every
right module (equivalently, for `m = 1` in `M = A`) exactly when `d (d a) = a * w - w * a`.
Positselski's curvature element `h` satisfies `d (d a) = h * a - a * h`; in his convention our
curvature is `w = -h`. This sign is load-bearing: storing `h` while using the right-module square
`m • w` is inconsistent.

The curvature is not assumed central. If it is, or more generally if it commutes with every
element, then `d` squares to zero and `A` is an ordinary differential graded algebra. Conversely
a differential graded algebra is a curved one with curvature zero.

## Main definitions

* `TauCeti.IsCurvedDGAlgebra 𝒜 d w`: the curved differential graded algebra axioms on an
  internally `ℤ`-graded unital `R`-algebra, an `R`-linear endomorphism of its carrier, and a
  curvature element.

## Main results

* `TauCeti.IsCurvedDGAlgebra.sq_eq_neg_lie`: the square of the differential is the commutator
  with `-w`, the graded-commutator form in Positselski's normalization.
* `TauCeti.IsCurvedDGAlgebra.map_one_eq_zero` and `TauCeti.IsCurvedDGAlgebra.map_algebraMap`: the
  differential annihilates the unit and the image of the ground ring.
* `TauCeti.IsCurvedDGAlgebra.toIsDGAlgebra_of_mem_center`: a central curvature gives an ordinary
  differential graded algebra.
* `TauCeti.isCurvedDGAlgebra_zero_iff`: curved differential graded algebras of curvature zero
  are exactly the differential graded algebras.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2, for
  curved DG algebras. His curvature `h` is the negative of the curvature `w` stored here.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the Leibniz sign
  convention `d (a * b) = d a * b + (-1) ^ |a| * (a * d b)`.
-/

public section

open DirectSum

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- A **curved differential graded algebra**: an internally `ℤ`-graded `R`-algebra `𝒜` on a
carrier `A`, an `R`-linear map `d` which raises degree by one and satisfies the graded Leibniz rule
on a homogeneous left factor, and a curvature `w` of degree two killed by `d` such that
`d (d a) = a * w - w * a`. The sign `(-1) ^ p` is `Int.negOnePow p`, acting through the units of
`ℤ`. The commutator sign is the right-module convention: Positselski's curvature is `-w`. -/
structure IsCurvedDGAlgebra (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A) (w : A) :
    Prop where
  /-- The differential raises the degree by one. -/
  map_mem : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → d a ∈ 𝒜 (p + 1)
  /-- The graded Leibniz rule for a left factor of degree `p`. -/
  leibniz : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ b : A,
    d (a * b) = d a * b + p.negOnePow • (a * d b)
  /-- The curvature has degree two. -/
  curvature_mem : w ∈ 𝒜 2
  /-- The square of the differential is the commutator with the curvature, in the right-module
  convention. -/
  sq_eq (a : A) : d (d a) = a * w - w * a
  /-- The differential annihilates the curvature. -/
  map_curvature : d w = 0

attribute [grind =>] IsCurvedDGAlgebra.map_mem

variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

namespace IsCurvedDGAlgebra

/-- The differential commutes with homogeneous projections, up to the degree shift by one. -/
@[simp]
theorem map_decompose (h : IsCurvedDGAlgebra 𝒜 d w) (p : ℤ) (a : A) :
    d (DirectSum.decompose 𝒜 a p : A) = (DirectSum.decompose 𝒜 (d a) (p + 1) : A) :=
  (LinearMap.isHomogeneous_def.mpr fun _ _ ha ↦ h.map_mem ha).map_decompose p a

/-- The Leibniz rule against a cycle in the right factor. The vanishing signed term permits an
arbitrary left factor, without a homogeneity hypothesis. -/
theorem leibniz_of_map_eq_zero (h : IsCurvedDGAlgebra 𝒜 d w) (a : A) {b : A} (hb : d b = 0) :
    d (a * b) = d a * b :=
  map_mul_of_leibniz_of_map_eq_zero h.leibniz a hb

/-- The Leibniz rule against the curvature in the right factor: the curvature is a cycle. -/
theorem map_mul_curvature (h : IsCurvedDGAlgebra 𝒜 d w) (a : A) : d (a * w) = d a * w :=
  h.leibniz_of_map_eq_zero a h.map_curvature

/-- The differential of a curved differential graded algebra annihilates the unit: the Leibniz
rule for `1 * 1` reads `d 1 = d 1 + d 1`. -/
theorem map_one_eq_zero (h : IsCurvedDGAlgebra 𝒜 d w) : d 1 = 0 :=
  map_one_eq_zero_of_leibniz h.leibniz

/-- The differential of a curved differential graded algebra annihilates the image of the ground
ring. -/
theorem map_algebraMap (h : IsCurvedDGAlgebra 𝒜 d w) (r : R) : d (algebraMap R A r) = 0 :=
  map_algebraMap_of_leibniz h.leibniz r

/-- **The graded-commutator form of the curvature equation.** The square of the differential is
the commutator `⁅-w, a⁆ = -w * a - a * -w` with the negative of the curvature. Since the curvature
has even degree, this ordinary commutator is also the graded commutator, and `-w` is the curvature
in Positselski's convention. -/
theorem sq_eq_neg_lie (h : IsCurvedDGAlgebra 𝒜 d w) (a : A) : d (d a) = ⁅-w, a⁆ := by
  rw [h.sq_eq, Ring.lie_def, neg_mul, mul_neg, sub_neg_eq_add, neg_add_eq_sub]

/-- The differential of a curved differential graded algebra squares to zero on the elements
commuting with the curvature. -/
theorem sq_eq_zero_of_commute (h : IsCurvedDGAlgebra 𝒜 d w) {a : A} (ha : Commute a w) :
    d (d a) = 0 := by
  rw [h.sq_eq, ha.eq, sub_self]

/-- **Central curvature.** A curved differential graded algebra whose curvature is central is an
ordinary differential graded algebra: the commutator with the curvature vanishes, so the
differential squares to zero. -/
theorem toIsDGAlgebra_of_mem_center (h : IsCurvedDGAlgebra 𝒜 d w) (hw : w ∈ Set.center A) :
    IsDGAlgebra 𝒜 d where
  map_mem := h.map_mem
  sq_zero a := h.sq_eq_zero_of_commute ((Set.mem_center_iff.1 hw).comm a).symm
  leibniz := h.leibniz

/-- A curved differential graded algebra of curvature zero is a differential graded algebra. -/
theorem toIsDGAlgebra_of_curvature_eq_zero (h : IsCurvedDGAlgebra 𝒜 d w) (hw : w = 0) :
    IsDGAlgebra 𝒜 d :=
  h.toIsDGAlgebra_of_mem_center (hw ▸ Set.zero_mem_center)

end IsCurvedDGAlgebra

/-- A differential graded algebra is a curved differential graded algebra of curvature zero. -/
theorem IsDGAlgebra.isCurvedDGAlgebra_zero (h : IsDGAlgebra 𝒜 d) :
    IsCurvedDGAlgebra 𝒜 d 0 where
  map_mem := h.map_mem
  leibniz := h.leibniz
  curvature_mem := zero_mem _
  sq_eq a := by rw [h.sq_zero, mul_zero, zero_mul, sub_zero]
  map_curvature := map_zero d

/-- **Zero curvature.** The curved differential graded algebras of curvature zero are exactly the
differential graded algebras. -/
theorem isCurvedDGAlgebra_zero_iff : IsCurvedDGAlgebra 𝒜 d 0 ↔ IsDGAlgebra 𝒜 d :=
  ⟨fun h ↦ h.toIsDGAlgebra_of_curvature_eq_zero rfl, fun h ↦ h.isCurvedDGAlgebra_zero⟩

end TauCeti

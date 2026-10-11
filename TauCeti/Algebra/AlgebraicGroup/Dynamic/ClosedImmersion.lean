/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic

/-!
# Dynamic Levi subgroups under closed immersions

A morphism of affine group schemes carries the Levi subgroup of a cocharacter into the Levi
subgroup of the induced cocharacter. If the morphism is a closed immersion, its map on points is
injective over every commutative value algebra, and Levi membership is detected by the ambient
group. This lets a Levi subgroup of a closed subgroup be obtained by intersecting with an
ambient Levi subgroup, a useful step when constructing its representing closed subgroup scheme.

The result holds over a commutative semiring and for arbitrary commutative value algebras. In
coordinates a closed immersion is a surjective bialgebra homomorphism; no smoothness or
finite-type assumption is needed.

## Main results

* `TauCeti.Cocharacter.mapDomain_conjugate`: a group-scheme morphism commutes with generic
  cocharacter conjugation.
* `TauCeti.Cocharacter.mem_levi_iff_of_injective`: an injective map on points detects Levi
  membership in the ambient group.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
-/

public section

namespace TauCeti.Cocharacter

open WithConv

variable {R H K A : Type*} [CommSemiring R] [Semiring H] [Semiring K]
variable [_root_.HopfAlgebra R H] [_root_.HopfAlgebra R K]
variable [CommSemiring A] [Algebra R A]

/-- The generic point of a cocharacter commutes with precomposition by a bialgebra morphism. -/
theorem mapDomain_genericPoint (φ : H →ₐc[R] K)
    (l : K →ₐc[R] LaurentPolynomial R) :
    AlgHom.mapDomain φ (genericPoint A l) = genericPoint A (l.comp φ) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  simp only [AlgHom.mapDomain_apply_apply, genericPoint_eq_pointsHom,
    pointsHom_apply]
  rfl

/-- A constant point commutes with precomposition by a bialgebra morphism. -/
theorem mapDomain_constPoint (φ : H →ₐc[R] K)
    (g : WithConv (K →ₐ[R] A)) :
    AlgHom.mapDomain φ (constPoint A g) =
      constPoint A (AlgHom.mapDomain φ g) := by
  rw [constPoint_apply, constPoint_apply, AlgHom.mapDomain_apply,
    AlgHom.mapDomain_apply, AlgHom.comp_assoc]

/-- Generic conjugation is natural in the coordinate Hopf algebra. -/
theorem mapDomain_conjugate (φ : H →ₐc[R] K)
    (l : K →ₐc[R] LaurentPolynomial R) (g : WithConv (K →ₐ[R] A)) :
    AlgHom.mapDomain φ (conjugate A l g) =
      conjugate A (l.comp φ) (AlgHom.mapDomain φ g) := by
  simp only [conjugate_apply, map_mul, map_inv, mapDomain_genericPoint,
    mapDomain_constPoint]

/-- Every morphism of affine group schemes carries the Levi of a cocharacter into the Levi of
the induced cocharacter. -/
theorem mapDomain_mem_levi (φ : H →ₐc[R] K)
    (l : K →ₐc[R] LaurentPolynomial R) {g : WithConv (K →ₐ[R] A)}
    (hg : g ∈ levi A l) : AlgHom.mapDomain φ g ∈ levi A (l.comp φ) := by
  rw [mem_levi_iff, ← mapDomain_conjugate, ← mapDomain_constPoint,
    mem_levi_iff.mp hg]

/-- For a closed immersion, a point is in the dynamic Levi exactly when its image lies in the
ambient dynamic Levi. The equality holds over every commutative value algebra, including
nonreduced ones. -/
theorem mem_levi_iff_of_injective (φ : H →ₐc[R] K)
    (hφ : Function.Injective (AlgHom.mapDomain (A := LaurentPolynomial A) φ))
    (l : K →ₐc[R] LaurentPolynomial R)
    (g : WithConv (K →ₐ[R] A)) :
    g ∈ levi A l ↔ AlgHom.mapDomain φ g ∈ levi A (l.comp φ) := by
  refine ⟨mapDomain_mem_levi φ l, fun hg => ?_⟩
  apply mem_levi_iff.mpr
  apply hφ
  rw [mapDomain_conjugate, mapDomain_constPoint]
  exact mem_levi_iff.mp hg

/-- The dynamic Levi of a closed subgroup is the inverse image of the ambient dynamic Levi. -/
theorem levi_eq_comap_of_injective (φ : H →ₐc[R] K)
    (hφ : Function.Injective (AlgHom.mapDomain (A := LaurentPolynomial A) φ))
    (l : K →ₐc[R] LaurentPolynomial R) :
    levi A l = (levi A (l.comp φ)).comap (AlgHom.mapDomain φ) := by
  ext g
  exact mem_levi_iff_of_injective φ hφ l g

end TauCeti.Cocharacter

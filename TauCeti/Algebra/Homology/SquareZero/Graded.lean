/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.Algebra.Ring.NegOnePow

/-!
# Degree-wise cohomology of a linear endomorphism and products on it

Let `D` be a linear endomorphism of a module `M`, and let `G : ℤ → Submodule R M` be a family of
homogeneous pieces. The degree-`i` cocycles of `D` are the elements of `G i` killed by `D`, the
degree-`i` coboundaries are the images under `D` of elements of `G (i - 1)`, and the degree-`i`
cohomology is the quotient of the first by the second (`LinearMap.cohomology`). This is the
cohomology of the cochain convention, in which a differential raises degree by one.

The definitions need no hypothesis on `D` or `G`; in particular `M` need not be the direct sum of
the pieces `G i`. This covers completed modules, in which a completed combination need not be a
sum of homogeneous ones. Unlike `TauCeti.gradedCochainComplex`, which assembles a differential of
degree one into a cochain complex for Mathlib's categorical homology, these are concrete quotients
whose elements are classes of elements of `M`, in the manner of `LinearMap.homology` (the homology
of a square-zero endomorphism, in `TauCeti.Algebra.Homology.SquareZero`).

A bilinear map `μ : M₁ → M₂ → M₀` which shifts degree by `ε` and obeys the Leibniz rule
`D₀ (μ a b) = μ (D₁ a) b + (-1)^i μ a (D₂ b)` for `a` of degree `i` sends two cocycles to a
cocycle, and a cocycle and a coboundary, in either order, to a coboundary. Hence it descends to a
bilinear map `H^i × H^j → H^k` for `k = i + j + ε` (`LinearMap.cohomologyProduct`).

## Main definitions

* `LinearMap.cocycles`, `LinearMap.coboundaries`: the degree-`i` cocycles and coboundaries of a
  linear endomorphism with respect to a family of homogeneous pieces.
* `LinearMap.cohomology`: the degree-`i` cohomology.
* `LinearMap.cohomologyProduct`: the product on cohomology induced by a bilinear map obeying the
  Leibniz rule.

## Main results

* `LinearMap.coboundaries_le_cocycles`: coboundaries are cocycles for a differential of degree
  one.
* `LinearMap.cohomology_mk_eq_zero_iff`, `LinearMap.cohomology_mk_eq_mk_iff`: when the class of
  a cocycle vanishes, and when two classes are equal.
* `LinearMap.apply_mem_cocycles`, `LinearMap.apply_mem_coboundaries_of_left`,
  `LinearMap.apply_mem_coboundaries_of_right`: products of cocycles are cocycles, and products
  with a coboundary are coboundaries.
* `LinearMap.cohomologyProduct_mk`: the product on cohomology is computed on representing
  cocycles.
-/

public section

noncomputable section

open TauCeti

namespace LinearMap

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  (D : M →ₗ[R] M) (G : ℤ → Submodule R M) (i : ℤ)

/-- The degree-`i` cocycles of an endomorphism `D` with respect to homogeneous pieces `G`: the
elements of `G i` which `D` sends to zero. -/
def cocycles : Submodule R M :=
  ker D ⊓ G i

/-- The degree-`i` coboundaries of an endomorphism `D` with respect to homogeneous pieces `G`: the
images under `D` of the elements of `G (i - 1)`. -/
def coboundaries : Submodule R M :=
  (G (i - 1)).map D

variable {D G i}

/-- A cocycle of degree `i` is an element of `G i` killed by `D`. -/
@[simp]
theorem mem_cocycles_iff {a : M} : a ∈ D.cocycles G i ↔ D a = 0 ∧ a ∈ G i :=
  Iff.rfl

/-- A coboundary of degree `i` is the image of an element of `G (i - 1)`. -/
@[simp]
theorem mem_coboundaries_iff {a : M} : a ∈ D.coboundaries G i ↔ ∃ x ∈ G (i - 1), D x = a :=
  Iff.rfl

/-- If `D` squares to zero and raises degrees by one on `G (i - 1)`, as a differential of degree
one does, then every degree-`i` coboundary is a cocycle. -/
theorem coboundaries_le_cocycles (hD : ∀ x ∈ G (i - 1), D (D x) = 0)
    (hdeg : ∀ x ∈ G (i - 1), D x ∈ G i) :
    D.coboundaries G i ≤ D.cocycles G i := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨hD x hx, hdeg x hx⟩

end Semiring

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (D : M →ₗ[R] M) (G : ℤ → Submodule R M) (i : ℤ)

/-- The degree-`i` cohomology of an endomorphism `D` with respect to homogeneous pieces `G`: its
degree-`i` cocycles modulo those which are degree-`i` coboundaries. -/
abbrev cohomology : Type _ :=
  D.cocycles G i ⧸ (D.coboundaries G i).comap (D.cocycles G i).subtype

variable {D G i}

/-- The class of a cocycle vanishes in cohomology exactly when the cocycle is a coboundary. -/
theorem cohomology_mk_eq_zero_iff {a : D.cocycles G i} :
    (Submodule.Quotient.mk a : D.cohomology G i) = 0 ↔ (a : M) ∈ D.coboundaries G i :=
  Submodule.Quotient.mk_eq_zero _

/-- Two cocycles have the same class in cohomology exactly when their difference is a
coboundary. -/
theorem cohomology_mk_eq_mk_iff {a b : D.cocycles G i} :
    (Submodule.Quotient.mk a : D.cohomology G i) = Submodule.Quotient.mk b ↔
      (a - b : M) ∈ D.coboundaries G i :=
  Submodule.Quotient.eq _

end Ring

section Product

variable {R M₁ M₂ M₀ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [AddCommGroup M₀] [Module R M₀]
  {D₁ : M₁ →ₗ[R] M₁} {D₂ : M₂ →ₗ[R] M₂} {D₀ : M₀ →ₗ[R] M₀}
  {G₁ : ℤ → Submodule R M₁} {G₂ : ℤ → Submodule R M₂} {G₀ : ℤ → Submodule R M₀}
  (μ : M₁ →ₗ[R] M₂ →ₗ[R] M₀) {ε : ℤ}
  (hdeg : ∀ {i j : ℤ} {a : M₁} {b : M₂}, a ∈ G₁ i → b ∈ G₂ j → μ a b ∈ G₀ (i + j + ε))
  (hL : ∀ {i : ℤ} {a : M₁}, a ∈ G₁ i → ∀ b,
    D₀ (μ a b) = μ (D₁ a) b + negOnePowCast R i • μ a (D₂ b))
  {i j k : ℤ} (hk : i + j + ε = k)

include hdeg hL hk

/-- The product of two cocycles is a cocycle, of the sum of their degrees and the degree shift
of the product. -/
theorem apply_mem_cocycles {a : M₁} {b : M₂} (ha : a ∈ D₁.cocycles G₁ i)
    (hb : b ∈ D₂.cocycles G₂ j) : μ a b ∈ D₀.cocycles G₀ k := by
  subst hk
  rw [mem_cocycles_iff] at ha hb ⊢
  refine ⟨?_, hdeg ha.2 hb.2⟩
  rw [hL ha.2, ha.1, hb.1]
  simp

/-- The product of a coboundary with a cocycle is a coboundary. -/
theorem apply_mem_coboundaries_of_left {a : M₁} {b : M₂} (ha : a ∈ D₁.coboundaries G₁ i)
    (hb : b ∈ D₂.cocycles G₂ j) : μ a b ∈ D₀.coboundaries G₀ k := by
  subst hk
  obtain ⟨x, hx, rfl⟩ := mem_coboundaries_iff.1 ha
  rw [mem_cocycles_iff] at hb
  refine mem_coboundaries_iff.2 ⟨μ x b, ?_, ?_⟩
  · have he : i - 1 + j + ε = i + j + ε - 1 := by ring
    exact he ▸ hdeg hx hb.2
  · rw [hL hx, hb.1]
    simp

/-- The product of a cocycle with a coboundary is a coboundary. -/
theorem apply_mem_coboundaries_of_right {a : M₁} {b : M₂} (ha : a ∈ D₁.cocycles G₁ i)
    (hb : b ∈ D₂.coboundaries G₂ j) : μ a b ∈ D₀.coboundaries G₀ k := by
  subst hk
  obtain ⟨y, hy, rfl⟩ := mem_coboundaries_iff.1 hb
  rw [mem_cocycles_iff] at ha
  refine mem_coboundaries_iff.2 ⟨negOnePowCast R i • μ a y, Submodule.smul_mem _ _ ?_, ?_⟩
  · have he : i + (j - 1) + ε = i + j + ε - 1 := by ring
    exact he ▸ hdeg ha.2 hy
  · rw [map_smul, hL ha.2, ha.1, smul_add, negOnePowCast_smul_negOnePowCast_smul]
    simp

/-- **The product on cohomology.** A bilinear map of degree shift `ε` obeying the Leibniz rule
with the endomorphisms induces a bilinear map from degree-`i` and degree-`j` cohomology to
degree-`k` cohomology, for `k = i + j + ε`. -/
def cohomologyProduct :
    D₁.cohomology G₁ i →ₗ[R] D₂.cohomology G₂ j →ₗ[R] D₀.cohomology G₀ k :=
  liftQ₂ _ _
    ((mk₂ R (fun (a : D₁.cocycles G₁ i) (b : D₂.cocycles G₂ j) =>
        (⟨μ a b, apply_mem_cocycles μ hdeg hL hk a.2 b.2⟩ : D₀.cocycles G₀ k))
      (fun _ _ _ => Subtype.ext (μ.map_add₂ _ _ _))
      (fun _ _ _ => Subtype.ext (μ.map_smul₂ _ _ _))
      (fun _ _ _ => Subtype.ext ((μ _).map_add _ _))
      (fun _ _ _ => Subtype.ext ((μ _).map_smul _ _))).compr₂ (Submodule.mkQ _))
    (fun _ ha => ext fun b => (Submodule.Quotient.mk_eq_zero _).2
      (apply_mem_coboundaries_of_left μ hdeg hL hk ha b.2))
    (fun _ hb => ext fun a => (Submodule.Quotient.mk_eq_zero _).2
      (apply_mem_coboundaries_of_right μ hdeg hL hk a.2 hb))

/-- The product on cohomology of the classes of two cocycles is the class of their product. -/
@[simp]
theorem cohomologyProduct_mk (a : D₁.cocycles G₁ i) (b : D₂.cocycles G₂ j) :
    cohomologyProduct μ hdeg hL hk (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk ⟨μ a b, apply_mem_cocycles μ hdeg hL hk a.2 b.2⟩ :=
  (rfl)

end Product

end LinearMap

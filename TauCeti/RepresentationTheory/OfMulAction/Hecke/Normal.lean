/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.OfMulAction.Hecke.Level

/-!
# The Hecke algebra of a normal level is a group algebra

Let `U` be a normal subgroup of a group `G` and `A` a commutative ring. Then `G` acts on the
quotient group `Q = G ⧸ U` by left multiplication through `G → Q`, the point stabilizers are all
equal to `U`, and `U` acts trivially on `Q`, so the stabilizer orbits are points
(`TauCeti.HeckeAlgebraLevel.finiteStabilizerOrbits_of_normal`). An element `h` of the Hecke algebra
of level `U`, `H(G, U; A) = Fun_G(Q × Q, A)` (`TauCeti.HeckeAlgebraLevel`), is determined by its
first row: `h(x, y) = h(1, x⁻¹ y)` by invariance. The matrix product of two such functions is the
convolution of their first rows, so `h ↦ ∑_q h(1, q) q` is an isomorphism of `A`-algebras
`H(G, U; A) ≃ₐ[A] A[G ⧸ U]` (`TauCeti.HeckeAlgebraLevel.toMonoidAlgebraAlgEquiv`). It sends the
basis element of the double coset `UgU = gU` to `g U`.

## Main definitions

* `TauCeti.HeckeAlgebraLevel.toMonoidAlgebraAlgEquiv`: for `U` normal, the isomorphism
  `H(G, U; A) ≃ₐ[A] A[G ⧸ U]`, `h ↦ ∑_q h(1, q) q`.

## Main results

* the instance `TauCeti.HeckeAlgebraLevel.finiteStabilizerOrbits_of_normal`.
* `TauCeti.HeckeAlgebraLevel.apply_eq_apply_one_inv_mul`: `h(x, y) = h(1, x⁻¹ y)`.
* `TauCeti.HeckeAlgebraLevel.coeff_toMonoidAlgebraAlgEquiv_apply`,
  `TauCeti.HeckeAlgebraLevel.toMonoidAlgebraAlgEquiv_symm_apply`: the isomorphism and its inverse
  on coefficients.

## References

* D. Treumann and A. Venkatesh, *Functoriality, Smith theory, and the Brauer homomorphism*,
  Ann. of Math. 183 (2016), §2.10, (2.10.1)–(2.10.3), pp. 187–188 (arXiv:1407.2346v1 §2.10).
-/

public section
noncomputable section

open MulAction

namespace TauCeti

namespace HeckeAlgebraLevel

variable {G : Type*} [Group G] {U : Subgroup G} [U.Normal] {A : Type*} [CommRing A]

/-- The action of `G` on `G ⧸ U` is left multiplication through `G → G ⧸ U`. -/
private theorem smul_eq_mul (g : G) (q : G ⧸ U) : g • q = (g : G ⧸ U) * q := by
  induction q using QuotientGroup.induction_on
  rfl

/-- For `U` normal, the orbits of the point stabilizers on `G ⧸ U` are points: every stabilizer is
`U`, which acts trivially on `G ⧸ U`. -/
instance finiteStabilizerOrbits_of_normal : FiniteStabilizerOrbits G (G ⧸ U) := by
  refine ⟨fun x y ↦ (Set.finite_singleton y).subset ?_⟩
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  have hg' : (g : G ⧸ U) = 1 := by
    have h : (g : G ⧸ U) * x = x := (smul_eq_mul g x).symm.trans (mem_stabilizer_iff.1 hg)
    simpa using h
  change g • y = y
  rw [smul_eq_mul, hg', one_mul]

/-- An element of the Hecke algebra of a normal level is determined by its first row:
`h(x, y) = h(1, x⁻¹ y)`. -/
theorem apply_eq_apply_one_inv_mul (h : HeckeAlgebraLevel G U A) (x y : G ⧸ U) :
    (h : (G ⧸ U) × (G ⧸ U) → A) (x, y) = (h : (G ⧸ U) × (G ⧸ U) → A) (1, x⁻¹ * y) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← PermutationHecke.apply_smul h a⁻¹, smul_eq_mul, smul_eq_mul, QuotientGroup.mk_inv,
    inv_mul_cancel]

/-- A finitely supported function `f` on `G ⧸ U` gives the element `(x, y) ↦ f(x⁻¹ y)` of the Hecke
algebra of level `U`. -/
private theorem ofMonoidAlgebra_mem (f : MonoidAlgebra A (G ⧸ U)) :
    (fun p : (G ⧸ U) × (G ⧸ U) ↦ f.coeff (p.1⁻¹ * p.2)) ∈ permutationHeckeModule G (G ⧸ U) A := by
  refine PermutationHecke.mem_iff.2 ⟨fun g p ↦ ?_, ?_⟩
  · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left]
  refine (f.coeff.support.finite_toSet.image
    fun q ↦ Quotient.mk (orbitRel G ((G ⧸ U) × (G ⧸ U))) (1, q)).subset ?_
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨(a : G ⧸ U)⁻¹ * y, Finsupp.mem_support_iff.2 hxy, Quotient.sound ⟨a⁻¹, ?_⟩⟩
  simp [smul_eq_mul]

/-- The first row `q ↦ h(1, q)` of an element of the Hecke algebra of a normal level, as an
element of the group algebra. -/
private def toMonoidAlgebra : HeckeAlgebraLevel G U A →ₗ[A] MonoidAlgebra A (G ⧸ U) where
  toFun h := MonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite _
    (PermutationHecke.finite_support_row h (1 : G ⧸ U)))
  map_add' _ _ := MonoidAlgebra.coeff_injective (Finsupp.ext fun _ ↦ rfl)
  map_smul' _ _ := MonoidAlgebra.coeff_injective (Finsupp.ext fun _ ↦ rfl)

private theorem coeff_toMonoidAlgebra (h : HeckeAlgebraLevel G U A) (q : G ⧸ U) :
    (toMonoidAlgebra h).coeff q = (h : (G ⧸ U) × (G ⧸ U) → A) (1, q) :=
  (rfl)

/-- The first row, as an `A`-linear equivalence. -/
private def toMonoidAlgebraLinearEquiv :
    HeckeAlgebraLevel G U A ≃ₗ[A] MonoidAlgebra A (G ⧸ U) where
  __ := toMonoidAlgebra
  invFun f := ⟨_, ofMonoidAlgebra_mem f⟩
  left_inv h := Subtype.ext (funext fun p ↦ by
    change (toMonoidAlgebra h).coeff (p.1⁻¹ * p.2) = _
    rw [coeff_toMonoidAlgebra, ← apply_eq_apply_one_inv_mul])
  right_inv f := MonoidAlgebra.coeff_injective (Finsupp.ext fun q ↦ by
    change (fun p : (G ⧸ U) × (G ⧸ U) ↦ f.coeff (p.1⁻¹ * p.2)) (1, q) = f.coeff q
    simp)

private theorem toMonoidAlgebra_one : toMonoidAlgebra (1 : HeckeAlgebraLevel G U A) = 1 := by
  classical
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun q ↦ ?_)
  rw [coeff_toMonoidAlgebra, PermutationHecke.one_apply, MonoidAlgebra.one_def,
    MonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

private theorem toMonoidAlgebra_mul (h₁ h₂ : HeckeAlgebraLevel G U A) :
    toMonoidAlgebra (h₁ * h₂) = toMonoidAlgebra h₁ * toMonoidAlgebra h₂ := by
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun z ↦ ?_)
  rw [coeff_toMonoidAlgebra, PermutationHecke.mul_apply, MonoidAlgebra.coeff_mul_apply_left,
    Finsupp.sum]
  refine (finsum_eq_sum_of_support_subset _ fun y hy ↦ ?_).trans
    (Finset.sum_congr rfl fun y _ ↦ ?_)
  · exact Finsupp.mem_support_iff.2 (left_ne_zero_of_mul hy)
  · rw [coeff_toMonoidAlgebra, coeff_toMonoidAlgebra, apply_eq_apply_one_inv_mul h₂]

variable (G U A) in
/-- **The Hecke algebra of a normal level is the group algebra of the quotient**: for `U` normal,
`h ↦ ∑_q h(1, q) q` is an isomorphism of `A`-algebras `H(G, U; A) ≃ₐ[A] A[G ⧸ U]`. -/
def toMonoidAlgebraAlgEquiv : HeckeAlgebraLevel G U A ≃ₐ[A] MonoidAlgebra A (G ⧸ U) :=
  AlgEquiv.ofLinearEquiv toMonoidAlgebraLinearEquiv toMonoidAlgebra_one toMonoidAlgebra_mul

/-- The coefficient of `q` in the image of `h` is `h(1, q)`. -/
@[simp]
theorem coeff_toMonoidAlgebraAlgEquiv_apply (h : HeckeAlgebraLevel G U A) (q : G ⧸ U) :
    (toMonoidAlgebraAlgEquiv G U A h).coeff q = (h : (G ⧸ U) × (G ⧸ U) → A) (1, q) :=
  (rfl)

/-- The inverse sends `f` to `(x, y) ↦ f(x⁻¹ y)`. -/
@[simp]
theorem toMonoidAlgebraAlgEquiv_symm_apply (f : MonoidAlgebra A (G ⧸ U)) (x y : G ⧸ U) :
    ((toMonoidAlgebraAlgEquiv G U A).symm f : (G ⧸ U) × (G ⧸ U) → A) (x, y) =
      f.coeff (x⁻¹ * y) :=
  (rfl)

end HeckeAlgebraLevel

end TauCeti

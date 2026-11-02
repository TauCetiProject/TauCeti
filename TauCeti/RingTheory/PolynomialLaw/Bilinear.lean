/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Homogeneous
public import TauCeti.LinearAlgebra.BilinearMap.BaseChange

/-!
# The polynomial law of a bilinear map

An `R`-bilinear map `B : M →ₗ[R] N →ₗ[R] P` induces the polynomial law
`B.toPolynomialLaw₂ : M × N →ₚₗ[R] P`, sending `(m, n)` to `B m n`. After scalar extension to a
commutative `R`-algebra `S` it is the base change of `B`, evaluated on the two components of an
element of `S ⊗[R] (M × N)`; for instance
`(∑ᵢ sᵢ ⊗ (mᵢ, 0) + ∑ⱼ tⱼ ⊗ (0, nⱼ)) ↦ ∑ᵢ ∑ⱼ sᵢ tⱼ ⊗ B mᵢ nⱼ`.
It is homogeneous of degree two, and natural in all three modules.

Composing such a law with the universal homogeneous law of divided powers produces the laws on
`M × N` that represent maps out of tensor products of homogeneous divided-power pieces.

## Main declarations

* `LinearMap.toPolynomialLaw₂`: the polynomial law of a bilinear map.
* `LinearMap.toPolynomialLaw₂_toFun`: its component at an algebra in any universe.
* `LinearMap.toPolynomialLaw₂_toFun_sum_add_sum`: its value on a sum of vectors from the two
  factors.
* `LinearMap.isHomogeneousOfDegree_toPolynomialLaw₂`: it is homogeneous of degree two.
* `LinearMap.toPolynomialLaw₂_compl₁₂` and `LinearMap.toPolynomialLaw₂_compr₂`: naturality in the
  source modules and in the target module.

## References

* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963),
  Chapitre I][Roby-1963]
* The underlying `PolynomialLaw`s are the Mathlib formalization by Antoine Chambert-Loir and
  María Inés de Frutos-Fernández.
-/

public section

noncomputable section

universe u

open TensorProduct
open LinearMap (BilinMap)

namespace LinearMap

variable {R : Type u} [CommSemiring R]
variable {M N P M' N' P' : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N']
  [Module R N'] [AddCommMonoid P'] [Module R P']

/-- The polynomial law `M × N →ₚₗ[R] P` of an `R`-bilinear map `B`, sending `(m, n)` to `B m n`.
Its component at a commutative `R`-algebra `S` evaluates the base change of `B` on the two
components of an element of `S ⊗[R] (M × N)`. -/
def toPolynomialLaw₂ (B : M →ₗ[R] N →ₗ[R] P) : M × N →ₚₗ[R] P where
  toFun' S _ _ x := BilinMap.baseChange S (B.compl₁₂ (fst R M N) (snd R M N)) x x
  isCompat' φ := funext fun x ↦ BilinMap.rTensor_baseChange_apply _ φ x x

theorem toPolynomialLaw₂_toFun' (B : M →ₗ[R] N →ₗ[R] P) (S : Type u) [CommSemiring S]
    [Algebra R S] (x : S ⊗[R] (M × N)) :
    B.toPolynomialLaw₂.toFun' S x =
      BilinMap.baseChange S (B.compl₁₂ (fst R M N) (snd R M N)) x x :=
  (rfl)

/-- The component of `B.toPolynomialLaw₂` at an `R`-algebra in an arbitrary universe evaluates
the base change of `B` on the two components of its argument. -/
theorem toPolynomialLaw₂_toFun (B : M →ₗ[R] N →ₗ[R] P) (S : Type*) [CommSemiring S]
    [Algebra R S] (x : S ⊗[R] (M × N)) :
    B.toPolynomialLaw₂.toFun S x =
      BilinMap.baseChange S (B.compl₁₂ (fst R M N) (snd R M N)) x x := by
  obtain ⟨n, ψ, p, rfl⟩ := PolynomialLaw.exists_lift x
  rw [← PolynomialLaw.isCompat_apply, ← PolynomialLaw.toFun'_eq_toFun]
  exact BilinMap.rTensor_baseChange_apply _ ψ p p

/-- The value of `B.toPolynomialLaw₂` on a pure tensor: `s ⊗ (m, n) ↦ s ^ 2 ⊗ B m n`. -/
@[simp]
theorem toPolynomialLaw₂_toFun_tmul (B : M →ₗ[R] N →ₗ[R] P) {S : Type*} [CommSemiring S]
    [Algebra R S] (s : S) (x : M × N) :
    B.toPolynomialLaw₂.toFun S (s ⊗ₜ[R] x) = (s ^ 2) ⊗ₜ[R] B x.1 x.2 := by
  simp [toPolynomialLaw₂_toFun, sq]

/-- The value of `B.toPolynomialLaw₂` on a sum of vectors from the two factors:
`∑ᵢ sᵢ ⊗ (mᵢ, 0) + ∑ⱼ tⱼ ⊗ (0, nⱼ) ↦ ∑ᵢ ∑ⱼ sᵢ tⱼ ⊗ B mᵢ nⱼ`. -/
theorem toPolynomialLaw₂_toFun_sum_add_sum (B : M →ₗ[R] N →ₗ[R] P) {S : Type*}
    [CommSemiring S] [Algebra R S] {ι κ : Type*} (t : Finset ι) (t' : Finset κ) (s : ι → S)
    (m : ι → M) (s' : κ → S) (n : κ → N) :
    B.toPolynomialLaw₂.toFun S
        (∑ i ∈ t, s i ⊗ₜ[R] (m i, 0) + ∑ j ∈ t', s' j ⊗ₜ[R] (0, n j)) =
      ∑ i ∈ t, ∑ j ∈ t', (s i * s' j) ⊗ₜ[R] B (m i) (n j) := by
  simp [toPolynomialLaw₂_toFun, map_sum, sum_apply]

/-- The ground map of `B.toPolynomialLaw₂` is `(m, n) ↦ B m n`. -/
@[simp]
theorem ground_toPolynomialLaw₂ (B : M →ₗ[R] N →ₗ[R] P) (x : M × N) :
    B.toPolynomialLaw₂.ground x = B x.1 x.2 := by
  simp [PolynomialLaw.ground_apply, PolynomialLaw.toFun'_eq_toFun]

/-- The polynomial law of a bilinear map is homogeneous of degree two. -/
theorem isHomogeneousOfDegree_toPolynomialLaw₂ (B : M →ₗ[R] N →ₗ[R] P) :
    B.toPolynomialLaw₂.IsHomogeneousOfDegree 2 :=
  PolynomialLaw.isHomogeneousOfDegree_iff.mpr fun S _ _ s x ↦ by
    simp only [toPolynomialLaw₂, map_smul, smul_apply, smul_smul, sq]

/-- Precomposing a bilinear map with linear maps of its arguments precomposes its law with the
law of the product map. -/
theorem toPolynomialLaw₂_compl₁₂ (B : M' →ₗ[R] N' →ₗ[R] P) (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    (B.compl₁₂ f g).toPolynomialLaw₂ = B.toPolynomialLaw₂.comp (f.prodMap g).toPolynomialLaw := by
  ext S _ _ x
  simp only [PolynomialLaw.comp_toFun', Function.comp_apply, toPolynomialLaw_toFun',
    toPolynomialLaw₂_toFun']
  have hB : (B.compl₁₂ f g).compl₁₂ (fst R M N) (snd R M N) =
      (B.compl₁₂ (fst R M' N') (snd R M' N')).compl₁₂ (f.prodMap g) (f.prodMap g) := by
    ext <;> simp
  rw [hB, BilinMap.baseChange_compl₁₂, compl₁₂_apply]

/-- Postcomposing a bilinear map with a linear map postcomposes its law with the law of the
linear map. -/
theorem toPolynomialLaw₂_compr₂ (B : M →ₗ[R] N →ₗ[R] P) (h : P →ₗ[R] P') :
    (B.compr₂ h).toPolynomialLaw₂ = h.toPolynomialLaw.comp B.toPolynomialLaw₂ := by
  ext S _ _ x
  simp only [PolynomialLaw.comp_toFun', Function.comp_apply, toPolynomialLaw_toFun',
    toPolynomialLaw₂_toFun']
  have hB : (B.compr₂ h).compl₁₂ (fst R M N) (snd R M N) =
      (B.compl₁₂ (fst R M N) (snd R M N)).compr₂ h := by
    ext <;> simp
  rw [hB, BilinMap.baseChange_compr₂, compr₂_apply]

end LinearMap

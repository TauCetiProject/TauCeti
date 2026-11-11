/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeD

/-!
# Type `DD` structures and exterior tensor products of type `D` structures

A bordered three-manifold with two boundary components, each parametrized by a pointed matched
circle, has a type `DD` bimodule over the two bordered algebras `A` and `B`. Following Lipshitz,
Ozsváth and Thurston, a type `DD` structure over `A` and `B` is a type `D` structure over the
tensor product algebra `A ⊗ B`, with the differential `dA ⊗ 1 + 1 ⊗ dB` and the idempotents
`ιA s ⊗ ιB t` (`TauCeti.TypeDDStructure`). Over a ring of characteristic two this is an ungraded
differential algebra (`TauCeti.IsUngradedDGAlgebra.tensorProduct`), so the whole type `D` theory of
`TauCeti.LowDimTopology.Bordered.TypeD` applies to type `DD` structures: their morphisms, the
morphism differential, mapping cones, iterates, boundedness and box tensor products. A type `D`
action of `B` on the right is a left action of the opposite algebra, so the left-left convention
used here covers the bimodules `ᴬNᴮ` too.

The simplest type `DD` structures are **exterior tensor products**. For a type `D` structure `N`
over `A` with generators `X` and a type `D` structure `N'` over `B` with generators `X'`, the type
`DD` structure `N ⊗ N'` (`TauCeti.TypeDStructure.tensorProduct`) has the generators `X × X'`, the
pairs of idempotents, and the coefficient matrix

  `δ ⊗ 1 + 1 ⊗ δ'`,

a sum of Kronecker products in which `1` is the diagonal matrix of idempotents
`TauCeti.TypeDStructure.idMorphism`. Here `A` acts through the first factor and `B` through the
second, independently. The structure equation holds because the cross terms `δ ⊗ δ'` appear twice
and cancel in characteristic two
(`TauCeti.TypeDStructure.map_tensorProductCoeff_add_tensorProductCoeff_mul_tensorProductCoeff`).

The construction is functorial. Kronecker products of morphisms are morphisms
(`TauCeti.TypeDStructure.kroneckerTMul_mem_morphisms`), they compose factorwise
(`Matrix.mul_kroneckerTMul_mul`), the identity of `N ⊗ N'` is the product of the identities
(`TauCeti.TypeDStructure.idMorphism_tensorProduct`), and the morphism differential satisfies the
Leibniz rule

  `∂(F ⊗ G) = ∂F ⊗ G + F ⊗ ∂G`

(`TauCeti.TypeDStructure.morphismDifferential_tensorProduct_kroneckerTMul`), with no sign in
characteristic two. So homomorphisms tensor to homomorphisms, and a homotopy `H` with
`∂H = F + F₂` gives the homotopy `H ⊗ G` between `F ⊗ G` and `F₂ ⊗ G` for each homomorphism `G`.
Finally, if the coefficients of `N` and `N'` strictly increase height functions `h` and `h'`, then
those of `N ⊗ N'` strictly increase `h + h'`, so the exterior tensor product of such type `D`
structures is bounded (`TauCeti.TypeDStructure.isBounded_tensorProduct_of_lt`), as the box tensor
product with a type `A` module requires.

## Main definitions

* `TauCeti.TypeDDStructure`: a type `DD` structure over two differential algebras.
* `TauCeti.TypeDStructure.tensorProduct`: the exterior tensor product `N ⊗ N'` of type `D`
  structures, a type `DD` structure.

## Main results

* `TauCeti.TypeDStructure.map_tensorProductCoeff_add_tensorProductCoeff_mul_tensorProductCoeff`:
  the structure equation of `N ⊗ N'` in terms of those of `N` and `N'`.
* `TauCeti.TypeDStructure.kroneckerTMul_mem_morphisms`,
  `TauCeti.TypeDStructure.idMorphism_tensorProduct`: Kronecker products of morphisms are morphisms,
  and the identity of `N ⊗ N'` is the product of the identities.
* `TauCeti.TypeDStructure.morphismDifferential_tensorProduct_kroneckerTMul`: the Leibniz rule
  `∂(F ⊗ G) = ∂F ⊗ G + F ⊗ ∂G`.
* `TauCeti.TypeDStructure.isBounded_tensorProduct_of_lt`: exterior tensor products of type `D`
  structures increasing height functions are bounded.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), 525–724, [arXiv:1003.0598](https://arxiv.org/abs/1003.0598), §2.2
  (type `DD` structures as type `D` structures over a tensor product of algebras).
* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  §2.2 (type `D` structures and their morphisms).
-/

public section

open scoped TensorProduct Kronecker

namespace TauCeti

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  (dA : A →ₗ[R] A) (dB : B →ₗ[R] B) {S T : Type*} (ιA : S → A) (ιB : T → B)

/-- A **type `DD` structure** over the differential algebras `(A, dA)` and `(B, dB)` with
idempotents `ιA` and `ιB`, in a basis of generators `Y`: a type `D` structure over the tensor
product `A ⊗[R] B` with the differential `dA ⊗ 1 + 1 ⊗ dB` and the idempotents `ιA s ⊗ ιB t`.
Each generator lies over a pair of idempotents, and its coefficients are sums of elementary
tensors `a ⊗ b`. -/
abbrev TypeDDStructure (Y : Type*) [Fintype Y] :=
  TypeDStructure (ungradedTensorDifferential dA dB) (fun st : S × T => ιA st.1 ⊗ₜ[R] ιB st.2) Y

namespace TypeDStructure

variable {dA dB ιA ιB} {X X' : Type*} [Fintype X] [Fintype X'] [DecidableEq X] [DecidableEq X']

section Coefficients

variable (N : TypeDStructure dA ιA X) (N' : TypeDStructure dB ιB X')

/-- The coefficient matrix `δ ⊗ 1 + 1 ⊗ δ'` of the exterior tensor product of `N` and `N'`, where
`1` stands for the diagonal matrices of idempotents. -/
def tensorProductCoeff : Matrix (X × X') (X × X') (A ⊗[R] B) :=
  N.coeff ⊗ₖₜ[R] N'.idMorphism + N.idMorphism ⊗ₖₜ[R] N'.coeff

theorem tensorProductCoeff_def :
    tensorProductCoeff N N' = N.coeff ⊗ₖₜ[R] N'.idMorphism + N.idMorphism ⊗ₖₜ[R] N'.coeff :=
  (rfl)

theorem tensorProductCoeff_apply (x y : X) (x' y' : X') :
    tensorProductCoeff N N' (x, x') (y, y') =
      N.coeff x y ⊗ₜ[R] (if x' = y' then ιB (N'.idem x') else 0) +
        (if x = y then ιA (N.idem x) else 0) ⊗ₜ[R] N'.coeff x' y' := by
  simp [tensorProductCoeff]

/-- **The structure equation of an exterior tensor product.** When the idempotents are
idempotent cycles, the curvature `d Δ + Δ * Δ` of `Δ = δ ⊗ 1 + 1 ⊗ δ'` is
`(d δ + δ * δ) ⊗ 1 + 1 ⊗ (d δ' + δ' * δ')`. The cross terms `δ ⊗ δ'` appear twice and cancel in
characteristic two. -/
theorem map_tensorProductCoeff_add_tensorProductCoeff_mul_tensorProductCoeff [CharP R 2]
    (hιA : ∀ s, IsIdempotentElem (ιA s)) (hιB : ∀ t, IsIdempotentElem (ιB t))
    (hdA : ∀ s, dA (ιA s) = 0) (hdB : ∀ t, dB (ιB t) = 0) :
    (tensorProductCoeff N N').map (ungradedTensorDifferential dA dB) +
        tensorProductCoeff N N' * tensorProductCoeff N N' =
      (N.coeff.map dA + N.coeff * N.coeff) ⊗ₖₜ[R] N'.idMorphism +
        N.idMorphism ⊗ₖₜ[R] (N'.coeff.map dB + N'.coeff * N'.coeff) := by
  have hI := idMorphism_mul (idMorphism_mem_morphisms N hιA)
  have hI' := idMorphism_mul (idMorphism_mem_morphisms N' hιB)
  have h2 := add_self_eq_zero_of_charTwo R (N.coeff ⊗ₖₜ[R] N'.coeff)
  have hadd (P Q : Matrix X X A) : (P + Q) ⊗ₖₜ[R] N'.idMorphism =
      P ⊗ₖₜ[R] N'.idMorphism + Q ⊗ₖₜ[R] N'.idMorphism :=
    Matrix.kroneckerMap_add_left _ TensorProduct.add_tmul _ _ _
  simp only [tensorProductCoeff_def, hadd, Matrix.map_add _ (map_add _),
    Matrix.kroneckerTMul_map_ungradedTensorDifferential, map_idMorphism N hdA,
    map_idMorphism N' hdB, Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_kroneckerTMul_mul,
    idMorphism_mul (coeff_mem_morphisms N), mul_idMorphism (coeff_mem_morphisms N),
    idMorphism_mul (coeff_mem_morphisms N'), mul_idMorphism (coeff_mem_morphisms N'), hI, hI',
    Matrix.zero_kroneckerTMul, Matrix.kroneckerTMul_zero, Matrix.kroneckerTMul_add]
  calc _ = N.coeff.map dA ⊗ₖₜ[R] N'.idMorphism + N.idMorphism ⊗ₖₜ[R] N'.coeff.map dB +
        (N.coeff * N.coeff) ⊗ₖₜ[R] N'.idMorphism + N.idMorphism ⊗ₖₜ[R] (N'.coeff * N'.coeff) +
        (N.coeff ⊗ₖₜ[R] N'.coeff + N.coeff ⊗ₖₜ[R] N'.coeff) := by abel
    _ = _ := by rw [h2, add_zero]; abel

end Coefficients

/-- The **exterior tensor product** `N ⊗ N'` of a type `D` structure `N` over `A` and a type `D`
structure `N'` over `B`, when the idempotents are idempotent cycles: the type `DD` structure on
the generators `X × X'`, over the pairs of idempotents, with the coefficient matrix
`δ ⊗ 1 + 1 ⊗ δ'`. -/
def tensorProduct [CharP R 2] (N : TypeDStructure dA ιA X) (N' : TypeDStructure dB ιB X')
    (hιA : ∀ s, IsIdempotentElem (ιA s)) (hιB : ∀ t, IsIdempotentElem (ιB t))
    (hdA : ∀ s, dA (ιA s) = 0) (hdB : ∀ t, dB (ιB t) = 0) :
    TypeDDStructure dA dB ιA ιB (X × X') where
  idem p := (N.idem p.1, N'.idem p.2)
  coeff := tensorProductCoeff N N'
  idem_mul_coeff := by
    rintro ⟨x, x'⟩ ⟨y, y'⟩
    simp only [tensorProductCoeff_apply, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
      N.idem_mul_coeff, N'.idem_mul_coeff]
    split_ifs with h h' <;> simp [(hιA _).eq, (hιB _).eq]
  coeff_mul_idem := by
    rintro ⟨x, x'⟩ ⟨y, y'⟩
    simp only [tensorProductCoeff_apply, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
      N.coeff_mul_idem, N'.coeff_mul_idem]
    split_ifs with h h' <;> subst_vars <;> simp [(hιA _).eq, (hιB _).eq]
  map_coeff_add_coeff_mul_coeff := by
    rw [map_tensorProductCoeff_add_tensorProductCoeff_mul_tensorProductCoeff N N' hιA hιB hdA hdB,
      N.map_coeff_add_coeff_mul_coeff, N'.map_coeff_add_coeff_mul_coeff,
      Matrix.zero_kroneckerTMul, Matrix.kroneckerTMul_zero, add_zero]

section TensorProduct

variable [CharP R 2] (hιA : ∀ s, IsIdempotentElem (ιA s)) (hιB : ∀ t, IsIdempotentElem (ιB t))
  (hdA : ∀ s, dA (ιA s) = 0) (hdB : ∀ t, dB (ιB t) = 0)

@[simp]
theorem tensorProduct_idem (N : TypeDStructure dA ιA X) (N' : TypeDStructure dB ιB X')
    (p : X × X') : (N.tensorProduct N' hιA hιB hdA hdB).idem p = (N.idem p.1, N'.idem p.2) :=
  (rfl)

@[simp]
theorem tensorProduct_coeff (N : TypeDStructure dA ιA X) (N' : TypeDStructure dB ιB X') :
    (N.tensorProduct N' hιA hιB hdA hdB).coeff = tensorProductCoeff N N' :=
  (rfl)

variable {X₂ X₂' : Type*} [Fintype X₂] [Fintype X₂'] [DecidableEq X₂] [DecidableEq X₂']
  {N : TypeDStructure dA ιA X} {N' : TypeDStructure dB ιB X'}
  {N₂ : TypeDStructure dA ιA X₂} {N₂' : TypeDStructure dB ιB X₂'}

variable (N N') in
/-- The identity morphism of an exterior tensor product is the Kronecker product of the identity
morphisms. -/
theorem idMorphism_tensorProduct :
    (N.tensorProduct N' hιA hιB hdA hdB).idMorphism = N.idMorphism ⊗ₖₜ[R] N'.idMorphism := by
  ext ⟨x, x'⟩ ⟨y, y'⟩
  simp only [idMorphism_apply, Prod.mk.injEq, tensorProduct_idem, Matrix.kroneckerTMul_apply]
  by_cases hx : x = y <;> by_cases hx' : x' = y' <;> simp [hx, hx']

/-- **Kronecker products of morphisms are morphisms** of exterior tensor products. -/
theorem kroneckerTMul_mem_morphisms {F : Matrix X X₂ A} {G : Matrix X' X₂' B}
    (hF : F ∈ morphisms N N₂) (hG : G ∈ morphisms N' N₂') :
    F ⊗ₖₜ[R] G ∈
      morphisms (N.tensorProduct N' hιA hιB hdA hdB) (N₂.tensorProduct N₂' hιA hιB hdA hdB) := by
  refine mem_morphisms_iff.2 fun ⟨x, x'⟩ ⟨y, y'⟩ => ?_
  simp only [tensorProduct_idem, Matrix.kroneckerTMul_apply, Algebra.TensorProduct.tmul_mul_tmul]
  have hF := mem_morphisms_iff.1 hF x y
  have hG := mem_morphisms_iff.1 hG x' y'
  exact ⟨by rw [hF.1, hG.1], by rw [hF.2, hG.2]⟩

/-- **The Leibniz rule for exterior tensor products of morphisms.** For morphisms `F` from `N` to
`N₂` and `G` from `N'` to `N₂'`, the morphism differential of `F ⊗ G` is `∂F ⊗ G + F ⊗ ∂G`.
The identities of the factors act as units on `F` and `G`, which is what separates the four
terms of `Δ₂` and `Δ₁` into the two factors. -/
theorem morphismDifferential_tensorProduct_kroneckerTMul {F : Matrix X X₂ A}
    {G : Matrix X' X₂' B} (hF : F ∈ morphisms N N₂) (hG : G ∈ morphisms N' N₂') :
    morphismDifferential (N.tensorProduct N' hιA hιB hdA hdB)
        (N₂.tensorProduct N₂' hιA hιB hdA hdB) (F ⊗ₖₜ[R] G) =
      morphismDifferential N N₂ F ⊗ₖₜ[R] G + F ⊗ₖₜ[R] morphismDifferential N' N₂' G := by
  have hadd (P Q : Matrix X X₂ A) : (P + Q) ⊗ₖₜ[R] G = P ⊗ₖₜ[R] G + Q ⊗ₖₜ[R] G :=
    Matrix.kroneckerMap_add_left _ TensorProduct.add_tmul _ _ _
  simp only [morphismDifferential_apply, tensorProduct_coeff, tensorProductCoeff_def,
    Matrix.kroneckerTMul_map_ungradedTensorDifferential, Matrix.mul_add, Matrix.add_mul,
    ← Matrix.mul_kroneckerTMul_mul, mul_idMorphism hF, mul_idMorphism hG, idMorphism_mul hF,
    idMorphism_mul hG, hadd, Matrix.kroneckerTMul_add]
  abel

/-- Exterior tensor products of homomorphisms of type `D` structures are homomorphisms. -/
theorem morphismDifferential_tensorProduct_kroneckerTMul_eq_zero {F : Matrix X X₂ A}
    {G : Matrix X' X₂' B} (hF : F ∈ morphisms N N₂) (hG : G ∈ morphisms N' N₂')
    (hF' : morphismDifferential N N₂ F = 0) (hG' : morphismDifferential N' N₂' G = 0) :
    morphismDifferential (N.tensorProduct N' hιA hιB hdA hdB)
        (N₂.tensorProduct N₂' hιA hιB hdA hdB) (F ⊗ₖₜ[R] G) = 0 := by
  rw [morphismDifferential_tensorProduct_kroneckerTMul hιA hιB hdA hdB hF hG, hF', hG',
    Matrix.zero_kroneckerTMul, Matrix.kroneckerTMul_zero, add_zero]

variable (N N') in
/-- **Exterior tensor products of bounded type `D` structures.** If the coefficients of `N`
strictly increase a height function `h` and those of `N'` strictly increase `h'`, then the
coefficients of `N ⊗ N'` strictly increase `h + h'`, so `N ⊗ N'` is bounded. -/
theorem isBounded_tensorProduct_of_lt (h : X → ℕ) (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y)
    (h' : X' → ℕ) (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) :
    (N.tensorProduct N' hιA hιB hdA hdB).IsBounded := by
  refine (N.tensorProduct N' hιA hιB hdA hdB).isBounded_of_lt (fun p => h p.1 + h' p.2)
    fun ⟨x, x'⟩ ⟨y, y'⟩ hne => ?_
  rw [tensorProduct_coeff, tensorProductCoeff_apply] at hne
  by_contra hlt
  dsimp only at hlt
  -- Each of the two terms of the coefficient would increase the total height.
  have h₁ : N.coeff x y ⊗ₜ[R] (if x' = y' then ιB (N'.idem x') else 0) = 0 := by
    split_ifs with hx'
    · subst hx'
      by_cases hc : N.coeff x y = 0
      · rw [hc, TensorProduct.zero_tmul]
      · exact absurd (by have := hh x y hc; omega) hlt
    · exact TensorProduct.tmul_zero _ _
  have h₂ : (if x = y then ιA (N.idem x) else 0) ⊗ₜ[R] N'.coeff x' y' = 0 := by
    split_ifs with hx
    · subst hx
      by_cases hc : N'.coeff x' y' = 0
      · rw [hc, TensorProduct.tmul_zero]
      · exact absurd (by have := hh' x' y' hc; omega) hlt
    · exact TensorProduct.zero_tmul _ _
  exact hne (by rw [h₁, h₂, add_zero])

end TensorProduct

end TypeDStructure

end TauCeti

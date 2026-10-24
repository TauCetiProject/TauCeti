/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Semisimple.Multiplicity
-- Private: `dualTensorHom_bijective` supplies the finite family `∑ᵢ φᵢ(t) vᵢ = t` used only inside
-- the proof of bijectivity.
import Mathlib.LinearAlgebra.Contraction

/-!
# Modules over an algebra acting on `S` as all of `End S`

Let `k` be a commutative ring, `S` a finite projective `k`-module, and `A` a `k`-algebra acting on
`S` so that the action map `Algebra.lsmul k k S : A →ₐ[k] Module.End k S` is bijective: `A` *is*
the endomorphism algebra of `S`. This is the situation of an irreducible module over a central
simple algebra that is split, for instance of the spinor module `S` of an even-dimensional
complex Clifford algebra `Cℓ(V) ≃ End(S)`.

Then every `A`-module `M` is `S` tensored with its **multiplicity space** `S →ₗ[A] M`: evaluation

`TauCeti.isotypicEval k : S ⊗[k] (S →ₗ[A] M) →ₗ[A] M`,  `s ⊗ T ↦ T s`,

is an isomorphism of `A`-modules (`TauCeti.isotypicTensorEquivOfBijective`). Nothing is assumed
of `M`: it need not be finite, free or semisimple, and `k` need not be a field. Nor is `S` asked
to be nonzero: for `S = 0` the algebra `A` is zero and so is every `A`-module. This is one half
of the Morita correspondence for `S`: the counit `S ⊗[k] (S →ₗ[A] M) → M` is an isomorphism; the
unit `X → S →ₗ[A] (S ⊗[k] X)` is not treated here. When `S` is also a generator (for instance
nonzero over a field), the two functors `X ↦ S ⊗[k] X` and `M ↦ S →ₗ[A] M` give a Morita
equivalence between `k` and `End_k S`.

The inverse is explicit. A linear form `φ` on `S` and a vector `x : M` give the `A`-linear map
`TauCeti.homOfDual h φ x : S →ₗ[A] M` sending `s` to `a • x`, where `a ∈ A` acts on `S` as the
rank-one endomorphism `t ↦ φ t • s`. For a basis `(eᵢ)` of `S` with coordinate forms `(eᵢ*)` these
are matrix units, and the inverse of evaluation is `x ↦ ∑ᵢ eᵢ ⊗ homOfDual h eᵢ* x`
(`TauCeti.isotypicTensorEquivOfBijective_symm_apply_basis`). The identity behind both inverse
laws is `homOfDual h φ (T s) = φ s • T` for every `A`-linear `T`
(`TauCeti.homOfDual_apply_map`), the matrix-unit relation `Eᵢⱼ T(eⱼ) = T(eᵢ)`.

## Main definitions

* `TauCeti.homOfDual`: the element of the multiplicity space attached to a linear form on `S`
  and a vector of `M`.
* `TauCeti.isotypicTensorEquivOfBijective`: **evaluation** `S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] M`.

## Main results

* `TauCeti.isotypicEval_bijective_of_bijective_lsmul`: evaluation is bijective.
* `TauCeti.isotypicTensorEquivOfBijective_symm_apply` and
  `TauCeti.isotypicTensorEquivOfBijective_symm_apply_basis`: the inverse, for a finite family
  `∑ᵢ φᵢ(t) vᵢ = t` and for a finite basis.
* `TauCeti.isotypicTensorEquivOfBijective_symm_apply_map`: naturality of the inverse in `M`;
  naturality of evaluation itself is `TauCeti.isotypicEval_map_apply`.
* `TauCeti.finrank_eq_finrank_mul_finrank_linearMap_of_bijective_lsmul`: over a field,
  `dim M = dim S · dim (S →ₗ[A] M)`.

## Implementation notes

Evaluation is the map `TauCeti.isotypicEval` already used for isotypic components of semisimple
modules, where its injectivity is proved for `S` simple and finite-dimensional over an
algebraically closed field (`TauCeti.isotypicEval_injective`). Here the hypothesis on `A` replaces
these assumptions, and the inverse is written down directly: a finite projective
`S` has a finite family with `∑ᵢ φᵢ(t) vᵢ = t`, because the identity of `S` lies in the range of
Mathlib's `dualTensorHom` (`dualTensorHom_bijective`).

## References

* T. Y. Lam, *Lectures on Modules and Rings*, GTM 189 (1999), Chapter 7.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

namespace TauCeti

open Module TensorProduct

section CommRing

variable {k A S M N : Type*} [CommRing k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable (h : Function.Bijective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))

/-! ### The matrix units attached to linear forms -/

/-- The element of `A` acting as an endomorphism `f` of `S` acts on a vector by `f`. -/
@[simp]
theorem ofBijective_lsmul_symm_smul (f : Module.End k S) (s : S) :
    (AlgEquiv.ofBijective _ h).symm f • s = f s := by
  conv_rhs => rw [← (AlgEquiv.ofBijective _ h).apply_symm_apply f]
  rw [AlgEquiv.ofBijective_apply, Algebra.lsmul_apply]

/-- For `A ≅ End_k S`, a linear form `φ` on `S` and a vector `x : M`, the `A`-linear map
`S →ₗ[A] M` sending `s` to `a • x`, where `a ∈ A` acts on `S` as the rank-one endomorphism
`t ↦ φ t • s`. For a basis of `S` and `φ` a coordinate form, these elements of `A` are matrix
units, and `homOfDual` assembles the inverse of evaluation. -/
noncomputable def homOfDual (φ : Dual k S) : M →ₗ[k] S →ₗ[A] M where
  toFun x :=
    { toFun := fun s ↦ (AlgEquiv.ofBijective _ h).symm (φ.smulRight s) • x
      map_add' := fun s t ↦ by
        rw [← LinearMap.smulRightₗ_apply, (LinearMap.smulRightₗ φ).map_add,
          LinearMap.smulRightₗ_apply, LinearMap.smulRightₗ_apply, map_add, add_smul]
      map_smul' := fun a s ↦ by
        -- The rank-one endomorphism `t ↦ φ t • a • s` is `a` composed with `t ↦ φ t • s`.
        have : (AlgEquiv.ofBijective _ h).symm (φ.smulRight (a • s)) =
            a * (AlgEquiv.ofBijective _ h).symm (φ.smulRight s) := by
          apply (AlgEquiv.ofBijective _ h).injective
          rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
          ext t
          simp [AlgEquiv.ofBijective_apply, smul_comm (φ t) a s]
        rw [this, mul_smul, RingHom.id_apply] }
  map_add' x y := by ext; simp [smul_add]
  map_smul' c x := by ext; simp [smul_comm _ c x]

/-- The value of `homOfDual h φ x` at `s` is `x` acted on by the preimage in `A` of the rank-one
endomorphism `t ↦ φ t • s`. -/
@[simp]
theorem homOfDual_apply_apply (φ : Dual k S) (x : M) (s : S) :
    homOfDual h φ x s = (AlgEquiv.ofBijective _ h).symm (φ.smulRight s) • x :=
  (rfl)

/-- **The matrix-unit relation.** On a value of an `A`-linear map `T`, `homOfDual` returns `T`
itself, scaled by `φ s`; for a basis `(eᵢ)` this is `Eᵢⱼ T(eⱼ) = T(eᵢ)`. -/
@[simp]
theorem homOfDual_apply_map (φ : Dual k S) (T : S →ₗ[A] M) (s : S) :
    homOfDual h φ (T s) = φ s • T := by
  ext t
  rw [homOfDual_apply_apply, ← T.map_smul, ofBijective_lsmul_symm_smul, LinearMap.smulRight_apply,
    LinearMap.smul_apply, LinearMap.map_smul_of_tower]

/-! ### Evaluation is an isomorphism -/

/-- The candidate inverse of evaluation attached to a family `∑ᵢ φᵢ(t) vᵢ = t`. -/
private noncomputable def isotypicEvalInv {ι : Type*} (s : Finset ι) (φ : ι → Dual k S)
    (v : ι → S) : M →ₗ[k] S ⊗[k] (S →ₗ[A] M) :=
  ∑ i ∈ s, TensorProduct.mk k S (S →ₗ[A] M) (v i) ∘ₗ homOfDual h (φ i)

private theorem isotypicEval_isotypicEvalInv {ι : Type*} (s : Finset ι) (φ : ι → Dual k S)
    (v : ι → S) (hv : ∀ t, ∑ i ∈ s, φ i t • v i = t) (x : M) :
    isotypicEval k (isotypicEvalInv h s φ v x) = x := by
  -- The rank-one endomorphisms `t ↦ φᵢ t • vᵢ` sum to the identity.
  have hsum : ∑ i ∈ s, (AlgEquiv.ofBijective _ h).symm ((φ i).smulRight (v i)) = 1 := by
    apply (AlgEquiv.ofBijective _ h).injective
    rw [map_sum, map_one]
    ext t
    simp [hv t]
  simp only [isotypicEvalInv, LinearMap.sum_apply, LinearMap.comp_apply,
    TensorProduct.mk_apply, map_sum, isotypicEval_tmul, homOfDual_apply_apply, ← Finset.sum_smul,
    hsum, one_smul]

private theorem isotypicEvalInv_isotypicEval {ι : Type*} (s : Finset ι) (φ : ι → Dual k S)
    (v : ι → S) (hv : ∀ t, ∑ i ∈ s, φ i t • v i = t) (y : S ⊗[k] (S →ₗ[A] M)) :
    isotypicEvalInv h s φ v (isotypicEval k y) = y := by
  induction y using TensorProduct.inductionOn with
  | tmul t T =>
    simp only [isotypicEvalInv, LinearMap.sum_apply, LinearMap.comp_apply,
      TensorProduct.mk_apply, isotypicEval_tmul, homOfDual_apply_map, ← TensorProduct.smul_tmul,
      ← TensorProduct.sum_tmul, hv t]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

include h in
/-- **Evaluation is bijective** when `A` acts on the finite projective module `S` as the whole
endomorphism algebra `End_k S`: every `A`-module `M` is `S ⊗[k] (S →ₗ[A] M)`. -/
theorem isotypicEval_bijective_of_bijective_lsmul [Module.Finite k S] [Module.Projective k S] :
    Function.Bijective (isotypicEval k (A := A) (S := S) (M := M)) := by
  -- The identity of `S` lies in the range of `dualTensorHom`, which gives a finite family
  -- `∑ᵢ φᵢ(t) vᵢ = t`.
  obtain ⟨u, hu⟩ := (dualTensorHom_bijective (R := k) (M := S) (N := S)).2 LinearMap.id
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset u
  have hs (t : S) : ∑ p ∈ s, p.1 t • p.2 = t := by
    simpa [dualTensorHom_apply] using LinearMap.congr_fun hu t
  exact ⟨Function.LeftInverse.injective (isotypicEvalInv_isotypicEval h s _ _ hs),
    Function.RightInverse.surjective (isotypicEval_isotypicEvalInv h s _ _ hs)⟩

variable [Module.Finite k S] [Module.Projective k S]

/-- **Every module over `A ≅ End_k S` is `S` tensored with its multiplicity space.** Evaluation
`s ⊗ T ↦ T s` is an isomorphism of `A`-modules `S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] M`, with `A` acting on
the left factor. -/
noncomputable def isotypicTensorEquivOfBijective : S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] M :=
  .ofBijective (isotypicEval k) (isotypicEval_bijective_of_bijective_lsmul h)

/-- The equivalence is evaluation, `s ⊗ T ↦ T s`. -/
@[simp]
theorem isotypicTensorEquivOfBijective_apply (x : S ⊗[k] (S →ₗ[A] M)) :
    isotypicTensorEquivOfBijective h x = isotypicEval k x :=
  (rfl)

/-- **The inverse of evaluation**, for any finite family with `∑ᵢ φᵢ(t) vᵢ = t`. -/
theorem isotypicTensorEquivOfBijective_symm_apply {ι : Type*} (s : Finset ι) (φ : ι → Dual k S)
    (v : ι → S) (hv : ∀ t, ∑ i ∈ s, φ i t • v i = t) (x : M) :
    (isotypicTensorEquivOfBijective h).symm x = ∑ i ∈ s, v i ⊗ₜ homOfDual h (φ i) x := by
  rw [LinearEquiv.symm_apply_eq, isotypicTensorEquivOfBijective_apply]
  exact (isotypicEval_isotypicEvalInv h s φ v hv x).symm.trans (by simp [isotypicEvalInv])

/-- **The inverse of evaluation in a basis** `(eᵢ)` of `S`: `x ↦ ∑ᵢ eᵢ ⊗ homOfDual h eᵢ* x`. -/
theorem isotypicTensorEquivOfBijective_symm_apply_basis {ι : Type*} [Fintype ι]
    (b : Basis ι k S) (x : M) :
    (isotypicTensorEquivOfBijective h).symm x = ∑ i, b i ⊗ₜ homOfDual h (b.coord i) x :=
  isotypicTensorEquivOfBijective_symm_apply h Finset.univ b.coord b
    (fun t ↦ by simp [Basis.coord_apply]) x

/-- **Naturality of the inverse**: through the decomposition an `A`-linear map
`g : M →ₗ[A] N` becomes `1 ⊗ (g ∘ ·)`. -/
@[simp]
theorem isotypicTensorEquivOfBijective_symm_apply_map (g : M →ₗ[A] N) (y : M) :
    (isotypicTensorEquivOfBijective h (M := N)).symm (g y) =
      AlgebraTensorModule.map (LinearMap.id (R := A) (M := S))
        (LinearMap.compRight (M := S) k g) ((isotypicTensorEquivOfBijective h).symm y) := by
  apply (isotypicTensorEquivOfBijective h (M := N)).injective
  rw [LinearEquiv.apply_symm_apply, isotypicTensorEquivOfBijective_apply, isotypicEval_map_apply,
    ← isotypicTensorEquivOfBijective_apply h, LinearEquiv.apply_symm_apply]

end CommRing

section Field

variable {k A S M : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [FiniteDimensional k S]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- **The dimension of a module over `A ≅ End_k S`** is the dimension of `S` times that of its
multiplicity space. -/
theorem finrank_eq_finrank_mul_finrank_linearMap_of_bijective_lsmul
    (h : Function.Bijective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S)) :
    finrank k M = finrank k S * finrank k (S →ₗ[A] M) := by
  rw [← ((isotypicTensorEquivOfBijective h (M := M)).restrictScalars k).finrank_eq,
    finrank_tensorProduct]

end Field

end TauCeti

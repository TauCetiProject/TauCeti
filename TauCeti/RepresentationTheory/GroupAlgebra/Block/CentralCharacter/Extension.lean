/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.CenterMap
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.CentralCharacter

/-!
# Central characters under scalar extension

Let `f : k →+* k'` be a homomorphism of fields and `G` a finite group. Every `k`-algebra
homomorphism `λ : Z(k[G]) → k`, for instance the central character `λ_B` of a block, extends to a
`k'`-algebra homomorphism `λ' : Z(k'[G]) → k'` with `λ'(x) = f(λ(x))` on the image of `Z(k[G])`:
`λ'` takes the value `f(λ(K_C))` at the class sum `K_C`. It is multiplicative because the products
of class sums of `k'[G]` are the images of those of `k[G]`. This is the statement of the scalar
extension of ModularCharactersAndBlocks §6.2 that the central character over `k'` extends `λ_b`.

The construction is an instance of a general one: a `k`-algebra homomorphism `A → k` extends along
a ring homomorphism `F : A → A'`, compatible with `f` on scalars, that carries a `k`-basis of `A` to
a `k'`-basis of `A'` (`TauCeti.exists_algHom_comp_eq_of_basis`).

## Main results

* `TauCeti.exists_algHom_comp_eq_of_basis`: the general extension.
* `TauCeti.exists_algHom_centerMapRingHom`: for `f : k →+* k'` and `λ : Z(k[G]) →ₐ[k] k`, there
  is `λ' : Z(k'[G]) →ₐ[k'] k'` with `λ'(f_* x) = f(λ(x))`.
-/

public section

namespace TauCeti

section Basis

variable {k k' A A' ι : Type*} [Field k] [Field k'] [CommRing A] [Algebra k A] [CommRing A']
  [Algebra k' A']

/-- **Extending a character along a basis-preserving map.** Let `f : k →+* k'` be a homomorphism of
fields, `F : A →+* A'` a ring homomorphism of commutative algebras with
`F(algebraMap r) = algebraMap (f r)`, carrying a `k`-basis `v` of `A` to a `k'`-basis `v'` of `A'`.
Every `k`-algebra homomorphism `φ : A → k` extends to a `k'`-algebra homomorphism `φ' : A' → k'`
with `φ'(F x) = f(φ(x))`: `φ'` takes the value `f(φ(v i))` at `v' i`. -/
theorem exists_algHom_comp_eq_of_basis (f : k →+* k') (F : A →+* A')
    (hF : ∀ r, F (algebraMap k A r) = algebraMap k' A' (f r)) (v : Module.Basis ι k A)
    (v' : Module.Basis ι k' A') (hv : ∀ i, F (v i) = v' i) (φ : A →ₐ[k] k) :
    ∃ φ' : A' →ₐ[k'] k', ∀ x, φ' (F x) = f (φ x) := by
  classical
  let ψ : A' →ₗ[k'] k' := v'.constr k' fun i => f (φ (v i))
  have hψv (i : ι) : ψ (v' i) = f (φ (v i)) := v'.constr_basis k' _ i
  -- `ψ ∘ F = f ∘ φ`, checked on `x = ∑ᵢ xᵢ v i`, the sum being finite.
  have hψF (x : A) : ψ (F x) = f (φ x) := by
    have hFs (c : k) (a : A) : F (c • a) = f c • F a := by
      rw [Algebra.smul_def, map_mul, hF, Algebra.smul_def]
    rw [← v.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
      map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFs, hv, map_smul, hψv, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  have hmul : ∀ x y, ψ (x * y) = ψ x * ψ y := by
    -- Both sides are `k'`-bilinear in `(x, y)`; compare them on the basis `v'`.
    have h := v'.ext fun i => v'.ext fun j => (show
      ((LinearMap.mul k' A').compr₂ ψ) (v' i) (v' j) =
        ((LinearMap.mul k' k').compl₁₂ ψ ψ) (v' i) (v' j) by
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply']
      rw [← hv, ← hv, ← map_mul, hψF, hψF, hψF, map_mul, map_mul])
    exact fun x y => LinearMap.congr_fun₂ h x y
  have hone : ψ 1 = 1 := by
    rw [← map_one F, hψF, map_one, map_one]
  exact ⟨AlgHom.ofLinearMap ψ hone hmul, hψF⟩

end Basis

open _root_.MonoidAlgebra

variable {k k' G : Type*} [Field k] [Field k'] [Group G] [Finite G]

/-- **Central characters extend along scalar extension.** For a homomorphism of fields
`f : k →+* k'`, every `k`-algebra homomorphism `λ : Z(k[G]) → k`, for instance the central
character of a block, extends to a `k'`-algebra homomorphism `λ' : Z(k'[G]) → k'` with
`λ'(f_* x) = f(λ(x))` for the induced map `f_* : Z(k[G]) → Z(k'[G])`. -/
theorem exists_algHom_centerMapRingHom (f : k →+* k')
    (φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k) :
    ∃ φ' : Subalgebra.center k' (MonoidAlgebra k' G) →ₐ[k'] k',
      ∀ x, φ' (centerMapRingHom G f x) = f (φ x) := by
  classical
  have := Fintype.ofFinite G
  exact exists_algHom_comp_eq_of_basis f (centerMapRingHom G f) (centerMapRingHom_algebraMap G f)
    classSumBasis classSumBasis (fun C => by
      rw [classSumBasis_apply, classSumBasis_apply, centerMapRingHom_classSumCenter]) φ

end TauCeti

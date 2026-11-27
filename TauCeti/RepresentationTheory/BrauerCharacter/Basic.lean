/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.Charpoly
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.LinearAlgebra.Eigenspace.Split
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis
import TauCeti.LinearAlgebra.End.FiniteOrder
import TauCeti.RingTheory.Polynomial.Roots

/-!
# Brauer characters

Let `k` be a field and `m` a positive integer, and fix an isomorphism
`τ : rootsOfUnity m k ≃* rootsOfUnity m L` onto the `m`-th roots of unity of a commutative ring
`L` (the case of interest is `L = ℂ`, with `k` of characteristic `p`, `p ∤ m` and `k` containing
a primitive `m`-th root of unity). The **Brauer character** `ρ.brauerCharacter p τ` of a
representation `ρ` of a group `G` on a finite-dimensional `k`-vector space takes, at a `p`-regular
`g` (an element of order prime to `p`), the value `∑ τ(λ)`, the sum over the roots `λ` of the
characteristic polynomial of `ρ g` counted with multiplicity, and the value `0` at the other
elements. A root that is not an `m`-th root of unity contributes `0`
(`TauCeti.rootsOfUnityLift`); when the order of `g` divides `m`, every root is an `m`-th root of
unity, so this convention is never used there.

When the order of `g` divides `m` and `k` contains a primitive `m`-th root of unity, `ρ g` is
diagonalizable over `k` itself (`Module.End.iSup_eigenspace_eq_top_of_pow_eq_one`): it is
annihilated by `X ^ m - 1`, which splits into distinct linear factors. In an eigenbasis the
Brauer character is the sum of the `τ`-lifts of the eigenvalues, and the tensor product formula
follows from the tensor product of eigenbases.

## Main definitions

* `TauCeti.rootsOfUnityLift τ`: the function `k → L` that is `τ` on the `m`-th roots of unity and
  `0` elsewhere.
* `Representation.brauerCharacter p τ ρ`: the Brauer character of `ρ`.

## Main results

* `Representation.brauerCharacter_one`: the value at `1` is the dimension.
* `Representation.Equiv.brauerCharacter_eq`, `Representation.brauerCharacter_conj`: invariance
  under isomorphism and conjugation.
* `Representation.brauerCharacter_eq_subrepresentation_add_quotient`: additivity on an invariant
  subspace and its quotient; `Representation.brauerCharacter_prod` on direct sums.
* `Representation.brauerCharacter_dual`: the Brauer character of the dual is `g ↦ φ(g⁻¹)`.
* `Representation.brauerCharacter_comp`: restriction and inflation along a homomorphism at
  `p`-regular elements; `Representation.brauerCharacter_comp_of_injective` at every element along
  an injective homomorphism.
* `Representation.brauerCharacter_ofLinearCharacter`: the Brauer character of a one-dimensional
  representation is the lift of its character.
* `Representation.brauerCharacter_eq_sum_of_apply_eq_smul`,
  `Representation.exists_brauerCharacter_eq_sum`: in an eigenbasis the Brauer character is the
  sum of the lifted eigenvalues, so its values are sums of `dim V` roots of unity of `L`.
* `Representation.brauerCharacter_tprod`: when `k` contains a primitive `m`-th root of unity,
  the Brauer character of a tensor product is the product at every element of order dividing `m`.
* `Representation.brauerCharacter_eq_of_dvd`: compatibility with a change of `m` to a multiple and
  of `τ` to an isomorphism that agrees with it on the `m`-th roots of unity.
* `Representation.brauerCharacter_baseChange`: when `k` contains a primitive `m`-th root of
  unity, invariance under scalar extension to `k'` with an isomorphism `τ'` compatible with `τ`, at
  every element of order dividing `m`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, 2016, §10.1, p. 170, and
  Proposition 10.1.3, pp. 170–171.
* J. M. Martínez, *Modular representation theory of finite groups*, course notes, Firenze 2024,
  Lecture 1.
-/

public section

open Module Polynomial

namespace TauCeti

variable {k L : Type*} [CommMonoid k] [CommMonoidWithZero L] {m : ℕ} [NeZero m]

open Classical in
/-- The lift of an element of `k` along `τ : rootsOfUnity m k ≃* rootsOfUnity m L`: the image
under `τ` of an `m`-th root of unity, and `0` for an element that is not an `m`-th root of
unity. -/
noncomputable def rootsOfUnityLift (τ : rootsOfUnity m k ≃* rootsOfUnity m L) (x : k) : L :=
  if h : x ^ m = 1 then ((τ (rootsOfUnity.mkOfPowEq x h) : Lˣ) : L) else 0

variable (τ : rootsOfUnity m k ≃* rootsOfUnity m L)

/-- An `m`-th root of unity lifts to its image under `τ`. -/
theorem rootsOfUnityLift_of_pow_eq_one {x : k} (h : x ^ m = 1) :
    rootsOfUnityLift τ x = ((τ (rootsOfUnity.mkOfPowEq x h) : Lˣ) : L) := by
  simp [rootsOfUnityLift, h]

/-- An element that is not an `m`-th root of unity lifts to `0`. -/
theorem rootsOfUnityLift_of_pow_ne_one {x : k} (h : x ^ m ≠ 1) : rootsOfUnityLift τ x = 0 := by
  simp [rootsOfUnityLift, h]

/-- An element of `rootsOfUnity m k` lifts to its image under `τ`. -/
@[simp]
theorem rootsOfUnityLift_coe (ζ : rootsOfUnity m k) :
    rootsOfUnityLift τ ((ζ : kˣ) : k) = ((τ ζ : Lˣ) : L) := by
  have h : ((ζ : kˣ) : k) ^ m = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity m _).1 ζ.property, Units.val_one]
  rw [rootsOfUnityLift_of_pow_eq_one τ h]
  congr 3
  ext
  rw [rootsOfUnity.coe_mkOfPowEq]

/-- The lift of `1` is `1`. -/
@[simp]
theorem rootsOfUnityLift_one : rootsOfUnityLift τ (1 : k) = 1 := by
  simpa using rootsOfUnityLift_coe τ 1

/-- The lift is multiplicative on `m`-th roots of unity. -/
theorem rootsOfUnityLift_mul {x y : k} (hx : x ^ m = 1) (hy : y ^ m = 1) :
    rootsOfUnityLift τ (x * y) = rootsOfUnityLift τ x * rootsOfUnityLift τ y := by
  have hxy : (x * y) ^ m = 1 := by rw [mul_pow, hx, hy, one_mul]
  rw [rootsOfUnityLift_of_pow_eq_one τ hx, rootsOfUnityLift_of_pow_eq_one τ hy,
    rootsOfUnityLift_of_pow_eq_one τ hxy, ← Units.val_mul, ← Subgroup.coe_mul, ← map_mul]
  congr 3
  ext
  simp

end TauCeti

namespace Representation

open TauCeti

variable {k L G V W : Type*} [Field k] [CommRing L] {m : ℕ} [NeZero m]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

section Monoid

variable [Monoid G]

open Classical in
/-- The **Brauer character** of a representation `ρ` of `G` on a finite-dimensional `k`-vector
space, for a prime `p` and an isomorphism `τ : rootsOfUnity m k ≃* rootsOfUnity m L`: at an
element `g` of order prime to `p`, the sum of the `τ`-lifts of the roots of the characteristic
polynomial of `ρ g`, counted with multiplicity; at the other elements, `0`. -/
noncomputable def brauerCharacter (p : ℕ) (τ : rootsOfUnity m k ≃* rootsOfUnity m L)
    (ρ : Representation k G V) (g : G) : L :=
  if p.Coprime (orderOf g) then ((ρ g).charpoly.roots.map (rootsOfUnityLift τ)).sum else 0

variable (p : ℕ) (τ : rootsOfUnity m k ≃* rootsOfUnity m L) (ρ : Representation k G V)
  (σ : Representation k G W)

/-- The Brauer character at a `p`-regular element. -/
theorem brauerCharacter_of_coprime {g : G} (hg : p.Coprime (orderOf g)) :
    ρ.brauerCharacter p τ g = ((ρ g).charpoly.roots.map (rootsOfUnityLift τ)).sum := by
  simp [brauerCharacter, hg]

/-- The Brauer character vanishes at an element whose order is not prime to `p`. -/
theorem brauerCharacter_of_not_coprime {g : G} (hg : ¬ p.Coprime (orderOf g)) :
    ρ.brauerCharacter p τ g = 0 := by
  simp [brauerCharacter, hg]

/-- The Brauer character at `1` is the dimension. -/
@[simp]
theorem brauerCharacter_one : ρ.brauerCharacter p τ 1 = finrank k V := by
  rw [brauerCharacter_of_coprime p τ ρ (by simp), map_one, LinearMap.charpoly_one, ← C_1,
    roots_pow, roots_X_sub_C]
  simp [Multiset.map_nsmul, Multiset.sum_nsmul]

variable {ρ σ} in
/-- Isomorphic representations have the same Brauer character. -/
theorem Equiv.brauerCharacter_eq (φ : ρ.Equiv σ) :
    ρ.brauerCharacter p τ = σ.brauerCharacter p τ := by
  ext g
  simp only [brauerCharacter, φ.charpoly_apply_eq]

/-- **Additivity.** The Brauer character of `ρ` is the sum of those of an invariant subspace and of
the quotient by it. -/
theorem brauerCharacter_eq_subrepresentation_add_quotient (U : Submodule k V)
    (le_comap : ∀ g, U ≤ U.comap (ρ g)) (g : G) :
    ρ.brauerCharacter p τ g = (ρ.subrepresentation U le_comap).brauerCharacter p τ g +
      (ρ.quotient U le_comap).brauerCharacter p τ g := by
  by_cases hg : p.Coprime (orderOf g)
  · simp only [brauerCharacter_of_coprime p τ _ hg]
    rw [ρ.charpoly_apply_eq_subrepresentation_mul_quotient U le_comap g,
      roots_mul ((LinearMap.charpoly_monic _).mul (LinearMap.charpoly_monic _)).ne_zero,
      Multiset.map_add, Multiset.sum_add]
  · simp [brauerCharacter_of_not_coprime p τ _ hg]

/-- The Brauer character of a direct sum is the sum of the Brauer characters. -/
@[simp]
theorem brauerCharacter_prod (g : G) :
    (ρ.prod σ).brauerCharacter p τ g = ρ.brauerCharacter p τ g + σ.brauerCharacter p τ g := by
  by_cases hg : p.Coprime (orderOf g)
  · simp only [brauerCharacter_of_coprime p τ _ hg]
    rw [charpoly_prod_apply,
      roots_mul ((LinearMap.charpoly_monic _).mul (LinearMap.charpoly_monic _)).ne_zero,
      Multiset.map_add, Multiset.sum_add]
  · simp [brauerCharacter_of_not_coprime p τ _ hg]

/-- **Restriction and inflation.** Along a homomorphism `f : H →* G`, the Brauer character of
`ρ ∘ f` at a `p`-regular element `h` is that of `ρ` at `f h`. -/
theorem brauerCharacter_comp {H : Type*} [Monoid H] (f : H →* G) {h : H}
    (hh : p.Coprime (orderOf h)) :
    brauerCharacter p τ (ρ.comp f) h = ρ.brauerCharacter p τ (f h) := by
  rw [brauerCharacter_of_coprime p τ _ hh,
    brauerCharacter_of_coprime p τ _ (hh.coprime_dvd_right (orderOf_map_dvd f h)),
    MonoidHom.coe_comp, Function.comp_apply]

/-- Along an injective homomorphism `f : H →* G`, for instance the inclusion of a subgroup, the
Brauer character of `ρ ∘ f` is the restriction of that of `ρ`. -/
theorem brauerCharacter_comp_of_injective {H : Type*} [Monoid H] (f : H →* G)
    (hf : Function.Injective f) (h : H) :
    brauerCharacter p τ (ρ.comp f) h = ρ.brauerCharacter p τ (f h) := by
  by_cases hh : p.Coprime (orderOf h)
  · exact brauerCharacter_comp p τ ρ f hh
  · rw [brauerCharacter_of_not_coprime p τ _ hh, brauerCharacter_of_not_coprime p τ _
      (by rwa [orderOf_injective f hf])]

/-- In a basis `b` of eigenvectors of `ρ g`, with `ρ g (b i) = d i • b i`, the Brauer character at
a `p`-regular `g` is the sum of the lifts of the eigenvalues `d i`. -/
theorem brauerCharacter_eq_sum_of_apply_eq_smul {ι : Type*} [Fintype ι] {g : G}
    (hg : p.Coprime (orderOf g)) (b : Basis ι k V) {d : ι → k}
    (hb : ∀ i, ρ g (b i) = d i • b i) :
    ρ.brauerCharacter p τ g = ∑ i, rootsOfUnityLift τ (d i) := by
  rw [brauerCharacter_of_coprime p τ ρ hg, LinearMap.roots_charpoly_of_apply_eq_smul b hb,
    Multiset.map_map, Function.comp_def, Finset.sum_map_val]

variable {ρ} in
/-- If the order of `g` divides `m` and `k` contains a primitive `m`-th root of unity, then `ρ g`
is diagonal in some basis, with eigenvalues `m`-th roots of unity. -/
theorem exists_basis_apply_eq_smul [HasEnoughRootsOfUnity k m] {g : G} (hgm : orderOf g ∣ m) :
    ∃ (b : Basis (Fin (finrank k V)) k V) (d : Fin (finrank k V) → k),
      (∀ i, ρ g (b i) = d i • b i) ∧ ∀ i, d i ^ m = 1 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k m
  exact Module.End.exists_basis_apply_eq_smul_of_pow_eq_one hζ
    (orderOf_dvd_iff_pow_eq_one.1 ((orderOf_map_dvd ρ g).trans hgm))

/-- The Brauer character of the one-dimensional representation of a character `χ : G →* kˣ`
at a `p`-regular `g` is the lift of `χ g`. -/
theorem brauerCharacter_ofLinearCharacter (χ : G →* kˣ) {g : G} (hg : p.Coprime (orderOf g)) :
    (ofLinearCharacter χ).brauerCharacter p τ g = rootsOfUnityLift τ (χ g : k) := by
  rw [brauerCharacter_eq_sum_of_apply_eq_smul p τ _ hg (Basis.singleton Unit k) (d := fun _ ↦ χ g)
    fun _ ↦ by simp, Finset.univ_unique, Finset.sum_singleton]

/-- **Values are sums of roots of unity.** If the order of `g` divides `m` and `k` contains a
primitive `m`-th root of unity, the Brauer character at a `p`-regular `g` is a sum of `dim V`
roots of unity of `L`. -/
theorem exists_brauerCharacter_eq_sum [HasEnoughRootsOfUnity k m] {g : G}
    (hg : p.Coprime (orderOf g)) (hgm : orderOf g ∣ m) :
    ∃ ζ : Fin (finrank k V) → rootsOfUnity m L,
      ρ.brauerCharacter p τ g = ∑ i, ((ζ i : Lˣ) : L) := by
  obtain ⟨b, d, hb, hd⟩ := exists_basis_apply_eq_smul (ρ := ρ) hgm
  refine ⟨fun i ↦ τ (rootsOfUnity.mkOfPowEq (d i) (hd i)), ?_⟩
  rw [brauerCharacter_eq_sum_of_apply_eq_smul p τ ρ hg b hb]
  exact Finset.sum_congr rfl fun i _ ↦ rootsOfUnityLift_of_pow_eq_one τ (hd i)

/-- **Compatibility with a change of `m` and `τ`.** Let `τ'` be an isomorphism for some `m'`, for
instance a multiple of `m`, that agrees with `τ` on the `m`-th roots of unity. At every element
whose order divides `m`, the Brauer characters for `τ` and for `τ'` agree. -/
theorem brauerCharacter_eq_of_dvd {m' : ℕ} [NeZero m']
    (τ' : rootsOfUnity m' k ≃* rootsOfUnity m' L)
    (hτ : ∀ x : k, x ^ m = 1 → rootsOfUnityLift τ' x = rootsOfUnityLift τ x) {g : G}
    (hgm : orderOf g ∣ m) : ρ.brauerCharacter p τ' g = ρ.brauerCharacter p τ g := by
  by_cases hg : p.Coprime (orderOf g)
  · rw [brauerCharacter_of_coprime p τ' ρ hg, brauerCharacter_of_coprime p τ ρ hg]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun x hx ↦
      hτ x (Module.End.pow_eq_one_of_isRoot_charpoly
        (orderOf_dvd_iff_pow_eq_one.1 ((orderOf_map_dvd ρ g).trans hgm)) (isRoot_of_mem_roots hx)))
  · rw [brauerCharacter_of_not_coprime p τ' ρ hg, brauerCharacter_of_not_coprime p τ ρ hg]

/-- **Invariance under scalar extension.** Let `k'` be a field extension of `k` and `τ'` an
isomorphism for `k'` that agrees with `τ` on the `m`-th roots of unity of `k`. If `k` contains a
primitive `m`-th root of unity, then at every element whose order divides `m`, the Brauer
character of the scalar extension `k' ⊗[k] V` for `τ'` is that of `V` for `τ`. -/
theorem brauerCharacter_baseChange [HasEnoughRootsOfUnity k m] (k' : Type*) [Field k']
    [Algebra k k'] (τ' : rootsOfUnity m k' ≃* rootsOfUnity m L)
    (hτ : ∀ x : k, x ^ m = 1 → rootsOfUnityLift τ' (algebraMap k k' x) = rootsOfUnityLift τ x)
    {g : G} (hgm : orderOf g ∣ m) :
    (ρ.baseChange k').brauerCharacter p τ' g = ρ.brauerCharacter p τ g := by
  by_cases hg : p.Coprime (orderOf g)
  · obtain ⟨b, d, hb, hd⟩ := exists_basis_apply_eq_smul (ρ := ρ) hgm
    rw [brauerCharacter_of_coprime p τ' _ hg, baseChange_apply, LinearMap.charpoly_baseChange,
      LinearMap.charpoly_eq_prod_of_apply_eq_smul b hb, Polynomial.map_prod,
      brauerCharacter_eq_sum_of_apply_eq_smul p τ ρ hg b hb]
    simp only [Polynomial.map_sub, map_X, map_C]
    rw [roots_prod_X_sub_C_map, Multiset.map_map]
    exact Finset.sum_congr rfl fun i _ ↦ hτ _ (hd i)
  · rw [brauerCharacter_of_not_coprime p τ' _ hg, brauerCharacter_of_not_coprime p τ ρ hg]

/-- **Tensor products.** If `k` contains a primitive `m`-th root of unity, then at every element
whose order divides `m`, the Brauer character of `ρ ⊗ σ` is the product of those of `ρ` and
`σ`. -/
theorem brauerCharacter_tprod [HasEnoughRootsOfUnity k m] {g : G} (hgm : orderOf g ∣ m) :
    (ρ.tprod σ).brauerCharacter p τ g = ρ.brauerCharacter p τ g * σ.brauerCharacter p τ g := by
  by_cases hg : p.Coprime (orderOf g)
  · obtain ⟨b, d, hb, hd⟩ := exists_basis_apply_eq_smul (ρ := ρ) hgm
    obtain ⟨c, e, hc, he⟩ := exists_basis_apply_eq_smul (ρ := σ) hgm
    rw [brauerCharacter_eq_sum_of_apply_eq_smul p τ ρ hg b hb,
      brauerCharacter_eq_sum_of_apply_eq_smul p τ σ hg c hc,
      brauerCharacter_eq_sum_of_apply_eq_smul p τ (ρ.tprod σ) hg (b.tensorProduct c)
        (d := fun x ↦ d x.1 * e x.2) (fun x ↦ by
          rw [tprod_apply, Basis.tensorProduct_apply', TensorProduct.map_tmul, hb, hc,
            TensorProduct.smul_tmul_smul]),
      Fintype.sum_prod_type, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      rootsOfUnityLift_mul τ (hd i) (he j)
  · simp [brauerCharacter_of_not_coprime p τ _ hg]

end Monoid

section Group

variable [Group G] (p : ℕ) (τ : rootsOfUnity m k ≃* rootsOfUnity m L) (ρ : Representation k G V)

/-- The Brauer character is constant on conjugacy classes. -/
@[simp]
theorem brauerCharacter_conj (g h : G) :
    ρ.brauerCharacter p τ (g * h * g⁻¹) = ρ.brauerCharacter p τ h := by
  have ho : orderOf (g * h * g⁻¹) = orderOf h := by
    simpa [MulAut.conj_apply] using
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective h
  simp only [brauerCharacter, ho, charpoly_apply_conj]

/-- **Duals.** The Brauer character of the contragredient representation is `g ↦ φ(g⁻¹)`. -/
@[simp]
theorem brauerCharacter_dual (g : G) :
    ρ.dual.brauerCharacter p τ g = ρ.brauerCharacter p τ g⁻¹ := by
  simp only [brauerCharacter, orderOf_inv, charpoly_dual_apply]

end Group

end Representation

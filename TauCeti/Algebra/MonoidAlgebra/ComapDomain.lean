/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# Pulling coefficients of a monoid algebra back along an injective map

For an injective map `f : M → N`, Mathlib's `MonoidAlgebra.comapDomain f hf : R[N] → R[M]` keeps
the coefficients of an element of `R[N]` at the points of the range of `f` and drops the others.
This file adds its interaction with the module structure and with `MonoidAlgebra.mapDomain`, and,
for an injective group homomorphism `φ : K →* G`, its interaction with multiplication.

Along `φ`, `comapDomain φ` is the *restriction to the subgroup* `Set.range φ`: it is a retraction of
`mapDomain φ`, and it is linear for the two-sided action of `R[K]` on `R[G]` through `mapDomain φ`.
Together with the monomials at a transversal of `Set.range φ` it decomposes every element of `R[G]`:
for a family `t` of representatives of the right cosets `Set.range φ * t i`,
`y = ∑ i, mapDomain φ (comapDomain φ (y * single (t i)⁻¹ 1)) * single (t i) 1`, and symmetrically
for the left cosets. These identities are what show that `R[G]` is free over `R[K]` on the coset
representatives with explicit coordinates, and they are the levelwise input for the same
statement about completed group algebras.

## Main results

* `MonoidAlgebra.comapDomain_smul`: `comapDomain` commutes with scalar multiplication.
* `MonoidAlgebra.comapDomain_mapDomain`: `comapDomain f` is a retraction of `mapDomain f`, with
  additive form `AddMonoidAlgebra.comapDomain_mapDomain`.
* `MonoidAlgebra.support_coeff_comapDomain_subset`,
  `MonoidAlgebra.comapDomain_mul_of_support_subset_range`,
  `MonoidAlgebra.comapDomain_dvd_comapDomain`: along an injective map, `comapDomain` pulls back
  support bounds `x.coeff.support ⊆ f '' s` to `s`, and for multiplicative/additive homomorphisms
  preserves products and factorisations of elements supported in `Set.range f` (with additive forms
  in `AddMonoidAlgebra`).
* `MonoidAlgebra.mapDomain_comapDomain_eq_comapDomain_mapDomain`: `comapDomain` commutes with
  `mapDomain` along a commutative square in which every point mapped into the range of one
  injection already lies in the range of the other.
* `MonoidAlgebra.comapDomain_mapDomain_mul`, `MonoidAlgebra.comapDomain_mul_mapDomain`: along an
  injective group homomorphism `φ`, `comapDomain φ` is linear for the left and right actions of
  the source group algebra through `mapDomain φ`. The left version only needs a monoid as target,
  and has the additive form `AddMonoidAlgebra.comapDomain_mapDomain_mul`.
* `MonoidAlgebra.sum_mapDomain_comapDomain_mul_single`,
  `MonoidAlgebra.sum_single_mul_mapDomain_comapDomain`: the decomposition of an element of `R[G]`
  along representatives of the right, respectively left, cosets of `Set.range φ`.
-/

public section

namespace MonoidAlgebra

variable {R : Type*} [Semiring R]

section Map

variable {M N : Type*}

/-- `comapDomain` commutes with scalar multiplication. -/
@[simp]
theorem comapDomain_smul {S : Type*} [SMulZeroClass S R] (f : M → N) (hf : f.Injective) (s : S)
    (x : MonoidAlgebra R N) : comapDomain f hf (s • x) = s • comapDomain f hf x :=
  ext <| by simp [Finsupp.comapDomain_smul_of_injective hf]

/-- Pulling back along an injective map the coefficients pushed forward along it recovers the
original element. -/
@[to_additive (dont_translate := R) (attr := simp)
/-- Pulling back along an injective map the coefficients pushed forward along it recovers the
original element. -/]
theorem comapDomain_mapDomain (f : M → N) (hf : f.Injective) (x : MonoidAlgebra R M) :
    comapDomain f hf (mapDomain f x) = x :=
  ext <| by rw [coeff_comapDomain, coeff_mapDomain, Finsupp.comapDomain_mapDomain _ hf]

/-- If `x` is supported on the image `f '' s` of an injective map `f`, then `comapDomain f hf x`
is supported on `s`. -/
@[to_additive (dont_translate := R)
/-- If `x` is supported on the image `f '' s` of an injective map `f`, then `comapDomain f hf x`
is supported on `s`. -/]
theorem support_coeff_comapDomain_subset {f : M → N} (hf : f.Injective)
    {x : MonoidAlgebra R N} {s : Set M} (hx : (x.coeff.support : Set N) ⊆ f '' s) :
    ((comapDomain f hf x).coeff.support : Set M) ⊆ s := by
  simpa only [coeff_comapDomain, Finsupp.comapDomain_support, Finset.coe_preimage,
    Set.preimage_image_eq _ hf] using Set.preimage_mono (f := f) hx

/-- Along an injective multiplicative map, `comapDomain` preserves products of elements supported in
its range. -/
@[to_additive (dont_translate := R)
/-- Along an injective additive map, `comapDomain` preserves products of elements supported in its
range. -/]
theorem comapDomain_mul_of_support_subset_range [Mul M] [Mul N] {F : Type*} [FunLike F M N]
    [MulHomClass F M N] {f : F} (hf : Function.Injective f) {x y : MonoidAlgebra R N}
    (hx : (x.coeff.support : Set N) ⊆ Set.range f)
    (hy : (y.coeff.support : Set N) ⊆ Set.range f) :
    comapDomain f hf (x * y) = comapDomain f hf x * comapDomain f hf y := by
  conv_lhs => rw [← mapDomain_comapDomain hx hf, ← mapDomain_comapDomain hy hf]
  rw [← mapDomain_mul, comapDomain_mapDomain]

/-- Along an injective monoid map `f`, if `y = x * z` with `x` and `z` supported in `Set.range f`,
then `comapDomain f hf x` divides `comapDomain f hf y`. -/
@[to_additive (dont_translate := R)
/-- Along an injective additive monoid map `f`, if `y = x * z` with `x` and `z` supported in
`Set.range f`, then `comapDomain f hf x` divides `comapDomain f hf y`. -/]
theorem comapDomain_dvd_comapDomain [Monoid M] [Monoid N] {F : Type*} [FunLike F M N]
    [MulHomClass F M N] {f : F} (hf : Function.Injective f) {x y z : MonoidAlgebra R N}
    (h : y = x * z) (hx : (x.coeff.support : Set N) ⊆ Set.range f)
    (hz : (z.coeff.support : Set N) ⊆ Set.range f) :
    comapDomain f hf x ∣ comapDomain f hf y :=
  ⟨comapDomain f hf z, by rw [h, comapDomain_mul_of_support_subset_range hf hx hz]⟩

/-- A monomial pulled back and pushed forward along an injective map survives exactly when its
index lies in the range of the map. -/
theorem mapDomain_comapDomain_single (f : M → N) (hf : f.Injective) (n : N) (r : R)
    [Decidable (n ∈ Set.range f)] :
    mapDomain f (comapDomain f hf (single n r)) = if n ∈ Set.range f then single n r else 0 := by
  split_ifs with hn
  · obtain ⟨m, rfl⟩ := hn
    rw [comapDomain_single_map, mapDomain_single]
  · rw [comapDomain_single_of_notMem_range hn, mapDomain_zero]

/-- `comapDomain` commutes with `mapDomain` along a commutative square `b ∘ f₁ = f₂ ∘ a` of maps
with `f₁`, `f₂` injective, provided that every point which `b` maps into the range of `f₂` lies in
the range of `f₁`. -/
theorem mapDomain_comapDomain_eq_comapDomain_mapDomain {M₂ N₂ : Type*} {f₁ : M → N}
    (hf₁ : f₁.Injective) {f₂ : M₂ → N₂} (hf₂ : f₂.Injective) {a : M → M₂} {b : N → N₂}
    (hcomm : ∀ m, b (f₁ m) = f₂ (a m)) (hrange : ∀ n, b n ∈ Set.range f₂ → n ∈ Set.range f₁)
    (x : MonoidAlgebra R N) :
    mapDomain a (comapDomain f₁ hf₁ x) = comapDomain f₂ hf₂ (mapDomain b x) := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [comapDomain_add, mapDomain_add, hx, hy, mapDomain_add, comapDomain_add]
  | single n r =>
    by_cases hn : n ∈ Set.range f₁
    · obtain ⟨m, rfl⟩ := hn
      rw [comapDomain_single_map, mapDomain_single, mapDomain_single, hcomm,
        comapDomain_single_map]
    · rw [comapDomain_single_of_notMem_range hn, mapDomain_zero, mapDomain_single,
        comapDomain_single_of_notMem_range (mt (hrange n) hn)]

end Map

section Group

variable {K G : Type*} [Group K]

/-- Along an injective monoid homomorphism `φ : K →* G` out of a group, pulling coefficients back
is linear for the left action of `R[K]` on `R[G]` through `mapDomain φ`. -/
@[to_additive (dont_translate := R)
/-- Along an injective additive monoid homomorphism `φ : K →+ G` out of an additive group, pulling
coefficients back is linear for the left action of `R[K]` on `R[G]` through `mapDomain φ`. -/]
theorem comapDomain_mapDomain_mul [Monoid G] (φ : K →* G) (hφ : Function.Injective φ)
    (a : MonoidAlgebra R K) (y : MonoidAlgebra R G) :
    comapDomain φ hφ (mapDomain φ a * y) = a * comapDomain φ hφ y := by
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => rw [mapDomain_add, add_mul, comapDomain_add, ha, hb, add_mul]
  | single k r =>
    induction y using induction_linear with
    | zero => simp
    | add y z hy hz => rw [mul_add, comapDomain_add, hy, hz, comapDomain_add, mul_add]
    | single g s =>
      rw [mapDomain_single, single_mul_single]
      by_cases hg : g ∈ Set.range φ
      · obtain ⟨k', rfl⟩ := hg
        rw [← map_mul, comapDomain_single_map, comapDomain_single_map, single_mul_single]
      · have hkg : φ k * g ∉ Set.range φ := fun ⟨k', hk'⟩ ↦
          hg ⟨k⁻¹ * k', by rw [map_mul, hk', ← mul_assoc, ← map_mul, inv_mul_cancel, map_one,
            one_mul]⟩
        rw [comapDomain_single_of_notMem_range hkg, comapDomain_single_of_notMem_range hg,
          mul_zero]

variable [Group G] (φ : K →* G) (hφ : Function.Injective φ)

/-- Along an injective group homomorphism `φ : K →* G`, pulling coefficients back is linear for
the right action of `R[K]` on `R[G]` through `mapDomain φ`. -/
theorem comapDomain_mul_mapDomain (y : MonoidAlgebra R G) (a : MonoidAlgebra R K) :
    comapDomain φ hφ (y * mapDomain φ a) = comapDomain φ hφ y * a := by
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => rw [mapDomain_add, mul_add, comapDomain_add, ha, hb, mul_add]
  | single k r =>
    induction y using induction_linear with
    | zero => simp
    | add y z hy hz => rw [add_mul, comapDomain_add, hy, hz, comapDomain_add, add_mul]
    | single g s =>
      rw [mapDomain_single, single_mul_single]
      by_cases hg : g ∈ Set.range φ
      · obtain ⟨k', rfl⟩ := hg
        rw [← map_mul, comapDomain_single_map, comapDomain_single_map, single_mul_single]
      · have hgk : g * φ k ∉ Set.range φ := fun ⟨k', hk'⟩ ↦
          hg ⟨k' * k⁻¹, by rw [map_mul, hk', map_inv, mul_inv_cancel_right]⟩
        rw [comapDomain_single_of_notMem_range hgk, comapDomain_single_of_notMem_range hg,
          zero_mul]

/-- **Decomposition along right cosets.** If `t` is a family of representatives of the right
cosets of `φ.range` (every `g` lies in `φ.range * t i` for exactly one `i`), every element `y` of
`R[G]` is the sum over `i` of the part of `y * (t i)⁻¹` supported on `φ.range`, multiplied on the
right by `t i`. -/
theorem sum_mapDomain_comapDomain_mul_single {ι : Type*} [Fintype ι] (t : ι → G)
    (ht : ∀ g, ∃! i, g * (t i)⁻¹ ∈ Set.range φ) (y : MonoidAlgebra R G) :
    ∑ i, mapDomain φ (comapDomain φ hφ (y * single (t i)⁻¹ 1)) * single (t i) 1 = y := by
  classical
  induction y using induction_linear with
  | zero => simp
  | add y z hy hz =>
    simp only [add_mul, comapDomain_add, mapDomain_add, Finset.sum_add_distrib, hy, hz]
  | single g r =>
    obtain ⟨i, hi, hi'⟩ := ht g
    rw [Finset.sum_eq_single i (fun j _ hj ↦ ?_) (by simp)]
    · rw [single_mul_single, mul_one, mapDomain_comapDomain_single, ite_eq_left hi,
        single_mul_single, inv_mul_cancel_right, mul_one]
    · rw [single_mul_single, mul_one, mapDomain_comapDomain_single,
        ite_eq_right fun h ↦ hj (hi' j h), zero_mul]

/-- **Decomposition along left cosets.** If `s` is a family of representatives of the left
cosets of `φ.range` (every `g` lies in `s i * φ.range` for exactly one `i`), every element `y` of
`R[G]` is the sum over `i` of `s i` multiplied on the right by the part of `(s i)⁻¹ * y` supported
on `φ.range`. -/
theorem sum_single_mul_mapDomain_comapDomain {ι : Type*} [Fintype ι] (s : ι → G)
    (hs : ∀ g, ∃! i, (s i)⁻¹ * g ∈ Set.range φ) (y : MonoidAlgebra R G) :
    ∑ i, single (s i) 1 * mapDomain φ (comapDomain φ hφ (single (s i)⁻¹ 1 * y)) = y := by
  classical
  induction y using induction_linear with
  | zero => simp
  | add y z hy hz =>
    simp only [mul_add, comapDomain_add, mapDomain_add, Finset.sum_add_distrib, hy, hz]
  | single g r =>
    obtain ⟨i, hi, hi'⟩ := hs g
    rw [Finset.sum_eq_single i (fun j _ hj ↦ ?_) (by simp)]
    · rw [single_mul_single, one_mul, mapDomain_comapDomain_single, ite_eq_left hi,
        single_mul_single, mul_inv_cancel_left, one_mul]
    · rw [single_mul_single, one_mul, mapDomain_comapDomain_single,
        ite_eq_right fun h ↦ hj (hi' j h), mul_zero]

end Group

end MonoidAlgebra

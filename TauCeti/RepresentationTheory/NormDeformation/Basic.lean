/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.Group.Submonoid.Finite
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# First-order deformations of the norm

Let `ρ : Γ →* R` be a multiplicative map from a finite group to a ring. Its *norm* is
`Nm = ∑ g, ρ g`. For a product `Γ = ∏ⱼ Γⱼ` of finite groups write `Nmⱼ` for the norm of the
factor `Γⱼ`, and let each `Nmⱼ` be deformed to first order, `Nmⱼ + αⱼ ∂ⱼ`, with commuting
variables `αⱼ` and elements `∂ⱼ ∈ R`. When `Nmⱼ` and `∂ⱼ` lie in pairwise commuting subrings
`𝒜ⱼ` of `R`, the product `∏ⱼ (Nmⱼ + αⱼ ∂ⱼ)` is a polynomial in the `αⱼ`, of degree at most one in
each, whose coefficient at `∏_{j ∈ S} αⱼ` is `N_S = ∏_{j ∈ S} ∂ⱼ ∏_{j ∉ S} Nmⱼ`.

A congruence `a ≡ b` is an equality `σ a = σ b` after a ring map `σ`. This file proves the three
algebraic properties of the coefficients `N_S` that the operators at auxiliary places use:

* (a) `N_S` commutes with everything that commutes with the `𝒜ⱼ`, `N_∅ = Nm` is the norm of the
  whole group, and `N_S` and `N_{S ∪ {j}}` share all factors but the one at `j`;
* (b) if `Nmⱼ t = 0` and `∂ⱼ t ≡ Nmⱼ r`, the top coefficient of `𝒩 · G (t - Xⱼ r)` is `≡ 0`,
  where `𝒩 = ∑_S N_S ∏_{i ∈ S} Xᵢ` and `G` is any polynomial;
* (c) if `n ∂ⱼ (g - 1) ≡ Nmⱼ Z` with `δ' Nm Z = 0`, then `δ ^ i N_S ≡ Y Nm` for `i ≥ #S` and
  `δ = n² δ'`, where `∑ g⁻¹ Ψ g = n`.

## Main definitions

* `TauCeti.commutingProd`: the product `∏ⱼ xⱼ` of elements of pairwise commuting subrings.
* `TauCeti.normDeformationCoeff`: the coefficient `N_S = ∏_{j ∈ S} ∂ⱼ ∏_{j ∉ S} Nmⱼ`.

## Main results

* `TauCeti.nsmul_eq_norm_mul`, `TauCeti.nsmul_eq_mul_norm`: if `∑ g⁻¹ Ψ g = n`, then `n` times
  an element fixed by the group is a multiple of the norm.
* `TauCeti.commutingProd_add_eq_sum_normDeformationCoeff`: `∏ⱼ (Nmⱼ + ∂ⱼ) = ∑_S N_S`.
* `TauCeti.exists_empty_eq_sum_and_insert_eq_mul`: the properties (a) of the coefficients.
* `TauCeti.map_top_coeff_mul_C_sub_X_mul_C_eq_zero`: the vanishing (b) of a top coefficient.
* `TauCeti.exists_map_pow_mul_family_eq_mul_norm`: the factorisation (c) through the norm.

## References

The statements and their proofs are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0,
Copyright 2026 Anthropic PBC), file `src/New/Congruences/FirstOrder/OnePrime.lean`
(`New.Patching.familyCoeff`, `New.Patching.exists_empty_eq_sum_and_insert_eq_mul`,
`New.Patching.map_top_coeff_mul_C_sub_X_mul_C_eq_zero`,
`New.Patching.exists_map_pow_mul_family_eq_mul_norm`). The first-order deformation of the norm is
the algebraic core of the Taylor–Wiles patching argument at auxiliary primes: A. Wiles, *Modular
elliptic curves and Fermat's Last Theorem*, Ann. of Math. 141 (1995), and R. Taylor and A. Wiles,
*Ring-theoretic properties of certain Hecke algebras*, ibid.
-/

public section

open Finset

namespace TauCeti

section Norms

variable {Γ R : Type*} [Group Γ] [Fintype Γ] [Ring R] (ρ : Γ →* R)

/-- The norm `∑ ρ h` is fixed by left multiplication with `ρ g`. -/
theorem mul_sum_monoidHom (g : Γ) : ρ g * ∑ h : Γ, ρ h = ∑ h : Γ, ρ h := by
  simp only [mul_sum, ← map_mul]
  exact Equiv.sum_comp (.mulLeft g) ρ

/-- The norm `∑ ρ h` is fixed by right multiplication with `ρ g`. -/
theorem sum_monoidHom_mul (g : Γ) : (∑ h : Γ, ρ h) * ρ g = ∑ h : Γ, ρ h := by
  simp only [sum_mul, ← map_mul]
  exact Equiv.sum_comp (.mulRight g) ρ

variable {ρ} {Ψ : R} {n : ℕ}

/-- If `∑ g⁻¹ Ψ g = n` and `g A = A` for all `g`, then `n A = Nm Ψ A`, where `g` stands for `ρ g`
and `Nm = ∑ g` is the norm. -/
theorem nsmul_eq_norm_mul (hΨ : ∑ g : Γ, ρ g⁻¹ * Ψ * ρ g = n) {A : R}
    (hA : ∀ g : Γ, ρ g * A = A) : n • A = (∑ g : Γ, ρ g) * Ψ * A := by
  have sum_inv : ∑ g, ρ g⁻¹ = ∑ g, ρ g := Equiv.sum_comp (.inv Γ) ρ
  calc n • A = (∑ g, ρ g⁻¹ * Ψ * ρ g) * A := by rw [hΨ, nsmul_eq_mul]
    _ = (∑ g, ρ g⁻¹) * Ψ * A := by simp only [sum_mul, mul_assoc, hA]
    _ = (∑ g, ρ g) * Ψ * A := by rw [sum_inv]

/-- If `∑ g⁻¹ Ψ g = n` and `A g = A` for all `g`, then `n A = A Ψ Nm`, where `g` stands for `ρ g`
and `Nm = ∑ g` is the norm. -/
theorem nsmul_eq_mul_norm (hΨ : ∑ g : Γ, ρ g⁻¹ * Ψ * ρ g = n) {A : R}
    (hA : ∀ g : Γ, A * ρ g = A) : n • A = A * Ψ * ∑ g : Γ, ρ g :=
  calc n • A = A * ∑ g, ρ g⁻¹ * Ψ * ρ g := by rw [hΨ, nsmul_eq_mul']
    _ = A * Ψ * ∑ g, ρ g := by simp only [mul_sum, ← mul_assoc, hA]

end Norms

section Family

variable {J R R' : Type*} [Fintype J] [DecidableEq J] [Ring R] [Ring R'] {σ : R →+* R'}
  {Γ : J → Type*} [∀ j : J, Group (Γ j)] [∀ j : J, Fintype (Γ j)]

/-- Let `ρ` map the product of the finite groups `Γ j` to the ring `R`, and let `σ : R → R'` be a
ring map. Write `g` for `ρ g`, `Nm = ∑ g` for the norm, and `a ≡ b` for `σ a = σ b`. If
`∑ g⁻¹ Ψ g = n` and `A (g - 1) ≡ 0` for all `g` in each factor `Γ j`, then `n A ≡ A Ψ Nm`. -/
theorem map_nsmul_eq_mul_norm (ρ : (∀ j : J, Γ j) →* R) {Ψ A : R} {n : ℕ}
    (hΨ : ∑ g : (j : J) → Γ j, ρ g⁻¹ * Ψ * ρ g = n)
    (hA : ∀ (j : J) (g : Γ j), σ (A * (ρ (Pi.mulSingle j g) - 1)) = 0) :
    σ (n • A) = σ (A * Ψ * ∑ g : (j : J) → Γ j, ρ g) := by
  -- The hypothesis extends to the whole group, which the factors generate.
  have invariant (g : ∀ j, Γ j) : σ A * σ (ρ g) = σ A := by
    let H : Submonoid (∀ j, Γ j) :=
      { carrier := {g | σ A * σ (ρ g) = σ A}
        mul_mem' := fun {g h} hg hh ↦ by
          rw [Set.mem_ofPred_eq] at hg hh ⊢
          rw [map_mul, map_mul, ← mul_assoc, hg, hh]
        one_mem' := by simp }
    have mem_H (x : ∀ j, Γ j) : x ∈ H ↔ σ A * σ (ρ x) = σ A := Iff.rfl
    refine (mem_H g).1 (Submonoid.pi_mem_of_mulSingle_mem g fun j ↦ (mem_H _).2 ?_)
    rw [← map_mul, ← sub_eq_zero, ← map_sub, ← mul_sub_one, hA]
  rw [map_nsmul, map_mul, map_mul, map_sum]
  exact nsmul_eq_mul_norm (ρ := σ.toMonoidHom.comp ρ) (by simpa using congrArg σ hΨ) invariant

variable {𝒜 : J → Subring R} (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b)

/-- The product `x ↦ ∏ⱼ xⱼ` of elements `xⱼ ∈ 𝒜 j` of pairwise commuting subrings of `R`. As the
factors commute, the order of the product does not matter. -/
noncomputable def commutingProd : (∀ j : J, 𝒜 j) →* R :=
  MonoidHom.noncommPiCoprod (fun j ↦ (𝒜 j).subtype.toMonoidHom)
    fun i j hij a b ↦ h𝒜 i j hij a a.property b b.property

omit [DecidableEq J] in
/-- `commutingProd` is the product of its factors, in any order. -/
theorem commutingProd_apply (x : ∀ j : J, 𝒜 j) :
    commutingProd h𝒜 x = (univ : Finset J).noncommProd (fun j ↦ (x j : R))
      (fun i _ j _ hij ↦ h𝒜 i j hij _ (x i).property _ (x j).property) :=
  MonoidHom.noncommPiCoprod_apply _ x

/-- The product of a family with a single factor `a` different from `1` is `a`. -/
@[simp]
theorem commutingProd_mulSingle (j : J) (a : 𝒜 j) : commutingProd h𝒜 (Pi.mulSingle j a) = a := by
  simp [commutingProd]

/-- In a product of elements of pairwise commuting subrings, any one factor can be written
last. -/
theorem commutingProd_update (x : ∀ j : J, 𝒜 j) (j : J) (a : 𝒜 j) :
    commutingProd h𝒜 (Function.update x j a) = commutingProd h𝒜 (Function.update x j 1) * a := by
  have split : Function.update x j a = Function.update x j 1 * Pi.mulSingle j a := by
    ext k : 1
    by_cases hk : k = j
    · subst hk
      simp
    · simp [Function.update_of_ne hk, Pi.mulSingle_eq_of_ne hk]
  rw [split, map_mul, commutingProd_mulSingle]

/-- A product of sums of elements of pairwise commuting subrings expands as a sum of products:
`∏ⱼ ∑ᵢ xⱼᵢ = ∑_f ∏ⱼ xⱼ(f j)`. -/
theorem commutingProd_sum {ι : J → Type*} [∀ j : J, Fintype (ι j)] (x : ∀ j : J, ι j → 𝒜 j) :
    commutingProd h𝒜 (fun j : J ↦ ∑ i : ι j, x j i) =
      ∑ f : (j : J) → ι j, commutingProd h𝒜 fun j : J ↦ x j (f j) := by
  -- The product is multilinear, because any one factor can be written last.
  let Φ : (∀ j : J, 𝒜 j) →* R := commutingProd h𝒜
  have last (y : ∀ j : J, 𝒜 j) (j : J) (a : 𝒜 j) :
      Φ (Function.update y j a) = Φ (Function.update y j 1) * a := commutingProd_update h𝒜 y j a
  have Φ_add (y : ∀ j : J, 𝒜 j) (j : J) (a b : 𝒜 j) : Φ (Function.update y j (a + b)) =
      Φ (Function.update y j a) + Φ (Function.update y j b) := by
    rw [last y j (a + b), last y j a, last y j b, Subring.coe_add, mul_add]
  have Φ_smul (y : ∀ j : J, 𝒜 j) (j : J) (r : ℕ) (a : 𝒜 j) :
      Φ (Function.update y j (r • a)) = r • Φ (Function.update y j a) := by
    rw [last y j (r • a), last y j a, AddSubmonoidClass.coe_nsmul, mul_smul_comm]
  let M : (Π j : J, 𝒜 j) →ₘₗ[ℕ] R := .mk' Φ Φ_add Φ_smul
  exact M.map_sum x

/-- The coefficient `N_S = ∏_{j ∈ S} ∂ⱼ ∏_{j ∉ S} Nmⱼ` of `∏_{j ∈ S} αⱼ` in the product
`∏ⱼ (Nmⱼ + αⱼ ∂ⱼ)` in commuting variables `αⱼ`, where `Nmⱼ` and `∂ⱼ = der j` lie in the `j`-th
of the pairwise commuting subrings `𝒜 j`
(`commutingProd_add_eq_sum_normDeformationCoeff`). -/
noncomputable def normDeformationCoeff (Nm der : ∀ j : J, 𝒜 j) (S : Finset J) : R :=
  commutingProd h𝒜 (S.piecewise der Nm)

theorem normDeformationCoeff_def (Nm der : ∀ j : J, 𝒜 j) (S : Finset J) :
    normDeformationCoeff h𝒜 Nm der S = commutingProd h𝒜 (S.piecewise der Nm) :=
  (rfl)

/-- The product `∏ⱼ (Nmⱼ + ∂ⱼ)` is the sum of the coefficients `N_S` over all `S`. Applied with
`αⱼ ∂ⱼ` in place of `∂ⱼ`, for scalars `αⱼ` commuting with `𝒜 j`, this exhibits `N_S` as the
coefficient of `∏_{j ∈ S} αⱼ` in `∏ⱼ (Nmⱼ + αⱼ ∂ⱼ)`. -/
theorem commutingProd_add_eq_sum_normDeformationCoeff (Nm der : ∀ j : J, 𝒜 j) :
    commutingProd h𝒜 (Nm + der) = ∑ S : Finset J, normDeformationCoeff h𝒜 Nm der S := by
  let x (j : J) (b : Bool) : 𝒜 j := if b then der j else Nm j
  have sum_x : Nm + der = fun j ↦ ∑ b : Bool, x j b := funext fun j ↦ by simp [x, add_comm]
  rw [sum_x, commutingProd_sum]
  refine Fintype.sum_bijective (fun f ↦ univ.filter fun j ↦ f j = true) ⟨fun f f' h ↦ ?_,
    fun S ↦ ⟨fun j ↦ decide (j ∈ S), by simp⟩⟩ _ _ fun f ↦ ?_
  · exact funext fun j ↦ Bool.eq_iff_iff.2 (by simpa using Finset.ext_iff.1 h j)
  · simp only [normDeformationCoeff_def]
    congr 1
    funext j
    cases hf : f j <;> simp [x, hf, Finset.piecewise]

/-- An element that commutes with all the subrings `𝒜 j` commutes with every coefficient
`N_S = ∏_{j ∈ S} ∂ⱼ ∏_{j ∉ S} Nmⱼ`. -/
theorem commute_normDeformationCoeff (Nm der : ∀ j : J, 𝒜 j) {t : R}
    (ht : ∀ j : J, ∀ a ∈ 𝒜 j, Commute t a) (S : Finset J) :
    Commute t (normDeformationCoeff h𝒜 Nm der S) :=
  MonoidHom.commute_noncommPiCoprod _ (fun j (a : 𝒜 j) ↦ ht j a a.property) (S.piecewise der Nm)

/-- Let `ρ` map the product of the finite groups `Γ j` to `R`, with `Γ j` going into `𝒜 j`. If
`Nmⱼ` is the sum of `ρ` over `Γ j`, then the coefficient `N_∅ = ∏ⱼ Nmⱼ`, in which no `∂ⱼ` occurs,
is the sum of `ρ` over the whole group. -/
theorem normDeformationCoeff_empty (ρ : (∀ j : J, Γ j) →* R)
    (hρ : ∀ (j : J) (g : Γ j), ρ (Pi.mulSingle j g) ∈ 𝒜 j) {Nm : ∀ j : J, 𝒜 j}
    (h_norm : ∀ j : J, (Nm j : R) = ∑ g : Γ j, ρ (Pi.mulSingle j g)) (der : ∀ j : J, 𝒜 j) :
    normDeformationCoeff h𝒜 Nm der ∅ = ∑ g : (j : J) → Γ j, ρ g := by
  let r (j : J) (g : Γ j) : 𝒜 j := ⟨ρ (Pi.mulSingle j g), hρ j g⟩
  have norm_eq : Nm = fun j ↦ ∑ g : Γ j, r j g := funext fun j ↦ Subtype.ext (by simp [h_norm, r])
  have prod_single (g : ∀ j : J, Γ j) : commutingProd h𝒜 (fun j ↦ r j (g j)) = ρ g :=
    DFunLike.congr_fun (MonoidHom.noncommPiCoprodEquiv.right_inv ρ) g
  calc normDeformationCoeff h𝒜 Nm der ∅ = commutingProd h𝒜 fun j ↦ ∑ g : Γ j, r j g := by
        rw [normDeformationCoeff_def, piecewise_empty, norm_eq]
    _ = ∑ g : (j : J) → Γ j, commutingProd h𝒜 fun j ↦ r j (g j) := commutingProd_sum h𝒜 r
    _ = ∑ g : (j : J) → Γ j, ρ g := sum_congr rfl fun g _ ↦ prod_single g

/-- For `j ∉ S` the coefficients `N_S` and `N_{S ∪ {j}}` differ only in the factor at `j`: they
are `N' Nmⱼ` and `N' ∂ⱼ` for one `N'`. -/
theorem exists_normDeformationCoeff_eq_mul (Nm der : ∀ j : J, 𝒜 j) {j : J} {S : Finset J}
    (hj : j ∉ S) :
    ∃ N' : R, normDeformationCoeff h𝒜 Nm der S = N' * Nm j ∧
      normDeformationCoeff h𝒜 Nm der (insert j S) = N' * der j := by
  refine ⟨commutingProd h𝒜 (Function.update (S.piecewise der Nm) j 1), ?_, ?_⟩
  · rw [← commutingProd_update, ← piecewise_eq_of_notMem S der Nm hj, Function.update_eq_self,
      normDeformationCoeff_def]
  · rw [← commutingProd_update, normDeformationCoeff_def, piecewise_insert]

/-- **The coefficients of a product of first-order deformations of norms.** Let `ρ` map the product
of the finite groups `Γ j` to the ring `R`. Let `𝒜 j` be pairwise commuting subrings that contain
`∂ⱼ = der j` and the image of `Γ j`, and let `Nmⱼ` be the sum of `ρ` over `Γ j`. There are elements
`N S` that commute with every `t` commuting with all `𝒜 j`, such that `N ∅` is the sum of `ρ` over
the whole group and, for `j ∉ S`, `N S = N' Nmⱼ` and `N (insert j S) = N' ∂ⱼ` for some `N'`. One may
take `N S` to be the coefficient of `∏_{j ∈ S} αⱼ` in `∏ⱼ (Nmⱼ + αⱼ ∂ⱼ)`, namely
`normDeformationCoeff`. -/
theorem exists_empty_eq_sum_and_insert_eq_mul (ρ : (∀ j : J, Γ j) →* R) (𝒜 : J → Subring R)
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b)
    (hρ : ∀ (j : J) (g : Γ j), ρ (Pi.mulSingle j g) ∈ 𝒜 j) {der : J → R}
    (h_der : ∀ j : J, der j ∈ 𝒜 j) :
    ∃ N : Finset J → R,
      (∀ t : R, (∀ j : J, ∀ a ∈ 𝒜 j, Commute t a) → ∀ S : Finset J, Commute t (N S)) ∧
      N ∅ = ∑ g : (j : J) → Γ j, ρ g ∧
      ∀ (j : J) (S : Finset J), j ∉ S → ∃ N' : R,
        N S = N' * ∑ g : Γ j, ρ (Pi.mulSingle j g) ∧ N (insert j S) = N' * der j := by
  let Nm (j : J) : 𝒜 j := ⟨∑ g : Γ j, ρ (Pi.mulSingle j g), sum_mem fun g _ ↦ hρ j g⟩
  let der' (j : J) : 𝒜 j := ⟨der j, h_der j⟩
  exact ⟨normDeformationCoeff h𝒜 Nm der', fun t ht ↦ commute_normDeformationCoeff h𝒜 Nm der' ht,
    normDeformationCoeff_empty h𝒜 ρ hρ (fun j ↦ rfl) der',
    fun j S hj ↦ exists_normDeformationCoeff_eq_mul h𝒜 Nm der' hj⟩

end Family

section TopCoefficient

open MvPolynomial

/-- For `j ∉ S`, the coefficient of `∏_{i ∈ S} Xᵢ` in `G (t - Xⱼ r)` is `t` times that in `G`. -/
theorem _root_.MvPolynomial.coeff_mul_C_sub_X_mul_C_of_notMem {J T : Type*} [CommRing T]
    (G : MvPolynomial J T) (t r : T) {j : J} {S : Finset J} (hj : j ∉ S) :
    (G * (C t - X j * C r)).coeff (∑ i ∈ S, .single i 1) =
      t * G.coeff (∑ i ∈ S, .single i 1) := by
  classical
  simp [mul_sub, ← mul_assoc, mul_comm _ (C _), coeff_mul_X', Finsupp.finsetSum_apply,
    Finsupp.single_apply, hj]

/-- For `j ∉ S`, the coefficient of `Xⱼ ∏_{i ∈ S} Xᵢ` in `G (t - Xⱼ r)` is `t` times that in `G`
minus `r` times the coefficient of `∏_{i ∈ S} Xᵢ` in `G`. -/
theorem _root_.MvPolynomial.coeff_mul_C_sub_X_mul_C_insert {J T : Type*} [DecidableEq J]
    [CommRing T] (G : MvPolynomial J T) (t r : T) {j : J} {S : Finset J} (hj : j ∉ S) :
    (G * (C t - X j * C r)).coeff (∑ i ∈ insert j S, .single i 1) =
      t * G.coeff (∑ i ∈ insert j S, .single i 1) - r * G.coeff (∑ i ∈ S, .single i 1) := by
  rw [mul_sub, mul_left_comm G, sum_insert hj]
  simp [coeff_X_mul, mul_comm G]

variable {J R R' : Type*} [Fintype J] [DecidableEq J] [Ring R] [Ring R'] {σ : R →+* R'}

/-- **The top coefficient of a multiple of a tie vanishes.** Let `σ : R → R'` be a ring map, write
`a ≡ b` for `σ a = σ b` and `∂ⱼ = der j`, and let the commutative ring `T` map to `R` by `ac`. Let
`𝒩 = ∑_S N_S ∏_{i ∈ S} Xᵢ` be the polynomial over `R` with coefficients `N S`, of degree at most one
in each of the variables `Xᵢ`, which commute with each other and with `R`. For a polynomial `P` over
`T`, the coefficient of `∏_{i ∈ J} Xᵢ` in `𝒩 P` is then `∑_S N Sᶜ · c_S(P)`, where `c_S(P)` is the
coefficient of `∏_{i ∈ S} Xᵢ` in `P`. Suppose that for `j ∉ S` there is `N'` with `N S = N' Nmⱼ` and
`N (insert j S) = N' ∂ⱼ`. If `Nmⱼ t = 0` and `∂ⱼ t ≡ Nmⱼ r`, then this coefficient is `≡ 0` for
every multiple `P = G (t - Xⱼ r)`. -/
theorem map_top_coeff_mul_C_sub_X_mul_C_eq_zero {N : Finset J → R} {der : J → R} {T : Type*}
    [CommRing T] (ac : T →+* R) {Nm : J → R}
    (h_factor : ∀ (j : J) (S : Finset J), j ∉ S →
      ∃ N' : R, N S = N' * Nm j ∧ N (insert j S) = N' * der j)
    {j : J} {t r : T} (h_norm : Nm j * ac t = 0) (h_tie : σ (der j * ac t) = σ (Nm j * ac r))
    (G : MvPolynomial J T) :
    σ (∑ S : Finset J,
      N Sᶜ * ac ((G * (C t - X j * C r)).coeff (∑ i ∈ S, .single i 1))) = 0 := by
  -- Pair each `S` without `j` with `insert j S`; the coefficients of `N` at the two complements
  -- differ only in the factor at `j`.
  rw [← powerset_univ, ← insert_erase (mem_univ j), sum_powerset_insert (notMem_erase j _),
    ← sum_add_distrib, map_sum]
  refine sum_eq_zero fun S hS ↦ ?_
  have hj : j ∉ S := fun h ↦ notMem_erase j _ (mem_powerset.1 hS h)
  obtain ⟨N', h_insert, h_S⟩ : ∃ N' : R, N (insert j S)ᶜ = N' * Nm j ∧ N Sᶜ = N' * der j := by
    simpa only [insert_compl_insert hj] using h_factor j (insert j S)ᶜ (by simp)
  have kill (b : T) : N' * Nm j * ac (t * b) = 0 := by
    simp [mul_assoc, ← mul_assoc (Nm j), h_norm]
  have tie (b : T) : σ (N' * der j * ac (t * b)) = σ (N' * Nm j * ac (r * b)) := by
    simpa only [map_mul, mul_assoc] using congrArg (σ N' * · * σ (ac b)) h_tie
  rw [map_add, coeff_mul_C_sub_X_mul_C_of_notMem G t r hj, coeff_mul_C_sub_X_mul_C_insert G t r hj,
    h_S, h_insert, tie, map_sub ac, mul_sub, kill]
  simp

end TopCoefficient

section Factorisation

variable {J R R' : Type*} [Fintype J] [DecidableEq J] [Ring R] [Ring R'] {σ : R →+* R'}
  {Γ : J → Type*} [∀ j : J, Group (Γ j)] [∀ j : J, Fintype (Γ j)]

/-- **Powers of `δ` times the coefficients factor through the norm.** Let `ρ` map the product of the
finite groups `Γ j` to the ring `R`, and let `σ : R → R'` be a ring map. Write `g` for `ρ g`, `Nm =
∑ g` for the norm, `Nmⱼ` for the sum over `Γ j`, `∂ⱼ = der j`, and `a ≡ b` for `σ a = σ b`. Let `N S
∈ R` be indexed by the subsets `S` of `J`, with `N ∅ = Nm`, and for `j ∉ S` let `N S = N' Nmⱼ` and
`N (insert j S) = N' ∂ⱼ` for some `N'`, as for the coefficients of `∏ⱼ (Nmⱼ + αⱼ ∂ⱼ)`. Let `∑ g⁻¹ Ψ
g = n` and `δ = n² δ'`, where `δ'` commutes with the group and with all `N S`. Suppose that each `g
∈ Γ j` has a `Z` with `n ∂ⱼ (g - 1) ≡ Nmⱼ Z` and `δ' Nm Z = 0`. Then for `i ≥ #S` there is a `Y`
with `δ ^ i N S ≡ Y Nm`, and `Y = δ ^ i` if `S` is empty. -/
theorem exists_map_pow_mul_family_eq_mul_norm {ρ : (∀ j : J, Γ j) →* R} {N : Finset J → R}
    {der : J → R} {Ψ δ' : R} {n : ℕ} (hΨ : ∑ g : (j : J) → Γ j, ρ g⁻¹ * Ψ * ρ g = n)
    (hδ'ρ : ∀ g : (j : J) → Γ j, Commute δ' (ρ g)) (hδ'N : ∀ S : Finset J, Commute δ' (N S))
    (h_empty : N ∅ = ∑ g : (j : J) → Γ j, ρ g)
    (h_factor : ∀ (j : J) (S : Finset J), j ∉ S → ∃ N' : R,
      N S = N' * ∑ g : Γ j, ρ (Pi.mulSingle j g) ∧ N (insert j S) = N' * der j)
    (h_der : ∀ (j : J) (g : Γ j), ∃ Z : R,
      σ (n • (der j * (ρ (Pi.mulSingle j g) - 1))) = σ ((∑ k : Γ j, ρ (Pi.mulSingle j k)) * Z) ∧
        δ' * (∑ k : (j : J) → Γ j, ρ k) * Z = 0)
    (S : Finset J) {i : ℕ} (hi : #S ≤ i) :
    ∃ Y : R,
      σ ((n ^ 2 • δ') ^ i * N S) = σ (Y * ∑ g : (j : J) → Γ j, ρ g) ∧
      (S = ∅ → Y = (n ^ 2 • δ') ^ i) := by
  -- Induction on `S`. For nonempty `S` write `i = e + 1`; the operator `A = n δ' δ ^ e N S` has
  -- `A (g - 1) ≡ 0`, and `n A = δ ^ (e + 1) N S` factors through the norm.
  set δ : R := n ^ 2 • δ'
  have hδ'δ : Commute δ' δ := (Commute.refl δ').smul_right (n ^ 2)
  have hδ'_norm : Commute δ' (∑ g, ρ g) := .sum_right univ ρ δ' fun g _ ↦ hδ'ρ g
  induction S using Finset.strongInduction generalizing i with | _ S ih
  rcases S.eq_empty_or_nonempty with rfl | hS
  · exact ⟨δ ^ i, by rw [h_empty], fun _ ↦ rfl⟩
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, i = e + 1 := ⟨i - 1, by grind [Finset.card_pos]⟩
  set A : R := n • (δ' * δ ^ e * N S) with hA
  have invariant (j : J) (g : Γ j) : σ (A * (ρ (Pi.mulSingle j g) - 1)) = 0 := by
    by_cases hj : j ∈ S
    · -- Write `N S = N' ∂ⱼ`, so that `N' Nmⱼ = N (S.erase j)`, to which the induction applies.
      obtain ⟨N', h_erase, h_S⟩ : ∃ N' : R,
          N (S.erase j) = N' * ∑ k : Γ j, ρ (Pi.mulSingle j k) ∧ N S = N' * der j := by
        simpa only [insert_erase hj] using h_factor j (S.erase j) (notMem_erase j S)
      obtain ⟨Z, hZ, hZ_zero⟩ := h_der j g
      obtain ⟨Y, hY⟩ : ∃ Y : R, σ (δ ^ e * N (S.erase j)) = σ (Y * ∑ g, ρ g) :=
        (ih (S.erase j) (erase_ssubset hj) (i := e) (by grind [card_erase_of_mem])).imp
          fun Y ↦ And.left
      -- `δ'` moves to the right of `N (S.erase j)` first: `Y` need not commute with it.
      have h_move : δ' * δ ^ e * N (S.erase j) = δ ^ e * N (S.erase j) * δ' := by
        rw [mul_assoc, ((hδ'δ.pow_right e).mul_right (hδ'N _)).eq]
      calc σ (A * (ρ (Pi.mulSingle j g) - 1))
          = σ (δ' * δ ^ e * N') * σ (n • (der j * (ρ (Pi.mulSingle j g) - 1))) := by
            simp only [hA, h_S, ← map_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
        _ = σ (δ' * δ ^ e * N (S.erase j)) * σ Z := by
            simp only [hZ, h_erase, map_mul, mul_assoc]
        _ = σ (Y * (δ' * (∑ g, ρ g) * Z)) := by
            rw [h_move, map_mul, hY, ← map_mul, ← map_mul, mul_assoc Y, ← hδ'_norm.eq]
            simp only [mul_assoc]
        _ = 0 := by rw [hZ_zero, mul_zero, map_zero]
    · -- The norm at `j` is a factor of `N S`.
      obtain ⟨N', h_S⟩ : ∃ N' : R, N S = N' * ∑ k : Γ j, ρ (Pi.mulSingle j k) :=
        (h_factor j S hj).imp fun N' ↦ And.left
      have norm_inv : (∑ k : Γ j, ρ (Pi.mulSingle j k)) * ρ (Pi.mulSingle j g) =
          ∑ k : Γ j, ρ (Pi.mulSingle j k) :=
        sum_monoidHom_mul (ρ.comp (MonoidHom.mulSingle Γ j)) g
      simp only [hA, h_S, smul_mul_assoc, mul_assoc, mul_sub_one, norm_inv, sub_self, map_zero]
  have pow_mul_eq : δ ^ (e + 1) * N S = n • A := by
    rw [hA, smul_smul, ← sq, pow_succ', ← smul_mul_assoc, ← smul_mul_assoc]
  refine ⟨A * Ψ, ?_, fun h ↦ absurd h hS.ne_empty⟩
  rw [pow_mul_eq, map_nsmul_eq_mul_norm ρ hΨ invariant]

end Factorisation

end TauCeti

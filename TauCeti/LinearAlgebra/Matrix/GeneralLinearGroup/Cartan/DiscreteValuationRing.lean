/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.Integer
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence
import TauCeti.LinearAlgebra.Matrix.InvariantFactor
import TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Basic

/-!
# The Cartan decomposition of `GLₙ` over a discretely valued field

Let `R` be a discrete valuation ring with fraction field `K`, `ϖ` a uniformizer of `R`, and `π` its
image in `Kˣ`. The **Cartan decomposition** says that every `g ∈ GLₙ(K)` lies in exactly one
double coset

```text
GLₙ(R) · diag(π^{a₀}, …, π^{aₙ₋₁}) · GLₙ(R),    a₀ ≤ a₁ ≤ ⋯ ≤ aₙ₋₁,
```

of the integral points `GLₙ(R)`, embedded in `GLₙ(K)` by `Matrix.GeneralLinearGroup.map`. For
`K = ℚ_p` and `R = ℤ_p` this is the decomposition `GLₙ(ℚ_p) = ⊔ GLₙ(ℤ_p) p^a GLₙ(ℤ_p)` over the
dominant exponents `a`.

Existence clears denominators and takes a Smith normal form over `R`
(`Matrix.exists_smith_normal_form_of_isDiscreteValuationRing`). Uniqueness reads the exponents
off the valuations of minors: `a₀ + ⋯ + aₖ₋₁` is the least valuation of a `k × k` minor, a
quantity that two-sided multiplication by `GLₙ(R)` does not change
(`Matrix.exists_valuation_det_submatrix_eq_prefixSum_of_mul_mul_eq_diagonal`).

## Main results

* `TauCeti.exists_monotone_mem_doubleCoset_diagGL_zpow`: every `g ∈ GLₙ(K)` lies in the double
  coset of `diag(π^{a₀}, …, π^{aₙ₋₁})` for some monotone `a`.
* `TauCeti.eq_of_monotone_of_mem_doubleCoset_diagGL_zpow`: the monotone exponent vector is unique.
* `TauCeti.existsUnique_monotone_mem_doubleCoset_diagGL_zpow`: the two together.

## References

* I. G. Macdonald, *Spherical Functions on a Group of p-adic Type*, Ramanujan Institute (1971),
  Chapter II, §2.6.
* N. Jacobson, *Basic Algebra I*, second edition, W. H. Freeman, 1985, §3.9, for the invariant
  factors.
-/

public section

open Matrix DoubleCoset

namespace TauCeti

section Denominators

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R}
  {ι : Type*}

/-- **Clearing the denominators of a matrix over the fraction field of a discrete valuation
ring.** Some power of a uniformizer multiplies a given matrix over `K` into the image of the
matrices over `R`. -/
theorem exists_map_eq_pow_smul_of_irreducible [Finite ι] (hϖ : Irreducible ϖ)
    (M : Matrix ι ι K) :
    ∃ (m : ℕ) (A : Matrix ι ι R), A.map (algebraMap R K) = algebraMap R K ϖ ^ m • M := by
  have := Fintype.ofFinite ι
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ
    (fun p : ι × ι ↦ M p.1 p.2)
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero b.property) hϖ
  choose r hr using fun i j ↦ hb (i, j) (Finset.mem_univ _)
  refine ⟨m, Matrix.of fun i j ↦ ↑u⁻¹ * r i j, ?_⟩
  ext i j
  simp only [map_apply, of_apply, map_mul, hr, Algebra.smul_def, hu]
  rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← mul_assoc, ← map_mul, Units.inv_mul, map_one,
    one_mul, map_pow]

end Denominators

section Diagonal

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] {ϖ : R} {π : Kˣ} {n : ℕ}

/-- A diagonal matrix of powers of `π`, with nonnegative exponents, is the image of the diagonal
matrix of the same powers of `ϖ`. -/
private theorem coe_diagGL_zpow_natCast (hπ : algebraMap R K ϖ = π) (α : Fin n → ℕ) :
    ((diagGL fun i ↦ π ^ (α i : ℤ) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (diagonal fun i ↦ ϖ ^ α i).map (algebraMap R K) := by
  ext i j
  by_cases hij : i = j <;> simp [hij, ← hπ]

/-- Multiplying the exponents of `diag(π^a)` by a common shift multiplies it by a scalar. -/
private theorem diagGL_zpow_add_const (a : Fin n → ℤ) (m : ℤ) :
    (diagGL fun i ↦ π ^ (a i + m) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) (π ^ m) * diagGL fun i ↦ π ^ a i := by
  rw [← diagGL_const_mul]
  simp only [_root_.zpow_add, mul_comm]

end Diagonal

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R} {π : Kˣ} {n : ℕ}

/-- **Uniqueness of a Smith normal form with uniformizer powers.** If two diagonal matrices of
powers of a uniformizer, with monotone exponents, are equivalent under `GLₙ(R)`, then their
exponents agree. -/
private theorem eq_of_diagonal_pow_eq_mul_mul (hϖ : Irreducible ϖ) {α β : Fin n → ℕ}
    (hα : Monotone α) (hβ : Monotone β) (L Q : GL (Fin n) R)
    (h : (diagonal fun i ↦ ϖ ^ α i) = (L : Matrix (Fin n) (Fin n) R) *
      diagonal (fun i ↦ ϖ ^ β i) * (Q : Matrix (Fin n) (Fin n) R)) : α = β := by
  set v := IsDiscreteValuationRing.addVal R
  have hv : ∀ x, 0 ≤ v x := fun _ ↦ zero_le
  have hval (γ : Fin n → ℕ) (i : Fin n) : v (ϖ ^ γ i) = (γ i : ℕ∞) := by
    rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
      nsmul_one]
  have hchain (γ : Fin n → ℕ) (hγ : Monotone γ) :
      ∀ ⦃i j : Fin n⦄, i ≤ j → ϖ ^ γ i ∣ ϖ ^ γ j := fun _ _ hij ↦ pow_dvd_pow ϖ (hγ hij)
  -- `diagonal (ϖ ^ α)` has the Smith normal forms `ϖ ^ α` and, through `h`, `ϖ ^ β`.
  have hβsnf : (↑L⁻¹ : Matrix (Fin n) (Fin n) R) * (diagonal fun i ↦ ϖ ^ α i) *
      (↑Q⁻¹ : Matrix (Fin n) (Fin n) R) = diagonal fun i ↦ ϖ ^ β i :=
    (GeneralLinearGroup.inv_mul_mul_inv_eq_iff_mul_mul_eq L Q).2 h.symm
  have hαsnf : (1 : Matrix (Fin n) (Fin n) R) * (diagonal fun i ↦ ϖ ^ α i) * 1 =
      diagonal fun i ↦ ϖ ^ α i := by rw [Matrix.one_mul, Matrix.mul_one]
  have hunit (g : GL (Fin n) R) : IsUnit (g : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.GeneralLinearGroup.det g).isUnit
  -- the least valuation of a `k × k` minor is the prefix sum of either exponent vector
  have hprefix (k : ℕ) (hk : k ≤ n) : prefixSum k α = prefixSum k β := by
    have key (γ δ : Fin n → ℕ) (hγ : Monotone γ) (hδ : Monotone δ) (L' Q' : Matrix _ _ R)
        (hL' : IsUnit L'.det) (hQ' : IsUnit Q'.det)
        (hγsnf : L' * (diagonal fun i ↦ ϖ ^ α i) * Q' = diagonal fun i ↦ ϖ ^ γ i)
        (L'' Q'' : Matrix _ _ R) (hL'' : IsUnit L''.det) (hQ'' : IsUnit Q''.det)
        (hδsnf : L'' * (diagonal fun i ↦ ϖ ^ α i) * Q'' = diagonal fun i ↦ ϖ ^ δ i) :
        (prefixSum k fun i ↦ (γ i : ℕ∞)) ≤ prefixSum k fun i ↦ (δ i : ℕ∞) := by
      obtain ⟨f, g, hfg⟩ := exists_valuation_det_submatrix_eq_prefixSum_of_mul_mul_eq_diagonal
        hv hL'' hQ'' (hchain δ hδ) hδsnf hk
      have hle := prefixSum_le_valuation_det_submatrix_of_mul_mul_eq_diagonal
        hv hL' hQ' (hchain γ hγ) hγsnf hk f g
      simp only [hval] at hfg hle
      exact hle.trans hfg.le
    have h₁ := key α β hα hβ 1 1 (by simp) (by simp) hαsnf _ _ (hunit L⁻¹) (hunit Q⁻¹) hβsnf
    have h₂ := key β α hβ hα _ _ (hunit L⁻¹) (hunit Q⁻¹) hβsnf 1 1 (by simp) (by simp) hαsnf
    have hcast (γ : Fin n → ℕ) : (prefixSum k fun i ↦ (γ i : ℕ∞)) = (prefixSum k γ : ℕ) := by
      simp [prefixSum_def]
    rw [hcast, hcast] at h₁ h₂
    exact_mod_cast le_antisymm h₁ h₂
  funext i
  have h₁ := hprefix (i + 1) i.isLt
  rw [prefixSum_succ i.isLt, prefixSum_succ i.isLt, hprefix i i.isLt.le] at h₁
  exact Nat.add_left_cancel h₁

/-- **Existence in the Cartan decomposition of `GLₙ(K)`.** Every `g ∈ GLₙ(K)` lies in the `GLₙ(R)`
double coset of `diag(π^{a₀}, …, π^{aₙ₋₁})` for some monotone `a`. Here `π` is the image of a
uniformizer of the discrete valuation ring `R` in its fraction field `K`. -/
theorem exists_monotone_mem_doubleCoset_diagGL_zpow (hϖ : Irreducible ϖ)
    (hπ : algebraMap R K ϖ = π) (g : GL (Fin n) K) :
    ∃ a : Fin n → ℤ, Monotone a ∧ g ∈ doubleCoset (diagGL fun i ↦ π ^ a i)
      (GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range
      (GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range := by
  obtain ⟨m, A, hA⟩ := exists_map_eq_pow_smul_of_irreducible hϖ (g : Matrix (Fin n) (Fin n) K)
  obtain ⟨L, Q, s, hL, hQ, hs, hLAQ⟩ := exists_smith_normal_form_of_isDiscreteValuationRing A
  set L' : GL (Fin n) R := nonsingInvUnit L hL
  set Q' : GL (Fin n) R := nonsingInvUnit Q hQ
  have hA' : (↑L'⁻¹ : Matrix (Fin n) (Fin n) R) * diagonal s * (↑Q'⁻¹ : Matrix (Fin n) (Fin n) R) =
      A :=
    (GeneralLinearGroup.inv_mul_mul_inv_eq_iff_mul_mul_eq L' Q').2 hLAQ
  -- the diagonal entries are nonzero, since `A` is nonsingular
  have hdetA : A.det ≠ 0 := fun h0 ↦ by
    have hπ0 : algebraMap R K ϖ ≠ 0 := hπ ▸ π.ne_zero
    have h := congrArg (algebraMap R K) h0
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hA, det_smul, map_zero] at h
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hπ0))
      ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero h
  have hs0 (i : Fin n) : s i ≠ 0 := by
    have h := congrArg det hLAQ
    rw [det_diagonal, det_mul, det_mul] at h
    exact Finset.prod_ne_zero_iff.mp (h ▸ mul_ne_zero (mul_ne_zero hL.ne_zero hdetA) hQ.ne_zero)
      i (Finset.mem_univ i)
  choose e u hsu using fun i ↦ IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hs0 i) hϖ
  have he : Monotone e := fun i j hij ↦ by
    have h := hs hij
    rw [hsu, hsu, Units.mul_left_dvd, Units.dvd_mul_left] at h
    exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp h
  refine ⟨fun i ↦ (e i : ℤ) + -(m : ℤ), fun i j hij ↦ by have := he hij; dsimp only; omega,
    mem_doubleCoset.mpr ⟨_, ⟨L'⁻¹ * diagGL u, rfl⟩, _,
      ⟨Q'⁻¹, rfl⟩, ?_⟩⟩
  -- `π^m g = L⁻¹ diag(u) diag(π^e) Q⁻¹`, so `g = L⁻¹ diag(u) diag(π^{e - m}) Q⁻¹`
  have hmat : GeneralLinearGroup.scalar (Fin n) (π ^ (m : ℤ)) * g =
      GeneralLinearGroup.map (algebraMap R K) (L'⁻¹ * diagGL u) *
        diagGL (fun i ↦ π ^ (e i : ℤ)) *
          GeneralLinearGroup.map (algebraMap R K) Q'⁻¹ := by
    refine Units.ext ?_
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_eq_diagonal_mul,
      zpow_natCast, Units.val_pow_eq_pow_val, ← hπ, ← hA, ← hA']
    simp only [Units.val_mul, coe_diagGL_zpow_natCast hπ, GeneralLinearGroup.val_map_apply,
      diagGL_coe, ← RingHom.mapMatrix_apply, ← map_mul]
    rw [show s = fun i ↦ (u i : R) * ϖ ^ e i from funext hsu, ← diagonal_mul_diagonal]
    simp only [Matrix.mul_assoc]
  have hc := Subgroup.mem_center_iff.mp (scalar_mem_center (ι := Fin n) (π ^ (-(m : ℤ))))
  rw [diagGL_zpow_add_const, ← mul_assoc, hc, mul_assoc, mul_assoc,
    ← mul_assoc (GeneralLinearGroup.map _ _), ← hmat, ← mul_assoc, ← map_mul, ← _root_.zpow_add,
    neg_add_cancel, zpow_zero, map_one,
    one_mul]

/-- Two diagonal elements `diag(π^a)` and `diag(π^b)` of `GLₙ(K)` with monotone exponents lie in the
same `GLₙ(R)` double coset only if `a = b`. -/
private theorem eq_of_monotone_of_diagGL_zpow_mem_doubleCoset (hϖ : Irreducible ϖ)
    (hπ : algebraMap R K ϖ = π) {a b : Fin n → ℤ} (ha : Monotone a) (hb : Monotone b)
    (hab : (diagGL fun i ↦ π ^ a i) ∈ doubleCoset (diagGL fun i ↦ π ^ b i)
      (GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range
      (GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range) : a = b := by
  obtain ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, hxy⟩ := mem_doubleCoset.mp hab
  -- shift both exponent vectors into the nonnegative range
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ i, 0 ≤ a i + m ∧ 0 ≤ b i + m := by
    obtain ⟨c, hc⟩ := (Set.finite_range a).bddBelow
    obtain ⟨d, hd⟩ := (Set.finite_range b).bddBelow
    refine ⟨(-min c d).toNat, fun i ↦ ?_⟩
    have := hc ⟨i, rfl⟩
    have := hd ⟨i, rfl⟩
    have := Int.self_le_toNat (-min c d)
    omega
  set α : Fin n → ℕ := fun i ↦ (a i + m).toNat
  set β : Fin n → ℕ := fun i ↦ (b i + m).toNat
  have hαa : ∀ i, (α i : ℤ) = a i + m := fun i ↦ Int.toNat_of_nonneg (hm i).1
  have hβb : ∀ i, (β i : ℤ) = b i + m := fun i ↦ Int.toNat_of_nonneg (hm i).2
  have hαmono : Monotone α := fun i j hij ↦ Int.toNat_le_toNat (by have := ha hij; omega)
  have hβmono : Monotone β := fun i j hij ↦ Int.toNat_le_toNat (by have := hb hij; omega)
  -- `diag(π^α) = x · diag(π^β) · y`, an equation between images of integral matrices
  have hGL : (diagGL fun i ↦ π ^ (α i : ℤ) : GL (Fin n) K) =
      GeneralLinearGroup.map (algebraMap R K) x * diagGL (fun i ↦ π ^ (β i : ℤ)) *
        GeneralLinearGroup.map (algebraMap R K) y := by
    have hc := Subgroup.mem_center_iff.mp (scalar_mem_center (ι := Fin n) (π ^ (m : ℤ)))
    simp only [hαa, hβb, diagGL_zpow_add_const, hxy, ← mul_assoc]
    rw [hc]
  have hR := congrArg (fun g : GL (Fin n) K ↦ (g : Matrix (Fin n) (Fin n) K)) hGL
  simp only [Units.val_mul, coe_diagGL_zpow_natCast hπ, GeneralLinearGroup.val_map_apply,
    ← RingHom.mapMatrix_apply, ← map_mul] at hR
  have hαβ := eq_of_diagonal_pow_eq_mul_mul hϖ hαmono hβmono _ _
    (Matrix.map_injective (IsFractionRing.injective R K) hR)
  funext i
  have := congrFun hαβ i
  have := hαa i
  have := hβb i
  omega

/-- **Uniqueness in the Cartan decomposition of `GLₙ(K)`.** If `g` lies in the `GLₙ(R)` double
cosets of `diag(π^a)` and `diag(π^b)` with `a`, `b` monotone, then `a = b`. Here `π` is the image
of a uniformizer of the discrete valuation ring `R` in its fraction field `K`. -/
theorem eq_of_monotone_of_mem_doubleCoset_diagGL_zpow (hϖ : Irreducible ϖ)
    (hπ : algebraMap R K ϖ = π) {a b : Fin n → ℤ} (ha : Monotone a) (hb : Monotone b)
    {g : GL (Fin n) K}
    (hga : g ∈ doubleCoset (diagGL fun i ↦ π ^ a i)
      (GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range
      (GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range)
    (hgb : g ∈ doubleCoset (diagGL fun i ↦ π ^ b i)
      (GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range
      (GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range) : a = b := by
  -- `diag(π^a)` lies in the double coset of `diag(π^b)`
  have hab : (diagGL fun i ↦ π ^ a i) ∈ doubleCoset (diagGL fun i ↦ π ^ b i)
      (GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range
      (GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range := by
    rw [← doubleCoset_eq_of_mem hgb, doubleCoset_eq_of_mem hga]
    exact mem_doubleCoset_self _ _ _
  exact eq_of_monotone_of_diagGL_zpow_mem_doubleCoset hϖ hπ ha hb hab

/-- **The Cartan decomposition of `GLₙ(K)`.** Every `g ∈ GLₙ(K)` lies in the `GLₙ(R)` double
coset of `diag(π^{a₀}, …, π^{aₙ₋₁})` for exactly one monotone exponent vector `a`. Here `π` is the
image of a uniformizer of the discrete valuation ring `R` in its fraction field `K`. -/
theorem existsUnique_monotone_mem_doubleCoset_diagGL_zpow (hϖ : Irreducible ϖ)
    (hπ : algebraMap R K ϖ = π) (g : GL (Fin n) K) :
    ∃! a : Fin n → ℤ, Monotone a ∧ g ∈ doubleCoset (diagGL fun i ↦ π ^ a i)
      (GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range
      (GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range :=
  let ⟨a, ha, hga⟩ := exists_monotone_mem_doubleCoset_diagGL_zpow hϖ hπ g
  ⟨a, ⟨ha, hga⟩, fun _ ⟨hb, hgb⟩ ↦
    (eq_of_monotone_of_mem_doubleCoset_diagGL_zpow hϖ hπ ha hb hga hgb).symm⟩

end TauCeti

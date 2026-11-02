/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.ElementaryDivisors
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.UpperTriCosets
public import TauCeti.NumberTheory.HeckeRing.GLn.CoprimeMul
import Mathlib.Data.Nat.Prime.Int
import TauCeti.Data.ZMod.Units
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.CoprimeCosets
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Adjugate

/-!
# Coprime products of the double cosets `Γ₁(N) · diag(1, n) · Γ₁(N)`

Write `Dₙ = Γ₁(N) · diag(1, n) · Γ₁(N)` for the double coset whose operator is the Hecke operator
`Tₙ` at level `Γ₁(N)`. For coprime `m` and `n` this file proves

`Dₘ · Dₙ = Dₘₙ`,

and that the products `a b` of elements `a ∈ Dₘ`, `b ∈ Dₙ` have no right-coset collisions beyond
those of the factors: the right coset `Γ₁(N) a b` determines `Γ₁(N) b`. Together these are the two
hypotheses of the single-coset composition law for Hecke operators, so they give
`T_{mn} = Tₘ Tₙ` for the Hecke operators on modular symbols
(`TauCeti.ModularSymbols.heckeTSymbol_mul_of_coprime`). No condition relating `m` or `n` to the
level is needed.

The first identity runs through the elementary divisors at level `Γ₀(N)`
(`HeckeRing.GL2.mem_doubleCoset_natDiagGL_of_primitive`): an element of `Dₘ Dₙ` is primitive
because the determinants are coprime, so it lies in `Γ₀(N) · diag(1, mn) · Γ₀(N)`, and the
congruence `a ≡ 1 (mod N)` on its upper-left entry brings it down to `Γ₁(N)`
(`HeckeRing.GL2.mem_doubleCoset_Gamma1_of_mem_doubleCoset_Gamma0`). The descent moves a
diamond label across `diag(1, n)` by a matrix of `Γ₀(N)` whose upper-right entry is divisible
by `n`, which exists for every `n`, whether or not it is prime to the level.

The second is integrality: if `Γ₁(N) a b = Γ₁(N) a' b'`, then `b' b⁻¹` becomes integral after
multiplication by `n` (as `b'` and `b` have determinant `n`) and after multiplication by `m` (as it
is conjugate through `a`, `a'` to an element of `Γ₁(N)`), hence is integral, and the congruences
satisfied by `b` and `b'` put it in `Γ₁(N)`.

## Main results

* `HeckeRing.GL2.mem_doubleCoset_Gamma1_of_mem_doubleCoset_Gamma0`: an element of
  `Γ₀(N) · diag(1, n) · Γ₀(N)` with upper-left entry `≡ 1 (mod N)` lies in `Dₙ`.
* `HeckeRing.GL2.mem_doubleCoset_natDiagGL_Gamma1_of_primitive`: a primitive integral matrix of
  determinant `n` which is `!![1, *; 0, *]` modulo `N` lies in `Dₙ`.
* `HeckeRing.GL2.natDiagGL_mul_mapGL_mul_natDiagGL_mem_doubleCoset`: for coprime `m`, `n` and
  `γ ∈ Γ₁(N)`, `diag(1, m) γ diag(1, n) ∈ Dₘₙ`.
* `HeckeRing.GL2.doubleCoset_natDiagGL_mul_of_coprime`: `Dₘₙ = Dₘ · Dₙ` for coprime `m`, `n`.
* `HeckeRing.GL2.op_smul_eq_of_op_mul_smul_eq`: for coprime `m`, `n`, `a, a' ∈ Dₘ` and
  `b, b' ∈ Dₙ`, the equality `Γ₁(N) a b = Γ₁(N) a' b'` forces `Γ₁(N) b = Γ₁(N) b'`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3–3.4: Proposition 3.32 for the elementary divisors at level `Γ₀(N)`, and Proposition 3.16
  for the level-one coprime product, `HeckeRing.GLn.mul_mem_doubleCoset_of_coprime`.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.2.4.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup DoubleCoset HeckeRing.GLn

open scoped MatrixGroups Pointwise

namespace HeckeRing.GL2

variable {N : ℕ}

/-- **The elements of `Dₙ` are `!![1, *; 0, *]` modulo `N`.** Every element of
`Γ₁(N) · diag(1, n) · Γ₁(N)` is represented by an integral matrix whose upper-left entry is `1`
and whose lower-left entry is `0` modulo `N`. -/
theorem exists_intMatrix_of_mem_doubleCoset_natDiagGL {n : ℕ} (hn : 0 < n) {x : GL (Fin 2) ℚ}
    (hx : x ∈ doubleCoset (natDiagGL 2 ![1, n]) ((Gamma1 N).map (mapGL ℚ))
      ((Gamma1 N).map (mapGL ℚ))) :
    ∃ X : Matrix (Fin 2) (Fin 2) ℤ,
      (↑x : Matrix (Fin 2) (Fin 2) ℚ) = X.map (Int.cast : ℤ → ℚ) ∧
        ((X 0 0 : ℤ) : ZMod N) = 1 ∧ ((X 1 0 : ℤ) : ZMod N) = 0 := by
  obtain ⟨_, ⟨g₁, hg₁, rfl⟩, _, ⟨g₂, hg₂, rfl⟩, rfl⟩ := mem_doubleCoset.mp hx
  obtain ⟨h₁00, -, h₁10⟩ := (Gamma1_mem N g₁).mp hg₁
  obtain ⟨h₂00, -, h₂10⟩ := (Gamma1_mem N g₂).mp hg₂
  refine ⟨_, mapGL_mul_coe_eq_intMatrix 2 g₁ g₂ _ _ (coe_natDiagGL_one_eq_map hn), ?_, ?_⟩
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    simp [h₁00, h₂00, h₂10]
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    simp [h₁10, h₂00, h₂10]

/-- **Descent from `Γ₀(N)` to `Γ₁(N)`.** An element of `Γ₀(N) · diag(1, n) · Γ₀(N)` whose
integral matrix has upper-left entry `≡ 1 (mod N)` lies in `Γ₁(N) · diag(1, n) · Γ₁(N)`. No
condition relating `n` to `N` is needed.

Writing the element as `g₁ · diag(1, n) · g₂` with `gᵢ ∈ Γ₀(N)`, the congruence says that the
diamond labels of `g₁` and `g₂` are inverse to each other, and a matrix `A ∈ Γ₀(N)` with
upper-right entry divisible by `n` and the label of `g₁` moves across `diag(1, n)` to correct
both factors at once. -/
theorem mem_doubleCoset_Gamma1_of_mem_doubleCoset_Gamma0 {n : ℕ} (hn : 0 < n)
    {x : GL (Fin 2) ℚ} {X : Matrix (Fin 2) (Fin 2) ℤ}
    (hX : (↑x : Matrix (Fin 2) (Fin 2) ℚ) = X.map (Int.cast : ℤ → ℚ))
    (hX00 : ((X 0 0 : ℤ) : ZMod N) = 1)
    (hx : x ∈ doubleCoset (natDiagGL 2 ![1, n]) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ))) :
    x ∈ doubleCoset (natDiagGL 2 ![1, n]) ((Gamma1 N).map (mapGL ℚ))
      ((Gamma1 N).map (mapGL ℚ)) := by
  obtain ⟨_, ⟨g₁, hg₁, rfl⟩, _, ⟨g₂, hg₂, rfl⟩, rfl⟩ := mem_doubleCoset.mp hx
  have hXeq : X = (g₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (n : ℤ)] * g₂ :=
    Matrix.map_injective Int.cast_injective
      (hX.symm.trans (mapGL_mul_coe_eq_intMatrix 2 g₁ g₂ _ _ (coe_natDiagGL_one_eq_map hn)))
  -- the upper-left entry of `x` is `g₁₀₀ g₂₀₀` modulo `N`, so `g₂₀₀ ≡ g₁₁₁` modulo `N`
  have h₁ := intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hg₁
  have h₀₀ : ((g₁ 0 0 : ℤ) : ZMod N) * ((g₂ 0 0 : ℤ) : ZMod N) = 1 := by
    rw [hXeq] at hX00
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at hX00
    push_cast at hX00
    simpa [Gamma0_mem.mp hg₂] using hX00
  have h₂₁ : ((g₂ 0 0 : ℤ) : ZMod N) = ((g₁ 1 1 : ℤ) : ZMod N) := by
    linear_combination (g₁ 1 1 : ZMod N) * h₀₀ - (g₂ 0 0 : ZMod N) * h₁
  -- an integer `t ≡ g₁₁₁ (mod N)` coprime to `n N`
  have : NeZero n := ⟨hn.ne'⟩
  let u : (ZMod N)ˣ := ⟨g₁ 1 1, g₁ 0 0, by rw [mul_comm]; exact h₁, h₁⟩
  obtain ⟨t, htc, htu⟩ := ZMod.exists_isCoprime_mul_intCast_eq n u
  have ht : ((t : ℤ) : ZMod N) = ((g₁ 1 1 : ℤ) : ZMod N) := htu
  obtain ⟨A, A', hA10, hA11, hA'10, hA'11, hcomm⟩ :=
    exists_natDiagGL_mul_mapGL_eq_of_isCoprime hn htc
  refine mem_doubleCoset.mpr ⟨mapGL ℚ (g₁ * A'⁻¹), Subgroup.mem_map_of_mem _ ?_,
    mapGL ℚ (A * g₂), Subgroup.mem_map_of_mem _ ?_, ?_⟩
  · -- `g₁` and `A'` have the same lower row modulo `N`
    rw [mul_inv_mem_Gamma1_iff_dvd_sub, hA'10, hA'11]
    refine ⟨dvd_sub (mem_Gamma0_iff_dvd.mp hg₁) (dvd_mul_left _ _), ?_⟩
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, ht]
  · -- `A` and `g₂⁻¹` have the same lower row modulo `N`
    rw [← inv_inv g₂, mul_inv_mem_Gamma1_iff_dvd_sub, hA10, hA11, SL2_inv_expl]
    refine ⟨?_, ?_⟩
    · simpa using dvd_add (dvd_refl (N : ℤ)) (mem_Gamma0_iff_dvd.mp hg₂)
    · rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, ht, ← h₂₁]
      simp
  · -- `A'⁻¹ · diag(1, n) · A = diag(1, n)`
    have hδ : (mapGL ℚ A')⁻¹ * natDiagGL 2 ![1, n] * mapGL ℚ A = natDiagGL 2 ![1, n] := by
      rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [map_mul, map_mul, map_inv]
    conv_lhs => rw [← hδ]
    group

/-- **A primitive matrix that is `!![1, *; 0, *]` modulo `N` lies in `Dₙ`.** If `x ∈ GL₂(ℚ)` is
represented by an integral matrix `X` of determinant `n` whose entries have no common prime
factor, with `X₀₀ ≡ 1` and `X₁₀ ≡ 0` modulo `N`, then `x ∈ Γ₁(N) · diag(1, n) · Γ₁(N)`. This is
the `Γ₁(N)` form of Shimura's description of a double coset by its elementary divisors. -/
theorem mem_doubleCoset_natDiagGL_Gamma1_of_primitive [NeZero N] (n : ℕ) {x : GL (Fin 2) ℚ}
    {X : Matrix (Fin 2) (Fin 2) ℤ}
    (hX : (↑x : Matrix (Fin 2) (Fin 2) ℚ) = X.map (Int.cast : ℤ → ℚ))
    (hX00 : ((X 0 0 : ℤ) : ZMod N) = 1) (hX10 : ((X 1 0 : ℤ) : ZMod N) = 0)
    (hdet : (↑x : Matrix (Fin 2) (Fin 2) ℚ).det = n)
    (hprim : ∀ p : ℕ, p.Prime → ¬((p : ℤ) ∣ X 0 0 ∧ (p : ℤ) ∣ X 0 1 ∧ (p : ℤ) ∣ X 1 0 ∧
      (p : ℤ) ∣ X 1 1)) :
    x ∈ doubleCoset (natDiagGL 2 ![1, n]) ((Gamma1 N).map (mapGL ℚ))
      ((Gamma1 N).map (mapGL ℚ)) := by
  have hn : 0 < n := by
    have hne := Matrix.GeneralLinearGroup.det_ne_zero x
    rw [hdet] at hne
    exact Nat.pos_of_ne_zero (by exact_mod_cast hne)
  refine mem_doubleCoset_Gamma1_of_mem_doubleCoset_Gamma0 hn hX hX00 <|
    mem_doubleCoset_natDiagGL_of_primitive N n x X hX
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hX10)
      (Int.isUnit_intCast_iff_gcd_eq_one.mp (hX00 ▸ isUnit_one)) hdet hprim

/-- **The coprime sandwich.** For coprime `m`, `n` and `γ ∈ Γ₁(N)`, the product
`diag(1, m) · γ · diag(1, n)` lies in `Γ₁(N) · diag(1, m n) · Γ₁(N)`. Its integral matrix
`!![a, b n; m c, m n d]` is primitive: a prime dividing `a` and `b n` but not `b` divides `n`,
hence not `m`, hence divides `c`, and no prime divides both `a` and `c`. -/
theorem natDiagGL_mul_mapGL_mul_natDiagGL_mem_doubleCoset [NeZero N] {m n : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : m.Coprime n) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) :
    natDiagGL 2 ![1, m] * mapGL ℚ γ * natDiagGL 2 ![1, n] ∈
      doubleCoset (natDiagGL 2 ![1, m * n]) ((Gamma1 N).map (mapGL ℚ))
        ((Gamma1 N).map (mapGL ℚ)) := by
  obtain ⟨h00, -, h10⟩ := (Gamma1_mem N γ).mp hγ
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  have hX : (↑(natDiagGL 2 ![1, m] * mapGL ℚ γ * natDiagGL 2 ![1, n]) :
      Matrix (Fin 2) (Fin 2) ℚ) =
      (!![γ 0 0, γ 0 1 * n; m * γ 1 0, m * n * γ 1 1]).map (Int.cast : ℤ → ℚ) := by
    rw [Units.val_mul, Units.val_mul, coe_natDiagGL_one hm, coe_natDiagGL_one hn,
      coe_mapGL_int_rat_fin_two, mul_fin_two, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp; ring
  refine mem_doubleCoset_natDiagGL_Gamma1_of_primitive (m * n) hX (by simpa using h00)
    (by simp [h10]) ?_ ?_
  · rw [hX, ← Int.cast_det, det_fin_two_of]
    push_cast
    linear_combination ((m : ℚ) * n) * (by exact_mod_cast hdet :
      ((γ 0 0 : ℤ) : ℚ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1)
  · rintro p hp ⟨ha, hb, hc, -⟩
    have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    -- a prime dividing both entries of a row or a column of `γ` divides `det γ = 1`
    have hrow : ¬((p : ℤ) ∣ γ 0 0 ∧ (p : ℤ) ∣ γ 0 1) := fun h ↦ hp'.not_dvd_one <| hdet ▸
      dvd_sub (dvd_mul_of_dvd_left h.1 _) (dvd_mul_of_dvd_left h.2 _)
    have hcol : ¬((p : ℤ) ∣ γ 0 0 ∧ (p : ℤ) ∣ γ 1 0) := fun h ↦ hp'.not_dvd_one <| hdet ▸
      dvd_sub (dvd_mul_of_dvd_left h.1 _) (dvd_mul_of_dvd_right h.2 _)
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one] at ha hb hc
    rcases hp'.dvd_or_dvd hb with hb | hb
    · exact hrow ⟨ha, hb⟩
    · -- `p ∣ n`, so `p ∤ m` and `p ∣ m c` gives `p ∣ c`
      have hpm : ¬(p : ℤ) ∣ m := fun hpm ↦ hp.one_lt.ne' <| Nat.dvd_one.mp <|
        hmn ▸ Nat.dvd_gcd (Int.natCast_dvd_natCast.mp hpm) (Int.natCast_dvd_natCast.mp hb)
      exact hcol ⟨ha, (hp'.dvd_or_dvd hc).resolve_left hpm⟩

/-- **`Dₘₙ = Dₘ · Dₙ` for coprime `m`, `n`.** The product set of the double cosets of `diag(1, m)`
and `diag(1, n)` at level `Γ₁(N)` is the single double coset of `diag(1, m n)`. -/
theorem doubleCoset_natDiagGL_mul_of_coprime [NeZero N] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : m.Coprime n) :
    doubleCoset (natDiagGL 2 ![1, m * n]) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) =
      doubleCoset (natDiagGL 2 ![1, m]) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) *
        doubleCoset (natDiagGL 2 ![1, n]) ((Gamma1 N).map (mapGL ℚ))
          ((Gamma1 N).map (mapGL ℚ)) := by
  have hδ : natDiagGL 2 ![1, m] * natDiagGL 2 ![1, n] = natDiagGL 2 ![1, m * n] := by
    rw [natDiagGL_mul 2 _ _ (fun i ↦ by fin_cases i <;> simp [hm]) fun i ↦ by
      fin_cases i <;> simp [hn]]
    congr 1
    ext i
    fin_cases i <;> simp
  ext x
  constructor
  · rintro hx
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := mem_doubleCoset.mp hx
    have hsplit : h₁ * natDiagGL 2 ![1, m * n] * h₂ =
        h₁ * natDiagGL 2 ![1, m] * (natDiagGL 2 ![1, n] * h₂) := by rw [← hδ]; group
    rw [hsplit]
    exact Set.mul_mem_mul (mem_doubleCoset.mpr ⟨h₁, hh₁, 1, one_mem _, by group⟩)
      (mem_doubleCoset.mpr ⟨1, one_mem _, h₂, hh₂, by group⟩)
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := mem_doubleCoset.mp hy
    obtain ⟨h₃, hh₃, h₄, hh₄, rfl⟩ := mem_doubleCoset.mp hz
    obtain ⟨γ, hγ, hγeq⟩ := Subgroup.mem_map.mp (mul_mem hh₂ hh₃)
    obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ :=
      mem_doubleCoset.mp (natDiagGL_mul_mapGL_mul_natDiagGL_mem_doubleCoset hm hn hmn hγ)
    refine mem_doubleCoset.mpr ⟨h₁ * k₁, mul_mem hh₁ hk₁, k₂ * h₄, mul_mem hk₂ hh₄, ?_⟩
    calc h₁ * natDiagGL 2 ![1, m] * h₂ * (h₃ * natDiagGL 2 ![1, n] * h₄)
        = h₁ * (natDiagGL 2 ![1, m] * (h₂ * h₃) * natDiagGL 2 ![1, n]) * h₄ := by group
      _ = h₁ * k₁ * natDiagGL 2 ![1, m * n] * (k₂ * h₄) := by rw [← hγeq, hk]; group

/-- The elements of `Γ₁(N) · diag(1, k) · Γ₁(N)` have determinant `k`. -/
private lemma det_of_mem_doubleCoset_natDiagGL {k : ℕ} (hk : 0 < k) {y : GL (Fin 2) ℚ}
    (hy : y ∈ doubleCoset (natDiagGL 2 ![1, k]) ((Gamma1 N).map (mapGL ℚ))
      ((Gamma1 N).map (mapGL ℚ))) :
    (↑y : Matrix (Fin 2) (Fin 2) ℚ).det = k := by
  have hle := (Subgroup.map_mono (Gamma1_in_Gamma0 N)).trans (Gamma0_map_le_SLnZ N)
  rw [det_eq_of_mem_doubleCoset_of_le_SLnZ 2 hle hle hy,
    natDiagGL_det 2 _ fun i ↦ by fin_cases i <;> simp [hk]]
  simp

/-- **Products from coprime double cosets have no extra right-coset collisions.** For coprime
`m`, `n`, elements `a, a' ∈ Dₘ` and `b, b' ∈ Dₙ` at level `Γ₁(N)`, if `Γ₁(N) a b = Γ₁(N) a' b'`
then `Γ₁(N) b = Γ₁(N) b'`.

The quotient `b' b⁻¹` is a determinant-one matrix which is integral after scaling by `n`, being
`b' · adj(b) / n`, and after scaling by `m`, being conjugate through `a`, `a'` to an element of
`Γ₁(N)`; so it is integral, and comparing `b' = (b' b⁻¹) b` modulo `N` puts it in `Γ₁(N)`. -/
theorem op_smul_eq_of_op_mul_smul_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : m.Coprime n) {a a' b b' : GL (Fin 2) ℚ}
    (ha : a ∈ doubleCoset (natDiagGL 2 ![1, m]) ((Gamma1 N).map (mapGL ℚ))
      ((Gamma1 N).map (mapGL ℚ)))
    (ha' : a' ∈ doubleCoset (natDiagGL 2 ![1, m]) ((Gamma1 N).map (mapGL ℚ))
      ((Gamma1 N).map (mapGL ℚ)))
    (hb : b ∈ doubleCoset (natDiagGL 2 ![1, n]) ((Gamma1 N).map (mapGL ℚ))
      ((Gamma1 N).map (mapGL ℚ)))
    (hb' : b' ∈ doubleCoset (natDiagGL 2 ![1, n]) ((Gamma1 N).map (mapGL ℚ))
      ((Gamma1 N).map (mapGL ℚ)))
    (h : MulOpposite.op (a * b) • ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) =
      MulOpposite.op (a' * b') • ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ))) :
    MulOpposite.op b • ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) =
      MulOpposite.op b' • ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) := by
  obtain ⟨A, hA, -, -⟩ := exists_intMatrix_of_mem_doubleCoset_natDiagGL hm ha
  obtain ⟨A', hA', -, -⟩ := exists_intMatrix_of_mem_doubleCoset_natDiagGL hm ha'
  obtain ⟨B, hB, hB00, hB10⟩ := exists_intMatrix_of_mem_doubleCoset_natDiagGL hn hb
  obtain ⟨B', hB', hB'00, hB'10⟩ := exists_intMatrix_of_mem_doubleCoset_natDiagGL hn hb'
  obtain ⟨σh, -, hσh⟩ := Subgroup.mem_map.mp (rightCoset_eq_iff _ |>.mp h)
  obtain ⟨H, hH⟩ := (hasIntEntries_iff 2).mp (hasIntEntries_of_mem_SLnZ 2 (coe_mem_SLnZ 2 σh))
  set Y := b' * b⁻¹ with hYdef
  -- `Y` is integral after scaling by `n` and after scaling by `m`
  have hYn : (n : ℚ) • (↑Y : Matrix (Fin 2) (Fin 2) ℚ) =
      (B' * B.adjugate).map (Int.cast : ℤ → ℚ) := by
    rw [hYdef, Units.val_mul, ← Matrix.mul_smul,
      Matrix.GeneralLinearGroup.natCast_smul_coe_inv hB (det_of_mem_doubleCoset_natDiagGL hn hb),
      hB', Matrix.map_mul_intCast]
  have hYm : (m : ℚ) • (↑Y : Matrix (Fin 2) (Fin 2) ℚ) =
      (A'.adjugate * H * A).map (Int.cast : ℤ → ℚ) := by
    have hY : Y = a'⁻¹ * mapGL ℚ σh * a := by rw [hσh, hYdef]; group
    rw [hY, Units.val_mul, Units.val_mul, ← Matrix.smul_mul, ← Matrix.smul_mul,
      Matrix.GeneralLinearGroup.natCast_smul_coe_inv hA' (det_of_mem_doubleCoset_natDiagGL hm ha'),
      hA, hH,
      Matrix.map_mul_intCast, Matrix.map_mul_intCast]
  have hYdet : (↑Y : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    rw [hYdef, Units.val_mul, Matrix.det_mul, Matrix.coe_units_inv, Matrix.det_nonsing_inv,
      det_of_mem_doubleCoset_natDiagGL hn hb', det_of_mem_doubleCoset_natDiagGL hn hb,
      Ring.inverse_eq_inv', mul_inv_cancel₀ (by exact_mod_cast hn.ne')]
  obtain ⟨σ, hσ⟩ := (mem_SLnZ_iff 2).mp <| mem_SLnZ_of_coprime_scaling 2 Y m n hmn hYdet
    (fun i j ↦ ⟨_, by simpa using congrFun (congrFun hYm i) j⟩)
    (fun i j ↦ ⟨_, by simpa using congrFun (congrFun hYn i) j⟩)
  -- `σ B = B'` over `ℤ`, and reading it modulo `N` puts `σ` in `Γ₁(N)`
  have hσB : (σ : Matrix (Fin 2) (Fin 2) ℤ) * B = B' := by
    have hmul : (mapGL ℚ σ : GL (Fin 2) ℚ) * b = b' := by rw [hσ, hYdef, inv_mul_cancel_right]
    have hQ : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * B).map (Int.cast : ℤ → ℚ) =
        B'.map (Int.cast : ℤ → ℚ) := by
      rw [Matrix.map_mul_intCast, ← hB, ← hB', ← hmul, Units.val_mul]
      simp [mapGL_coe_matrix, algebraMap_int_eq]
    exact Matrix.map_injective Int.cast_injective hQ
  rw [rightCoset_eq_iff, ← hYdef, ← hσ]
  exact Subgroup.mem_map_of_mem _ (mem_Gamma1_of_mul_eq hσB hB00 hB10 hB'00 hB'10)

end HeckeRing.GL2

end

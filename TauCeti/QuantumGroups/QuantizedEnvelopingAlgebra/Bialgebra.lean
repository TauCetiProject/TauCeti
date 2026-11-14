/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Basic
import Mathlib.Tactic

/-!
# The bialgebra structure on a quantized enveloping algebra

This file constructs the counit and coproduct of the Drinfeld–Jimbo quantized enveloping algebra
`TauCeti.QuantizedEnvelopingAlgebra D q` of a Cartan datum `D : TauCeti.CartanDatum ι X Y` over a
field `K`:

* `ε(Eᵢ) = 0`, `ε(Fᵢ) = 0`, `ε(K_y) = 1` (unconditional on `q`);
* `Δ(Eᵢ) = Eᵢ ⊗ 1 + Kᵢ ⊗ Eᵢ`, `Δ(Fᵢ) = Fᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ Fᵢ`, `Δ(K_y) = K_y ⊗ K_y`.

The coproduct `comulAlgHom` descends through the divided-power presentation whenever `q ≠ 0` and
the Serre-degree quantum factorials `[1 - aᵢⱼ]_(qᵢ)!` (`i ≠ j`) are nonzero: expanding
`(Eᵢ ⊗ 1 + Kᵢ ⊗ Eᵢ)^(r)` by the divided-power `q`-binomial theorem splits the `E`-Serre expression
into two root-disjoint parts whose mixed slices vanish by the alternating `q`-binomial identity
`TauCeti.sum_range_neg_one_pow_mul_zpow_mul_quantumBinomial`, while the `F`-Serre relation follows
from the `E`-Serre relation along `(ω ⊗ ω) ∘ flip` for the Chevalley involution `ω`.

At a generic quantum parameter `[Fact (IsGenericQuantumParameter q)]`, all quantum factorials at
`qᵢ = q^(dᵢ)` are nonzero, registering a canonical `Bialgebra` instance. We also derive the
divided-power coproduct formulas for `Δ(Eᵢ^(n))` and `Δ(Fᵢ^(n))`, introduce the
Kashiwara-normalized Chevalley operators `eᵢ = Kᵢ⁻¹ Eᵢ` and `fᵢ = Fᵢ Kᵢ` with their coproducts,
and upgrade `TauCeti.QuantizedEnvelopingAlgebra.map` along morphisms of Cartan data to a bialgebra
homomorphism.

## Main definitions

* `TauCeti.QuantizedEnvelopingAlgebra.counit`: the unconditional augmentation `U →ₐ[K] K`.
* `TauCeti.QuantizedEnvelopingAlgebra.comulAlgHom` and `bialgebraOfSerre`: explicit-hypothesis
  coproduct and `Bialgebra` structure under `q ≠ 0` and Serre-degree factorial nonvanishing.
* `TauCeti.QuantizedEnvelopingAlgebra.instBialgebra`: canonical `Bialgebra` instance at
  `[Fact (IsGenericQuantumParameter q)]`.
* `TauCeti.QuantizedEnvelopingAlgebra.normalizedE` and `normalizedF`: the normalized generators
  `eᵢ = Kᵢ⁻¹ Eᵢ` and `fᵢ = Fᵢ Kᵢ`.
* `TauCeti.QuantizedEnvelopingAlgebra.mapBialgHom`: functoriality of the bialgebra structure along
  `TauCeti.CartanDatum.Hom`.

## Main results

* `TauCeti.QuantizedEnvelopingAlgebra.comul_eDividedPower` and `comul_fDividedPower`:
  `Δ(Eᵢ^(n)) = ∑_{a=0}^n qᵢ^(a(n-a)) Eᵢ^(a) Kᵢ^(n-a) ⊗ Eᵢ^(n-a)` and
  `Δ(Fᵢ^(n)) = ∑_{a=0}^n qᵢ^(a(n-a)) Fᵢ^(a) ⊗ Fᵢ^(n-a) Kᵢ^(-a)`.
* `TauCeti.QuantizedEnvelopingAlgebra.comul_normalizedE` and `comul_normalizedF`:
  `Δ(eᵢ) = eᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ eᵢ` and `Δ(fᵢ) = fᵢ ⊗ 1 + Kᵢ ⊗ fᵢ`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, §§4.8–4.9.
-/

public section

open Finset
open scoped TensorProduct

namespace TauCeti.QuantizedEnvelopingAlgebra

variable {K ι X Y : Type*} [Field K] [AddCommGroup X] [AddCommGroup Y]

/-! ### Unconditional counit -/

section Counit

private noncomputable def counitTuple (D : CartanDatum ι X Y) (q : K) :
    GeneratorTuple D q K where
  e _ := 0
  f _ := 0
  k _ := 1
  k_zero := rfl
  k_mul_k _ _ := mul_one 1
  k_mul_e _ _ := by simp
  k_mul_f _ _ := by simp
  e_mul_f_sub_f_mul_e_self _ := by simp
  e_mul_f_sub_f_mul_e_of_ne _ := by simp
  serre_e _ := by simp
  serre_f _ := by simp

/-- The unconditional augmentation `ε : QuantizedEnvelopingAlgebra D q →ₐ[K] K`, sending `Eᵢ` and
`Fᵢ` to `0` and every toral generator `K_y` to `1`. -/
noncomputable def counit (D : CartanDatum ι X Y) (q : K) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] K :=
  lift (counitTuple D q)

variable {D : CartanDatum ι X Y} {q : K}

@[simp]
theorem counit_apply_e (i : ι) : counit D q (e D q i) = 0 :=
  lift_e _ i

@[simp]
theorem counit_apply_f (i : ι) : counit D q (f D q i) = 0 :=
  lift_f _ i

@[simp]
theorem counit_apply_k (y : Y) : counit D q (k D q y) = 1 :=
  lift_k _ y

theorem counit_apply_ki (i : ι) : counit D q (ki D q i) = 1 :=
  counit_apply_k (D.simpleTorus i)

theorem counit_apply_kiInv (i : ι) : counit D q (kiInv D q i) = 1 :=
  counit_apply_k (-D.simpleTorus i)

@[simp]
theorem counit_chevalleyInvolution (x : QuantizedEnvelopingAlgebra D q) :
    counit D q (chevalleyInvolution D q x) = counit D q x := by
  change (counit D q).comp (chevalleyInvolution D q).toAlgHom x = counit D q x
  congr 1
  ext <;> simp

end Counit

/-! ### Coproduct -/

section Comul

private lemma sum_triple_reindex {M : Type*} [AddCommMonoid M] (m : ℕ)
    (F : ℕ → ℕ → ℕ → M) :
    (∑ r ∈ range (m + 1), ∑ a ∈ range (r + 1), ∑ c ∈ range (m - r + 1), F r a c) =
      ∑ p ∈ range (m + 1), ∑ a ∈ range (p + 1), ∑ u ∈ range (m - p + 1),
        F (a + u) a (p - a) := by
  rw [sum_sigma', sum_sigma', sum_sigma', sum_sigma']
  refine sum_bij'
    (fun x _ ↦ ⟨⟨x.1.2 + x.2, x.1.2⟩, x.1.1 - x.1.2⟩)
    (fun y _ ↦ ⟨⟨y.1.2 + y.2, y.1.2⟩, y.1.1 - y.1.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨r, a⟩, c⟩ hx
    simp only [mem_sigma, mem_range] at hx ⊢
    omega
  · rintro ⟨⟨p, a⟩, u⟩ hy
    simp only [mem_sigma, mem_range] at hy ⊢
    omega
  · rintro ⟨⟨r, a⟩, c⟩ hx
    simp only [mem_sigma, mem_range] at hx
    have h1 : a + (r - a) = r := by omega
    have h2 : a + c - a = c := by omega
    simp only [h1, h2]
  · rintro ⟨⟨p, a⟩, u⟩ hy
    simp only [mem_sigma, mem_range] at hy
    have h1 : a + (p - a) = p := by omega
    have h2 : a + u - a = u := by omega
    simp only [h1, h2]
  · rintro ⟨⟨r, a⟩, c⟩ hx
    simp only [mem_sigma, mem_range] at hx
    have h1 : a + (r - a) = r := by omega
    have h2 : a + c - a = c := by omega
    simp only [h1, h2]

variable (D : CartanDatum ι X Y) {q : K}

private lemma comulE_comm (i : ι) :
    (ki D q i ⊗ₜ[K] e D q i) * (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) =
      (q ^ D.symmetrizer i) ^ 2 •
        ((e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) * (ki D q i ⊗ₜ[K] e D q i)) := by
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ki_mul_e,
    D.cartan_apply_self, zpow_two, ← sq, TensorProduct.smul_tmul']

private lemma quantumDividedPower_comulE (i : ι) {n : ℕ}
    (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    quantumDividedPower (q ^ D.symmetrizer i)
        (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) + ki D q i ⊗ₜ[K] e D q i) n =
      ∑ a ∈ range (n + 1),
        (q ^ D.symmetrizer i) ^ (a * (n - a)) •
          ((eDividedPower D q i a * ki D q i ^ (n - a)) ⊗ₜ[K] eDividedPower D q i (n - a)) := by
  rw [quantumDividedPower_add (comulE_comm D i) hn]
  refine sum_congr rfl fun a _ ↦ ?_
  congr 1
  have h1 : quantumDividedPower (q ^ D.symmetrizer i)
      (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) a =
      eDividedPower D q i a ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) := by
    rw [quantumDividedPower_def, Algebra.TensorProduct.tmul_pow, one_pow,
      TensorProduct.smul_tmul', ← quantumDividedPower_def, ← eDividedPower]
  have h2 : quantumDividedPower (q ^ D.symmetrizer i) (ki D q i ⊗ₜ[K] e D q i) (n - a) =
      (ki D q i ^ (n - a)) ⊗ₜ[K] eDividedPower D q i (n - a) := by
    symm
    rw [eDividedPower, quantumDividedPower_def, TensorProduct.tmul_smul,
      ← Algebra.TensorProduct.tmul_pow, ← quantumDividedPower_def]
  rw [h1, h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private lemma ki_pow_mul_e (i j : ι) (u : ℕ) :
    ki D q i ^ u * e D q j =
      (q ^ D.symmetrizer i) ^ ((u : ℤ) * D.cartan i j) • (e D q j * ki D q i ^ u) := by
  rw [ki, k_pow, k_mul_e, map_nsmul, D.pairing_root_simpleTorus, nsmul_eq_mul]
  have hexp : (u : ℤ) * (D.symmetrizer j * D.cartan j i) =
      D.symmetrizer i * ((u : ℤ) * D.cartan i j) := by
    linear_combination (u : ℤ) * D.symmetrizer_mul_cartan j i
  rw [hexp, zpow_mul, zpow_natCast]

private lemma ki_pow_mul_eDividedPower (i : ι) (u c : ℕ) :
    ki D q i ^ u * eDividedPower D q i c =
      (q ^ D.symmetrizer i) ^ (2 * (c : ℤ) * (u : ℤ)) •
        (eDividedPower D q i c * ki D q i ^ u) := by
  rw [ki, k_pow, k_mul_eDividedPower, map_nsmul, D.pairing_root_simpleTorus_self, nsmul_eq_mul]
  have hexp : (c : ℤ) * ((u : ℤ) * (2 * D.symmetrizer i)) =
      D.symmetrizer i * (2 * (c : ℤ) * (u : ℤ)) := by ring
  rw [hexp, zpow_mul, zpow_natCast]

private lemma ki_pow_mul_kj_mul_eDividedPower (i j : ι) (u c : ℕ) :
    ki D q i ^ u * ki D q j * eDividedPower D q i c =
      (q ^ D.symmetrizer i) ^ (2 * (c : ℤ) * (u : ℤ) + (c : ℤ) * D.cartan i j) •
        (eDividedPower D q i c * (ki D q j * ki D q i ^ u)) := by
  rw [ki, ki, k_pow, k_mul_k, k_mul_eDividedPower, map_add, map_nsmul,
    D.pairing_root_simpleTorus_self, D.pairing_root_simpleTorus, nsmul_eq_mul,
    ← k_mul_k, (commute_k_k (u • D.simpleTorus i) (D.simpleTorus j)).eq]
  have hexp : (c : ℤ) * ((u : ℤ) * (2 * D.symmetrizer i) + D.symmetrizer i * D.cartan i j) =
      D.symmetrizer i * (2 * (c : ℤ) * (u : ℤ) + (c : ℤ) * D.cartan i j) := by ring
  rw [hexp, zpow_mul, zpow_natCast]

private lemma comul_serre_e (hq : q ≠ 0) {i j : ι} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) :
    ∑ r ∈ range (serreLength D i j + 1),
      (-1 : K) ^ r •
        (quantumDividedPower (q ^ D.symmetrizer i)
            (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) + ki D q i ⊗ₜ[K] e D q i) r *
          (e D q j ⊗ₜ[K] 1 + ki D q j ⊗ₜ[K] e D q j) *
          quantumDividedPower (q ^ D.symmetrizer i)
            (e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i) (serreLength D i j - r)) = 0 := by
  let m := serreLength D i j
  let qi := q ^ D.symmetrizer i
  have hqi : qi ≠ 0 := pow_ne_zero _ hq
  -- Split the middle factor `Eⱼ ⊗ 1 + Kⱼ ⊗ Eⱼ` into its two root-disjoint pieces.
  have hsplit : ∀ r ∈ range (m + 1),
      (-1 : K) ^ r •
        (quantumDividedPower qi (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) +
            ki D q i ⊗ₜ[K] e D q i) r *
          (e D q j ⊗ₜ[K] 1 + ki D q j ⊗ₜ[K] e D q j) *
          quantumDividedPower qi (e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i) (m - r)) =
      (-1 : K) ^ r •
        (quantumDividedPower qi (e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i) r *
          (e D q j ⊗ₜ[K] 1) *
          quantumDividedPower qi (e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i) (m - r)) +
      (-1 : K) ^ r •
        (quantumDividedPower qi (e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i) r *
          (ki D q j ⊗ₜ[K] e D q j) *
          quantumDividedPower qi (e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i) (m - r)) :=
    fun r _ ↦ by rw [mul_add, add_mul, smul_add]
  change ∑ r ∈ range (m + 1), _ = 0
  rw [sum_congr rfl hsplit, sum_add_distrib]
  -- First sum: middle factor `Eⱼ ⊗ 1`.
  have hS1 : ∑ r ∈ range (m + 1),
      (-1 : K) ^ r •
        (quantumDividedPower qi (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) +
            ki D q i ⊗ₜ[K] e D q i) r *
          (e D q j ⊗ₜ[K] 1) *
          quantumDividedPower qi (e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i) (m - r)) = 0 := by
    have hexpand : ∀ r ∈ range (m + 1),
        (-1 : K) ^ r •
          (quantumDividedPower qi (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) +
              ki D q i ⊗ₜ[K] e D q i) r *
            (e D q j ⊗ₜ[K] 1) *
            quantumDividedPower qi (e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i) (m - r)) =
        ∑ a ∈ range (r + 1), ∑ c ∈ range (m - r + 1),
          ((-1 : K) ^ r * qi ^ (a * (r - a)) * qi ^ (c * (m - r - c))) •
            ((eDividedPower D q i a * (ki D q i ^ (r - a) *
                (e D q j * (eDividedPower D q i c * ki D q i ^ (m - r - c))))) ⊗ₜ[K]
              (eDividedPower D q i (r - a) * eDividedPower D q i (m - r - c))) := by
      intro r hr
      have hr' : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
      rw [quantumDividedPower_comulE D i (quantumFactorial_ne_zero_of_le hr' hfac),
        quantumDividedPower_comulE D i (quantumFactorial_ne_zero_of_le (Nat.sub_le m r) hfac),
        sum_mul, sum_mul, smul_sum]
      refine sum_congr rfl fun a _ ↦ ?_
      rw [mul_sum, smul_sum]
      refine sum_congr rfl fun c _ ↦ ?_
      simp only [smul_mul_assoc, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        smul_smul, mul_assoc]
      refine congrArg (· • _) ?_
      change (-1 : K) ^ r * (qi ^ (c * (m - r - c)) * qi ^ (a * (r - a))) =
        (-1 : K) ^ r * (qi ^ (a * (r - a)) * qi ^ (c * (m - r - c)))
      ring
    rw [sum_congr rfl hexpand, sum_triple_reindex]
    have hterm : ∀ p ∈ range (m + 1),
        (∑ a ∈ range (p + 1), ∑ u ∈ range (m - p + 1),
          ((-1 : K) ^ (a + u) * qi ^ (a * (a + u - a)) * qi ^ ((p - a) * (m - (a + u) - (p - a)))) •
            ((eDividedPower D q i a * (ki D q i ^ (a + u - a) *
                (e D q j * (eDividedPower D q i (p - a) *
                  ki D q i ^ (m - (a + u) - (p - a)))))) ⊗ₜ[K]
              (eDividedPower D q i (a + u - a) * eDividedPower D q i (m - (a + u) - (p - a))))) =
        ∑ a ∈ range (p + 1), ∑ u ∈ range (m - p + 1),
          ((-1 : K) ^ a * qi ^ ((p - a) * (m - p)) *
              ((-1 : K) ^ u * qi⁻¹ ^ ((u : ℤ) * ((m - p : ℕ) - 1)) *
                quantumBinomial qi⁻¹ (m - p) u)) •
            ((eDividedPower D q i a * e D q j * eDividedPower D q i (p - a) *
                ki D q i ^ (m - p)) ⊗ₜ[K]
              eDividedPower D q i (m - p)) := by
      intro p hp
      have hp' : p ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hp)
      refine sum_congr rfl fun a ha ↦ sum_congr rfl fun u hu ↦ ?_
      have ha' : a ≤ p := Nat.lt_succ_iff.mp (mem_range.mp ha)
      have hu' : u ≤ m - p := Nat.lt_succ_iff.mp (mem_range.mp hu)
      have hsub1 : a + u - a = u := Nat.add_sub_cancel_left a u
      have hsub2 : m - (a + u) - (p - a) = m - p - u := by omega
      have huv : u + (m - p - u) = m - p := Nat.add_sub_of_le hu'
      rw [hsub1, hsub2]
      have hleft : eDividedPower D q i a * (ki D q i ^ u *
          (e D q j * (eDividedPower D q i (p - a) * ki D q i ^ (m - p - u)))) =
          (qi ^ ((u : ℤ) * D.cartan i j) * qi ^ (2 * ((p - a : ℕ) : ℤ) * (u : ℤ))) •
            (eDividedPower D q i a * e D q j * eDividedPower D q i (p - a) *
              ki D q i ^ (m - p)) := by
        rw [← mul_assoc (ki D q i ^ u), ki_pow_mul_e, smul_mul_assoc, mul_assoc (e D q j),
          ← mul_assoc (ki D q i ^ u), ki_pow_mul_eDividedPower, smul_mul_assoc,
          mul_assoc (eDividedPower D q i (p - a)), ← pow_add, huv]
        simp only [mul_smul_comm, smul_smul, mul_assoc]
        refine congrArg (· • _) ?_
        change (qi ^ ((u : ℤ) * D.cartan i j) * qi ^ (2 * (((p - a : ℕ) : ℤ) * (u : ℤ)))) = _
        rw [← mul_assoc 2]
      have hright : eDividedPower D q i u * eDividedPower D q i (m - p - u) =
          quantumBinomial qi⁻¹ (m - p) u • eDividedPower D q i (m - p) := by
        rw [eDividedPower, eDividedPower,
          quantumDividedPower_mul_quantumDividedPower _
            (huv.symm ▸ quantumFactorial_ne_zero_of_le (Nat.sub_le m p) hfac),
          huv, ← quantumBinomial_inv, ← eDividedPower]
      rw [hleft, hright, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, smul_smul]
      refine congrArg (· • _) ?_
      have hexp : ((a * u : ℕ) : ℤ) + (((p - a) * (m - p - u) : ℕ) : ℤ) +
          ((u : ℤ) * D.cartan i j + 2 * ((p - a : ℕ) : ℤ) * (u : ℤ)) =
          (((p - a) * (m - p) : ℕ) : ℤ) + -((u : ℤ) * ((m - p : ℕ) - 1)) := by
        rw [cartan_eq_one_sub_serreLength D hij]
        change ((a * u : ℕ) : ℤ) + (((p - a) * (m - p - u) : ℕ) : ℤ) +
          ((u : ℤ) * (1 - (m : ℤ)) + 2 * ((p - a : ℕ) : ℤ) * (u : ℤ)) = _
        push_cast
        rw [Nat.cast_sub hu', Nat.cast_sub hp', Nat.cast_sub ha']
        ring
      have hpow : qi ^ (a * u) * qi ^ ((p - a) * (m - p - u)) *
          (qi ^ ((u : ℤ) * D.cartan i j) * qi ^ (2 * ((p - a : ℕ) : ℤ) * (u : ℤ))) =
          qi ^ ((p - a) * (m - p)) * qi⁻¹ ^ ((u : ℤ) * ((m - p : ℕ) - 1)) := by
        rw [← zpow_natCast qi (a * u), ← zpow_natCast qi ((p - a) * (m - p - u)),
          ← zpow_natCast qi ((p - a) * (m - p)), inv_zpow, ← zpow_neg,
          ← zpow_add₀ hqi, ← zpow_add₀ hqi, ← zpow_add₀ hqi, ← zpow_add₀ hqi, hexp]
      rw [pow_add (-1 : K)]
      linear_combination (quantumBinomial qi⁻¹ (m - p) u * (-1 : K) ^ a * (-1 : K) ^ u) * hpow
    rw [sum_congr rfl hterm, sum_range_succ]
    have hlow : ∑ p ∈ range m, ∑ a ∈ range (p + 1), ∑ u ∈ range (m - p + 1),
        ((-1 : K) ^ a * qi ^ ((p - a) * (m - p)) *
            ((-1 : K) ^ u * qi⁻¹ ^ ((u : ℤ) * ((m - p : ℕ) - 1)) *
              quantumBinomial qi⁻¹ (m - p) u)) •
          ((eDividedPower D q i a * e D q j * eDividedPower D q i (p - a) *
              ki D q i ^ (m - p)) ⊗ₜ[K]
            eDividedPower D q i (m - p)) = 0 := by
      refine sum_eq_zero fun p hp ↦ sum_eq_zero fun a _ ↦ ?_
      have hmp : m - p ≠ 0 := by have := mem_range.mp hp; omega
      have hinner : ∀ u ∈ range (m - p + 1),
          ((-1 : K) ^ a * qi ^ ((p - a) * (m - p)) *
              ((-1 : K) ^ u * qi⁻¹ ^ ((u : ℤ) * ((m - p : ℕ) - 1)) *
                quantumBinomial qi⁻¹ (m - p) u)) •
            ((eDividedPower D q i a * e D q j * eDividedPower D q i (p - a) *
                ki D q i ^ (m - p)) ⊗ₜ[K]
              eDividedPower D q i (m - p)) =
          ((-1 : K) ^ a * qi ^ ((p - a) * (m - p))) •
            (((-1 : K) ^ u * qi⁻¹ ^ ((u : ℤ) * ((m - p : ℕ) - 1)) *
                quantumBinomial qi⁻¹ (m - p) u) •
              ((eDividedPower D q i a * e D q j * eDividedPower D q i (p - a) *
                  ki D q i ^ (m - p)) ⊗ₜ[K]
                eDividedPower D q i (m - p))) := fun _ _ ↦ mul_smul _ _ _
      rw [sum_congr rfl hinner, ← smul_sum, ← sum_smul,
        sum_range_neg_one_pow_mul_zpow_mul_quantumBinomial (inv_ne_zero hqi) hmp, zero_smul,
        smul_zero]
    rw [hlow, zero_add, Nat.sub_self, Nat.zero_add, range_one]
    simp only [sum_singleton, Nat.cast_zero, zero_mul, mul_zero, zpow_zero, pow_zero,
      quantumBinomial_zero_right, mul_one, eDividedPower, quantumDividedPower_zero,
      TensorProduct.smul_tmul', ← TensorProduct.sum_tmul]
    simpa only [eDividedPower, TensorProduct.zero_tmul] using
      congrArg (· ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) (serre_e (D := D) (q := q) hij)
  -- Second sum: middle factor `Kⱼ ⊗ Eⱼ`.
  have hS2 : ∑ r ∈ range (m + 1),
      (-1 : K) ^ r •
        (quantumDividedPower qi (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) +
            ki D q i ⊗ₜ[K] e D q i) r *
          (ki D q j ⊗ₜ[K] e D q j) *
          quantumDividedPower qi (e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i) (m - r)) = 0 := by
    have hexpand : ∀ r ∈ range (m + 1),
        (-1 : K) ^ r •
          (quantumDividedPower qi (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) +
              ki D q i ⊗ₜ[K] e D q i) r *
            (ki D q j ⊗ₜ[K] e D q j) *
            quantumDividedPower qi (e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i) (m - r)) =
        ∑ a ∈ range (r + 1), ∑ c ∈ range (m - r + 1),
          ((-1 : K) ^ r * qi ^ (a * (r - a)) * qi ^ (c * (m - r - c))) •
            ((eDividedPower D q i a * (ki D q i ^ (r - a) *
                (ki D q j * (eDividedPower D q i c * ki D q i ^ (m - r - c))))) ⊗ₜ[K]
              (eDividedPower D q i (r - a) * (e D q j * eDividedPower D q i (m - r - c)))) := by
      intro r hr
      have hr' : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
      rw [quantumDividedPower_comulE D i (quantumFactorial_ne_zero_of_le hr' hfac),
        quantumDividedPower_comulE D i (quantumFactorial_ne_zero_of_le (Nat.sub_le m r) hfac),
        sum_mul, sum_mul, smul_sum]
      refine sum_congr rfl fun a _ ↦ ?_
      rw [mul_sum, smul_sum]
      refine sum_congr rfl fun c _ ↦ ?_
      simp only [smul_mul_assoc, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul,
        smul_smul, mul_assoc]
      refine congrArg (· • _) ?_
      change (-1 : K) ^ r * (qi ^ (c * (m - r - c)) * qi ^ (a * (r - a))) =
        (-1 : K) ^ r * (qi ^ (a * (r - a)) * qi ^ (c * (m - r - c)))
      ring
    rw [sum_congr rfl hexpand, sum_triple_reindex]
    have hterm : ∀ p ∈ range (m + 1),
        (∑ a ∈ range (p + 1), ∑ u ∈ range (m - p + 1),
          ((-1 : K) ^ (a + u) * qi ^ (a * (a + u - a)) * qi ^ ((p - a) * (m - (a + u) - (p - a)))) •
            ((eDividedPower D q i a * (ki D q i ^ (a + u - a) *
                (ki D q j * (eDividedPower D q i (p - a) *
                  ki D q i ^ (m - (a + u) - (p - a)))))) ⊗ₜ[K]
              (eDividedPower D q i (a + u - a) *
                (e D q j * eDividedPower D q i (m - (a + u) - (p - a)))))) =
        ∑ u ∈ range (m - p + 1), ∑ a ∈ range (p + 1),
          ((-1 : K) ^ u * qi ^ ((p : ℤ) * ((u : ℤ) + 1 - p)) *
              ((-1 : K) ^ a * qi ^ ((a : ℤ) * ((p : ℕ) - 1)) * quantumBinomial qi p a)) •
            ((eDividedPower D q i p * (ki D q j * ki D q i ^ (m - p))) ⊗ₜ[K]
              (eDividedPower D q i u * e D q j * eDividedPower D q i (m - p - u))) := by
      intro p hp
      have hp' : p ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hp)
      rw [sum_comm]
      refine sum_congr rfl fun u hu ↦ sum_congr rfl fun a ha ↦ ?_
      have ha' : a ≤ p := Nat.lt_succ_iff.mp (mem_range.mp ha)
      have hu' : u ≤ m - p := Nat.lt_succ_iff.mp (mem_range.mp hu)
      have hsub1 : a + u - a = u := Nat.add_sub_cancel_left a u
      have hsub2 : m - (a + u) - (p - a) = m - p - u := by omega
      have huv : u + (m - p - u) = m - p := Nat.add_sub_of_le hu'
      have hac : a + (p - a) = p := Nat.add_sub_of_le ha'
      rw [hsub1, hsub2]
      have hleft : eDividedPower D q i a * (ki D q i ^ u *
          (ki D q j * (eDividedPower D q i (p - a) * ki D q i ^ (m - p - u)))) =
          (qi ^ (2 * ((p - a : ℕ) : ℤ) * (u : ℤ) + ((p - a : ℕ) : ℤ) * D.cartan i j) *
              quantumBinomial qi p a) •
            (eDividedPower D q i p * (ki D q j * ki D q i ^ (m - p))) := by
        have hassoc : ki D q i ^ u *
            (ki D q j * (eDividedPower D q i (p - a) * ki D q i ^ (m - p - u))) =
            (ki D q i ^ u * ki D q j * eDividedPower D q i (p - a)) *
              ki D q i ^ (m - p - u) := by
          simp only [mul_assoc]
        rw [hassoc, ki_pow_mul_kj_mul_eDividedPower, smul_mul_assoc, mul_smul_comm,
          ← mul_assoc (eDividedPower D q i a),
          ← mul_assoc (eDividedPower D q i a) (eDividedPower D q i (p - a)),
          eDividedPower, eDividedPower,
          quantumDividedPower_mul_quantumDividedPower _
            (hac.symm ▸ quantumFactorial_ne_zero_of_le hp' hfac),
          hac, ← eDividedPower, smul_mul_assoc, smul_mul_assoc, smul_smul]
        refine congrArg₂ (· • ·) rfl ?_
        rw [mul_assoc, mul_assoc, ← pow_add, huv]
      rw [hleft, ← TensorProduct.smul_tmul', smul_smul, ← mul_assoc (eDividedPower D q i u)]
      refine congrArg (· • _) ?_
      have hexp : ((a * u : ℕ) : ℤ) + (((p - a) * (m - p - u) : ℕ) : ℤ) +
          (2 * ((p - a : ℕ) : ℤ) * (u : ℤ) + ((p - a : ℕ) : ℤ) * D.cartan i j) =
          (p : ℤ) * ((u : ℤ) + 1 - p) + (a : ℤ) * ((p : ℕ) - 1) := by
        rw [cartan_eq_one_sub_serreLength D hij]
        change ((a * u : ℕ) : ℤ) + (((p - a) * (m - p - u) : ℕ) : ℤ) +
          (2 * ((p - a : ℕ) : ℤ) * (u : ℤ) + ((p - a : ℕ) : ℤ) * (1 - (m : ℤ))) = _
        push_cast
        rw [Nat.cast_sub hu', Nat.cast_sub hp', Nat.cast_sub ha']
        ring
      have hpow : qi ^ (a * u) * qi ^ ((p - a) * (m - p - u)) *
          qi ^ (2 * ((p - a : ℕ) : ℤ) * (u : ℤ) + ((p - a : ℕ) : ℤ) * D.cartan i j) =
          qi ^ ((p : ℤ) * ((u : ℤ) + 1 - p)) * qi ^ ((a : ℤ) * ((p : ℕ) - 1)) := by
        rw [← zpow_natCast qi (a * u), ← zpow_natCast qi ((p - a) * (m - p - u)),
          ← zpow_add₀ hqi, ← zpow_add₀ hqi, ← zpow_add₀ hqi, hexp]
      rw [pow_add (-1 : K)]
      linear_combination ((-1 : K) ^ a * (-1 : K) ^ u * quantumBinomial qi p a) * hpow
    rw [sum_congr rfl hterm, sum_range_succ']
    have hhigh : ∑ p ∈ range m, ∑ u ∈ range (m - (p + 1) + 1), ∑ a ∈ range (p + 1 + 1),
        ((-1 : K) ^ u * qi ^ (((p + 1 : ℕ) : ℤ) * ((u : ℤ) + 1 - (p + 1 : ℕ))) *
            ((-1 : K) ^ a * qi ^ ((a : ℤ) * ((p + 1 : ℕ) - 1)) *
              quantumBinomial qi (p + 1) a)) •
          ((eDividedPower D q i (p + 1) * (ki D q j * ki D q i ^ (m - (p + 1)))) ⊗ₜ[K]
            (eDividedPower D q i u * e D q j * eDividedPower D q i (m - (p + 1) - u))) = 0 := by
      refine sum_eq_zero fun p _ ↦ sum_eq_zero fun u _ ↦ ?_
      have hinner : ∀ a ∈ range (p + 1 + 1),
          ((-1 : K) ^ u * qi ^ (((p + 1 : ℕ) : ℤ) * ((u : ℤ) + 1 - (p + 1 : ℕ))) *
              ((-1 : K) ^ a * qi ^ ((a : ℤ) * ((p + 1 : ℕ) - 1)) *
                quantumBinomial qi (p + 1) a)) •
            ((eDividedPower D q i (p + 1) * (ki D q j * ki D q i ^ (m - (p + 1)))) ⊗ₜ[K]
              (eDividedPower D q i u * e D q j * eDividedPower D q i (m - (p + 1) - u))) =
          ((-1 : K) ^ u * qi ^ (((p + 1 : ℕ) : ℤ) * ((u : ℤ) + 1 - (p + 1 : ℕ)))) •
            (((-1 : K) ^ a * qi ^ ((a : ℤ) * ((p + 1 : ℕ) - 1)) *
                quantumBinomial qi (p + 1) a) •
              ((eDividedPower D q i (p + 1) * (ki D q j * ki D q i ^ (m - (p + 1)))) ⊗ₜ[K]
                (eDividedPower D q i u * e D q j *
                  eDividedPower D q i (m - (p + 1) - u)))) := fun _ _ ↦ mul_smul _ _ _
      rw [sum_congr rfl hinner, ← smul_sum, ← sum_smul,
        sum_range_neg_one_pow_mul_zpow_mul_quantumBinomial hqi (Nat.succ_ne_zero p),
        zero_smul, smul_zero]
    rw [hhigh, zero_add, Nat.sub_zero, Nat.zero_add, range_one]
    simp only [sum_singleton, Nat.cast_zero, zero_mul, zpow_zero, pow_zero,
      quantumBinomial_zero_right, mul_one, eDividedPower, quantumDividedPower_zero, one_mul]
    simp only [← TensorProduct.tmul_smul, ← TensorProduct.tmul_sum]
    simpa only [eDividedPower, TensorProduct.tmul_zero] using
      congrArg ((ki D q j * ki D q i ^ m) ⊗ₜ[K] ·) (serre_e (D := D) (q := q) hij)
  rw [hS1, hS2, add_zero]

private noncomputable def comulTuple (hq : q ≠ 0)
    (hserre : ∀ {i j : ι}, i ≠ j →
      quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) :
    GeneratorTuple D q
      (QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q) where
  e i := e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i
  f i := f D q i ⊗ₜ[K] kiInv D q i + 1 ⊗ₜ[K] f D q i
  k y := k D q y ⊗ₜ[K] k D q y
  k_zero := by simp [Algebra.TensorProduct.one_def]
  k_mul_k y z := by simp [Algebra.TensorProduct.tmul_mul_tmul, k_mul_k]
  k_mul_e y i := by
    simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      k_mul_e, ki, (commute_k_k y (D.simpleTorus i)).eq, TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, smul_add]
  k_mul_f y i := by
    simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      k_mul_f, kiInv, (commute_k_k y (-D.simpleTorus i)).eq, TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, smul_add]
  e_mul_f_sub_f_mul_e_self i := by
    have hqi : q ^ D.symmetrizer i ≠ 0 := pow_ne_zero _ hq
    simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [ki_mul_f, e_mul_kiInv, D.cartan_apply_self]
    simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, zpow_neg, zpow_two,
      mul_inv_cancel₀ (mul_ne_zero hqi hqi), one_smul]
    calc
      _ = (e D q i * f D q i - f D q i * e D q i) ⊗ₜ[K] kiInv D q i +
            ki D q i ⊗ₜ[K] (e D q i * f D q i - f D q i * e D q i) := by
          simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
          abel
      _ = (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
            (k D q (D.simpleTorus i) ⊗ₜ[K] k D q (D.simpleTorus i) -
              k D q (-D.simpleTorus i) ⊗ₜ[K] k D q (-D.simpleTorus i)) := by
          rw [e_mul_f_sub_f_mul_e_self, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
            ← smul_add, TensorProduct.sub_tmul, TensorProduct.tmul_sub, ki, kiInv]
          congr 1
          abel
  e_mul_f_sub_f_mul_e_of_ne {i j} hij := by
    simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [ki, kiInv, k_mul_f, e_mul_k, map_neg, neg_neg, D.pairing_root_simpleTorus,
      D.pairing_root_simpleTorus]
    simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
    have hcancel : q ^ (D.symmetrizer i * D.cartan i j) *
        q ^ (-(D.symmetrizer j * D.cartan j i)) = 1 := by
      rw [← zpow_add₀ hq, D.symmetrizer_mul_cartan i j, add_neg_cancel, zpow_zero]
    rw [hcancel, one_smul, e_mul_f_of_ne hij]
    abel
  serre_e hij := comul_serre_e D hq hij (hserre hij)
  serre_f {i j} hij := by
    let τ : QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q →ₐ[K]
        QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q :=
      (Algebra.TensorProduct.map
          (chevalleyInvolution D q).toAlgHom (chevalleyInvolution D q).toAlgHom).comp
        (Algebra.TensorProduct.comm K _ _).toAlgHom
    have hτ (m : ι) :
        τ (e D q m ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) + ki D q m ⊗ₜ[K] e D q m) =
          f D q m ⊗ₜ[K] kiInv D q m + 1 ⊗ₜ[K] f D q m := by
      simp [τ, add_comm]
    simpa only [map_sum, map_smul, map_mul, map_quantumDividedPower, hτ, map_zero] using
      congrArg τ (comul_serre_e D hq hij (hserre hij))

/-- The coproduct `Δ : U →ₐ[K] U ⊗[K] U` under `q ≠ 0` and nonvanishing of the Serre-degree
quantum factorials `[1 - aᵢⱼ]_(qᵢ)!` (`i ≠ j`). -/
noncomputable def comulAlgHom (hq : q ≠ 0)
    (hserre : ∀ {i j : ι}, i ≠ j →
      quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) :
    QuantizedEnvelopingAlgebra D q →ₐ[K]
      QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q :=
  lift (comulTuple D hq hserre)

variable {D}

@[simp]
theorem comulAlgHom_e (hq : q ≠ 0)
    (hserre : ∀ {i j : ι}, i ≠ j →
      quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) (i : ι) :
    comulAlgHom D hq hserre (e D q i) =
      e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i :=
  lift_e _ i

@[simp]
theorem comulAlgHom_f (hq : q ≠ 0)
    (hserre : ∀ {i j : ι}, i ≠ j →
      quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) (i : ι) :
    comulAlgHom D hq hserre (f D q i) =
      f D q i ⊗ₜ[K] kiInv D q i + 1 ⊗ₜ[K] f D q i :=
  lift_f _ i

@[simp]
theorem comulAlgHom_k (hq : q ≠ 0)
    (hserre : ∀ {i j : ι}, i ≠ j →
      quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) (y : Y) :
    comulAlgHom D hq hserre (k D q y) = k D q y ⊗ₜ[K] k D q y :=
  lift_k _ y

theorem comulAlgHom_ki (hq : q ≠ 0)
    (hserre : ∀ {i j : ι}, i ≠ j →
      quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) (i : ι) :
    comulAlgHom D hq hserre (ki D q i) = ki D q i ⊗ₜ[K] ki D q i :=
  comulAlgHom_k hq hserre (D.simpleTorus i)

theorem comulAlgHom_kiInv (hq : q ≠ 0)
    (hserre : ∀ {i j : ι}, i ≠ j →
      quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) (i : ι) :
    comulAlgHom D hq hserre (kiInv D q i) = kiInv D q i ⊗ₜ[K] kiInv D q i :=
  comulAlgHom_k hq hserre (-D.simpleTorus i)

/-- The Chevalley involution `ω` is a coalgebra anti-automorphism:
`Δ(ω x) = (ω ⊗ ω)(flip(Δ x))`. -/
theorem comulAlgHom_chevalleyInvolution (hq : q ≠ 0)
    (hserre : ∀ {i j : ι}, i ≠ j →
      quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0)
    (x : QuantizedEnvelopingAlgebra D q) :
    comulAlgHom D hq hserre (chevalleyInvolution D q x) =
      Algebra.TensorProduct.map
        (chevalleyInvolution D q).toAlgHom (chevalleyInvolution D q).toAlgHom
        (Algebra.TensorProduct.comm K _ _ (comulAlgHom D hq hserre x)) := by
  change (comulAlgHom D hq hserre).comp (chevalleyInvolution D q).toAlgHom x =
    ((Algebra.TensorProduct.map
        (chevalleyInvolution D q).toAlgHom (chevalleyInvolution D q).toAlgHom).comp
      ((Algebra.TensorProduct.comm K _ _).toAlgHom.comp (comulAlgHom D hq hserre))) x
  congr 1
  ext <;> simp [add_comm]

end Comul

/-! ### Bialgebra structure and divided-power coproducts -/

section Bialgebra

variable (D : CartanDatum ι X Y) {q : K}

/-- Explicit-hypothesis `Bialgebra` structure on `QuantizedEnvelopingAlgebra D q` under `q ≠ 0`
and nonvanishing of the Serre-degree quantum factorials `[1 - aᵢⱼ]_(qᵢ)!` (`i ≠ j`). -/
@[expose, instance_reducible]
noncomputable def bialgebraOfSerre (hq : q ≠ 0)
    (hserre : ∀ {i j : ι}, i ≠ j →
      quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) :
    Bialgebra K (QuantizedEnvelopingAlgebra D q) :=
  Bialgebra.ofAlgHom (comulAlgHom D hq hserre) (counit D q)
    (by
      ext <;>
        simp [TensorProduct.tmul_add, TensorProduct.add_tmul, add_assoc,
          Algebra.TensorProduct.one_def])
    (by ext <;> simp)
    (by ext <;> simp)

section Generic

variable (q : K) [Fact (IsGenericQuantumParameter q)]

/-- The canonical `K`-bialgebra structure on `QuantizedEnvelopingAlgebra D q` at a generic quantum
parameter `q`. -/
noncomputable instance instBialgebra : Bialgebra K (QuantizedEnvelopingAlgebra D q) :=
  bialgebraOfSerre D (Fact.out : IsGenericQuantumParameter q).ne_zero fun {i j} _ ↦
    quantumFactorial_ne_zero
      ((Fact.out : IsGenericQuantumParameter q).pow (D.symmetrizer_pos i)) (serreLength D i j)

variable {D q}

@[simp]
theorem comul_e (i : ι) :
    Coalgebra.comul (R := K) (e D q i) =
      e D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] e D q i :=
  comulAlgHom_e (Fact.out : IsGenericQuantumParameter q).ne_zero _ i

@[simp]
theorem comul_f (i : ι) :
    Coalgebra.comul (R := K) (f D q i) =
      f D q i ⊗ₜ[K] kiInv D q i + 1 ⊗ₜ[K] f D q i :=
  comulAlgHom_f (Fact.out : IsGenericQuantumParameter q).ne_zero _ i

@[simp]
theorem comul_k (y : Y) :
    Coalgebra.comul (R := K) (k D q y) = k D q y ⊗ₜ[K] k D q y :=
  comulAlgHom_k (Fact.out : IsGenericQuantumParameter q).ne_zero _ y

theorem comul_ki (i : ι) :
    Coalgebra.comul (R := K) (ki D q i) = ki D q i ⊗ₜ[K] ki D q i :=
  comul_k (D.simpleTorus i)

theorem comul_kiInv (i : ι) :
    Coalgebra.comul (R := K) (kiInv D q i) = kiInv D q i ⊗ₜ[K] kiInv D q i :=
  comul_k (-D.simpleTorus i)

@[simp]
theorem counit_e (i : ι) : Coalgebra.counit (R := K) (e D q i) = 0 :=
  counit_apply_e i

@[simp]
theorem counit_f (i : ι) : Coalgebra.counit (R := K) (f D q i) = 0 :=
  counit_apply_f i

@[simp]
theorem counit_k (y : Y) : Coalgebra.counit (R := K) (k D q y) = 1 :=
  counit_apply_k y

theorem counit_ki (i : ι) : Coalgebra.counit (R := K) (ki D q i) = 1 :=
  counit_apply_ki i

theorem counit_kiInv (i : ι) : Coalgebra.counit (R := K) (kiInv D q i) = 1 :=
  counit_apply_kiInv i

@[simp]
theorem counit_apply (x : QuantizedEnvelopingAlgebra D q) :
    counit D q x = Coalgebra.counit x :=
  (rfl)

/-- Every toral generator `K_y` is group-like in `QuantizedEnvelopingAlgebra D q`. -/
theorem isGroupLikeElem_k (y : Y) : IsGroupLikeElem K (k D q y) :=
  ⟨counit_k y, comul_k y⟩

/-- `Kᵢ` is group-like in `QuantizedEnvelopingAlgebra D q`. -/
theorem isGroupLikeElem_ki (i : ι) : IsGroupLikeElem K (ki D q i) :=
  isGroupLikeElem_k (D.simpleTorus i)

/-- `Kᵢ⁻¹` is group-like in `QuantizedEnvelopingAlgebra D q`. -/
theorem isGroupLikeElem_kiInv (i : ι) : IsGroupLikeElem K (kiInv D q i) :=
  isGroupLikeElem_k (-D.simpleTorus i)

/-- The Chevalley involution `ω` is a coalgebra anti-automorphism with respect to `Coalgebra.comul`:
`Δ(ω x) = (ω ⊗ ω)(flip(Δ x))`. -/
theorem comul_chevalleyInvolution (x : QuantizedEnvelopingAlgebra D q) :
    Coalgebra.comul (R := K) (chevalleyInvolution D q x) =
      Algebra.TensorProduct.map
        (chevalleyInvolution D q).toAlgHom (chevalleyInvolution D q).toAlgHom
        (Algebra.TensorProduct.comm K _ _ (Coalgebra.comul x)) :=
  comulAlgHom_chevalleyInvolution (Fact.out : IsGenericQuantumParameter q).ne_zero _ x

/-- Coproduct of the raising divided powers:
`Δ(Eᵢ^(n)) = ∑_{a = 0}^n qᵢ^(a(n - a)) Eᵢ^(a) Kᵢ^(n - a) ⊗ Eᵢ^(n - a)`. -/
theorem comul_eDividedPower (i : ι) (n : ℕ) :
    Coalgebra.comul (R := K) (eDividedPower D q i n) =
      ∑ a ∈ range (n + 1),
        (q ^ D.symmetrizer i) ^ (a * (n - a)) •
          ((eDividedPower D q i a * ki D q i ^ (n - a)) ⊗ₜ[K] eDividedPower D q i (n - a)) := by
  change (Bialgebra.comulAlgHom K (QuantizedEnvelopingAlgebra D q)) (eDividedPower D q i n) = _
  rw [eDividedPower, map_quantumDividedPower, Bialgebra.comulAlgHom_apply, comul_e,
    quantumDividedPower_comulE D i
      (quantumFactorial_ne_zero
        ((Fact.out : IsGenericQuantumParameter q).pow (D.symmetrizer_pos i)) n)]

/-- Coproduct of the lowering divided powers:
`Δ(Fᵢ^(n)) = ∑_{a = 0}^n qᵢ^(a(n - a)) Fᵢ^(a) ⊗ Fᵢ^(n - a) Kᵢ^(-a)`. -/
theorem comul_fDividedPower (i : ι) (n : ℕ) :
    Coalgebra.comul (R := K) (fDividedPower D q i n) =
      ∑ a ∈ range (n + 1),
        (q ^ D.symmetrizer i) ^ (a * (n - a)) •
          (fDividedPower D q i a ⊗ₜ[K] (fDividedPower D q i (n - a) * kiInv D q i ^ a)) := by
  rw [← chevalleyInvolution_eDividedPower, comul_chevalleyInvolution, comul_eDividedPower,
    map_sum, map_sum, ← sum_range_reflect]
  refine sum_congr rfl fun a ha ↦ ?_
  have ha' : a ≤ n := Nat.lt_succ_iff.mp (mem_range.mp ha)
  rw [Nat.add_one_sub_one, Nat.sub_sub_self ha', mul_comm (n - a) a]
  simp [map_smul, map_mul, map_pow]

end Generic

end Bialgebra

/-! ### Kashiwara-normalized Chevalley operators -/

section Normalized

/-- The Kashiwara-normalized raising operator `eᵢ = Kᵢ⁻¹ Eᵢ`, skew-primitive on the right relative
to `Kᵢ⁻¹` (`Δ(eᵢ) = eᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ eᵢ`). -/
noncomputable def normalizedE (D : CartanDatum ι X Y) (q : K) (i : ι) :
    QuantizedEnvelopingAlgebra D q :=
  kiInv D q i * e D q i

/-- The Kashiwara-normalized lowering operator `fᵢ = Fᵢ Kᵢ`, skew-primitive on the left relative to
`Kᵢ` (`Δ(fᵢ) = fᵢ ⊗ 1 + Kᵢ ⊗ fᵢ`). -/
noncomputable def normalizedF (D : CartanDatum ι X Y) (q : K) (i : ι) :
    QuantizedEnvelopingAlgebra D q :=
  f D q i * ki D q i

variable {D : CartanDatum ι X Y} {q : K}

theorem normalizedE_def (i : ι) : normalizedE D q i = kiInv D q i * e D q i := (rfl)

theorem normalizedF_def (i : ι) : normalizedF D q i = f D q i * ki D q i := (rfl)

@[simp]
theorem counit_apply_normalizedE (i : ι) : counit D q (normalizedE D q i) = 0 := by
  simp [normalizedE_def]

@[simp]
theorem counit_apply_normalizedF (i : ι) : counit D q (normalizedF D q i) = 0 := by
  simp [normalizedF_def]

section GenericNormalized

variable [Fact (IsGenericQuantumParameter q)]

@[simp]
theorem counit_normalizedE (i : ι) : Coalgebra.counit (R := K) (normalizedE D q i) = 0 :=
  counit_apply_normalizedE i

@[simp]
theorem counit_normalizedF (i : ι) : Coalgebra.counit (R := K) (normalizedF D q i) = 0 :=
  counit_apply_normalizedF i

/-- Coproduct of the normalized raising operator `eᵢ = Kᵢ⁻¹ Eᵢ`:
`Δ(eᵢ) = eᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ eᵢ`. -/
@[simp]
theorem comul_normalizedE (i : ι) :
    Coalgebra.comul (R := K) (normalizedE D q i) =
      normalizedE D q i ⊗ₜ[K] kiInv D q i + 1 ⊗ₜ[K] normalizedE D q i := by
  rw [normalizedE_def, Bialgebra.comul_mul, comul_kiInv, comul_e, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, kiInv, ki, k_neg_mul_k, ← kiInv, ← normalizedE_def]

/-- Coproduct of the normalized lowering operator `fᵢ = Fᵢ Kᵢ`:
`Δ(fᵢ) = fᵢ ⊗ 1 + Kᵢ ⊗ fᵢ`. -/
@[simp]
theorem comul_normalizedF (i : ι) :
    Coalgebra.comul (R := K) (normalizedF D q i) =
      normalizedF D q i ⊗ₜ[K] 1 + ki D q i ⊗ₜ[K] normalizedF D q i := by
  rw [normalizedF_def, Bialgebra.comul_mul, comul_f, comul_ki, add_mul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, kiInv, ki, k_neg_mul_k, ← ki, ← normalizedF_def]

end GenericNormalized

end Normalized

/-! ### Functoriality as bialgebra morphisms -/

section MapBialgHom

variable {D : CartanDatum ι X Y} {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
  {D' : CartanDatum ι X' Y'} {q : K} [Fact (IsGenericQuantumParameter q)]

/-- A morphism `φ : CartanDatum.Hom D D'` of Cartan data induces a `K`-bialgebra homomorphism on
quantized enveloping algebras. -/
noncomputable def mapBialgHom (φ : CartanDatum.Hom D D') :
    QuantizedEnvelopingAlgebra D q →ₐc[K] QuantizedEnvelopingAlgebra D' q :=
  BialgHom.ofAlgHom (map φ)
    (by ext <;> simp [← counit_apply])
    (by ext <;> simp [Bialgebra.comulAlgHom_apply])

@[simp]
theorem mapBialgHom_toAlgHom (φ : CartanDatum.Hom D D') :
    (mapBialgHom (q := q) φ).toAlgHom = map φ :=
  (rfl)

@[simp]
theorem mapBialgHom_apply (φ : CartanDatum.Hom D D') (x : QuantizedEnvelopingAlgebra D q) :
    mapBialgHom φ x = map φ x :=
  (rfl)

end MapBialgHom

end TauCeti.QuantizedEnvelopingAlgebra

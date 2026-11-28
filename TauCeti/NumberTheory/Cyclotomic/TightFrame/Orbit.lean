/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Cyclotomic.TightFrame.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Tight frames from cyclotomic Galois orbits

Multiplying each conjugate of a vector by all the powers of a cyclotomic generator
produces a tight frame in embedding coordinates. Orthogonality of the powers kills the
cross terms between different embeddings. Summing over the conjugates makes the diagonal
independent of the embedding. Adjoining the inverse powers gives the initial frame used
before pairing those powers with the scaled trace-dual vectors.

The orbit construction is the one in `New.Parameters.isTightFrame_orbit` and
`New.Parameters.exists_isTightFrame_coprime` of lsernau/grh-lean
(`72fead1`, `grh/src/New/Derivatives/Vacuum/ShortVectors.lean`).
-/

public section

open Matrix
open scoped ComplexConjugate

namespace PowerBasis

open Classical in
/-- The inverse powers of a root generating a power basis satisfy the same orthogonality
relation as its powers. -/
theorem sum_conj_mul_apply_gen_inv_pow {K E : Type*} [CommRing K] [Field E]
    [Algebra K E] [Algebra K ℂ] {n : ℕ} (pb : PowerBasis K E) (hζ : pb.gen ^ n = 1)
    (σ τ : E →ₐ[K] ℂ) :
    ∑ i : Fin n, conj (σ (pb.gen⁻¹ ^ (i : ℕ))) * τ (pb.gen⁻¹ ^ (i : ℕ)) =
      if σ = τ then (n : ℂ) else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  have hc (ρ : E →ₐ[K] ℂ) (i : Fin n) :
      ρ (pb.gen⁻¹ ^ (i : ℕ)) = conj (ρ (pb.gen ^ (i : ℕ))) := by
    have hρ : (ρ pb.gen) ^ n = 1 := by rw [← map_pow, hζ, map_one]
    simp only [map_pow, map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hρ hn)]
  simp only [hc, Complex.conj_conj]
  rw [eq_comm (a := σ)]
  exact (Finset.sum_congr rfl fun i _ ↦ mul_comm _ _).trans
    (pb.sum_conj_mul_apply_gen_pow hζ τ σ)

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra K ℂ] {n : ℕ}

open Classical in
/-- For a finite family `v`, take every Galois conjugate of each `v i` and every multiple
of each conjugate by a power of the root. Its frame operator is scalar, with scalar the
number of powers times the sum of squared absolute values of the embedded `v i`. -/
theorem conjTranspose_mul_self_embeddingsMatrix_galois_orbit_pow {ι : Type*} [Fintype ι]
    [Fintype (E ≃ₐ[K] E)] [Fintype (E →ₐ[K] ℂ)] (pb : PowerBasis K E)
    (hζ : pb.gen ^ n = 1) (v : ι → E) :
    let A := Algebra.embeddingsMatrix K ℂ
      (fun i : ι × ((E ≃ₐ[K] E) × Fin n) ↦ pb.gen ^ (i.2.2 : ℕ) * i.2.1 (v i.1))
    Aᴴ * A = ((n : ℂ) * ∑ i, ∑ ρ : E →ₐ[K] ℂ, (‖ρ (v i)‖ ^ 2 : ℝ)) •
      (1 : Matrix (E →ₐ[K] ℂ) (E →ₐ[K] ℂ) ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext σ τ
    simp [Matrix.mul_apply]
  -- Normality follows by viewing the generator as a primitive root of its exact order.
  have : NeZero (orderOf pb.gen) := ⟨(Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hζ) hn).ne'⟩
  have : IsCyclotomicExtension {orderOf pb.gen} K E := by
    refine (IsCyclotomicExtension.iff_singleton ..).mpr ⟨⟨_, IsPrimitiveRoot.orderOf _⟩, fun x ↦ ?_⟩
    have hle : Algebra.adjoin K {pb.gen} ≤ Algebra.adjoin K {b : E | b ^ orderOf pb.gen = 1} :=
      Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (pow_orderOf_eq_one _))
    rw [pb.adjoin_gen_eq_top] at hle
    exact hle trivial
  have : IsGalois K E := IsCyclotomicExtension.isGalois {orderOf pb.gen} K E
  ext σ τ
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Algebra.embeddingsMatrix_apply,
    Complex.star_def, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Fintype.sum_prod_type]
  have hsum (x : E) (g : E ≃ₐ[K] E) :
      ∑ i : Fin n, conj (σ (pb.gen ^ (i : ℕ) * g x)) * τ (pb.gen ^ (i : ℕ) * g x) =
        (if σ = τ then (n : ℂ) else 0) * (conj (σ (g x)) * τ (g x)) := by
    rw [← pb.sum_conj_mul_apply_gen_pow hζ σ τ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [map_mul]; ring
  simp only [hsum]
  by_cases h : σ = τ
  · subst τ
    let : Algebra E ℂ := σ.toRingHom.toAlgebra
    have : IsScalarTower K E ℂ := IsScalarTower.of_algHom σ
    let e : (E →ₐ[K] ℂ) ≃ (E ≃ₐ[K] E) := Normal.algHomEquivAut K ℂ E
    simp only [ite_true, mul_one, ← Finset.mul_sum]
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ Fintype.sum_equiv e.symm _ _ fun g ↦ ?_
    rw [mul_comm, Complex.mul_conj, ← Complex.ofReal_pow, Complex.sq_norm]
    simp [e, RingHom.algebraMap_toAlgebra]
  · simp [h]

open Classical in
/-- Adjoin the inverse powers to the Galois-orbit frame. Its scalar frame bound includes the
contribution `n` of the inverse powers. For `n > 0` the family includes each `v i`, at the
identity automorphism and exponent zero. -/
theorem conjTranspose_mul_self_embeddingsMatrix_inv_pow_sumElim_galois_orbit_pow
    {ι : Type*} [Fintype ι] [Fintype (E ≃ₐ[K] E)] [Fintype (E →ₐ[K] ℂ)]
    (pb : PowerBasis K E) (hζ : pb.gen ^ n = 1) (v : ι → E) :
    let A := Algebra.embeddingsMatrix K ℂ
      (Sum.elim (fun i : Fin n ↦ pb.gen⁻¹ ^ (i : ℕ))
        (fun i : ι × ((E ≃ₐ[K] E) × Fin n) ↦ pb.gen ^ (i.2.2 : ℕ) * i.2.1 (v i.1)))
    Aᴴ * A = ((n : ℂ) * (1 + ∑ i, ∑ ρ : E →ₐ[K] ℂ, (‖ρ (v i)‖ ^ 2 : ℝ))) •
      (1 : Matrix (E →ₐ[K] ℂ) (E →ₐ[K] ℂ) ℂ) := by
  ext σ τ
  have horbit := congr($(pb.conjTranspose_mul_self_embeddingsMatrix_galois_orbit_pow hζ v) σ τ)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Algebra.embeddingsMatrix_apply,
    Complex.star_def, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at horbit ⊢
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [pb.sum_conj_mul_apply_gen_inv_pow hζ σ τ, horbit]
  split_ifs <;> ring

end PowerBasis

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-!
# Rigidity of additive functions of nonsingular matrices

`Matrix.eq_zero_of_map_mul_of_diagonal_of_transvection` shows that an additive function on
nonsingular matrices over a domain vanishes if it vanishes on nonsingular diagonal matrices and
transvections. The proof clears denominators to apply Mathlib's diagonal-transvection induction
over the fraction field.
-/

public section

namespace Matrix

variable {A ι : Type*} [CommRing A] [IsDomain A] [Fintype ι] [DecidableEq ι]

/-- **Rigidity of additive functions of nonsingular matrices.** Over a domain `A`, a function `g`
on square matrices with `g (M * N) = g M + g N` for nonsingular `M` and `N`, vanishing on
nonsingular diagonal matrices and on transvections, vanishes on every nonsingular matrix. -/
theorem eq_zero_of_map_mul_of_diagonal_of_transvection {G : Type*}
    [AddZeroClass G] (g : Matrix ι ι A → G)
    (hmul : ∀ M N : Matrix ι ι A, M.det ≠ 0 → N.det ≠ 0 → g (M * N) = g M + g N)
    (hdiag : ∀ d : ι → A, (∀ i, d i ≠ 0) → g (diagonal d) = 0)
    (htransvec : ∀ i j : ι, i ≠ j → ∀ x : A, g (transvection i j x) = 0)
    {M : Matrix ι ι A} (hM : M.det ≠ 0) : g M = 0 := by
  classical
  let K := FractionRing A
  let φ : Matrix ι ι A →+* Matrix ι ι K := (algebraMap A K).mapMatrix
  have hφ : ∀ M : Matrix ι ι A, φ M = M.map (algebraMap A K) := fun _ ↦ rfl
  have hinj : Function.Injective φ := Matrix.map_injective (IsFractionRing.injective A K)
  have hdet : ∀ M : Matrix ι ι A, (φ M).det = algebraMap A K M.det := fun M ↦
    ((algebraMap A K).map_det M).symm
  have hsmul : ∀ (s : A) (M : Matrix ι ι A), φ (s • M) = algebraMap A K s • φ M := fun s M ↦ by
    ext; simp [hφ]
  -- Multiplying by a nonzero scalar does not change `g`.
  have hscal : ∀ (s : A) (M : Matrix ι ι A), s ≠ 0 → M.det ≠ 0 → g (s • M) = g M := by
    intro s M hs hM
    rw [smul_eq_diagonal_mul, hmul _ _ (by simp [det_diagonal, hs]) hM,
      hdiag _ fun _ ↦ hs, zero_add]
  -- An integral multiple of a nonsingular matrix over `K` is nonsingular.
  have hrep_det : ∀ (N : Matrix ι ι K) (s : A) (M : Matrix ι ι A), s ≠ 0 → N.det ≠ 0 →
      φ M = algebraMap A K s • N → M.det ≠ 0 := by
    intro N s M hs hN hM h0
    have := congrArg det hM
    rw [hdet, h0, map_zero, det_smul] at this
    exact mul_ne_zero (pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hs))
      hN this.symm
  -- Two integral multiples of the same nonsingular matrix have the same value.
  have hrep_eq : ∀ (N : Matrix ι ι K) (s t : A) (M M' : Matrix ι ι A), s ≠ 0 → t ≠ 0 →
      N.det ≠ 0 → φ M = algebraMap A K s • N → φ M' = algebraMap A K t • N → g M = g M' := by
    intro N s t M M' hs ht hN hM hM'
    have h : t • M = s • M' := hinj (by rw [hsmul, hsmul, hM, hM', smul_smul, smul_smul, mul_comm])
    rw [← hscal t M ht (hrep_det N s M hs hN hM), h, hscal s M' hs (hrep_det N t M' ht hN hM')]
  -- Every matrix over `K` has an integral multiple.
  have hrep : ∀ N : Matrix ι ι K, ∃ s : A, s ≠ 0 ∧ ∃ M : Matrix ι ι A,
      φ M = algebraMap A K s • N := by
    intro N
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
      fun p : ι × ι ↦ N p.1 p.2
    choose M hM using hb
    refine ⟨b, nonZeroDivisors.coe_ne_zero b, of fun i j ↦ M (i, j), ?_⟩
    ext i j
    rw [hφ, map_apply, of_apply, hM]
    exact Algebra.smul_def _ _
  -- The matrices over `K` on all of whose integral multiples `g` vanishes.
  let Good (N : Matrix ι ι K) : Prop :=
    ∀ (s : A) (M : Matrix ι ι A), s ≠ 0 → φ M = algebraMap A K s • N → g M = 0
  have hgood_mul : ∀ N N' : Matrix ι ι K, N.det ≠ 0 → N'.det ≠ 0 → Good N → Good N' →
      Good (N * N') := by
    intro N N' hN hN' hgN hgN' s M hs hM
    obtain ⟨s₁, hs₁, M₁, hM₁⟩ := hrep N
    obtain ⟨s₂, hs₂, M₂, hM₂⟩ := hrep N'
    have hM₁₂ : φ (M₁ * M₂) = algebraMap A K (s₁ * s₂) • (N * N') := by
      rw [map_mul, hM₁, hM₂, smul_mul_smul_comm, map_mul]
    rw [hrep_eq _ s (s₁ * s₂) M (M₁ * M₂) hs (mul_ne_zero hs₁ hs₂)
      (by rw [det_mul]; exact mul_ne_zero hN hN') hM hM₁₂,
      hmul _ _ (hrep_det N s₁ M₁ hs₁ hN hM₁) (hrep_det N' s₂ M₂ hs₂ hN' hM₂),
      hgN s₁ M₁ hs₁ hM₁, hgN' s₂ M₂ hs₂ hM₂, add_zero]
  have hgood_diag : ∀ D : ι → K, (∀ i, D i ≠ 0) → Good (diagonal D) := by
    intro D hD s M hs hM
    have hentry : ∀ i j, algebraMap A K (M i j) = algebraMap A K s * diagonal D i j := fun i j ↦ by
      simpa [hφ] using congrFun (congrFun hM i) j
    have hMd : M = diagonal fun i ↦ M i i := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · refine IsFractionRing.injective A K ?_
        rw [hentry, diagonal_apply_ne _ hij, diagonal_apply_ne _ hij, mul_zero, map_zero]
    rw [hMd]
    refine hdiag _ fun i h ↦ ?_
    have := hentry i i
    rw [h, map_zero, diagonal_apply_eq] at this
    exact mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hs) (hD i) this.symm
  have hgood_transvec : ∀ (i j : ι), i ≠ j → ∀ c : K, Good (transvection i j c) := by
    intro i j hij c s M hs hM
    obtain ⟨x, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := A) c
    have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
    have htK : algebraMap A K t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ht0
    -- The transvection with entry `x / t` is `t⁻¹ • u * T x * v`, for the diagonal `u` and `v`.
    let u : ι → A := Function.update 1 j t
    let v : ι → A := Function.update (fun _ ↦ t) j 1
    have hu : ∀ k, u k ≠ 0 := fun k ↦ by
      by_cases hk : k = j <;> simp [u, hk, ht0]
    have hv : ∀ k, v k ≠ 0 := fun k ↦ by
      by_cases hk : k = j <;> simp [v, hk, ht0]
    have hM₀ : φ (diagonal u * transvection i j x * diagonal v) =
        algebraMap A K t • transvection i j (algebraMap A K x / algebraMap A K t) := by
      ext a b
      simp only [hφ, map_apply, mul_diagonal, diagonal_mul,
        transvection, u, v, Function.update_apply,
        Pi.one_apply]
      by_cases hab : a = b
      · subst hab
        have : ¬(i = a ∧ j = a) := fun h ↦ hij (h.1.trans h.2.symm)
        by_cases haj : a = j <;> simp [haj, this, mul_comm, hij]
      · by_cases h : i = a ∧ j = b
        · obtain ⟨rfl, rfl⟩ := h
          simp [hab, mul_div_cancel₀ _ htK]
        · simp [hab, h]
    have hdu : (diagonal u).det ≠ 0 := by
      rw [det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun k _ ↦ hu k
    have hdv : (diagonal v).det ≠ 0 := by
      rw [det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun k _ ↦ hv k
    have hT : (transvection i j x).det ≠ 0 := by
      rw [det_transvection_of_ne _ _ hij]; exact one_ne_zero
    have hTK : (transvection i j (algebraMap A K x / algebraMap A K t)).det ≠ 0 := by
      rw [det_transvection_of_ne _ _ hij]; exact one_ne_zero
    rw [hrep_eq _ s t M _ hs ht0 hTK hM hM₀,
      hmul _ _ (by rw [det_mul]; exact mul_ne_zero hdu hT) hdv, hmul _ _ hdu hT,
      hdiag u hu, hdiag v hv, htransvec i j hij x, add_zero, add_zero]
  have hφM : (φ M).det ≠ 0 := by
    rw [hdet]; exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hM
  have hgood : Good (φ M) := by
    refine diagonal_transvection_induction_of_det_ne_zero Good (φ M) hφM
      (fun D hD ↦ hgood_diag D ?_)
      (fun T ↦ hgood_transvec T.i T.j T.hij T.c) hgood_mul
    simpa only [det_diagonal, Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const] using hD
  exact hgood 1 M one_ne_zero (by rw [map_one, one_smul])

end Matrix

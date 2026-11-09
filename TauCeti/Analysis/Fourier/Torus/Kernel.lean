/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Torus.Smooth
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# The Schwartz kernel theorem on the torus

Let `B` be a bilinear map on pairs of smooth functions on the tori `UnitAddTorus a` and
`UnitAddTorus b`, with values in a complex Banach space `F`, which is continuous for the `C^N`
norms: `‖B f g‖ ≤ C * M₁ * M₂` whenever `DerivBound N M₁ f` and `DerivBound N M₂ g`. This file
proves that `B` has a unique kernel: a linear map `K` on the smooth functions on the product torus
`UnitAddTorus (a ⊕ b)`, continuous for some `C^N'` norm, with `K (f ⊗ g) = B f g` for all smooth
`f` and `g`. Here `(f ⊗ g)(x, y) = f x * g y` is `UnitAddTorus.tensor f g`.

The kernel `LinearMap.schwartzKernel B` is the double Fourier pairing

`K h = ∑ (k, l), mFourierCoeff h (Sum.elim k l) • B (mFourier k) (mFourier l)`.

Continuity of `B` bounds its values on the Fourier monomials polynomially in `(k, l)`, while the
Fourier coefficients of a smooth `h` decay rapidly, so the series converges absolutely, with a
bound by a `C^N'` norm of `h`. The coefficients of `f ⊗ g` are the products
`mFourierCoeff f k * mFourierCoeff g l`, and expanding `f` and `g` in their Fourier series inside
`B` gives `K (f ⊗ g) = B f g`. Uniqueness holds because a continuous linear map is determined by
its values on the monomials, and `mFourier (k, l) = mFourier k ⊗ mFourier l`.

Smooth functions supported in a compact coordinate box are smooth functions on a torus after
periodic extension, so this periodic statement is the local step of the Fourier-series proof of
the Schwartz kernel theorem for distributions.

## Main definitions

* `UnitAddTorus.tensor f g`: the function `(x, y) ↦ f x * g y` on the product torus.
* `LinearMap.schwartzKernel B hB`: the kernel of a continuous bilinear map `B`.

## Main results

* `UnitAddTorus.tensor_add_left`, `UnitAddTorus.tensor_smul_left` and their `right` versions:
  `tensor` is bilinear.
* `UnitAddTorus.tensor_mFourier`: `mFourier k ⊗ mFourier l = mFourier (k, l)`.
* `UnitAddTorus.mFourierCoeff_tensor`: the Fourier coefficients of `f ⊗ g` are the
  products of those of `f` and `g`.
* `LinearMap.exists_norm_schwartzKernel_le`: the kernel is continuous for a `C^N'` norm.
* `LinearMap.schwartzKernel_tensor`: `K (f ⊗ g) = B f g`.
* `LinearMap.eq_schwartzKernel` and `LinearMap.existsUnique_schwartzKernel`: the kernel is the
  unique continuous linear map with this property.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 5.2.1 (the Schwartz kernel theorem, proved by Fourier series on a
  cube).
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped Real

namespace UnitAddTorus

variable {a b : Type*}

/-! ### Tensor products of functions on tori -/

/-- The tensor product `(f ⊗ g)(x, y) = f x * g y` of functions on two tori, as a function on the
product torus `UnitAddTorus (a ⊕ b)`. -/
def tensor (f : UnitAddTorus a → ℂ) (g : UnitAddTorus b → ℂ) : UnitAddTorus (a ⊕ b) → ℂ :=
  fun z ↦ f (fun i ↦ z (.inl i)) * g (fun i ↦ z (.inr i))

@[simp]
theorem tensor_apply (f : UnitAddTorus a → ℂ) (g : UnitAddTorus b → ℂ) (z : UnitAddTorus (a ⊕ b)) :
    tensor f g z = f (fun i ↦ z (.inl i)) * g (fun i ↦ z (.inr i)) :=
  (rfl)

@[simp]
theorem tensor_zero_left (g : UnitAddTorus b → ℂ) : tensor (0 : UnitAddTorus a → ℂ) g = 0 := by
  funext z
  simp

@[simp]
theorem tensor_zero_right (f : UnitAddTorus a → ℂ) : tensor f (0 : UnitAddTorus b → ℂ) = 0 := by
  funext z
  simp

theorem tensor_add_left (f f' : UnitAddTorus a → ℂ) (g : UnitAddTorus b → ℂ) :
    tensor (f + f') g = tensor f g + tensor f' g := by
  funext z
  simp [add_mul]

theorem tensor_add_right (f : UnitAddTorus a → ℂ) (g g' : UnitAddTorus b → ℂ) :
    tensor f (g + g') = tensor f g + tensor f g' := by
  funext z
  simp [mul_add]

theorem tensor_smul_left (c : ℂ) (f : UnitAddTorus a → ℂ) (g : UnitAddTorus b → ℂ) :
    tensor (c • f) g = c • tensor f g := by
  funext z
  simp [mul_assoc]

theorem tensor_smul_right (c : ℂ) (f : UnitAddTorus a → ℂ) (g : UnitAddTorus b → ℂ) :
    tensor f (c • g) = c • tensor f g := by
  funext z
  simp [mul_left_comm]

variable [Fintype a] [Fintype b]

/-- The tensor product of two Fourier monomials is a Fourier monomial. -/
@[simp]
theorem tensor_mFourier (k : a → ℤ) (l : b → ℤ) :
    tensor (mFourier k) (mFourier l) = mFourier (Sum.elim k l) := by
  funext z
  simp [tensor, mFourier, Fintype.prod_sum_type]

/-- The Fourier coefficients of a tensor product are the products of the Fourier coefficients of
its factors. -/
@[simp]
theorem mFourierCoeff_tensor (f : UnitAddTorus a → ℂ) (g : UnitAddTorus b → ℂ)
    (n : a ⊕ b → ℤ) :
    mFourierCoeff (tensor f g) n =
      mFourierCoeff f (fun i ↦ n (.inl i)) * mFourierCoeff g (fun i ↦ n (.inr i)) := by
  simp only [TauCeti.UnitAddTorus.mFourierCoeff_eq_integral_volume]
  rw [← (volume_measurePreserving_sumPiEquivProdPi_symm fun _ : a ⊕ b ↦ UnitAddCircle).integral_comp
    (MeasurableEquiv.measurableEmbedding _), Measure.volume_eq_prod, ← integral_prod_mul]
  congr 1 with p
  simp [tensor, mFourier, Fintype.prod_sum_type, MeasurableEquiv.sumPiEquivProdPi]
  ring

end UnitAddTorus

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {a b : Type*} [Fintype a] [Fintype b]

theorem tensor_mem_smoothFunctions {f : UnitAddTorus a → ℂ} {g : UnitAddTorus b → ℂ}
    (hf : f ∈ smoothFunctions a) (hg : g ∈ smoothFunctions b) :
    tensor f g ∈ smoothFunctions (a ⊕ b) := by
  rw [mem_smoothFunctions] at *
  exact (hf.comp (contDiff_pi.2 fun i ↦ by fun_prop)).mul
    (hg.comp (contDiff_pi.2 fun i ↦ by fun_prop))

end TauCeti.UnitAddTorus

/-! ### The kernel of a continuous bilinear map -/

namespace LinearMap

open TauCeti.UnitAddTorus _root_.UnitAddTorus

variable {a b : Type*} [Fintype a] [Fintype b]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  (B : smoothFunctions a →ₗ[ℂ] smoothFunctions b →ₗ[ℂ] F)
  (hB : ∃ (C : ℝ) (N : ℕ), ∀ (f : smoothFunctions a) (g : smoothFunctions b) (M₁ M₂ : ℝ),
    DerivBound N M₁ (f : UnitAddTorus a → ℂ) →
      DerivBound N M₂ (g : UnitAddTorus b → ℂ) → ‖B f g‖ ≤ C * M₁ * M₂)

omit [CompleteSpace F] in
/-- The constant in a continuity bound for `B` is nonnegative. -/
private theorem nonneg_of_bound {C : ℝ} {N : ℕ}
    (hCN : ∀ (f : smoothFunctions a) (g : smoothFunctions b) (M₁ M₂ : ℝ),
      DerivBound N M₁ (f : UnitAddTorus a → ℂ) → DerivBound N M₂ (g : UnitAddTorus b → ℂ) →
        ‖B f g‖ ≤ C * M₁ * M₂) : 0 ≤ C := by
  have h0 : DerivBound N 1 ((0 : smoothFunctions a) : UnitAddTorus a → ℂ) :=
    (derivBound_zero N).mono zero_le_one
  have h0' : DerivBound N 1 ((0 : smoothFunctions b) : UnitAddTorus b → ℂ) :=
    (derivBound_zero N).mono zero_le_one
  simpa using (norm_nonneg _).trans (hCN 0 0 1 1 h0 h0')

omit [CompleteSpace F] in
/-- The values of `B` on pairs of Fourier monomials grow at most polynomially. -/
private theorem norm_apply_mFourierSmooth_le {C : ℝ} {N : ℕ}
    (hCN : ∀ (f : smoothFunctions a) (g : smoothFunctions b) (M₁ M₂ : ℝ),
      DerivBound N M₁ (f : UnitAddTorus a → ℂ) → DerivBound N M₂ (g : UnitAddTorus b → ℂ) →
        ‖B f g‖ ≤ C * M₁ * M₂) (n : a ⊕ b → ℤ) :
    ‖B (mFourierSmooth fun i ↦ n (.inl i)) (mFourierSmooth fun i ↦ n (.inr i))‖ ≤
      C * (1 + 2 * π * Fintype.card (a ⊕ b) * ‖n‖) ^ (2 * N) := by
  have hl : ‖fun i ↦ n (.inl i)‖ ≤ ‖n‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg n)).2 fun i ↦ norm_le_pi_norm n (.inl i)
  have hr : ‖fun i ↦ n (.inr i)‖ ≤ ‖n‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg n)).2 fun i ↦ norm_le_pi_norm n (.inr i)
  have hca : (Fintype.card a : ℝ) ≤ Fintype.card (a ⊕ b) := by
    rw [Fintype.card_sum, Nat.cast_add]
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card b)]
  have hcb : (Fintype.card b : ℝ) ≤ Fintype.card (a ⊕ b) := by
    rw [Fintype.card_sum, Nat.cast_add]
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card a)]
  have h1 : DerivBound N ((1 + 2 * π * Fintype.card (a ⊕ b) * ‖n‖) ^ N)
      ((mFourierSmooth fun i ↦ n (.inl i) : smoothFunctions a) : UnitAddTorus a → ℂ) := by
    rw [coe_mFourierSmooth]
    exact (derivBound_mFourier _ N).mono (by gcongr)
  have h2 : DerivBound N ((1 + 2 * π * Fintype.card (a ⊕ b) * ‖n‖) ^ N)
      ((mFourierSmooth fun i ↦ n (.inr i) : smoothFunctions b) : UnitAddTorus b → ℂ) := by
    rw [coe_mFourierSmooth]
    exact (derivBound_mFourier _ N).mono (by gcongr)
  exact (hCN _ _ _ _ h1 h2).trans_eq (by ring)

include hB in
private theorem summable_schwartzKernel (h : smoothFunctions (a ⊕ b)) :
    Summable fun n ↦ mFourierCoeff (h : UnitAddTorus (a ⊕ b) → ℂ) n •
      B (mFourierSmooth fun i ↦ n (.inl i)) (mFourierSmooth fun i ↦ n (.inr i)) := by
  obtain ⟨C, N, hCN⟩ := hB
  refine Summable.of_norm_bounded ((summable_norm_mFourierCoeff_mul_pow h.2
    (R := 2 * π * Fintype.card (a ⊕ b)) (by positivity) (2 * N)).mul_left C) fun n ↦ ?_
  rw [norm_smul]
  calc _ ≤ ‖mFourierCoeff (h : UnitAddTorus (a ⊕ b) → ℂ) n‖ *
        (C * (1 + 2 * π * Fintype.card (a ⊕ b) * ‖n‖) ^ (2 * N)) := by
        gcongr
        exact norm_apply_mFourierSmooth_le B hCN n
    _ = _ := by ring

/-- The kernel of a bilinear map `B` on smooth functions on two tori which is continuous for the
`C^N` norms: the linear map on smooth functions on the product torus given by the double Fourier
pairing `h ↦ ∑ (k, l), mFourierCoeff h (Sum.elim k l) • B (mFourier k) (mFourier l)`. -/
def schwartzKernel : smoothFunctions (a ⊕ b) →ₗ[ℂ] F where
  toFun h := ∑' n, mFourierCoeff (h : UnitAddTorus (a ⊕ b) → ℂ) n •
    B (mFourierSmooth fun i ↦ n (.inl i)) (mFourierSmooth fun i ↦ n (.inr i))
  map_add' h h' := by
    rw [← (summable_schwartzKernel B hB h).tsum_add (summable_schwartzKernel B hB h')]
    congr 1 with n
    rw [Submodule.coe_add, UnitAddTorus.mFourierCoeff_add (integrable_of_mem_smoothFunctions h.2)
      (integrable_of_mem_smoothFunctions h'.2), add_smul]
  map_smul' c h := by
    rw [RingHom.id_apply, ← (summable_schwartzKernel B hB h).tsum_const_smul c]
    congr 1 with n
    rw [Submodule.coe_smul, UnitAddTorus.mFourierCoeff_smul, smul_eq_mul, mul_smul]

theorem schwartzKernel_apply (h : smoothFunctions (a ⊕ b)) :
    schwartzKernel B hB h = ∑' n, mFourierCoeff (h : UnitAddTorus (a ⊕ b) → ℂ) n •
      B (mFourierSmooth fun i ↦ n (.inl i)) (mFourierSmooth fun i ↦ n (.inr i)) :=
  (rfl)

/-- **Continuity of the kernel.** The kernel of `B` is continuous for a `C^N'` norm. -/
theorem exists_norm_schwartzKernel_le : ∃ (C' : ℝ) (N' : ℕ), ∀ (h : smoothFunctions (a ⊕ b)) M,
    DerivBound N' M (h : UnitAddTorus (a ⊕ b) → ℂ) → ‖schwartzKernel B hB h‖ ≤ C' * M := by
  have ⟨C, N, hCN⟩ := hB
  have hC := nonneg_of_bound B hCN
  refine ⟨C * (1 + 2 * π * Fintype.card (a ⊕ b)) ^ (2 * N) *
    (2 ^ (2 * N + Fintype.card (a ⊕ b) + 2) *
      ∑' n : a ⊕ b → ℤ, ((1 + ‖n‖) ^ (Fintype.card (a ⊕ b) + 1))⁻¹),
    2 * N + Fintype.card (a ⊕ b) + 1, fun h M hM ↦ ?_⟩
  have hM0 := hM.nonneg
  -- The `n`-th term is bounded by a constant times `M` times a summable weight.
  have key (n : a ⊕ b → ℤ) : ‖mFourierCoeff (h : UnitAddTorus (a ⊕ b) → ℂ) n •
      B (mFourierSmooth fun i ↦ n (.inl i)) (mFourierSmooth fun i ↦ n (.inr i))‖ ≤
      C * (1 + 2 * π * Fintype.card (a ⊕ b)) ^ (2 * N) *
        (2 ^ (2 * N + Fintype.card (a ⊕ b) + 2) * M *
          ((1 + ‖n‖) ^ (Fintype.card (a ⊕ b) + 1))⁻¹) := by
    have hpow : (1 + 2 * π * Fintype.card (a ⊕ b) * ‖n‖) ^ (2 * N) ≤
        (1 + 2 * π * Fintype.card (a ⊕ b)) ^ (2 * N) * (1 + ‖n‖) ^ (2 * N) := by
      rw [← mul_pow]
      gcongr
      nlinarith [norm_nonneg n, (by positivity : (0 : ℝ) ≤ 2 * π * Fintype.card (a ⊕ b))]
    have hcd : ContDiff ℝ (2 * N + Fintype.card (a ⊕ b) + 1)
        fun x : a ⊕ b → ℝ ↦ (h : UnitAddTorus (a ⊕ b) → ℂ) fun i ↦ (x i : UnitAddCircle) :=
      (mem_smoothFunctions.1 h.2).of_le (WithTop.coe_le_coe.2 le_top)
    have hdecay := one_add_norm_pow_mul_norm_mFourierCoeff_le_mul_inv (N := 2 * N) hcd hM n
    rw [norm_smul]
    calc _ ≤ ‖mFourierCoeff (h : UnitAddTorus (a ⊕ b) → ℂ) n‖ *
          (C * ((1 + 2 * π * Fintype.card (a ⊕ b)) ^ (2 * N) * (1 + ‖n‖) ^ (2 * N))) := by
          gcongr
          exact (norm_apply_mFourierSmooth_le B hCN n).trans (by gcongr)
      _ = C * (1 + 2 * π * Fintype.card (a ⊕ b)) ^ (2 * N) *
          ((1 + ‖n‖) ^ (2 * N) * ‖mFourierCoeff (h : UnitAddTorus (a ⊕ b) → ℂ) n‖) := by ring
      _ ≤ _ := by gcongr
  rw [schwartzKernel_apply]
  refine (tsum_of_norm_bounded
    ((TauCeti.summable_pi_int_inv_one_add_norm_pow.mul_left _).mul_left _).hasSum key).trans_eq ?_
  rw [tsum_mul_left, tsum_mul_left]
  ring

/-- **The kernel theorem.** The kernel of `B` represents `B` on tensor products:
`K (f ⊗ g) = B f g`. -/
theorem schwartzKernel_tensor (f : smoothFunctions a) (g : smoothFunctions b) :
    schwartzKernel B hB ⟨tensor f g, tensor_mem_smoothFunctions f.2 g.2⟩ = B f g := by
  have ⟨C, N, hCN⟩ := hB
  obtain ⟨Mg, hMg⟩ := exists_derivBound g.2 N
  -- Expansion of `B (mFourier k) g` in the Fourier series of `g`.
  have hrow (k : a → ℤ) : HasSum (fun l ↦ mFourierCoeff (g : UnitAddTorus b → ℂ) l •
      B (mFourierSmooth k) (mFourierSmooth l)) (B (mFourierSmooth k) g) :=
    (B (mFourierSmooth k)).hasSum_mFourierCoeff_smul_apply
      (C := C * (1 + 2 * π * Fintype.card a * ‖k‖) ^ N) (N := N) (fun v M hv ↦
        (hCN _ v _ M (by simpa using derivBound_mFourier k N) hv).trans_eq (by ring)) g
  -- Expansion of `B f g` in the Fourier series of `f`.
  have hcol : HasSum (fun k ↦ mFourierCoeff (f : UnitAddTorus a → ℂ) k • B (mFourierSmooth k) g)
      (B f g) := by
    simpa using (B.flip g).hasSum_mFourierCoeff_smul_apply (C := C * Mg) (N := N)
      (fun u M hu ↦ by simpa [mul_right_comm] using hCN u g M Mg hu hMg) f
  -- The double Fourier series converges absolutely.
  have hp : Summable fun q : (a → ℤ) × (b → ℤ) ↦ mFourierCoeff (f : UnitAddTorus a → ℂ) q.1 •
      mFourierCoeff (g : UnitAddTorus b → ℂ) q.2 • B (mFourierSmooth q.1) (mFourierSmooth q.2) := by
    refine Summable.of_norm_bounded
      (((summable_norm_mFourierCoeff_mul_pow f.2 (R := 2 * π * Fintype.card a) (by positivity)
        N).mul_of_nonneg (summable_norm_mFourierCoeff_mul_pow g.2
          (R := 2 * π * Fintype.card b) (by positivity) N) (fun _ ↦ by positivity)
          (fun _ ↦ by positivity)).mul_left C) fun q ↦ ?_
    have hq := hCN (mFourierSmooth q.1) (mFourierSmooth q.2) _ _
      (by simpa using derivBound_mFourier q.1 N) (by simpa using derivBound_mFourier q.2 N)
    rw [norm_smul, norm_smul]
    calc _ ≤ ‖mFourierCoeff (f : UnitAddTorus a → ℂ) q.1‖ *
          (‖mFourierCoeff (g : UnitAddTorus b → ℂ) q.2‖ *
            (C * (1 + 2 * π * Fintype.card a * ‖q.1‖) ^ N *
              (1 + 2 * π * Fintype.card b * ‖q.2‖) ^ N)) := by gcongr
      _ = _ := by ring
  have hfib := hp.hasSum.prod_fiberwise fun k ↦ (hrow k).const_smul
    (mFourierCoeff (f : UnitAddTorus a → ℂ) k)
  rw [schwartzKernel_apply, hcol.unique hfib,
    ← (Equiv.sumArrowEquivProdArrow a b ℤ).symm.tsum_eq]
  congr 1 with ⟨k, l⟩
  simp [mFourierCoeff_tensor, mul_smul]

/-- **Uniqueness of the kernel.** A linear map on smooth functions on the product torus, continuous
for some `C^N` norm, which represents `B` on tensor products is the kernel of `B`. -/
theorem eq_schwartzKernel {K : smoothFunctions (a ⊕ b) →ₗ[ℂ] F}
    (hK : ∃ (C : ℝ) (N : ℕ), ∀ (h : smoothFunctions (a ⊕ b)) M,
      DerivBound N M (h : UnitAddTorus (a ⊕ b) → ℂ) → ‖K h‖ ≤ C * M)
    (hKB : ∀ (f : smoothFunctions a) (g : smoothFunctions b),
      K ⟨tensor f g, tensor_mem_smoothFunctions f.2 g.2⟩ = B f g) :
    K = schwartzKernel B hB := by
  refine linearMap_eq_of_apply_mFourierSmooth_eq hK (exists_norm_schwartzKernel_le B hB)
    fun n ↦ ?_
  have hn : mFourierSmooth n = ⟨tensor (mFourierSmooth fun i ↦ n (.inl i) : smoothFunctions a)
      (mFourierSmooth fun i ↦ n (.inr i) : smoothFunctions b),
      tensor_mem_smoothFunctions (mFourierSmooth _).2 (mFourierSmooth _).2⟩ := by
    have he : Sum.elim (fun i ↦ n (.inl i)) (fun i ↦ n (.inr i)) = n :=
      funext fun i ↦ by cases i <;> rfl
    refine Subtype.ext ?_
    simp only [coe_mFourierSmooth, tensor_mFourier, he]
  rw [hn, hKB, schwartzKernel_tensor]

include hB in
/-- **The Schwartz kernel theorem on the torus.** A bilinear map on smooth functions on two tori
which is continuous for the `C^N` norms has a unique kernel: a linear map on smooth functions on
the product torus, continuous for some `C^N'` norm, which agrees with it on tensor products. -/
theorem existsUnique_schwartzKernel : ∃! K : smoothFunctions (a ⊕ b) →ₗ[ℂ] F,
    (∃ (C : ℝ) (N : ℕ), ∀ (h : smoothFunctions (a ⊕ b)) M,
      DerivBound N M (h : UnitAddTorus (a ⊕ b) → ℂ) → ‖K h‖ ≤ C * M) ∧
    ∀ (f : smoothFunctions a) (g : smoothFunctions b),
      K ⟨tensor f g, tensor_mem_smoothFunctions f.2 g.2⟩ = B f g :=
  ⟨schwartzKernel B hB, ⟨exists_norm_schwartzKernel_le B hB, schwartzKernel_tensor B hB⟩,
    fun _ hK ↦ eq_schwartzKernel B hB hK.1 hK.2⟩

end LinearMap

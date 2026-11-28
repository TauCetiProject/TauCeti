/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Convolution
public import TauCeti.Analysis.Normed.Algebra.DividedPower
public import TauCeti.Analysis.Normed.Unbundled.RingSeminorm
public import TauCeti.Analysis.Normed.Field.Basic
public import TauCeti.Analysis.Normed.Field.NatCast
public import TauCeti.Topology.Algebra.Valued.NormedValued
public import TauCeti.Algebra.Coalgebra.Convolution.FiniteCoefficients
public import TauCeti.RingTheory.IntegralClosure.AlgHom
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Integral nearly primitive functionals

A functional on a finite free cocommutative bialgebra over the integers of an algebraically closed
ultrametric field is integral after scaling by the factorial radius, provided its values
at group-like elements and its deviation from the Leibniz rule are integral.
The proof combines character descent, bounded powers of integral elements, and the
ultrametric divided-power estimate. No completeness assumption is needed.

## References

The argument is due to L. Alpöge, from his formal Lean proof of the Riemann hypothesis
for Dirichlet L-functions (2026), https://github.com/leanprover-community/riemann-hypothesis;
the formalization here is independent of that source.
-/

public noncomputable section

open TensorProduct WithConv

namespace WithConv

section Valuation

variable {C : Type*} [NormedField C] [IsUltrametricDist C]

local notation "O(" C ")" => Valuation.valuationSubring (NormedField.valuation (K := C))

section Coalgebra

variable {A : Type*} [AddCommGroup A] [Module O(C) A] [Coalgebra O(C) A]
  [Coalgebra.IsCocomm O(C) A] [Module.Finite O(C) A] [Module.Free O(C) A]

/-- A functional integral at all group-like elements has bounded convolution powers. -/
theorem exists_bound_pow_of_groupLike [IsAlgClosed C] (y : WithConv (A →ₗ[O(C)] C))
    (hy : ∀ u : GroupLike O(C) A, y.ofConv u.val ∈ O(C)) :
    ∃ K : ℝ, ∀ n : ℕ, (y ^ n).ofConv.supNorm ≤ K := by
  have : Module.Finite C (WithConv (A →ₗ[O(C)] C)) :=
    Module.Finite.equiv (WithConv.linearEquiv C _).symm
  have hyint : IsIntegral O(C) y :=
    (TauCeti.isIntegral_iff_forall_algHom_mem_range (R := O(C)) (K := C)).mpr fun χ ↦ by
      obtain ⟨u, hu, -⟩ := TauCeti.ConvolutionDual.existsUnique_groupLike_algHom_coefficients χ
      rw [hu]
      exact ⟨⟨y.ofConv u.val, hy u⟩, rfl⟩
  simp_rw [← supNormRingSeminorm_apply
    (Valuation.valuationSubring.integers _).norm_algebraMap_le_one]
  apply (supNormRingSeminorm (M := A)
    (Valuation.valuationSubring.integers _).norm_algebraMap_le_one).exists_bound_pow_of_isIntegral _
      hyint
  intro r f
  have heq : (r • f : WithConv (A →ₗ[O(C)] C)) = (r : C) • f :=
    (algebraMap_smul C r f).symm
  simp only [heq, supNormRingSeminorm_apply, ofConv_smul, LinearMap.supNorm_smul]
  exact (mul_le_mul_of_nonneg_right
    ((Valuation.valuationSubring.integers _).norm_algebraMap_le_one r)
    f.ofConv.supNorm_nonneg).trans_eq
    (one_mul _)

end Coalgebra

variable {A : Type*} [Ring A] [Bialgebra O(C) A] [Coalgebra.IsCocomm O(C) A]
  [Module.Finite O(C) A] [Module.Free O(C) A]

/-- A nearly primitive functional integral at group-like elements becomes integral after
scaling by any scalar in the closed factorial radius, at every prime including `2`. -/
theorem mul_apply_mem_valuationSubring_of_groupLike [IsAlgClosed C]
    (p : ℕ) (hp : p.Prime) (hpC : ‖(p : C)‖ < 1) (y : WithConv (A →ₗ[O(C)] C))
    (hy : ∀ u : GroupLike O(C) A, y.ofConv u.val ∈ O(C))
    (he : ∀ a b : A, y.ofConv (a * b) -
      algebraMap O(C) C (Coalgebra.counit b) * y.ofConv a -
      algebraMap O(C) C (Coalgebra.counit a) * y.ofConv b ∈ O(C))
    (κ : C) (hκ : ‖κ‖ ^ (p - 1) ≤ ‖(p : C)‖) (a : A) :
    κ * y.ofConv a ∈ O(C) := by
  by_cases hp0 : (p : C) = 0
  · have hκ0 : κ = 0 := eq_zero_of_pow_eq_zero (norm_le_zero_iff.mp
      (by simpa only [norm_pow, hp0, norm_zero] using hκ : ‖κ ^ (p - 1)‖ ≤ 0))
    simp [hκ0]
  have : CharZero C := NormedField.charZero_of_norm_natCast_ne_one hpC.ne hp0
  let : NontriviallyNormedField C := NontriviallyNormedField.ofNormNeOne
    ⟨(p : C), Nat.cast_ne_zero.mpr hp.ne_zero, hpC.ne⟩
  let : DenselyNormedField C :=
    { ‹NontriviallyNormedField C› with
      lt_norm_lt := fun _ _ h₀ hlt ↦
        NormedField.exists_lt_norm_lt_of_isAlgClosed C h₀ hlt }
  let N := supNormRingSeminorm (M := A)
    ((Valuation.valuationSubring.integers _).norm_algebraMap_le_one (K := C))
  let M := supNormRingSeminorm (M := A ⊗[O(C)] A)
    ((Valuation.valuationSubring.integers _).norm_algebraMap_le_one (K := C))
  have herr : M (TauCeti.Bialgebra.convolutionDelta O(C) C A y -
      tensorCounitRight O(C) C A A y - tensorCounitLeft O(C) C A A y) ≤ 1 := by
    simp only [M, supNormRingSeminorm_apply]
    apply (LinearMap.supNorm_le_iff _
      (Valuation.valuationSubring.integers _).norm_algebraMap_le_one).mpr
    apply LinearMap.norm_apply_le_of_tmul
    intro a b
    have h := he a b
    have hn : ‖y.ofConv (a * b) -
        algebraMap O(C) C (Coalgebra.counit b) * y.ofConv a -
        algebraMap O(C) C (Coalgebra.counit a) * y.ofConv b‖ ≤ 1 := by
      rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply] at h
      exact_mod_cast h
    simpa [mul_comm] using hn
  have hcross (f g : WithConv (A →ₗ[O(C)] C)) :
      M (tensorCounitRight O(C) C A A f * tensorCounitLeft O(C) C A A g) = N f * N g := by
    have h : tensorCounitRight O(C) C A A f * tensorCounitLeft O(C) C A A g = mulTensor f g := by
      simp
    simp only [h, M, N, supNormRingSeminorm_apply]
    exact supNorm_mulTensor f g (Valuation.valuationSubring.integers _).norm_algebraMap_le_one
  have hbound := N.smul_le_one_of_bounded_powers M
    (isNonarchimedean_supNormRingSeminorm _) (fun c f ↦ by
      simpa only [N, supNormRingSeminorm_apply, ofConv_smul] using
        LinearMap.supNorm_smul c f.ofConv)
    (TauCeti.Bialgebra.convolutionDelta O(C) C A) (tensorCounitRight O(C) C A A)
    (tensorCounitLeft O(C) C A A) (fun f ↦ by
      simpa only [M, N, supNormRingSeminorm_apply] using supNorm_convolutionDelta_le f
        (Valuation.valuationSubring.integers _).norm_algebraMap_le_one)
    hcross p hp hpC y (by
      simpa only [N, supNormRingSeminorm_apply] using exists_bound_pow_of_groupLike y hy) herr κ hκ
  exact (LinearMap.supNorm_le_one_iff _).mp
    (by simpa only [N, supNormRingSeminorm_apply] using hbound) a

/-- A linear functional which is divisible by `q` on group-like elements and satisfies the
Leibniz rule modulo `q` is divisible by `q` everywhere after scaling in the factorial radius. -/
theorem _root_.TauCeti.dvd_mul_apply_of_groupLike [IsAlgClosed C]
    (p : ℕ) (hp : p.Prime) (hpC : ‖(p : C)‖ < 1)
    (D : A →ₗ[O(C)] O(C)) {q : O(C)} (hq : q ≠ 0)
    (hgroup : ∀ u : GroupLike O(C) A, q ∣ D u.val)
    (hrel : ∀ a b : A, q ∣ D (a * b) - Coalgebra.counit b * D a - Coalgebra.counit a * D b)
    (κ : O(C)) (hκ : ‖(κ : C)‖ ^ (p - 1) ≤ ‖(p : C)‖) (a : A) :
    q ∣ κ * D a := by
  have hqC : algebraMap O(C) C q ≠ 0 :=
    fun h ↦ hq ((IsFractionRing.injective O(C) C) (h.trans (map_zero _).symm))
  let y := toConv ((algebraMap O(C) C q)⁻¹ • ((Algebra.linearMap O(C) C).comp D))
  have hy_apply (b : A) : y.ofConv b = (algebraMap O(C) C q)⁻¹ * (algebraMap O(C) C (D b)) := by
    simp [y]
  have hy (u : GroupLike O(C) A) : y.ofConv u.val ∈ O(C) := by
    obtain ⟨c, hc⟩ := hgroup u
    rw [hy_apply, hc, map_mul, inv_mul_cancel_left₀ hqC]
    simpa only [ValuationSubring.algebraMap_apply] using c.property
  have he (b c : A) : y.ofConv (b * c) -
      algebraMap O(C) C (Coalgebra.counit c) * y.ofConv b -
      algebraMap O(C) C (Coalgebra.counit b) * y.ofConv c ∈ O(C) := by
    obtain ⟨d, hd⟩ := hrel b c
    have heq : y.ofConv (b * c) -
        algebraMap O(C) C (Coalgebra.counit c) * y.ofConv b -
        algebraMap O(C) C (Coalgebra.counit b) * y.ofConv c = algebraMap O(C) C d := by
      calc
        _ = (algebraMap O(C) C q)⁻¹ * algebraMap O(C) C
            (D (b * c) - Coalgebra.counit c * D b - Coalgebra.counit b * D c) := by
          simp only [hy_apply, map_sub, map_mul]
          ring
        _ = _ := by rw [hd, map_mul, inv_mul_cancel_left₀ hqC]
    rw [heq]
    simpa only [ValuationSubring.algebraMap_apply] using d.property
  have h := mul_apply_mem_valuationSubring_of_groupLike p hp hpC y hy he (κ : C) hκ a
  refine ⟨⟨(κ : C) * y.ofConv a, h⟩, ?_⟩
  apply IsFractionRing.injective O(C) C
  simp only [map_mul, ValuationSubring.algebraMap_apply, hy_apply]
  simp only [ValuationSubring.algebraMap_apply] at hqC
  field_simp

end Valuation

end WithConv

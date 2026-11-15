/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Ring.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.LinearTopology

/-!
# Restricted formal power series over a left-linearly topologized ring

Over a topological ring `A` with a left-linear topology (`IsLinearTopology A A`), formal power
series `f ∈ A⟦X⟧` with `coeff n f → 0` are closed under Cauchy multiplication
(`PowerSeries.tendsto_coeff_mul_atTop_nhds_zero`), forming `PowerSeries.coeffTendstoZeroSubring A`
and `PowerSeries.coeffTendstoZeroSubalgebra R A`. Centrality in both `A⟦X⟧` and the restricted
subalgebra is coefficientwise centrality in `A`, constants and `R[X]` intersect in `⊥`
(`PowerSeries.range_coeffTendstoZeroCAlgHom_inf_adjoin_X`), and restricted series can be evaluated
at central elements of complete Hausdorff left-linearly topologized algebras
(`PowerSeries.coeffTendstoZeroEval`).

## References

* N. Bourbaki, *Commutative Algebra*, Chapter III, §4.2.
* E. Frenkel, *Langlands Correspondence for Loop Groups*, §4.3.2.
-/

public section

open Filter
open scoped Topology

namespace PowerSeries

section Center

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- A formal power series in `A⟦X⟧` is central if and only if each coefficient is central in `A`. -/
theorem mem_center_iff {f : A⟦X⟧} :
    f ∈ Subalgebra.center R A⟦X⟧ ↔ ∀ n, coeff n f ∈ Subalgebra.center R A := by
  refine ⟨fun hf n ↦ Subalgebra.mem_center_iff.2 fun a ↦ ?_,
    fun hf ↦ Subalgebra.mem_center_iff.2 fun g ↦ ?_⟩
  · simpa only [coeff_C_mul, coeff_mul_C] using
      congrArg (coeff n) (Subalgebra.mem_center_iff.1 hf (C a))
  · ext n
    rw [coeff_mul, coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
    exact Finset.sum_congr rfl fun p _ ↦ Subalgebra.mem_center_iff.1 (hf p.1) (coeff p.2 g)

end Center

section Semiring

variable {A : Type*} [Semiring A] [TopologicalSpace A]

/-- Constant series have coefficients eventually zero, hence tending to `0`. -/
theorem tendsto_coeff_C_atTop_nhds_zero (a : A) :
    Tendsto (fun n ↦ coeff n (C a)) atTop (𝓝 0) :=
  tendsto_const_nhds.congr' <| by
    filter_upwards [eventually_ge_atTop 1] with n hn; simp [coeff_C, Nat.ne_of_gt hn]

/-- Monomials have coefficients eventually zero, hence tending to `0`. -/
theorem tendsto_coeff_monomial_atTop_nhds_zero (d : ℕ) (a : A) :
    Tendsto (fun n ↦ coeff n (monomial d a)) atTop (𝓝 0) :=
  tendsto_const_nhds.congr' <| by
    filter_upwards [eventually_ge_atTop (d + 1)] with n hn; simp [coeff_monomial, Nat.ne_of_gt hn]

/-- The indeterminate `X` has coefficients tending to `0`. -/
theorem tendsto_coeff_X_atTop_nhds_zero :
    Tendsto (fun n ↦ coeff n (X : A⟦X⟧)) atTop (𝓝 0) :=
  tendsto_const_nhds.congr' <| by
    filter_upwards [eventually_ge_atTop 2] with n hn; simp [coeff_X, show n ≠ 1 by omega]

end Semiring

section LinearTopology

variable {A : Type*} [Ring A] [TopologicalSpace A]

/-- **Cauchy products of restricted series** over a left-linearly topologized ring `A`. -/
theorem tendsto_coeff_mul_atTop_nhds_zero [IsTopologicalRing A] [IsLinearTopology A A]
    {f g : A⟦X⟧} (hf : Tendsto (fun n ↦ coeff n f) atTop (𝓝 0))
    (hg : Tendsto (fun n ↦ coeff n g) atTop (𝓝 0)) :
    Tendsto (fun n ↦ coeff n (f * g)) atTop (𝓝 0) := by
  rw [(IsLinearTopology.hasBasis_submodule A).tendsto_right_iff]
  rintro J (hJ : (J : Set A) ∈ 𝓝 0)
  obtain ⟨L, hL⟩ := eventually_atTop.1 (hg hJ)
  have hfin : ∀ᶠ k in atTop, ∀ l ∈ Finset.range L, coeff k f * coeff l g ∈ J :=
    (Finset.range L).eventually_all.2 fun l _ ↦ hf <|
      (show ContinuousAt (fun x : A ↦ x * coeff l g) 0 from
        (continuous_id.mul continuous_const).continuousAt).preimage_mem_nhds
        (by simpa only [zero_mul] using hJ)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hfin
  refine eventually_atTop.2 ⟨K + L, fun n hn ↦ ?_⟩
  rw [coeff_mul]
  refine J.sum_mem fun p hp ↦ ?_
  have hp' : p.1 + p.2 = n := Finset.mem_antidiagonal.1 hp
  by_cases hl : L ≤ p.2
  · exact J.smul_mem (coeff p.1 f) (hL p.2 hl)
  · exact hK p.1 (by omega) p.2 (Finset.mem_range.2 (not_le.1 hl))

variable (A) in
/-- **The subring of restricted formal power series** `{f ∈ A⟦X⟧ | coeff n f → 0}`. -/
noncomputable def coeffTendstoZeroSubring [IsTopologicalRing A] [IsLinearTopology A A] :
    Subring A⟦X⟧ where
  carrier := {f | Tendsto (fun n ↦ coeff n f) atTop (𝓝 0)}
  zero_mem' := by change Tendsto _ _ _; simpa only [map_zero] using tendsto_const_nhds
  one_mem' := by
    change Tendsto _ _ _; simpa only [← map_one C] using tendsto_coeff_C_atTop_nhds_zero (1 : A)
  add_mem' hf hg := by change Tendsto _ _ _; simpa only [map_add, add_zero] using hf.add hg
  neg_mem' hf := by change Tendsto _ _ _; simpa only [map_neg, neg_zero] using hf.neg
  mul_mem' hf hg := tendsto_coeff_mul_atTop_nhds_zero hf hg

variable [IsTopologicalRing A] [IsLinearTopology A A]

@[simp]
theorem mem_coeffTendstoZeroSubring_iff {f : A⟦X⟧} :
    f ∈ coeffTendstoZeroSubring A ↔ Tendsto (fun n ↦ coeff n f) atTop (𝓝 0) := Iff.rfl

theorem C_mem_coeffTendstoZeroSubring (a : A) : C a ∈ coeffTendstoZeroSubring A :=
  tendsto_coeff_C_atTop_nhds_zero a

theorem monomial_mem_coeffTendstoZeroSubring (d : ℕ) (a : A) :
    monomial d a ∈ coeffTendstoZeroSubring A := tendsto_coeff_monomial_atTop_nhds_zero d a

theorem X_mem_coeffTendstoZeroSubring : (X : A⟦X⟧) ∈ coeffTendstoZeroSubring A :=
  tendsto_coeff_X_atTop_nhds_zero

end LinearTopology

section Subalgebra

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

variable (R A) in
/-- **The `R`-subalgebra of restricted formal power series** `{f ∈ A⟦X⟧ | coeff n f → 0}`. -/
noncomputable def coeffTendstoZeroSubalgebra : Subalgebra R A⟦X⟧ where
  __ := coeffTendstoZeroSubring A
  algebraMap_mem' r := by rw [algebraMap_apply]; exact C_mem_coeffTendstoZeroSubring _

@[simp]
theorem mem_coeffTendstoZeroSubalgebra_iff {f : A⟦X⟧} :
    f ∈ coeffTendstoZeroSubalgebra R A ↔ Tendsto (fun n ↦ coeff n f) atTop (𝓝 0) := Iff.rfl

variable (R A) in
/-- The embedding of constants `a ↦ C a` into `coeffTendstoZeroSubalgebra R A`. -/
noncomputable def coeffTendstoZeroCAlgHom : A →ₐ[R] coeffTendstoZeroSubalgebra R A where
  toFun a := ⟨C a, C_mem_coeffTendstoZeroSubring a⟩
  map_one' := Subtype.ext (map_one C)
  map_mul' a b := Subtype.ext (map_mul C a b)
  map_zero' := Subtype.ext (map_zero C)
  map_add' a b := Subtype.ext (map_add C a b)
  commutes' _ := Subtype.ext algebraMap_apply.symm

@[simp]
theorem coe_coeffTendstoZeroCAlgHom (a : A) :
    (coeffTendstoZeroCAlgHom R A a : A⟦X⟧) = C a := (rfl)

theorem coeffTendstoZeroCAlgHom_injective :
    Function.Injective (coeffTendstoZeroCAlgHom R A) := fun _ _ h ↦ by
  simpa using congrArg (fun f : coeffTendstoZeroSubalgebra R A ↦ coeff 0 (f : A⟦X⟧)) h

variable (R A) in
/-- The indeterminate `X` as an element of `coeffTendstoZeroSubalgebra R A`. -/
noncomputable def coeffTendstoZeroX : coeffTendstoZeroSubalgebra R A :=
  ⟨X, X_mem_coeffTendstoZeroSubring⟩

@[simp]
theorem coe_coeffTendstoZeroX : (coeffTendstoZeroX R A : A⟦X⟧) = X := (rfl)

/-- Centrality in `coeffTendstoZeroSubalgebra R A` is coefficientwise centrality in `A`. -/
theorem mem_center_coeffTendstoZeroSubalgebra_iff {f : coeffTendstoZeroSubalgebra R A} :
    f ∈ Subalgebra.center R (coeffTendstoZeroSubalgebra R A) ↔
      ∀ n, coeff n (f : A⟦X⟧) ∈ Subalgebra.center R A := by
  refine ⟨fun hf n ↦ Subalgebra.mem_center_iff.2 fun a ↦ ?_,
    fun hf ↦ Subalgebra.mem_center_iff.2 fun g ↦
      Subtype.ext (Subalgebra.mem_center_iff.1 (mem_center_iff.2 hf) (g : A⟦X⟧))⟩
  simpa only [Subalgebra.coe_mul, coe_coeffTendstoZeroCAlgHom, coeff_C_mul, coeff_mul_C] using
    congrArg (fun x : coeffTendstoZeroSubalgebra R A ↦ coeff n (x : A⟦X⟧))
      (Subalgebra.mem_center_iff.1 hf (coeffTendstoZeroCAlgHom R A a))

theorem coeff_zero_mem_range_algebraMap_of_mem_adjoin_X {f : coeffTendstoZeroSubalgebra R A}
    (hf : f ∈ Algebra.adjoin R ({coeffTendstoZeroX R A} : Set (coeffTendstoZeroSubalgebra R A))) :
    coeff 0 (f : A⟦X⟧) ∈ Set.range (algebraMap R A) := by
  induction hf using Algebra.adjoin_induction with
  | mem _ hx => rw [Set.mem_singleton_iff] at hx; subst hx; exact ⟨0, by simp⟩
  | algebraMap r => exact ⟨r, by simp [algebraMap_apply]⟩
  | add _ _ _ _ hx hy =>
    obtain ⟨r, hr⟩ := hx; obtain ⟨s, hs⟩ := hy; exact ⟨r + s, by simp [map_add, hr, hs]⟩
  | mul _ _ _ _ hx hy =>
    obtain ⟨r, hr⟩ := hx; obtain ⟨s, hs⟩ := hy
    exact ⟨r * s, by rw [map_mul, hr, hs, Subalgebra.coe_mul, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul]⟩

/-- **Constants and scalar polynomials in `X` intersect only in `R`.** -/
@[simp]
theorem range_coeffTendstoZeroCAlgHom_inf_adjoin_X :
    (coeffTendstoZeroCAlgHom R A).range ⊓
        Algebra.adjoin R ({coeffTendstoZeroX R A} : Set (coeffTendstoZeroSubalgebra R A)) = ⊥ := by
  rw [eq_bot_iff]; rintro f ⟨hx, hf⟩
  rcases (AlgHom.mem_range _).1 hx with ⟨a, rfl⟩
  obtain ⟨r, hr⟩ := coeff_zero_mem_range_algebraMap_of_mem_adjoin_X hf
  refine Algebra.mem_bot.2 ⟨r, Subtype.ext ?_⟩
  rw [Subalgebra.coe_algebraMap, algebraMap_apply, coe_coeffTendstoZeroCAlgHom]
  exact congrArg C (by simpa using hr)

/-- **Center reduction for restricted formal power series.** -/
theorem center_eq_bot_of_center_coeffTendstoZeroSubalgebra_le_adjoin
    (h : Subalgebra.center R (coeffTendstoZeroSubalgebra R A) ≤
      Algebra.adjoin R ({coeffTendstoZeroX R A} : Set (coeffTendstoZeroSubalgebra R A))) :
    Subalgebra.center R A = ⊥ := by
  rw [eq_bot_iff]; intro z hz
  have hzC : coeffTendstoZeroCAlgHom R A z ∈
      Subalgebra.center R (coeffTendstoZeroSubalgebra R A) :=
    mem_center_coeffTendstoZeroSubalgebra_iff.2 <| by rintro (_ | n) <;> simp [hz]
  have hbot : coeffTendstoZeroCAlgHom R A z ∈
      (⊥ : Subalgebra R (coeffTendstoZeroSubalgebra R A)) := by
    rw [← range_coeffTendstoZeroCAlgHom_inf_adjoin_X]; exact ⟨⟨z, rfl⟩, h hzC⟩
  obtain ⟨r, hr⟩ := Algebra.mem_bot.1 hbot
  exact Algebra.mem_bot.2 ⟨r, coeffTendstoZeroCAlgHom_injective (R := R) (by rwa [AlgHom.commutes])⟩

end Subalgebra

section Eval

variable {R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [Ring B] [Algebra R B] [UniformSpace B] [IsUniformAddGroup B]
  [CompleteSpace B] [T2Space B] [IsTopologicalRing B] [IsLinearTopology B B]

omit [T2Space B] in
theorem summable_apply_coeff_mul_pow_of_mem_center {φ : A →ₐ[R] B} (hφ : Continuous φ)
    {z : B} (hz : z ∈ Subalgebra.center R B) (f : coeffTendstoZeroSubalgebra R A) :
    Summable fun n ↦ φ (coeff n (f : A⟦X⟧)) * z ^ n := by
  let := IsLinearTopology.nonarchimedeanAddGroup B (M := B)
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop,
    (IsLinearTopology.hasBasis_submodule B).tendsto_right_iff]
  rintro J (hJ : (J : Set B) ∈ 𝓝 0)
  filter_upwards [((hφ.tendsto' 0 0 (map_zero φ)).comp f.2) hJ] with n hn
  rw [SetLike.mem_coe, Subalgebra.mem_center_iff.1 (pow_mem hz n) (φ (coeff n (f : A⟦X⟧)))]
  exact J.smul_mem (z ^ n) hn

/-- **Evaluation of restricted formal power series** `f ↦ ∑' n, φ (coeff n f) * z ^ n` at a
central element `z ∈ Subalgebra.center R B`. -/
noncomputable def coeffTendstoZeroEval {φ : A →ₐ[R] B} (hφ : Continuous φ)
    {z : B} (hz : z ∈ Subalgebra.center R B) : coeffTendstoZeroSubalgebra R A →ₐ[R] B where
  toFun f := ∑' n, φ (coeff n (f : A⟦X⟧)) * z ^ n
  map_zero' := by simp
  map_one' := (tsum_eq_single 0 fun n hn ↦ by
    rw [Subalgebra.coe_one, ← map_one C]; simp [hn]).trans (by simp)
  map_add' f g := by
    rw [← (summable_apply_coeff_mul_pow_of_mem_center hφ hz f).tsum_add
      (summable_apply_coeff_mul_pow_of_mem_center hφ hz g)]
    exact tsum_congr fun _ ↦ by rw [Subalgebra.coe_add, map_add, map_add, add_mul]
  map_mul' f g := by
    let := IsLinearTopology.nonarchimedeanRing B
    have hf := summable_apply_coeff_mul_pow_of_mem_center hφ hz f
    have hg := summable_apply_coeff_mul_pow_of_mem_center hφ hz g
    rw [hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg (hf.mul_of_nonarchimedean hg)]
    refine tsum_congr fun n ↦ ?_
    rw [Subalgebra.coe_mul, coeff_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl ↦ ?_
    have hcomm := Subalgebra.mem_center_iff.1 (pow_mem hz kl.1) (φ (coeff kl.2 (g : A⟦X⟧)))
    rw [map_mul, ← Finset.mem_antidiagonal.1 hkl, pow_add]
    simp only [mul_assoc]; rw [← mul_assoc (φ (coeff kl.2 _)), hcomm, mul_assoc]
  commutes' r := (tsum_eq_single 0 fun n hn ↦ by
    rw [Subalgebra.coe_algebraMap, algebraMap_apply]; simp [coeff_C, hn]).trans
    (by simp [algebraMap_apply, coeff_C])

theorem coeffTendstoZeroEval_apply {φ : A →ₐ[R] B} (hφ : Continuous φ)
    {z : B} (hz : z ∈ Subalgebra.center R B) (f : coeffTendstoZeroSubalgebra R A) :
    coeffTendstoZeroEval hφ hz f = ∑' n, φ (coeff n (f : A⟦X⟧)) * z ^ n := (rfl)

@[simp]
theorem coeffTendstoZeroEval_C {φ : A →ₐ[R] B} (hφ : Continuous φ)
    {z : B} (hz : z ∈ Subalgebra.center R B) (a : A) :
    coeffTendstoZeroEval hφ hz (coeffTendstoZeroCAlgHom R A a) = φ a :=
  (tsum_eq_single 0 fun n hn ↦ by rw [coe_coeffTendstoZeroCAlgHom]; simp [coeff_C, hn]).trans
    (by simp [coeff_C])

@[simp]
theorem coeffTendstoZeroEval_X {φ : A →ₐ[R] B} (hφ : Continuous φ)
    {z : B} (hz : z ∈ Subalgebra.center R B) :
    coeffTendstoZeroEval hφ hz (coeffTendstoZeroX R A) = z :=
  (tsum_eq_single 1 fun n hn ↦ by rw [coe_coeffTendstoZeroX]; simp [coeff_X, hn]).trans
    (by simp [coeff_X])

end Eval

end PowerSeries

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.RingTheory.Huber.WeightedEval.UniversalProperty
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
public import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries

/-!
# Small perturbations of the variables of `A⟨X⟩`

Let `A` be a complete Hausdorff nonarchimedean ring with a pair of definition `(A₀, I)`, and let
`A⟨X⟩ = A⟨X₁, …, Xₖ⟩` be the ring of restricted power series. For power-bounded
`ε₁, …, εₖ ∈ A⟨X⟩`, the universal property of `A⟨X⟩` gives a unique continuous `A`-algebra
endomorphism `θ_ε` with `θ_ε(Xᵢ) = Xᵢ + εᵢ`. This file shows that when every `εᵢ` lies in
`I⟨X⟩`, the series with all coefficients in `I`, then `θ_ε` is an automorphism of `A⟨X⟩` whose
inverse is again of the form `θ_ε'` with `ε'ᵢ ∈ I⟨X⟩`. So a change of variables that is the
identity modulo the ideal of definition is invertible: this is what lets a presentation of a
quotient of `A⟨X⟩` be transported along generators that are close to the given ones.

The proof is a Neumann series. Write `Iⁿ⟨X⟩` for the series with all coefficients in `Iⁿ`. Then
`f ↦ f - θ_ε(f)` carries `Iᵐ⟨X⟩` into `Iᵐ⁺¹⟨X⟩`
(`TauCeti.Huber.perturbX_sub_mem_weightedNhd`), so for each variable the series
`yᵢ = ∑ (1 - θ_ε)ⁿ Xᵢ` converges and `θ_ε(yᵢ) = Xᵢ`. The substitution `Xᵢ ↦ yᵢ` is then a right
inverse of `θ_ε` by the uniqueness half of the universal property, and a right inverse of the
same shape for it makes the two inverses agree.

The perturbation also preserves `S⟨X⟩` for every open subring `S` of `A` containing the
coefficients of the `εᵢ` (`TauCeti.Huber.perturbX_mem_weightedSubring`); the cases of interest
are a ring of definition `A₀` and a ring of integral elements `A⁺`.

## Main definitions

* `TauCeti.Huber.perturbX`: the continuous `A`-algebra endomorphism `Xᵢ ↦ Xᵢ + εᵢ` of `A⟨X⟩`.
* `TauCeti.Huber.perturbXEquiv`: for `εᵢ ∈ I⟨X⟩`, the same map as a continuous `A`-algebra
  automorphism.

## Main results

* `TauCeti.Huber.perturbX_eq_of_continuous`: `θ_ε` is the only continuous `A`-algebra
  endomorphism with `Xᵢ ↦ Xᵢ + εᵢ`.
* `TauCeti.Huber.perturbX_mem_weightedSubring`: `θ_ε` preserves `S⟨X⟩` for open subrings `S`.
* `TauCeti.Huber.perturbX_sub_mem_weightedNhd`: `θ_ε(f) - f ∈ Iᵐ⁺¹⟨X⟩` for `f ∈ Iᵐ⟨X⟩`.
* `TauCeti.Huber.exists_perturbX_inverse`: `θ_ε` has a two-sided inverse `θ_ε'` with
  `ε'ᵢ ∈ I⟨X⟩`.
* `TauCeti.Huber.bijective_perturbX`: `θ_ε` is bijective.
* `TauCeti.Huber.perturbXEquiv_symm_eq`: the inverse is the perturbation by
  `θ_ε⁻¹(Xᵢ) - Xᵢ`.

## References

* [R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*], proof of
  Proposition 1.7.1, point (3), where small perturbations of topological generators are shown to
  define automorphisms for noetherian rings.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.50, the universal property of `A⟨X⟩`.
-/

public section

open Filter Topology

namespace TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A]

local notation "A⟨X⟩" =>
  weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight

/-! ### The `I`-adic levels of `A⟨X⟩` -/

section Levels

variable [TopologicalSpace A] [NonarchimedeanRing A] (P : PairOfDefinition A)

/-- `Iⁿ⟨X⟩`, the series all of whose coefficients lie in `Iⁿ`. -/
local notation "𝓘" n => weightedNhd (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
  (P.idealImage n)

/-- A series with coefficients in `Iⁿ` has them in `A₀`, so lies in `A₀⟨X⟩`. -/
private theorem mem_weightedRingOfDefinition_of_mem {n : ℕ} {f : A⟨X⟩} (hf : f ∈ 𝓘 n) :
    f ∈ P.weightedRingOfDefinition isWeightFamily_one_weight :=
  (P.mem_weightedRingOfDefinition _).mpr (weightedNhd_mono (P.idealImage_le_ringOfDefinition n) hf)

/-- **Series with coefficients in `Iⁿ` are power-bounded**: they lie in the ring of definition
`A₀⟨X⟩`, which is bounded. -/
theorem isPowerBounded_of_mem_weightedNhd_idealImage {n : ℕ} {f : A⟨X⟩} (hf : f ∈ 𝓘 n) :
    IsPowerBounded f :=
  (P.weighted isWeightFamily_one_weight).isBounded_ringOfDefinition.isPowerBounded_of_mem
    (by simpa using mem_weightedRingOfDefinition_of_mem P hf)

private theorem isClosed_weightedNhd_idealImage (n : ℕ) : IsClosed ((𝓘 n) : Set A⟨X⟩) :=
  AddSubgroup.isClosed_of_isOpen _ (isOpen_weightedNhd _ (P.isOpen_idealImage n))

private theorem weightedX_mem_weightedNhd_idealImage_zero (i : Fin k) :
    weightedX _ isWeightFamily_one_weight i ∈ 𝓘 0 := by
  simpa using weightedC_mul_weightedX_pow_mem_weightedNhd (j := 1) (c := 1) (i := i)
    (U := P.idealImage 0) isWeightFamily_one_weight (by simp [weightMul_one_weight])

/-- `Iᵃ⟨X⟩ · Iᵇ⟨X⟩ ⊆ Iᵃ⁺ᵇ⟨X⟩`. -/
private theorem mul_mem_weightedNhd_idealImage_add {a b : ℕ} {f g : A⟨X⟩} (hf : f ∈ 𝓘 a)
    (hg : g ∈ 𝓘 b) : f * g ∈ 𝓘 (a + b) := by
  simpa using (P.mem_weightedIdeal _ _).mp (P.weightedIdeal_mul_le isWeightFamily_one_weight a b
    (Ideal.mul_mem_mul (r := ⟨f, mem_weightedRingOfDefinition_of_mem P hf⟩)
      (s := ⟨g, mem_weightedRingOfDefinition_of_mem P hg⟩) ((P.mem_weightedIdeal _ _).mpr hf)
      ((P.mem_weightedIdeal _ _).mpr hg)))

/-- A sequence whose `n`-th term lies in `Iⁿ⟨X⟩` tends to zero. -/
private theorem tendsto_zero_of_mem_weightedNhd_idealImage {x : ℕ → A⟨X⟩}
    (hx : ∀ n, x n ∈ 𝓘 n) : Tendsto x atTop (𝓝 0) := by
  rw [(hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).tendsto_right_iff]
  intro U _
  obtain ⟨m, -, hm⟩ := P.hasBasis_nhds_zero.mem_iff.mp (U.isOpen.mem_nhds U.zero_mem)
  filter_upwards [eventually_ge_atTop m] with n hn
  exact weightedNhd_mono (fun _ ha ↦ hm (P.idealImage_anti hn ha)) (hx n)

/-- If every `εᵢ` lies in `I⟨X⟩` then `(X + ε)ᵛ ≡ Xᵛ` modulo `I⟨X⟩`. -/
private theorem prod_pow_sub_prod_pow_mem {ε : Fin k → A⟨X⟩} (hεI : ∀ i, ε i ∈ 𝓘 1)
    (ν : Fin k →₀ ℕ) :
    ∏ i, (weightedX _ isWeightFamily_one_weight i + ε i) ^ ν i -
      ∏ i, weightedX _ isWeightFamily_one_weight i ^ ν i ∈ 𝓘 1 := by
  let x : Fin k → P.weightedRingOfDefinition isWeightFamily_one_weight := fun i ↦
    ⟨_, mem_weightedRingOfDefinition_of_mem P (weightedX_mem_weightedNhd_idealImage_zero P i)⟩
  let e : Fin k → P.weightedRingOfDefinition isWeightFamily_one_weight := fun i ↦
    ⟨ε i, mem_weightedRingOfDefinition_of_mem P (hεI i)⟩
  have he (i : Fin k) : Ideal.Quotient.mk (P.weightedIdeal isWeightFamily_one_weight 1) (e i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr ((P.mem_weightedIdeal _ _).mpr (hεI i))
  have hmem : ∏ i, (x i + e i) ^ ν i - ∏ i, x i ^ ν i ∈
      P.weightedIdeal isWeightFamily_one_weight 1 :=
    Ideal.Quotient.eq.mp (by simp [map_prod, he])
  simpa [x, e] using (P.mem_weightedIdeal _ _).mp hmem

end Levels

/-! ### The substitution `Xᵢ ↦ Xᵢ + εᵢ` -/

section Perturbation

variable [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A]
  [T0Space A]

/-- The continuous `A`-algebra endomorphism `θ_ε` of `A⟨X⟩` with `θ_ε(Xᵢ) = Xᵢ + εᵢ`, for
power-bounded `εᵢ`. It is the evaluation of Wedhorn's Proposition 5.50 at the power-bounded tuple
`X + ε`, and is the only continuous `A`-algebra map with these values
(`TauCeti.Huber.perturbX_eq_of_continuous`). -/
noncomputable def perturbX (ε : Fin k → A⟨X⟩) (hε : ∀ i, IsPowerBounded (ε i)) :
    A⟨X⟩ →ₐ[A] A⟨X⟩ where
  toRingHom := weightedEvalHom isWeightFamily_one_weight
    (continuous_weightedC isWeightFamily_one_weight).continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun i ↦
      (isPowerBounded_weightedX_one_weight i).add (hε i))
  commutes' := weightedEvalHom_weightedC _ _ _

-- Spelled out: the local notation `A⟨X⟩` is not available inside `variable`.
variable (ε : Fin k → weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
  isWeightFamily_one_weight) (hε : ∀ i, IsPowerBounded (ε i))

/-- `θ_ε(f)` is the evaluation of `f` at `X + ε`. -/
theorem perturbX_apply (f : A⟨X⟩) :
    perturbX ε hε f = weightedEval (weightedC _ isWeightFamily_one_weight)
      (fun i ↦ weightedX _ isWeightFamily_one_weight i + ε i) (f : MvPowerSeries (Fin k) A) :=
  coe_weightedEvalHom _ _ _ f

/-- `θ_ε` sends `Xᵢ` to `Xᵢ + εᵢ`. -/
@[simp]
theorem perturbX_weightedX (i : Fin k) :
    perturbX ε hε (weightedX _ isWeightFamily_one_weight i) =
      weightedX _ isWeightFamily_one_weight i + ε i :=
  weightedEvalHom_weightedX _ _ _ i

/-- `θ_ε` is continuous. -/
theorem continuous_perturbX : Continuous (perturbX ε hε) :=
  continuous_weightedEvalHom _ _ _

/-- **`θ_ε` is the only continuous `A`-algebra endomorphism with `Xᵢ ↦ Xᵢ + εᵢ`.** -/
theorem perturbX_eq_of_continuous {φ : A⟨X⟩ →ₐ[A] A⟨X⟩} (hφ : Continuous φ)
    (hX : ∀ i, φ (weightedX _ isWeightFamily_one_weight i) =
      weightedX _ isWeightFamily_one_weight i + ε i) :
    perturbX ε hε = φ :=
  AlgHom.toRingHom_injective <| weightedRestrictedSubring_ringHom_ext_of_continuous _
    (continuous_perturbX ε hε) hφ (fun a ↦ by
      simp [← algebraMap_weightedRestrictedSubring]) fun i ↦ by simp [hX]

/-- The zero perturbation is the identity. -/
@[simp]
theorem perturbX_zero : perturbX (0 : Fin k → A⟨X⟩) (fun _ ↦ isPowerBounded_zero) =
    AlgHom.id A A⟨X⟩ :=
  perturbX_eq_of_continuous _ _ continuous_id fun _ ↦ by simp

/-- The terms of `θ_ε(f)`: it is the sum of the `aᵥ (X + ε)ᵛ` over the coefficients `aᵥ` of `f`. -/
private theorem hasSum_perturbX (f : A⟨X⟩) :
    HasSum (fun ν ↦ weightedC _ isWeightFamily_one_weight (MvPowerSeries.coeff ν
        (f : MvPowerSeries (Fin k) A)) *
        ∏ i, (weightedX _ isWeightFamily_one_weight i + ε i) ^ ν i) (perturbX ε hε f) := by
  have h := hasSum_weightedEval_of_forall_isPowerBounded
    (continuous_weightedC isWeightFamily_one_weight).continuousAt
    (fun i ↦ (isPowerBounded_weightedX_one_weight i).add (hε i))
    (mem_weightedRestrictedSubring.mp f.2)
  rwa [← perturbX_apply ε hε, show weightedEvalTerm _ _ _ = _ from
    funext (weightedEvalTerm_def _ _ _)] at h

/-- **`θ_ε` preserves `S⟨X⟩`** for an open subring `S` of `A` containing the coefficients of every
`εᵢ`. With `S` a ring of definition or a ring of integral elements, this says that the
perturbation preserves `A₀⟨X⟩` and `A⁺⟨X⟩`. -/
theorem perturbX_mem_weightedSubring {S : Subring A} (hS : IsOpen (S : Set A))
    (hεS : ∀ i, ε i ∈ weightedSubring _ isWeightFamily_one_weight S) {f : A⟨X⟩}
    (hf : f ∈ weightedSubring _ isWeightFamily_one_weight S) :
    perturbX ε hε f ∈ weightedSubring _ isWeightFamily_one_weight S := by
  have hclosed : IsClosed (weightedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight S : Set A⟨X⟩) := by
    simpa using AddSubgroup.isClosed_of_isOpen
      (weightedSubring _ isWeightFamily_one_weight S).toAddSubgroup
      (by simpa using isOpen_weightedSubring isWeightFamily_one_weight hS)
  refine hclosed.mem_of_tendsto (hasSum_perturbX ε hε f) (Eventually.of_forall fun s ↦
    sum_mem fun ν _ ↦ mul_mem ?_ (prod_mem fun i _ ↦ pow_mem (add_mem ?_ (hεS i)) _))
  · refine (weightedC_mem_weightedSubring _).mpr ?_
    simpa [weightMul_one_weight] using mem_weightedNhd.mp (mem_weightedSubring.mp hf) ν
  · simpa using weightedC_mul_weightedX_mem_weightedSubring (T := fun _ : Fin k ↦ ({1} : Set A))
      (hT := isWeightFamily_one_weight) (R := S) (i := i) (Set.mem_singleton 1)

variable (P : PairOfDefinition A)

/-- `Iⁿ⟨X⟩`, the series all of whose coefficients lie in `Iⁿ`. -/
local notation "𝓘" n => weightedNhd (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
  (P.idealImage n)

/-- **`θ_ε` raises the `I`-adic level of `f - θ_ε(f)`**: if every `εᵢ` lies in `I⟨X⟩`, then
`θ_ε(f) - f ∈ Iᵐ⁺¹⟨X⟩` for every `f ∈ Iᵐ⟨X⟩`. In particular `θ_ε` is the identity modulo
`I⟨X⟩` on `A₀⟨X⟩`. -/
theorem perturbX_sub_mem_weightedNhd (hεI : ∀ i, ε i ∈ 𝓘 1) {m : ℕ} {f : A⟨X⟩}
    (hf : f ∈ 𝓘 m) : perturbX ε hε f - f ∈ 𝓘 (m + 1) := by
  have h₀ := hasSum_perturbX (0 : Fin k → A⟨X⟩) (fun _ ↦ isPowerBounded_zero) f
  simp only [Pi.zero_apply, add_zero, perturbX_zero, AlgHom.id_apply] at h₀
  refine (isClosed_weightedNhd_idealImage P (m + 1)).mem_of_tendsto
    ((hasSum_perturbX ε hε f).sub h₀) (Eventually.of_forall fun s ↦ sum_mem fun ν _ ↦ ?_)
  rw [← mul_sub]
  refine mul_mem_weightedNhd_idealImage_add P ?_ (prod_pow_sub_prod_pow_mem P hεI ν)
  refine (weightedC_mem_weightedNhd _).mpr ?_
  simpa [weightMul_one_weight] using mem_weightedNhd.mp hf ν

/-! ### Invertibility -/

/-- **`θ_ε` has a right inverse of the same shape**: for `εᵢ ∈ I⟨X⟩` there are `ε'ᵢ ∈ I⟨X⟩` with
`θ_ε ∘ θ_ε' = id`. -/
private theorem exists_perturbX_comp_eq_id (hεI : ∀ i, ε i ∈ 𝓘 1) :
    ∃ (ε' : Fin k → A⟨X⟩) (hε' : ∀ i, ε' i ∈ 𝓘 1),
      (perturbX ε hε).comp
          (perturbX ε' fun i ↦ isPowerBounded_of_mem_weightedNhd_idealImage P (hε' i)) =
        AlgHom.id A A⟨X⟩ := by
  -- `N = 1 - θ_ε` raises the `I`-adic level, so `yᵢ = ∑ Nⁿ Xᵢ` converges and `θ_ε(yᵢ) = Xᵢ`;
  -- the inverse substitution is `Xᵢ ↦ yᵢ = Xᵢ + N(yᵢ)`.
  set θ := perturbX ε hε
  let N : A⟨X⟩ →+ A⟨X⟩ := AddMonoidHom.id _ - (θ : A⟨X⟩ →+* A⟨X⟩).toAddMonoidHom
  have hN_apply (f : A⟨X⟩) : N f = f - θ f := rfl
  have hN {m : ℕ} {f : A⟨X⟩} (hf : f ∈ 𝓘 m) : N f ∈ 𝓘 (m + 1) := by
    simpa [hN_apply] using neg_mem (perturbX_sub_mem_weightedNhd ε hε P hεI hf)
  have hNc : Continuous N := continuous_id.sub (continuous_perturbX ε hε)
  have hiter (i : Fin k) (n : ℕ) : N^[n] (weightedX _ isWeightFamily_one_weight i) ∈ 𝓘 n := by
    induction n with
    | zero => exact weightedX_mem_weightedNhd_idealImage_zero P i
    | succ n ih => simpa only [Function.iterate_succ_apply'] using hN ih
  set y : Fin k → A⟨X⟩ := fun i ↦ ∑' n, N^[n] (weightedX _ isWeightFamily_one_weight i)
  have hy (i : Fin k) : y i - N (y i) = weightedX _ isWeightFamily_one_weight i :=
    AddMonoidHom.tsum_iterate_sub_apply_tsum_iterate hNc
      (tendsto_zero_of_mem_weightedNhd_idealImage P (hiter i))
  have hy₀ (i : Fin k) : y i ∈ 𝓘 0 :=
    (isClosed_weightedNhd_idealImage P 0).mem_of_tendsto
      (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (Nat.cofinite_eq_atTop ▸
        tendsto_zero_of_mem_weightedNhd_idealImage P (hiter i))).hasSum
      (Eventually.of_forall fun s ↦ sum_mem fun n _ ↦
        weightedNhd_mono (P.idealImage_anti (Nat.zero_le n)) (hiter i n))
  have hε' (i : Fin k) : N (y i) ∈ 𝓘 1 := by simpa using hN (hy₀ i)
  refine ⟨fun i ↦ N (y i), hε', ?_⟩
  -- `θ_ε ∘ θ_ε'` is continuous and fixes every `Xᵢ`, so it is the zero perturbation
  refine (perturbX_eq_of_continuous 0 (fun _ ↦ isPowerBounded_zero)
    (by rw [AlgHom.coe_comp]; exact (continuous_perturbX ε hε).comp (continuous_perturbX _ _))
    fun i ↦ ?_).symm.trans perturbX_zero
  rw [AlgHom.comp_apply, perturbX_weightedX, Pi.zero_apply, add_zero]
  have hθ : θ (y i) = weightedX _ isWeightFamily_one_weight i := by
    simpa [hN_apply] using hy i
  have hX : weightedX _ isWeightFamily_one_weight i + N (y i) = y i := by
    rw [← hy i, sub_add_cancel]
  rw [hX, hθ]

/-- **Small perturbations of the variables are invertible**: for `εᵢ ∈ I⟨X⟩` there are
`ε'ᵢ ∈ I⟨X⟩` with `θ_ε ∘ θ_ε' = id` and `θ_ε' ∘ θ_ε = id`. -/
theorem exists_perturbX_inverse (hεI : ∀ i, ε i ∈ 𝓘 1) :
    ∃ (ε' : Fin k → A⟨X⟩) (hε' : ∀ i, ε' i ∈ 𝓘 1),
      (perturbX ε hε).comp
          (perturbX ε' fun i ↦ isPowerBounded_of_mem_weightedNhd_idealImage P (hε' i)) =
        AlgHom.id A A⟨X⟩ ∧
      (perturbX ε' fun i ↦ isPowerBounded_of_mem_weightedNhd_idealImage P (hε' i)).comp
          (perturbX ε hε) = AlgHom.id A A⟨X⟩ := by
  obtain ⟨ε', hε', h₁⟩ := exists_perturbX_comp_eq_id ε hε P hεI
  obtain ⟨ε'', hε'', h₂⟩ := exists_perturbX_comp_eq_id ε'
    (fun i ↦ isPowerBounded_of_mem_weightedNhd_idealImage P (hε' i)) P hε'
  -- a right inverse of a map with a left inverse is that left inverse
  have h : perturbX ε hε =
      perturbX ε'' fun i ↦ isPowerBounded_of_mem_weightedNhd_idealImage P (hε'' i) := by
    rw [← AlgHom.comp_id (perturbX ε hε), ← h₂, ← AlgHom.comp_assoc, h₁, AlgHom.id_comp]
  exact ⟨ε', hε', h₁, h ▸ h₂⟩

/-- **Small perturbations of the variables are bijective.** -/
theorem bijective_perturbX (hεI : ∀ i, ε i ∈ 𝓘 1) : Function.Bijective (perturbX ε hε) := by
  obtain ⟨ε', hε', h₁, h₂⟩ := exists_perturbX_inverse ε hε P hεI
  exact ⟨Function.LeftInverse.injective (AlgHom.congr_fun h₂),
    Function.RightInverse.surjective (AlgHom.congr_fun h₁)⟩

/-- **The perturbation `Xᵢ ↦ Xᵢ + εᵢ` as a continuous automorphism** of `A⟨X⟩`, for `εᵢ ∈ I⟨X⟩`.
Its inverse is the perturbation by `θ_ε⁻¹(Xᵢ) - Xᵢ` (`TauCeti.Huber.perturbXEquiv_symm_eq`). -/
noncomputable def perturbXEquiv {ε : Fin k → A⟨X⟩} (hεI : ∀ i, ε i ∈ 𝓘 1) :
    A⟨X⟩ ≃A[A] A⟨X⟩ :=
  have h := exists_perturbX_inverse ε
    (fun i ↦ isPowerBounded_of_mem_weightedNhd_idealImage P (hεI i)) P hεI
  { AlgEquiv.ofAlgHom _ _ h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2 with
    continuous_toFun := continuous_perturbX _ _
    continuous_invFun := continuous_perturbX _ _ }

variable {ε} in
@[simp]
theorem coe_perturbXEquiv (hεI : ∀ i, ε i ∈ 𝓘 1) :
    ⇑(perturbXEquiv P hεI) =
      perturbX ε fun i ↦ isPowerBounded_of_mem_weightedNhd_idealImage P (hεI i) :=
  funext fun _ ↦ rfl

variable {ε} in
/-- The inverse of `perturbXEquiv` is some perturbation by elements of `I⟨X⟩`. -/
private theorem exists_perturbXEquiv_symm (hεI : ∀ i, ε i ∈ 𝓘 1) :
    ∃ (ε' : Fin k → A⟨X⟩) (hε' : ∀ i, ε' i ∈ 𝓘 1), ⇑(perturbXEquiv P hεI).symm =
      perturbX ε' fun i ↦ isPowerBounded_of_mem_weightedNhd_idealImage P (hε' i) :=
  have h := exists_perturbX_inverse ε
    (fun i ↦ isPowerBounded_of_mem_weightedNhd_idealImage P (hεI i)) P hεI
  ⟨h.choose, h.choose_spec.choose, funext fun _ ↦ rfl⟩

variable {ε} in
/-- The inverse of `θ_ε` moves each variable by an element of `I⟨X⟩`. -/
theorem perturbXEquiv_symm_weightedX_sub_mem (hεI : ∀ i, ε i ∈ 𝓘 1) (i : Fin k) :
    (perturbXEquiv P hεI).symm (weightedX _ isWeightFamily_one_weight i) -
      weightedX _ isWeightFamily_one_weight i ∈ 𝓘 1 := by
  obtain ⟨ε', hε', h⟩ := exists_perturbXEquiv_symm P hεI
  rw [h, perturbX_weightedX, add_sub_cancel_left]
  exact hε' i

variable {ε} in
/-- **The inverse of `θ_ε` is a perturbation**: it is `θ_ε'` with `ε'ᵢ = θ_ε⁻¹(Xᵢ) - Xᵢ`. -/
theorem perturbXEquiv_symm_eq (hεI : ∀ i, ε i ∈ 𝓘 1) :
    ⇑(perturbXEquiv P hεI).symm = perturbX
      (fun i ↦ (perturbXEquiv P hεI).symm (weightedX _ isWeightFamily_one_weight i) -
        weightedX _ isWeightFamily_one_weight i)
      fun i ↦ isPowerBounded_of_mem_weightedNhd_idealImage P
        (perturbXEquiv_symm_weightedX_sub_mem P hεI i) := by
  obtain ⟨ε', hε', h⟩ := exists_perturbXEquiv_symm P hεI
  have hε : (fun i ↦ (perturbXEquiv P hεI).symm (weightedX _ isWeightFamily_one_weight i) -
      weightedX _ isWeightFamily_one_weight i) = ε' := by
    funext i
    rw [h, perturbX_weightedX, add_sub_cancel_left]
  simp_rw [hε]
  exact h

end Perturbation

end TauCeti.Huber

end

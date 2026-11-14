/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.RingTheory.Huber.Pair
public import TauCeti.RingTheory.Huber.WeightedEval.Continuous
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
* `TauCeti.Huber.perturbX_sub_mem_weightedNhd`: `θ_ε(f) - f ∈ Iᵐ⁺ⁿ⟨X⟩` for `f ∈ Iᵐ⟨X⟩` when
  every `εᵢ` lies in `Iⁿ⟨X⟩`.
* `TauCeti.Huber.exists_perturbX_inverse`: `θ_ε` has a two-sided inverse `θ_ε'` with
  `ε'ᵢ ∈ I⟨X⟩`.
* `TauCeti.Huber.perturbX_bijective`: `θ_ε` is bijective.
* `TauCeti.Huber.coe_perturbXEquiv_symm`: the inverse is the perturbation by
  `θ_ε⁻¹(Xᵢ) - Xᵢ`.
* `TauCeti.Huber.perturbXEquiv_mem_weightedSubring_iff`: `θ_ε` and its inverse preserve `S⟨X⟩`
  for open subrings `S` containing `I`, in particular `A₀⟨X⟩`
  (`TauCeti.Huber.perturbXEquiv_mem_weightedRingOfDefinition_iff`) and `A⁺⟨X⟩` for every ring of
  integral elements `A⁺`
  (`TauCeti.Huber.perturbXEquiv_mem_weightedSubring_iff_of_isRingOfIntegralElements`).

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

private theorem weightedX_mem_weightedNhd_idealImage_zero (i : Fin k) :
    weightedX _ isWeightFamily_one_weight i ∈ 𝓘 0 :=
  P.mem_weightedNhd_idealImage_zero.mpr (by
    simpa using P.weightedC_mul_weightedX_mem_weightedRingOfDefinition isWeightFamily_one_weight
      (Set.mem_singleton 1) (i := i))

/-- If every `εᵢ` lies in `Iⁿ⟨X⟩` then `(X + ε)ᵛ ≡ Xᵛ` modulo `Iⁿ⟨X⟩`. -/
private theorem prod_pow_sub_prod_pow_mem {n : ℕ} {ε : Fin k → A⟨X⟩} (hεI : ∀ i, ε i ∈ 𝓘 n)
    (ν : Fin k →₀ ℕ) :
    ∏ i, (weightedX _ isWeightFamily_one_weight i + ε i) ^ ν i -
      ∏ i, weightedX _ isWeightFamily_one_weight i ^ ν i ∈ 𝓘 n := by
  let x : Fin k → P.weightedRingOfDefinition isWeightFamily_one_weight := fun i ↦
    ⟨_, P.mem_weightedRingOfDefinition_of_mem_weightedNhd_idealImage
      (weightedX_mem_weightedNhd_idealImage_zero P i)⟩
  let e : Fin k → P.weightedRingOfDefinition isWeightFamily_one_weight := fun i ↦
    ⟨ε i, P.mem_weightedRingOfDefinition_of_mem_weightedNhd_idealImage (hεI i)⟩
  have he (i : Fin k) : Ideal.Quotient.mk (P.weightedIdeal isWeightFamily_one_weight n) (e i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr ((P.mem_weightedIdeal _ _).mpr (hεI i))
  have hmem : ∏ i, (x i + e i) ^ ν i - ∏ i, x i ^ ν i ∈
      P.weightedIdeal isWeightFamily_one_weight n :=
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

/-- `θ_ε` fixes the constants. -/
@[simp]
theorem perturbX_weightedC (a : A) :
    perturbX ε hε (weightedC _ isWeightFamily_one_weight a) =
      weightedC _ isWeightFamily_one_weight a :=
  weightedEvalHom_weightedC _ _ _ a

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
theorem hasSum_perturbX (f : A⟨X⟩) :
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
  refine mem_weightedSubring.mpr <| (hasSum_perturbX ε hε f).mem
    (isClosed_weightedNhd isWeightFamily_one_weight (U := S.toAddSubgroup) hS) fun ν ↦
      mem_weightedSubring.mp <| mul_mem ?_ (prod_mem fun i _ ↦ pow_mem (add_mem ?_ (hεS i)) _)
  · refine (weightedC_mem_weightedSubring _).mpr ?_
    simpa [weightMul_one_weight] using mem_weightedNhd.mp (mem_weightedSubring.mp hf) ν
  · simpa using weightedC_mul_weightedX_mem_weightedSubring (T := fun _ : Fin k ↦ ({1} : Set A))
      (hT := isWeightFamily_one_weight) (R := S) (i := i) (Set.mem_singleton 1)

variable (P : PairOfDefinition A)

/-- `Iⁿ⟨X⟩`, the series all of whose coefficients lie in `Iⁿ`. -/
local notation "𝓘" n => weightedNhd (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
  (P.idealImage n)

/-- **`f ↦ θ_ε(f) - f` raises the `I`-adic level**: if every `εᵢ` lies in `Iⁿ⟨X⟩`, then
`θ_ε(f) - f ∈ Iᵐ⁺ⁿ⟨X⟩` for every `f ∈ Iᵐ⟨X⟩`. In particular, for `n = 1`, `θ_ε` is the identity
modulo `I⟨X⟩` on `A₀⟨X⟩`. -/
theorem perturbX_sub_mem_weightedNhd {n : ℕ} (hεI : ∀ i, ε i ∈ 𝓘 n) {m : ℕ} {f : A⟨X⟩}
    (hf : f ∈ 𝓘 m) : perturbX ε hε f - f ∈ 𝓘 (m + n) := by
  have h₀ := hasSum_perturbX (0 : Fin k → A⟨X⟩) (fun _ ↦ isPowerBounded_zero) f
  simp only [Pi.zero_apply, add_zero, perturbX_zero, AlgHom.id_apply] at h₀
  refine ((hasSum_perturbX ε hε f).sub h₀).mem
    (isClosed_weightedNhd _ (P.isOpen_idealImage (m + n))) fun ν ↦ ?_
  rw [← mul_sub]
  refine P.mul_mem_weightedNhd_idealImage_add ?_ (prod_pow_sub_prod_pow_mem P hεI ν)
  refine (weightedC_mem_weightedNhd _).mpr ?_
  simpa [weightMul_one_weight] using mem_weightedNhd.mp hf ν

/-! ### Invertibility -/

/-- **`θ_ε` has a right inverse of the same shape**: for `εᵢ ∈ I⟨X⟩` there are `ε'ᵢ ∈ I⟨X⟩` with
`θ_ε ∘ θ_ε' = id`. -/
private theorem exists_perturbX_comp_eq_id (hεI : ∀ i, ε i ∈ 𝓘 1) :
    ∃ (ε' : Fin k → A⟨X⟩) (hε' : ∀ i, ε' i ∈ 𝓘 1),
      (perturbX ε hε).comp
          (perturbX ε' fun i ↦ P.isPowerBounded_of_mem_weightedNhd_idealImage (hε' i)) =
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
    NonarchimedeanAddGroup.tsum_iterate_sub_apply_tsum_iterate hNc
      (P.tendsto_zero_of_mem_weightedNhd_idealImage (hiter i))
  have hy₀ (i : Fin k) : y i ∈ 𝓘 0 :=
    tsum_mem (isClosed_weightedNhd _ (P.isOpen_idealImage 0)) fun n ↦
      weightedNhd_mono (P.idealImage_anti (Nat.zero_le n)) (hiter i n)
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
          (perturbX ε' fun i ↦ P.isPowerBounded_of_mem_weightedNhd_idealImage (hε' i)) =
        AlgHom.id A A⟨X⟩ ∧
      (perturbX ε' fun i ↦ P.isPowerBounded_of_mem_weightedNhd_idealImage (hε' i)).comp
          (perturbX ε hε) = AlgHom.id A A⟨X⟩ := by
  obtain ⟨ε', hε', h₁⟩ := exists_perturbX_comp_eq_id ε hε P hεI
  obtain ⟨ε'', hε'', h₂⟩ := exists_perturbX_comp_eq_id ε'
    (fun i ↦ P.isPowerBounded_of_mem_weightedNhd_idealImage (hε' i)) P hε'
  -- a right inverse of a map with a left inverse is that left inverse
  have h : perturbX ε hε =
      perturbX ε'' fun i ↦ P.isPowerBounded_of_mem_weightedNhd_idealImage (hε'' i) := by
    rw [← AlgHom.comp_id (perturbX ε hε), ← h₂, ← AlgHom.comp_assoc, h₁, AlgHom.id_comp]
  exact ⟨ε', hε', h₁, h ▸ h₂⟩

/-- **Small perturbations of the variables are bijective.** -/
theorem perturbX_bijective (hεI : ∀ i, ε i ∈ 𝓘 1) : Function.Bijective (perturbX ε hε) := by
  obtain ⟨ε', hε', h₁, h₂⟩ := exists_perturbX_inverse ε hε P hεI
  exact ⟨Function.LeftInverse.injective (AlgHom.congr_fun h₂),
    Function.RightInverse.surjective (AlgHom.congr_fun h₁)⟩

variable {ε} in
/-- The shifts `ε'` of the inverse `θ_ε'` of `θ_ε`, chosen once by
`TauCeti.Huber.exists_perturbX_inverse`; `perturbXEquiv` is built from them. -/
private noncomputable def perturbXInv (hεI : ∀ i, ε i ∈ 𝓘 1) : Fin k → A⟨X⟩ :=
  (exists_perturbX_inverse ε
    (fun i ↦ P.isPowerBounded_of_mem_weightedNhd_idealImage (hεI i)) P hεI).choose

variable {ε} in
private theorem perturbXInv_mem (hεI : ∀ i, ε i ∈ 𝓘 1) (i : Fin k) :
    perturbXInv P hεI i ∈ 𝓘 1 :=
  (exists_perturbX_inverse ε
    (fun i ↦ P.isPowerBounded_of_mem_weightedNhd_idealImage (hεI i)) P hεI).choose_spec.choose i

/-- **The perturbation `Xᵢ ↦ Xᵢ + εᵢ` as a continuous automorphism** of `A⟨X⟩`, for `εᵢ ∈ I⟨X⟩`.
Its inverse is the perturbation by `θ_ε⁻¹(Xᵢ) - Xᵢ` (`TauCeti.Huber.coe_perturbXEquiv_symm`). -/
noncomputable def perturbXEquiv {ε : Fin k → A⟨X⟩} (hεI : ∀ i, ε i ∈ 𝓘 1) :
    A⟨X⟩ ≃A[A] A⟨X⟩ :=
  -- the inverse is `θ_ε'` with `ε' = perturbXInv P hεI`, which unfolds to the chosen witness
  have h := (exists_perturbX_inverse ε
    (fun i ↦ P.isPowerBounded_of_mem_weightedNhd_idealImage (hεI i)) P hεI).choose_spec.choose_spec
  { AlgEquiv.ofAlgHom (perturbX ε _)
      (perturbX (perturbXInv P hεI) fun i ↦
        P.isPowerBounded_of_mem_weightedNhd_idealImage (perturbXInv_mem P hεI i)) h.1 h.2 with
    continuous_toFun := continuous_perturbX _ _
    continuous_invFun := continuous_perturbX _ _ }

variable {ε} in
@[simp]
theorem coe_perturbXEquiv (hεI : ∀ i, ε i ∈ 𝓘 1) :
    ⇑(perturbXEquiv P hεI) =
      perturbX ε fun i ↦ P.isPowerBounded_of_mem_weightedNhd_idealImage (hεI i) :=
  funext fun _ ↦ rfl

/-- The zero perturbation is the identity automorphism. -/
@[simp]
theorem perturbXEquiv_zero (h0 : ∀ i, (0 : Fin k → A⟨X⟩) i ∈ 𝓘 1) :
    perturbXEquiv P h0 = ContinuousAlgEquiv.refl A A⟨X⟩ :=
  ContinuousAlgEquiv.ext (by simp)

variable {ε} in
private theorem coe_perturbXEquiv_symm_eq_perturbXInv (hεI : ∀ i, ε i ∈ 𝓘 1) :
    ⇑(perturbXEquiv P hεI).symm = perturbX (perturbXInv P hεI) fun i ↦
      P.isPowerBounded_of_mem_weightedNhd_idealImage (perturbXInv_mem P hεI i) :=
  rfl

variable {ε} in
/-- The inverse of `θ_ε` moves each variable by an element of `I⟨X⟩`. -/
theorem perturbXEquiv_symm_weightedX_sub_mem (hεI : ∀ i, ε i ∈ 𝓘 1) (i : Fin k) :
    (perturbXEquiv P hεI).symm (weightedX _ isWeightFamily_one_weight i) -
      weightedX _ isWeightFamily_one_weight i ∈ 𝓘 1 := by
  rw [coe_perturbXEquiv_symm_eq_perturbXInv, perturbX_weightedX, add_sub_cancel_left]
  exact perturbXInv_mem P hεI i

variable {ε} in
/-- **The inverse of `θ_ε` is a perturbation**: it is `θ_ε'` with `ε'ᵢ = θ_ε⁻¹(Xᵢ) - Xᵢ`. -/
theorem coe_perturbXEquiv_symm (hεI : ∀ i, ε i ∈ 𝓘 1) :
    ⇑(perturbXEquiv P hεI).symm = perturbX
      (fun i ↦ (perturbXEquiv P hεI).symm (weightedX _ isWeightFamily_one_weight i) -
        weightedX _ isWeightFamily_one_weight i)
      fun i ↦ P.isPowerBounded_of_mem_weightedNhd_idealImage
        (perturbXEquiv_symm_weightedX_sub_mem P hεI i) :=
  congrArg DFunLike.coe (perturbX_eq_of_continuous _ _
    (φ := (perturbXEquiv P hεI).symm.toAlgEquiv.toAlgHom) (perturbXEquiv P hεI).symm.continuous
    fun _ ↦ (add_sub_cancel _ _).symm).symm

variable {ε} in
/-- **`θ_ε` preserves `S⟨X⟩` in both directions**, for an open subring `S` of `A` containing the
image of `I`: `θ_ε(f) ∈ S⟨X⟩` if and only if `f ∈ S⟨X⟩`. -/
theorem perturbXEquiv_mem_weightedSubring_iff {S : Subring A} (hS : IsOpen (S : Set A))
    (hIS : P.idealImage 1 ≤ S.toAddSubgroup) (hεI : ∀ i, ε i ∈ 𝓘 1) {f : A⟨X⟩} :
    perturbXEquiv P hεI f ∈ weightedSubring _ isWeightFamily_one_weight S ↔
      f ∈ weightedSubring _ isWeightFamily_one_weight S := by
  have hle {g : A⟨X⟩} (hg : g ∈ 𝓘 1) : g ∈ weightedSubring _ isWeightFamily_one_weight S :=
    mem_weightedSubring.mpr (weightedNhd_mono hIS hg)
  refine ⟨fun hf ↦ ?_, fun hf ↦ perturbX_mem_weightedSubring _ _ hS (fun i ↦ hle (hεI i)) hf⟩
  rw [← (perturbXEquiv P hεI).symm_apply_apply f, coe_perturbXEquiv_symm]
  exact perturbX_mem_weightedSubring _ _ hS
    (fun i ↦ hle (perturbXEquiv_symm_weightedX_sub_mem P hεI i)) hf

variable {ε} in
/-- **`θ_ε` preserves `A₀⟨X⟩` in both directions.** -/
theorem perturbXEquiv_mem_weightedRingOfDefinition_iff (hεI : ∀ i, ε i ∈ 𝓘 1) {f : A⟨X⟩} :
    perturbXEquiv P hεI f ∈ P.weightedRingOfDefinition isWeightFamily_one_weight ↔
      f ∈ P.weightedRingOfDefinition isWeightFamily_one_weight := by
  rw [PairOfDefinition.weightedRingOfDefinition_def]
  exact perturbXEquiv_mem_weightedSubring_iff P P.isOpen_ringOfDefinition
    (P.idealImage_le_ringOfDefinition 1) hεI

variable {ε} in
/-- **`θ_ε` preserves `A⁺⟨X⟩` in both directions**, for every ring of integral elements `A⁺`: it
contains the image of `I`, whose elements are topologically nilpotent. -/
theorem perturbXEquiv_mem_weightedSubring_iff_of_isRingOfIntegralElements {Aplus : Subring A}
    (hA : IsRingOfIntegralElements Aplus) (hεI : ∀ i, ε i ∈ 𝓘 1) {f : A⟨X⟩} :
    perturbXEquiv P hεI f ∈ weightedSubring _ isWeightFamily_one_weight Aplus ↔
      f ∈ weightedSubring _ isWeightFamily_one_weight Aplus :=
  perturbXEquiv_mem_weightedSubring_iff P hA.isOpen
    (fun _ ha ↦ hA.mem_of_isTopologicallyNilpotent
      (P.isTopologicallyNilpotent_of_mem_idealImage one_ne_zero ha)) hεI

end Perturbation

end TauCeti.Huber

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.Fredholm.Snake.UpperTriangular
public import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Examples for snake sequences of Fredholm operators

Three concrete examples illustrating the Fredholm snake sequence:

1. **Finite-dimensional shear** `(x, y) ↦ (y, 0)` on `0 → ℂ → ℂ × ℂ → ℂ → 0` covering `0` and `0`:
   all six snake terms have dimension `1`, `ker M → ker 0` is zero, the connecting map is `id` on
   `ℂ`, and `ind M = 0 = 0 + 0`.
2. **Shift direct sum** `S ⊕ S†` on `0 → ℓ²(ℕ) → ℓ²(ℕ) × ℓ²(ℕ) → ℓ²(ℕ) → 0` with the unilateral
   forward shift `S` (`ind S = -1`), its adjoint `S†` (`ind S† = 1`), and `ind (S ⊕ S†) = 0`.
3. **Failure of one-out-of-three** on `0 → ℓ²(ℕ) → ℓ²(ℕ) × ℓ²(ℕ) → ℓ²(ℕ) → 0`: the operator
   `(x, y) ↦ (a x + b y, d y)` with `a(δₙ) = δ_{2n}`, `b(y) = ∑ y_{2n} δ_{2n+1}`, and
   `d(y) = (y₁, y₃, …)` is invertible (Fredholm of index `0`), whereas neither `a` nor `d` is
   Fredholm and the connecting map `ker d → ℓ²(ℕ) ⧸ range a` is a bijection between
   infinite-dimensional spaces.
-/

public section

open ContinuousLinearMap Module
open scoped InnerProduct

namespace TauCeti.FredholmSnakeExample

/-! ### 1. Finite-dimensional shear `[[0, 1], [0, 0]]` on `0 → ℂ → ℂ × ℂ → ℂ → 0` -/

section FiniteDimShear

/-- The upper-triangular shear `(x, y) ↦ (y, 0)` on `ℂ × ℂ`, covering `0` on both `ℂ` factors. -/
noncomputable def shearOp : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  upperTriangular (0 : ℂ →L[ℂ] ℂ) (ContinuousLinearMap.id ℂ ℂ) (0 : ℂ →L[ℂ] ℂ)

@[simp]
lemma shearOp_apply (x y : ℂ) : shearOp (x, y) = (y, 0) := by simp [shearOp]

/-- Canonical identification `ℂ ≃ₗ[ℂ] ker (0 : ℂ →L[ℂ] ℂ)`. -/
def zeroKerEquiv : ℂ ≃ₗ[ℂ] (0 : ℂ →L[ℂ] ℂ).ker :=
  { toFun := fun x ↦ ⟨x, rfl⟩, invFun := Subtype.val, map_add' := fun _ _ ↦ rfl,
    map_smul' := fun _ _ ↦ rfl, left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }

/-- Canonical identification `(ℂ ⧸ range (0 : ℂ →L[ℂ] ℂ)) ≃ₗ[ℂ] ℂ`. -/
noncomputable def zeroCokerEquiv : (ℂ ⧸ (0 : ℂ →L[ℂ] ℂ).range) ≃ₗ[ℂ] ℂ :=
  Submodule.quotEquivOfEqBot _ (LinearMap.range_zero (R := ℂ) (M := ℂ) (M₂ := ℂ))

lemma zeroCokerEquiv_mk (y : ℂ) : zeroCokerEquiv (Submodule.Quotient.mk y) = y := (rfl)

/-- Identification `ℂ ≃ₗ[ℂ] ker shearOp` via `x ↦ (x, 0)`. -/
noncomputable def shearKerEquiv : ℂ ≃ₗ[ℂ] shearOp.ker where
  toFun x := ⟨(x, 0), by simp⟩
  invFun z := z.1.1
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext (by simp)
  left_inv _ := rfl
  right_inv := fun ⟨⟨_, _⟩, hz⟩ ↦ by
    rw [LinearMap.mem_ker, coe_coe, shearOp_apply, Prod.mk_eq_zero] at hz
    exact Subtype.ext (Prod.ext rfl hz.1.symm)

/-- Identification `((ℂ × ℂ) ⧸ range shearOp) ≃ₗ[ℂ] ℂ` via `[(u, v)] ↦ v`. -/
noncomputable def shearCokerEquiv : ((ℂ × ℂ) ⧸ shearOp.range) ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofLinearMap
    (shearOp.range.liftQ (LinearMap.snd ℂ ℂ ℂ) fun _ ⟨⟨_, _⟩, h⟩ ↦ by
      rw [LinearMap.mem_ker, ← h]; simp)
    (shearOp.range.mkQ.comp (LinearMap.inr ℂ ℂ ℂ)) (by ext; rfl)
    (by
      apply Submodule.linearMap_qext; apply LinearMap.ext; rintro ⟨u, _⟩
      exact (Submodule.Quotient.eq _).mpr ⟨(0, -u), by simp⟩)

/-- All six terms of the snake sequence for `shearOp` have complex dimension `1`. -/
theorem finrank_shear_snake_terms :
    finrank ℂ (0 : ℂ →L[ℂ] ℂ).ker = 1 ∧ finrank ℂ shearOp.ker = 1 ∧
      finrank ℂ (0 : ℂ →L[ℂ] ℂ).ker = 1 ∧ finrank ℂ (ℂ ⧸ (0 : ℂ →L[ℂ] ℂ).range) = 1 ∧
      finrank ℂ ((ℂ × ℂ) ⧸ shearOp.range) = 1 ∧ finrank ℂ (ℂ ⧸ (0 : ℂ →L[ℂ] ℂ).range) = 1 := by
  have hker0 : finrank ℂ (0 : ℂ →L[ℂ] ℂ).ker = 1 := by rw [← zeroKerEquiv.finrank_eq, finrank_self]
  have hcok0 : finrank ℂ (ℂ ⧸ (0 : ℂ →L[ℂ] ℂ).range) = 1 := by
    rw [zeroCokerEquiv.finrank_eq, finrank_self]
  exact ⟨hker0, by rw [← shearKerEquiv.finrank_eq, finrank_self], hker0, hcok0,
    by rw [shearCokerEquiv.finrank_eq, finrank_self], hcok0⟩

/-- Under `zeroKerEquiv` and `zeroCokerEquiv`, the snake connecting map of `shearOp` is `id`. -/
theorem shear_connecting_eq_id (y : ℂ) :
    zeroCokerEquiv (snakeConnectingL (0 : ℂ →L[ℂ] ℂ) shearOp (0 : ℂ →L[ℂ] ℂ)
      (inr ℂ ℂ ℂ) (fst ℂ ℂ ℂ) (zeroKerEquiv y)) = y := by
  rw [shearOp, snakeConnectingL_upperTriangular]; rfl

/-- The kernel map `ker shearOp →L[ℂ] ker 0` induced by `snd` is zero. -/
theorem shear_kerMap_eq_zero :
    snakeKerMapL (snd ℂ ℂ ℂ)
      (snd_comp_upperTriangular (0 : ℂ →L[ℂ] ℂ) (ContinuousLinearMap.id ℂ ℂ) (0 : ℂ →L[ℂ] ℂ)) =
      0 := by
  apply ContinuousLinearMap.ext; rintro ⟨⟨x, y⟩, hz⟩
  rw [LinearMap.mem_ker, coe_coe] at hz; change shearOp (x, y) = 0 at hz
  rw [shearOp_apply, Prod.mk_eq_zero] at hz
  apply Subtype.ext; rw [coe_snakeKerMapL_apply, zero_apply, ZeroMemClass.coe_zero]; exact hz.1

/-- `shearOp` is Fredholm and its index satisfies `0 = 0 + 0` via the snake index theorem. -/
theorem shear_isFredholm_and_index :
    shearOp.IsFredholm ∧ shearOp.index = (0 : ℂ →L[ℂ] ℂ).index + (0 : ℂ →L[ℂ] ℂ).index ∧
      shearOp.index = 0 := by
  have h0 : (0 : ℂ →L[ℂ] ℂ).IsFredholm := isFredholm_of_finiteDimensional 0
  have hadd : shearOp.index = (0 : ℂ →L[ℂ] ℂ).index + (0 : ℂ →L[ℂ] ℂ).index :=
    index_upperTriangular_of_diag _ h0 h0
  have hzero : (0 : ℂ →L[ℂ] ℂ).index = 0 := by
    rw [index_eq_finrank_sub, finrank_shear_snake_terms.1, finrank_shear_snake_terms.2.2.2.1,
      sub_self]
  exact ⟨isFredholm_upperTriangular_of_diag _ h0 h0, hadd, by rw [hadd, hzero, add_zero]⟩

end FiniteDimShear

/-! ### Common `ℓ²(ℕ)` sequence-space reindexing helper -/

section L2Reindex

/-- Complex square-summable sequences `ℓ²(ℕ, ℂ)`. -/
abbrev L2Nat : Type := lp (fun _ : ℕ ↦ ℂ) 2

/-- Continuous linear reindexing operator on `ℓ²(ℕ, ℂ)` reading along `g` on `s` and vanishing
outside `s`. -/
noncomputable def reindexL2 (g : ℕ → ℕ) (s : Set ℕ) (hg : s.InjOn g) : L2Nat →L[ℂ] L2Nat :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ⟨s.indicator (x ∘ g), (lp.memℓp x).indicator_comp hg⟩
      map_add' := fun x y ↦ lp.ext <| funext fun n ↦ by
        simp only [lp.coeFn_add, Pi.add_apply]; by_cases h : n ∈ s <;> simp [h]
      map_smul' := fun c x ↦ lp.ext <| funext fun n ↦ by
        simp only [lp.coeFn_smul, Pi.smul_apply]; by_cases h : n ∈ s <;> simp [h] }
    1 fun x ↦ by
      rw [one_mul]; exact lp.norm_le_of_forall_eq_indicator_comp (by norm_num) hg fun _ ↦ rfl

@[simp]
lemma reindexL2_apply (g : ℕ → ℕ) (s : Set ℕ) (hg : s.InjOn g) (x : L2Nat) (n : ℕ) :
    reindexL2 g s hg x n = s.indicator (x ∘ g) n := (rfl)

private lemma sum_smul_lp_single_apply {f : ℕ → ℕ} (hf : Function.Injective f)
    {s : Finset ℕ} (c : ℕ → ℂ) {k : ℕ} (hk : k ∈ s) :
    ∑ i ∈ s, (c i • lp.single (E := fun _ : ℕ ↦ ℂ) 2 (f i) (1 : ℂ)) (f k) = c k := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik; simp [lp.single_apply, show f k ≠ f i from fun h ↦ hik (hf h).symm]
  · exact fun hk' ↦ absurd hk hk'

end L2Reindex

/-! ### 2. Unilateral shift direct sum `S ⊕ S†` on `0 → ℓ² → ℓ² × ℓ² → ℓ² → 0` -/

section ShiftDirectSum

/-- The forward unilateral shift `(S x) 0 = 0`, `(S x) (n + 1) = x n` on `ℓ²(ℕ, ℂ)`. -/
noncomputable def forwardShift : L2Nat →L[ℂ] L2Nat :=
  reindexL2 (fun n ↦ n - 1) {n | 1 ≤ n} fun _ ha _ hb h ↦ by
    simp only [Set.mem_ofPred_eq] at ha hb; dsimp only at h; omega

/-- The backward unilateral shift `(S† x) n = x (n + 1)` on `ℓ²(ℕ, ℂ)`. -/
noncomputable def backwardShift : L2Nat →L[ℂ] L2Nat :=
  reindexL2 (fun n ↦ n + 1) Set.univ fun _ _ _ _ h ↦ Nat.succ.inj h

@[simp]
lemma forwardShift_apply_zero (x : L2Nat) : forwardShift x 0 = 0 :=
  (reindexL2_apply _ _ _ x 0).trans (by simp)

@[simp]
lemma forwardShift_apply_succ (x : L2Nat) (n : ℕ) : forwardShift x (n + 1) = x n :=
  (reindexL2_apply _ _ _ x (n + 1)).trans (by simp)

@[simp]
lemma backwardShift_apply (x : L2Nat) (n : ℕ) : backwardShift x n = x (n + 1) :=
  (reindexL2_apply _ _ _ x n).trans (by simp)

/-- The Hilbert-space adjoint of `forwardShift` is `backwardShift`. -/
theorem forwardShift_adjoint : forwardShift.adjoint = backwardShift := by
  symm; rw [eq_adjoint_iff]; intro x y
  rw [lp.inner_eq_tsum (𝕜 := ℂ), lp.inner_eq_tsum (𝕜 := ℂ),
    (lp.summable_inner (𝕜 := ℂ) x (forwardShift y)).tsum_eq_zero_add]
  simp only [forwardShift_apply_zero, inner_zero_right, zero_add, forwardShift_apply_succ,
    backwardShift_apply]

/-- `forwardShift` is injective. -/
theorem injective_forwardShift : Function.Injective forwardShift := fun _ _ h ↦ by
  ext n; simpa using congrFun (congrArg Subtype.val h) (n + 1)

/-- The cokernel of `forwardShift` is one-dimensional, identified with `ℂ` via `[y] ↦ y 0`. -/
noncomputable def forwardShiftCokerEquiv : (L2Nat ⧸ forwardShift.range) ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofLinearMap
    (forwardShift.range.liftQ
      { toFun := fun y ↦ y 0, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
      fun _ ⟨x, hx⟩ ↦ by rw [LinearMap.mem_ker, ← hx]; exact forwardShift_apply_zero x)
    { toFun := fun c ↦ Submodule.Quotient.mk (lp.single 2 0 c)
      map_add' := fun _ _ ↦ by rw [← Submodule.Quotient.mk_add, lp.single_add]
      map_smul' := fun _ _ ↦ by rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul,
        lp.single_smul] }
    (by ext; exact show (lp.single (E := fun _ : ℕ ↦ ℂ) 2 0 (1 : ℂ)) 0 = 1 by simp)
    (by
      apply Submodule.linearMap_qext; apply LinearMap.ext; intro y
      refine (Submodule.Quotient.eq _).mpr ⟨-backwardShift y, ?_⟩
      ext n; cases n with
      | zero => exact show forwardShift (-backwardShift y) 0 =
          (lp.single 2 0 (y 0) - y : L2Nat) 0 by simp
      | succ n => simp)

/-- The forward unilateral shift is Fredholm with index `-1`. -/
theorem forwardShift_isFredholm_and_index :
    forwardShift.IsFredholm ∧ forwardShift.index = -1 := by
  have hker : forwardShift.ker = ⊥ := LinearMap.ker_eq_bot.mpr injective_forwardShift
  have hfinKer : FiniteDimensional ℂ forwardShift.ker := by rw [hker]; infer_instance
  refine ⟨IsFredholm.of_finite_ker_coker forwardShift hfinKer
    forwardShiftCokerEquiv.symm.finiteDimensional, ?_⟩
  rw [index_eq_finrank_sub, hker, finrank_bot, forwardShiftCokerEquiv.finrank_eq, finrank_self]
  norm_num

/-- On `0 → ℓ² → ℓ² × ℓ² → ℓ² → 0`, `S ⊕ S†` is Fredholm with index
`ind S + ind S† = -1 + 1 = 0`. -/
theorem shift_prod_adjoint_isFredholm_and_index :
    (forwardShift.prodMap forwardShift.adjoint).IsFredholm ∧
      (forwardShift.prodMap forwardShift.adjoint).index =
        forwardShift.index + forwardShift.adjoint.index ∧
      (forwardShift.prodMap forwardShift.adjoint).index = 0 := by
  have hS := forwardShift_isFredholm_and_index.1
  have hmid : forwardShift.prodMap forwardShift.adjoint =
      upperTriangular forwardShift 0 forwardShift.adjoint :=
    (upperTriangular_zero forwardShift forwardShift.adjoint).symm
  have hadd : (forwardShift.prodMap forwardShift.adjoint).index =
      forwardShift.index + forwardShift.adjoint.index := by
    rw [hmid]; exact index_upperTriangular_of_diag 0 hS hS.adjoint
  refine ⟨by rw [hmid]; exact isFredholm_upperTriangular_of_diag 0 hS hS.adjoint, hadd, ?_⟩
  rw [hadd, index_adjoint forwardShift hS, forwardShift_isFredholm_and_index.2]; norm_num

end ShiftDirectSum

/-! ### 3. Counterexample: invertible middle operator with non-Fredholm outer operators -/

section NonFredholmOuterCounterexample

/-- Even-coordinate embedding `a(δₙ) = δ_{2n}` on `ℓ²(ℕ, ℂ)`. -/
noncomputable def evenShift : L2Nat →L[ℂ] L2Nat :=
  reindexL2 (fun n ↦ n / 2) {n | Even n} fun _ ⟨_, ha⟩ _ ⟨_, hb⟩ h ↦ by
    subst ha hb; dsimp only at h; omega

/-- Odd-coordinate projection `(d y) n = y (2n + 1)` on `ℓ²(ℕ, ℂ)`. -/
noncomputable def oddProj : L2Nat →L[ℂ] L2Nat :=
  reindexL2 (fun n ↦ 2 * n + 1) Set.univ fun _ _ _ _ h ↦ by dsimp only at h; omega

/-- Off-diagonal coupling `b(y) = ∑ y_{2n} δ_{2n+1}` on `ℓ²(ℕ, ℂ)`. -/
noncomputable def evenToOdd : L2Nat →L[ℂ] L2Nat :=
  reindexL2 (fun n ↦ n - 1) {n | Odd n} fun _ ⟨_, ha⟩ _ ⟨_, hb⟩ h ↦ by
    subst ha hb; dsimp only at h; omega

/-- The upper-triangular operator `(x, y) ↦ (a x + b y, d y)` on `ℓ²(ℕ, ℂ) × ℓ²(ℕ, ℂ)`. -/
noncomputable def counterexampleMid : (L2Nat × L2Nat) →L[ℂ] (L2Nat × L2Nat) :=
  upperTriangular evenShift evenToOdd oddProj

@[simp]
lemma evenShift_apply_even (x : L2Nat) (k : ℕ) : evenShift x (2 * k) = x k :=
  (reindexL2_apply _ _ _ x (2 * k)).trans (by simp)

@[simp]
lemma evenShift_apply_odd (x : L2Nat) (k : ℕ) : evenShift x (2 * k + 1) = 0 :=
  (reindexL2_apply _ _ _ x (2 * k + 1)).trans (by simp)

@[simp]
lemma oddProj_apply (y : L2Nat) (k : ℕ) : oddProj y k = y (2 * k + 1) :=
  (reindexL2_apply _ _ _ y k).trans (by simp)

@[simp]
lemma evenToOdd_apply_even (y : L2Nat) (k : ℕ) : evenToOdd y (2 * k) = 0 :=
  (reindexL2_apply _ _ _ y (2 * k)).trans (by simp)

@[simp]
lemma evenToOdd_apply_odd (y : L2Nat) (k : ℕ) : evenToOdd y (2 * k + 1) = y (2 * k) :=
  (reindexL2_apply _ _ _ y (2 * k + 1)).trans <| by
    simp [Set.indicator_of_mem (show 2 * k + 1 ∈ ({n : ℕ | Odd n} : Set ℕ) from ⟨k, rfl⟩)]

/-- `counterexampleMid` is a continuous linear automorphism of `ℓ²(ℕ, ℂ) × ℓ²(ℕ, ℂ)`. -/
noncomputable def counterexampleMidEquiv : (L2Nat × L2Nat) ≃L[ℂ] (L2Nat × L2Nat) :=
  let evenProj : L2Nat →L[ℂ] L2Nat :=
    reindexL2 (fun n ↦ 2 * n) Set.univ fun _ _ _ _ h ↦ by dsimp only at h; omega
  let oddToEven : L2Nat →L[ℂ] L2Nat :=
    reindexL2 (fun n ↦ n + 1) {n | Even n} fun _ _ _ _ h ↦ by dsimp only at h; omega
  let oddShift : L2Nat →L[ℂ] L2Nat :=
    reindexL2 (fun n ↦ n / 2) {n | Odd n} fun _ ⟨_, ha⟩ _ ⟨_, hb⟩ h ↦ by
      subst ha hb; dsimp only at h; omega
  have heP : ∀ (u : L2Nat) (k : ℕ), evenProj u k = u (2 * k) :=
    fun u k ↦ (reindexL2_apply _ _ _ u k).trans (by simp)
  have hoEe : ∀ (u : L2Nat) (k : ℕ), oddToEven u (2 * k) = u (2 * k + 1) :=
    fun u k ↦ (reindexL2_apply _ _ _ u (2 * k)).trans (by simp)
  have hoEo : ∀ (u : L2Nat) (k : ℕ), oddToEven u (2 * k + 1) = 0 :=
    fun u k ↦ (reindexL2_apply _ _ _ u (2 * k + 1)).trans (by simp)
  have hoSe : ∀ (v : L2Nat) (k : ℕ), oddShift v (2 * k) = 0 :=
    fun v k ↦ (reindexL2_apply _ _ _ v (2 * k)).trans (by simp)
  have hoSo : ∀ (v : L2Nat) (k : ℕ), oddShift v (2 * k + 1) = v k := fun v k ↦
    (reindexL2_apply _ _ _ v (2 * k + 1)).trans <| by
      have hdiv : (2 * k + 1) / 2 = k := by omega
      simp [Set.indicator_of_mem (show 2 * k + 1 ∈ ({n : ℕ | Odd n} : Set ℕ) from ⟨k, rfl⟩), hdiv]
  ContinuousLinearEquiv.equivOfInverse counterexampleMid
    ((evenProj.comp (fst ℂ L2Nat L2Nat)).prod
      (oddToEven.comp (fst ℂ L2Nat L2Nat) + oddShift.comp (snd ℂ L2Nat L2Nat)))
    (fun ⟨_, _⟩ ↦ by
      ext n
      · simp [counterexampleMid, heP]
      · rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · rw [← two_mul]; simp [counterexampleMid, hoEe, hoSe]
        · simp [counterexampleMid, hoEo, hoSo])
    (fun ⟨_, _⟩ ↦ by
      ext n
      · rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · rw [← two_mul]; simp [counterexampleMid, heP]
        · simp [counterexampleMid, hoEe, hoSe]
      · simp [counterexampleMid, hoEo, hoSo])

/-- The middle operator `counterexampleMid` is Fredholm of index `0`. -/
theorem counterexampleMid_isFredholm_and_index :
    counterexampleMid.IsFredholm ∧ counterexampleMid.index = 0 := by
  have heq : (counterexampleMidEquiv : (L2Nat × L2Nat) →L[ℂ] (L2Nat × L2Nat)) =
      counterexampleMid := rfl
  refine ⟨by rw [← heq]; simpa using
      (IsFredholm.id (𝕜 := ℂ) (E := L2Nat × L2Nat)).equiv_comp counterexampleMidEquiv, ?_⟩
  rw [← heq, index_def]; exact counterexampleMidEquiv.toLinearEquiv.index_eq_zero

/-- The cokernel of `evenShift` is infinite-dimensional, so `evenShift` is not Fredholm. -/
theorem evenShift_not_isFredholm :
    ¬ FiniteDimensional ℂ (L2Nat ⧸ evenShift.range) ∧ ¬ evenShift.IsFredholm := by
  have hli : LinearIndependent ℂ (fun n : ℕ ↦
      (Submodule.Quotient.mk (lp.single 2 (2 * n + 1) (1 : ℂ)) : L2Nat ⧸ evenShift.range)) := by
    rw [linearIndependent_iff']; intro s c hc k hk
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp
      (show evenShift.range.mkQ
        (∑ i ∈ s, c i • lp.single (E := fun _ : ℕ ↦ ℂ) 2 (2 * i + 1) (1 : ℂ)) = 0 by
        simpa [map_sum, map_smul] using hc)
    rw [coe_coe] at hx
    have hev := congrFun (congrArg Subtype.val hx) (2 * k + 1)
    rw [evenShift_apply_odd, lp.coeFn_sum, Finset.sum_apply,
      sum_smul_lp_single_apply (f := fun n ↦ 2 * n + 1)
        (fun _ _ h ↦ by dsimp only at h; omega) c hk] at hev
    exact hev.symm
  have hnotfin : ¬ FiniteDimensional ℂ (L2Nat ⧸ evenShift.range) := fun _ ↦
    have := hli.finite; not_finite ℕ
  exact ⟨hnotfin, fun hF ↦ hnotfin hF.finite_coker⟩

/-- The kernel of `oddProj` is infinite-dimensional, so `oddProj` is not Fredholm. -/
theorem oddProj_not_isFredholm :
    ¬ FiniteDimensional ℂ oddProj.ker ∧ ¬ oddProj.IsFredholm := by
  have hmem : ∀ n : ℕ, lp.single (E := fun _ : ℕ ↦ ℂ) 2 (2 * n) (1 : ℂ) ∈ oddProj.ker :=
    fun n ↦ by
      rw [LinearMap.mem_ker]; ext k
      simp [oddProj_apply, lp.single_apply, show 2 * k + 1 ≠ 2 * n by omega]
  have hli : LinearIndependent ℂ (fun n : ℕ ↦
      (⟨lp.single (E := fun _ : ℕ ↦ ℂ) 2 (2 * n) (1 : ℂ), hmem n⟩ : oddProj.ker)) := by
    rw [linearIndependent_iff']; intro s c hc k hk
    have hev := congrFun (congrArg Subtype.val (congrArg Subtype.val hc)) (2 * k)
    simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero, lp.coeFn_sum,
      Finset.sum_apply] at hev
    rwa [sum_smul_lp_single_apply (f := fun n ↦ 2 * n)
      (fun _ _ h ↦ by dsimp only at h; omega) c hk] at hev
  have hnotfin : ¬ FiniteDimensional ℂ oddProj.ker := fun _ ↦ have := hli.finite; not_finite ℕ
  exact ⟨hnotfin, fun hF ↦ hnotfin hF.finite_ker⟩

/-- In the counterexample's snake sequence, `ker oddProj →L[ℂ] ℓ² ⧸ range evenShift` is a
bijection between infinite-dimensional spaces. -/
theorem counterexample_connecting_bijective :
    Function.Bijective
      (snakeConnectingL evenShift counterexampleMid oddProj
        (inr ℂ L2Nat L2Nat) (fst ℂ L2Nat L2Nat)) := by
  have hex : Function.Exact (inl ℂ L2Nat L2Nat) (snd ℂ L2Nat L2Nat) :=
    fun ⟨x, _⟩ ↦ ⟨fun hy ↦ ⟨x, Prod.ext rfl hy.symm⟩, fun ⟨_, ha⟩ ↦ (congrArg Prod.snd ha).symm⟩
  exact bijective_snakeConnectingL (i := inl ℂ L2Nat L2Nat) (p := snd ℂ L2Nat L2Nat)
    (j := inl ℂ L2Nat L2Nat) (q := snd ℂ L2Nat L2Nat) hex (fun _ _ h ↦ congrArg Prod.fst h) hex
    (inl_comp_eq_upperTriangular_comp_inl evenShift evenToOdd oddProj)
    (snd_comp_upperTriangular evenShift evenToOdd oddProj)
    (fun _ ↦ rfl) (fun _ ↦ rfl) counterexampleMidEquiv.bijective

end NonFredholmOuterCounterexample

end TauCeti.FredholmSnakeExample

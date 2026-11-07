/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.FullFockSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily
import TauCeti.Analysis.InnerProductSpace.RangeProjection

/-!
# Creation and annihilation operators on full Fock space

On the full Fock space `FullFockSpace 𝕜 H` (`𝓕(H) = 𝕜 Ω ⊕ ⊕_{n ≥ 1} H^{\widehat{⊗} n}`, defined
in `TauCeti.Analysis.InnerProductSpace.FullFockSpace.Defs`), we construct the vacuum state
infrastructure and the left creation and annihilation operators:

* **Left creation** `FullFockSpace.creation 𝕜 h` (`ℓ(h)`), sending `Ω ↦ h` and
  `x₁ ⊗ ⋯ ⊗ xₙ ↦ h ⊗ x₁ ⊗ ⋯ ⊗ xₙ`. Each `creation 𝕜 h` is `‖h‖` times an isometry on the entire
  Fock space (`‖creation 𝕜 h x‖ = ‖h‖ * ‖x‖`), so `creationₗᵢ 𝕜 H` embeds `H` linearly and
  isometrically into `FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H`.
* **Left annihilation** `FullFockSpace.annihilation 𝕜 h` (`ℓ(h)*`), defined as the Hilbert-space
  adjoint of `creation 𝕜 h`. It annihilates the vacuum (`annihilation 𝕜 h vacuum = 0`) and
  satisfies the Cuntz–Toeplitz relation `annihilation 𝕜 h ∘L creation 𝕜 k = ⟪h, k⟫_𝕜 • id`.

Finite pure tensor words `FullFockSpace.wordVector 𝕜 [h₁, …, hₙ] = h₁ ⊗ ⋯ ⊗ hₙ` span a dense
subspace of `FullFockSpace 𝕜 H`. The self-adjoint field operators
`creation 𝕜 h + annihilation 𝕜 h` (`ℓ(h) + ℓ(h)*`) have exact operator norm `2 * ‖h‖`. Finally,
for an orthonormal `HilbertBasis` `b` of `H`, the creation operators `creation 𝕜 (b i)` are
isometries whose orthogonal range projections `creation 𝕜 (b i) ∘L annihilation 𝕜 (b i)` are
pairwise orthogonal and sum in the strong operator topology to `1 - vacuumProj`.

Gauge (differential second quantization) operators `Λ(T)` on `FullFockSpace 𝕜 H` are developed in
`TauCeti.Analysis.InnerProductSpace.FullFockSpace.Gauge`.

## Main definitions

* `TauCeti.FullFockSpace.vacuum`, `TauCeti.FullFockSpace.vacuumProj`: the unit vacuum vector `Ω`
  and the orthogonal projection onto `𝕜 ∙ Ω`.
* `TauCeti.FullFockSpace.creation`, `TauCeti.FullFockSpace.creationₗᵢ`: left creation operators and
  their bundled linear isometric embedding.
* `TauCeti.FullFockSpace.annihilation`, `TauCeti.FullFockSpace.annihilationₗᵢ`: left annihilation
  operators and their bundled conjugate-linear isometric embedding.
* `TauCeti.FullFockSpace.wordVector`: pure tensor words `h₁ ⊗ ⋯ ⊗ hₙ` indexed by `List H`.

## Main results

* `TauCeti.FullFockSpace.norm_creation`, `TauCeti.FullFockSpace.norm_annihilation`: exact operator
  norms `‖ℓ(h)‖ = ‖h‖` and `‖ℓ(h)*‖ = ‖h‖`.
* `TauCeti.FullFockSpace.annihilation_comp_creation`: the Cuntz–Toeplitz identity
  `ℓ(h)* ∘L ℓ(k) = ⟪h, k⟫ • id`.
* `TauCeti.FullFockSpace.topologicalClosure_span_range_wordVector`: finite tensor words span a
  dense subspace of `FullFockSpace 𝕜 H`.
* `TauCeti.FullFockSpace.norm_creation_add_annihilation`: `‖ℓ(h) + ℓ(h)*‖ = 2 * ‖h‖`.
* `TauCeti.FullFockSpace.creation_comp_annihilation_eq_starProjection`: for a unit vector `h`,
  `ℓ(h) ∘L ℓ(h)*` is the orthogonal projection onto `(creation 𝕜 h).range`.
* `HilbertBasis.hasSum_creation_comp_annihilation`: for a `HilbertBasis` `b`,
  `∑' i, ℓ(b i) ℓ(b i)* x = (1 - P_Ω) x` in norm for every `x : FullFockSpace 𝕜 H`.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Series, Vol. 1,
  American Mathematical Society, 1992, §2.6.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Mathematical
  Society Lecture Note Series, Vol. 335, Cambridge University Press, 2006, Lecture 7.
* K. R. Parthasarathy, *An Introduction to Quantum Stochastic Calculus*, Birkhäuser, 1992, §II.19.
-/

public section

noncomputable section

open UniformSpace Filter
open scoped InnerProductSpace TensorProduct Topology ENNReal NNReal

namespace TauCeti

universe u v

namespace FullFockSpace

section Vacuum

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ### The vacuum vector and vacuum projection -/

/-- The unit *vacuum vector* `Ω ∈ 𝓕(H)`, supported in tensor grade `0` with scalar value `1`. -/
def vacuum : FullFockSpace 𝕜 H :=
  lp.single 2 0 ((CompletedTensorPower.zeroEquiv 𝕜 H).symm 1)

@[simp]
theorem vacuum_apply_zero :
    (vacuum : FullFockSpace 𝕜 H) 0 = (CompletedTensorPower.zeroEquiv 𝕜 H).symm 1 :=
  lp.single_apply_self 2 0 _

@[simp]
theorem vacuum_apply_succ (n : ℕ) : (vacuum : FullFockSpace 𝕜 H) (n + 1) = 0 :=
  lp.single_apply_ne 2 0 _ (Nat.succ_ne_zero n)

@[simp]
theorem norm_vacuum : ‖(vacuum : FullFockSpace 𝕜 H)‖ = 1 := by
  rw [vacuum, lp.norm_single (by norm_num), LinearIsometryEquiv.norm_map, norm_one]

theorem inner_vacuum_self : ⟪(vacuum : FullFockSpace 𝕜 H), vacuum⟫_𝕜 = 1 := by
  simp

theorem vacuum_ne_zero : (vacuum : FullFockSpace 𝕜 H) ≠ 0 := by
  intro h
  have h0 := norm_vacuum (𝕜 := 𝕜) (H := H)
  simp [h] at h0

instance instNontrivial : Nontrivial (FullFockSpace 𝕜 H) :=
  ⟨⟨vacuum, 0, vacuum_ne_zero⟩⟩

theorem inner_vacuum_left (x : FullFockSpace 𝕜 H) :
    ⟪(vacuum : FullFockSpace 𝕜 H), x⟫_𝕜 = CompletedTensorPower.zeroEquiv 𝕜 H (x 0) := by
  rw [vacuum, lp.inner_single_left, ← (CompletedTensorPower.zeroEquiv 𝕜 H).inner_map_map]
  simp

/-- The orthogonal projection $P_\Omega(x) = \langle \Omega, x \rangle \Omega$ onto the vacuum
line `𝕜 ∙ vacuum`. -/
def vacuumProj : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H :=
  InnerProductSpace.rankOne 𝕜 (vacuum : FullFockSpace 𝕜 H) (vacuum : FullFockSpace 𝕜 H)

theorem vacuumProj_apply (x : FullFockSpace 𝕜 H) :
    vacuumProj x = ⟪vacuum, x⟫_𝕜 • vacuum :=
  (rfl)

@[simp]
theorem vacuumProj_vacuum : vacuumProj (vacuum : FullFockSpace 𝕜 H) = vacuum := by
  simp [vacuumProj_apply]

@[simp]
theorem vacuumProj_apply_zero (x : FullFockSpace 𝕜 H) :
    (vacuumProj x) 0 = x 0 := by
  rw [vacuumProj_apply, lp.coeFn_smul, Pi.smul_apply, vacuum_apply_zero, inner_vacuum_left,
    ← map_smul, smul_eq_mul, mul_one, LinearIsometryEquiv.symm_apply_apply]

@[simp]
theorem vacuumProj_apply_succ (x : FullFockSpace 𝕜 H) (n : ℕ) :
    (vacuumProj x) (n + 1) = 0 := by
  simp [vacuumProj_apply]

theorem isStarProjection_vacuumProj :
    IsStarProjection (vacuumProj : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) :=
  InnerProductSpace.isStarProjection_rankOne_self norm_vacuum

@[simp]
theorem vacuumProj_comp_vacuumProj :
    (vacuumProj : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) ∘L vacuumProj = vacuumProj :=
  isStarProjection_vacuumProj.isIdempotentElem

@[simp]
theorem adjoint_vacuumProj :
    (vacuumProj : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H).adjoint = vacuumProj :=
  InnerProductSpace.adjoint_rankOne vacuum vacuum

@[simp]
theorem star_vacuumProj :
    star (vacuumProj : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) = vacuumProj :=
  adjoint_vacuumProj

/-- `vacuumProj` agrees with the submodule orthogonal projection onto `𝕜 ∙ vacuum`. -/
theorem vacuumProj_eq_starProjection :
    (vacuumProj : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) =
      (𝕜 ∙ (vacuum : FullFockSpace 𝕜 H)).starProjection := by
  ext x : 1
  rw [Submodule.starProjection_singleton, vacuumProj_apply, norm_vacuum]
  simp

@[simp]
theorem norm_vacuumProj : ‖(vacuumProj : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H)‖ = 1 := by
  rw [vacuumProj, InnerProductSpace.norm_rankOne, norm_vacuum, mul_one]

end Vacuum

/-! ### Left creation operators -/

section Creation

/-- Tensoring on the left by `h : H` from grade `n` to grade `n + 1`. -/
private def stepCreation (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (h : H) (n : ℕ) :
    CompletedTensorPower 𝕜 H n →L[𝕜] CompletedTensorPower 𝕜 H (n + 1) :=
  (CompletedTensorPower.succEquiv 𝕜 H n).symm.toLinearIsometry.toContinuousLinearMap ∘L
    (UniformSpace.Completion.toComplL (S := 𝕜)).comp
      (TensorProduct.mkL 𝕜 H (CompletedTensorPower 𝕜 H n) h)

section
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

private theorem stepCreation_apply (h : H) (n : ℕ) (x : CompletedTensorPower 𝕜 H n) :
    stepCreation 𝕜 h n x =
      (CompletedTensorPower.succEquiv 𝕜 H n).symm
        ((h ⊗ₜ[𝕜] x : H ⊗[𝕜] CompletedTensorPower 𝕜 H n) :
          UniformSpace.Completion (H ⊗[𝕜] CompletedTensorPower 𝕜 H n)) :=
  rfl

private theorem inner_stepCreation (h k : H) (n : ℕ) (x y : CompletedTensorPower 𝕜 H n) :
    ⟪stepCreation 𝕜 h n x, stepCreation 𝕜 k n y⟫_𝕜 = ⟪h, k⟫_𝕜 * ⟪x, y⟫_𝕜 := by
  rw [stepCreation_apply, stepCreation_apply, LinearIsometryEquiv.inner_map_map,
    UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]

private theorem norm_stepCreation_apply (h : H) (n : ℕ) (x : CompletedTensorPower 𝕜 H n) :
    ‖stepCreation 𝕜 h n x‖ = ‖h‖ * ‖x‖ := by
  rw [stepCreation_apply, LinearIsometryEquiv.norm_map, UniformSpace.Completion.norm_coe,
    TensorProduct.norm_tmul]

private theorem stepCreation_add (h k : H) (n : ℕ) :
    stepCreation 𝕜 (h + k) n = stepCreation 𝕜 h n + stepCreation 𝕜 k n := by
  ext x : 1
  simp [stepCreation_apply, TensorProduct.add_tmul, Completion.coe_add]

private theorem stepCreation_smul (c : 𝕜) (h : H) (n : ℕ) :
    stepCreation 𝕜 (c • h) n = c • stepCreation 𝕜 h n := by
  ext x : 1
  rw [smul_apply, stepCreation_apply, stepCreation_apply, ← TensorProduct.smul_tmul',
    Completion.coe_smul, map_smul]

private def creationRaw (h : H) (x : FullFockSpace 𝕜 H) : ∀ n, CompletedTensorPower 𝕜 H n
  | 0 => 0
  | n + 1 => stepCreation 𝕜 h n (x n)

private theorem memℓp_creationRaw (h : H) (x : FullFockSpace 𝕜 H) :
    Memℓp (creationRaw h x) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat]
  rw [← _root_.summable_nat_add_iff 1]
  have hx : Summable fun n => ‖x n‖ ^ (2 : ℝ) := by
    simpa using (lp.memℓp x).summable (by simp)
  have heq : (fun n => ‖creationRaw h x (n + 1)‖ ^ (2 : ℝ)) =
      fun n => ‖h‖ ^ (2 : ℝ) * ‖x n‖ ^ (2 : ℝ) := by
    ext n
    simp [creationRaw, norm_stepCreation_apply, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  rw [heq]
  exact hx.mul_left _

end

/-- The *left creation operator* `ℓ(h)` on `FullFockSpace 𝕜 H`, shifting each grade `n` to grade
`n + 1` by tensoring on the left with `h`. -/
def creation (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (h : H) :
    FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H :=
  LinearMap.mkContinuous
    { toFun x := ⟨creationRaw h x, memℓp_creationRaw h x⟩
      map_add' x y := by
        apply lp.ext
        rw [lp.coeFn_add]
        ext (_ | n) <;> simp [creationRaw]
      map_smul' c x := by
        ext (_ | n) <;> simp [creationRaw] }
    ‖h‖ fun x => by
      refine lp.norm_le_of_tsum_le (by simp) (mul_nonneg (norm_nonneg h) (norm_nonneg x)) ?_
      simp only [ENNReal.toReal_ofNat]
      have hs : Summable fun i => ‖creationRaw h x i‖ ^ (2 : ℝ) := by
        simpa using (memℓp_creationRaw h x).summable (by simp)
      refine le_of_eq (hs.tsum_eq_zero_add.trans ?_)
      have hzero : ‖creationRaw h x 0‖ ^ (2 : ℝ) = 0 := by simp [creationRaw]
      have htail : (∑' n, ‖creationRaw h x (n + 1)‖ ^ (2 : ℝ)) =
          ∑' n, ‖h‖ ^ (2 : ℝ) * ‖x n‖ ^ (2 : ℝ) := by
        congr 1; ext n
        simp [creationRaw, norm_stepCreation_apply, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
      have hx_tsum : (∑' n, ‖x n‖ ^ (2 : ℝ)) = ‖x‖ ^ (2 : ℝ) := by
        simpa using (lp.norm_rpow_eq_tsum (p := 2) (by simp) x).symm
      rw [hzero, zero_add, htail, tsum_mul_left, hx_tsum,
        Real.mul_rpow (norm_nonneg h) (norm_nonneg x)]

section
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

@[simp]
theorem creation_apply_zero (h : H) (x : FullFockSpace 𝕜 H) :
    (creation 𝕜 h x) 0 = 0 :=
  (rfl)

@[simp]
theorem creation_apply_succ (h : H) (x : FullFockSpace 𝕜 H) (n : ℕ) :
    (creation 𝕜 h x) (n + 1) =
      (CompletedTensorPower.succEquiv 𝕜 H n).symm
        ((h ⊗ₜ[𝕜] x n : H ⊗[𝕜] CompletedTensorPower 𝕜 H n) :
          UniformSpace.Completion (H ⊗[𝕜] CompletedTensorPower 𝕜 H n)) :=
  (rfl)

private theorem creation_single (h : H) (n : ℕ) (x : CompletedTensorPower 𝕜 H n) :
    creation 𝕜 h (lp.single 2 n x) = lp.single 2 (n + 1) (stepCreation 𝕜 h n x) := by
  ext (_ | m)
  · simp [lp.single_apply]
  · rw [creation_apply_succ, ← stepCreation_apply]
    rcases eq_or_ne m n with rfl | hmn
    · simp
    · have hmn' : m + 1 ≠ n + 1 := Nat.succ_ne_succ_iff.mpr hmn
      rw [lp.single_apply_ne 2 n x hmn, lp.single_apply_ne 2 (n + 1) _ hmn', map_zero]

@[simp]
theorem inner_creation_creation (h k : H) (x y : FullFockSpace 𝕜 H) :
    ⟪creation 𝕜 h x, creation 𝕜 k y⟫_𝕜 = ⟪h, k⟫_𝕜 * ⟪x, y⟫_𝕜 := by
  have hs : Summable fun i => ⟪(creation 𝕜 h x) i, (creation 𝕜 k y) i⟫_𝕜 :=
    lp.summable_inner (𝕜 := 𝕜) (creation 𝕜 h x) (creation 𝕜 k y)
  have hstep : (fun n => ⟪(creation 𝕜 h x) (n + 1), (creation 𝕜 k y) (n + 1)⟫_𝕜) =
      fun n => ⟪h, k⟫_𝕜 * ⟪x n, y n⟫_𝕜 :=
    funext fun n => inner_stepCreation h k n (x n) (y n)
  rw [lp.inner_eq_tsum, hs.tsum_eq_zero_add, creation_apply_zero, inner_zero_left, zero_add,
    hstep, tsum_mul_left, lp.inner_eq_tsum]

@[simp]
theorem norm_creation_apply (h : H) (x : FullFockSpace 𝕜 H) :
    ‖creation 𝕜 h x‖ = ‖h‖ * ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg h) (norm_nonneg x)),
    norm_sq_eq_re_inner (𝕜 := 𝕜), inner_creation_creation, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]
  simp [mul_pow]

/-- Left creation `ℓ(h)` has exact operator norm `‖h‖`. -/
@[simp]
theorem norm_creation (h : H) : ‖creation 𝕜 h‖ = ‖h‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg h) fun x =>
    (norm_creation_apply h x).le) ?_
  simpa using (creation 𝕜 h).le_opNorm vacuum

@[simp]
theorem creation_add (h k : H) : creation 𝕜 (h + k) = creation 𝕜 h + creation 𝕜 k := by
  ext x (_ | n)
  · simp
  · simpa [← stepCreation_apply] using congrArg (fun S => S (x n)) (stepCreation_add h k n)

@[simp]
theorem creation_smul (c : 𝕜) (h : H) : creation 𝕜 (c • h) = c • creation 𝕜 h := by
  ext x (_ | n)
  · simp
  · simpa [← stepCreation_apply] using congrArg (fun S => S (x n)) (stepCreation_smul c h n)

end

/-- Left creation as a linear isometric embedding of `H` into the bounded operators on
`FullFockSpace 𝕜 H`. -/
def creationₗᵢ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] :
    H →ₗᵢ[𝕜] FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H where
  toFun := creation 𝕜
  map_add' := creation_add
  map_smul' := creation_smul
  norm_map' := norm_creation

section
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

@[simp]
theorem creationₗᵢ_apply (h : H) : creationₗᵢ 𝕜 H h = creation 𝕜 h :=
  (rfl)

@[simp]
theorem creation_zero : creation 𝕜 (0 : H) = 0 :=
  (creationₗᵢ 𝕜 H).map_zero

@[simp]
theorem creation_neg (h : H) : creation 𝕜 (-h) = -creation 𝕜 h :=
  (creationₗᵢ 𝕜 H).map_neg h

@[simp]
theorem creation_sub (h k : H) : creation 𝕜 (h - k) = creation 𝕜 h - creation 𝕜 k :=
  (creationₗᵢ 𝕜 H).map_sub h k

/-- For a unit vector `h`, left creation `creation 𝕜 h` is an isometry on `FullFockSpace 𝕜 H`. -/
theorem isometry_creation {h : H} (hh : ‖h‖ = 1) : Isometry (creation 𝕜 h) :=
  AddMonoidHomClass.isometry_of_norm (creation 𝕜 h) fun x => by simp [hh]

@[simp]
theorem inner_vacuum_creation (h : H) (x : FullFockSpace 𝕜 H) :
    ⟪vacuum, creation 𝕜 h x⟫_𝕜 = 0 := by
  simp [inner_vacuum_left]

@[simp]
theorem inner_creation_vacuum (h : H) (x : FullFockSpace 𝕜 H) :
    ⟪creation 𝕜 h x, vacuum⟫_𝕜 = 0 := by
  rw [← inner_conj_symm, inner_vacuum_creation, map_zero]

@[simp]
theorem vacuumProj_creation (h : H) (x : FullFockSpace 𝕜 H) :
    vacuumProj (creation 𝕜 h x) = 0 := by
  simp [vacuumProj_apply]

@[simp]
theorem vacuumProj_comp_creation (h : H) :
    vacuumProj ∘L creation 𝕜 h = 0 :=
  ContinuousLinearMap.ext (vacuumProj_creation h)

end

end Creation

/-! ### Left annihilation operators and Cuntz–Toeplitz relations -/

section Annihilation

/-- The *left annihilation operator* `ℓ(h)*` on `FullFockSpace 𝕜 H`, defined as the Hilbert-space
adjoint of `creation 𝕜 h`. -/
def annihilation (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (h : H) :
    FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H :=
  (creation 𝕜 h).adjoint

/-- Left annihilation as a conjugate-linear isometric embedding of `H` into the bounded operators
on `FullFockSpace 𝕜 H`. -/
def annihilationₗᵢ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] :
    H →ₗᵢ⋆[𝕜] FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H :=
  ContinuousLinearMap.adjoint.toLinearIsometry.comp (creationₗᵢ 𝕜 H)

section
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

@[simp]
theorem adjoint_creation (h : H) : (creation 𝕜 h).adjoint = annihilation 𝕜 h :=
  (rfl)

@[simp]
theorem star_creation (h : H) : star (creation 𝕜 h) = annihilation 𝕜 h :=
  (rfl)

@[simp]
theorem adjoint_annihilation (h : H) : (annihilation 𝕜 h).adjoint = creation 𝕜 h :=
  ContinuousLinearMap.adjoint_adjoint (creation 𝕜 h)

@[simp]
theorem star_annihilation (h : H) : star (annihilation 𝕜 h) = creation 𝕜 h :=
  adjoint_annihilation h

theorem inner_annihilation_right (h : H) (x y : FullFockSpace 𝕜 H) :
    ⟪x, annihilation 𝕜 h y⟫_𝕜 = ⟪creation 𝕜 h x, y⟫_𝕜 :=
  ContinuousLinearMap.adjoint_inner_right (creation 𝕜 h) x y

theorem inner_annihilation_left (h : H) (x y : FullFockSpace 𝕜 H) :
    ⟪annihilation 𝕜 h x, y⟫_𝕜 = ⟪x, creation 𝕜 h y⟫_𝕜 :=
  ContinuousLinearMap.adjoint_inner_left (creation 𝕜 h) y x

@[simp]
theorem annihilationₗᵢ_apply (h : H) : annihilationₗᵢ 𝕜 H h = annihilation 𝕜 h :=
  (rfl)

@[simp]
theorem annihilation_zero : annihilation 𝕜 (0 : H) = 0 :=
  (annihilationₗᵢ 𝕜 H).map_zero

@[simp]
theorem annihilation_add (h k : H) :
    annihilation 𝕜 (h + k) = annihilation 𝕜 h + annihilation 𝕜 k :=
  (annihilationₗᵢ 𝕜 H).map_add h k

@[simp]
theorem annihilation_smul (c : 𝕜) (h : H) :
    annihilation 𝕜 (c • h) = star c • annihilation 𝕜 h :=
  (annihilationₗᵢ 𝕜 H).map_smulₛₗ c h

@[simp]
theorem annihilation_neg (h : H) : annihilation 𝕜 (-h) = -annihilation 𝕜 h :=
  (annihilationₗᵢ 𝕜 H).map_neg h

@[simp]
theorem annihilation_sub (h k : H) :
    annihilation 𝕜 (h - k) = annihilation 𝕜 h - annihilation 𝕜 k :=
  (annihilationₗᵢ 𝕜 H).map_sub h k

/-- Left annihilation `ℓ(h)*` has exact operator norm `‖h‖`. -/
@[simp]
theorem norm_annihilation (h : H) : ‖annihilation 𝕜 h‖ = ‖h‖ :=
  (annihilationₗᵢ 𝕜 H).norm_map h

/-- Left annihilation kills the vacuum vector. -/
@[simp]
theorem annihilation_vacuum (h : H) : annihilation 𝕜 h vacuum = 0 := by
  refine ext_inner_left 𝕜 fun x => ?_
  rw [inner_annihilation_right, inner_creation_vacuum, inner_zero_right]

@[simp]
theorem annihilation_comp_vacuumProj (h : H) :
    annihilation 𝕜 h ∘L vacuumProj = 0 := by
  ext x : 1
  simp [vacuumProj_apply]

/-- **Cuntz–Toeplitz relation** on full Fock space: `ℓ(h)* ∘L ℓ(k) = ⟪h, k⟫ • id`. -/
@[simp]
theorem annihilation_comp_creation (h k : H) :
    annihilation 𝕜 h ∘L creation 𝕜 k =
      ⟪h, k⟫_𝕜 • ContinuousLinearMap.id 𝕜 (FullFockSpace 𝕜 H) := by
  refine ContinuousLinearMap.ext fun y => ext_inner_left 𝕜 fun x => ?_
  rw [ContinuousLinearMap.comp_apply, inner_annihilation_right, inner_creation_creation,
    smul_apply, ContinuousLinearMap.id_apply, inner_smul_right]

@[simp]
theorem annihilation_mul_creation (h k : H) :
    annihilation 𝕜 h * creation 𝕜 k =
      ⟪h, k⟫_𝕜 • (1 : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) :=
  annihilation_comp_creation h k

@[simp]
theorem annihilation_creation (h k : H) (x : FullFockSpace 𝕜 H) :
    annihilation 𝕜 h (creation 𝕜 k x) = ⟪h, k⟫_𝕜 • x :=
  DFunLike.congr_fun (annihilation_comp_creation h k) x

end

end Annihilation

/-! ### Pure tensor words and density of finite words -/

section Words

/-- The pure tensor word `h₁ ⊗ ⋯ ⊗ hₙ ∈ 𝓕(H)` attached to a list `w = [h₁, …, hₙ] : List H`,
with `wordVector 𝕜 [] = vacuum`. -/
def wordVector (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (w : List H) : FullFockSpace 𝕜 H :=
  w.foldr (fun h x => creation 𝕜 h x) vacuum

section
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

@[simp]
theorem wordVector_nil : wordVector 𝕜 ([] : List H) = (vacuum : FullFockSpace 𝕜 H) :=
  (rfl)

@[simp]
theorem wordVector_cons (h : H) (w : List H) :
    wordVector 𝕜 (h :: w) = creation 𝕜 h (wordVector 𝕜 w) :=
  (rfl)

@[simp]
theorem norm_wordVector (w : List H) :
    ‖wordVector 𝕜 w‖ = (w.map norm).prod := by
  induction w with
  | nil => simp
  | cons h w ih => simp [ih]

private def wordTensor : (w : List H) → CompletedTensorPower 𝕜 H w.length
  | [] => (CompletedTensorPower.zeroEquiv 𝕜 H).symm 1
  | h :: w => stepCreation 𝕜 h w.length (wordTensor w)

private theorem wordVector_eq_single (w : List H) :
    wordVector 𝕜 w = lp.single 2 w.length (wordTensor w) := by
  induction w with
  | nil => rfl
  | cons h w ih =>
    rw [wordVector_cons, ih, creation_single]
    rfl

/-- Pure tensor words of different lengths lie in distinct tensor grades and are therefore
orthogonal. -/
theorem inner_wordVector_of_length_ne {v w : List H} (h : v.length ≠ w.length) :
    ⟪wordVector 𝕜 v, wordVector 𝕜 w⟫_𝕜 = 0 := by
  rw [wordVector_eq_single v, wordVector_eq_single w, lp.inner_single_left,
    lp.single_apply_ne 2 w.length _ h]
  simp

/-- The inner product of two pure tensor words of the same length factors as the product of
factorwise inner products. -/
theorem inner_wordVector_of_length_eq {v w : List H} (h : v.length = w.length) :
    ⟪wordVector 𝕜 v, wordVector 𝕜 w⟫_𝕜 = (List.zipWith (inner 𝕜) v w).prod := by
  induction v generalizing w with
  | nil =>
    cases w with
    | nil => simp
    | cons _ _ => simp at h
  | cons a v ih =>
    cases w with
    | nil => simp at h
    | cons b w =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [wordVector_cons, wordVector_cons, inner_creation_creation, ih h, List.zipWith_cons_cons,
        List.prod_cons]

/-- Finite linear combinations of pure tensor words `wordVector 𝕜 w` (`w : List H`) are dense in
`FullFockSpace 𝕜 H`. -/
theorem topologicalClosure_span_range_wordVector :
    (Submodule.span 𝕜 (Set.range (wordVector 𝕜 (H := H)))).topologicalClosure = ⊤ := by
  set M := (Submodule.span 𝕜 (Set.range (wordVector 𝕜 (H := H)))).topologicalClosure
  have hM_closed : IsClosed (M : Set (FullFockSpace 𝕜 H)) :=
    Submodule.isClosed_topologicalClosure _
  have hcre : ∀ (h : H) {y : FullFockSpace 𝕜 H}, y ∈ M → creation 𝕜 h y ∈ M := by
    intro h y hy
    have hspan : Submodule.span 𝕜 (Set.range (wordVector 𝕜 (H := H))) ≤
        M.comap (creation 𝕜 h).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨w, rfl⟩
      exact Submodule.le_topologicalClosure _
        (Submodule.subset_span ⟨h :: w, (wordVector_cons (𝕜 := 𝕜) h w).symm⟩)
    exact Submodule.topologicalClosure_minimal _ hspan
      (hM_closed.preimage (creation 𝕜 h).continuous) hy
  have hsingle : ∀ (n : ℕ) (x : CompletedTensorPower 𝕜 H n), lp.single 2 n x ∈ M := by
    intro n
    induction n with
    | zero =>
      intro x
      have hx : x = CompletedTensorPower.zeroEquiv 𝕜 H x •
          (CompletedTensorPower.zeroEquiv 𝕜 H).symm 1 := by
        rw [← map_smul, smul_eq_mul, mul_one, LinearIsometryEquiv.symm_apply_apply]
      rw [hx, lp.single_smul]
      exact M.smul_mem _ (Submodule.le_topologicalClosure _
        (Submodule.subset_span ⟨[], wordVector_nil⟩))
    | succ n ih =>
      intro x
      let embed : UniformSpace.Completion (H ⊗[𝕜] CompletedTensorPower 𝕜 H n) →L[𝕜]
          FullFockSpace 𝕜 H :=
        (lp.singleContinuousLinearMap 𝕜 _ 2 (n + 1)).comp
          (CompletedTensorPower.succEquiv 𝕜 H n).symm.toLinearIsometry.toContinuousLinearMap
      have hx : lp.single 2 (n + 1) x = embed (CompletedTensorPower.succEquiv 𝕜 H n x) := by
        simp [embed]
      rw [hx]
      refine Completion.induction_on (CompletedTensorPower.succEquiv 𝕜 H n x)
          (hM_closed.preimage embed.continuous) fun u => ?_
      refine TensorProduct.inductionOn u (fun h w => ?_) (fun u₁ u₂ hu₁ hu₂ => ?_)
      · have htmul : embed (h ⊗ₜ[𝕜] w : H ⊗[𝕜] CompletedTensorPower 𝕜 H n) =
            creation 𝕜 h (lp.single 2 n w) := by
          rw [creation_single]
          rfl
        rw [htmul]
        exact hcre h (ih w)
      · rw [Completion.coe_add, map_add]
        exact M.add_mem hu₁ hu₂
  rw [eq_top_iff]
  exact fun f _ => hM_closed.mem_of_tendsto (lp.hasSum_single (by simp) f)
    (Eventually.of_forall fun s => M.sum_mem fun n _ => hsingle n (f n))

end

end Words

/-! ### Exact operator norm of self-adjoint field operators `ℓ(h) + ℓ(h)*` -/

section FieldNorm

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

private theorem two_le_norm_creation_add_annihilation_of_norm_eq_one {e : H} (he : ‖e‖ = 1) :
    2 ≤ ‖creation 𝕜 e + annihilation 𝕜 e‖ := by
  set S : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H := creation 𝕜 e + annihilation 𝕜 e
  let v : ℕ → FullFockSpace 𝕜 H := fun k => wordVector 𝕜 (List.replicate k e)
  have hv_norm : ∀ k, ‖v k‖ = 1 := fun k => by simp [v, he]
  have hv_orth : Pairwise fun j k => ⟪v j, v k⟫_𝕜 = 0 := fun j k hjk =>
    inner_wordVector_of_length_ne (by simpa [v] using hjk)
  have hv_inner : ∀ j k, ⟪v j, v k⟫_𝕜 = if j = k then 1 else 0 := by
    intro j k
    split_ifs with hjk
    · subst hjk
      rw [inner_self_eq_norm_sq_to_K, hv_norm]
      simp
    · exact hv_orth hjk
  have hbound : ∀ N : ℕ, (2 : ℝ) * N ≤ ‖S‖ * (N + 1) := by
    intro N
    let x : FullFockSpace 𝕜 H := ∑ k ∈ Finset.range (N + 1), v k
    have hx_sq : ‖x‖ ^ 2 = (N : ℝ) + 1 := by
      have := TauCeti.norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero hv_orth
        (Finset.range (N + 1))
      simpa [x, hv_norm] using this
    have hcre_x : creation 𝕜 e x = ∑ k ∈ Finset.range (N + 1), v (k + 1) := by
      simp [x, map_sum, v, List.replicate_succ]
    have hv_x : ∀ m, ⟪x, v m⟫_𝕜 = if m < N + 1 then 1 else 0 := fun m => by
      simp [x, sum_inner, hv_inner]
    have hcre_inner : ⟪x, creation 𝕜 e x⟫_𝕜 = (N : ℝ) := by
      rw [hcre_x, inner_sum]
      simp_rw [hv_x]
      rw [Finset.sum_range_succ]
      simp [Finset.filter_true_of_mem fun _ hx => Finset.mem_range.mp hx]
    have hann_inner : ⟪x, annihilation 𝕜 e x⟫_𝕜 = (N : ℝ) := by
      rw [inner_annihilation_right, ← inner_conj_symm, hcre_inner]
      simp
    have hS_inner : ⟪x, S x⟫_𝕜 = ((2 * (N : ℝ) : ℝ) : 𝕜) := by
      rw [add_apply, inner_add_right, hcre_inner, hann_inner]
      push_cast
      ring
    calc
      (2 : ℝ) * N = ‖(((2 * (N : ℝ) : ℝ) : 𝕜))‖ := by
        rw [RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
      _ = ‖⟪x, S x⟫_𝕜‖ := by rw [hS_inner]
      _ ≤ ‖x‖ * ‖S x‖ := norm_inner_le_norm x (S x)
      _ ≤ ‖x‖ * (‖S‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (S.le_opNorm x) (norm_nonneg x)
      _ = ‖S‖ * ‖x‖ ^ 2 := by ring
      _ = ‖S‖ * (N + 1) := by rw [hx_sq]
  by_contra! hlt
  have hpos : 0 < 2 - ‖S‖ := sub_pos.mpr hlt
  obtain ⟨N, hN⟩ := exists_nat_gt (‖S‖ / (2 - ‖S‖))
  have hN' : ‖S‖ < (N : ℝ) * (2 - ‖S‖) := (div_lt_iff₀ hpos).mp hN
  linarith [hbound N]

/-- The self-adjoint field operator `ℓ(h) + ℓ(h)*` has exact operator norm `2 * ‖h‖`. -/
@[simp]
theorem norm_creation_add_annihilation (h : H) :
    ‖creation 𝕜 h + annihilation 𝕜 h‖ = 2 * ‖h‖ := by
  refine le_antisymm ?_ ?_
  · calc
      ‖creation 𝕜 h + annihilation 𝕜 h‖ ≤ ‖creation 𝕜 h‖ + ‖annihilation 𝕜 h‖ :=
        norm_add_le _ _
      _ = 2 * ‖h‖ := by
        rw [norm_creation, norm_annihilation]
        ring
  · rcases eq_or_ne h 0 with rfl | hh
    · simp
    · have hnorm : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
      have hnormK : (‖h‖ : 𝕜) ≠ 0 := by exact_mod_cast hnorm
      let e : H := ((‖h‖ : 𝕜)⁻¹) • h
      have he_norm : ‖e‖ = 1 := by simp [e, norm_smul, inv_mul_cancel₀ hnorm]
      have he_eq : h = (‖h‖ : 𝕜) • e := by simp [e, smul_smul, mul_inv_cancel₀ hnormK]
      have hscale : creation 𝕜 h + annihilation 𝕜 h =
          (‖h‖ : 𝕜) • (creation 𝕜 e + annihilation 𝕜 e) := by
        conv_lhs => rw [he_eq]
        rw [creation_smul, annihilation_smul, RCLike.star_def, RCLike.conj_ofReal, smul_add]
      rw [hscale, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg h), mul_comm (2 : ℝ)]
      exact mul_le_mul_of_nonneg_left
        (two_le_norm_creation_add_annihilation_of_norm_eq_one (𝕜 := 𝕜) he_norm) (norm_nonneg h)

end FieldNorm

/-! ### Creation range projections and the strong sum over a `HilbertBasis` -/

section RangeProjections

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem isSelfAdjoint_creation_comp_annihilation (h : H) :
    IsSelfAdjoint (creation 𝕜 h ∘L annihilation 𝕜 h) := by
  rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    adjoint_annihilation, adjoint_creation]

theorem creation_comp_annihilation_comp (h k : H) :
    (creation 𝕜 h ∘L annihilation 𝕜 h) ∘L (creation 𝕜 k ∘L annihilation 𝕜 k) =
      ⟪h, k⟫_𝕜 • (creation 𝕜 h ∘L annihilation 𝕜 k) := by
  ext x : 1
  simp [ContinuousLinearMap.comp_apply]

theorem isIdempotentElem_creation_comp_annihilation {h : H} (hh : ‖h‖ = 1) :
    IsIdempotentElem (creation 𝕜 h ∘L annihilation 𝕜 h) := by
  rw [IsIdempotentElem, ContinuousLinearMap.mul_def, creation_comp_annihilation_comp,
    inner_self_eq_norm_sq_to_K, hh]
  simp

/-- For a unit vector `h`, `creation 𝕜 h ∘L annihilation 𝕜 h` is a self-adjoint projection. -/
theorem isStarProjection_creation_comp_annihilation {h : H} (hh : ‖h‖ = 1) :
    IsStarProjection (creation 𝕜 h ∘L annihilation 𝕜 h) :=
  ⟨isIdempotentElem_creation_comp_annihilation hh, isSelfAdjoint_creation_comp_annihilation h⟩

theorem creation_comp_annihilation_comp_of_inner_eq_zero {h k : H} (horth : ⟪h, k⟫_𝕜 = 0) :
    (creation 𝕜 h ∘L annihilation 𝕜 h) ∘L (creation 𝕜 k ∘L annihilation 𝕜 k) = 0 := by
  ext x : 1
  simp [ContinuousLinearMap.comp_apply, horth]

/-- For every `h : H`, the range of `creation 𝕜 h` is closed in `FullFockSpace 𝕜 H`. -/
instance isClosed_range_creation (h : H) :
    IsClosed ((creation 𝕜 h).range : Set (FullFockSpace 𝕜 H)) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  · have hanti : AntilipschitzWith (‖h‖₊⁻¹) (creation 𝕜 h) :=
      AntilipschitzWith.of_le_mul_dist fun x y => by
        simp [dist_eq_norm, ← map_sub, inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hh)]
    exact hanti.isClosed_range (creation 𝕜 h).uniformContinuous

/-- For a unit vector `h`, `creation 𝕜 h ∘L annihilation 𝕜 h` is the orthogonal projection onto the
closed range of `creation 𝕜 h`. -/
theorem creation_comp_annihilation_eq_starProjection {h : H} (hh : ‖h‖ = 1) :
    creation 𝕜 h ∘L annihilation 𝕜 h = (creation 𝕜 h).range.starProjection :=
  ContinuousLinearMap.comp_adjoint_eq_starProjection_range (isometry_creation hh)

end RangeProjections

end FullFockSpace

end TauCeti

section OrthonormalAndBasis

open TauCeti TauCeti.FullFockSpace

variable {ι : Type*} {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Any finite sum of creation range projections attached to an orthonormal family in `H` is a
self-adjoint projection on `FullFockSpace 𝕜 H`. -/
theorem _root_.Orthonormal.isStarProjection_sum_creation_comp_annihilation {v : ι → H}
    (hv : Orthonormal 𝕜 v) (s : Finset ι) :
    IsStarProjection (∑ i ∈ s, creation 𝕜 (v i) ∘L annihilation 𝕜 (v i)) := by
  classical
  refine ⟨?_, isSelfAdjoint_sum (R := FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) s fun i _ =>
    isSelfAdjoint_creation_comp_annihilation (v i)⟩
  rw [IsIdempotentElem, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · exact isIdempotentElem_creation_comp_annihilation (hv.1 i)
  · exact fun j _ hji => creation_comp_annihilation_comp_of_inner_eq_zero (hv.2 hji.symm)
  · exact fun hi' => (hi' hi).elim

/-- Each element of a `HilbertBasis` induces a creation isometry on `FullFockSpace 𝕜 H`. -/
theorem _root_.HilbertBasis.isometry_creation (b : _root_.HilbertBasis ι 𝕜 H) (i : ι) :
    Isometry (creation 𝕜 (b i)) :=
  FullFockSpace.isometry_creation (b.orthonormal.1 i)

/-- For a `HilbertBasis` `b`, `creation 𝕜 (b i) ∘L annihilation 𝕜 (b i)` is the orthogonal
projection onto `(creation 𝕜 (b i)).range`. -/
theorem _root_.HilbertBasis.creation_comp_annihilation_eq_starProjection
    (b : _root_.HilbertBasis ι 𝕜 H) (i : ι) :
    creation 𝕜 (b i) ∘L annihilation 𝕜 (b i) = (creation 𝕜 (b i)).range.starProjection :=
  FullFockSpace.creation_comp_annihilation_eq_starProjection (b.orthonormal.1 i)

/-- Distinct basis elements of a `HilbertBasis` have orthogonal creation range projections. -/
theorem _root_.HilbertBasis.creation_comp_annihilation_comp_of_ne
    (b : _root_.HilbertBasis ι 𝕜 H) {i j : ι} (hij : i ≠ j) :
    (creation 𝕜 (b i) ∘L annihilation 𝕜 (b i)) ∘L
      (creation 𝕜 (b j) ∘L annihilation 𝕜 (b j)) = 0 :=
  creation_comp_annihilation_comp_of_inner_eq_zero (b.orthonormal.2 hij)

/-- For a `HilbertBasis` `b` of `H`, the pairwise orthogonal range projections
`creation 𝕜 (b i) ∘L annihilation 𝕜 (b i)` sum in the strong operator topology to
`1 - vacuumProj`. -/
theorem _root_.HilbertBasis.hasSum_creation_comp_annihilation
    (b : _root_.HilbertBasis ι 𝕜 H) (x : FullFockSpace 𝕜 H) :
    HasSum (fun i => (creation 𝕜 (b i) ∘L annihilation 𝕜 (b i)) x) ((1 - vacuumProj) x) := by
  classical
  let P : ι → FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H :=
    fun i => creation 𝕜 (b i) ∘L annihilation 𝕜 (b i)
  let Q : Finset ι → FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H := fun s => ∑ i ∈ s, P i
  have hQ_iff : (∃ C, ∀ s, ‖Q s‖ ≤ C) ↔ Equicontinuous ((↑) ∘ Q) :=
    (NormedSpace.equicontinuous_tfae Q).out 6 2
  have hQ_equi : Equicontinuous ((↑) ∘ Q) := hQ_iff.mp
    ⟨1, fun s => (b.orthonormal.isStarProjection_sum_creation_comp_annihilation s).norm_le⟩
  have hclosed : IsClosed {y : FullFockSpace 𝕜 H |
      Tendsto (fun s => Q s y) atTop (𝓝 ((1 - vacuumProj) y))} :=
    hQ_equi.isClosed_setOfPred_tendsto (1 - vacuumProj).continuous
  let S : Submodule 𝕜 (FullFockSpace 𝕜 H) :=
    { carrier := {y | HasSum (fun i => P i y) ((1 - vacuumProj) y)}
      zero_mem' := by simp [hasSum_zero]
      add_mem' ha hb := by simpa only [Set.mem_ofPred_eq, map_add] using ha.add hb
      smul_mem' c y hy := by simpa only [Set.mem_ofPred_eq, map_smul] using hy.const_smul c }
  have hS_closed : IsClosed (S : Set (FullFockSpace 𝕜 H)) := by
    simpa [S, HasSum, Q] using hclosed
  have hmem : ∀ y, y ∈ S ↔ HasSum (fun i => P i y) ((1 - vacuumProj) y) := fun _ => Iff.rfl
  have hword : Submodule.span 𝕜 (Set.range (wordVector 𝕜 (H := H))) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, hmem]
    cases w with
    | nil =>
      simp [P, hasSum_zero]
    | cons h ws =>
      have heval : ((ContinuousLinearMap.apply 𝕜 (FullFockSpace 𝕜 H) (wordVector 𝕜 ws)).comp
          (creationₗᵢ 𝕜 H).toContinuousLinearMap : H →L[𝕜] FullFockSpace 𝕜 H) h =
            creation 𝕜 h (wordVector 𝕜 ws) := rfl
      have hsum := (b.hasSum_repr h).mapL
        ((ContinuousLinearMap.apply 𝕜 (FullFockSpace 𝕜 H) (wordVector 𝕜 ws)).comp
          (creationₗᵢ 𝕜 H).toContinuousLinearMap)
      rw [heval] at hsum
      have hterm : (fun i => P i (creation 𝕜 h (wordVector 𝕜 ws))) =
          fun i => creation 𝕜 (b.repr h i • b i) (wordVector 𝕜 ws) := by
        ext i
        simp [P, ContinuousLinearMap.comp_apply, b.repr_apply_apply]
      rw [wordVector_cons, hterm]
      simpa using hsum
  have htop : (⊤ : Submodule 𝕜 (FullFockSpace 𝕜 H)) ≤ S := by
    rw [← topologicalClosure_span_range_wordVector]
    exact Submodule.topologicalClosure_minimal _ hword hS_closed
  exact htop trivial

/-- Pointwise norm-convergent expansion `(1 - vacuumProj) x = ∑' i, ℓ(b i) ℓ(b i)* x` for a
`HilbertBasis` `b` of `H`. -/
theorem _root_.HilbertBasis.tsum_creation_comp_annihilation
    (b : _root_.HilbertBasis ι 𝕜 H) (x : FullFockSpace 𝕜 H) :
    (∑' i, (creation 𝕜 (b i) ∘L annihilation 𝕜 (b i)) x) = (1 - vacuumProj) x :=
  (b.hasSum_creation_comp_annihilation x).tsum_eq

end OrthonormalAndBasis

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic

/-!
# Hilbert–Schmidt operators as `ℓ²` families of columns

Fix a Hilbert basis `(bᵢ)` of `E`. A family of vectors `f ∈ ℓ²(ι, F)` represents the bounded
operator

`T_f x = ∑' i, ⟪bᵢ, x⟫ • fᵢ`,

whose columns are `T_f bᵢ = fᵢ`. This file shows that `f ↦ T_f` is a bounded linear injection
`ℓ²(ι, F) →L[𝕜] (E →L[𝕜] F)` of norm at most `1`, whose image is exactly the set of operators of
finite Hilbert–Schmidt energy `E_b(T) = ∑' i, ‖T bᵢ‖ₑ²`; the inverse sends such an operator to its
column family `i ↦ T bᵢ`. The energy of `T_f` is `‖f‖²`, so the Hilbert–Schmidt norm of `T_f` is the
`ℓ²` norm of `f`.

Each `T_f` is a norm limit of the finite-rank operators attached to the finitely supported
truncations of `f`, so it is compact. Consequently **every operator of finite Hilbert–Schmidt
energy is compact**.

## Main definitions

* `HilbertBasis.columnOperator b : ℓ²(ι, F) →L[𝕜] E →L[𝕜] F`: the operator `T_f` represented by
  an `ℓ²` family of columns `f`, relative to the Hilbert basis `b`.

## Main results

* `HilbertBasis.columnOperator_apply_self`: the columns of `T_f` are `f`, `T_f bᵢ = fᵢ`.
* `HilbertBasis.columnOperator_injective`: distinct column families give distinct operators.
* `HilbertBasis.columnOperator_eq_iff`: `T_f = T` exactly when `fᵢ = T bᵢ` for every `i`.
* `HilbertBasis.columnOperator_mk`: an operator whose columns are square-summable is the operator
  represented by its columns.
* `HilbertBasis.range_columnOperator`: the represented operators are exactly the operators of
  finite Hilbert–Schmidt energy, and `HilbertBasis.existsUnique_columnOperator_eq` gives the unique
  representative.
* `HilbertBasis.norm_columnOperator_apply_le`, `HilbertBasis.norm_columnOperator_le`: `‖T_f‖ ≤ ‖f‖`.
* `HilbertBasis.hilbertSchmidtEnergy_columnOperator` and
  `HilbertBasis.hilbertSchmidtNorm_columnOperator`: `E_b(T_f) = ‖f‖ₑ²` and `‖T_f‖_HS = ‖f‖`.
* `ContinuousLinearMap.hilbertSchmidtEnergy_ne_top_iff_memℓp` and
  `ContinuousLinearMap.hilbertSchmidtEnergy_ne_top_iff_summable`: an operator has finite energy
  exactly when its columns lie in `ℓ²`.
* `ContinuousLinearMap.isCompactOperator_of_hilbertSchmidtEnergy_ne_top`: **Hilbert–Schmidt
  operators are compact**.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  edition, Academic Press, 1980, Section VI.6.
* B. Simon, *Trace Ideals and Their Applications*, second edition, Mathematical Surveys and
  Monographs 120, American Mathematical Society, 2005, Section 2.
-/

public section

open scoped InnerProductSpace ENNReal lp

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace HilbertBasis

section Normed

variable [NormedAddCommGroup F] (b : HilbertBasis ι 𝕜 E)

/-- The series `∑' i, ⟪bᵢ, x⟫ • fᵢ` defining the operator represented by `f ∈ ℓ²(ι, F)` converges
absolutely: by Cauchy–Schwarz in `ℓ²`, `∑' i, ‖⟪bᵢ, x⟫‖ ‖fᵢ‖ ≤ ‖x‖ ‖f‖`. -/
theorem summable_norm_inner_mul_norm (f : ℓ²(ι, F)) (x : E) :
    Summable fun i ↦ ‖⟪b i, x⟫_𝕜‖ * ‖f i‖ := by
  simpa [b.repr_apply_apply] using lp.summable_mul (p := 2) (q := 2)
    (by simpa using Real.HolderConjugate.two_two) (lp.toNorm (b.repr x)) (lp.toNorm f)

/-- **Cauchy–Schwarz for the column series.** `∑' i, ‖⟪bᵢ, x⟫‖ ‖fᵢ‖ ≤ ‖x‖ ‖f‖`. -/
theorem tsum_norm_inner_mul_norm_le (f : ℓ²(ι, F)) (x : E) :
    ∑' i, ‖⟪b i, x⟫_𝕜‖ * ‖f i‖ ≤ ‖x‖ * ‖f‖ := by
  simpa [b.repr_apply_apply, lp.norm_toNorm] using lp.tsum_mul_le_mul_norm' (p := 2) (q := 2)
    (by simpa using Real.HolderConjugate.two_two) (lp.toNorm (b.repr x)) (lp.toNorm f)

variable [NormedSpace 𝕜 F]

/-- The column series is bounded by `‖f‖ ‖x‖`. -/
theorem norm_tsum_inner_smul_le (f : ℓ²(ι, F)) (x : E) :
    ‖∑' i, ⟪b i, x⟫_𝕜 • f i‖ ≤ ‖f‖ * ‖x‖ := by
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · simpa only [norm_smul] using b.summable_norm_inner_mul_norm f x
  · simpa only [norm_smul, mul_comm ‖f‖] using b.tsum_norm_inner_mul_norm_le f x

variable [CompleteSpace F]

/-- The column series `∑' i, ⟪bᵢ, x⟫ • fᵢ` converges in a complete target. -/
theorem summable_inner_smul (f : ℓ²(ι, F)) (x : E) : Summable fun i ↦ ⟪b i, x⟫_𝕜 • f i :=
  .of_norm <| by simpa only [norm_smul] using b.summable_norm_inner_mul_norm f x

/-- The **operator represented by an `ℓ²` family of columns**: relative to a Hilbert basis `(bᵢ)`
of `E`, the family `f ∈ ℓ²(ι, F)` represents `x ↦ ∑' i, ⟪bᵢ, x⟫ • fᵢ`, whose columns are
`fᵢ` (`columnOperator_apply_self`). The assignment `f ↦ T_f` is linear and bounded with norm at
most `1`. -/
noncomputable def columnOperator : ℓ²(ι, F) →L[𝕜] E →L[𝕜] F :=
  LinearMap.mkContinuous₂
    { toFun f :=
        { toFun x := ∑' i, ⟪b i, x⟫_𝕜 • f i
          map_add' x y := by
            simp only [inner_add_right, add_smul]
            exact (b.summable_inner_smul f x).tsum_add (b.summable_inner_smul f y)
          map_smul' c x := by
            simp only [inner_smul_right, mul_smul, RingHom.id_apply]
            exact tsum_const_smul'' c }
      map_add' f g := by
        ext x
        simp only [lp.coeFn_add, Pi.add_apply, smul_add, LinearMap.add_apply, LinearMap.coe_mk,
          AddHom.coe_mk]
        exact (b.summable_inner_smul f x).tsum_add (b.summable_inner_smul g x)
      map_smul' c f := by
        ext x
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_comm _ c, LinearMap.smul_apply,
          LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
        exact tsum_const_smul'' c }
    1 fun f x ↦ by rw [one_mul]; exact b.norm_tsum_inner_smul_le f x

theorem columnOperator_apply (f : ℓ²(ι, F)) (x : E) :
    b.columnOperator f x = ∑' i, ⟪b i, x⟫_𝕜 • f i :=
  (rfl)

/-- The column series sums to the value of the represented operator. -/
theorem hasSum_columnOperator_apply (f : ℓ²(ι, F)) (x : E) :
    HasSum (fun i ↦ ⟪b i, x⟫_𝕜 • f i) (b.columnOperator f x) :=
  (b.summable_inner_smul f x).hasSum

/-- **The columns of the represented operator.** `T_f bᵢ = fᵢ`. -/
@[simp]
theorem columnOperator_apply_self (f : ℓ²(ι, F)) (i : ι) : b.columnOperator f (b i) = f i := by
  classical
  rw [columnOperator_apply, tsum_eq_single i fun j hj ↦ by simp [b.orthonormal.2 hj]]
  simp [b.orthonormal.1 i]

/-- **Injectivity of the column representation.** An operator determines the `ℓ²` family of
columns representing it. -/
theorem columnOperator_injective : Function.Injective (b.columnOperator (F := F)) := fun f g h ↦
  lp.ext <| funext fun i ↦ by rw [← b.columnOperator_apply_self f, h, columnOperator_apply_self]

/-- An `ℓ²` family represents the operator `T` exactly when it is the column family of `T`. -/
theorem columnOperator_eq_iff {f : ℓ²(ι, F)} {T : E →L[𝕜] F} :
    b.columnOperator f = T ↔ ∀ i, f i = T (b i) := by
  refine ⟨fun h i ↦ by rw [← h, columnOperator_apply_self], fun h ↦ ?_⟩
  ext x
  refine (b.hasSum_columnOperator_apply f x).unique ?_
  simpa [h, b.repr_apply_apply] using (b.hasSum_repr x).mapL T

/-- **Reconstruction from columns.** An operator whose columns `i ↦ T bᵢ` are square-summable is
the operator represented by its columns. -/
theorem columnOperator_mk (T : E →L[𝕜] F) (hT : Memℓp (fun i ↦ T (b i)) 2) :
    b.columnOperator ⟨fun i ↦ T (b i), hT⟩ = T :=
  b.columnOperator_eq_iff.2 fun _ ↦ rfl

/-- **Operator-norm bound.** `‖T_f‖ ≤ ‖f‖`. -/
theorem norm_columnOperator_apply_le (f : ℓ²(ι, F)) : ‖b.columnOperator f‖ ≤ ‖f‖ :=
  (b.columnOperator f).opNorm_le_bound (norm_nonneg f) (b.norm_tsum_inner_smul_le f)

/-- The column representation `f ↦ T_f` has norm at most `1`. -/
theorem norm_columnOperator_le : ‖b.columnOperator (F := F)‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- The squared columns of `T_f` sum to `‖f‖²`. -/
theorem tsum_norm_columnOperator_apply_self_sq (f : ℓ²(ι, F)) :
    ∑' i, ‖b.columnOperator f (b i)‖ ^ 2 = ‖f‖ ^ 2 := by
  simpa using (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f).symm

/-- The family supported at one index represents a rank-one operator. -/
theorem columnOperator_single [DecidableEq ι] (i : ι) (v : F) :
    b.columnOperator (lp.single 2 i v) = (innerSL 𝕜 (b i)).smulRight v := by
  ext x
  rw [columnOperator_apply, tsum_eq_single i fun j hj ↦ by simp [Pi.single_eq_of_ne hj]]
  simp

/-- **The represented operators are compact**: `T_f` is the norm limit of the finite-rank operators
represented by the finitely supported truncations of `f`. -/
theorem isCompactOperator_columnOperator (f : ℓ²(ι, F)) :
    IsCompactOperator (b.columnOperator f) := by
  classical
  have hsum := (lp.hasSum_single ENNReal.ofNat_ne_top f).mapL b.columnOperator
  refine isCompactOperator_of_tendsto hsum (.of_forall fun s ↦ ?_)
  refine (compactOperator (RingHom.id 𝕜) E F).sum_mem fun i _ ↦ ?_
  rw [columnOperator_single]
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL 𝕜 (b i))).clm_comp
    ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (f i))

end Normed

section Inner

variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- An operator has finite Hilbert–Schmidt energy exactly when its column family `i ↦ T bᵢ` is
square-summable. -/
theorem _root_.ContinuousLinearMap.hilbertSchmidtEnergy_ne_top_iff_summable (T : E →L[𝕜] F)
    (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtEnergy b ≠ ∞ ↔ Summable fun i ↦ ‖T (b i)‖ ^ 2 := by
  rw [ContinuousLinearMap.hilbertSchmidtEnergy_def]
  have h := tsum_enorm_ne_top_iff_summable_norm (f := fun i ↦ ‖T (b i)‖ ^ 2)
  simpa only [enorm_pow, enorm_norm, norm_pow, norm_norm] using h

/-- An operator has finite Hilbert–Schmidt energy exactly when its column family `i ↦ T bᵢ` lies
in `ℓ²`. -/
theorem _root_.ContinuousLinearMap.hilbertSchmidtEnergy_ne_top_iff_memℓp (T : E →L[𝕜] F)
    (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtEnergy b ≠ ∞ ↔ Memℓp (fun i ↦ T (b i)) 2 := by
  rw [T.hilbertSchmidtEnergy_ne_top_iff_summable, memℓp_gen_iff (by norm_num)]
  simp

variable [CompleteSpace F] (b : HilbertBasis ι 𝕜 E)

/-- **Energy identity.** The Hilbert–Schmidt energy of `T_f` is `‖f‖ₑ²`. -/
@[simp]
theorem hilbertSchmidtEnergy_columnOperator (f : ℓ²(ι, F)) :
    (b.columnOperator f).hilbertSchmidtEnergy b = ‖f‖ₑ ^ 2 := by
  have hs := lp.hasSum_norm (p := 2) (by norm_num) f
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
  simp_rw [ContinuousLinearMap.hilbertSchmidtEnergy_def, columnOperator_apply_self, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), ← hs.tsum_eq]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hs.summable).symm

/-- The operators represented by `ℓ²` families of columns are exactly the operators of finite
Hilbert–Schmidt energy. -/
theorem range_columnOperator :
    Set.range (b.columnOperator (F := F)) = {T | T.hilbertSchmidtEnergy b ≠ ∞} := by
  ext T
  refine ⟨?_, fun hT ↦ ?_⟩
  · rintro ⟨f, rfl⟩
    simp
  · exact ⟨_, b.columnOperator_mk T ((T.hilbertSchmidtEnergy_ne_top_iff_memℓp b).1 hT)⟩

/-- **Unique column representative.** An operator of finite Hilbert–Schmidt energy is represented
by exactly one `ℓ²` family of columns. -/
theorem existsUnique_columnOperator_eq {T : E →L[𝕜] F} (hT : T.hilbertSchmidtEnergy b ≠ ∞) :
    ∃! f : ℓ²(ι, F), b.columnOperator f = T := by
  obtain ⟨f, rfl⟩ : T ∈ Set.range b.columnOperator := by rwa [range_columnOperator]
  exact ⟨f, rfl, fun g hg ↦ b.columnOperator_injective hg⟩

/-- **Hilbert–Schmidt norm identity.** The Hilbert–Schmidt norm of `T_f` is the `ℓ²` norm of
`f`. -/
@[simp]
theorem hilbertSchmidtNorm_columnOperator [CompleteSpace E] (f : ℓ²(ι, F)) :
    (b.columnOperator f).hilbertSchmidtNorm = ‖f‖ := by
  rw [(b.columnOperator f).hilbertSchmidtNorm_eq_sqrt b, hilbertSchmidtEnergy_columnOperator,
    ENNReal.toReal_pow, toReal_enorm, Real.sqrt_sq (norm_nonneg f)]

variable {b} in
/-- **Hilbert–Schmidt operators are compact.** An operator of finite Hilbert–Schmidt energy is a
compact operator. -/
theorem _root_.ContinuousLinearMap.isCompactOperator_of_hilbertSchmidtEnergy_ne_top
    {T : E →L[𝕜] F} (hT : T.hilbertSchmidtEnergy b ≠ ∞) : IsCompactOperator T := by
  rw [← b.columnOperator_mk T ((T.hilbertSchmidtEnergy_ne_top_iff_memℓp b).1 hT)]
  exact b.isCompactOperator_columnOperator _

end Inner

end HilbertBasis

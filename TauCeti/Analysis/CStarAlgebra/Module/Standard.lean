/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.CStarAlgebra.Module.DirectSum
public import TauCeti.Analysis.CStarAlgebra.Module.Self
public import TauCeti.Analysis.Normed.Operator.Compact.HilbertAdjoint
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.Normed.Lp.Diagonal.Positive

/-!
# The standard Hilbert C⋆-module `H_A = ℓ²(ℕ, A)`

For a (possibly nonunital) C⋆-algebra `A`, the standard right Hilbert `A`-module
`TauCeti.StandardHilbertModule A` (commonly denoted `H_A` or `ℓ²(ℕ, A)`) is the countable Hilbert
direct sum `HilbertDirectSum Aᵐᵒᵖ (fun _ : ℕ ↦ A)` of copies of `A` equipped with the right
self-module structure `CStarModule Aᵐᵒᵖ A` from `TauCeti.Analysis.CStarAlgebra.Module.Self`.
Concretely, its elements are sequences `x : ℕ → A` for which `∑' n, star (x n) * x n` converges in
norm in `A`, with right action `(op a • x) n = x n * a`, `A`-valued inner product
`unop ⟪x, y⟫_{Aᵐᵒᵖ} = ∑' n, star (x n) * y n`, and norm `‖x‖ = √‖∑' n, star (x n) * x n‖`. Like
`A` itself, `StandardHilbertModule A` is full over `A`.

While the Banach `ℓ²` space `lp (fun _ : ℕ ↦ A) 2` of sequences satisfying `∑' n, ‖x n‖ ^ 2 < ∞`
embeds contractively and with dense range into `StandardHilbertModule A` via
`HilbertDirectSum.ofLp`, norm-summability of `star (x n) * x n` in `A` is strictly weaker than
scalar square-summability of `‖x n‖` in general. Following Lance (Chapter 1, p. 7), for the
nonunital C⋆-algebra `K(ℓ²(ℕ, ℂ))` of compact operators on `ℓ²(ℕ, ℂ)`, the sequence
`a n = (√(n + 1))⁻¹ • P_n` of scaled coordinate projections satisfies
`∑' n, star (a n) * a n = diag((n + 1)⁻¹)` in operator norm, yet `∑ n, ‖a n‖ ^ 2 = ∑ n, (n + 1)⁻¹`
diverges, proving that `HilbertDirectSum.ofLp` is not surjective
(`StandardHilbertModule.not_surjective_ofLp_compactOperator`).

## Main declarations

* `TauCeti.StandardHilbertModule`: the standard right Hilbert `A`-module
  `HilbertDirectSum Aᵐᵒᵖ (fun _ : ℕ ↦ A)`.
* `TauCeti.StandardHilbertModule.mkOfSummable`: construct an element of `StandardHilbertModule A`
  from `f : ℕ → A` with `Summable fun n ↦ star (f n) * f n`.
* `TauCeti.StandardHilbertModule.unop_inner_eq_tsum`,
  `TauCeti.StandardHilbertModule.norm_eq_sqrt_norm_tsum`: explicit formulas for the `A`-valued
  inner product and norm on `StandardHilbertModule A`.
* `TauCeti.StandardHilbertModule.dense_range_unop_inner`,
  `TauCeti.StandardHilbertModule.topologicalClosure_span_range_unop_inner`: fullness of
  `StandardHilbertModule A` over `A`.
* `TauCeti.StandardHilbertModule.exists_notMem_range_ofLp_compactOperator`,
  `TauCeti.StandardHilbertModule.not_surjective_ofLp_compactOperator`: strictness of the inclusion
  `lp (fun _ : ℕ ↦ K(ℓ²)) 2 → StandardHilbertModule K(ℓ²)`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1,
  pp. 6–7.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Example 2.14.
-/

public section

noncomputable section

open Filter Topology MulOpposite
open scoped lp ENNReal NNReal

namespace TauCeti

/-- The standard right Hilbert `A`-module `H_A = ℓ²(ℕ, A)`, defined as the countable Hilbert direct
sum of copies of `A` as a right Hilbert module over itself (`CStarModule Aᵐᵒᵖ A`). -/
abbrev StandardHilbertModule (A : Type*)
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] : Type _ :=
  HilbertDirectSum Aᵐᵒᵖ (fun _ : ℕ ↦ A)

namespace StandardHilbertModule

section General

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Construct an element of `StandardHilbertModule A` from a sequence `f : ℕ → A` whose squares
`star (f n) * f n` are norm-summable in `A`. -/
def mkOfSummable (f : ℕ → A) (hf : Summable fun n ↦ star (f n) * f n) :
    StandardHilbertModule A :=
  ⟨f, hf.op⟩

/-- Evaluating `mkOfSummable f hf` at `n` returns `f n`. -/
@[simp]
theorem mkOfSummable_apply (f : ℕ → A) (hf : Summable fun n ↦ star (f n) * f n) (n : ℕ) :
    mkOfSummable f hf n = f n := (rfl)

/-- For any `x : StandardHilbertModule A`, the series `∑' n, star (x n) * x n` is norm-summable in
`A`. -/
theorem summable_star_mul_self (x : StandardHilbertModule A) :
    Summable fun n ↦ star (x n) * x n :=
  summable_unop.mpr x.summable_inner_self

/-- For any `x, y : StandardHilbertModule A`, the series `∑' n, star (x n) * y n` is norm-summable
in `A`. -/
theorem summable_star_mul (x y : StandardHilbertModule A) :
    Summable fun n ↦ star (x n) * y n :=
  summable_unop.mpr (HilbertDirectSum.summable_inner x y)

/-- The `A`-valued inner product on `StandardHilbertModule A` is the unconditional norm sum of
`star (x n) * y n`. -/
theorem hasSum_unop_inner (x y : StandardHilbertModule A) :
    HasSum (fun n ↦ star (x n) * y n) (unop (inner Aᵐᵒᵖ x y)) :=
  HilbertDirectSum.hasSum_unop_inner x y

/-- The `A`-valued inner product on `StandardHilbertModule A` is `∑' n, star (x n) * y n`. -/
theorem unop_inner_eq_tsum (x y : StandardHilbertModule A) :
    unop (inner Aᵐᵒᵖ x y) = ∑' n, star (x n) * y n :=
  HilbertDirectSum.unop_inner_def x y

/-- The norm on `StandardHilbertModule A` is `√‖∑' n, star (x n) * x n‖`. -/
theorem norm_eq_sqrt_norm_tsum (x : StandardHilbertModule A) :
    ‖x‖ = √‖∑' n, star (x n) * x n‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Aᵐᵒᵖ) x, ← norm_unop, unop_inner_eq_tsum]

/-- The squared norm on `StandardHilbertModule A` is `‖∑' n, star (x n) * x n‖`. -/
theorem norm_sq_eq_norm_tsum (x : StandardHilbertModule A) :
    ‖x‖ ^ 2 = ‖∑' n, star (x n) * x n‖ := by
  rw [CStarModule.norm_sq_eq Aᵐᵒᵖ (x := x), ← norm_unop, unop_inner_eq_tsum]

/-- The right `A`-action on `StandardHilbertModule A` multiplies each coordinate on the right. -/
theorem op_smul_apply (a : A) (x : StandardHilbertModule A) (n : ℕ) :
    (op a • x) n = x n * a := (rfl)

/-- The `A`-valued inner products on `StandardHilbertModule A` form a dense subset of `A`. -/
theorem dense_range_unop_inner :
    Dense (Set.range fun p : StandardHilbertModule A × StandardHilbertModule A ↦
      unop (inner Aᵐᵒᵖ p.1 p.2)) := by
  refine CStarModule.dense_range_unop_inner_mulOpposite.mono ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact ⟨(HilbertDirectSum.single Aᵐᵒᵖ (fun _ : ℕ ↦ A) 0 a,
      HilbertDirectSum.single Aᵐᵒᵖ (fun _ : ℕ ↦ A) 0 b), by simp⟩

/-- The standard Hilbert module `StandardHilbertModule A` is full over `A`: the closed complex
linear span of its `A`-valued inner products is all of `A`. -/
theorem topologicalClosure_span_range_unop_inner :
    (Submodule.span ℂ (Set.range fun p : StandardHilbertModule A × StandardHilbertModule A ↦
      unop (inner Aᵐᵒᵖ p.1 p.2))).topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp <|
    dense_range_unop_inner.mono Submodule.subset_span

end General

/-! ### Strictness of `lp (fun _ : ℕ ↦ K(ℓ²)) 2 ↪ StandardHilbertModule K(ℓ²)` -/

section CompactSeparation

private theorem antitone_inv_add_one :
    Antitone (fun n : ℕ ↦ (⟨((n : ℝ) + 1)⁻¹, by positivity⟩ : ℝ≥0)) := fun m n hmn ↦
  Subtype.mk_le_mk.mpr <| inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)

private def harmonicDiag : ℓ^∞(ℕ, ℂ) :=
  lp.ofAntitone ℂ antitone_inv_add_one

private theorem harmonicDiag_apply (n : ℕ) :
    harmonicDiag n = (((n : ℝ) + 1)⁻¹ : ℝ) :=
  lp.ofAntitone_apply ℂ antitone_inv_add_one n

private theorem norm_harmonicDiag_apply (n : ℕ) :
    ‖harmonicDiag n‖ = ((n : ℝ) + 1)⁻¹ :=
  lp.norm_ofAntitone_apply ℂ antitone_inv_add_one n

private theorem tendsto_norm_harmonicDiag :
    Tendsto (fun n : ℕ ↦ ‖harmonicDiag n‖) cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop]
  refine tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n ↦ ?_
  rw [norm_harmonicDiag_apply, one_div]

private def harmonicCoord (n : ℕ) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ) :=
  ⟨lp.diagonalCLM (p := 2) (lp.single ∞ n (((√((n : ℝ) + 1))⁻¹ : ℝ) : ℂ)),
    ContinuousLinearMap.mem_compactOperatorStarSubalgebra_iff.mpr <|
      lp.isCompactOperator_diagonalCLM _ <| tendsto_nhds_of_eventually_eq <|
        eventually_cofinite.mpr <| (Set.finite_singleton n).subset fun i hi ↦ by
          by_contra hne
          rw [Set.mem_singleton_iff] at hne
          exact hi (by simp [hne])⟩

@[simp]
private theorem coe_harmonicCoord (n : ℕ) :
    (harmonicCoord n : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)) =
      lp.diagonalCLM (p := 2) (lp.single ∞ n (((√((n : ℝ) + 1))⁻¹ : ℝ) : ℂ)) := (rfl)

private theorem star_mul_self_harmonicCoord (n : ℕ) :
    ((star (harmonicCoord n) * harmonicCoord n :
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ)) :
      ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)) =
      lp.diagonalCLM (p := 2) (lp.single ∞ n (harmonicDiag n)) := by
  set e : ℓ^∞(ℕ, ℂ) := lp.single ∞ n (((√((n : ℝ) + 1))⁻¹ : ℝ) : ℂ)
  have hself : IsSelfAdjoint (lp.diagonalCLM (p := 2) e) :=
    (lp.isSelfAdjoint_diagonalCLM_iff e).mpr fun i ↦ by
      by_cases hi : i = n
      · subst i; simp [e]
      · simp [e, Pi.single_eq_of_ne hi]
  have he_sq : e * e = lp.single ∞ n (harmonicDiag n) := by
    refine lp.ext (funext fun i ↦ ?_)
    have hmul : (e * e) i = e i * e i := congrFun (lp.infty_coeFn_mul e e) i
    rw [hmul]
    by_cases hi : i = n
    · subst i
      have hpos : 0 ≤ (n : ℝ) + 1 := by positivity
      simp only [e, lp.single_apply_self, harmonicDiag_apply, ← Complex.ofReal_mul]
      rw [← mul_inv, Real.mul_self_sqrt hpos]
    · simp [e, Pi.single_eq_of_ne hi]
  rw [MulMemClass.coe_mul, StarMemClass.coe_star, coe_harmonicCoord, hself.star_eq,
    ContinuousLinearMap.mul_def, ← lp.diagonalCLM_mul, he_sq]

private theorem hasSum_star_mul_self_harmonicCoord :
    HasSum (fun n ↦ star (harmonicCoord n) * harmonicCoord n)
      (⟨lp.diagonalCLM (p := 2) harmonicDiag,
        ContinuousLinearMap.mem_compactOperatorStarSubalgebra_iff.mpr
          (lp.isCompactOperator_diagonalCLM harmonicDiag tendsto_norm_harmonicDiag)⟩ :
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ)) := by
  rw [HasSum, SummationFilter.unconditional_filter, tendsto_subtype_rng]
  refine (lp.tendsto_diagonalTruncation (p := 2) harmonicDiag tendsto_norm_harmonicDiag).congr'
    (Eventually.of_forall fun s ↦ ?_)
  let diagHom : ℓ^∞(ℕ, ℂ) →+ (ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)) :=
    ⟨⟨lp.diagonalCLM (p := 2), lp.diagonalCLM_zero⟩, lp.diagonalCLM_add⟩
  exact (lp.diagonalTruncation_eq_diagonalCLM (p := 2) harmonicDiag s).trans <|
    (map_sum diagHom (fun n ↦ lp.single ∞ n (harmonicDiag n)) s).trans <|
      (Finset.sum_congr rfl fun n _ ↦ (star_mul_self_harmonicCoord n).symm).trans
        (map_sum (AddSubmonoidClass.subtype
          (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ)))
          (fun n ↦ star (harmonicCoord n) * harmonicCoord n) s).symm

private theorem norm_harmonicCoord_sq (n : ℕ) :
    ‖harmonicCoord n‖ ^ 2 = 1 / ((n + 1 : ℕ) : ℝ) := by
  have hnn : 0 ≤ (√((n : ℝ) + 1))⁻¹ := by positivity
  have hnorm : ‖harmonicCoord n‖ = (√((n : ℝ) + 1))⁻¹ := by
    rw [AddSubgroupClass.coe_norm, coe_harmonicCoord, lp.norm_diagonalCLM,
      lp.norm_single ENNReal.zero_lt_top, Complex.norm_real, Real.norm_of_nonneg hnn]
  rw [hnorm, inv_pow, Real.sq_sqrt (by positivity), Nat.cast_add, Nat.cast_one, one_div]

/-- For the C⋆-algebra `K(ℓ²(ℕ, ℂ))` of compact operators on `ℓ²(ℕ, ℂ)`, there exists a vector in
`StandardHilbertModule K(ℓ²(ℕ, ℂ))` outside the range of the Banach `ℓ²` inclusion
`HilbertDirectSum.ofLp`. -/
theorem exists_notMem_range_ofLp_compactOperator :
    ∃ x : StandardHilbertModule
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ)),
      x ∉ Set.range
        (HilbertDirectSum.ofLp
          (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ))ᵐᵒᵖ
          (fun _ : ℕ ↦ ContinuousLinearMap.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ))) := by
  refine ⟨mkOfSummable harmonicCoord hasSum_star_mul_self_harmonicCoord.summable, ?_⟩
  rintro ⟨y, hy⟩
  have hcoord : (y : ℕ → _) = harmonicCoord := funext fun n ↦ by
    simpa [HilbertDirectSum.ofLp_apply] using
      congrArg (fun z : StandardHilbertModule _ ↦ z n) hy
  have h2 : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hmem : Summable fun n : ℕ ↦ ‖harmonicCoord n‖ ^ 2 := by
    simpa [hcoord] using (memℓp_gen_iff h2).mp y.prop
  simp_rw [norm_harmonicCoord_sq] at hmem
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hmem)

/-- The contractive dense embedding `lp (fun _ : ℕ ↦ K(ℓ²)) 2 →L[ℂ] StandardHilbertModule K(ℓ²)`
is not surjective. -/
theorem not_surjective_ofLp_compactOperator :
    ¬ Function.Surjective
      (HilbertDirectSum.ofLp
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ))ᵐᵒᵖ
        (fun _ : ℕ ↦ ContinuousLinearMap.compactOperatorStarSubalgebra ℂ ℓ^2(ℕ, ℂ))) := by
  intro hsurj
  obtain ⟨x, hx⟩ := exists_notMem_range_ofLp_compactOperator
  exact hx (hsurj x)

end CompactSeparation

end StandardHilbertModule

end TauCeti

end

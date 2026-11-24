/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Algebra.TemperleyLieb.Dimension
public import TauCeti.Algebra.TemperleyLieb.Quotient.Positivity
public import TauCeti.Analysis.CStarAlgebra.ConditionalExpectation.CompletelyPositive
public import TauCeti.Analysis.StarAlgebra.GNS.FiniteDimensional
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
/-! # The C⋆-tower of positive Jones quotients and its conditional expectations

For `δ ∈ jonesLoopParameters`, `htr.Quotient n` forms a unital C⋆-algebra tower equipped with
faithful tracial states (`normalizedQuotientTrace`), isometric `⋆`-inclusions
(`quotientStrandIncl` / `quotientStrandStarAlgHom`), Jones projections (`jonesProjection`), and
unique trace-compatible completely positive conditional expectations (`quotientExpect`,
`cstarConditionalExpectation`, intertwined with `pathAlgebraExpect` by
`quotientPathAlgebraEquiv_quotientExpect`, `discreteQuotientEquiv_quotientExpect`, and
`genericQuotientEquiv_quotientExpect`).

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25 (tower of positive
  Temperley–Lieb quotients, Jones projections, normalized Markov trace, and trace-preserving
  conditional expectations).
* F. M. Goodman, P. de la Harpe, V. F. R. Jones, *Coxeter Graphs and Towers of Algebras*, MSRI
  Publications 14, Springer (1989) (path-algebra conditional expectations and multimatrix tower
  models). -/
public section
noncomputable section
open scoped ComplexOrder CStarAlgebra
namespace TauCeti.TemperleyLieb
namespace IsMarkovTrace
section JonesTower
open Real SimpleGraph
private structure JonesModel (δ : ℝ) : Type 1 where
  V : Type
  [decEq : DecidableEq V]
  G : SimpleGraph V
  [decAdj : DecidableRel G.Adj]
  [locFin : G.LocallyFinite]
  v₀ : V
  r : V → ℂ
  hr : ∀ v, r v ≠ 0
  hrs : ∀ v, IsSelfAdjoint (r v)
  hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = (δ : ℂ) * r v ^ 2
  f : V → ℕ
  hf : Function.Injective f
  hf₀ : f v₀ = 0
  hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x
attribute [instance] JonesModel.decEq JonesModel.decAdj JonesModel.locFin
private def jonesModel {δ : ℝ} (hδ : δ ∈ jonesLoopParameters) : JonesModel δ := by
  classical
  exact if hm : ∃ m : ℕ, 3 ≤ m ∧ δ = 2 * cos (π / m) then
    let m := Classical.choose hm
    { V := Fin (m - 1), G := pathGraph (m - 1),
      v₀ := ⟨0, Nat.sub_pos_of_lt (by have := (Classical.choose_spec hm).1; omega)⟩,
      r := discretePathWeight m, hr := discretePathWeight_ne_zero,
      hrs := isSelfAdjoint_discretePathWeight m,
      hδ := fun v ↦ (Classical.choose_spec hm).2 ▸ sum_neighborFinset_discretePathWeight_sq v,
      f := Fin.val, hf := Fin.val_injective, hf₀ := rfl, hadj := fun h ↦ pathGraph_adj.1 h }
  else
    have h2 : 2 ≤ δ := (mem_jonesLoopParameters.1 hδ).resolve_left hm
    { V := ℕ, G := hasse ℕ, v₀ := 0, r := genericPathWeight δ,
      hr := genericPathWeight_ne_zero h2, hrs := isSelfAdjoint_genericPathWeight δ,
      hδ := sum_neighborFinset_genericPathWeight_sq h2,
      f := id, hf := Function.injective_id, hf₀ := rfl, hadj := fun h ↦ hasse_nat_adj.1 h }
variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
/-- The **Jones projection** `p_n = δ⁻¹ • mk (e δ (Fin.last n))` in `htr.Quotient (n + 2)`, for
nonzero `δ`. -/
def jonesProjection (_hδ : δ ≠ 0) (n : ℕ) : htr.Quotient (n + 2) :=
  (δ : ℂ)⁻¹ • Ideal.Quotient.mk (htr.traceRadical (n + 2)) (e (δ : ℂ) (Fin.last n))
/-- Every Jones projection is self-adjoint. -/
theorem isSelfAdjoint_jonesProjection (hδ : δ ≠ 0) (n : ℕ) :
    IsSelfAdjoint (htr.jonesProjection hδ n) := by
  rw [IsSelfAdjoint, jonesProjection, star_smul, Ideal.Quotient.star_mk, star_e, star_inv₀,
    IsSelfAdjoint.star_eq (Complex.conj_ofReal _)]
omit [Fact (IsSelfAdjoint (δ : ℂ))] in
/-- For `δ ≠ 0`, every Jones projection is idempotent. -/
theorem isIdempotentElem_jonesProjection (hδ : δ ≠ 0) (n : ℕ) :
    IsIdempotentElem (htr.jonesProjection hδ n) := by
  rw [IsIdempotentElem, jonesProjection, ← Ideal.Quotient.mkₐ_eq_mk ℂ, smul_mul_smul_comm,
    ← map_mul, e_mul_self, map_smul, smul_smul, mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 hδ), mul_one]
variable (hδ : δ ∈ jonesLoopParameters)
private abbrev jonesEquiv (n : ℕ) :=
  let M := jonesModel hδ
  htr.quotientPathAlgebraEquiv M.G M.v₀ M.hr M.hrs M.hδ M.hf M.hf₀ M.hadj n
/-- **Trace-preserving conditional expectation on positive Jones quotients**. -/
def quotientExpect (n : ℕ) : htr.Quotient (n + 1) →ₗ[ℂ] htr.Quotient n :=
  let M := jonesModel hδ
  (htr.jonesEquiv hδ n).symm.toAlgEquiv.toLinearMap.comp <|
    (pathAlgebraExpect M.G M.v₀ M.r (δ : ℂ)).comp (htr.jonesEquiv hδ (n + 1)).toAlgEquiv.toLinearMap
/-- `quotientExpect` is unital. -/
@[simp] theorem quotientExpect_one (n : ℕ) : htr.quotientExpect hδ n 1 = 1 := by
  simp [quotientExpect, pathAlgebraExpect_one (jonesModel hδ).hr
    (isUnit_of_mem_jonesLoopParameters hδ).ne_zero (jonesModel hδ).hδ]
/-- Left bimodule property of `quotientExpect` over `quotientStrandIncl`. -/
@[simp] theorem quotientExpect_mul_left {n : ℕ} (x : htr.Quotient n) (y : htr.Quotient (n + 1)) :
    htr.quotientExpect hδ n (htr.quotientStrandIncl n x * y) = x * htr.quotientExpect hδ n y := by
  dsimp [quotientExpect, jonesEquiv]
  rw [map_mul,
    htr.quotientPathAlgebraEquiv_quotientStrandIncl (jonesModel hδ).G (jonesModel hδ).v₀]
  simp
/-- Right bimodule property of `quotientExpect` over `quotientStrandIncl`. -/
@[simp] theorem quotientExpect_mul_right {n : ℕ} (y : htr.Quotient (n + 1)) (x : htr.Quotient n) :
    htr.quotientExpect hδ n (y * htr.quotientStrandIncl n x) = htr.quotientExpect hδ n y * x := by
  dsimp [quotientExpect, jonesEquiv]
  rw [map_mul,
    htr.quotientPathAlgebraEquiv_quotientStrandIncl (jonesModel hδ).G (jonesModel hδ).v₀]
  simp
/-- `quotientExpect` is a left inverse to `quotientStrandIncl`. -/
@[simp] theorem quotientExpect_quotientStrandIncl {n : ℕ} (x : htr.Quotient n) :
    htr.quotientExpect hδ n (htr.quotientStrandIncl n x) = x := by
  simpa using htr.quotientExpect_mul_left hδ x 1
/-- Trace compatibility of `quotientExpect` with the unnormalized
`quotientStarPositiveFunctional`. -/
@[simp] theorem quotientStarPositiveFunctional_quotientExpect {n : ℕ} (y : htr.Quotient (n + 1)) :
    htr.quotientStarPositiveFunctional hδ n (htr.quotientExpect hδ n y) =
      (δ : ℂ)⁻¹ * htr.quotientStarPositiveFunctional hδ (n + 1) y := by
  let M := jonesModel hδ
  have hw {k} (z : htr.Quotient k) := (htr.quotientStarPositiveFunctional_apply hδ k z).trans
    (htr.pathAlgebraTrace_quotientPathAlgebraEquiv M.G M.v₀ M.hr M.hrs M.hδ M.hf M.hf₀
      M.hadj z).symm
  rw [hw, hw]; simp [-pathAlgebraTrace_quotientPathAlgebraEquiv, quotientExpect, jonesEquiv, M,
    pathAlgebraTrace_pathAlgebraExpect M.hr]
/-- Algebraic positivity: `quotientExpect (star y * y)` is a finite sum of squares. -/
theorem exists_sum_star_mul_self_quotientExpect_star_mul_self {n : ℕ} (y : htr.Quotient (n + 1)) :
    ∃ (m : ℕ) (z : Fin m → htr.Quotient n),
      htr.quotientExpect hδ n (star y * y) = ∑ i : Fin m, star (z i) * z i := by
  obtain ⟨m, Z, hZ⟩ := exists_sum_star_mul_self_pathAlgebraExpect_star_mul_self (jonesModel hδ).hrs
    (pos_of_mem_jonesLoopParameters hδ) (htr.jonesEquiv hδ (n + 1) y)
  exact ⟨m, fun i ↦ (htr.jonesEquiv hδ n).symm (Z i), by
    simp [quotientExpect, hZ, map_sum, map_mul, StarHomClass.map_star]⟩
/-- **Uniqueness of `quotientExpect`**: left `quotientStrandIncl`-module maps compatible with the
trace agree with `quotientExpect`. -/
theorem quotientExpect_unique {n : ℕ} (F : htr.Quotient (n + 1) →ₗ[ℂ] htr.Quotient n)
    (hmul : ∀ x y, F (htr.quotientStrandIncl n x * y) = x * F y)
    (htrace : ∀ y, htr.quotientStarPositiveFunctional hδ n (F y) =
      (δ : ℂ)⁻¹ * htr.quotientStarPositiveFunctional hδ (n + 1) y) :
    F = htr.quotientExpect hδ n :=
  LinearMap.ext fun _ ↦ htr.eq_of_forall_quotientStarPositiveFunctional_mul_eq hδ fun _ ↦ by
    rw [← hmul, ← htr.quotientExpect_mul_left, htrace,
      htr.quotientStarPositiveFunctional_quotientExpect]
/-- `quotientPathAlgebraEquiv` intertwines `quotientExpect` with `pathAlgebraExpect` for every graph
model at an admissible loop parameter. -/
theorem quotientPathAlgebraEquiv_quotientExpect {V : Type*} (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] [G.LocallyFinite] (v₀ : V) {r : V → ℂ} (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v))
    (hGδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = (δ : ℂ) * r v ^ 2) {f : V → ℕ}
    (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) {n : ℕ}
    (y : htr.Quotient (n + 1)) :
    htr.quotientPathAlgebraEquiv G v₀ hr hrs hGδ hf hf₀ hadj n (htr.quotientExpect hδ n y) =
      pathAlgebraExpect G v₀ r (δ : ℂ)
        (htr.quotientPathAlgebraEquiv G v₀ hr hrs hGδ hf hf₀ hadj (n + 1) y) := by
  let e := fun k ↦ htr.quotientPathAlgebraEquiv G v₀ hr hrs hGδ hf hf₀ hadj k
  let F : htr.Quotient (n + 1) →ₗ[ℂ] htr.Quotient n :=
    (e n).symm.toAlgEquiv.toLinearMap.comp
      ((pathAlgebraExpect G v₀ r (δ : ℂ)).comp (e (n + 1)).toAlgEquiv.toLinearMap)
  have hF : F = htr.quotientExpect hδ n := htr.quotientExpect_unique hδ F
    (fun x z ↦ by
      dsimp [F, e]
      rw [map_mul, htr.quotientPathAlgebraEquiv_quotientStrandIncl G v₀ hr hrs hGδ hf hf₀ hadj,
        pathAlgebraExpect_pathAlgebraExtend_mul, map_mul, StarAlgEquiv.symm_apply_apply])
    fun z ↦ by
      have hw {k} (w : htr.Quotient k) := (htr.quotientStarPositiveFunctional_apply hδ k w).trans
        (htr.pathAlgebraTrace_quotientPathAlgebraEquiv G v₀ hr hrs hGδ hf hf₀ hadj w).symm
      rw [hw, hw]
      simp [F, e, -pathAlgebraTrace_quotientPathAlgebraEquiv, pathAlgebraTrace_pathAlgebraExpect hr]
  simpa [F, e] using congrArg (fun g ↦ e n (g y)) hF.symm
/-- On the discrete `A_(m-1)` path algebra, `quotientExpect` computes as `pathAlgebraExpect`. -/
theorem discreteQuotientEquiv_quotientExpect {m : ℕ} (hm : 2 ≤ m)
    (hmδ : δ = 2 * cos (π / m)) {n : ℕ} (y : htr.Quotient (n + 1)) :
    htr.discreteQuotientEquiv hm hmδ n (htr.quotientExpect hδ n y) =
      pathAlgebraExpect (pathGraph (m - 1)) ⟨0, Nat.sub_pos_of_lt (by omega)⟩
        (discretePathWeight m) (δ : ℂ) (htr.discreteQuotientEquiv hm hmδ (n + 1) y) :=
  htr.quotientPathAlgebraEquiv_quotientExpect hδ (pathGraph (m - 1))
    ⟨0, Nat.sub_pos_of_lt (by omega)⟩ discretePathWeight_ne_zero
    (isSelfAdjoint_discretePathWeight m)
    (fun v ↦ by rw [hmδ]; exact sum_neighborFinset_discretePathWeight_sq v)
    Fin.val_injective rfl (fun h ↦ pathGraph_adj.1 h) y
/-- On the generic `A_∞` path algebra, `quotientExpect` computes as `pathAlgebraExpect`. -/
theorem genericQuotientEquiv_quotientExpect (hδ2 : 2 ≤ δ) {n : ℕ} (y : htr.Quotient (n + 1)) :
    htr.genericQuotientEquiv hδ2 n (htr.quotientExpect hδ n y) =
      pathAlgebraExpect (hasse ℕ) 0 (genericPathWeight δ) (δ : ℂ)
        (htr.genericQuotientEquiv hδ2 (n + 1) y) :=
  htr.quotientPathAlgebraEquiv_quotientExpect hδ (hasse ℕ) 0
    (genericPathWeight_ne_zero hδ2) (isSelfAdjoint_genericPathWeight δ)
    (sum_neighborFinset_genericPathWeight_sq hδ2) Function.injective_id rfl
    (fun h ↦ hasse_nat_adj.1 h) y
/-- The conditional expectation sends the last Temperley–Lieb generator to `δ⁻¹ • 1`. -/
@[simp] theorem quotientExpect_mk_e_last (n : ℕ) : htr.quotientExpect hδ (n + 1)
      (Ideal.Quotient.mk (htr.traceRadical (n + 2)) (e (δ : ℂ) (Fin.last n))) = (δ : ℂ)⁻¹ • 1 :=
  htr.eq_of_forall_quotientStarPositiveFunctional_mul_eq hδ fun x ↦ by
    obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← htr.quotientExpect_mul_left]; simp [← map_mul, htr.map_strandIncl_mul_e_last]
/-- Conditional expectation of the Jones projection `p_n` is `(δ⁻¹ ^ 2) • 1` (inverse index). -/
@[simp] theorem quotientExpect_jonesProjection (n : ℕ) :
    htr.quotientExpect hδ (n + 1) (htr.jonesProjection (pos_of_mem_jonesLoopParameters hδ).ne' n) =
      ((δ : ℂ)⁻¹ ^ 2) • 1 := by
  rw [jonesProjection, map_smul, htr.quotientExpect_mk_e_last, smul_smul, sq]
/-- Unnormalized Markov property: multiplying by `jonesProjection` scales the trace by `δ⁻¹`. -/
@[simp] theorem quotientStarPositiveFunctional_quotientStrandIncl_mul_jonesProjection {n : ℕ}
    (x : htr.Quotient (n + 1)) : htr.quotientStarPositiveFunctional hδ (n + 2)
      (htr.quotientStrandIncl (n + 1) x *
        htr.jonesProjection (pos_of_mem_jonesLoopParameters hδ).ne' n) =
      (δ : ℂ)⁻¹ * htr.quotientStarPositiveFunctional hδ (n + 1) x := by
  obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [jonesProjection, ← map_mul, htr.map_strandIncl_mul_e_last]
/-- **Jones compression identity:** sandwiching `quotientStrandIncl (n + 1) x` between copies of
`jonesProjection _ n` projects it onto `quotientExpect hδ n x`. -/
theorem jonesProjection_mul_quotientStrandIncl_mul_jonesProjection {n : ℕ}
    (x : htr.Quotient (n + 1)) :
    htr.jonesProjection (pos_of_mem_jonesLoopParameters hδ).ne' n *
        htr.quotientStrandIncl (n + 1) x *
        htr.jonesProjection (pos_of_mem_jonesLoopParameters hδ).ne' n =
      htr.quotientStrandIncl (n + 1) (htr.quotientStrandIncl n (htr.quotientExpect hδ n x)) *
        htr.jonesProjection (pos_of_mem_jonesLoopParameters hδ).ne' n := by
  let hδ0 := (pos_of_mem_jonesLoopParameters hδ).ne'
  let p := htr.jonesProjection hδ0 n
  have hp2 : p * p = p := (htr.isIdempotentElem_jonesProjection hδ0 n).eq
  have hcomm (z : htr.Quotient n) :
      Commute (htr.quotientStrandIncl (n + 1) (htr.quotientStrandIncl n z)) p := by
    obtain ⟨z₀, rfl⟩ := Ideal.Quotient.mk_surjective z
    cases n with
    | zero =>
      rw [htr.quotientStrandIncl_zero_mk, AlgHom.commutes]
      exact Algebra.commute_algebraMap_left _ _
    | succ m =>
      rw [htr.quotientStrandIncl_mk, htr.quotientStrandIncl_mk, strandInclAll_succ,
        strandInclAll_succ]
      simp only [p, jonesProjection, ← Ideal.Quotient.mkₐ_eq_mk ℂ, Commute, SemiconjBy,
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← map_mul,
        ← (commute_e_last_strandIncl_strandIncl z₀).eq]
  obtain ⟨y, hy⟩ : ∃ y : htr.Quotient n,
      p * htr.quotientStrandIncl (n + 1) x * p =
        htr.quotientStrandIncl (n + 1) (htr.quotientStrandIncl n y) * p := by
    obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
    cases n with
    | zero =>
      have hx₀ : x₀ = algebraMap ℂ (TemperleyLieb ℂ (δ : ℂ) 1) (aug x₀) := by
        have h := ((algEquivOfLeOne (δ : ℂ) (n := 1) le_rfl).symm_apply_apply x₀).symm
        rwa [algEquivOfLeOne_apply, algEquivOfLeOne_symm_apply] at h
      refine ⟨algebraMap ℂ (htr.Quotient 0) (aug x₀), ?_⟩
      simp only [AlgHom.commutes]
      conv_lhs => rw [hx₀]
      rw [Ideal.Quotient.mk_algebraMap, AlgHom.commutes]
      simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
        one_mul, hp2]
    | succ m =>
      obtain ⟨y₀, hy₀⟩ := exists_e_last_mul_strandIncl_mul_e_last_eq x₀
      refine ⟨(δ : ℂ)⁻¹ • Ideal.Quotient.mk (htr.traceRadical (m + 1)) y₀, ?_⟩
      have hmk := congrArg (Ideal.Quotient.mkₐ ℂ (htr.traceRadical (m + 3))) hy₀
      simp only [map_mul, Ideal.Quotient.mkₐ_eq_mk] at hmk
      simp only [map_smul, htr.quotientStrandIncl_mk, strandInclAll_succ, p, jonesProjection,
        smul_mul_assoc, mul_smul_comm, hmk, smul_smul]
  have hy_eq : y = htr.quotientExpect hδ n x := by
    refine htr.eq_of_forall_quotientStarPositiveFunctional_mul_eq hδ fun z ↦ ?_
    have hz_rhs :
        htr.quotientStarPositiveFunctional hδ (n + 2)
          (htr.quotientStrandIncl (n + 1) (htr.quotientStrandIncl n z) *
            (htr.quotientStrandIncl (n + 1) (htr.quotientStrandIncl n y) * p)) =
          htr.quotientStarPositiveFunctional hδ n (z * y) := by
      have hδne : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ0
      rw [← mul_assoc, ← map_mul, ← map_mul,
        htr.quotientStarPositiveFunctional_quotientStrandIncl_mul_jonesProjection,
        htr.quotientStarPositiveFunctional_quotientStrandIncl, ← mul_assoc,
        inv_mul_cancel₀ hδne, one_mul]
    have hz_lhs :
        htr.quotientStarPositiveFunctional hδ (n + 2)
          (htr.quotientStrandIncl (n + 1) (htr.quotientStrandIncl n z) *
            (p * htr.quotientStrandIncl (n + 1) x * p)) =
          htr.quotientStarPositiveFunctional hδ n (z * htr.quotientExpect hδ n x) := by
      rw [← mul_assoc, ← mul_assoc, (hcomm z).eq, mul_assoc, mul_assoc,
        htr.quotientStarPositiveFunctional_mul_comm, mul_assoc, mul_assoc, hp2, ← mul_assoc,
        ← map_mul, htr.quotientStarPositiveFunctional_quotientStrandIncl_mul_jonesProjection,
        ← htr.quotientStarPositiveFunctional_quotientExpect, htr.quotientExpect_mul_left]
    rw [← hz_rhs, ← hy, hz_lhs]
  rw [hy, hy_eq]
/-- `quotientExpect` preserves `normalizedQuotientTrace`. -/
@[simp] theorem normalizedQuotientTrace_quotientExpect {n : ℕ} (y : htr.Quotient (n + 1)) :
    htr.normalizedQuotientTrace hδ n (htr.quotientExpect hδ n y) =
      htr.normalizedQuotientTrace hδ (n + 1) y := by
  rw [normalizedQuotientTrace_apply, htr.quotientStarPositiveFunctional_quotientExpect,
    normalizedQuotientTrace_apply, pow_succ]; ring
/-- Normalized Markov property: multiplying by `p_n` scales the tracial state by `δ⁻¹ ^ 2`. -/
@[simp] theorem normalizedQuotientTrace_quotientStrandIncl_mul_jonesProjection {n : ℕ}
    (x : htr.Quotient (n + 1)) : htr.normalizedQuotientTrace hδ (n + 2)
      (htr.quotientStrandIncl (n + 1) x *
        htr.jonesProjection (pos_of_mem_jonesLoopParameters hδ).ne' n) =
      (δ : ℂ)⁻¹ ^ 2 * htr.normalizedQuotientTrace hδ (n + 1) x := by
  rw [normalizedQuotientTrace_apply,
    htr.quotientStarPositiveFunctional_quotientStrandIncl_mul_jonesProjection,
    normalizedQuotientTrace_apply, pow_succ]; ring
end JonesTower
section CStarTower
variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
/-- The GNS C⋆-algebra structure on `htr.Quotient n` (`δ ∈ jonesLoopParameters`). -/
@[expose, implicit_reducible]
def cstarAlgebraQuotient (hδ : δ ∈ jonesLoopParameters) (n : ℕ) : CStarAlgebra (htr.Quotient n) :=
  (htr.quotientStarPositiveFunctional hδ n).cstarAlgebra
    (htr.nullSubmodule_quotientStarPositiveFunctional hδ n)
variable [hδ : Fact (δ ∈ jonesLoopParameters)]
/-- The GNS C⋆-algebra instance on `htr.Quotient n` using the GNS C⋆-norm of
`quotientStarPositiveFunctional`, activated by `Fact (δ ∈ jonesLoopParameters)`. -/
noncomputable instance instCStarAlgebraQuotient (n : ℕ) : CStarAlgebra (htr.Quotient n) :=
  htr.cstarAlgebraQuotient hδ.out n
/-- The `CStarAlgebra.spectralOrder` partial order on `htr.Quotient n`, activated by
`Fact (δ ∈ jonesLoopParameters)`. -/
noncomputable instance instPartialOrderQuotient (n : ℕ) : PartialOrder (htr.Quotient n) :=
  CStarAlgebra.spectralOrder (htr.Quotient n)
/-- The `CStarAlgebra.spectralOrderedRing` star-ordered-ring instance on `htr.Quotient n`,
activated by `Fact (δ ∈ jonesLoopParameters)`. -/
instance instStarOrderedRingQuotient (n : ℕ) : StarOrderedRing (htr.Quotient n) :=
  CStarAlgebra.spectralOrderedRing (htr.Quotient n)
/-- Each tower inclusion `quotientStrandIncl` is an isometry for the GNS C⋆-norms. -/
theorem isometry_quotientStrandIncl (n : ℕ) : Isometry (htr.quotientStrandIncl n) := by
  rw [show ⇑(htr.quotientStrandIncl n) = ⇑(htr.quotientStrandStarAlgHom n) from
    funext fun _ ↦ (htr.quotientStrandStarAlgHom_apply n _).symm]
  exact NonUnitalStarAlgHom.isometry (htr.quotientStrandStarAlgHom n) fun _ _ h ↦
    htr.quotientStrandIncl_injective n
      (fun _ ↦ (isUnit_of_mem_jonesLoopParameters hδ.out).mul_right_injective) (by simpa using h)
/-- Each tower inclusion `quotientStrandIncl` preserves the GNS C⋆-norm. -/
@[simp] theorem norm_quotientStrandIncl (n : ℕ) (x : htr.Quotient n) :
    ‖htr.quotientStrandIncl n x‖ = ‖x‖ := by
  simpa [dist_zero_right] using (htr.isometry_quotientStrandIncl n).dist_eq x 0
/-- `quotientExpect` preserves positivity in the C⋆-algebra spectral order. -/
theorem quotientExpect_nonneg {n : ℕ} {y : htr.Quotient (n + 1)} (hy : 0 ≤ y) :
    0 ≤ htr.quotientExpect hδ.out n y := by
  let _ : NonUnitalContinuousFunctionalCalculus ℝ (htr.Quotient (n + 1)) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let _ : NonnegSpectrumClass ℝ (htr.Quotient (n + 1)) := CStarAlgebra.instNonnegSpectrumClass'
  obtain ⟨r, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hy
  obtain ⟨_, z, hz⟩ := htr.exists_sum_star_mul_self_quotientExpect_star_mul_self hδ.out r
  rw [hz]; exact Finset.sum_nonneg fun i _ ↦ star_mul_self_nonneg (z i)
/-- **C⋆-conditional expectation on the positive Jones quotient tower.** -/
def cstarConditionalExpectation (n : ℕ) :
    CStarConditionalExpectation (htr.quotientStrandStarAlgHom n) where
  toPositiveLinearMap := .mk₀ (htr.quotientExpect hδ.out n) fun _ hy ↦ htr.quotientExpect_nonneg hy
  map_one' := htr.quotientExpect_one hδ.out n
  map_mul_left' a b := by
    rw [quotientStrandStarAlgHom_apply]; exact htr.quotientExpect_mul_left hδ.out a b
  map_mul_right' a b := by
    rw [quotientStrandStarAlgHom_apply]; exact htr.quotientExpect_mul_right hδ.out a b
/-- Evaluating `cstarConditionalExpectation` agrees with `quotientExpect`. -/
@[simp] theorem cstarConditionalExpectation_apply (n : ℕ) (y : htr.Quotient (n + 1)) :
    cstarConditionalExpectation htr n y = htr.quotientExpect hδ.out n y := (rfl)
end CStarTower
end IsMarkovTrace
end TauCeti.TemperleyLieb

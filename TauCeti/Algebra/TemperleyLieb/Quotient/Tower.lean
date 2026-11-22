/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Algebra.TemperleyLieb.Quotient.Positivity
public import TauCeti.Analysis.CStarAlgebra.ConditionalExpectation.CompletelyPositive
public import TauCeti.Analysis.StarAlgebra.GNS.FiniteDimensional
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
/-! # The C⋆-tower of positive Jones quotients and its conditional expectations

For `δ ∈ jonesLoopParameters`, `htr.Quotient n` forms a unital C⋆-algebra tower equipped with
faithful tracial states (`normalizedQuotientTrace`), isometric `⋆`-inclusions (`jonesStrandIncl`),
Jones projections (`jonesProjection`), and unique trace-compatible completely positive conditional
expectations (`quotientExpect`, `cstarConditionalExpectation`).

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
/-- Every admissible Jones loop parameter is a unit in `ℂ`. -/
theorem isUnit_of_mem_jonesLoopParameters {δ : ℝ} (hδ : δ ∈ jonesLoopParameters) :
    IsUnit (δ : ℂ) := (Complex.ofReal_ne_zero.2 (pos_of_mem_jonesLoopParameters hδ).ne').isUnit
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
/-- The **Jones projection** `p_n = δ⁻¹ • mk (e δ (Fin.last n))` in `htr.Quotient (n + 2)`. -/
def jonesProjection (n : ℕ) : htr.Quotient (n + 2) :=
  (δ : ℂ)⁻¹ • Ideal.Quotient.mk (htr.traceRadical (n + 2)) (e (δ : ℂ) (Fin.last n))
/-- Every Jones projection is self-adjoint. -/
theorem isSelfAdjoint_jonesProjection (n : ℕ) : IsSelfAdjoint (htr.jonesProjection n) := by
  rw [IsSelfAdjoint, jonesProjection, star_smul, Ideal.Quotient.star_mk, star_e, star_inv₀,
    IsSelfAdjoint.star_eq (Complex.conj_ofReal _)]
omit [Fact (IsSelfAdjoint (δ : ℂ))] in
/-- For `δ ≠ 0`, every Jones projection is idempotent. -/
theorem isIdempotentElem_jonesProjection (hδ : δ ≠ 0) (n : ℕ) :
    IsIdempotentElem (htr.jonesProjection n) := by
  rw [IsIdempotentElem, jonesProjection, ← Ideal.Quotient.mkₐ_eq_mk ℂ, smul_mul_smul_comm,
    ← map_mul, e_mul_self, map_smul, smul_smul, mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 hδ), mul_one]
variable (hδ : δ ∈ jonesLoopParameters)
/-- `positiveQuotientTrace` agrees with the algebraic `quotientTrace` of `tr n`. -/
theorem positiveQuotientTrace_eq_quotientTrace (n : ℕ) (x : htr.Quotient n) :
    htr.positiveQuotientTrace hδ n x = (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (htr.positiveQuotientTrace_mk hδ _).trans (LinearMap.quotientTrace_mk _ _ _).symm
private theorem eq_of_forall_positiveQuotientTrace_mul_eq {n : ℕ} {a b : htr.Quotient n}
    (h : ∀ x, htr.positiveQuotientTrace hδ n (x * a) = htr.positiveQuotientTrace hδ n (x * b)) :
    a = b := by
  have hmem : a - b ∈ (htr.positiveQuotientTrace hδ n).nullSubmodule :=
    ((htr.positiveQuotientTrace hδ n).mem_nullSubmodule_iff_apply_star_mul_self_eq_zero _).2 <| by
      rw [mul_sub, map_sub, h, sub_self]
  rwa [htr.nullSubmodule_positiveQuotientTrace hδ n, Submodule.mem_bot, sub_eq_zero] at hmem
/-- Unital `⋆`-algebra strand map `htr.Quotient n →⋆ₐ[ℂ] htr.Quotient (n + 1)` (`n ≥ 0`),
which is an inclusion at every successor level and at level `0` whenever `δ ≠ 0` (in particular,
for every `δ ∈ jonesLoopParameters`). -/
def jonesStrandIncl (n : ℕ) : htr.Quotient n →⋆ₐ[ℂ] htr.Quotient (n + 1) :=
  htr.quotientStrandStarAlgHom n
@[simp] theorem jonesStrandIncl_mk (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.jonesStrandIncl n (Ideal.Quotient.mk (htr.traceRadical n) x) =
      Ideal.Quotient.mk (htr.traceRadical (n + 1)) (strandInclAll n x) :=
  htr.quotientStrandStarAlgHom_mk n x
include hδ in
/-- For `δ ∈ jonesLoopParameters`, each tower strand map `jonesStrandIncl` is injective. -/
theorem jonesStrandIncl_injective (n : ℕ) : Function.Injective (htr.jonesStrandIncl n) :=
  htr.quotientStrandStarAlgHom_injective n fun _ ↦
    (isUnit_of_mem_jonesLoopParameters hδ).mul_right_injective
/-- `jonesStrandIncl` scales the unnormalized `positiveQuotientTrace` by `δ`. -/
@[simp] theorem positiveQuotientTrace_jonesStrandIncl (n : ℕ) (x : htr.Quotient n) :
    htr.positiveQuotientTrace hδ (n + 1) (htr.jonesStrandIncl n x) =
      (δ : ℂ) * htr.positiveQuotientTrace hδ n x := by
  obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective x; simp [htr.map_strandInclAll]
private abbrev jonesEquiv (n : ℕ) :=
  let M := jonesModel hδ
  htr.quotientPathAlgebraEquiv M.G M.v₀ M.hr M.hrs M.hδ M.hf M.hf₀ M.hadj n
private theorem jonesEquiv_jonesStrandIncl {n : ℕ} (x : htr.Quotient n) :
    htr.jonesEquiv hδ (n + 1) (htr.jonesStrandIncl n x) =
      walkExtend (jonesModel hδ).G (jonesModel hδ).v₀ (htr.jonesEquiv hδ n x) :=
  htr.quotientPathAlgebraEquiv_quotientStrandStarAlgHom _ _ _ _ _ _ _ _ n x
/-- **Trace-preserving conditional expectation on positive Jones quotients**. -/
def quotientExpect (n : ℕ) : htr.Quotient (n + 1) →ₗ[ℂ] htr.Quotient n :=
  let M := jonesModel hδ
  (htr.jonesEquiv hδ n).symm.toAlgEquiv.toLinearMap.comp <|
    (walkExpect M.G M.v₀ M.r (δ : ℂ)).comp (htr.jonesEquiv hδ (n + 1)).toAlgEquiv.toLinearMap
/-- `quotientExpect` is unital. -/
@[simp] theorem quotientExpect_one (n : ℕ) : htr.quotientExpect hδ n 1 = 1 := by
  simp [quotientExpect, walkExpect_one (jonesModel hδ).hr
    (isUnit_of_mem_jonesLoopParameters hδ).ne_zero (jonesModel hδ).hδ]
/-- Left bimodule property of `quotientExpect` over `jonesStrandIncl`. -/
@[simp] theorem quotientExpect_mul_left {n : ℕ} (x : htr.Quotient n) (y : htr.Quotient (n + 1)) :
    htr.quotientExpect hδ n (htr.jonesStrandIncl n x * y) = x * htr.quotientExpect hδ n y := by
  simp [quotientExpect, jonesEquiv_jonesStrandIncl]
/-- Right bimodule property of `quotientExpect` over `jonesStrandIncl`. -/
@[simp] theorem quotientExpect_mul_right {n : ℕ} (y : htr.Quotient (n + 1)) (x : htr.Quotient n) :
    htr.quotientExpect hδ n (y * htr.jonesStrandIncl n x) = htr.quotientExpect hδ n y * x := by
  simp [quotientExpect, jonesEquiv_jonesStrandIncl]
/-- `quotientExpect` is a left inverse to `jonesStrandIncl`. -/
@[simp] theorem quotientExpect_jonesStrandIncl {n : ℕ} (x : htr.Quotient n) :
    htr.quotientExpect hδ n (htr.jonesStrandIncl n x) = x := by
  simpa using htr.quotientExpect_mul_left hδ x 1
/-- Trace compatibility of `quotientExpect` with the unnormalized `positiveQuotientTrace`. -/
@[simp] theorem positiveQuotientTrace_quotientExpect {n : ℕ} (y : htr.Quotient (n + 1)) :
    htr.positiveQuotientTrace hδ n (htr.quotientExpect hδ n y) =
      (δ : ℂ)⁻¹ * htr.positiveQuotientTrace hδ (n + 1) y := by
  let M := jonesModel hδ
  have hw {k} (z : htr.Quotient k) := (htr.positiveQuotientTrace_eq_quotientTrace hδ k z).trans
    (htr.walkTrace_quotientPathAlgebraEquiv M.G M.v₀ M.hr M.hrs M.hδ M.hf M.hf₀ M.hadj z).symm
  rw [hw, hw]; simp [-walkTrace_quotientPathAlgebraEquiv, quotientExpect, jonesEquiv, M,
    walkTrace_walkExpect M.hr]
/-- Algebraic positivity: `quotientExpect (star y * y)` is a finite sum of squares. -/
theorem exists_sum_star_mul_self_quotientExpect_star_mul_self {n : ℕ} (y : htr.Quotient (n + 1)) :
    ∃ (m : ℕ) (z : Fin m → htr.Quotient n),
      htr.quotientExpect hδ n (star y * y) = ∑ i : Fin m, star (z i) * z i := by
  obtain ⟨m, Z, hZ⟩ := exists_sum_star_mul_self_walkExpect_star_mul_self (jonesModel hδ).hrs
    (pos_of_mem_jonesLoopParameters hδ) (htr.jonesEquiv hδ (n + 1) y)
  exact ⟨m, fun i ↦ (htr.jonesEquiv hδ n).symm (Z i), by
    simp [quotientExpect, hZ, map_sum, map_mul, StarHomClass.map_star]⟩
/-- **Uniqueness of `quotientExpect`**: left `jonesStrandIncl`-module maps compatible with the trace
agree with `quotientExpect`. -/
theorem quotientExpect_unique {n : ℕ} (F : htr.Quotient (n + 1) →ₗ[ℂ] htr.Quotient n)
    (hmul : ∀ x y, F (htr.jonesStrandIncl n x * y) = x * F y)
    (htrace : ∀ y, htr.positiveQuotientTrace hδ n (F y) =
      (δ : ℂ)⁻¹ * htr.positiveQuotientTrace hδ (n + 1) y) : F = htr.quotientExpect hδ n :=
  LinearMap.ext fun _ ↦ htr.eq_of_forall_positiveQuotientTrace_mul_eq hδ fun _ ↦ by
    rw [← hmul, ← htr.quotientExpect_mul_left, htrace, htr.positiveQuotientTrace_quotientExpect]
/-- The conditional expectation sends the last Temperley–Lieb generator to `δ⁻¹ • 1`. -/
@[simp] theorem quotientExpect_mk_e_last (n : ℕ) : htr.quotientExpect hδ (n + 1)
      (Ideal.Quotient.mk (htr.traceRadical (n + 2)) (e (δ : ℂ) (Fin.last n))) = (δ : ℂ)⁻¹ • 1 :=
  htr.eq_of_forall_positiveQuotientTrace_mul_eq hδ fun x ↦ by
    obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← htr.quotientExpect_mul_left]; simp [← map_mul, htr.map_strandIncl_mul_e_last]
/-- Conditional expectation of the last generator sandwiched between included elements. -/
theorem quotientExpect_mul_mk_e_last_mul {n : ℕ} (a b : htr.Quotient (n + 1)) :
    htr.quotientExpect hδ (n + 1) (htr.jonesStrandIncl (n + 1) a *
      Ideal.Quotient.mk (htr.traceRadical (n + 2)) (e (δ : ℂ) (Fin.last n)) *
      htr.jonesStrandIncl (n + 1) b) = (δ : ℂ)⁻¹ • (a * b) := by
  simp
/-- Conditional expectation of the Jones projection `p_n` is `(δ⁻¹ ^ 2) • 1` (inverse index). -/
@[simp] theorem quotientExpect_jonesProjection (n : ℕ) :
    htr.quotientExpect hδ (n + 1) (htr.jonesProjection n) = ((δ : ℂ)⁻¹ ^ 2) • 1 := by
  rw [jonesProjection, map_smul, htr.quotientExpect_mk_e_last, smul_smul, sq]
/-- Unnormalized Markov property: multiplying by `jonesProjection n` scales the trace by `δ⁻¹`. -/
@[simp] theorem positiveQuotientTrace_jonesStrandIncl_mul_jonesProjection {n : ℕ}
    (x : htr.Quotient (n + 1)) : htr.positiveQuotientTrace hδ (n + 2)
      (htr.jonesStrandIncl (n + 1) x * htr.jonesProjection n) =
      (δ : ℂ)⁻¹ * htr.positiveQuotientTrace hδ (n + 1) x := by
  obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [jonesProjection, ← map_mul, htr.map_strandIncl_mul_e_last]
/-- The **normalized faithful positive trace** `δ⁻ⁿ • positiveQuotientTrace` on `htr.Quotient n`. -/
def normalizedQuotientTrace (n : ℕ) : StarPositiveFunctional (htr.Quotient n) where
  toLinearMap := ((δ : ℂ)⁻¹ ^ n) • (htr.positiveQuotientTrace hδ n).toLinearMap
  square_nonneg x := by
    rw [LinearMap.smul_apply, smul_eq_mul, ← Complex.ofReal_inv, ← Complex.ofReal_pow]
    exact mul_nonneg (Complex.zero_le_real.2 (pow_nonneg (inv_nonneg.2
      (pos_of_mem_jonesLoopParameters hδ).le) n)) ((htr.positiveQuotientTrace hδ n).square_nonneg x)
theorem normalizedQuotientTrace_apply {n : ℕ} (x : htr.Quotient n) :
    htr.normalizedQuotientTrace hδ n x = (δ : ℂ)⁻¹ ^ n * htr.positiveQuotientTrace hδ n x := (rfl)
/-- `normalizedQuotientTrace` is a state: it sends `1` to `1`. -/
@[simp] theorem normalizedQuotientTrace_one (n : ℕ) : htr.normalizedQuotientTrace hδ n 1 = 1 := by
  rw [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_one, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero n (isUnit_of_mem_jonesLoopParameters hδ).ne_zero)]
/-- `normalizedQuotientTrace` is tracial on `htr.Quotient n`. -/
theorem normalizedQuotientTrace_mul_comm {n : ℕ} (x y : htr.Quotient n) :
    htr.normalizedQuotientTrace hδ n (x * y) = htr.normalizedQuotientTrace hδ n (y * x) := by
  simp only [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_mul_comm]
/-- `normalizedQuotientTrace` is faithful on `htr.Quotient n`. -/
@[simp] theorem nullSubmodule_normalizedQuotientTrace (n : ℕ) :
    (htr.normalizedQuotientTrace hδ n).nullSubmodule = ⊥ := by
  ext; simp [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    normalizedQuotientTrace_apply, (isUnit_of_mem_jonesLoopParameters hδ).ne_zero,
    ← StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero
      (htr.positiveQuotientTrace hδ n), htr.nullSubmodule_positiveQuotientTrace hδ n]
/-- `normalizedQuotientTrace` is invariant along the tower inclusions `jonesStrandIncl`. -/
@[simp] theorem normalizedQuotientTrace_jonesStrandIncl {n : ℕ} (x : htr.Quotient n) :
    htr.normalizedQuotientTrace hδ (n + 1) (htr.jonesStrandIncl n x) =
      htr.normalizedQuotientTrace hδ n x := by
  have := (isUnit_of_mem_jonesLoopParameters hδ).ne_zero
  rw [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_jonesStrandIncl,
    normalizedQuotientTrace_apply, pow_succ]; field_simp
/-- `quotientExpect` preserves `normalizedQuotientTrace`. -/
@[simp] theorem normalizedQuotientTrace_quotientExpect {n : ℕ} (y : htr.Quotient (n + 1)) :
    htr.normalizedQuotientTrace hδ n (htr.quotientExpect hδ n y) =
      htr.normalizedQuotientTrace hδ (n + 1) y := by
  rw [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_quotientExpect,
    normalizedQuotientTrace_apply, pow_succ]; ring
/-- Normalized Markov property: multiplying by `p_n` scales the tracial state by `δ⁻¹ ^ 2`. -/
@[simp] theorem normalizedQuotientTrace_jonesStrandIncl_mul_jonesProjection {n : ℕ}
    (x : htr.Quotient (n + 1)) : htr.normalizedQuotientTrace hδ (n + 2)
      (htr.jonesStrandIncl (n + 1) x * htr.jonesProjection n) =
      (δ : ℂ)⁻¹ ^ 2 * htr.normalizedQuotientTrace hδ (n + 1) x := by
  rw [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_jonesStrandIncl_mul_jonesProjection,
    normalizedQuotientTrace_apply, pow_succ]; ring
end JonesTower
section CStarTower
variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
/-- The GNS C⋆-algebra structure on `htr.Quotient n` (`δ ∈ jonesLoopParameters`). -/
@[expose, implicit_reducible]
def cstarAlgebraQuotient (hδ : δ ∈ jonesLoopParameters) (n : ℕ) : CStarAlgebra (htr.Quotient n) :=
  letI := htr.finiteDimensional_quotient hδ n
  (htr.positiveQuotientTrace hδ n).cstarAlgebra (htr.nullSubmodule_positiveQuotientTrace hδ n)
variable [hδ : Fact (δ ∈ jonesLoopParameters)]
instance instFiniteDimensionalQuotient (n : ℕ) : FiniteDimensional ℂ (htr.Quotient n) :=
  htr.finiteDimensional_quotient hδ.out n
noncomputable instance instCStarAlgebraQuotient (n : ℕ) : CStarAlgebra (htr.Quotient n) :=
  htr.cstarAlgebraQuotient hδ.out n
noncomputable instance instPartialOrderQuotient (n : ℕ) : PartialOrder (htr.Quotient n) :=
  CStarAlgebra.spectralOrder (htr.Quotient n)
instance instStarOrderedRingQuotient (n : ℕ) : StarOrderedRing (htr.Quotient n) :=
  CStarAlgebra.spectralOrderedRing (htr.Quotient n)
/-- Each tower inclusion `jonesStrandIncl` is an isometry for the GNS C⋆-norms. -/
theorem isometry_jonesStrandIncl (n : ℕ) : Isometry (htr.jonesStrandIncl n) :=
  NonUnitalStarAlgHom.isometry _ (htr.jonesStrandIncl_injective hδ.out n)
/-- Each tower inclusion `jonesStrandIncl` preserves the GNS C⋆-norm. -/
theorem norm_jonesStrandIncl (n : ℕ) (x : htr.Quotient n) :
    ‖htr.jonesStrandIncl n x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map _ (htr.jonesStrandIncl_injective hδ.out n) x
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
def cstarConditionalExpectation (n : ℕ) : CStarConditionalExpectation (htr.jonesStrandIncl n)
    where
  toPositiveLinearMap := .mk₀ (htr.quotientExpect hδ.out n) fun _ hy ↦ htr.quotientExpect_nonneg hy
  map_one' := htr.quotientExpect_one hδ.out n
  map_mul_left' := htr.quotientExpect_mul_left hδ.out
  map_mul_right' := htr.quotientExpect_mul_right hδ.out
@[simp] theorem cstarConditionalExpectation_apply (n : ℕ) (y : htr.Quotient (n + 1)) :
    cstarConditionalExpectation htr n y = htr.quotientExpect hδ.out n y := (rfl)
end CStarTower
end IsMarkovTrace
end TauCeti.TemperleyLieb

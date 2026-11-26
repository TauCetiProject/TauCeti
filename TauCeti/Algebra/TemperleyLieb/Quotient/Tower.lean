/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Algebra.TemperleyLieb.Dimension
public import TauCeti.Algebra.TemperleyLieb.Quotient.Positivity
public import TauCeti.Algebra.TemperleyLieb.Trace.Expectation
public import TauCeti.Analysis.CStarAlgebra.ConditionalExpectation.CompletelyPositive
public import TauCeti.Analysis.StarAlgebra.GNS.FiniteDimensional
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
/-! # The C⋆-tower of positive Jones quotients and its conditional expectations

For `δ ∈ jonesLoopParameters`, `htr.Quotient n` forms a unital C⋆-algebra tower equipped with
faithful tracial states (`normalizedQuotientTrace`), isometric `⋆`-inclusions
(`quotientStrandIncl` / `quotientStrandStarAlgHom`), Jones projections (`jonesProjection`), and
unique trace-compatible completely positive conditional expectations (`quotientExpectation`,
`cstarConditionalExpectation`, intertwined with `pathAlgebraExpect` by
`quotientPathAlgebraEquiv_quotientExpectation`, `discreteQuotientEquiv_quotientExpectation`, and
`genericQuotientEquiv_quotientExpectation`).

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
/-- The **Jones projection** `p_n = δ⁻¹ • mk (e δ (Fin.last n))` in `htr.Quotient (n + 2)`. -/
def jonesProjection (n : ℕ) : htr.Quotient (n + 2) :=
  (δ : ℂ)⁻¹ • Ideal.Quotient.mk (htr.traceRadical (n + 2)) (e (δ : ℂ) (Fin.last n))
omit [Fact (IsSelfAdjoint (δ : ℂ))] in
/-- Unfolding equation for `jonesProjection`. -/
theorem jonesProjection_def (n : ℕ) :
    htr.jonesProjection n =
      (δ : ℂ)⁻¹ • Ideal.Quotient.mk (htr.traceRadical (n + 2)) (e (δ : ℂ) (Fin.last n)) :=
  (rfl)
/-- Every Jones projection is self-adjoint. -/
theorem isSelfAdjoint_jonesProjection (n : ℕ) :
    IsSelfAdjoint (htr.jonesProjection n) := by
  rw [IsSelfAdjoint, jonesProjection_def, star_smul, Ideal.Quotient.star_mk, star_e, star_inv₀,
    IsSelfAdjoint.star_eq (Complex.conj_ofReal _)]
omit [Fact (IsSelfAdjoint (δ : ℂ))] in
/-- For `δ ≠ 0`, every Jones projection is idempotent. -/
theorem isIdempotentElem_jonesProjection (hδ : δ ≠ 0) (n : ℕ) :
    IsIdempotentElem (htr.jonesProjection n) := by
  rw [IsIdempotentElem, jonesProjection_def, ← Ideal.Quotient.mkₐ_eq_mk ℂ, smul_mul_smul_comm,
    ← map_mul, e_mul_self, map_smul, smul_smul, mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 hδ), mul_one]
private abbrev jonesEquiv (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :=
  let M := jonesModel hδ
  htr.quotientPathAlgebraEquiv M.G M.v₀ M.hr M.hrs M.hδ M.hf M.hf₀ M.hadj n
omit [Fact (IsSelfAdjoint (δ : ℂ))] in
/-- Trace compatibility of `quotientExpectation` with the unnormalized
`quotientStarPositiveFunctional`. -/
@[simp] theorem quotientStarPositiveFunctional_quotientExpectation
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} (y : htr.Quotient (n + 1)) :
    htr.quotientStarPositiveFunctional hδ n (htr.quotientExpectation n y) =
      (δ : ℂ)⁻¹ * htr.quotientStarPositiveFunctional hδ (n + 1) y := by
  simp [htr.quotientStarPositiveFunctional_apply]
omit [Fact (IsSelfAdjoint (δ : ℂ))] in
/-- **Uniqueness of `quotientExpectation`**: left `quotientStrandIncl`-module maps compatible with
`quotientStarPositiveFunctional` agree with `quotientExpectation`. -/
theorem quotientExpectation_unique (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (F : htr.Quotient (n + 1) →ₗ[ℂ] htr.Quotient n)
    (hmul : ∀ x y, F (htr.quotientStrandIncl n x * y) = x * F y)
    (htrace : ∀ y, htr.quotientStarPositiveFunctional hδ n (F y) =
      (δ : ℂ)⁻¹ * htr.quotientStarPositiveFunctional hδ (n + 1) y) :
    F = htr.quotientExpectation n :=
  htr.eq_quotientExpectation_of_quotientStrandIncl_mul F hmul fun y ↦ by
    simpa [htr.quotientStarPositiveFunctional_apply] using htrace y
private def graphExpect {V : Type*} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    [G.LocallyFinite] (v₀ : V) {r : V → ℂ} (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v))
    (hGδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = (δ : ℂ) * r v ^ 2) {f : V → ℕ}
    (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) (n : ℕ) :
    htr.Quotient (n + 1) →ₗ[ℂ] htr.Quotient n :=
  let e := fun k ↦ htr.quotientPathAlgebraEquiv G v₀ hr hrs hGδ hf hf₀ hadj k
  (e n).symm.toAlgEquiv.toLinearMap.comp
    ((pathAlgebraExpect G v₀ r (δ : ℂ)).comp (e (n + 1)).toAlgEquiv.toLinearMap)
private theorem graphExpect_mul_left {V : Type*} (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] [G.LocallyFinite] (v₀ : V) {r : V → ℂ} (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v))
    (hGδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = (δ : ℂ) * r v ^ 2) {f : V → ℕ}
    (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) {n : ℕ}
    (x : htr.Quotient n) (y : htr.Quotient (n + 1)) :
    htr.graphExpect G v₀ hr hrs hGδ hf hf₀ hadj n (htr.quotientStrandIncl n x * y) =
      x * htr.graphExpect G v₀ hr hrs hGδ hf hf₀ hadj n y := by
  dsimp [graphExpect]
  rw [map_mul, htr.quotientPathAlgebraEquiv_quotientStrandIncl G v₀ hr hrs hGδ hf hf₀ hadj,
    pathAlgebraExpect_pathAlgebraExtend_mul, map_mul, StarAlgEquiv.symm_apply_apply]
private theorem quotientTrace_graphExpect {V : Type*} (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] (v₀ : V) {r : V → ℂ}
    (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v))
    (hGδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = (δ : ℂ) * r v ^ 2) {f : V → ℕ}
    (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) {n : ℕ}
    (y : htr.Quotient (n + 1)) :
    (tr n).quotientTrace (htr.map_mul_comm n)
        (htr.graphExpect G v₀ hr hrs hGδ hf hf₀ hadj n y) =
      (δ : ℂ)⁻¹ * (tr (n + 1)).quotientTrace (htr.map_mul_comm (n + 1)) y := by
  rw [← htr.pathAlgebraTrace_quotientPathAlgebraEquiv G v₀ hr hrs hGδ hf hf₀ hadj,
    ← htr.pathAlgebraTrace_quotientPathAlgebraEquiv G v₀ hr hrs hGδ hf hf₀ hadj]
  simp only [graphExpect, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    StarAlgEquiv.coe_toAlgEquiv, StarAlgEquiv.apply_symm_apply,
    pathAlgebraTrace_pathAlgebraExpect hr]
/-- `quotientPathAlgebraEquiv` intertwines `quotientExpectation` with `pathAlgebraExpect` for
every graph model. -/
theorem quotientPathAlgebraEquiv_quotientExpectation {V : Type*} (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] [G.LocallyFinite] (v₀ : V) {r : V → ℂ} (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v))
    (hGδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = (δ : ℂ) * r v ^ 2) {f : V → ℕ}
    (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) {n : ℕ}
    (y : htr.Quotient (n + 1)) :
    htr.quotientPathAlgebraEquiv G v₀ hr hrs hGδ hf hf₀ hadj n (htr.quotientExpectation n y) =
      pathAlgebraExpect G v₀ r (δ : ℂ)
        (htr.quotientPathAlgebraEquiv G v₀ hr hrs hGδ hf hf₀ hadj (n + 1) y) := by
  have hF := htr.eq_quotientExpectation_of_quotientStrandIncl_mul
    (htr.graphExpect G v₀ hr hrs hGδ hf hf₀ hadj n)
    (htr.graphExpect_mul_left G v₀ hr hrs hGδ hf hf₀ hadj)
    (htr.quotientTrace_graphExpect G v₀ hr hrs hGδ hf hf₀ hadj)
  have hy := congrArg (fun g ↦ htr.quotientPathAlgebraEquiv G v₀ hr hrs hGδ hf hf₀ hadj n (g y))
    hF.symm
  simpa [graphExpect] using hy
private theorem jonesEquiv_quotientExpectation (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (y : htr.Quotient (n + 1)) :
    htr.jonesEquiv hδ n (htr.quotientExpectation n y) =
      pathAlgebraExpect (jonesModel hδ).G (jonesModel hδ).v₀ (jonesModel hδ).r (δ : ℂ)
        (htr.jonesEquiv hδ (n + 1) y) :=
  htr.quotientPathAlgebraEquiv_quotientExpectation (jonesModel hδ).G (jonesModel hδ).v₀
    (jonesModel hδ).hr (jonesModel hδ).hrs (jonesModel hδ).hδ (jonesModel hδ).hf
    (jonesModel hδ).hf₀ (jonesModel hδ).hadj y
/-- Algebraic positivity: `quotientExpectation (star y * y)` is a finite sum of squares. -/
theorem exists_sum_star_mul_self_quotientExpectation_star_mul_self
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} (y : htr.Quotient (n + 1)) :
    ∃ (m : ℕ) (z : Fin m → htr.Quotient n),
      htr.quotientExpectation n (star y * y) = ∑ i : Fin m, star (z i) * z i := by
  obtain ⟨m, Z, hZ⟩ := exists_sum_star_mul_self_pathAlgebraExpect_star_mul_self (jonesModel hδ).hrs
    (pos_of_mem_jonesLoopParameters hδ) (htr.jonesEquiv hδ (n + 1) y)
  refine ⟨m, fun i ↦ (htr.jonesEquiv hδ n).symm (Z i), EquivLike.injective (htr.jonesEquiv hδ n) ?_⟩
  rw [htr.jonesEquiv_quotientExpectation hδ, map_mul, StarHomClass.map_star, hZ, map_sum]
  simp_rw [map_mul, StarHomClass.map_star, StarAlgEquiv.apply_symm_apply]
/-- On the discrete `A_(m-1)` path algebra, `quotientExpectation` computes as
`pathAlgebraExpect`. -/
theorem discreteQuotientEquiv_quotientExpectation {m : ℕ} (hm : 2 ≤ m)
    (hmδ : δ = 2 * cos (π / m)) {n : ℕ} (y : htr.Quotient (n + 1)) :
    htr.discreteQuotientEquiv hm hmδ n (htr.quotientExpectation n y) =
      pathAlgebraExpect (pathGraph (m - 1)) ⟨0, Nat.sub_pos_of_lt (by omega)⟩
        (discretePathWeight m) (δ : ℂ) (htr.discreteQuotientEquiv hm hmδ (n + 1) y) := by
  simp only [discreteQuotientEquiv_eq]
  exact htr.quotientPathAlgebraEquiv_quotientExpectation (pathGraph (m - 1))
    ⟨0, Nat.sub_pos_of_lt (by omega)⟩ discretePathWeight_ne_zero
    (isSelfAdjoint_discretePathWeight m)
    (fun v ↦ by rw [hmδ]; exact sum_neighborFinset_discretePathWeight_sq v)
    Fin.val_injective rfl (fun h ↦ pathGraph_adj.1 h) y
/-- On the generic `A_∞` path algebra, `quotientExpectation` computes as `pathAlgebraExpect`. -/
theorem genericQuotientEquiv_quotientExpectation (hδ2 : 2 ≤ δ) {n : ℕ} (y : htr.Quotient (n + 1)) :
    htr.genericQuotientEquiv hδ2 n (htr.quotientExpectation n y) =
      pathAlgebraExpect (hasse ℕ) 0 (genericPathWeight δ) (δ : ℂ)
        (htr.genericQuotientEquiv hδ2 (n + 1) y) := by
  simp only [genericQuotientEquiv_eq]
  exact htr.quotientPathAlgebraEquiv_quotientExpectation (hasse ℕ) 0
    (genericPathWeight_ne_zero hδ2) (isSelfAdjoint_genericPathWeight δ)
    (sum_neighborFinset_genericPathWeight_sq hδ2) Function.injective_id rfl
    (fun h ↦ hasse_nat_adj.1 h) y
omit [Fact (IsSelfAdjoint (δ : ℂ))] in
/-- Conditional expectation of the Jones projection `p_n` is `(δ⁻¹ ^ 2) • 1` (inverse index). -/
@[simp] theorem quotientExpectation_jonesProjection (n : ℕ) :
    htr.quotientExpectation (n + 1) (htr.jonesProjection n) = ((δ : ℂ)⁻¹ ^ 2) • 1 := by
  rw [jonesProjection_def, map_smul, htr.quotientExpectation_mk_e_last, smul_smul, sq]
omit [Fact (IsSelfAdjoint (δ : ℂ))] in
/-- Unnormalized Markov property: multiplying by `jonesProjection` scales the trace by `δ⁻¹`. -/
@[simp] theorem quotientStarPositiveFunctional_quotientStrandIncl_mul_jonesProjection
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} (x : htr.Quotient (n + 1)) :
    htr.quotientStarPositiveFunctional hδ (n + 2)
      (htr.quotientStrandIncl (n + 1) x * htr.jonesProjection n) =
      (δ : ℂ)⁻¹ * htr.quotientStarPositiveFunctional hδ (n + 1) x := by
  obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [jonesProjection_def, ← map_mul, htr.map_strandIncl_mul_e_last]
omit [Fact (IsSelfAdjoint (δ : ℂ))] in
/-- **Jones compression identity:** sandwiching `quotientStrandIncl (n + 1) x` between copies of
`jonesProjection n` projects it onto `quotientExpectation n x`. -/
theorem jonesProjection_mul_quotientStrandIncl_mul_jonesProjection (hδ : δ ≠ 0) {n : ℕ}
    (x : htr.Quotient (n + 1)) :
    htr.jonesProjection n * htr.quotientStrandIncl (n + 1) x * htr.jonesProjection n =
      htr.quotientStrandIncl (n + 1) (htr.quotientStrandIncl n (htr.quotientExpectation n x)) *
        htr.jonesProjection n := by
  have hδne : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ
  have hmk := htr.mk_e_last_mul_quotientStrandIncl_mul_mk_e_last hδne n x
  simp only [jonesProjection_def, smul_mul_assoc, mul_smul_comm]
  rw [hmk, smul_mul_assoc, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hδne, mul_one]
omit [Fact (IsSelfAdjoint (δ : ℂ))] in
/-- `quotientExpectation` preserves `normalizedQuotientTrace`. -/
@[simp] theorem normalizedQuotientTrace_quotientExpectation (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (y : htr.Quotient (n + 1)) :
    htr.normalizedQuotientTrace hδ n (htr.quotientExpectation n y) =
      htr.normalizedQuotientTrace hδ (n + 1) y := by
  rw [normalizedQuotientTrace_apply, htr.quotientStarPositiveFunctional_quotientExpectation,
    normalizedQuotientTrace_apply, pow_succ]; ring
omit [Fact (IsSelfAdjoint (δ : ℂ))] in
/-- Normalized Markov property: multiplying by `p_n` scales the tracial state by `δ⁻¹ ^ 2`. -/
@[simp] theorem normalizedQuotientTrace_quotientStrandIncl_mul_jonesProjection
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} (x : htr.Quotient (n + 1)) :
    htr.normalizedQuotientTrace hδ (n + 2)
      (htr.quotientStrandIncl (n + 1) x * htr.jonesProjection n) =
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
  have hiso : Isometry (htr.quotientStrandStarAlgHom n) :=
    NonUnitalStarAlgHom.isometry (htr.quotientStrandStarAlgHom n) fun _ _ h ↦
      htr.quotientStrandIncl_injective n
        (fun _ ↦ (isUnit_of_mem_jonesLoopParameters hδ.out).mul_right_injective)
        (by simpa [quotientStrandStarAlgHom_apply] using h)
  intro x y
  simpa only [quotientStrandStarAlgHom_apply] using hiso x y
/-- Each tower inclusion `quotientStrandIncl` preserves the GNS C⋆-norm. -/
@[simp] theorem norm_quotientStrandIncl (n : ℕ) (x : htr.Quotient n) :
    ‖htr.quotientStrandIncl n x‖ = ‖x‖ := by
  simpa [dist_zero_right] using (htr.isometry_quotientStrandIncl n).dist_eq x 0
/-- `quotientExpectation` preserves positivity in the C⋆-algebra spectral order. -/
theorem quotientExpectation_nonneg {n : ℕ} {y : htr.Quotient (n + 1)} (hy : 0 ≤ y) :
    0 ≤ htr.quotientExpectation n y := by
  let _ : NonUnitalContinuousFunctionalCalculus ℝ (htr.Quotient (n + 1)) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let _ : NonnegSpectrumClass ℝ (htr.Quotient (n + 1)) := CStarAlgebra.instNonnegSpectrumClass'
  obtain ⟨r, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hy
  obtain ⟨_, z, hz⟩ := htr.exists_sum_star_mul_self_quotientExpectation_star_mul_self hδ.out r
  rw [hz]; exact Finset.sum_nonneg fun i _ ↦ star_mul_self_nonneg (z i)
/-- **C⋆-conditional expectation on the positive Jones quotient tower.** -/
def cstarConditionalExpectation (n : ℕ) :
    CStarConditionalExpectation (htr.quotientStrandStarAlgHom n) where
  toPositiveLinearMap :=
    .mk₀ (htr.quotientExpectation n) fun _ hy ↦ htr.quotientExpectation_nonneg hy
  map_one' := htr.quotientExpectation_one
    (Complex.ofReal_ne_zero.2 (pos_of_mem_jonesLoopParameters hδ.out).ne') n
  map_mul_left' a b := by
    rw [quotientStrandStarAlgHom_apply]; exact htr.quotientExpectation_quotientStrandIncl_mul n a b
  map_mul_right' a b := by
    rw [quotientStrandStarAlgHom_apply]; exact htr.quotientExpectation_mul_quotientStrandIncl n a b
/-- Evaluating `cstarConditionalExpectation` agrees with `quotientExpectation`. -/
@[simp] theorem cstarConditionalExpectation_apply (n : ℕ) (y : htr.Quotient (n + 1)) :
    cstarConditionalExpectation htr n y = htr.quotientExpectation n y := (rfl)
end CStarTower
end IsMarkovTrace
end TauCeti.TemperleyLieb

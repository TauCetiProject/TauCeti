/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Analysis.Fredholm.ContinuousFamily
public import TauCeti.Analysis.Normed.Operator.Compact.RieszTheory

import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Finite.Rank

/-!
# Compact perturbations of Fredholm operators and Atkinson's theorem

A continuous linear map between Banach spaces is Fredholm exactly when it is invertible modulo
compact operators (Atkinson's theorem). Consequently a compact perturbation of a Fredholm operator
is Fredholm, with the same index. This is the last of the three classical stability statements
for the Fredholm index, after finite-rank perturbations (`TauCeti.Analysis.Fredholm.FiniteRank`)
and small perturbations (`TauCeti.Analysis.Fredholm.SmallPerturbation`). The parametrix form is
the one used for elliptic operators, whose parametrices invert them modulo compact remainders.

The starting point is the Riesz--Schauder theory of
`TauCeti.Analysis.Normed.Operator.Compact.RieszTheory`: for a compact operator `K` the kernel of
`1 - K` is finite dimensional and its cokernel is finite dimensional, so `1 - K` is Fredholm.

The two sides of a parametrix `S` of `T` are used separately. If `S ∘ T - 1` is compact, the
identity `x = S (T x) - (S ∘ T - 1) x` is an estimate `‖x‖ ≤ ‖S‖ ‖T x‖ + ‖K x‖` with compact
error, so `T` has finite-dimensional kernel and, on a Banach space, closed range by Peetre's
lemma. If `T ∘ S - 1` is compact, the range of `T` contains the range of the Fredholm operator
`T ∘ S`, so it has finite codimension. Conversely, a continuous quasi-inverse of a Fredholm
operator inverts it modulo finite-rank, hence compact, operators. A parametrix of `T` is also a
parametrix of `T + C` for `C` compact, which gives the perturbation statement.

The index statement is then a connectedness argument rather than a new computation: the family
`c ↦ T + c • C` is a continuous family of Fredholm operators over the preconnected parameter space
`𝕜`, so the local constancy of the index proved in `TauCeti.Analysis.Fredholm.ContinuousFamily`
forces the values at `c = 0` and `c = 1` to agree. Additivity of the index under composition
then shows that a parametrix of `T` has index `-index T`.

## Main declarations

* `TauCeti.isFredholm_one_sub` and `TauCeti.isFredholm_one_add`: `1 - K` and `1 + K` are Fredholm
  for `K` compact.
* `ContinuousLinearMap.finiteDimensional_ker_of_isCompactOperator_comp_sub_one` and
  `ContinuousLinearMap.isClosed_range_of_isCompactOperator_comp_sub_one`: an operator with a
  left parametrix modulo compact operators has finite-dimensional kernel and closed range.
* `ContinuousLinearMap.cofg_range_of_isCompactOperator_comp_sub_one`: an operator with a right
  parametrix modulo compact operators has finite-codimensional range.
* `ContinuousLinearMap.IsFredholm.of_isCompactOperator_comp_sub_one`,
  `ContinuousLinearMap.IsFredholm.exists_isCompactOperator_comp_sub_one` and
  `TauCeti.isFredholm_iff_exists_isCompactOperator_comp_sub_one`: Atkinson's theorem.
* `ContinuousLinearMap.IsFredholm.add_of_isCompactOperator`: a compact perturbation of a Fredholm
  operator is Fredholm.
* `ContinuousLinearMap.index_add_of_isCompactOperator`: a compact perturbation leaves the
  index unchanged.
* `ContinuousLinearMap.index_one_sub_eq_zero` and
  `ContinuousLinearMap.index_one_add_eq_zero`: `1 - K` and `1 + K` have index `0` for `K`
  compact.
* `ContinuousLinearMap.index_eq_neg_of_isCompactOperator_comp_sub_one`: a parametrix modulo
  compact operators has the opposite index.
* `ContinuousLinearMap.IsFredholm.exists_isInvertible_sub_isCompactOperator_of_index_eq_zero`: an
  index-zero Fredholm operator has an invertible compact perturbation.
* `ContinuousLinearMap.IsFredholm.joinedIn_of_isCompactOperator_sub`: an affine compact
  perturbation stays in the Fredholm locus.

The finite-defect completion and affine path are adapted from
[AtiyahSinger/Analysis/FredholmPaths.lean][fredholm-paths] in Lean-Atiyah-Singer.
They are supplementary analytic steps for the Fredholm path argument of Lawson--Michelsohn,
*Spin Geometry*, III §7, Lemmas 7.6--7.7, p. 203.

## References

* F. V. Atkinson, *The normal solubility of linear equations in normed spaces*, Mat. Sbornik
  N.S. 28 (70) (1951), 3--14.
* J. B. Conway, *A Course in Functional Analysis*, Chapter XI.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1, whose
  conventions for Fredholm operators are followed here.
* H. B. Lawson, Jr., and M.-L. Michelsohn, *Spin Geometry*, Princeton Mathematical Series 38,
  Princeton University Press, 1989, Chapter III, §7, Lemmas 7.6--7.7, p. 203,
  [DOI](https://doi.org/10.1515/9781400883912).

[fredholm-paths]: https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/FredholmPaths.lean
-/

public section

namespace TauCeti

open Module

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Riesz--Schauder**: a compact perturbation of the identity is a Fredholm operator. -/
theorem isFredholm_one_sub {K : E →L[𝕜] E} (hK : IsCompactOperator K) :
    ContinuousLinearMap.IsFredholm (1 - K : E →L[𝕜] E) :=
  ContinuousLinearMap.IsFredholm.of_finite_ker_coker _
    ((1 - K : E →L[𝕜] E).finiteDimensional_ker_of_compact_estimate hK (C := 1)
      (fun x ↦ by simpa using norm_le_norm_sub_add x (K x)))
    (IsCompactOperator.finiteDimensional_quotient_range_one_sub hK)

/-- **Riesz--Schauder**, in the form in which compact perturbations of the identity arise below. -/
theorem isFredholm_one_add {K : E →L[𝕜] E} (hK : IsCompactOperator K) :
    ContinuousLinearMap.IsFredholm (1 + K : E →L[𝕜] E) := by
  have hneg : IsCompactOperator (-K : E →L[𝕜] E) := by
    simpa only [FunLike.coe_neg] using hK.neg
  have hrw : (1 + K : E →L[𝕜] E) = 1 - (-K) := by abel
  rw [hrw]
  exact isFredholm_one_sub hneg

variable {T C : E →L[𝕜] F} {S : F →L[𝕜] E}

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- An operator with a left parametrix modulo compact operators has finite-dimensional kernel:
if `S ∘ T - 1` is compact then `ker T` is finite dimensional. No completeness of `E` or `F` is
needed. -/
theorem _root_.ContinuousLinearMap.finiteDimensional_ker_of_isCompactOperator_comp_sub_one
    (T : E →L[𝕜] F) {S : F →L[𝕜] E} (hST : IsCompactOperator (S.comp T - 1 : E →L[𝕜] E)) :
    FiniteDimensional 𝕜 T.ker :=
  T.finiteDimensional_ker_of_compact_estimate hST
    (T.norm_le_opNorm_mul_norm_add_norm_comp_sub_one S)

omit [CompleteSpace F] in
/-- An operator on a Banach space with a left parametrix modulo compact operators has closed
range: if `S ∘ T - 1` is compact then `range T` is closed. -/
theorem _root_.ContinuousLinearMap.isClosed_range_of_isCompactOperator_comp_sub_one
    (T : E →L[𝕜] F) {S : F →L[𝕜] E} (hST : IsCompactOperator (S.comp T - 1 : E →L[𝕜] E)) :
    IsClosed (T.range : Set F) :=
  T.isClosed_range_of_compact_estimate hST (T.norm_le_opNorm_mul_norm_add_norm_comp_sub_one S)

omit [CompleteSpace E] in
/-- An operator with a right parametrix modulo compact operators has finite-codimensional range:
if `T ∘ S - 1` is compact then `F ⧸ range T` is finite dimensional. Between Banach spaces the
range is then closed by `ContinuousLinearMap.isClosed_range_of_finite_coker`. -/
theorem _root_.ContinuousLinearMap.cofg_range_of_isCompactOperator_comp_sub_one
    (T : E →L[𝕜] F) {S : F →L[𝕜] E} (hTS : IsCompactOperator (T.comp S - 1 : F →L[𝕜] F)) :
    T.range.CoFG := by
  have hrw : T.comp S = 1 + (T.comp S - 1) := by abel
  have hfred := isFredholm_one_add hTS
  rw [← hrw] at hfred
  -- The range of `T` contains the range of the Fredholm operator `T ∘ S`.
  have hrange : (T.comp S).range ≤ T.range := by
    rintro y ⟨z, rfl⟩
    exact ⟨S z, rfl⟩
  exact hfred.finite_coker.of_le hrange

/-- **Atkinson's theorem**, parametrix direction: an operator between Banach spaces with a
two-sided parametrix modulo compact operators is Fredholm. -/
theorem _root_.ContinuousLinearMap.IsFredholm.of_isCompactOperator_comp_sub_one
    (hST : IsCompactOperator (S.comp T - 1 : E →L[𝕜] E))
    (hTS : IsCompactOperator (T.comp S - 1 : F →L[𝕜] F)) :
    ContinuousLinearMap.IsFredholm T :=
  ContinuousLinearMap.IsFredholm.of_finite_ker_coker T
    (T.finiteDimensional_ker_of_isCompactOperator_comp_sub_one hST)
    (T.cofg_range_of_isCompactOperator_comp_sub_one hTS)

omit [CompleteSpace E] [CompleteSpace F] in
/-- A Fredholm operator has a two-sided parametrix modulo compact operators: any continuous
quasi-inverse, which inverts it modulo operators of finite rank, will do. -/
theorem _root_.ContinuousLinearMap.IsFredholm.exists_isCompactOperator_comp_sub_one
    (hT : ContinuousLinearMap.IsFredholm T) :
    ∃ S : F →L[𝕜] E, IsCompactOperator (S.comp T - 1 : E →L[𝕜] E) ∧
      IsCompactOperator (T.comp S - 1 : F →L[𝕜] F) := by
  have : LocallyCompactSpace 𝕜 := by
    let _i := IsRCLikeNormedField.rclike 𝕜
    infer_instance
  obtain ⟨S, hS⟩ := hT.exists_isQuasiInverse
  refine ⟨S, ?_, ?_⟩ <;> apply LinearMap.HasFiniteRange.isCompactOperator
  · simpa only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id] using
      LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hS.1
  · simpa only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id] using
      LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hS.2

/-- **Atkinson's theorem**: an operator between Banach spaces is Fredholm if and only if it is
invertible modulo compact operators. -/
theorem isFredholm_iff_exists_isCompactOperator_comp_sub_one :
    ContinuousLinearMap.IsFredholm T ↔ ∃ S : F →L[𝕜] E,
      IsCompactOperator (S.comp T - 1 : E →L[𝕜] E) ∧
        IsCompactOperator (T.comp S - 1 : F →L[𝕜] F) :=
  ⟨fun hT ↦ hT.exists_isCompactOperator_comp_sub_one,
    fun ⟨_, hST, hTS⟩ ↦ .of_isCompactOperator_comp_sub_one hST hTS⟩

/-- A compact perturbation of a Fredholm operator between Banach spaces is Fredholm: a
parametrix of `T` modulo compact operators is also one of `T + C`. -/
theorem _root_.ContinuousLinearMap.IsFredholm.add_of_isCompactOperator
    (hT : ContinuousLinearMap.IsFredholm T) (hC : IsCompactOperator C) :
    ContinuousLinearMap.IsFredholm (T + C) := by
  obtain ⟨S, hST, hTS⟩ := hT.exists_isCompactOperator_comp_sub_one
  refine .of_isCompactOperator_comp_sub_one (S := S) ?_ ?_
  · have hrw : S.comp (T + C) - 1 = (S.comp T - 1) + S.comp C := by
      rw [ContinuousLinearMap.comp_add]
      abel
    rw [hrw, FunLike.coe_add]
    exact hST.add (hC.clm_comp S)
  · have hrw : (T + C).comp S - 1 = (T.comp S - 1) + C.comp S := by
      rw [ContinuousLinearMap.add_comp]
      abel
    rw [hrw, FunLike.coe_add]
    exact hTS.add (hC.comp_clm S)

/-- A compact perturbation leaves the Fredholm index unchanged.

The scalar family `c ↦ T + c • C` is a continuous family of Fredholm operators over the
preconnected parameter space `𝕜`, so its index is constant; comparing `c = 0` with `c = 1` gives
the claim. -/
theorem _root_.ContinuousLinearMap.index_add_of_isCompactOperator
    (hT : ContinuousLinearMap.IsFredholm T)
    (hC : IsCompactOperator C) : ContinuousLinearMap.index (T + C) = ContinuousLinearMap.index T :=
      by
  let _i := IsRCLikeNormedField.rclike 𝕜
  have hpre : PreconnectedSpace 𝕜 :=
    ⟨(convex_univ : Convex ℝ (Set.univ : Set 𝕜)).isPreconnected⟩
  have hcont : Continuous fun c : 𝕜 => T + c • C := by fun_prop
  have hfred : ∀ c : 𝕜, ContinuousLinearMap.IsFredholm (T + c • C) := fun c =>
    hT.add_of_isCompactOperator (by simpa using hC.smul c)
  simpa using Continuous.index_eq_of_preconnectedSpace hcont hfred 1 0

/-- A compact perturbation of the identity has index `0`. -/
@[simp]
theorem _root_.ContinuousLinearMap.index_one_sub_eq_zero {K : E →L[𝕜] E} (hK : IsCompactOperator K)
    :
    ContinuousLinearMap.index (1 - K : E →L[𝕜] E) = 0 := by
  have hneg : IsCompactOperator (-K : E →L[𝕜] E) := by
    simpa only [FunLike.coe_neg] using hK.neg
  have hrw : (1 - K : E →L[𝕜] E) = ContinuousLinearMap.id 𝕜 E + (-K) := by
    ext x
    simp [sub_eq_add_neg]
  rw [hrw, ContinuousLinearMap.index_add_of_isCompactOperator .id hneg,
    ContinuousLinearMap.index_id]

/-- A compact perturbation of the identity has index `0`, in additive form. -/
@[simp]
theorem _root_.ContinuousLinearMap.index_one_add_eq_zero {K : E →L[𝕜] E} (hK : IsCompactOperator K)
    :
    ContinuousLinearMap.index (1 + K : E →L[𝕜] E) = 0 := by
  have hrw : (1 + K : E →L[𝕜] E) = ContinuousLinearMap.id 𝕜 E + K := rfl
  rw [hrw, ContinuousLinearMap.index_add_of_isCompactOperator .id hK, ContinuousLinearMap.index_id]

/-- A parametrix modulo compact operators of a Fredholm operator has the opposite index:
if `S ∘ T - 1` and `T ∘ S - 1` are compact then `index S = -index T`. -/
theorem _root_.ContinuousLinearMap.index_eq_neg_of_isCompactOperator_comp_sub_one
    (hST : IsCompactOperator (S.comp T - 1 : E →L[𝕜] E))
    (hTS : IsCompactOperator (T.comp S - 1 : F →L[𝕜] F)) :
    ContinuousLinearMap.index S = -ContinuousLinearMap.index T := by
  have hT : ContinuousLinearMap.IsFredholm T := .of_isCompactOperator_comp_sub_one hST hTS
  have hS : ContinuousLinearMap.IsFredholm S := .of_isCompactOperator_comp_sub_one hTS hST
  have hcomp := hS.index_comp hT
  have hrw : S.comp T = 1 + (S.comp T - 1) := by abel
  rw [← ContinuousLinearMap.index_def, hrw, ContinuousLinearMap.index_one_add_eq_zero hST] at hcomp
  rw [ContinuousLinearMap.index_def, ContinuousLinearMap.index_def]
  omega


end TauCeti

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- An index-zero Fredholm operator can be made invertible by a compact perturbation. -/
theorem IsFredholm.exists_isInvertible_sub_isCompactOperator_of_index_eq_zero
    {T : E →L[𝕜] F} (hT : T.IsFredholm) (hind : T.index = 0) :
    ∃ C : E →L[𝕜] F, C.IsInvertible ∧ IsCompactOperator (C - T) := by
  let _i := IsRCLikeNormedField.rclike 𝕜
  -- The Fredholm package isolates the only missing block: kernel to cokernel.
  obtain ⟨pkg⟩ := hT.nonempty_fredholmPackage
  let := pkg.decDom.finite_X₀
  let := pkg.decCodom.finite_X₀
  have hcoker : Module.finrank 𝕜 (F ⧸ pkg.decCodom.X₁) =
      Module.finrank 𝕜 pkg.decCodom.X₀ :=
    (pkg.decCodom.X₁.quotientEquivOfIsTopCompl pkg.decCodom.X₀
      pkg.decCodom.isTopCompl).toLinearEquiv.finrank_eq
  have hdim : Module.finrank 𝕜 pkg.decDom.X₀ = Module.finrank 𝕜 pkg.decCodom.X₀ := by
    rw [ContinuousLinearMap.index_def, LinearMap.index_eq_finrank_sub,
      pkg.ker_eq, pkg.range_eq, hcoker] at hind
    omega
  let e₀ : pkg.decDom.X₀ ≃L[𝕜] pkg.decCodom.X₀ :=
    ContinuousLinearEquiv.ofFinrankEq hdim
  -- Complete the diagonal operator with an isomorphism of the finite missing blocks.
  let dE : (pkg.decDom.X₁ × pkg.decDom.X₀) ≃L[𝕜] E :=
    pkg.decDom.X₁.prodEquivOfIsTopCompl pkg.decDom.X₀ pkg.decDom.isTopCompl
  let dF : (pkg.decCodom.X₁ × pkg.decCodom.X₀) ≃L[𝕜] F :=
    pkg.decCodom.X₁.prodEquivOfIsTopCompl pkg.decCodom.X₀ pkg.decCodom.isTopCompl
  let C : E ≃L[𝕜] F := dE.symm.trans ((pkg.equiv.prodCongr e₀).trans dF)
  let P₀ : E →L[𝕜] pkg.decDom.X₀ :=
    pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm
  let K : E →L[𝕜] F := pkg.decCodom.X₀.subtypeL.comp (e₀.toContinuousLinearMap.comp P₀)
  have hK : IsCompactOperator K := by
    exact (isCompactOperator_of_locallyCompactSpace_rng
      (pkg.decCodom.X₀.subtypeL.comp e₀.toContinuousLinearMap)).comp_clm P₀
  have hCT : (C : E →L[𝕜] F) - T = K := by
    ext x
    have hTx : T x = (pkg.equiv (pkg.decDom.proj x) : F) :=
      DFunLike.congr_fun pkg.eq_equiv x
    simp only [sub_apply, hTx, C, dE, dF,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
      Submodule.prodEquivOfIsTopCompl_symm_apply, ContinuousLinearEquiv.prodCongr_apply,
      Submodule.prodEquivOfIsTopCompl_apply]
    simp [K, P₀, FredholmDecomposition.proj]
  refine ⟨C, ⟨C, rfl⟩, ?_⟩
  rwa [hCT]

/-- An affine compact perturbation gives a norm-continuous path through Fredholm operators. -/
theorem IsFredholm.joinedIn_of_isCompactOperator_sub
    {T₀ T₁ : E →L[𝕜] F} (hT₀ : ContinuousLinearMap.IsFredholm T₀)
    (hK : IsCompactOperator (T₁ - T₀)) :
    JoinedIn {T : E →L[𝕜] F | T.IsFredholm} T₀ T₁ := by
  let _i := IsRCLikeNormedField.rclike 𝕜
  let γ : Path T₀ T₁ :=
    ((Path.segment (0 : 𝕜) 1).map (f := fun c ↦ T₀ + c • (T₁ - T₀))
      (continuous_const.add (continuous_id.smul continuous_const))).cast
      (by simp) (by simp)
  refine ⟨γ, fun t ↦ ?_⟩
  simpa only [γ, Path.cast_coe, Path.map_coe, Function.comp_apply, Set.mem_ofPred_eq] using
    hT₀.add_of_isCompactOperator (hK.smul ((Path.segment (0 : 𝕜) 1) t))

end ContinuousLinearMap

end

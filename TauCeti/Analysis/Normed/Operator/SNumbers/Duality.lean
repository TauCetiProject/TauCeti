/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Module.Dual.Functoriality
public import TauCeti.Analysis.Normed.Operator.SNumbers.Gelfand
public import TauCeti.Analysis.Normed.Operator.SNumbers.Kolmogorov
import TauCeti.Analysis.Normed.Module.Annihilator
import TauCeti.Analysis.Normed.Module.Dual.LocalReflexivity
import TauCeti.Analysis.Normed.Module.Dual.Quotient
import TauCeti.Analysis.Normed.Module.Dual.Submodule
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Finite.Rank
import TauCeti.Analysis.Normed.Operator.LinearIsometry
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Precomp

/-!
# Duality between Gelfand and Kolmogorov numbers

For a bounded linear operator `T : E →L[𝕜] F` and its adjoint
`T' = ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E`, subspace-quotient
duality links restrictions of `T` to quotients of `T'` and quotients of `T` to restrictions of `T'`:

* Over any nontrivially normed field, `cₙ(T') ≤ dₙ(T)`
  (`ContinuousLinearMap.gelfandNumber_precomp_le`): the annihilator of an `n`-dimensional subspace
  `V ≤ F` has codimension at most `n` in `F'`, and `T'` restricted to `Vᗮ` is isometrically
  `(V.mkQL ∘L T)'`, whose norm is at most `‖V.mkQL ∘L T‖`.
* Over any `IsRCLikeNormedField`, `dₙ(T') = cₙ(T)` (`ContinuousLinearMap.kolmogorovNumber_precomp`):
  Hahn–Banach identifies `E' ⧸ Mᗮ` isometrically with `M'`, and every finite-dimensional subspace
  `G ≤ E'` is the annihilator of its preannihilator `G⊥`, whose codimension equals `dim G`.
  Consequently `dₙ(T'') ≤ dₙ(T)` (`ContinuousLinearMap.kolmogorovNumber_precomp_precomp_le`).
* Over any `IsRCLikeNormedField`, if `T` maps the closed unit ball to a totally bounded set — in
  particular if `T` is compact (`IsCompactOperator.gelfandNumber_precomp`) or has finite-dimensional
  range (`ContinuousLinearMap.gelfandNumber_precomp_of_finiteDimensional_range`) — then
  `cₙ(T') = dₙ(T)` and `dₙ(T'') = dₙ(T)`
  (`ContinuousLinearMap.gelfandNumber_precomp_of_totallyBounded_image_closedBall`,
  `ContinuousLinearMap.kolmogorovNumber_precomp_precomp_of_totallyBounded_image_closedBall`).

No completeness or Hausdorff assumption on `E` or `F` is required anywhere: the local-reflexivity
step pulls a finite-dimensional bidual subspace and a finite net back to the Hausdorff normed
quotient `SeparationQuotient F` without assuming completeness, and invariance of Kolmogorov numbers
under surjective linear isometries lifts the equality back to seminormed codomains.

## Main declarations

* `ContinuousLinearMap.gelfandNumber_precomp_le`: `cₙ(T') ≤ dₙ(T)`.
* `ContinuousLinearMap.kolmogorovNumber_precomp`: `dₙ(T') = cₙ(T)`.
* `ContinuousLinearMap.kolmogorovNumber_precomp_precomp_le`: `dₙ(T'') ≤ dₙ(T)`.
* `ContinuousLinearMap.gelfandNumber_precomp_of_totallyBounded_image_closedBall`: `cₙ(T') = dₙ(T)`
  when `T '' closedBall 0 1` is totally bounded.
* `ContinuousLinearMap.kolmogorovNumber_precomp_precomp_of_totallyBounded_image_closedBall`:
  `dₙ(T'') = dₙ(T)` when `T '' closedBall 0 1` is totally bounded.
* `IsCompactOperator.gelfandNumber_precomp`: `cₙ(T') = dₙ(T)` for compact `T`.
* `IsCompactOperator.kolmogorovNumber_precomp_precomp`: `dₙ(T'') = dₙ(T)` for compact `T`.
* `ContinuousLinearMap.gelfandNumber_precomp_of_finiteDimensional_range`: `cₙ(T') = dₙ(T)` when
  `T.range` is finite-dimensional.
* `ContinuousLinearMap.kolmogorovNumber_precomp_precomp_of_finiteDimensional_range`:
  `dₙ(T'') = dₙ(T)` when `T.range` is finite-dimensional.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. **51** (1974), §6,
  Theorems 6.2 and 6.3.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §2.6.
* J. Lindenstrauss and H. P. Rosenthal, *The `ℒ_p` spaces*, Israel J. Math. **7** (1969), 325–349.
-/

public section

open scoped NNReal

namespace ContinuousLinearMap

section NontriviallyNormedField

universe u v w

variable {𝕜 : Type u} {E : Type v} {F : Type w} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The Gelfand numbers of the adjoint are bounded above by the Kolmogorov numbers of the
operator: `cₙ(T') ≤ dₙ(T)`. No Hahn–Banach or completeness hypothesis is needed. -/
theorem gelfandNumber_precomp_le (T : E →L[𝕜] F) (n : ℕ) :
    (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).gelfandNumber n ≤
      T.kolmogorovNumber n := by
  refine le_kolmogorovNumber_iff.mpr fun V hV ↦ ?_
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
  have hcodim :
      Module.rank 𝕜 (StrongDual 𝕜 F ⧸ V.orthogonalBilin (topDualPairing 𝕜 F).flip) ≤ n := by
    have h := V.rank_quotient_orthogonalBilin_topDualPairing_flip_le.trans
      (Cardinal.lift_le.mpr hV)
    simpa only [Cardinal.lift_natCast, Cardinal.lift_le_nat_iff] using h
  refine ((ContinuousLinearMap.precomp 𝕜 T).gelfandNumber_le hcodim).trans ?_
  rw [← V.quotientDualEquivAnnihilator.nnNorm_comp_toContinuousLinearMap,
    V.precomp_comp_subtypeL_comp_quotientDualEquivAnnihilator]
  exact_mod_cast ContinuousLinearMap.norm_precomp_le (V.mkQL.comp T)

/-- Pointwise quotient-norm estimate for a unit vector `x` when `T x` lies within `ε` of a vector
`y` whose image under `J_F : F →L[𝕜] F''` belongs to a subspace `U ≥ W` admitting a
`(1 + ε)`-bounded linear operator `R : U →L[𝕜] F` that inverts `J_F` on `U`. -/
private theorem norm_mkQL_map_comap_comp_apply_le {E'' F'' : Type*}
    [SeminormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    [SeminormedAddCommGroup F''] [NormedSpace 𝕜 F'']
    (T : E →L[𝕜] F) (T'' : E'' →L[𝕜] F'') (J_E : E →L[𝕜] E'') (J_F : F →L[𝕜] F'')
    (hJ_E : ∀ x, ‖J_E x‖ ≤ ‖x‖) (hJ_F : ∀ y, ‖J_F y‖ ≤ ‖y‖)
    (hnat : ∀ x, T'' (J_E x) = J_F (T x)) {W U : Submodule 𝕜 F''} (hWU : W ≤ U)
    (R : U →L[𝕜] F) {ε : ℝ} (hε : 0 < ε) (hR : ∀ u : U, ‖R u‖ ≤ (1 + ε) * ‖u‖)
    (hR_id : ∀ (u : U) (y : F), (u : F'') = J_F y → R u = y)
    {x : E} (hx : ‖x‖ = 1) {y : F} (hyU : J_F y ∈ U) (hyx : ‖T x - y‖ < ε) :
    ‖(((W.comap U.subtype).map R.toLinearMap).mkQL ∘L T) x‖ ≤
      (1 + ε) * ‖W.mkQL ∘L T''‖ + (2 + ε) * ε := by
  let V : Submodule 𝕜 F := (W.comap U.subtype).map R.toLinearMap
  have hJx : ‖J_E x‖ ≤ 1 := (hJ_E x).trans hx.le
  have hJTx : ‖(Submodule.Quotient.mk (J_F (T x)) : F'' ⧸ W)‖ ≤ ‖W.mkQL ∘L T''‖ := by
    simpa only [← hnat x, comp_apply, Submodule.coe_mkQL, Submodule.mkQ_apply, mul_one] using
      ((W.mkQL ∘L T'').le_opNorm _).trans (mul_le_mul_of_nonneg_left hJx (norm_nonneg _))
  have hJy : ‖(Submodule.Quotient.mk (J_F y) : F'' ⧸ W)‖ < ‖W.mkQL ∘L T''‖ + ε := by
    have hsub : J_F y = J_F (T x) - J_F (T x - y) := by simp [map_sub]
    rw [hsub, Submodule.Quotient.mk_sub]
    calc ‖(Submodule.Quotient.mk (J_F (T x)) : F'' ⧸ W) - Submodule.Quotient.mk (J_F (T x - y))‖
      _ ≤ ‖(Submodule.Quotient.mk (J_F (T x)) : F'' ⧸ W)‖ +
            ‖(Submodule.Quotient.mk (J_F (T x - y)) : F'' ⧸ W)‖ := norm_sub_le _ _
      _ ≤ ‖W.mkQL ∘L T''‖ + ‖T x - y‖ :=
            add_le_add hJTx ((Submodule.Quotient.norm_mk_le W _).trans (hJ_F _))
      _ < ‖W.mkQL ∘L T''‖ + ε := by linarith
  obtain ⟨z, hz_eq, hz_lt⟩ := (QuotientAddGroup.norm_lt_iff (S := W.toAddSubgroup)).mp hJy
  have hw : J_F y - z ∈ W := (Submodule.Quotient.eq W).mp hz_eq.symm
  have hzU : z ∈ U := by simpa only [sub_sub_cancel] using U.sub_mem hyU (hWU hw)
  let v : F := R ⟨J_F y - z, hWU hw⟩
  have hvV : v ∈ V := ⟨⟨J_F y - z, hWU hw⟩, hw, rfl⟩
  have hy_sub_v : y - v = R ⟨z, hzU⟩ := by
    rw [← hR_id ⟨J_F y, hyU⟩ y rfl, ← map_sub]
    exact congrArg R (Subtype.ext (by simp [sub_sub_cancel]))
  have hquot : V.mkQL (T x) = Submodule.Quotient.mk (T x - v) := by
    symm
    simpa only [Submodule.coe_mkQL, Submodule.mkQ_apply, Submodule.Quotient.eq,
      sub_sub_cancel_left, neg_mem_iff] using hvV
  calc ‖(V.mkQL ∘L T) x‖ = ‖(Submodule.Quotient.mk (T x - v) : F ⧸ V)‖ := by
        rw [comp_apply, hquot]
    _ ≤ ‖(T x - y) + (y - v)‖ := by
        simpa only [sub_add_sub_cancel] using Submodule.Quotient.norm_mk_le V (T x - v)
    _ ≤ ‖T x - y‖ + ‖R ⟨z, hzU⟩‖ := hy_sub_v ▸ norm_add_le _ _
    _ ≤ ε + (1 + ε) * (‖W.mkQL ∘L T''‖ + ε) :=
        add_le_add hyx.le ((hR ⟨z, hzU⟩).trans
          (mul_le_mul_of_nonneg_left hz_lt.le (by positivity)))
    _ = (1 + ε) * ‖W.mkQL ∘L T''‖ + (2 + ε) * ε := by ring

end NontriviallyNormedField

section IsRCLikeNormedField

universe u v w

variable {𝕜 : Type u} {E : Type v} {F : Type w}
  [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over an `IsRCLikeNormedField`, the Kolmogorov numbers of the adjoint equal the Gelfand numbers
of the operator: `dₙ(T') = cₙ(T)`. -/
@[simp]
theorem kolmogorovNumber_precomp (T : E →L[𝕜] F) (n : ℕ) :
    (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).kolmogorovNumber n =
      T.gelfandNumber n := by
  let _ : SeminormedAddCommGroup (StrongDual 𝕜 E) := inferInstance
  let _ : NormedSpace 𝕜 (StrongDual 𝕜 E) := inferInstance
  let _ : SeminormedAddCommGroup (StrongDual 𝕜 F) := inferInstance
  let _ : NormedSpace 𝕜 (StrongDual 𝕜 F) := inferInstance
  let T' : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E := ContinuousLinearMap.precomp 𝕜 T
  have hnorm (M : Submodule 𝕜 E) :
      ‖(M.orthogonalBilin (topDualPairing 𝕜 E).flip).mkQL ∘L T'‖₊ = ‖T ∘L M.subtypeL‖₊ := by
    rw [← M.quotientAnnihilatorEquivDual.nnNorm_toContinuousLinearMap_comp,
      M.quotientAnnihilatorEquivDual_comp_mkQL_comp_precomp, ContinuousLinearMap.nnnorm_precomp]
  apply le_antisymm
  · refine le_gelfandNumber_iff.mpr fun M _ hM ↦ ?_
    have : FiniteDimensional 𝕜 (E ⧸ M) :=
      Module.rank_lt_aleph0_iff.mp (hM.trans_lt Cardinal.natCast_lt_aleph0)
    have hrank : Module.rank 𝕜 (M.orthogonalBilin (topDualPairing 𝕜 E).flip) ≤ n := by
      have h := M.rank_orthogonalBilin_topDualPairing_flip_le.trans (Cardinal.lift_le.mpr hM)
      simpa only [Cardinal.lift_natCast, Cardinal.lift_le_nat_iff] using h
    exact (T'.kolmogorovNumber_le hrank).trans_eq (hnorm M)
  · refine le_kolmogorovNumber_iff.mpr fun G hG ↦ ?_
    have : FiniteDimensional 𝕜 G :=
      Module.rank_lt_aleph0_iff.mp (hG.trans_lt Cardinal.natCast_lt_aleph0)
    let M := G.orthogonalBilin (topDualPairing 𝕜 E)
    have hM : Module.rank 𝕜 (E ⧸ M) ≤ n := by
      rw [G.rank_quotient_orthogonalBilin_topDualPairing_eq_finrank]
      exact Nat.cast_le.mpr (Nat.cast_le.mp ((Module.finrank_eq_rank 𝕜 G).trans_le hG))
    have hMG : ‖(M.orthogonalBilin (topDualPairing 𝕜 E).flip).mkQL ∘L T'‖₊ = ‖G.mkQL ∘L T'‖₊ :=
      congrArg (fun W : Submodule 𝕜 (StrongDual 𝕜 E) ↦ ‖W.mkQL ∘L T'‖₊)
        G.orthogonalBilin_orthogonalBilin_topDualPairing_flip_eq_of_finiteDimensional
    exact (T.gelfandNumber_le hM).trans_eq ((hnorm M).symm.trans hMG)

/-- Over an `IsRCLikeNormedField`, the Kolmogorov numbers of the bidual operator `T''` are at most
those of `T`: `dₙ(T'') ≤ dₙ(T)`. -/
theorem kolmogorovNumber_precomp_precomp_le (T : E →L[𝕜] F) (n : ℕ) :
    kolmogorovNumber (𝕜 := 𝕜) (E := StrongDual 𝕜 (StrongDual 𝕜 E))
      (F := StrongDual 𝕜 (StrongDual 𝕜 F))
      (ContinuousLinearMap.precomp 𝕜
        (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
          StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)) n ≤
      T.kolmogorovNumber n := by
  rw [kolmogorovNumber_precomp]
  exact T.gelfandNumber_precomp_le n

/-- Local-reflexivity upper bound `dₙ(T) ≤ cₙ(T')` on a Hausdorff normed codomain `F₀`: every
subspace `W ≤ F₀''` of rank at most `n` and every `ε`-net of `T '' closedBall 0 1` pull back to a
subspace `V ≤ F₀` of rank at most `n` with `‖V.mkQL ∘L T‖ ≤ (1 + ε) ‖W.mkQL ∘L T''‖ + (2 + ε) ε`. -/
private theorem kolmogorovNumber_le_gelfandNumber_precomp_of_totallyBounded_image_closedBall_normed
    {F₀ : Type w} [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀] (T : E →L[𝕜] F₀)
    (hT : TotallyBounded (T '' Metric.closedBall 0 1)) (n : ℕ) :
    T.kolmogorovNumber n ≤
      (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F₀ →L[𝕜] StrongDual 𝕜 E).gelfandNumber n := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let E'' := StrongDual 𝕜 (StrongDual 𝕜 E)
  let F₀'' := StrongDual 𝕜 (StrongDual 𝕜 F₀)
  let _ : SeminormedAddCommGroup E'' := inferInstance
  let _ : NormedSpace 𝕜 E'' := inferInstance
  let _ : NormedAddCommGroup F₀'' := inferInstance
  let _ : NormedSpace 𝕜 F₀'' := inferInstance
  let T'' : E'' →L[𝕜] F₀'' := ContinuousLinearMap.precomp 𝕜
    (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F₀ →L[𝕜] StrongDual 𝕜 E)
  let J : F₀ →L[𝕜] F₀'' := NormedSpace.inclusionInDoubleDual 𝕜 F₀
  rw [← kolmogorovNumber_precomp]
  refine le_kolmogorovNumber_iff (𝕜 := 𝕜) (E := E'') (F := F₀'').mpr fun W hW ↦
    NNReal.coe_le_coe.mp ?_
  rw [coe_nnNorm]
  have hc : Continuous (fun ε : ℝ ↦ (1 + ε) * ‖W.mkQL ∘L T''‖ + (2 + ε) * ε) := by fun_prop
  have hlim : Filter.Tendsto (fun ε : ℝ ↦ (1 + ε) * ‖W.mkQL ∘L T''‖ + (2 + ε) * ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ‖W.mkQL ∘L T''‖) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim (Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε ↦ ?_)
  rw [Set.mem_Ioi] at hε
  obtain ⟨t, -, ht_fin, ht_cov⟩ := Metric.finite_approx_of_totallyBounded hT ε hε
  have : FiniteDimensional 𝕜 W :=
    Module.rank_lt_aleph0_iff.mp (hW.trans_lt Cardinal.natCast_lt_aleph0)
  have : FiniteDimensional 𝕜 (Submodule.span 𝕜 (J '' t)) :=
    FiniteDimensional.span_of_finite 𝕜 (ht_fin.image J)
  let U : Submodule 𝕜 F₀'' := W ⊔ Submodule.span 𝕜 (J '' t)
  have : FiniteDimensional 𝕜 U := Submodule.finiteDimensional_sup W _
  obtain ⟨R, hR, -, hR_id⟩ := LinearIsometry.exists_continuousLinearMap_of_doubleDual_norm_le_mul
    (𝕜 := 𝕜) (E := F₀) (V := U) U.subtypeₗᵢ ⊥ hε
  let V : Submodule 𝕜 F₀ := (W.comap U.subtype).map R.toLinearMap
  have hV : Module.rank 𝕜 V ≤ n := by
    have hr := (lift_rank_map_le R.toLinearMap (W.comap U.subtype)).trans (Cardinal.lift_le.mpr
      ((Submodule.comapSubtypeEquivOfLe (le_sup_left : W ≤ U)).rank_eq.trans_le hW))
    simpa only [Cardinal.lift_natCast, Cardinal.lift_le_nat_iff] using hr
  refine (NNReal.coe_le_coe.mpr (T.kolmogorovNumber_le hV)).trans ?_
  refine opNorm_le_of_unit_norm (by positivity) fun x hx ↦ ?_
  obtain ⟨y, hy, hyx⟩ := Set.mem_iUnion₂.mp
    (ht_cov ⟨x, by simp [Metric.mem_closedBall, hx.le], rfl⟩)
  rw [Metric.mem_ball, dist_eq_norm] at hyx
  exact norm_mkQL_map_comap_comp_apply_le T T'' (NormedSpace.inclusionInDoubleDual 𝕜 E) J
    (NormedSpace.double_dual_bound 𝕜 E) (NormedSpace.double_dual_bound 𝕜 F₀)
    T.precomp_precomp_inclusionInDoubleDual le_sup_left R hε (fun u ↦ (hR u).1) hR_id hx
    (Submodule.mem_sup_right (Submodule.subset_span ⟨y, hy, rfl⟩)) hyx

/-- Over an `IsRCLikeNormedField`, if `T` maps the closed unit ball to a totally bounded set, then
the Gelfand numbers of the adjoint equal the Kolmogorov numbers of `T`: `cₙ(T') = dₙ(T)`. Neither
completeness nor separation of `E` or `F` is required. -/
theorem gelfandNumber_precomp_of_totallyBounded_image_closedBall (T : E →L[𝕜] F)
    (hT : TotallyBounded (T '' Metric.closedBall 0 1)) (n : ℕ) :
    (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).gelfandNumber n =
      T.kolmogorovNumber n := by
  refine (T.gelfandNumber_precomp_le n).antisymm ?_
  -- Pass to the Hausdorff normed quotient `SeparationQuotient F`.
  let J : F →ₗᵢ[𝕜] SeparationQuotient F :=
    ⟨(SeparationQuotient.mkCLM 𝕜 F).toLinearMap, SeparationQuotient.norm_mk⟩
  let QT : E →L[𝕜] SeparationQuotient F := J.toContinuousLinearMap ∘L T
  have hQT : TotallyBounded (QT '' Metric.closedBall 0 1) := by
    rw [coe_comp, Set.image_comp]
    exact hT.image J.toContinuousLinearMap.uniformContinuous
  rw [← T.kolmogorovNumber_linearIsometry_comp_of_surjective (J := J)
    SeparationQuotient.surjective_mk n]
  refine (kolmogorovNumber_le_gelfandNumber_precomp_of_totallyBounded_image_closedBall_normed
    QT hQT n).trans ?_
  -- Since `(J ∘L T)' = T' ∘L J'` and `‖J'‖ ≤ 1`, its Gelfand numbers are `≤ cₙ(T')`.
  let T' : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E := ContinuousLinearMap.precomp 𝕜 T
  let Q' : StrongDual 𝕜 (SeparationQuotient F) →L[𝕜] StrongDual 𝕜 F :=
    ContinuousLinearMap.precomp 𝕜 J.toContinuousLinearMap
  have hQT_adj :
      (ContinuousLinearMap.precomp 𝕜 QT :
        StrongDual 𝕜 (SeparationQuotient F) →L[𝕜] StrongDual 𝕜 E) = T' ∘L Q' :=
    ContinuousLinearMap.precomp_comp T J.toContinuousLinearMap
  rw [hQT_adj]
  have hQ_norm : ‖Q'‖₊ ≤ 1 := by
    exact_mod_cast (ContinuousLinearMap.norm_precomp_le (Z := 𝕜) J.toContinuousLinearMap).trans
      J.norm_toContinuousLinearMap_le
  have hid_le : ‖ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E)‖₊ ≤ 1 := by
    exact_mod_cast norm_id_le
  have hideal := gelfandNumber_comp_comp_le (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E)) T' Q' n
  rw [id_comp] at hideal
  refine hideal.trans ?_
  calc ‖ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E)‖₊ * T'.gelfandNumber n * ‖Q'‖₊
      ≤ 1 * T'.gelfandNumber n * 1 := by gcongr
    _ = T'.gelfandNumber n := by simp

/-- Over an `IsRCLikeNormedField`, if `T` maps the closed unit ball to a totally bounded set, then
the Kolmogorov numbers of the bidual operator `T''` equal those of `T`: `dₙ(T'') = dₙ(T)`. -/
theorem kolmogorovNumber_precomp_precomp_of_totallyBounded_image_closedBall (T : E →L[𝕜] F)
    (hT : TotallyBounded (T '' Metric.closedBall 0 1)) (n : ℕ) :
    kolmogorovNumber (𝕜 := 𝕜) (E := StrongDual 𝕜 (StrongDual 𝕜 E))
      (F := StrongDual 𝕜 (StrongDual 𝕜 F))
      (ContinuousLinearMap.precomp 𝕜
        (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
          StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)) n =
      T.kolmogorovNumber n := by
  rw [kolmogorovNumber_precomp, T.gelfandNumber_precomp_of_totallyBounded_image_closedBall hT]

/-- Over an `IsRCLikeNormedField`, if `T` is a compact operator, then the Gelfand numbers of its
adjoint equal the Kolmogorov numbers of `T`: `cₙ(T') = dₙ(T)`. -/
theorem _root_.IsCompactOperator.gelfandNumber_precomp {T : E →L[𝕜] F}
    (hT : IsCompactOperator T) (n : ℕ) :
    (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).gelfandNumber n =
      T.kolmogorovNumber n := by
  obtain ⟨K, hK, hKT⟩ := hT.image_closedBall_subset_compact (𝕜₁ := 𝕜) (𝕜₂ := 𝕜) 1
  exact T.gelfandNumber_precomp_of_totallyBounded_image_closedBall (hK.totallyBounded.subset hKT) n

/-- Over an `IsRCLikeNormedField`, if `T` is a compact operator, then the Kolmogorov numbers of
its bidual `T''` equal those of `T`: `dₙ(T'') = dₙ(T)`. -/
theorem _root_.IsCompactOperator.kolmogorovNumber_precomp_precomp {T : E →L[𝕜] F}
    (hT : IsCompactOperator T) (n : ℕ) :
    kolmogorovNumber (𝕜 := 𝕜) (E := StrongDual 𝕜 (StrongDual 𝕜 E))
      (F := StrongDual 𝕜 (StrongDual 𝕜 F))
      (ContinuousLinearMap.precomp 𝕜
        (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
          StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)) n =
      T.kolmogorovNumber n := by
  rw [kolmogorovNumber_precomp, hT.gelfandNumber_precomp]

/-- Over an `IsRCLikeNormedField`, an operator with finite-dimensional range satisfies
`cₙ(T') = dₙ(T)`. -/
theorem gelfandNumber_precomp_of_finiteDimensional_range (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 T.range] (n : ℕ) :
    (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).gelfandNumber n =
      T.kolmogorovNumber n := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  have := FiniteDimensional.proper_rclike 𝕜 𝕜
  have hfin : (T : E →ₗ[𝕜] F).HasFiniteRange := Submodule.FG.of_finite
  exact hfin.isCompactOperator.gelfandNumber_precomp n

/-- Over an `IsRCLikeNormedField`, an operator with finite-dimensional range satisfies
`dₙ(T'') = dₙ(T)`. -/
theorem kolmogorovNumber_precomp_precomp_of_finiteDimensional_range (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 T.range] (n : ℕ) :
    kolmogorovNumber (𝕜 := 𝕜) (E := StrongDual 𝕜 (StrongDual 𝕜 E))
      (F := StrongDual 𝕜 (StrongDual 𝕜 F))
      (ContinuousLinearMap.precomp 𝕜
        (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
          StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)) n =
      T.kolmogorovNumber n := by
  rw [kolmogorovNumber_precomp, T.gelfandNumber_precomp_of_finiteDimensional_range]

end IsRCLikeNormedField

end ContinuousLinearMap

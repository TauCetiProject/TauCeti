/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import TauCeti.Analysis.Normed.Operator.LinearPMap.Relative.Compact
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.InnerProductSpace.LinearPMap.KatoRellich
import TauCeti.Analysis.Normed.Operator.Dense

/-!
# Relatively compact perturbations on Hilbert space

Let `A : E →ₗ.[𝕜] F` be a closable partial linear map between Hilbert spaces over an `RCLike`
field, and let `V` be `A`-compact (`LinearPMap.IsRelativelyCompact`). Then `V` has `A`-bound zero:
for every `ε > 0` there is an `a` with `‖V x‖ ≤ a ‖x‖ + ε ‖A x‖` on `dom A`
(`LinearPMap.IsRelativelyCompact.exists_isRelativelyBounded`; Teschl, Lemma 6.22, and Kato,
§IV.1.3). Closability cannot be dropped: for a discontinuous linear functional `φ` on a
dense subspace and a unit vector `e`, the map `A = V = φ(·) e` is `A`-compact with `A`-bound one.

Consequently `V` stays compact relative to `A + V` (Teschl, Lemma 6.23). Over any `RCLike` field,
a symmetric `A`-compact perturbation of a self-adjoint `A` is self-adjoint on `dom A`, by the
Kato–Rellich theorem (`IsSelfAdjoint.add_of_isRelativelyCompact`), and the resolvents of `A + V`
and `A` differ by a compact operator at every nonreal point, the input of Weyl's theorem.

## Main declarations

* `LinearPMap.IsRelativelyCompact.exists_isRelativelyBounded`: for closable `A`, relative
  compactness gives relative bound zero.
* `LinearPMap.IsRelativelyCompact.add_right`, `LinearPMap.IsRelativelyCompact.add_right_self`: for
  closable `A` and `A`-compact `V`, every `A`-compact map, in particular `V`, is
  `(A + V)`-compact.
* `IsSelfAdjoint.add_of_isRelativelyCompact`: symmetric relatively compact perturbations of a
  self-adjoint operator are self-adjoint.
* `IsSelfAdjoint.isCompactOperator_resolvent_add_sub_of_isRelativelyCompact`: the resolvent
  difference is compact at every nonreal point.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, AMS (2009), Lemmas 6.22 and 6.23.
* T. Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Springer (1976), §IV.1.3 and
  Theorem V.4.3.
-/

public section

open Filter Topology
open scoped InnerProductSpace

namespace LinearPMap

variable {𝕜 E F G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- For a closable `A` and a sequence `uₙ → 0` of `dom A` with `‖A uₙ‖ ≤ 1`, the vectors `A uₙ`
tend to zero weakly. -/
private theorem tendsto_inner_apply_of_isClosable {A : E →ₗ.[𝕜] F} (hA : A.IsClosable)
    {u : ℕ → A.domain} (hu : Tendsto (fun n ↦ (u n : E)) atTop (𝓝 0))
    (hAu : ∀ n, ‖A (u n)‖ ≤ 1) (k : F) : Tendsto (fun n ↦ ⟪A (u n), k⟫_𝕜) atTop (𝓝 0) := by
  let e := WithLp.prodContinuousLinearEquiv 2 𝕜 E F
  let S : Submodule 𝕜 (WithLp 2 (E × F)) := A.graph.comap e.toLinearMap
  -- The second coordinates of the vectors orthogonal to the graph.
  let D : Submodule 𝕜 F :=
    Sᗮ.map ((LinearMap.snd 𝕜 E F).comp (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap)
  have horth (w : WithLp 2 (E × F)) (hw : w ∈ Sᗮ) (x : A.domain) :
      ⟪(x : E), (WithLp.ofLp w).1⟫_𝕜 + ⟪A x, (WithLp.ofLp w).2⟫_𝕜 = 0 := by
    have hx : WithLp.toLp 2 ((x : E), A x) ∈ S := by
      rw [Submodule.mem_comap]
      simp [e]
    simpa [WithLp.prod_inner_apply] using (Submodule.mem_orthogonal S w).1 hw _ hx
  -- Closability makes these second coordinates dense.
  have hdense : Dense (D : Set F) := by
    refine Submodule.dense_iff_topologicalClosure_eq_top.2
      (Submodule.topologicalClosure_eq_top_iff.2 ((Submodule.eq_bot_iff _).2 fun c hc ↦ ?_))
    have h0c : WithLp.toLp 2 ((0 : E), c) ∈ S.topologicalClosure := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure]
      refine (Submodule.mem_orthogonal' _ _).2 fun w hw ↦ ?_
      have hwD : (WithLp.ofLp w).2 ∈ D := ⟨w, hw, rfl⟩
      simpa [WithLp.prod_inner_apply] using (Submodule.mem_orthogonal' D c).1 hc _ hwD
    have hcl : ((0 : E), c) ∈ _root_.closure (A.graph : Set (E × F)) := by
      have hsub : (S.topologicalClosure : Set (WithLp 2 (E × F))) ⊆
          e ⁻¹' A.graph.topologicalClosure :=
        closure_minimal (fun s hs ↦ Submodule.le_topologicalClosure _ hs)
          ((Submodule.isClosed_topologicalClosure _).preimage e.continuous)
      simpa [e] using hsub h0c
    obtain ⟨f', hf'⟩ := hA
    rw [← Submodule.topologicalClosure_coe, hf'] at hcl
    exact f'.graph_fst_eq_zero_snd hcl rfl
  have hD (b : F) (hb : b ∈ D) : Tendsto (fun n ↦ ⟪A (u n), b⟫_𝕜) atTop (𝓝 0) := by
    obtain ⟨w, hw, rfl⟩ := hb
    have hw' : Tendsto (fun n ↦ -⟪(u n : E), (WithLp.ofLp w).1⟫_𝕜) atTop (𝓝 0) := by
      have hc : Continuous fun x : E ↦ ⟪x, (WithLp.ofLp w).1⟫_𝕜 :=
        continuous_id.inner continuous_const
      simpa using ((hc.tendsto 0).comp hu).neg
    refine hw'.congr fun n ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply,
      LinearEquiv.coe_coe, WithLp.coe_linearEquiv]
    linear_combination (horth w hw (u n)).symm
  have := ContinuousLinearMap.tendsto_apply_of_dense hdense (l := atTop)
    (f := fun n ↦ innerSL 𝕜 (A (u n))) (g := 0) (C := 1)
    (.of_forall fun n ↦ (innerSL_apply_norm 𝕜 _).trans_le (hAu n))
    (fun b hb ↦ by simpa using hD b hb) k
  simpa using this

omit [CompleteSpace E] [CompleteSpace F] in
/-- For an `A`-bounded `V`, every functional of `V x` is a continuous functional of `(x, A x)`,
by Hahn–Banach on the graph of `A`. -/
private theorem exists_dual_apply_eq_of_isRelativelyBounded {A : E →ₗ.[𝕜] F} {V : E →ₗ.[𝕜] G}
    {a b : ℝ} (hV : V.IsRelativelyBounded A a b) (f : StrongDual 𝕜 G) :
    ∃ g : StrongDual 𝕜 (E × F), ∀ x : A.domain,
      f (V ⟨x, hV.domain_le x.2⟩) = g ((x : E), A x) := by
  let L : A.domain →ₗ[𝕜] E × F := A.domain.subtype.prod A.toFun
  have hL : Function.Injective L := fun x y h ↦ Subtype.ext (congrArg Prod.fst h)
  let Φ : A.domain →ₗ[𝕜] 𝕜 :=
    (f : G →ₗ[𝕜] 𝕜) ∘ₗ V.toFun ∘ₗ Submodule.inclusion hV.domain_le
  let ψ : LinearMap.range L →ₗ[𝕜] 𝕜 := Φ ∘ₗ (LinearEquiv.ofInjective L hL).symm.toLinearMap
  have hψ (x : A.domain) : ψ ⟨L x, x, rfl⟩ = f (V ⟨x, hV.domain_le x.2⟩) := by
    have hx : (LinearEquiv.ofInjective L hL).symm ⟨L x, x, rfl⟩ = x :=
      (LinearEquiv.ofInjective L hL).symm_apply_eq.2
        (Subtype.ext (LinearEquiv.ofInjective_apply L x).symm)
    simp only [ψ, Φ, LinearMap.comp_apply, LinearEquiv.coe_coe, hx, ContinuousLinearMap.coe_coe,
      LinearPMap.toFun_eq_coe, Submodule.inclusion_apply]
  have hbound (s : LinearMap.range L) : ‖ψ s‖ ≤ ‖f‖ * (|a| + |b|) * ‖s‖ := by
    obtain ⟨_, x, rfl⟩ := s
    have hLx : L x = ((x : E), A x) := by simp [L]
    have hn : ‖(⟨L x, x, rfl⟩ : LinearMap.range L)‖ = max ‖(x : E)‖ ‖A x‖ := by
      rw [← Submodule.norm_coe]
      dsimp only
      rw [hLx, Prod.norm_def]
    rw [hψ, hn]
    refine (f.le_opNorm _).trans ?_
    rw [mul_assoc]
    gcongr
    refine (hV.norm_apply_le x).trans ?_
    have h₁ : a * ‖(x : E)‖ ≤ |a| * max ‖(x : E)‖ ‖A x‖ :=
      (mul_le_mul_of_nonneg_right (le_abs_self a) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (abs_nonneg a))
    have h₂ : b * ‖A x‖ ≤ |b| * max ‖(x : E)‖ ‖A x‖ :=
      (mul_le_mul_of_nonneg_right (le_abs_self b) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg b))
    linarith
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range L) (ψ.mkContinuous _ hbound)
  refine ⟨g, fun x ↦ ?_⟩
  rw [← hψ, ← LinearMap.mkContinuous_apply ψ _ hbound, ← hg]
  simp [L]

/-- For a closable `A`, an `A`-bounded `V` and a sequence `uₙ → 0` of `dom A` with `‖A uₙ‖ ≤ 1`,
the vectors `V uₙ` tend to zero weakly. -/
private theorem tendsto_dual_apply_of_isClosable {A : E →ₗ.[𝕜] F} {V : E →ₗ.[𝕜] G}
    (hA : A.IsClosable) {a b : ℝ} (hV : V.IsRelativelyBounded A a b) {u : ℕ → A.domain}
    (hu : Tendsto (fun n ↦ (u n : E)) atTop (𝓝 0)) (hAu : ∀ n, ‖A (u n)‖ ≤ 1)
    (f : StrongDual 𝕜 G) : Tendsto (fun n ↦ f (V ⟨u n, hV.domain_le (u n).2⟩)) atTop (𝓝 0) := by
  obtain ⟨g, hg⟩ := exists_dual_apply_eq_of_isRelativelyBounded hV f
  have hsplit (n : ℕ) : f (V ⟨u n, hV.domain_le (u n).2⟩) =
      g (ContinuousLinearMap.inl 𝕜 E F (u n)) + g (ContinuousLinearMap.inr 𝕜 E F (A (u n))) := by
    rw [hg, ← _root_.map_add g]
    simp
  have h₁ : Tendsto (fun n ↦ g (ContinuousLinearMap.inl 𝕜 E F (u n))) atTop (𝓝 0) := by
    simpa [Function.comp_def, Prod.mk_zero_zero] using
      ((g.comp (ContinuousLinearMap.inl 𝕜 E F)).continuous.tendsto 0).comp hu
  -- The second coordinate is represented by a vector `k` of the Hilbert space `F`.
  set k := (InnerProductSpace.toDual 𝕜 F).symm (g.comp (ContinuousLinearMap.inr 𝕜 E F))
  have h₂ : Tendsto (fun n ↦ g (ContinuousLinearMap.inr 𝕜 E F (A (u n)))) atTop (𝓝 0) := by
    have hk (y : F) : g (ContinuousLinearMap.inr 𝕜 E F y) = ⟪k, y⟫_𝕜 := by
      rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply]
    simp_rw [hk]
    have := ((RCLike.continuous_conj (K := 𝕜)).tendsto 0).comp
      (tendsto_inner_apply_of_isClosable hA hu hAu k)
    rw [_root_.map_zero] at this
    exact this.congr fun n ↦ inner_conj_symm _ _
  simp_rw [hsplit]
  simpa using h₁.add h₂

/-- **A relatively compact map has relative bound zero** (Teschl, Lemma 6.22; Kato, §IV.1.3).
Let `A` be a closable partial linear map between Hilbert spaces. If `V` is `A`-compact, then for
every `ε > 0` there is an `a` with `‖V x‖ ≤ a ‖x‖ + ε ‖A x‖` on `dom A`. -/
theorem IsRelativelyCompact.exists_isRelativelyBounded {A : E →ₗ.[𝕜] F} {V : E →ₗ.[𝕜] G}
    (hV : V.IsRelativelyCompact A) (hA : A.IsClosable) {ε : ℝ} (hε : 0 < ε) :
    ∃ a, V.IsRelativelyBounded A a ε := by
  by_contra! hcon
  choose u hu1 hu2 using fun n : ℕ ↦
    exists_normalized_of_not_isRelativelyBounded hV.domain_le (hcon n)
  obtain ⟨K, hK, hKV⟩ := hV.exists_isCompact 1
  have hmem (n : ℕ) : V ⟨u n, hV.domain_le (u n).2⟩ ∈ K := hKV (u n) (hu1 n).le
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  have hAu (n : ℕ) : ‖A (u n)‖ ≤ 1 := by linarith [hu1 n, norm_nonneg (u n : E)]
  have hu0 : Tendsto (fun n ↦ ‖(u n : E)‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat M)
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [le_div_iff₀ (by exact_mod_cast hn)]
    nlinarith [hu2 n, hM _ (hmem n), mul_nonneg hε.le (norm_nonneg (A (u n)))]
  obtain ⟨w, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hw : ε ≤ ‖w‖ := by
    have h₁ : Tendsto (fun n ↦ ε * (1 - ‖(u (φ n) : E)‖)) atTop (𝓝 ε) := by
      simpa using ((hu0.comp hφ.tendsto_atTop).const_sub 1).const_mul ε
    refine le_of_tendsto_of_tendsto' h₁ hlim.norm fun n ↦ ?_
    have h₂ : 1 - ‖(u (φ n) : E)‖ = ‖A (u (φ n))‖ := by linarith [hu1 (φ n)]
    rw [h₂]
    have := hu2 (φ n)
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) (φ n)) (norm_nonneg (u (φ n) : E))
    simp only [Function.comp_apply]
    linarith
  obtain ⟨C, hC⟩ := hV.exists_isRelativelyBounded_const
  have hu : Tendsto (fun n ↦ (u n : E)) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.2 hu0
  have hw0 : w = 0 := SeparatingDual.eq_zero_of_forall_dual_eq_zero fun f ↦
    tendsto_nhds_unique ((f.continuous.tendsto w).comp hlim)
      ((tendsto_dual_apply_of_isClosable hA hC hu hAu f).comp hφ.tendsto_atTop)
  rw [hw0, norm_zero] at hw
  linarith

/-- **Relatively compact perturbations preserve relative compactness.** If `A` is closable and
`V` is `A`-compact, then every `A`-compact `W` is `(A + V)`-compact. -/
theorem IsRelativelyCompact.add_right {S H : Type*} [Ring S] {σ : 𝕜 →+* S} [AddCommGroup H]
    [TopologicalSpace H] [Module S H] {A V : E →ₗ.[𝕜] F} {W : E →ₛₗ.[σ] H}
    (hW : W.IsRelativelyCompact A) (hV : V.IsRelativelyCompact A) (hA : A.IsClosable) :
    W.IsRelativelyCompact (A + V) := by
  obtain ⟨a, ha⟩ := hV.exists_isRelativelyBounded hA one_half_pos
  exact hW.add_right_of_isRelativelyBounded ha (by norm_num)

/-- **A relatively compact perturbation stays relatively compact** (Teschl, Lemma 6.23). If `A`
is closable and `V` is `A`-compact, then `V` is `(A + V)`-compact. -/
theorem IsRelativelyCompact.add_right_self {A V : E →ₗ.[𝕜] F} (hV : V.IsRelativelyCompact A)
    (hA : A.IsClosable) : V.IsRelativelyCompact (A + V) :=
  hV.add_right hV hA

end LinearPMap

open LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {A V : E →ₗ.[𝕜] E}

/-- **Relatively compact perturbations preserve self-adjointness.** If `A` is self-adjoint and
`V` is symmetric and `A`-compact, then `A + V`, with domain `dom A`, is self-adjoint. -/
theorem IsSelfAdjoint.add_of_isRelativelyCompact (hA : IsSelfAdjoint A)
    (hV : V.IsFormalAdjoint V) (hAV : V.IsRelativelyCompact A) : IsSelfAdjoint (A + V) := by
  obtain ⟨a, ha⟩ := hAV.exists_isRelativelyBounded hA.isClosed.isClosable one_half_pos
  exact hA.add_of_isRelativelyBounded hV ha (by norm_num)

/-- **Compact resolvent difference of a relatively compact perturbation.** If `A` is
self-adjoint and `V` is symmetric and `A`-compact, then at every `z` with nonzero imaginary part
`R_{A+V}(z) - R_A(z)` is a compact operator. -/
theorem IsSelfAdjoint.isCompactOperator_resolvent_add_sub_of_isRelativelyCompact
    (hA : IsSelfAdjoint A) (hV : V.IsFormalAdjoint V) (hAV : V.IsRelativelyCompact A) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) : IsCompactOperator ((A + V).resolvent z - A.resolvent z) :=
  hAV.isCompactOperator_resolvent_add_sub (hA.mem_resolventSet_of_im_ne_zero hz)
    ((hA.add_of_isRelativelyCompact hV hAV).mem_resolventSet_of_im_ne_zero hz)

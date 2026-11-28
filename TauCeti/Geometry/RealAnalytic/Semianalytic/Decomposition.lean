/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Geometry.RealAlgebraic.SignInvariant
public import TauCeti.Geometry.RealAnalytic.Semianalytic.NormalDecomposition.Basic

import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Analysis.Analytic.SingularDirection
import TauCeti.Analysis.Polynomial.Monic.RootBound
import TauCeti.Data.Set.Lattice
import TauCeti.Geometry.RealAnalytic.Projection
import TauCeti.Geometry.RealAnalytic.Semianalytic.NormalDecomposition.Lift

/-!
# Local normal decomposition of real analytic germs and semianalytic sets

Given finitely many real functions analytic at `x₀ ∈ ℝⁿ` and a prescribed neighborhood `V ∈ 𝓝 x₀`,
there exist an open neighborhood `U ⊆ V` of `x₀` (automatically semianalytic via
`TauCeti.isSemianalytic_of_isNormalDecomposition`) and a normal decomposition `𝒞` of `U`
(`TauCeti.IsNormalDecomposition U 𝒞`) on every piece of which every function of the family has
constant sign (`TauCeti.exists_isNormalDecomposition_signInvariant`). In particular, `U` is a finite
disjoint union of connected, semianalytic real analytic submanifolds with preconnected approach
regions (`TauCeti.IsPreconnectedApproachAt`) at every ambient point of `ℝⁿ`, satisfying both parts
of Łojasiewicz's frontier condition (`(B ∩ closure C).Nonempty → B ⊆ closure C`, and
`B ⊆ closure C`, `B ≠ C → dim B < dim C`), so closures and strict frontiers inside `U` are unions of
pieces via `TauCeti.IsNormalDecomposition.inter_closure_eq_sUnion_of_isOpen` and
`TauCeti.IsNormalDecomposition.inter_closure_sdiff_eq_sUnion_of_isOpen`.

Transporting along linear coordinate equivalences yields coordinate-free local connected,
semianalytic, locally closed partitions in any finite-dimensional real normed space
(`TauCeti.exists_isConnected_partition_signInvariant`). Applying sign-condition normal form to
semianalytic germs yields simultaneous local decompositions compatible with any finite family of
germs semianalytic at `x₀` (`TauCeti.exists_isNormalDecomposition_subset_or_disjoint`,
`TauCeti.exists_isConnected_partition_subset_or_disjoint`), as well as single-germ specializations
and partitions of `s ∩ U` (`TauCeti.SemianalyticAt.exists_isNormalDecomposition`,
`TauCeti.SemianalyticAt.exists_isAnalyticSubmanifold_partition_inter`,
`TauCeti.SemianalyticAt.exists_isConnected_partition_inter`).

The proof inducts on the ambient dimension `n`: after discarding germs vanishing near `x₀` and
applying a continuous linear change of coordinates
(`TauCeti.exists_continuousLinearEquiv_finSucc_forall_analyticOrderAt_ne_top`) to place the
remaining germs in simultaneous Weierstrass general position along the `0`-th coordinate,
`AnalyticAt.exists_weierstrassPreparation_real` factors each germ on a small cylindrical slab up to
a constant unit sign into a shifted monic Weierstrass polynomial whose coefficients vanish at the
base point. Shrinking the base neighborhood bounds those coefficients so that Fujiwara's root bound
(`Polynomial.IsRoot.norm_le_two_mul`) confines all real roots over the base to the open slab height
interval `(t₀ - ε, t₀ + ε)`. Taking the analytic Collins projection
(`TauCeti.exists_analyticOnNhd_projection_delineation`), decomposing a ball inside the base by the
induction hypothesis, lifting to the bounded open slab (`TauCeti.IsNormalDecomposition.lift`), and
pushing forward along the linear equivalence
(`TauCeti.IsNormalDecomposition.image_continuousLinearEquiv`) completes the step.

## Main results

* `TauCeti.exists_isNormalDecomposition_signInvariant`: local normal decomposition of an open
  neighborhood of `x₀ : Fin n → ℝ` on which finitely many analytic germs are sign-invariant.
* `TauCeti.exists_isNormalDecomposition_subset_or_disjoint`,
  `TauCeti.SemianalyticAt.exists_isNormalDecomposition`: local normal decompositions compatible with
  finitely many (or one) semianalytic germs in `Fin n → ℝ`.
* `TauCeti.SemianalyticAt.exists_isAnalyticSubmanifold_partition_inter`: local analytic submanifold
  partition of `s ∩ U` for a semianalytic germ `s` in `Fin n → ℝ`.
* `TauCeti.exists_isConnected_partition_signInvariant`,
  `TauCeti.exists_isConnected_partition_subset_or_disjoint`,
  `TauCeti.SemianalyticAt.exists_isConnected_partition_inter`: coordinate-free versions in any
  finite-dimensional real normed space.

## References

* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS, 1965, §15–18.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §1–2.
* E. Bierstone and P. D. Milman, *Semianalytic and subanalytic sets*, Publications Mathématiques de
  l'IHÉS 67 (1988), 5–42, §2.
* M. Fujiwara, *Über die obere Schranke des absoluten Betrages der Wurzeln einer algebraischen
  Gleichung*, Tôhoku Math. J. 10 (1916), 167–171.
* G. E. Collins, *Quantifier elimination for real closed fields by cylindrical algebraic
  decomposition*, Lecture Notes in Computer Science 33 (1975), 134–183.
* S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Section 5.1 and Chapters 10–11.
* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  Springer (1998), 242–268 (analytic delineability and lifting).
-/

public section

open Filter Function Polynomial Set Topology

namespace TauCeti

/-! ### Shifted Weierstrass polynomials and slab preparation -/

section SlabHelpers

variable {n : ℕ} {ι₁ : Type*} {d : ι₁ → ℕ}

private noncomputable def shiftedMonic {d : ℕ} (t₀ : ℝ) (a : Fin d → ℝ) : ℝ[X] :=
  (TauCeti.Polynomial.monicOfCoeff a).comp (X - C t₀)

private theorem monic_shiftedMonic {d : ℕ} (t₀ : ℝ) (a : Fin d → ℝ) :
    (shiftedMonic t₀ a).Monic :=
  (TauCeti.Polynomial.monic_monicOfCoeff a).comp_X_sub_C t₀

private theorem natDegree_shiftedMonic {d : ℕ} (t₀ : ℝ) (a : Fin d → ℝ) :
    (shiftedMonic t₀ a).natDegree = d := by
  rw [shiftedMonic, natDegree_comp, TauCeti.Polynomial.natDegree_monicOfCoeff,
    natDegree_X_sub_C, mul_one]

private theorem analyticOnNhd_coeff_shiftedMonic {d : ℕ} {B₀ : Set (Fin n → ℝ)} (t₀ : ℝ)
    {c : Fin d → (Fin n → ℝ) → ℝ} (hc : ∀ k, AnalyticOnNhd ℝ (c k) B₀) (m : ℕ) :
    AnalyticOnNhd ℝ (fun z ↦ (shiftedMonic t₀ (c · z)).coeff m) B₀ := by
  have hcoeff (z : Fin n → ℝ) :
      (shiftedMonic t₀ (c · z)).coeff m =
        ((X - C t₀ : ℝ[X]) ^ d).coeff m +
          ∑ k : Fin d, c k z * ((X - C t₀ : ℝ[X]) ^ k.val).coeff m := by
    conv_lhs =>
      rw [shiftedMonic, (TauCeti.Polynomial.monicOfCoeff fun k ↦ c k z).as_sum_range_C_mul_X_pow,
        TauCeti.Polynomial.natDegree_monicOfCoeff, Finset.sum_range_succ,
        ← Fin.sum_univ_eq_sum_range]
    simp [add_comm]
  simp_rw [hcoeff]
  exact analyticOnNhd_const.add <|
    Finset.analyticOnNhd_fun_sum Finset.univ fun k _ ↦ (hc k).mul analyticOnNhd_const

private theorem mem_Ioo_of_isRoot_shiftedMonic {d : ℕ} {t₀ ε : ℝ} (hε : 0 < ε) {a : Fin d → ℝ}
    (ha : ∀ k : Fin d, ‖a k‖ ≤ (ε / 4) ^ (d - k.val)) {t : ℝ}
    (hrt : (shiftedMonic t₀ a).IsRoot t) :
    t ∈ Ioo (t₀ - ε) (t₀ + ε) := by
  have hrt' : (TauCeti.Polynomial.monicOfCoeff a).IsRoot (t - t₀) := by
    rwa [IsRoot.def, shiftedMonic, eval_comp, eval_sub, eval_X, eval_C] at hrt
  have hbnd : ‖t - t₀‖ ≤ 2 * (ε / 4) :=
    hrt'.norm_le_two_mul (TauCeti.Polynomial.monic_monicOfCoeff a) fun k hk ↦ by
      rw [TauCeti.Polynomial.natDegree_monicOfCoeff] at hk ⊢
      simpa [TauCeti.Polynomial.coeff_monicOfCoeff a ⟨k, hk⟩] using ha ⟨k, hk⟩
  rw [Real.norm_eq_abs, abs_sub_le_iff] at hbnd
  exact ⟨by linarith [hbnd.right], by linarith [hbnd.left]⟩

private theorem exists_slab_weierstrass_sign [Finite ι₁]
    {g : ι₁ → (Fin (n + 1) → ℝ) → ℝ} {y₀ : Fin (n + 1) → ℝ} {V₂ : Set (Fin (n + 1) → ℝ)}
    (hg : ∀ j, AnalyticAt ℝ (g j) y₀)
    (hord : ∀ j, analyticOrderAt (fun t ↦ g j (Fin.cons t (Fin.tail y₀))) (y₀ 0) ≠ ⊤)
    (hV₂ : V₂ ∈ 𝓝 y₀) :
    ∃ (d : ι₁ → ℕ) (c : ∀ j, Fin (d j) → (Fin n → ℝ) → ℝ) (u₀ : ι₁ → SignType)
      (B₀ : Set (Fin n → ℝ)) (ε : ℝ),
      IsOpen B₀ ∧ Fin.tail y₀ ∈ B₀ ∧ 0 < ε ∧
      (∀ j k, AnalyticOnNhd ℝ (c j k) B₀) ∧
      (∀ j k, ∀ z ∈ B₀, ‖c j k z‖ ≤ (ε / 4) ^ (d j - k.val)) ∧
      ∀ y : Fin (n + 1) → ℝ, Fin.tail y ∈ B₀ → y 0 ∈ Ioo (y₀ 0 - ε) (y₀ 0 + ε) →
        y ∈ V₂ ∧ ∀ j, SignType.sign (g j y) =
          SignType.sign ((shiftedMonic (y₀ 0) (c j · (Fin.tail y))).eval (y 0)) * u₀ j := by
  classical
  cases nonempty_fintype ι₁
  set z₀ := Fin.tail y₀
  set t₀ := y₀ 0 with ht₀
  let e : (Fin n → ℝ) × ℝ → Fin (n + 1) → ℝ := fun p ↦ Fin.cons p.snd p.fst
  have he₀ : e (z₀, t₀) = y₀ := Fin.cons_self_tail y₀
  have he_an (p : (Fin n → ℝ) × ℝ) : AnalyticAt ℝ e p :=
    AnalyticAt.pi fun m ↦ Fin.cases analyticAt_snd
      (fun k ↦ ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) k).comp
        (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ)).analyticAt p) m
  have hg' (j : ι₁) : AnalyticAt ℝ (g j ∘ e) (z₀, t₀) := (hg j).comp_of_eq (he_an _) he₀
  choose d hd using fun j ↦ ENat.ne_top_iff_exists.mp (hord j)
  choose c u hc hc0 hu hu0 hfac using fun j ↦ (hg' j).exists_weierstrassPreparation_real (hd j).symm
  have hunit (j : ι₁) : ∀ᶠ p in 𝓝 (z₀, t₀), SignType.sign (u j p) = SignType.sign (u j (z₀, t₀)) :=
    ((continuousAt_sign_of_ne_zero (hu0 j)).comp (hu j).continuousAt)
      ((isOpen_discrete _).mem_nhds (mem_singleton _))
  have hprod : ∀ᶠ p in 𝓝 (z₀, t₀), e p ∈ V₂ ∧ ∀ j,
      SignType.sign (g j (e p)) =
        SignType.sign ((TauCeti.Polynomial.monicOfCoeff (fun k ↦ c j k p.fst)).eval (p.snd - t₀)) *
          SignType.sign (u j (z₀, t₀)) := by
    have heV : e ⁻¹' V₂ ∈ 𝓝 (z₀, t₀) := (he_an _).continuousAt.preimage_mem_nhds (he₀ ▸ hV₂)
    filter_upwards [heV, eventually_all.mpr hfac, eventually_all.mpr hunit] with p hpV hpf hpu
    refine ⟨hpV, fun j ↦ ?_⟩
    rw [← Function.comp_apply (f := g j), hpf j, sign_mul, hpu j]
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hprod
  have hc_nhds : ∀ᶠ z in 𝓝 z₀, ∀ j k,
      AnalyticAt ℝ (c j k) z ∧ ‖c j k z‖ ≤ (δ / 4) ^ (d j - k.val) :=
    eventually_all.mpr fun j ↦ eventually_all.mpr fun k ↦ by
      have hpos : 0 < (δ / 4) ^ (d j - k.val) := pow_pos (by linarith) _
      have hlt : ∀ᶠ z in 𝓝 z₀, ‖c j k z‖ < (δ / 4) ^ (d j - k.val) :=
        (hc j k).continuousAt.norm.eventually
          (gt_mem_nhds (by dsimp only; rw [hc0 j k, norm_zero]; exact hpos))
      exact (hc j k).eventually_analyticAt.and (hlt.mono fun _ hz ↦ hz.le)
  obtain ⟨B₀, hB₀sub, hB₀o, hz₀B₀⟩ :=
    eventually_nhds_iff.mp (inter_mem (Metric.ball_mem_nhds z₀ hδ) hc_nhds)
  refine ⟨d, c, fun j ↦ SignType.sign (u j (z₀, t₀)), B₀, δ, hB₀o, hz₀B₀, hδ,
    fun j k z hz ↦ ((hB₀sub z hz).right j k).left,
    fun j k z hz ↦ ((hB₀sub z hz).right j k).right, fun y hyB hyI ↦ ?_⟩
  have hdist : dist (Fin.tail y, y 0) (z₀, t₀) < δ := by
    rw [Prod.dist_eq]
    refine max_lt (hB₀sub _ hyB).left ?_
    rw [ht₀, Real.dist_eq, abs_sub_lt_iff]
    exact ⟨by linarith [(mem_Ioo.mp hyI).right], by linarith [(mem_Ioo.mp hyI).left]⟩
  obtain ⟨hyV, hysign⟩ := hball hdist
  have hey : e (Fin.tail y, y 0) = y := Fin.cons_self_tail y
  rw [hey] at hyV hysign
  refine ⟨hyV, fun j ↦ ?_⟩
  simpa [shiftedMonic, Polynomial.eval_comp] using hysign j

private theorem signInvariant_image_of_slab {n : ℕ} {ι : Type*}
    {f : ι → (Fin (n + 1) → ℝ) → ℝ} {x₀ : Fin (n + 1) → ℝ} {V₁ : Set (Fin (n + 1) → ℝ)}
    (hV₁zero : ∀ x ∈ V₁, ∀ i, f i =ᶠ[𝓝 x₀] 0 → f i x = 0)
    (L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) {E : Set (Fin (n + 1) → ℝ)}
    {p : {i : ι // ¬ f i =ᶠ[𝓝 x₀] 0} → (Fin (n + 1) → ℝ) → ℝ}
    {u₀ : {i : ι // ¬ f i =ᶠ[𝓝 x₀] 0} → SignType}
    (hEV₁ : ∀ y ∈ E, L y ∈ V₁)
    (hsign : ∀ y ∈ E, ∀ j, SignType.sign (f j.val (L y)) = SignType.sign (p j y) * u₀ j)
    (hEsign : ∀ j, SignInvariant (p j) E) (i : ι) :
    SignInvariant (f i) (L '' E) := by
  by_cases hi : f i =ᶠ[𝓝 x₀] 0
  · exact (signInvariant_const 0).congr fun x ⟨y, hyE, hxy⟩ ↦
      hxy ▸ (hV₁zero (L y) (hEV₁ y hyE) i hi).symm
  · rw [signInvariant_image, signInvariant_def]
    intro y₁ hy₁ y₂ hy₂
    rw [Function.comp_apply, Function.comp_apply, hsign y₁ hy₁ ⟨i, hi⟩, hsign y₂ hy₂ ⟨i, hi⟩,
      signInvariant_def.mp (hEsign ⟨i, hi⟩) y₁ hy₁ y₂ hy₂]

private theorem image_continuousLinearEquiv_partition {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {Q : Set E₂ → Prop} (e : E₁ ≃L[ℝ] E₂) {x₀ : E₂} {V : Set E₂} {W : Set E₁}
    {𝒞₀ : Set (Set E₁)} (hWo : IsOpen W) (hy₀W : e.symm x₀ ∈ W) (hWV : e '' W ⊆ V)
    (h𝒞₀fin : 𝒞₀.Finite) (h𝒞₀disj : 𝒞₀.PairwiseDisjoint id) (h𝒞₀cov : ⋃₀ 𝒞₀ = W)
    (h𝒞₀cell : ∀ E ∈ 𝒞₀, IsConnected E ∧ IsSemianalytic E ∧ Q (e '' E)) :
    IsOpen (e '' W) ∧ x₀ ∈ e '' W ∧ e '' W ⊆ V ∧ IsSemianalytic (e '' W) ∧
      (image e '' 𝒞₀).Finite ∧ (image e '' 𝒞₀).PairwiseDisjoint id ∧ ⋃₀ (image e '' 𝒞₀) = e '' W ∧
      ∀ C ∈ image e '' 𝒞₀, IsConnected C ∧ IsSemianalytic C ∧ Q C := by
  have h𝒞cov : ⋃₀ (image e '' 𝒞₀) = e '' W := by rw [← image_sUnion, h𝒞₀cov]
  have h𝒞cell : ∀ C ∈ image e '' 𝒞₀, IsConnected C ∧ IsSemianalytic C ∧ Q C := by
    rintro _ ⟨E, hE, rfl⟩
    obtain ⟨hEc, hEsa, hEQ⟩ := h𝒞₀cell E hE
    refine ⟨hEc.image e e.continuous.continuousOn, ?_, hEQ⟩
    rw [e.image_eq_preimage_symm]
    exact hEsa.preimage fun x _ ↦ e.symm.analyticAt x
  refine ⟨e.toHomeomorph.isOpenMap W hWo, ⟨e.symm x₀, hy₀W, e.apply_symm_apply x₀⟩,
    hWV, ?_, h𝒞₀fin.image _, ?_, h𝒞cov, h𝒞cell⟩
  · rw [← h𝒞cov, sUnion_eq_biUnion]
    exact IsSemianalytic.biUnion (h𝒞₀fin.image _) fun C hC ↦ (h𝒞cell C hC).right.left
  · rintro _ ⟨E₁, hE₁, rfl⟩ _ ⟨E₂, hE₂, rfl⟩ hne
    exact (disjoint_image_iff e.injective).mpr (h𝒞₀disj hE₁ hE₂ fun h ↦ hne (h ▸ rfl))

private theorem step_isNormalDecomposition_signInvariant.{u} {n : ℕ}
    (ih : ∀ {ι : Type u} [Finite ι] {f : ι → (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ}
      {V : Set (Fin n → ℝ)}, (∀ i, AnalyticAt ℝ (f i) x₀) → V ∈ 𝓝 x₀ →
      ∃ (U : Set (Fin n → ℝ)) (𝒞 : Set (Set (Fin n → ℝ))),
        IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsNormalDecomposition U 𝒞 ∧
        ∀ C ∈ 𝒞, ∀ i, SignInvariant (f i) C)
    {ι : Type u} [Finite ι] {f : ι → (Fin (n + 1) → ℝ) → ℝ} {x₀ : Fin (n + 1) → ℝ}
    {V : Set (Fin (n + 1) → ℝ)} (hf : ∀ i, AnalyticAt ℝ (f i) x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set (Fin (n + 1) → ℝ)) (𝒞 : Set (Set (Fin (n + 1) → ℝ))),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsNormalDecomposition U 𝒞 ∧
      ∀ C ∈ 𝒞, ∀ i, SignInvariant (f i) C := by
  classical
  have hzero : ∀ᶠ x in 𝓝 x₀, ∀ i, f i =ᶠ[𝓝 x₀] 0 → f i x = 0 :=
    eventually_all.mpr fun i ↦ by
      by_cases hi : f i =ᶠ[𝓝 x₀] 0
      exacts [hi.mono fun _ hx _ ↦ hx, .of_forall fun _ h ↦ (hi h).elim]
  obtain ⟨V₁, hV₁sub, hV₁o, hx₀V₁⟩ := eventually_nhds_iff.mp (inter_mem hV hzero)
  let ι₁ := {i : ι // ¬ f i =ᶠ[𝓝 x₀] 0}
  obtain ⟨L, hord⟩ := exists_continuousLinearEquiv_finSucc_forall_analyticOrderAt_ne_top
    (f := fun j : ι₁ ↦ f j.val) (fun j ↦ hf j.val) (fun j ↦ j.property)
  set y₀ := L.symm x₀
  obtain ⟨d, c, u₀, B₀, ε, hB₀o, hz₀B₀, hε, hc, hcbnd, hslab⟩ := exists_slab_weierstrass_sign
    (g := fun j : ι₁ ↦ f j.val ∘ L)
    (fun j ↦ (hf j.val).comp_of_eq (L.analyticAt y₀) (L.apply_symm_apply x₀)) hord
    ((hV₁o.preimage L.continuous).mem_nhds (by simpa [y₀] using hx₀V₁))
  let P : ι₁ → (Fin n → ℝ) → ℝ[X] := fun j z ↦ shiftedMonic (y₀ 0) (c j · z)
  obtain ⟨g, hg_an, hg_delin⟩ := exists_analyticOnNhd_projection_delineation (F := P) (d := d)
    (fun j m _ ↦ analyticOnNhd_coeff_shiftedMonic (y₀ 0) (hc j) m)
    (fun j z _ ↦ (natDegree_shiftedMonic (y₀ 0) (c j · z)).le)
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp hB₀o (Fin.tail y₀) hz₀B₀
  obtain ⟨U', 𝒟, hU'o, hz₀U', hU'ball, h𝒟, h𝒟sign⟩ :=
    ih (f := fun a : ULift.{u} g ↦ a.down.val) (fun a ↦ hg_an a.down.val a.down.property _ hz₀B₀)
      (Metric.ball_mem_nhds (Fin.tail y₀) (half_pos hr₀))
  have hU'cl : closure U' ⊆ B₀ :=
    (closure_mono hU'ball).trans <|
      Metric.closure_ball_subset_closedBall.trans <|
        (Metric.closedBall_subset_ball (half_lt_self hr₀)).trans hball₀
  let D (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) : Delineation fun j (x : S) ↦ P j x :=
    (hg_delin S ((h𝒟.subset_of_mem hS).trans (subset_closure.trans hU'cl)) (h𝒟.isPreconnected hS)
      fun a ha x hx y hy ↦ by
        rw [← sign_eq_zero_iff (a := a x), ← sign_eq_zero_iff (a := a y),
          signInvariant_def.mp (h𝒟sign S hS (ULift.up ⟨a, ha⟩)) x hx y hy]).some
  have hW := h𝒟.lift (P := P) (d := d) hB₀o hU'cl (a := y₀ 0 - ε) (b := y₀ 0 + ε) (by linarith)
    (fun j z _ ↦ monic_shiftedMonic _ _) (fun j z _ ↦ natDegree_shiftedMonic _ _)
    (fun j m _ ↦ analyticOnNhd_coeff_shiftedMonic (y₀ 0) (hc j) m)
    (fun j z hz _ hrt ↦
      mem_Ioo_of_isRoot_shiftedMonic hε (fun k ↦ hcbnd j k z (subset_closure.trans hU'cl hz)) hrt)
    D
  have hWo : IsOpen {y : Fin (n + 1) → ℝ | Fin.tail y ∈ U' ∧ y 0 ∈ Ioo (y₀ 0 - ε) (y₀ 0 + ε)} :=
    (hU'o.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (continuous_apply 0))
  refine ⟨_, _, L.toHomeomorph.isOpenMap _ hWo,
    ⟨y₀, ⟨hz₀U', by simp [hε]⟩, L.apply_symm_apply x₀⟩,
    fun _ ⟨y, hyW, hxy⟩ ↦
      hxy ▸ (hV₁sub _ (hslab y (subset_closure.trans hU'cl hyW.left) hyW.right).left).left,
    hW.image_continuousLinearEquiv L, ?_⟩
  rintro _ ⟨E, hE, rfl⟩ i
  obtain ⟨S, hS, hES⟩ := mem_iUnion₂.mp hE
  have hEW := hW.subset_of_mem hE
  exact signInvariant_image_of_slab (fun x hx ↦ (hV₁sub x hx).right) L
    (fun y hy ↦ (hslab y (subset_closure.trans hU'cl (hEW hy).left) (hEW hy).right).left)
    (fun y hy j ↦ (hslab y (subset_closure.trans hU'cl (hEW hy).left) (hEW hy).right).right j)
    (fun j ↦ (D S hS).signInvariant_eval_of_mem_boundedStackCells j hES) i

end SlabHelpers

/-! ### Local normal decompositions in coordinate space `Fin n → ℝ` -/

/-- **Local normal decomposition of real analytic germs in `Fin n → ℝ`.** Given a finite family of
functions `f i` analytic at `x₀ : Fin n → ℝ` and a neighborhood `V` of `x₀`, there exist an open
neighborhood `U ⊆ V` of `x₀` and a normal decomposition `𝒞` of `U` on every piece of which every
`f i` is sign-invariant. -/
theorem exists_isNormalDecomposition_signInvariant.{u} {n : ℕ} {ι : Type u} [Finite ι]
    {f : ι → (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ} {V : Set (Fin n → ℝ)}
    (hf : ∀ i, AnalyticAt ℝ (f i) x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set (Fin n → ℝ)) (𝒞 : Set (Set (Fin n → ℝ))),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsNormalDecomposition U 𝒞 ∧
      ∀ C ∈ 𝒞, ∀ i, SignInvariant (f i) C := by
  induction n generalizing ι with
  | zero =>
    have hVuniv : univ ⊆ V := fun y _ ↦ Subsingleton.elim y x₀ ▸ mem_of_mem_nhds hV
    exact ⟨univ, {univ}, isOpen_univ, mem_univ x₀, hVuniv, isNormalDecomposition_singleton_univ,
      fun _ _ _ ↦ subsingleton_of_subsingleton.signInvariant⟩
  | succ n ih =>
    exact step_isNormalDecomposition_signInvariant ih hf hV

/-- **Simultaneous local normal decomposition for semianalytic germs in `Fin n → ℝ`.**
Given finitely many sets `s i` semianalytic at `x₀ : Fin n → ℝ` and a neighborhood `V` of `x₀`,
there exist an open neighborhood `U ⊆ V` of `x₀` and a normal decomposition `𝒞` of `U` whose pieces
each lie either inside or outside every `s i`. -/
theorem exists_isNormalDecomposition_subset_or_disjoint {n : ℕ} {ι : Type*} [Finite ι]
    {s : ι → Set (Fin n → ℝ)} {x₀ : Fin n → ℝ} {V : Set (Fin n → ℝ)}
    (hs : ∀ i, SemianalyticAt (s i) x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set (Fin n → ℝ)) (𝒞 : Set (Set (Fin n → ℝ))),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsNormalDecomposition U 𝒞 ∧
      ∀ C ∈ 𝒞, ∀ i, C ⊆ s i ∨ Disjoint C (s i) := by
  classical
  cases nonempty_fintype ι
  choose W hW t ht hst using fun i ↦ semianalyticAt_def.mp (hs i)
  choose m f hf Φ ht_eq using fun i ↦ (ht i).exists_eq_setOf_sign
  have hfx (p : Σ i, Fin (m i)) : AnalyticAt ℝ (f p.fst p.snd) x₀ :=
    hf p.fst p.snd x₀ (mem_of_mem_nhds (hW p.fst))
  obtain ⟨U, 𝒞, hUo, hx₀U, hUW, h𝒞, h𝒞sign⟩ :=
    exists_isNormalDecomposition_signInvariant (f := fun p : Σ i, Fin (m i) ↦ f p.fst p.snd)
      hfx (inter_mem hV (iInter_mem.mpr hW))
  refine ⟨U, 𝒞, hUo, hx₀U, hUW.trans inter_subset_left, h𝒞, fun C hC i ↦ ?_⟩
  have hCU : C ⊆ W i := fun y hy ↦ mem_iInter.mp (hUW (h𝒞.subset_of_mem hC hy)).right i
  rcases subset_or_disjoint_setOf_sign (t := C) (f := fun k ↦ f i k)
      (fun k ↦ h𝒞sign C hC ⟨i, k⟩) (Φ i) with hsub | hdisj
  · refine .inl fun y hyC ↦ ?_
    have hmem := Set.ext_iff.mp (hst i) y
    exact (hmem.mpr ⟨ht_eq i ▸ hsub hyC, hCU hyC⟩).left
  · refine .inr (disjoint_left.mpr fun y hyC hys ↦ disjoint_left.mp hdisj hyC ?_)
    have hmem := Set.ext_iff.mp (hst i) y
    exact ht_eq i ▸ (hmem.mp ⟨hys, hCU hyC⟩).left

/-- **Local normal decomposition adapted to a single semianalytic germ in `Fin n → ℝ`.** -/
theorem SemianalyticAt.exists_isNormalDecomposition {n : ℕ} {s V : Set (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} (hs : SemianalyticAt s x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set (Fin n → ℝ)) (𝒞 : Set (Set (Fin n → ℝ))),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsNormalDecomposition U 𝒞 ∧
      ∀ C ∈ 𝒞, C ⊆ s ∨ Disjoint C s := by
  obtain ⟨U, 𝒞, hUo, hx₀U, hUV, h𝒞, hcompat⟩ :=
    exists_isNormalDecomposition_subset_or_disjoint (fun _ : Unit ↦ hs) hV
  exact ⟨U, 𝒞, hUo, hx₀U, hUV, h𝒞, fun C hC ↦ hcompat C hC ()⟩

/-- **Local connected analytic submanifold partition of a semianalytic germ in `Fin n → ℝ`.** If `s`
is semianalytic at `x₀ : Fin n → ℝ` and `V ∈ 𝓝 x₀`, there is an open semianalytic neighborhood
`U ⊆ V` of `x₀` such that `s ∩ U` is globally semianalytic and partitioned into finitely many
pairwise disjoint connected semianalytic real analytic submanifolds. -/
theorem SemianalyticAt.exists_isAnalyticSubmanifold_partition_inter {n : ℕ}
    {s V : Set (Fin n → ℝ)} {x₀ : Fin n → ℝ} (hs : SemianalyticAt s x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set (Fin n → ℝ)) (𝒞 : Set (Set (Fin n → ℝ))),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧ IsSemianalytic (s ∩ U) ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = s ∩ U ∧
      ∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧ ∃ d ≤ n, IsAnalyticSubmanifold d C := by
  obtain ⟨U, 𝒟, hUo, hx₀U, hUV, h𝒟, hcompat⟩ := hs.exists_isNormalDecomposition hV
  have h𝒞fin : {C ∈ 𝒟 | C ⊆ s}.Finite := h𝒟.finite.subset (sep_subset _ _)
  have h𝒞cov : ⋃₀ {C ∈ 𝒟 | C ⊆ s} = s ∩ U := (h𝒟.inter_eq_sUnion_sep hcompat).symm
  have hsUsa : IsSemianalytic (s ∩ U) := by
    rw [← h𝒞cov, sUnion_eq_biUnion]
    exact .biUnion h𝒞fin fun C hC ↦ h𝒟.isSemianalytic hC.left
  exact ⟨U, {C ∈ 𝒟 | C ⊆ s}, hUo, hx₀U, hUV, isSemianalytic_of_isNormalDecomposition h𝒟, hsUsa,
    h𝒞fin, h𝒟.pairwiseDisjoint.subset (sep_subset _ _), h𝒞cov,
    fun C hC ↦ ⟨h𝒟.isConnected hC.left, h𝒟.isSemianalytic hC.left,
      h𝒟.exists_isAnalyticSubmanifold_le hC.left⟩⟩

/-! ### Coordinate-free local decompositions in finite-dimensional real normed spaces -/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Local sign-invariant decomposition of real analytic germs.** Given finitely many real
functions `f i` analytic at a point `x₀` of a finite-dimensional real normed space `E` and a
neighborhood `V` of `x₀`, there exists an open semianalytic neighborhood `U ⊆ V` of `x₀` partitioned
into finitely many pairwise disjoint connected, semianalytic, locally closed sets on each of which
every `f i` is sign-invariant. -/
theorem exists_isConnected_partition_signInvariant {ι : Type*} [Finite ι]
    {f : ι → E → ℝ} {x₀ : E} {V : Set E}
    (hf : ∀ i, AnalyticAt ℝ (f i) x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set E) (𝒞 : Set (Set E)),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = U ∧
      ∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧ IsLocallyClosed C ∧
        ∀ i, SignInvariant (f i) C := by
  let φ : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  obtain ⟨U₀, 𝒞₀, hU₀o, hx₀U₀, hU₀V, h𝒞₀, h𝒞₀sign⟩ :=
    exists_isNormalDecomposition_signInvariant (f := fun i ↦ f i ∘ φ.symm)
      (fun i ↦ (hf i).comp_of_eq (φ.symm.analyticAt (φ x₀)) (φ.symm_apply_apply x₀))
      (φ.toHomeomorph.symm.continuous.continuousAt.preimage_mem_nhds
        (by simpa [φ.symm_apply_apply] using hV))
  refine ⟨_, _, image_continuousLinearEquiv_partition φ.symm hU₀o hx₀U₀ (image_subset_iff.mpr hU₀V)
    h𝒞₀.finite h𝒞₀.pairwiseDisjoint h𝒞₀.sUnion_eq fun C₀ hC₀ ↦ ?_⟩
  exact ⟨h𝒞₀.isConnected hC₀, h𝒞₀.isSemianalytic hC₀,
    (φ.symm.image_eq_preimage_symm C₀).symm ▸ (h𝒞₀.isLocallyClosed hC₀).preimage φ.continuous,
    fun i ↦ signInvariant_image.mpr (h𝒞₀sign C₀ hC₀ i)⟩

/-- **Simultaneous local connected partition for semianalytic germs.** Given finitely many sets
`s i` semianalytic at a point `x₀` of a finite-dimensional real normed space `E` and `V ∈ 𝓝 x₀`,
there exists an open semianalytic neighborhood `U ⊆ V` of `x₀` partitioned into finitely many
pairwise disjoint connected, semianalytic, locally closed sets, each lying inside or outside every
`s i`. -/
theorem exists_isConnected_partition_subset_or_disjoint {ι : Type*} [Finite ι]
    {s : ι → Set E} {x₀ : E} {V : Set E}
    (hs : ∀ i, SemianalyticAt (s i) x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set E) (𝒞 : Set (Set E)),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = U ∧
      ∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧ IsLocallyClosed C ∧
        ∀ i, C ⊆ s i ∨ Disjoint C (s i) := by
  let φ : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  have hs' (i : ι) : SemianalyticAt (φ.symm ⁻¹' s i) (φ x₀) :=
    (φ.symm_apply_apply x₀ ▸ hs i).preimage (φ.symm.analyticAt (φ x₀))
  obtain ⟨U₀, 𝒞₀, hU₀o, hx₀U₀, hU₀V, h𝒞₀, h𝒞₀compat⟩ :=
    exists_isNormalDecomposition_subset_or_disjoint hs'
      (φ.toHomeomorph.symm.continuous.continuousAt.preimage_mem_nhds
        (by simpa [φ.symm_apply_apply] using hV))
  refine ⟨_, _, image_continuousLinearEquiv_partition φ.symm hU₀o hx₀U₀ (image_subset_iff.mpr hU₀V)
    h𝒞₀.finite h𝒞₀.pairwiseDisjoint h𝒞₀.sUnion_eq fun C₀ hC₀ ↦ ?_⟩
  refine ⟨h𝒞₀.isConnected hC₀, h𝒞₀.isSemianalytic hC₀,
    (φ.symm.image_eq_preimage_symm C₀).symm ▸ (h𝒞₀.isLocallyClosed hC₀).preimage φ.continuous,
    fun i ↦ ?_⟩
  rcases h𝒞₀compat C₀ hC₀ i with hsub | hdisj
  · exact .inl (image_subset_iff.mpr hsub)
  · exact .inr (disjoint_left.mpr fun _ ⟨y, hy, hxy⟩ hys ↦
      disjoint_left.mp hdisj hy (by simpa [mem_preimage, hxy] using hys))

/-- **Local connected partition of a semianalytic germ.** If `s` is semianalytic at a point `x₀` of
a finite-dimensional real normed space `E` and `V ∈ 𝓝 x₀`, there exists an open semianalytic
neighborhood `U ⊆ V` of `x₀` such that `s ∩ U` is globally semianalytic and partitioned into
finitely many pairwise disjoint connected, semianalytic, locally closed sets. -/
theorem SemianalyticAt.exists_isConnected_partition_inter {s V : Set E} {x₀ : E}
    (hs : SemianalyticAt s x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set E) (𝒞 : Set (Set E)),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧ IsSemianalytic (s ∩ U) ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = s ∩ U ∧
      ∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧ IsLocallyClosed C := by
  obtain ⟨U, 𝒟, hUo, hx₀U, hUV, hUsa, h𝒟fin, h𝒟disj, h𝒟cov, h𝒟cell⟩ :=
    exists_isConnected_partition_subset_or_disjoint (fun _ : Unit ↦ hs) hV
  have h𝒞fin : {C ∈ 𝒟 | C ⊆ s}.Finite := h𝒟fin.subset (sep_subset _ _)
  have h𝒞cov : ⋃₀ {C ∈ 𝒟 | C ⊆ s} = s ∩ U := by
    rw [sUnion_sep_subset_eq_inter fun C hC ↦ (h𝒟cell C hC).right.right.right (), h𝒟cov]
  have hsUsa : IsSemianalytic (s ∩ U) := by
    rw [← h𝒞cov, sUnion_eq_biUnion]
    exact .biUnion h𝒞fin fun C hC ↦ (h𝒟cell C hC.left).right.left
  exact ⟨U, {C ∈ 𝒟 | C ⊆ s}, hUo, hx₀U, hUV, hUsa, hsUsa, h𝒞fin, h𝒟disj.subset (sep_subset _ _),
    h𝒞cov, fun C hC ↦ ⟨(h𝒟cell C hC.left).left, (h𝒟cell C hC.left).right.left,
      (h𝒟cell C hC.left).right.right.left⟩⟩

end FiniteDimensional

end TauCeti

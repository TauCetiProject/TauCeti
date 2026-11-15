/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import TauCeti.Geometry.RealAlgebraic.SignInvariant
public import TauCeti.Geometry.RealAnalytic.Semianalytic.NormalDecomposition.Basic

import Mathlib.Algebra.Polynomial.BigOperators
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Polynomial.Monic.RootBound
import TauCeti.Geometry.RealAnalytic.Projection
import TauCeti.Geometry.RealAnalytic.Semianalytic.NormalDecomposition.Lift

/-!
# Existence of local normal decompositions

Every finite family of real-analytic functions near a point `x₀ ∈ ℝⁿ` admits an open neighborhood
`U` of `x₀` inside any prescribed neighborhood `V ∈ 𝓝 x₀` together with a normal decomposition `𝒞`
of `U` on each piece of which every member of the family is sign-invariant
(`TauCeti.exists_isNormalDecomposition_signInvariant_nhds`). Applying sign-condition normal form to
semianalytic germs immediately yields local normal decompositions adapted to any finite family of
sets semianalytic at `x₀` (`TauCeti.exists_isNormalDecomposition_semianalyticAt_nhds`,
`TauCeti.SemianalyticAt.exists_isNormalDecomposition_nhds`).

## Proof outline

The proof proceeds by induction on the ambient dimension `n`:

* For `n = 0`, `ℝ⁰` is a singleton and `{univ}` is a normal decomposition of `univ`.
* For `n + 1`, `TauCeti.exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top` puts the
  nonvanishing germs of the family in simultaneous general position with respect to the vertical
  coordinate. For each nonvanishing germ, `AnalyticAt.exists_weierstrassPreparation_real` factors it
  on a small cylinder `ball y₀ r₀ ×ˢ Ioo (t₀ - δ) (t₀ + δ)` into a monic Weierstrass polynomial in
  `t - t₀` with analytic coefficients vanishing at `y₀` times a nonvanishing analytic unit of
  constant sign. Shrinking `r₀` while keeping `δ` fixed bounds the coefficients so that Fujiwara's
  root bound (`Polynomial.IsRoot.norm_le_two_mul`) confines all real roots over `ball y₀ r₀` to
  `[t₀ - δ / 2, t₀ + δ / 2] ⊂ (t₀ - δ, t₀ + δ)`. Finally,
  `TauCeti.exists_analyticOnNhd_projection_delineation` produces a finite analytic projection family
  on `ball y₀ r₀`, the induction hypothesis decomposes a neighborhood `B ⊆ ball y₀ (r₀ / 2)` of
  `y₀`, and `TauCeti.IsNormalDecomposition.lift` lifts that base decomposition to the cylinder and
  transports it back along the linear change of coordinates.

## Main declarations

* `TauCeti.exists_isNormalDecomposition_signInvariant_nhds`: existence of a sign-invariant local
  normal decomposition for any finite family of functions analytic at `x₀ ∈ ℝⁿ`.
* `TauCeti.exists_isNormalDecomposition_semianalyticAt_nhds`: existence of a local normal
  decomposition adapted to any finite family of sets semianalytic at `x₀ ∈ ℝⁿ`.
* `TauCeti.SemianalyticAt.exists_isNormalDecomposition_nhds`: single-germ specialization.

## References

* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS lecture notes, 1965, §16–18.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §2.
* E. Bierstone and P. D. Milman, *Semianalytic and subanalytic sets*, Publications Mathématiques de
  l'IHÉS 67 (1988), 5–42, Theorem 2.10.
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

/-! ### Shifted monic Weierstrass polynomials and cylinder preparation -/

private def consCLE (n : ℕ) : ((Fin n → ℝ) × ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
  (ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ).trans
    (Fin.consEquivL ℝ fun _ : Fin (n + 1) ↦ ℝ)

private theorem consCLE_apply {n : ℕ} (p : (Fin n → ℝ) × ℝ) :
    consCLE n p = Fin.cons p.2 p.1 :=
  rfl

@[simp]
private theorem consCLE_symm_apply {n : ℕ} (v : Fin (n + 1) → ℝ) :
    (consCLE n).symm v = (Fin.tail v, v 0) :=
  (consCLE n).injective (by simp [consCLE_apply, Fin.cons_self_tail])

private noncomputable def shiftedMonic {d : ℕ} (t₀ : ℝ) (a : Fin d → ℝ) : ℝ[X] :=
  (TauCeti.Polynomial.monicOfCoeff a).comp (X - C t₀)

private theorem eval_shiftedMonic {d : ℕ} (t₀ : ℝ) (a : Fin d → ℝ) (t : ℝ) :
    (shiftedMonic t₀ a).eval t = (TauCeti.Polynomial.monicOfCoeff a).eval (t - t₀) := by
  simp [shiftedMonic, eval_comp]

private theorem monic_shiftedMonic {d : ℕ} (t₀ : ℝ) (a : Fin d → ℝ) :
    (shiftedMonic t₀ a).Monic :=
  (TauCeti.Polynomial.monic_monicOfCoeff a).comp_X_sub_C t₀

private theorem natDegree_shiftedMonic {d : ℕ} (t₀ : ℝ) (a : Fin d → ℝ) :
    (shiftedMonic t₀ a).natDegree = d := by
  rw [shiftedMonic, natDegree_comp, TauCeti.Polynomial.natDegree_monicOfCoeff,
    natDegree_X_sub_C, mul_one]

private theorem monicOfCoeff_eq {d : ℕ} (a : Fin d → ℝ) :
    TauCeti.Polynomial.monicOfCoeff a = X ^ d + ∑ j : Fin d, monomial (j : ℕ) (a j) := by
  have h := (TauCeti.Polynomial.monicOfCoeff a).as_sum_range' (d + 1)
    (by simp [TauCeti.Polynomial.natDegree_monicOfCoeff])
  rw [Finset.sum_range_succ, TauCeti.Polynomial.coeff_monicOfCoeff_self,
    ← C_mul_X_pow_eq_monomial, C_1, one_mul, add_comm,
    ← Fin.sum_univ_eq_sum_range (fun j ↦ monomial j ((TauCeti.Polynomial.monicOfCoeff a).coeff j))]
    at h
  simpa only [TauCeti.Polynomial.coeff_monicOfCoeff] using h

private theorem analyticOnNhd_coeff_shiftedMonic {n d : ℕ} {B₀ : Set (Fin n → ℝ)} (t₀ : ℝ)
    {c : Fin d → (Fin n → ℝ) → ℝ} (hc : ∀ j, AnalyticOnNhd ℝ (c j) B₀) (m : ℕ) :
    AnalyticOnNhd ℝ (fun x ↦ (shiftedMonic t₀ (c · x)).coeff m) B₀ := by
  have hfun : (fun x ↦ (shiftedMonic t₀ (c · x)).coeff m) =
      fun x ↦ ((X - C t₀) ^ d).coeff m +
        ∑ j : Fin d, c j x * ((X - C t₀) ^ (j : ℕ)).coeff m := by
    ext x
    simp only [shiftedMonic, monicOfCoeff_eq, add_comp, pow_comp, X_comp, sum_comp, monomial_comp,
      coeff_add, finsetSum_coeff, coeff_C_mul]
  rw [hfun]
  exact (analyticOnNhd_const (v := _)).add
    (Finset.analyticOnNhd_fun_sum _ fun j _ ↦ (hc j).mul (analyticOnNhd_const (v := _)))

private theorem mem_Icc_of_isRoot_shiftedMonic {d : ℕ} {t₀ δ : ℝ} {a : Fin d → ℝ}
    (ha : ∀ j : Fin d, ‖a j‖ ≤ (δ / 4) ^ (d - (j : ℕ))) {t : ℝ}
    (hrt : (shiftedMonic t₀ a).IsRoot t) :
    t ∈ Icc (t₀ - δ / 2) (t₀ + δ / 2) := by
  have hrt' : (TauCeti.Polynomial.monicOfCoeff a).IsRoot (t - t₀) := by
    rwa [IsRoot.def, eval_shiftedMonic] at hrt
  have hbnd : ‖t - t₀‖ ≤ 2 * (δ / 4) :=
    hrt'.norm_le_two_mul (TauCeti.Polynomial.monic_monicOfCoeff a) fun j hj ↦ by
      rw [TauCeti.Polynomial.natDegree_monicOfCoeff] at hj ⊢
      simpa [TauCeti.Polynomial.coeff_monicOfCoeff a ⟨j, hj⟩] using ha ⟨j, hj⟩
  rw [Real.norm_eq_abs, abs_sub_le_iff] at hbnd
  exact ⟨by linarith [hbnd.2], by linarith [hbnd.1]⟩

private theorem exists_weierstrass_cylinder_data {n : ℕ} {ι : Type*} [Finite ι]
    {h : ι → (Fin n → ℝ) × ℝ → ℝ} {y₀ : Fin n → ℝ} {t₀ : ℝ} {W : Set ((Fin n → ℝ) × ℝ)}
    (hh : ∀ i, AnalyticAt ℝ (h i) (y₀, t₀)) (hW : W ∈ 𝓝 (y₀, t₀))
    (hord : ∀ i, ¬h i =ᶠ[𝓝 (y₀, t₀)] 0 → analyticOrderAt (fun t ↦ h i (y₀, t)) t₀ ≠ ⊤) :
    let I₁ := {i : ι // ¬h i =ᶠ[𝓝 (y₀, t₀)] 0}
    ∃ (r₀ δ : ℝ) (d : I₁ → ℕ) (c : (i : I₁) → Fin (d i) → (Fin n → ℝ) → ℝ) (σ : I₁ → SignType),
      0 < r₀ ∧ 0 < δ ∧
      Metric.ball y₀ r₀ ×ˢ Ioo (t₀ - δ) (t₀ + δ) ⊆ W ∧
      (∀ i : ι, h i =ᶠ[𝓝 (y₀, t₀)] 0 →
        ∀ p ∈ Metric.ball y₀ r₀ ×ˢ Ioo (t₀ - δ) (t₀ + δ), h i p = 0) ∧
      (∀ (i : I₁) (j : Fin (d i)), AnalyticOnNhd ℝ (c i j) (Metric.ball y₀ r₀)) ∧
      (∀ (i : I₁) (j : Fin (d i)), ∀ x ∈ Metric.ball y₀ r₀,
        ‖c i j x‖ ≤ (δ / 4) ^ (d i - (j : ℕ))) ∧
      (∀ i : I₁, ∀ p ∈ Metric.ball y₀ r₀ ×ˢ Ioo (t₀ - δ) (t₀ + δ),
        SignType.sign (h i.1 p) =
          SignType.sign ((shiftedMonic t₀ (c i · p.1)).eval p.2) * σ i) := by
  classical
  intro I₁
  let I₀ := {i : ι // h i =ᶠ[𝓝 (y₀, t₀)] 0}
  choose d hd using fun i : I₁ ↦ ENat.ne_top_iff_exists.1 (hord i.1 i.2)
  choose c u hc hc0 hu hu0 hfac using fun i : I₁ ↦
    (hh i.1).exists_weierstrassPreparation_real (hd i).symm
  have hsign₀ (i : I₁) : ∀ᶠ p in 𝓝 (y₀, t₀), SignType.sign (h i.1 p) =
      SignType.sign ((shiftedMonic t₀ (c i · p.1)).eval p.2) * SignType.sign (u i (y₀, t₀)) := by
    have hus : ∀ᶠ p in 𝓝 (y₀, t₀), SignType.sign (u i p) = SignType.sign (u i (y₀, t₀)) :=
      ((continuousAt_sign_of_ne_zero (hu0 i)).comp (hu i).continuousAt)
        ((isOpen_discrete _).mem_nhds (mem_singleton _))
    filter_upwards [hfac i, hus] with p hp hup
    rw [hp, sign_mul, eval_shiftedMonic, hup]
  have hM₀ : ∀ᶠ p in 𝓝 (y₀, t₀), p ∈ W ∧ (∀ i : I₀, h i.1 p = 0) ∧
      ∀ i : I₁, SignType.sign (h i.1 p) =
        SignType.sign ((shiftedMonic t₀ (c i · p.1)).eval p.2) * SignType.sign (u i (y₀, t₀)) :=
    (eventually_mem_set.2 hW).and
      ((eventually_all.2 fun i : I₀ ↦ i.2).and (eventually_all.2 hsign₀))
  obtain ⟨δ, hδ, hM⟩ := Metric.eventually_nhds_iff.1 hM₀
  have hc_nhds (a : Σ i : I₁, Fin (d i)) :
      ∀ᶠ x in 𝓝 y₀, AnalyticAt ℝ (c a.1 a.2) x ∧
        ‖c a.1 a.2 x‖ ≤ (δ / 4) ^ (d a.1 - (a.2 : ℕ)) := by
    have hpos : 0 < (δ / 4) ^ (d a.1 - (a.2 : ℕ)) := pow_pos (by linarith) _
    have hlt : ∀ᶠ x in 𝓝 y₀, ‖c a.1 a.2 x‖ < (δ / 4) ^ (d a.1 - (a.2 : ℕ)) :=
      (hc a.1 a.2).continuousAt.norm.eventually
        (gt_mem_nhds (by dsimp only; rw [hc0 a.1 a.2, norm_zero]; exact hpos))
    exact (hc a.1 a.2).eventually_analyticAt.and (hlt.mono fun _ hx ↦ hx.le)
  obtain ⟨r₁, hr₁, hr₁c⟩ := Metric.eventually_nhds_iff.1 (eventually_all.2 hc_nhds)
  have hdist {x : Fin n → ℝ} {t : ℝ} (hx : x ∈ Metric.ball y₀ (min r₁ δ))
      (ht : t ∈ Ioo (t₀ - δ) (t₀ + δ)) : dist (x, t) (y₀, t₀) < δ := by
    rw [Metric.mem_ball] at hx
    rw [← Real.ball_eq_Ioo, Metric.mem_ball] at ht
    rw [Prod.dist_eq]
    exact max_lt (hx.trans_le (min_le_right _ _)) ht
  refine ⟨min r₁ δ, δ, d, c, fun i ↦ SignType.sign (u i (y₀, t₀)), lt_min hr₁ hδ, hδ,
    fun ⟨x, t⟩ ⟨hx, ht⟩ ↦ (hM (hdist hx ht)).1,
    fun i hi ⟨x, t⟩ ⟨hx, ht⟩ ↦ (hM (hdist hx ht)).2.1 ⟨i, hi⟩,
    fun i j x hx ↦ (hr₁c (Metric.mem_ball.1 hx |>.trans_le (min_le_left _ _)) ⟨i, j⟩).1,
    fun i j x hx ↦ (hr₁c (Metric.mem_ball.1 hx |>.trans_le (min_le_left _ _)) ⟨i, j⟩).2,
    fun i ⟨x, t⟩ ⟨hx, ht⟩ ↦ (hM (hdist hx ht)).2.2 i⟩

private theorem step_vertical_nonsingular {n : ℕ}
    (ih : ∀ {m : ℕ} {g : Fin m → (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} {W₀ : Set (Fin n → ℝ)},
      (∀ k, AnalyticAt ℝ (g k) y) → W₀ ∈ 𝓝 y →
      ∃ B : Set (Fin n → ℝ), IsOpen B ∧ y ∈ B ∧ B ⊆ W₀ ∧
        ∃ 𝒟 : Set (Set (Fin n → ℝ)), IsNormalDecomposition B 𝒟 ∧
          ∀ k, ∀ S ∈ 𝒟, SignInvariant (g k) S)
    {m : ℕ} {h : Fin m → (Fin n → ℝ) × ℝ → ℝ} {y₀ : Fin n → ℝ} {t₀ : ℝ}
    {W : Set ((Fin n → ℝ) × ℝ)} (hh : ∀ i, AnalyticAt ℝ (h i) (y₀, t₀)) (hW : W ∈ 𝓝 (y₀, t₀))
    (hord : ∀ i, ¬h i =ᶠ[𝓝 (y₀, t₀)] 0 → analyticOrderAt (fun t ↦ h i (y₀, t)) t₀ ≠ ⊤) :
    ∃ U₁ : Set (Fin (n + 1) → ℝ), IsOpen U₁ ∧ Fin.cons t₀ y₀ ∈ U₁ ∧
      (∀ v ∈ U₁, (Fin.tail v, v 0) ∈ W) ∧
      ∃ 𝒞₁ : Set (Set (Fin (n + 1) → ℝ)), IsNormalDecomposition U₁ 𝒞₁ ∧
        ∀ i, ∀ E ∈ 𝒞₁, SignInvariant (fun v ↦ h i (Fin.tail v, v 0)) E := by
  classical
  obtain ⟨r₀, δ, d, c, σ, hr₀, hδ, hsubW, hzero, hcan, hcbnd, hsign⟩ :=
    exists_weierstrass_cylinder_data hh hW hord
  let I₁ := {i : Fin m // ¬h i =ᶠ[𝓝 (y₀, t₀)] 0}
  let B₀ : Set (Fin n → ℝ) := Metric.ball y₀ r₀
  let P : I₁ → (Fin n → ℝ) → ℝ[X] := fun i x ↦ shiftedMonic t₀ (c i · x)
  have hPcoeff (i : I₁) (k : ℕ) (_ : k ≤ d i) :
      AnalyticOnNhd ℝ (fun x ↦ (P i x).coeff k) B₀ :=
    analyticOnNhd_coeff_shiftedMonic t₀ (hcan i) k
  obtain ⟨g, hg_an, hg_delin⟩ := exists_analyticOnNhd_projection_delineation (d := d) hPcoeff
    fun i x _ ↦ (natDegree_shiftedMonic _ _).le
  obtain ⟨mg, ⟨eg⟩⟩ := Finite.exists_equiv_fin g
  obtain ⟨B, hBopen, hy₀B, hBball, 𝒟, hB, hgsign⟩ :=
    ih (g := fun k ↦ (eg.symm k).1)
      (fun k ↦ hg_an (eg.symm k).1 (eg.symm k).2 y₀ (Metric.mem_ball_self hr₀))
      (Metric.ball_mem_nhds y₀ (half_pos hr₀))
  have hBB₀ : closure B ⊆ B₀ :=
    (closure_mono hBball).trans
      (Metric.closure_ball_subset_closedBall.trans
        (Metric.closedBall_subset_ball (half_lt_self hr₀)))
  let D (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) : Delineation fun i (x : S) ↦ P i x :=
    (hg_delin S ((hB.subset_of_mem hS).trans (subset_closure.trans hBB₀)) (hB.isPreconnected hS)
      fun a ha x hx y hy ↦ by
        have hsa := signInvariant_def.1 (hgsign (eg ⟨a, ha⟩) S hS) x hx y hy
        simp only [Equiv.symm_apply_apply] at hsa
        rw [← sign_eq_zero_iff, hsa, sign_eq_zero_iff]).some
  have hU₁ := hB.lift (P := P) (d := d) Metric.isOpen_ball hBB₀
    (a := t₀ - δ) (a' := t₀ - δ / 2) (b' := t₀ + δ / 2) (b := t₀ + δ)
    (by linarith) (by linarith) (by linarith) (fun i x _ ↦ monic_shiftedMonic t₀ (c i · x))
    (fun i x _ ↦ natDegree_shiftedMonic t₀ (c i · x)) hPcoeff
    (fun i x hx _ hrt ↦
      mem_Icc_of_isRoot_shiftedMonic (fun j ↦ hcbnd i j x (subset_closure.trans hBB₀ hx)) hrt) D
  have htail : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by fun_prop
  refine ⟨_, (hBopen.preimage htail).inter (isOpen_Ioo.preimage (continuous_apply 0)),
    ⟨by simpa using hy₀B, by simpa using hδ⟩,
    fun v ⟨hvB, hvI⟩ ↦ hsubW ⟨subset_closure.trans hBB₀ hvB, hvI⟩, _, hU₁, fun i E hE ↦ ?_⟩
  obtain ⟨S, hS, hES⟩ := mem_iUnion₂.1 hE
  have hvB₀ {v : Fin (n + 1) → ℝ} (hv : v ∈ E) :
      (Fin.tail v, v 0) ∈ B₀ ×ˢ Ioo (t₀ - δ) (t₀ + δ) :=
    let ⟨hvB, hvI⟩ := hU₁.subset_of_mem hE hv
    ⟨subset_closure.trans hBB₀ hvB, hvI⟩
  by_cases hi : h i =ᶠ[𝓝 (y₀, t₀)] 0
  · exact (signInvariant_const (0 : ℝ)).congr fun v hv ↦ (hzero i hi _ (hvB₀ hv)).symm
  · have heval := signInvariant_def.1
      (signInvariant_eval_of_mem_boundedStackCells (D S hS) ⟨i, hi⟩ hES)
    rw [signInvariant_def]
    intro v₁ hv₁ v₂ hv₂
    rw [hsign ⟨i, hi⟩ _ (hvB₀ hv₁), hsign ⟨i, hi⟩ _ (hvB₀ hv₂), heval v₁ hv₁ v₂ hv₂]

private theorem exists_isNormalDecomposition_signInvariant_fin {n : ℕ} :
    ∀ {m : ℕ} {f : Fin m → (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ} {V : Set (Fin n → ℝ)},
      (∀ i, AnalyticAt ℝ (f i) x₀) → V ∈ 𝓝 x₀ →
      ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧
        ∃ 𝒞 : Set (Set (Fin n → ℝ)), IsNormalDecomposition U 𝒞 ∧
          ∀ i, ∀ S ∈ 𝒞, SignInvariant (f i) S := by
  induction n with
  | zero =>
    intro m f x₀ V _ hV
    have hx₀ : x₀ ∈ V := mem_of_mem_nhds hV
    exact ⟨univ, isOpen_univ, mem_univ x₀, fun y _ ↦ Subsingleton.elim y x₀ ▸ hx₀,
      {univ}, isNormalDecomposition_singleton_univ,
      fun _ S _ ↦ (subsingleton_of_subsingleton (s := S)).signInvariant⟩
  | succ n ih =>
    intro m f x₀ V hf hV
    let f₀ : Fin m → (Fin n → ℝ) × ℝ → ℝ := fun i p ↦ f i (consCLE n p)
    let p₀ : (Fin n → ℝ) × ℝ := (consCLE n).symm x₀
    have hf₀ (i : Fin m) : AnalyticAt ℝ (f₀ i) p₀ :=
      (hf i).comp_of_eq ((consCLE n).analyticAt p₀) ((consCLE n).apply_symm_apply x₀)
    obtain ⟨L, ⟨y₀, t₀⟩, hLp₀, hord⟩ :=
      exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top hf₀
    let E_equiv : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
      (consCLE n).symm.trans (L.trans (consCLE n))
    let h : Fin m → (Fin n → ℝ) × ℝ → ℝ := fun i p ↦ f₀ i (L p)
    have hLcons : consCLE n (L (y₀, t₀)) = x₀ := by rw [hLp₀, (consCLE n).apply_symm_apply]
    have hh (i : Fin m) : AnalyticAt ℝ (h i) (y₀, t₀) :=
      (hf₀ i).comp_of_eq (L.analyticAt _) hLp₀
    have hW : (L.trans (consCLE n)) ⁻¹' V ∈ 𝓝 (y₀, t₀) :=
      (L.trans (consCLE n)).continuous.continuousAt.preimage_mem_nhds
        (by simpa [hLcons] using hV)
    have hord' (i : Fin m) (hi : ¬h i =ᶠ[𝓝 (y₀, t₀)] 0) :
        analyticOrderAt (fun t ↦ h i (y₀, t)) t₀ ≠ ⊤ :=
      hord i fun hf₀0 ↦ hi <|
        (L.continuous.continuousAt.tendsto.mono_right (le_of_eq (congrArg 𝓝 hLp₀))).eventually hf₀0
    obtain ⟨U₁, hU₁open, hq₀U₁, hU₁W, 𝒞₁, h𝒞₁, hsign₁⟩ :=
      step_vertical_nonsingular ih hh hW hord'
    have hEapply (v : Fin (n + 1) → ℝ) : E_equiv v = consCLE n (L (Fin.tail v, v 0)) := by
      simp [E_equiv]
    refine ⟨E_equiv '' U₁, E_equiv.toHomeomorph.isOpenMap U₁ hU₁open,
      ⟨Fin.cons t₀ y₀, hq₀U₁, by simp [hEapply, hLcons]⟩, ?_,
      image E_equiv '' 𝒞₁, h𝒞₁.image_continuousLinearEquiv E_equiv, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      simpa [hEapply] using hU₁W v hv
    · rintro i _ ⟨E, hE, rfl⟩
      rw [signInvariant_image]
      exact (hsign₁ i E hE).congr fun v _ ↦ by simp [h, f₀, hEapply]

/-! ### Main existence theorems -/

/-- **Local normal decomposition for finite real-analytic families.** Given finitely many real
functions `f i` analytic at `x₀ ∈ ℝⁿ` and a neighborhood `V ∈ 𝓝 x₀`, there exist an open
neighborhood `U ⊆ V` of `x₀` and a normal decomposition `𝒞` of `U` on every piece of which every
`f i` is sign-invariant. -/
theorem exists_isNormalDecomposition_signInvariant_nhds {n : ℕ} {ι : Type*} [Finite ι]
    {f : ι → (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ} {V : Set (Fin n → ℝ)}
    (hf : ∀ i, AnalyticAt ℝ (f i) x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧
      ∃ 𝒞 : Set (Set (Fin n → ℝ)), IsNormalDecomposition U 𝒞 ∧
        ∀ i, ∀ S ∈ 𝒞, SignInvariant (f i) S := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨U, hUo, hx₀U, hUV, 𝒞, h𝒞, hsign⟩ :=
    exists_isNormalDecomposition_signInvariant_fin (f := fun k ↦ f (e.symm k))
      (fun k ↦ hf (e.symm k)) hV
  exact ⟨U, hUo, hx₀U, hUV, 𝒞, h𝒞, fun i S hS ↦ by simpa using hsign (e i) S hS⟩

/-- **Local normal decomposition adapted to finitely many semianalytic germs.** Given finitely many
sets `s i ⊆ ℝⁿ` that are semianalytic at `x₀` and a neighborhood `V ∈ 𝓝 x₀`, there exist an open
neighborhood `U ⊆ V` of `x₀` and a normal decomposition `𝒞` of `U` compatible with every `s i`:
each piece of `𝒞` is either contained in `s i` or disjoint from `s i`. Consequently, `U ∩ s i`,
`U ∩ closure (s i)`, and `U ∩ (closure (s i) \ s i)` are unions of pieces of `𝒞` (via
`IsNormalDecomposition.inter_eq_sUnion_sep`,
`IsNormalDecomposition.inter_closure_eq_sUnion_of_isOpen`, and
`IsNormalDecomposition.inter_closure_sdiff_eq_sUnion_of_isOpen`). -/
theorem exists_isNormalDecomposition_semianalyticAt_nhds {n : ℕ} {ι : Type*} [Finite ι]
    {s : ι → Set (Fin n → ℝ)} {x₀ : Fin n → ℝ} {V : Set (Fin n → ℝ)}
    (hs : ∀ i, SemianalyticAt (s i) x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧
      ∃ 𝒞 : Set (Set (Fin n → ℝ)), IsNormalDecomposition U 𝒞 ∧
        ∀ i, ∀ S ∈ 𝒞, S ⊆ s i ∨ Disjoint S (s i) := by
  classical
  let := Fintype.ofFinite ι
  choose W hW _ t ht hst using fun i ↦ (hs i).exists_subset hV
  choose m g hg Φ hΦ using fun i ↦ (ht i).exists_eq_setOf_sign
  have hW' : V ∩ (⋂ i, interior (W i)) ∈ 𝓝 x₀ :=
    inter_mem hV (iInter_mem.2 fun i ↦ interior_mem_nhds.2 (hW i))
  have hgan (p : Σ i : ι, Fin (m i)) : AnalyticAt ℝ (g p.1 p.2) x₀ :=
    hg p.1 p.2 x₀ (mem_of_mem_nhds (hW p.1))
  obtain ⟨U, hUo, hx₀U, hUW', 𝒞, h𝒞, hgsign⟩ :=
    exists_isNormalDecomposition_signInvariant_nhds hgan hW'
  refine ⟨U, hUo, hx₀U, hUW'.trans inter_subset_left, 𝒞, h𝒞, fun i S hS ↦ ?_⟩
  have hSW : S ⊆ W i :=
    (h𝒞.subset_of_mem hS).trans
      (hUW'.trans (inter_subset_right.trans ((iInter_subset _ i).trans interior_subset)))
  rcases subset_or_disjoint_setOf_sign (fun j ↦ hgsign ⟨i, j⟩ S hS) (Φ i) with hsub | hdisj
  · rw [← hΦ i] at hsub
    refine Or.inl fun x hx ↦ ?_
    have hxt : x ∈ t i ∩ W i := ⟨hsub hx, hSW hx⟩
    rw [← hst i] at hxt
    exact hxt.1
  · rw [← hΦ i] at hdisj
    refine Or.inr (disjoint_left.2 fun x hxS hxs ↦ ?_)
    have hxt : x ∈ t i ∩ W i := by
      rw [← hst i]
      exact ⟨hxs, hSW hxS⟩
    exact disjoint_left.1 hdisj hxS hxt.1

/-- **Local normal decomposition for a single semianalytic germ.** -/
theorem SemianalyticAt.exists_isNormalDecomposition_nhds {n : ℕ} {s V : Set (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} (hs : SemianalyticAt s x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧
      ∃ 𝒞 : Set (Set (Fin n → ℝ)), IsNormalDecomposition U 𝒞 ∧
        ∀ S ∈ 𝒞, S ⊆ s ∨ Disjoint S s := by
  obtain ⟨U, hUo, hx₀U, hUV, 𝒞, h𝒞, hcompat⟩ :=
    exists_isNormalDecomposition_semianalyticAt_nhds (ι := Unit) (fun _ ↦ hs) hV
  exact ⟨U, hUo, hx₀U, hUV, 𝒞, h𝒞, hcompat ()⟩

end TauCeti

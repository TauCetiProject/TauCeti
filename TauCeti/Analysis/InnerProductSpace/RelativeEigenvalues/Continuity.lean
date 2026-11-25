/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.Sorted
import TauCeti.LinearAlgebra.Dimension.CardEqFinrank

/-!
# Continuity of the sorted eigenvalue vector relative to a varying form

The sorted eigenvalue vector `λ_h[a]` (`TauCeti.relEigenvalueVector`) depends continuously on the
pair of forms `(h, a)`, the reference form `h` included, at every positive definite `h`: if
Hermitian forms `h_i` and `a_i` converge pointwise to `h₀` and `a₀`, with `h₀` positive definite,
then `λ_{h_i}[a_i] → λ_{h₀}[a₀]` (`TauCeti.tendsto_relEigenvalueVector`). Weyl's bound
(`LinearMap.IsSymm.abs_relEigenvalues_sub_le_opNorm`) covers a fixed reference inner product only;
here the reference form moves, as a Hermitian metric does from point to point.

The proof is a compactness argument in the coordinates of a basis. Near `h₀`, the forms `h_i` are
bounded below by a fixed multiple of the squared coordinate norm, so the `h_i`-orthonormal
eigenvector families of the `a_i` and the eigenvalue vectors stay bounded. Along any ultrafilter on
which the eigenvalue vectors converge to some `μ`, the eigenvector families have a limit point,
which shows that `μ` is an antitone eigenvalue vector of `a₀` relative to `h₀`, so `μ = λ_{h₀}[a₀]`
by uniqueness (`TauCeti.IsRelEigenvalueVector.eq_of_antitone`).

## Main results

* `TauCeti.tendsto_relEigenvalueVector`: `λ_{h_i}[a_i] → λ_{h₀}[a₀]` along any filter, for pointwise
  convergent Hermitian forms with positive definite `h₀`.
* `TauCeti.continuousAt_relEigenvalueVector`: the same for families of forms on a topological
  space.
-/

public section

open Filter Module Metric Topology

noncomputable section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

section Coordinates

variable {m : ℕ}

/-- The sesquilinear form with Gram matrix `G`, in coordinates. -/
private def coordForm (G : Fin m → Fin m → 𝕜) (p q : Fin m → 𝕜) : 𝕜 :=
  ∑ k, ∑ l, starRingEnd 𝕜 (p k) * q l * G k l

private theorem apply_eq_coordForm (b : Basis (Fin m) 𝕜 E) (s : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜)
    (u v : E) : s u v = coordForm (fun k l ↦ s (b k) (b l)) (b.equivFun u) (b.equivFun v) := by
  conv_lhs => rw [← b.sum_equivFun u, ← b.sum_equivFun v]
  simp only [coordForm, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
  ring

private theorem coordForm_sub (G G' : Fin m → Fin m → 𝕜) (p : Fin m → 𝕜) :
    coordForm (G - G') p p = coordForm G p p - coordForm G' p p := by
  simp only [coordForm, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem coordForm_smul (G : Fin m → Fin m → 𝕜) (t : 𝕜) (p : Fin m → 𝕜) :
    coordForm G (t • p) (t • p) = (starRingEnd 𝕜 t * t) * coordForm G p p := by
  simp only [coordForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
  ring

private theorem norm_coordForm_le (G : Fin m → Fin m → 𝕜) (p : Fin m → 𝕜) :
    ‖coordForm G p p‖ ≤ (∑ k, ∑ l, ‖G k l‖) * ‖p‖ ^ 2 := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ ↦ (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ ↦ ?_
  rw [norm_mul, norm_mul, RCLike.norm_conj, sq]
  have hk := norm_le_pi_norm p k
  have hl := norm_le_pi_norm p l
  have := mul_le_mul hk hl (norm_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (G k l)]

private theorem tendsto_coordForm {ι : Type*} {l : Filter ι} {G : ι → Fin m → Fin m → 𝕜}
    {G₀ : Fin m → Fin m → 𝕜} {p q : ι → Fin m → 𝕜} {p₀ q₀ : Fin m → 𝕜}
    (hG : ∀ k k', Tendsto (fun i ↦ G i k k') l (𝓝 (G₀ k k'))) (hp : Tendsto p l (𝓝 p₀))
    (hq : Tendsto q l (𝓝 q₀)) :
    Tendsto (fun i ↦ coordForm (G i) (p i) (q i)) l (𝓝 (coordForm G₀ p₀ q₀)) :=
  tendsto_finsetSum _ fun k _ ↦ tendsto_finsetSum _ fun k' _ ↦
    ((((RCLike.continuous_conj.tendsto _).comp (((continuous_apply k).tendsto _).comp hp)).mul
      (((continuous_apply k').tendsto _).comp hq))).mul (hG k k')

private theorem continuous_coordForm (G : Fin m → Fin m → 𝕜) :
    Continuous fun p ↦ coordForm G p p :=
  continuous_iff_continuousAt.2 fun _ ↦
    tendsto_coordForm (fun _ _ ↦ tendsto_const_nhds) tendsto_id tendsto_id

/-- A positive definite form is bounded below on coordinates by a multiple of the squared norm. -/
private theorem exists_pos_mul_sq_le_re_coordForm {G : Fin m → Fin m → 𝕜}
    (hG : ∀ p, p ≠ 0 → 0 < RCLike.re (coordForm G p p)) :
    ∃ c > 0, ∀ p, c * ‖p‖ ^ 2 ≤ RCLike.re (coordForm G p p) := by
  -- the scaling `p = ‖p‖ • (‖p‖⁻¹ • p)` reduces the bound to the unit sphere
  have hscale (p : Fin m → 𝕜) (hp : p ≠ 0) :
      RCLike.re (coordForm G p p) =
        ‖p‖ ^ 2 * RCLike.re (coordForm G (((‖p‖⁻¹ : ℝ) : 𝕜) • p) (((‖p‖⁻¹ : ℝ) : 𝕜) • p)) := by
    rw [coordForm_smul, RCLike.conj_ofReal, ← RCLike.ofReal_mul, RCLike.re_ofReal_mul]
    field_simp
  have hsphere (p : Fin m → 𝕜) (hp : p ≠ 0) : ((‖p‖⁻¹ : ℝ) : 𝕜) • p ∈ sphere 0 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hp)]
  rcases (sphere (0 : Fin m → 𝕜) 1).eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun p ↦ ?_⟩
    rcases eq_or_ne p 0 with rfl | hp
    · simp [coordForm]
    · exact absurd (hS ▸ hsphere p hp) (Set.notMem_empty _)
  obtain ⟨p₀, hp₀, hmin⟩ := (isCompact_sphere (0 : Fin m → 𝕜) 1).exists_isMinOn hS
    (RCLike.continuous_re.comp (continuous_coordForm G)).continuousOn
  have hp₀0 : p₀ ≠ 0 := ne_zero_of_mem_unit_sphere ⟨p₀, hp₀⟩
  refine ⟨_, hG p₀ hp₀0, fun p ↦ ?_⟩
  rcases eq_or_ne p 0 with rfl | hp
  · simp [coordForm]
  rw [hscale p hp, mul_comm]
  exact mul_le_mul_of_nonneg_left (hmin (hsphere p hp)) (sq_nonneg _)

end Coordinates

section Limits

variable {ι : Type*} {h a : ι → E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜} {h₀ a₀ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜}

/-- Near a positive definite `h₀`, the forms `h i` are bounded below on coordinates by a fixed
multiple of the squared norm. -/
private theorem exists_eventually_le_re_coordForm {m : ℕ} {l : Filter ι} (b : Basis (Fin m) 𝕜 E)
    (hpos₀ : ∀ v, v ≠ 0 → 0 < RCLike.re (h₀ v v))
    (hhl : ∀ u v, Tendsto (fun i ↦ h i u v) l (𝓝 (h₀ u v))) :
    ∃ c > 0, ∀ᶠ i in l, ∀ p, c * ‖p‖ ^ 2 ≤
      RCLike.re (coordForm (fun k k' ↦ h i (b k) (b k')) p p) := by
  set G : ι → Fin m → Fin m → 𝕜 := fun i k k' ↦ h i (b k) (b k')
  set G₀ : Fin m → Fin m → 𝕜 := fun k k' ↦ h₀ (b k) (b k')
  obtain ⟨c, hc, hc₀⟩ := exists_pos_mul_sq_le_re_coordForm (G := G₀) fun p hp ↦ by
    have := hpos₀ _ (b.equivFun.symm.map_ne_zero_iff.2 hp)
    rwa [apply_eq_coordForm b, LinearEquiv.apply_symm_apply] at this
  have hdist : Tendsto (fun i ↦ ∑ k, ∑ k', ‖(G i - G₀) k k'‖) l (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ fun k _ ↦ tendsto_finsetSum Finset.univ fun k' _ ↦
      ((hhl (b k) (b k')).sub_const (G₀ k k')).norm
    simpa [G, G₀] using this
  refine ⟨c / 2, half_pos hc, ?_⟩
  filter_upwards [hdist.eventually (gt_mem_nhds (half_pos hc))] with i hi p
  have h1 := (RCLike.abs_re_le_norm (coordForm (G i - G₀) p p)).trans
    ((norm_coordForm_le _ p).trans (mul_le_mul_of_nonneg_right hi.le (sq_nonneg _)))
  rw [coordForm_sub, map_sub] at h1
  linarith [hc₀ p, (abs_le.1 h1).1]

/-- **The eigenvalue-vector relation is closed.** If `h i`-orthonormal families `B i`
diagonalizing `a i` with diagonal `M i` have converging coordinates, and `M i → μ`, then `μ` is an
eigenvalue vector of `a₀` relative to `h₀`. -/
private theorem isRelEigenvalueVector_of_tendsto {F : Filter ι} [F.NeBot]
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) {B : ι → Fin (finrank 𝕜 E) → E}
    {M : ι → Fin (finrank 𝕜 E) → ℝ} {Q₀ : Fin (finrank 𝕜 E) → Fin (finrank 𝕜 E) → 𝕜}
    {μ : Fin (finrank 𝕜 E) → ℝ}
    (hB : ∀ᶠ i in F, ∀ k k', h i (B i k) (B i k') = (if k = k' then 1 else 0) ∧
      a i (B i k) (B i k') = (if k = k' then (M i k : 𝕜) else 0))
    (hQ : Tendsto (fun i k ↦ b.equivFun (B i k)) F (𝓝 Q₀)) (hM : Tendsto M F (𝓝 μ))
    (hhl : ∀ u v, Tendsto (fun i ↦ h i u v) F (𝓝 (h₀ u v)))
    (hal : ∀ u v, Tendsto (fun i ↦ a i u v) F (𝓝 (a₀ u v))) :
    IsRelEigenvalueVector (h₀ · ·) (a₀ · ·) μ := by
  set B₀ : Fin (finrank 𝕜 E) → E := fun k ↦ b.equivFun.symm (Q₀ k)
  have hcoord (k) : Tendsto (fun i ↦ b.equivFun (B i k)) F (𝓝 (b.equivFun (B₀ k))) := by
    rw [show b.equivFun (B₀ k) = Q₀ k from LinearEquiv.apply_symm_apply _ _]
    exact ((continuous_apply k).tendsto _).comp hQ
  have hlim (s : ι → E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (s₀ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜)
      (hs : ∀ u v, Tendsto (fun i ↦ s i u v) F (𝓝 (s₀ u v))) (k k') :
      Tendsto (fun i ↦ s i (B i k) (B i k')) F (𝓝 (s₀ (B₀ k) (B₀ k'))) := by
    rw [apply_eq_coordForm b s₀ (B₀ k) (B₀ k')]
    refine (tendsto_coordForm (G := fun i k k' ↦ s i (b k) (b k'))
      (fun _ _ ↦ hs _ _) (hcoord k) (hcoord k')).congr fun i ↦ ?_
    exact (apply_eq_coordForm b (s i) _ _).symm
  refine (isRelEigenvalueVector_def _ _ _).2 ⟨B₀, fun k k' ↦ ⟨?_, ?_⟩⟩
  · refine tendsto_nhds_unique (hlim h h₀ hhl k k') (tendsto_const_nhds.congr' ?_)
    filter_upwards [hB] with i hi using ((hi k k').1).symm
  · refine tendsto_nhds_unique (hlim a a₀ hal k k') ?_
    have hite : Tendsto (fun i ↦ if k = k' then (M i k : 𝕜) else 0) F
        (𝓝 (if k = k' then (μ k : 𝕜) else 0)) := by
      split_ifs
      · exact (RCLike.continuous_ofReal.tendsto _).comp (((continuous_apply k).tendsto _).comp hM)
      · exact tendsto_const_nhds
    refine hite.congr' ?_
    filter_upwards [hB] with i hi using ((hi k k').2).symm

/-- A cluster point of the sorted eigenvalue vectors of `a i` relative to `h i`, along which the
eigenvector families stay bounded, is `λ_{h₀}[a₀]`. -/
private theorem eq_relEigenvalueVector_of_mapClusterPt {l : Filter ι}
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) {B : ι → Fin (finrank 𝕜 E) → E} {R : ℝ}
    {μ : Fin (finrank 𝕜 E) → ℝ}
    (hB : ∀ᶠ i in l, ∀ k k', h i (B i k) (B i k') = (if k = k' then 1 else 0) ∧
      a i (B i k) (B i k') =
        (if k = k' then (relEigenvalueVector (h i · ·) (a i · ·) k : 𝕜) else 0))
    (hQ : ∀ᶠ i in l, (fun k ↦ b.equivFun (B i k)) ∈ closedBall 0 R)
    (hμ : MapClusterPt μ l fun i ↦ relEigenvalueVector (h i · ·) (a i · ·))
    (hhl : ∀ u v, Tendsto (fun i ↦ h i u v) l (𝓝 (h₀ u v)))
    (hal : ∀ u v, Tendsto (fun i ↦ a i u v) l (𝓝 (a₀ u v))) :
    μ = relEigenvalueVector (h₀ · ·) (a₀ · ·) := by
  obtain ⟨U, hUl, hU⟩ := mapClusterPt_iff_ultrafilter.1 hμ
  obtain ⟨Q₀, -, hQ₀⟩ := (isCompact_closedBall _ _).ultrafilter_le_nhds'
    (U.map fun i k ↦ b.equivFun (B i k)) (Ultrafilter.mem_map.2 (hUl hQ))
  have hμa : Antitone μ := fun k k' hkk' ↦
    le_of_tendsto_of_tendsto (((continuous_apply k').tendsto _).comp hU)
      (((continuous_apply k).tendsto _).comp hU)
      (Eventually.of_forall fun i ↦ antitone_relEigenvalueVector _ _ hkk')
  exact ((isRelEigenvalueVector_of_tendsto b (hUl hB) hQ₀ hU (fun u v ↦ (hhl u v).mono_left hUl)
    fun u v ↦ (hal u v).mono_left hUl).relEigenvalueVector_eq hμa).symm

/-- **Continuity of the sorted eigenvalue vector in the pair of forms.** If Hermitian forms `h i`
and `a i` converge pointwise to `h₀` and `a₀` along a filter, with `h₀` positive definite, then
`λ_{h i}[a i] → λ_{h₀}[a₀]`. The reference forms `h i` are allowed to vary. -/
theorem tendsto_relEigenvalueVector {l : Filter ι}
    (hh : ∀ᶠ i in l, (h i).IsSymm) (ha : ∀ᶠ i in l, (a i).IsSymm)
    (hpos₀ : ∀ v, v ≠ 0 → 0 < RCLike.re (h₀ v v))
    (hhl : ∀ u v, Tendsto (fun i ↦ h i u v) l (𝓝 (h₀ u v)))
    (hal : ∀ u v, Tendsto (fun i ↦ a i u v) l (𝓝 (a₀ u v))) :
    Tendsto (fun i ↦ relEigenvalueVector (h i · ·) (a i · ·)) l
      (𝓝 (relEigenvalueVector (h₀ · ·) (a₀ · ·))) := by
  by_cases hE : FiniteDimensional 𝕜 E
  swap
  · -- in infinite dimension `finrank 𝕜 E = 0` and the eigenvalue vectors are empty
    have : IsEmpty (Fin (finrank 𝕜 E)) :=
      Module.isEmpty_of_card_eq_finrank_of_not_finite (Fintype.card_fin _) hE
    exact tendsto_const_nhds.congr fun _ ↦ Subsingleton.elim _ _
  set n := finrank 𝕜 E
  set b := Module.finBasis 𝕜 E
  set M := fun i ↦ relEigenvalueVector (h i · ·) (a i · ·)
  obtain ⟨c, hc, hlow⟩ := exists_eventually_le_re_coordForm b hpos₀ hhl
  -- eventually `a i` is bounded above by `K` on coordinates
  set K := ∑ k, ∑ k', ‖a₀ (b k) (b k')‖ + 1
  have hK : ∀ᶠ i in l, ∑ k, ∑ k', ‖a i (b k) (b k')‖ < K :=
    (tendsto_finsetSum Finset.univ fun k _ ↦ tendsto_finsetSum Finset.univ fun k' _ ↦
      (hal (b k) (b k')).norm).eventually (gt_mem_nhds (lt_add_one _))
  have hpos : ∀ᶠ i in l, ∀ v, v ≠ 0 → 0 < RCLike.re (h i v v) := by
    filter_upwards [hlow] with i hi v hv
    rw [apply_eq_coordForm b]
    exact (mul_pos hc (pow_pos (norm_pos_iff.2 (by simpa using hv)) 2)).trans_le (hi _)
  -- eigenvector families `B i` of `a i` relative to `h i`, with coordinates `Q i`
  set P : ι → (Fin n → E) → Prop := fun i B ↦ ∀ k k',
    h i (B k) (B k') = (if k = k' then 1 else 0) ∧
      a i (B k) (B k') = (if k = k' then (M i k : 𝕜) else 0)
  set B : ι → Fin n → E := fun i ↦ Classical.epsilon (P i)
  have hB : ∀ᶠ i in l, P i (B i) := by
    filter_upwards [hh, ha, hpos] with i hhi hai hposi
    exact Classical.epsilon_spec ((isRelEigenvalueVector_def _ _ _).1
      (isRelEigenvalueVector_relEigenvalueVector hhi hposi hai))
  set Q : ι → Fin n → Fin n → 𝕜 := fun i k ↦ b.equivFun (B i k)
  have hQsq : ∀ᶠ i in l, ∀ k, ‖Q i k‖ ^ 2 ≤ c⁻¹ := by
    filter_upwards [hB, hlow] with i hBi hlowi k
    have h1 := hlowi (Q i k)
    rw [show coordForm _ (Q i k) (Q i k) = 1 by
      rw [← apply_eq_coordForm b]; simpa using (hBi k k).1, RCLike.one_re] at h1
    rwa [← le_div_iff₀' hc, one_div] at h1
  have hQ : ∀ᶠ i in l, Q i ∈ closedBall 0 (1 + c⁻¹) := by
    filter_upwards [hQsq] with i hi
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    exact fun k ↦ by nlinarith [hi k, norm_nonneg (Q i k)]
  have hM : ∀ᶠ i in l, M i ∈ closedBall 0 (K * c⁻¹) := by
    filter_upwards [hB, hQsq, hK] with i hBi hQi hKi
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    have h1 : (M i k : 𝕜) = coordForm (fun k k' ↦ a i (b k) (b k')) (Q i k) (Q i k) := by
      rw [← apply_eq_coordForm b]; simpa using ((hBi k k).2).symm
    rw [Real.norm_eq_abs, ← RCLike.norm_ofReal (K := 𝕜), h1]
    exact (norm_coordForm_le _ _).trans (mul_le_mul hKi.le (hQi k) (sq_nonneg _) (by positivity))
  -- every cluster point of the eigenvalue vectors is `λ_{h₀}[a₀]`
  exact (isCompact_closedBall _ _).tendsto_nhds_of_unique_mapClusterPt hM fun μ _ hμ ↦
    eq_relEigenvalueVector_of_mapClusterPt b hB hQ hμ hhl hal

/-- **Continuity of the sorted eigenvalue vector of a family of forms.** If families of Hermitian
forms `h x` and `a x` on a topological space are pointwise continuous at `x₀`, with `h x₀`
positive definite, then `x ↦ λ_{h x}[a x]` is continuous at `x₀`. -/
theorem continuousAt_relEigenvalueVector {X : Type*} [TopologicalSpace X]
    {h a : X → E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜} {x₀ : X}
    (hh : ∀ᶠ x in 𝓝 x₀, (h x).IsSymm) (ha : ∀ᶠ x in 𝓝 x₀, (a x).IsSymm)
    (hpos₀ : ∀ v, v ≠ 0 → 0 < RCLike.re (h x₀ v v))
    (hhc : ∀ u v, ContinuousAt (fun x ↦ h x u v) x₀)
    (hac : ∀ u v, ContinuousAt (fun x ↦ a x u v) x₀) :
    ContinuousAt (fun x ↦ relEigenvalueVector (h x · ·) (a x · ·)) x₀ :=
  tendsto_relEigenvalueVector hh ha hpos₀ hhc hac

end Limits

end TauCeti

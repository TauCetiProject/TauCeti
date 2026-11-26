/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.Sorted
import TauCeti.Analysis.Matrix.PosDef
import TauCeti.LinearAlgebra.Dimension.CardEqFinrank
import TauCeti.Topology.Instances.Matrix

/-!
# Continuity of the sorted eigenvalue vector relative to a varying form

The sorted eigenvalue vector `λ_h[a]` (`TauCeti.relEigenvalueVector`) depends continuously on the
pair of forms `(h, a)`, the reference form `h` included, at every positive definite `h`: if
Hermitian forms `h_i` and `a_i` converge pointwise to `h₀` and `a₀`, with `h₀` positive definite,
then `λ_{h_i}[a_i] → λ_{h₀}[a₀]` (`TauCeti.tendsto_relEigenvalueVector`). Weyl's bound
(`LinearMap.IsSymm.abs_relEigenvalues_sub_le_opNorm`) covers a fixed reference inner product only;
here the reference form moves, as a Hermitian metric does from point to point.

The proof is a compactness argument on the Gram matrices (`LinearMap.toMatrix₂`) of the forms in a
basis. Positivity of the real part of a matrix form on nonzero vectors is an open condition
(`TauCeti.isOpen_setOfPred_re_dotProduct_pos`), so near `h₀` the forms `h_i` still dominate a fixed
multiple of the squared coordinates and fixed multiples of `± a_i`. Hence the `h_i`-orthonormal
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

open Filter Matrix Module Metric Topology

noncomputable section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

section Coordinates

variable {m : ℕ}

/-- The real part of `star p ⬝ᵥ p` bounds the square of each coordinate of `p`. -/
private theorem norm_sq_le_re_star_dotProduct_self (p : Fin m → 𝕜) (k : Fin m) :
    ‖p k‖ ^ 2 ≤ RCLike.re (star p ⬝ᵥ p) := by
  have : RCLike.re (star p ⬝ᵥ p) = ∑ l, ‖p l‖ ^ 2 := by
    simp [dotProduct, RCLike.conj_mul]
  rw [this]
  exact Finset.single_le_sum (f := fun l ↦ ‖p l‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
    (Finset.mem_univ k)

/-- A vector `q` with `star q ⬝ᵥ G *ᵥ q = 1` has norm at most `1 + c⁻¹` when `G - c • 1` still has
a form with positive real part on nonzero vectors. -/
private theorem norm_le_of_star_dotProduct_mulVec_eq_one {G : Matrix (Fin m) (Fin m) 𝕜} {c : ℝ}
    (hc : 0 < c) (hG : ∀ p, p ≠ 0 →
      0 < RCLike.re (star p ⬝ᵥ G *ᵥ p) + c * RCLike.re (star p ⬝ᵥ (-1 : Matrix _ _ 𝕜) *ᵥ p))
    {q : Fin m → 𝕜} (hq : star q ⬝ᵥ G *ᵥ q = 1) : ‖q‖ ≤ 1 + c⁻¹ := by
  have h1 := hG q (by rintro rfl; simp at hq)
  simp only [neg_mulVec, one_mulVec, dotProduct_neg, map_neg, hq, RCLike.one_re] at h1
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k ↦ ?_
  have h2 := norm_sq_le_re_star_dotProduct_self q k
  have h3 : ‖q k‖ ^ 2 ≤ c⁻¹ := by
    rw [← one_div, le_div_iff₀ hc]
    nlinarith [mul_le_mul_of_nonneg_right h2 hc.le]
  nlinarith [norm_nonneg (q k)]

/-- If `star q ⬝ᵥ G *ᵥ q = 1` and `star q ⬝ᵥ A *ᵥ q = x`, then `‖x‖ ≤ t⁻¹ + t'⁻¹`
when `G + t • A` and `G - t' • A` still have forms with positive real part on nonzero vectors. -/
private theorem norm_le_of_star_dotProduct_mulVec_eq {G A : Matrix (Fin m) (Fin m) 𝕜}
    {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t')
    (hup : ∀ p, p ≠ 0 → 0 < RCLike.re (star p ⬝ᵥ G *ᵥ p) + t * RCLike.re (star p ⬝ᵥ A *ᵥ p))
    (hdown : ∀ p, p ≠ 0 → 0 < RCLike.re (star p ⬝ᵥ G *ᵥ p) + t' * RCLike.re (star p ⬝ᵥ -A *ᵥ p))
    {q : Fin m → 𝕜} (hq : star q ⬝ᵥ G *ᵥ q = 1) {x : ℝ} (hx : star q ⬝ᵥ A *ᵥ q = x) :
    ‖x‖ ≤ t⁻¹ + t'⁻¹ := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have h1 := hup q hq0
  have h2 := hdown q hq0
  simp only [neg_mulVec, dotProduct_neg, map_neg, hq, hx, RCLike.one_re, RCLike.ofReal_re]
    at h1 h2
  have h3 : -x < t⁻¹ := by
    rw [← one_div, lt_div_iff₀ ht]
    linarith
  have h4 : x < t'⁻¹ := by
    rw [← one_div, lt_div_iff₀ ht']
    linarith
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [inv_pos.2 ht, inv_pos.2 ht']

end Coordinates

section Limits

variable {ι : Type*} {h a : ι → E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜} {h₀ a₀ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜}

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
    rw [apply_eq_star_dotProduct_toMatrix₂_mulVec b (B := s₀)]
    refine (((by fun_prop : Continuous fun z : Matrix (Fin (finrank 𝕜 E)) (Fin (finrank 𝕜 E)) 𝕜 ×
      (Fin (finrank 𝕜 E) → 𝕜) × (Fin (finrank 𝕜 E) → 𝕜) ↦ star z.2.1 ⬝ᵥ z.1 *ᵥ z.2.2).tendsto
        _).comp ((LinearMap.tendsto_toMatrix₂ b b hs).prodMk_nhds
          ((hcoord k).prodMk_nhds (hcoord k')))).congr fun i ↦ ?_
    exact (apply_eq_star_dotProduct_toMatrix₂_mulVec b (B := s i) _ _).symm
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
  -- Gram matrices of the forms in the basis `b`
  have hG := LinearMap.tendsto_toMatrix₂ b b hhl
  have hA := LinearMap.tendsto_toMatrix₂ b b hal
  have hG₀ := (LinearMap.forall_re_pos_iff_toMatrix₂ b).1 hpos₀
  -- eventually `h i` dominates `c` times the coordinate form and `t`, `t'` times `± a i`
  obtain ⟨c, hc, hlow⟩ := exists_pos_eventually_re_add_smul_pos hG
    (tendsto_const_nhds (x := -1)) hG₀
  obtain ⟨t, ht, hup⟩ := exists_pos_eventually_re_add_smul_pos hG hA hG₀
  obtain ⟨t', ht', hdown⟩ := exists_pos_eventually_re_add_smul_pos hG hA.neg hG₀
  have hpos : ∀ᶠ i in l, ∀ v, v ≠ 0 → 0 < RCLike.re (h i v v) :=
    (hG.eventually (isOpen_setOfPred_re_dotProduct_pos.mem_nhds hG₀)).mono fun i hi ↦
      (LinearMap.forall_re_pos_iff_toMatrix₂ b).2 hi
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
  have hQ1 : ∀ᶠ i in l, ∀ k, star (Q i k) ⬝ᵥ LinearMap.toMatrix₂ b b (h i) *ᵥ Q i k = 1 ∧
      star (Q i k) ⬝ᵥ LinearMap.toMatrix₂ b b (a i) *ᵥ Q i k = M i k := by
    filter_upwards [hB] with i hBi k
    simp only [Q, Basis.equivFun_apply, ← apply_eq_star_dotProduct_toMatrix₂_mulVec b]
    simpa using hBi k k
  have hQ : ∀ᶠ i in l, Q i ∈ closedBall 0 (1 + c⁻¹) := by
    filter_upwards [hlow, hQ1] with i hlowi hQi
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    exact fun k ↦ norm_le_of_star_dotProduct_mulVec_eq_one hc hlowi (hQi k).1
  have hM : ∀ᶠ i in l, M i ∈ closedBall 0 (t⁻¹ + t'⁻¹) := by
    filter_upwards [hup, hdown, hQ1] with i hupi hdowni hQi
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    exact fun k ↦ norm_le_of_star_dotProduct_mulVec_eq ht ht' hupi hdowni (hQi k).1 (hQi k).2
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

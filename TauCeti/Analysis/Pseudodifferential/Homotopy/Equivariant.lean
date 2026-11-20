/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Homotopy.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Integral
public import TauCeti.RepresentationTheory.Compact.Haar
public import TauCeti.RepresentationTheory.Continuous.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Topology.MetricSpace.ContinuousRadius

/-!
# Smooth equivariant homotopies of elliptic homogeneous symbols

Let a compact group `G` act by representations (`ContRepresentation`) that are continuous in the
operator norm: linearly on positions by `ρ`, norm-preservingly on frequencies by `κ`, and by
contractions `σV`, `σW` on the coefficient spaces `V` and `W`. A homogeneous symbol `a` is
*equivariant* when `a(ρ g x, κ g ξ) ∘ σV g = σW g ∘ a(x, ξ)` for every `g`, equivalently
`σW g ∘ a(ρ g⁻¹ x, κ g⁻¹ ξ) ∘ σV g⁻¹ = a(x, ξ)`. The equivariant index theory of §7.2 of the
roadmap compares equivariant elliptic operators along homotopies of equivariant symbols, and
quantizes these homotopies, which therefore have to be smooth.

This file refines `HomogeneousSymbol.exists_contDiffOn_isElliptic_homotopy`, which smooths a
continuous homotopy `a t` of invertible symbols between smooth endpoints, to the equivariant
setting: if every `a t` is equivariant, the smooth elliptic homotopy can be chosen equivariant as
well, still with the same endpoints, joint smoothness in `(t, x, ξ)` at nonzero frequencies and
closeness to `a` after a time change
(`HomogeneousSymbol.exists_contDiffOn_isElliptic_equivariant_homotopy`).

## The argument

Smooth first, then average. The smooth homotopy `b t` given by the non-equivariant theorem is
averaged over the normalized Haar measure `μ` of `G`,

`b' t (x, ξ) = ∫ σW g ∘ b t (ρ g⁻¹ x, κ g⁻¹ ξ) ∘ σV g⁻¹ dμ(g)`,

which is equivariant since `μ` is left-invariant. Time is treated as one more position variable,
so that `HomogeneousSymbol.integral` of the family of conjugates of `(t, x, ξ) ↦ b t (x, ξ)` gives
joint smoothness in `(t, x, ξ)`. Its hypothesis, joint continuity of all jets of the conjugates in
`g`, holds because the conjugate is a jointly smooth function of `(t, x, ξ)` and of the operators
`ρ g⁻¹`, `κ g⁻¹`, `σW g`, `σV g⁻¹` (`ContDiffOn.continuousOn_iteratedFDeriv_partial`).

Averaging fixes equivariant symbols, so the endpoints are kept. For invertibility the precision
given to the smoothing step is at most half of an invariant margin of invertibility of the
homotopy: the least margin of invertibility of `a s (ρ g x, u)` over `g ∈ G`, `s ∈ [0, 1]` and
unit frequencies `u`, which depends continuously on `x` by compactness. Since `a s` is equivariant
and the actions on `V` and `W` are contractions, the distance from `b' t` to `a (σ t)` at a unit
frequency is at most the largest distance from `b t` to `a (σ t)` over the orbit, hence below the
margin.

## Main declaration

* `TauCeti.HomogeneousSymbol.exists_contDiffOn_isElliptic_equivariant_homotopy`: a continuous
  homotopy through invertible equivariant maps between two smooth homogeneous symbols can be
  approximated, after a time change fixing the ends, by a jointly smooth homotopy of equivariant
  elliptic homogeneous symbols with the same endpoints.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, §§5–6, for averaging over a compact group and equivariant symbol homotopies.
-/

public section

noncomputable section

open Set Function Metric MeasureTheory
open scoped ContDiff

namespace TauCeti

namespace HomogeneousSymbol

variable {X E V W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ} {G : Type*} [Group G]

/-! ### Equivariance on the unit sphere -/

section Sphere

variable {ρ : ContRepresentation ℝ G X} {κ : ContRepresentation ℝ G E}
  {σV : ContRepresentation ℂ G V}
  {σW : ContRepresentation ℂ G W}

/-- `τ (h * g)⁻¹` undoes `τ h` up to `τ g⁻¹`. -/
private theorem map_mul_inv_apply {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] (τ : ContRepresentation R G M) (h g : G)
    (x : M) :
    τ (h * g)⁻¹ (τ h x) = τ g⁻¹ x := by
  rw [mul_inv_rev, map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  congr 1
  simpa using τ.apply_inv_apply (g := h⁻¹) (v := x)

/-- `τ (h * g)⁻¹ ∘ τ h = τ g⁻¹`. -/
private theorem map_mul_inv_comp {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] (τ : ContRepresentation R G M) (h g : G) :
    τ (h * g)⁻¹ ∘L τ h = τ g⁻¹ :=
  ContinuousLinearMap.ext fun x ↦ map_mul_inv_apply τ h g x

/-- `τ g ∘ T ∘ τ g⁻¹ = S` when `S ∘ τ g = τ g ∘ T`. -/
private theorem comp_comp_inv_eq {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [AddCommGroup N] [Module R N]
    [TopologicalSpace N] [IsTopologicalAddGroup N] (τ : ContRepresentation R G M)
    (τ' : ContRepresentation R G N) (g : G) {S T : M →L[R] N} (h : S ∘L τ g = τ' g ∘L T) :
    τ' g ∘L T ∘L τ g⁻¹ = S := by
  rw [← ContinuousLinearMap.comp_assoc, ← h, ContinuousLinearMap.comp_assoc, τ.comp_inv_self,
    ContinuousLinearMap.comp_id]

/-- A homogeneous symbol that is equivariant at unit frequencies is equivariant at all
frequencies, by homogeneity. -/
private theorem coefficient_comp_eq_of_norm_eq_one (a : HomogeneousSymbol X E V W m)
    (h : ∀ g x ξ, ‖ξ‖ = 1 → a.coefficient (ρ g x, κ g ξ) ∘L σV g = σW g ∘L a.coefficient (x, ξ))
    (g : G) (x : X) (ξ : E) :
    a.coefficient (ρ g x, κ g ξ) ∘L σV g = σW g ∘L a.coefficient (x, ξ) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [a.zero_covector]
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set u : E := ‖ξ‖⁻¹ • ξ
  have hu : ‖u‖ = 1 := by simpa using norm_smul_inv_norm (𝕜 := ℝ) hξ
  have hξu : ξ = ‖ξ‖ • u := by simp [u, smul_smul, hn.ne']
  rw [hξu, map_smul, a.homogeneous _ _ _ hn, a.homogeneous _ _ _ hn,
    ContinuousLinearMap.smul_comp, h g x u hu, ContinuousLinearMap.comp_smul]

end Sphere

/-! ### Averaging a smooth family over a compact group -/

section Conjugates

variable [TopologicalSpace G] [IsTopologicalGroup G] {ρ : ContRepresentation ℝ G X}
  {κ : ContRepresentation ℝ G E} {σV : ContRepresentation ℂ G V} {σW : ContRepresentation ℂ G W}

/-- The composition `(T, A, S) ↦ T ∘ A ∘ S` of complex-linear maps is smooth over `ℝ`. -/
private theorem contDiff_comp_comp :
    ContDiff ℝ ∞ fun p : (W →L[ℂ] W) × (V →L[ℂ] W) × (V →L[ℂ] V) ↦ p.1 ∘L p.2.1 ∘L p.2.2 :=
  (by fun_prop : ContDiff ℂ ∞ fun p : (W →L[ℂ] W) × (V →L[ℂ] W) × (V →L[ℂ] V) ↦
    p.1 ∘L p.2.1 ∘L p.2.2).restrict_scalars ℝ

/-- The conjugates `σW g ∘ b t (ρ g⁻¹ x, κ g⁻¹ ξ) ∘ σV g⁻¹` of a family of homogeneous symbols
that is jointly smooth in `(t, x, ξ)` at nonzero frequencies, as homogeneous symbols with positions
`(t, x)`. Their jets are jointly continuous in `g` and the position-frequency variables at nonzero
frequencies, and each of their values is continuous in `g`. -/
private theorem exists_conjugates (hρ : Continuous ρ) (hκ : Continuous κ)
    (hκ_norm : ∀ g ξ, ‖κ g ξ‖ = ‖ξ‖) (hσV : Continuous σV) (hσW : Continuous σW)
    (b : ℝ → HomogeneousSymbol X E V W m)
    (hb : ContDiffOn ℝ ∞ (fun p : ℝ × X × E ↦ (b p.1).coefficient p.2) {p | p.2.2 ≠ 0}) :
    ∃ M : G → HomogeneousSymbol (ℝ × X) E V W m,
      (∀ g t x ξ, (M g).coefficient ((t, x), ξ) =
        σW g ∘L (b t).coefficient (ρ g⁻¹ x, κ g⁻¹ ξ) ∘L σV g⁻¹) ∧
      (∀ k : ℕ, ContinuousOn
        (fun p : G × ((ℝ × X) × E) ↦ iteratedFDeriv ℝ k (M p.1).coefficient p.2)
        (univ ×ˢ {p | p.2 ≠ 0})) ∧
      ∀ q, Continuous fun g ↦ (M g).coefficient q := by
  -- The conjugate by `g` is a smooth function `F` of `(t, x, ξ)` and of the operators
  -- `θ g = (ρ g⁻¹, κ g⁻¹, σW g, σV g⁻¹)`.
  let θ : G → (X →L[ℝ] X) × (E →L[ℝ] E) × (W →L[ℂ] W) × (V →L[ℂ] V) :=
    fun g ↦ (ρ g⁻¹, κ g⁻¹, σW g, σV g⁻¹)
  have hθ : Continuous θ := (hρ.comp continuous_inv).prodMk
    ((hκ.comp continuous_inv).prodMk (hσW.prodMk (hσV.comp continuous_inv)))
  let F : ((ℝ × X) × E) × ((X →L[ℝ] X) × (E →L[ℝ] E) × (W →L[ℂ] W) × (V →L[ℂ] V)) →
      V →L[ℂ] W :=
    fun w ↦ w.2.2.2.1 ∘L (b w.1.1.1).coefficient (w.2.1 w.1.1.2, w.2.2.1 w.1.2) ∘L w.2.2.2.2
  let S : Set (((ℝ × X) × E) × ((X →L[ℝ] X) × (E →L[ℝ] E) × (W →L[ℂ] W) × (V →L[ℂ] V))) :=
    {w | w.2.2.1 w.1.2 ≠ 0}
  have hS : IsOpen S := isOpen_ne_fun (by fun_prop) continuous_const
  have hF : ContDiffOn ℝ ∞ F S := by
    have hcoeff : ContDiffOn ℝ ∞ (fun w : ((ℝ × X) × E) ×
        ((X →L[ℝ] X) × (E →L[ℝ] E) × (W →L[ℂ] W) × (V →L[ℂ] V)) ↦
          (b w.1.1.1).coefficient (w.2.1 w.1.1.2, w.2.2.1 w.1.2)) S :=
      hb.comp (by fun_prop : ContDiff ℝ ∞ fun w : ((ℝ × X) × E) ×
        ((X →L[ℝ] X) × (E →L[ℝ] E) × (W →L[ℂ] W) × (V →L[ℂ] V)) ↦
          (w.1.1.1, w.2.1 w.1.1.2, w.2.2.1 w.1.2)).contDiffOn fun _ hw ↦ hw
    exact contDiff_comp_comp.comp_contDiffOn
      (contDiff_snd.snd.snd.fst.contDiffOn.prodMk
        (hcoeff.prodMk contDiff_snd.snd.snd.snd.contDiffOn))
  have hθS (g : G) (q : (ℝ × X) × E) (hq : q.2 ≠ 0) : (q, θ g) ∈ S := by
    change κ g⁻¹ q.2 ≠ 0
    rw [← norm_ne_zero_iff, hκ_norm]
    exact norm_ne_zero_iff.2 hq
  refine ⟨fun g ↦
    { coefficient := fun q ↦ F (q, θ g)
      zero_covector := fun y ↦ by simp [F, θ, (b _).zero_covector]
      contDiffOn_coefficient := hF.comp (by fun_prop : ContDiff ℝ ∞ fun q : (ℝ × X) × E ↦
        (q, θ g)).contDiffOn fun q hq ↦ hθS g q hq
      homogeneous := fun y ξ t ht ↦ by
        simp [F, θ, (b _).homogeneous _ _ t ht, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul] },
    fun g t x ξ ↦ rfl, fun k ↦ ?_, fun q ↦ ?_⟩
  · exact (hF.continuousOn_iteratedFDeriv_partial hS (mod_cast le_top)).comp
      (continuous_snd.prodMk (hθ.comp continuous_fst)).continuousOn fun p hp ↦ hθS p.1 p.2 hp.2
  · rcases eq_or_ne q.2 0 with hq | hq
    · refine (continuous_const (y := (0 : V →L[ℂ] W))).congr fun g ↦ ?_
      obtain ⟨⟨t, x⟩, ξ⟩ := q
      simp only at hq
      subst hq
      simp [F, θ, (b t).zero_covector]
    · exact hF.continuousOn.comp_continuous (continuous_const.prodMk hθ) fun g ↦ hθS g q hq

end Conjugates

section Average

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] {ρ : ContRepresentation ℝ G X} {κ : ContRepresentation ℝ G E}
  {σV : ContRepresentation ℂ G V}
  {σW : ContRepresentation ℂ G W}

/-- The average over the normalized Haar measure of a smooth family of homogeneous symbols. If
`(t, x, ξ) ↦ b t (x, ξ)` is jointly smooth at nonzero frequencies, so is the family of averages
`b' t (x, ξ) = ∫ σW g ∘ b t (ρ g⁻¹ x, κ g⁻¹ ξ) ∘ σV g⁻¹ dμ(g)`, the integrand is integrable, and
every `b' t` is equivariant, by left invariance of `μ`. -/
private theorem exists_average [CompleteSpace W] (hρ : Continuous ρ) (hκ : Continuous κ)
    (hκ_norm : ∀ g ξ, ‖κ g ξ‖ = ‖ξ‖) (hσV : Continuous σV) (hσW : Continuous σW)
    (b : ℝ → HomogeneousSymbol X E V W m)
    (hb : ContDiffOn ℝ ∞ (fun p : ℝ × X × E ↦ (b p.1).coefficient p.2) {p | p.2.2 ≠ 0}) :
    ∃ b' : ℝ → HomogeneousSymbol X E V W m,
      ContDiffOn ℝ ∞ (fun p : ℝ × X × E ↦ (b' p.1).coefficient p.2) {p | p.2.2 ≠ 0} ∧
      (∀ t x ξ, (b' t).coefficient (x, ξ) =
        ∫ g, σW g ∘L (b t).coefficient (ρ g⁻¹ x, κ g⁻¹ ξ) ∘L σV g⁻¹ ∂haarProb G) ∧
      (∀ t x ξ, Integrable
        (fun g ↦ σW g ∘L (b t).coefficient (ρ g⁻¹ x, κ g⁻¹ ξ) ∘L σV g⁻¹) (haarProb G)) ∧
      ∀ t g x ξ, (b' t).coefficient (ρ g x, κ g ξ) ∘L σV g = σW g ∘L (b' t).coefficient (x, ξ) := by
  obtain ⟨M, hM, hjets, hMcont⟩ := exists_conjugates hρ hκ hκ_norm hσV hσW b hb
  let B := integral (haarProb G) M hjets
  have hB (t : ℝ) (x : X) (ξ : E) : B.coefficient ((t, x), ξ) =
      ∫ g, σW g ∘L (b t).coefficient (ρ g⁻¹ x, κ g⁻¹ ξ) ∘L σV g⁻¹ ∂haarProb G := by
    simp only [B, coefficient_integral, hM]
  have hint (t : ℝ) (x : X) (ξ : E) : Integrable
      (fun g ↦ σW g ∘L (b t).coefficient (ρ g⁻¹ x, κ g⁻¹ ξ) ∘L σV g⁻¹) (haarProb G) := by
    simpa only [hM] using (hMcont ((t, x), ξ)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨fun t ↦ B.compPosition (fun x ↦ (t, x)) (contDiff_const.prodMk contDiff_id), ?_,
    fun t x ξ ↦ by simpa using hB t x ξ, hint, fun t h x ξ ↦ ?_⟩
  · refine (B.contDiffOn_coefficient.comp_continuousLinearMap
      (ContinuousLinearEquiv.prodAssoc ℝ ℝ X E).symm.toContinuousLinearMap).congr ?_
    rintro ⟨t, x, ξ⟩ -
    simp [ContinuousLinearEquiv.prodAssoc_symm_apply]
  -- Equivariance: substitute `g ↦ h * g` in the integral, by left invariance of `μ`.
  simp only [coefficient_compPosition, hB]
  have h₁ := ((ContinuousLinearMap.compL ℂ V V W).flip (σV h)).integral_comp_comm
    (hint t (ρ h x) (κ h ξ))
  have h₂ := (ContinuousLinearMap.compL ℂ V W W (σW h)).integral_comp_comm (hint t x ξ)
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply] at h₁ h₂
  rw [← h₁, ← h₂, ← integral_mul_left_eq_self _ h]
  congr 1
  funext g
  simp only [map_mul_inv_apply, map_mul, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc, map_mul_inv_comp]

/-- The average of an equivariant homogeneous symbol is the symbol itself. -/
private theorem eq_of_coefficient_eq_average [CompleteSpace W] {b' e : HomogeneousSymbol X E V W m}
    (hb' : ∀ x ξ, b'.coefficient (x, ξ) =
      ∫ g, σW g ∘L e.coefficient (ρ g⁻¹ x, κ g⁻¹ ξ) ∘L σV g⁻¹ ∂haarProb G)
    (he : ∀ g x ξ, e.coefficient (ρ g x, κ g ξ) ∘L σV g = σW g ∘L e.coefficient (x, ξ)) :
    b' = e := by
  refine ext_of_ne_zero fun x ξ _ ↦ ?_
  have hg (g : G) :
      σW g ∘L e.coefficient (ρ g⁻¹ x, κ g⁻¹ ξ) ∘L σV g⁻¹ = e.coefficient (x, ξ) := by
    have h := he g (ρ g⁻¹ x) (κ g⁻¹ ξ)
    rw [ρ.apply_inv_apply, κ.apply_inv_apply] at h
    exact comp_comp_inv_eq σV σW g h
  simp [hb', hg]

/-- At a point `(x, ξ)`, the average `b'` of `b` is within `C` of `A (x, ξ)` if `A` is
equivariant along the orbit of `(x, ξ)`, `b` is within `C` of `A` on that orbit, and the actions
on `V` and `W` are contractions. -/
private theorem dist_le_of_coefficient_eq_average [CompleteSpace W] (hσV_norm : ∀ g, ‖σV g‖ ≤ 1)
    (hσW_norm : ∀ g, ‖σW g‖ ≤ 1) {b b' : HomogeneousSymbol X E V W m}
    {A : X × E → V →L[ℂ] W} {x : X} {ξ : E} {C : ℝ}
    (hb' : b'.coefficient (x, ξ) =
      ∫ g, σW g ∘L b.coefficient (ρ g⁻¹ x, κ g⁻¹ ξ) ∘L σV g⁻¹ ∂haarProb G)
    (hint : Integrable (fun g ↦ σW g ∘L b.coefficient (ρ g⁻¹ x, κ g⁻¹ ξ) ∘L σV g⁻¹) (haarProb G))
    (hA : ∀ g, A (x, ξ) = σW g ∘L A (ρ g⁻¹ x, κ g⁻¹ ξ) ∘L σV g⁻¹)
    (hC : ∀ g, dist (b.coefficient (ρ g⁻¹ x, κ g⁻¹ ξ)) (A (ρ g⁻¹ x, κ g⁻¹ ξ)) ≤ C) :
    dist (b'.coefficient (x, ξ)) (A (x, ξ)) ≤ C := by
  have hconst : ∫ _ : G, A (x, ξ) ∂haarProb G = A (x, ξ) := by simp
  rw [dist_eq_norm, hb', ← hconst, ← integral_sub hint (integrable_const _)]
  refine (norm_integral_le_of_norm_le_const (ae_of_all _ fun g ↦ ?_)).trans_eq
    (by rw [probReal_univ, mul_one])
  rw [hA g, ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
  calc ‖σW g ∘L (b.coefficient (ρ g⁻¹ x, κ g⁻¹ ξ) - A (ρ g⁻¹ x, κ g⁻¹ ξ)) ∘L σV g⁻¹‖
      ≤ ‖σW g‖ * (‖b.coefficient (ρ g⁻¹ x, κ g⁻¹ ξ) - A (ρ g⁻¹ x, κ g⁻¹ ξ)‖ * ‖σV g⁻¹‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖b.coefficient (ρ g⁻¹ x, κ g⁻¹ ξ) - A (ρ g⁻¹ x, κ g⁻¹ ξ)‖ * 1) := by
        gcongr
        exacts [hσW_norm g, hσV_norm g⁻¹]
    _ ≤ C := by
        rw [one_mul, mul_one, ← dist_eq_norm]
        exact hC g

end Average

/-! ### An invariant margin of invertibility -/

section Margin

variable [TopologicalSpace G] [CompactSpace G] {ρ : ContRepresentation ℝ G X}

/-- A margin of invertibility of a continuous family `a s`, `s ∈ [0, 1]`, of invertible maps on
the unit sphere, depending continuously on the position, positive, and invariant under `ρ`: the
least margin of invertibility of `a s (ρ g x, u)` over `g`, `s` and unit frequencies `u`. -/
private theorem exists_invariant_margin [FiniteDimensional ℝ E] [CompleteSpace V]
    (hρ : Continuous ρ) {a : ℝ → X × E → V →L[ℂ] W}
    (ha : ContinuousOn (uncurry a) (Icc 0 1 ×ˢ {q : X × E | ‖q.2‖ = 1}))
    (ha_inv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ξ, ‖ξ‖ = 1 → (a t (x, ξ)).IsInvertible) :
    ∃ c : X → ℝ, Continuous c ∧ (∀ x, 0 < c x) ∧ (∀ g x, c (ρ g x) = c x) ∧
      ∀ x, ∀ s ∈ Icc (0 : ℝ) 1, ∀ u : E, ‖u‖ = 1 → ∀ T : V →L[ℂ] W,
        dist T (a s (x, u)) < c x → T.IsInvertible := by
  classical
  obtain ⟨r, hr_cont, hr_nonneg, hr_pos, hr_ball⟩ :=
    ContinuousLinearMap.isOpen_setOfPred_isInvertible.exists_continuous_forall_dist_lt
      (continuous_id (X := V →L[ℂ] W))
  let f : X → G × Icc (0 : ℝ) 1 × sphere (0 : E) 1 → ℝ :=
    fun x k ↦ r (a k.2.1 (ρ k.1 x, k.2.2))
  have hf : Continuous (uncurry f) := hr_cont.comp <| ha.comp_continuous
    (by fun_prop : Continuous fun p : X × G × Icc (0 : ℝ) 1 × sphere (0 : E) 1 ↦
      ((p.2.2.1 : ℝ), ρ p.2.1 p.1, (p.2.2.2 : E)))
    fun p ↦ ⟨p.2.2.1.2, by simp⟩
  -- Without unit frequencies no margin is needed, and `c = 1`.
  let c : X → ℝ := fun x ↦ if Nonempty (sphere (0 : E) 1) then sInf (f x '' univ) else 1
  refine ⟨c, ?_, fun x ↦ ?_, fun g x ↦ ?_, fun x s hs u hu T hT ↦ hr_ball _ _ (hT.trans_le ?_)⟩
  · by_cases hE : Nonempty (sphere (0 : E) 1)
    · simpa only [c, hE, ↓reduceIte] using isCompact_univ.continuous_sInf (f := f) hf
    · simpa only [c, hE, ↓reduceIte] using continuous_const
  · by_cases hE : Nonempty (sphere (0 : E) 1)
    · simp only [c, hE, ↓reduceIte]
      obtain ⟨k, -, hk⟩ := (isCompact_univ.image (f := f x)
        (hf.comp (Continuous.prodMk_right x))).sInf_mem (univ_nonempty.image _)
      rw [← hk]
      exact hr_pos _ (ha_inv _ k.2.1.2 _ _ (by simp))
    · simp only [c, hE, ↓reduceIte, zero_lt_one]
  · by_cases hE : Nonempty (sphere (0 : E) 1)
    · simp only [c, hE, ↓reduceIte, image_univ]
      have hfg : f (ρ g x) = f x ∘ fun k ↦ (k.1 * g, k.2) := by
        funext k
        simp [f]
      rw [hfg, (Function.RightInverse.surjective (g := fun k ↦ (k.1 * g⁻¹, k.2))
        fun k ↦ by simp).range_comp]
    · simp only [c, hE, ↓reduceIte]
  · have hE : Nonempty (sphere (0 : E) 1) := ⟨⟨u, by simpa using hu⟩⟩
    simp only [c, hE, ↓reduceIte]
    refine csInf_le (s := f x '' univ) ⟨0, ?_⟩
      ⟨(1, ⟨s, hs⟩, ⟨u, by simpa using hu⟩), mem_univ _, by simp [f]⟩
    rintro _ ⟨k, -, rfl⟩
    exact hr_nonneg _

end Margin

/-! ### Smooth equivariant homotopies -/

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ρ : ContRepresentation ℝ G X} {κ : ContRepresentation ℝ G E} {σV : ContRepresentation ℂ G V}
  {σW : ContRepresentation ℂ G W}

/-- **Smoothing an equivariant homotopy of elliptic symbols.** Let a compact group `G` act, by
representations continuous in the operator norm, through linear maps `ρ g` on positions,
norm-preserving linear maps `κ g` on frequencies and contractions `σV g`, `σW g` on the coefficient
spaces. Let `a t`, `t ∈ [0, 1]`, be maps that
depend continuously on `(t, x, ξ)`, are invertible and equivariant on the unit sphere of
frequencies, `a t (ρ g x, κ g ξ) ∘ σV g = σW g ∘ a t (x, ξ)`, and join two homogeneous symbols
`a₀` and `a₁` of degree `m` there. Let `δ` be a continuous positive precision invariant under the
action. Then there are a continuous time change `σ : ℝ → [0, 1]`, equal to `0` for `t ≤ 0` and to
`1` for `1 ≤ t`, and equivariant elliptic homogeneous symbols `b t` of degree `m` for all `t`, with
`b t = a₀` for `t ≤ 0` and `b t = a₁` for `1 ≤ t`, whose coefficient is jointly smooth in
`(t, x, ξ)` at nonzero frequencies and is within `δ (t, x, ξ)` of `a (σ t) (x, ξ)` on the unit
sphere.

The endpoints `a₀` and `a₁` are equivariant, since `a 0` and `a 1` are; this is not assumed. -/
theorem exists_contDiffOn_isElliptic_equivariant_homotopy [FiniteDimensional ℝ X]
    [FiniteDimensional ℝ E] [CompleteSpace V] [CompleteSpace W] (hρ : Continuous ρ)
    (hκ : Continuous κ) (hκ_norm : ∀ g ξ, ‖κ g ξ‖ = ‖ξ‖) (hσV : Continuous σV)
    (hσV_norm : ∀ g, ‖σV g‖ ≤ 1) (hσW : Continuous σW) (hσW_norm : ∀ g, ‖σW g‖ ≤ 1)
    (a₀ a₁ : HomogeneousSymbol X E V W m) {a : ℝ → X × E → V →L[ℂ] W}
    (ha : ContinuousOn (uncurry a) (Icc 0 1 ×ˢ {q : X × E | ‖q.2‖ = 1}))
    (ha_inv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ξ, ‖ξ‖ = 1 → (a t (x, ξ)).IsInvertible)
    (ha_equivariant : ∀ g, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ξ, ‖ξ‖ = 1 →
      a t (ρ g x, κ g ξ) ∘L σV g = σW g ∘L a t (x, ξ))
    (ha₀ : ∀ x ξ, ‖ξ‖ = 1 → a 0 (x, ξ) = a₀.coefficient (x, ξ))
    (ha₁ : ∀ x ξ, ‖ξ‖ = 1 → a 1 (x, ξ) = a₁.coefficient (x, ξ)) {δ : ℝ × X × E → ℝ}
    (hδ : Continuous δ) (hδ_pos : ∀ p, 0 < δ p)
    (hδ_invariant : ∀ g t x ξ, δ (t, ρ g x, κ g ξ) = δ (t, x, ξ)) :
    ∃ (σ : ℝ → ℝ) (b : ℝ → HomogeneousSymbol X E V W m),
      Continuous σ ∧ (∀ t, σ t ∈ Icc (0 : ℝ) 1) ∧ (∀ t ≤ 0, σ t = 0) ∧ (∀ t, 1 ≤ t → σ t = 1) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × X × E ↦ (b p.1).coefficient p.2) {p | p.2.2 ≠ 0} ∧
      (∀ t, (b t).IsElliptic) ∧ (∀ t ≤ 0, b t = a₀) ∧ (∀ t, 1 ≤ t → b t = a₁) ∧
      (∀ t g x ξ, (b t).coefficient (ρ g x, κ g ξ) ∘L σV g = σW g ∘L (b t).coefficient (x, ξ)) ∧
      ∀ t x ξ, ‖ξ‖ = 1 → dist ((b t).coefficient (x, ξ)) (a (σ t) (x, ξ)) < δ (t, x, ξ) := by
  borelize G
  obtain ⟨c, hc, hc_pos, hc_invariant, hc_inv⟩ := exists_invariant_margin hρ ha ha_inv
  -- Smooth the homotopy within half of the invariant precision `min δ c`, then average it.
  obtain ⟨σ, b, hσ_cont, hσ_mem, hσ₀, hσ₁, hb, -, hb₀, hb₁, hb_close⟩ :=
    exists_contDiffOn_isElliptic_homotopy a₀ a₁ ha ha_inv ha₀ ha₁
      (δ := fun p ↦ min (δ p) (c p.2.1) / 2) (by fun_prop)
      fun p ↦ half_pos (lt_min (hδ_pos p) (hc_pos p.2.1))
  obtain ⟨b', hb', hb'_coeff, hb'_int, hb'_equivariant⟩ :=
    exists_average hρ hκ hκ_norm hσV hσW b hb
  -- The endpoints are equivariant, hence fixed by the average.
  have hendpoint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (e : HomogeneousSymbol X E V W m)
      (hse : ∀ x ξ, ‖ξ‖ = 1 → a s (x, ξ) = e.coefficient (x, ξ)) (t : ℝ) (ht : b t = e) :
      b' t = e :=
    eq_of_coefficient_eq_average (fun x ξ ↦ by rw [hb'_coeff, ht])
      (coefficient_comp_eq_of_norm_eq_one e fun g x ξ hξ ↦ by
        rw [← hse _ _ hξ, ← hse _ _ ((hκ_norm g ξ).trans hξ)]
        exact ha_equivariant g s hs x ξ hξ)
  -- On the unit sphere the average stays within half of `min δ c` of `a (σ t)`.
  have hclose (t : ℝ) (x : X) (ξ : E) (hξ : ‖ξ‖ = 1) :
      dist ((b' t).coefficient (x, ξ)) (a (σ t) (x, ξ)) ≤ min (δ (t, x, ξ)) (c x) / 2 := by
    have hη (g : G) : ‖κ g⁻¹ ξ‖ = 1 := by rw [hκ_norm, hξ]
    refine dist_le_of_coefficient_eq_average hσV_norm hσW_norm (hb'_coeff t x ξ) (hb'_int t x ξ)
      (fun g ↦ ?_) fun g ↦ ?_
    · have h := ha_equivariant g (σ t) (hσ_mem t) (ρ g⁻¹ x) (κ g⁻¹ ξ) (hη g)
      rw [ρ.apply_inv_apply, κ.apply_inv_apply] at h
      exact (comp_comp_inv_eq σV σW g h).symm
    · simpa only [hδ_invariant, hc_invariant] using (hb_close t (ρ g⁻¹ x) (κ g⁻¹ ξ) (hη g)).le
  refine ⟨σ, b', hσ_cont, hσ_mem, hσ₀, hσ₁, hb', fun t ↦ ?_,
    fun t ht ↦ hendpoint 0 ⟨le_rfl, zero_le_one⟩ a₀ ha₀ t (hb₀ t ht),
    fun t ht ↦ hendpoint 1 ⟨zero_le_one, le_rfl⟩ a₁ ha₁ t (hb₁ t ht),
    hb'_equivariant, fun t x ξ hξ ↦ (hclose t x ξ hξ).trans_lt ?_⟩
  · rw [← ofSphere_coefficient (b' t), isElliptic_ofSphere_iff]
    exact fun x ξ hξ ↦ hc_inv x (σ t) (hσ_mem t) ξ hξ _ ((hclose t x ξ hξ).trans_lt
      (by linarith [hc_pos x, min_le_right (δ (t, x, ξ)) (c x)]))
  · linarith [hδ_pos (t, x, ξ), min_le_left (δ (t, x, ξ)) (c x)]

end HomogeneousSymbol

end TauCeti

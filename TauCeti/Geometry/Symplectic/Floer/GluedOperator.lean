/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Pregluing
public import TauCeti.Geometry.Symplectic.Floer.Splicing
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.ODE.Regularity

/-!
# The formal adjoint along pre-glued Floer cylinders

Let `(V, ω)` be a symplectic vector space, `H_t` a Hamiltonian and `J_t(y)` a family of
endomorphisms, both of period one in `t`, and let `x` be a one-periodic orbit of `X_{H_t}`. Two
Floer cylinders `u` and `v` for the cylindrical datum `K = H_t dt`, with `u` converging to `x` as
`s → +∞` and `v` as `s → -∞`, pre-glue to the maps `w_R = TauCeti.Floer.preglue x u v R`, equal to
`u(· + R, ·)` for `s ≤ -1` and to `v(· - R, ·)` for `s ≥ 1`. The gluing theorem corrects `w_R` to a
solution by a Newton iteration, which needs a right inverse of the linearized operator `D_{w_R}`
bounded **uniformly in `R`**. Its analytic input is an injectivity estimate
`‖η‖²_{W^{1,2}} ≤ C' ‖D_{w_R}^* η‖²_{L²}` for the formal adjoint
(`TauCeti.SymplecticForm.floerLinearizationAdjoint`) with `C'` independent of `R`; the Sobolev
completion and the right inverse built from it are not treated here.

This file proves that estimate. If the formal adjoints along `u` and `v` satisfy the injectivity
estimate with the constant `C`, the situation of regular trajectories, where `D_u` and `D_v` are
onto, then for every large `R` the formal adjoint along `w_R` satisfies it with the constant `64 C`
(`eventually_setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_preglue`).
The maps `u` and `v` are assumed to converge to `x` uniformly in `t`, together with their
`t`-derivatives; no rate of convergence is needed.

The proof applies the abstract splicing estimate
`setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_of_splice` to `D_{w_R}^*`
and the translates `D_{u(· + R)}^*` and `D_{v(· - R)}^*`, which satisfy the estimate with the
same constant (`setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_comp_add_right`).
It remains to check that the coefficients `J(z, w_R z)` and `A = ∂t J - C` of
`D_{w_R}^* η = -(∂s η + (∂t η) ∘ J + η ∘ A)` are close to those of the translates on the two
half-cylinders `s ≤ T` and `s ≥ -T`, for the fixed `T` that the splicing estimate requires.

* For the cylindrical datum, these coefficients at `z = (s, t)` are a continuous function of `t`,
  of the value `m z` of the map and of its `t`-derivative `∂t m z`, of period one in `t`. By
  uniform continuity near the compact orbit, they are uniformly close to their values along the
  stationary cylinder over `x` whenever `m z` is close to `x(t)` and `∂t m z` to `x'(t)`.
* Off the neck, `w_R` agrees with the translates near `z`, so the coefficients coincide.
* On the strip `|s| ≤ T` around the neck, for large `R`, all three maps are close to `x` with
  their `t`-derivatives (`TauCeti.Floer.norm_preglue_sub_le`,
  `TauCeti.Floer.norm_fderiv_preglue_apply_sub_le`), so the coefficients are close to those of the
  stationary cylinder, hence to each other.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 10.5,
  on the uniformly bounded right inverses of glued Cauchy–Riemann operators.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Section 2.5, on gluing Floer trajectories.
-/

public section

open Filter Set Topology Function ContinuousLinearMap Metric

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ}

/-- The two coefficients `(J, A)` of the formal adjoint `-(∂s η + (∂t η) ∘ J + η ∘ A)` along a map
`m` at `z`, for the cylindrical datum `(J_t, H_t dt)`: `J = J_t(m z)` and `A = ∂t J - C`, with
`∂t J` the `t`-derivative of `w ↦ J_{w.2}(m w)` and `C` the zeroth-order part of the linearized
operator. -/
private noncomputable def adjointCoeffs (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (m : ℝ × ℝ → V) (z : ℝ × ℝ) : (V →L[ℝ] V) × (V →L[ℝ] V) :=
  (J z.2 (m z), fderiv ℝ (fun w ↦ J w.2 (m w)) z stdComplexLineImag -
    ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) m z)

/-- The coefficients `(J, A)` of `adjointCoeffs` as a function of the time `t`, the value `y` of the
map and its `t`-derivative `η`. -/
private noncomputable def adjointJet (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (q : ℝ × V × V) : (V →L[ℝ] V) × (V →L[ℝ] V) :=
  (J q.1 q.2.1, fderiv ℝ (uncurry J) (q.1, q.2.1) (1, q.2.2) -
    ((fderiv ℝ (J q.1) q.2.1).flip (q.2.2 - ω.hamiltonianVectorField (H q.1) q.2.1) -
      (J q.1 q.2.1).comp (fderiv ℝ (ω.hamiltonianVectorField (H q.1)) q.2.1)))

/-- The coefficients of the formal adjoint along `m` at `z` depend only on `t`, `m z` and
`∂t m z`. -/
private theorem adjointCoeffs_eq (hJ : Differentiable ℝ (uncurry J)) {m : ℝ × ℝ → V}
    {z : ℝ × ℝ} (hm : DifferentiableAt ℝ m z) :
    adjointCoeffs ω J H m z = adjointJet ω J H (z.2, m z, fderiv ℝ m z stdComplexLineImag) := by
  have hc := (hJ (z.2, m z)).hasFDerivAt.comp z (hasFDerivAt_snd.prodMk hm.hasFDerivAt)
  rw [adjointCoeffs, adjointJet,
    show (fun w : ℝ × ℝ ↦ J w.2 (m w)) = uncurry J ∘ fun w ↦ (w.2, m w) from rfl, hc.fderiv]
  ext1
  · rfl
  · ext y
    simp [floerLinearizationCoeff_apply, stdComplexLineImag]

/-- Germs of maps that agree at `z` have the same adjoint coefficients there. -/
private theorem adjointCoeffs_congr {m₁ m₂ : ℝ × ℝ → V} {z : ℝ × ℝ} (h : m₁ =ᶠ[𝓝 z] m₂) :
    adjointCoeffs ω J H m₁ z = adjointCoeffs ω J H m₂ z := by
  have hJm : (fun w : ℝ × ℝ ↦ J w.2 (m₁ w)) =ᶠ[𝓝 z] fun w ↦ J w.2 (m₂ w) :=
    h.mono fun w hw ↦ by simp only [hw]
  have hC : ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) m₁ z =
      ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) m₂ z := by
    ext y
    simp only [floerLinearizationCoeff_apply, h.eq_of_nhds, h.fderiv_eq]
  simp only [adjointCoeffs, hC, h.eq_of_nhds, hJm.fderiv_eq]

/-- The adjoint jet of `C¹` almost complex data and a `C²` Hamiltonian is continuous. -/
private theorem continuous_adjointJet (hJ : ContDiff ℝ 1 (uncurry J))
    (hH : ContDiff ℝ 2 (uncurry H)) : Continuous (adjointJet ω J H) := by
  have hX : ContDiff ℝ 1 fun w : ℝ × V ↦ ω.hamiltonianVectorField (H w.1) w.2 :=
    ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH
  have hty : Continuous fun q : ℝ × V × V ↦ (q.1, q.2.1) := continuous_fst.prodMk continuous_snd.fst
  have hJc : Continuous fun q : ℝ × V × V ↦ J q.1 q.2.1 := hJ.continuous.comp hty
  have hXc : Continuous fun q : ℝ × V × V ↦ ω.hamiltonianVectorField (H q.1) q.2.1 :=
    hX.continuous.comp hty
  have hdJ : Continuous fun q : ℝ × V × V ↦ fderiv ℝ (uncurry J) (q.1, q.2.1) :=
    (hJ.continuous_fderiv one_ne_zero).comp hty
  have hdJy : Continuous fun q : ℝ × V × V ↦ fderiv ℝ (J q.1) q.2.1 :=
    (ContDiff.fderiv (f := fun (q : ℝ × V × V) (y : V) ↦ J q.1 y)
      (hJ.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd.fst (n := 0)
      (by simp)).continuous
  have hdX : Continuous fun q : ℝ × V × V ↦ fderiv ℝ (ω.hamiltonianVectorField (H q.1)) q.2.1 :=
    (ContDiff.fderiv (f := fun (q : ℝ × V × V) (y : V) ↦ ω.hamiltonianVectorField (H q.1) y)
      (hX.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd.fst (n := 0)
      (by simp)).continuous
  have hflip : Continuous fun q : ℝ × V × V ↦ (fderiv ℝ (J q.1) q.2.1).flip :=
    (flipₗᵢ ℝ V V V).continuous.comp hdJy
  exact hJc.prodMk ((hdJ.clm_apply (continuous_const.prodMk continuous_snd.snd)).sub
    ((hflip.clm_apply (continuous_snd.snd.sub hXc)).sub (hJc.clm_comp hdX)))

/-- The adjoint jet is unchanged by an integer shift of time, for data of period one. -/
private theorem adjointJet_sub_intCast (hJp : Periodic J 1) (hHp : Periodic H 1) (n : ℤ)
    (q : ℝ × V × V) : adjointJet ω J H (q.1 - n, q.2) = adjointJet ω J H q := by
  have hJn : J (q.1 - n) = J q.1 := by simpa using hJp.sub_int_mul_eq (x := q.1) n
  have hHn : H (q.1 - n) = H q.1 := by simpa using hHp.sub_int_mul_eq (x := q.1) n
  have hJs : (fun p : ℝ × V ↦ uncurry J (p + (-(n : ℝ), 0))) = uncurry J := funext fun p ↦ by
    simpa [uncurry, ← sub_eq_add_neg] using congrFun (hJp.sub_int_mul_eq (x := p.1) n) p.2
  have hdJ : fderiv ℝ (uncurry J) (q.1 - n, q.2.1) = fderiv ℝ (uncurry J) (q.1, q.2.1) := by
    rw [show ((q.1 - n, q.2.1) : ℝ × V) = (q.1, q.2.1) + (-(n : ℝ), 0) by
      ext <;> simp [sub_eq_add_neg], ← fderiv_comp_add_right, hJs]
  simp only [adjointJet, hJn, hHn, hdJ]

/-- **Uniform continuity of the adjoint jet near the orbit.** For data of period one and a loop
`x` of period one, the adjoint jet at `(t, y, η)` is within `ε` of its value at
`(t, x(t), X_{H_t}(x t))` whenever `y` is within `δ` of `x(t)` and `η` of `X_{H_t}(x t)`. -/
private theorem exists_pos_forall_dist_adjointJet_lt (hJ : ContDiff ℝ 1 (uncurry J))
    (hJp : Periodic J 1) (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : Continuous x) (hxp : Periodic x 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (t : ℝ) (y η : V), ‖y - x t‖ < δ →
      ‖η - ω.hamiltonianVectorField (H t) (x t)‖ < δ →
        dist (adjointJet ω J H (t, y, η))
          (adjointJet ω J H (t, x t, ω.hamiltonianVectorField (H t) (x t))) < ε := by
  set p : ℝ → ℝ × V × V := fun t ↦ (t, x t, ω.hamiltonianVectorField (H t) (x t))
  have hX : Continuous fun w : ℝ × V ↦ ω.hamiltonianVectorField (H w.1) w.2 :=
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH).continuous
  have hp : Continuous p := continuous_id.prodMk (hx.prodMk (hX.comp (continuous_id.prodMk hx)))
  -- The jet is uniformly continuous at the compact set of orbit jets over one period.
  obtain ⟨δ, hδ, hδU⟩ := mem_uniformity_dist.1
    ((isCompact_Icc.image hp).uniformContinuousAt_of_continuousAt (adjointJet ω J H)
      (fun _ _ ↦ (continuous_adjointJet hJ hH).continuousAt) (dist_mem_uniformity hε))
  refine ⟨δ, hδ, fun t y η hy hη ↦ ?_⟩
  -- Reduce `t` to `t₀ = t - ⌊t⌋ ∈ [0, 1)` by periodicity.
  set t₀ := Int.fract t
  have ht₀ : t₀ ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hx₀ : x t₀ = x t := by simpa using hxp.sub_int_mul_eq (x := t) ⌊t⌋
  have hH₀ : H t₀ = H t := by simpa using hHp.sub_int_mul_eq (x := t) ⌊t⌋
  have hj (y' η' : V) : adjointJet ω J H (t₀, y', η') = adjointJet ω J H (t, y', η') :=
    adjointJet_sub_intCast hJp hHp ⌊t⌋ (t, y', η')
  have hd : dist (p t₀) (t₀, y, η) < δ := by
    simp only [p, Prod.dist_eq, dist_self, hx₀, hH₀]
    refine max_lt hδ (max_lt ?_ ?_) <;> rwa [dist_comm, dist_eq_norm]
  have h : dist (adjointJet ω J H (p t₀)) (adjointJet ω J H (t₀, y, η)) < ε :=
    hδU hd ⟨t₀, ht₀, rfl⟩
  rw [dist_comm] at h
  simpa only [p, hx₀, hH₀, hj] using h

/-- Two maps whose values and `t`-derivatives at `z` are within `δ` of those of the stationary
cylinder over `x` have adjoint coefficients within `2 ε` of each other there, for the `δ` of
`exists_pos_forall_dist_adjointJet_lt`. -/
private theorem dist_adjointCoeffs_lt (hJ : Differentiable ℝ (uncurry J)) {x : ℝ → V} {ε δ : ℝ}
    (hjet : ∀ (t : ℝ) (y η : V), ‖y - x t‖ < δ → ‖η - ω.hamiltonianVectorField (H t) (x t)‖ < δ →
      dist (adjointJet ω J H (t, y, η))
        (adjointJet ω J H (t, x t, ω.hamiltonianVectorField (H t) (x t))) < ε)
    {m₁ m₂ : ℝ × ℝ → V} {z : ℝ × ℝ} (hm₁ : DifferentiableAt ℝ m₁ z)
    (hm₂ : DifferentiableAt ℝ m₂ z) (h₁ : ‖m₁ z - x z.2‖ < δ)
    (h₁' : ‖fderiv ℝ m₁ z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (x z.2)‖ < δ)
    (h₂ : ‖m₂ z - x z.2‖ < δ)
    (h₂' : ‖fderiv ℝ m₂ z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (x z.2)‖ < δ) :
    dist (adjointCoeffs ω J H m₁ z) (adjointCoeffs ω J H m₂ z) < 2 * ε := by
  rw [adjointCoeffs_eq hJ hm₁, adjointCoeffs_eq hJ hm₂, two_mul]
  exact (dist_triangle_right _ _ _).trans_lt (add_lt_add (hjet _ _ _ h₁ h₁') (hjet _ _ _ h₂ h₂'))

omit [FiniteDimensional ℝ V] in
/-- **The pieces of the pre-glued map near the neck.** If `u` and `v` converge to `x` as
`s → +∞` and `s → -∞`, uniformly in `t` together with their `t`-derivatives, then for every `T`
and every large `R`, on the strip `|s| ≤ T` the translates `u(· + R, ·)` and `v(· - R, ·)` and the
pre-glued map are within `δ` of `x` with their `t`-derivatives. -/
private theorem eventually_forall_norm_preglue_sub_lt {x x' : ℝ → V} {u v : ℝ × ℝ → V}
    (hx : ∀ t, HasDerivAt x (x' t) t) (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop)
    (hdux : TendstoUniformly (fun s t ↦ fderiv ℝ u (s, t) stdComplexLineImag) x' atTop)
    (hvx : TendstoUniformly (fun s t ↦ v (s, t)) x atBot)
    (hdvx : TendstoUniformly (fun s t ↦ fderiv ℝ v (s, t) stdComplexLineImag) x' atBot)
    {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    ∀ᶠ R in atTop, ∀ z : ℝ × ℝ, |z.1| ≤ T →
      (‖u (z + (R, 0)) - x z.2‖ < δ ∧
        ‖fderiv ℝ u (z + (R, 0)) stdComplexLineImag - x' z.2‖ < δ) ∧
      (‖v (z - (R, 0)) - x z.2‖ < δ ∧
        ‖fderiv ℝ v (z - (R, 0)) stdComplexLineImag - x' z.2‖ < δ) ∧
      (‖preglue x u v R z - x z.2‖ < δ ∧
        ‖fderiv ℝ (preglue x u v R) z stdComplexLineImag - x' z.2‖ < δ) := by
  have hδ₂ : 0 < δ / 2 := half_pos hδ
  obtain ⟨s₁, hs₁⟩ := eventually_atTop.1 ((tendstoUniformly_iff.1 hux _ hδ₂).and
    (tendstoUniformly_iff.1 hdux _ hδ₂))
  obtain ⟨s₂, hs₂⟩ := eventually_atBot.1 ((tendstoUniformly_iff.1 hvx _ hδ₂).and
    (tendstoUniformly_iff.1 hdvx _ hδ₂))
  filter_upwards [eventually_ge_atTop (s₁ + T), eventually_ge_atTop (T - s₂)] with R hR₁ hR₂ z hz
  obtain ⟨hz₁, hz₂⟩ := abs_le.1 hz
  have hzu : z + (R, 0) = (z.1 + R, z.2) := by ext <;> simp
  have hzv : z - (R, 0) = (z.1 - R, z.2) := by ext <;> simp
  obtain ⟨hu₀, hu₁⟩ := hs₁ (z.1 + R) (by linarith)
  obtain ⟨hv₀, hv₁⟩ := hs₂ (z.1 - R) (by linarith)
  have hu₀' : ‖u (z + (R, 0)) - x z.2‖ < δ / 2 := by
    rw [hzu, ← dist_eq_norm, dist_comm]; exact hu₀ z.2
  have hu₁' : ‖fderiv ℝ u (z + (R, 0)) stdComplexLineImag - x' z.2‖ < δ / 2 := by
    rw [hzu, ← dist_eq_norm, dist_comm]; exact hu₁ z.2
  have hv₀' : ‖v (z - (R, 0)) - x z.2‖ < δ / 2 := by
    rw [hzv, ← dist_eq_norm, dist_comm]; exact hv₀ z.2
  have hv₁' : ‖fderiv ℝ v (z - (R, 0)) stdComplexLineImag - x' z.2‖ < δ / 2 := by
    rw [hzv, ← dist_eq_norm, dist_comm]; exact hv₁ z.2
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · linarith [norm_preglue_sub_le (x := x) (u := u) (v := v) (R := R) (z := z)]
  · linarith [norm_fderiv_preglue_apply_sub_le (hx z.2) (hu (z + (R, 0))) (hv (z - (R, 0)))]

/-- **Closeness of the adjoint coefficients along the pre-glued map.** Under the hypotheses of
`eventually_setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_preglue`, for every
`T ≥ 1` and `ε > 0`, eventually in `R` the adjoint coefficients along `w_R` are within `ε` of those
along `u(· + R, ·)` on `s ≤ T`, and of those along `v(· - R, ·)` on `s ≥ -T`. -/
private theorem eventually_dist_adjointCoeffs_preglue_lt (hJ : ContDiff ℝ 1 (uncurry J))
    (hJp : Periodic J 1) (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {u v : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop)
    (hdux : TendstoUniformly (fun s t ↦ fderiv ℝ u (s, t) stdComplexLineImag)
      (fun t ↦ ω.hamiltonianVectorField (H t) (x t)) atTop)
    (hvx : TendstoUniformly (fun s t ↦ v (s, t)) x atBot)
    (hdvx : TendstoUniformly (fun s t ↦ fderiv ℝ v (s, t) stdComplexLineImag)
      (fun t ↦ ω.hamiltonianVectorField (H t) (x t)) atBot)
    {T ε : ℝ} (hT : 1 ≤ T) (hε : 0 < ε) :
    ∀ᶠ R in atTop,
      (∀ z : ℝ × ℝ, z.1 ≤ T → dist (adjointCoeffs ω J H (preglue x u v R) z)
        (adjointCoeffs ω J H (fun p ↦ u (p + (R, 0))) z) < ε) ∧
      (∀ z : ℝ × ℝ, -T ≤ z.1 → dist (adjointCoeffs ω J H (preglue x u v R) z)
        (adjointCoeffs ω J H (fun p ↦ v (p - (R, 0))) z) < ε) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  obtain ⟨δ, hδ, hjet⟩ := exists_pos_forall_dist_adjointJet_lt (ω := ω) hJ hJp hH hHp hxc hxp
    (half_pos hε)
  have hJd : Differentiable ℝ (uncurry J) := hJ.differentiable one_ne_zero
  have hud := hu.differentiable one_ne_zero
  have hvd := hv.differentiable one_ne_zero
  have hxd : ContDiff ℝ 1 x := contDiff_one_of_hasDerivAt
    (X := fun t ↦ ω.hamiltonianVectorField (H t))
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH).continuous hx
  filter_upwards [eventually_forall_norm_preglue_sub_lt hx hud hvd hux hdux hvx hdvx hδ T]
    with R hR
  have hwd : Differentiable ℝ (preglue x u v R) :=
    (contDiff_preglue hxd hu hv).differentiable one_ne_zero
  have hε₂ : 2 * (ε / 2) = ε := by ring
  refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rcases lt_or_ge z.1 (-T) with hzT | hzT
    · rw [adjointCoeffs_congr (preglue_eventuallyEq_of_lt_neg_one (by linarith)), dist_self]
      exact hε
    · obtain ⟨⟨hu₀, hu₁⟩, -, hw₀, hw₁⟩ := hR z (abs_le.2 ⟨hzT, hz⟩)
      rw [← hε₂]
      exact dist_adjointCoeffs_lt hJd hjet (hwd z) ((hud _).comp z (hasFDerivAt_id z |>.add_const
        _ |>.differentiableAt)) hw₀ hw₁ hu₀ (by rwa [fderiv_comp_add_right])
  · rcases le_or_gt z.1 T with hzT | hzT
    · obtain ⟨-, ⟨hv₀, hv₁⟩, hw₀, hw₁⟩ := hR z (abs_le.2 ⟨hz, hzT⟩)
      rw [← hε₂]
      exact dist_adjointCoeffs_lt hJd hjet (hwd z) ((hvd _).comp z (hasFDerivAt_id z |>.sub_const
        _ |>.differentiableAt)) hw₀ hw₁ hv₀ (by rwa [fderiv_comp_sub])
    · rw [adjointCoeffs_congr (preglue_eventuallyEq_of_one_lt (by linarith)), dist_self]
      exact hε

/-- **The uniform estimate for the formal adjoint along pre-glued Floer cylinders.** Let `H` and
`J` be `C²` and `C¹` and of period one in `t`, let `x` be a one-periodic orbit of `X_{H_t}`, and
let `u` and `v` be `C¹` maps converging to `x` as `s → +∞` and `s → -∞` respectively, uniformly in
`t` together with their `t`-derivatives. Suppose that the formal adjoints of the linearized Floer
operators along `u` and `v`, for the cylindrical datum `(J_t, H_t dt)`, satisfy the injectivity
estimate `‖η‖²_{W^{1,2}} ≤ C ‖D^* η‖²_{L²}` on `C²` covector fields of period one in `t` vanishing
outside a strip. Then for every large gluing parameter `R`, the formal adjoint along the pre-glued
map `w_R` satisfies the injectivity estimate with the constant `64 C`, independent of `R`. -/
theorem eventually_setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_preglue
    (hJ : ContDiff ℝ 1 (uncurry J)) (hJp : Periodic J 1) (hH : ContDiff ℝ 2 (uncurry H))
    (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {u v : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop)
    (hdux : TendstoUniformly (fun s t ↦ fderiv ℝ u (s, t) stdComplexLineImag)
      (fun t ↦ ω.hamiltonianVectorField (H t) (x t)) atTop)
    (hvx : TendstoUniformly (fun s t ↦ v (s, t)) x atBot)
    (hdvx : TendstoUniformly (fun s t ↦ fderiv ℝ v (s, t) stdComplexLineImag)
      (fun t ↦ ω.hamiltonianVectorField (H t) (x t)) atBot)
    {C : ℝ} (hC : 0 ≤ C)
    (hestu : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → (∀ s t, η (s, t + 1) = η (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint (fun p ↦ J p.2)
            (fun _ _ ↦ 0) (fun p ↦ H p.2) u η z‖ ^ 2)
    (hestv : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → (∀ s t, η (s, t + 1) = η (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint (fun p ↦ J p.2)
            (fun _ _ ↦ 0) (fun p ↦ H p.2) v η z‖ ^ 2) :
    ∀ᶠ R in atTop, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ s t, η (s, t + 1) = η (s, t)) → ∀ ⦃a b : ℝ⦄, a ≤ b →
        (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          64 * C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint
            (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (preglue x u v R) η z‖ ^ 2 := by
  -- The neck half-length `T` and the closeness `ε` required by the splicing estimate.
  set T : ℝ := 64 * C + 1
  set ε : ℝ := 1 / (8 * C + 1)
  have hT : 1 ≤ T := by linarith
  have hε : 0 < ε := by positivity
  have hε₁ : 8 * C * ε ^ 2 ≤ 1 := by
    have h8 : 8 * C * ε = 8 * C / (8 * C + 1) := by ring
    have hle : 8 * C / (8 * C + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    have hε1 : ε ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    nlinarith
  -- Regularity of the cylindrical datum.
  have hJc : ContDiff ℝ 1 (uncurry fun p : ℝ × ℝ ↦ J p.2) :=
    hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)
  have hKt : ContDiff ℝ 2 (uncurry fun p : ℝ × ℝ ↦ H p.2) :=
    hH.comp (contDiff_fst.snd.prodMk contDiff_snd)
  have hxd : ContDiff ℝ 1 x := contDiff_one_of_hasDerivAt
    (X := fun t ↦ ω.hamiltonianVectorField (H t))
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH).continuous hx
  filter_upwards [eventually_dist_adjointCoeffs_preglue_lt hJ hJp hH hHp hx hxp hu hv hux hdux
    hvx hdvx hT hε] with R hR η hη hper a b hab hη₀
  obtain ⟨hR₁, hR₂⟩ := hR
  have hv₁ : (fun w : ℝ × ℝ ↦ v (w + (-R, 0))) = fun w ↦ v (w - (R, 0)) :=
    funext fun w ↦ by congr 1; ext <;> simp [sub_eq_add_neg]
  -- The pieces are the translates `u(· + R, ·)` and `v(· - R, ·)`, whose formal adjoints satisfy
  -- the estimates of `u` and `v`.
  refine ω.setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_of_splice
    (J₁ := fun p ↦ J p.2) (Ks₁ := fun _ _ ↦ 0) (Kt₁ := fun p ↦ H p.2)
    (u₁ := fun p ↦ u (p + (R, 0))) (J₂ := fun p ↦ J p.2) (Ks₂ := fun _ _ ↦ 0)
    (Kt₂ := fun p ↦ H p.2) (u₂ := fun p ↦ v (p - (R, 0))) (C := C) (ε := ε) (T := T)
    (fun _ ↦ hJc.contDiffAt) (fun _ ↦ contDiffAt_const) (fun _ ↦ hKt.contDiffAt)
    (contDiff_preglue hxd hu hv) (fun _ ↦ hJc.contDiffAt) (fun _ ↦ contDiffAt_const)
    (fun _ ↦ hKt.contDiffAt) (hu.comp (contDiff_id.add contDiff_const)) (fun _ ↦ hJc.contDiffAt)
    (fun _ ↦ contDiffAt_const) (fun _ ↦ hKt.contDiffAt) (hv.comp (contDiff_id.sub contDiff_const))
    hC (by linarith) (by nlinarith) hε₁ (fun z hz ↦ ?_) (fun z hz ↦ ?_) (fun z hz ↦ ?_)
    (fun z hz ↦ ?_) (fun η' hη' hper' a' b' hab' h₀' ↦ ?_) (fun η' hη' hper' a' b' hab' h₀' ↦ ?_)
    hη hper hab hη₀
  · simpa [adjointCoeffs] using
      (norm_fst_le _).trans ((dist_eq_norm _ _).symm.trans_le (hR₁ z hz).le)
  · simpa [adjointCoeffs] using
      (norm_snd_le _).trans ((dist_eq_norm _ _).symm.trans_le (hR₁ z hz).le)
  · simpa [adjointCoeffs] using
      (norm_fst_le _).trans ((dist_eq_norm _ _).symm.trans_le (hR₂ z hz).le)
  · simpa [adjointCoeffs] using
      (norm_snd_le _).trans ((dist_eq_norm _ _).symm.trans_le (hR₂ z hz).le)
  · simpa only [Prod.snd_add, add_zero] using
      setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_comp_add_right ω R hestu hη'
        hper' hab' h₀'
  · simpa only [Prod.snd_add, add_zero, hv₁] using
      setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_comp_add_right ω (-R) hestv
        hη' hper' hab' h₀'

end TauCeti.SymplecticForm

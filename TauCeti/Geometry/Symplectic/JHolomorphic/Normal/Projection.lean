/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Beltrami.Linear
public import TauCeti.Geometry.Symplectic.AlmostComplex.Quotient
public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Rescaling
public import TauCeti.Geometry.Symplectic.JHolomorphic.Varying
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Projecting pseudoholomorphic curves to the base of normal coordinates

Near an embedded pseudoholomorphic curve `C`, Taubes uses coordinates `(z, W) ∈ E × N` coming
from a foliation of a tube around `C` by pseudoholomorphic normal discs: the curve is the zero
section and every fibre `{z} × N` is a complex curve. In such coordinates each value `J(z, W)` of
the almost complex structure preserves the vertical subspace `{0} × N`, and so induces a complex
structure `J_E(z, W) v = (J(z, W) (v, 0)).1` on the base `E`
(`TauCeti.AlmostComplexStructure.descend`, `TauCeti.AlmostComplexStructure.descend_fst_apply`). The
projection `E × N → E` is complex linear from `J(z, W)` to `J_E(z, W)`. This file draws the
consequences for a pseudoholomorphic map `u` into `E × N` and its base component `f = u.1`.

* **Holomorphic projection.** `df` is complex linear into `J_E(u)`
  (`TauCeti.IsJHolomorphicAt.isComplexLinearMap_fderiv_fst`). The base structure depends on the
  whole point `u`, not only on its base point `f`, so `f` is holomorphic for a structure on the
  base that varies along the curve. In particular `u` projects positively: if `du(v)` is not
  vertical, every symplectic form taming `J_E(u)` is positive on `(df v, df (j v))`
  (`TauCeti.IsJHolomorphicAt.apply_fderiv_fst_pos`).
* **The Beltrami equation of the projection.** For a curve `u : ℂ → ℂ × N` this says that `f`
  solves the target Beltrami equation `\bar∂f = -μ conj (∂f)`, where `μ` is the coefficient of
  `J_E(u)`. Its modulus is `|b - i| / |b + i|` for `b = J_E(u) 1`, so
  `|\bar∂f| |b + i| = |b - i| |∂f|`
  (`TauCeti.norm_conjWirtingerDeriv_fst_mul_norm_add_I_eq`), and the projection satisfies the
  pointwise distortion bound `|\bar∂f| ≤ |b - i| |∂f|`
  (`TauCeti.norm_conjWirtingerDeriv_fst_le`). Its Jacobian `|∂f|² - |\bar∂f|²` is at least
  `(1 - |b - i|²) |∂f|²` (`TauCeti.mul_normSq_le_stdComplexSymplecticForm_fderiv_fst`).
* **Small distortion after normal dilation.** The base structure of the normal dilation
  `δ_a^* J` at `(z, W)` is that of `J` at `(z, a W)`
  (`TauCeti.fst_comp_normalDilation_comp_inl`, in
  `TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Rescaling`), so it converges to the structure
  `J_E(z, 0)` of the curve uniformly on compact sets as `a → 0`
  (`TauCeti.tendstoUniformlyOn_fst_comp_normalDilation_comp_inl`); continuity of `J` along the
  zero section suffices. When the base coordinate is holomorphic along the curve,
  `J_E(z, 0) 1 = i`, the projections of all `δ_a^* J`-holomorphic curves through a fixed compact set
  therefore have arbitrarily small distortion for `a` small
  (`TauCeti.eventually_norm_conjWirtingerDeriv_fst_le`).

The coordinate fields `J : E × N → (E × N →L[ℝ] E × N)` are those of
`TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Rescaling`. For curves from `ℂ` the
Cauchy–Riemann equation is written `du(i) = J(u) du(1)`, as in
`TauCeti.Geometry.Symplectic.JHolomorphic.RemovableSingularity`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *GR = SW: counting curves and connections*,
  J. Differential Geom. 52 (1999), 453–609.
-/

public section

open Complex Filter Set Topology
open scoped ComplexConjugate

namespace TauCeti

section General

variable {U E N : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- **Pseudoholomorphic maps project holomorphically.** If `u` is `J`-holomorphic at `x` and
`J(u x)` preserves the vertical subspace `{0} × N`, the differential of the base component `u.1` is
complex linear into the structure induced by `J(u x)` on the base. -/
theorem IsJHolomorphicAt.isComplexLinearMap_fderiv_fst {j : U → AlmostComplexStructure U}
    {J : E × N → AlmostComplexStructure (E × N)} {u : U → E × N} {x : U}
    (hu : IsJHolomorphicAt j J u x) (hJ : ∀ v : E × N, v.1 = 0 → (J (u x) v).1 = 0) :
    IsComplexLinearMap (j x)
      ((J (u x)).descend (LinearMap.fst ℝ E N) LinearMap.fst_surjective hJ)
      (fderiv ℝ (fun y ↦ (u y).1) x).toLinearMap := by
  obtain ⟨f', hf', hlin⟩ := (isJHolomorphicAt_iff j J u x).1 hu
  rw [hf'.fst.fderiv, ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.coe_fst]
  exact (AlmostComplexStructure.isComplexLinearMap_descend _ _ _ _).comp hlin

/-- **Nonvertical pseudoholomorphic directions project positively.** If `u` is `J`-holomorphic at
`x`, `J(u x)` preserves the vertical subspace, and `ω` tames the structure induced on the base,
then `ω (df v, df (j v)) > 0` for the base component `f = u.1` and every `v` whose image `du(v)` is
not vertical. -/
theorem IsJHolomorphicAt.apply_fderiv_fst_pos {j : U → AlmostComplexStructure U}
    {J : E × N → AlmostComplexStructure (E × N)} {u : U → E × N} {x : U}
    (hu : IsJHolomorphicAt j J u x) (hJ : ∀ v : E × N, v.1 = 0 → (J (u x) v).1 = 0)
    {ω : SymplecticForm E}
    (hω : ω.Tames ((J (u x)).descend (LinearMap.fst ℝ E N) LinearMap.fst_surjective hJ)) {v : U}
    (hv : (fderiv ℝ u x v).1 ≠ 0) :
    0 < ω (fderiv ℝ (fun y ↦ (u y).1) x v) (fderiv ℝ (fun y ↦ (u y).1) x (j x v)) := by
  have hf : fderiv ℝ (fun y ↦ (u y).1) x v = (fderiv ℝ u x v).1 := by
    simp [hu.differentiableAt.hasFDerivAt.fst.fderiv]
  have h := (isComplexLinearMap_iff_apply _ _ _).1 (hu.isComplexLinearMap_fderiv_fst hJ) v
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [h]
  exact hω _ (hf ▸ hv)

end General

section Plane

variable {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- The complex structure induced on the base `ℂ` by a value `A` of a coordinate field which
squares to `-1` and preserves the vertical subspace, and the complex linearity of the projected
differential of a curve solving the Cauchy–Riemann equation for `A`. -/
private theorem exists_isComplexLinear_fderiv_fst {A : ℂ × N →L[ℝ] ℂ × N} {u : ℂ → ℂ × N}
    {x : ℂ} (hu : DifferentiableAt ℝ u x) (hCR : fderiv ℝ u x I = A (fderiv ℝ u x 1))
    (hsq : ∀ w, A (A w) = -w) (hV : ∀ n, (A (0, n)).1 = 0) :
    ∃ Jb : AlmostComplexStructure ℂ, Jb 1 = (A (1, 0)).1 ∧
      IsComplexLinear (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap Jb.toLinearMap
        (fderiv ℝ (fun y ↦ (u y).1) x).toLinearMap := by
  let JA : AlmostComplexStructure (ℂ × N) :=
    ⟨A.toLinearMap, LinearMap.ext fun w ↦ by
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hsq, LinearMap.neg_apply,
        LinearMap.id_apply]⟩
  -- By construction `JA` acts as `A`.
  have hJA (w : ℂ × N) : JA w = A w := rfl
  have hV' : ∀ v : ℂ × N, v.1 = 0 → (JA v).1 = 0 := by
    rintro ⟨v₁, v₂⟩ (rfl : v₁ = 0)
    rw [hJA]
    exact hV v₂
  -- The Cauchy–Riemann equation at `1` makes `du` complex linear, so `u` is pseudoholomorphic at
  -- `x` for the constant structures `i` and `JA`.
  have hhol : IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ) (fun _ ↦ JA) u
      x := isJHolomorphicAt_of_hasFDerivAt hu.hasFDerivAt <|
    (isComplexLinearMap_iff_apply _ _ _).2 fun w ↦ by
      simpa only [ContinuousLinearMap.coe_coe, AlmostComplexStructure.ofComplexModule_apply,
        smul_eq_mul, hJA, mul_comm I w] using
        (fderiv ℝ u x : ℂ →ₗ[ℝ] ℂ × N).apply_mul_I_eq_of_apply_I_eq (A := A.toLinearMap) hCR hsq w
  exact ⟨JA.descend (LinearMap.fst ℝ ℂ N) LinearMap.fst_surjective hV',
    (AlmostComplexStructure.descend_fst_apply JA hV' 1).trans (congrArg Prod.fst (hJA (1, 0))),
    (isComplexLinearMap_iff_isComplexLinear _ _ _).1 (hhol.isComplexLinearMap_fderiv_fst hV')⟩

variable {J : ℂ × N → ℂ × N →L[ℝ] ℂ × N} {u : ℂ → ℂ × N} {x : ℂ}

/-- **The distortion of the projection of a pseudoholomorphic curve.** Let `u : ℂ → ℂ × N` solve
the Cauchy–Riemann equation `du(i) = J(u) du(1)` at `x`, where `J(u x)` squares to `-1`,
preserves the vertical subspace, and induces on the base a structure with `b = J_E(u x) 1` in the
upper half plane. Then the base component `f = u.1` satisfies `|\bar∂f| |b + i| = |b - i| |∂f|`
at `x`. -/
theorem norm_conjWirtingerDeriv_fst_mul_norm_add_I_eq (hu : DifferentiableAt ℝ u x)
    (hCR : fderiv ℝ u x I = J (u x) (fderiv ℝ u x 1)) (hsq : ∀ w, J (u x) (J (u x) w) = -w)
    (hV : ∀ n, (J (u x) (0, n)).1 = 0) (him : 0 < (J (u x) (1, 0)).1.im) :
    ‖conjWirtingerDeriv (fun y ↦ (u y).1) x 1‖ * ‖(J (u x) (1, 0)).1 + I‖ =
      ‖(J (u x) (1, 0)).1 - I‖ * ‖wirtingerDeriv (fun y ↦ (u y).1) x 1‖ := by
  obtain ⟨Jb, hb, hlin⟩ := exists_isComplexLinear_fderiv_fst hu hCR hsq hV
  exact hb ▸ Beltrami.norm_conjWirtingerDeriv_mul_norm_apply_one_add_I_eq_of_isComplexLinear Jb
    ((stdComplexSymplecticForm_tames_iff_im_pos Jb).2 (hb ▸ him)) hlin

/-- **Pointwise distortion bound for the projection of a pseudoholomorphic curve.** Under the
hypotheses of `TauCeti.norm_conjWirtingerDeriv_fst_mul_norm_add_I_eq`, the base component
`f = u.1` satisfies `|\bar∂f| ≤ |b - i| |∂f|` at `x`, where `b = J_E(u x) 1`. -/
theorem norm_conjWirtingerDeriv_fst_le (hu : DifferentiableAt ℝ u x)
    (hCR : fderiv ℝ u x I = J (u x) (fderiv ℝ u x 1)) (hsq : ∀ w, J (u x) (J (u x) w) = -w)
    (hV : ∀ n, (J (u x) (0, n)).1 = 0) (him : 0 < (J (u x) (1, 0)).1.im) :
    ‖conjWirtingerDeriv (fun y ↦ (u y).1) x 1‖ ≤
      ‖(J (u x) (1, 0)).1 - I‖ * ‖wirtingerDeriv (fun y ↦ (u y).1) x 1‖ := by
  obtain ⟨Jb, hb, hlin⟩ := exists_isComplexLinear_fderiv_fst hu hCR hsq hV
  exact hb ▸ Beltrami.norm_conjWirtingerDeriv_le_of_isComplexLinear Jb
    ((stdComplexSymplecticForm_tames_iff_im_pos Jb).2 (hb ▸ him)) hlin

/-- **Lower bound for the Jacobian of the projection of a pseudoholomorphic curve.** Under the
hypotheses of `TauCeti.norm_conjWirtingerDeriv_fst_mul_norm_add_I_eq`, the standard area form
pulls back under the base component `f = u.1` to at least `(1 - |b - i|²) |∂f|²` on the coordinate
frame, where `b = J_E(u x) 1`. -/
theorem mul_normSq_le_stdComplexSymplecticForm_fderiv_fst (hu : DifferentiableAt ℝ u x)
    (hCR : fderiv ℝ u x I = J (u x) (fderiv ℝ u x 1)) (hsq : ∀ w, J (u x) (J (u x) w) = -w)
    (hV : ∀ n, (J (u x) (0, n)).1 = 0) (him : 0 < (J (u x) (1, 0)).1.im) :
    (1 - ‖(J (u x) (1, 0)).1 - I‖ ^ 2) *
        Complex.normSq (wirtingerDeriv (fun y ↦ (u y).1) x 1) ≤
      stdComplexSymplecticForm (fderiv ℝ (fun y ↦ (u y).1) x 1)
        (fderiv ℝ (fun y ↦ (u y).1) x I) := by
  obtain ⟨Jb, hb, hlin⟩ := exists_isComplexLinear_fderiv_fst hu hCR hsq hV
  exact hb ▸ Beltrami.mul_normSq_le_stdComplexSymplecticForm_fderiv_of_isComplexLinear Jb
    ((stdComplexSymplecticForm_tames_iff_im_pos Jb).2 (hb ▸ him)) hlin

/-- **Small distortion of the projections after normal dilation.** Let `J` be continuous along the
zero section over a compact set `K`, with base structure `i` there: `J_E(z, 0) 1 = i`, the
coordinate `z` being holomorphic along the curve. Then for every `ε > 0` and all sufficiently small
`a`, every curve `u : ℂ → ℂ × N` through `K` solving the Cauchy–Riemann equation for the normal
dilation `δ_a^* J` at `x`, where `δ_a^* J` squares to `-1` and preserves the vertical subspace,
projects to a map with `|\bar∂f| ≤ ε |∂f|` at `x`. -/
theorem eventually_norm_conjWirtingerDeriv_fst_le {K : Set (ℂ × N)} (hK : IsCompact K)
    (hJ : ∀ p ∈ K, ContinuousAt J (p.1, 0)) (hJ₀ : ∀ p ∈ K, (J (p.1, 0) (1, 0)).1 = I) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ a in 𝓝 (0 : ℝ), ∀ (u : ℂ → ℂ × N) (x : ℂ), u x ∈ K → DifferentiableAt ℝ u x →
      fderiv ℝ u x I = normalDilation J a (u x) (fderiv ℝ u x 1) →
      (∀ w, normalDilation J a (u x) (normalDilation J a (u x) w) = -w) →
      (∀ n, (normalDilation J a (u x) (0, n)).1 = 0) →
      ‖conjWirtingerDeriv (fun y ↦ (u y).1) x 1‖ ≤
        ε * ‖wirtingerDeriv (fun y ↦ (u y).1) x 1‖ := by
  have hconv := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_fst_comp_normalDilation_comp_inl hK hJ) (min ε 1) (lt_min hε one_pos)
  filter_upwards [hconv] with a ha u x hxK hu hCR hsq hV
  -- The base value `b = J_E(u x) 1` of the dilated structure lies within `min ε 1` of `i`.
  have hb : ‖(normalDilation J a (u x) (1, 0)).1 - I‖ < min ε 1 := by
    set D := ContinuousLinearMap.fst ℝ ℂ N ∘L normalDilation J a (u x) ∘L
      ContinuousLinearMap.inl ℝ ℂ N -
        ContinuousLinearMap.fst ℝ ℂ N ∘L J ((u x).1, 0) ∘L ContinuousLinearMap.inl ℝ ℂ N with hD
    have h1 := D.le_opNorm (1 : ℂ)
    rw [hD, sub_apply] at h1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.coe_fst', hJ₀ _ hxK, norm_one, mul_one] at h1
    have h2 := ha (u x) hxK
    rw [dist_eq_norm'] at h2
    exact h1.trans_lt h2
  have him : 0 < (normalDilation J a (u x) (1, 0)).1.im := by
    have h := (Complex.abs_im_le_norm ((normalDilation J a (u x) (1, 0)).1 - I)).trans_lt
      (hb.trans_le (min_le_right _ _))
    rw [Complex.sub_im, Complex.I_im] at h
    linarith [neg_abs_le ((normalDilation J a (u x) (1, 0)).1.im - 1)]
  exact (norm_conjWirtingerDeriv_fst_le hu hCR hsq hV him).trans
    (mul_le_mul_of_nonneg_right (hb.le.trans (min_le_left _ _)) (norm_nonneg _))

end Plane

end TauCeti

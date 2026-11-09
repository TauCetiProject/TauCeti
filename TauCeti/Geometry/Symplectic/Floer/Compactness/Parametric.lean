/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Calculus.FDeriv.WithLp

/-!
# Compactness of Floer solutions over a compact parameter window

The moduli problems of Floer theory come in families: continuation homotopies, the input-exchange
family, the cutoff and neck-stretching comparison family, and the two-parameter families comparing
choices. A parameter `p` ranges over a set `Q` of a real inner product space `P`, and the data of
the inhomogeneous Cauchy–Riemann equation

`∂ₜu - X(p, z, u) i = J(p, z, u) (∂ₛu - X(p, z, u) 1)`

depend on it. Compactness for such a family concerns sequences `uₖ` of solutions for parameters
`pₖ ∈ Q` that are allowed to vary with `k`. This file proves that, when `Q` is compact and the data
are jointly `C²` in the parameter, the domain point and the target point, the conclusions of
`TauCeti.Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset` hold uniformly over
the window
(`TauCeti.Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_parametric`).
There is one threshold `δ > 0` for the whole window such that every sequence of solutions with
image in a compact set `K` and energy `∫_Ω ‖∂ₛuₖ‖² ≤ E` has a subsequence along which the
parameters converge to some `p₀ ∈ Q` and the maps converge locally uniformly off a finite set `Z`
of bubbling points, with `#Z * δ ≤ E`, energy at least `δ` concentrating at each point of `Z`, and
derivatives bounded on compact subsets of `Ω \ Z`. The same uniformity holds for the mean-value
inequality
(`TauCeti.Floer.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy_parametric`),
whose threshold depends only on the data over `Q × D × K`.

The parameter becomes a target coordinate. A solution `u` for the parameter `p` is the same as
the map `z ↦ ((p, 0), u z)` into the Euclidean product of the complexification `P × P` of the
parameter space with `V`, solving the equation for the structure that is the rotation
`(a, b) ↦ (-b, a)` on `P × P` and `J(a, z, x)` on `V` at the point `((a, b), x)`, and the one-form
that is `X(a, z, x)` in the `V` direction and zero in the parameter directions. The constant
parameter coordinate contributes nothing to the derivative or the energy, and the image stays in
the compact set of points `((p, 0), x)` with `p ∈ Q` and `x ∈ K`. The complexification is needed
because the parameter directions must carry a complex structure, while `P` may have odd dimension,
as for the real parameter of a one-parameter family.

As for a single datum, the limit is only shown to be continuous. Its regularity, the bubbles at
the points of `Z` and breaking along cylindrical ends are not treated here.

## Main results

* `TauCeti.Floer.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy_parametric`:
  the mean-value inequality for Floer solutions with a threshold uniform over a compact parameter
  window.
* `TauCeti.Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_parametric`:
  sequences of Floer solutions with parameters in a compact window and bounded energy have
  subsequences along which the parameters converge and the maps converge off finitely many
  bubbling points.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the graph construction for the
  inhomogeneous equation).
-/

public section

open Complex ContinuousLinearMap Filter MeasureTheory Metric Real Set Topology

namespace TauCeti.Floer

variable {P V : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The parameter as a target coordinate -/

section Extension

/-- The rotation `(a, b) ↦ (-b, a)` of the complexification `P × P` of the parameter space. -/
private noncomputable def paramRot : WithLp 2 (P × P) →L[ℝ] WithLp 2 (P × P) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ P P).symm.toContinuousLinearMap ∘L
    ((-ContinuousLinearMap.snd ℝ P P).prod (ContinuousLinearMap.fst ℝ P P)) ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℝ P P).toContinuousLinearMap

private theorem paramRot_toLp (a b : P) :
    paramRot (WithLp.toLp 2 (a, b)) = WithLp.toLp 2 (-b, a) := by
  simp [paramRot]

private theorem paramRot_paramRot (c : WithLp 2 (P × P)) : paramRot (paramRot c) = -c := by
  obtain ⟨a, b⟩ := c
  rw [paramRot_toLp, paramRot_toLp, ← Prod.neg_mk, WithLp.toLp_neg]

/-- The coordinates `(a, z, x)` of a point `(z, ((a, b), x))` of the extended problem: the
parameter `a`, the domain point `z` and the target point `x`. -/
private noncomputable def paramCoord :
    ℂ × WithLp 2 (WithLp 2 (P × P) × V) →L[ℝ] P × ℂ × V :=
  ((WithLp.fstL 2 ℝ P P ∘L WithLp.fstL 2 ℝ (WithLp 2 (P × P)) V) ∘L
      ContinuousLinearMap.snd ℝ ℂ _).prod
    ((ContinuousLinearMap.fst ℝ ℂ _).prod
      (WithLp.sndL 2 ℝ (WithLp 2 (P × P)) V ∘L ContinuousLinearMap.snd ℝ ℂ _))

private theorem paramCoord_apply (z : ℂ) (a b : P) (x : V) :
    paramCoord (z, WithLp.toLp 2 (WithLp.toLp 2 (a, b), x)) = (a, z, x) := by
  simp [paramCoord]

/-- The inclusion `x ↦ (0, x)` of `V` into the extended target. -/
private noncomputable def paramInr : V →L[ℝ] WithLp 2 (WithLp 2 (P × P) × V) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (P × P)) V).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℝ (WithLp 2 (P × P)) V

/-- The rotation of the complexified parameter directions of the extended target, `0` on `V`. -/
private noncomputable def paramRotExt :
    WithLp 2 (WithLp 2 (P × P) × V) →L[ℝ] WithLp 2 (WithLp 2 (P × P) × V) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (P × P)) V).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl ℝ (WithLp 2 (P × P)) V ∘L paramRot ∘L
      WithLp.fstL 2 ℝ (WithLp 2 (P × P)) V

/-- The almost complex structure of the extended problem: the rotation on the complexified
parameter directions and `J(a, z, x)` on `V`. -/
private noncomputable def paramStructure (J : P × ℂ × V → V →L[ℝ] V)
    (q : ℂ × WithLp 2 (WithLp 2 (P × P) × V)) :
    WithLp 2 (WithLp 2 (P × P) × V) →L[ℝ] WithLp 2 (WithLp 2 (P × P) × V) :=
  paramRotExt + paramInr (P := P) ∘L J (paramCoord q) ∘L WithLp.sndL 2 ℝ (WithLp 2 (P × P)) V

private theorem paramStructure_toLp (J : P × ℂ × V → V →L[ℝ] V)
    (q : ℂ × WithLp 2 (WithLp 2 (P × P) × V)) (c : WithLp 2 (P × P)) (v : V) :
    paramStructure J q (WithLp.toLp 2 (c, v)) = WithLp.toLp 2 (paramRot c, J (paramCoord q) v) := by
  simp [paramStructure, paramRotExt, paramInr, ← WithLp.toLp_add]

/-- The Hamiltonian one-form of the extended problem: `X(a, z, x)` in the `V` direction and zero
in the parameter directions. -/
private noncomputable def paramOneForm (X : P × ℂ × V → ℂ →L[ℝ] V)
    (q : ℂ × WithLp 2 (WithLp 2 (P × P) × V)) : ℂ →L[ℝ] WithLp 2 (WithLp 2 (P × P) × V) :=
  paramInr (P := P) ∘L X (paramCoord q)

private theorem paramOneForm_apply (X : P × ℂ × V → ℂ →L[ℝ] V)
    (q : ℂ × WithLp 2 (WithLp 2 (P × P) × V)) (ξ : ℂ) :
    paramOneForm X q ξ = WithLp.toLp 2 (0, X (paramCoord q) ξ) := by
  simp [paramOneForm, paramInr]

private theorem contDiffOn_paramStructure {n : WithTop ℕ∞} {J : P × ℂ × V → V →L[ℝ] V}
    {W : Set (P × ℂ × V)} (hJ : ContDiffOn ℝ n J W) :
    ContDiffOn ℝ n (paramStructure J) (paramCoord ⁻¹' W) :=
  contDiffOn_const.add <| contDiffOn_const.clm_comp <|
    (hJ.comp (paramCoord (P := P) (V := V)).contDiff.contDiffOn (mapsTo_preimage _ _)).clm_comp
      contDiffOn_const

private theorem contDiffOn_paramOneForm {n : WithTop ℕ∞} {X : P × ℂ × V → ℂ →L[ℝ] V}
    {W : Set (P × ℂ × V)} (hX : ContDiffOn ℝ n X W) :
    ContDiffOn ℝ n (paramOneForm X) (paramCoord ⁻¹' W) :=
  contDiffOn_const.clm_comp
    (hX.comp (paramCoord (P := P) (V := V)).contDiff.contDiffOn (mapsTo_preimage _ _))

/-- The extended structure squares to `-1` at the points `((a, b), x)` at which `J(a, z, x)`
does. -/
private theorem paramStructure_paramStructure {J : P × ℂ × V → V →L[ℝ] V} {z : ℂ} {a b : P} {x : V}
    (hJ : ∀ v, J (a, z, x) (J (a, z, x) v) = -v) (w : WithLp 2 (WithLp 2 (P × P) × V)) :
    paramStructure J (z, WithLp.toLp 2 (WithLp.toLp 2 (a, b), x))
      (paramStructure J (z, WithLp.toLp 2 (WithLp.toLp 2 (a, b), x)) w) = -w := by
  obtain ⟨c, v⟩ := w
  rw [paramStructure_toLp, paramStructure_toLp, paramRot_paramRot, paramCoord_apply, hJ,
    ← Prod.neg_mk, WithLp.toLp_neg]

end Extension

/-! ### Uniform estimates over the parameter window -/

section Window

variable {J : P × ℂ × V → V →L[ℝ] V} {X : P × ℂ × V → ℂ →L[ℝ] V} {W : Set (P × ℂ × V)}
  {Q : Set P} {D : Set ℂ} {K : Set V}

omit [InnerProductSpace ℝ P] [InnerProductSpace ℝ V] in
/-- The compact set of points `((p, 0), x)`, `p ∈ Q`, `x ∈ K`, of the extended target. -/
private theorem isCompact_paramImage (hQ : IsCompact Q) (hK : IsCompact K) :
    IsCompact ((fun r : P × V ↦ WithLp.toLp 2 (WithLp.toLp 2 (r.1, (0 : P)), r.2)) '' Q ×ˢ K) :=
  (hQ.prod hK).image (by fun_prop)

/-- The data of the extended problem are `C²` near the compact set `D × {((p, 0), x)}`, and its
structure squares to `-1` there. -/
private theorem paramData_hyp (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W)
    (hQDKW : Q ×ˢ D ×ˢ K ⊆ W)
    (hJsq : ∀ p ∈ Q, ∀ z ∈ D, ∀ x ∈ K, ∀ v, J (p, z, x) (J (p, z, x) v) = -v) :
    IsOpen (paramCoord (P := P) (V := V) ⁻¹' W) ∧
      ContDiffOn ℝ 2 (paramStructure J) (paramCoord (P := P) (V := V) ⁻¹' W) ∧
      ContDiffOn ℝ 2 (paramOneForm X) (paramCoord (P := P) (V := V) ⁻¹' W) ∧
      D ×ˢ ((fun r : P × V ↦ WithLp.toLp 2 (WithLp.toLp 2 (r.1, (0 : P)), r.2)) '' Q ×ˢ K) ⊆
        paramCoord (P := P) (V := V) ⁻¹' W ∧
      ∀ z ∈ D, ∀ y ∈ (fun r : P × V ↦ WithLp.toLp 2 (WithLp.toLp 2 (r.1, (0 : P)), r.2)) '' Q ×ˢ K,
        ∀ w, paramStructure J (z, y) (paramStructure J (z, y) w) = -w := by
  refine ⟨hW.preimage (paramCoord (P := P) (V := V)).continuous, contDiffOn_paramStructure hJ,
    contDiffOn_paramOneForm hX, ?_, ?_⟩
  · rintro ⟨z, _⟩ ⟨hz, ⟨p, x⟩, ⟨hp, hx⟩, rfl⟩
    simpa [mem_preimage, paramCoord_apply] using hQDKW ⟨hp, hz, hx⟩
  · rintro z hz _ ⟨⟨p, x⟩, ⟨hp, hx⟩, rfl⟩ w
    exact paramStructure_paramStructure (hJsq p hp z hz x hx) w

/-- A solution `u` for the parameter `p` gives the solution `z ↦ ((p, 0), u z)` of the extended
problem. -/
private theorem fderiv_paramLift_I_eq {p : P} {u : ℂ → V} {y : ℂ}
    (hCR : fderiv ℝ u y I - X (p, y, u y) I = J (p, y, u y) (fderiv ℝ u y 1 - X (p, y, u y) 1)) :
    fderiv ℝ (fun w ↦ WithLp.toLp 2 (WithLp.toLp 2 (p, (0 : P)), u w)) y I -
        paramOneForm X (y, WithLp.toLp 2 (WithLp.toLp 2 (p, (0 : P)), u y)) I =
      paramStructure J (y, WithLp.toLp 2 (WithLp.toLp 2 (p, (0 : P)), u y))
        (fderiv ℝ (fun w ↦ WithLp.toLp 2 (WithLp.toLp 2 (p, (0 : P)), u w)) y 1 -
          paramOneForm X (y, WithLp.toLp 2 (WithLp.toLp 2 (p, (0 : P)), u y)) 1) := by
  rw [fderiv_toLp_const_prodMk_apply, fderiv_toLp_const_prodMk_apply, paramOneForm_apply,
    paramOneForm_apply, ← WithLp.toLp_sub, ← WithLp.toLp_sub, Prod.mk_sub_mk, Prod.mk_sub_mk,
    sub_zero, paramStructure_toLp, paramCoord_apply, map_zero, hCR]

/-- **The mean-value inequality over a compact parameter window.** Let `J` and `X` be `C²` on an
open set `W ⊆ P × ℂ × V` containing `Q × D × K` for compact `Q ⊆ P`, `D ⊆ ℂ` and `K ⊆ V`, with
`J(p, z, x)² = -1` on `Q × D × K`. There is a threshold `δ > 0` with the following property, for
every parameter `p ∈ Q`. Let `u` be `C³` on an open disc `B_r(z₀) ⊆ D`, with `∂ₛu` continuous up
to the boundary, and on the disc let it solve
`∂ₜu - X(p, z, u) i = J(p, z, u)(∂ₛu - X(p, z, u) 1)` with image in `K`. If
`π r² + ∫_{B_r(z₀)} ‖∂ₛu‖² < δ`, then `π r² ‖∂ₛu(z₀)‖² ≤ 7 π r² + 8 ∫_{B_r(z₀)} ‖∂ₛu‖²`. -/
theorem exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy_parametric
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W)
    (hQ : IsCompact Q) (hD : IsCompact D) (hK : IsCompact K) (hQDKW : Q ×ˢ D ×ˢ K ⊆ W)
    (hJsq : ∀ p ∈ Q, ∀ z ∈ D, ∀ x ∈ K, ∀ v, J (p, z, x) (J (p, z, x) v) = -v) :
    ∃ δ > 0, ∀ ⦃p : P⦄ ⦃u : ℂ → V⦄ ⦃z₀ : ℂ⦄ ⦃r : ℝ⦄, p ∈ Q → 0 ≤ r → ball z₀ r ⊆ D →
      ContDiffOn ℝ 3 u (ball z₀ r) → ContinuousOn (fun y ↦ fderiv ℝ u y 1) (closedBall z₀ r) →
      (∀ y ∈ ball z₀ r, fderiv ℝ u y I - X (p, y, u y) I =
        J (p, y, u y) (fderiv ℝ u y 1 - X (p, y, u y) 1)) →
      (∀ y ∈ ball z₀ r, u y ∈ K) →
      π * r ^ 2 + ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 < δ →
      π * r ^ 2 * ‖fderiv ℝ u z₀ 1‖ ^ 2 ≤
        7 * π * r ^ 2 + 8 * ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 := by
  obtain ⟨hW', hJ', hX', hDKW', hJsq'⟩ := paramData_hyp hW hJ hX hQDKW hJsq
  obtain ⟨δ, hδ, hmean⟩ := exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy
    hW' hJ' hX' hD (isCompact_paramImage hQ hK) hDKW' hJsq'
  refine ⟨δ, hδ, fun p u z₀ r hp hr hrD hu hu' hCR huK hE ↦ ?_⟩
  -- The lift `z ↦ ((p, 0), u z)` solves the extended problem with the same energy density.
  have hint : ∫ y in ball z₀ r,
      ‖fderiv ℝ (fun w ↦ WithLp.toLp 2 (WithLp.toLp 2 (p, (0 : P)), u w)) y 1‖ ^ 2 =
        ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 := by
    simp only [norm_fderiv_toLp_const_prodMk_apply]
  have h := hmean (u := fun w ↦ WithLp.toLp 2 (WithLp.toLp 2 (p, (0 : P)), u w)) hr hrD
    (WithLp.contDiff_toLp.comp_contDiffOn (contDiffOn_const.prodMk hu))
    (((WithLp.prod_continuous_toLp 2 (WithLp 2 (P × P)) V).comp_continuousOn
      ((continuousOn_const (c := (0 : WithLp 2 (P × P)))).prodMk hu')).congr fun y _ ↦
        fderiv_toLp_const_prodMk_apply _ u y 1)
    (fun y hy ↦ fderiv_paramLift_I_eq (hCR y hy))
    (fun y hy ↦ ⟨(p, u y), ⟨hp, huK y hy⟩, rfl⟩) (by rwa [hint])
  rwa [hint, norm_fderiv_toLp_const_prodMk_apply] at h

/-- **Floer solutions over a compact parameter window converge off finitely many bubbling
points.** Let `J` and `X` be `C²` on an open set `W ⊆ P × ℂ × V` containing `Q × D × K` for
compact `Q ⊆ P`, `D ⊆ ℂ` and `K ⊆ V`, with `J(p, z, x)² = -1` on `Q × D × K`. There is a threshold
`δ > 0` with the following property. Let `pₖ ∈ Q` be parameters and let `uₖ` be `C³` solutions of
`∂ₜu - X(pₖ, z, u) i = J(pₖ, z, u)(∂ₛu - X(pₖ, z, u) 1)` on an open set `Ω ⊆ D`, with image in
`K` and energy `∫_Ω ‖∂ₛuₖ‖² ≤ E`. Then there are a subsequence `φ`, a parameter `p₀ ∈ Q`, a
finite set `Z ⊆ Ω` with `#Z * δ ≤ E`, and a continuous `v : Ω \ Z → K` such that along `φ` the
parameters converge to `p₀`, every disc about a point of `Z` eventually carries energy at least
`δ`, the differentials are uniformly bounded on every compact subset of `Ω \ Z`, and
`u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_parametric
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W)
    (hQ : IsCompact Q) (hD : IsCompact D) (hK : IsCompact K) (hQDKW : Q ×ˢ D ×ˢ K ⊆ W)
    (hJsq : ∀ p ∈ Q, ∀ z ∈ D, ∀ x ∈ K, ∀ v, J (p, z, x) (J (p, z, x) v) = -v) :
    ∃ δ > 0, ∀ ⦃Ω : Set ℂ⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℂ → V⦄ ⦃E : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, p k ∈ Q) → (∀ k, ContDiffOn ℝ 3 (u k) Ω) →
      (∀ k, ∀ y ∈ Ω, fderiv ℝ (u k) y I - X (p k, y, u k y) I =
        J (p k, y, u k y) (fderiv ℝ (u k) y 1 - X (p k, y, u k y) 1)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (fun y ↦ ‖fderiv ℝ (u k) y 1‖ ^ 2) Ω) →
      (∀ k, ∫ y in Ω, ‖fderiv ℝ (u k) y 1‖ ^ 2 ≤ E) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset ℂ) (v : ℂ → V), StrictMono φ ∧ p₀ ∈ Q ∧
        Tendsto (p ∘ φ) atTop (𝓝 p₀) ∧ ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ‖fderiv ℝ (u (φ n)) y 1‖ ^ 2) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  obtain ⟨hW', hJ', hX', hDKW', hJsq'⟩ := paramData_hyp hW hJ hX hQDKW hJsq
  obtain ⟨δ, hδ, hconv⟩ := exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    hW' hJ' hX' hD (isCompact_paramImage hQ hK) hDKW' hJsq'
  refine ⟨δ, hδ, fun Ω p u E hΩ hΩD hp hu hCR huK hint hE ↦ ?_⟩
  -- First extract a subsequence `ψ` along which the parameters converge.
  obtain ⟨p₀, hp₀, ψ, hψ, hpψ⟩ := hQ.tendsto_subseq hp
  -- Along `ψ`, the lifts `z ↦ ((p, 0), u z)` solve the extended problem with the same energy
  -- density.
  set U : ℕ → ℂ → WithLp 2 (WithLp 2 (P × P) × V) :=
    fun k w ↦ WithLp.toLp 2 (WithLp.toLp 2 (p (ψ k), (0 : P)), u (ψ k) w)
  have hnorm : ∀ k y, ‖fderiv ℝ (U k) y 1‖ = ‖fderiv ℝ (u (ψ k)) y 1‖ := fun k y ↦
    norm_fderiv_toLp_const_prodMk_apply _ _ y 1
  have henergy : ∀ k S, ∫ y in S, ‖fderiv ℝ (U k) y 1‖ ^ 2 =
      ∫ y in S, ‖fderiv ℝ (u (ψ k)) y 1‖ ^ 2 := fun k S ↦ by simp only [hnorm]
  obtain ⟨φ, Z, w, hφ, hZΩ, hcard, hconc, hbd, hwcont, hwK, hlim⟩ := hconv hΩ hΩD (u := U)
    (fun k ↦ WithLp.contDiff_toLp.comp_contDiffOn (contDiffOn_const.prodMk (hu (ψ k))))
    (fun k y hy ↦ fderiv_paramLift_I_eq (hCR (ψ k) y hy))
    (fun k y hy ↦ ⟨(p (ψ k), u (ψ k) y), ⟨hp (ψ k), huK (ψ k) hy⟩, rfl⟩)
    (fun k ↦ by simpa only [hnorm] using hint (ψ k))
    (fun k ↦ (henergy k Ω).trans_le (hE (ψ k)))
  refine ⟨ψ ∘ φ, p₀, Z, fun z ↦ (w z).snd, hψ.comp hφ, hp₀, hpψ.comp hφ.tendsto_atTop, hZΩ,
    hcard, fun z hz ε hε ↦ (hconc z hz ε hε).mono fun n hn ↦ ?_, fun C hC hCZ ↦ ?_,
    (WithLp.sndL 2 ℝ (WithLp 2 (P × P)) V).continuous.comp_continuousOn hwcont, ?_, ?_⟩
  · rwa [henergy] at hn
  · obtain ⟨M, hM⟩ := hbd C hC hCZ
    refine ⟨M, fun n y hy ↦ (norm_fderiv_le_norm_fderiv_toLp_prodMk_right
      (differentiableAt_const _) ?_).trans (hM n y hy)⟩
    exact ((hu _).differentiableOn (by norm_num)).differentiableAt (hΩ.mem_nhds (hCZ hy).1)
  · rintro z hz
    obtain ⟨⟨q, x⟩, ⟨-, hx⟩, hqx⟩ := hwK hz
    simpa [← hqx] using hx
  · simpa [Function.comp_def, U] using
      (WithLp.sndL 2 ℝ (WithLp 2 (P × P)) V).uniformContinuous.comp_tendstoLocallyUniformlyOn hlim

end Window

end TauCeti.Floer

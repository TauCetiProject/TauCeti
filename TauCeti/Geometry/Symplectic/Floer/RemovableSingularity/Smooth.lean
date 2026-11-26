/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.RemovableSingularity
import TauCeti.Analysis.Calculus.FDeriv.Puncture
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Puncture
import TauCeti.LinearAlgebra.Complex.LinearPart

/-!
# Removal of finite-energy punctures of Floer solutions: regularity of the filling

Let `J(z, x)` and the Hamiltonian one-form `X(z, x)` be of class `C^ℓ`, `2 ≤ ℓ ≤ ∞`, on an open set
containing `B(z₀, R) × K` for a compact `K ⊆ V`, with `J² = -1` there. A `C³` solution `u` of the
inhomogeneous Cauchy–Riemann equation

`∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)`

on the punctured disc `B(z₀, R) \ {z₀}`, with image in `K`, tamed by a symplectic form and of
finite energy, extends continuously across the puncture
(`TauCeti.Floer.exists_continuousOn_update_of_finite_energy`). This file proves that the extension
is of class `C^ℓ` on the whole disc and solves the equation at every point of it, the puncture
included (`TauCeti.Floer.exists_contDiffOn_update_of_finite_energy`); it is smooth when `J` and `X`
are. Together with the continuous extension this is removal of singularities for Floer solutions
in a coordinate disc (McDuff–Salamon, Section 4.5, and Section 8.1 for the inhomogeneous
equation), the step that extends a finite-energy solution, such as a limit of Floer solutions off
its finitely many bubbling points, across an isolated puncture.

In the form `∂ₛu + J(z, u) ∂ₜu = X(z, u) 1 + J(z, u) X(z, u) i` of the equation
(`TauCeti.add_apply_eq_add_apply_iff_sub_eq_apply_sub`), the extension is a weak solution across
the puncture (`TauCeti.Floer.exists_isWeakCauchyRiemannOn_update_of_finite_energy`): its
weak derivative is the classical derivative of `u`
(`TauCeti.Floer.exists_hasWeakFDerivOn_update_of_finite_energy`), which lies in `Lᵖ` for some
`p > 2` near the puncture
(`TauCeti.Floer.exists_continuousOn_update_memLp_fderiv_of_finite_energy`). Interior regularity of
the nonlinear Cauchy–Riemann equation across a point then gives the regularity, and the classical
equation at the puncture follows by continuity
(`TauCeti.contDiffOn_ball_and_fderiv_apply_one_add_eq_of_isWeakCauchyRiemannOn`).

## Main results

* `TauCeti.Floer.exists_isWeakCauchyRiemannOn_update_of_finite_energy`: the filling is a weak
  solution across the puncture, with an exponent `p > 2`.
* `TauCeti.Floer.exists_contDiffOn_update_of_finite_energy`: the filling is a `C^ℓ` solution of
  the equation on the whole disc.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (removal of singularities), Section 8.1 (the inhomogeneous equation) and
  Appendix B.4 (elliptic bootstrapping).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology TopologicalSpace

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V} {J : ℂ × V → V →L[ℝ] V}
  {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)} {K : Set V} {u : ℂ → V} {z₀ : ℂ} {R c : ℝ}
  {ℓ : ℕ∞}

open Classical in
/-- **The filled Floer solution is a weak solution.** Under the hypotheses of
`TauCeti.Floer.exists_continuousOn_update_of_finite_energy`, the continuous filling of `u` at `z₀`
by its limit `q` solves `∂ₛu + J(z, u) ∂ₜu = X(z, u) 1 + J(z, u) X(z, u) i`, the inhomogeneous
Cauchy–Riemann form of the equation, weakly on a smaller disc about `z₀`, with weak derivative in
`Lᵖ` for some `p > 2`. -/
theorem exists_isWeakCauchyRiemannOn_update_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W) (hK : IsCompact K)
    (hKW : ball z₀ R ×ˢ K ⊆ W) (hJsq : ∀ p ∈ ball z₀ R ×ˢ K, ∀ v, J p (J p v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hF : ∀ z ∈ ball z₀ R \ {z₀},
      fderiv ℝ u z I - X (z, u z) I = J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (z, u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ q ∈ K, Tendsto u (𝓝[≠] z₀) (𝓝 q) ∧ MapsTo (Function.update u z₀ q) (ball z₀ R) K ∧
      ∃ ε > 0, ε < R ∧ ∃ p : ℝ, 2 < p ∧
        IsWeakCauchyRiemannOn (ENNReal.ofReal p) (ball z₀ ε) (fun z x ↦ J (z, x))
          (fun z x ↦ X (z, x) 1 + J (z, x) (X (z, x) I)) (Function.update u z₀ q) := by
  obtain ⟨q, hq, hlim, -, hmaps⟩ :=
    exists_continuousOn_update_of_finite_energy hg hc hR hW hJ hX hK hKW hJsq hu hF huK htame
      henergy
  obtain ⟨q₁, -, hcont, -, hweak⟩ :=
    exists_hasWeakFDerivOn_update_of_finite_energy hg hc hR hW hJ hX hK hKW hJsq hu hF huK
      htame henergy
  obtain ⟨q₂, -, hcont₂, -, ε, hε, hεR, p, hp, hmem⟩ :=
    exists_continuousOn_update_memLp_fderiv_of_finite_energy hg hc hR hW hJ hX hK hKW hJsq hu
      hF huK htame henergy
  -- The three fillings agree: each value is the limit of `u` at `z₀`.
  have hq₁ : q₁ = q := tendsto_nhds_unique
    (continuousAt_update_same.1 (hcont.continuousAt (ball_mem_nhds z₀ hR))) hlim
  have hq₂ : q₂ = q := tendsto_nhds_unique
    (continuousAt_update_same.1 (hcont₂.continuousAt (ball_mem_nhds z₀ hR))) hlim
  rw [hq₁] at hcont hweak
  rw [hq₂] at hmem
  have hεR' : ball z₀ ε ⊆ ball z₀ R := ball_subset_ball hεR.le
  refine ⟨q, hq, hlim, hmaps, ε, hε, hεR, p, hp, ?_⟩
  rw [← Opens.coe_mk (U := ball z₀ ε) (hU := isOpen_ball), isWeakCauchyRiemannOn_iff_of_isOpen]
  have hae : ∀ᵐ z ∂volume.restrict (ball z₀ ε), z ∈ ball z₀ R \ {z₀} := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne z₀)] with z hz hzne
    exact ⟨hεR' hz, hzne⟩
  -- The weak derivative is the classical derivative of `u`, which is that of the filling off `z₀`.
  refine ⟨hcont.mono hεR', (hcont.mono hεR').memLpLoc, fderiv ℝ u,
    hweak.mono (SetLike.coe_subset_coe.1 hεR'), (hmem.ae_eq ?_).memLpLoc, ?_⟩
  · filter_upwards [hae] with z hz
    exact fderiv_update_of_ne hz.2 _
  · filter_upwards [hae] with z hz
    rw [Function.update_of_ne hz.2,
      add_apply_eq_add_apply_iff_sub_eq_apply_sub (hJsq _ ⟨hz.1, huK hz⟩)]
    exact hF z hz

open Classical in
/-- **Removal of finite-energy punctures of Floer solutions.** Let `J(z, x)` and the Hamiltonian
one-form `X(z, x)` be `C^ℓ`, `2 ≤ ℓ ≤ ∞`, on an open set `W` containing `B(z₀, R) × K` for a
compact `K ⊆ V`, with `J² = -1` on `B(z₀, R) × K`, and let `u` be a `C³` solution of
`∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)` on `B(z₀, R) \ {z₀}`, with image in `K`, tamed by `ω`
with a uniform constant, and of finite energy. The fixed structure `J₀` identifies the given inner
product with a symplectic metric. Then `u` has a limit `q ∈ K` at `z₀`, and the filling
`Function.update u z₀ q` is of class `C^ℓ` on `B(z₀, R)`, with image in `K`, and solves the
equation at every point of `B(z₀, R)`, the puncture included. -/
theorem exists_contDiffOn_update_of_finite_energy (hℓ : 2 ≤ ℓ)
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ J W) (hX : ContDiffOn ℝ ℓ X W) (hK : IsCompact K)
    (hKW : ball z₀ R ×ˢ K ⊆ W) (hJsq : ∀ p ∈ ball z₀ R ×ˢ K, ∀ v, J p (J p v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hF : ∀ z ∈ ball z₀ R \ {z₀},
      fderiv ℝ u z I - X (z, u z) I = J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (z, u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ q ∈ K, Tendsto u (𝓝[≠] z₀) (𝓝 q) ∧ MapsTo (Function.update u z₀ q) (ball z₀ R) K ∧
      ContDiffOn ℝ ℓ (Function.update u z₀ q) (ball z₀ R) ∧
      ∀ z ∈ ball z₀ R,
        fderiv ℝ (Function.update u z₀ q) z I - X (z, Function.update u z₀ q z) I =
          J (z, Function.update u z₀ q z)
            (fderiv ℝ (Function.update u z₀ q) z 1 - X (z, Function.update u z₀ q z) 1) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ℓ := WithTop.coe_le_coe.2 hℓ
  obtain ⟨q, hq, hlim, hmaps, ε, hε, hεR, p, hp, hweak⟩ :=
    exists_isWeakCauchyRiemannOn_update_of_finite_energy hg hc hR hW (hJ.of_le h2) (hX.of_le h2)
      hK hKW hJsq hu hF huK htame henergy
  set v := Function.update u z₀ q
  have hvu : EqOn v u (ball z₀ R \ {z₀}) := fun z hz ↦ Function.update_of_ne hz.2 _ _
  have hvK (z : ℂ) (hz : z ∈ ball z₀ R) : (z, v z) ∈ ball z₀ R ×ˢ K := ⟨hz, hmaps hz⟩
  -- Off the puncture `v` is `u`, a classical solution of `∂ₛv + J(z, v) ∂ₜv = η(z, v)`.
  set η : ℂ → V → V := fun z x ↦ X (z, x) 1 + J (z, x) (X (z, x) I)
  have hCRv (z : ℂ) (hz : z ∈ ball z₀ R \ {z₀}) :
      fderiv ℝ v z 1 + J (z, v z) (fderiv ℝ v z I) = η z (v z) := by
    rw [fderiv_update_of_ne hz.2, hvu hz,
      add_apply_eq_add_apply_iff_sub_eq_apply_sub (hJsq _ (hvu hz ▸ hvK z hz.1))]
    exact hF z hz
  obtain ⟨hv, hCR⟩ :=
    contDiffOn_ball_and_fderiv_apply_one_add_eq_of_isWeakCauchyRiemannOn
      (J := fun z x ↦ J (z, x)) (η := η) (le_trans (by norm_num) hℓ)
      (by simpa using (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hp) hε hεR.le hW hJ
      ((hX.clm_apply contDiffOn_const).add (hJ.clm_apply (hX.clm_apply contDiffOn_const)))
      (fun z hz ↦ hKW (hvK z hz)) (fun z hz ↦ hJsq _ (hvK z hz))
      ((hu.of_le (by norm_num)).congr hvu) hCRv hweak
  exact ⟨q, hq, hlim, hmaps, hv, fun z hz ↦
    (add_apply_eq_add_apply_iff_sub_eq_apply_sub (hJsq _ (hvK z hz)) _ _ _ _).1 (hCR z hz)⟩

end TauCeti.Floer

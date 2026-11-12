/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.EndLinearization
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import TauCeti.Geometry.Symplectic.Area.Basic
import TauCeti.Geometry.Symplectic.Duality
import TauCeti.Geometry.Symplectic.Floer.Linearization
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Basic

/-!
# The semi-Fredholm estimate of the linearized Floer operator

Let `(V, ω)` be a symplectic vector space, `H_t` a one-periodic Hamiltonian, `J_t(y)` a family of
almost complex structures and `u` a map of the cylinder whose loops converge, as `s → ±∞`, to
nondegenerate one-periodic orbits `x_±` of `H`, as a Floer cylinder of finite energy does. The
linearized Floer operator along `u` is

`D_u ξ = ∂s ξ + J_t(u) (∂t ξ - dX_{H_t}(u) ξ) + (dJ_t(u) ξ) (∂t u - X_{H_t}(u))`

(`TauCeti.SymplecticForm.floerLinearization` for the datum `K = H_t dt`). This file proves the
estimate behind its Fredholm property: there are constants `C` and `T` such that every `C²` map
`ξ` of period one in `t` and compact support in `s` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over the cylinder
(`exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_setIntegral`).
The last term is an integral over a fixed compact piece of the cylinder; since the inclusion of
`W^{1,2}` into `L²` on such a piece is compact, an estimate of this form shows that the extension
of `D_u` to the Sobolev completion has finite-dimensional kernel and closed range.

* **The interior estimate.** On a rectangle `[c, d] × [0, 1]`, for any `C¹` family `J(z, y)` that
  is compatible along `u` and any `C²` perturbation `K = Ks ds + Kt dt`, maps `ξ` vanishing on the
  two slices satisfy `∫ (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C ∫ (‖D_u ξ‖² + ‖ξ‖²)`
  (`TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add`).
  In the pointwise metric `g_z = ω(·, J ·)` the Cauchy–Riemann part satisfies
  `g(∂s ξ + J ∂t ξ) = g(∂s ξ) + g(∂t ξ) - 2 ω(∂s ξ, ∂t ξ)`, and the symplectic area
  `∫ ω(∂s ξ, ∂t ξ)` of `ξ` vanishes by Stokes' theorem, because `ξ` vanishes on the two slices
  and is periodic in `t`. Only `ω`, not `J`, enters the cross term, so no derivative of `J` is
  needed. The remaining terms of `D_u` are of order zero
  (`TauCeti.SymplecticForm.norm_floerLinearization_sub_le`).
* **Patching.** The estimate on the two ends,
  `TauCeti.SymplecticForm.exists_mem_forall_setIntegral_le_mul_setIntegral_floerLinearization`,
  controls `ξ` beyond some `R₀` and below `-R₀` by `D_u ξ` alone. Cutoffs `β₊(s)`, `β₋(s)` equal to
  one far out on the ends and `β₀ = 1 - β₊ - β₋` supported in `[-T, T]`, `T = R₀ + 1`, split
  `ξ` into three pieces, one for each estimate. By the Leibniz rule
  `D_u (β ξ) = β D_u ξ + β' ξ` (`TauCeti.SymplecticForm.floerLinearization_smul_fst`), the cutoffs
  only add terms `β' ξ`, which are supported in `[-T, T]`.

These are estimates on smooth maps; the Sobolev completion and the Fredholm property itself are
not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the linearized operator `∂s + J ∂t + S(s, t)` along a
  Floer trajectory and its Fredholm property.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.1 and Appendix B (the energy identity of the
  Cauchy–Riemann operator).
* M. Schwarz, *Morse homology*, Progress in Mathematics 111, Birkhäuser, 1993, Section 2.2 (the
  semi-Fredholm estimate from estimates on the ends and a compact core).
-/

public section

open Filter Set MeasureTheory Topology ContinuousLinearMap
open scoped Manifold NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The interior `L²` estimate of the linearized Floer operator.** Let `J(z, y)` be a `C¹`
family of almost complex structures depending on the domain point `z = (s, t)` and the target
point `y`, let `K = Ks ds + Kt dt` be a `C²` Hamiltonian perturbation, and let `u` be `C¹` on the
rectangle `[c, d] × [0, 1]`, with `J(z, u(z))` compatible with `ω` there. Then there is a constant
`C ≥ 0` such that every map `ξ` that is `C²` on the rectangle, has equal values at `t = 0` and
`t = 1`, and vanishes on the slices `s = c` and `s = d`, satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C ∫ (‖D_u ξ‖² + ‖ξ‖²)`

over `[c, d] × [0, 1]`, for the linearized Floer operator `D_u` of `(J, K)` along `u`. The constant
does not depend on `ξ`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    {Ks Kt : ℝ × ℝ → V → ℝ} (hKs : ContDiff ℝ 2 (Function.uncurry Ks))
    (hKt : ContDiff ℝ 2 (Function.uncurry Kt)) {u : ℝ × ℝ → V} {c d : ℝ}
    (hu : ∀ z ∈ Icc c d ×ˢ Icc 0 1, ContDiffAt ℝ 1 u z)
    (hJu : ∀ z ∈ Icc c d ×ˢ Icc 0 1, ω.Compatible (J z (u z))) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, (∀ z ∈ Icc c d ×ˢ Icc 0 1, ContDiffAt ℝ 2 ξ z) →
      (∀ s ∈ Icc c d, ξ (s, 1) = ξ (s, 0)) → (∀ t ∈ Icc (0 : ℝ) 1, ξ (c, t) = 0) →
      (∀ t ∈ Icc (0 : ℝ) 1, ξ (d, t) = 0) →
      ∫ z in Icc c d ×ˢ Icc 0 1,
          (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
        C * ∫ z in Icc c d ×ˢ Icc 0 1,
          (‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
              ξ z‖ ^ 2 + ‖ξ z‖ ^ 2) := by
  set R := Icc c d ×ˢ Icc (0 : ℝ) 1 with hRdef
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  set Jc : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  have hJc : ContDiff ℝ 1 (Function.uncurry Jc) := hJ
  have hgraph (z : ℝ × ℝ) (hz : z ∈ R) : ContinuousAt (fun w ↦ (w, u w)) z :=
    continuousAt_id.prodMk (hu z hz).continuousAt
  -- The metrics `g_z = ω(·, J(z, u(z)) ·)` are uniformly equivalent to the norm on `R`.
  have hJuA (z : ℝ × ℝ) (hz : z ∈ R) : ContinuousAt (fun w ↦ Jc w (u w)) z :=
    ContinuousAt.comp (f := fun w ↦ (w, u w)) hJc.continuous.continuousAt (hgraph z hz)
  have hJuc : ContinuousOn (fun w ↦ Jc w (u w)) R := fun z hz ↦ (hJuA z hz).continuousWithinAt
  obtain ⟨m, hm, M, hM, hmM⟩ := ω.exists_pos_forall_mul_norm_sq_le_associatedBilinForm hR hJuc
    fun z hz ↦ (hJu z hz).tames
  -- The coefficient of the zeroth-order part of `D_u` is bounded on `R`.
  set f : ℝ × ℝ → ℝ := fun z ↦ ‖fderiv ℝ (ω.hamiltonianVectorField (Ks z)) (u z)‖ +
    ‖fderiv ℝ (Jc z) (u z)‖ *
      ‖fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)‖ +
    ‖Jc z (u z)‖ * ‖fderiv ℝ (ω.hamiltonianVectorField (Kt z)) (u z)‖
  have hfc : ContinuousOn f R := by
    intro z hz
    have hX {K : ℝ × ℝ → V → ℝ} (hK : ContDiff ℝ 2 (Function.uncurry K)) :
        ContinuousAt (fun w ↦ ω.hamiltonianVectorField (K w) (u w)) z ∧
          ContinuousAt (fun w ↦ fderiv ℝ (ω.hamiltonianVectorField (K w)) (u w)) z := by
      have hF : ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ ω.hamiltonianVectorField (K p.1) p.2)
          (z, u z) :=
        ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) hK.contDiffAt
      exact ⟨ContinuousAt.comp (f := fun w ↦ (w, u w)) hF.continuousAt (hgraph z hz),
        (ContDiffAt.fderiv (f := fun w y ↦ ω.hamiltonianVectorField (K w) y) hF
          ((hu z hz).of_le zero_le_one) le_rfl).continuousAt⟩
    have hdJ :=
      (ContDiffAt.fderiv (f := Jc) hJc.contDiffAt ((hu z hz).of_le zero_le_one)
        le_rfl).continuousAt
    have hdu := (hu z hz).continuousAt_fderiv one_ne_zero
    exact ((((hX hKs).2.norm.add (hdJ.norm.mul ((hdu.clm_apply continuousAt_const).sub
      (hX hKt).1).norm)).add ((hJuA z hz).norm.mul (hX hKt).2.norm))).continuousWithinAt
  obtain ⟨N, hN⟩ := hR.exists_bound_of_continuousOn hfc
  refine ⟨2 * M * (1 + N ^ 2) / m, by positivity, fun ξ hξ hper hξ₀ hξ₁ ↦ ?_⟩
  rcases lt_or_ge d c with hdc | hcd
  · simp [hRdef, Icc_eq_empty_of_lt hdc]
  -- Continuity of the integrands on `R`.
  have hdξ : ContinuousOn (fderiv ℝ ξ) R := fun z hz ↦
    ((hξ z hz).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hξc : ContinuousOn ξ R := fun z hz ↦ (hξ z hz).continuousAt.continuousWithinAt
  have hs : ContinuousOn (fun z ↦ fderiv ℝ ξ z stdComplexLineReal) R :=
    hdξ.clm_apply continuousOn_const
  have ht : ContinuousOn (fun z ↦ fderiv ℝ ξ z stdComplexLineImag) R :=
    hdξ.clm_apply continuousOn_const
  have hDc : ContinuousOn (ω.floerLinearization Jc Ks Kt u ξ) R := fun z hz ↦
    (ω.continuousAt_floerLinearization hJc.contDiffAt hKs.contDiffAt hKt.contDiffAt (hu z hz)
      ((hξ z hz).of_le one_le_two)).continuousWithinAt
  have hg {v : ℝ × ℝ → V} (hv : ContinuousOn v R) :
      ContinuousOn (fun z ↦ ω.associatedBilinForm (J z (u z)) (v z) (v z)) R :=
    (ω.continuousOn_apply_comp hv (hJuc.clm_apply hv)).congr fun z _ ↦ by simp [Jc]
  have hint {φ : ℝ × ℝ → ℝ} (hφ : ContinuousOn φ R) : IntegrableOn φ R :=
    hφ.integrableOn_compact hR
  set w : ℝ × ℝ → V := fun z ↦
    fderiv ℝ ξ z stdComplexLineReal + Jc z (u z) (fderiv ℝ ξ z stdComplexLineImag) with hwdef
  have hw : ContinuousOn w R := hs.add (hJuc.clm_apply ht)
  have hE : ContinuousOn (fun z ↦ ω.associatedBilinForm (J z (u z))
      (fderiv ℝ ξ z stdComplexLineReal) (fderiv ℝ ξ z stdComplexLineReal) +
      ω.associatedBilinForm (J z (u z))
        (fderiv ℝ ξ z stdComplexLineImag) (fderiv ℝ ξ z stdComplexLineImag)) R :=
    (hg hs).add (hg ht)
  -- The metrics dominate the squared norms of the partial derivatives.
  have hI₁ : m * ∫ z in R,
      (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
      ∫ z in R, (ω.associatedBilinForm (J z (u z))
        (fderiv ℝ ξ z stdComplexLineReal) (fderiv ℝ ξ z stdComplexLineReal) +
        ω.associatedBilinForm (J z (u z))
          (fderiv ℝ ξ z stdComplexLineImag) (fderiv ℝ ξ z stdComplexLineImag)) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hint (continuousOn_const.mul ((hs.norm.pow 2).add
      (ht.norm.pow 2)))) (hint hE) hR.measurableSet fun z hz ↦ ?_
    have h₁ := (hmM z hz (fderiv ℝ ξ z stdComplexLineReal)).1
    have h₂ := (hmM z hz (fderiv ℝ ξ z stdComplexLineImag)).1
    rw [mul_add]
    exact add_le_add h₁ h₂
  -- The energy identity: the cross term `2 ω(∂s ξ, ∂t ξ)` integrates to zero.
  have hI₂ : ∫ z in R, (ω.associatedBilinForm (J z (u z))
        (fderiv ℝ ξ z stdComplexLineReal) (fderiv ℝ ξ z stdComplexLineReal) +
        ω.associatedBilinForm (J z (u z))
          (fderiv ℝ ξ z stdComplexLineImag) (fderiv ℝ ξ z stdComplexLineImag)) =
      ∫ z in R, ω.associatedBilinForm (J z (u z)) (w z) (w z) := by
    have hpt : ∀ z ∈ R, ω.associatedBilinForm (J z (u z)) (w z) (w z) =
        (ω.associatedBilinForm (J z (u z))
          (fderiv ℝ ξ z stdComplexLineReal) (fderiv ℝ ξ z stdComplexLineReal) +
          ω.associatedBilinForm (J z (u z))
            (fderiv ℝ ξ z stdComplexLineImag) (fderiv ℝ ξ z stdComplexLineImag)) -
          2 * ω (fderiv ℝ ξ z stdComplexLineReal) (fderiv ℝ ξ z stdComplexLineImag) := by
      intro z hz
      have h := stdComplexLineEnergyDensity_sub_two_mul_symplecticForm (hJu z hz).invariant
        (fderiv ℝ ξ z : (ℝ × ℝ) →L[ℝ] V).toLinearMap
      simp only [stdComplexLineEnergyDensity_def, ContinuousLinearMap.coe_coe] at h
      simp only [hwdef, Jc, LinearMap.coe_toContinuousLinearMap']
      exact h.symm
    have hω : ContinuousOn (fun z ↦
        ω (fderiv ℝ ξ z stdComplexLineReal) (fderiv ℝ ξ z stdComplexLineImag)) R :=
      ω.continuousOn_apply_comp hs ht
    -- The symplectic area is the difference of the loop areas of the two zero slices.
    have hzero {s : ℝ} (hs : ∀ t ∈ Icc (0 : ℝ) 1, ξ (s, t) = 0) :
        ω.loopArea (fun t ↦ ξ (s, t)) = 0 := by
      rw [loopArea_def, intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_]
      · simp
      · rw [uIcc_of_le zero_le_one] at ht
        simp [hs t ht]
    rw [setIntegral_congr_fun hR.measurableSet hpt, integral_sub (hint hE)
      ((hint hω).const_mul 2), integral_const_mul,
      ω.integral_symplecticForm_fderiv_eq_loopArea_sub hcd hξ hper, hzero hξ₁, hzero hξ₀]
    ring
  -- `‖w‖ ≤ ‖D_u ξ‖ + |N| ‖ξ‖`, so `g(w, w) ≤ 2 M (1 + N²) (‖D_u ξ‖² + ‖ξ‖²)`.
  have hI₃ : ∫ z in R, ω.associatedBilinForm (J z (u z)) (w z) (w z) ≤
      ∫ z in R, 2 * M * (1 + N ^ 2) *
        (‖ω.floerLinearization Jc Ks Kt u ξ z‖ ^ 2 + ‖ξ z‖ ^ 2) := by
    refine setIntegral_mono_on (hint (hg hw)) (hint (continuousOn_const.mul
      ((hDc.norm.pow 2).add (hξc.norm.pow 2)))) hR.measurableSet fun z hz ↦ ?_
    have hle := norm_floerLinearization_sub_le ω Jc Ks Kt u ξ z
    have hfz : f z ≤ |N| := (Real.le_norm_self _).trans ((hN z hz).trans (le_abs_self N))
    have hwle : ‖w z‖ ≤ ‖ω.floerLinearization Jc Ks Kt u ξ z‖ + |N| * ‖ξ z‖ := by
      have h₁ := norm_le_norm_add_norm_sub' (w z) (ω.floerLinearization Jc Ks Kt u ξ z)
      rw [norm_sub_rev] at h₁
      have h₂ : f z * ‖ξ z‖ ≤ |N| * ‖ξ z‖ := by gcongr
      simp only [hwdef] at h₁ ⊢
      linarith
    have hsq : ‖w z‖ ^ 2 ≤ 2 * (1 + N ^ 2) *
        (‖ω.floerLinearization Jc Ks Kt u ξ z‖ ^ 2 + ‖ξ z‖ ^ 2) := by
      have h₀ := pow_le_pow_left₀ (norm_nonneg _) hwle 2
      have hN2 : |N| ^ 2 = N ^ 2 := sq_abs N
      nlinarith [sq_nonneg (‖ω.floerLinearization Jc Ks Kt u ξ z‖ - |N| * ‖ξ z‖),
        sq_nonneg (‖ω.floerLinearization Jc Ks Kt u ξ z‖), sq_nonneg (N * ‖ξ z‖),
        sq_nonneg ‖ξ z‖, sq_nonneg N]
    calc ω.associatedBilinForm (J z (u z)) (w z) (w z) ≤ M * ‖w z‖ ^ 2 := (hmM z hz (w z)).2
      _ ≤ M * (2 * (1 + N ^ 2) *
          (‖ω.floerLinearization Jc Ks Kt u ξ z‖ ^ 2 + ‖ξ z‖ ^ 2)) := by gcongr
      _ = _ := by ring
  have h := (hI₁.trans_eq hI₂).trans hI₃
  rw [integral_const_mul] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  linarith

/-- The `L²` estimate of `exists_mem_forall_setIntegral_le_mul_setIntegral_floerLinearization` on
the far part of an end, restated in the norm of `V`:
`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C ∫ ‖D_u ξ‖²` over `[a, b] × [0, 1]`. -/
private theorem exists_mem_forall_setIntegral_norm_sq_le_mul_setIntegral_floerLinearization
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) (hHp : Function.Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hxp : Function.Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJx : ∀ t, ω.Compatible (J t (x t))) {l : Filter ℝ} {u : ℝ × ℝ → V}
    (hu : ContDiff ℝ 1 u) (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l (Icc 0 1))
    (hδ : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 l (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ U ∈ l, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ →
      (∀ s t, ξ (s, t + 1) = ξ (s, t)) → ∀ ⦃a b : ℝ⦄, a ≤ b → Icc a b ⊆ U →
      (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1,
            ‖ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
              (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ z‖ ^ 2 := by
  obtain ⟨C₀, hC₀, U, hU, hest⟩ :=
    ω.exists_mem_forall_setIntegral_le_mul_setIntegral_floerLinearization hX hH hHp hx hxp hnd hJ
      hJx (Eventually.of_forall fun _ _ _ ↦ hu.contDiffAt) hux hδ
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hJxc : Continuous fun p : ℝ × V ↦ J p.1 (x p.1) p.2 :=
    (hJ.continuous.comp (continuous_fst.prodMk (hxc.comp continuous_fst))).clm_apply
      continuous_snd
  have he : Continuous fun t ↦ (J t (x t)).toLinearMap.toContinuousLinearMap :=
    hJ.continuous.comp (continuous_id.prodMk hxc)
  -- On `t ∈ [0, 1]`, `m ‖v‖² ≤ g_t(v, v) ≤ M ‖v‖²` and `‖S_t‖ ≤ |B|`.
  obtain ⟨m, hm, M, hM, hmM⟩ := ω.exists_pos_forall_mul_norm_sq_le_associatedBilinForm
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)) he.continuousOn fun t _ ↦ (hJx t).tames
  have hSc := ω.continuous_fderiv_hamiltonianVectorField_comp hH hxc
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hSc.continuousOn
  refine ⟨(2 + 2 * B ^ 2) * C₀ * M / m, by positivity, U, hU,
    fun ξ hξ hper a b hab hab' ha hb ↦ ?_⟩
  set R := Icc a b ×ˢ Icc (0 : ℝ) 1
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  set S : ℝ → V →L[ℝ] V := fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)
  set D := ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
    (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ
  have hdξ : Continuous (fderiv ℝ ξ) := hξ.continuous_fderiv (by norm_num)
  have hs : Continuous fun z ↦ fderiv ℝ ξ z stdComplexLineReal := hdξ.clm_apply continuous_const
  have ht : Continuous fun z ↦ fderiv ℝ ξ z stdComplexLineImag := hdξ.clm_apply continuous_const
  have hDc : Continuous D := continuous_iff_continuousAt.2 fun z ↦
    ω.continuousAt_floerLinearization (J := fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2)
      (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt contDiffAt_const
      (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt hu.contDiffAt
      (hξ.contDiffAt.of_le one_le_two)
  set Jx : ℝ → AlmostComplexStructure V := fun t ↦ J t (x t)
  have hG := (Floer.continuous_associatedBilinForm_add_apply_self (ω := ω) (J := Jx) hJxc hSc
    (hξ.of_le one_le_two)).add
    (Floer.continuous_associatedBilinForm_apply_self (ω := ω) (J := Jx) hJxc hξ.continuous)
  have hgD := Floer.continuous_associatedBilinForm_apply_self (ω := ω) (J := Jx) hJxc hDc
  have h₁ := hest hξ hper hab hab' ha hb
  -- The metrics dominate the squared norms, with `‖∂t ξ‖² ≤ 2 ‖∂t ξ - S ξ‖² + 2 B² ‖ξ‖²`.
  have h₂ : m * ∫ z in R, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
      (2 + 2 * B ^ 2) * ∫ z in R,
        ((ω.associatedBilinForm (J z.2 (x z.2)) (fderiv ℝ ξ z stdComplexLineReal)
            (fderiv ℝ ξ z stdComplexLineReal) +
          ω.associatedBilinForm (J z.2 (x z.2)) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
            (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))) +
          ω.associatedBilinForm (J z.2 (x z.2)) (ξ z) (ξ z)) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_mono_on ((continuous_const.mul (((hs.norm.pow 2).add (ht.norm.pow 2)).add
      (hξ.continuous.norm.pow 2))).continuousOn.integrableOn_compact hR)
      ((continuous_const.mul hG).continuousOn.integrableOn_compact hR) hR.measurableSet
      fun z ⟨_, hz⟩ ↦ ?_
    have e₁ := (hmM z.2 hz (fderiv ℝ ξ z stdComplexLineReal)).1
    have e₂ := (hmM z.2 hz (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))).1
    have e₃ := (hmM z.2 hz (ξ z)).1
    have hSξ : ‖S z.2 (ξ z)‖ ≤ |B| * ‖ξ z‖ :=
      (le_opNorm _ _).trans (by gcongr; exact (hB z.2 hz).trans (le_abs_self B))
    have hdt : ‖fderiv ℝ ξ z stdComplexLineImag‖ ≤
        ‖fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)‖ + |B| * ‖ξ z‖ := by
      have := norm_le_norm_add_norm_sub' (fderiv ℝ ξ z stdComplexLineImag) (S z.2 (ξ z))
      linarith
    have hdt2 : ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 ≤
        2 * ‖fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)‖ ^ 2 + 2 * B ^ 2 * ‖ξ z‖ ^ 2 := by
      have h₀ := pow_le_pow_left₀ (norm_nonneg _) hdt 2
      have hB2 : |B| ^ 2 = B ^ 2 := sq_abs B
      nlinarith [sq_nonneg (‖fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)‖ - |B| * ‖ξ z‖)]
    have hg₀ : 0 ≤ ω.associatedBilinForm (J z.2 (x z.2)) (fderiv ℝ ξ z stdComplexLineReal)
        (fderiv ℝ ξ z stdComplexLineReal) :=
      (mul_nonneg hm.le (sq_nonneg _)).trans e₁
    have hg₁ : 0 ≤ ω.associatedBilinForm (J z.2 (x z.2)) (ξ z) (ξ z) :=
      (mul_nonneg hm.le (sq_nonneg _)).trans e₃
    have hg₂ : 0 ≤ ω.associatedBilinForm (J z.2 (x z.2))
        (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
        (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)) :=
      (mul_nonneg hm.le (sq_nonneg _)).trans e₂
    have e₃' := mul_le_mul_of_nonneg_left e₃ (by positivity : (0 : ℝ) ≤ 2 * B ^ 2 + 1)
    linarith [mul_nonneg (sq_nonneg B) hg₀, mul_nonneg (sq_nonneg B) hg₂,
      mul_le_mul_of_nonneg_left hdt2 hm.le]
  -- The metric along `x` is bounded by `M` times the squared norm.
  have h₃ : ∫ z in R, ω.associatedBilinForm (J z.2 (x z.2)) (D z) (D z) ≤
      M * ∫ z in R, ‖D z‖ ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hgD.continuousOn.integrableOn_compact hR)
      ((continuous_const.mul (hDc.norm.pow 2)).continuousOn.integrableOn_compact hR)
      hR.measurableSet fun z ⟨_, hz⟩ ↦ (hmM z.2 hz (D z)).2
  have h₄ : m * ∫ z in R, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
      (2 + 2 * B ^ 2) * C₀ * M * ∫ z in R, ‖D z‖ ^ 2 := by
    calc _ ≤ _ := h₂
      _ ≤ (2 + 2 * B ^ 2) * (C₀ * (M * ∫ z in R, ‖D z‖ ^ 2)) := by
        gcongr
        exact h₁.trans (by gcongr)
      _ = _ := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  linarith

/-- **The semi-Fredholm estimate of the linearized Floer operator along a Floer cylinder.**
Let `H` be a one-periodic, jointly `C²` Hamiltonian whose suspended vector field is globally
Lipschitz, with nondegenerate one-periodic orbits `x₋` and `x₊`, and let `J_t(y)` be a `C¹` family
of almost complex structures, compatible with `ω` along `x₋`, `x₊` and the `C¹` map `u`. Suppose
that the loops of `u` converge uniformly to `x₋` as `s → -∞` and to `x₊` as `s → ∞`, while the
slice defect `∂t u - X_{H_t}(u)` tends uniformly to zero, as for a Floer cylinder from `x₋` to
`x₊`. Then there are constants `C ≥ 0` and `T` such that every `C²` map `ξ` of period one in `t`
that vanishes for `s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`,

the first two integrals over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the
datum `K = H_t dt`. The constants do not depend on `a`, `b` or `ξ`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_setIntegral
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) (hHp : Function.Periodic H 1) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hxmp : Function.Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
    (hxpp : Function.Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u)
    (hJu : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, ω.Compatible (J t (u (s, t))))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, (∀ z : ℝ × ℝ, z.1 ∉ Ioo a b → ξ z = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc 0 1,
              ‖ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
                (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2) := by
  -- Outline: the end estimates hold beyond `R₀` and below `-R₀`, the interior estimate on
  -- `[-T, T]` with `T = R₀ + 1`. Cutoffs `βp`, `βm`, `β₀` with `βp + βm + β₀ = 1` split `ξ` into
  -- three pieces, each supported where one estimate applies; the cutoffs only add the terms
  -- `β' ξ` to `D_u`, supported in `[-T, T]`. All integrals are compared on one window `W`.
  set D := ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
    (fun _ _ ↦ 0) (fun w ↦ H w.2) u with hDdef
  -- The estimates on the two ends hold beyond `R₀` and below `-R₀`.
  obtain ⟨Cp, hCp, Up, hUp, hestp⟩ :=
    exists_mem_forall_setIntegral_norm_sq_le_mul_setIntegral_floerLinearization ω hX hH hHp hxp
      hxpp hndp hJ hJxp hu huxp hδp
  obtain ⟨Cm, hCm, Um, hUm, hestm⟩ :=
    exists_mem_forall_setIntegral_norm_sq_le_mul_setIntegral_floerLinearization ω hX hH hHp hxm
      hxmp hndm hJ hJxm hu huxm hδm
  obtain ⟨Tp, hTp⟩ := mem_atTop_sets.1 hUp
  obtain ⟨Tm, hTm⟩ := mem_atBot_sets.1 hUm
  set R₀ := max (max Tp (-Tm)) 0
  have hR₀0 : 0 ≤ R₀ := le_max_right _ _
  have hR₀p : Tp ≤ R₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hR₀m : -Tm ≤ R₀ := (le_max_right _ _).trans (le_max_left _ _)
  set T := R₀ + 1
  -- The interior estimate on `[-T, T] × [0, 1]`.
  obtain ⟨C₀, hC₀, hest₀⟩ := exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add ω
    (J := fun z y ↦ J z.2 y) (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd))
    (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2) contDiff_const
    (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)) (c := -T) (d := T)
    (fun _ _ ↦ hu.contDiffAt) fun z hz ↦ hJu z.1 z.2 hz.2
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  refine ⟨6 * Cp + 6 * Cm + 6 * C₀ + (6 * Cp * L ^ 2 + 6 * Cm * L ^ 2 + 24 * C₀ * L ^ 2 +
    3 * C₀ + 3), by positivity, T, fun ξ hξ hper a b hsupp ↦ ?_⟩
  -- All integrals are compared on the window `W = [A, B] × [0, 1]` containing `[a, b]` and
  -- `[-T, T]`.
  set A := min a (-T)
  set B := max b T
  set W := Icc A B ×ˢ Icc (0 : ℝ) 1
  have hAT : A ≤ -T := min_le_right _ _
  have hBT : T ≤ B := le_max_right _ _
  have hAa : A ≤ a := min_le_left _ _
  have hBb : b ≤ B := le_max_left _ _
  have hint {f : ℝ × ℝ → ℝ} (hf : Continuous f) {c d : ℝ} :
      IntegrableOn f (Icc c d ×ˢ Icc 0 1) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  -- Enlarging a window does not change the integral of a function vanishing outside it.
  have hwindow {f : ℝ × ℝ → ℝ} {c d c' d' : ℝ} (hc : c' ≤ c) (hd : d ≤ d')
      (hf : ∀ z : ℝ × ℝ, z.1 < c ∨ d < z.1 → f z = 0) :
      ∫ z in Icc c' d' ×ˢ Icc 0 1, f z = ∫ z in Icc c d ×ˢ Icc 0 1, f z :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_Icc.prod measurableSet_Icc)
      (prod_mono (Icc_subset_Icc hc hd) subset_rfl) fun z hz ↦ hf z (by
        have h : z.1 ∉ Icc c d := fun h ↦ hz.2 ⟨h, hz.1.2⟩
        simpa only [mem_Icc, not_and_or, not_le] using h)
  have hDc {η : ℝ × ℝ → V} (hη : ContDiff ℝ 1 η) : Continuous (D η) :=
    continuous_iff_continuousAt.2 fun z ↦
      ω.continuousAt_floerLinearization
        (J := fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
        (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2)
        (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt contDiffAt_const
        (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt hu.contDiffAt hη.contDiffAt
  have hQc {η : ℝ × ℝ → V} (hη : ContDiff ℝ 1 η) : Continuous fun z ↦
      ‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 +
        ‖η z‖ ^ 2 := by
    have hd := hη.continuous_fderiv one_ne_zero
    exact (((hd.clm_apply continuous_const).norm.pow 2).add
      ((hd.clm_apply continuous_const).norm.pow 2)).add (hη.continuous.norm.pow 2)
  -- A map vanishing for `s ∉ (c, d)` has vanishing integrands for `s < c` and `s > d`.
  have hvanish {η : ℝ × ℝ → V} {c d : ℝ} (hη : ∀ w : ℝ × ℝ, w.1 ∉ Ioo c d → η w = 0)
      {z : ℝ × ℝ} (hz : z.1 < c ∨ d < z.1) :
      ‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 +
          ‖η z‖ ^ 2 = 0 ∧ ‖D η z‖ ^ 2 = 0 := by
    have h : η =ᶠ[𝓝 z] 0 := by
      rcases hz with hz | hz
      · exact eventually_of_mem ((isOpen_lt continuous_fst continuous_const).mem_nhds hz)
          fun w hw ↦ hη w fun hw' ↦ lt_irrefl _ (hw.trans hw'.1)
      · exact eventually_of_mem ((isOpen_lt continuous_const continuous_fst).mem_nhds hz)
          fun w hw ↦ hη w fun hw' ↦ lt_irrefl _ (hw.trans hw'.2)
    refine ⟨?_, ?_⟩
    · rw [h.fderiv_eq, h.eq_of_nhds]
      simp
    · rw [hDdef, floerLinearization_def, h.fderiv_eq, h.eq_of_nhds]
      simp
  -- The cutoffs `βp = 1` far out on the positive end, `βm = 1` on the negative end and
  -- `β₀ = 1 - βp - βm`, supported in `[-T, T]`.
  set βp : ℝ → ℝ := fun s ↦ Real.smoothTransition (s - R₀)
  set βm : ℝ → ℝ := fun s ↦ Real.smoothTransition (-s - R₀)
  set β₀ : ℝ → ℝ := fun s ↦ 1 - βp s - βm s with hβ₀
  have hβpc : ContDiff ℝ 2 βp :=
    Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  have hβmc : ContDiff ℝ 2 βm :=
    Real.smoothTransition.contDiff.comp (contDiff_neg.sub contDiff_const)
  have hβ₀c : ContDiff ℝ 2 β₀ := (contDiff_const.sub hβpc).sub hβmc
  have hβpd (s : ℝ) : deriv βp s = deriv Real.smoothTransition (s - R₀) := by
    simpa using (((hasDerivAt_id s).sub_const R₀).smoothTransition).deriv
  have hβmd (s : ℝ) : deriv βm s = -deriv Real.smoothTransition (-s - R₀) := by
    simpa using (((hasDerivAt_neg s).sub_const R₀).smoothTransition).deriv
  have hβ₀d (s : ℝ) : deriv β₀ s = -deriv βp s - deriv βm s := by
    have h : HasDerivAt β₀ (0 - deriv βp s - deriv βm s) s :=
      ((hasDerivAt_const s (1 : ℝ)).sub (hβpc.differentiable (by norm_num) s).hasDerivAt).sub
        (hβmc.differentiable (by norm_num) s).hasDerivAt
    rw [h.deriv]
    ring
  have hβpT (s : ℝ) (hs : T < |s|) : deriv βp s = 0 := by
    rw [hβpd]
    rcases lt_abs.1 hs with hs | hs
    · exact Real.smoothTransition.deriv_of_one_lt (by linarith)
    · exact Real.smoothTransition.deriv_of_neg (by linarith)
  have hβmT (s : ℝ) (hs : T < |s|) : deriv βm s = 0 := by
    rw [hβmd, neg_eq_zero]
    rcases lt_abs.1 hs with hs | hs
    · exact Real.smoothTransition.deriv_of_neg (by linarith)
    · exact Real.smoothTransition.deriv_of_one_lt (by linarith)
  have hβpL (s : ℝ) : |deriv βp s| ≤ L := by rw [hβpd, ← Real.norm_eq_abs]; exact hL _
  have hβmL (s : ℝ) : |deriv βm s| ≤ L := by
    rw [hβmd, abs_neg, ← Real.norm_eq_abs]; exact hL _
  have hβp0 {s : ℝ} (hs : s ≤ R₀) : βp s = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hβm0 {s : ℝ} (hs : -R₀ ≤ s) : βm s = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  -- The error `D_u (β ξ) - β D_u ξ = β' ξ` of a cutoff is supported in `[-T, T]`.
  have hkey (β : ℝ → ℝ) (L' : ℝ) (hβ : ContDiff ℝ 2 β) (hβ1 : ∀ s, |β s| ≤ 1)
      (hβL : ∀ s, |deriv β s| ≤ L') (hβT : ∀ s, T < |s| → deriv β s = 0) :
      ∫ z in W, ‖D (fun w ↦ β w.1 • ξ w) z‖ ^ 2 ≤
        2 * (∫ z in W, ‖D ξ z‖ ^ 2) + 2 * L' ^ 2 * ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 := by
    have hβ' : Continuous (deriv β) := hβ.continuous_deriv (by norm_num)
    have hη : ContDiff ℝ 2 fun w : ℝ × ℝ ↦ β w.1 • ξ w := (hβ.comp contDiff_fst).smul hξ
    have hξD := hDc (hξ.of_le one_le_two)
    have hc₁ : Continuous fun z : ℝ × ℝ ↦ deriv β z.1 ^ 2 * ‖ξ z‖ ^ 2 :=
      ((hβ'.comp continuous_fst).pow 2).mul (hξ.continuous.norm.pow 2)
    have hpt (z : ℝ × ℝ) : ‖D (fun w ↦ β w.1 • ξ w) z‖ ^ 2 ≤
        2 * ‖D ξ z‖ ^ 2 + 2 * (deriv β z.1 ^ 2 * ‖ξ z‖ ^ 2) := by
      rw [hDdef, floerLinearization_smul_fst _ _ _ _ _ _ (hβ.differentiable (by norm_num) _)
        (hξ.differentiable (by norm_num) _), ← hDdef]
      have h₁ : ‖β z.1 • D ξ z + deriv β z.1 • ξ z‖ ≤ ‖D ξ z‖ + |deriv β z.1| * ‖ξ z‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
        exact mul_le_of_le_one_left (norm_nonneg _) (hβ1 _)
      have h₂ := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
      nlinarith [sq_nonneg (‖D ξ z‖ - |deriv β z.1| * ‖ξ z‖), sq_abs (deriv β z.1)]
    have hE : ∫ z in W, deriv β z.1 ^ 2 * ‖ξ z‖ ^ 2 =
        ∫ z in Icc (-T) T ×ˢ Icc 0 1, deriv β z.1 ^ 2 * ‖ξ z‖ ^ 2 :=
      hwindow hAT hBT fun z hz ↦ by
        rw [hβT z.1 (by
          rcases hz with hz | hz
          · exact lt_abs.2 (Or.inr (by linarith))
          · exact lt_abs.2 (Or.inl hz))]
        simp
    have hle : ∫ z in Icc (-T) T ×ˢ Icc 0 1, deriv β z.1 ^ 2 * ‖ξ z‖ ^ 2 ≤
        L' ^ 2 * ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on (hint hc₁) (hint (continuous_const.mul
        (hξ.continuous.norm.pow 2))) (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ ?_
      have h := pow_le_pow_left₀ (abs_nonneg _) (hβL z.1) 2
      rw [sq_abs] at h
      exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
    have i₁ : IntegrableOn (fun z : ℝ × ℝ ↦ 2 * ‖D ξ z‖ ^ 2) W :=
      hint (continuous_const.mul (hξD.norm.pow 2))
    have i₂ : IntegrableOn (fun z : ℝ × ℝ ↦ 2 * (deriv β z.1 ^ 2 * ‖ξ z‖ ^ 2)) W :=
      hint (continuous_const.mul hc₁)
    have h₁ : ∫ z in W, ‖D (fun w ↦ β w.1 • ξ w) z‖ ^ 2 ≤
        2 * (∫ z in W, ‖D ξ z‖ ^ 2) + 2 * ∫ z in W, deriv β z.1 ^ 2 * ‖ξ z‖ ^ 2 := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add i₁ i₂]
      exact setIntegral_mono_on (hint ((hDc (hη.of_le one_le_two)).norm.pow 2)) (i₁.add i₂)
        (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ hpt z
    rw [hE] at h₁
    refine h₁.trans ?_
    rw [mul_assoc 2 (L' ^ 2)]
    gcongr
  -- Bounds on the cutoffs.
  have hβp1 (s : ℝ) : |βp s| ≤ 1 := Real.smoothTransition.abs_le_one _
  have hβm1 (s : ℝ) : |βm s| ≤ 1 := Real.smoothTransition.abs_le_one _
  have hβp1' {s : ℝ} (hs : T ≤ s) : βp s = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  have hβm1' {s : ℝ} (hs : s ≤ -T) : βm s = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hβ₀1 (s : ℝ) : |β₀ s| ≤ 1 := by
    have h₁ : 0 ≤ βp s := Real.smoothTransition.nonneg _
    have h₂ : βp s ≤ 1 := Real.smoothTransition.le_one _
    have h₃ : 0 ≤ βm s := Real.smoothTransition.nonneg _
    have h₄ : βm s ≤ 1 := Real.smoothTransition.le_one _
    rw [abs_le]
    rcases le_or_gt s R₀ with hs | hs
    · constructor <;> simp only [hβ₀] <;> linarith [hβp0 hs]
    · constructor <;> simp only [hβ₀] <;> linarith [hβm0 (by linarith : -R₀ ≤ s)]
  have hβ₀L (s : ℝ) : |deriv β₀ s| ≤ 2 * L := by
    rw [hβ₀d, sub_eq_add_neg, ← neg_add, abs_neg]
    linarith [abs_add_le (deriv βp s) (deriv βm s), hβpL s, hβmL s]
  have hβ₀T (s : ℝ) (hs : T < |s|) : deriv β₀ s = 0 := by
    rw [hβ₀d, hβpT s hs, hβmT s hs]
    ring
  -- The three pieces `ξ = βp ξ + βm ξ + β₀ ξ` and their supports.
  set ηp : ℝ × ℝ → V := fun w ↦ βp w.1 • ξ w with hηp
  set ηm : ℝ × ℝ → V := fun w ↦ βm w.1 • ξ w with hηm
  set η₀ : ℝ × ℝ → V := fun w ↦ β₀ w.1 • ξ w with hη₀
  have hηpc : ContDiff ℝ 2 ηp := (hβpc.comp contDiff_fst).smul hξ
  have hηmc : ContDiff ℝ 2 ηm := (hβmc.comp contDiff_fst).smul hξ
  have hη₀c : ContDiff ℝ 2 η₀ := (hβ₀c.comp contDiff_fst).smul hξ
  have hξa {w : ℝ × ℝ} (hw : w.1 ≤ a ∨ b ≤ w.1) : ξ w = 0 :=
    hsupp w fun h ↦ by rcases hw with hw | hw <;> linarith [h.1, h.2]
  have hsuppp (w : ℝ × ℝ) (hw : w.1 ∉ Ioo R₀ B) : ηp w = 0 := by
    simp only [mem_Ioo, not_and_or, not_lt] at hw
    rcases hw with hw | hw
    · simp only [hηp, hβp0 hw, zero_smul]
    · simp only [hηp, hξa (Or.inr (hBb.trans hw)), smul_zero]
  have hsuppm (w : ℝ × ℝ) (hw : w.1 ∉ Ioo A (-R₀)) : ηm w = 0 := by
    simp only [mem_Ioo, not_and_or, not_lt] at hw
    rcases hw with hw | hw
    · simp only [hηm, hξa (Or.inl (hw.trans hAa)), smul_zero]
    · simp only [hηm, hβm0 hw, zero_smul]
  have hsupp₀ (w : ℝ × ℝ) (hw : w.1 ∉ Ioo (-T) T) : η₀ w = 0 := by
    simp only [mem_Ioo, not_and_or, not_lt] at hw
    have h : β₀ w.1 = 0 := by
      rcases hw with hw | hw
      · simp only [hβ₀, hβp0 (by linarith : w.1 ≤ R₀), hβm1' hw]
        ring
      · simp only [hβ₀, hβp1' hw, hβm0 (by linarith : -R₀ ≤ w.1)]
        ring
    simp only [hη₀, h, zero_smul]
  have hperη (β : ℝ → ℝ) (s t : ℝ) : β (s, t + 1).1 • ξ (s, t + 1) = β (s, t).1 • ξ (s, t) := by
    simp only [hper]
  -- Moving integrals between windows inside `W`.
  have htransfer {η : ℝ × ℝ → V} {c d : ℝ} (hη : ∀ w : ℝ × ℝ, w.1 ∉ Ioo c d → η w = 0)
      (hc : A ≤ c) (hd : d ≤ B) :
      (∫ z in W, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2)) =
        (∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2)) ∧
      (∫ z in W, ‖D η z‖ ^ 2) = ∫ z in Icc c d ×ˢ Icc 0 1, ‖D η z‖ ^ 2 :=
    ⟨hwindow hc hd fun z hz ↦ (hvanish hη hz).1,
      hwindow hc hd fun z hz ↦ (hvanish hη hz).2⟩
  -- The positive end.
  have hp : (∫ z in W, (‖fderiv ℝ ηp z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ηp z stdComplexLineImag‖ ^ 2 + ‖ηp z‖ ^ 2)) ≤ Cp * ∫ z in W, ‖D ηp z‖ ^ 2 := by
    obtain ⟨e₁, e₂⟩ := htransfer hsuppp (by linarith) le_rfl
    rw [e₁, e₂]
    exact hestp hηpc (hperη βp) (by linarith) (fun s hs ↦ hTp s (by linarith [hs.1]))
      (fun t ↦ hsuppp _ (by simp)) (fun t ↦ hsuppp _ (by simp))
  -- The negative end.
  have hm : (∫ z in W, (‖fderiv ℝ ηm z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ηm z stdComplexLineImag‖ ^ 2 + ‖ηm z‖ ^ 2)) ≤ Cm * ∫ z in W, ‖D ηm z‖ ^ 2 := by
    obtain ⟨e₁, e₂⟩ := htransfer hsuppm le_rfl (by linarith)
    rw [e₁, e₂]
    exact hestm hηmc (hperη βm) (by linarith) (fun s hs ↦ hTm s (by linarith [hs.2]))
      (fun t ↦ hsuppm _ (by simp)) (fun t ↦ hsuppm _ (by simp))
  -- The compact core.
  have h₀ : (∫ z in W, (‖fderiv ℝ η₀ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ η₀ z stdComplexLineImag‖ ^ 2 + ‖η₀ z‖ ^ 2)) ≤
      C₀ * ((∫ z in W, ‖D η₀ z‖ ^ 2) + ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2) +
        ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 := by
    obtain ⟨e₁, e₂⟩ := htransfer hsupp₀ hAT hBT
    rw [e₁, e₂]
    have hcore : (∫ z in Icc (-T) T ×ˢ Icc 0 1, (‖fderiv ℝ η₀ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η₀ z stdComplexLineImag‖ ^ 2)) ≤
        C₀ * ∫ z in Icc (-T) T ×ˢ Icc 0 1, (‖D η₀ z‖ ^ 2 + ‖η₀ z‖ ^ 2) :=
      hest₀ (fun z _ ↦ hη₀c.contDiffAt) (fun s _ ↦ by simpa using hperη β₀ s 0)
        (fun t _ ↦ hsupp₀ _ (by simp)) (fun t _ ↦ hsupp₀ _ (by simp))
    have hd₀ := hη₀c.continuous_fderiv (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hi₁ : IntegrableOn (fun z ↦ ‖fderiv ℝ η₀ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η₀ z stdComplexLineImag‖ ^ 2) (Icc (-T) T ×ˢ Icc 0 1) :=
      hint (((hd₀.clm_apply continuous_const).norm.pow 2).add
        ((hd₀.clm_apply continuous_const).norm.pow 2))
    have hi₂ : IntegrableOn (fun z ↦ ‖η₀ z‖ ^ 2) (Icc (-T) T ×ˢ Icc 0 1) :=
      hint (hη₀c.continuous.norm.pow 2)
    have hi₃ : IntegrableOn (fun z ↦ ‖D η₀ z‖ ^ 2) (Icc (-T) T ×ˢ Icc 0 1) :=
      hint ((hDc (hη₀c.of_le one_le_two)).norm.pow 2)
    have hηξ : ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖η₀ z‖ ^ 2 ≤
        ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 :=
      setIntegral_mono_on hi₂ (hint (hξ.continuous.norm.pow 2))
        (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ by
          simp only [hη₀, norm_smul, Real.norm_eq_abs, mul_pow]
          exact mul_le_of_le_one_left (sq_nonneg _) (by
            simpa [sq_abs] using pow_le_one₀ (abs_nonneg _) (hβ₀1 z.1) (n := 2))
    rw [integral_add hi₁ hi₂]
    rw [integral_add hi₃ hi₂] at hcore
    nlinarith [mul_le_mul_of_nonneg_left hηξ hC₀]
  -- Splitting `ξ` into the three pieces costs a factor `3`.
  have hdecomp : ξ = fun w ↦ ηp w + ηm w + η₀ w := funext fun w ↦ by
    simp only [hηp, hηm, hη₀, hβ₀]
    module
  have hdiff {η : ℝ × ℝ → V} (hη : ContDiff ℝ 2 η) (z : ℝ × ℝ) : DifferentiableAt ℝ η z :=
    hη.differentiable (by norm_num) z
  have hdξ (z : ℝ × ℝ) :
      fderiv ℝ ξ z = fderiv ℝ ηp z + fderiv ℝ ηm z + fderiv ℝ η₀ z := by
    conv_lhs => rw [hdecomp]
    exact (((hdiff hηpc z).hasFDerivAt.add (hdiff hηmc z).hasFDerivAt).add
      (hdiff hη₀c z).hasFDerivAt).fderiv
  have hS : (∫ z in W, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2)) ≤
      3 * ((∫ z in W, (‖fderiv ℝ ηp z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ηp z stdComplexLineImag‖ ^ 2 + ‖ηp z‖ ^ 2)) +
      (∫ z in W, (‖fderiv ℝ ηm z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ηm z stdComplexLineImag‖ ^ 2 + ‖ηm z‖ ^ 2)) +
      ∫ z in W, (‖fderiv ℝ η₀ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η₀ z stdComplexLineImag‖ ^ 2 + ‖η₀ z‖ ^ 2)) := by
    have ip := hint (hQc (hηpc.of_le one_le_two)) (c := A) (d := B)
    have im := hint (hQc (hηmc.of_le one_le_two)) (c := A) (d := B)
    have i₀ := hint (hQc (hη₀c.of_le one_le_two)) (c := A) (d := B)
    have ipm := Integrable.fun_add ip im
    rw [← integral_add ip im, ← integral_add ipm i₀, ← integral_const_mul]
    refine setIntegral_mono_on (hint (hQc (hξ.of_le one_le_two)))
      ((ipm.fun_add i₀).const_mul 3) (measurableSet_Icc.prod measurableSet_Icc)
      fun z _ ↦ ?_
    have hsq3 (p q r : V) : ‖p + q + r‖ ^ 2 ≤ 3 * (‖p‖ ^ 2 + ‖q‖ ^ 2 + ‖r‖ ^ 2) := by
      have h₀ := pow_le_pow_left₀ (norm_nonneg _) (norm_add₃_le (a := p) (b := q) (c := r)) 2
      nlinarith [sq_nonneg (‖p‖ - ‖q‖), sq_nonneg (‖q‖ - ‖r‖), sq_nonneg (‖p‖ - ‖r‖)]
    have hv : ξ z = ηp z + ηm z + η₀ z := congrFun hdecomp z
    rw [hdξ z, hv]
    simp only [add_apply]
    nlinarith [hsq3 (fderiv ℝ ηp z stdComplexLineReal)
      (fderiv ℝ ηm z stdComplexLineReal) (fderiv ℝ η₀ z stdComplexLineReal),
      hsq3 (fderiv ℝ ηp z stdComplexLineImag)
      (fderiv ℝ ηm z stdComplexLineImag) (fderiv ℝ η₀ z stdComplexLineImag),
      hsq3 (ηp z) (ηm z) (η₀ z)]
  -- The errors of the cutoffs.
  have hkp : ∫ z in W, ‖D ηp z‖ ^ 2 ≤ 2 * (∫ z in W, ‖D ξ z‖ ^ 2) +
      2 * L ^ 2 * ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 := hkey βp L hβpc hβp1 hβpL hβpT
  have hkm : ∫ z in W, ‖D ηm z‖ ^ 2 ≤ 2 * (∫ z in W, ‖D ξ z‖ ^ 2) +
      2 * L ^ 2 * ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 := hkey βm L hβmc hβm1 hβmL hβmT
  have hk₀ : ∫ z in W, ‖D η₀ z‖ ^ 2 ≤ 2 * (∫ z in W, ‖D ξ z‖ ^ 2) +
      2 * (2 * L) ^ 2 * ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 :=
    hkey β₀ (2 * L) hβ₀c hβ₀1 hβ₀L hβ₀T
  -- Back to the window `[a, b] × [0, 1]` of the statement.
  obtain ⟨e₁, e₂⟩ := htransfer hsupp hAa hBb
  rw [← e₁, ← e₂]
  have hID : 0 ≤ ∫ z in W, ‖D ξ z‖ ^ 2 := setIntegral_nonneg (measurableSet_Icc.prod
    measurableSet_Icc) fun _ _ ↦ sq_nonneg _
  have hIT : 0 ≤ ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 := setIntegral_nonneg
    (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ sq_nonneg _
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  nlinarith [mul_le_mul_of_nonneg_left hkp hCp, mul_le_mul_of_nonneg_left hkm hCm,
    mul_le_mul_of_nonneg_left hk₀ hC₀, mul_nonneg (mul_nonneg hCp hL2) hID,
    mul_nonneg (mul_nonneg hCm hL2) hID, mul_nonneg (mul_nonneg hC₀ hL2) hID,
    mul_nonneg hC₀ hID, mul_nonneg hCp hIT, mul_nonneg hCm hIT, mul_nonneg hC₀ hIT]

end TauCeti.SymplecticForm

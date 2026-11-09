/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Breaking
public import TauCeti.Geometry.Symplectic.Floer.CylindricalEnd
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# Translates of finite-energy Floer half-cylinders converge to orbit cylinders

Let `(V, ω)` be a symplectic vector space and let `u` solve the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on the half-cylinder `s > a`, for the cylindrical perturbation
`K = H_t dt` of a `1`-periodic Hamiltonian `H`, with `1`-periodic loops `t ↦ u(s, t)` in a compact
set and finite energy. This is the situation on a cylindrical end of a punctured Floer domain, read
in a coordinate chart of the target. The almost complex structures `J(z, x)` are `C²`, tamed by
`ω`, and periodic under `z ↦ z + (1, 0)` and `z ↦ z + (0, 1)`; Floer data that are cylindrical on
the end, `J = J_t`, are of this form.

The first result is that the derivative of `u` is bounded on every half-cylinder `s ≥ b` with
`b > a` (`TauCeti.SymplecticForm.exists_forall_norm_fderiv_le_of_floer`). This is
`TauCeti.Floer.exists_forall_norm_fderiv_le_of_lintegral_ne_top` from
`TauCeti.Geometry.Symplectic.Floer.CylindricalEnd`, transported from the complex coordinate form of
the equation used there to the form `(du - X_K)^{0,1} = 0` in which the Floer energy identity and
the half-cylinder results of `TauCeti.Geometry.Symplectic.Floer.HalfCylinder` are stated. For the
cylindrical perturbation `X_{K_s} = 0`, so the Floer energy density bounds `‖∂_s u‖²` up to the
taming constant, and finite Floer energy gives the finite energy `∫ ‖∂_s u‖²` that the mean-value
argument needs. The taming and norm constants of `J` are uniform by periodicity.

The second result concerns domain-dependent almost complex structures `J(z)`
(`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoLocallyUniformly_comp_add_of_floer`):
for every sequence `s_n → ∞`, a subsequence of the translates `(s, t) ↦ u(s + s_n, t)` converges
locally uniformly on `ℝ × ℝ` to the stationary cylinder `(s, t) ↦ x(t)` over a `1`-periodic orbit
`x' = X_{H_t}(x)`. This is the step of Floer breaking at an end that extracts an orbit. The uniform
derivative bound makes `u` Lipschitz on `s ≥ a + 1`, so the Arzelà–Ascoli theorem for translates
along a half-plane (`TauCeti.exists_tendstoLocallyUniformly_comp_add_subseq_of_lipschitzOnWith`)
extracts a locally uniformly convergent subsequence. Its limit is identified as an orbit cylinder
by `TauCeti.SymplecticForm.eq_of_tendstoLocallyUniformlyOn_comp_add` and
`TauCeti.SymplecticForm.hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add` from
`TauCeti.Geometry.Symplectic.Floer.Breaking`, which assume the convergence of the translates, and
then on all of `ℝ × ℝ` by periodicity. No nondegeneracy of the orbits is assumed, so the orbit may
depend on the sequence.

## Main results

* `TauCeti.SymplecticForm.exists_forall_norm_fderiv_le_of_floer`: finite-energy Floer
  half-cylinders have bounded derivative away from the boundary of the end.
* `TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoLocallyUniformly_comp_add_of_floer`:
  every sequence of translates along the end has a subsequence converging locally uniformly to
  the stationary cylinder over a periodic Hamiltonian orbit.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer cylinders and their limits at the ends.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 4.5 and the
  chapter on Floer homology.
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology
open scoped ENNReal NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {u : ℝ × ℝ → V} {K : Set V} {a b : ℝ}

/-- Uniform taming and norm constants for continuous almost complex structures `J(z, x)` that are
periodic in the domain point `z` under `z ↦ z + (1, 0)` and `z ↦ z + (0, 1)`, over a compact set
of target points. -/
private theorem exists_pos_forall_of_periodic {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : Continuous fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJs : ∀ x, Periodic (fun z ↦ J z x) (1, 0)) (hJt : ∀ x, Periodic (fun z ↦ J z x) (0, 1))
    (hK : IsCompact K) (hJK : ∀ z, ∀ x ∈ K, ω.Tames (J z x)) :
    ∃ c > 0, ∃ M, ∀ z, ∀ x ∈ K, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z x v) ∧ ‖J z x v‖ ≤ M * ‖v‖ := by
  set Jc : (ℝ × ℝ) × V → V →L[ℝ] V := fun p ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap
  set D : Set ((ℝ × ℝ) × V) := (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ K
  have hT : IsCompact (Jc '' D) := ((isCompact_Icc.prod isCompact_Icc).prod hK).image hJ
  obtain ⟨c, hc, hcT⟩ := hT.exists_pos_forall_mul_norm_sq_le_compRight
    ω.toBilinForm.toContinuousBilinearMap (by
      rintro _ ⟨p, hp, rfl⟩ v hv
      simpa [Jc] using hJK p.1 p.2 hp.2 v hv)
  obtain ⟨M, hM⟩ := hT.isBounded.exists_norm_le
  refine ⟨c, hc, M, fun z x hx v ↦ ?_⟩
  set w : ℝ × ℝ := (Int.fract z.1, Int.fract z.2)
  have hw : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    ⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hp : Jc (w, x) ∈ Jc '' D := ⟨(w, x), ⟨hw, hx⟩, rfl⟩
  rw [← (hJs x).apply_fract_fract (hJt x) z]
  refine ⟨by simpa [Jc] using hcT _ hp v, ?_⟩
  simpa [Jc] using ((Jc (w, x)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hM _ hp) (norm_nonneg v))

/-- For the cylindrical perturbation `K = H_t dt` and almost complex structures with a uniform
taming constant, a solution of the Floer equation of finite Floer energy over the half-strip
`(a, ∞) × [0, 1]` has finite energy `∫ ‖∂_s u‖²` there: since `X_{K_s} = 0`, the Floer energy
density bounds `‖∂_s u‖²` up to the taming constant. -/
private theorem lintegral_norm_fderiv_sq_ne_top_of_floer {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {c : ℝ} (hc : 0 < c) (hJc : ∀ z ∈ Ioi a ×ˢ univ, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z (u z) v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ univ, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z (u z)) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ‖fderiv ℝ u z (1, 0)‖ₑ ^ 2 ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 2 / c)) hE) ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' (measurableSet_Ioi.prod measurableSet_Icc) fun z hz ↦ ?_
  have hzU : z ∈ Ioi a ×ˢ (univ : Set ℝ) := ⟨hz.1, mem_univ _⟩
  have h := ω.norm_fderiv_stdComplexLineReal_sq_le hc (hJc z hzU) (hfloer z hzU)
  rw [hamiltonianVectorField_const, Pi.zero_apply, norm_zero, stdComplexLineReal_eq] at h
  rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by simpa using h)

/-- **Finite-energy Floer half-cylinders have bounded derivative.** Let `H` be a `C³` Hamiltonian,
`1`-periodic in time, and let `J(z, x)` be `C²` almost complex structures, periodic in `z` under
`z ↦ z + (1, 0)` and `z ↦ z + (0, 1)` and tamed by `ω` at the points of a compact set `K`. Let
`u` be `C³` on the half-cylinder `s > a`, with `1`-periodic loops `t ↦ u(s, t)` in `K`, and solve
the Floer equation `∂_s u + J(z, u) (∂_t u - X_{H_t}(u)) = 0` there, with finite energy over
`(a, ∞) × [0, 1]`. Then the derivative of `u` is bounded on the half-cylinder `s ≥ b` for every
`b > a`. -/
theorem exists_forall_norm_fderiv_le_of_floer {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1)
    (hJ : ContDiff ℝ 2 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJs : ∀ x, Periodic (fun z ↦ J z x) (1, 0)) (hJt : ∀ x, Periodic (fun z ↦ J z x) (0, 1))
    (hJK : ∀ z, ∀ x ∈ K, ω.Tames (J z x)) (hab : a < b)
    (hu : ContDiffOn ℝ 3 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (hK : IsCompact K)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hfloer : ∀ z ∈ Ioi a ×ˢ univ, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z (u z)) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ C, ∀ z ∈ Ici b ×ˢ univ, ‖fderiv ℝ u z‖ ≤ C := by
  -- We extend `u` to a map that is `1`-periodic in `t` on all of `ℝ × ℝ`, read it in the complex
  -- coordinate, check the hypotheses of `Floer.exists_forall_norm_fderiv_le_of_lintegral_ne_top`
  -- there, and transport its bound back. A uniform taming constant turns finite Floer energy into
  -- finite energy `∫ ‖∂ₛu‖²`.
  obtain ⟨c, hc, _, hcM⟩ := exists_pos_forall_of_periodic hJ.continuous hJs hJt hK hJK
  set U : Set (ℝ × ℝ) := Ioi a ×ˢ univ
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have heU {y : ℂ} (hy : a < y.re) : equivRealProdCLM y ∈ U := ⟨hy, mem_univ _⟩
  -- Extend `u` to the left of the end so that it is `1`-periodic in `t` everywhere.
  set ue : ℝ × ℝ → V := fun z ↦ if a < z.1 then u z else u (a + 1, z.2)
  have hueeq {z : ℝ × ℝ} (hz : a < z.1) : ue z = u z := by simp [ue, hz]
  have hueU : ∀ z ∈ U, ue =ᶠ[𝓝 z] u := fun z hz ↦
    Filter.mem_of_superset (hUo.mem_nhds hz) fun w hw ↦ hueeq hw.1
  have hueper (z : ℝ × ℝ) : ue (z + (0, 1)) = ue z := by
    obtain ⟨s, t⟩ := z
    by_cases hs : a < s
    · simpa [ue, hs] using hper s hs t
    · simpa [ue, hs] using hper (a + 1) (lt_add_one a) t
  -- The data of the complex coordinate form of the equation.
  set Ks : ℝ × ℝ → V → ℝ := fun _ _ ↦ 0
  set Kt : ℝ × ℝ → V → ℝ := fun w ↦ H w.2
  set X : ℂ × V → ℂ →L[ℝ] V := fun q ↦
    ω.hamiltonianOneForm Ks Kt (equivRealProdCLM q.1) q.2 ∘L (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)
  set Jc : ℂ × V → V →L[ℝ] V :=
    fun q ↦ (J (equivRealProdCLM q.1) q.2).toLinearMap.toContinuousLinearMap
  have hg : ContDiff ℝ 2 fun q : ℂ × V ↦ (equivRealProdCLM q.1, q.2) :=
    (equivRealProdCLM.contDiff.comp contDiff_fst).prodMk contDiff_snd
  have he1 (y : ℂ) : equivRealProdCLM (y + 1) = equivRealProdCLM y + (1, 0) := by simp
  have heI (y : ℂ) : equivRealProdCLM (y + I) = equivRealProdCLM y + (0, 1) := by simp
  have hJc : ContDiffOn ℝ 2 Jc univ := (hJ.comp hg).contDiffOn
  have hXc : ContDiffOn ℝ 2 X univ := by
    have hKs : ContDiffOn ℝ (2 + 1) (uncurry Ks) univ := by
      simpa [Ks, uncurry_def] using (contDiffOn_const (c := (0 : ℝ)))
    have hKt : ContDiffOn ℝ (2 + 1) (uncurry Kt) univ :=
      (hH.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)).contDiffOn
    exact ((ω.contDiffOn_hamiltonianOneForm isOpen_univ hKs hKt).comp hg.contDiffOn
      (mapsTo_univ _ _)).clm_comp contDiffOn_const
  have hJ1 (x : V) : Periodic (fun y ↦ Jc (y, x)) 1 := fun y ↦ by
    simp only [Jc, he1, hJs x _]
  have hJI (x : V) : Periodic (fun y ↦ Jc (y, x)) I := fun y ↦ by
    simp only [Jc, heI, hJt x _]
  have hX1 (x : V) : Periodic (fun y ↦ X (y, x)) 1 := fun y ↦ by
    refine ContinuousLinearMap.ext fun w ↦ ?_
    simp [X, Ks, Kt]
  have hXI (x : V) : Periodic (fun y ↦ X (y, x)) I := fun y ↦ by
    refine ContinuousLinearMap.ext fun w ↦ ?_
    simp [X, Ks, Kt, hHper _]
  have hvc : ContDiffOn ℝ 3 (ue ∘ equivRealProdCLM) {y : ℂ | a < y.re} :=
    (hu.congr fun z hz ↦ hueeq hz.1).comp equivRealProdCLM.contDiff.contDiffOn fun y hy ↦ heU hy
  have hvper : Periodic (ue ∘ equivRealProdCLM) I := fun y ↦ by
    simp only [comp_apply, heI, hueper]
  have hvK (y : ℂ) (hy : a < y.re) : (ue ∘ equivRealProdCLM) y ∈ K := by
    rw [comp_apply, hueeq (heU hy).1]
    exact huK _ hy _
  have hCR (y : ℂ) (hy : a < y.re) :
      fderiv ℝ (ue ∘ equivRealProdCLM) y I - X (y, ue (equivRealProdCLM y)) I =
        Jc (y, ue (equivRealProdCLM y))
          (fderiv ℝ (ue ∘ equivRealProdCLM) y 1 - X (y, ue (equivRealProdCLM y)) 1) := by
    have h := hfloer _ (heU hy)
    rw [← ω.perturbedFDeriv_congr_of_eventuallyEq _ _ (hueU _ (heU hy)),
      ← (hueU _ (heU hy)).eq_of_nhds] at h
    exact ω.fderiv_comp_equivRealProdCLM_I_sub (J := J) h
  have hfin : ∫⁻ y in Ioi a ×ℂ Icc 0 1,
      ‖fderiv ℝ (ue ∘ equivRealProdCLM) y 1‖ₑ ^ 2 ≠ ⊤ := by
    have hS : MeasurableSet (Ioi a ×ˢ Icc (0 : ℝ) 1) := measurableSet_Ioi.prod measurableSet_Icc
    have hcv : ∫⁻ y in Ioi a ×ℂ Icc 0 1, ‖fderiv ℝ (ue ∘ equivRealProdCLM) y 1‖ₑ ^ 2 =
        ∫⁻ z in Ioi a ×ˢ Icc 0 1, ‖fderiv ℝ ue z (1, 0)‖ₑ ^ 2 := by
      simp only [fderiv_comp_equivRealProdCLM_one, stdComplexLineReal_eq,
        ← preimage_equivRealProd_prod]
      exact Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
        equivRealProdCLM.toHomeomorph.measurableEmbedding
        (fun z ↦ ‖fderiv ℝ ue z (1, 0)‖ₑ ^ 2) _
    rw [hcv, setLIntegral_congr_fun hS fun z hz ↦ by rw [(hueU z ⟨hz.1, mem_univ _⟩).fderiv_eq]]
    exact lintegral_norm_fderiv_sq_ne_top_of_floer hc
      (fun z hz w ↦ (hcM z _ (huK _ hz.1 _) w).1) hfloer hE
  obtain ⟨M, hM⟩ := Floer.exists_forall_norm_fderiv_le_of_lintegral_ne_top isOpen_univ hJc hXc hK
    (subset_univ _) (fun y x _ w ↦ by simp [Jc]) hJ1 hJI hX1 hXI hab hvc hvper hCR hvK hfin
  -- Back to the real coordinates.
  refine ⟨M * ‖((equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ).symm : ℝ × ℝ →L[ℝ] ℂ)‖, fun z hz ↦ ?_⟩
  have hzU : z ∈ U := ⟨hab.trans_le hz.1, mem_univ _⟩
  have hvue : (ue ∘ equivRealProdCLM) ∘ (equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ).symm = ue :=
    funext fun w ↦ by simp
  have hd := (equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ).symm.comp_right_fderiv
    (f := ue ∘ equivRealProdCLM) (x := z)
  rw [hvue, (hueU z hzU).fderiv_eq] at hd
  rw [hd]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hM _ ?_) (norm_nonneg _))
  simpa using hz.1

/-- A locally uniform limit `g` of translates `u(· + (s_n, 0))`, `s_n → ∞`, of a finite-energy
Floer half-cylinder with domain-dependent almost complex structures and uniform constants is the
stationary cylinder `(s, t) ↦ x(t)` over a `1`-periodic Hamiltonian orbit `x`. The limit is
identified on the strip `ℝ × [0, 1]` by
`TauCeti.SymplecticForm.eq_of_tendstoLocallyUniformlyOn_comp_add` and
`TauCeti.SymplecticForm.hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add`, and extends to
`ℝ × ℝ` by periodicity. -/
private theorem exists_periodic_hasDerivAt_eq_of_tendstoLocallyUniformly_comp_add
    {J : ℝ × ℝ → AlmostComplexStructure V} {c M : ℝ}
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc (0 : ℝ) 1, ∀ w, c * ‖w‖ ^ 2 ≤ ω w (J z w))
    (hJM : ∀ z ∈ Ioi a ×ˢ Icc (0 : ℝ) 1, ∀ w, ‖J z w‖ ≤ M * ‖w‖)
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc (0 : ℝ) 1, IsComplexLinearMap
      (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) {g : C(ℝ × ℝ, V)}
    (hg : TendstoLocallyUniformly (fun n z ↦ u (z + (s n, 0))) g atTop) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∀ z, g z = x z.2 := by
  have hUo : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hEU : Ioi a ×ˢ Icc (0 : ℝ) 1 ⊆ Ioi a ×ˢ univ := prod_mono le_rfl (subset_univ _)
  have hW : ∀ α β : ℝ, ∀ᶠ k in atTop,
      Icc (α + s k) (β + s k) ×ˢ Icc (0 : ℝ) 1 ⊆ Ioi a ×ˢ Icc 0 1 := fun α β ↦
    (hs.eventually_gt_atTop (a - α)).mono fun k hk z hz ↦
      ⟨show a < z.1 by linarith [hz.1.1], hz.2⟩
  have hsc : Tendsto s atTop (cocompact ℝ) := hs.mono_right atTop_le_cocompact
  have hv : TendstoLocallyUniformlyOn (fun k z ↦ u (z + (s k, 0))) g atTop
      ((univ : Set ℝ) ×ˢ Icc 0 1) := hg.tendstoLocallyUniformlyOn
  have hstat := eq_of_tendstoLocallyUniformlyOn_comp_add hUo hu hEU hc hJc hJM hfloer hE hsc hW hv
  have hder := hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add hH hUo hu hEU hc hJc hJM
    hfloer hE hsc hW hv
  -- The limit is `1`-periodic in `t`, as a limit of maps that eventually are near each point.
  have hg' := tendstoLocallyUniformlyOn_univ.2 hg
  have hgper (z : ℝ × ℝ) : g (z + (0, 1)) = g z := by
    refine tendsto_nhds_unique (hg'.tendsto_at (mem_univ (z + (0, 1)))) ?_
    refine (hg'.tendsto_at (mem_univ z)).congr' ((hs.eventually_gt_atTop (a - z.1)).mono
      fun n hn ↦ ?_)
    have h₁ : z + (0, 1) + (s n, 0) = (z.1 + s n, z.2 + 1) := by ext <;> simp
    have h₂ : z + (s n, 0) = (z.1 + s n, z.2) := by ext <;> simp
    simp only [h₁, h₂]
    exact (hper (z.1 + s n) (by linarith) z.2).symm
  set x : ℝ → V := fun t ↦ g (0, t)
  have hxper : Periodic x 1 := fun t ↦ by simpa using hgper (0, t)
  have hxc : Continuous x := g.continuous.comp (continuous_const.prodMk continuous_id)
  have hgx (z : ℝ × ℝ) : g z = x z.2 := by
    have hrper : Periodic (fun t ↦ g (z.1, t)) 1 := fun t ↦ by simpa using hgper (z.1, t)
    have hfr : Int.fract z.2 ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    rw [← hrper.apply_fract, ← hxper.apply_fract, hstat z.1 _ hfr]
  -- The orbit equation on `[0, 1]` extends periodically to all times.
  set Y : ℝ → V := fun t ↦ ω.hamiltonianVectorField (H t) (x t) with hY_def
  have hY : Continuous Y :=
    (ω.continuous_uncurry_hamiltonianVectorField hH).comp (continuous_id.prodMk hxc)
  have hYper : Periodic Y 1 := fun t ↦ by simp only [hY_def, hHper t, hxper t]
  have hint : ∀ t ∈ Icc (0 : ℝ) 1, x t - x 0 = ∫ τ in 0..t, Y τ := fun t ht ↦
    (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 hxc.continuousOn
      (fun τ hτ ↦ ((hder τ ⟨hτ.1.le, hτ.2.le.trans ht.2⟩).hasDerivAt
        (Icc_mem_nhds hτ.1 (hτ.2.trans_le ht.2))).hasDerivWithinAt)
      (hY.intervalIntegrable 0 t)).symm
  exact ⟨x, hxper, hasDerivAt_of_periodic_of_sub_eq_integral one_pos hxper hY hYper hint, hgx⟩

/-- **Translates of a finite-energy Floer half-cylinder converge to orbit cylinders.** Let `H` be a
`C³` Hamiltonian, `1`-periodic in time, and let `J(z)` be `C²` almost complex structures tamed by
`ω`, periodic under `z ↦ z + (1, 0)` and `z ↦ z + (0, 1)`. Let `u` be `C³` on the half-cylinder
`s > a`, with `1`-periodic loops `t ↦ u(s, t)` in a compact set, and solve the Floer equation
`∂_s u + J(z) (∂_t u - X_{H_t}(u)) = 0` there, with finite energy over `(a, ∞) × [0, 1]`. Then for
every sequence `s_n → ∞` there are a subsequence `s_{φ n}` and a `1`-periodic orbit `x` of the
Hamiltonian vector field such that the translates `(s, t) ↦ u(s + s_{φ n}, t)` converge locally
uniformly on `ℝ × ℝ` to the stationary cylinder `(s, t) ↦ x(t)`. -/
theorem exists_periodic_hasDerivAt_tendstoLocallyUniformly_comp_add_of_floer
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1)
    (hJ : ContDiff ℝ 2 fun z ↦ (J z).toLinearMap.toContinuousLinearMap)
    (hJs : Periodic J (1, 0)) (hJt : Periodic J (0, 1)) (hJω : ∀ z, ω.Tames (J z))
    (hu : ContDiffOn ℝ 3 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (hK : IsCompact K)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hfloer : ∀ z ∈ Ioi a ×ˢ univ, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ℝ → V, Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoLocallyUniformly (fun n z ↦ u (z + (s (φ n), 0))) (fun z ↦ x z.2) atTop := by
  have hJ' : ContDiff ℝ 2 fun p : (ℝ × ℝ) × V ↦ (J p.1).toLinearMap.toContinuousLinearMap :=
    hJ.comp contDiff_fst
  -- A uniform derivative bound makes `u` Lipschitz on `s ≥ a + 1`.
  obtain ⟨C, hC⟩ := exists_forall_norm_fderiv_le_of_floer (J := fun z _ ↦ J z) hH hHper hJ'
    (fun _ ↦ hJs) (fun _ ↦ hJt) (fun z _ _ ↦ hJω z) (lt_add_one a) hu hper hK huK hfloer hE
  have hUo : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hLip : LipschitzOnWith C.toNNReal u (Ici (a + 1) ×ˢ univ) := by
    refine ((convex_Ici _).prod convex_univ).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      (fun z hz ↦ ?_) fun z hz ↦ ?_
    · have hz' : z ∈ Ioi a ×ˢ (univ : Set ℝ) := ⟨(lt_add_one a).trans_le hz.1, mem_univ _⟩
      exact (hu.differentiableOn (by norm_num) z hz').differentiableAt (hUo.mem_nhds hz')
    · rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact (hC z hz).trans (Real.le_coe_toNNReal C)
  -- Arzelà–Ascoli extracts a locally uniformly convergent subsequence of the translates.
  obtain ⟨φ, hφ, g, hg⟩ := exists_tendstoLocallyUniformly_comp_add_subseq_of_lipschitzOnWith hK
    hLip (fun z hz ↦ huK _ ((lt_add_one a).trans_le hz.1) _) hs
  -- Its limit is the stationary cylinder over a periodic orbit.
  obtain ⟨c, hc, M, hcM⟩ := exists_pos_forall_of_periodic (ω := ω) (K := {0}) hJ'.continuous
    (fun _ ↦ hJs) (fun _ ↦ hJt) isCompact_singleton fun z _ _ ↦ hJω z
  obtain ⟨x, hxper, hx, hgx⟩ := exists_periodic_hasDerivAt_eq_of_tendstoLocallyUniformly_comp_add
    (hH.of_le (by norm_num)) hHper hc (fun z _ w ↦ by simpa using (hcM z 0 rfl w).1)
    (fun z _ w ↦ by simpa using (hcM z 0 rfl w).2) (hu.of_le (by norm_num)) hper
    (fun z hz ↦ hfloer z ⟨hz.1, mem_univ _⟩) hE (hs.comp hφ.tendsto_atTop) hg
  refine ⟨φ, hφ, x, hxper, hx, ?_⟩
  rw [show (fun z : ℝ × ℝ ↦ x z.2) = ⇑g from funext fun z ↦ (hgx z).symm]
  exact hg

end TauCeti.SymplecticForm

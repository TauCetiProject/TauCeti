/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Rescaling.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Quantization
import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Energy quantization of bubbles at frozen structures

A bubble of a sequence of Floer solutions `(du - X_K)^{0,1} = 0` at a bubbling point `z₀` is a
plane `v : ℝ × ℝ → V` which is holomorphic for the almost complex structure `J(z₀, ·)` frozen at
`z₀` (`TauCeti.SymplecticForm.isComplexLinearMap_of_tendsto_rescale`), and its symplectic area is
at most the energy that the sequence concentrates at `z₀`
(`TauCeti.SymplecticForm.lintegral_symplecticForm_le_liminf_of_tendsto_rescale`). This file gives
the lower bound that makes the bubbles countable: a *nonconstant* bubble has area at least a
fixed `η > 0`, with one `η` for all the frozen structures of a compact family.

Let `J p` be almost complex structures on a finite-dimensional inner product space `V`, depending on
a parameter `p` in a normed space, `C²` jointly in `(p, x)` on an open set containing `C × K` for
compact `C` and `K`, and tamed by a linear symplectic form `ω` there. Then there is `η > 0` such
that every nonconstant `C³` plane `v` with image in `K` which is holomorphic for one of the
structures `J p`, `p ∈ C`, has

`η ≤ ∫ ω(∂ₛv, ∂ₜv)`

(`TauCeti.SymplecticForm.exists_pos_forall_ofReal_le_lintegral_of_ne`). For bubbles of Floer
solutions the parameter is the bubbling point `z₀` in a compact window `D` of the domain, possibly
together with the parameter of a family of Floer data; for a sphere tree, bubbles on bubbles are
holomorphic for the same frozen structure. The proof combines the uniform taming constant on the
compact set `C × K`, which gives `ω(∂ₛv, ∂ₜv) = ω(∂ₛv, J ∂ₛv) ≥ c ‖∂ₛv‖²`, with the energy
quantization for compact families of structures
(`TauCeti.exists_pos_forall_le_integral_norm_fderiv_one_sq_of_ne_parametric`), read in the complex
coordinate `Complex.equivRealProdCLM`.

Combined with the area bound of rescaled limits, a nonconstant bubble at a point `z₀ ∈ D` takes at
least `η` of the energy of the sequence near `z₀`: over every disc about `z₀` the Floer energies of
the sequence have limit inferior at least `η`
(`TauCeti.SymplecticForm.exists_pos_forall_ofReal_le_liminf_of_tendsto_rescale`). This is the
lower bound that limits the number of nonconstant bubbles of a sequence of energy at most `E` to
`E / η`; the counting itself is not carried out here.

The regularity of the bubble, `C³` and the convergence of the derivatives of the rescaled maps, is
a hypothesis here; elliptic regularity of the limit is not treated.

## Main results

* `TauCeti.SymplecticForm.exists_pos_forall_ofReal_le_lintegral_of_ne`: nonconstant planes that are
  holomorphic for a structure of a compact family have area at least a uniform `η > 0`.
* `TauCeti.SymplecticForm.exists_pos_forall_ofReal_le_liminf_of_tendsto_rescale`: a nonconstant
  bubble at a point of a compact window takes energy at least `η` from the sequence.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Proposition 4.1.4 (the lower bound for the energy of nonconstant spheres)
  and Sections 4.6 and 8.1 (bubbling for sequences of structures and for Floer solutions).
-/

public section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **Energy quantization for a compact family of frozen structures.** Let `J p (x)` be almost
complex structures, `C²` jointly in `(p, x)` on an open set `W` containing `C × K` for compact `C`
and `K`, and tamed by `ω` on `C × K`. There is `η > 0` such that every nonconstant `C³` plane
`v : ℝ × ℝ → V` with image in `K` that is holomorphic for one of the structures `J p`, `p ∈ C`, has
symplectic area `∫ ω(∂ₛv, ∂ₜv) ≥ η`. -/
theorem exists_pos_forall_ofReal_le_lintegral_of_ne (ω : SymplecticForm V)
    {J : P → V → AlmostComplexStructure V} {W : Set (P × V)} {C : Set P} {K : Set V}
    (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun q : P × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hK : IsCompact K) (hCKW : C ×ˢ K ⊆ W)
    (hJt : ∀ p ∈ C, ∀ x ∈ K, ω.Tames (J p x)) :
    ∃ η > 0, ∀ ⦃p : P⦄, p ∈ C → ∀ ⦃v : ℝ × ℝ → V⦄, ContDiff ℝ 3 v →
      (∀ w, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p (v w))
        (fderiv ℝ v w : ℝ × ℝ →ₗ[ℝ] V)) → range v ⊆ K → ∀ ⦃w w' : ℝ × ℝ⦄, v w ≠ v w' →
      ENNReal.ofReal η ≤ ∫⁻ w, ENNReal.ofReal
        (ω (fderiv ℝ v w stdComplexLineReal) (fderiv ℝ v w stdComplexLineImag)) := by
  set Jc : P × V → V →L[ℝ] V := fun q ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap
  have hCK : IsCompact (C ×ˢ K) := hC.prod hK
  -- A uniform taming constant `c ‖v‖² ≤ ω(v, J p (x) v)` on `C × K`.
  obtain ⟨c, hc, hJc⟩ := hCK.exists_pos_forall_mul_norm_sq_le
    (b := fun q ↦ ((ContinuousLinearMap.compL ℝ V V ℝ).flip (Jc q)).comp
      ω.toBilinForm.toContinuousBilinearMap)
    (((ContinuousLinearMap.compL ℝ V V ℝ).flip.continuous.comp_continuousOn
      (hJ.continuousOn.mono hCKW)).clm_comp continuousOn_const)
    (fun q hq v hv ↦ by simpa [Jc] using hJt q.1 hq.1 q.2 hq.2 v hv)
  -- The energy quantization for the family `J`, as matrix-valued structures on `V`.
  obtain ⟨δ, hδ, hquant⟩ := exists_pos_forall_le_integral_norm_fderiv_one_sq_of_ne_parametric
    (J := fun p x ↦ (J p x).toLinearMap.toContinuousLinearMap) hW hJ hC hK hCKW
    (fun p _ x _ v ↦ by simp)
  refine ⟨c * δ, by positivity, fun p hp v hv hCR hvK w w' hww' ↦ ?_⟩
  have he : MeasurePreserving equivRealProdCLM := Complex.volume_preserving_equiv_real_prod
  have hme : MeasurableEmbedding equivRealProdCLM :=
    equivRealProdCLM.toHomeomorph.measurableEmbedding
  set f : ℝ × ℝ → ℝ := fun y ↦ ‖fderiv ℝ v y stdComplexLineReal‖ ^ 2
  have hfc : Continuous f :=
    ((hv.continuous_fderiv (by norm_num)).clm_apply continuous_const).norm.pow 2
  -- The Cauchy--Riemann equation `∂ₜv = J p (v) ∂ₛv`.
  have hCR' (y : ℝ × ℝ) : fderiv ℝ v y stdComplexLineImag =
      J p (v y) (fderiv ℝ v y stdComplexLineReal) := by
    simpa using (hCR y).apply_stdComplexLineImag
  -- Pointwise, the area density is at least `c` times `‖∂ₛv‖²`.
  have hpt (y : ℝ × ℝ) :
      c * f y ≤ ω (fderiv ℝ v y stdComplexLineReal) (fderiv ℝ v y stdComplexLineImag) := by
    rw [hCR' y]
    simpa [Jc] using hJc (p, v y) ⟨hp, hvK (mem_range_self y)⟩ (fderiv ℝ v y stdComplexLineReal)
  -- The energy `∫ ‖∂ₛv‖²` is at least `δ`.
  have hδf : ENNReal.ofReal δ ≤ ∫⁻ y, ENNReal.ofReal (f y) := by
    by_cases htop : ∫⁻ y, ENNReal.ofReal (f y) = ⊤
    · rw [htop]
      exact le_top
    have hf0 : 0 ≤ᵐ[volume] f := Eventually.of_forall fun _ ↦ by positivity
    have hfi : Integrable f :=
      ⟨hfc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hf0).2 (lt_top_iff_ne_top.2 htop)⟩
    have hu : ContDiff ℝ 3 (v ∘ equivRealProdCLM) := hv.comp equivRealProdCLM.contDiff
    have hfe : (fun z ↦ ‖fderiv ℝ (v ∘ equivRealProdCLM) z 1‖ ^ 2) = f ∘ equivRealProdCLM := by
      funext z
      simp only [Function.comp_apply, f, fderiv_comp_equivRealProdCLM_one]
    have hδle := hquant hp hu
      (fun z ↦ by
        rw [fderiv_comp_equivRealProdCLM_I, fderiv_comp_equivRealProdCLM_one,
          hCR' (equivRealProdCLM z)]
        rfl)
      (by rintro _ ⟨z, rfl⟩; exact hvK (mem_range_self _))
      (by rw [hfe]; exact he.integrable_comp_emb hme |>.2 hfi)
      (z := equivRealProdCLM.symm w) (w := equivRealProdCLM.symm w') (by simpa using hww')
    rw [hfe, Function.comp_def, he.integral_comp hme] at hδle
    rw [← ofReal_integral_eq_lintegral_ofReal hfi hf0]
    exact ENNReal.ofReal_le_ofReal hδle
  calc ENNReal.ofReal (c * δ) = ENNReal.ofReal c * ENNReal.ofReal δ :=
        ENNReal.ofReal_mul hc.le
    _ ≤ ENNReal.ofReal c * ∫⁻ y, ENNReal.ofReal (f y) := by gcongr
    _ = ∫⁻ y, ENNReal.ofReal (c * f y) := by
        rw [← lintegral_const_mul _ (by fun_prop)]
        simp_rw [ENNReal.ofReal_mul hc.le]
    _ ≤ _ := lintegral_mono fun y ↦ ENNReal.ofReal_le_ofReal (hpt y)

/-- **A nonconstant bubble takes energy at least `η`.** Let `J(z, x)` be `C²` on an open set `W`
containing `D × K` for compact `D` and `K`, and tamed by `ω` on `D × K`. There is `η > 0` with the
following property. Let `uᵢ` be `C¹` on an open set `U` containing a point `z₀ ∈ D`, rescaled at
centres `cᵢ → z₀` by scales `εᵢ → 0`, and suppose that the rescaled maps `w ↦ uᵢ(cᵢ + εᵢ w)` and
their derivatives converge pointwise to a `C³` plane `v` with image in `K` and its derivative. If
`v` is holomorphic for the structure `J(z₀, ·)` frozen at `z₀`, as limits of rescaled solutions of
the Floer equation are (`TauCeti.SymplecticForm.isComplexLinearMap_of_tendsto_rescale`), and `v` is
not constant, then for every `δ > 0` the Floer energies of the `uᵢ` over the disc `B_δ(z₀)` have
limit inferior at least `η`. -/
theorem exists_pos_forall_ofReal_le_liminf_of_tendsto_rescale (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)}
    {K : Set V} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ K, ω.Tames (J z x)) :
    ∃ η > 0, ∀ ⦃ι : Type*⦄ ⦃l : Filter ι⦄ [l.NeBot] [l.IsCountablyGenerated]
      ⦃u : ι → ℝ × ℝ → V⦄ ⦃c : ι → ℝ × ℝ⦄ ⦃ε : ι → ℝ⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃U : Set (ℝ × ℝ)⦄
      ⦃v : ℝ × ℝ → V⦄ ⦃Ks Kt : ℝ × ℝ → V → ℝ⦄, z₀ ∈ D → IsOpen U → z₀ ∈ U →
      (∀ i, ContDiffOn ℝ 1 (u i) U) →
      ContDiffOn ℝ 1 (Function.uncurry Ks) (U ×ˢ univ) →
      ContDiffOn ℝ 1 (Function.uncurry Kt) (U ×ˢ univ) →
      Tendsto c l (𝓝 z₀) → Tendsto ε l (𝓝 0) →
      (∀ w, Tendsto (fun i ↦ u i (c i + ε i • w)) l (𝓝 (v w))) →
      (∀ w, Tendsto (fun i ↦ fderiv ℝ (fun w' ↦ u i (c i + ε i • w')) w) l
        (𝓝 (fderiv ℝ v w))) →
      ContDiff ℝ 3 v →
      (∀ w, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z₀ (v w))
        (fderiv ℝ v w : ℝ × ℝ →ₗ[ℝ] V)) → range v ⊆ K →
      ∀ ⦃w w' : ℝ × ℝ⦄, v w ≠ v w' → ∀ ⦃δ : ℝ⦄, 0 < δ →
      ENNReal.ofReal η ≤ liminf (fun i ↦
        ∫⁻ z in Metric.ball z₀ δ, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u i) z)) l := by
  obtain ⟨η, hη, hquant⟩ := ω.exists_pos_forall_ofReal_le_lintegral_of_ne hW hJ hD hK hDKW hJt
  refine ⟨η, hη, fun ι l _ _ u c ε z₀ U v Ks Kt hz₀D hU hz₀ hu hKs hKt hc hε hvlim hdv hv hCR
    hvK w w' hww' δ hδ ↦ ?_⟩
  exact (hquant hz₀D hv hCR hvK hww').trans
    (ω.lintegral_symplecticForm_le_liminf_of_tendsto_rescale hU hz₀ hu hKs hKt hc hε hvlim hdv hδ)

end TauCeti.SymplecticForm

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Rotation
public import TauCeti.Geometry.Symplectic.Floer.Stationary
import TauCeti.Geometry.Symplectic.Floer.Manifold.Limit
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip

/-!
# Limits of translated Floer cylinders in a manifold

Along a cylindrical end of a Floer trajectory, or of a pair of pants, a solution with finite
energy breaks off Hamiltonian orbits. This file shows that whenever the translates of such a
solution further and further along the end converge in the sense specified below, the limit is a
stationary cylinder `(s, t) ↦ x(t)` over a Hamiltonian orbit segment `x`. It treats a manifold
target `M`, such as a closed symplectic manifold, with a nondegenerate two-form `ω`; it assumes the
convergence and does not establish it. It is the manifold counterpart of
`TauCeti.Geometry.Symplectic.Floer.Breaking`, which treats a symplectic vector space.

Let `u` solve the Floer equation `∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` for the cylindrical
perturbation `K = H_t dt` on a part `D` of the strip `ℝ × [0, 1]`, with almost complex
structures `J_t(x)` on `T_x M` independent of `s`, as on a cylindrical end, and let `u` have finite
energy over `D`. Let `s_k` be translation parameters with `|s_k| → ∞` such that every window
`[a + s_k, b + s_k] × [0, 1]` eventually lies in `D`. Suppose that the translates
`z ↦ u(z + (s_k, 0))` converge in `C¹` on the strip to a `C¹` map `v`: at every point of the strip
their derivatives converge in the tangent bundle to the derivative of `v`. This is the form of
convergence that compactness of Floer solutions with bounded derivatives provides. Then:

* the energy densities of the translates converge pointwise to that of `v`, so by Fatou's lemma
  `v` has zero energy over the strip, the energy of `u` over the translated windows tending to
  zero (`SmoothTwoForm.lintegral_floerEnergyDensity_eq_zero_of_tendsto_mfderiv_comp_add`);
* `v` solves the Floer equation on the strip, for the same structures `J_t`
  (`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_of_tendsto_mfderiv_comp_add`);
* hence, for structures tamed by `ω` along `v`, `v` does not depend on `s`
  (`SmoothTwoForm.IsNondegenerate.eq_of_tendsto_mfderiv_comp_add`), by the characterization of
  stationary Floer cylinders by their zero energy
  (`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_zero_iff`);
* `x(t) = v(0, t)` is an orbit segment of the Hamiltonian vector field, `x'(t) = X_{H_t}(x(t))` for
  `t ∈ [0, 1]` (`SmoothTwoForm.IsNondegenerate.hasMFDerivAt_of_tendsto_mfderiv_comp_add`), and the
  perturbed derivative `dv - X_K(v)` vanishes on the strip, so `v` is the stationary Floer cylinder
  over `x` (`SmoothTwoForm.IsNondegenerate.perturbedMFDeriv_eq_zero_of_tendsto_mfderiv_comp_add`).

On a manifold the energy density `ω(∂_s u - X_{K_s}, ∂_t u - X_{K_t})` is intrinsic, but there is
no norm of the derivative without a choice of metric; the convergence of the derivatives is
therefore convergence in the tangent bundle, and the structures `J_t` enter through their
continuity in tangent coordinates (`ContinuousLinearMap.inCoordinates`). The convergence of the
translates, the convergence of the whole end rather than a sequence of translates, and, for ends
with periodic boundary conditions making `x` a loop, the limits of the capped actions of the end
loops are not treated here.

## Main results

* `SmoothTwoForm.lintegral_floerEnergyDensity_eq_zero_of_tendsto_mfderiv_comp_add`: the limit of
  the translates has zero energy over the strip.
* `SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_of_tendsto_mfderiv_comp_add`: the limit of
  the translates is a Floer cylinder.
* `SmoothTwoForm.IsNondegenerate.eq_of_tendsto_mfderiv_comp_add`: the limit of the translates is
  independent of `s`.
* `SmoothTwoForm.IsNondegenerate.hasMFDerivAt_of_tendsto_mfderiv_comp_add`: the limit is a
  Hamiltonian orbit segment.
* `SmoothTwoForm.IsNondegenerate.perturbedMFDeriv_eq_zero_of_tendsto_mfderiv_comp_add`: the limit is
  a stationary Floer cylinder.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer cylinders and their limits at the ends.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 4.5 and the
  chapter on Floer homology, on the removal of the ends of finite-energy solutions.
-/

public section

open Bundle Filter Function MeasureTheory Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E]
  {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ}
  {J : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
  {u v : ℝ × ℝ → M} {s : ℕ → ℝ} {U D : Set (ℝ × ℝ)}

/-- For `K = H_t dt` with `H` jointly `C¹`, the Hamiltonian vector field of the `dt` component of
`K` is continuous on the domain times `M`, as a map into the tangent bundle. -/
private theorem IsNondegenerate.continuous_hamiltonianVectorField_cylindrical
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) :
    Continuous fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField ((fun w : ℝ × ℝ ↦ H w.2) p.1) p.2⟩ : TangentBundle I M) := by
  have hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (0 + 1) (uncurry fun (w : ℝ × ℝ) ↦ H w.2) := by
    rw [zero_add]
    exact hH.comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  exact (hω.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp) hK).continuous

/-- The Hamiltonian vector field of the zero `ds` component of `K = H_t dt` is continuous on the
domain times `M`, as a map into the tangent bundle. -/
private theorem IsNondegenerate.continuous_hamiltonianVectorField_zero (hω : ω.IsNondegenerate) :
    Continuous fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField ((fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ)) p.1) p.2⟩ :
        TangentBundle I M) := by
  have hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (0 + 1)
      (uncurry fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ)) := contMDiff_const
  exact (hω.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp) hK).continuous

/-- The energy of the limit of the translates over a rectangle `[a, b] × [0, 1]` vanishes, by
Fatou's lemma: the energy densities of the translates converge pointwise to that of `v`, and the
energy of `u` over the translated windows `[a + s_k, b + s_k] × [0, 1]` tends to zero. -/
private theorem setLIntegral_Icc_prod_floerEnergyDensity_eq_zero (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hDU : D ⊆ U)
    (hfin : ∫⁻ z in D,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ D)
    (hdu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ e, Tendsto (fun k ↦ (⟨u (z + (s k, 0)),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (s k, 0))) z e⟩ : TangentBundle I M)) atTop
      (𝓝 ⟨v z, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z e⟩)) (a b : ℝ) :
    ∫⁻ z in Icc a b ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) v z) = 0 := by
  set e : (ℝ × ℝ → M) → ℝ × ℝ → ENNReal := fun w z ↦
    ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) w z) with he
  have hXt := hω.continuous_hamiltonianVectorField_cylindrical hH
  have hXs := hω.continuous_hamiltonianVectorField_zero (I := I)
  have hcont : ContinuousOn (e u) U := ENNReal.continuous_ofReal.comp_continuousOn
    (ω.continuousOn_floerEnergyDensity hU hu hXs.continuousOn hXt.continuousOn)
  set W : Set (ℝ × ℝ) := Icc a b ×ˢ Icc 0 1
  have hWm : MeasurableSet W := measurableSet_Icc.prod measurableSet_Icc
  -- The translation `z ↦ z + (c, 0)` preserves the Lebesgue measure of the plane and maps `W`
  -- onto the window `[a + c, b + c] × [0, 1]`.
  have hμ (c : ℝ) : MeasurePreserving (fun z : ℝ × ℝ ↦ z + ((c, 0) : ℝ × ℝ)) volume volume := by
    have hfun : (fun z : ℝ × ℝ ↦ z + ((c, 0) : ℝ × ℝ)) = Prod.map (· + c) id :=
      funext fun z ↦ Prod.ext (by simp) (by simp)
    rw [hfun]
    exact (measurePreserving_add_right volume c).prod (MeasurePreserving.id volume)
  have hpre (c : ℝ) :
      W = (fun z ↦ z + ((c, 0) : ℝ × ℝ)) ⁻¹' (Icc (a + c) (b + c) ×ˢ Icc 0 1) := by
    ext ⟨x, y⟩
    simp only [W, mem_preimage, mem_prod, Prod.mk_add_mk, mem_Icc, add_zero]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h₃⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hW a b)
  have hmem {n : ℕ} {z : ℝ × ℝ} (hz : z ∈ W) : z + (s (n + N), 0) ∈ D := by
    rw [hpre (s (n + N))] at hz
    exact hN (n + N) (Nat.le_add_left N n) hz
  -- Along the tail `k = n + N`, the translated energy densities converge pointwise on `W` to the
  -- energy density of `v`.
  have hlim (z : ℝ × ℝ) (hz : z ∈ W) :
      Tendsto (fun n : ℕ ↦ e u (z + (s (n + N), 0))) atTop (𝓝 (e v z)) := by
    have h := (ENNReal.continuous_ofReal.tendsto _).comp
      (ω.tendsto_floerEnergyDensity (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2)
        (u := fun k w ↦ u (w + (s k, 0))) tendsto_const_nhds
        (hdu z ⟨mem_univ _, hz.2⟩) hXs.continuousAt hXt.continuousAt)
    refine ((tendsto_add_atTop_iff_nat N).2 h).congr fun n ↦ ?_
    simp only [comp_apply, he]
    rw [floerEnergyDensity_cylindrical_comp_add_right]
  -- The energies of `u` over the translated windows tend to zero.
  have hE : Tendsto (fun n : ℕ ↦ ∫⁻ z in W, e u (z + (s (n + N), 0))) atTop (𝓝 0) := by
    have h := tendsto_setLIntegral_of_eventually_subset hfin
      (A := fun k ↦ Icc (a + s k) (b + s k) ×ˢ Icc 0 1)
      (eventually_Icc_add_prod_subset_inter hs (hW a b))
    refine ((tendsto_add_atTop_iff_nat N).2 h).congr fun n ↦ ?_
    rw [hpre (s (n + N))]
    exact ((hμ (s (n + N))).setLIntegral_comp_preimage_emb (measurableEmbedding_addRight _)
      (e u) _).symm
  -- Fatou's lemma.
  have hmeas (n : ℕ) : AEMeasurable (fun z ↦ e u (z + (s (n + N), 0))) (volume.restrict W) :=
    (hcont.comp (continuous_id.add continuous_const).continuousOn
      fun z hz ↦ hDU (hmem hz)).aemeasurable hWm
  refine le_antisymm ?_ zero_le
  calc ∫⁻ z in W, e v z
      = ∫⁻ z in W, liminf (fun n : ℕ ↦ e u (z + (s (n + N), 0))) atTop :=
        setLIntegral_congr_fun hWm fun z hz ↦ (hlim z hz).liminf_eq.symm
    _ ≤ liminf (fun n : ℕ ↦ ∫⁻ z in W, e u (z + (s (n + N), 0))) atTop :=
        lintegral_liminf_le' hmeas
    _ = 0 := hE.liminf_eq

/-- **The limit of translated Floer cylinders has zero energy.** Let `u` be `C¹` on an open set `U`
containing `D`, with finite energy over `D` for the cylindrical perturbation `K = H_t dt`, where `H`
is jointly `C¹`. Let `|s_k| → ∞`, with every window `[a + s_k, b + s_k] × [0, 1]` eventually in
`D`, and suppose that at every point of the strip `ℝ × [0, 1]` the derivatives of the translates
`w ↦ u (w + (s_k, 0))` converge in the tangent bundle to the derivative of a map `v`. Then the
energy of `v` over the strip vanishes. No Floer equation is needed: the energy densities converge
pointwise, and the energy of `u` over the translated windows tends to zero. -/
theorem lintegral_floerEnergyDensity_eq_zero_of_tendsto_mfderiv_comp_add (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hDU : D ⊆ U)
    (hfin : ∫⁻ z in D,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ D)
    (hdu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ e, Tendsto (fun k ↦ (⟨u (z + (s k, 0)),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (s k, 0))) z e⟩ : TangentBundle I M)) atTop
      (𝓝 ⟨v z, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z e⟩)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) v z) = 0 := by
  -- The rectangles `[-n, n] × [0, 1]` exhaust the strip.
  rw [← iUnion_Icc_neg_prod]
  exact le_antisymm ((lintegral_iUnion_le _ _).trans (tsum_eq_zero_iff.2 fun n ↦
    setLIntegral_Icc_prod_floerEnergyDensity_eq_zero hω hH hU hu hDU hfin hs hW hdu _ _).le)
    zero_le

/-- **The limit of translated Floer cylinders is a Floer cylinder.** Let `u` solve the Floer
equation `∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` on `D`, for the cylindrical perturbation
`K = H_t dt` with `H` jointly `C¹` and structures `J_t` independent of `s`. Suppose that at every
point `z` of the strip `ℝ × [0, 1]` the translates `z + (s_k, 0)` eventually lie in `D`, the
derivatives of the translates `w ↦ u (w + (s_k, 0))` converge in the tangent bundle to the
derivative of a map `v`, and that `J` is continuous at `(z.2, v z)` in the tangent coordinates at
`v z`. Then `v` solves the Floer equation on the strip. -/
theorem isComplexLinearMap_perturbedMFDeriv_of_tendsto_mfderiv_comp_add (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hfloer : ∀ z ∈ D, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hD : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ᶠ k in atTop, z + (s k, 0) ∈ D)
    (hdu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ e, Tendsto (fun k ↦ (⟨u (z + (s k, 0)),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (s k, 0))) z e⟩ : TangentBundle I M)) atTop
      (𝓝 ⟨v z, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z e⟩))
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ContinuousAt (fun p : ℝ × M ↦
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) (v z) p.2 (v z) p.2
        (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z.2, v z)) :
    ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (v z)) (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) v z).toLinearMap := by
  intro z hz
  -- The translates solve the Floer equation at `z` as soon as `z + (s_k, 0)` lies in `D`.
  have hsol : ∀ᶠ k in atTop, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u (z + (s k, 0)))) (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (fun w ↦ u (w + (s k, 0))) z).toLinearMap := by
    filter_upwards [hD z hz] with k hzk
    have hF := hfloer _ hzk
    have h2 : (z + (s k, 0)).2 = z.2 := by simp
    rw [h2] at hF
    exact ω.isComplexLinearMap_perturbedMFDeriv_comp_add_right rfl (by simp) hF
  have hJ' := (hJ z hz).comp (x := (z, v z)) (f := fun p : (ℝ × ℝ) × M ↦ (p.1.2, p.2))
    (by fun_prop)
  exact ω.isComplexLinearMap_perturbedMFDeriv_of_tendsto (Ks := fun _ _ ↦ 0)
    (Kt := fun w ↦ H w.2) (J := fun w x ↦ J w.2 x) (u := fun k w ↦ u (w + (s k, 0)))
    tendsto_const_nhds (hdu z hz) hJ' hω.continuous_hamiltonianVectorField_zero.continuousAt
    (hω.continuous_hamiltonianVectorField_cylindrical hH).continuousAt hsol

/-- **The limit of translated Floer cylinders is independent of `s`.** Under the hypotheses of
`TauCeti.SmoothTwoForm.lintegral_floerEnergyDensity_eq_zero_of_tendsto_mfderiv_comp_add` and
`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_of_tendsto_mfderiv_comp_add`, if the
limit `v` is `C¹` and the structures `J_t` are tamed by `ω` at the points of `v` on the strip
`ℝ × [0, 1]`, then `v (r, t) = v (0, t)` on the strip. -/
theorem IsNondegenerate.eq_of_tendsto_mfderiv_comp_add (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hDU : D ⊆ U)
    (hfloer : ∀ z ∈ D, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hfin : ∫⁻ z in D,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ D)
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hdu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ e, Tendsto (fun k ↦ (⟨u (z + (s k, 0)),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (s k, 0))) z e⟩ : TangentBundle I M)) atTop
      (𝓝 ⟨v z, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z e⟩))
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ContinuousAt (fun p : ℝ × M ↦
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) (v z) p.2 (v z) p.2
        (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z.2, v z))
    (hJt : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (v z)).Tames (J z.2 (v z))) :
    ∀ r, ∀ t ∈ Icc (0 : ℝ) 1, v (r, t) = v (0, t) := by
  have hsol := isComplexLinearMap_perturbedMFDeriv_of_tendsto_mfderiv_comp_add hω hH hfloer
    (fun z hz ↦ (hW z.1 z.1).mono fun _ hk ↦ hk ⟨⟨by simp, by simp⟩, by simpa using hz.2⟩) hdu hJ
  refine (hω.lintegral_floerEnergyDensity_eq_zero_iff (J := fun z ↦ J z.2 (v z)) hH hv hJt
    (fun z hz ↦ ?_)).1 (lintegral_floerEnergyDensity_eq_zero_of_tendsto_mfderiv_comp_add hω hH hU
      hu hDU hfin hs hW hdu)
  have h := (ω.isComplexLinearMap_perturbedMFDeriv_iff _ _ v z _).1 (hsol z hz)
  -- The `ds` component of `K` vanishes, and so does its Hamiltonian vector field.
  rwa [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] at h

/-- Both components of the perturbed derivative of the limit vanish on the strip: `∂_s v = 0` and
`∂_t v = X_{H_t}(v)`. -/
private theorem IsNondegenerate.mfderiv_eq_of_tendsto_mfderiv_comp_add (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hDU : D ⊆ U)
    (hfloer : ∀ z ∈ D, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hfin : ∫⁻ z in D,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ D)
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hdu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ e, Tendsto (fun k ↦ (⟨u (z + (s k, 0)),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (s k, 0))) z e⟩ : TangentBundle I M)) atTop
      (𝓝 ⟨v z, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z e⟩))
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ContinuousAt (fun p : ℝ × M ↦
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) (v z) p.2 (v z) p.2
        (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z.2, v z))
    (hJt : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (v z)).Tames (J z.2 (v z)))
    {z : ℝ × ℝ} (hz : z ∈ (univ : Set ℝ) ×ˢ Icc 0 1) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I v z stdComplexLineReal = 0 ∧
      mfderiv 𝓘(ℝ, ℝ × ℝ) I v z stdComplexLineImag = ω.hamiltonianVectorField (H z.2) (v z) := by
  have hstat := hω.eq_of_tendsto_mfderiv_comp_add hH hU hu hDU hfloer hfin hs hW hv hdu hJ hJt
  have hs0 : mfderiv 𝓘(ℝ, ℝ × ℝ) I v z stdComplexLineReal = 0 := by
    rw [stdComplexLineReal_eq]
    exact Manifold.mfderiv_apply_one_zero_eq_zero_of_apply_eq
      ((hv z).mdifferentiableAt one_ne_zero) fun q ↦ hstat q z.2 hz.2
  refine ⟨hs0, ?_⟩
  -- The Floer equation `∂_s v + J (∂_t v - X) = 0` with `∂_s v = 0` gives `J (∂_t v - X) = 0`, and
  -- an almost complex structure is injective, since `J (J w) = -w`.
  have hF := (ω.isComplexLinearMap_perturbedMFDeriv_iff _ _ v z _).1
    (isComplexLinearMap_perturbedMFDeriv_of_tendsto_mfderiv_comp_add hω hH hfloer
      (fun z hz ↦ (hW z.1 z.1).mono fun _ hk ↦ hk ⟨⟨by simp, by simp⟩, by simpa using hz.2⟩)
      hdu hJ z hz)
  rw [hs0, hamiltonianVectorField_const, Pi.zero_apply, sub_zero, zero_add] at hF
  have h' := congrArg (J z.2 (v z)) hF
  rw [AlmostComplexStructure.apply_apply, map_zero, neg_eq_zero] at h'
  exact sub_eq_zero.1 h'

/-- **The limit of translated Floer cylinders is a Hamiltonian orbit segment.** Under the
hypotheses of `TauCeti.SmoothTwoForm.IsNondegenerate.eq_of_tendsto_mfderiv_comp_add`, the curve
`x(t) = v (0, t)` solves `x'(t) = X_{H_t}(x(t))` for every `t ∈ [0, 1]`. -/
theorem IsNondegenerate.hasMFDerivAt_of_tendsto_mfderiv_comp_add (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hDU : D ⊆ U)
    (hfloer : ∀ z ∈ D, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hfin : ∫⁻ z in D,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ D)
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hdu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ e, Tendsto (fun k ↦ (⟨u (z + (s k, 0)),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (s k, 0))) z e⟩ : TangentBundle I M)) atTop
      (𝓝 ⟨v z, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z e⟩))
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ContinuousAt (fun p : ℝ × M ↦
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) (v z) p.2 (v z) p.2
        (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z.2, v z))
    (hJt : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (v z)).Tames (J z.2 (v z))) :
    ∀ t ∈ Icc (0 : ℝ) 1, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t ↦ v (0, t)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H t) (v (0, t)))) := by
  intro t ht
  have hvt : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v (0, t) := (hv _).mdifferentiableAt one_ne_zero
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun t ↦ v (0, t)) t :=
    hvt.comp t ((differentiableAt_const 0).prodMk differentiableAt_id).mdifferentiableAt
  have h := Manifold.hasMFDerivAt_curveVelocity hc
  rwa [Manifold.curveVelocity_eq_mfderiv_snd (f := fun a b ↦ v (a, b)) hvt, ← stdComplexLineImag_eq,
    (hω.mfderiv_eq_of_tendsto_mfderiv_comp_add hH hU hu hDU hfloer hfin hs hW hv hdu hJ hJt
      (z := (0, t)) ⟨mem_univ _, ht⟩).2] at h

/-- **The limit of translated Floer cylinders is a stationary Floer cylinder.** Under the
hypotheses of `TauCeti.SmoothTwoForm.IsNondegenerate.eq_of_tendsto_mfderiv_comp_add`, the
perturbed derivative `dv - X_K(v)` of the limit vanishes on the strip `ℝ × [0, 1]`. -/
theorem IsNondegenerate.perturbedMFDeriv_eq_zero_of_tendsto_mfderiv_comp_add
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hDU : D ⊆ U)
    (hfloer : ∀ z ∈ D, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hfin : ∫⁻ z in D,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ D)
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hdu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ e, Tendsto (fun k ↦ (⟨u (z + (s k, 0)),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (s k, 0))) z e⟩ : TangentBundle I M)) atTop
      (𝓝 ⟨v z, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z e⟩))
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ContinuousAt (fun p : ℝ × M ↦
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) (v z) p.2 (v z) p.2
        (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z.2, v z))
    (hJt : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (v z)).Tames (J z.2 (v z))) :
    ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) v z = 0 := by
  intro z hz
  obtain ⟨hs0, ht0⟩ :=
    hω.mfderiv_eq_of_tendsto_mfderiv_comp_add hH hU hu hDU hfloer hfin hs hW hv hdu hJ hJt hz
  -- A linear map on `ℝ × ℝ` vanishes when it vanishes on `(1, 0)` and `(0, 1)`.
  refine ContinuousLinearMap.ext fun e ↦ ?_
  have he : e = e.1 • stdComplexLineReal + e.2 • stdComplexLineImag := by
    simp [stdComplexLineReal_eq, stdComplexLineImag_eq]
  rw [he, map_add, map_smul, map_smul, perturbedMFDeriv_apply_stdComplexLineReal,
    perturbedMFDeriv_apply_stdComplexLineImag, hs0, ht0, hamiltonianVectorField_const]
  simp

end TauCeti.SmoothTwoForm

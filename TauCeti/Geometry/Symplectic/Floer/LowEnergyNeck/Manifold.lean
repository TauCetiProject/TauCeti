/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Geometry.Symplectic.Floer.Rotation
import TauCeti.Geometry.Symplectic.Hamiltonian.PeriodicOrbit
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# Floer cylinders of small energy in a closed manifold stay near a single orbit

Let `ω` be a nondegenerate two-form on a compact boundaryless manifold `M`, such as a closed
symplectic manifold, `H : ℝ → M → ℝ` a Hamiltonian, `1`-periodic in time, and `J_t` almost complex
structures on the tangent spaces of `M`. When a sequence of Floer cylinders
`∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` breaks, its energy concentrates at finitely many levels,
and between two consecutive levels it runs along a *neck*: a long window `(a, b) × ℝ` of the
cylinder carrying little energy. This file proves that a neck stays uniformly close to a single
`1`-periodic orbit, which is how the levels of the broken limit are joined at orbits. The
vector-space version is `TauCeti.Geometry.Symplectic.Floer.LowEnergyNeck.Basic`.

Distances in `M` are measured through a `C¹` map `e : M → F` into a finite-dimensional normed
space, injective and with injective differential, such as a Whitney embedding of `M`
(`TauCeti.SmoothEmbedding.exists_nonempty_euclidean_of_compact`), and the structures are uniformly
tame with respect to `e`: `c ‖d e v‖² ≤ ω(v, J_t v)` with `c > 0`.

* **Necks with bounded derivative.** Let the `1`-periodic orbits in a compact set `K` be isolated.
  For every `C` and `ε > 0` there are `δ > 0` and `η > 0` such that every Floer cylinder `u` on a
  window `(a, b) × ℝ` with `a + η ≤ b - η`, with loops in `K`, `‖d (e ∘ u)‖ ≤ C` and energy less
  than `δ` over `(a, b) × [0, 1]`, stays within `ε` of a single `1`-periodic orbit `x` in `K`,
  measured through `e`, on `[a + η, b - η] × ℝ`
  (`IsNondegenerate.exists_pos_forall_exists_mem_periodicSolutions_forall_dist_lt_of_isCompact`).
  The pushforward `d e (X_{H_t})` extends to a continuous field `Y` on `F`, the energy bounds the
  squared `L²` defect of the loops of `e ∘ u` from `y' = Y(t, y)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_norm_sq_sliceDefect_comp_le`), the periodic
  solutions of `y' = Y(t, y)` in `e(K)` are the images of the orbits in `K` and are isolated
  (`TauCeti.exists_pos_forall_eq_of_forall_dist_lt_of_mem_image`), and loops with bounded
  derivative and small defect stay near one of them
  (`TauCeti.exists_pos_forall_exists_periodic_hasDerivAt_forall_dist_lt`).
* **No bubbling on necks.** On a closed manifold, small energy over a window bounds the energy
  density, and hence the derivative of `e ∘ u`, away from the ends of the window
  (`IsNondegenerate.exists_pos_forall_floerEnergyDensity_le_of_setLIntegral_le`). If not, the
  densities of cylinders of energies at most `δ` would blow up at points which, after translating
  in `s` and using the periodicity in `t`, converge in `{0} × [0, 1]`. Energy at least a fixed
  threshold then concentrates near the limit point
  (`IsNondegenerate.exists_pos_forall_eventually_le_setIntegral_floerEnergyDensity_ball`), while
  the energy of the translates over `(-1, 1) × (-1/2, 3/2)` is at most `3 δ`.
* **Necks in a closed manifold.** If every `1`-periodic orbit is nondegenerate, the two combine:
  for every `ε > 0` there are `δ > 0` and `η > 0` such that every Floer cylinder on a window
  `(a, b) × ℝ` with `a + η ≤ b - η` and energy less than `δ` over `(a, b) × [0, 1]` stays within
  `ε` of a single `1`-periodic orbit on `[a + η, b - η] × ℝ`
  (`IsNondegenerate.exists_pos_forall_exists_mem_periodicSolutions_forall_dist_lt_of_floer`).
  The constants depend neither on `u` nor on the length of the window.

As in `TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`, the structures and the Hamiltonian
vector fields are assumed `C²` in the charts of `M`. The results are in the namespace
`TauCeti.SmoothTwoForm`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on the compactness of the moduli spaces of Floer trajectories.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6,
  on bubbling off finitely many points.
-/

public section

open Set Filter Topology MeasureTheory Function Metric
open scoped ENNReal Manifold

namespace TauCeti.SmoothTwoForm

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {e : M → F}

/-- **A Floer cylinder of small energy and bounded derivative stays near a single orbit.** Let `ω`
be a nondegenerate two-form on a manifold `M`, `H` a `C¹` Hamiltonian, `1`-periodic in time, `K`
a compact set and `e : M → F` a `C¹` map, injective on `K` and with injective differential at the
points of `K`. Suppose that the `1`-periodic orbits in `K` are isolated: for each such orbit `x`,
every orbit in `K` starting close enough to `x 0` is `x`. Let `c > 0` and `C` be constants.

Then for every `ε > 0` there are `δ > 0` and `η > 0` with the following property. Let `u` be `C¹`
on a window `(a, b) × ℝ` with `a + η ≤ b - η`, with `1`-periodic loops `t ↦ u(s, t)` in `K`,
solving the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `(a, b) × [0, 1]` for structures
with `c ‖d e v‖² ≤ ω(v, J z v)`, and with `‖d (e ∘ u)‖ ≤ C` on the window. If the energy of `u`
over `(a, b) × [0, 1]` is less than `δ`, then there is a `1`-periodic orbit `x` in `K` such that
`e(u(s, t))` is within `ε` of `e(x(t))` for all `s ∈ [a + η, b - η]` and all `t`. -/
theorem IsNondegenerate.exists_pos_forall_exists_mem_periodicSolutions_forall_dist_lt_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p))
    (hiso : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) →
      ∀ᶠ p in 𝓝 (x 0), ∀ x' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, x' t ∈ K) → x' 0 = p → x' = x)
    {c : ℝ} (hc : 0 < c) (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ η > 0, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃a b : ℝ⦄, a + η ≤ b - η →
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioo a b ×ˢ univ) →
      (∀ s ∈ Ioo a b, Periodic (fun t ↦ u (s, t)) 1) → (∀ s ∈ Ioo a b, ∀ t, u (s, t) ∈ K) →
      ∀ J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)),
      (∀ z ∈ Ioo a b ×ˢ Icc 0 1, ∀ v,
        c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v)) →
      (∀ z ∈ Ioo a b ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap) →
      (∀ z ∈ Ioo a b ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C) →
      ∫⁻ z in Ioo a b ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) <
          ENNReal.ofReal δ →
      ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
        ∀ s ∈ Icc (a + η) (b - η), ∀ t, dist (e (u (s, t))) (e (x t)) < ε := by
  -- Extend `d e (X_{H_t})` from `e(K)` to `F`; the periodic solutions of the extension in `e(K)`
  -- are read from the orbits in `K`, so they are isolated.
  obtain ⟨Y, hYc, hYper, hYe⟩ := hω.exists_continuous_periodic_extension hH hHper he hK he_inj
  have hKe : IsCompact (e '' K) := hK.image he.continuous
  obtain ⟨δ₀, hδ₀, η, hη, hneck⟩ := exists_pos_forall_exists_periodic_hasDerivAt_forall_dist_lt
    hKe hYc hYper (fun _ ↦ exists_pos_forall_eq_of_forall_dist_lt_of_mem_image hK he_inj hde hYe
      hiso) C hε
  refine ⟨δ₀ * c, by positivity, η, hη, fun u a b hab hu hper huK J hJc hfl hC hE ↦ ?_⟩
  have hU : IsOpen (Ioo a b ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hsub : Ioo a b ×ˢ Icc (0 : ℝ) 1 ⊆ Ioo a b ×ˢ univ := prod_mono le_rfl (subset_univ _)
  -- The energy bounds the squared defect of the loops of `e ∘ u` from `y' = Y(t, y)`.
  have hdef : ∫⁻ z in Ioo a b ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect Y (e ∘ u) z‖ ^ 2) <
      ENNReal.ofReal δ₀ := by
    refine (hω.lintegral_norm_sq_sliceDefect_comp_le (measurableSet_Ioo.prod measurableSet_Icc)
      (fun _ _ ↦ he.mdifferentiableAt one_ne_zero)
      (fun z hz ↦ (hu.contMDiffAt (hU.mem_nhds (hsub hz))).mdifferentiableAt one_ne_zero)
      (fun z hz ↦ hYe _ _ (huK z.1 hz.1 z.2)) J hc hJc fun z hz ↦ ?_).trans_lt ?_
    · simpa using (ω.isComplexLinearMap_perturbedMFDeriv_iff _ _ u z (J z)).1 (hfl z hz)
    calc ENNReal.ofReal c⁻¹ * ∫⁻ z in Ioo a b ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z)
        < ENNReal.ofReal c⁻¹ * ENNReal.ofReal (δ₀ * c) :=
          ENNReal.mul_lt_mul_right
            (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity) ENNReal.ofReal_ne_top hE
      _ = ENNReal.ofReal δ₀ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  -- The loops of `e ∘ u` stay near one periodic solution of `y' = Y(t, y)` in `e(K)`.
  obtain ⟨y, hyper, hy, hyK, hyd⟩ := hneck hab
    (contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn hu))
    (fun s hs t ↦ by simp only [comp_apply, hper s hs t])
    (fun s hs t ↦ mem_image_of_mem e (huK s hs t)) hC hdef
  obtain ⟨x, hx, hxK, rfl⟩ := exists_mem_periodicSolutions_comp_eq hK he_inj hde hYe hyper hy hyK
  exact ⟨x, hx, hxK, hyd⟩

omit [FiniteDimensional ℝ F] in
/-- On a compact manifold, the pushforwards `d e (X_{H_t})` of the Hamiltonian vector fields of a
`C¹` Hamiltonian `H`, `1`-periodic in time, by a `C¹` map `e : M → F` are uniformly bounded. -/
private theorem IsNondegenerate.exists_forall_norm_mvfderiv_hamiltonianVectorField_le
    [CompactSpace M] (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) :
    ∃ B, ∀ t x, ‖mvfderiv I e x (ω.hamiltonianVectorField (H t) x)‖ ≤ B := by
  have hXe : Continuous fun q : ℝ × M ↦ mvfderiv I e q.2 (ω.hamiltonianVectorField (H q.1) q.2) :=
    (he.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp
      (hω.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp)
        (by simpa using hH)).continuous
  obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_univ (X := M))).exists_bound_of_continuousOn hXe.continuousOn
  refine ⟨B, fun t x ↦ ?_⟩
  obtain ⟨t', ht', hHt⟩ := hHper.exists_mem_Ico₀ one_pos t
  rw [hHt]
  exact hB (t', x) ⟨Ico_subset_Icc_self ht', mem_univ x⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A structure `J` on `T_x M` with `c ‖d e v‖² ≤ ω(v, J v)` for some `c > 0`, where `d e` is
injective at `x`, is tamed by `ω`. -/
private theorem IsNondegenerate.tames_of_mul_norm_sq_le (hω : ω.IsNondegenerate) {x : M}
    (hde : Injective (mvfderiv I e x)) {c : ℝ} (hc : 0 < c)
    {J : AlmostComplexStructure (TangentSpace I x)}
    (hJc : ∀ v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J v)) :
    (hω.symplecticFormAt x).Tames J := fun v hv ↦
  (mul_pos hc (pow_pos (norm_pos_iff.2 fun h ↦ hv (hde (h.trans (map_zero _).symm))) 2)).trans_le
    (hJc v)

omit [FiniteDimensional ℝ E] in
/-- For a Hamiltonian of period one in time, the Floer energy density of a cylinder of period one
in `t` has period one in `t`. -/
private theorem floerEnergyDensity_add_one (hHper : Periodic H 1) {u : ℝ × ℝ → M}
    (hper : ∀ s t, u (s, t + 1) = u (s, t)) (s t : ℝ) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u (s, t + 1) =
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u (s, t) := by
  have hu1 : (fun w ↦ u (w + ((0 : ℝ), (1 : ℝ)))) = u :=
    funext fun ⟨s, t⟩ ↦ by simpa using hper s t
  have hH1 : (fun w : ℝ × ℝ ↦ H (w + ((0 : ℝ), (1 : ℝ))).2) = fun w ↦ H w.2 :=
    funext fun w ↦ by simpa using hHper w.2
  have h := ω.floerEnergyDensity_comp_add_right (fun _ _ ↦ 0) (fun w ↦ H w.2) u
    ((0 : ℝ), (1 : ℝ)) (s, t)
  simp only [hu1, hH1, Prod.mk_add_mk, add_zero] at h
  exact h.symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The Floer energy of the translate `(s, t) ↦ u(s + s₀, t)` of a cylinder of period one in `t`
over the window `(-1, 1) × (-1/2, 3/2)` is at most three times the energy of `u` over
`(a, b) × [0, 1]`, when `s₀ ∈ [a + 1, b - 1]`. -/
private theorem lintegral_ball_floerEnergyDensity_comp_add_le (hHper : Periodic H 1)
    {u : ℝ × ℝ → M} (hper : ∀ s t, u (s, t + 1) = u (s, t)) {a b s₀ : ℝ}
    (hs₀ : s₀ ∈ Icc (a + 1) (b - 1)) :
    ∫⁻ w in ball ((0 : ℝ), (1 / 2 : ℝ)) 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (fun w ↦ u (w + (s₀, 0))) w) ≤
      3 * ∫⁻ z in Ioo a b ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) := by
  set g : ℝ × ℝ → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z)
  have hmeas : MeasurableSet (Ioo a b ×ˢ (univ : Set ℝ)) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  -- The window, translated by `(s₀, 0)`, lies in `(a, b) × [-1, 2]`.
  have hsub : ball ((0 : ℝ), (1 / 2 : ℝ)) 1 ⊆
      (· + (s₀, (0 : ℝ))) ⁻¹' (Ioo a b ×ˢ Icc (-1) 2) := by
    intro z hz
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at hz
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
    exact ⟨⟨by simp only [Prod.fst_add]; linarith [hs₀.1], by simp only [Prod.fst_add]; linarith
      [hs₀.2]⟩, by simp only [Prod.snd_add]; linarith, by simp only [Prod.snd_add]; linarith⟩
  have hv : MeasurePreserving (· + (s₀, (0 : ℝ))) volume volume :=
    (measurePreserving_add_right volume s₀).prod (measurePreserving_add_right volume 0)
  -- Restricted to `(a, b) × ℝ`, the energy density is still of period one in `t`.
  have hgper (s t : ℝ) : (Ioo a b ×ˢ univ).indicator g (s, t + 1) =
      (Ioo a b ×ˢ univ).indicator g (s, t) := by
    simp only [indicator, mem_prod, mem_univ, and_true, g, floerEnergyDensity_add_one hHper hper]
  calc ∫⁻ w in ball ((0 : ℝ), (1 / 2 : ℝ)) 1, ENNReal.ofReal (ω.floerEnergyDensity
          (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ u (w + (s₀, 0))) w)
      = ∫⁻ w in ball ((0 : ℝ), (1 / 2 : ℝ)) 1, g (w + (s₀, 0)) := by
        simp only [g, floerEnergyDensity_cylindrical_comp_add_right]
    _ ≤ ∫⁻ w in (· + (s₀, (0 : ℝ))) ⁻¹' (Ioo a b ×ˢ Icc (-1) 2), g (w + (s₀, 0)) :=
        lintegral_mono_set hsub
    _ = ∫⁻ z in Ioo a b ×ˢ Icc (-1) 2, g z :=
        hv.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight _) g _
    _ = ∫⁻ z in univ ×ˢ Icc (-1) 2, (Ioo a b ×ˢ univ).indicator g z := by
        rw [setLIntegral_indicator hmeas, prod_inter_prod, univ_inter, inter_univ]
    _ ≤ 3 * ∫⁻ z in univ ×ˢ Icc 0 1, (Ioo a b ×ˢ univ).indicator g z :=
        setLIntegral_univ_prod_Icc_neg_one_two_le hgper
    _ = 3 * ∫⁻ z in Ioo a b ×ˢ Icc 0 1, g z := by
        rw [setLIntegral_indicator hmeas, prod_inter_prod, univ_inter, inter_univ]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The translate `w ↦ u(w + (s₀, 0))` of a `C³` Floer cylinder `u` on `(a, b) × ℝ`, with
`s₀ ∈ [a + 1, b - 1]`, is a `C³` Floer cylinder on the window `(-1, 1) × (-1/2, 3/2)`. -/
private theorem contMDiffOn_and_isComplexLinearMap_perturbedMFDeriv_comp_add
    {J : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {u : ℝ × ℝ → M} {a b s₀ : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (Ioo a b ×ˢ univ))
    (hfl : ∀ z ∈ Ioo a b ×ˢ univ, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u z)) (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hs₀ : s₀ ∈ Icc (a + 1) (b - 1)) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (fun w ↦ u (w + (s₀, 0))) (ball ((0 : ℝ), (1 / 2 : ℝ)) 1) ∧
      ∀ w ∈ ball ((0 : ℝ), (1 / 2 : ℝ)) 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J w.2 (u (w + (s₀, 0))))
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (fun w ↦ u (w + (s₀, 0))) w).toLinearMap := by
  have hmaps : MapsTo (· + (s₀, (0 : ℝ))) (ball ((0 : ℝ), (1 / 2 : ℝ)) 1) (Ioo a b ×ˢ univ) := by
    intro w hw
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt] at hw
    exact ⟨⟨by simp only [Prod.fst_add]; linarith [hs₀.1, hw.1.1],
      by simp only [Prod.fst_add]; linarith [hs₀.2, hw.1.2]⟩, mem_univ _⟩
  refine ⟨hu.comp (contDiff_id.add contDiff_const).contMDiff.contMDiffOn hmaps, fun w hw ↦ ?_⟩
  have h2 : (w + (s₀, (0 : ℝ))).2 = w.2 := by simp
  have h := hfl _ (hmaps hw)
  rw [h2] at h
  exact ω.isComplexLinearMap_perturbedMFDeriv_comp_add_right rfl (by simp) h

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The Floer energy density of the translate `w ↦ u(w + (s₀, 0))` of a `C³` Floer cylinder `u` on
`(a, b) × ℝ`, of period one in `t`, with `s₀ ∈ [a + 1, b - 1]`, is integrable on the window
`(-1, 1) × (-1/2, 3/2)`, with integral at most three times the energy of `u` over
`(a, b) × [0, 1]`. -/
private theorem IsNondegenerate.integrableOn_and_setIntegral_floerEnergyDensity_comp_add_le
    [I.Boundaryless] (hω : ω.IsNondegenerate) (hHper : Periodic H 1)
    {J : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hX : ∀ α, ContinuousOn (ω.hamiltonianVectorFieldInChartAt α fun z ↦ H z.2)
      (univ ×ˢ (extChartAt I α).target))
    (hJt : ∀ t x, (hω.symplecticFormAt x).Tames (J t x)) {u : ℝ × ℝ → M} {a b s₀ S : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (Ioo a b ×ˢ univ)) (hper : ∀ s t, u (s, t + 1) = u (s, t))
    (hfl : ∀ z ∈ Ioo a b ×ˢ univ, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u z)) (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap)
    (hS : 0 ≤ S) (hE : ∫⁻ z in Ioo a b ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≤ ENNReal.ofReal S)
    (hs₀ : s₀ ∈ Icc (a + 1) (b - 1)) :
    IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) fun w ↦ u (w + (s₀, 0)))
        (ball ((0 : ℝ), (1 / 2 : ℝ)) 1) ∧
      ∫ w in ball ((0 : ℝ), (1 / 2 : ℝ)) 1,
        ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ u (w + (s₀, 0))) w ≤ 3 * S := by
  obtain ⟨hv, hvfl⟩ := contMDiffOn_and_isComplexLinearMap_perturbedMFDeriv_comp_add hu hfl hs₀
  have hnonneg := ae_restrict_of_forall_mem (μ := volume) measurableSet_ball fun w hw ↦
    floerEnergyDensity_nonneg hω (hJt _ _) (hvfl w hw)
  have hint : ∫⁻ w in ball ((0 : ℝ), (1 / 2 : ℝ)) 1, ENNReal.ofReal (ω.floerEnergyDensity
      (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ u (w + (s₀, 0))) w) ≤ ENNReal.ofReal (3 * S) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    exact (lintegral_ball_floerEnergyDensity_comp_add_le hHper hper hs₀).trans (by gcongr)
  have hintOn : IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
      fun w ↦ u (w + (s₀, 0))) (ball ((0 : ℝ), (1 / 2 : ℝ)) 1) := by
    refine ⟨(ω.continuousOn_floerEnergyDensity_of_continuousOn_inChartAt isOpen_ball
      (hv.of_le (by norm_num))
      (fun α ↦ by rw [hamiltonianVectorFieldInChartAt_zero]; exact continuousOn_const)
      (fun α ↦ (hX α).mono (prod_mono (subset_univ _) le_rfl))).aestronglyMeasurable
      measurableSet_ball, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnonneg]
    exact hint.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hintOn, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hintOn.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hint

omit [FiniteDimensional ℝ F] in
/-- **Floer cylinders of small energy in a closed manifold have bounded energy density.** Let `ω`
be a nondegenerate two-form on a compact boundaryless manifold `M`, `H` a Hamiltonian, `1`-periodic
in time, and `J_t` almost complex structures, with `J_t` and the Hamiltonian vector fields `X_{H_t}`
`C²` in the charts of `M`. Let `e : M → F` be a differentiable injective map with injective
differential, with the structures uniformly tame with respect to `e`,
`c ‖d e v‖² ≤ ω(v, J_t v)` with `c > 0`, and the pushforwards `d e (X_{H_t})` at most `B`.

There are `δ > 0` and `A` with the following property. Let `u` be `C³` on a window `(a, b) × ℝ`,
of period one in `t`, solving the Floer equation `∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` there.
If the energy of `u` over `(a, b) × [0, 1]` is at most `δ`, then the Floer energy density of `u`
is at most `A` at every point `(s, t)` with `s ∈ [a + 1, b - 1]`. -/
theorem IsNondegenerate.exists_pos_forall_floerEnergyDensity_le_of_setLIntegral_le
    [CompactSpace M] [I.Boundaryless] (hω : ω.IsNondegenerate) (hHper : Periodic H 1)
    {J : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α fun z ↦ J z.2)
      (univ ×ˢ (extChartAt I α).target))
    (hX : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α fun z ↦ H z.2)
      (univ ×ˢ (extChartAt I α).target))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ t x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J t x v))
    (hB : ∀ t x, ‖mvfderiv I e x (ω.hamiltonianVectorField (H t) x)‖ ≤ B) :
    ∃ δ > 0, ∃ A, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃a b : ℝ⦄,
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (Ioo a b ×ˢ univ) → (∀ s t, u (s, t + 1) = u (s, t)) →
      (∀ z ∈ Ioo a b ×ˢ univ, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J z.2 (u z)) (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap) →
      ∫⁻ z in Ioo a b ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≤
          ENNReal.ofReal δ →
      ∀ z : ℝ × ℝ, z.1 ∈ Icc (a + 1) (b - 1) →
        ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z ≤ A := by
  have hJt (t : ℝ) (x : M) := hω.tames_of_mul_norm_sq_le (hde x) hc (hJc t x)
  obtain ⟨δ, hδ, hconc⟩ := hω.exists_pos_forall_eventually_le_setIntegral_floerEnergyDensity_ball
    (J := fun z ↦ J z.2) (Ks := fun _ _ ↦ 0) (Kt := fun z ↦ H z.2) he he_inj isOpen_univ
    (isCompact_closedBall ((0 : ℝ), (1 / 2 : ℝ)) 1) (subset_univ _) hJ
    (fun α ↦ by rw [hamiltonianVectorFieldInChartAt_zero]; exact contDiffOn_const) hX
    (fun z _ x ↦ hJt z.2 x) hc (fun z _ x v ↦ hJc z.2 x v) (B := max B 0)
    (fun _ _ x ↦ by
      rw [hamiltonianVectorField_const, Pi.zero_apply, map_zero, norm_zero]
      exact le_max_right B 0)
    (fun z _ x ↦ (hB z.2 x).trans (le_max_left _ _))
  refine ⟨δ / 4, by positivity, ?_⟩
  by_contra! hA
  -- Cylinders `uₖ` of energy at most `δ / 4` whose densities exceed `k` at points `zₖ`.
  choose u a b hu hper hfl hE z hz hρ using fun k : ℕ ↦ hA k
  set ρ : ℕ → ℝ × ℝ → ℝ := fun k ↦ ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k)
  -- By periodicity in `t`, the points can be taken in `{sₖ} × [0, 1)`.
  have hred (k : ℕ) : ∃ t ∈ Ico (0 : ℝ) 1, ρ k (z k) = ρ k ((z k).1, t) :=
    Periodic.exists_mem_Ico₀ (f := fun t ↦ ρ k ((z k).1, t))
      (fun t ↦ floerEnergyDensity_add_one hHper (hper k) (z k).1 t) one_pos (z k).2
  choose t ht htz using hred
  -- Translate each cylinder by `(sₖ, 0)`; the points become `wₖ = (0, tₖ)`, with a limit `w₀`.
  set v : ℕ → ℝ × ℝ → M := fun k w ↦ u k (w + ((z k).1, 0))
  have hv (k : ℕ) := contMDiffOn_and_isComplexLinearMap_perturbedMFDeriv_comp_add (hu k) (hfl k)
    (hz k)
  have hint (k : ℕ) := hω.integrableOn_and_setIntegral_floerEnergyDensity_comp_add_le hHper
    (fun α ↦ (hX α).continuousOn) hJt (hu k) (hper k) (hfl k) (by positivity) (hE k) (hz k)
  obtain ⟨w₀, hw₀, φ, hφ, hlim⟩ := (isCompact_singleton.prod isCompact_Icc).tendsto_subseq
    (x := fun k ↦ ((0 : ℝ), t k)) fun k ↦ ⟨rfl, (ht k).1, (ht k).2.le⟩
  have hw₀Ω : w₀ ∈ ball ((0 : ℝ), (1 / 2 : ℝ)) 1 := by
    obtain ⟨h0, h1, h2⟩ := hw₀
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt,
      show w₀.1 = 0 from h0]
    exact ⟨by norm_num, by constructor <;> linarith⟩
  -- The densities of the translates blow up at `wₖ → w₀`.
  have hblow : Tendsto (fun n ↦ ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (v (φ n))
      ((0 : ℝ), t (φ n))) atTop atTop := by
    refine tendsto_atTop_mono (fun n ↦ ?_) (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
    rw [comp_apply, floerEnergyDensity_cylindrical_comp_add_right, Prod.mk_add_mk, zero_add,
      add_zero]
    exact (hρ (φ n)).le.trans_eq (htz (φ n))
  -- So energy `δ` concentrates near `w₀`, but the translates have energy at most `3 δ / 4`.
  obtain ⟨n, hn⟩ := (hconc isOpen_ball ball_subset_closedBall (fun n ↦ (hv (φ n)).1)
    (fun n ↦ (hv (φ n)).2) (fun n ↦ (hint (φ n)).1) hw₀Ω hlim hblow 1 one_pos).exists
  have hle := (setIntegral_mono_set (hint (φ n)).1 (ae_restrict_of_forall_mem measurableSet_ball
    fun w hw ↦ floerEnergyDensity_nonneg hω (hJt _ _) ((hv (φ n)).2 w hw))
    (Eventually.of_forall fun _ (hx : _ ∈ ball w₀ 1 ∩ ball ((0 : ℝ), (1 / 2 : ℝ)) 1) ↦ hx.2)).trans
      (hint (φ n)).2
  linarith

/-- **A Floer cylinder of small energy in a closed manifold stays near a single orbit.** Let `ω`
be a nondegenerate two-form on a compact boundaryless manifold `M`, `H` a `C²` Hamiltonian,
`1`-periodic in time, all of whose `1`-periodic orbits are nondegenerate, and `J_t` almost complex
structures; let `J_t` and the Hamiltonian vector fields `X_{H_t}` be `C²` in the charts of `M`. Let
`e : M → F` be a `C¹` injective map with injective differential into a finite-dimensional normed
space, such as a Whitney embedding, with the structures uniformly tame with respect to `e`:
`c ‖d e v‖² ≤ ω(v, J_t v)` with `c > 0`.

Then for every `ε > 0` there are `δ > 0` and `η > 0` with the following property. Let `u` be `C³`
on a window `(a, b) × ℝ` with `a + η ≤ b - η`, of period one in `t`, solving the Floer equation
`∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` there. If the energy of `u` over `(a, b) × [0, 1]` is
less than `δ`, then there is a `1`-periodic orbit `x` such that `e(u(s, t))` is within `ε` of
`e(x(t))` for all `s ∈ [a + η, b - η]` and all `t`. -/
theorem IsNondegenerate.exists_pos_forall_exists_mem_periodicSolutions_forall_dist_lt_of_floer
    [CompactSpace M] [T2Space M] [I.Boundaryless] (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry H)) (hHper : Periodic H 1)
    {J : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α fun z ↦ J z.2)
      (univ ×ˢ (extChartAt I α).target))
    (hX : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α fun z ↦ H z.2)
      (univ ×ˢ (extChartAt I α).target))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ t x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J t x v))
    (hnd : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      IsNondegenerateFixedPt I (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1)
        (x 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ η > 0, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃a b : ℝ⦄, a + η ≤ b - η →
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (Ioo a b ×ˢ univ) → (∀ s t, u (s, t + 1) = u (s, t)) →
      (∀ z ∈ Ioo a b ×ˢ univ, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J z.2 (u z)) (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap) →
      ∫⁻ z in Ioo a b ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) <
          ENNReal.ofReal δ →
      ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        ∀ s ∈ Icc (a + η) (b - η), ∀ t, dist (e (u (s, t))) (e (x t)) < ε := by
  -- Small energy bounds the density, hence the derivative of `e ∘ u`, away from the ends.
  obtain ⟨B, hB⟩ :=
    hω.exists_forall_norm_mvfderiv_hamiltonianVectorField_le (hH.of_le one_le_two) hHper he
  obtain ⟨δ₁, hδ₁, A, hA⟩ := hω.exists_pos_forall_floerEnergyDensity_le_of_setLIntegral_le hHper
    hJ hX (fun _ ↦ he.mdifferentiableAt one_ne_zero) he_inj hde hc hJc hB
  -- Nondegenerate orbits are isolated, so necks with bounded derivative stay near one orbit.
  obtain ⟨δ₀, hδ₀, η, hη, hneck⟩ :=
    hω.exists_pos_forall_exists_mem_periodicSolutions_forall_dist_lt_of_isCompact
      (hH.of_le one_le_two) hHper he isCompact_univ he_inj.injOn (fun p _ ↦ hde p)
      (fun x hx _ ↦ (hω.eventually_forall_mem_periodicSolutions_hamiltonianVectorField_eq hH hx
        (hnd x hx)).mono fun _ hp y hy _ ↦ hp y hy) hc (2 * (√(A / c) + max B 0)) hε
  refine ⟨min δ₁ δ₀, lt_min hδ₁ hδ₀, η + 1, by positivity,
    fun u a b hab hu hper hfl hE ↦ ?_⟩
  have hsub : Ioo (a + 1) (b - 1) ⊆ Ioo a b := Ioo_subset_Ioo (by linarith) (by linarith)
  have hU : IsOpen (Ioo a b ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hρ := hA hu hper hfl (hE.le.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
  have hderiv : ∀ z ∈ Ioo (a + 1) (b - 1) ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤
      2 * (√(A / c) + max B 0) := fun z hz ↦
    hω.norm_fderiv_comp_le_of_floerEnergyDensity_le hc (he.mdifferentiableAt one_ne_zero)
      ((hu.contMDiffAt (hU.mem_nhds ⟨hsub hz.1, mem_univ _⟩)).mdifferentiableAt (by norm_num))
      (hJc z.2 (u z))
      (by
        rw [hamiltonianVectorField_const, Pi.zero_apply, map_zero, norm_zero]
        exact le_max_right B 0)
      ((hB z.2 (u z)).trans (le_max_left _ _))
      (hfl z ⟨hsub hz.1, mem_univ _⟩) (hρ z ⟨hz.1.1.le, hz.1.2.le⟩)
  obtain ⟨x, hx, -, hxd⟩ := hneck (a := a + 1) (b := b - 1) (by linarith)
    ((hu.of_le (by norm_num)).mono (prod_mono hsub le_rfl)) (fun s _ t ↦ hper s t)
    (fun _ _ _ ↦ mem_univ _) (fun z ↦ J z.2 (u z)) (fun z _ v ↦ hJc z.2 (u z) v)
    (fun z hz ↦ hfl z ⟨hsub hz.1, mem_univ _⟩) hderiv
    ((lintegral_mono_set (prod_mono hsub le_rfl)).trans_lt
      (hE.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _))))
  exact ⟨x, hx, fun s hs ↦ hxd s ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩

end TauCeti.SmoothTwoForm

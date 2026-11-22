/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Geometry.Symplectic.Floer.Manifold.Translation
import TauCeti.MeasureTheory.Integral.Rectangle
import TauCeti.MeasureTheory.Measure.Haar.Prod

/-!
# Floer cylinders of small energy have uniformly bounded derivatives

Let `(V, ω)` be a symplectic vector space, `C` a compact set of parameters and `K ⊆ V` compact.
For `p ∈ C` let `(Hs p)_t` be a Hamiltonian of period one in `t` and `(Js p)_t(x)` an almost
complex structure tamed by `ω` on `K`, depending jointly `C³` and `C²` on `(p, t, x)`. Consider
the Floer cylinders of these data: maps `u : ℝ × ℝ → V` of period one in `t` solving
`∂s u + (Js p)_t(u) (∂t u - X_{(Hs p)_t}(u)) = 0`, with image in `K`.

There are `δ > 0` and `M` such that every such cylinder whose Floer energy over the strip
`ℝ × [0, 1]` is at most `δ` satisfies `‖du‖ ≤ M` everywhere, for every `p ∈ C`
(`exists_pos_forall_norm_fderiv_le_of_mem_of_setLIntegral_floerEnergyDensity_le`).
For a single Hamiltonian, small energy over a band already bounds the derivative
(`TauCeti.SymplecticForm.exists_pos_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_le`);
the point here is that `δ` and `M` are uniform over the family. This is the absence of
bubbling below the energy threshold of Gromov–Floer compactness. If the derivatives of a sequence
of such cylinders blew up at points `zₖ`, translating each cylinder in `s` (the data do not depend
on `s`) and using its periodicity in `t` would move `zₖ` into the compact segment `{0} × [0, 1]`.
The translated cylinders have energy at most `3 δ` on the window `(-1, 1) × (-1/2, 3/2)`, which
lies in the strip `ℝ × [-1, 2]`. Compactness over the compact parameter set
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
then gives a subsequence whose derivatives are bounded on `{0} × [0, 1]` once `3 δ` is below the
bubbling threshold, since then there is no bubbling point.

## Main results

* `exists_pos_forall_norm_fderiv_le_of_mem_of_setLIntegral_floerEnergyDensity_le`:
  Floer cylinders of a compact family of time-periodic Hamiltonians and almost complex structures,
  in a compact set and of small energy, have uniformly bounded derivatives.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (inhomogeneous equations).
-/

public section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V}

/-- The Floer energy of a translate `(s, t) ↦ u(s + s₀, t)` of a cylinder of period one, for a
Hamiltonian `H_t` of period one in `t`, over the window `(-1, 1) × (-1/2, 3/2)` is at most three
times the energy of `u` over the strip `ℝ × [0, 1]`. -/
private theorem lintegral_ball_floerEnergyDensity_comp_add_le {H : ℝ → V → ℝ}
    (hHper : Function.Periodic H 1) {u : ℝ × ℝ → V} (hper : ∀ s t, u (s, t + 1) = u (s, t))
    (s₀ : ℝ) :
    ∫⁻ w in ball ((0 : ℝ), (1 / 2 : ℝ)) 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (fun w ↦ u (w + (s₀, 0))) w) ≤
      3 * ∫⁻ z in univ ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) := by
  have hsub : ball ((0 : ℝ), (1 / 2 : ℝ)) 1 ⊆ univ ×ˢ Icc (-1) 2 := by
    intro z hz
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hz
    obtain ⟨-, h⟩ := hz
    rw [abs_lt] at h
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  have hpre : (· + (s₀, (0 : ℝ))) ⁻¹' (univ ×ˢ Icc (-1 : ℝ) 2) = univ ×ˢ Icc (-1 : ℝ) 2 := by
    ext ⟨s, t⟩
    simp
  have hu1 : (fun w ↦ u (w + ((0 : ℝ), (1 : ℝ)))) = u :=
    funext fun ⟨s, t⟩ ↦ by simpa using hper s t
  have hH1 : (fun w : ℝ × ℝ ↦ H (w + ((0 : ℝ), (1 : ℝ))).2) = fun w ↦ H w.2 :=
    funext fun w ↦ by simpa using hHper w.2
  have hgper (s t : ℝ) : ENNReal.ofReal
      (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u (s, t + 1)) =
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u (s, t)) := by
    have h := ω.floerEnergyDensity_comp_add_right (fun _ _ ↦ 0) (fun w ↦ H w.2) u
      ((0 : ℝ), (1 : ℝ)) (s, t)
    simp only [hu1, hH1, Prod.mk_add_mk, add_zero] at h
    rw [h]
  have htr := ω.constSmooth.lintegral_floerEnergyDensity_comp_add_right (fun _ _ ↦ 0)
    (fun w ↦ H w.2) u (s₀, 0) (univ ×ˢ Icc (-1) 2)
  rw [hpre] at htr
  simp only [floerEnergyDensity_constSmooth] at htr
  refine (lintegral_mono_set hsub).trans (le_of_eq_of_le ?_
    (htr.le.trans (setLIntegral_univ_prod_Icc_neg_one_two_le hgper)))
  refine lintegral_congr fun w ↦ congrArg ENNReal.ofReal ?_
  exact (ω.floerEnergyDensity_cylindrical_comp_add_right H u s₀ w).trans
    (ω.floerEnergyDensity_comp_add_right _ _ u _ w).symm

/-- A translate `(s, t) ↦ u(s + s₀, t)` of a Floer cylinder of a Hamiltonian `H_t` for an almost
complex structure `J_t(x)` is again one. -/
private theorem isComplexLinearMap_perturbedFDeriv_comp_add_right {H : ℝ → V → ℝ}
    {J : ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V}
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (s₀ : ℝ) (w : ℝ × ℝ) : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J w.2 (u (w + (s₀, 0))))
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ u (w + (s₀, 0))) w :
        ℝ × ℝ →ₗ[ℝ] V) := by
  have h := ω.perturbedFDeriv_comp_add_right (fun _ _ ↦ 0) (fun w ↦ H w.2) u (s₀, 0) w
  simp only [Prod.snd_add, add_zero] at h
  have h2 : (w + (s₀, (0 : ℝ))).2 = w.2 := by rw [Prod.snd_add, add_zero]
  rw [h, ← h2]
  exact hfl _

/-- The energy bound on the window `(-1, 1) × (-1/2, 3/2)` in the form that the compactness
theorems take: if a Floer cylinder `u` of period one, of a Hamiltonian `H_t` of period one in `t`
for an almost complex structure `J_t(x)` tamed by `ω` on `ℝ × K`, has image in `K` and energy at
most `E` over the strip `ℝ × [0, 1]`, then the energy density of its translate
`(s, t) ↦ u(s + s₀, t)` is integrable on the window, with integral at most `3 E`. -/
private theorem integrableOn_and_setIntegral_floerEnergyDensity_comp_add_le {H : ℝ → V → ℝ}
    {J : ℝ → V → AlmostComplexStructure V} {K : Set V} (hJ : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hH : ContDiff ℝ 3 (Function.uncurry H)) (hHper : Function.Periodic H 1) {u : ℝ × ℝ → V}
    {E : ℝ} (hu : ContDiff ℝ 3 u) (hper : ∀ s t, u (s, t + 1) = u (s, t))
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (huK : ∀ z, u z ∈ K) (hE0 : 0 ≤ E) (hE : ∫⁻ z in univ ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≤
        ENNReal.ofReal E) (s₀ : ℝ) :
    IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (fun w ↦ u (w + (s₀, 0)))) (ball ((0 : ℝ), (1 / 2 : ℝ)) 1) ∧
      ∫ w in ball ((0 : ℝ), (1 / 2 : ℝ)) 1, ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (fun w ↦ u (w + (s₀, 0))) w ≤ 3 * E := by
  refine ω.integrableOn_and_setIntegral_floerEnergyDensity_le isOpen_ball measurableSet_ball
    subset_rfl (((hu.comp (contDiff_id.add contDiff_const)).of_le (by norm_num)).contDiffOn)
    contDiffOn_const ((contDiff_uncurry_cylindrical hH).of_le (by norm_num)).contDiffOn
    (fun w _ ↦ ω.floerEnergyDensity_nonneg (hJ _ _ (huK _))
      (isComplexLinearMap_perturbedFDeriv_comp_add_right hfl _ w)) (by positivity) ?_
  refine (lintegral_ball_floerEnergyDensity_comp_add_le hHper hper _).trans ?_
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  gcongr

/-- The segment `{0} × [0, 1]` lies in the window `(-1, 1) × (-1/2, 3/2)`. -/
private theorem singleton_prod_Icc_subset_ball :
    ({0} ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ⊆ ball ((0 : ℝ), (1 / 2 : ℝ)) 1 := by
  rintro ⟨s, t⟩ ⟨hs, h0, h1⟩
  rw [mem_singleton_iff] at hs
  subst hs
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
  exact ⟨by norm_num, by constructor <;> linarith⟩

/-- **Floer cylinders of small energy for a compact family of Hamiltonians have bounded
derivatives.** Let `Hs p` be a family of Hamiltonians of period one in `t`, depending jointly
`C³` on `(p, t, x)`, and `Js p` a family of almost complex structures depending jointly `C²` on
`(p, t, x)`. Let `C` be a compact set of parameters and `K ⊆ V` compact, with `Js p t x` tamed by
`ω` for `p ∈ C` and `x ∈ K`. There are `δ > 0` and `M` with the following property, for every
`p ∈ C`. Let `u` be a `C³` solution of the Floer equation
`∂s u + (Js p)_t(u) (∂t u - X_{(Hs p)_t}(u)) = 0` of `(Hs p)_t dt`, of period one in `t`, with
image in `K` and Floer energy at most `δ` over the strip `ℝ × [0, 1]`. Then `‖du‖ ≤ M`
everywhere. -/
theorem exists_pos_forall_norm_fderiv_le_of_mem_of_setLIntegral_floerEnergyDensity_le
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] {Hs : P → ℝ → V → ℝ}
    {Js : P → ℝ → V → AlmostComplexStructure V} {C : Set P} {K : Set V}
    (hHs : ContDiff ℝ 3 (fun q : P × ℝ × V ↦ Hs q.1 q.2.1 q.2.2))
    (hHper : ∀ p ∈ C, Function.Periodic (Hs p) 1)
    (hJs : ContDiff ℝ 2
      (fun q : P × ℝ × V ↦ (Js q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap))
    (hC : IsCompact C) (hK : IsCompact K) (hJt : ∀ p ∈ C, ∀ t, ∀ x ∈ K, ω.Tames (Js p t x)) :
    ∃ δ > 0, ∃ M, ∀ ⦃p : P⦄ ⦃u : ℝ × ℝ → V⦄, p ∈ C → ContDiff ℝ 3 u →
      (∀ s t, u (s, t + 1) = u (s, t)) →
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Js p z.2 (u z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ Hs p w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ z, u z ∈ K) →
      ∫⁻ z in univ ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ Hs p w.2) u z) ≤
        ENNReal.ofReal δ →
      ∀ z, ‖fderiv ℝ u z‖ ≤ M := by
  set Ω : Set (ℝ × ℝ) := ball ((0 : ℝ), (1 / 2 : ℝ)) 1
  have hπ : ContDiff ℝ ⊤ (fun q : P × ((ℝ × ℝ) × V) ↦ (q.1, q.2.1.2, q.2.2)) := by
    fun_prop
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun _ _ _ ↦ 0) (Kt := fun p z ↦ Hs p z.2) (J := fun p z ↦ Js p z.2)
    (W := univ) (C := C) (D := closedBall ((0 : ℝ), (1 / 2 : ℝ)) 1) (K := K) isOpen_univ
    contDiffOn_const (hHs.comp (hπ.of_le le_top)).contDiffOn
    (hJs.comp (hπ.of_le le_top)).contDiffOn hC (isCompact_closedBall _ _) hK (subset_univ _)
    fun p hp z _ x hx ↦ hJt p hp z.2 x hx
  refine ⟨δ / 4, by positivity, ?_⟩
  by_contra hM
  push Not at hM
  -- A sequence of cylinders whose derivatives blow up at points `(sₖ, tₖ)` with `tₖ ∈ [0, 1)`.
  choose p u hp hu hper hfl huK hE z hz using fun k : ℕ ↦ hM k
  have hred (k : ℕ) : ∃ t ∈ Ico (0 : ℝ) 1, (k : ℝ) < ‖fderiv ℝ (u k) ((z k).1, t)‖ := by
    have hpd : Function.Periodic (fun t ↦ fderiv ℝ (u k) ((z k).1, t)) 1 :=
      fun t ↦ fderiv_add_snd_of_periodic_snd (hper k) _ t
    obtain ⟨t, ht, heq⟩ := hpd.exists_mem_Ico₀ zero_lt_one (z k).2
    exact ⟨t, ht, by simpa [← heq] using hz k⟩
  choose t ht htz using hred
  -- Translate each cylinder by `(sₖ, 0)`.
  set v : ℕ → ℝ × ℝ → V := fun k w ↦ u k (w + ((z k).1, 0))
  have hvd (k : ℕ) (w : ℝ × ℝ) : fderiv ℝ (v k) w = fderiv ℝ (u k) (w + ((z k).1, 0)) :=
    fderiv_comp_add_right _
  have hvfl (k : ℕ) := isComplexLinearMap_perturbedFDeriv_comp_add_right (hfl k) (z k).1
  have hint (k : ℕ) := integrableOn_and_setIntegral_floerEnergyDensity_comp_add_le
    (H := Hs (p k)) (hJt _ (hp k)) (hHs.comp ((contDiff_const (c := p k)).prodMk contDiff_id))
    (hHper _ (hp k)) (hu k) (hper k) (hfl k) (huK k) (by positivity) (hE k) (z k).1
  obtain ⟨φ, -, Z, -, hφ, -, -, -, hcard, -, hbd, -⟩ :=
    hconv (Ω := Ω) (p := p) (u := v) isOpen_ball ball_subset_closedBall (fun k ↦ hp k)
      (fun k ↦ ((hu k).comp (contDiff_id.add contDiff_const)).contDiffOn)
      (fun k w _ ↦ hvfl k w) (fun k w _ ↦ huK k _) (fun k ↦ (hint k).1) (fun k ↦ (hint k).2)
  -- Below the threshold there is no bubbling point.
  have hZ : Z = ∅ := by
    rw [← Finset.card_eq_zero]
    by_contra hne
    have h1 : (1 : ℝ) ≤ Z.card := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
    nlinarith
  -- So the derivatives are bounded on the segment `{0} × [0, 1]`, a contradiction.
  have hseg : ({0} ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ⊆ Ω \ ↑Z := by
    rw [hZ, Finset.coe_empty, sdiff_empty]
    exact singleton_prod_Icc_subset_ball
  obtain ⟨B, hB⟩ := hbd _ (isCompact_singleton.prod isCompact_Icc) hseg
  obtain ⟨n, hn⟩ := exists_nat_ge B
  have hmem : ((0 : ℝ), t (φ n)) ∈ ({0} ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) :=
    ⟨rfl, (ht (φ n)).1, (ht (φ n)).2.le⟩
  have h := hB n _ hmem
  rw [hvd, Prod.mk_add_mk, zero_add, add_zero] at h
  have hφn : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
  linarith [htz (φ n)]

end TauCeti.SymplecticForm

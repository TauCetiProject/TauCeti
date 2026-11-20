/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.SmallHamiltonian
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.MeasureTheory.Integral.Rectangle
import TauCeti.MeasureTheory.Measure.Haar.Prod

/-!
# Floer cylinders of small energy for small Hamiltonians are time-independent

Let `(V, ω)` be a symplectic vector space, `J` a constant almost complex structure tamed by `ω`,
`H : V → ℝ` an autonomous `C³` Hamiltonian and `K ⊆ V` compact. For `ε ∈ [0, 1]` consider the
Floer cylinders of `ε H`: maps `u : ℝ × ℝ → V` of period one in `t` solving
`∂s u + J (∂t u - ε X_H(u)) = 0`, with image in `K`.

**The a priori bound.** There are `δ > 0` and `M` such that every such cylinder whose Floer energy
over the strip `ℝ × [0, 1]` is at most `δ` satisfies `‖du‖ ≤ M` everywhere, for every
`ε ∈ [0, 1]`
(`exists_pos_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_const_mul_le`).
For a single Hamiltonian, small energy over a band already bounds the derivative
(`TauCeti.SymplecticForm.exists_pos_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_le`);
the point here is that `δ` and `M` are uniform over the family `ε H`. This is the absence of
bubbling below the energy threshold of Gromov–Floer compactness. If the derivatives of a sequence
of such cylinders blew up at points `zₖ`, translating each cylinder in `s` (the data do not depend
on `s`) and using its periodicity in `t` would move `zₖ` into the compact segment `{0} × [0, 1]`.
The translated cylinders have energy at most `3 δ` on the window `(-1, 1) × (-1/2, 3/2)`, which
lies in the strip `ℝ × [-1, 2]`. Compactness over the compact parameter window `[0, 1]`
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
then gives a subsequence whose derivatives are bounded on `{0} × [0, 1]` once `3 δ` is below the
bubbling threshold, since then there is no bubbling point.

**Time independence.** If moreover the derivatives of `X_H` are bounded everywhere,
`‖dX_H‖ ≤ a` and `‖d²X_H‖ ≤ c`, and the inner product of `V` is the metric `ω(·, J ·)`, then there
is `ε₀ > 0` such that for `0 ≤ ε ≤ ε₀` every such cylinder of energy at most `δ` is independent of
`t`, and `s ↦ u(s, 0)` is an upward gradient line of `ε H`
(`exists_pos_forall_eq_comp_fst_of_setLIntegral_floerEnergyDensity_const_mul_le`).
Indeed `X_{ε H} = ε X_H`, so `‖dX_{ε H}‖ ≤ ε a` and `‖d²X_{ε H}‖ ≤ ε c`, while the a priori
bound `M` does not depend on `ε`. For small `ε` the smallness condition `ε c M < 2 (2π - ε a)²` of
`TauCeti.SymplecticForm.eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv` holds.

This is the step of Floer's comparison of the Floer complex of a `C²`-small Morse Hamiltonian
with its Morse complex that bounds the derivative of the Floer cylinders in terms of the
Hamiltonian. A cylinder of `ε H` between two constant orbits has energy `ε` times the difference
of the values of `H` at them, so for small `ε` its energy is below `δ`; that energy identity is not
used here. The bounds on `X_H` hold for a Hamiltonian with compact support, and for a Hamiltonian
invariant under a lattice `Λ ⊆ V`, the lift of a Hamiltonian on the flat torus `V / Λ`.

## Main results

* `exists_pos_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_const_mul_le`:
  Floer cylinders of `ε H`, `ε ∈ [0, 1]`, in a compact set and of small energy have uniformly
  bounded derivatives.
* `exists_pos_forall_eq_comp_fst_of_setLIntegral_floerEnergyDensity_const_mul_le`:
  for small `ε` they are independent of `t`, and are gradient lines of `ε H`.

## References

* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (inhomogeneous equations).
-/

public section

open Real Set Filter Topology MeasureTheory Metric
open scoped Gradient RealInnerProductSpace ENNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : V → ℝ}

/-- The Floer energy of a cylinder of period one over the window `(-1, 1) × (-1/2, 3/2)`,
translated by `(s₀, 0)`, is at most three times its energy over the strip `ℝ × [0, 1]`. -/
private theorem lintegral_ball_comp_add_le {g : ℝ × ℝ → ℝ≥0∞}
    (hg : ∀ s t, g (s, t + 1) = g (s, t)) (s₀ : ℝ) :
    ∫⁻ z in ball ((0 : ℝ), (1 / 2 : ℝ)) 1, g (z + (s₀, 0)) ≤
      3 * ∫⁻ z in univ ×ˢ Icc 0 1, g z := by
  have hsub : ball ((0 : ℝ), (1 / 2 : ℝ)) 1 ⊆ univ ×ˢ Icc (-1) 2 := by
    intro z hz
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hz
    obtain ⟨-, h⟩ := hz
    rw [abs_lt] at h
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  have hφ := measurePreserving_add_right (volume : Measure (ℝ × ℝ)) (s₀, (0 : ℝ))
  have hpre : (· + (s₀, (0 : ℝ))) ⁻¹' (univ ×ˢ Icc (-1 : ℝ) 2) = univ ×ˢ Icc (-1 : ℝ) 2 := by
    ext ⟨s, t⟩
    simp
  calc ∫⁻ z in ball ((0 : ℝ), (1 / 2 : ℝ)) 1, g (z + (s₀, 0))
      ≤ ∫⁻ z in univ ×ˢ Icc (-1) 2, g (z + (s₀, 0)) := lintegral_mono_set hsub
    _ = ∫⁻ z in univ ×ˢ Icc (-1) 2, g z := by
        rw [← hφ.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight _) g, hpre]
    _ ≤ 3 * ∫⁻ z in univ ×ˢ Icc 0 1, g z := setLIntegral_univ_prod_Icc_neg_one_two_le hg

/-- The Floer energy of a translate `(s, t) ↦ u(s + s₀, t)` of a Floer cylinder of `ε H` of period
one over the window `(-1, 1) × (-1/2, 3/2)` is at most three times the energy of `u` over the
strip `ℝ × [0, 1]`. -/
private theorem lintegral_ball_floerEnergyDensity_comp_add_le {u : ℝ × ℝ → V} {ε : ℝ}
    (hper : ∀ s t, u (s, t + 1) = u (s, t)) (s₀ : ℝ) :
    ∫⁻ w in ball ((0 : ℝ), (1 / 2 : ℝ)) 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun _ x ↦ ε * H x) (fun w ↦ u (w + (s₀, 0))) w) ≤
      3 * ∫⁻ z in univ ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u z) := by
  have hu1 : (fun w ↦ u (w + ((0 : ℝ), (1 : ℝ)))) = u :=
    funext fun ⟨s, t⟩ ↦ by simpa using hper s t
  have hgper (s t : ℝ) : ENNReal.ofReal
      (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u (s, t + 1)) =
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u (s, t)) := by
    have h := ω.floerEnergyDensity_comp_add_right (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u
      ((0 : ℝ), (1 : ℝ)) (s, t)
    simp only [hu1, Prod.mk_add_mk, add_zero] at h
    rw [h]
  simp only [fun w ↦ ω.floerEnergyDensity_comp_add_right (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u
    (s₀, 0) w]
  exact lintegral_ball_comp_add_le (g := fun w ↦ ENNReal.ofReal
    (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u w)) hgper s₀

/-- A translate `(s, t) ↦ u(s + s₀, t)` of a Floer cylinder of the autonomous Hamiltonian `ε H` is
again one. -/
private theorem isComplexLinearMap_perturbedFDeriv_comp_add_right {u : ℝ × ℝ → V} {ε : ℝ}
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u z : ℝ × ℝ →ₗ[ℝ] V))
    (v w : ℝ × ℝ) : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) (fun w ↦ u (w + v)) w :
        ℝ × ℝ →ₗ[ℝ] V) := by
  rw [show ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) (fun w ↦ u (w + v)) w =
    ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u (w + v) from
    ω.perturbedFDeriv_comp_add_right (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u v w]
  exact hfl _

/-- The energy bound on the window `(-1, 1) × (-1/2, 3/2)` in the form that the compactness
theorems take: if a Floer cylinder `u` of `ε H` of period one has energy at most `E` over the
strip `ℝ × [0, 1]`, then the energy density of its translate `(s, t) ↦ u(s + s₀, t)` is
integrable on the window, with integral at most `3 E`. -/
private theorem integrableOn_and_setIntegral_floerEnergyDensity_comp_add_le (hJ : ω.Tames J)
    (hH : ContDiff ℝ 3 H) {u : ℝ × ℝ → V} {ε E : ℝ} (hu : ContDiff ℝ 3 u)
    (hper : ∀ s t, u (s, t + 1) = u (s, t))
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE0 : 0 ≤ E) (hE : ∫⁻ z in univ ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u z) ≤
        ENNReal.ofReal E) (s₀ : ℝ) :
    IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ x ↦ ε * H x)
        (fun w ↦ u (w + (s₀, 0)))) (ball ((0 : ℝ), (1 / 2 : ℝ)) 1) ∧
      ∫ w in ball ((0 : ℝ), (1 / 2 : ℝ)) 1, ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun _ x ↦ ε * H x) (fun w ↦ u (w + (s₀, 0))) w ≤ 3 * E := by
  refine ω.integrableOn_and_setIntegral_floerEnergyDensity_le isOpen_ball measurableSet_ball
    subset_rfl (((hu.comp (contDiff_id.add contDiff_const)).of_le (by norm_num)).contDiffOn)
    contDiffOn_const ((contDiff_const.mul (hH.comp contDiff_snd)).of_le (by norm_num)).contDiffOn
    (fun w _ ↦ ω.floerEnergyDensity_nonneg hJ
      (isComplexLinearMap_perturbedFDeriv_comp_add_right hfl _ w)) (by positivity) ?_
  refine (lintegral_ball_floerEnergyDensity_comp_add_le hper _).trans ?_
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

/-- **Floer cylinders of small energy for a family of small Hamiltonians have bounded
derivatives.** Let `J` be a constant almost complex structure tamed by `ω`, `H` a `C³` autonomous
Hamiltonian and `K ⊆ V` compact. There are `δ > 0` and `M` with the following property, for every
`ε ∈ [0, 1]`. Let `u` be a `C³` solution of the Floer equation `∂s u + J (∂t u - ε X_H(u)) = 0`
of `ε H dt`, of period one in `t`, with image in `K` and Floer energy at most `δ` over the strip
`ℝ × [0, 1]`. Then `‖du‖ ≤ M` everywhere. -/
theorem exists_pos_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_const_mul_le
    (hJ : ω.Tames J) (hH : ContDiff ℝ 3 H) {K : Set V} (hK : IsCompact K) :
    ∃ δ > 0, ∃ M, ∀ ⦃ε : ℝ⦄ ⦃u : ℝ × ℝ → V⦄, ε ∈ Icc (0 : ℝ) 1 → ContDiff ℝ 3 u →
      (∀ s t, u (s, t + 1) = u (s, t)) →
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ z, u z ∈ K) →
      ∫⁻ z in univ ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u z) ≤
        ENNReal.ofReal δ →
      ∀ z, ‖fderiv ℝ u z‖ ≤ M := by
  set Ω : Set (ℝ × ℝ) := ball ((0 : ℝ), (1 / 2 : ℝ)) 1
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (P := ℝ) (Ks := fun _ _ _ ↦ 0) (Kt := fun p _ x ↦ p * H x) (J := fun _ _ _ ↦ J)
    (W := univ) (C := Icc 0 1) (D := closedBall ((0 : ℝ), (1 / 2 : ℝ)) 1) (K := K) isOpen_univ
    contDiffOn_const ((contDiff_fst.mul (hH.comp (contDiff_snd.comp contDiff_snd))).contDiffOn)
    contDiffOn_const isCompact_Icc (isCompact_closedBall _ _) hK (subset_univ _)
    fun _ _ _ _ _ _ ↦ hJ
  refine ⟨δ / 4, by positivity, ?_⟩
  by_contra hM
  push Not at hM
  -- A sequence of cylinders whose derivatives blow up at points `(sₖ, tₖ)` with `tₖ ∈ [0, 1)`.
  choose ε u hε hu hper hfl huK hE z hz using fun k : ℕ ↦ hM k
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
  have hvfl (k : ℕ) := isComplexLinearMap_perturbedFDeriv_comp_add_right (hfl k) ((z k).1, 0)
  have hint (k : ℕ) := integrableOn_and_setIntegral_floerEnergyDensity_comp_add_le hJ hH (hu k)
    (hper k) (hfl k) (by positivity) (hE k) (z k).1
  obtain ⟨φ, -, Z, -, hφ, -, -, -, hcard, -, hbd, -⟩ :=
    hconv (Ω := Ω) (p := ε) (u := v) isOpen_ball ball_subset_closedBall (fun k ↦ hε k)
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

/-- The Hamiltonian vector field of `ε H` is `ε X_H`, so for `ε ≥ 0` bounds `a` on `‖dX_H‖` and
`c` on `‖d²X_H‖` give the bounds `ε a` on `‖dX_{ε H}‖` and `ε c` on `‖d²X_{ε H}‖`. -/
private theorem norm_fderiv_hamiltonianVectorField_const_mul_le {ε a c : ℝ} (hε0 : 0 ≤ ε)
    (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c) :
    (∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField (fun x ↦ ε * H x)) x‖ ≤ ε * a) ∧
      ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField (fun x ↦ ε * H x))) x‖ ≤ ε * c := by
  have hX : ω.hamiltonianVectorField (fun x ↦ ε * H x) = ε • ω.hamiltonianVectorField H :=
    funext (ω.hamiltonianVectorField_const_mul ε H)
  refine ⟨fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [hX, fderiv_const_smul_field, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hε0]
    exact mul_le_mul_of_nonneg_left (ha x) hε0
  · rw [hX, fderiv_const_smul_field, fderiv_const_smul_field, Pi.smul_apply]
    set L := fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hε0 ((norm_nonneg L).trans (hc x)))
      fun v ↦ ?_
    rw [smul_apply, norm_smul, Real.norm_of_nonneg hε0, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((L.le_opNorm v).trans (mul_le_mul_of_nonneg_right (hc x) (norm_nonneg v))) hε0

/-- The smallness conditions `ε a < 2π` and `ε b < 2 (2π - ε a)²` hold for
`ε ≤ min (π / (a + 1)) (π² / (b + 1))`. -/
private theorem mul_lt_two_mul_pi_and_mul_lt_of_le_div {ε a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hεa : ε ≤ π / (a + 1)) (hεb : ε ≤ π ^ 2 / (b + 1)) :
    ε * a < 2 * π ∧ ε * b < 2 * (2 * π - ε * a) ^ 2 := by
  have ha : ε * a < π := by
    have h : π / (a + 1) * a < π := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [pi_pos]
    exact (mul_le_mul_of_nonneg_right hεa ha0).trans_lt h
  have hb : ε * b < π ^ 2 := by
    have h : π ^ 2 / (b + 1) * b < π ^ 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [pi_pos]
    exact (mul_le_mul_of_nonneg_right hεb hb0).trans_lt h
  exact ⟨by linarith [pi_pos], by nlinarith [pi_pos]⟩

/-- **Floer cylinders of small energy for a small Hamiltonian are time-independent gradient
lines.** Let the inner product of `V` be the metric `ω(·, J ·)` of a constant compatible almost
complex structure `J`, let `H` be a `C³` autonomous Hamiltonian with `‖dX_H‖ ≤ a` and
`‖d²X_H‖ ≤ c` everywhere, and let `K ⊆ V` be compact. There are `ε₀ > 0` and `δ > 0` with the
following property, for every `ε ∈ [0, ε₀]`. Let `u` be a `C³` solution of the Floer equation
`∂s u + J (∂t u - ε X_H(u)) = 0` of `ε H dt`, of period one in `t`, with image in `K` and Floer
energy at most `δ` over the strip `ℝ × [0, 1]`. Then `u(s, t) = u(s, 0)`, and `γ(s) = u(s, 0)`
solves `γ' = ∇(ε H)(γ)`. -/
theorem exists_pos_forall_eq_comp_fst_of_setLIntegral_floerEnergyDensity_const_mul_le
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hH : ContDiff ℝ 3 H) {a c : ℝ}
    (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    {K : Set V} (hK : IsCompact K) :
    ∃ ε₀ > 0, ∃ δ > 0, ∀ ⦃ε : ℝ⦄ ⦃u : ℝ × ℝ → V⦄, ε ∈ Icc 0 ε₀ → ContDiff ℝ 3 u →
      (∀ s t, u (s, t + 1) = u (s, t)) →
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ z, u z ∈ K) →
      ∫⁻ z in univ ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u z) ≤
        ENNReal.ofReal δ →
      u = (fun z ↦ u (z.1, 0)) ∧
        ∀ s, HasDerivAt (fun s ↦ u (s, 0)) (∇ (fun x ↦ ε * H x) (u (s, 0))) s := by
  have hJ : ω.Tames J := fun v hv ↦ by
    rw [hg]
    exact real_inner_self_pos.2 hv
  obtain ⟨δ, hδ, M, hM⟩ :=
    exists_pos_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_const_mul_le hJ hH hK
  have ha0 : 0 ≤ a := (norm_nonneg (fderiv ℝ (ω.hamiltonianVectorField H) 0)).trans (ha 0)
  have hc0 : 0 ≤ c :=
    (norm_nonneg (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) 0)).trans (hc 0)
  set M' := max M 0
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hcM : 0 ≤ c * M' := mul_nonneg hc0 hM'0
  refine ⟨min 1 (min (π / (a + 1)) (π ^ 2 / (c * M' + 1))), by positivity, δ, hδ,
    fun ε u hε hu hper hfl huK hE ↦ ?_⟩
  obtain ⟨hε0, hε₀⟩ := hε
  have hε1 : ε ≤ 1 := hε₀.trans (min_le_left _ _)
  have hεa : ε ≤ π / (a + 1) := hε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεc : ε ≤ π ^ 2 / (c * M' + 1) := hε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbd (z : ℝ × ℝ) : ‖fderiv ℝ u z‖ ≤ M' :=
    (hM ⟨hε0, hε1⟩ hu hper hfl huK hE z).trans (le_max_left _ _)
  -- The derivatives of `X_{ε H} = ε X_H` are bounded by `ε a` and `ε c`, which are small.
  obtain ⟨hπ, hεc'⟩ := mul_lt_two_mul_pi_and_mul_lt_of_le_div ha0 hcM hεa hεc
  rw [← mul_assoc] at hεc'
  obtain ⟨haε, hcε⟩ := norm_fderiv_hamiltonianVectorField_const_mul_le (ω := ω) hε0 ha hc
  have hH' : ContDiff ℝ 3 (fun x ↦ ε * H x) := contDiff_const.mul hH
  exact ⟨eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv hg hH' haε hcε hπ hεc' hu hper hfl hbd,
    hasDerivAt_gradient_of_isComplexLinearMap_perturbedFDeriv hg hH' haε hcε hπ hεc' hu hper hfl
      hbd⟩

end TauCeti.SymplecticForm

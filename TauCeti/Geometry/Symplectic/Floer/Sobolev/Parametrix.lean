/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.Parametrix
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Stationary
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# The linearized Floer operator on the cylinder is Fredholm in a unitary trivialization

Let `F` be a finite-dimensional complex inner product space with symplectic form
`ω = Im ⟪·, ·⟫`, and let `D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` be the Sobolev realization
(`TauCeti.SymplecticForm.floerSobolevOperator`) of the linearized Floer operator along a map
`u : ℝ × ℝ → F`, for Floer data `(i, K_s, K_t)` with the complex structure `i` of `F` and
Hamiltonian perturbations that are cylindrical near the ends: `(K_s, K_t) = (0, H₋_t)` for
`s ≤ -R` and `(0, H₊_t)` for `s ≥ R` (`TauCeti.Floer.IsCylindricalNearEnds`). This file proves
that `D_u` is Fredholm whenever the loops `u(s, ·)` converge uniformly to nondegenerate
one-periodic orbits `x₋` of `H₋` as `s → -∞` and `x₊` of `H₊` as `s → +∞`
(`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical`). The two orbits may be
different, and `u` need not solve the Floer equation: only its asymptotics matter. Floer
trajectories, with the `s`-independent data `(i, 0, H_t)`, are the case `R = 0`
(`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator`); continuation cylinders are the case
of an `s`-dependent `K_t` interpolating between `H₋` and `H₊`.

The Fredholm property is what makes the Floer moduli spaces finite-dimensional, and its index
is their expected dimension. It complements the finite-dimensional kernel and closed range of
`TauCeti.SymplecticForm.finiteDimensional_ker_floerSobolevOperator_of_cylindrical` and
`TauCeti.SymplecticForm.isClosed_range_floerSobolevOperator_of_cylindrical` with the finiteness
of the cokernel.

The result is an instance of the parametrix theorem on the cylinder,
`TauCeti.CylinderSobolev.isFredholm_jetOperator_comp_subtypeL_of_isInvertible`, with models at the
ends the linearized operators at the stationary cylinders over `x₋` and `x₊`, which are invertible
on `W^{1,2}` in a unitary trivialization
(`TauCeti.SymplecticForm.isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt`). Because the
complex structure is the constant `i`, the operator and its models have the same principal part
`∂s + i ∂t`, and the derivative of the complex structure does not enter the zeroth-order part.
On the ends the zeroth-order parts are `-i dX_{H±_t}(u(s, t))` and `-i dX_{H±_t}(x±(t))`, which
are uniformly close far out because `u(s, ·) → x±` uniformly and `dX_{H±_t}` is uniformly
continuous on compact sets. For the same reason the coefficient field of `D_u` is bounded for any
continuous `u` with these asymptotics; no condition on the derivatives of `u` is needed.

## Main results

* `TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical`: for data `(i, K_s, K_t)`
  cylindrical near the ends, `D_u` is Fredholm along any continuous map asymptotic to
  nondegenerate orbits at both ends.
* `TauCeti.SymplecticForm.isFredholm_floerSobolevOperator`: the case of a Floer trajectory, with
  data `(i, 0, H_t)`, between nondegenerate orbits of `H`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm property of `∂s + J₀ ∂t + S(s, t)` along a Floer
  trajectory between nondegenerate orbits.
-/

public section

noncomputable section

open Filter Set Function MeasureTheory Topology ContinuousLinearMap
open scoped NNReal ENNReal Manifold

namespace TauCeti.SymplecticForm

open CylinderSobolev
open StripSobolev (stripMeasure)

section Constant

/-! ### The coefficient field for a constant complex structure -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- For a constant complex structure `J₀`, at a point where the data are those `(0, H_t)` of a
Floer trajectory, the coefficient field of the linearized Floer operator is that of
`∂s + J₀ ∂t - J₀ dX_{H_t}(u)`. -/
private theorem floerJetCoeff_const_of_eq (ω : SymplecticForm V) (J₀ : V →L[ℝ] V)
    {Ks Kt : ℝ × ℝ → V → ℝ} {H : ℝ → V → ℝ} (u : ℝ × ℝ → V) {z : ℝ × ℝ} (hKs : Ks z = 0)
    (hKt : Kt z = H z.2) :
    ω.floerJetCoeff (fun _ _ ↦ J₀) Ks Kt u z =
      firstOrderJetCoeff J₀ (-J₀.comp (fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (u z))) := by
  rw [floerJetCoeff_const, hKs, hKt, Pi.zero_def, hamiltonianVectorField_const]
  simp

/-- Along maps whose loops converge uniformly to a continuous loop `x`, the maps
`J₀ dX_{H_t}(u(s, t))` converge uniformly to `J₀ dX_{H_t}(x(t))` for `t ∈ [0, 1]`. -/
private theorem tendstoUniformlyOn_comp_fderiv_hamiltonianVectorField (ω : SymplecticForm V)
    (J₀ : V →L[ℝ] V) {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (uncurry H)) {x : ℝ → V}
    (hx : Continuous x) {u : ℝ × ℝ → V} {l : Filter ℝ}
    (hu : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l (Icc 0 1)) :
    TendstoUniformlyOn
      (fun s t ↦ J₀.comp (fderiv ℝ (ω.hamiltonianVectorField (H t)) (u (s, t))))
      (fun t ↦ J₀.comp (fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t))) l (Icc 0 1) := by
  have hP : Continuous fun p : ℝ × V ↦
      J₀.comp (fderiv ℝ (ω.hamiltonianVectorField (H p.1)) p.2) :=
    continuous_const.clm_comp
      (ContDiff.fderiv (f := fun (p : ℝ × V) y ↦ ω.hamiltonianVectorField (H p.1) y)
        ((ω.contDiff_hamiltonianVectorField_uncurry (n := 1) (K := H) hH).comp
          (contDiff_fst.fst.prodMk contDiff_snd)) (contDiff_snd (n := 0)) (by simp)).continuous
  exact (isCompact_Icc.image (continuous_id.prodMk hx)).comp_tendstoUniformlyOn
    (fun _ _ ↦ hP.continuousAt) hu.graph

/-- **The coefficient field is asymptotic to the model at an end.** For a constant complex
structure `J₀`, if the data are eventually those `(0, H_t)` of a Floer trajectory along `l` and the
loops of `u` converge uniformly to a continuous loop `x` along `l`, then the coefficient field of
the linearized Floer operator along `u` is eventually uniformly close, on the strip, to that along
the stationary cylinder over `x`. -/
private theorem eventually_norm_floerJetCoeff_sub_lt (ω : SymplecticForm V) (J₀ : V →L[ℝ] V)
    {Ks Kt : ℝ × ℝ → V → ℝ} {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (uncurry H)) {x : ℝ → V}
    (hx : Continuous x) {u : ℝ × ℝ → V} {l : Filter ℝ}
    (hu : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l (Icc 0 1))
    (hK : ∀ᶠ s in l, ∀ t, Ks (s, t) = 0 ∧ Kt (s, t) = H t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in l, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖ω.floerJetCoeff (fun _ _ ↦ J₀) Ks Kt u (s, t) -
        ω.floerJetCoeff (fun _ _ ↦ J₀) (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2) (s, t)‖ <
          ε := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_comp_fderiv_hamiltonianVectorField ω J₀ hH hx hu) ε hε, hK]
    with s hs hKs t ht
  rw [floerJetCoeff_const_of_eq ω J₀ u (hKs t).1 (hKs t).2,
    floerJetCoeff_const_of_eq ω J₀ _ (H := H) rfl rfl]
  refine (norm_firstOrderJetCoeff_sub_firstOrderJetCoeff_le _ _ _).trans_lt ?_
  rw [neg_sub_neg, ← dist_eq_norm]
  exact hs t ht

/-- For a constant complex structure `J₀`, the coefficient field of the linearized Floer operator
along a continuous map `u` is essentially bounded on the cylinder when the data are `C²` along the
graph of `u` and equal to those `(0, H±_t)` of Floer trajectories far out on the ends, and the
loops of `u` converge uniformly to continuous loops at both ends. -/
private theorem memLp_floerJetCoeff_const (ω : SymplecticForm V) (J₀ : V →L[ℝ] V)
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} (hu : Continuous u)
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    {Hm : ℝ → V → ℝ} (hHm : ContDiff ℝ 2 (uncurry Hm)) {xm : ℝ → V} (hxm : Continuous xm)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hm : ∀ᶠ s in atBot, ∀ t, Ks (s, t) = 0 ∧ Kt (s, t) = Hm t)
    {Hp : ℝ → V → ℝ} (hHp : ContDiff ℝ 2 (uncurry Hp)) {xp : ℝ → V} (hxp : Continuous xp)
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hp : ∀ᶠ s in atTop, ∀ t, Ks (s, t) = 0 ∧ Kt (s, t) = Hp t) :
    MemLp (ω.floerJetCoeff (fun _ _ ↦ J₀) Ks Kt u) ∞ stripMeasure := by
  set M := ω.floerJetCoeff (fun _ _ ↦ J₀) Ks Kt u
  -- `M` is continuous: it is a continuous function of `dX_{K_s(z)}(u z)` and `dX_{K_t(z)}(u z)`.
  have hM : Continuous M := by
    refine continuous_iff_continuousAt.2 fun z ↦ ?_
    have hu₀ : ContDiffAt ℝ 0 u z := (contDiff_zero.2 hu).contDiffAt
    have hdXs : ContinuousAt (fun z ↦ fderiv ℝ (ω.hamiltonianVectorField (Ks z)) (u z)) z :=
      ((ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) (hKs z)).fderiv
        (f := fun z y ↦ ω.hamiltonianVectorField (Ks z) y) hu₀ le_rfl).continuousAt
    have hdXt : ContinuousAt (fun z ↦ fderiv ℝ (ω.hamiltonianVectorField (Kt z)) (u z)) z :=
      ((ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) (hKt z)).fderiv
        (f := fun z y ↦ ω.hamiltonianVectorField (Kt z) y) hu₀ le_rfl).continuousAt
    rw [show M = _ from funext (floerJetCoeff_const ω J₀ Ks Kt u)]
    exact continuousAt_firstOrderJetCoeff continuousAt_const
      (hdXs.neg.sub (continuousAt_const.clm_comp hdXt))
  -- The coefficient fields of the models depend only on `t`, so they are bounded on the strip.
  have hbound {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (uncurry H)) {x : ℝ → V} (hx : Continuous x) :
      ∃ B, ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, ‖ω.floerJetCoeff (fun _ _ ↦ J₀) (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (fun w ↦ x w.2) (s, t)‖ ≤ B := by
    have hc : Continuous fun t ↦
        firstOrderJetCoeff J₀ (-J₀.comp (fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t))) :=
      continuous_iff_continuousAt.2 fun t ↦ continuousAt_firstOrderJetCoeff continuousAt_const
        (continuous_const.clm_comp
          (ω.continuous_fderiv_hamiltonianVectorField_comp hH hx)).neg.continuousAt
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨B, fun s t ht ↦ by rw [floerJetCoeff_const_of_eq ω J₀ _ (H := H) rfl rfl]; exact hB t ht⟩
  obtain ⟨Bm, hBm⟩ := hbound hHm hxm
  obtain ⟨Bp, hBp⟩ := hbound hHp hxp
  -- Far out on each end, `M` is within `1` of the model; in between, `M` is bounded on a compact
  -- set.
  obtain ⟨Sm, hSm⟩ :=
    eventually_atBot.1 (eventually_norm_floerJetCoeff_sub_lt ω J₀ hHm hxm huxm hm one_pos)
  obtain ⟨Sp, hSp⟩ :=
    eventually_atTop.1 (eventually_norm_floerJetCoeff_sub_lt ω J₀ hHp hxp huxp hp one_pos)
  obtain ⟨B₀, hB₀⟩ := ((isCompact_Icc (a := Sm) (b := Sp)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn hM.continuousOn
  refine memLp_top_of_bound hM.aestronglyMeasurable (max B₀ (max (Bm + 1) (Bp + 1))) ?_
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with ⟨s, t⟩ hz
  have ht : t ∈ Icc (0 : ℝ) 1 := hz.2
  rcases le_or_gt s Sm with hs | hs
  · exact ((norm_le_norm_add_norm_sub' _ _).trans (add_le_add (hBm s t ht)
      (hSm s hs t ht).le)).trans (le_max_of_le_right (le_max_left _ _))
  rcases le_or_gt Sp s with hs' | hs'
  · exact ((norm_le_norm_add_norm_sub' _ _).trans (add_le_add (hBp s t ht)
      (hSp s hs' t ht).le)).trans (le_max_of_le_right (le_max_right _ _))
  exact (hB₀ (s, t) ⟨⟨hs.le, hs'.le⟩, ht⟩).trans (le_max_left _ _)

end Constant

section Unitary

/-! ### The Fredholm property in a unitary trivialization -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The coefficient field of the linearized Floer operator with complex structure `i` at the
stationary cylinder over an orbit of a jointly `C²` Hamiltonian is essentially bounded. -/
private theorem memLp_floerJetCoeff_ofComplexModule_comp_snd (ω : SymplecticForm F)
    {H : ℝ → F → ℝ} (hH : ContDiff ℝ 2 (uncurry H)) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) :
    MemLp (ω.floerJetCoeff
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2)) ∞ stripMeasure := by
  rw [floerJetCoeff_eq_stationaryJetCoeff ω
    (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) H hx]
  exact Floer.memLp_stationaryJetCoeff continuous_const
    (ω.continuous_fderiv_hamiltonianVectorField_comp hH
      (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt))

/-- **The linearized Floer operator on the cylinder is Fredholm in a unitary trivialization.** Let
`F` be a finite-dimensional complex inner product space whose symplectic form `ω` is
`Im ⟪·, ·⟫`, and let the Floer data `(i, K_s, K_t)`, with the complex structure `i` of `F`, be
cylindrical near the ends: equal to `(i, 0, H₋_t)` for `s ≤ -R` and to `(i, 0, H₊_t)` for
`s ≥ R`, with `K_s`, `K_t` of class `C²` along the graph of `u`. Let `H±` be one-periodic, jointly
`C³` time-dependent Hamiltonians whose suspended vector fields are globally Lipschitz, and let
`x±` be one-periodic orbits of `H±` with `x±(0)` a nondegenerate fixed point of the time-one map.
If `u` is a continuous map whose loops `u(s, ·)` converge uniformly on `[0, 1]` to `x₋` as
`s → -∞` and to `x₊` as `s → +∞`, then the realization
`D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer operator is Fredholm. -/
theorem isFredholm_floerSobolevOperator_of_cylindrical (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {Ks Kt : ℝ × ℝ → F → ℝ} {Hm Hp : ℝ → F → ℝ} {R : ℝ}
    {u : ℝ × ℝ → F}
    (hcyl : Floer.IsCylindricalNearEnds (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) Ks
      Kt (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
      (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) Hm Hp R u)
    (hu : Continuous u)
    {Km : ℝ≥0} (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1) {xm : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t) (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    {Kp : ℝ≥0} (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpper : Periodic Hp 1) {xp : ℝ → F}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t) (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1)) :
    (ω.floerSobolevOperator
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        Ks Kt u).IsFredholm := by
  set J₀ := (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap
  have hHm₂ : ContDiff ℝ 2 (uncurry Hm) := hHm.of_le (by norm_num)
  have hHp₂ : ContDiff ℝ 2 (uncurry Hp) := hHp.of_le (by norm_num)
  have hxmc : Continuous xm := continuous_iff_continuousAt.2 fun t ↦ (hxm t).continuousAt
  have hxpc : Continuous xp := continuous_iff_continuousAt.2 fun t ↦ (hxp t).continuousAt
  -- Far out on the ends the data are those of the Floer trajectories of `H₋` and `H₊`.
  have hm : ∀ᶠ s in atBot, ∀ t, Ks (s, t) = 0 ∧ Kt (s, t) = Hm t := by
    filter_upwards [eventually_le_atBot (-R)] with s hs t
    exact ⟨hcyl.hamiltonianS_eq_zero (s, t) fun h ↦ (lt_irrefl _ (hs.trans_lt h.1)),
      hcyl.hamiltonianT_eq_of_le_neg (s, t) hs⟩
  have hp : ∀ᶠ s in atTop, ∀ t, Ks (s, t) = 0 ∧ Kt (s, t) = Hp t := by
    filter_upwards [eventually_ge_atTop R] with s hs t
    exact ⟨hcyl.hamiltonianS_eq_zero (s, t) fun h ↦ (lt_irrefl _ (h.2.trans_le hs)),
      hcyl.hamiltonianT_eq_of_le (s, t) hs⟩
  -- The models: the linearized operators at the stationary cylinders over `x₋` and `x₊`.
  have hDm := ω.isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt hXm hHm hHmper hxm
    hxmper hω hndm
  have hDp := ω.isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt hXp hHp hHpper hxp
    hxpper hω hndp
  rw [floerSobolevOperator_def] at hDm hDp ⊢
  -- All three operators have the principal part `∂s + i ∂t`.
  have hprin {Ks' Kt' : ℝ × ℝ → F → ℝ} {u' : ℝ × ℝ → F} (z : ℝ × ℝ) (a b : F) :
      ω.floerJetCoeff (fun _ _ ↦ J₀) Ks' Kt' u' z (0, a, b) = a + J₀ b := by
    simp [floerJetCoeff_apply]
  refine isFredholm_jetOperator_comp_subtypeL_of_isInvertible
    (memLp_floerJetCoeff_const ω J₀ hu hcyl.contDiffAt_hamiltonianS
      hcyl.contDiffAt_hamiltonianT hHm₂ hxmc huxm hm hHp₂ hxpc huxp hp)
    (memLp_floerJetCoeff_ofComplexModule_comp_snd ω hHm₂ hxm)
    (memLp_floerJetCoeff_ofComplexModule_comp_snd ω hHp₂ hxp) hDm hDp
    (.of_forall fun z a b ↦ by rw [hprin, hprin]) (.of_forall fun z a b ↦ by rw [hprin, hprin])
    (fun ε hε ↦ ?_) (fun ε hε ↦ ?_)
  -- The coefficient field is asymptotic to the models at the ends.
  · obtain ⟨S, hS⟩ :=
      eventually_atBot.1 (eventually_norm_floerJetCoeff_sub_lt ω J₀ hHm₂ hxmc huxm hm hε)
    refine ⟨-S, ?_⟩
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz hzS
    exact (hS z.1 (by linarith) z.2 hz.2).le
  · obtain ⟨S, hS⟩ :=
      eventually_atTop.1 (eventually_norm_floerJetCoeff_sub_lt ω J₀ hHp₂ hxpc huxp hp hε)
    refine ⟨S, ?_⟩
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz hzS
    exact (hS z.1 hzS.le z.2 hz.2).le

/-- **The linearized Floer operator along a Floer trajectory is Fredholm in a unitary
trivialization.** Let `F` be a finite-dimensional complex inner product space whose symplectic
form `ω` is `Im ⟪·, ·⟫`, and let `H` be a one-periodic, jointly `C³` time-dependent Hamiltonian
whose suspended vector field is globally Lipschitz, with one-periodic orbits `x₋` and `x₊` whose
initial points are nondegenerate fixed points of the time-one map. For the `s`-independent Floer
data `(i, 0, H_t)` and a continuous map `u` whose loops converge uniformly on `[0, 1]` to `x₋` as
`s → -∞` and to `x₊` as `s → +∞`, the realization `D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of
the linearized Floer operator is Fredholm. -/
theorem isFredholm_floerSobolevOperator (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) {xm xp : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t) (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t) (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {u : ℝ × ℝ → F} (hu : Continuous u)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1)) :
    (ω.floerSobolevOperator
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) u).IsFredholm :=
  ω.isFredholm_floerSobolevOperator_of_cylindrical hω
    (Floer.isCylindricalNearEnds_comp_snd (J := fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
      contDiff_const (hH.of_le (by norm_num)) u) hu hX hH
    hHper hxm hxmper hndm huxm hX hH hHper hxp hxpper hndp huxp

end Unitary

end TauCeti.SymplecticForm

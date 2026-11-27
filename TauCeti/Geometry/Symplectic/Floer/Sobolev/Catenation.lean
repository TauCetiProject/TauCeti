/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Fredholm
import TauCeti.Analysis.Sobolev.Cylinder.Gluing.Index
import TauCeti.Analysis.SpecialFunctions.SmoothSegmentPath
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Floer.Continuation
import TauCeti.Geometry.Symplectic.Floer.Sobolev.Parametrix
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# The index of the linearized Floer operator is additive under catenation

Let `F` be a finite-dimensional complex inner product space whose symplectic form `ω` is
`Im ⟪·, ·⟫`, and let `x₋`, `y` and `x₊` be nondegenerate one-periodic orbits of Hamiltonians
`H₋`, `H₀` and `H₊`. For Floer data cylindrical near the ends, with compatible almost complex
structures, the realization `D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer
operator along a map `u` from `x₋` to `x₊` is Fredholm, and its index depends only on the end
Hamiltonians and the asymptotic orbits
(`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_of_cylindrical_data`,
`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_of_cylindrical`). This file proves that the
index is additive under catenation at the intermediate orbit `y`:

`ind D_u = ind D_{u₁} + ind D_{u₂}`

for maps `u₁` from `x₋` to `y` and `u₂` from `y` to `x₊`, with any such Floer data
(`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_add`). Taking `x₊ = x₋`, where the index
vanishes, the index from `y` back to `x₋` is minus the index from `x₋` to `y`
(`TauCeti.SymplecticForm.index_floerSobolevOperator_add_eq_zero`). Together with the vanishing of
the index from an orbit to itself, these are the catenation and inversion laws of the index of a
Floer cylinder, the properties shared with the difference `μ(x₊) - μ(x₋)` of gradings of the
asymptotic orbits.

**Proof.** The index of every such operator is that of the data `(i, 0, H_{(s, t)})` of the
continuation homotopy `TauCeti.Floer.continuationHomotopy` between the end Hamiltonians, along the
interpolating cylinder `x(t) + β(s) (x'(t) - x(t))` between the asymptotic orbits, with `β` the
smooth transition from `0` on `s ≤ 0` to `1` on `s ≥ 1`. For these comparison operators, the
coefficient field of the linearized operator at `(s, t)` only depends on the Hamiltonian and on
the value of the map at `(s, t)`, because the complex structure `i` is constant. So the
comparison operator of the glued Hamiltonian
`H₋ + β(s + R) (H₀ - H₋) + β(s - R) (H₊ - H₀)` along the glued cylinder
`x₋ + β(s + R) (y - x₋) + β(s - R) (x₊ - y)`, which runs from `x₋` to `x₊`, has exactly the glued
coefficient field `TauCeti.gluedCoeff` of the two comparison operators from `x₋` to `y` and from `y`
to `x₊`, for every neck length `R ≥ 1`. Their coefficient fields are constant near the glued
ends, equal to that of the stationary cylinder over `y`. The additivity of the index under linear
gluing on the cylinder
(`TauCeti.CylinderSobolev.exists_forall_ge_isFredholm_and_index_jetOperator_gluedCoeff_eq`)
then gives the sum of the indices for long necks.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm theory of the operators `∂s + J ∂t + S` on the
  cylinder and the additivity of their index under gluing.
-/

public section

open Filter Function Set Topology Real MeasureTheory
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

section Interpolation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The cylinder `x(t) + β(s) (x'(t) - x(t))` from the loop `x` to the loop `x'`, the smooth path
`TauCeti.smoothSegmentPath` from `x(t)` to `x'(t)` in each loop. -/
private noncomputable def loopInterpolation (x x' : ℝ → V) (z : ℝ × ℝ) : V :=
  smoothSegmentPath (x z.2) (x' z.2) z.1

private theorem contDiff_loopInterpolation {x x' : ℝ → V} (hx : ContDiff ℝ 1 x)
    (hx' : ContDiff ℝ 1 x') : ContDiff ℝ 1 (loopInterpolation x x') := by
  have h : loopInterpolation x x' = fun z ↦ x z.2 + smoothTransition z.1 • (x' z.2 - x z.2) :=
    funext fun z ↦ smoothSegmentPath_def _ _ z.1
  rw [h]
  exact (hx.comp contDiff_snd).add ((smoothTransition.contDiff.comp contDiff_fst).smul
    ((hx'.comp contDiff_snd).sub (hx.comp contDiff_snd)))

/-- The interpolating cylinder from `x` to `x'` has loops converging uniformly to `x` at `-∞` and
to `x'` at `+∞`, with slice defects for the vector fields of `x` and `x'` tending uniformly to
zero there. -/
private theorem tendstoUniformlyOn_loopInterpolation {X X' : ℝ → V → V} {x x' : ℝ → V}
    (hx : ∀ t, HasDerivAt x (X t (x t)) t) (hx' : ∀ t, HasDerivAt x' (X' t (x' t)) t) :
    (TendstoUniformlyOn (fun s t ↦ loopInterpolation x x' (s, t)) x atBot (Icc 0 1) ∧
      TendstoUniformlyOn (fun s t ↦ sliceDefect X (loopInterpolation x x') (s, t)) 0 atBot
        (Icc 0 1)) ∧
    (TendstoUniformlyOn (fun s t ↦ loopInterpolation x x' (s, t)) x' atTop (Icc 0 1) ∧
      TendstoUniformlyOn (fun s t ↦ sliceDefect X' (loopInterpolation x x') (s, t)) 0 atTop
        (Icc 0 1)) :=
  have hbot := tendstoUniformly_and_sliceDefect_of_eventuallyEq (u := loopInterpolation x x') hx
    ((eventually_lt_atBot 0).mono fun _ hs _ ↦ eventually_of_mem
      ((isOpen_lt continuous_fst continuous_const).mem_nhds hs) fun _ hw ↦
        smoothSegmentPath_of_nonpos _ _ (le_of_lt hw))
  have htop := tendstoUniformly_and_sliceDefect_of_eventuallyEq (u := loopInterpolation x x') hx'
    ((eventually_gt_atTop 1).mono fun _ hs _ ↦ eventually_of_mem
      ((isOpen_lt continuous_const continuous_fst).mem_nhds hs) fun _ hw ↦
        smoothSegmentPath_of_one_le _ _ (le_of_lt hw))
  ⟨⟨hbot.1.tendstoUniformlyOn, hbot.2.tendstoUniformlyOn⟩,
    ⟨htop.1.tendstoUniformlyOn, htop.2.tendstoUniformlyOn⟩⟩

/-- The cylinder `x₋ + β(s + R) (y - x₋) + β(s - R) (x₊ - y)` obtained by gluing the interpolating
cylinders from `x₋` to `y` and from `y` to `x₊` along a neck of length `2 R`. -/
private noncomputable def gluedLoopInterpolation (xm y xp : ℝ → V) (R : ℝ) (z : ℝ × ℝ) : V :=
  loopInterpolation xm y (z.1 + R, z.2) + smoothTransition (z.1 - R) • (xp z.2 - y z.2)

private theorem contDiff_gluedLoopInterpolation {xm y xp : ℝ → V} (hxm : ContDiff ℝ 1 xm)
    (hy : ContDiff ℝ 1 y) (hxp : ContDiff ℝ 1 xp) (R : ℝ) :
    ContDiff ℝ 1 (gluedLoopInterpolation xm y xp R) :=
  ((contDiff_loopInterpolation hxm hy).comp
      ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)).add
    ((smoothTransition.contDiff.comp (contDiff_fst.sub contDiff_const)).smul
      ((hxp.comp contDiff_snd).sub (hy.comp contDiff_snd)))

/-- On `s < 0`, the glued cylinder is the interpolating cylinder from `x₋` to `y`, translated by
`R ≥ 1`. -/
private theorem gluedLoopInterpolation_of_neg {xm y xp : ℝ → V} {R : ℝ} (hR : 1 ≤ R) {s : ℝ}
    (hs : s < 0) (t : ℝ) :
    gluedLoopInterpolation xm y xp R (s, t) = loopInterpolation xm y (s + R, t) := by
  simp [gluedLoopInterpolation, smoothTransition.zero_of_nonpos (show s - R ≤ 0 by linarith)]

/-- On `s ≥ 0`, the glued cylinder is the interpolating cylinder from `y` to `x₊`, translated by
`-R` for `R ≥ 1`. -/
private theorem gluedLoopInterpolation_of_nonneg {xm y xp : ℝ → V} {R : ℝ} (hR : 1 ≤ R) {s : ℝ}
    (hs : 0 ≤ s) (t : ℝ) :
    gluedLoopInterpolation xm y xp R (s, t) = loopInterpolation y xp (s - R, t) := by
  simp only [gluedLoopInterpolation, loopInterpolation,
    smoothSegmentPath_of_one_le _ _ (show 1 ≤ s + R by linarith), smoothSegmentPath_def]

/-- The glued cylinder runs from `x₋` to `x₊`, for `R ≥ 0`. -/
private theorem tendstoUniformlyOn_gluedLoopInterpolation {Xm Xp : ℝ → V → V} {xm y xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (Xm t (xm t)) t) (hxp : ∀ t, HasDerivAt xp (Xp t (xp t)) t)
    {R : ℝ} (hR : 0 ≤ R) :
    (TendstoUniformlyOn (fun s t ↦ gluedLoopInterpolation xm y xp R (s, t)) xm atBot
        (Icc 0 1) ∧
      TendstoUniformlyOn (fun s t ↦ sliceDefect Xm (gluedLoopInterpolation xm y xp R) (s, t)) 0
        atBot (Icc 0 1)) ∧
    (TendstoUniformlyOn (fun s t ↦ gluedLoopInterpolation xm y xp R (s, t)) xp atTop
        (Icc 0 1) ∧
      TendstoUniformlyOn (fun s t ↦ sliceDefect Xp (gluedLoopInterpolation xm y xp R) (s, t)) 0
        atTop (Icc 0 1)) := by
  have hbot := tendstoUniformly_and_sliceDefect_of_eventuallyEq
    (u := gluedLoopInterpolation xm y xp R) hxm
    ((eventually_lt_atBot (-R)).mono fun _ hs _ ↦ eventually_of_mem
      ((isOpen_lt continuous_fst continuous_const).mem_nhds hs) fun w (hw : w.1 < -R) ↦ by
        simp [gluedLoopInterpolation, loopInterpolation,
          smoothSegmentPath_of_nonpos _ _ (show w.1 + R ≤ 0 by linarith),
          smoothTransition.zero_of_nonpos (show w.1 - R ≤ 0 by linarith)])
  have htop := tendstoUniformly_and_sliceDefect_of_eventuallyEq
    (u := gluedLoopInterpolation xm y xp R) hxp
    ((eventually_gt_atTop (R + 1)).mono fun _ hs _ ↦ eventually_of_mem
      ((isOpen_lt continuous_const continuous_fst).mem_nhds hs) fun w (hw : R + 1 < w.1) ↦ by
        simp only [gluedLoopInterpolation, loopInterpolation,
          smoothSegmentPath_of_one_le _ _ (show 1 ≤ w.1 + R by linarith),
          smoothTransition.one_of_one_le (show 1 ≤ w.1 - R by linarith), one_smul]
        abel)
  exact ⟨⟨hbot.1.tendstoUniformlyOn, hbot.2.tendstoUniformlyOn⟩,
    ⟨htop.1.tendstoUniformlyOn, htop.2.tendstoUniformlyOn⟩⟩

end Interpolation

section GluedHamiltonian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The Hamiltonian `H₋ + β(s + R) (H₀ - H₋) + β(s - R) (H₊ - H₀)` obtained by gluing the
continuation homotopies from `H₋` to `H₀` and from `H₀` to `H₊` along a neck of length `2 R`. -/
private noncomputable def gluedContinuationHomotopy (Hm H₀ Hp : ℝ → V → ℝ) (R : ℝ) (z : ℝ × ℝ)
    (x : V) : ℝ :=
  Floer.continuationHomotopy Hm H₀ (z.1 + R, z.2) x +
    smoothTransition (z.1 - R) * (Hp z.2 x - H₀ z.2 x)

private theorem contDiff_uncurry_gluedContinuationHomotopy {n : ℕ∞} {Hm H₀ Hp : ℝ → V → ℝ}
    (hHm : ContDiff ℝ n (uncurry Hm)) (hH₀ : ContDiff ℝ n (uncurry H₀))
    (hHp : ContDiff ℝ n (uncurry Hp)) (R : ℝ) :
    ContDiff ℝ n (uncurry (gluedContinuationHomotopy Hm H₀ Hp R)) := by
  have hp : ContDiff ℝ n fun p : (ℝ × ℝ) × V ↦ (p.1.2, p.2) :=
    (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  have hs : ContDiff ℝ n fun p : (ℝ × ℝ) × V ↦ p.1.1 := contDiff_fst.comp contDiff_fst
  exact ((Floer.contDiff_uncurry_continuationHomotopy hHm hH₀).comp
      (((hs.add contDiff_const).prodMk (contDiff_snd.comp contDiff_fst)).prodMk contDiff_snd)).add
    ((smoothTransition.contDiff.comp (hs.sub contDiff_const)).mul
      ((hHp.comp hp).sub (hH₀.comp hp)))

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- On `s < 0`, the glued Hamiltonian is the continuation homotopy from `H₋` to `H₀`, translated by
`R ≥ 1`. -/
private theorem gluedContinuationHomotopy_of_neg {Hm H₀ Hp : ℝ → V → ℝ} {R : ℝ} (hR : 1 ≤ R)
    {s : ℝ} (hs : s < 0) (t : ℝ) :
    gluedContinuationHomotopy Hm H₀ Hp R (s, t) = Floer.continuationHomotopy Hm H₀ (s + R, t) := by
  funext x
  simp [gluedContinuationHomotopy, smoothTransition.zero_of_nonpos (show s - R ≤ 0 by linarith)]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- On `s ≥ 0`, the glued Hamiltonian is the continuation homotopy from `H₀` to `H₊`, translated
by `-R` for `R ≥ 1`. -/
private theorem gluedContinuationHomotopy_of_nonneg {Hm H₀ Hp : ℝ → V → ℝ} {R : ℝ} (hR : 1 ≤ R)
    {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    gluedContinuationHomotopy Hm H₀ Hp R (s, t) = Floer.continuationHomotopy H₀ Hp (s - R, t) := by
  funext x
  rw [gluedContinuationHomotopy, Floer.continuationHomotopy_of_one_le (z := (s + R, t))
    (show 1 ≤ s + R by linarith), Floer.continuationHomotopy_def]

end GluedHamiltonian

section Unitary

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The data `(i, 0, H_{(s, t)})` of the continuation homotopy from `H` to `H'` are cylindrical
near the ends with radius `1`, along every map. -/
private theorem isCylindricalNearEnds_continuationHomotopy_ofComplexModule {H H' : ℝ → F → ℝ}
    (hH : ContDiff ℝ 2 (uncurry H)) (hH' : ContDiff ℝ 2 (uncurry H')) (u : ℝ × ℝ → F) :
    Floer.IsCylindricalNearEnds (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
      (fun _ _ ↦ 0) (Floer.continuationHomotopy H H')
      (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
      (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) H H' 1 u where
  almostComplex_eq_of_le_neg _ _ := rfl
  almostComplex_eq_of_le _ _ := rfl
  hamiltonianS_eq_zero _ _ := rfl
  hamiltonianT_eq_of_le_neg _ hz :=
    funext (Floer.continuationHomotopy_of_nonpos (hz.trans (by norm_num)))
  hamiltonianT_eq_of_le _ hz := funext (Floer.continuationHomotopy_of_one_le hz)
  contDiffAt_almostComplex _ := contDiffAt_const
  contDiffAt_hamiltonianS _ := contDiffAt_const
  contDiffAt_hamiltonianT _ := (Floer.contDiff_uncurry_continuationHomotopy hH hH').contDiffAt

/-- The data `(i, 0, H_{(s, t)})` of the glued Hamiltonian are cylindrical near the ends with
radius `R + 1`, along every map, for `R ≥ 0`. -/
private theorem isCylindricalNearEnds_gluedContinuationHomotopy {Hm H₀ Hp : ℝ → F → ℝ}
    (hHm : ContDiff ℝ 2 (uncurry Hm)) (hH₀ : ContDiff ℝ 2 (uncurry H₀))
    (hHp : ContDiff ℝ 2 (uncurry Hp)) {R : ℝ} (hR : 0 ≤ R) (u : ℝ × ℝ → F) :
    Floer.IsCylindricalNearEnds (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
      (fun _ _ ↦ 0) (gluedContinuationHomotopy Hm H₀ Hp R)
      (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
      (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) Hm Hp (R + 1) u where
  almostComplex_eq_of_le_neg _ _ := rfl
  almostComplex_eq_of_le _ _ := rfl
  hamiltonianS_eq_zero _ _ := rfl
  hamiltonianT_eq_of_le_neg z hz := by
    funext x
    simp [gluedContinuationHomotopy,
      Floer.continuationHomotopy_of_nonpos (z := (z.1 + R, z.2)) (show z.1 + R ≤ 0 by linarith),
      smoothTransition.zero_of_nonpos (show z.1 - R ≤ 0 by linarith)]
  hamiltonianT_eq_of_le z hz := by
    funext x
    simp only [gluedContinuationHomotopy,
      Floer.continuationHomotopy_of_one_le (z := (z.1 + R, z.2)) (show 1 ≤ z.1 + R by linarith),
      smoothTransition.one_of_one_le (show 1 ≤ z.1 - R by linarith), one_mul]
    ring
  contDiffAt_almostComplex _ := contDiffAt_const
  contDiffAt_hamiltonianS _ := contDiffAt_const
  contDiffAt_hamiltonianT _ :=
    (contDiff_uncurry_gluedContinuationHomotopy hHm hH₀ hHp R).contDiffAt

variable (ω : SymplecticForm F)

/-- The comparison operator from `x` to `x'`, of the data `(i, 0, H_{(s, t)})` of the continuation
homotopy along the interpolating cylinder, has bounded coefficients and is Fredholm. -/
private theorem memLp_and_isFredholm_floerSobolevOperator_loopInterpolation
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H H' : ℝ → F → ℝ} {K K' : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1)
    (hX' : LipschitzWith K' (ω.timeDependentHamiltonianSuspension H'))
    (hH' : ContDiff ℝ 3 (uncurry H')) (hH'per : Periodic H' 1) {x x' : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxper : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    (hx' : ∀ t, HasDerivAt x' (ω.hamiltonianVectorField (H' t) (x' t)) t) (hx'per : Periodic x' 1)
    (hnd' : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H' hX' 0 1) (x' 0)) :
    MemLp (ω.floerJetCoeff
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (Floer.continuationHomotopy H H') (loopInterpolation x x')) ⊤
        StripSobolev.stripMeasure ∧
      (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (Floer.continuationHomotopy H H') (loopInterpolation x x')).IsFredholm := by
  have hH₂ : ContDiff ℝ 2 (uncurry H) := hH.of_le (by norm_num)
  have hH'₂ : ContDiff ℝ 2 (uncurry H') := hH'.of_le (by norm_num)
  have hcyl := isCylindricalNearEnds_continuationHomotopy_ofComplexModule hH₂ hH'₂
    (loopInterpolation x x')
  have hu := contDiff_loopInterpolation
    (ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField (hH₂.of_le one_le_two) hx)
    (ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField (hH'₂.of_le one_le_two) hx')
  obtain ⟨⟨hux, hδ⟩, ⟨hux', hδ'⟩⟩ := tendstoUniformlyOn_loopInterpolation hx hx'
  exact ⟨ω.memLp_floerJetCoeff_of_cylindrical hcyl hu hH₂ contDiff_const hux hδ hH'₂
      contDiff_const hux' hδ',
    ω.isFredholm_floerSobolevOperator_of_cylindrical hω hcyl hu.continuous hX hH hHper hx hxper
      hnd hux hX' hH' hH'per hx' hx'per hnd' hux'⟩

/-- The coefficient field of the comparison operator from `x` to `y` converges at `+∞`, uniformly
in time, to that of the stationary cylinder over `y` with the data `(J₀, 0, H₀)`. -/
private theorem tendstoUniformlyOn_curry_floerJetCoeff_loopInterpolation_atTop (J₀ : F →L[ℝ] F)
    (H H₀ : ℝ → F → ℝ) (x y : ℝ → F) :
    TendstoUniformlyOn (curry (ω.floerJetCoeff (fun _ _ ↦ J₀) (fun _ _ ↦ 0)
        (Floer.continuationHomotopy H H₀) (loopInterpolation x y)))
      (fun t ↦ ω.floerJetCoeff (fun _ _ ↦ J₀) (fun _ _ ↦ 0) (fun z ↦ H₀ z.2) (fun z ↦ y z.2)
        (0, t)) atTop (Icc 0 1) :=
  (tendstoUniformlyOn_const _ atTop _).congr <| (eventually_ge_atTop 1).mono fun s hs t _ ↦
    floerJetCoeff_const_congr ω J₀ rfl
      (funext (Floer.continuationHomotopy_of_one_le (z := (s, t)) hs)).symm
      (smoothSegmentPath_of_one_le _ _ hs).symm

/-- The coefficient field of the comparison operator from `y` to `x'` converges at `-∞`, uniformly
in time, to that of the stationary cylinder over `y` with the data `(J₀, 0, H₀)`. -/
private theorem tendstoUniformlyOn_curry_floerJetCoeff_loopInterpolation_atBot (J₀ : F →L[ℝ] F)
    (H₀ H' : ℝ → F → ℝ) (y x' : ℝ → F) :
    TendstoUniformlyOn (curry (ω.floerJetCoeff (fun _ _ ↦ J₀) (fun _ _ ↦ 0)
        (Floer.continuationHomotopy H₀ H') (loopInterpolation y x')))
      (fun t ↦ ω.floerJetCoeff (fun _ _ ↦ J₀) (fun _ _ ↦ 0) (fun z ↦ H₀ z.2) (fun z ↦ y z.2)
        (0, t)) atBot (Icc 0 1) :=
  (tendstoUniformlyOn_const _ atBot _).congr <| (eventually_le_atBot 0).mono fun s hs t _ ↦
    floerJetCoeff_const_congr ω J₀ rfl
      (funext (Floer.continuationHomotopy_of_nonpos (z := (s, t)) hs)).symm
      (smoothSegmentPath_of_nonpos _ _ hs).symm

/-- **The glued coefficient field.** For `R ≥ 1`, gluing the coefficient fields of the comparison
operators from `x₋` to `y` and from `y` to `x₊` along a neck of length `2 R` gives the coefficient
field of the glued data along the glued cylinder. -/
private theorem uncurry_gluedCoeff_floerJetCoeff (J₀ : F →L[ℝ] F) (Hm H₀ Hp : ℝ → F → ℝ)
    (xm y xp : ℝ → F) {R : ℝ} (hR : 1 ≤ R) :
    uncurry (gluedCoeff
        (curry (ω.floerJetCoeff (fun _ _ ↦ J₀) (fun _ _ ↦ 0) (Floer.continuationHomotopy Hm H₀)
          (loopInterpolation xm y)))
        (curry (ω.floerJetCoeff (fun _ _ ↦ J₀) (fun _ _ ↦ 0) (Floer.continuationHomotopy H₀ Hp)
          (loopInterpolation y xp))) R) =
      ω.floerJetCoeff (fun _ _ ↦ J₀) (fun _ _ ↦ 0) (gluedContinuationHomotopy Hm H₀ Hp R)
        (gluedLoopInterpolation xm y xp R) := by
  funext ⟨s, t⟩
  rcases lt_or_ge s 0 with hs | hs
  · rw [uncurry_apply_pair, gluedCoeff_of_neg _ _ _ hs]
    exact floerJetCoeff_const_congr ω J₀ rfl (gluedContinuationHomotopy_of_neg hR hs t).symm
      (gluedLoopInterpolation_of_neg hR hs t).symm
  · rw [uncurry_apply_pair, gluedCoeff_of_nonneg _ _ _ hs]
    exact floerJetCoeff_const_congr ω J₀ rfl (gluedContinuationHomotopy_of_nonneg hR hs t).symm
      (gluedLoopInterpolation_of_nonneg hR hs t).symm

/-- **Catenation for the comparison operators.** The operator of the data `(i, 0, H_{(s, t)})`
of the continuation homotopy from `H₋` to `H₊` along the interpolating cylinder from `x₋` to `x₊`
has the sum of the indices of the corresponding operators from `x₋` to `y` and from `y` to
`x₊`. -/
private theorem index_floerSobolevOperator_loopInterpolation_eq_add
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {Hm H₀ Hp : ℝ → F → ℝ} {Km K₀ Kp : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1)
    (hX₀ : LipschitzWith K₀ (ω.timeDependentHamiltonianSuspension H₀))
    (hH₀ : ContDiff ℝ 3 (uncurry H₀)) (hH₀per : Periodic H₀ 1)
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpper : Periodic Hp 1) {xm y xp : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t) (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (hy : ∀ t, HasDerivAt y (ω.hamiltonianVectorField (H₀ t) (y t)) t) (hyper : Periodic y 1)
    (hnd₀ : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H₀ hX₀ 0 1) (y 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t) (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0)) :
    (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (Floer.continuationHomotopy Hm Hp) (loopInterpolation xm xp)).index =
      (ω.floerSobolevOperator 2
          (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (Floer.continuationHomotopy Hm H₀) (loopInterpolation xm y)).index +
        (ω.floerSobolevOperator 2
          (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (Floer.continuationHomotopy H₀ Hp) (loopInterpolation y xp)).index := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  set J₀ := (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap
  have hA : ∀ (_ : ℝ × ℝ) (_ : F), ω.Compatible (AlmostComplexStructure.ofComplexModule F) :=
    fun _ _ ↦ ω.compatible_ofComplexModule_of_forall_eq_im_inner hω
  have hJ₀ : ContDiff ℝ 1 fun _ : (ℝ × ℝ) × F ↦ J₀ := contDiff_const
  have hHm₂ : ContDiff ℝ 2 (uncurry Hm) := hHm.of_le (by norm_num)
  have hHp₂ : ContDiff ℝ 2 (uncurry Hp) := hHp.of_le (by norm_num)
  -- Glue the comparison operators from `x₋` to `y` and from `y` to `x₊` along a long neck.
  obtain ⟨hM₁L, hD₁⟩ := memLp_and_isFredholm_floerSobolevOperator_loopInterpolation ω hω hXm hHm
    hHmper hX₀ hH₀ hH₀per hxm hxmper hndm hy hyper hnd₀
  obtain ⟨hM₂L, hD₂⟩ := memLp_and_isFredholm_floerSobolevOperator_loopInterpolation ω hω hX₀ hH₀
    hH₀per hXp hHp hHpper hy hyper hnd₀ hxp hxpper hndp
  rw [floerSobolevOperator_def] at hD₁ hD₂
  obtain ⟨R₀, hR₀⟩ :=
    CylinderSobolev.exists_forall_ge_isFredholm_and_index_jetOperator_gluedCoeff_eq hM₁L hM₂L
      (tendstoUniformlyOn_curry_floerJetCoeff_loopInterpolation_atTop ω J₀ Hm H₀ xm y)
      (tendstoUniformlyOn_curry_floerJetCoeff_loopInterpolation_atBot ω J₀ H₀ Hp y xp) hD₁ hD₂
  set R := max R₀ 1
  have hR : 1 ≤ R := le_max_right _ _
  obtain ⟨hG, hGi⟩ := hR₀ R (le_max_left _ _)
  rw [uncurry_gluedCoeff_floerJetCoeff ω J₀ Hm H₀ Hp xm y xp hR, ← floerSobolevOperator_def,
    ← floerSobolevOperator_def, ← floerSobolevOperator_def] at hGi
  rw [uncurry_gluedCoeff_floerJetCoeff ω J₀ Hm H₀ Hp xm y xp hR, ← floerSobolevOperator_def] at hG
  -- Compare the glued operator with the operator from `x₋` to `x₊`: first the data, then the map.
  have hxmc := ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField (hHm₂.of_le one_le_two) hxm
  have hxpc := ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField (hHp₂.of_le one_le_two) hxp
  have hw := contDiff_gluedLoopInterpolation hxmc
    (ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField (hH₀.of_le (by norm_num)) hy) hxpc R
  obtain ⟨⟨hwxm, hwδm⟩, ⟨hwxp, hwδp⟩⟩ :=
    tendstoUniformlyOn_gluedLoopInterpolation (y := y) hxm hxp (zero_le_one.trans hR)
  obtain ⟨⟨hvxm, hvδm⟩, ⟨hvxp, hvδp⟩⟩ := tendstoUniformlyOn_loopInterpolation hxm hxp
  have hcylG := isCylindricalNearEnds_gluedContinuationHomotopy hHm₂ (hH₀.of_le (by norm_num))
    hHp₂ (zero_le_one.trans hR) (gluedLoopInterpolation xm y xp R)
  have hcylC (u : ℝ × ℝ → F) :=
    isCylindricalNearEnds_continuationHomotopy_ofComplexModule hHm₂ hHp₂ u
  have hKG := contDiff_uncurry_gluedContinuationHomotopy hHm₂ (hH₀.of_le (by norm_num)) hHp₂ R
  have hKC := Floer.contDiff_uncurry_continuationHomotopy hHm₂ hHp₂
  have hdata := index_floerSobolevOperator_eq_of_cylindrical_data ω hcylG (hcylC _) hJ₀
    contDiff_const hKG hJ₀ contDiff_const hKC hA hA hw hXm hxm hndm hwxm hwδm hXp hxp hndp hwxp
    hwδp hG
  have hG' := (isFredholm_floerSobolevOperator_iff_of_cylindrical_data ω hcylG (hcylC _) hJ₀
    contDiff_const hKG hJ₀ contDiff_const hKC hA hA hw hXm hxm hndm hwxm hwδm hXp hxp hndp hwxp
    hwδp).1 hG
  have hmap := index_floerSobolevOperator_eq_of_cylindrical ω (hcylC _) hJ₀ contDiff_const hKC hA
    hw (contDiff_loopInterpolation hxmc hxpc) hXm hxm hndm hwxm hwδm hvxm hvδm
    hXp hxp hndp hwxp hwδp hvxp hvδp hG'
  exact (hmap.trans hdata).trans hGi

/-- **Reduction to the comparison operators.** The operator of any Floer data cylindrical near the
ends, with compatible almost complex structures, along a map from `x` to `x'` has the index of the
operator of the data `(i, 0, H_{(s, t)})` of the continuation homotopy along the interpolating
cylinder from `x` to `x'`. -/
private theorem index_floerSobolevOperator_eq_loopInterpolation
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {Hm Hp : ℝ → F → ℝ} {Km Kp : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1)
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpper : Periodic Hp 1) {xm xp : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t) (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t) (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    {J : ℝ × ℝ → F → AlmostComplexStructure F} {Ks Kt : ℝ × ℝ → F → ℝ}
    {Jm Jp : ℝ → F → AlmostComplexStructure F} {R : ℝ} {u : ℝ × ℝ → F}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJc : ∀ z y, ω.Compatible (J z y)) (hu : ContDiff ℝ 1 u)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    (ω.floerSobolevOperator 2 (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
        u).index =
      (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (Floer.continuationHomotopy Hm Hp) (loopInterpolation xm xp)).index := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hA : ∀ (_ : ℝ × ℝ) (_ : F), ω.Compatible (AlmostComplexStructure.ofComplexModule F) :=
    fun _ _ ↦ ω.compatible_ofComplexModule_of_forall_eq_im_inner hω
  have hJ₀ : ContDiff ℝ 1 fun _ : (ℝ × ℝ) × F ↦
      (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap :=
    contDiff_const
  have hHm₂ : ContDiff ℝ 2 (uncurry Hm) := hHm.of_le (by norm_num)
  have hHp₂ : ContDiff ℝ 2 (uncurry Hp) := hHp.of_le (by norm_num)
  have hcylC (v : ℝ × ℝ → F) :=
    isCylindricalNearEnds_continuationHomotopy_ofComplexModule hHm₂ hHp₂ v
  have hKC := Floer.contDiff_uncurry_continuationHomotopy hHm₂ hHp₂
  obtain ⟨⟨hvxm, hvδm⟩, ⟨hvxp, hvδp⟩⟩ := tendstoUniformlyOn_loopInterpolation hxm hxp
  -- Along `u`, the comparison data give a Fredholm operator, with the index of the given data.
  have hF := ω.isFredholm_floerSobolevOperator_of_cylindrical hω (hcylC u) hu.continuous hXm hHm
    hHmper hxm hxmper hndm huxm hXp hHp hHpper hxp hxpper hndp huxp
  have hdata := index_floerSobolevOperator_eq_of_cylindrical_data ω (hcylC u) hcyl hJ₀
    contDiff_const hKC hJ hKs hKt hA hJc hu hXm hxm hndm huxm hδm hXp hxp hndp huxp hδp hF
  -- The comparison operator along `u` has the index of the comparison operator along the
  -- interpolating cylinder.
  have hmap := index_floerSobolevOperator_eq_of_cylindrical ω (hcylC u) hJ₀ contDiff_const hKC hA
    hu (contDiff_loopInterpolation
      (ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField (hHm₂.of_le one_le_two) hxm)
      (ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField (hHp₂.of_le one_le_two) hxp))
    hXm hxm hndm huxm hδm hvxm hvδm hXp hxp hndp huxp hδp hvxp hvδp hF
  exact hdata.trans hmap.symm

/-- **The index of the linearized Floer operator is additive under catenation.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, and let
`H₋`, `H₀` and `H₊` be one-periodic, jointly `C³` time-dependent Hamiltonians whose suspended vector
fields are globally Lipschitz, with one-periodic orbits `x₋`, `y` and `x₊` starting at nondegenerate
fixed points of the time-one maps. Let `(J, K_s, K_t)`, `(J₁, K_{s,1}, K_{t,1})` and
`(J₂, K_{s,2}, K_{t,2})` be Floer data, `C¹` (with `C²` Hamiltonians) on the whole cylinder,
compatible with `ω` and cylindrical near the ends, with end Hamiltonians `(H₋, H₊)`, `(H₋, H₀)` and
`(H₀, H₊)` respectively. Let `u`, `u₁` and `u₂` be `C¹` maps whose loops converge uniformly to the
corresponding asymptotic orbits, from `x₋` to `x₊`, from `x₋` to `y` and from `y` to `x₊`, with
slice defects tending uniformly to zero at the ends. Then the realizations
`W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer operators satisfy

`ind D_u = ind D_{u₁} + ind D_{u₂}`.

All three are Fredholm by
`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible`. -/
theorem index_floerSobolevOperator_eq_add
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {Hm H₀ Hp : ℝ → F → ℝ} {Km K₀ Kp : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1)
    (hX₀ : LipschitzWith K₀ (ω.timeDependentHamiltonianSuspension H₀))
    (hH₀ : ContDiff ℝ 3 (uncurry H₀)) (hH₀per : Periodic H₀ 1)
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpper : Periodic Hp 1) {xm y xp : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t) (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (hy : ∀ t, HasDerivAt y (ω.hamiltonianVectorField (H₀ t) (y t)) t) (hyper : Periodic y 1)
    (hnd₀ : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H₀ hX₀ 0 1) (y 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t) (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    {J : ℝ × ℝ → F → AlmostComplexStructure F} {Ks Kt : ℝ × ℝ → F → ℝ}
    {Jm Jp : ℝ → F → AlmostComplexStructure F} {R : ℝ} {u : ℝ × ℝ → F}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJc : ∀ z y, ω.Compatible (J z y)) (hu : ContDiff ℝ 1 u)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1))
    {J₁ : ℝ × ℝ → F → AlmostComplexStructure F} {Ks₁ Kt₁ : ℝ × ℝ → F → ℝ}
    {Jm₁ Jp₁ : ℝ → F → AlmostComplexStructure F} {R₁ : ℝ} {u₁ : ℝ × ℝ → F}
    (hcyl₁ : Floer.IsCylindricalNearEnds J₁ Ks₁ Kt₁ Jm₁ Jp₁ Hm H₀ R₁ u₁)
    (hJ₁ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × F ↦ (J₁ p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs₁ : ContDiff ℝ 2 (uncurry Ks₁)) (hKt₁ : ContDiff ℝ 2 (uncurry Kt₁))
    (hJc₁ : ∀ z y, ω.Compatible (J₁ z y)) (hu₁ : ContDiff ℝ 1 u₁)
    (hu₁xm : TendstoUniformlyOn (fun s t ↦ u₁ (s, t)) xm atBot (Icc 0 1))
    (hδ₁m : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u₁ (s, t)) 0 atBot
        (Icc 0 1))
    (hu₁y : TendstoUniformlyOn (fun s t ↦ u₁ (s, t)) y atTop (Icc 0 1))
    (hδ₁p : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H₀ t)) u₁ (s, t)) 0 atTop
        (Icc 0 1))
    {J₂ : ℝ × ℝ → F → AlmostComplexStructure F} {Ks₂ Kt₂ : ℝ × ℝ → F → ℝ}
    {Jm₂ Jp₂ : ℝ → F → AlmostComplexStructure F} {R₂ : ℝ} {u₂ : ℝ × ℝ → F}
    (hcyl₂ : Floer.IsCylindricalNearEnds J₂ Ks₂ Kt₂ Jm₂ Jp₂ H₀ Hp R₂ u₂)
    (hJ₂ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × F ↦ (J₂ p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs₂ : ContDiff ℝ 2 (uncurry Ks₂)) (hKt₂ : ContDiff ℝ 2 (uncurry Kt₂))
    (hJc₂ : ∀ z y, ω.Compatible (J₂ z y)) (hu₂ : ContDiff ℝ 1 u₂)
    (hu₂y : TendstoUniformlyOn (fun s t ↦ u₂ (s, t)) y atBot (Icc 0 1))
    (hδ₂m : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H₀ t)) u₂ (s, t)) 0 atBot
        (Icc 0 1))
    (hu₂xp : TendstoUniformlyOn (fun s t ↦ u₂ (s, t)) xp atTop (Icc 0 1))
    (hδ₂p : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u₂ (s, t)) 0 atTop
        (Icc 0 1)) :
    (ω.floerSobolevOperator 2 (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
        u).index =
      (ω.floerSobolevOperator 2 (fun w y ↦ (J₁ w y).toLinearMap.toContinuousLinearMap) Ks₁ Kt₁
          u₁).index +
        (ω.floerSobolevOperator 2 (fun w y ↦ (J₂ w y).toLinearMap.toContinuousLinearMap) Ks₂ Kt₂
          u₂).index := by
  rw [index_floerSobolevOperator_eq_loopInterpolation ω hω hXm hHm hHmper hXp hHp hHpper hxm
      hxmper hndm hxp hxpper hndp hcyl hJ hKs hKt hJc hu huxm hδm huxp hδp,
    index_floerSobolevOperator_eq_loopInterpolation ω hω hXm hHm hHmper hX₀ hH₀ hH₀per hxm
      hxmper hndm hy hyper hnd₀ hcyl₁ hJ₁ hKs₁ hKt₁ hJc₁ hu₁ hu₁xm hδ₁m hu₁y hδ₁p,
    index_floerSobolevOperator_eq_loopInterpolation ω hω hX₀ hH₀ hH₀per hXp hHp hHpper hy hyper
      hnd₀ hxp hxpper hndp hcyl₂ hJ₂ hKs₂ hKt₂ hJc₂ hu₂ hu₂y hδ₂m hu₂xp hδ₂p]
  exact index_floerSobolevOperator_loopInterpolation_eq_add ω hω hXm hHm hHmper hX₀ hH₀ hH₀per hXp
    hHp hHpper hxm hxmper hndm hy hyper hnd₀ hxp hxpper hndp

/-- **The index of the reversed linearized Floer operator is the opposite.** Under the hypotheses
of `TauCeti.SymplecticForm.index_floerSobolevOperator_eq_add`, for Floer data
`(J₁, K_{s,1}, K_{t,1})` with end Hamiltonians `(H₋, H₀)` along a map `u₁` from `x₋` to `y`, and
`(J₂, K_{s,2}, K_{t,2})` with end Hamiltonians `(H₀, H₋)` along a map `u₂` from `y` back to `x₋`,
the indices of the realizations of the linearized Floer operators add up to zero:

`ind D_{u₁} + ind D_{u₂} = 0`.

This is catenation into an operator from `x₋` to itself, whose index vanishes
(`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_zero_of_isNondegenerateFixedPt`). -/
theorem index_floerSobolevOperator_add_eq_zero
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {Hm H₀ : ℝ → F → ℝ} {Km K₀ : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1)
    (hX₀ : LipschitzWith K₀ (ω.timeDependentHamiltonianSuspension H₀))
    (hH₀ : ContDiff ℝ 3 (uncurry H₀)) (hH₀per : Periodic H₀ 1) {xm y : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t) (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (hy : ∀ t, HasDerivAt y (ω.hamiltonianVectorField (H₀ t) (y t)) t) (hyper : Periodic y 1)
    (hnd₀ : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H₀ hX₀ 0 1) (y 0))
    {J₁ : ℝ × ℝ → F → AlmostComplexStructure F} {Ks₁ Kt₁ : ℝ × ℝ → F → ℝ}
    {Jm₁ Jp₁ : ℝ → F → AlmostComplexStructure F} {R₁ : ℝ} {u₁ : ℝ × ℝ → F}
    (hcyl₁ : Floer.IsCylindricalNearEnds J₁ Ks₁ Kt₁ Jm₁ Jp₁ Hm H₀ R₁ u₁)
    (hJ₁ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × F ↦ (J₁ p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs₁ : ContDiff ℝ 2 (uncurry Ks₁)) (hKt₁ : ContDiff ℝ 2 (uncurry Kt₁))
    (hJc₁ : ∀ z y, ω.Compatible (J₁ z y)) (hu₁ : ContDiff ℝ 1 u₁)
    (hu₁xm : TendstoUniformlyOn (fun s t ↦ u₁ (s, t)) xm atBot (Icc 0 1))
    (hδ₁m : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u₁ (s, t)) 0 atBot
        (Icc 0 1))
    (hu₁y : TendstoUniformlyOn (fun s t ↦ u₁ (s, t)) y atTop (Icc 0 1))
    (hδ₁p : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H₀ t)) u₁ (s, t)) 0 atTop
        (Icc 0 1))
    {J₂ : ℝ × ℝ → F → AlmostComplexStructure F} {Ks₂ Kt₂ : ℝ × ℝ → F → ℝ}
    {Jm₂ Jp₂ : ℝ → F → AlmostComplexStructure F} {R₂ : ℝ} {u₂ : ℝ × ℝ → F}
    (hcyl₂ : Floer.IsCylindricalNearEnds J₂ Ks₂ Kt₂ Jm₂ Jp₂ H₀ Hm R₂ u₂)
    (hJ₂ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × F ↦ (J₂ p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs₂ : ContDiff ℝ 2 (uncurry Ks₂)) (hKt₂ : ContDiff ℝ 2 (uncurry Kt₂))
    (hJc₂ : ∀ z y, ω.Compatible (J₂ z y)) (hu₂ : ContDiff ℝ 1 u₂)
    (hu₂y : TendstoUniformlyOn (fun s t ↦ u₂ (s, t)) y atBot (Icc 0 1))
    (hδ₂m : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H₀ t)) u₂ (s, t)) 0 atBot
        (Icc 0 1))
    (hu₂xm : TendstoUniformlyOn (fun s t ↦ u₂ (s, t)) xm atTop (Icc 0 1))
    (hδ₂p : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u₂ (s, t)) 0 atTop
        (Icc 0 1)) :
    (ω.floerSobolevOperator 2 (fun w y ↦ (J₁ w y).toLinearMap.toContinuousLinearMap) Ks₁ Kt₁
          u₁).index +
        (ω.floerSobolevOperator 2 (fun w y ↦ (J₂ w y).toLinearMap.toContinuousLinearMap) Ks₂ Kt₂
          u₂).index = 0 := by
  rw [index_floerSobolevOperator_eq_loopInterpolation ω hω hXm hHm hHmper hX₀ hH₀ hH₀per hxm
      hxmper hndm hy hyper hnd₀ hcyl₁ hJ₁ hKs₁ hKt₁ hJc₁ hu₁ hu₁xm hδ₁m hu₁y hδ₁p,
    index_floerSobolevOperator_eq_loopInterpolation ω hω hX₀ hH₀ hH₀per hXm hHm hHmper hy hyper
      hnd₀ hxm hxmper hndm hcyl₂ hJ₂ hKs₂ hKt₂ hJc₂ hu₂ hu₂y hδ₂m hu₂xm hδ₂p,
    ← index_floerSobolevOperator_loopInterpolation_eq_add ω hω hXm hHm hHmper hX₀ hH₀ hH₀per hXm
      hHm hHmper hxm hxmper hndm hy hyper hnd₀ hxm hxmper hndm]
  -- The comparison operator from `x₋` to itself is that of the stationary cylinder over `x₋`.
  have hloop := ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField (hHm.of_le (by norm_num)) hxm
  obtain ⟨⟨hvm, hvδm⟩, ⟨hvp, hvδp⟩⟩ := tendstoUniformlyOn_loopInterpolation hxm hxm
  rw [Floer.continuationHomotopy_self]
  exact index_floerSobolevOperator_eq_zero_of_isNondegenerateFixedPt ω hXm hHm hHmper hxm hxmper
    (contDiff_loopInterpolation hloop hloop) hvm hvδm hvp hvδp hω hndm

end Unitary

end TauCeti.SymplecticForm

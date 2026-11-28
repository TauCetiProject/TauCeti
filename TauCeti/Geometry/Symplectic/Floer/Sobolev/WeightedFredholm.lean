/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Fredholm
import TauCeti.Analysis.Sobolev.Cylinder.Frame
import TauCeti.Analysis.Sobolev.Cylinder.Parametrix
import TauCeti.Geometry.Symplectic.AlmostComplex.Frame
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.FrameTrivialization
import TauCeti.Geometry.Symplectic.Floer.Sobolev.Stationary
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.Topology.Constructions.SumProd
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# The weighted linearized Floer operator is Fredholm for every compatible structure

Let `F` be a finite-dimensional complex inner product space with symplectic form
`ω = Im ⟪·, ·⟫`, and let `D_u - c(s) : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` be the realization
(`TauCeti.SymplecticForm.floerWeightedSobolevOperator`) of the linearized Floer operator along a
map `u` of the cylinder, conjugated by an exponential weight `e^{κ(s)}` with slope `c = κ'` equal to
constants `δ±` near `±∞`. This file proves that `D_u - c(s)` is Fredholm for Floer data
`(J, K_s, K_t)` cylindrical near the ends with any `ω`-compatible almost complex structures,
as soon as the shifted fields `dX_{H±_t}(x±(t)) - δ± J±_t(x±(t))` at the asymptotic orbits have
nondegenerate return maps, that is, as soon as `δ±` are not eigenvalues of the asymptotic operators
(`TauCeti.SymplecticForm.isFredholm_floerWeightedSobolevOperator_of_cylindrical_of_compatible`).
For the complex structure `i` this is
`TauCeti.SymplecticForm.isFredholm_floerWeightedSobolevOperator_of_cylindrical`.

For the unweighted operator, deforming the structures from `i` to `J` keeps the operator Fredholm
(`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible`). With a
weight this argument does not apply: the spectrum of the asymptotic operator `J±_t (∂t - S±_t)`
moves with `J±`, so an eigenvalue may cross `δ±` along the deformation, where the semi-Fredholm
estimate fails. Instead the operator is read in unitary frames.

* **Reduction to a map stationary near the ends.** The Fredholm property of `D_u - c(s)` depends
  only on the asymptotic orbits of `u`
  (`TauCeti.SymplecticForm.isFredholm_floerWeightedSobolevOperator_iff_of_cylindrical`), so `u` may
  be replaced by a map equal to `x₋` for `s ≤ -a` and to `x₊` for `s ≥ a`.
* **Unitary frames.** Along such a map the canonical unitary frames
  (`TauCeti.SymplecticForm.unitaryFrame`) of the structures `J(z, u z)` form a `C²` frame `Φ` of
  the cylinder, of period one in `t`, carrying `i` to `J(z, u z)`, and independent of `s` far out.
  Read in this frame (`TauCeti.CylinderSobolev.isFredholm_jetOperator_firstOrderJetCoeff_frame_iff`)
  the operator `∂s + J ∂t + (A - c)` becomes an operator with principal part `∂s + i ∂t`.
* **The ends.** Far out it is the stationary cylinder operator `∂s + J±_t (∂t - (S±_t - δ± J±_t))`
  read in the loop of frames of `J±_t(x±(t))`
  (`TauCeti.CylinderSobolev.firstOrderJetCoeff_frame_loop_eq`), that is `∂s + i (∂t - T±_t)` for the
  trivialized loop `T±`. Its return map is conjugate to that of `S±_t - δ± J±_t`
  (`TauCeti.SymplecticForm.exists_loop_eq_trivializedCoeff`), so this model is invertible
  (`TauCeti.Floer.stationarySobolevEquiv`). The parametrix of the cylinder
  (`TauCeti.CylinderSobolev.isFredholm_jetOperator_comp_subtypeL_of_isInvertible`) then makes the
  operator read in the frame Fredholm.

The frame is built from `J` along the map, so `J` is taken `C²` and of period one in `t`, as frames
of the cylinder are.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix C, on real Cauchy–Riemann operators in unitary trivializations and their Fredholm
  theory.
* R. B. Lockhart and R. C. McOwen, *Elliptic differential operators on noncompact manifolds*,
  Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 12 (1985), 409–447, on the Fredholm property on
  exponentially weighted spaces when the weights avoid the spectra of the asymptotic operators.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
-/

public section

noncomputable section

open Filter Set Function MeasureTheory Topology ContinuousLinearMap
open scoped NNReal ENNReal Manifold

namespace TauCeti.SymplecticForm

open CylinderSobolev
open StripSobolev (stripMeasure frameJetCoeff)

section Helpers

/-- A map of the cylinder which, for `s` eventually along `l`, agrees near `(s, t)` with the
stationary cylinder over an orbit `x` of `H`, converges uniformly to `x` along `l`, with slice
defect `∂t u - X_{H_t}(u)` tending uniformly to zero. -/
private theorem tendstoUniformlyOn_and_sliceDefect_of_eventuallyEq {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) {u : ℝ × ℝ → V}
    {l : Filter ℝ} (h : ∀ᶠ s in l, ∀ t, u =ᶠ[𝓝 (s, t)] fun w ↦ x w.2) :
    TendstoUniformlyOn (fun s t ↦ u (s, t)) x l (Icc 0 1) ∧
      TendstoUniformlyOn (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t))
        0 l (Icc 0 1) := by
  refine ⟨(tendstoUniformlyOn_const x l _).congr (h.mono fun s hs t _ ↦ (hs t).eq_of_nhds.symm),
    (tendstoUniformlyOn_const 0 l _).congr (h.mono fun s hs t _ ↦ ?_)⟩
  dsimp only
  rw [Pi.zero_apply, eq_comm, sliceDefect_def, (hs t).fderiv_eq, (hs t).eq_of_nhds]
  simpa only [sliceDefect_def, Pi.zero_apply] using
    congrFun (sliceDefect_comp_snd_eq_zero hx) (s, t)

end Helpers

section EndModel

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The end model in a unitary frame.** Let `x` be a one-periodic orbit of a one-periodic,
jointly `C³` Hamiltonian `H`, let `Φ_t` be a `C²` one-periodic loop of invertible maps of `F`
carrying `Im ⟪·, ·⟫` to `ω` and `i` to `J_t`, and let `δ` be such that `S_t - δ J_t`,
`S_t = dX_{H_t}(x(t))`, has a nondegenerate return map. Read in the frame, `S - δ J` becomes a loop
`T` on the circle, and the stationary cylinder operator `∂s + i (∂t - T_t)` is an isomorphism
`W^{1,2}(ℝ × S¹, F) ≃ L²(ℝ × S¹, F)`. -/
private theorem exists_loop_isInvertible_stationarySobolevOperator (ω : SymplecticForm F)
    {H : ℝ → F → ℝ} (hH : ContDiff ℝ 3 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {Je : ℝ → AlmostComplexStructure F} {Φ : ℝ → F →L[ℝ] F} (hΦ : ContDiff ℝ 2 Φ)
    (hΦp : Periodic Φ 1) (hΦi : ∀ t, (Φ t).IsInvertible)
    (hΦω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    (hΦJ : ∀ t v, Je t (Φ t v) = Φ t (Complex.I • v)) (hJep : Periodic Je 1) {δ : ℝ}
    (hdet : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t) -
        δ • (Je t).toLinearMap.toContinuousLinearMap) 1 : F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0) :
    ∃ T : C(AddCircle (1 : ℝ), F →L[ℝ] F), (fun t : ℝ ↦ T t) =
        trivializedCoeff Φ (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t) -
          δ • (Je t).toLinearMap.toContinuousLinearMap) ∧
      (Floer.stationarySobolevOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
        fun t : ℝ ↦ T t).IsInvertible := by
  have : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
  -- `S_t = dX_{H_t}(x(t))` is a `C¹` one-periodic loop of infinitesimally symplectic maps.
  have hS₁ := ω.contDiff_fderiv_hamiltonianVectorField_comp (n := 1) hH
    (ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField (hH.of_le (by norm_num)) hx)
  have hSp := ω.periodic_fderiv_hamiltonianVectorField_comp hHp hxp
  -- `J_t = Φ_t i Φ_t⁻¹` is a `C¹` one-periodic loop of `ω`-compatible structures.
  have hJec (t : ℝ) : ω.Compatible (Je t) :=
    ω.compatible_of_isInvertible_of_forall_eq_im_inner (hΦi t) (hΦω t) (hΦJ t)
  have hJe : ContDiff ℝ 1 fun t ↦ (Je t).toLinearMap.toContinuousLinearMap := by
    have heq : (fun t ↦ (Je t).toLinearMap.toContinuousLinearMap) = fun t ↦
        Φ t ∘L (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap ∘L
          (Φ t).inverse := funext fun t ↦ ContinuousLinearMap.ext fun v ↦ by
      conv_lhs => rw [← (hΦi t).self_apply_inverse v]
      simp [hΦJ, AlmostComplexStructure.ofComplexModule_apply]
    rw [heq]
    exact (hΦ.of_le one_le_two).clm_comp
      (contDiff_const.clm_comp ((hΦ.clm_inverse hΦi).of_le one_le_two))
  have hJep' : Periodic (fun t ↦ (Je t).toLinearMap.toContinuousLinearMap) 1 := fun t ↦ by
    simp only [hJep t]
  -- `S_t - δ J_t` is infinitesimally symplectic, as both `S_t` and `J_t` are.
  have hSω (t : ℝ) (v w : F) :
      ω ((fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t) -
        δ • (Je t).toLinearMap.toContinuousLinearMap) v) w +
      ω v ((fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t) -
        δ • (Je t).toLinearMap.toContinuousLinearMap) w) = 0 := by
    have h₁ := ω.apply_fderiv_hamiltonianVectorField_add (H := H t)
      (((hH.of_le (by norm_num)).comp (contDiff_prodMk_right t)).contDiffAt (x := x t)) v w
    have h₂ := (hJec t).invariant.apply_add_apply_eq_zero v w
    simp only [sub_apply, smul_apply, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap', smul_eq_mul]
    linear_combination h₁ - δ * h₂
  obtain ⟨T, hT, hT₁, hTω, hTdet⟩ := ω.exists_loop_eq_trivializedCoeff hΦ hΦp hΦi hΦω
    (hS₁.sub (hJe.const_smul δ)) (hSp.sub (hJep'.smul δ)) hSω hdet
  exact ⟨T, hT, ⟨Floer.stationarySobolevEquiv hT₁ hTω hTdet, Floer.coe_stationarySobolevEquiv ..⟩⟩

end EndModel

section Point

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- At a point where the Floer data, the map and the weight slope are those of the stationary
cylinder over an orbit `x` of an end Hamiltonian `H`, with almost complex structures `J_t` and
slope `δ`, the zeroth-order part of `D_u - c(s)` is that of `∂s + J_t (∂t - (S_t - δ J_t))`,
`S_t = dX_{H_t}(x(t))`, at `t = z.2`. -/
private theorem floerLinearizationCoeff_sub_smul_eq_of_eventuallyEq (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {c : ℝ → ℝ} {Je : ℝ → V → AlmostComplexStructure V} {He : ℝ → V → ℝ} {xe : ℝ → V}
    (hxe : ∀ t, HasDerivAt xe (ω.hamiltonianVectorField (He t) (xe t)) t) {δ : ℝ} {z : ℝ × ℝ}
    (hJz : J z = Je z.2) (hKs : Ks z = 0) (hKt : Kt z = He z.2)
    (hu : u =ᶠ[𝓝 z] fun w ↦ xe w.2) (hc : c z.1 = δ) :
    ω.floerLinearizationCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u z -
        c z.1 • ContinuousLinearMap.id ℝ V =
      -(Je z.2 (xe z.2)).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField (He z.2)) (xe z.2) -
          δ • (Je z.2 (xe z.2)).toLinearMap.toContinuousLinearMap) := by
  -- The coefficient only sees the data at `z`, `u z` and `du(z)`, which are stationary.
  have hcoeff : ω.floerLinearizationCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      Ks Kt u z = ω.floerLinearizationCoeff
        (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ He w.2) (fun w ↦ xe w.2) z := by
    rw [ω.floerLinearizationCoeff_congr_data u
      (J' := fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (Ks' := fun _ _ ↦ 0)
      (Kt' := fun w ↦ He w.2) (by simp only [hJz]) hKs hKt]
    refine ContinuousLinearMap.ext fun v ↦ ?_
    rw [floerLinearizationCoeff_apply, floerLinearizationCoeff_apply, hu.fderiv_eq,
      hu.eq_of_nhds]
  -- At the stationary cylinder, the zeroth-order part is `-J_t S_t`.
  have hstat (v : V) : ω.floerLinearizationCoeff
      (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ He w.2)
        (fun w ↦ xe w.2) z v =
      -Je z.2 (xe z.2) (fderiv ℝ (ω.hamiltonianVectorField (He z.2)) (xe z.2) v) := by
    have h := congrArg (fun M ↦ M z (v, 0, 0)) (ω.floerJetCoeff_eq_stationaryJetCoeff Je He hxe)
    simpa [floerJetCoeff_apply, Floer.stationaryJetCoeff_apply] using h
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [hcoeff, sub_apply, hstat, hc]
  simp only [smul_apply, id_apply, comp_sub, comp_smulₛₗ, RingHom.id_apply, neg_sub, sub_apply,
    ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
    AlmostComplexStructure.apply_apply, smul_neg]
  abel

end Point

section FramePoint

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The operator in the frame at a stationary point.** At a point where the Floer data, the map,
the weight slope and the frame `Φ` are those of the stationary cylinder over an orbit `x` of an end
Hamiltonian `H`, with structures `J_t`, slope `δ` and a loop of frames `Φ_t` carrying `i` to
`J_t(x(t))`, the operator `D_u - c(s)` read in the frame `Φ` has the coefficient field of the
stationary cylinder operator `∂s + i (∂t - T_t)`, where `T` is `S_t - δ J_t(x(t))` read in the loop
of frames, `S_t = dX_{H_t}(x(t))`. -/
private theorem firstOrderJetCoeff_frame_eq_stationaryJetCoeff (ω : SymplecticForm F)
    {J : ℝ × ℝ → F → AlmostComplexStructure F} {Ks Kt : ℝ × ℝ → F → ℝ} {u : ℝ × ℝ → F}
    {c : ℝ → ℝ} {Φ : ℝ × ℝ → F →L[ℝ] F} {Je : ℝ → F → AlmostComplexStructure F}
    {He : ℝ → F → ℝ} {xe : ℝ → F}
    (hxe : ∀ t, HasDerivAt xe (ω.hamiltonianVectorField (He t) (xe t)) t)
    {Φe : ℝ → F →L[ℝ] F} (hΦei : ∀ t, (Φe t).IsInvertible)
    (hΦeJ : ∀ t v, Je t (xe t) (Φe t v) = Φe t (Complex.I • v)) {δ : ℝ} {z : ℝ × ℝ}
    (hJz : J z = Je z.2) (hKs : Ks z = 0) (hKt : Kt z = He z.2)
    (hu : u =ᶠ[𝓝 z] fun w ↦ xe w.2) (hc : c z.1 = δ) (hΦ : Φ =ᶠ[𝓝 z] fun w ↦ Φe w.2) :
    firstOrderJetCoeff ((Φ z).inverse.comp
        ((J z (u z)).toLinearMap.toContinuousLinearMap.comp (Φ z)))
      ((Φ z).inverse.comp ((ω.floerLinearizationCoeff
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u z -
          c z.1 • ContinuousLinearMap.id ℝ F).comp (Φ z) + fderiv ℝ Φ z (1, 0) +
        (J z (u z)).toLinearMap.toContinuousLinearMap.comp (fderiv ℝ Φ z (0, 1)))) =
      Floer.stationaryJetCoeff (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
        (trivializedCoeff Φe fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (He t)) (xe t) -
          δ • (Je t (xe t)).toLinearMap.toContinuousLinearMap) z := by
  have hJu : J z (u z) = Je z.2 (xe z.2) := by rw [hJz, hu.eq_of_nhds]
  rw [ω.floerLinearizationCoeff_sub_smul_eq_of_eventuallyEq hxe hJz hKs hKt hu hc, hJu,
    hΦ.fderiv_eq, hΦ.eq_of_nhds, Floer.stationaryJetCoeff_eq_firstOrderJetCoeff]
  exact firstOrderJetCoeff_frame_loop_eq
    (J := fun t ↦ (Je t (xe t)).toLinearMap.toContinuousLinearMap)
    (J₀ := fun _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
    (S := fun w ↦ fderiv ℝ (ω.hamiltonianVectorField (He w.2)) (xe w.2) -
      δ • (Je w.2 (xe w.2)).toLinearMap.toContinuousLinearMap) hΦei
    (fun t ↦ ContinuousLinearMap.ext fun v ↦ by
      simp [hΦeJ, AlmostComplexStructure.ofComplexModule_apply]) z

end FramePoint

section Core

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **Unitary frames in a complex inner product space.** When `ω = Im ⟪·, ·⟫`, every
`ω`-compatible structure `J` has a frame `G J`, invertible, symplectic from `Im ⟪·, ·⟫` to `ω` and
carrying `i` to `J`, which depends `C²` on `J` along `C²` families
(`TauCeti.SymplecticForm.unitaryFrame` for the inner product `Re ⟪·, ·⟫`). -/
private theorem exists_unitaryFrame (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im) :
    ∃ G : AlmostComplexStructure F → F →L[ℝ] F,
      (∀ {K : ℝ × ℝ → AlmostComplexStructure F},
        (ContDiff ℝ 2 fun z ↦ (K z).toLinearMap.toContinuousLinearMap) →
          (∀ z, ω.Compatible (K z)) → ContDiff ℝ 2 fun z ↦ G (K z)) ∧
      ∀ J, ω.Compatible J → (G J).IsInvertible ∧ (∀ v, J (G J v) = G J (Complex.I • v)) ∧
        ∀ v w, ω (G J v) (G J w) = (inner ℂ v w).im := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hg (v w : F) : ω v (AlmostComplexStructure.ofComplexModule F w) = inner ℝ v w :=
    ω.apply_ofComplexModule_eq_inner hω v w
  refine ⟨ω.unitaryFrame, fun hK hKc ↦ hK.unitaryFrame hKc,
    fun J hJ ↦ ⟨hJ.isInvertible_unitaryFrame, fun v ↦ ?_, fun v w ↦ ?_⟩⟩
  · rw [hJ.apply_unitaryFrame hg, AlmostComplexStructure.ofComplexModule_apply]
  · rw [hJ.apply_unitaryFrame_unitaryFrame hg, hω]

/-- **Fredholm operators read in a unitary frame.** Let `Φ` be a `C²` frame on the cylinder of
period one in `t`, bounded with its derivative and its inverses, carrying `i` to the coefficients
`A(z)` of `∂t` in `∂s + A ∂t + C`. If, read in the frame, the operator is the stationary cylinder
operator `∂s + i (∂t - T±_t)` for `±s > R`, with invertible models, then `∂s + A ∂t + C` is
Fredholm: read in the frame, its principal part is `∂s + i ∂t`, that of its models, so the
parametrix of the cylinder applies. -/
private theorem isFredholm_jetOperator_firstOrderJetCoeff_of_frame {Φ : ℝ × ℝ → F →L[ℝ] F}
    (hΦ : ContDiff ℝ 2 Φ) (hΦp : ∀ s t, Φ (s, t + 1) = Φ (s, t)) (hΦi : ∀ z, (Φ z).IsInvertible)
    {B B' D : ℝ} (hB : ∀ z, ‖Φ z‖ ≤ B) (hB' : ∀ z, ‖fderiv ℝ Φ z‖ ≤ B')
    (hD : ∀ z, ‖(Φ z).inverse‖ ≤ D) {A C : ℝ × ℝ → F →L[ℝ] F}
    (hAC : MemLp (fun z ↦ firstOrderJetCoeff (A z) (C z)) ∞ stripMeasure)
    (hAΦ : ∀ z v, A z (Φ z v) = Φ z (Complex.I • v)) {Tm Tp : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hDm : (Floer.stationarySobolevOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
      fun t : ℝ ↦ Tm t).IsInvertible)
    (hDp : (Floer.stationarySobolevOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
      fun t : ℝ ↦ Tp t).IsInvertible) {R : ℝ}
    (hm : ∀ z : ℝ × ℝ, z.1 < -R → firstOrderJetCoeff ((Φ z).inverse.comp ((A z).comp (Φ z)))
      ((Φ z).inverse.comp ((C z).comp (Φ z) + fderiv ℝ Φ z (1, 0) +
        (A z).comp (fderiv ℝ Φ z (0, 1)))) =
      Floer.stationaryJetCoeff (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
        (fun t : ℝ ↦ Tm t) z)
    (hp : ∀ z : ℝ × ℝ, R < z.1 → firstOrderJetCoeff ((Φ z).inverse.comp ((A z).comp (Φ z)))
      ((Φ z).inverse.comp ((C z).comp (Φ z) + fderiv ℝ Φ z (1, 0) +
        (A z).comp (fderiv ℝ Φ z (0, 1)))) =
      Floer.stationaryJetCoeff (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
        (fun t : ℝ ↦ Tp t) z) :
    ((jetOperator 2 stripMeasure fun z ↦ firstOrderJetCoeff (A z) (C z)).comp
      (H1 F).subtypeL).IsFredholm := by
  have : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
  have hΨ : ContDiff ℝ 2 fun z ↦ (Φ z).inverse := hΦ.clm_inverse hΦi
  rw [← isFredholm_jetOperator_firstOrderJetCoeff_frame_iff hΦ hΦp hB hB' hΨ hD
    (fun z ↦ (hΦi z).inverse_comp_self) (fun z ↦ (hΦi z).self_comp_inverse) hAC]
  rw [Floer.stationarySobolevOperator_def] at hDm hDp
  -- The operator in the frame has bounded coefficients.
  have hΨL : MemLp (fun z ↦ (Φ z).inverse) ∞ stripMeasure :=
    memLp_top_of_bound hΨ.continuous.aestronglyMeasurable D (ae_of_all _ hD)
  have hM' := (hΨL.clm_comp ∞ hAC).clm_comp ∞
    (StripSobolev.memLp_frameJetCoeff (hΦ.of_le one_le_two) hB hB')
  rw [funext fun z ↦ StripSobolev.comp_firstOrderJetCoeff_comp_frameJetCoeff (Φ := Φ)
    (Ψ := fun z ↦ (Φ z).inverse) (A := A) (C := C) (z := z) (hΦi z).inverse_comp_self] at hM'
  -- Its principal part is `∂s + i ∂t`, that of the models.
  have hprin (z : ℝ × ℝ) (a b : F) {T : ℝ → F →L[ℝ] F} : firstOrderJetCoeff
      ((Φ z).inverse.comp ((A z).comp (Φ z))) ((Φ z).inverse.comp ((C z).comp (Φ z) +
        fderiv ℝ Φ z (1, 0) + (A z).comp (fderiv ℝ Φ z (0, 1)))) (0, a, b) =
      Floer.stationaryJetCoeff (fun _ ↦ AlmostComplexStructure.ofComplexModule F) T z
        (0, a, b) := by
    simp [Floer.stationaryJetCoeff_apply, hAΦ, AlmostComplexStructure.ofComplexModule_apply,
      (hΦi z).inverse_apply_self]
  -- Far out on each end it is the model.
  have hzero {M M' : F × F × F →L[ℝ] F} (h : M = M') {ε : ℝ} (hε : 0 < ε) : ‖M - M'‖ ≤ ε := by
    rw [h, sub_self]
    exact ContinuousLinearMap.opNorm_le_bound _ hε.le fun v ↦ by
      simpa using mul_nonneg hε.le (norm_nonneg v)
  exact isFredholm_jetOperator_comp_subtypeL_of_isInvertible
    (Mneg := Floer.stationaryJetCoeff (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
      fun t : ℝ ↦ Tm t)
    (Mpos := Floer.stationaryJetCoeff (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
      fun t : ℝ ↦ Tp t) hM'
    (Floer.memLp_stationaryJetCoeff continuous_const ((map_continuous Tm).comp
      (AddCircle.continuous_mk' 1)))
    (Floer.memLp_stationaryJetCoeff continuous_const ((map_continuous Tp).comp
      (AddCircle.continuous_mk' 1))) hDm hDp (.of_forall fun z a b ↦ hprin z a b)
    (.of_forall fun z a b ↦ hprin z a b)
    (fun ε hε ↦ ⟨R, ae_of_all _ fun z hz ↦ hzero (hm z hz) hε⟩)
    (fun ε hε ↦ ⟨R, ae_of_all _ fun z hz ↦ hzero (hp z hz) hε⟩)

/-- **The weighted operator at a map that is stationary near the ends is Fredholm.** For `C²`
Floer data `(J, K_s, K_t)` of period one in `t`, cylindrical near the ends, and a `C²` map `u` of
period one in `t` which equals the orbit `x₋` for `s ≤ -R` and the orbit `x₊` for `s ≥ R`, read
`D_u - c(s)` in the unitary frames `Φ(z)` of the structures `J(z, u z)`. The result has principal
part `∂s + i ∂t` and, for `|s| > R`, is the stationary cylinder operator of the end, read in the
loop of frames there, which is invertible; the parametrix of the cylinder makes it Fredholm. -/
private theorem isFredholm_floerWeightedSobolevOperator_of_eq_comp_snd (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {J : ℝ × ℝ → F → AlmostComplexStructure F}
    {Ks Kt : ℝ × ℝ → F → ℝ} {Hm Hp : ℝ → F → ℝ} {Jm Jp : ℝ → F → AlmostComplexStructure F}
    {R : ℝ} {u : ℝ × ℝ → F} (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hJ : ContDiff ℝ 2 fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJper : ∀ s t, J (s, t + 1) = J (s, t)) (hJc : ∀ z y, ω.Compatible (J z y))
    (hu : ContDiff ℝ 2 u) (hup : ∀ s t, u (s, t + 1) = u (s, t)) {c : ℝ → ℝ} {δm δp : ℝ}
    (hcm : ∀ s ≤ -R, c s = δm) (hcp : ∀ s, R ≤ s → c s = δp)
    (hM : MemLp (fun z ↦ ω.floerJetCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      Ks Kt u z - c z.1 • fst ℝ F (F × F)) ∞ stripMeasure)
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1) {xm : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hxmper : Periodic xm 1) (hum : ∀ s ≤ -R, ∀ t, u (s, t) = xm t)
    (hdetm : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (Hm t)) (xm t) -
        δm • (Jm t (xm t)).toLinearMap.toContinuousLinearMap) 1 : F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0)
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpper : Periodic Hp 1) {xp : ℝ → F}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hxpper : Periodic xp 1) (hup' : ∀ s, R ≤ s → ∀ t, u (s, t) = xp t)
    (hdetp : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (Hp t)) (xp t) -
        δp • (Jp t (xp t)).toLinearMap.toContinuousLinearMap) 1 : F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0) :
    (ω.floerWeightedSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
      c).IsFredholm := by
  have : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
  -- The unitary frames `Φ z = G (J(z, u z))` of the structures `J(z, u z)`, with inverses `Ψ z`.
  obtain ⟨G, hGs, hG⟩ := exists_unitaryFrame ω hω
  set Φ : ℝ × ℝ → F →L[ℝ] F := fun z ↦ G (J z (u z))
  have hΦ : ContDiff ℝ 2 Φ := hGs (hJ.comp (contDiff_id.prodMk hu)) fun z ↦ hJc z (u z)
  have hΦi (z : ℝ × ℝ) : (Φ z).IsInvertible := (hG _ (hJc z (u z))).1
  have hΦJ (z : ℝ × ℝ) (v : F) : J z (u z) (Φ z v) = Φ z (Complex.I • v) :=
    (hG _ (hJc z (u z))).2.1 v
  have hΦω (z : ℝ × ℝ) (v w : F) : ω (Φ z v) (Φ z w) = (inner ℂ v w).im :=
    (hG _ (hJc z (u z))).2.2 v w
  have hΦp (s t : ℝ) : Φ (s, t + 1) = Φ (s, t) := by simp only [Φ, hJper, hup]
  -- Far out on the ends the frames are the loops `Φ (∓R, t)`, so they are bounded.
  have hΦm (s : ℝ) (hs : s ≤ -R) (t : ℝ) : Φ (s, t) = Φ (-R, t) := by
    simp only [Φ, hcyl.almostComplex_eq_of_le_neg (s, t) hs,
      hcyl.almostComplex_eq_of_le_neg (-R, t) le_rfl, hum s hs, hum (-R) le_rfl]
  have hΦp' (s : ℝ) (hs : R ≤ s) (t : ℝ) : Φ (s, t) = Φ (R, t) := by
    simp only [Φ, hcyl.almostComplex_eq_of_le (s, t) hs, hcyl.almostComplex_eq_of_le (R, t) le_rfl,
      hup' s hs, hup' R le_rfl]
  obtain ⟨B, B', D, hB, hB', hD⟩ := exists_forall_norm_le_of_eq_comp_snd (hΦ.of_le one_le_two)
    hΦi hΦp hΦm hΦp'
  -- The structures of the ends along the orbits, read through the cylinder data at `s = ∓R`.
  have hJm (t : ℝ) : Jm t = J (-R, t) := (hcyl.almostComplex_eq_of_le_neg (-R, t) le_rfl).symm
  have hJp (t : ℝ) : Jp t = J (R, t) := (hcyl.almostComplex_eq_of_le (R, t) le_rfl).symm
  have hΦJm (t : ℝ) (v : F) : Jm t (xm t) (Φ (-R, t) v) = Φ (-R, t) (Complex.I • v) := by
    simpa only [hJm, hum (-R) le_rfl] using hΦJ (-R, t) v
  have hΦJp (t : ℝ) (v : F) : Jp t (xp t) (Φ (R, t) v) = Φ (R, t) (Complex.I • v) := by
    simpa only [hJp, hup' R le_rfl] using hΦJ (R, t) v
  -- The end models: the stationary operators of the ends, read in the loops of frames at `s = ∓R`.
  obtain ⟨Tm, hTm, hDm⟩ := exists_loop_isInvertible_stationarySobolevOperator ω hHm hHmper hxm
    hxmper (Je := fun t ↦ Jm t (xm t)) (Φ := fun t ↦ Φ (-R, t))
    (hΦ.comp (contDiff_const.prodMk contDiff_id)) (fun t ↦ hΦp (-R) t) (fun t ↦ hΦi _)
    (fun t ↦ hΦω _) hΦJm (fun t ↦ by simp only [hJm, hJper, hxmper t]) hdetm
  obtain ⟨Tp, hTp, hDp⟩ := exists_loop_isInvertible_stationarySobolevOperator ω hHp hHpper hxp
    hxpper (Je := fun t ↦ Jp t (xp t)) (Φ := fun t ↦ Φ (R, t))
    (hΦ.comp (contDiff_const.prodMk contDiff_id)) (fun t ↦ hΦp R t) (fun t ↦ hΦi _)
    (fun t ↦ hΦω _) hΦJp (fun t ↦ by simp only [hJp, hJper, hxpper t]) hdetp
  -- Read `D_u - c(s) = ∂s + A ∂t + C` in the frames `Φ`; far out it is the end model.
  have hfo := funext fun z ↦ floerJetCoeff_sub_smul_fst_eq_firstOrderJetCoeff ω
    (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u (c z.1) z
  rw [floerWeightedSobolevOperator_def]
  rw [hfo] at hM ⊢
  refine isFredholm_jetOperator_firstOrderJetCoeff_of_frame hΦ hΦp hΦi hB hB' hD hM hΦJ hDm hDp
    (R := R) (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · rw [firstOrderJetCoeff_frame_eq_stationaryJetCoeff ω hxm (Φe := fun t ↦ Φ (-R, t))
      (fun t ↦ hΦi _) hΦJm (hcyl.almostComplex_eq_of_le_neg z hz.le)
      (hcyl.hamiltonianS_eq_zero z fun h ↦ (lt_irrefl _ (hz.trans h.1)))
      (hcyl.hamiltonianT_eq_of_le_neg z hz.le) (eventuallyEq_comp_snd_of_lt hum hz)
      (hcm z.1 hz.le) (eventuallyEq_comp_snd_of_lt hΦm hz), ← hTm]
  · rw [firstOrderJetCoeff_frame_eq_stationaryJetCoeff ω hxp (Φe := fun t ↦ Φ (R, t))
      (fun t ↦ hΦi _) hΦJp (hcyl.almostComplex_eq_of_le z hz.le)
      (hcyl.hamiltonianS_eq_zero z fun h ↦ (lt_irrefl _ (h.2.trans hz)))
      (hcyl.hamiltonianT_eq_of_le z hz.le) (eventuallyEq_comp_snd_of_gt hup' hz)
      (hcp z.1 hz.le) (eventuallyEq_comp_snd_of_gt hΦp' hz), ← hTp]

end Core

section Compatible

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The weighted linearized Floer operator on the cylinder is Fredholm for every compatible
almost complex structure.** Let `F` be a finite-dimensional complex inner product space whose
symplectic form `ω` is `Im ⟪·, ·⟫`, and let the Floer data `(J, K_s, K_t)`, of class `C²` and with
`J` of period one in `t` and compatible with `ω`, be cylindrical near the ends: equal to
`(J₋_t, 0, H₋_t)` for `s ≤ -R` and to `(J₊_t, 0, H₊_t)` for `s ≥ R`. Let `H±` be one-periodic,
jointly `C³` Hamiltonians with one-periodic orbits `x±`, and let the slope `c` of the weight be
continuous and equal to `δ₋` for `s ≤ -R` and to `δ₊` for `s ≥ R`, where the shifted fields
`dX_{H±_t}(x±(t)) - δ± J±_t(x±(t))` have nondegenerate return maps: `δ±` is not an eigenvalue of
the asymptotic operator at `x±`. If `u` is a `C¹` map whose loops converge uniformly to `x₋` at
`-∞` and to `x₊` at `+∞`, with slice defects `∂t u - X_{H±_t}(u)` tending uniformly to zero there,
then the realization `D_u - c(s) : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer
operator conjugated by the weight `e^{κ(s)}`, `κ' = c`, is Fredholm. -/
theorem isFredholm_floerWeightedSobolevOperator_of_cylindrical_of_compatible
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    {J : ℝ × ℝ → F → AlmostComplexStructure F} {Ks Kt : ℝ × ℝ → F → ℝ} {Hm Hp : ℝ → F → ℝ}
    {Jm Jp : ℝ → F → AlmostComplexStructure F} {R : ℝ} {u : ℝ × ℝ → F}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hJ : ContDiff ℝ 2 fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJper : ∀ s t, J (s, t + 1) = J (s, t)) (hKs : ContDiff ℝ 2 (uncurry Ks))
    (hKt : ContDiff ℝ 2 (uncurry Kt)) (hJc : ∀ z y, ω.Compatible (J z y)) (hu : ContDiff ℝ 1 u)
    {c : ℝ → ℝ} (hc : Continuous c) {δm δp : ℝ} (hcm : ∀ s ≤ -R, c s = δm)
    (hcp : ∀ s, R ≤ s → c s = δp)
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1) {xm : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hxmper : Periodic xm 1)
    (hdetm : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (Hm t)) (xm t) -
        δm • (Jm t (xm t)).toLinearMap.toContinuousLinearMap) 1 : F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpper : Periodic Hp 1) {xp : ℝ → F}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hxpper : Periodic xp 1)
    (hdetp : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (Hp t)) (xp t) -
        δp • (Jp t (xp t)).toLinearMap.toContinuousLinearMap) 1 : F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0)
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    (ω.floerWeightedSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
      c).IsFredholm := by
  have hJ₁ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap :=
    hJ.of_le one_le_two
  -- A `C²` map `u'`, equal to the orbit `x₋` for `s ≤ -a` and to the orbit `x₊` for `s ≥ a`.
  set a : ℝ := |R| + 1
  have hRa : R ≤ a := by linarith [le_abs_self R]
  obtain ⟨u', hu', hu'per, hu'm, hu'p⟩ := exists_contDiff_eq_comp_snd
    (ω.contDiff_of_hasDerivAt_hamiltonianVectorField (n := 1) (hHm.of_le (by norm_num)) hxm)
    (ω.contDiff_of_hasDerivAt_hamiltonianVectorField (n := 1) (hHp.of_le (by norm_num)) hxp)
    hxmper hxpper (by positivity : 0 < a)
  obtain ⟨hu'xm, hδ'm⟩ := tendstoUniformlyOn_and_sliceDefect_of_eventuallyEq ω hxm
    (eventually_atBot.2 ⟨-a - 1, fun s hs t ↦ eventuallyEq_comp_snd_of_lt hu'm
      (by simp only; linarith)⟩)
  obtain ⟨hu'xp, hδ'p⟩ := tendstoUniformlyOn_and_sliceDefect_of_eventuallyEq ω hxp
    (eventually_atTop.2 ⟨a + 1, fun s hs t ↦ eventuallyEq_comp_snd_of_gt hu'p
      (by simp only; linarith)⟩)
  -- The Fredholm property depends only on the asymptotics of the map, so it suffices to prove it
  -- for `u'`.
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [ω.isFredholm_floerWeightedSobolevOperator_iff_of_cylindrical hcyl hJ₁ hKs hKt hJc hu
    (hu'.of_le one_le_two) hc hcm hcp hxm hdetm huxm hδm hu'xm hδ'm hxp hdetp huxp hδp hu'xp hδ'p]
  -- The structures of the ends are `C¹`, as values of `J` at `s = ∓R`.
  have hJe₁ {Je : ℝ → F → AlmostComplexStructure F} (b : ℝ) (hb : ∀ t, J (b, t) = Je t) :
      ContDiff ℝ 1 fun p : ℝ × F ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap := by
    have heq : (fun p : ℝ × F ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap) =
        (fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) ∘
          fun p : ℝ × F ↦ ((b, p.1), p.2) := funext fun p ↦ by simp [hb]
    rw [heq]
    exact hJ₁.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  have hcyl' := Floer.isCylindricalNearEnds_of_contDiff (hcyl.mono hRa) hJ₁ hKs hKt u'
  have hcm' (s : ℝ) (hs : s ≤ -a) : c s = δm := hcm s (by linarith)
  have hcp' (s : ℝ) (hs : a ≤ s) : c s = δp := hcp s (by linarith)
  exact isFredholm_floerWeightedSobolevOperator_of_eq_comp_snd ω hω hcyl' hJ hJper hJc hu' hu'per
    hcm' hcp' (ω.memLp_floerJetCoeff_sub_smul_fst_of_cylindrical hcyl' (hu'.of_le one_le_two)
      (hHm.of_le (by norm_num)) (hJe₁ (-R) fun t ↦ hcyl.almostComplex_eq_of_le_neg (-R, t) le_rfl)
      hu'xm hδ'm (hHp.of_le (by norm_num))
      (hJe₁ R fun t ↦ hcyl.almostComplex_eq_of_le (R, t) le_rfl) hu'xp hδ'p hc hcm' hcp')
    hHm hHmper hxm hxmper hu'm hdetm hHp hHpper hxp hxpper hu'p hdetp

end Compatible

end TauCeti.SymplecticForm

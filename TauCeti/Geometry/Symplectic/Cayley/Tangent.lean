/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cayley.Smooth
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import TauCeti.Analysis.Calculus.Deriv.BoundedReparametrization
public import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Geometry.Symplectic.Transport

/-!
# Tangent conditions for variations of tame and compatible complex structures

Transversality arguments for pseudoholomorphic curves and Floer trajectories vary the almost
complex structure, possibly depending on a point of the domain. A variation of a complex
structure `J` on a finite-dimensional real vector space `V` is the velocity `Y = J'(0)` of a
family of complex structures through `J`. Differentiating `J² = -1` gives the linear condition
`Y J + J Y = 0`. For a family of `ω`-compatible structures, differentiating the invariance
`ω(J v, J w) = ω(v, w)` shows that `Y` is moreover skew-adjoint for `ω`:
`ω(Y v, w) + ω(v, Y w) = 0`. Tameness is an open condition and imposes nothing further, so the
two conditions differ: tame variations only anticommute with `J`, while compatible variations
are also skew-adjoint.

The two linear spaces of endomorphisms are defined algebraically in
`TauCeti.Geometry.Symplectic.AlmostComplex`:

* `TauCeti.AlmostComplexStructure.tangentSpace J`: the `Y` with `Y J + J Y = 0`;
* `TauCeti.SymplecticForm.compatibleTangentSpace ω J`: the `Y` in it that are also
  skew-adjoint for `ω`.

This file proves that they are exactly the velocities of curves of tame, respectively compatible,
structures:

* `TauCeti.AlmostComplexStructure.mem_tangentSpace_of_hasFDerivAt`: every directional derivative
  of a differentiable family of complex structures, over any normed parameter space, satisfies
  `Y J + J Y = 0`.
* `TauCeti.SymplecticForm.mem_compatibleTangentSpace_of_hasFDerivAt`: if the family preserves
  `ω` near the base point, its directional derivatives lie in the compatible tangent space.
* `TauCeti.SymplecticForm.Compatible.exists_contDiff_hasDerivAt`: conversely, every `Y` in the
  compatible tangent space of a compatible `J` is the velocity at `0` of a curve of compatible
  structures through `J` that is defined and analytic on the whole real line. The curve is the
  inverse Cayley chart of `TauCeti.SymplecticForm.Compatible.compatibleCayleyEquiv` along a
  bounded reparametrization of the line through `-(1/2) J Y`.
* `TauCeti.SymplecticForm.Tames.exists_contDiff_hasDerivAt`: every `Y` anticommuting with a
  tame `J` is the velocity at `0` of an analytic curve of tame structures through `J`, obtained by
  conjugating `J` by `1 + φ(t) Z` with `Z = -(1/2) Y J`.
* `TauCeti.SymplecticForm.Compatible.mem_compatibleTangentSpace_iff_exists_hasDerivAt` and
  `TauCeti.SymplecticForm.Tames.mem_tangentSpace_iff_exists_hasDerivAt`: the resulting
  characterizations of the two tangent spaces.

The curves are defined on the whole real line by composing a line with the bounded
reparametrization `TauCeti.exists_contDiff_hasDerivAt_abs_le`.

The companion algebraic statement, in `TauCeti.Geometry.Symplectic.AlmostComplex`, is that
compatible variations reach every vector at every nonzero vector: for `ξ ≠ 0` and any
`η` there is `Y` in the compatible tangent space with `Y ξ = η`
(`TauCeti.SymplecticForm.Compatible.exists_mem_compatibleTangentSpace_apply_eq`). In the
linearization of the Floer operator `∂_s u - X_{K_s} + J (∂_t u - X_{K_t})`, a variation `Y` of
`J` contributes the term `Y (∂_t u - X_{K_t})`. So this is the pointwise range statement for
variations of the almost complex structure at points where the perturbed derivative is nonzero.
Unlike Hamiltonian variations, these variations multiply the perturbed derivative and reach
nothing at its zeros.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.2 (the tangent space of the space of compatible
  almost complex structures and the values of its elements at a nonzero vector).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.5 (the Cayley chart on compatible complex structures).
-/

public section

open Filter Topology

namespace TauCeti

/-! ### Velocities of families of complex structures -/

namespace AlmostComplexStructure

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {J : P → AlmostComplexStructure V} {x : P} {F' : P →L[ℝ] V →L[ℝ] V}

/-- **Velocities of complex structures anticommute with them.** If a family of complex
structures is differentiable at `x`, as a family of continuous endomorphisms, then each of its
directional derivatives `Y` satisfies `Y J + J Y = 0` at `J = J x`. -/
theorem mem_tangentSpace_of_hasFDerivAt
    (hF : HasFDerivAt (fun p => LinearMap.toContinuousLinearMap (J p).toLinearMap) F' x)
    (h : P) : (F' h : Module.End ℝ V) ∈ (J x).tangentSpace := by
  set F := fun p => LinearMap.toContinuousLinearMap (J p).toLinearMap
  have hsq : F * F = fun _ => -1 := funext fun p => by
    ext v
    simp [F]
  have hd := hF.mul' hF
  rw [hsq] at hd
  have h0 := congrArg (· h) (hd.unique (hasFDerivAt_const _ x))
  simp only [add_apply, smul_apply, smul_eq_mul,
    zero_apply] at h0
  rw [mem_tangentSpace_iff_apply]
  intro v
  have hv := congrArg (fun A : V →L[ℝ] V => A v) h0
  simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, add_apply, mul_apply_eq_comp,
    zero_apply, F, LinearMap.coe_toContinuousLinearMap'] at hv
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact hv

end AlmostComplexStructure

namespace SymplecticForm

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ω : SymplecticForm V} {J : P → AlmostComplexStructure V} {x : P} {F' : P →L[ℝ] V →L[ℝ] V}

/-- **Velocities of compatible structures.** If a family of complex structures preserving `ω`
near `x` is differentiable at `x`, as a family of continuous endomorphisms, then each of its
directional derivatives lies in the compatible tangent space at `J x`. -/
theorem mem_compatibleTangentSpace_of_hasFDerivAt (hJ : ∀ᶠ p in 𝓝 x, ω.Invariant (J p))
    (hF : HasFDerivAt (fun p => LinearMap.toContinuousLinearMap (J p).toLinearMap) F' x)
    (h : P) : (F' h : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J x) := by
  have hT := AlmostComplexStructure.mem_tangentSpace_of_hasFDerivAt hF h
  rw [mem_compatibleTangentSpace]
  refine ⟨AlmostComplexStructure.mem_tangentSpace_iff_apply.1 hT, fun v w => ?_⟩
  -- Invariance of a complex structure is the linear condition `ω (J v) w + ω v (J w) = 0`.
  let ℓ : (V →L[ℝ] V) →ₗ[ℝ] ℝ :=
    { toFun := fun A => ω (A v) w + ω v (A w)
      map_add' := fun A B => by
        simp only [add_apply, map_add, LinearMap.add_apply]
        ring
      map_smul' := fun r A => by
        simp only [smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }
  have hℓ : (fun p => LinearMap.toContinuousLinearMap ℓ
      (LinearMap.toContinuousLinearMap (J p).toLinearMap)) =ᶠ[𝓝 x] fun _ => 0 :=
    hJ.mono fun p hp => by
      simpa [ℓ] using Invariant.apply_add_apply_eq_zero hp v w
  have hd := (LinearMap.toContinuousLinearMap ℓ).hasFDerivAt.comp x hF
  have h0 := congrArg (· h) (hd.unique ((hasFDerivAt_const 0 x).congr_of_eventuallyEq hℓ))
  simpa [ℓ] using h0

/-! ### Curves of compatible and tame structures with prescribed velocity -/

/-- Small multiples of a coordinate of the compatible Cayley ball of a compatible `J` lie in
that ball. -/
private theorem Compatible.exists_pos_smul_mem_compatibleCayleyBall
    {J : AlmostComplexStructure V} (h : ω.Compatible J) {C : Module.End ℝ V}
    (hC : C ∈ J.tangentSpace) (hCs : (ω.associatedBilinForm J).IsSelfAdjoint C) :
    ∃ ε > 0, ∀ s : ℝ, |s| ≤ ε → s • C ∈ ω.compatibleCayleyBall J := by
  -- The forms `g - s² B`, with `g = ω(·, J ·)` and `B = g(C ·, C ·)`, are positive at `s = 0`, and
  -- positivity is open.
  set g := (ω.associatedBilinForm J).toContinuousBilinearMap
  set B := ((ω.associatedBilinForm J).compl₁₂ C C).toContinuousBilinearMap
  -- Supply the existing topological instance for the nested operator space explicitly.
  let : ContinuousAdd (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.isTopologicalAddGroup.toContinuousAdd
  have hf : Continuous fun s : ℝ => g + -s ^ 2 • B := by fun_prop
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ v, v ≠ 0 → 0 < (g + -s ^ 2 • B) v v :=
    hf.continuousAt.preimage_mem_nhds (isOpen_setOf_forall_bilinear_apply_self_pos.mem_nhds
      fun v hv => by simpa [g] using h.tames v hv)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨r / 2, half_pos hr, fun s hs => ?_⟩
  have hpos := hball (show dist s 0 < r by rw [Real.dist_eq, sub_zero]; linarith)
  refine mem_compatibleCayleyBall.2 ⟨mem_cayleyBall.2 ⟨?_, fun v hv => ?_⟩, fun v w => ?_⟩
  · rw [smul_mul_assoc, mul_smul_comm, ← smul_neg,
      eq_neg_of_add_eq_zero_left (AlmostComplexStructure.mem_tangentSpace.1 hC)]
  · have h₁ := hpos v hv
    simp only [g, B, add_apply, smul_apply,
      LinearMap.toContinuousBilinearMap_apply, LinearMap.compl₁₂_apply, associatedBilinForm_apply,
      smul_eq_mul] at h₁
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    nlinarith
  · have := hCs v w
    simp only [associatedBilinForm_apply] at this
    simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [this]

/-- **Every compatible variation is a velocity.** For an `ω`-compatible `J` and `Y` in the
compatible tangent space at `J`, there is a curve of `ω`-compatible structures through `J`,
defined and analytic on the whole real line, with velocity `Y` at `0`. -/
theorem Compatible.exists_contDiff_hasDerivAt {J : AlmostComplexStructure V}
    (h : ω.Compatible J) {Y : V →L[ℝ] V}
    (hY : (Y : Module.End ℝ V) ∈ ω.compatibleTangentSpace J) :
    ∃ c : ℝ → AlmostComplexStructure V, (∀ t, ω.Compatible (c t)) ∧ c 0 = J ∧
      ContDiff ℝ ⊤ (fun t => LinearMap.toContinuousLinearMap (c t).toLinearMap) ∧
      HasDerivAt (fun t => LinearMap.toContinuousLinearMap (c t).toLinearMap) Y 0 := by
  set Jc := LinearMap.toContinuousLinearMap J.toLinearMap
  -- Under the inverse Cayley chart `C ↦ J (1 + C)(1 - C)⁻¹`, the line through
  -- `C = -(1/2) J Y` has velocity `2 J C = Y` at `0`.
  set C : V →L[ℝ] V := -(1 / 2 : ℝ) • (Jc * Y)
  obtain ⟨hCT, hCs⟩ := h.invariant.mul_mem_tangentSpace_and_isSelfAdjoint hY
  have hCl : (C : Module.End ℝ V) = -(1 / 2 : ℝ) • (J.toLinearMap * Y) := by
    simp [C, Jc]
  obtain ⟨ε, hε, hball⟩ := h.exists_pos_smul_mem_compatibleCayleyBall (C := C)
    (by rw [hCl]; exact Submodule.smul_mem _ _ hCT)
    (by rw [hCl]; exact Submodule.smul_mem (ω.associatedBilinForm J).selfAdjointSubmodule _ hCs)
  -- A bounded reparametrization of the line keeps it inside the ball.
  obtain ⟨φ, hφs, hφ0, hφd, hφ⟩ := exists_contDiff_hasDerivAt_abs_le hε
  have hmem (t : ℝ) : (φ t • C : V →L[ℝ] V).toLinearMap ∈ ω.compatibleCayleyBall J := by
    simpa using hball (φ t) (hφ t)
  set c : ℝ → AlmostComplexStructure V := fun t =>
    (h.compatibleCayleyEquiv.symm ⟨(φ t • C : V →L[ℝ] V).toLinearMap, hmem t⟩).val
  have hc0 : c 0 = J := AlmostComplexStructure.toLinearMap_injective (by simp [c, hφ0])
  have hcs : ContDiff ℝ ⊤ (fun t => LinearMap.toContinuousLinearMap (c t).toLinearMap) :=
    h.contDiff_compatibleCayleyEquiv_symm hmem (hφs.smul contDiff_const)
  refine ⟨c, fun t => (h.compatibleCayleyEquiv.symm _).property, hc0, hcs, ?_⟩
  -- Differentiate the identity `c t (1 - φ t C) = J (1 + φ t C)` at `0`.
  set G := fun t => LinearMap.toContinuousLinearMap (c t).toLinearMap
  have hG : HasDerivAt G (deriv G 0) 0 :=
    ((hcs.differentiable (by simp)) 0).hasDerivAt
  have hid : (fun t => G t * (1 - φ t • C)) = fun t => Jc * (1 + φ t • C) := funext fun t => by
    simp only [G, c, h.compatibleCayleyEquiv_symm_apply_toContinuousLinearMap _ (hmem t)]
    rw [mul_assoc, Ring.inverse_mul_cancel _
      (isUnit_one_sub_of_toLinearMap_mem_cayleyBall
        (compatibleCayleyBall_subset_cayleyBall (hmem t))), mul_one]
  have hC' : HasDerivAt (fun t => φ t • C) C 0 := by simpa using hφd.smul_const C
  have hL : HasDerivAt (fun t => G t * (1 - φ t • C))
      (deriv G 0 * (1 - φ 0 • C) + G 0 * (0 - C)) 0 :=
    hG.mul ((hasDerivAt_const 0 (1 : V →L[ℝ] V)).sub hC')
  have hR : HasDerivAt (fun t => Jc * (1 + φ t • C)) (0 * (1 + φ 0 • C) + Jc * (0 + C)) 0 :=
    (hasDerivAt_const 0 Jc).mul ((hasDerivAt_const 0 (1 : V →L[ℝ] V)).add hC')
  rw [hid] at hL
  have heq := hL.unique hR
  have hG0 : G 0 = Jc := by simp [G, hc0, Jc]
  have hJJ : Jc * Jc = -1 := by
    ext v
    simp [Jc]
  simp only [hφ0, zero_smul, sub_zero, add_zero, mul_one, hG0, zero_add, zero_sub,
    mul_neg] at heq
  have hJC : Jc * C = (1 / 2 : ℝ) • Y := by
    simp [C, ← mul_assoc, hJJ]
  have hY' : deriv G 0 = Y := by
    rw [hJC] at heq
    linear_combination (norm := module) heq
  rwa [hY'] at hG

/-- **The compatible tangent space consists of velocities.** For an `ω`-compatible `J`, a
continuous endomorphism `Y` lies in the compatible tangent space at `J` exactly when it is the
velocity at `0` of a curve of `ω`-compatible structures through `J`. -/
theorem Compatible.mem_compatibleTangentSpace_iff_exists_hasDerivAt
    {J : AlmostComplexStructure V} (h : ω.Compatible J) {Y : V →L[ℝ] V} :
    (Y : Module.End ℝ V) ∈ ω.compatibleTangentSpace J ↔
      ∃ c : ℝ → AlmostComplexStructure V, (∀ t, ω.Compatible (c t)) ∧ c 0 = J ∧
        HasDerivAt (fun t => LinearMap.toContinuousLinearMap (c t).toLinearMap) Y 0 := by
  refine ⟨fun hY => ?_, ?_⟩
  · obtain ⟨c, hc, hc0, -, hd⟩ := h.exists_contDiff_hasDerivAt hY
    exact ⟨c, hc, hc0, hd⟩
  · rintro ⟨c, hc, rfl, hd⟩
    simpa using mem_compatibleTangentSpace_of_hasFDerivAt
      (Eventually.of_forall fun t => (hc t).invariant) hd.hasFDerivAt 1


/-- Conjugating a tame structure by an endomorphism close to the identity keeps it tame: for
small multiples `s Z` of a fixed `Z`, the endomorphism `1 + s Z` is invertible (`‖s Z‖ < 1`) and
`ω((1 + s Z) w, (1 + s Z) J w)` is positive for `w ≠ 0`. -/
private theorem Tames.exists_pos_norm_smul_lt_one_and_pos {J : AlmostComplexStructure V}
    (h : ω.Tames J) (Z : V →L[ℝ] V) :
    ∃ ε > 0, ∀ s : ℝ, |s| ≤ ε → ‖s • Z‖ < 1 ∧
      ∀ w, w ≠ 0 → 0 < ω ((1 + s • Z) w) ((1 + s • Z) (J w)) := by
  -- The conjugated form is the polynomial family `g + s B₁ + s² B₂` with `g = ω(·, J ·)`. It is
  -- positive at `s = 0`, and positivity is open.
  set g := (ω.associatedBilinForm J).toContinuousBilinearMap
  set B₁ := (ω.toBilinForm.compl₁₂ Z.toLinearMap J.toLinearMap +
    ω.toBilinForm.compl₂ (Z.toLinearMap * J.toLinearMap)).toContinuousBilinearMap
  set B₂ := (ω.toBilinForm.compl₁₂ Z.toLinearMap
    (Z.toLinearMap * J.toLinearMap)).toContinuousBilinearMap
  -- Supply the existing topological instance for the nested operator space explicitly.
  let : ContinuousAdd (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.isTopologicalAddGroup.toContinuousAdd
  have hf₁ : Continuous fun s : ℝ => g + s • B₁ := by fun_prop
  have hf : Continuous fun s : ℝ => g + s • B₁ + s ^ 2 • B₂ := hf₁.add (by fun_prop)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ),
      ‖s • Z‖ < 1 ∧ ∀ w, w ≠ 0 → 0 < (g + s • B₁ + s ^ 2 • B₂) w w :=
    ((continuous_id.smul continuous_const).norm.continuousAt.eventually_lt continuousAt_const
      (by simp)).and
      (hf.continuousAt.preimage_mem_nhds (isOpen_setOf_forall_bilinear_apply_self_pos.mem_nhds
        fun w hw => by simpa [g] using h w hw))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨r / 2, half_pos hr, fun s hs => ?_⟩
  obtain ⟨hn, hpos⟩ := hball (show dist s 0 < r by rw [Real.dist_eq, sub_zero]; linarith)
  refine ⟨hn, fun w hw => ?_⟩
  have h₁ := hpos w hw
  simp only [g, B₁, B₂, add_apply, smul_apply,
    LinearMap.toContinuousBilinearMap_apply, LinearMap.add_apply, LinearMap.compl₁₂_apply,
    LinearMap.compl₂_apply, ContinuousLinearMap.coe_coe, mul_apply_eq_comp,
    associatedBilinForm_apply, smul_eq_mul] at h₁
  simp only [add_apply, one_apply_eq_self, smul_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  nlinarith


/-- **Every tame variation is a velocity.** For an `ω`-tame `J` and a continuous endomorphism
`Y` anticommuting with `J`, there is a curve of `ω`-tame structures through `J`, defined and
analytic on the whole real line, with velocity `Y` at `0`. The curve conjugates `J` by
`1 + φ(t) Z` with `Z = -(1/2) Y J` and a bounded reparametrization `φ`. -/
theorem Tames.exists_contDiff_hasDerivAt {J : AlmostComplexStructure V} (h : ω.Tames J)
    {Y : V →L[ℝ] V} (hY : (Y : Module.End ℝ V) ∈ J.tangentSpace) :
    ∃ c : ℝ → AlmostComplexStructure V, (∀ t, ω.Tames (c t)) ∧ c 0 = J ∧
      ContDiff ℝ ⊤ (fun t => LinearMap.toContinuousLinearMap (c t).toLinearMap) ∧
      HasDerivAt (fun t => LinearMap.toContinuousLinearMap (c t).toLinearMap) Y 0 := by
  set Jc := LinearMap.toContinuousLinearMap J.toLinearMap
  have hJJ : Jc * Jc = -1 := by
    ext v
    simp [Jc]
  have hYJ : Jc * Y = -(Y * Jc) := by
    ext v
    have hv := AlmostComplexStructure.mem_tangentSpace_iff_apply.1 hY v
    simp only [ContinuousLinearMap.coe_coe] at hv
    simp [Jc, hv]
  -- Conjugation by `P t = 1 + φ t Z` has velocity `Z J - J Z = Y` at `0`.
  set Z : V →L[ℝ] V := -(1 / 2 : ℝ) • (Y * Jc)
  obtain ⟨ε, hε, hsmall⟩ := h.exists_pos_norm_smul_lt_one_and_pos Z
  obtain ⟨φ, hφs, hφ0, hφd, hφ⟩ := exists_contDiff_hasDerivAt_abs_le hε
  set P : ℝ → V →L[ℝ] V := fun t => 1 + φ t • Z
  have hPu (t : ℝ) : IsUnit (P t) := by
    have hn : ‖-(φ t • Z)‖ < 1 := by rw [norm_neg]; exact (hsmall _ (hφ t)).1
    simpa [P, sub_neg_eq_add] using (Units.oneSub _ hn).isUnit
  set K : ℝ → V →L[ℝ] V := fun t => P t * Jc * Ring.inverse (P t)
  have hKP (t : ℝ) : K t * P t = P t * Jc := by
    simp only [K]
    rw [mul_assoc, Ring.inverse_mul_cancel _ (hPu t), mul_one]
  set e : ℝ → V ≃L[ℝ] V := fun t => ContinuousLinearEquiv.unitsEquiv ℝ V (hPu t).unit
  have he (t : ℝ) (v : V) : e t v = P t v := by simp [e]
  have he' (t : ℝ) (v : V) : (e t).symm v = Ring.inverse (P t) v := by
    rw [ContinuousLinearEquiv.symm_apply_eq, he, ← mul_apply_eq_comp,
      Ring.mul_inverse_cancel _ (hPu t), one_apply_eq_self]
  set c : ℝ → AlmostComplexStructure V := fun t => J.transport (e t).toLinearEquiv
  have hcK : (fun t => LinearMap.toContinuousLinearMap (c t).toLinearMap) = K := by
    funext t
    ext v
    simp only [c, K, Jc, LinearMap.coe_toContinuousLinearMap', mul_apply_eq_comp,
      AlmostComplexStructure.transport_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.coe_symm_toLinearEquiv, he, he']
  have hP0 : P 0 = 1 := by simp [P, hφ0]
  have hK0 : K 0 = Jc := by simp [K, hP0]
  have hKs : ContDiff ℝ ⊤ K := by
    refine contDiff_iff_contDiffAt.2 fun t => ?_
    obtain ⟨u, hu⟩ := hPu t
    have hP : ContDiffAt ℝ ⊤ P t := (contDiff_const.add (hφs.smul contDiff_const)).contDiffAt
    have hi : ContDiffAt ℝ ⊤ (fun t => Ring.inverse (P t)) t := by
      have hi := contDiffAt_ringInverse (n := ⊤) ℝ u
      rw [hu] at hi
      exact hi.comp t hP
    exact (hP.mul contDiffAt_const).mul hi
  refine ⟨c, fun t v hv => ?_, AlmostComplexStructure.toLinearMap_injective ?_, hcK ▸ hKs, ?_⟩
  · -- Writing `v = P t w`, the form `ω(v, c t v)` is `ω(P t w, P t (J w))`.
    obtain ⟨u, hu⟩ := hPu t
    set w := (↑u⁻¹ : V →L[ℝ] V) v
    have hvw : v = P t w := by
      have h1 : ((u : V →L[ℝ] V) * ↑u⁻¹) v = v := by rw [Units.mul_inv, one_apply_eq_self]
      rw [← hu]
      exact h1.symm
    have hw : w ≠ 0 := by
      rintro hw0
      exact hv (by rw [hvw, hw0, map_zero])
    have hKv : K t v = P t (J w) := by
      simp only [K, ← hu, Ring.inverse_unit, mul_apply_eq_comp, w, Jc,
        LinearMap.coe_toContinuousLinearMap']
    have hcv : c t v = K t v := congrArg (fun A : V →L[ℝ] V => A v) (congrFun hcK t)
    rw [hcv, hKv, hvw]
    exact (hsmall _ (hφ t)).2 w hw
  · ext v
    simpa [hK0, Jc] using congrArg (fun A : V →L[ℝ] V => A v) (congrFun hcK 0)
  -- Differentiate the identity `K t * P t = P t * J` at `0`.
  rw [hcK]
  have hK : HasDerivAt K (deriv K 0) 0 := ((hKs.differentiable (by simp)) 0).hasDerivAt
  have hP' : HasDerivAt P Z 0 := ((hφd.smul_const Z).const_add 1).congr_deriv (one_smul ℝ Z)
  have hL : HasDerivAt (fun t => K t * P t) (deriv K 0 * P 0 + K 0 * Z) 0 := hK.mul hP'
  have hR : HasDerivAt (fun t => P t * Jc) (Z * Jc + P 0 * 0) 0 :=
    hP'.mul (hasDerivAt_const 0 Jc)
  rw [show (fun t => K t * P t) = fun t => P t * Jc from funext hKP] at hL
  have heq := hL.unique hR
  have hZJ : Z * Jc = (1 / 2 : ℝ) • Y := by
    simp [Z, mul_assoc, hJJ]
  have hJZ : Jc * Z = -((1 / 2 : ℝ) • Y) := by
    simp only [Z, mul_smul_comm, ← mul_assoc, hYJ]
    simp [mul_assoc, hJJ]
  have hK' : deriv K 0 = Y := by
    simp only [hP0, hK0, mul_one, mul_zero, add_zero, hZJ, hJZ] at heq
    linear_combination (norm := module) heq
  rwa [hK'] at hK

/-- **The tangent space at a tame structure consists of velocities.** For an `ω`-tame `J`, a
continuous endomorphism `Y` anticommutes with `J` exactly when it is the velocity at `0` of a
curve of `ω`-tame structures through `J`. -/
theorem Tames.mem_tangentSpace_iff_exists_hasDerivAt {J : AlmostComplexStructure V}
    (h : ω.Tames J) {Y : V →L[ℝ] V} :
    (Y : Module.End ℝ V) ∈ J.tangentSpace ↔
      ∃ c : ℝ → AlmostComplexStructure V, (∀ t, ω.Tames (c t)) ∧ c 0 = J ∧
        HasDerivAt (fun t => LinearMap.toContinuousLinearMap (c t).toLinearMap) Y 0 := by
  refine ⟨fun hY => ?_, ?_⟩
  · obtain ⟨c, hc, hc0, -, hd⟩ := h.exists_contDiff_hasDerivAt hY
    exact ⟨c, hc, hc0, hd⟩
  · rintro ⟨c, -, rfl, hd⟩
    simpa using AlmostComplexStructure.mem_tangentSpace_of_hasFDerivAt hd.hasFDerivAt 1

end SymplecticForm

end TauCeti

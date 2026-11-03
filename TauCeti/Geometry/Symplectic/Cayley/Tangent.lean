/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cayley.Smooth
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import TauCeti.Topology.Algebra.Module.BilinearForm

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

This file defines the two linear spaces of endomorphisms,

* `TauCeti.AlmostComplexStructure.tangentSpace J`: the `Y` with `Y J + J Y = 0`;
* `TauCeti.SymplecticForm.compatibleTangentSpace ω J`: the `Y` in it that are also
  skew-adjoint for `ω`,

and proves that they are exactly the velocities of curves of tame, respectively compatible,
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

Among endomorphisms anticommuting with `J`, skew-adjointness for `ω` is self-adjointness for the
form `g = ω(·, J ·)` (`TauCeti.SymplecticForm.mem_compatibleTangentSpace_iff_isSelfAdjoint`).

Finally, compatible variations reach every vector at every nonzero vector: for `ξ ≠ 0` and any
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

namespace AlmostComplexStructure

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The tangent condition at a complex structure `J`: the endomorphisms `Y` with
`Y J + J Y = 0`. Velocities of families of complex structures through `J` satisfy it
(`AlmostComplexStructure.mem_tangentSpace_of_hasFDerivAt`), and for a tame `J` it is exactly the
set of velocities of curves of tame structures
(`SymplecticForm.Tames.mem_tangentSpace_iff_exists_hasDerivAt`). -/
def tangentSpace (J : AlmostComplexStructure V) : Submodule ℝ (Module.End ℝ V) :=
  LinearMap.ker (LinearMap.mulRight ℝ J.toLinearMap + LinearMap.mulLeft ℝ J.toLinearMap)

/-- Membership in the tangent space at `J` is anticommutation with `J`. -/
@[simp]
theorem mem_tangentSpace {J : AlmostComplexStructure V} {Y : Module.End ℝ V} :
    Y ∈ J.tangentSpace ↔ Y * J.toLinearMap + J.toLinearMap * Y = 0 := by
  simp [tangentSpace]

/-- Membership in the tangent space at `J`, pointwise: `Y (J v) = -J (Y v)`. -/
theorem mem_tangentSpace_iff_apply {J : AlmostComplexStructure V} {Y : Module.End ℝ V} :
    Y ∈ J.tangentSpace ↔ ∀ v, Y (J v) = -J (Y v) := by
  rw [mem_tangentSpace, LinearMap.ext_iff]
  refine forall_congr' fun v => ?_
  simp only [LinearMap.add_apply, mul_apply_eq_comp, LinearMap.zero_apply]
  exact add_eq_zero_iff_eq_neg

end AlmostComplexStructure

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {Y : Module.End ℝ V}

variable (ω J) in
/-- The tangent condition at an `ω`-compatible complex structure `J`: the endomorphisms that
anticommute with `J` and are skew-adjoint for `ω`. For a compatible `J` it is exactly the set of
velocities of curves of compatible structures
(`SymplecticForm.Compatible.mem_compatibleTangentSpace_iff_exists_hasDerivAt`). -/
def compatibleTangentSpace : Submodule ℝ (Module.End ℝ V) :=
  J.tangentSpace ⊓ ω.toBilinForm.skewAdjointSubmodule

/-- Membership in the compatible tangent space: `Y (J v) = -J (Y v)` and
`ω (Y v) w + ω v (Y w) = 0`. -/
theorem mem_compatibleTangentSpace :
    Y ∈ ω.compatibleTangentSpace J ↔
      (∀ v, Y (J v) = -J (Y v)) ∧ ∀ v w, ω (Y v) w + ω v (Y w) = 0 := by
  rw [compatibleTangentSpace, Submodule.mem_inf, AlmostComplexStructure.mem_tangentSpace_iff_apply,
    LinearMap.mem_skewAdjointSubmodule]
  refine and_congr Iff.rfl (forall₂_congr fun v w => ?_)
  -- `IsSkewAdjoint` unfolds to `IsAdjointPair`, which is stated pointwise by definition.
  change ω (Y v) w = ω v (-Y w) ↔ _
  beta_reduce
  rw [map_neg, ← sub_eq_zero, sub_neg_eq_add]

/-- The compatible tangent condition is stronger than the tangent condition. -/
theorem compatibleTangentSpace_le_tangentSpace : ω.compatibleTangentSpace J ≤ J.tangentSpace :=
  inf_le_left

/-- Among endomorphisms anticommuting with `J`, skew-adjointness for `ω` is self-adjointness for
the associated form `g = ω(·, J ·)`. No compatibility of `J` is needed. -/
theorem mem_compatibleTangentSpace_iff_isSelfAdjoint (hY : Y ∈ J.tangentSpace) :
    Y ∈ ω.compatibleTangentSpace J ↔ (ω.associatedBilinForm J).IsSelfAdjoint Y := by
  rw [AlmostComplexStructure.mem_tangentSpace_iff_apply] at hY
  rw [mem_compatibleTangentSpace, and_iff_right hY]
  -- `IsSelfAdjoint` unfolds to `IsAdjointPair`, which is stated pointwise by definition.
  change _ ↔ ∀ v w, ω (Y v) (J w) = ω v (J (Y w))
  beta_reduce
  constructor
  · intro h v w
    have := h v (J w)
    beta_reduce at this
    rw [hY, map_neg] at this
    linarith
  · intro h v w
    have := h v (-J w)
    beta_reduce at this
    simp only [map_neg, AlmostComplexStructure.apply_apply, neg_neg, hY] at this
    linarith

/-- For a complex structure `J` preserving `ω`, the endomorphism `J` itself is skew-adjoint
for `ω`. This is the form of invariance that is linear in `J`. -/
private theorem Invariant.apply_add_apply_eq_zero (hJ : ω.Invariant J) (v w : V) :
    ω (J v) w + ω v (J w) = 0 := by
  have := (ω.invariant_iff J).mp hJ v (J w)
  rw [AlmostComplexStructure.apply_apply] at this
  beta_reduce at this ⊢
  rw [map_neg] at this
  linarith

/-- For a compatible `J`, the variations in the compatible tangent space are, after composing with
`J`, the endomorphisms anticommuting with `J` and self-adjoint for `g = ω(·, J ·)`: these are the
coordinates of the compatible Cayley ball. -/
private theorem Compatible.mul_mem_tangentSpace_and_isSelfAdjoint (h : ω.Compatible J)
    (hY : Y ∈ ω.compatibleTangentSpace J) :
    J.toLinearMap * Y ∈ J.tangentSpace ∧
      (ω.associatedBilinForm J).IsSelfAdjoint (J.toLinearMap * Y) := by
  rw [mem_compatibleTangentSpace] at hY
  refine ⟨AlmostComplexStructure.mem_tangentSpace_iff_apply.2 fun v => ?_, fun v w => ?_⟩
  · simp [hY.1]
  · have h₁ := h.invariant_apply (Y v) w
    have h₂ := hY.2 v w
    simp only [associatedBilinForm_apply, mul_apply_eq_comp, AlmostComplexStructure.apply_apply]
    beta_reduce at h₁ h₂ ⊢
    rw [h₁, map_neg]
    linarith

/-- For `S` self-adjoint for `g = ω(·, J ·)`, the average `S + J S J` lies in the compatible
tangent space of a compatible `J`. -/
private theorem Compatible.add_mul_mul_mem_compatibleTangentSpace (h : ω.Compatible J)
    {S : Module.End ℝ V} (hS : (ω.associatedBilinForm J).IsSelfAdjoint S) :
    S + J.toLinearMap * S * J.toLinearMap ∈ ω.compatibleTangentSpace J := by
  have hT : S + J.toLinearMap * S * J.toLinearMap ∈ J.tangentSpace :=
    AlmostComplexStructure.mem_tangentSpace_iff_apply.2 fun v => by
      simp only [LinearMap.add_apply, mul_apply_eq_comp, AlmostComplexStructure.apply_apply,
        map_neg, map_add]
      abel
  refine (mem_compatibleTangentSpace_iff_isSelfAdjoint hT).2 fun v w => ?_
  have h₀ := hS v w
  have h₁ := hS (J v) (-J w)
  have h₂ := h.invariant_apply (S (J v)) w
  have h₃ := h.invariant_apply v (S (J w))
  simp only [associatedBilinForm_apply, LinearMap.add_apply, mul_apply_eq_comp,
    AlmostComplexStructure.apply_apply, map_neg, map_add] at h₀ h₁ ⊢
  beta_reduce at h₀ h₁ h₂ h₃ ⊢
  linarith

/-- **Variations of compatible structures reach every vector.** For an `ω`-compatible `J`, a
nonzero vector `ξ` and any vector `η`, some variation `Y` in the compatible tangent space at `J`
sends `ξ` to `η`. -/
theorem Compatible.exists_mem_compatibleTangentSpace_apply_eq (h : ω.Compatible J) {ξ : V}
    (hξ : ξ ≠ 0) (η : V) : ∃ Y ∈ ω.compatibleTangentSpace J, Y ξ = η := by
  set g := ω.associatedBilinForm J
  have ha : g ξ ξ ≠ 0 := (h.tames ξ hξ).ne'
  -- The rank-two `g`-self-adjoint map `v ↦ g(ξ, v) ζ + g(ζ, v) ξ`, averaged with `J`, sends `ξ`
  -- to `η` for this choice of `ζ`.
  set ζ : V := (g ξ ξ)⁻¹ •
    (η - (g η ξ / (2 * g ξ ξ)) • ξ - (g η (J ξ) / (2 * g ξ ξ)) • J ξ)
  set S : Module.End ℝ V := (g ξ).smulRight ζ + (g ζ).smulRight ξ
  have hS : g.IsSelfAdjoint S := fun v w => by
    simp only [S, LinearMap.add_apply, LinearMap.smulRight_apply, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [h.associatedBilinForm_isSymm.eq ζ w, h.associatedBilinForm_isSymm.eq ξ w,
      h.associatedBilinForm_isSymm.eq v ζ, h.associatedBilinForm_isSymm.eq v ξ]
    ring
  refine ⟨S + J.toLinearMap * S * J.toLinearMap,
    h.add_mul_mul_mem_compatibleTangentSpace hS, ?_⟩
  have hξJ : g ξ (J ξ) = 0 := by simp [g]
  have hJξ : g (J ξ) ξ = 0 := by rw [h.associatedBilinForm_isSymm.eq, hξJ]
  have hJJ : g (J ξ) (J ξ) = g ξ ξ := ω.associatedBilinForm_apply_apply_self_eq J ξ
  have hζξ : g ζ ξ = g η ξ / (2 * g ξ ξ) := by
    simp only [ζ, map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, hJξ,
      smul_eq_mul]
    field_simp
    ring
  have hζJξ : g ζ (J ξ) = g η (J ξ) / (2 * g ξ ξ) := by
    simp only [ζ, map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, hξJ, hJJ,
      smul_eq_mul]
    field_simp
    ring
  simp only [S, LinearMap.add_apply, mul_apply_eq_comp, LinearMap.smulRight_apply,
    map_smul, hξJ, hζξ, hζJξ, zero_smul, zero_add]
  simp only [ζ]
  match_scalars <;> field_simp <;> ring

end SymplecticForm

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

/-- A bounded analytic reparametrization of the line with unit velocity at `0`. -/
private theorem exists_contDiff_hasDerivAt_abs_le {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ⊤ φ ∧ φ 0 = 0 ∧ HasDerivAt φ 1 0 ∧ ∀ t, |φ t| ≤ ε := by
  refine ⟨fun t => ε * Real.sin (t / ε),
    contDiff_const.mul (Real.contDiff_sin.comp (contDiff_id.div_const ε)), by simp, ?_,
    fun t => ?_⟩
  · have := ((Real.hasDerivAt_sin (0 / ε)).comp 0 ((hasDerivAt_id 0).div_const ε)).const_mul ε
    simpa [hε.ne'] using this
  · rw [abs_mul, abs_of_pos hε]
    exact mul_le_of_le_one_right hε.le (Real.abs_sin_le_one _)

/-- The diagonal of the associated form of a tame structure is bounded below by a positive
multiple of the squared norm. -/
private theorem Tames.exists_pos_mul_norm_sq_le {J : AlmostComplexStructure V} (h : ω.Tames J) :
    ∃ c > 0, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J v) := by
  obtain ⟨c, hc, hcv⟩ := IsCompact.exists_pos_forall_mul_norm_sq_le (K := (Set.univ : Set Unit))
    isCompact_univ (b := fun _ => (ω.associatedBilinForm J).toContinuousBilinearMap)
    continuousOn_const fun _ _ v hv => by simpa using h v hv
  exact ⟨c, hc, fun v => by simpa using hcv () trivial v⟩

/-- Small multiples of a coordinate of the compatible Cayley ball of a compatible `J` lie in
that ball. -/
private theorem Compatible.exists_pos_smul_mem_compatibleCayleyBall
    {J : AlmostComplexStructure V} (h : ω.Compatible J) {C : Module.End ℝ V}
    (hC : C ∈ J.tangentSpace) (hCs : (ω.associatedBilinForm J).IsSelfAdjoint C) :
    ∃ ε > 0, ∀ s : ℝ, |s| ≤ ε → s • C ∈ ω.compatibleCayleyBall J := by
  -- `ω(v, J v)` is bounded below, and `ω(C v, J C v)` above, by multiples of `‖v‖²`.
  obtain ⟨c, hc, hcv⟩ := h.tames.exists_pos_mul_norm_sq_le
  set B := ((ω.associatedBilinForm J).compl₁₂ C C).toContinuousBilinearMap
  set M := ‖B‖
  have hM0 : 0 ≤ M := B.opNorm_nonneg
  have hM (v : V) : |B v v| ≤ M * ‖v‖ ^ 2 := by
    simpa [sq, mul_assoc, Real.norm_eq_abs] using B.le_opNorm₂ v v
  refine ⟨min 1 (c / (2 * (M + 1))), lt_min one_pos (by positivity), fun s hs => ?_⟩
  have hs1 : |s| ≤ 1 := hs.trans (min_le_left _ _)
  have hs2 : |s| * (2 * (M + 1)) ≤ c :=
    (le_div_iff₀ (by positivity)).1 (hs.trans (min_le_right _ _))
  have hsq : s ^ 2 * (M + 1) ≤ c / 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg s]
  refine mem_compatibleCayleyBall.2 ⟨mem_cayleyBall.2 ⟨?_, fun v hv => ?_⟩, fun v w => ?_⟩
  · rw [smul_mul_assoc, mul_smul_comm, ← smul_neg,
      eq_neg_of_add_eq_zero_left (AlmostComplexStructure.mem_tangentSpace.1 hC)]
  · have hv2 : 0 < ‖v‖ ^ 2 := by positivity
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    have h₁ := hcv v
    have h₂ := mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM v)) (sq_nonneg s)
    have h₃ : s ^ 2 * M * ‖v‖ ^ 2 ≤ c / 2 * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg s]) hv2.le
    simp only [B, LinearMap.toContinuousBilinearMap_apply, LinearMap.compl₁₂_apply,
      associatedBilinForm_apply] at h₂
    beta_reduce at h₁ h₂ ⊢
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
  obtain ⟨hCT, hCs⟩ := h.mul_mem_tangentSpace_and_isSelfAdjoint hY
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
    simp only [C]
    rw [neg_smul, mul_neg, mul_smul_comm, ← mul_assoc, hJJ, neg_one_mul, smul_neg, neg_neg]
  have hY' : deriv G 0 = Y := by
    rw [hJC, ← sub_eq_add_neg, sub_eq_iff_eq_add, ← add_smul] at heq
    rw [heq]
    norm_num
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
  obtain ⟨c, hc, hcv⟩ := h.exists_pos_mul_norm_sq_le
  -- The cross term and the quadratic term of the conjugated form are bounded by `‖w‖²`.
  set B₁ := (ω.toBilinForm.compl₁₂ Z.toLinearMap J.toLinearMap +
    ω.toBilinForm.compl₂ (Z.toLinearMap * J.toLinearMap)).toContinuousBilinearMap
  set B₂ := (ω.toBilinForm.compl₁₂ Z.toLinearMap
    (Z.toLinearMap * J.toLinearMap)).toContinuousBilinearMap
  set M₁ := ‖B₁‖
  set M₂ := ‖B₂‖
  have hM₁0 : 0 ≤ M₁ := B₁.opNorm_nonneg
  have hM₂0 : 0 ≤ M₂ := B₂.opNorm_nonneg
  have hM₁ (w : V) : |B₁ w w| ≤ M₁ * ‖w‖ ^ 2 := by
    simpa [sq, mul_assoc, Real.norm_eq_abs] using B₁.le_opNorm₂ w w
  have hM₂ (w : V) : |B₂ w w| ≤ M₂ * ‖w‖ ^ 2 := by
    simpa [sq, mul_assoc, Real.norm_eq_abs] using B₂.le_opNorm₂ w w
  set ε := min (min 1 (c / (2 * (M₁ + M₂ + 1)))) (1 / (2 * (‖Z‖ + 1)))
  have hε : 0 < ε := lt_min (lt_min one_pos (by positivity)) (by positivity)
  refine ⟨ε, hε, fun s hs => ⟨?_, fun w hw => ?_⟩⟩
  · have hsZ : |s| * (2 * (‖Z‖ + 1)) ≤ 1 :=
      (le_div_iff₀ (by positivity)).1 (hs.trans (min_le_right _ _))
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [norm_nonneg Z, abs_nonneg s]
  · have hs1 : |s| ≤ 1 := (hs.trans (min_le_left _ _)).trans (min_le_left _ _)
    have hs2 : |s| * (2 * (M₁ + M₂ + 1)) ≤ c :=
      (le_div_iff₀ (by positivity)).1 ((hs.trans (min_le_left _ _)).trans (min_le_right _ _))
    have hw2 : 0 < ‖w‖ ^ 2 := by positivity
    have hss : s ^ 2 ≤ |s| := by rw [← sq_abs]; nlinarith [abs_nonneg s]
    -- For small `s`, both terms are small compared with `c ‖w‖²`.
    have hA := mul_le_mul_of_nonneg_left (hM₁ w) (abs_nonneg s)
    have hB := mul_le_mul_of_nonneg_left (hM₂ w) (sq_nonneg s)
    rw [← abs_mul] at hA
    rw [← abs_of_nonneg (sq_nonneg s), ← abs_mul, abs_of_nonneg (sq_nonneg s)] at hB
    have hA' := (abs_le.1 hA).1
    have hB' := (abs_le.1 hB).1
    have hc' := mul_le_mul_of_nonneg_right hs2 hw2.le
    have h₀ := hcv w
    simp only [B₁, B₂, LinearMap.toContinuousBilinearMap_apply, LinearMap.add_apply,
      LinearMap.compl₁₂_apply, LinearMap.compl₂_apply, ContinuousLinearMap.coe_coe,
      mul_apply_eq_comp] at hA' hB'
    simp only [add_apply, one_apply_eq_self, smul_apply, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
    beta_reduce at h₀ ⊢
    nlinarith [mul_nonneg hM₁0 hw2.le, mul_nonneg hM₂0 hw2.le, abs_nonneg s,
      mul_le_mul_of_nonneg_right hss (mul_nonneg hM₂0 hw2.le)]

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
  have hKK (t : ℝ) : K t * K t = -1 := by
    obtain ⟨u, hu⟩ := hPu t
    simp only [K, ← hu, Ring.inverse_unit]
    calc (u : V →L[ℝ] V) * Jc * ↑u⁻¹ * (↑u * Jc * ↑u⁻¹) = ↑u * (Jc * Jc) * ↑u⁻¹ := by
          simp only [mul_assoc, Units.inv_mul_cancel_left]
      _ = -1 := by rw [hJJ, mul_neg_one, neg_mul, Units.mul_inv]
  set c : ℝ → AlmostComplexStructure V := fun t =>
    ⟨(K t).toLinearMap, by
      ext v
      simpa using congrArg (fun A : V →L[ℝ] V => A v) (hKK t)⟩
  have hcK : (fun t => LinearMap.toContinuousLinearMap (c t).toLinearMap) = K := by
    funext t
    ext v
    rfl
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
      have h1 : ((u : V →L[ℝ] V) * ↑u⁻¹) v = v := by rw [Units.mul_inv]; rfl
      rw [← hu]
      exact h1.symm
    have hw : w ≠ 0 := by
      rintro hw0
      exact hv (by rw [hvw, hw0, map_zero])
    have hKv : K t v = P t (J w) := by
      simp only [K, ← hu, Ring.inverse_unit, mul_apply_eq_comp, w]
      rfl
    have hcv : c t v = K t v := rfl
    rw [hcv, hKv, hvw]
    exact (hsmall _ (hφ t)).2 w hw
  · ext v
    simp [c, hK0, Jc]
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
    simp only [Z]
    rw [smul_mul_assoc, mul_assoc, hJJ, mul_neg_one, smul_neg, neg_smul, neg_neg]
  have hJZ : Jc * Z = -((1 / 2 : ℝ) • Y) := by
    simp only [Z]
    rw [mul_smul_comm, ← mul_assoc, hYJ, neg_mul, mul_assoc, hJJ, mul_neg_one, neg_neg, neg_smul]
  rw [hP0, hK0, mul_one, mul_zero, add_zero, hZJ, hJZ, ← sub_eq_add_neg, sub_eq_iff_eq_add,
    ← add_smul] at heq
  rw [heq] at hK
  norm_num at hK
  exact hK

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

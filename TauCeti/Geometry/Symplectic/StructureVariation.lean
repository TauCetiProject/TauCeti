/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Analysis.SpecialFunctions.Exponential
public import TauCeti.Analysis.SpecialFunctions.Exponential.BilinForm
public import TauCeti.Analysis.Normed.Operator.Exponential
public import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# Infinitesimal variations of tame and compatible almost complex structures

Let `J` be a linear complex structure on a finite-dimensional real vector space `V` with
symplectic form `ω`. Differentiating `J² = -1` shows that the velocity `Y` of any differentiable
family of complex structures through `J` is `J`-antilinear: `J Y + Y J = 0`. These endomorphisms
form the submodule `TauCeti.AlmostComplexStructure.tangent`. A complex structure preserves `ω`
exactly when it is skew-adjoint for `ω`, so if every structure of the family preserves `ω`, then
`Y` is skew-adjoint for `ω` as well: `ω(Y v, w) + ω(v, Y w) = 0`. The antilinear and
infinitesimally symplectic endomorphisms form the submodule
`TauCeti.SymplecticForm.compatibleTangent`, both defined in
`TauCeti.Geometry.Symplectic.AlmostComplex`.

Both conditions are also sufficient, and they are distinct. For an antilinear `Y` put
`B = ½ J Y`. Then `t ↦ exp(t B) J exp(-t B)` is a smooth path of complex structures through `J`
with velocity `Y` (`TauCeti.AlmostComplexStructure.tangentPath`). If `J` is `ω`-compatible and
`Y` satisfies the compatible tangent condition, then `B` is infinitesimally symplectic, so every
`exp(t B)` is a linear symplectomorphism and the whole path consists of `ω`-compatible
structures. Tameness is an open condition
(`TauCeti.SymplecticForm.Tames.eventually_of_continuousAt`), so for a tame `J` and any antilinear
`Y` the path is `ω`-tame for small `t`. Thus:

* the variations of an `ω`-tame structure through tame structures are exactly the `J`-antilinear
  endomorphisms (`TauCeti.SymplecticForm.Tames.mem_tangent_iff_exists`);
* the variations of an `ω`-compatible structure through compatible structures are exactly the
  antilinear endomorphisms that are skew-adjoint for `ω`
  (`TauCeti.SymplecticForm.Compatible.mem_compatibleTangent_iff_exists`).

These are the pointwise tangent conditions on the variations `δJ` of domain-dependent almost
complex structures used in transversality arguments for Floer and pseudoholomorphic curve
equations. The path depends smoothly on `J`, `Y` and the time parameter jointly
(`TauCeti.AlmostComplexStructure.contMDiffAt_tangentPath`), so a smooth family of structures and
a smooth family of tangent vectors over a manifold of parameters give a smooth family of
variations.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.2 (the tangent space of the space of compatible
  almost complex structures).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.5.
-/

public section

noncomputable section

open NormedSpace Filter Topology Metric Manifold

namespace TauCeti

variable {V : Type*}

section Normed

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

namespace AlmostComplexStructure

/-- In the operator-norm algebra, an almost complex structure squares to `-1`. -/
@[simp]
theorem toContinuousLinearMap_mul_self (J : AlmostComplexStructure V) :
    LinearMap.toContinuousLinearMap J.toLinearMap * LinearMap.toContinuousLinearMap J.toLinearMap =
      -1 := by
  ext v
  simp

/-- The velocity of a differentiable family of complex structures is antilinear: differentiate
`J(t)² = -1`. -/
theorem mem_tangent_of_hasDerivAt {J : ℝ → AlmostComplexStructure V} {Y : V →L[ℝ] V} {t : ℝ}
    (hJ : HasDerivAt (fun s => LinearMap.toContinuousLinearMap (J s).toLinearMap) Y t) :
    Y.toLinearMap ∈ (J t).tangent := by
  have hd : HasDerivAt (fun _ : ℝ => (-1 : V →L[ℝ] V))
      (Y * LinearMap.toContinuousLinearMap (J t).toLinearMap +
        LinearMap.toContinuousLinearMap (J t).toLinearMap * Y) t :=
    (hJ.mul hJ).congr_of_eventuallyEq
      (Eventually.of_forall fun s => ((J s).toContinuousLinearMap_mul_self).symm)
  rw [mem_tangent, add_comm]
  exact congrArg ContinuousLinearMap.toLinearMap (hd.unique (hasDerivAt_const t _))

end AlmostComplexStructure

namespace SymplecticForm

/-- The velocity of a differentiable family of complex structures that all preserve `ω` near
`t` satisfies the compatible tangent condition. A complex structure `J` preserves `ω` exactly when
it is infinitesimally symplectic, `ω(J v, w) + ω(v, J w) = 0`; differentiate this identity. -/
theorem mem_compatibleTangent_of_hasDerivAt {ω : SymplecticForm V}
    {J : ℝ → AlmostComplexStructure V} {Y : V →L[ℝ] V} {t : ℝ}
    (hω : ∀ᶠ s in 𝓝 t, ω.Invariant (J s))
    (hJ : HasDerivAt (fun s => LinearMap.toContinuousLinearMap (J s).toLinearMap) Y t) :
    Y.toLinearMap ∈ ω.compatibleTangent (J t) := by
  refine mem_compatibleTangent.2 ⟨AlmostComplexStructure.mem_tangent_of_hasDerivAt hJ,
    fun v w => ?_⟩
  let φ : (V →L[ℝ] V) →ₗ[ℝ] ℝ :=
    { toFun := fun A => ω (A v) w + ω v (A w)
      map_add' := fun A B => by
        simp only [FunLike.coe_add, Pi.add_apply, map_add, LinearMap.add_apply]
        ring
      map_smul' := fun c A => by
        simp only [FunLike.coe_smul, Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }
  have hd : HasDerivAt (fun s => φ (LinearMap.toContinuousLinearMap (J s).toLinearMap)) (φ Y) t :=
    (LinearMap.toContinuousLinearMap φ).hasFDerivAt.comp_hasDerivAt t hJ
  have hz : (fun s => φ (LinearMap.toContinuousLinearMap (J s).toLinearMap)) =ᶠ[𝓝 t]
      fun _ => 0 := by
    filter_upwards [hω] with s hs
    have := (J s).bilinForm_apply_left_eq_neg_apply_right ((ω.invariant_iff _).1 hs) v w
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_toContinuousLinearMap']
    exact add_eq_zero_iff_eq_neg.2 this
  have h0 := hd.unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hz)
  simp only [φ, LinearMap.coe_mk, AddHom.coe_mk] at h0
  simp only [ContinuousLinearMap.coe_coe, Pi.neg_apply, map_neg]
  exact eq_neg_of_add_eq_zero_left h0

/-- Tameness is an open condition: if a family of complex structures is continuous at `x` in
the operator-norm topology and `ω`-tame there, it is `ω`-tame near `x`. -/
theorem Tames.eventually_of_continuousAt {X : Type*} [TopologicalSpace X] {ω : SymplecticForm V}
    {J : X → AlmostComplexStructure V} {x : X}
    (hJ : ContinuousAt (fun y => LinearMap.toContinuousLinearMap (J y).toLinearMap) x)
    (h : ω.Tames (J x)) : ∀ᶠ y in 𝓝 x, ω.Tames (J y) := by
  let ωc := ω.toBilinForm.toContinuousBilinearMap
  have hωc (v w : V) : ωc v w = ω v w := LinearMap.toContinuousBilinearMap_apply _ _ _
  have hq : Continuous fun p : (V →L[ℝ] V) × V => ωc p.2 (p.1 p.2) := by fun_prop
  set A₀ := LinearMap.toContinuousLinearMap (J x).toLinearMap
  have hK : ∀ᶠ A in 𝓝 A₀, ∀ v ∈ sphere (0 : V) 1, 0 < ωc v (A v) := by
    refine (isCompact_sphere (0 : V) 1).eventually_forall_of_forall_eventually fun v hv => ?_
    have hv0 : v ≠ 0 := ne_zero_of_mem_unit_sphere ⟨v, hv⟩
    exact hq.continuousAt.eventually (Ioi_mem_nhds (by simpa [hωc, A₀] using h v hv0))
  filter_upwards [hJ.eventually hK] with y hy v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hu : ‖v‖⁻¹ • v ∈ sphere (0 : V) 1 := by
    simp [norm_smul, inv_mul_cancel₀ hn.ne']
  have hy' : 0 < ω (‖v‖⁻¹ • v) (J y (‖v‖⁻¹ • v)) := hy _ hu
  have key : ω (‖v‖⁻¹ • v) (J y (‖v‖⁻¹ • v)) = (‖v‖⁻¹ * ‖v‖⁻¹) * ω v (J y v) := by
    dsimp only
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  exact pos_of_mul_pos_right (key ▸ hy') (by positivity)

end SymplecticForm

attribute [local instance] TauCeti.normedAlgebraRatOfReal

namespace AlmostComplexStructure

/-- The complex structure `exp(B) J exp(-B)`: the transport of `J` along the linear automorphism
`exp B` of `V`. -/
def expConj (J : AlmostComplexStructure V) (B : V →L[ℝ] V) :
    AlmostComplexStructure V :=
  J.transport B.expEquiv.toLinearEquiv

@[simp]
theorem expConj_toLinearMap (J : AlmostComplexStructure V) (B : V →L[ℝ] V) :
    (J.expConj B).toLinearMap =
      (exp B * LinearMap.toContinuousLinearMap J.toLinearMap * exp (-B)).toLinearMap :=
  LinearMap.ext fun v => by simp [expConj, mul_apply_eq_comp]

theorem expConj_apply (J : AlmostComplexStructure V) (B : V →L[ℝ] V) (v : V) :
    J.expConj B v = exp B (J (exp (-B) v)) := by
  simp [expConj]

@[simp]
theorem expConj_zero (J : AlmostComplexStructure V) : J.expConj 0 = J := by
  apply toLinearMap_injective
  simp [expConj_toLinearMap]

/-- The path `t ↦ exp(t B) J exp(-t B)` with `B = ½ J Y`. When `Y` is `J`-antilinear it is a
smooth path of complex structures through `J` with velocity `Y`
(`TauCeti.AlmostComplexStructure.hasDerivAt_tangentPath`). -/
def tangentPath (J : AlmostComplexStructure V) (Y : V →L[ℝ] V) (t : ℝ) :
    AlmostComplexStructure V :=
  J.expConj (t • (2⁻¹ : ℝ) • (LinearMap.toContinuousLinearMap J.toLinearMap * Y))

/-- In operator-norm coordinates the tangent path is `exp(t B) J exp(-t B)` with `B = ½ J Y`. -/
theorem toContinuousLinearMap_tangentPath (J : AlmostComplexStructure V) (Y : V →L[ℝ] V)
    (t : ℝ) :
    LinearMap.toContinuousLinearMap (J.tangentPath Y t).toLinearMap =
      exp (t • (2⁻¹ : ℝ) • (LinearMap.toContinuousLinearMap J.toLinearMap * Y)) *
        LinearMap.toContinuousLinearMap J.toLinearMap *
        exp (-(t • (2⁻¹ : ℝ) • (LinearMap.toContinuousLinearMap J.toLinearMap * Y))) :=
  ContinuousLinearMap.ext fun v => by simp only [tangentPath, LinearMap.coe_toContinuousLinearMap',
    expConj_apply, mul_apply_eq_comp]

@[simp]
theorem tangentPath_zero (J : AlmostComplexStructure V) (Y : V →L[ℝ] V) :
    J.tangentPath Y 0 = J := by
  simp [tangentPath]

/-- The path `TauCeti.AlmostComplexStructure.tangentPath` has velocity `Y` at `t = 0` whenever
`Y` is `J`-antilinear. -/
theorem hasDerivAt_tangentPath {J : AlmostComplexStructure V} {Y : V →L[ℝ] V}
    (hY : Y.toLinearMap ∈ J.tangent) :
    HasDerivAt (fun t => LinearMap.toContinuousLinearMap (J.tangentPath Y t).toLinearMap) Y 0 := by
  set j := LinearMap.toContinuousLinearMap J.toLinearMap
  set B : V →L[ℝ] V := (2⁻¹ : ℝ) • (j * Y)
  have hjj : j * j = -1 := J.toContinuousLinearMap_mul_self
  have hjY : j * Y = -(Y * j) :=
    ContinuousLinearMap.coe_injective (mul_eq_neg_mul_of_mem_tangent hY)
  have hd := hasDerivAt_exp_mul_const_mul_exp_neg B j
  have hBj : B * j - j * B = Y := by
    have h1 : j * Y * j = Y := by rw [hjY, neg_mul, mul_assoc, hjj, mul_neg_one, neg_neg]
    have h2 : j * (j * Y) = -Y := by rw [← mul_assoc, hjj, neg_one_mul]
    simp only [B, smul_mul_assoc, mul_smul_comm, h1, h2, smul_neg, sub_neg_eq_add]
    rw [← add_smul]
    norm_num
  rw [hBj] at hd
  refine hd.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [toContinuousLinearMap_tangentPath, smul_neg]

end AlmostComplexStructure

namespace AlmostComplexStructure

/-- The tangent path is smooth in time, structure and tangent vector jointly: for families
`J`, `Y` and times `τ` that are `C^n` at a point `p` of a manifold, so is the family of
structures `(J p).tangentPath (Y p) (τ p)`. -/
theorem contMDiffAt_tangentPath {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]
    {J : N → AlmostComplexStructure V} {Y : N → V →L[ℝ] V} {τ : N → ℝ} {n : WithTop ℕ∞} {p : N}
    (hJ : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n
      (fun y => LinearMap.toContinuousLinearMap (J y).toLinearMap) p)
    (hY : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n Y p) (hτ : ContMDiffAt I 𝓘(ℝ) n τ p) :
    ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n
      (fun y => LinearMap.toContinuousLinearMap ((J y).tangentPath (Y y) (τ y)).toLinearMap)
      p := by
  -- In operator-norm coordinates the path is a smooth expression in `(τ, J, Y)`.
  have hF : ContDiff ℝ n fun q : ℝ × (V →L[ℝ] V) × (V →L[ℝ] V) =>
      exp (q.1 • (2⁻¹ : ℝ) • (q.2.1 * q.2.2)) * q.2.1 *
        exp (-(q.1 • (2⁻¹ : ℝ) • (q.2.1 * q.2.2))) := by
    have hexp : ContDiff ℝ n (exp : (V →L[ℝ] V) → V →L[ℝ] V) :=
      contDiff_iff_contDiffAt.2 fun x => (exp_analytic (𝕂 := ℝ) x).contDiffAt
    have hB : ContDiff ℝ n fun q : ℝ × (V →L[ℝ] V) × (V →L[ℝ] V) =>
        q.1 • (2⁻¹ : ℝ) • (q.2.1 * q.2.2) := by
      fun_prop
    exact ((hexp.comp hB).mul (contDiff_fst.comp contDiff_snd)).mul (hexp.comp hB.neg)
  have h := hF.contDiffAt.comp_contMDiffAt (hτ.prodMk_space (hJ.prodMk_space hY))
  simp only [Function.comp_def] at h
  simpa only [toContinuousLinearMap_tangentPath] using h

/-- The tangent path is smooth in time. -/
theorem contDiff_tangentPath (J : AlmostComplexStructure V) (Y : V →L[ℝ] V) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun t => LinearMap.toContinuousLinearMap (J.tangentPath Y t).toLinearMap :=
  contMDiff_iff_contDiff.1 fun _ =>
    contMDiffAt_tangentPath (J := fun _ => J) (Y := fun _ => Y) contMDiffAt_const
      contMDiffAt_const contMDiffAt_id

end AlmostComplexStructure

namespace SymplecticForm

variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- The exponential of an infinitesimally symplectic endomorphism is a linear
symplectomorphism. -/
theorem isSymplectomorphism_expEquiv {B : V →L[ℝ] V} (hB : ω.toBilinForm.IsSkewAdjoint B) :
    IsSymplectomorphism ω ω B.expEquiv.toLinearEquiv :=
  isSymplectomorphism_iff.2 fun v w => by simpa using hB.apply_exp_apply_exp v w

/-- Conjugating an `ω`-compatible structure by the exponential of an infinitesimally symplectic
endomorphism gives an `ω`-compatible structure. -/
theorem Compatible.expConj (hJ : ω.Compatible J) {B : V →L[ℝ] V}
    (hB : ω.toBilinForm.IsSkewAdjoint B) : ω.Compatible (J.expConj B) := by
  have h := hJ.transport B.expEquiv.toLinearEquiv
  rwa [isSymplectomorphism_iff_transport_eq.1 (isSymplectomorphism_expEquiv hB)] at h

/-- The tangent path of an `ω`-compatible structure in a direction satisfying the compatible
tangent condition consists of `ω`-compatible structures. -/
theorem Compatible.tangentPath (hJ : ω.Compatible J) {Y : V →L[ℝ] V}
    (hY : Y.toLinearMap ∈ ω.compatibleTangent J) (t : ℝ) :
    ω.Compatible (J.tangentPath Y t) := by
  refine hJ.expConj ((LinearMap.mem_skewAdjointSubmodule _).1 ?_)
  rw [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.toLinearMap_mul, LinearMap.coe_toContinuousLinearMap]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    ((LinearMap.mem_skewAdjointSubmodule _).2
      (hJ.invariant.isSkewAdjoint_mul_of_mem_compatibleTangent hY)))

/-- The tangent path of an `ω`-tame structure is `ω`-tame for small times, in every direction. -/
theorem Tames.eventually_tangentPath (hJ : ω.Tames J) (Y : V →L[ℝ] V) :
    ∀ᶠ t in 𝓝 0, ω.Tames (J.tangentPath Y t) :=
  Tames.eventually_of_continuousAt ((J.contDiff_tangentPath Y (n := 0)).continuous.continuousAt)
    (by simpa using hJ)

/-- **The tame tangent condition.** The velocities at `J` of smooth paths of complex structures
through an `ω`-tame `J`, tame for small times, are exactly the `J`-antilinear endomorphisms. -/
theorem Tames.mem_tangent_iff_exists (hJ : ω.Tames J) {Y : V →L[ℝ] V} :
    Y.toLinearMap ∈ J.tangent ↔ ∃ J' : ℝ → AlmostComplexStructure V, J' 0 = J ∧
      (∀ᶠ t in 𝓝 0, ω.Tames (J' t)) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun t => LinearMap.toContinuousLinearMap (J' t).toLinearMap) ∧
      HasDerivAt (fun t => LinearMap.toContinuousLinearMap (J' t).toLinearMap) Y 0 := by
  refine ⟨fun hY => ⟨J.tangentPath Y, J.tangentPath_zero Y, hJ.eventually_tangentPath Y,
    J.contDiff_tangentPath Y, AlmostComplexStructure.hasDerivAt_tangentPath hY⟩, ?_⟩
  rintro ⟨J', rfl, -, -, hd⟩
  exact AlmostComplexStructure.mem_tangent_of_hasDerivAt hd

/-- **The compatible tangent condition.** The velocities at `J` of smooth paths of
`ω`-compatible structures through an `ω`-compatible `J` are exactly the elements of
`TauCeti.SymplecticForm.compatibleTangent`: the `J`-antilinear endomorphisms that are
infinitesimally symplectic. -/
theorem Compatible.mem_compatibleTangent_iff_exists (hJ : ω.Compatible J) {Y : V →L[ℝ] V} :
    Y.toLinearMap ∈ ω.compatibleTangent J ↔ ∃ J' : ℝ → AlmostComplexStructure V, J' 0 = J ∧
      (∀ t, ω.Compatible (J' t)) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun t => LinearMap.toContinuousLinearMap (J' t).toLinearMap) ∧
      HasDerivAt (fun t => LinearMap.toContinuousLinearMap (J' t).toLinearMap) Y 0 := by
  refine ⟨fun hY => ⟨J.tangentPath Y, J.tangentPath_zero Y, hJ.tangentPath hY,
    J.contDiff_tangentPath Y,
    AlmostComplexStructure.hasDerivAt_tangentPath (mem_compatibleTangent.1 hY).1⟩, ?_⟩
  rintro ⟨J', rfl, hc, -, hd⟩
  exact mem_compatibleTangent_of_hasDerivAt (Eventually.of_forall fun t => (hc t).invariant) hd

end SymplecticForm

end Normed

end TauCeti

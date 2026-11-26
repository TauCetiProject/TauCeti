/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Coordinates
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Rotation
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Naturality
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace
public import TauCeti.Geometry.Symplectic.Manifold.Opens
import Mathlib.Analysis.Complex.Isometry

/-!
# The reduced spaces of planar central forces

Identify the configuration plane with `ℂ`, so that the phase space of a planar particle kept away
from the centre of force is the punctured phase space `M = {(q, p) ∈ ℂ × ℂ | q ≠ 0}`
(`TauCeti.puncturedPhaseSpace ℂ`) with the restriction `σ` of the standard symplectic form
`ω₀ = dq₁ ∧ dp₁ + dq₂ ∧ dp₂`. The circle acts on it by rotating positions and momenta, and this
action is Hamiltonian with moment map `μ(x) = L(x) ψ₀`, where `L = q₁ p₂ - q₂ p₁` is the angular
momentum and `ψ₀(ξ) = Im (ι_* ξ)` for the inclusion `ι : Circle → ℂ`
(`TauCeti.hamiltonianTorusData_angularMomentum_puncturedPhaseSpace`). This file computes its
Marsden–Weinstein–Meyer reduced spaces.

The rotations act freely and properly on `M` (`TauCeti.stabilizer_circle_puncturedPhaseSpace`),
so every value of `μ` is regular
(`TauCeti.differential_surjective_angularMomentum_puncturedPhaseSpace`), and the level of
`ℓ ψ₀` is the level `L = ℓ` of the angular momentum
(`TauCeti.mem_levelSubMulAction_angularMomentum_iff`). For every real `ℓ`, including `ℓ = 0`,
the reduced space `μ⁻¹(ℓ ψ₀) / S¹` of the Marsden–Weinstein–Meyer theorem is the cotangent bundle
`T*(0, ∞) = (0, ∞) × ℝ` of the radial half-line (`TauCeti.radialPhaseSpace`), with coordinates
`(r, p_r)` and symplectic form `dr ∧ dp_r`:

* the orbit of a state `(q, p)` of angular momentum `ℓ` is sent to its radius and radial momentum
  `(‖q‖, ⟪q, p⟫ / ‖q‖)` (`TauCeti.radialProjection`) by a diffeomorphism
  (`TauCeti.angularMomentumReducedSpaceDiffeomorph`,
  `TauCeti.coe_angularMomentumReducedSpaceDiffeomorph_mk`);
* this diffeomorphism pulls `dr ∧ dp_r` back to the reduced symplectic form
  (`TauCeti.mpullback_angularMomentumReducedSpaceDiffeomorph`);
* a central-force Hamiltonian `H = ‖p‖² / (2m) + U(‖q‖)` descends to the reduced Hamiltonian
  `H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)`, with the effective potential
  `U_ℓ(r) = ℓ² / (2 m r²) + U(r)`
  (`TauCeti.centralForceHamiltonian_effectivePotential_angularMomentumReducedSpaceDiffeomorph_mk`).

The diffeomorphism is obtained from the recognition of reduced spaces
(`TauCeti.SmoothTwoForm.exists_diffeomorph_comp_eq_and_mpullback_eq`). Its two inputs are proved
here.

* **The fibres.** Two states with the same radius, radial momentum and angular momentum differ by
  a rotation, and conversely (`TauCeti.exists_circle_smul_eq_iff`): `conj q * p` has real part
  `⟪q, p⟫` and imaginary part `L`, so the rotation by `q / q'` carries `(q', p')` to `(q, p)`.
* **The forms.** Along any smooth map `f` into the punctured phase space of an inner product
  plane on which the angular momentum is constant, `f^* ω₀ = (r, p_r)^* (dr ∧ dp_r)`
  (`TauCeti.mpullback_stdSymplecticForm_of_angularMomentum_eq`). In the global polar canonical
  coordinates `(r, p_r, θ, L)` of `TauCeti.polarCanonicalDiffeomorph`, the standard form is
  `dr ∧ dp_r + dθ ∧ dL`, and `dL` pulls back to zero.

The statements take as arguments the data `h`, `hreg`, `hn` and `d` from which the
Marsden–Weinstein–Meyer theorem builds the atlases of the level and of the reduced space; `h` and
`hreg` hold by `TauCeti.hamiltonianTorusData_angularMomentum_puncturedPhaseSpace` and
`TauCeti.differential_surjective_angularMomentum_puncturedPhaseSpace`.

## Main definitions

* `TauCeti.radialPhaseSpace`: the phase space `(0, ∞) × ℝ` of the radial motion.
* `TauCeti.angularMomentumReducedSpaceDiffeomorph`: the diffeomorphism from the reduced space at
  angular momentum `ℓ` onto `(0, ∞) × ℝ`.

## Main results

* `TauCeti.mpullback_stdSymplecticForm_of_angularMomentum_eq`: on a level of the angular momentum,
  the standard symplectic form is `dr ∧ dp_r`.
* `TauCeti.exists_circle_smul_eq_iff`: the rotation orbits are the common levels of the radius,
  the radial momentum and the angular momentum.
* `TauCeti.mpullback_angularMomentumReducedSpaceDiffeomorph`: the reduced space at angular
  momentum `ℓ` is symplectomorphic to `(T*(0, ∞), dr ∧ dp_r)`.
* `TauCeti.centralForceHamiltonian_effectivePotential_angularMomentumReducedSpaceDiffeomorph_mk`:
  the reduced Hamiltonian is `p_r² / (2m) + U_ℓ(r)`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8 (the reduction of a central field to the radial
  motion in the effective potential).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Chapter 1.7 and Chapter 11 (the rotational momentum map and the
  reduction of planar central-force problems).
-/

public section

noncomputable section

open Complex Function Module Real
open scoped Manifold InnerProductSpace ComplexConjugate ContDiff

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-! ### The standard form on a level of the angular momentum -/

section Plane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The radial projection `(q, p) ↦ (‖q‖, ⟪q, p⟫ / ‖q‖)` is smooth on the punctured phase space
`{(q, p) | q ≠ 0}`. -/
theorem contMDiff_radialProjection_comp_subtypeVal :
    ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ, ℝ × ℝ) ∞
      (radialProjection ∘ Subtype.val : puncturedPhaseSpace V → ℝ × ℝ) := by
  intro x
  have hq : (x : V × V).1 ≠ 0 := mem_puncturedPhaseSpace.1 x.property
  have hn : ContDiffAt ℝ ∞ (fun y : V × V ↦ ‖y.1‖) (x : V × V) :=
    (contDiffAt_norm ℝ hq).comp _ contDiffAt_fst
  have hr : ContDiffAt ℝ ∞ radialProjection (x : V × V) := by
    rw [show radialProjection = fun y : V × V ↦ (‖y.1‖, ⟪y.1, y.2⟫_ℝ / ‖y.1‖) from
      funext fun y ↦ radialProjection_apply y.1 y.2]
    exact hn.prodMk ((contDiffAt_fst.inner ℝ contDiffAt_snd).div hn (norm_ne_zero_iff.2 hq))
  exact hr.contMDiffAt.comp x contMDiff_subtypeVal.contMDiffAt

variable [FiniteDimensional ℝ V] (b : OrthonormalBasis (Fin 2) ℝ V)

/-- **On a level of the angular momentum, the standard form is `dr ∧ dp_r`.** Let `b` be an
orthonormal basis of a plane `V` and `f` a smooth map into the punctured phase space
`{(q, p) | q ≠ 0}` along which the angular momentum `q₁ p₂ - q₂ p₁` in the basis `b` is constant.
Then `f` pulls the standard symplectic form `ω₀ = Σ dqᵢ ∧ dpᵢ` back to the pullback of the area
form `dr ∧ dp_r` of `ℝ × ℝ` along the radius and radial momentum `(‖q‖, ⟪q, p⟫ / ‖q‖)` of `f`. -/
theorem mpullback_stdSymplecticForm_of_angularMomentum_eq {EZ HZ Z : Type*}
    [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
    {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold IZ ∞ Z]
    {f : Z → puncturedPhaseSpace V} (hf : ContMDiff IZ 𝓘(ℝ, V × V) ∞ f) {ℓ : ℝ}
    (hℓ : ∀ z, angularMomentum (b 0) (b 1) (f z : V × V) = ℓ) :
    SmoothForm.mpullback f hf (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V)
        contMDiff_subtypeVal (SymplecticForm.constSmooth (stdSymplecticForm (V := V)))) =
      SmoothForm.mpullback ((radialProjection ∘ Subtype.val) ∘ f)
        (contMDiff_radialProjection_comp_subtypeVal.comp hf)
        (SymplecticForm.constSmooth (stdSymplecticForm (V := ℝ))) := by
  set φ := polarCanonicalDiffeomorph b
  have hG : ContMDiff IZ (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) ∞ (Subtype.val ∘ φ.symm ∘ f) :=
    contMDiff_subtypeVal.comp (φ.symm.contMDiff.comp hf)
  -- In polar canonical coordinates, `ω₀ = dr ∧ dp_r + dθ ∧ dL`.
  rw [← SmoothForm.mpullback_symm_eq_of_mpullback_eq (mpullback_polarCanonicalDiffeomorph b),
    SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback, SmoothTwoForm.prod_def,
    map_add, SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]
  rw [SmoothForm.mpullback_wedge (k := 1) (l := 1) _ (contMDiff_snd.comp hG)]
  -- The coordinate `L` is constant along `f`, so `dL` pulls back to zero.
  have hL : SmoothForm.mpullback _ (contMDiff_snd.comp hG)
      (SmoothForm.mpullback Prod.snd contMDiff_snd SmoothForm.realLineCoordForm) = 0 := by
    rw [SmoothForm.mpullback_mpullback,
      SmoothForm.mpullback_congr (g := fun _ ↦ ℓ) _ contMDiff_const (funext fun z ↦ by
        simp only [comp_apply, φ, coe_polarCanonicalDiffeomorph_symm_apply, hℓ])]
    exact Subtype.ext (by
      rw [SmoothForm.coe_mpullback, TauCeti.mpullback_const one_ne_zero, ZeroMemClass.coe_zero])
  rw [hL, map_zero, add_zero]
  -- The coordinates `(r, p_r)` are the radial projection.
  refine SmoothForm.mpullback_congr _ _ (funext fun z ↦ ?_) _
  simp only [comp_apply, coe_polarCanonicalDiffeomorph_symm_apply]
  exact (Prod.ext (radialProjection_fst _) (radialProjection_snd _)).symm

end Plane

/-! ### The rotations of the punctured planar phase space -/

local notation "𝕄" => puncturedPhaseSpace ℂ

/-- The rotations act properly on the punctured planar phase space, as the circle is compact. -/
instance : ProperSMul Circle 𝕄 :=
  haveI : ContinuousSMul Circle 𝕄 :=
    ⟨(continuous_fst.smul (continuous_subtypeVal.comp continuous_snd)).subtype_mk _⟩
  properSMul_of_compactSpace _ _

/-- The rotations act freely on the punctured planar phase space: a rotation fixing a state of
nonzero position is the identity. -/
theorem stabilizer_circle_puncturedPhaseSpace (x : 𝕄) : MulAction.stabilizer Circle x = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz ↦ ?_
  have h : (z : ℂ) * (x : ℂ × ℂ).1 = (x : ℂ × ℂ).1 :=
    congrArg (fun y : 𝕄 ↦ (y : ℂ × ℂ).1) (MulAction.mem_stabilizer_iff.1 hz)
  exact Circle.coe_inj.1 (mul_right_cancel₀ (mem_puncturedPhaseSpace.1 x.property)
    (h.trans (one_mul _).symm))

/-- Rotations preserve the radius and the radial momentum. -/
@[simp]
theorem radialProjection_circle_smul (g : Circle) (x : ℂ × ℂ) :
    radialProjection (g • x) = radialProjection x := by
  obtain ⟨q, p⟩ := x
  have hq : ‖(g : ℂ) * q‖ = ‖q‖ := by simp
  have hqp : ⟪(g : ℂ) * q, (g : ℂ) * p⟫_ℝ = ⟪q, p⟫_ℝ := by
    simpa [rotation_apply] using (rotation g).inner_map_map q p
  simp only [Circle.smul_def, Prod.smul_mk, smul_eq_mul, radialProjection_apply, hq, hqp]

/-- **The rotation orbits are the common levels of `(r, p_r, L)`.** Two states of the punctured
planar phase space differ by a rotation exactly when they have the same radius, radial momentum
and angular momentum. -/
theorem exists_circle_smul_eq_iff {x x' : 𝕄} :
    (∃ g : Circle, g • x' = x) ↔
      radialProjection (x : ℂ × ℂ) = radialProjection (x' : ℂ × ℂ) ∧
        angularMomentum 1 I (x : ℂ × ℂ) = angularMomentum 1 I (x' : ℂ × ℂ) := by
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun ⟨hr, hL⟩ ↦ ?_⟩
  · rw [← hg, coe_smul_puncturedPhaseSpace]
    exact ⟨radialProjection_circle_smul g _, angularMomentum_circle_smul g _⟩
  obtain ⟨⟨q, p⟩, hq⟩ := x
  obtain ⟨⟨q', p'⟩, hq'⟩ := x'
  rw [mem_puncturedPhaseSpace] at hq hq'
  simp only [radialProjection_apply, Prod.mk.injEq] at hr
  obtain ⟨hn, hrad⟩ := hr
  have hn₀ : ‖q'‖ ≠ 0 := norm_ne_zero_iff.2 hq'
  rw [hn, div_left_inj₀ hn₀] at hrad
  rw [angularMomentum_one_I, angularMomentum_one_I] at hL
  -- `conj q * p` is determined by `⟪q, p⟫ = Re (conj q * p)` and `L = Im (conj q * p)`.
  have hc : conj q * p = conj q' * p' := Complex.ext (by
    simpa [Complex.inner, mul_re, mul_comm] using hrad) hL
  have hg : ‖q / q'‖ = 1 := by rw [norm_div, hn, div_self hn₀]
  have hgq : q / q' * q' = q := div_mul_cancel₀ q hq'
  refine ⟨⟨q / q', by simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hg⟩,
    Subtype.ext (Prod.ext hgq ?_)⟩
  -- The rotation by `g = q / q'` acts on momenta by multiplication by `g`.
  change q / q' * p' = p
  generalize q / q' = g at hg hgq
  -- `conj q * (g p') = |g|² conj q' * p' = conj q * p`, and `q ≠ 0`.
  have hconj : conj g * g = 1 := by
    rw [conj_mul', hg, ofReal_one, one_pow]
  refine mul_left_cancel₀ (map_ne_zero (starRingEnd ℂ) |>.2 hq) ?_
  rw [hc, ← hgq, map_mul]
  linear_combination (conj q' * p') * hconj

/-- The phase space `T*(0, ∞) = (0, ∞) × ℝ` of the radial motion, with coordinates `(r, p_r)`: an
open subset of `ℝ × ℝ`, with the area form `dr ∧ dp_r` restricted from `ℝ × ℝ`. -/
def radialPhaseSpace : TopologicalSpace.Opens (ℝ × ℝ) :=
  ⟨{x | 0 < x.1}, isOpen_lt continuous_const continuous_fst⟩

@[simp]
theorem mem_radialPhaseSpace {x : ℝ × ℝ} : x ∈ radialPhaseSpace ↔ 0 < x.1 :=
  Iff.rfl

/-! ### The levels of the rotational moment map -/

/-- The functional `ψ₀(ξ) = Im (ι_* ξ)` on the Lie algebra of the circle, for the inclusion
`ι : Circle → ℂ`; the rotational moment map is `x ↦ L(x) ψ₀`. -/
local notation "ψ₀" => (ContinuousLinearMap.toLinearMap
  (imCLM ∘L mvfderiv (𝓡 1) (fun z : Circle ↦ (z : ℂ)) 1) :
    Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle))

/-- The standard symplectic form of the punctured planar phase space. -/
local notation "σL" => SmoothForm.mpullback (Subtype.val : 𝕄 → ℂ × ℂ) contMDiff_subtypeVal
  (SymplecticForm.constSmooth (stdSymplecticForm (V := ℂ)))

/-- The rotational moment map. -/
local notation "μL" => fun x : 𝕄 ↦ angularMomentum 1 I (x : ℂ × ℂ) • ψ₀

private theorem isSymplectic_σL : SmoothTwoForm.IsSymplectic (σL) :=
  SmoothTwoForm.IsSymplectic.mpullback_subtype_val (SymplecticForm.isSymplectic_constSmooth _) _

/-- **Every value of the rotational moment map is regular.** Since the rotations act freely on the
punctured planar phase space, the differential of the moment map `x ↦ L(x) ψ₀` is onto at every
point. -/
theorem differential_surjective_angularMomentum_puncturedPhaseSpace
    (h : SmoothTwoForm.IsEquivariantMomentMap (σL) μL) (x : 𝕄) :
    Surjective (h.differential x) :=
  h.toIsMomentMap.differential_surjective_of_stabilizer_eq_bot
    (isSymplectic_σL.isNondegenerate.nondegenerate_bilinFormAt x)
    (stabilizer_circle_puncturedPhaseSpace x)

/-- The rotations act freely on every level of the rotational moment map. -/
instance (h : SmoothTwoForm.IsEquivariantMomentMap (σL) μL)
    (c : Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)) :
    IsCancelSMul ((Lie.coadjointRepresentation ℝ (𝓡 1) Circle).stabilizer c)
      (h.levelSubMulAction c) :=
  h.isCancelSMul_levelSubMulAction fun x _ ↦ stabilizer_circle_puncturedPhaseSpace x

private theorem ψ₀_apply_mfderiv_circleExp : ψ₀ (mfderiv 𝓘(ℝ) (𝓡 1) Circle.exp 0 (1 : ℝ)) = 1 := by
  -- `ψ₀` is the imaginary part of the derivative of the inclusion, which sends the generator of
  -- `t ↦ exp (t i)` to `i`.
  change (mvfderiv (𝓡 1) (fun z : Circle ↦ (z : ℂ)) 1
    (mfderiv 𝓘(ℝ) (𝓡 1) Circle.exp 0 (1 : ℝ))).im = 1
  rw [mvfderiv_coe_mfderiv_circleExp, I_im]

/-- **The levels of the rotational moment map are the levels of the angular momentum.** A state of
the punctured planar phase space lies on the level of `ℓ ψ₀` exactly when its angular momentum is
`ℓ`. -/
theorem mem_levelSubMulAction_angularMomentum_iff
    {h : SmoothTwoForm.IsEquivariantMomentMap (σL) μL} {ℓ : ℝ} {x : 𝕄} :
    x ∈ h.levelSubMulAction (ℓ • ψ₀) ↔ angularMomentum 1 I (x : ℂ × ℂ) = ℓ := by
  rw [h.mem_levelSubMulAction]
  refine ⟨fun hx ↦ ?_, fun hx ↦ by rw [hx]⟩
  have := LinearMap.congr_fun hx (mfderiv 𝓘(ℝ) (𝓡 1) Circle.exp 0 (1 : ℝ))
  -- Scalar multiples of a dual vector are evaluated pointwise.
  change angularMomentum 1 I (x : ℂ × ℂ) * ψ₀ (mfderiv 𝓘(ℝ) (𝓡 1) Circle.exp 0 (1 : ℝ)) =
    ℓ * ψ₀ (mfderiv 𝓘(ℝ) (𝓡 1) Circle.exp 0 (1 : ℝ)) at this
  rwa [ψ₀_apply_mfderiv_circleExp, mul_one, mul_one] at this

/-- The circle is commutative, so it fixes every functional on its Lie algebra. -/
private theorem finrank_lieAnnihilator_circle (c : Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)) :
    finrank ℝ (lieAnnihilator ℝ (GroupLieAlgebra (𝓡 1) Circle) c) = 1 := by
  have : lieAnnihilator ℝ (GroupLieAlgebra (𝓡 1) Circle) c = ⊤ :=
    (lieAnnihilator_eq_top_iff ℝ _).2 fun x ↦ LinearMap.ext fun y ↦ by simp [trivial_lie_zero]
  rw [this, LieSubalgebra.topEquiv.toLinearEquiv.finrank_eq]
  simp

/-! ### The reduced spaces -/

section ReducedSpace

variable {ℓ : ℝ} {h : SmoothTwoForm.IsEquivariantMomentMap (σL) μL}
  (hreg : ∀ x : 𝕄, angularMomentum 1 I (x : ℂ × ℂ) • ψ₀ = ℓ • ψ₀ → Surjective (h.differential x))
  {n : ℕ} (hn : finrank ℝ (ℂ × ℂ) - finrank ℝ (GroupLieAlgebra (𝓡 1) Circle) = n)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData (𝓡 1)
    ((Lie.coadjointRepresentation ℝ (𝓡 1) Circle).stabilizer (ℓ • ψ₀)) F)

/-- The radius and radial momentum of a state on the level of `ℓ ψ₀`. -/
private def levelRadialProjection (z : h.levelSubMulAction (ℓ • ψ₀)) : radialPhaseSpace :=
  ⟨radialProjection ((z : 𝕄) : ℂ × ℂ), by
    rw [mem_radialPhaseSpace, radialProjection_fst]
    exact norm_pos_iff.2 (mem_puncturedPhaseSpace.1 (z : 𝕄).property)⟩

/-- Every point `(r, p_r)` with `r > 0` is the radius and radial momentum of the state
`(r, p_r + (ℓ / r) i)` of angular momentum `ℓ`. -/
private theorem levelRadialProjection_surjective :
    Surjective (levelRadialProjection (ℓ := ℓ) (h := h)) := by
  rintro ⟨⟨r, s⟩, hr⟩
  rw [mem_radialPhaseSpace] at hr
  let x : 𝕄 := ⟨((r : ℂ), (s : ℂ) + ((ℓ / r : ℝ) : ℂ) * I),
    mem_puncturedPhaseSpace.2 (ofReal_ne_zero.2 hr.ne')⟩
  have hx : angularMomentum 1 I (x : ℂ × ℂ) = ℓ := by
    rw [angularMomentum_one_I]
    simp only [conj_ofReal, mul_im, ofReal_re, add_im, ofReal_im, I_im, I_re, add_re, mul_re]
    field_simp
    ring
  refine ⟨⟨x, mem_levelSubMulAction_angularMomentum_iff.2 hx⟩, Subtype.ext ?_⟩
  simp only [levelRadialProjection, radialProjection_apply, x, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr, Prod.mk.injEq, true_and]
  simp only [Complex.inner, conj_ofReal, mul_re, ofReal_re, add_re, ofReal_im, mul_im, I_re,
    I_im, add_im]
  field_simp
  ring

/-- Two states on the level have the same radius and radial momentum exactly when they lie in the
same orbit. -/
private theorem levelRadialProjection_eq_iff (z z' : h.levelSubMulAction (ℓ • ψ₀)) :
    levelRadialProjection z = levelRadialProjection z' ↔
      (Quotient.mk _ z : MulAction.orbitRel.Quotient
        ((Lie.coadjointRepresentation ℝ (𝓡 1) Circle).stabilizer (ℓ • ψ₀))
        (h.levelSubMulAction (ℓ • ψ₀))) = Quotient.mk _ z' := by
  have hL (z : h.levelSubMulAction (ℓ • ψ₀)) : angularMomentum 1 I ((z : 𝕄) : ℂ × ℂ) = ℓ :=
    mem_levelSubMulAction_angularMomentum_iff.1 z.property
  rw [Quotient.eq, h.orbitRel_levelSubMulAction_iff, MulAction.orbitRel_apply,
    MulAction.mem_orbit_iff, exists_circle_smul_eq_iff, hL, hL, levelRadialProjection,
    levelRadialProjection, Subtype.mk.injEq]
  exact (and_iff_left rfl).symm

include hreg hn d in
/-- The reduced space at angular momentum `ℓ` is recognized as `(T*(0, ∞), dr ∧ dp_r)` through
the radius and the radial momentum. -/
private theorem exists_reducedSpace_diffeomorph :
    letI := h.levelSubMulActionChartedSpace (ℓ • ψ₀) hreg hn
    letI := h.orbitRelQuotientChartedSpace (ℓ • ψ₀) hreg hn d
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∃ Φ : MulAction.orbitRel.Quotient
        ((Lie.coadjointRepresentation ℝ (𝓡 1) Circle).stabilizer (ℓ • ψ₀))
        (h.levelSubMulAction (ℓ • ψ₀)) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)),
          𝓘(ℝ, ℝ × ℝ)⟯ radialPhaseSpace,
      (∀ z, Φ (Quotient.mk _ z) = levelRadialProjection z) ∧
      ∀ η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
          (MulAction.orbitRel.Quotient
            ((Lie.coadjointRepresentation ℝ (𝓡 1) Circle).stabilizer (ℓ • ψ₀))
            (h.levelSubMulAction (ℓ • ψ₀))),
        SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff
            η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff (σL) →
        SmoothForm.mpullback Φ Φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : radialPhaseSpace → ℝ × ℝ) contMDiff_subtypeVal
            (SymplecticForm.constSmooth (stdSymplecticForm (V := ℝ)))) = η := by
  let := h.levelSubMulActionChartedSpace (ℓ • ψ₀) hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace (ℓ • ψ₀) hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  have hι := (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
  have hp := h.isSubmersion_quotientMk_levelSubMulAction hreg hn d
  obtain ⟨η₀, ⟨hη₀s, hη₀⟩, -⟩ :=
    h.existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback hreg hn d isSymplectic_σL
      hamiltonianTorusData_angularMomentum_puncturedPhaseSpace.mpullback_smul
  have hΨ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (levelRadialProjection (ℓ := ℓ) (h := h)) :=
    (ContMDiff.subtypeVal_comp_iff radialPhaseSpace _).1
      (contMDiff_radialProjection_comp_subtypeVal.comp hι)
  -- Along the level, `σ` is `dr ∧ dp_r`.
  have hpΨ : SmoothForm.mpullback _ hΨ
      (SmoothForm.mpullback (Subtype.val : radialPhaseSpace → ℝ × ℝ) contMDiff_subtypeVal
        (SymplecticForm.constSmooth (stdSymplecticForm (V := ℝ)))) =
      SmoothForm.mpullback _ hp.contMDiff η₀ := by
    rw [hη₀, SmoothForm.mpullback_mpullback,
      mpullback_stdSymplecticForm_of_angularMomentum_eq Complex.orthonormalBasisOneI hι
        fun z ↦ by simpa [Complex.coe_orthonormalBasisOneI] using
          mem_levelSubMulAction_angularMomentum_iff.1 z.property]
    -- Both sides pull back along `z ↦ radialProjection z`, through `radialPhaseSpace` or not.
    exact SmoothForm.mpullback_congr _ _ rfl _
  -- The reduced space has dimension `4 - 1 - 1 = 2`.
  obtain ⟨z₀⟩ : Nonempty (h.levelSubMulAction (ℓ • ψ₀)) :=
    (levelRadialProjection_surjective ⟨(1, 0), by simp⟩).nonempty
  have hdim : finrank ℝ (ProperSMul.QuotientModelSpace F (Fin n → ℝ)) = finrank ℝ (ℝ × ℝ) := by
    have := h.finrank_quotientModelSpace_add_finrank_add_finrank_lieAnnihilator hreg hn d
      isSymplectic_σL.isNondegenerate z₀
    rw [finrank_lieAnnihilator_circle] at this
    simp at this ⊢
    omega
  obtain ⟨Φ, hΦp, hΦη⟩ := SmoothTwoForm.exists_diffeomorph_comp_eq_and_mpullback_eq hp
    Quotient.mk_surjective hη₀s.isNondegenerate hΨ levelRadialProjection_surjective
    (fun z z' ↦ levelRadialProjection_eq_iff z z') hdim hpΨ
  refine ⟨Φ, fun z ↦ congrFun hΦp z, fun η hη ↦ hΦη.trans ?_⟩
  -- Pulling back along the orbit projection is injective, so `η` is the reduced form.
  exact SmoothForm.mpullback_injective_of_surjective hp.contMDiff Quotient.mk_surjective
    (fun _ ↦ hp.surjective_mfderiv (by simp) _) (hη₀.trans hη.symm)

variable (h) in
/-- **The reduced space of planar central forces at angular momentum `ℓ`.** For every real `ℓ`,
the Marsden–Weinstein–Meyer reduced space `μ⁻¹(ℓ ψ₀) / S¹` of the rotations of the punctured
planar phase space, with the atlas of the Marsden–Weinstein–Meyer theorem, is diffeomorphic to the
phase space `(0, ∞) × ℝ` of the radial motion. The diffeomorphism sends the orbit of a state
`(q, p)` of angular momentum `ℓ` to its radius and radial momentum `(‖q‖, ⟪q, p⟫ / ‖q‖)`
(`TauCeti.coe_angularMomentumReducedSpaceDiffeomorph_mk`), and it carries the reduced symplectic
form to `dr ∧ dp_r` (`TauCeti.mpullback_angularMomentumReducedSpaceDiffeomorph`).

The hypotheses `h` and `hreg` are those of the atlas: they hold by
`TauCeti.hamiltonianTorusData_angularMomentum_puncturedPhaseSpace` and
`TauCeti.differential_surjective_angularMomentum_puncturedPhaseSpace`. -/
def angularMomentumReducedSpaceDiffeomorph :
    letI := h.orbitRelQuotientChartedSpace (ℓ • ψ₀) hreg hn d
    MulAction.orbitRel.Quotient
        ((Lie.coadjointRepresentation ℝ (𝓡 1) Circle).stabilizer (ℓ • ψ₀))
        (h.levelSubMulAction (ℓ • ψ₀)) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)),
          𝓘(ℝ, ℝ × ℝ)⟯ radialPhaseSpace :=
  (exists_reducedSpace_diffeomorph hreg hn d).choose

/-- **The reduced space at angular momentum `ℓ`, in coordinates.** The diffeomorphism
`μ⁻¹(ℓ ψ₀) / S¹ ≅ (0, ∞) × ℝ` sends the orbit of a state `(q, p)` of angular momentum `ℓ` to its
radius and radial momentum `(‖q‖, ⟪q, p⟫ / ‖q‖)`. -/
theorem coe_angularMomentumReducedSpaceDiffeomorph_mk (z : h.levelSubMulAction (ℓ • ψ₀)) :
    letI := h.orbitRelQuotientChartedSpace (ℓ • ψ₀) hreg hn d
    (angularMomentumReducedSpaceDiffeomorph h hreg hn d (Quotient.mk _ z) : ℝ × ℝ) =
      radialProjection ((z : 𝕄) : ℂ × ℂ) :=
  congrArg Subtype.val ((exists_reducedSpace_diffeomorph hreg hn d).choose_spec.1 z)

/-- **Reduction of planar central forces: the symplectic forms.** The diffeomorphism
`μ⁻¹(ℓ ψ₀) / S¹ ≅ (0, ∞) × ℝ` pulls the area form `dr ∧ dp_r` back to the reduced symplectic form
`η` of the Marsden–Weinstein–Meyer theorem, the form on the reduced space with `π^* η = i^* σ` for
the orbit projection `π` and the inclusion `i` of the level into the punctured phase space
(`existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback` in
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`). So the reduced space is symplectomorphic to the
cotangent bundle `(T*(0, ∞), dr ∧ dp_r)` of the radial half-line. -/
theorem mpullback_angularMomentumReducedSpaceDiffeomorph :
    letI := h.levelSubMulActionChartedSpace (ℓ • ψ₀) hreg hn
    letI := h.orbitRelQuotientChartedSpace (ℓ • ψ₀) hreg hn d
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∀ η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient
          ((Lie.coadjointRepresentation ℝ (𝓡 1) Circle).stabilizer (ℓ • ψ₀))
          (h.levelSubMulAction (ℓ • ψ₀))),
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff
          η =
        SmoothForm.mpullback Subtype.val
          (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff (σL) →
      SmoothForm.mpullback (angularMomentumReducedSpaceDiffeomorph h hreg hn d)
          (angularMomentumReducedSpaceDiffeomorph h hreg hn d).contMDiff
          (SmoothForm.mpullback (Subtype.val : radialPhaseSpace → ℝ × ℝ) contMDiff_subtypeVal
            (SymplecticForm.constSmooth (stdSymplecticForm (V := ℝ)))) = η :=
  (exists_reducedSpace_diffeomorph hreg hn d).choose_spec.2

/-- **Reduction of planar central forces: the reduced Hamiltonian.** On the level of angular
momentum `ℓ`, a central-force Hamiltonian `H = ‖p‖² / (2m) + U(‖q‖)` is the reduced Hamiltonian
`H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)` of the image of the orbit in `(0, ∞) × ℝ`, with the effective
potential `U_ℓ(r) = ℓ² / (2 m r²) + U(r)`. -/
theorem centralForceHamiltonian_effectivePotential_angularMomentumReducedSpaceDiffeomorph_mk
    (m : ℝ) (U : ℝ → ℝ) (z : h.levelSubMulAction (ℓ • ψ₀)) :
    letI := h.orbitRelQuotientChartedSpace (ℓ • ψ₀) hreg hn d
    centralForceHamiltonian m (effectivePotential m ℓ U)
        (angularMomentumReducedSpaceDiffeomorph h hreg hn d (Quotient.mk _ z) : ℝ × ℝ) =
      centralForceHamiltonian m U ((z : 𝕄) : ℂ × ℂ) := by
  rw [coe_angularMomentumReducedSpaceDiffeomorph_mk]
  refine centralForceHamiltonian_radialProjection (mem_puncturedPhaseSpace.1 (z : 𝕄).property) ?_
  rw [← sq_angularMomentum Complex.orthonormalBasisOneI]
  simp [Complex.coe_orthonormalBasisOneI, mem_levelSubMulAction_angularMomentum_iff.1 z.property]

end ReducedSpace

end TauCeti

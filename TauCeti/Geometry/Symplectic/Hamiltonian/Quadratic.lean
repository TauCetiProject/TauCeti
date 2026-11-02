/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SkewAdjoint
public import TauCeti.Analysis.Calculus.FDeriv.QuadraticMap
public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap

/-!
# Quadratic Hamiltonians and the symplectic Lie algebra

Let `(V, ω)` be a finite-dimensional real symplectic vector space. A quadratic form `Q` on `V`,
viewed as a Hamiltonian, has a linear Hamiltonian vector field: with the convention
`ι_{X_H} ω = dH` and `dQ_v = polar Q v`, it is `v ↦ A_Q v` for the endomorphism `A_Q`
(`TauCeti.SymplecticForm.hamiltonianEnd ω Q`) characterized by

`ω (A_Q v) w = polar Q v w`.

Since `polar Q` is symmetric and `ω` is alternating, `A_Q` is skew-adjoint for `ω`, that is it
lies in the symplectic Lie algebra `sp(V, ω)`, Mathlib's `skewAdjointLieSubalgebra ω`. Conversely
every skew-adjoint `A` is `A_Q` for the quadratic form `v ↦ ω (A v) v / 2`, the component `μ_A` of
the moment map of the linear action of `sp(V, ω)` (`TauCeti.SymplecticForm.linearMomentMap`).
This identifies quadratic forms with `sp(V, ω)` (`TauCeti.SymplecticForm.hamiltonianEndEquiv`).

Under this identification the Poisson bracket of quadratic Hamiltonians,
`{Q, R}(v) = ω (A_Q v) (A_R v)` (`TauCeti.SymplecticForm.quadraticPoissonBracket`), becomes the
commutator: `A_{Q, R} = ⁅A_Q, A_R⁆`. In particular two quadratic Hamiltonians Poisson-commute
exactly when their Hamiltonian endomorphisms commute.

For a `C²` Hamiltonian `H`, the linearization of its Hamiltonian vector field at any point is the
Hamiltonian endomorphism of its quadratic Taylor term `½ Hess H`. If two `C²` functions `F`, `G`
are critical at `x` and Poisson-commute on a neighbourhood of `x`, then the quadratic Hamiltonians
`½ Hess F` and `½ Hess G` Poisson-commute, so the linearizations of `X_F` and `X_G` at `x`
commute. Thus, at a common critical point of a family of pairwise Poisson-commuting functions, the
Hamiltonian endomorphisms of their Hessians pairwise commute in `sp(V, ω)`. This is the linear
data on which Williamson's classification of nondegenerate critical points of integrable systems
operates.

## Main definitions

* `TauCeti.SymplecticForm.hamiltonianEnd ω`: the linear map `Q ↦ A_Q` from quadratic forms to
  endomorphisms.
* `TauCeti.SymplecticForm.hamiltonianEndEquiv ω`: the linear equivalence between quadratic forms
  and `sp(V, ω)`.
* `TauCeti.SymplecticForm.quadraticPoissonBracket ω Q R`: the Poisson bracket of two quadratic
  forms, as a quadratic form.

## Main results

* `TauCeti.SymplecticForm.apply_hamiltonianEnd`, `TauCeti.SymplecticForm.eq_hamiltonianEnd_iff`:
  the characterizing identity `ω (A_Q v) w = polar Q v w`.
* `TauCeti.SymplecticForm.hamiltonianEnd_mem_skewAdjointLieSubalgebra`: `A_Q ∈ sp(V, ω)`.
* `TauCeti.SymplecticForm.hamiltonianEndEquiv_symm_apply_apply`: the inverse equivalence sends `A`
  to the linear moment map component `μ_A`.
* `TauCeti.SymplecticForm.hamiltonianEnd_quadraticPoissonBracket`: `A_{Q, R} = ⁅A_Q, A_R⁆`.
* `TauCeti.SymplecticForm.quadraticPoissonBracket_eq_zero_iff`: `{Q, R} = 0` exactly when `A_Q`
  and `A_R` commute.
* `TauCeti.SymplecticForm.hamiltonianVectorField_quadraticForm`,
  `TauCeti.SymplecticForm.poissonBracket_quadraticForm`: the Hamiltonian vector field of `Q` is
  `A_Q`, and the Poisson bracket of the functions `Q` and `R` is `{Q, R}`.
* `TauCeti.SymplecticForm.fderiv_hamiltonianVectorField`: the linearization of `X_H` at `x` is
  `A_{½ Hess H(x)}`.
* `TauCeti.SymplecticForm.commute_fderiv_hamiltonianVectorField`: at a common critical point of
  two functions which Poisson-commute near it, the linearizations of their Hamiltonian vector
  fields commute.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Appendix 6 (quadratic Hamiltonians and `sp(2n)`).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.1 (the Lie algebra of the linear symplectic group).
-/

public section

noncomputable section

open Filter Topology

-- `sp(V, ω)` is a Lie subalgebra of `Module.End ℝ V` for the commutator bracket, as in Mathlib's
-- `Mathlib.Algebra.Lie.SkewAdjoint`.
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.SymplecticForm

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

omit [FiniteDimensional ℝ V] in
/-- Two endomorphisms agree once `ω` pairs their values identically with every vector. -/
private theorem ext_of_apply_left {A B : Module.End ℝ V} (h : ∀ v w, ω (A v) w = ω (B v) w) :
    A = B :=
  LinearMap.ext fun v ↦ LinearMap.ker_eq_bot.1
    (LinearMap.separatingLeft_iff_ker_eq_bot.1 ω.separatingLeft) (LinearMap.ext (h v))

/-- The **Hamiltonian endomorphism** `A_Q` of a quadratic form `Q`, the unique endomorphism with
`ω (A_Q v) w = polar Q v w`. Viewing `Q` as a Hamiltonian, `A_Q` is its Hamiltonian vector
field, under the convention `ι_{X_H} ω = dH`. -/
def hamiltonianEnd : QuadraticForm ℝ V →ₗ[ℝ] Module.End ℝ V where
  toFun Q := LinearMap.BilinForm.symmCompOfNondegenerate (QuadraticMap.polarBilin Q) ω.toBilinForm
    ω.nondegenerate
  map_add' Q R := ω.ext_of_apply_left fun v w ↦ by
    simp [QuadraticMap.polar_add]
  map_smul' c Q := ω.ext_of_apply_left fun v w ↦ by
    simp [QuadraticMap.polar_smul]

/-- The characterizing identity `ω (A_Q v) w = polar Q v w` of the Hamiltonian endomorphism. -/
@[simp]
theorem apply_hamiltonianEnd (Q : QuadraticForm ℝ V) (v w : V) :
    ω (ω.hamiltonianEnd Q v) w = QuadraticMap.polar Q v w :=
  LinearMap.BilinForm.symmCompOfNondegenerate_left_apply (QuadraticMap.polarBilin Q)
    ω.nondegenerate w v

/-- The Hamiltonian endomorphism of `Q` is the only endomorphism `A` with
`ω (A v) w = polar Q v w`. -/
theorem eq_hamiltonianEnd_iff {Q : QuadraticForm ℝ V} {A : Module.End ℝ V} :
    A = ω.hamiltonianEnd Q ↔ ∀ v w, ω (A v) w = QuadraticMap.polar Q v w := by
  refine ⟨fun h v w ↦ h ▸ ω.apply_hamiltonianEnd Q v w, fun h ↦ ω.ext_of_apply_left fun v w ↦ ?_⟩
  rw [h, apply_hamiltonianEnd]

/-- Pairing on the right: `ω v (A_Q w) = -polar Q v w`. -/
@[simp]
theorem apply_hamiltonianEnd_right (Q : QuadraticForm ℝ V) (v w : V) :
    ω v (ω.hamiltonianEnd Q w) = -QuadraticMap.polar Q v w := by
  rw [← ω.neg_eq, apply_hamiltonianEnd, QuadraticMap.polar_comm]

/-- The Hamiltonian endomorphism of a quadratic form is skew-adjoint for `ω`: it lies in the
symplectic Lie algebra `sp(V, ω)`. -/
theorem hamiltonianEnd_mem_skewAdjointLieSubalgebra (Q : QuadraticForm ℝ V) :
    ω.hamiltonianEnd Q ∈ skewAdjointLieSubalgebra ω.toBilinForm := by
  refine (LinearMap.mem_skewAdjointSubmodule _).2 fun v w ↦ ?_
  have h₁ := ω.apply_hamiltonianEnd Q v w
  have h₂ := ω.apply_hamiltonianEnd_right Q v w
  beta_reduce at h₁ h₂ ⊢
  rw [Pi.neg_apply, map_neg, h₁, h₂, neg_neg]

/-- The Hamiltonian endomorphism of `Q` vanishes only for `Q = 0`. -/
theorem hamiltonianEnd_injective : Function.Injective ω.hamiltonianEnd := by
  refine (injective_iff_map_eq_zero _).2 fun Q hQ ↦ QuadraticMap.ext fun v ↦ ?_
  have h := ω.apply_hamiltonianEnd Q v v
  rw [hQ, LinearMap.zero_apply] at h
  beta_reduce at h
  rw [map_zero, LinearMap.zero_apply, QuadraticMap.polar_self, two_smul] at h
  simpa using (add_self_eq_zero.1 h.symm)

/-- The quadratic form `v ↦ ω (A v) v / 2` of a skew-adjoint endomorphism `A`. -/
private def quadraticFormOfSkewAdjoint (A : skewAdjointLieSubalgebra ω.toBilinForm) :
    QuadraticForm ℝ V :=
  LinearMap.BilinMap.toQuadraticMap
    ((2⁻¹ : ℝ) • ω.toBilinForm.compl₁₂ (A : Module.End ℝ V) LinearMap.id)

omit [FiniteDimensional ℝ V] in
private theorem quadraticFormOfSkewAdjoint_apply (A : skewAdjointLieSubalgebra ω.toBilinForm)
    (v : V) : ω.quadraticFormOfSkewAdjoint A v = ω ((A : Module.End ℝ V) v) v / 2 := by
  simp only [quadraticFormOfSkewAdjoint, LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.smul_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply, smul_eq_mul]
  ring

/-- The quadratic form `v ↦ ω (A v) v / 2` of a skew-adjoint endomorphism `A` has Hamiltonian
endomorphism `A`. -/
private theorem hamiltonianEnd_quadraticFormOfSkewAdjoint
    (A : skewAdjointLieSubalgebra ω.toBilinForm) :
    ω.hamiltonianEnd (ω.quadraticFormOfSkewAdjoint A) = A := by
  refine (ω.eq_hamiltonianEnd_iff.2 fun v w ↦ ?_).symm
  have h := skewAdjointLieSubalgebra.apply_left A w v
  rw [QuadraticMap.polar, quadraticFormOfSkewAdjoint_apply, quadraticFormOfSkewAdjoint_apply,
    quadraticFormOfSkewAdjoint_apply]
  beta_reduce at h ⊢
  have h' := ω.isAlt.neg_eq ((A : Module.End ℝ V) v) w
  simp only [map_add, LinearMap.add_apply, h, ← h']
  ring

/-- **Quadratic forms are the symplectic Lie algebra.** The Hamiltonian endomorphism is a linear
equivalence between quadratic forms on `V` and `sp(V, ω)`, with inverse `A ↦ (v ↦ ω (A v) v / 2)`.
-/
def hamiltonianEndEquiv : QuadraticForm ℝ V ≃ₗ[ℝ] skewAdjointLieSubalgebra ω.toBilinForm :=
  LinearEquiv.ofBijective
    ((ω.hamiltonianEnd).codRestrict (skewAdjointLieSubalgebra ω.toBilinForm).toSubmodule
      ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra)
    ⟨fun _ _ h ↦ ω.hamiltonianEnd_injective (congrArg Subtype.val h), fun A ↦
      ⟨_, Subtype.ext (ω.hamiltonianEnd_quadraticFormOfSkewAdjoint A)⟩⟩

/-- The equivalence `hamiltonianEndEquiv` sends `Q` to its Hamiltonian endomorphism. -/
@[simp]
theorem coe_hamiltonianEndEquiv_apply (Q : QuadraticForm ℝ V) :
    (ω.hamiltonianEndEquiv Q : Module.End ℝ V) = ω.hamiltonianEnd Q :=
  (rfl)

/-- The inverse of `hamiltonianEndEquiv` sends `A` to the moment map component
`μ_A(v) = ω (A v) v / 2` of the linear action. -/
@[simp]
theorem hamiltonianEndEquiv_symm_apply_apply (A : skewAdjointLieSubalgebra ω.toBilinForm)
    (v : V) : ω.hamiltonianEndEquiv.symm A v = ω.linearMomentMap v A := by
  rw [linearMomentMap_apply, ← quadraticFormOfSkewAdjoint_apply,
    ω.hamiltonianEndEquiv.symm_apply_eq.2
      (Subtype.ext (ω.hamiltonianEnd_quadraticFormOfSkewAdjoint A).symm)]

/-! ### The Poisson bracket of quadratic Hamiltonians -/

/-- The **Poisson bracket** of two quadratic Hamiltonians, `{Q, R}(v) = ω (A_Q v) (A_R v)`. This
is again a quadratic form. -/
def quadraticPoissonBracket (Q R : QuadraticForm ℝ V) : QuadraticForm ℝ V :=
  LinearMap.BilinMap.toQuadraticMap
    (ω.toBilinForm.compl₁₂ (ω.hamiltonianEnd Q) (ω.hamiltonianEnd R))

/-- The value of the quadratic Poisson bracket: `{Q, R}(v) = ω (A_Q v) (A_R v)`. -/
@[simp]
theorem quadraticPoissonBracket_apply (Q R : QuadraticForm ℝ V) (v : V) :
    ω.quadraticPoissonBracket Q R v = ω (ω.hamiltonianEnd Q v) (ω.hamiltonianEnd R v) :=
  (rfl)

/-- The quadratic Poisson bracket is additive in its first argument. -/
theorem quadraticPoissonBracket_add_left (Q Q' R : QuadraticForm ℝ V) :
    ω.quadraticPoissonBracket (Q + Q') R =
      ω.quadraticPoissonBracket Q R + ω.quadraticPoissonBracket Q' R := by
  ext v
  simp only [quadraticPoissonBracket_apply, map_add, add_apply, LinearMap.add_apply]

/-- The quadratic Poisson bracket is additive in its second argument. -/
theorem quadraticPoissonBracket_add_right (Q R R' : QuadraticForm ℝ V) :
    ω.quadraticPoissonBracket Q (R + R') =
      ω.quadraticPoissonBracket Q R + ω.quadraticPoissonBracket Q R' := by
  ext v
  simp only [quadraticPoissonBracket_apply, map_add, add_apply, LinearMap.add_apply]

/-- The quadratic Poisson bracket is homogeneous in its first argument. -/
theorem quadraticPoissonBracket_smul_left (c : ℝ) (Q R : QuadraticForm ℝ V) :
    ω.quadraticPoissonBracket (c • Q) R = c • ω.quadraticPoissonBracket Q R := by
  ext v
  simp only [quadraticPoissonBracket_apply, map_smul, smul_apply, LinearMap.smul_apply]

/-- The quadratic Poisson bracket is homogeneous in its second argument. -/
theorem quadraticPoissonBracket_smul_right (c : ℝ) (Q R : QuadraticForm ℝ V) :
    ω.quadraticPoissonBracket Q (c • R) = c • ω.quadraticPoissonBracket Q R := by
  ext v
  simp only [quadraticPoissonBracket_apply, map_smul, smul_apply, LinearMap.smul_apply]

/-- The quadratic Poisson bracket is antisymmetric. -/
theorem neg_quadraticPoissonBracket (Q R : QuadraticForm ℝ V) :
    -ω.quadraticPoissonBracket R Q = ω.quadraticPoissonBracket Q R := by
  ext v
  rw [neg_apply, quadraticPoissonBracket_apply, quadraticPoissonBracket_apply]
  exact ω.neg_eq _ _

/-- **The Hamiltonian endomorphism turns the Poisson bracket into the commutator**:
`A_{Q, R} = ⁅A_Q, A_R⁆`. -/
theorem hamiltonianEnd_quadraticPoissonBracket (Q R : QuadraticForm ℝ V) :
    ω.hamiltonianEnd (ω.quadraticPoissonBracket Q R) =
      ⁅ω.hamiltonianEnd Q, ω.hamiltonianEnd R⁆ := by
  refine (ω.eq_hamiltonianEnd_iff.2 fun v w ↦ ?_).symm
  -- Move each endomorphism across `ω`: `ω (A_Q (A_R v)) w = -ω (A_R v) (A_Q w)` and
  -- `ω (A_R (A_Q v)) w = -ω (A_Q v) (A_R w)`.
  have h₁ := ω.apply_hamiltonianEnd Q (ω.hamiltonianEnd R v) w
  have h₂ := ω.apply_hamiltonianEnd_right Q (ω.hamiltonianEnd R v) w
  have h₃ := ω.apply_hamiltonianEnd R (ω.hamiltonianEnd Q v) w
  have h₄ := ω.apply_hamiltonianEnd_right R (ω.hamiltonianEnd Q v) w
  have h₅ := ω.neg_eq (ω.hamiltonianEnd R v) (ω.hamiltonianEnd Q w)
  rw [quadraticPoissonBracket, LinearMap.BilinMap.polar_toQuadraticMap, Ring.lie_def]
  beta_reduce at h₁ h₂ h₃ h₄ h₅ ⊢
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, LinearMap.compl₁₂_apply]
  rw [h₁, h₃, ← h₅, h₂, h₄]
  ring

/-- The equivalence between quadratic forms and `sp(V, ω)` intertwines the Poisson bracket with the
Lie bracket. -/
theorem hamiltonianEndEquiv_quadraticPoissonBracket (Q R : QuadraticForm ℝ V) :
    ω.hamiltonianEndEquiv (ω.quadraticPoissonBracket Q R) =
      ⁅ω.hamiltonianEndEquiv Q, ω.hamiltonianEndEquiv R⁆ :=
  Subtype.ext (ω.hamiltonianEnd_quadraticPoissonBracket Q R)

/-- Two quadratic Hamiltonians Poisson-commute exactly when their Hamiltonian endomorphisms
commute. -/
theorem quadraticPoissonBracket_eq_zero_iff {Q R : QuadraticForm ℝ V} :
    ω.quadraticPoissonBracket Q R = 0 ↔ Commute (ω.hamiltonianEnd Q) (ω.hamiltonianEnd R) := by
  rw [commute_iff_lie_eq, ← hamiltonianEnd_quadraticPoissonBracket,
    ← map_zero ω.hamiltonianEnd, ω.hamiltonianEnd_injective.eq_iff]

end Algebraic

section Analytic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

/-- The Hamiltonian vector field of a quadratic Hamiltonian `Q` is the linear vector field `A_Q`.
-/
theorem hamiltonianVectorField_quadraticForm (Q : QuadraticForm ℝ V) :
    ω.hamiltonianVectorField Q = ω.hamiltonianEnd Q := by
  funext x
  refine ((ω.eq_hamiltonianVectorField_iff Q x _).2 fun v ↦ ?_).symm
  rw [apply_hamiltonianEnd, Q.fderiv_apply]

/-- The Poisson bracket of the quadratic functions `Q` and `R` is their quadratic Poisson
bracket. -/
theorem poissonBracket_quadraticForm (Q R : QuadraticForm ℝ V) :
    ω.poissonBracket Q R = ω.quadraticPoissonBracket Q R := by
  funext x
  simp only [poissonBracket_def, hamiltonianVectorField_quadraticForm,
    quadraticPoissonBracket_apply]

/-- **The linearization of a Hamiltonian vector field** at `x` is the Hamiltonian endomorphism of
the quadratic Taylor term `½ Hess H(x)` of the Hamiltonian. -/
theorem fderiv_hamiltonianVectorField {H : V → ℝ} {x : V} (hH : ContDiffAt ℝ 2 H x) :
    (fderiv ℝ (ω.hamiltonianVectorField H) x : Module.End ℝ V) =
      ω.hamiltonianEnd ((2⁻¹ : ℝ) • hessianQuadraticForm H x) := by
  have hd := (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  refine ω.eq_hamiltonianEnd_iff.2 fun v w ↦ ?_
  rw [ContinuousLinearMap.coe_coe, ω.apply_fderiv_hamiltonianVectorField hd, QuadraticMap.polar]
  simp only [smul_apply, hessianQuadraticForm_apply, map_add, add_apply, smul_eq_mul]
  rw [hH.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) w v]
  ring

/-- Along the ray `t ↦ x + t w` from a critical point `x` of `H`, the rescaled Hamiltonian vector
field `t⁻¹ X_H(x + t w)` tends to the linearization of `X_H` at `x` applied to `w`. -/
private theorem tendsto_inv_smul_hamiltonianVectorField {H : V → ℝ} {x : V}
    (hH : ContDiffAt ℝ 2 H x) (hx : fderiv ℝ H x = 0) (w : V) :
    Tendsto (fun t : ℝ ↦ t⁻¹ • ω.hamiltonianVectorField H (x + t • w)) (𝓝[≠] 0)
      (𝓝 (fderiv ℝ (ω.hamiltonianVectorField H) x w)) := by
  have hd := (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hX : DifferentiableAt ℝ (ω.hamiltonianVectorField H) x := by
    have hdef : ω.hamiltonianVectorField H =
        fun y ↦ ω.toBilinForm.toContinuousBilinearMap.inverse (fderiv ℝ H y) :=
      funext (hamiltonianVectorField_def ω H)
    rw [hdef]
    exact (ω.toBilinForm.toContinuousBilinearMap.inverse.hasFDerivAt.comp x
      hd.hasFDerivAt).differentiableAt
  have hX0 : ω.hamiltonianVectorField H x = 0 := by
    rw [hamiltonianVectorField_def, hx, map_zero]
  have hray : HasDerivAt (fun t : ℝ ↦ x + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  simpa [Function.comp_def, hX0] using
    (hX.hasFDerivAt.comp_hasDerivAt_of_eq 0 hray (by simp)).tendsto_slope_zero

/-- **Hessians of Poisson-commuting functions Poisson-commute.** If `F` and `G` are `C²`, critical
at `x` and Poisson-commute on a neighbourhood of `x`, then their quadratic Taylor terms
`½ Hess F(x)` and `½ Hess G(x)` Poisson-commute. -/
theorem quadraticPoissonBracket_hessianQuadraticForm_eq_zero {F G : V → ℝ} {x : V}
    (hF : ContDiffAt ℝ 2 F x) (hG : ContDiffAt ℝ 2 G x) (hFx : fderiv ℝ F x = 0)
    (hGx : fderiv ℝ G x = 0) (hFG : ω.poissonBracket F G =ᶠ[𝓝 x] 0) :
    ω.quadraticPoissonBracket ((2⁻¹ : ℝ) • hessianQuadraticForm F x)
      ((2⁻¹ : ℝ) • hessianQuadraticForm G x) = 0 := by
  ext w
  rw [zero_apply, quadraticPoissonBracket_apply, ← fderiv_hamiltonianVectorField ω hF,
    ← fderiv_hamiltonianVectorField ω hG, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_coe]
  -- Along the ray `x + t w`, `t⁻² {F, G}(x + t w) = ω (t⁻¹ X_F) (t⁻¹ X_G)` tends to
  -- `ω (dX_F w) (dX_G w)`, while it vanishes for small `t ≠ 0`.
  have hlim := (ω.toBilinForm.toContinuousBilinearMap.continuous₂.tendsto _).comp
    ((ω.tendsto_inv_smul_hamiltonianVectorField hF hFx w).prodMk_nhds
      (ω.tendsto_inv_smul_hamiltonianVectorField hG hGx w))
  refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
  have hray : Tendsto (fun t : ℝ ↦ x + t • w) (𝓝[≠] 0) (𝓝 x) := by
    have hc : Continuous fun t : ℝ ↦ x + t • w := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [hray.eventually hFG] with t ht
  simp only [poissonBracket_def, Pi.zero_apply] at ht
  simp [ht]

/-- **Linearizations of Poisson-commuting Hamiltonian vector fields commute.** If `F` and `G` are
`C²`, critical at `x` and Poisson-commute on a neighbourhood of `x`, then the linearizations at
`x` of their Hamiltonian vector fields commute. -/
theorem commute_fderiv_hamiltonianVectorField {F G : V → ℝ} {x : V} (hF : ContDiffAt ℝ 2 F x)
    (hG : ContDiffAt ℝ 2 G x) (hFx : fderiv ℝ F x = 0) (hGx : fderiv ℝ G x = 0)
    (hFG : ω.poissonBracket F G =ᶠ[𝓝 x] 0) :
    Commute (fderiv ℝ (ω.hamiltonianVectorField F) x)
      (fderiv ℝ (ω.hamiltonianVectorField G) x) := by
  have h := (ω.quadraticPoissonBracket_eq_zero_iff).1
    (ω.quadraticPoissonBracket_hessianQuadraticForm_eq_zero hF hG hFx hGx hFG)
  rw [← fderiv_hamiltonianVectorField ω hF, ← fderiv_hamiltonianVectorField ω hG] at h
  refine (commute_iff_eq _ _).2 (ContinuousLinearMap.ext fun v ↦ ?_)
  simpa using LinearMap.congr_fun h.eq v

end Analytic

end TauCeti.SymplecticForm

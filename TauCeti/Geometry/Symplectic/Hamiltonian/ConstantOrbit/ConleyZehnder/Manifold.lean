/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent.RestPoint
public import TauCeti.Geometry.Symplectic.ConleyZehnder
public import TauCeti.Geometry.Symplectic.Hamiltonian.ConstantOrbit.Manifold
import TauCeti.Analysis.ODE.DysonSeries
import TauCeti.Analysis.SpecialFunctions.Exponential.BilinForm

/-!
# The Conley–Zehnder index of the constant orbits of a small Hamiltonian on a manifold

Let `σ` be a nondegenerate two-form on a boundaryless manifold `M` of dimension `2n`, for instance
the symplectic form of a closed symplectic manifold, and `F : M → ℝ` a `C³` function with a
nondegenerate critical point `p`. The point `p` is a zero of the Hamiltonian vector field of `ε F`
for every `ε`, so it is a constant orbit of the autonomous Hamiltonian `ε F`, and the differentials
`Ψ(t) = dφ_{0,t}(p)` of its flow maps are operators on the single tangent space `T_p M`. This file
computes the Conley–Zehnder index of the path `t ↦ Ψ(t)`, `t ∈ [0, 1]`, of linear symplectic maps
of `(T_p M, σ_p)` (`TauCeti.SymplecticForm.conleyZehnderIndex` for the tangent-space symplectic
form `TauCeti.SmoothTwoForm.IsNondegenerate.symplecticFormAt`): for small `ε > 0` it is
`ind_p(F) - n`, where `ind_p(F)` is the Morse index `TauCeti.manifoldMorseIndex`. It is the manifold
form of `TauCeti.SymplecticForm.eventually_conleyZehnderIndex_eq_morseIndex_sub_card`.

A constant orbit has the constant disc as a cap, and along the constant disc the tangent bundle is
framed by any fixed symplectic basis of `T_p M`. The index of `Ψ` in such a basis is therefore the
Conley–Zehnder grading of the constant orbit capped by the constant disc. The coordinate-free index
reads `Ψ` in bases in which `σ_p` has the matrix `J`; in the complex coordinates of `ℂⁿ`, in which
`σ_p` has the matrix `-J`, the index changes sign and is `n - ind_p(F)`
(`TauCeti.SymplecticForm.eventually_conleyZehnderIndex_eq_card_sub_morseIndex`). With the
convention `μ = -CZ` of Hamiltonian Floer theory, in those complex coordinates, the critical point
`p` thus has degree `μ = ind_p(F) - n`, which is the value computed here.

The computation has three steps.

* **The linearized flow is an exponential.** Let `L` be the derivative at the chart image of `p`
  of the coordinate expression of `X_F` in the preferred chart at `p`, the linearization of `X_F`
  at its rest point `p`. The field of `ε F` is `ε X_F`, whose linearization is `ε L`, so by the
  variational equation at a rest point
  (`TauCeti.hasDerivAt_mfderiv_timeDependentFlowOf_of_forall_eq_zero`) `Ψ' = ε L Ψ` with `Ψ(0) = 1`,
  and `Ψ(t) = exp (t ε L)` (`mfderiv_timeDependentFlowOf_hamiltonianVectorField_smul`).
* **The linearization is infinitesimally symplectic.** At a critical point the Hessian is
  `Hess F (p) (w, u) = σ_p(L w, u)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.criticalHessian_apply_eq_eval₂_fderiv`). As the Hessian
  is symmetric and `σ_p` antisymmetric, `L` is skew-adjoint for `σ_p`, so each `Ψ(t)` preserves
  `σ_p`; this needs no closedness of `σ`.
* **The normalization.** For an endomorphism `L` with `σ_p(L w, u) = Q(w, u)` for a nondegenerate
  symmetric form `Q`, the path `exp (t ε L)` has index `ind(Q) - n` for small `ε > 0`
  (`TauCeti.SymplecticForm.eventually_conleyZehnderIndex_eq_sigNeg_sub`, the coordinate-free form
  of the signature axiom). Here `Q` is the Hessian, whose negative index of inertia is the Morse
  index (`TauCeti.manifoldMorseIndex_eq_sigNeg_criticalHessian`).

Combined with the description of the one-periodic orbits of `ε F` for a Morse function `F` on a
compact manifold, this grades all the generators of the Floer complex of a small Morse
Hamiltonian: for small `ε > 0`, every one-periodic orbit `γ` of `ε F` starts at a critical point
`q = γ 0`, is nondegenerate, and has index `ind_q(F) - n`
(`exists_pos_forall_conleyZehnderIndex_eq_manifoldMorseIndex_sub` in the namespace
`TauCeti.SmoothTwoForm.IsNondegenerate`).

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `mfderiv_timeDependentFlowOf_hamiltonianVectorField_smul`: at a critical point, the linearized
  flow of `ε F` is the exponential `exp (t ε L)` of the linearization of `X_F`.
* `symplecticFormAt_fderiv_mpullbackWithin_hamiltonianVectorField_apply`: at a critical point,
  `σ_p(L w, u)` is the critical Hessian `Hess F (p) (w, u)`.
* `isSkewAdjoint_fderiv_mpullbackWithin_hamiltonianVectorField`: at a critical point, the
  linearization of `X_F` is skew-adjoint for `σ_p`.
* `symplecticFormAt_mfderiv_timeDependentFlowOf_hamiltonianVectorField_smul`: the linearized flow
  of `ε F` at a critical point preserves `σ_p`.
* `exists_path_mfderiv_timeDependentFlowOf_hamiltonianVectorField_smul`: these differentials form a
  path starting at the identity.
* `eventually_conleyZehnderIndex_eq_manifoldMorseIndex_sub`: for small `ε > 0`, its
  Conley–Zehnder index is `ind_p(F) - n`.
* `exists_pos_forall_conleyZehnderIndex_eq_manifoldMorseIndex_sub`: for a Morse function on a
  compact manifold and small `ε > 0`, every one-periodic orbit `γ` of `ε F` starts at a critical
  point `q = γ 0`, is nondegenerate, and has index `ind_q(F) - n`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 1 and 2 (the Hamiltonian `ε H` of a Morse function `H` and the
  grading of its Floer complex).
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 12.1 (the `C²`-small Morse Hamiltonians of the PSS
  comparison).
-/

public section

open Filter Set
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {F : M → ℝ} {p : M}

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The linearization of the Hamiltonian vector field of `ε F` at a point is `ε` times that of
`X_F`, since the field of `ε F` is `ε X_F`. -/
private theorem fderiv_mpullbackWithin_hamiltonianVectorField_smul (ε : ℝ) :
    fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
        (σ.hamiltonianVectorField (ε • F)) (range I)) (extChartAt I p p) =
      ε • fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
        (σ.hamiltonianVectorField F) (range I)) (extChartAt I p p) := by
  have hX : σ.hamiltonianVectorField (ε • F) = ε • σ.hamiltonianVectorField F :=
    funext (hamiltonianVectorField_const_smul ε)
  rw [hX, VectorField.mpullbackWithin_const_smul]
  exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := (VectorField.mpullbackWithin 𝓘(ℝ, E) I
    (extChartAt I p).symm (σ.hamiltonianVectorField F) (range I) : E → E)) ε) _

variable [T2Space M]

/-- **The linearized flow at a critical point is an exponential.** Let `σ` be a nondegenerate
two-form, `F` a `C³` function and `p` a critical point of `F`, and let `L` be the derivative at the
chart image of `p` of the coordinate expression of `X_F` in the preferred chart at `p`. For all
`ε` and `t`, the differential at `p` of the flow of the autonomous Hamiltonian `ε F` from time `0`
to time `t` is `exp (t ε L)`. -/
theorem mfderiv_timeDependentFlowOf_hamiltonianVectorField_smul (h : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) 3 F) (hcrit : mvfderiv I F p = 0) (ε t : ℝ) :
    (mfderiv I I (timeDependentFlowOf (fun _ ↦ σ.hamiltonianVectorField (ε • F)) 0 t) p :
        E →L[ℝ] E) =
      NormedSpace.exp ((t * ε) • fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I
        (extChartAt I p).symm (σ.hamiltonianVectorField F) (range I)) (extChartAt I p p)) := by
  set L := fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
    (σ.hamiltonianVectorField F) (range I)) (extChartAt I p p)
  -- The time-independent field `X_{ε F}` is jointly `C²` and vanishes at `p`.
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun q : ℝ × M ↦ (⟨q.2, σ.hamiltonianVectorField (ε • F) q.2⟩ : TangentBundle I M)) :=
    (h.contMDiff_hamiltonianVectorField (n := 2) (by simp)
      ((contDiff_const_smul ε).contMDiff.comp hF)).comp contMDiff_snd
  have hp : ∀ _ : ℝ, σ.hamiltonianVectorField (ε • F) p = 0 := fun _ ↦ by
    rw [hamiltonianVectorField_const_smul, h.hamiltonianVectorField_eq_zero_iff.2 hcrit,
      smul_zero]
  -- Name the differentials as endomorphisms of the model space `E`.
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ → E →L[ℝ] E, Ψ = fun u ↦
      mfderiv I I (timeDependentFlowOf (fun _ ↦ σ.hamiltonianVectorField (ε • F)) 0 u) p :=
    ⟨_, rfl⟩
  -- By the variational equation, `Ψ' = (ε L) Ψ`.
  have hD (u : ℝ) : HasDerivAt Ψ ((ε • L) * Ψ u) u := by
    have := hasDerivAt_mfderiv_timeDependentFlowOf_of_forall_eq_zero hX hp 0 u
    rw [fderiv_mpullbackWithin_hamiltonianVectorField_smul] at this
    subst hΨ
    exact this
  -- The solution starting at the identity is the exponential.
  have hΨ0 : Ψ 0 = 1 := by
    subst hΨ
    exact mfderiv_timeDependentFlowOf_self _ 0 p
  have hsol := eq_dysonSeriesLeft_mul continuous_const hD t
  rw [dysonSeriesLeft_const, hΨ0, mul_one, smul_smul] at hsol
  subst hΨ
  exact hsol

omit [T2Space M] in
/-- **The linearization at a critical point contracts with `σ_p` to the Hessian.** For a
nondegenerate two-form `σ`, a `C²` function `F` and a critical point `p` of `F`, let `L` be the
derivative at the chart image of `p` of the coordinate expression of `X_F` in the preferred chart
at `p`. Then `σ_p(L w, u) = Hess F (p) (w, u)`. -/
theorem symplecticFormAt_fderiv_mpullbackWithin_hamiltonianVectorField_apply
    (h : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) 2 F) (hcrit : mvfderiv I F p = 0) (w u : E) :
    h.symplecticFormAt p (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
        (σ.hamiltonianVectorField F) (range I)) (extChartAt I p p) w) u =
      criticalHessian I F p w u :=
  (h.symplecticFormAt_apply p _ u).trans (criticalHessian_apply_eq_eval₂_fderiv h hF hcrit w u).symm

omit [T2Space M] in
/-- **The linearization at a critical point is infinitesimally symplectic.** For a nondegenerate
two-form `σ`, a `C²` function `F` and a critical point `p` of `F`, the derivative at the chart
image of `p` of the coordinate expression of `X_F` in the preferred chart at `p` is skew-adjoint
for the symplectic form `σ_p` of `T_p M`. -/
theorem isSkewAdjoint_fderiv_mpullbackWithin_hamiltonianVectorField (h : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) 2 F) (hcrit : mvfderiv I F p = 0) :
    (h.symplecticFormAt p).toBilinForm.IsSkewAdjoint
      (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
        (σ.hamiltonianVectorField F) (range I)) (extChartAt I p p)) := by
  set L := fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
    (σ.hamiltonianVectorField F) (range I)) (extChartAt I p p)
  intro w u
  -- `σ_p (L w, u)` is the Hessian, which is symmetric, while `σ_p` is antisymmetric.
  have h1 := symplecticFormAt_fderiv_mpullbackWithin_hamiltonianVectorField_apply h hF hcrit w u
  have h2 := symplecticFormAt_fderiv_mpullbackWithin_hamiltonianVectorField_apply h hF hcrit u w
  have h3 : (h.symplecticFormAt p).toBilinForm w (-(L u)) =
      -(h.symplecticFormAt p).toBilinForm w (L u) :=
    map_neg _ _
  exact (h1.trans ((criticalHessian_apply_swap (hF p) w u).trans h2.symm)).trans
    (((h.symplecticFormAt p).neg_eq w (L u)).symm.trans h3.symm)

/-- **The linearized flow at a critical point is symplectic.** For a nondegenerate two-form `σ`, a
`C³` function `F` and a critical point `p` of `F`, the differential at `p` of the flow of `ε F`
from time `0` to time `t` preserves the symplectic form `σ_p` of `T_p M`. No closedness of `σ` is
needed. -/
theorem symplecticFormAt_mfderiv_timeDependentFlowOf_hamiltonianVectorField_smul
    (h : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) 3 F) (hcrit : mvfderiv I F p = 0)
    (ε t : ℝ) (u v : E) :
    h.symplecticFormAt p
        ((mfderiv I I (timeDependentFlowOf (fun _ ↦ σ.hamiltonianVectorField (ε • F)) 0 t) p :
          E →L[ℝ] E) u)
        ((mfderiv I I (timeDependentFlowOf (fun _ ↦ σ.hamiltonianVectorField (ε • F)) 0 t) p :
          E →L[ℝ] E) v) =
      h.symplecticFormAt p u v := by
  set L := fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
    (σ.hamiltonianVectorField F) (range I)) (extChartAt I p p)
  -- A multiple of a skew-adjoint operator is skew-adjoint.
  have hL := isSkewAdjoint_fderiv_mpullbackWithin_hamiltonianVectorField h
    (hF.of_le (by norm_num)) hcrit
  have hskew : (h.symplecticFormAt p).toBilinForm.IsSkewAdjoint ((t * ε) • L) := fun x y ↦
    (hL.smul (t * ε) x y).trans
      (congrArg ((h.symplecticFormAt p).toBilinForm x) (smul_neg (t * ε) (L y)))
  rw [mfderiv_timeDependentFlowOf_hamiltonianVectorField_smul h hF hcrit ε t]
  exact LinearMap.IsSkewAdjoint.apply_exp_apply_exp (V := E) hskew u v

attribute [local instance] TauCeti.normedAlgebraRatOfReal in
/-- **The path of linearized flows.** For a nondegenerate two-form `σ`, a `C³` function `F` with a
critical point `p` and every `ε`, the differentials at `p` of the flow maps of `ε F` from time `0`
to the times `t ∈ [0, 1]`, as operators of the model space `E` of `T_p M`, form a path starting at
the identity. -/
theorem exists_path_mfderiv_timeDependentFlowOf_hamiltonianVectorField_smul
    (h : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) 3 F) (hcrit : mvfderiv I F p = 0) (ε : ℝ) :
    ∃ (B : E →L[ℝ] E) (Ψ : Path 1 B), ∀ t : unitInterval, Ψ t =
      (mfderiv I I (timeDependentFlowOf (fun _ ↦ σ.hamiltonianVectorField (ε • F)) 0 t) p :
        E →L[ℝ] E) := by
  set L := fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
    (σ.hamiltonianVectorField F) (range I)) (extChartAt I p p)
  let Ψ : Path (1 : E →L[ℝ] E) (NormedSpace.exp ((1 * ε) • L)) :=
    { toFun := fun t ↦ NormedSpace.exp (((t : ℝ) * ε) • L)
      continuous_toFun := NormedSpace.exp_continuous.comp
        ((continuous_subtypeVal.mul continuous_const).smul continuous_const)
      source' := by simp
      target' := by simp }
  exact ⟨_, Ψ, fun t ↦
    (mfderiv_timeDependentFlowOf_hamiltonianVectorField_smul h hF hcrit ε t).symm⟩

/-- **The Conley–Zehnder index of the constant orbits of a small Hamiltonian on a manifold.** Let
`σ` be a nondegenerate two-form on a boundaryless manifold of dimension `2n` and `p` a
nondegenerate critical point of a `C³` function `F`. For every small `ε > 0`, the path
`t ↦ dφ_{0,t}(p)`, `t ∈ [0, 1]`, of the differentials at `p` of the flow maps of `ε F`, a path of
linear symplectic maps of `(T_p M, σ_p)`, has Conley–Zehnder index `ind_p(F) - n`. The index is
taken on the model space `E` of `T_p M`, which carries the norm. Such paths exist by
`exists_path_mfderiv_timeDependentFlowOf_hamiltonianVectorField_smul`, and preserve `σ_p` by
`symplecticFormAt_mfderiv_timeDependentFlowOf_hamiltonianVectorField_smul`. -/
theorem eventually_conleyZehnderIndex_eq_manifoldMorseIndex_sub (h : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) 3 F) (hp : IsManifoldNondegenerateCriticalPoint I F p) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ {A B : E →L[ℝ] E} (Ψ : Path A B)
      (hΨ : ∀ t u v, h.symplecticFormAt p (Ψ t u) (Ψ t v) = h.symplecticFormAt p u v),
      (∀ t : unitInterval, Ψ t = (mfderiv I I
        (timeDependentFlowOf (fun _ ↦ σ.hamiltonianVectorField (ε • F)) 0 t) p : E →L[ℝ] E)) →
      SymplecticForm.conleyZehnderIndex (V := E) (h.symplecticFormAt p) Ψ hΨ =
        manifoldMorseIndex I F p - (Module.finrank ℝ E : ℝ) / 2 := by
  have hF2 : ContMDiff I 𝓘(ℝ) 2 F := hF.of_le (by norm_num)
  have hcrit := (isManifoldNondegenerateCriticalPoint_iff_criticalHessian.1 hp).2.1
  -- `σ_p (L w, u)` is the critical Hessian, which is symmetric and nondegenerate.
  have hQnd : (criticalHessian I F p).toBilinForm.Nondegenerate :=
    ContinuousLinearMap.isInvertible_iff_nondegenerate_toBilinForm.1
      hp.isInvertible_criticalHessian
  -- The linearized flow is `exp (t ε L)`, so the coordinate-free normalization applies.
  filter_upwards [SymplecticForm.eventually_conleyZehnderIndex_eq_sigNeg_sub (V := E)
    (h.symplecticFormAt p)
    (symplecticFormAt_fderiv_mpullbackWithin_hamiltonianVectorField_apply h hF2 hcrit)
    (isSymm_toBilinForm_criticalHessian (hF2 p)) hQnd]
    with ε hε A B Ψ hΨ hΨt
  rw [hε Ψ hΨ fun t ↦ (hΨt t).trans
      (mfderiv_timeDependentFlowOf_hamiltonianVectorField_smul h hF hcrit ε t),
    manifoldMorseIndex_eq_sigNeg_criticalHessian]
  -- The two sides differ only in reading the model space `E` as `TangentSpace I p`.
  rfl

/-- **The grading of the generators of the Floer complex of a small Morse Hamiltonian.** Let `σ`
be a nondegenerate two-form on a compact boundaryless manifold of dimension `2n` and `F` a Morse
function. There is `ε₀ > 0` such that for `0 < ε ≤ ε₀` every one-periodic orbit `γ` of the
autonomous Hamiltonian `ε F` starts at a critical point `γ 0` of `F`, is nondegenerate, and the path
of the differentials at `γ 0` of the flow maps of `ε F` from time `0` to the times `t ∈ [0, 1]`
has Conley–Zehnder index `ind_{γ 0}(F) - n`. -/
theorem exists_pos_forall_conleyZehnderIndex_eq_manifoldMorseIndex_sub [CompactSpace M]
    (h : σ.IsNondegenerate) (hF : IsMorse I F) :
    ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ γ ∈ periodicSolutions (fun _ ↦ σ.hamiltonianVectorField (ε • F)) 1,
        γ 0 ∈ criticalPoints I F ∧
        IsNondegenerateFixedPt I
          (timeDependentFlowOf (fun _ ↦ σ.hamiltonianVectorField (ε • F)) 0 1) (γ 0) ∧
        ∀ {A B : E →L[ℝ] E} (Ψ : Path A B)
          (hΨ : ∀ t u v, h.symplecticFormAt (γ 0) (Ψ t u) (Ψ t v) =
            h.symplecticFormAt (γ 0) u v),
          (∀ t : unitInterval, Ψ t = (mfderiv I I
            (timeDependentFlowOf (fun _ ↦ σ.hamiltonianVectorField (ε • F)) 0 t) (γ 0) :
              E →L[ℝ] E)) →
          SymplecticForm.conleyZehnderIndex (V := E) (h.symplecticFormAt (γ 0)) Ψ hΨ =
            manifoldMorseIndex I F (γ 0) - (Module.finrank ℝ E : ℝ) / 2 := by
  have hF3 : ContMDiff I 𝓘(ℝ) 3 F := hF.contMDiff.of_le (by norm_num)
  obtain ⟨ε₀, hε₀, hper⟩ :=
    h.exists_pos_forall_periodicSolutions_hamiltonianVectorField_smul_eq_image_criticalPoints
      (hF3.of_le (by norm_num))
  obtain ⟨ε₁, hε₁, hnd⟩ := h.exists_pos_forall_isNondegenerateFixedPt_timeDependentFlowOf_smul hF
  -- Each of the finitely many critical points has the index `ind - n` for all small `ε > 0`.
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ q ∈ criticalPoints I F,
      ∀ {A B : E →L[ℝ] E} (Ψ : Path A B)
        (hΨ : ∀ t u v, h.symplecticFormAt q (Ψ t u) (Ψ t v) = h.symplecticFormAt q u v),
        (∀ t : unitInterval, Ψ t = (mfderiv I I
          (timeDependentFlowOf (fun _ ↦ σ.hamiltonianVectorField (ε • F)) 0 t) q : E →L[ℝ] E)) →
        SymplecticForm.conleyZehnderIndex (V := E) (h.symplecticFormAt q) Ψ hΨ =
          manifoldMorseIndex I F q - (Module.finrank ℝ E : ℝ) / 2 :=
    hF.finite_criticalPoints.eventually_all.2 fun q hq ↦
      eventually_conleyZehnderIndex_eq_manifoldMorseIndex_sub h hF3
        (hF.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hq)
  obtain ⟨ε₂, hε₂, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨min (min ε₀ ε₁) (ε₂ / 2), lt_min (lt_min hε₀ hε₁) (half_pos hε₂),
    fun ε hε hεle γ hγ ↦ ?_⟩
  have hεε₀ : ε ≤ ε₀ := hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεε₁ : ε ≤ ε₁ := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεε₂ : ε < ε₂ := by linarith [min_le_right (min ε₀ ε₁) (ε₂ / 2)]
  -- The orbit is the constant orbit at a critical point.
  have hcrit : γ 0 ∈ criticalPoints I F := by
    rw [hper ε hε hεε₀] at hγ
    obtain ⟨q, hq, rfl⟩ := hγ
    exact hq
  exact ⟨hcrit, hnd ε hε hεε₁ γ hγ, hsub ⟨hε, hεε₂⟩ (γ 0) hcrit⟩

end TauCeti.SmoothTwoForm.IsNondegenerate

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Torus
public import TauCeti.Geometry.Symplectic.Hamiltonian.Integrable

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Chart

/-!
# The Liouville–Arnold action–angle theorem on torus cotangent bundles

On the cotangent bundle `T*Tⁿ` of a torus `Tⁿ = ∀ i, AddCircle (p i)` with positive periods `p i`
and canonical symplectic form `ω = -dλ = ∑ i, dθ_i ∧ dI_i`, the action coordinates
`I_i(ξ) = ξ(e_i)` form a completely integrable system whose regular set is the entire phase space
(`TauCeti.CotangentBundle.isIntegrableSystem_torusAction`). Any Hamiltonian `H(ξ) = K(I(ξ))`
depending only on the actions has Hamiltonian vector field `∑ i, (∂K/∂I_i) ∂θ_i`
(`TauCeti.CotangentBundle.hamiltonianVectorField_comp_torusAction_torusTrivializationDiffeomorph`,
`TauCeti.CotangentBundle.mfderiv_proj_hamiltonianVectorField_comp_torusAction`), so its integral
curves wind linearly around each invariant action torus with constant angular frequencies
`∂K/∂I_i` (`TauCeti.CotangentBundle.isMIntegralCurve_torusTrivializationDiffeomorph`).

Combining the local period-`2π` covering parametrization around a compact regular level component
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact`)
with the rescaled covering projection `TauCeti.CotangentBundle.torusCover` yields the
**Liouville–Arnold action–angle theorem** onto `T*Tⁿ`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle_of_isCompact`,
`TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`): near any compact connected component `L`
of a level `F⁻¹(F x₀)` consisting of regular points of a smooth pairwise-commuting family `F` of
half the dimension of `M` (with no completeness hypothesis on the Hamiltonian vector fields), there
are an open neighbourhood `U ⊇ L`, an open action domain `D` and an injective local diffeomorphism
`φ : U → T*Tⁿ` onto `{ξ | I(ξ) ∈ D}` pulling the canonical symplectic form back to `σ` and carrying
`F` into a local diffeomorphism `h` of the actions.

Finally, any such action–angle chart embeds a torus smoothly with injective differentials into the
level component (`TauCeti.exists_contMDiff_injective_torus_of_actionAngle`), showing that neither
regularity nor compactness can be omitted: action–angle coordinates fail at the critical origin of
the harmonic oscillator (`TauCeti.not_exists_actionAngle_harmonicOscillator_zero`) and along the
noncompact regular line levels of `f(q, p) = p` on `ℝ²` (`TauCeti.not_exists_actionAngle_snd`).

## Main results

* `TauCeti.CotangentBundle.hamiltonianVectorField_comp_torusAction_torusTrivializationDiffeomorph`:
  the Hamiltonian vector field of `K ∘ I` on `T*Tⁿ` is `∑ i, (∂K/∂I_i) ∂θ_i`.
* `TauCeti.CotangentBundle.isMIntegralCurve_torusTrivializationDiffeomorph`: linear flows on
  invariant tori solve Hamilton's equations for `K ∘ I`.
* `TauCeti.CotangentBundle.isIntegrableSystem_torusAction`: the action coordinates on `T*Tⁿ` form a
  completely integrable system.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle_of_isCompact`: general Liouville–Arnold
  action–angle coordinates on `T*(∀ i, AddCircle (p i))` for arbitrary finite index types and
  positive periods.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`: the `Fin n` specialization with uniform
  period `p > 0`.
* `TauCeti.not_exists_actionAngle_harmonicOscillator_zero`,
  `TauCeti.not_exists_actionAngle_snd`: sharpness of the regularity and compactness hypotheses.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50.
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1.
-/

public section

noncomputable section

open Bundle Function Module Real Set
open scoped ContDiff Manifold Topology

namespace TauCeti

/-! ### The canonical integrable system and linear torus flows on `T*Tⁿ` -/

namespace CotangentBundle

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

private theorem mvfderiv_comp_torusAction_torusTrivializationDiffeomorph
    {K : (ι → ℝ) → ℝ} (θ : ∀ i, AddCircle (p i)) {c : ι → ℝ} (hK : DifferentiableAt ℝ K c)
    (a b : ι → ℝ) :
    mvfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (fun z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ↦
        K (fun i ↦ z.2 (Pi.single i 1)))
      (torusTrivializationDiffeomorph p (θ, c))
      (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (torusTrivializationDiffeomorph p) (θ, c)
        ((Manifold.tangentSpaceProdEquiv (θ, c)).symm (a, b))) =
      fderiv ℝ K c b := by
  let act : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) →
      ι → ℝ := fun z i ↦ z.2 (Pi.single i 1)
  let v₀ : TangentSpace ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ)) (θ, c) :=
    (Manifold.tangentSpaceProdEquiv (θ, c)).symm (a, b)
  have hact : MDifferentiableAt
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) 𝓘(ℝ, ι → ℝ) act
      (torusTrivializationDiffeomorph p (θ, c)) :=
    (contMDiff_torusAction p _).mdifferentiableAt (by simp)
  have he : MDifferentiableAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusTrivializationDiffeomorph p) (θ, c) :=
    ((torusTrivializationDiffeomorph p).contMDiff (θ, c)).mdifferentiableAt (by simp)
  have hKact : MDifferentiableAt
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) 𝓘(ℝ) (K ∘ act)
      (torusTrivializationDiffeomorph p (θ, c)) := by
    have hc : act (torusTrivializationDiffeomorph p (θ, c)) = c := by ext i; simp [act]
    exact (hc ▸ hK.mdifferentiableAt).comp _ hact
  have hcomp : (K ∘ act) ∘ torusTrivializationDiffeomorph p = K ∘ Prod.snd := by
    ext q
    simp [act]
  have hsnd : MDifferentiableAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      𝓘(ℝ, ι → ℝ) Prod.snd (θ, c) := mdifferentiableAt_snd
  change mvfderiv _ (K ∘ act) (torusTrivializationDiffeomorph p (θ, c))
    (mfderiv _ _ (torusTrivializationDiffeomorph p) (θ, c) v₀) = fderiv ℝ K c b
  rw [mvfderiv_apply_eq_mfderiv_apply, ← mfderiv_comp_apply (θ, c) hKact he v₀, hcomp,
    mfderiv_comp_apply (θ, c) hK.mdifferentiableAt hsnd v₀, mfderiv_snd]
  simp only [v₀, Manifold.tangentSpaceProdEquiv_symm_apply, mfderiv_eq_fderiv]
  rfl

/-- **Action-dependent Hamiltonians generate constant angular frequencies.** At
`torusTrivializationDiffeomorph p (θ, c)`, the Hamiltonian vector field of
`z ↦ K (fun i ↦ z.2 (Pi.single i 1))` is the pushforward of `((∂K/∂I_i(c))_i, 0)`. -/
theorem hamiltonianVectorField_comp_torusAction_torusTrivializationDiffeomorph
    {K : (ι → ℝ) → ℝ} (θ : ∀ i, AddCircle (p i)) {c : ι → ℝ} (hK : DifferentiableAt ℝ K c) :
    SmoothTwoForm.hamiltonianVectorField
        (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
        (fun z ↦ K (fun i ↦ z.2 (Pi.single i 1)))
        (torusTrivializationDiffeomorph p (θ, c)) =
      mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (torusTrivializationDiffeomorph p) (θ, c)
        ((Manifold.tangentSpaceProdEquiv (θ, c)).symm
          (fun i ↦ fderiv ℝ K c (Pi.single i 1), 0)) := by
  have hω := isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
    (M := ∀ i, AddCircle (p i))
  apply (hω.isNondegenerate.isInvertible_flat (torusTrivializationDiffeomorph p (θ, c))).injective
  rw [hω.isNondegenerate.flat_hamiltonianVectorField]
  ext w
  obtain ⟨u, rfl⟩ :=
    (((torusTrivializationDiffeomorph p).isLocalDiffeomorph (θ, c)).isInvertible_mfderiv
      (by simp)).surjective w
  obtain ⟨⟨a, b⟩, rfl⟩ := (Manifold.tangentSpaceProdEquiv (θ, c)).symm.surjective u
  let a' : ι → ℝ := a
  let b' : ι → ℝ := b
  refine (mvfderiv_comp_torusAction_torusTrivializationDiffeomorph p θ hK a' b').trans ?_
  rw [SmoothTwoForm.flat_apply,
    ← SmoothForm.eval₂_mpullback (torusTrivializationDiffeomorph p)
      (torusTrivializationDiffeomorph p).contMDiff]
  refine Eq.trans ?_
    (eval₂_mpullback_torusTrivializationDiffeomorph_symplecticForm p (θ, c)
      (fun i ↦ fderiv ℝ K c (Pi.single i 1)) a' 0 b').symm
  have hb : b' = ∑ i, b' i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hb, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, smul_eq_mul, Pi.zero_apply, mul_zero, sub_zero, mul_comm]

/-- **Base projection of an action-dependent Hamiltonian vector field.** At any covector `z` of
`T*Tⁿ`, the base projection maps the Hamiltonian vector field of `w ↦ K (fun i ↦ w.2 (e_i))` to the
angular frequency vector `i ↦ ∂K/∂I_i`. -/
theorem mfderiv_proj_hamiltonianVectorField_comp_torusAction
    {K : (ι → ℝ) → ℝ}
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
    (hK : DifferentiableAt ℝ K (fun i ↦ z.2 (Pi.single i 1))) :
    mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (π ((ι → ℝ) →L[ℝ] ℝ)
        (fun x : ∀ i, AddCircle (p i) ↦
          TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x →L[ℝ] ℝ)) z
      (SmoothTwoForm.hamiltonianVectorField
        (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
        (fun w ↦ K (fun i ↦ w.2 (Pi.single i 1))) z) =
      (fun i ↦ fderiv ℝ K (fun j ↦ z.2 (Pi.single j 1)) (Pi.single i 1) :
        TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) z.proj) := by
  obtain ⟨⟨θ, c⟩, rfl⟩ := EquivLike.surjective (torusTrivializationDiffeomorph p) z
  have hact : (fun j ↦ (torusTrivializationDiffeomorph p (θ, c)).2 (Pi.single j 1)) = c := by
    ext j
    simp
  have hKc : DifferentiableAt ℝ K c := hact ▸ hK
  have hproj : (π ((ι → ℝ) →L[ℝ] ℝ)
      (fun x : ∀ i, AddCircle (p i) ↦
        TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x →L[ℝ] ℝ)) ∘
      torusTrivializationDiffeomorph p = Prod.fst := by
    ext x
    simp
  have hp_smooth : ContMDiff
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞
      (π ((ι → ℝ) →L[ℝ] ℝ)
        (fun x : ∀ i, AddCircle (p i) ↦
          TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x →L[ℝ] ℝ)) :=
    contMDiff_proj _
  have hfst : mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) Prod.fst (θ, c)
      ((Manifold.tangentSpaceProdEquiv (θ, c)).symm
        (fun i ↦ fderiv ℝ K c (Pi.single i 1), 0)) =
      (fun i ↦ fderiv ℝ K c (Pi.single i 1) :
        TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (θ, c).1) := by
    rw [mfderiv_fst, Manifold.tangentSpaceProdEquiv_symm_apply]
    rfl
  let v₀ : TangentSpace ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ)) (θ, c) :=
    (Manifold.tangentSpaceProdEquiv (θ, c)).symm (fun i ↦ fderiv ℝ K c (Pi.single i 1), 0)
  have hcomp_apply : @Eq (ι → ℝ)
      (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (π ((ι → ℝ) →L[ℝ] ℝ)
          (fun x : ∀ i, AddCircle (p i) ↦
            TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x →L[ℝ] ℝ))
        (torusTrivializationDiffeomorph p (θ, c))
        (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (torusTrivializationDiffeomorph p) (θ, c) v₀))
      (fun i ↦ fderiv ℝ K c (Pi.single i 1)) :=
    (mfderiv_comp_apply (θ, c) ((hp_smooth _).mdifferentiableAt (by simp))
      (((torusTrivializationDiffeomorph p).contMDiff (θ, c)).mdifferentiableAt (by simp))
      v₀).symm.trans
      ((DFunLike.congr_fun
        (mfderiv_congr (I := (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
          (I' := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (x := (θ, c)) hproj) v₀).trans hfst)
  exact (congrArg _
    (hamiltonianVectorField_comp_torusAction_torusTrivializationDiffeomorph p θ hKc)).trans
    (hcomp_apply.trans (congrArg (fun u ↦ (fun i ↦ fderiv ℝ K u (Pi.single i 1) :
      TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (torusTrivializationDiffeomorph p (θ, c)).proj)) hact.symm))

/-- **Quasiperiodic linear torus flows.** On each invariant torus `I = c` of `T*Tⁿ`, the linear
angle curve `t ↦ (θ₀ + t ω(c), c)` with `ω_i(c) = ∂K/∂I_i(c)` is an integral curve of the
Hamiltonian vector field of `K ∘ I`. -/
theorem isMIntegralCurve_torusTrivializationDiffeomorph {K : (ι → ℝ) → ℝ}
    (θ₀ : ∀ i, AddCircle (p i)) {c : ι → ℝ} (hK : DifferentiableAt ℝ K c) :
    IsMIntegralCurve
      (fun t : ℝ ↦ torusTrivializationDiffeomorph p
        (θ₀ + fun i ↦ ((t * fderiv ℝ K c (Pi.single i 1) : ℝ) : AddCircle (p i)), c))
      (SmoothTwoForm.hamiltonianVectorField
        (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
        (fun z ↦ K (fun i ↦ z.2 (Pi.single i 1)))) := by
  intro t₀
  obtain ⟨ϑ₀, rfl⟩ := AddCircle.pi_coe_surjective p θ₀
  let freq : ι → ℝ := fun i ↦ fderiv ℝ K c (Pi.single i 1)
  let base : ℝ → ∀ i, AddCircle (p i) :=
    fun t ↦ (fun i ↦ (ϑ₀ i : AddCircle (p i))) + fun i ↦ ((t * freq i : ℝ) : AddCircle (p i))
  have hbase_eq : base = (fun v : ι → ℝ ↦ fun i ↦ (v i : AddCircle (p i))) ∘
      fun t : ℝ ↦ ϑ₀ + t • freq := by
    ext t i
    simp [base, QuotientAddGroup.mk_add]
  have hlin : HasFDerivAt (fun t : ℝ ↦ ϑ₀ + t • freq)
      ((1 : ℝ →L[ℝ] ℝ).smulRight freq) t₀ := by
    have h0 := (hasFDerivAt_const (𝕜 := ℝ) ϑ₀ t₀).add
      ((hasFDerivAt_id (𝕜 := ℝ) t₀).smul_const freq)
    exact h0.congr_fderiv (ContinuousLinearMap.ext fun s ↦ funext fun i ↦ by simp)
  have hbase : HasMFDerivAt 𝓘(ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) base t₀
      ((1 : ℝ →L[ℝ] ℝ).smulRight freq) := by
    rw [hbase_eq]
    exact ((AddCircle.hasMFDerivAt_pi_coe p (ϑ₀ + t₀ • freq)).comp t₀
      hlin.hasMFDerivAt).congr_mfderiv (ContinuousLinearMap.id_comp _)
  have hconst : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) (fun _ : ℝ ↦ c) t₀ 0 := hasMFDerivAt_const c t₀
  have hpair : HasMFDerivAt 𝓘(ℝ) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      (fun t : ℝ ↦ (base t, c)) t₀ (((1 : ℝ →L[ℝ] ℝ).smulRight freq).prod 0) :=
    hbase.prodMk hconst
  have he := (((torusTrivializationDiffeomorph p).contMDiff
    (base t₀, c)).mdifferentiableAt (by simp)).hasMFDerivAt
  refine (he.comp t₀ hpair).congr_mfderiv (ContinuousLinearMap.ext fun s ↦ ?_)
  let r' : ℝ := s
  let r : ℝ := (1 : ℝ →L[ℝ] ℝ) r'
  let u_lhs : TangentSpace ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      (base t₀, c) := (((1 : ℝ →L[ℝ] ℝ).smulRight freq).prod 0) s
  let w₀ : TangentSpace ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      (base t₀, c) := (Manifold.tangentSpaceProdEquiv (base t₀, c)).symm (freq, 0)
  have hpair_eq : @Eq ((ι → ℝ) × (ι → ℝ)) u_lhs (r • (freq, (0 : ι → ℝ))) :=
    (ContinuousLinearMap.prod_apply ((1 : ℝ →L[ℝ] ℝ).smulRight freq)
      (0 : ℝ →L[ℝ] (ι → ℝ)) r').trans
      ((Prod.ext ContinuousLinearMap.smulRight_apply
        ((zero_apply r').trans (smul_zero r).symm)).trans
        (Prod.smul_mk r freq (0 : ι → ℝ)).symm)
  have hu : u_lhs = r • w₀ :=
    (Manifold.tangentSpaceProdEquiv (base t₀, c)).injective
      ((Manifold.tangentSpaceProdEquiv_apply (base t₀, c) u_lhs).trans
        (hpair_eq.trans
          ((congrArg (r • ·)
            (ContinuousLinearEquiv.apply_symm_apply
              (Manifold.tangentSpaceProdEquiv (base t₀, c)) (freq, 0))).symm.trans
            (map_smul (Manifold.tangentSpaceProdEquiv (base t₀, c)) r w₀).symm)))
  let D := mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
    ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
    (torusTrivializationDiffeomorph p) (base t₀, c)
  exact (congrArg D hu).trans ((map_smul D r w₀).trans
    (congrArg (r • ·)
      (hamiltonianVectorField_comp_torusAction_torusTrivializationDiffeomorph p (base t₀) hK).symm))

/-- Any two action-dependent functions on `T*Tⁿ` that are differentiable at the actions of `z`
have vanishing Poisson bracket at `z`. -/
theorem poissonBracket_comp_torusAction_eq_zero {K₁ K₂ : (ι → ℝ) → ℝ}
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
    (hK₁ : DifferentiableAt ℝ K₁ (fun i ↦ z.2 (Pi.single i 1)))
    (hK₂ : DifferentiableAt ℝ K₂ (fun i ↦ z.2 (Pi.single i 1))) :
    SmoothTwoForm.poissonBracket
        (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
        (fun w ↦ K₁ (fun i ↦ w.2 (Pi.single i 1)))
        (fun w ↦ K₂ (fun i ↦ w.2 (Pi.single i 1))) z = 0 := by
  obtain ⟨⟨θ, c⟩, rfl⟩ := EquivLike.surjective (torusTrivializationDiffeomorph p) z
  have hω := isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
    (M := ∀ i, AddCircle (p i))
  have hK₁' : DifferentiableAt ℝ K₁ c := by simpa using hK₁
  have hK₂' : DifferentiableAt ℝ K₂ c := by simpa using hK₂
  rw [hω.isNondegenerate.poissonBracket_eq_mvfderiv]
  exact (congrArg _
    (hamiltonianVectorField_comp_torusAction_torusTrivializationDiffeomorph p θ hK₂')).trans
    ((mvfderiv_comp_torusAction_torusTrivializationDiffeomorph p θ hK₁' _ 0).trans (map_zero _))

/-- **The action coordinates on `T*Tⁿ` Poisson-commute.** -/
@[simp]
theorem poissonBracket_torusAction_eq_zero (i j : ι)
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    SmoothTwoForm.poissonBracket
        (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
        (fun w ↦ w.2 (Pi.single i 1)) (fun w ↦ w.2 (Pi.single j 1)) z = 0 :=
  poissonBracket_comp_torusAction_eq_zero p z
    (ContinuousLinearMap.proj i).differentiableAt (ContinuousLinearMap.proj j).differentiableAt

/-- **Every covector of `T*Tⁿ` is a regular point of the action map.** -/
theorem isRegularPoint_torusAction
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    IsRegularPoint ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      𝓘(ℝ, ι → ℝ) (fun w i ↦ w.2 (Pi.single i 1)) z := by
  rw [isRegularPoint_iff]
  let e := (torusTrivializationDiffeomorph p).symm
  have hcomp : (fun w : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i)) ↦ fun i ↦ w.2 (Pi.single i 1)) = Prod.snd ∘ e := by
    ext w i
    simp [e]
  have hsnd : MDifferentiableAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      𝓘(ℝ, ι → ℝ) Prod.snd (e z) := mdifferentiableAt_snd
  rw [hcomp]
  intro b
  obtain ⟨u, hu⟩ := ((e.isLocalDiffeomorph z).isInvertible_mfderiv (by simp)).surjective
    ((Manifold.tangentSpaceProdEquiv (e z)).symm (0, b))
  have hsnd_apply : mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      𝓘(ℝ, ι → ℝ) Prod.snd (e z)
      ((Manifold.tangentSpaceProdEquiv (e z)).symm (0, b)) =
      (b : TangentSpace 𝓘(ℝ, ι → ℝ) (e z).2) := by
    rw [mfderiv_snd, Manifold.tangentSpaceProdEquiv_symm_apply]
    rfl
  refine ⟨u, (mfderiv_comp_apply z hsnd ((e.contMDiff z).mdifferentiableAt (by simp)) u).trans ?_⟩
  exact (congrArg (mfderiv _ _ Prod.snd (e z)) hu).trans hsnd_apply

/-- **The canonical integrable system on `T*Tⁿ`.** For any finite family of positive periods `p i`,
the action coordinate map `z ↦ fun i ↦ z.2 (Pi.single i 1)` is a completely integrable system on
`T*(∀ i, AddCircle (p i))` with its canonical symplectic form. -/
theorem isIntegrableSystem_torusAction :
    SmoothTwoForm.IsIntegrableSystem
      (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
      (fun z i ↦ z.2 (Pi.single i 1)) where
  contMDiff := contMDiff_torusAction p
  poissonBracket_eq_zero := poissonBracket_torusAction_eq_zero p
  dense_setOf_isRegularPoint := dense_univ.mono fun z _ ↦ isRegularPoint_torusAction p z
  two_mul_card_eq_finrank := by
    let b : Module.Basis ι ℝ ((ι → ℝ) →L[ℝ] ℝ) :=
      (Pi.basisFun ℝ ι).dualBasis.map LinearMap.toContinuousLinearMap
    rw [Module.finrank_prod, Module.finrank_eq_card_basis (Pi.basisFun ℝ ι),
      Module.finrank_eq_card_basis b, two_mul]

end CotangentBundle

/-! ### Period rescaling and the Liouville–Arnold action–angle theorem -/

section PeriodScale

private def periodScale {ι : Type*} (p : ι → ℝ) [∀ i, Fact (0 < p i)] :
    (ι → ℝ) ≃L[ℝ] (ι → ℝ) where
  toFun v i := 2 * π * (p i)⁻¹ * v i
  map_add' u v := funext fun i ↦ mul_add (2 * π * (p i)⁻¹) (u i) (v i)
  map_smul' r v := funext fun i ↦ by simp [mul_left_comm]
  invFun v i := (2 * π)⁻¹ * p i * v i
  left_inv v := funext fun i ↦ by
    have hp : p i ≠ 0 := (Fact.out : 0 < p i).ne'
    field_simp
  right_inv v := funext fun i ↦ by
    have hp : p i ≠ 0 := (Fact.out : 0 < p i).ne'
    field_simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem periodScale_apply {ι : Type*} (p : ι → ℝ) [∀ i, Fact (0 < p i)]
    (v : ι → ℝ) (i : ι) : periodScale p v i = 2 * π * (p i)⁻¹ * v i := rfl

private theorem periodScale_eq_add_two_pi_iff {ι : Type*} (p : ι → ℝ)
    [∀ i, Fact (0 < p i)] {ϑ ϑ' : ι → ℝ} :
    (∃ m : ι → ℤ, periodScale p ϑ' = periodScale p ϑ + fun i ↦ 2 * π * m i) ↔
      ∃ m : ι → ℤ, ϑ' = ϑ + fun i ↦ m i • p i := by
  refine ⟨fun ⟨m, hm⟩ ↦ ⟨m, funext fun i ↦ ?_⟩, fun ⟨m, hm⟩ ↦ ⟨m, funext fun i ↦ ?_⟩⟩
  · have hi := congrFun (congrArg (periodScale p).symm hm) i
    change ((periodScale p).symm (periodScale p ϑ')) i =
      (2 * π)⁻¹ * p i * (2 * π * (p i)⁻¹ * ϑ i + 2 * π * m i) at hi
    rw [(periodScale p).symm_apply_apply] at hi
    have hp : p i ≠ 0 := (Fact.out : 0 < p i).ne'
    rw [hi, Pi.add_apply, zsmul_eq_mul]
    field_simp
  · have hp : p i ≠ 0 := (Fact.out : 0 < p i).ne'
    rw [hm, periodScale_apply, Pi.add_apply, Pi.add_apply, periodScale_apply, zsmul_eq_mul]
    field_simp

private def prodScalePartialDiffeomorph {ι : Type*} [Fintype ι] (p : ι → ℝ)
    [∀ i, Fact (0 < p i)] (ψ : PartialDiffeomorph 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (ι → ℝ) (ι → ℝ) ∞) :
    PartialDiffeomorph 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ι → ℝ) × (ι → ℝ)) ((ι → ℝ) × (ι → ℝ)) ∞ where
  toPartialEquiv := (periodScale p).toEquiv.toPartialEquiv.prod ψ.toPartialEquiv
  open_source := isOpen_univ.prod ψ.open_source
  open_target := isOpen_univ.prod ψ.open_target
  contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.2 <|
    (periodScale p).contDiff.contDiffOn.prodMap (contMDiffOn_iff_contDiffOn.1 ψ.contMDiffOn)
  contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.2 <|
    (periodScale p).symm.contDiff.contDiffOn.prodMap
      (contMDiffOn_iff_contDiffOn.1 ψ.symm.contMDiffOn)

private theorem isLocalDiffeomorphAt_congr_of_eqOn {E H M F G N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    [TopologicalSpace N] [ChartedSpace G N]
    {f g : M → N} {W : Set M} {x : M} (hf : IsLocalDiffeomorphAt I J ∞ f x)
    (hW : IsOpen W) (hxW : x ∈ W) (heq : EqOn g f W) :
    IsLocalDiffeomorphAt I J ∞ g x := by
  let Φ₀ := hf.localInverse.symm
  have hΦ₀ : EqOn f Φ₀ Φ₀.source := fun y hy ↦ by
    have h1 : hf.localInverse (Φ₀ y) = y := Φ₀.left_inv hy
    have h2 := hf.localInverse_right_inv (Φ₀.map_source hy)
    rwa [h1] at h2
  have hx_src : x ∈ (Φ₀.restrOpen W hW).source := by
    rw [Φ₀.restrOpen_source hW]
    exact ⟨hf.localInverse_mem_target, hxW⟩
  refine isLocalDiffeomorphAt_of_eqOn (Φ := Φ₀.restrOpen W hW) hx_src fun y hy ↦ ?_
  rw [Φ₀.restrOpen_source hW] at hy
  rw [Φ₀.coe_restrOpen hW]
  exact (heq hy.2).trans (hΦ₀ hy.1)

end PeriodScale

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem eval₂_mfderiv_rescaledAngleMap {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι]
    (p : ι → ℝ) [∀ i, Fact (0 < p i)] {Ψ : (ι → ℝ) × (ι → ℝ) → M} {A : (ι → ℝ) → ι → ℝ}
    {ψ : PartialDiffeomorph 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (ι → ℝ) (ι → ℝ) ∞}
    {ϑ J : ι → ℝ} (hJ : J ∈ ψ.source) (hA_diff : DifferentiableAt ℝ A (ψ J))
    (hAψ : ∀ J' ∈ ψ.source, periodScale p (A (ψ J')) = J')
    (hΨ_loc : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ (periodScale p ϑ, ψ J))
    (hΨ_pull : ∀ a a' b b', SmoothBundleForm.eval₂ σ (Ψ (periodScale p ϑ, ψ J))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (periodScale p ϑ, ψ J) (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (periodScale p ϑ, ψ J) (a', b')) =
      ∑ i, (a i * fderiv ℝ (fun c ↦ A c i) (ψ J) b' -
        a' i * fderiv ℝ (fun c ↦ A c i) (ψ J) b))
    (a a' b b' : ι → ℝ) :
    SmoothBundleForm.eval₂ σ ((Ψ ∘ Prod.map (periodScale p) ψ) (ϑ, J))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (Ψ ∘ Prod.map (periodScale p) ψ) (ϑ, J) (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (Ψ ∘ Prod.map (periodScale p) ψ) (ϑ, J) (a', b')) =
      ∑ i, (a i * b' i - a' i * b i) := by
  have hψJ : DifferentiableAt ℝ ψ J :=
    ((ψ.contMDiffOn J hJ).contMDiffAt (ψ.open_source.mem_nhds hJ) |>.mdifferentiableAt
      (by simp)).differentiableAt
  have hprod : HasFDerivAt (Prod.map (periodScale p) ψ)
      (((periodScale p).toContinuousLinearMap).prodMap (fderiv ℝ ψ J)) (ϑ, J) :=
    (periodScale p).hasFDerivAt.prodMap (ϑ, J) hψJ.hasFDerivAt
  have hmd (u v : ι → ℝ) : mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I
      (Ψ ∘ Prod.map (periodScale p) ψ) (ϑ, J) (u, v) =
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (periodScale p ϑ, ψ J)
        (periodScale p u, fderiv ℝ ψ J v) := by
    let uv : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (ϑ, J) := (u, v)
    change mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (Ψ ∘ Prod.map (periodScale p) ψ) (ϑ, J) uv = _
    rw [mfderiv_comp_apply (ϑ, J) (hΨ_loc.mdifferentiableAt (by simp))
      hprod.hasMFDerivAt.mdifferentiableAt uv, hprod.hasMFDerivAt.mfderiv]
    rfl
  have hchain (i : ι) (v : ι → ℝ) :
      2 * π * (p i)⁻¹ * fderiv ℝ (fun c ↦ A c i) (ψ J) (fderiv ℝ ψ J v) = v i := by
    have hev : (fun J' ↦ 2 * π * (p i)⁻¹ * A (ψ J') i) =ᶠ[𝓝 J]
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) :=
      Filter.eventually_of_mem (ψ.open_source.mem_nhds hJ) fun J' hJ' ↦ congrFun (hAψ J' hJ') i
    have hAi : HasFDerivAt (fun c ↦ A c i) (fderiv ℝ (fun c ↦ A c i) (ψ J)) (ψ J) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).differentiableAt.comp (ψ J)
        hA_diff).hasFDerivAt
    have hcomp_fd : HasFDerivAt (fun J' ↦ 2 * π * (p i)⁻¹ * A (ψ J') i)
        ((2 * π * (p i)⁻¹) • ((fderiv ℝ (fun c ↦ A c i) (ψ J)).comp (fderiv ℝ ψ J))) J :=
      (hAi.comp J hψJ.hasFDerivAt).const_mul (2 * π * (p i)⁻¹)
    have hf : (2 * π * (p i)⁻¹) • ((fderiv ℝ (fun c ↦ A c i) (ψ J)).comp (fderiv ℝ ψ J)) =
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i :=
      (hcomp_fd.congr_of_eventuallyEq hev.symm).unique
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasFDerivAt
    simpa [smul_eq_mul] using DFunLike.congr_fun hf v
  rw [hmd a b, hmd a' b']
  refine (hΨ_pull (periodScale p a) (periodScale p a') (fderiv ℝ ψ J b) (fderiv ℝ ψ J b')).trans ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  calc
    periodScale p a i * fderiv ℝ (fun c ↦ A c i) (ψ J) (fderiv ℝ ψ J b') -
        periodScale p a' i * fderiv ℝ (fun c ↦ A c i) (ψ J) (fderiv ℝ ψ J b)
      = a i * (2 * π * (p i)⁻¹ * fderiv ℝ (fun c ↦ A c i) (ψ J) (fderiv ℝ ψ J b')) -
          a' i * (2 * π * (p i)⁻¹ * fderiv ℝ (fun c ↦ A c i) (ψ J) (fderiv ℝ ψ J b)) := by
        rw [periodScale_apply, periodScale_apply]; ring
    _ = a i * b' i - a' i * b i := by rw [hchain i b', hchain i b]

private theorem exists_rescaledActionDiffeomorph {ι : Type*} [Fintype ι]
    (p : ι → ℝ) [∀ i, Fact (0 < p i)] {A : (ι → ℝ) → ι → ℝ} {U₀ : Set (ι → ℝ)} {c₀ : ι → ℝ}
    (hU₀ : IsOpen U₀) (hc₀ : c₀ ∈ U₀)
    (hA : IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ A c₀) :
    ∃ ψ : PartialDiffeomorph 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (ι → ℝ) (ι → ℝ) ∞,
      c₀ ∈ ψ.target ∧
      (∀ J ∈ ψ.source, ψ J ∈ U₀ ∧ DifferentiableAt ℝ A (ψ J)) ∧
      ∀ J ∈ ψ.source, periodScale p (A (ψ J)) = J := by
  obtain ⟨U_A, hU_A_loc, hU_A, hcU_A⟩ := eventually_nhds_iff.1 hA.eventually
  have hS : IsLocalDiffeomorph 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ (periodScale p) := by
    simpa using ((periodScale p).toContDiffDiffeomorph ∞).isLocalDiffeomorph
  have hA' : IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ (periodScale p ∘ A) c₀ :=
    hA.comp (hg := hS (A c₀))
  let ψ : PartialDiffeomorph 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (ι → ℝ) (ι → ℝ) ∞ :=
    (hA'.localInverse.symm.restrOpen (U₀ ∩ U_A) (hU₀.inter hU_A)).symm
  have hψ_tgt : ψ.target = hA'.localInverse.target ∩ (U₀ ∩ U_A) := by simp [ψ]
  have hψ_src : ψ.source = hA'.localInverse.source ∩ hA'.localInverse ⁻¹' (U₀ ∩ U_A) := by
    simp [ψ]
  have hψ_coe : ⇑ψ = ⇑hA'.localInverse := by simp [ψ]
  refine ⟨ψ, hψ_tgt.symm ▸ ⟨hA'.localInverse_mem_target, hc₀, hcU_A⟩, fun J hJ ↦ ?_,
    fun J hJ ↦ ?_⟩
  · have ht : ψ J ∈ ψ.target := ψ.map_source hJ
    rw [hψ_tgt] at ht
    exact ⟨ht.2.1, ((hU_A_loc _ ht.2.2).mdifferentiableAt (by simp)).differentiableAt⟩
  · rw [hψ_src] at hJ
    rw [hψ_coe]
    exact hA'.localInverse_right_inv hJ.1

private theorem eval₂_mfderiv_descendedTorusChart {σ : SmoothTwoForm I M}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) [∀ i, Fact (0 < p i)] {Ψ : (ι → ℝ) × (ι → ℝ) → M} {A : (ι → ℝ) → ι → ℝ}
    {ψ : PartialDiffeomorph 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (ι → ℝ) (ι → ℝ) ∞}
    {Ξ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) → M}
    (hΞ_loc : IsLocalDiffeomorphOn
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I ∞ Ξ
      {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ ψ.source})
    (hΞcov : ∀ ϑ, ∀ J ∈ ψ.source,
      Ξ (CotangentBundle.torusCover p (ϑ, J)) = (Ψ ∘ Prod.map (periodScale p) ψ) (ϑ, J))
    (hA_diff : ∀ J ∈ ψ.source, DifferentiableAt ℝ A (ψ J))
    (hAψ : ∀ J ∈ ψ.source, periodScale p (A (ψ J)) = J)
    (hΨ_loc : ∀ J ∈ ψ.source, ∀ θ,
      IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ (θ, ψ J))
    (hΨ_pull : ∀ J ∈ ψ.source, ∀ θ a a' b b',
      SmoothBundleForm.eval₂ σ (Ψ (θ, ψ J))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (θ, ψ J) (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (θ, ψ J) (a', b')) =
      ∑ i, (a i * fderiv ℝ (fun c ↦ A c i) (ψ J) b' -
        a' i * fderiv ℝ (fun c ↦ A c i) (ψ J) b))
    (ξ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
    (hξ : (fun i ↦ ξ.2 (Pi.single i 1)) ∈ ψ.source) (u w) :
    SmoothBundleForm.eval₂ σ (Ξ ξ)
        (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I Ξ ξ u)
        (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I Ξ ξ w) =
      SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (∀ i, AddCircle (p i))) ξ u w := by
  obtain ⟨⟨ϑ, J⟩, rfl⟩ := CotangentBundle.torusCover_surjective p ξ
  have hJ : J ∈ ψ.source := by
    simpa only [CotangentBundle.torusCover_snd_apply_single] using hξ
  have hcov := CotangentBundle.isLocalDiffeomorph_torusCover p (ϑ, J)
  obtain ⟨⟨a, b⟩, rfl⟩ := (hcov.isInvertible_mfderiv (by simp)).surjective u
  obtain ⟨⟨a', b'⟩, rfl⟩ := (hcov.isInvertible_mfderiv (by simp)).surjective w
  have hev : Ξ ∘ CotangentBundle.torusCover p =ᶠ[𝓝 (ϑ, J)] Ψ ∘ Prod.map (periodScale p) ψ :=
    Filter.eventually_of_mem ((isOpen_univ.prod ψ.open_source).mem_nhds ⟨mem_univ ϑ, hJ⟩)
      fun y hy ↦ hΞcov y.1 y.2 hy.2
  have hmd (u₀ v₀ : ι → ℝ) :
      @Eq E
        (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I Ξ
          (CotangentBundle.torusCover p (ϑ, J))
          (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
            ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
            (CotangentBundle.torusCover p) (ϑ, J) (u₀, v₀)))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (Ψ ∘ Prod.map (periodScale p) ψ) (ϑ, J) (u₀, v₀)) := by
    let uv₀ : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (ϑ, J) := (u₀, v₀)
    change @Eq E
      (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I Ξ
        (CotangentBundle.torusCover p (ϑ, J))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (CotangentBundle.torusCover p) (ϑ, J) uv₀))
      (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (Ψ ∘ Prod.map (periodScale p) ψ) (ϑ, J) uv₀)
    rw [← mfderiv_comp_apply (ϑ, J)
      ((hΞ_loc ⟨CotangentBundle.torusCover p (ϑ, J), hξ⟩).mdifferentiableAt (by simp))
      (hcov.mdifferentiableAt (by simp)) uv₀, hev.mfderiv_eq]
    rfl
  have hy : ∀ y, y = (Ψ ∘ Prod.map (periodScale p) ψ) (ϑ, J) →
      ∀ v₁ v₂ : TangentSpace I y,
      SmoothBundleForm.eval₂ σ y v₁ v₂ =
        SmoothBundleForm.eval₂ σ (Ψ (periodScale p ϑ, ψ J)) v₁ v₂ := by
    rintro _ rfl _ _
    rfl
  exact (hy _ (hΞcov ϑ J hJ) _ _).trans
    ((congrArg₂ (SmoothBundleForm.eval₂ σ (Ψ (periodScale p ϑ, ψ J))) (hmd a b) (hmd a' b')).trans
      ((eval₂_mfderiv_rescaledAngleMap p hJ (hA_diff J hJ) hAψ
        (hΨ_loc J hJ (periodScale p ϑ)) (hΨ_pull J hJ (periodScale p ϑ)) a a' b b').trans
      (CotangentBundle.eval₂_symplecticForm_mfderiv_torusCover p (ϑ, J) a a' b b').symm))

private theorem exists_inverse_torusChart [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
    (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x₀ : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x₀}) x₀, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x₀}) x₀))
    (p : ι → ℝ) [∀ i, Fact (0 < p i)] :
    ∃ (D : Set (ι → ℝ))
      (ψ : PartialDiffeomorph 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (ι → ℝ) (ι → ℝ) ∞)
      (Ξ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) → M),
      D = ψ.source ∧ F x₀ ∈ ψ.target ∧
      InjOn Ξ {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D} ∧
      IsLocalDiffeomorphOn
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I ∞ Ξ
        {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D} ∧
      Ξ '' {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) = ψ.symm (F x₀)} =
        connectedComponentIn (F ⁻¹' {F x₀}) x₀ ∧
      (∀ ξ, (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D →
        F (Ξ ξ) = ψ (fun i ↦ ξ.2 (Pi.single i 1))) ∧
      ∀ ξ, (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D →
        ∀ u w, SmoothBundleForm.eval₂ σ (Ξ ξ)
            (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I Ξ ξ u)
            (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I Ξ ξ w) =
          SmoothBundleForm.eval₂
            (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
              (∀ i, AddCircle (p i))) ξ u w := by
  obtain ⟨Ψ, A, U₀, hU₀, hxU₀, hA, hrange, hU₀c⟩ :=
    hσ.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact hF hcomm hdim hreg hK
  obtain ⟨ψ, hx_tgt, hψU₀, hAψ⟩ := exists_rescaledActionDiffeomorph p hU₀ hxU₀ hA
  let Ψ' : (ι → ℝ) × (ι → ℝ) → M := Ψ ∘ Prod.map (periodScale p) ψ
  let liftPt (ξ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
      (ι → ℝ) × (ι → ℝ) := Classical.choose (CotangentBundle.torusCover_surjective p ξ)
  have hlift (ξ) : CotangentBundle.torusCover p (liftPt ξ) = ξ :=
    Classical.choose_spec (CotangentBundle.torusCover_surjective p ξ)
  let Ξ := fun ξ ↦ Ψ' (liftPt ξ)
  have hΞcov (ϑ : ι → ℝ) (J : ι → ℝ) (hJ : J ∈ ψ.source) :
      Ξ (CotangentBundle.torusCover p (ϑ, J)) = Ψ' (ϑ, J) := by
    obtain ⟨hc, m, hm⟩ := (CotangentBundle.torusCover_eq_iff (q := p)).1
      (hlift (CotangentBundle.torusCover p (ϑ, J))).symm
    have hm' := (periodScale_eq_add_two_pi_iff p).2 ⟨m, hm⟩
    exact ((hU₀c (ψ J) (hψU₀ J hJ).1).2.2.2 (ψ (liftPt _).2) (hc ▸ (hψU₀ J hJ).1) _ _).2
      ⟨congrArg ψ hc, hm'⟩ |>.symm
  have hΞ_loc : IsLocalDiffeomorphOn
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I ∞ Ξ
      {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ ψ.source} := by
    rintro ⟨ξ, hξ⟩
    obtain ⟨⟨ϑ, J⟩, rfl⟩ := CotangentBundle.torusCover_surjective p ξ
    have hJ : J ∈ ψ.source := by
      simpa only [mem_ofPred_eq, CotangentBundle.torusCover_snd_apply_single] using hξ
    have hΨ'_loc : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ' (ϑ, J) :=
      ((prodScalePartialDiffeomorph p ψ).isLocalDiffeomorphAt _ _ _
        ⟨mem_univ ϑ, hJ⟩).comp (hg := (hU₀c (ψ J) (hψU₀ J hJ).1).2.1 _)
    have hcomp_loc : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞
        (Ξ ∘ CotangentBundle.torusCover p) (ϑ, J) :=
      isLocalDiffeomorphAt_congr_of_eqOn hΨ'_loc (isOpen_univ.prod ψ.open_source)
        ⟨mem_univ ϑ, hJ⟩ fun y hy ↦ hΞcov y.1 y.2 hy.2
    exact hcomp_loc.of_comp_right (CotangentBundle.isLocalDiffeomorph_torusCover p (ϑ, J))
  refine ⟨ψ.source, ψ, Ξ, rfl, hx_tgt, ?_, hΞ_loc, ?_, ?_,
    eval₂_mfderiv_descendedTorusChart p hΞ_loc hΞcov (fun J hJ ↦ (hψU₀ J hJ).2) hAψ
      (fun J hJ ↦ (hU₀c (ψ J) (hψU₀ J hJ).1).2.1)
      (fun J hJ ↦ (hU₀c (ψ J) (hψU₀ J hJ).1).2.2.1)⟩
  · intro ξ₁ hξ₁ ξ₂ hξ₂ hEq
    obtain ⟨⟨ϑ₁, J₁⟩, rfl⟩ := CotangentBundle.torusCover_surjective p ξ₁
    obtain ⟨⟨ϑ₂, J₂⟩, rfl⟩ := CotangentBundle.torusCover_surjective p ξ₂
    have hJ₁ : J₁ ∈ ψ.source := by
      simpa only [mem_ofPred_eq, CotangentBundle.torusCover_snd_apply_single] using hξ₁
    have hJ₂ : J₂ ∈ ψ.source := by
      simpa only [mem_ofPred_eq, CotangentBundle.torusCover_snd_apply_single] using hξ₂
    rw [hΞcov ϑ₁ J₁ hJ₁, hΞcov ϑ₂ J₂ hJ₂] at hEq
    obtain ⟨hψeq, m, hm⟩ :=
      ((hU₀c (ψ J₁) (hψU₀ J₁ hJ₁).1).2.2.2 (ψ J₂) (hψU₀ J₂ hJ₂).1 _ _).1 hEq
    exact (CotangentBundle.torusCover_eq_iff (q := p)).2
      ⟨ψ.toPartialEquiv.injOn hJ₂ hJ₁ hψeq, (periodScale_eq_add_two_pi_iff p).1 ⟨m, hm⟩⟩
  · rw [← hrange]
    ext y
    refine ⟨fun ⟨ξ, hξ, hy⟩ ↦ ?_, fun ⟨θ, hy⟩ ↦ ?_⟩
    · obtain ⟨⟨ϑ, J⟩, rfl⟩ := CotangentBundle.torusCover_surjective p ξ
      have hJ : J = ψ.symm (F x₀) := by
        simpa only [mem_ofPred_eq, CotangentBundle.torusCover_snd_apply_single] using hξ
      subst hJ
      rw [← hy, hΞcov ϑ _ (ψ.symm.map_source hx_tgt)]
      exact ⟨periodScale p ϑ, by simp [Ψ', ψ.right_inv hx_tgt]⟩
    · refine ⟨CotangentBundle.torusCover p ((periodScale p).symm θ, ψ.symm (F x₀)), ?_, ?_⟩
      · simp [CotangentBundle.torusCover_snd_apply_single]
      · rw [hΞcov _ _ (ψ.symm.map_source hx_tgt)]
        simpa [Ψ', ψ.right_inv hx_tgt] using hy
  · intro ξ hξ
    obtain ⟨⟨ϑ, J⟩, rfl⟩ := CotangentBundle.torusCover_surjective p ξ
    have hJ : J ∈ ψ.source := by
      simpa only [CotangentBundle.torusCover_snd_apply_single] using hξ
    simp only [CotangentBundle.torusCover_snd_apply_single]
    rw [hΞcov ϑ J hJ]
    exact (hU₀c (ψ J) (hψU₀ J hJ).1).1 (periodScale p ϑ)

/-- **The Liouville–Arnold action–angle theorem (general periods and index type).** On a Hausdorff
boundaryless symplectic manifold `(M, σ)` of dimension `2 · |ι|`, let `F : M → ι → ℝ` be a smooth
family of pairwise Poisson-commuting functions (whose Hamiltonian vector fields need not be
complete), and let `L` be a compact connected component of `F⁻¹(F x₀)` consisting of regular points
of `F`. For any positive periods `p : ι → ℝ`, there exist an open neighbourhood `U ⊇ L`, an open
action domain `D ⊆ ι → ℝ`, an injective local diffeomorphism `φ : U → T*(∀ i, AddCircle (p i))`
onto `{ξ | (ξ(e_i))_i ∈ D}` pulling the canonical symplectic form back to `σ`, and an injective
local diffeomorphism `h : D → ι → ℝ` carrying `L` to a single action torus and satisfying
`F x = h ((φ x).2 (e_i))_i` on `U`. -/
theorem exists_actionAngle_of_isCompact [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
    (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {L : Set M} {x₀ : M}
    (hL : L = connectedComponentIn (F ⁻¹' {F x₀}) x₀) (hLc : IsCompact L)
    (hreg : ∀ x ∈ L, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x)
    (p : ι → ℝ) [∀ i, Fact (0 < p i)] :
    ∃ U : Set M, IsOpen U ∧ L ⊆ U ∧ ∃ D : Set (ι → ℝ), IsOpen D ∧
      ∃ φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)),
        InjOn φ U ∧
        IsLocalDiffeomorphOn I
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ U ∧
        φ '' U = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D} ∧
        (∀ x ∈ U, ∀ v w : TangentSpace I x,
          SmoothBundleForm.eval₂
              (CotangentBundle.symplecticForm
                (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) (φ x)
              (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
                φ x v)
              (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
                φ x w) =
            SmoothBundleForm.eval₂ σ x v w) ∧
        ∃ h : (ι → ℝ) → ι → ℝ,
          InjOn h D ∧
          IsLocalDiffeomorphOn 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ h D ∧
          (∃ c₀ ∈ D, h c₀ = F x₀ ∧ φ '' L = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) = c₀}) ∧
          ∀ x ∈ U, F x = h (fun i ↦ (φ x).2 (Pi.single i 1)) := by
  subst hL
  obtain ⟨D, ψ, Ξ, rfl, hx_tgt, hΞ_inj, hΞ_loc, hΞL, hFΞ, hΞ_pull⟩ :=
    exists_inverse_torusChart hσ hF hcomm hdim hreg hLc p
  let V : Set (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :=
    {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ ψ.source}
  have hV : IsOpen V := ψ.open_source.preimage (CotangentBundle.contMDiff_torusAction p).continuous
  have : Nonempty (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i))) := ⟨CotangentBundle.torusCover p 0⟩
  let Ξ_part := hΞ_loc.partialDiffeomorphOfInjOn hV hΞ_inj
  let Φ := Ξ_part.symm
  have hΦ_src : Φ.source = Ξ '' V := by simp [Φ, Ξ_part, V]
  have hΦ_tgt : Φ.target = V := by simp [Φ, Ξ_part, V]
  have hΦ_symm_apply (z) : Φ.toPartialEquiv.symm z = Ξ z := by simp [Φ, Ξ_part]
  have hΞΦ : ∀ y ∈ Φ.source, Ξ (Φ y) = y := fun y hy ↦ by
    have h := Φ.left_inv hy
    rwa [hΦ_symm_apply] at h
  have hc₀ : ψ.symm (F x₀) ∈ ψ.source := ψ.symm.map_source hx_tgt
  have hLV_sub : {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) = ψ.symm (F x₀)} ⊆ V := fun ξ hξ ↦ by
    change (fun i ↦ ξ.2 (Pi.single i 1)) ∈ ψ.source
    rw [mem_ofPred_eq] at hξ
    rw [hξ]
    exact hc₀
  have hLU : connectedComponentIn (F ⁻¹' {F x₀}) x₀ ⊆ Φ.source := by
    rw [← hΞL, hΦ_src]
    exact image_mono hLV_sub
  refine ⟨Φ.source, Φ.open_source, hLU, ψ.source, ψ.open_source, Φ, Φ.toPartialEquiv.injOn,
    fun x ↦ Φ.isLocalDiffeomorphAt _ _ _ x.2,
    Φ.toPartialEquiv.image_source_eq_target.trans hΦ_tgt, ?_,
    ψ, ψ.toPartialEquiv.injOn, fun c ↦ ψ.isLocalDiffeomorphAt _ _ _ c.2,
    ⟨ψ.symm (F x₀), hc₀, ψ.right_inv hx_tgt, ?_⟩, fun x hx ↦ ?_⟩
  · intro x hx v w
    have hξ : Φ x ∈ V := hΦ_tgt ▸ Φ.map_source hx
    have hev : Ξ ∘ ⇑Φ =ᶠ[𝓝 x] id := Filter.eventually_of_mem (Φ.open_source.mem_nhds hx) hΞΦ
    let J_T := (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
    have hΦ_diff : MDifferentiableAt I J_T (⇑Φ) x := Φ.mdifferentiableAt (by simp) hx
    have hmd (u : TangentSpace I x) :
        @Eq E (mfderiv J_T I Ξ (Φ x) (mfderiv I J_T (⇑Φ) x u)) u :=
      (mfderiv_comp_apply x ((hΞ_loc ⟨Φ x, hξ⟩).mdifferentiableAt (by simp)) hΦ_diff u).symm.trans
        ((DFunLike.congr_fun hev.mfderiv_eq u).trans
          (DFunLike.congr_fun (mfderiv_id (I := I) (x := x)) u))
    have hy : ∀ y, y = x → ∀ v₁ v₂ : TangentSpace I y,
        SmoothBundleForm.eval₂ σ y v₁ v₂ = SmoothBundleForm.eval₂ σ x v₁ v₂ := by
      rintro _ rfl _ _
      rfl
    exact (hΞ_pull (Φ x) hξ (mfderiv I J_T (⇑Φ) x v) (mfderiv I J_T (⇑Φ) x w)).symm.trans
      ((hy _ (hΞΦ x hx) _ _).trans
        (congrArg₂ (SmoothBundleForm.eval₂ σ x) (hmd v) (hmd w)))
  · rw [← hΞL]
    ext ξ
    have hleft {ξ'} (hξ' : ξ' ∈ V) : Φ (Ξ ξ') = ξ' := by
      have hsrc : ξ' ∈ Φ.target := hΦ_tgt.symm ▸ hξ'
      have h := Φ.right_inv hsrc
      rwa [hΦ_symm_apply] at h
    refine ⟨?_, fun hξ ↦ ⟨Ξ ξ, ⟨ξ, hξ, rfl⟩, hleft (hLV_sub hξ)⟩⟩
    rintro ⟨y, ⟨ξ', hξ', rfl⟩, hy⟩
    rw [← hy, hleft (hLV_sub hξ')]
    exact hξ'
  · have hξ : Φ x ∈ V := hΦ_tgt ▸ Φ.map_source hx
    simpa [hΞΦ x hx] using hFΞ (Φ x) hξ

/-- **The Liouville–Arnold action–angle theorem.** On a Hausdorff boundaryless symplectic manifold
`(M, σ)` with a completely integrable system `F : M → Fin n → ℝ`, let `L` be a compact connected
component of `F⁻¹(F x₀)` consisting of regular points of `F`. Then for every positive period `p`
there exist an open neighbourhood `U ⊇ L`, an open set `D ⊆ Fin n → ℝ`, an injective local
diffeomorphism `φ` on `U` onto `{ξ ∈ T*(Fin n → AddCircle p) | (ξ(e_i))_i ∈ D}` pulling the
canonical symplectic form back to `σ`, and a map `h` such that `F x = h ((φ x).2 (e_i))_i` for all
`x ∈ U`. -/
theorem exists_actionAngle [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic) {n : ℕ} {F : M → Fin n → ℝ}
    (hF : σ.IsIntegrableSystem F) {L : Set M} {x₀ : M}
    (hL : L = connectedComponentIn (F ⁻¹' {F x₀}) x₀) (hLc : IsCompact L)
    (hreg : ∀ x ∈ L, IsRegularPoint I 𝓘(ℝ, Fin n → ℝ) F x)
    (p : ℝ) [Fact (0 < p)] :
    ∃ U : Set M, IsOpen U ∧ L ⊆ U ∧ ∃ D : Set (Fin n → ℝ), IsOpen D ∧
      ∃ φ : M → CotangentBundle (ModelWithCorners.pi fun _ : Fin n ↦ 𝓘(ℝ))
          (Fin n → AddCircle p),
        InjOn φ U ∧
        IsLocalDiffeomorphOn I ((ModelWithCorners.pi fun _ : Fin n ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin n → ℝ) →L[ℝ] ℝ)) ∞ φ U ∧
        φ '' U = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D} ∧
        (∀ x ∈ U, ∀ v w : TangentSpace I x,
          SmoothBundleForm.eval₂
              (CotangentBundle.symplecticForm
                (ModelWithCorners.pi fun _ : Fin n ↦ 𝓘(ℝ)) (Fin n → AddCircle p)) (φ x)
              (mfderiv I ((ModelWithCorners.pi fun _ : Fin n ↦ 𝓘(ℝ)).prod
                𝓘(ℝ, (Fin n → ℝ) →L[ℝ] ℝ)) φ x v)
              (mfderiv I ((ModelWithCorners.pi fun _ : Fin n ↦ 𝓘(ℝ)).prod
                𝓘(ℝ, (Fin n → ℝ) →L[ℝ] ℝ)) φ x w) =
            SmoothBundleForm.eval₂ σ x v w) ∧
        ∃ h : (Fin n → ℝ) → Fin n → ℝ, ∀ x ∈ U, F x = h (fun i ↦ (φ x).2 (Pi.single i 1)) := by
  obtain ⟨U, hU, hLU, D, hD, φ, hinj, hloc, himg, hpull, h, -, -, -, hFφ⟩ :=
    hσ.exists_actionAngle_of_isCompact hF.contMDiff hF.poissonBracket_eq_zero
      hF.two_mul_card_eq_finrank hL hLc hreg (fun _ ↦ p)
  exact ⟨U, hU, hLU, D, hD, φ, hinj, hloc, himg, hpull, h, hFφ⟩

end IsSymplectic

end SmoothTwoForm

/-! ### Torus immersion into level components and sharpness of the hypotheses -/

section Sharpness

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

private theorem injective_mfderiv_torusTrivializationDiffeomorph_mk
    {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]
    (c₀ : ι → ℝ) (θ : ∀ i, AddCircle (p i)) :
    Injective
      (mfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (fun θ' ↦ CotangentBundle.torusTrivializationDiffeomorph p (θ', c₀)) θ) := by
  let sec : (∀ i, AddCircle (p i)) →
      CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) :=
    fun θ' ↦ CotangentBundle.torusTrivializationDiffeomorph p (θ', c₀)
  let proj := π ((ι → ℝ) →L[ℝ] ℝ)
    (fun x : ∀ i, AddCircle (p i) ↦
      TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x →L[ℝ] ℝ)
  have hproj_sec : proj ∘ sec = id := by ext θ'; simp [proj, sec]
  have hsec_diff : MDifferentiableAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) sec θ :=
    (((CotangentBundle.torusTrivializationDiffeomorph p).contMDiff.comp
      (contMDiff_id.prodMk contMDiff_const)) θ).mdifferentiableAt (by simp)
  have hp_smooth : ContMDiff
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ proj :=
    contMDiff_proj _
  refine Function.LeftInverse.injective
    (g := mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) proj (sec θ)) fun v ↦ ?_
  rw [← mfderiv_comp_apply θ ((hp_smooth (sec θ)).mdifferentiableAt (by simp)) hsec_diff v,
    hproj_sec, mfderiv_id]
  rfl

/-- **Action–angle coordinates immerse a torus into the level component.** Whenever an open set
`U` containing `x₀` admits an injective local diffeomorphism `φ` onto `{ξ ∈ T*Tⁿ | I(ξ) ∈ D}` along
which `F` factors through the actions, the action torus through `φ x₀` maps into the connected
component of `x₀` in `F ⁻¹' {F x₀}` by a smooth injective immersion passing through `x₀`. -/
theorem exists_contMDiff_injective_torus_of_actionAngle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) [∀ i, Fact (0 < p i)] {F : M → α} {U : Set M} (hU : IsOpen U) {x₀ : M}
    (hx₀ : x₀ ∈ U) {D : Set (ι → ℝ)}
    {φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))}
    (hinj : InjOn φ U)
    (hloc : IsLocalDiffeomorphOn I
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ U)
    (himg : φ '' U = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D})
    {h : (ι → ℝ) → α} (hFφ : ∀ x ∈ U, F x = h (fun i ↦ (φ x).2 (Pi.single i 1))) :
    ∃ τ : (∀ i, AddCircle (p i)) → M,
      ContMDiff (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) I ∞ τ ∧
      Injective τ ∧
      (∀ θ, Injective (mfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) I τ θ)) ∧
      x₀ ∈ range τ ∧
      range τ ⊆ connectedComponentIn (F ⁻¹' {F x₀}) x₀ := by
  have : Nonempty M := ⟨x₀⟩
  let Φ := hloc.partialDiffeomorphOfInjOn hU hinj
  have hΦ_src : Φ.source = U := by simp [Φ]
  have hΦ_tgt : Φ.target = φ '' U := by simp [Φ]
  have hΦ_coe : ⇑Φ = φ := by simp [Φ]
  let c₀ : ι → ℝ := fun i ↦ (φ x₀).2 (Pi.single i 1)
  have hc₀ : c₀ ∈ D := by
    have hmem : φ x₀ ∈ φ '' U := mem_image_of_mem φ hx₀
    rwa [himg] at hmem
  let sec : (∀ i, AddCircle (p i)) →
      CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) :=
    fun θ ↦ CotangentBundle.torusTrivializationDiffeomorph p (θ, c₀)
  have hsec_smooth : ContMDiff (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) _ ∞ sec :=
    (CotangentBundle.torusTrivializationDiffeomorph p).contMDiff.comp
      (contMDiff_id.prodMk contMDiff_const)
  have hsec_mem (θ) : sec θ ∈ Φ.target := by
    rw [hΦ_tgt, himg]
    simp [sec, hc₀]
  let τ : (∀ i, AddCircle (p i)) → M := Φ.symm ∘ sec
  have hτ : ContMDiff (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) I ∞ τ :=
    Φ.symm.contMDiffOn.comp_contMDiff hsec_smooth hsec_mem
  have hx₀_τ : τ (φ x₀).proj = x₀ := by
    have hsec₀ : sec (φ x₀).proj = φ x₀ := by
      simpa [sec, c₀] using
        (CotangentBundle.torusTrivializationDiffeomorph p).apply_symm_apply (φ x₀)
    have hleft : Φ.symm (φ x₀) = x₀ := by
      have h0 := Φ.left_inv (hΦ_src.symm ▸ hx₀)
      rwa [hΦ_coe] at h0
    exact (congrArg Φ.symm hsec₀).trans hleft
  have hlevel : range τ ⊆ F ⁻¹' {F x₀} := by
    rintro _ ⟨θ, rfl⟩
    have hτU : τ θ ∈ U := hΦ_src ▸ Φ.symm.map_source (hsec_mem θ)
    have hφτ : φ (τ θ) = sec θ := by
      have h0 := Φ.right_inv (hsec_mem θ)
      rwa [hΦ_coe] at h0
    have hact_eq : (fun i ↦ (φ (τ θ)).2 (Pi.single i 1)) = c₀ := by
      ext i
      rw [hφτ]
      exact CotangentBundle.torusTrivializationDiffeomorph_snd_apply_single p (θ, c₀) i
    rw [mem_preimage, mem_singleton_iff, hFφ (τ θ) hτU, hFφ x₀ hx₀, hact_eq]
  have hconn : IsPreconnected (range τ) := by
    have hsurj : range (τ ∘ fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) = range τ :=
      (AddCircle.pi_coe_surjective p).range_comp τ
    rw [← hsurj, ← image_univ]
    exact isPreconnected_univ.image _
      (hτ.continuous.comp (AddCircle.contMDiff_pi_coe p ∞).continuous).continuousOn
  refine ⟨τ, hτ, fun θ₁ θ₂ hEq ↦ ?_, fun θ v₁ v₂ hv ↦ ?_, ⟨(φ x₀).proj, hx₀_τ⟩,
    hconn.subset_connectedComponentIn ⟨(φ x₀).proj, hx₀_τ⟩ hlevel⟩
  · have hsec_eq := Φ.symm.toPartialEquiv.injOn (hsec_mem θ₁) (hsec_mem θ₂) hEq
    exact congrArg Prod.fst ((CotangentBundle.torusTrivializationDiffeomorph p).injective hsec_eq)
  · rw [mfderiv_comp_apply θ (Φ.symm.mdifferentiableAt (by simp) (hsec_mem θ))
      ((hsec_smooth θ).mdifferentiableAt (by simp)) v₁,
      mfderiv_comp_apply θ (Φ.symm.mdifferentiableAt (by simp) (hsec_mem θ))
      ((hsec_smooth θ).mdifferentiableAt (by simp)) v₂] at hv
    exact injective_mfderiv_torusTrivializationDiffeomorph_mk p c₀ θ
      (((Φ.symm.isLocalDiffeomorphAt _ _ _ (hsec_mem θ)).isInvertible_mfderiv
        (by simp)).injective hv)

/-- No positive-dimensional action–angle chart exists around a point whose level component is a
singleton. -/
theorem not_exists_actionAngle_of_connectedComponentIn_eq_singleton
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : ι → ℝ) [∀ i, Fact (0 < p i)] {F : M → α} {x₀ : M}
    (hsingle : connectedComponentIn (F ⁻¹' {F x₀}) x₀ = {x₀}) :
    ¬∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ D : Set (ι → ℝ),
      ∃ φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)),
        InjOn φ U ∧
        IsLocalDiffeomorphOn I
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ U ∧
        φ '' U = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D} ∧
        ∃ h : (ι → ℝ) → α, ∀ x ∈ U, F x = h (fun i ↦ (φ x).2 (Pi.single i 1)) := by
  rintro ⟨U, hU, hx₀, D, φ, hinj, hloc, himg, h, hFφ⟩
  obtain ⟨τ, -, -, hτ_imm, -, hsub⟩ :=
    exists_contMDiff_injective_torus_of_actionAngle p hU hx₀ hinj hloc himg hFφ
  rw [hsingle] at hsub
  have hconst : τ = fun _ ↦ x₀ := funext fun θ ↦ mem_singleton_iff.1 (hsub (mem_range_self θ))
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let θ₀ : ∀ i, AddCircle (p i) := 0
  let e₀ : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) θ₀ := Pi.single i₀ 1
  let z₀ : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) θ₀ := 0
  have hzero : mfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) I τ θ₀ e₀ =
      mfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) I τ θ₀ z₀ := by
    rw [hconst, mfderiv_const, zero_apply, zero_apply]
  have hne : e₀ ≠ z₀ := fun h0 ↦ by
    have h0' : (Pi.single i₀ (1 : ℝ) : ι → ℝ) = 0 := h0
    exact (one_ne_zero (α := ℝ)) (by simpa using congrFun h0' i₀)
  exact hne (hτ_imm θ₀ hzero)

/-- **Regularity is not removable in `exists_actionAngle`.** At the critical point `(0, 0)` of the
harmonic oscillator `H(q, p) = (q² + p²) / 2` on `ℝ²`, the level component is the compact singleton
`{(0, 0)}`, yet no action–angle chart exists for any positive period `p`. -/
theorem not_exists_actionAngle_harmonicOscillator_zero (p : ℝ) [Fact (0 < p)] :
    let F : ℝ × ℝ → Fin 1 → ℝ := fun z _ ↦ (z.1 ^ 2 + z.2 ^ 2) / 2
    connectedComponentIn (F ⁻¹' {F 0}) 0 = {0} ∧
      ¬∃ U : Set (ℝ × ℝ), IsOpen U ∧ {0} ⊆ U ∧ ∃ D : Set (Fin 1 → ℝ), IsOpen D ∧
        ∃ φ : ℝ × ℝ → CotangentBundle (ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ))
            (Fin 1 → AddCircle p),
          InjOn φ U ∧
          IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × ℝ) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
            𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) ∞ φ U ∧
          φ '' U = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D} ∧
          ∃ h : (Fin 1 → ℝ) → Fin 1 → ℝ, ∀ x ∈ U, F x = h (fun i ↦ (φ x).2 (Pi.single i 1)) := by
  intro F
  have hF0 : F 0 = 0 := by ext i; simp [F]
  have hpre : F ⁻¹' {F 0} = {0} := by
    rw [hF0]
    ext ⟨q, r⟩
    simp only [F, mem_preimage, mem_singleton_iff, funext_iff, Fin.forall_fin_one, Pi.zero_apply,
      Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
    exact ⟨fun h0 ↦ ⟨by nlinarith [sq_nonneg q, sq_nonneg r],
      by nlinarith [sq_nonneg q, sq_nonneg r]⟩, fun ⟨hq, hr⟩ ↦ by rw [hq, hr]; ring⟩
  have hcomp : connectedComponentIn (F ⁻¹' {F 0}) 0 = {0} := by
    rw [hpre]
    exact subset_antisymm (connectedComponentIn_subset _ _)
      (singleton_subset_iff.2 (mem_connectedComponentIn (mem_singleton 0)))
  refine ⟨hcomp, fun ⟨U, hU, h0U, D, _, φ, hinj, hloc, himg, h, hFφ⟩ ↦ ?_⟩
  exact not_exists_actionAngle_of_connectedComponentIn_eq_singleton (fun _ : Fin 1 ↦ p) hcomp
    ⟨U, hU, h0U (mem_singleton 0), D, φ, hinj, hloc, himg, h, hFφ⟩

/-- Every point of the phase plane `ℝ × ℝ` is a regular point of the momentum coordinate
`z ↦ fun _ : Fin 1 ↦ z.2`. -/
theorem isRegularPoint_snd (z : ℝ × ℝ) :
    IsRegularPoint 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Fin 1 → ℝ) (fun w : ℝ × ℝ ↦ fun _ : Fin 1 ↦ w.2) z := by
  rw [isRegularPoint_iff_surjective_fderiv]
  have hf : HasFDerivAt (fun w : ℝ × ℝ ↦ fun _ : Fin 1 ↦ w.2)
      (ContinuousLinearMap.pi fun _ : Fin 1 ↦ ContinuousLinearMap.snd ℝ ℝ ℝ) z :=
    hasFDerivAt_pi.2 fun _ ↦ hasFDerivAt_snd
  rw [hf.fderiv]
  exact fun v ↦ ⟨(0, v 0), funext fun i ↦ by rw [Subsingleton.elim i 0]; rfl⟩

/-- The momentum coordinate `z ↦ fun _ : Fin 1 ↦ z.2` on `(ℝ × ℝ, ω₀)` is a completely integrable
system whose levels are horizontal lines. -/
theorem isIntegrableSystem_snd :
    (stdSymplecticForm (V := ℝ)).constSmooth.IsIntegrableSystem
      fun z : ℝ × ℝ ↦ fun _ : Fin 1 ↦ z.2 where
  contMDiff := contMDiff_iff_contDiff.2 (contDiff_pi.2 fun _ ↦ contDiff_snd)
  poissonBracket_eq_zero _ _ x := SmoothTwoForm.poissonBracket_self _ _ x
  dense_setOf_isRegularPoint := dense_univ.mono fun z _ ↦ isRegularPoint_snd z
  two_mul_card_eq_finrank := by simp

/-- **Compactness is not removable in `exists_actionAngle`.** For the everywhere-regular integrable
system `F(q, p) = p` on `(ℝ × ℝ, ω₀)`, every level component is a noncompact horizontal line, and
no point `x₀` admits an action–angle chart of any positive period `p`. -/
theorem not_exists_actionAngle_snd (x₀ : ℝ × ℝ) (p : ℝ) [Fact (0 < p)] :
    let F : ℝ × ℝ → Fin 1 → ℝ := fun z _ ↦ z.2
    ¬∃ U : Set (ℝ × ℝ), IsOpen U ∧ x₀ ∈ U ∧ ∃ D : Set (Fin 1 → ℝ),
      ∃ φ : ℝ × ℝ → CotangentBundle (ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ))
          (Fin 1 → AddCircle p),
        InjOn φ U ∧
        IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × ℝ) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) ∞ φ U ∧
        φ '' U = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D} ∧
        ∃ h : (Fin 1 → ℝ) → Fin 1 → ℝ, ∀ x ∈ U, F x = h (fun i ↦ (φ x).2 (Pi.single i 1)) := by
  intro F ⟨U, hU, hx₀, D, φ, hinj, hloc, himg, h, hFφ⟩
  obtain ⟨τ, hτ, -, hτ_imm, -, hsub⟩ :=
    exists_contMDiff_injective_torus_of_actionAngle (fun _ : Fin 1 ↦ p) hU hx₀ hinj hloc himg hFφ
  let cov : ℝ → Fin 1 → AddCircle p := fun t _ ↦ (t : AddCircle p)
  have hcov : ∀ t, HasMFDerivAt 𝓘(ℝ) (ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)) cov t
      (ContinuousLinearMap.pi fun _ : Fin 1 ↦ ContinuousLinearMap.id ℝ ℝ) := fun t ↦
    TauCeti.hasMFDerivAt_pi fun _ ↦ AddCircle.hasMFDerivAt_coe p t
  let Γ : ℝ → ℝ × ℝ := τ ∘ cov
  have hΓ_diff : ∀ t, DifferentiableAt ℝ Γ t := fun t ↦
    (((hτ (cov t)).mdifferentiableAt (by simp)).comp t (hcov t).mdifferentiableAt).differentiableAt
  have hΓ2 (t : ℝ) : (Γ t).2 = x₀.2 := by
    have ht := connectedComponentIn_subset (F ⁻¹' {F x₀}) x₀ (hsub (mem_range_self (cov t)))
    exact congrFun ht 0
  have hΓ_per : (Γ 0).1 = (Γ p).1 := by
    have hcp : cov 0 = cov p := funext fun _ ↦ by simp [cov, AddCircle.coe_period]
    exact congrArg (Prod.fst ∘ τ) hcp
  have hp_pos : 0 < p := Fact.out
  obtain ⟨t₀, -, ht₀⟩ := exists_deriv_eq_zero hp_pos
    (fun t _ ↦ (continuous_fst.continuousAt.comp (hΓ_diff t).continuousAt).continuousWithinAt)
    hΓ_per
  have hf1 : (fderiv ℝ Γ t₀ 1).1 = 0 :=
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp t₀
      (hΓ_diff t₀).hasFDerivAt).hasDerivAt).deriv.symm.trans ht₀
  have hf2 : (fderiv ℝ Γ t₀ 1).2 = 0 := by
    have hconst : Prod.snd ∘ Γ = fun _ ↦ x₀.2 := funext hΓ2
    exact (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp t₀
      (hΓ_diff t₀).hasFDerivAt).hasDerivAt).deriv.symm.trans (by simp [hconst])
  have hmΓ : mfderiv 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) Γ t₀ (1 : TangentSpace 𝓘(ℝ) t₀) = 0 := by
    rw [mfderiv_eq_fderiv]
    exact Prod.ext hf1 hf2
  rw [mfderiv_comp_apply t₀ ((hτ (cov t₀)).mdifferentiableAt (by simp))
    (hcov t₀).mdifferentiableAt, (hcov t₀).mfderiv] at hmΓ
  have hne : (ContinuousLinearMap.pi fun _ : Fin 1 ↦ ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) ≠ 0 :=
    fun h0 ↦ (one_ne_zero (α := ℝ)) (by simpa using congrFun h0 0)
  exact hne (hτ_imm (cov t₀) (hmΓ.trans (map_zero _).symm))

end Sharpness

end TauCeti

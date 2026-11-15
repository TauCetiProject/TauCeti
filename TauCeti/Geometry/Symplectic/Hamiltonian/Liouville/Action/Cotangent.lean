/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Chart
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The Liouville–Arnold theorem: action–angle coordinates in the cotangent bundle of a torus

Let `σ` be a symplectic form on a boundaryless Hausdorff manifold `M` of dimension `2n`, and let
`F : M → ℝⁿ` be `n` smooth, pairwise Poisson-commuting functions, with the conventions
`ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`. Let `L` be a compact connected component of a
level `F⁻¹(c₀)` consisting of regular points of `F`; other components of the level need not be
regular, and the Hamiltonian vector fields need not be complete.

This file proves the **Liouville–Arnold theorem** in its action–angle form
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`): for every period `p > 0` there are an
open neighbourhood `U` of `L`, an open set `D ⊆ ℝⁿ` and a map `φ` from `M` to the cotangent bundle
of the torus `Tⁿ = (ℝ / pℤ)ⁿ` such that

* `φ` is injective on `U` and a local diffeomorphism there;
* `φ(U)` is the set of covectors whose actions `I_i(ξ) = ξ(e_i)` lie in `D`, that is `Tⁿ × D` in the
  action–angle coordinates of `T*Tⁿ` (`TauCeti.CotangentBundle.torusActionAngle`);
* `φ` pulls the canonical symplectic form `ω = -dλ = ∑ i, dθ_i ∧ dI_i` back to `σ`;
* along `φ`, the function `F` is a function of the actions.

For `p = 2π` these are the classical action–angle coordinates. The hypotheses on `F` are those of
an integrable system (`TauCeti.SmoothTwoForm.IsIntegrableSystem`), except that regular points need
only fill `L` rather than a dense set.

The coordinates are those of the angle map: by
`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact`
there are a local diffeomorphism `Ψ : ℝⁿ × ℝⁿ → M` near `ℝⁿ × {F x₀}`, with `F (Ψ (θ, c)) = c`,
whose fibres over a neighbourhood of `F x₀` are the orbits of `2πℤⁿ` acting on the angles `θ`,
and action variables `A`, a local diffeomorphism at `F x₀`, with `Ψ^* σ = ∑ i, dθ_i ∧ dA_i`.
Restricting to values `c` in a neighbourhood `V` of `F x₀` on which `A` is injective, the map

`G (θ, c) = ∑ i, (r⁻¹ A_i(c)) dθ_i` at the point `([r θ_i])_i` of `Tⁿ`, `r = p / 2π`,

is constant on the fibres of `Ψ`, so it descends to a map `φ` on `U = Ψ(ℝⁿ × V)` with
`φ ∘ Ψ = G`. Rescaling the angles by `r` turns the period `2π` into `p`, and rescaling the actions
by `r⁻¹` preserves `∑ i, dθ_i ∧ dA_i`. Since `G^* ω = ∑ i, dθ_i ∧ dA_i = Ψ^* σ`
(`TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_torusActionAngle`), the map `φ` pulls `ω`
back to `σ`. It is therefore an immersion, and a local diffeomorphism by the inverse function
theorem, both spaces having dimension `2n`.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`: action–angle coordinates in `T*Tⁿ` near
  a compact regular component of a level of `n` Poisson-commuting functions.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50 (the Liouville–Arnold theorem and action–angle
  variables).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4, Theorem 18.12.
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706.
-/

public section

noncomputable section

open Set Filter Module Topology Function Real
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {ι : Type*} [Fintype ι]

/-! ### The action–angle map on `ℝⁿ × ℝⁿ` -/

variable {p : ℝ} [Fact (0 < p)]

/-- The covector `∑ i, (r⁻¹ A_i(c)) dθ_i` of the torus `(ℝ / pℤ)ⁿ` at the point `([r θ_i])_i`. -/
private def angleAction (p : ℝ) [Fact (0 < p)] (r : ℝ) (A : (ι → ℝ) → ι → ℝ)
    (q : (ι → ℝ) × (ι → ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
  CotangentBundle.torusActionAngle (fun _ ↦ p)
    (fun i ↦ ((r * q.1 i : ℝ) : AddCircle p), r⁻¹ • A q.2)

/-- Translating the angles by `2π`-periods does not change the action–angle covector, for
`r = p / 2π`. -/
private theorem angleAction_add (A : (ι → ℝ) → ι → ℝ) (θ c : ι → ℝ) (m : ι → ℤ) :
    angleAction p (p / (2 * π)) A (θ + fun i ↦ 2 * π * m i, c) =
      angleAction p (p / (2 * π)) A (θ, c) := by
  unfold angleAction
  congr 2
  funext i
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨m i, ?_⟩
  simp only [Pi.add_apply, zsmul_eq_mul]
  field_simp
  ring

/-- The actions of the covector `angleAction p r A (θ, c)` are `r⁻¹ A_i(c)`. -/
private theorem angleAction_snd_apply_single [DecidableEq ι] (r : ℝ) (A : (ι → ℝ) → ι → ℝ)
    (q : (ι → ℝ) × (ι → ℝ)) (i : ι) :
    (angleAction p r A q).2 (Pi.single i 1) = r⁻¹ * A q.2 i :=
  CotangentBundle.torusActionAngle_snd_apply_single _ _ i

/-- Two angle–action pairs with the same covector have the same actions, and angles differing by
`2π`-periods, for `r = p / 2π`. -/
private theorem eq_of_angleAction_eq {A : (ι → ℝ) → ι → ℝ} {q q' : (ι → ℝ) × (ι → ℝ)}
    (h : angleAction p (p / (2 * π)) A q = angleAction p (p / (2 * π)) A q') :
    A q.2 = A q'.2 ∧ ∃ m : ι → ℤ, q'.1 = q.1 + fun i ↦ 2 * π * m i := by
  have hr : p / (2 * π) ≠ 0 := div_ne_zero (Fact.out : 0 < p).ne' (by positivity)
  obtain ⟨hθ, hA⟩ := Prod.ext_iff.mp (CotangentBundle.torusActionAngle_injective _ h)
  refine ⟨smul_right_injective _ (inv_ne_zero hr) hA, ?_⟩
  -- The angle coordinates agree modulo `p` after rescaling by `p / 2π`.
  choose m hm using fun i ↦ (AddCircle.coe_eq_zero_iff (p := p)).mp
    ((AddCircle.coe_sub (p := p) _ _).trans (sub_eq_zero.mpr (congrFun hθ i)))
  refine ⟨fun i ↦ -m i, funext fun i ↦ ?_⟩
  have h1 := hm i
  simp only [zsmul_eq_mul] at h1
  have h2 : q.1 i - q'.1 i = m i * (2 * π) := by
    apply mul_left_cancel₀ hr
    rw [mul_sub, ← h1]
    field_simp
  simp only [Pi.add_apply, Int.cast_neg]
  linarith

/-- On values where `A` is injective, two angle–action pairs have the same covector exactly when
they have the same values and angles differing by `2π`-periods, for `r = p / 2π`. -/
private theorem angleAction_eq_angleAction_iff {A : (ι → ℝ) → ι → ℝ} {V : Set (ι → ℝ)}
    (hA : InjOn A V) {θ θ' c c' : ι → ℝ} (hc : c ∈ V) (hc' : c' ∈ V) :
    angleAction p (p / (2 * π)) A (θ, c) = angleAction p (p / (2 * π)) A (θ', c') ↔
      c' = c ∧ ∃ m : ι → ℤ, θ' = θ + fun i ↦ 2 * π * m i := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨hAc, m, hθ⟩ := eq_of_angleAction_eq h
    exact ⟨hA hc' hc hAc.symm, m, hθ⟩
  · rintro ⟨rfl, m, rfl⟩
    exact (angleAction_add A θ c' m).symm

/-- For `r ≠ 0`, the covectors `angleAction p r A (θ, c)` with `c ∈ V` are exactly those whose
actions, rescaled by `r`, are values of `A` on `V`. -/
private theorem image_angleAction [DecidableEq ι] {r : ℝ} (hr : r ≠ 0) (A : (ι → ℝ) → ι → ℝ)
    (V : Set (ι → ℝ)) :
    angleAction p r A '' (univ ×ˢ V) =
      {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ (fun I ↦ r • I) ⁻¹' (A '' V)} := by
  ext ξ
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.2, hq.2, ?_⟩
    ext i
    simp [angleAction_snd_apply_single, hr]
  · rintro ⟨c, hcV, hc⟩
    -- Lift the base point of `ξ` to `ℝⁿ`, and read off the values from its actions.
    choose t ht using fun i ↦ QuotientAddGroup.mk_surjective (ξ.proj i)
    refine ⟨(r⁻¹ • t, c), ⟨trivial, hcV⟩, ?_⟩
    refine Eq.trans ?_ (CotangentBundle.torusActionAngle_proj_snd_apply_single (fun _ ↦ p) ξ)
    refine congrArg (CotangentBundle.torusActionAngle (fun _ ↦ p))
      (Prod.ext (funext fun i ↦ ?_) ?_)
    · simp [hr, ← ht i]
    · simp only [hc, inv_smul_smul₀ hr]

/-- On values where `A` is injective, the value `c` is recovered from the actions of
`angleAction p r A (θ, c)`, rescaled by `r ≠ 0`, through an inverse of `A`. -/
private theorem invFunOn_smul_angleAction_snd [DecidableEq ι] {r : ℝ} (hr : r ≠ 0)
    {A : (ι → ℝ) → ι → ℝ} {V : Set (ι → ℝ)} (hA : InjOn A V) {q : (ι → ℝ) × (ι → ℝ)}
    (hq : q.2 ∈ V) :
    invFunOn A V (r • fun i ↦ (angleAction p r A q).2 (Pi.single i 1)) = q.2 := by
  have hrA : r • (fun i ↦ r⁻¹ * A q.2 i) = A q.2 := by
    ext i
    simp [hr]
  simp only [angleAction_snd_apply_single, hrA]
  exact hA.leftInvOn_invFunOn hq

/-- The derivative of the map `(θ, c) ↦ (([r θ_i])_i, r⁻¹ A(c))` into `Tⁿ × ℝⁿ`. -/
private theorem hasMFDerivAt_angleActionCoord (r : ℝ) {A : (ι → ℝ) → ι → ℝ}
    {A' : (ι → ℝ) →L[ℝ] ι → ℝ} {q : (ι → ℝ) × (ι → ℝ)} (hA : HasFDerivAt A A' q.2) :
    HasMFDerivAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      (fun q : (ι → ℝ) × (ι → ℝ) ↦ ((fun i ↦ ((r * q.1 i : ℝ) : AddCircle p)), r⁻¹ • A q.2)) q
      ((r • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).prod
        (r⁻¹ • A'.comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))) :=
  ((AddCircle.hasMFDerivAt_coe_pi p (r • q.1)).comp q
    (r • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).hasMFDerivAt).prodMk
    ((hA.comp q (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)).hasFDerivAt).const_smul
      r⁻¹).hasMFDerivAt

/-- **The action–angle map pulls `ω` back to `∑ i, dθ_i ∧ dA_i`.** For `r ≠ 0` and `A`
differentiable at `c`, the map `angleAction p r A` pairs the tangent vectors `(a, b)` and `(a', b')`
at `(θ, c)` to `∑ i, (a_i dA_i(b') - a'_i dA_i(b))`: rescaling the angles by `r` and the actions
by `r⁻¹` preserves `∑ i, dθ_i ∧ dI_i`. -/
private theorem eval₂_symplecticForm_mfderiv_angleAction {r : ℝ} (hr : r ≠ 0)
    {A : (ι → ℝ) → ι → ℝ} {q : (ι → ℝ) × (ι → ℝ)} (hA : DifferentiableAt ℝ A q.2)
    (a b a' b' : ι → ℝ) :
    SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
        (angleAction p r A q)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (angleAction p r A) q (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (angleAction p r A) q (a', b')) =
      ∑ i, (a i * fderiv ℝ (fun c ↦ A c i) q.2 b' - a' i * fderiv ℝ (fun c ↦ A c i) q.2 b) := by
  have hH := hasMFDerivAt_angleActionCoord (p := p) r hA.hasFDerivAt
  have hG := ((CotangentBundle.contMDiff_torusActionAngle (fun _ : ι ↦ p) _).mdifferentiableAt
    (by simp)).hasMFDerivAt.comp q hH
  rw [show angleAction p r A = _ ∘ _ from rfl, hG.mfderiv]
  refine (CotangentBundle.eval₂_symplecticForm_mfderiv_torusActionAngle (fun _ ↦ p) _
    (r • a) (r⁻¹ • fderiv ℝ A q.2 b) (r • a') (r⁻¹ • fderiv ℝ A q.2 b')).trans ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hAi (v : ι → ℝ) : fderiv ℝ (fun c ↦ A c i) q.2 v = fderiv ℝ A q.2 v i := by
    have hd : HasFDerivAt (fun c ↦ A c i) ((ContinuousLinearMap.proj i).comp (fderiv ℝ A q.2))
        q.2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasFDerivAt.comp q.2
          hA.hasFDerivAt
    rw [hd.fderiv]
    rfl
  simp only [Pi.smul_apply, smul_eq_mul, hAi]
  field_simp

/-- The action–angle map is smooth at `(θ, c)` when `A` is smooth at `c`. -/
private theorem contMDiffAt_angleAction (r : ℝ) {A : (ι → ℝ) → ι → ℝ} {q : (ι → ℝ) × (ι → ℝ)}
    (hA : ContDiffAt ℝ ∞ A q.2) :
    ContMDiffAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (angleAction p r A) q := by
  have hθ : ContMDiff 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞
      (fun q : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ ((r * q.1 i : ℝ) : AddCircle p)) :=
    contMDiff_pi_iff.2 fun i ↦ (AddCircle.contMDiff_coe p ∞).comp
      (contDiff_const.mul ((contDiff_apply (𝕜 := ℝ) (F' := fun _ : ι ↦ ℝ) i).comp
        contDiff_fst)).contMDiff
  exact (CotangentBundle.contMDiff_torusActionAngle (fun _ : ι ↦ p) _).comp q
    ((hθ q).prodMk ((hA.comp q contDiffAt_snd).const_smul r⁻¹).contMDiffAt)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} {F : M → ι → ℝ}

/-! ### Action–angle coordinates -/

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [BoundarylessManifold I M] in
/-- **Descending the action–angle map.** Let `Ψ` be a local diffeomorphism at `q`, along which `σ`
pulls back to `∑ i, dθ_i ∧ dA_i` at `q`, for an `A` smooth at the value `q.2`, and let
`φ ∘ Ψ = angleAction p r A` near `q`, with `r ≠ 0`. Then `φ` is smooth at `Ψ q` and pulls `ω`
back to `σ` there. -/
private theorem angleAction_descent {r : ℝ} (hr : r ≠ 0) {A : (ι → ℝ) → ι → ℝ}
    {Ψ : (ι → ℝ) × (ι → ℝ) → M} {q : (ι → ℝ) × (ι → ℝ)}
    (hΨ : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ q) (hA : ContDiffAt ℝ ∞ A q.2)
    (hpull : ∀ a a' b b' : ι → ℝ,
      SmoothBundleForm.eval₂ σ (Ψ q) (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ q (a, b))
          (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ q (a', b')) =
        ∑ i, (a i * fderiv ℝ (fun c ↦ A c i) q.2 b' - a' i * fderiv ℝ (fun c ↦ A c i) q.2 b))
    {φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)}
    (hφ : angleAction p r A =ᶠ[𝓝 q] φ ∘ Ψ) :
    ContMDiffAt I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ
        (Ψ q) ∧
      ∀ v w : TangentSpace I (Ψ q),
        SmoothBundleForm.eval₂
            (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
              (ι → AddCircle p)) (φ (Ψ q))
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
              𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ (Ψ q) v)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
              𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ (Ψ q) w) =
          SmoothBundleForm.eval₂ σ (Ψ q) v w := by
  -- Since `φ ∘ Ψ = G` near `q`, the map `φ` is smooth at `Ψ q`, and `dφ ∘ dΨ = dG`.
  have hφs : ContMDiffAt I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ (Ψ q) :=
    (hΨ.contMDiffAt_comp_iff le_rfl).mp
      ((contMDiffAt_angleAction r hA).congr_of_eventuallyEq hφ.symm)
  have hchain (u : (ι → ℝ) × (ι → ℝ)) :
      mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ (Ψ q)
          (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ q u) =
        mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (angleAction p r A) q u := by
    rw [(((hφs.mdifferentiableAt (by simp)).hasMFDerivAt.comp q
      (hΨ.mdifferentiableAt (by simp)).hasMFDerivAt).congr_of_eventuallyEq_abuse hφ).mfderiv]
    rfl
  -- Both forms pull back along `Ψ` to `∑ i, dθ_i ∧ dA_i`. Write tangent vectors at `Ψ q` as
  -- images under the invertible differential of `Ψ`.
  refine ⟨hφs, fun v w ↦ ?_⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := (hΨ.mfderivToContinuousLinearEquiv (by simp)).surjective v
  obtain ⟨⟨a', b'⟩, rfl⟩ := (hΨ.mfderivToContinuousLinearEquiv (by simp)).surjective w
  refine ((congrArg₂ _ (hchain (a, b)) (hchain (a', b'))).trans ?_).trans (hpull a a' b b').symm
  rw [show φ (Ψ q) = angleAction p r A q from hφ.self_of_nhds.symm]
  exact eval₂_symplecticForm_mfderiv_angleAction hr (hA.differentiableAt (by simp)) a b a' b'

omit [I.Boundaryless] [T2Space M] in
/-- A map into `T*Tⁿ`, smooth on an open set `U` and pulling `ω` back to a nondegenerate form `σ`
on `U`, is a local diffeomorphism there when `M` has dimension `2 |ι|`. -/
private theorem isLocalDiffeomorphOn_of_eval₂_eq (hσ : σ.IsNondegenerate)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {U : Set M} (hU : IsOpen U)
    {φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)}
    (hφ : ∀ x ∈ U,
      ContMDiffAt I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ x)
    (hform : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      SmoothBundleForm.eval₂
          (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
            (ι → AddCircle p)) (φ x)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
            𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ x v)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
            𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ x w) =
        SmoothBundleForm.eval₂ σ x v w) :
    IsLocalDiffeomorphOn I
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ U := by
  -- `φ` is an immersion since `σ` is nondegenerate, and the inverse function theorem applies.
  refine (isLocalDiffeomorphOn_iff _).mpr fun ⟨x, hx⟩ ↦
    isLocalDiffeomorphAt_of_injective_mfderiv (s := U) (fun y hy ↦ (hφ y hy).contMDiffWithinAt)
      hU hx BoundarylessManifold.isInteriorPoint (by simp) ?_ ?_
  · refine (injective_iff_map_eq_zero _).mpr fun v hv ↦
      isNondegenerate_iff_separatingLeft.mp hσ _ v fun w ↦ ?_
    rw [← hform x hx v w, hv, SmoothBundleForm.eval₂_zero_left]
  · rw [← hdim, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      ← LinearMap.toContinuousLinearMap.finrank_eq, Module.finrank_linearMap_self,
      Module.finrank_fintype_fun_eq_card, two_mul]

/-- **The Liouville–Arnold theorem: action–angle coordinates.** Let `σ` be a symplectic form on a
Hausdorff boundaryless manifold `M` of dimension `2n`, and let `F : M → ℝⁿ` be `n` smooth,
pairwise Poisson-commuting functions. Let the connected component `L` of `x₀` in its level
`F⁻¹(F x₀)` be compact and consist of regular points of `F`. Then for every period `p > 0` there are
an open neighbourhood `U` of `L`, an open set `D ⊆ ℝⁿ` and a map `φ` from `M` to the cotangent
bundle of the torus `Tⁿ = (ℝ / pℤ)ⁿ` such that `φ` is injective on `U` and a local diffeomorphism
there, `φ(U)` is the set of covectors `ξ` whose actions `ξ(e_i)` lie in `D`, `φ` pulls the canonical
symplectic form `ω = ∑ i, dθ_i ∧ dI_i` back to `σ`, and `F` is a function of the actions on `U`.
No completeness of the Hamiltonian vector fields is assumed. -/
theorem exists_actionAngle [DecidableEq ι] (hσ : σ.IsSymplectic) (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
    (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x₀ : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x₀}) x₀, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x₀}) x₀)) (p : ℝ) [Fact (0 < p)] :
    ∃ U : Set M, IsOpen U ∧ connectedComponentIn (F ⁻¹' {F x₀}) x₀ ⊆ U ∧
      ∃ D : Set (ι → ℝ), IsOpen D ∧
      ∃ φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p),
        InjOn φ U ∧
        IsLocalDiffeomorphOn I
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ U ∧
        φ '' U = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D} ∧
        (∀ x ∈ U, ∀ v w : TangentSpace I x,
          SmoothBundleForm.eval₂
              (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
                (ι → AddCircle p)) (φ x)
              (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
                𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ x v)
              (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
                𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ x w) =
            SmoothBundleForm.eval₂ σ x v w) ∧
        ∃ h : (ι → ℝ) → ι → ℝ, ∀ x ∈ U, F x = h (fun i ↦ (φ x).2 (Pi.single i 1)) := by
  obtain ⟨Ψ, A, U₀, hU₀, hxU₀, hA, hrange, hΨ⟩ :=
    hσ.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact hF hcomm hdim hreg hK
  set r := p / (2 * π)
  have hr : r ≠ 0 := div_ne_zero (Fact.out : 0 < p).ne' (by positivity)
  -- Restrict the values to an open neighbourhood `V` of `F x₀` on which `A` is an injective local
  -- diffeomorphism, and the angle–action pairs to `Ω = ℝⁿ × V`.
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp (inter_mem (inter_mem (hU₀.mem_nhds hxU₀)
    hA.exists_mem_nhds_injOn.choose_spec.1) hA.eventually)
  have hVU₀ (c : ι → ℝ) (hc : c ∈ V) : c ∈ U₀ := (hVsub hc).1.1
  have hAinj : InjOn A V := hA.exists_mem_nhds_injOn.choose_spec.2.mono fun c hc ↦ (hVsub hc).1.2
  set Ω : Set ((ι → ℝ) × (ι → ℝ)) := univ ×ˢ V
  have hΩo : IsOpen Ω := isOpen_univ.prod hVo
  have hΨloc (q : (ι → ℝ) × (ι → ℝ)) (hq : q ∈ Ω) :
      IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ q :=
    (hΨ q.2 (hVU₀ _ hq.2)).2.1 q.1
  -- On `Ω`, the action–angle map `G` is constant exactly on the fibres of `Ψ`, so it descends to a
  -- map `φ` on `Ψ(Ω)`.
  set G := angleAction p r A
  have hfib (q : (ι → ℝ) × (ι → ℝ)) (hq : q ∈ Ω) (q' : (ι → ℝ) × (ι → ℝ)) (hq' : q' ∈ Ω) :
      Ψ q = Ψ q' ↔ G q = G q' :=
    ((hΨ q.2 (hVU₀ _ hq.2)).2.2.2 q'.2 (hVU₀ _ hq'.2) q.1 q'.1).trans
      (angleAction_eq_angleAction_iff hAinj hq.2 hq'.2).symm
  set φ := extend (fun q : Ω ↦ Ψ q) (fun q : Ω ↦ G q) fun _ ↦ G (0, F x₀)
  have hfact : FactorsThrough (fun q : Ω ↦ G q) (fun q : Ω ↦ Ψ q) :=
    fun q q' h ↦ (hfib _ q.2 _ q'.2).mp h
  have hφ (q : (ι → ℝ) × (ι → ℝ)) (hq : q ∈ Ω) : φ (Ψ q) = G q := hfact.extend_apply _ ⟨q, hq⟩
  have hdesc (q : (ι → ℝ) × (ι → ℝ)) (hq : q ∈ Ω) := angleAction_descent (p := p) (φ := φ) hr
    (hΨloc q hq)
    ((hVsub hq.2).2.contMDiffAt.contDiffAt) ((hΨ q.2 (hVU₀ _ hq.2)).2.2.1 q.1)
    (eventually_of_mem (hΩo.mem_nhds hq) fun q' hq' ↦ (hφ q' hq').symm)
  have hUo : IsOpen (Ψ '' Ω) :=
    ((isLocalDiffeomorphOn_iff _).mpr fun q ↦ hΨloc q q.2).isLocalHomeomorphOn.isOpen_image hΩo
  refine ⟨Ψ '' Ω, hUo, ?_, (fun I ↦ r • I) ⁻¹' (A '' V),
    (((isLocalDiffeomorphOn_iff _).mpr fun c ↦ (hVsub c.2).2).isLocalHomeomorphOn.isOpen_image
      hVo).preimage (continuous_const_smul r), φ, ?_,
    isLocalDiffeomorphOn_of_eval₂_eq hσ.isNondegenerate hdim hUo
      (fun _ ⟨q, hq, h⟩ ↦ h ▸ (hdesc q hq).1) (fun _ ⟨q, hq, h⟩ ↦ h ▸ (hdesc q hq).2), ?_,
    fun _ ⟨q, hq, h⟩ ↦ h ▸ (hdesc q hq).2, fun I ↦ invFunOn A V (r • I), ?_⟩
  · rw [← hrange]
    rintro _ ⟨θ, rfl⟩
    exact ⟨(θ, F x₀), ⟨trivial, hxV⟩, rfl⟩
  · rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩ h
    rw [hφ q hq, hφ q' hq'] at h
    exact (hfib q hq q' hq').mpr h
  · rw [image_image, ← image_angleAction hr A V]
    exact image_congr fun q hq ↦ hφ q hq
  · -- On `Ψ(Ω)` the actions of `φ` are `r⁻¹ A`, and `F ∘ Ψ` is the projection to the values.
    rintro _ ⟨q, hq, rfl⟩
    rw [(hΨ q.2 (hVU₀ _ hq.2)).1 q.1, hφ q hq]
    exact (invFunOn_smul_angleAction_snd hr hAinj hq.2).symm

end IsSymplectic

end SmoothTwoForm

end TauCeti

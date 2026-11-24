/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle.Hamiltonian
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Chart

import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Basic

-- Access the body of `IsLocalDiffeomorphAt` to destructure the partial diffeomorphism witnessing
-- that the actions are a local diffeomorphism.
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The Liouville–Arnold normal form on the cotangent bundle of a torus

Let `σ` be a symplectic form on a boundaryless Hausdorff manifold `M` of dimension `2 |ι|`, and let
`F : M → (ι → ℝ)` be a smooth family of pairwise Poisson-commuting functions, with the conventions
`ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`. Let `L` be the connected component of a point
`x` in its level `F⁻¹(F x)`, and suppose that `L` is compact and consists of regular points of `F`.
The Hamiltonian vector fields of the `F_i` need not be complete.

The **Liouville–Arnold theorem** in action–angle form says that a neighbourhood of `L` is
symplectomorphic to an open piece of the cotangent bundle `T*Tⁿ` of the torus
`Tⁿ = ι → AddCircle p`, with its canonical symplectic form `ω = -dλ = ∑ j, dθ_j ∧ dI_j`
(`TauCeti.CotangentBundle.symplecticForm`), in such a way that `F` becomes a function of the
actions `I_j = ξ(e_j)` alone (`TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`). Precisely,
for every period `p > 0` there are an open set `U ⊇ L`, an open set `D ⊆ ℝ^ι`, a map
`Φ : M → T*Tⁿ` and a smooth function `h` on `D` such that

* `Φ` is injective on `U` and a local diffeomorphism at every point of `U`;
* `Φ` maps `U` onto the open set of covectors whose actions lie in `D`;
* `Φ` pulls `ω` back to `σ` on `U`;
* `F = h ∘ (actions of Φ)` on `U`, the actions being `TauCeti.CotangentBundle.torusActions`;
* the Hamiltonian vector field of each `F_i` is `∑ j, (∂h_i / ∂I_j) ∂θ_j` in these coordinates:
  the differential of `Φ` carries it to the image of `(∇h_i(I), 0)` under the differential of
  the action–angle covering map `κ` at `(θ, I)`
  (`TauCeti.CotangentBundle.mfderiv_hamiltonianVectorField_eq_mfderiv_actionAngleCover`).

The map `Φ` is assembled from the local action-angle coordinates near `L`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact`):
a local diffeomorphism `Ψ(θ, c)` on `ℝ^ι × U₀`, `2π`-periodic in the angles `θ` and injective
modulo `2πℤ^ι`, pulling `σ` back to `∑ i, dθ_i ∧ dA_i` for action variables `A`. On the image of
`Ψ` set

`Φ(Ψ(θ, c)) = κ((p / 2π) θ, (2π / p) A(c))`,

where `κ(θ, I) = ∑ j, I_j dθ_j` at `[θ]` is the action–angle covering map of `T*Tⁿ`
(`TauCeti.CotangentBundle.actionAngleCover`). This is well defined because `κ` is `p`-periodic in
the angles, and it pulls `ω` back to `σ` because `κ` pulls `ω` back to `∑ j, dθ_j ∧ dI_j`
(`TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_actionAngleCover`); the factors `p / 2π` and
`2π / p` cancel. Taking `p = 2π` gives the classical angles of period `2π` and the actions `A`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50 (the Liouville–Arnold theorem and action-angle
  variables).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4.
-/

public section

noncomputable section

open Set Function Real
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

/-! ### The rescaled action–angle model -/

section Model

variable {ι : Type*} [Fintype ι] (p : ℝ) [Fact (0 < p)] (a : ℝ) (A : (ι → ℝ) → ι → ℝ)

/-- The action–angle covering map of `T*(ι → AddCircle p)` composed with the rescaling
`(θ, c) ↦ (a θ, a⁻¹ A(c))` of angles and actions. With `a = p / 2π` it converts angles of period
`2π` and actions `A` into the coordinates of `T*(ι → AddCircle p)`. -/
private def rescaledCover (q : (ι → ℝ) × (ι → ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
  CotangentBundle.actionAngleCover p (a • q.1, a⁻¹ • A q.2)

variable {p a A}

/-- The actions of `rescaledCover p a A (θ, c)` are `a⁻¹ A(c)`. -/
private theorem torusActions_rescaledCover [DecidableEq ι] (q : (ι → ℝ) × (ι → ℝ)) :
    CotangentBundle.torusActions p (rescaledCover p a A q) = a⁻¹ • A q.2 :=
  CotangentBundle.torusActions_actionAngleCover p _

private theorem contMDiffAt_rescaledCover {q : (ι → ℝ) × (ι → ℝ)}
    (hA : ContDiffAt ℝ ∞ A q.2) :
    ContMDiffAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (rescaledCover p a A) q :=
  (CotangentBundle.contMDiff_actionAngleCover p _).comp q (contMDiffAt_iff_contDiffAt.2
    ((contDiffAt_fst.const_smul a).prodMk ((hA.comp q contDiffAt_snd).const_smul a⁻¹)))

/-- The differential of `rescaledCover p a A` is that of the action–angle covering map after the
rescaling `(u, w) ↦ (a u, a⁻¹ dA(w))`. -/
private theorem mfderiv_rescaledCover_apply {q : (ι → ℝ) × (ι → ℝ)}
    {A' : (ι → ℝ) →L[ℝ] ι → ℝ} (hA : HasFDerivAt A A' q.2)
    (u : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) q) :
    mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (rescaledCover p a A) q u =
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (CotangentBundle.actionAngleCover p) (a • q.1, a⁻¹ • A q.2) (a • u.1, a⁻¹ • A' u.2) := by
  have hS : HasFDerivAt (fun q : (ι → ℝ) × (ι → ℝ) ↦ (a • q.1, a⁻¹ • A q.2))
      ((a • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).prod
        (a⁻¹ • A'.comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))) q :=
    (hasFDerivAt_fst.const_smul a).prodMk ((hA.comp q hasFDerivAt_snd).const_smul a⁻¹)
  have hκ := ((CotangentBundle.contMDiff_actionAngleCover (ι := ι) p
    (a • q.1, a⁻¹ • A q.2)).mdifferentiableAt (by simp)).hasMFDerivAt
  -- `rescaledCover p a A` is the composite of the covering map and the rescaling.
  exact DFunLike.congr_fun (hκ.comp q hS.hasMFDerivAt).mfderiv u

/-- **The rescaled model pulls back the canonical form to `∑ i, dθ_i ∧ dA_i`.** The factors `a`
and `a⁻¹` cancel. -/
private theorem eval₂_symplecticForm_mfderiv_rescaledCover (ha : a ≠ 0)
    {q : (ι → ℝ) × (ι → ℝ)} {A' : (ι → ℝ) →L[ℝ] ι → ℝ} (hA : HasFDerivAt A A' q.2)
    (v w : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) q) :
    SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (ι → AddCircle p)) (rescaledCover p a A q)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (rescaledCover p a A) q v)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (rescaledCover p a A) q w) =
      ∑ i, (v.1 i * A' w.2 i - w.1 i * A' v.2 i) := by
  rw [mfderiv_rescaledCover_apply hA v, mfderiv_rescaledCover_apply hA w]
  refine (CotangentBundle.eval₂_symplecticForm_mfderiv_actionAngleCover p _
    (a • v.1, a⁻¹ • A' v.2) (a • w.1, a⁻¹ • A' w.2)).trans
    (Finset.sum_congr rfl fun i _ ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- **The fibres of the rescaled model.** For `a = p / 2π` and `A` injective on a set containing
`c` and `c'`, the points `(θ, c)` and `(θ', c')` have the same image exactly when `c' = c` and
`θ' - θ ∈ 2πℤ^ι`. -/
private theorem rescaledCover_eq_rescaledCover_iff (hpa : a = p / (2 * π)) {s : Set (ι → ℝ)}
    (hA : InjOn A s) {θ θ' c c' : ι → ℝ} (hc : c ∈ s) (hc' : c' ∈ s) :
    rescaledCover p a A (θ, c) = rescaledCover p a A (θ', c') ↔
      c' = c ∧ ∃ m : ι → ℤ, θ' = θ + fun i ↦ 2 * π * m i := by
  have ha : a ≠ 0 := hpa ▸ div_ne_zero (Fact.out : 0 < p).ne' (by positivity)
  have hap (m : ℤ) : a * (2 * π * m) = m * p := by
    rw [hpa]
    field_simp
  rw [rescaledCover, rescaledCover, CotangentBundle.actionAngleCover_eq_actionAngleCover_iff,
    (smul_right_injective _ (inv_ne_zero ha)).eq_iff, hA.eq_iff hc' hc]
  refine and_congr_right fun _ ↦ exists_congr fun m ↦ ?_
  simp only [funext_iff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hap, ← mul_add,
    (mul_right_injective₀ ha).eq_iff]

/-- The rescaled model has injective differential where `dA` is injective. -/
private theorem injective_mfderiv_rescaledCover (ha : a ≠ 0) {q : (ι → ℝ) × (ι → ℝ)}
    {A' : (ι → ℝ) →L[ℝ] ι → ℝ} (hA : HasFDerivAt A A' q.2) (hA' : Injective A') :
    Injective (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (rescaledCover p a A) q) := by
  have hκ := ((CotangentBundle.isLocalDiffeomorph_actionAngleCover (ι := ι) p
    (a • q.1, a⁻¹ • A q.2)).isInvertible_mfderiv (by simp)).injective
  intro u u' huu'
  rw [mfderiv_rescaledCover_apply hA u, mfderiv_rescaledCover_apply hA u'] at huu'
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj (hκ huu')
  exact Prod.ext (smul_right_injective _ ha h₁) (hA' (smul_right_injective _ (inv_ne_zero ha) h₂))

/-- The rescaled model is smooth on `ℝ^ι × t` when `A` is smooth on the open set `t`. -/
private theorem contMDiffOn_rescaledCover {t : Set (ι → ℝ)} (ht : IsOpen t)
    (hA : ContDiffOn ℝ ∞ A t) :
    ContMDiffOn 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (rescaledCover p a A) (univ ×ˢ t) :=
  fun q hq ↦ (contMDiffAt_rescaledCover
    ((hA q.2 hq.2).contDiffAt (ht.mem_nhds hq.2))).contMDiffWithinAt

end Model

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι] [DecidableEq ι] {F : M → ι → ℝ}

/-- The Liouville–Arnold normal form without the Hamiltonian vector fields: the construction of the
chart `Φ` and of the function `h` of the actions. -/
private theorem exists_actionAngle_aux (hσ : σ.IsSymplectic) (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
    (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = Module.finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) (p : ℝ) [Fact (0 < p)] :
    ∃ (U : Set M) (D : Set (ι → ℝ))
      (Φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
      (h : (ι → ℝ) → ι → ℝ),
      IsOpen U ∧ connectedComponentIn (F ⁻¹' {F x}) x ⊆ U ∧ IsOpen D ∧ InjOn Φ U ∧
      Φ '' U = {z | CotangentBundle.torusActions p z ∈ D} ∧
      (∀ y ∈ U, IsLocalDiffeomorphAt I
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ y) ∧
      (∀ y ∈ U, ∀ v w : TangentSpace I y,
        SmoothBundleForm.eval₂
            (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
              (ι → AddCircle p)) (Φ y)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
              Φ y v)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
              Φ y w) =
          SmoothBundleForm.eval₂ σ y v w) ∧
      ContDiffOn ℝ ∞ h D ∧ ∀ y ∈ U, F y = h (CotangentBundle.torusActions p (Φ y)) := by
  -- Start from the local action-angle coordinates `Ψ(θ, c)`, `2π`-periodic in `θ`, with actions
  -- `A`. On `W = ℝ^ι × U₀`, where `A` is a diffeomorphism, `Ψ` and the rescaled model
  -- `κ(θ, c) = ∑ j, (a⁻¹ A(c))_j dθ_j` at `[a θ]`, `a = p / 2π`, identify the same points, so `κ`
  -- factors as `Φ ∘ Ψ`. Then `Φ` inherits from `κ` and `Ψ` each property of the statement.
  obtain ⟨Ψ, A, U, hU, hxU, hA, hrange, hΨ⟩ :=
    hσ.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact hF hcomm hdim hreg hK
  -- Shrink the values to an open set `U₀` on which `A` is a diffeomorphism `ΦA`.
  obtain ⟨ΦA, hxA, hAeq⟩ := hA
  set U₀ := U ∩ ΦA.source
  have hU₀ : IsOpen U₀ := hU.inter ΦA.open_source
  have hAinj : InjOn A U₀ := (ΦA.toPartialEquiv.injOn.mono inter_subset_right).congr
    (hAeq.mono inter_subset_right).symm
  have hAloc (c : ι → ℝ) (hc : c ∈ U₀) :
      IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ A c :=
    isLocalDiffeomorphAt_of_eqOn hc.2 hAeq
  -- The rescaling `a = p / 2π` between angles of period `2π` and `p`, and the model `κ`.
  set a : ℝ := p / (2 * π) with ha_def
  have ha : a ≠ 0 := div_ne_zero (Fact.out : 0 < p).ne' (by positivity)
  set κ := rescaledCover p a A with hκ_def
  set W : Set ((ι → ℝ) × (ι → ℝ)) := univ ×ˢ U₀
  have hW : IsOpen W := isOpen_univ.prod hU₀
  -- On `W`, the model `κ` and `Ψ` identify the same points: both are `2π`-periodic in the angles.
  have hκeq (q q' : (ι → ℝ) × (ι → ℝ)) (hq : q ∈ W) (hq' : q' ∈ W) :
      κ q = κ q' ↔ Ψ q = Ψ q' := by
    obtain ⟨θ, c⟩ := q
    obtain ⟨θ', c'⟩ := q'
    rw [hκ_def, rescaledCover_eq_rescaledCover_iff ha_def hAinj hq.2 hq'.2,
      (hΨ c hq.2.1).2.2.2 c' hq'.2.1]
  -- So `κ` factors through `Ψ` on `W`, as `Φ ∘ Ψ`.
  set Φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
    extend (fun q : W ↦ Ψ q) (fun q : W ↦ κ q) fun _ ↦ κ 0
  have hΦΨ (q : (ι → ℝ) × (ι → ℝ)) (hq : q ∈ W) : Φ (Ψ q) = κ q :=
    FactorsThrough.extend_apply (f := fun q : W ↦ Ψ q) (g := fun q : W ↦ κ q)
      (fun q q' h ↦ (hκeq q q' q.property q'.property).2 h) _ ⟨q, hq⟩
  have hΨloc (q : (ι → ℝ) × (ι → ℝ)) (hq : q ∈ W) :
      IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ q :=
    (hΨ q.2 hq.2.1).2.1 q.1
  -- The derivative of `A` is injective on `U₀`.
  have hdA (c : ι → ℝ) (hc : c ∈ U₀) :
      HasFDerivAt A (fderiv ℝ A c) c ∧ Injective (fderiv ℝ A c) := by
    have hd := (mdifferentiableAt_iff_differentiableAt.1
      ((hAloc c hc).mdifferentiableAt (by simp))).hasFDerivAt
    refine ⟨hd, ?_⟩
    rw [← hd.hasMFDerivAt.mfderiv]
    exact ((hAloc c hc).isInvertible_mfderiv (by simp)).injective
  -- `Φ ∘ Ψ = κ` on the open set `W`, where `κ` has injective differential, so `Φ` is a local
  -- diffeomorphism on `Ψ '' W`.
  have hΦΨW : EqOn (Φ ∘ Ψ) κ W := fun q hq ↦ hΦΨ q hq
  have hΦloc (q : (ι → ℝ) × (ι → ℝ)) (hq : q ∈ W) :
      IsLocalDiffeomorphAt I
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ (Ψ q) :=
    isLocalDiffeomorphAt_of_eqOn_comp hW hq BoundarylessManifold.isInteriorPoint (by simp) hΦΨW
      (contMDiffOn_rescaledCover hU₀ fun c hc ↦ (contMDiffAt_iff_contDiffAt.1
        (hAloc c hc).contMDiffAt).contDiffWithinAt)
      (injective_mfderiv_rescaledCover ha (hdA q.2 hq.2).1 (hdA q.2 hq.2).2)
      (by simp only [Module.finrank_prod, ContinuousLinearMap.dual_finrank_eq]) (hΨloc q hq)
  refine ⟨Ψ '' W, (fun c ↦ a⁻¹ • A c) '' U₀, Φ, fun J ↦ ΦA.symm (a • J), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · -- `Ψ` is a local homeomorphism on the open set `W`, so `Ψ '' W` is open.
    exact ((isLocalDiffeomorphOn_iff W).2 fun q ↦ hΨloc q
        q.property).isLocalHomeomorphOn.isOpen_image hW
  · -- The component is swept out by the angles at the value `F x ∈ U₀`.
    rw [← hrange]
    rintro _ ⟨θ, rfl⟩
    exact ⟨(θ, F x), ⟨mem_univ _, hxU, hxA⟩, rfl⟩
  · -- `D` is the image of the open set `A '' U₀ = ΦA '' U₀` under a rescaling.
    have h : (fun c ↦ a⁻¹ • A c) '' U₀ = (a⁻¹ • ·) '' (ΦA '' U₀) := by
      rw [image_image]
      exact image_congr fun c hc ↦ by rw [hAeq hc.2]
    rw [h]
    exact isOpenMap_smul₀ (inv_ne_zero ha) _
      (ΦA.toOpenPartialHomeomorph.isOpen_image_of_subset_source hU₀ inter_subset_right)
  · rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩ he
    rw [hΦΨ q hq, hΦΨ q' hq'] at he
    exact (hκeq q q' hq hq').1 he
  · ext z
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      rw [Set.mem_ofPred_eq, hΦΨ q hq, hκ_def, torusActions_rescaledCover]
      exact ⟨q.2, hq.2, rfl⟩
    · rintro ⟨c, hc, hcz⟩
      obtain ⟨⟨θ₀, I₀⟩, rfl⟩ := CotangentBundle.surjective_actionAngleCover p z
      refine ⟨Ψ (a⁻¹ • θ₀, c), ⟨_, ⟨mem_univ _, hc⟩, rfl⟩, ?_⟩
      rw [hΦΨ _ ⟨mem_univ _, hc⟩, hκ_def, rescaledCover, smul_inv_smul₀ ha]
      congr 2
      exact hcz.trans (CotangentBundle.torusActions_actionAngleCover p _)
  · rintro _ ⟨q, hq, rfl⟩
    exact hΦloc q hq
  · rintro _ ⟨q, hq, rfl⟩ v w
    -- Write `v` and `w` as images under the invertible differential of `Ψ`, and compare the
    -- pullbacks along `Ψ` of `σ` and along `Φ ∘ Ψ = κ` of the canonical form.
    have hΨsurj := ((hΨloc q hq).isInvertible_mfderiv (by simp)).surjective
    obtain ⟨v', rfl⟩ := hΨsurj v
    obtain ⟨w', rfl⟩ := hΨsurj w
    have hchain := mfderiv_apply_mfderiv_of_eventuallyEq_comp
      (Filter.eventuallyEq_of_mem (hW.mem_nhds hq) hΦΨW) ((hΦloc q hq).mdifferentiableAt (by simp))
      ((hΨloc q hq).mdifferentiableAt (by simp))
    -- The components of `dA` are the derivatives of the components of `A`.
    have hAi (i : ι) (u : ι → ℝ) : fderiv ℝ A q.2 u i = fderiv ℝ (fun c ↦ A c i) q.2 u := by
      rw [((hasFDerivAt_pi'.1 (hdA q.2 hq.2).1) i).fderiv, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply]
    rw [CotangentBundle.eval₂_symplecticForm, hchain, hchain,
      ← CotangentBundle.eval₂_symplecticForm (κ q),
      eval₂_symplecticForm_mfderiv_rescaledCover ha (hdA q.2 hq.2).1]
    simp only [hAi]
    exact ((hΨ q.2 hq.2.1).2.2.1 q.1 v'.1 w'.1 v'.2 w'.2).symm
  · -- `h` is the inverse of `ΦA` after undoing the rescaling of the actions.
    refine ΦA.symm.contMDiffOn.contDiffOn.comp (contDiff_const_smul a).contDiffOn ?_
    rintro _ ⟨c, hc, rfl⟩
    rw [smul_inv_smul₀ ha, hAeq hc.2]
    exact ΦA.toPartialEquiv.map_source hc.2
  · rintro _ ⟨q, hq, rfl⟩
    dsimp only
    rw [hΦΨ q hq, hκ_def, torusActions_rescaledCover, smul_inv_smul₀ ha, hAeq hq.2.2]
    exact ((ΦA.toPartialEquiv.left_inv hq.2.2).trans ((hΨ q.2 hq.2.1).1 q.1).symm).symm

/-- **The Liouville–Arnold theorem in action–angle form.** On a symplectic manifold of dimension
`2 · |ι|`, let `F` be a smooth family of pairwise Poisson-commuting functions, and let the
connected component `L` of `x` in its level `F⁻¹(F x)` be compact and consist of regular points of
`F`. The Hamiltonian vector fields of the `F_i` need not be complete. Then for every period `p > 0`
there are an open neighbourhood `U` of `L`, an open set `D` of actions, a map `Φ` into the
cotangent bundle of the torus `ι → AddCircle p` and a smooth function `h` on `D` such that `Φ` is
injective on `U`, a local diffeomorphism at every point of `U`, maps `U` onto the covectors whose
actions `ξ(e_j)` lie in `D`, pulls the canonical symplectic form back to `σ` on `U`, and turns `F`
into the function `h` of the actions. In these coordinates the Hamiltonian vector field of each
`F_i` is `∑ j, (∂h_i / ∂I_j) ∂θ_j`: at `y ∈ U` with `Φ y = κ(θ, I)`, the differential of `Φ` carries
it to the image of `(∇h_i(I), 0)` under the differential at `(θ, I)` of the action–angle covering
map `κ`. -/
theorem exists_actionAngle (hσ : σ.IsSymplectic) (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
    (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = Module.finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) (p : ℝ) [Fact (0 < p)] :
    ∃ (U : Set M) (D : Set (ι → ℝ))
      (Φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
      (h : (ι → ℝ) → ι → ℝ),
      IsOpen U ∧ connectedComponentIn (F ⁻¹' {F x}) x ⊆ U ∧ IsOpen D ∧ InjOn Φ U ∧
      Φ '' U = {z | CotangentBundle.torusActions p z ∈ D} ∧
      (∀ y ∈ U, IsLocalDiffeomorphAt I
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ y) ∧
      (∀ y ∈ U, ∀ v w : TangentSpace I y,
        SmoothBundleForm.eval₂
            (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
              (ι → AddCircle p)) (Φ y)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
              Φ y v)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
              Φ y w) =
          SmoothBundleForm.eval₂ σ y v w) ∧
      ContDiffOn ℝ ∞ h D ∧ (∀ y ∈ U, F y = h (CotangentBundle.torusActions p (Φ y))) ∧
      ∀ y ∈ U, ∀ i, ∀ q : (ι → ℝ) × (ι → ℝ), CotangentBundle.actionAngleCover p q = Φ y →
        mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ y
            (σ.hamiltonianVectorField (F · i) y) =
          mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
            ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
            (CotangentBundle.actionAngleCover p) q
            (fun j ↦ fderiv ℝ (h · i) q.2 (Pi.single j 1), 0) := by
  obtain ⟨U, D, Φ, h, hU, hLU, hD, hinj, himage, hloc, hsymp, hh, hFh⟩ :=
    exists_actionAngle_aux hσ hF hcomm hdim hreg hK p
  refine ⟨U, D, Φ, h, hU, hLU, hD, hinj, himage, hloc, hsymp, hh, hFh, fun y hy i q hq ↦ ?_⟩
  -- Near `y`, `F_i` is the `i`-th component of `h` composed with the actions of `Φ`.
  have hFi : (F · i) =ᶠ[𝓝 y] (h · i) ∘ CotangentBundle.torusActions p ∘ Φ :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hy) fun y' hy' ↦ congrFun (hFh y' hy') i
  -- The actions of `Φ y` lie in the open set `D`, where `h` is smooth.
  have hqD : q.2 ∈ D := by
    have h' : Φ y ∈ Φ '' U := mem_image_of_mem Φ hy
    simpa [himage, ← hq] using h'
  have hhi : DifferentiableAt ℝ (h · i) q.2 :=
    differentiableAt_pi.1 ((hh.differentiableOn (by simp) q.2 hqD).differentiableAt
      (hD.mem_nhds hqD)) i
  exact CotangentBundle.mfderiv_hamiltonianVectorField_eq_mfderiv_actionAngleCover p
    hσ.isNondegenerate (hloc y hy) (hsymp y hy) hFi hq hhi

end IsSymplectic

end SmoothTwoForm

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Model
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle.Hamiltonian
import Mathlib.Algebra.Group.Subgroup.Finsupp
import TauCeti.Geometry.Manifold.Flow.Related
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Global action–angle coordinates force exact periods, injective actions and a Lagrangian section

Let `σ` be a symplectic form on a boundaryless manifold `M`, let `π : M → B` be a regular
Lagrangian torus fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`)
and let `p > 0`. **Global action–angle coordinates** are an injective local diffeomorphism

`Φ : M → T*(ι → ℝ/pℤ)`

into the cotangent bundle of the torus which pulls the canonical form `ω = ∑ j, dθ_j ∧ dI_j` back
to `σ` and whose actions are functions on the base, `I ∘ Φ = a ∘ π` for a map `a : B → ℝ^ι`
(`TauCeti.CotangentBundle.torusActions`). This is the conclusion of
`IsLagrangianTorusFibration.exists_actionAngle_of_lagrangian_section`, the sufficiency half of
Duistermaat's criterion. This file proves the necessity half: such a chart forces

* **exact periods**: the period lattice at `b` is spanned by the covectors `p • da_j(b)`
  (`IsLagrangianTorusFibration.periodLattice_eq_closure_of_actionAngle`), so the period forms are
  exact and globally framed, and the linear monodromy is trivial;
* **injective actions**: the developing map `a` is injective
  (`IsLagrangianTorusFibration.injective_of_actionAngle`);
* **a Lagrangian section**: the zero angles `θ = 0` give a smooth section `s` of `π` with
  `s^* σ = 0` (`IsLagrangianTorusFibration.exists_lagrangian_section_of_actionAngle`).

Together with `exists_actionAngle_of_lagrangian_section`, this characterizes the regular Lagrangian
torus fibrations admitting global action–angle coordinates.

Everything follows from one identity. The Hamiltonian flow of `(c ⬝ᵥ a) ∘ π` on `M` and that of
`c ⬝ᵥ I` on `T*Tⁿ` are related by `Φ`, since `Φ` is symplectic and `(c ⬝ᵥ a) ∘ π = (c ⬝ᵥ I) ∘ Φ`,
and the latter turns the angles linearly, `κ(θ, I) ↦ κ(θ + t c, I)`
(`TauCeti.CotangentBundle.isMIntegralCurve_actionAngleCover_add_smul`). The covector
`∑ j, c_j da_j(b)` acts on the fibre over `b` by the time-one map of the first flow, so in the
chart it translates the angles by `c`
(`IsLagrangianTorusFibration.apply_fiberAction_of_actionAngle`). A covector is a period exactly
when this translation fixes a point, that is, by injectivity of `Φ`, when `c ∈ p ℤ^ι`. Every
covector at `b` has this form, because `da_b` is invertible
(`IsLagrangianTorusFibration.bijective_mfderiv_of_actionAngle`): the actions are a submersion and
`B` has half the dimension of `M`. Translating the angles reaches the whole torus `{I = a(b)}`
from the fibre over `b`, so two fibres with the same actions have images meeting in a point, and
coincide by injectivity of `Φ`. The same translation makes the zero angles `κ(0, a(b))` a point of
the image of the fibre over `b`, and `Φ⁻¹(κ(0, a(·)))` is the Lagrangian section, since `κ(0, ·)`
pulls `ω` back to zero
(`TauCeti.CotangentBundle.mpullback_actionAngleCover_zero_comp_symplecticForm`).

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`.

* `apply_fiberAction_of_actionAngle`: in global action–angle coordinates the covector
  `∑ j, c_j da_j(b)` translates the angles by `c`.
* `bijective_mfderiv_of_actionAngle`: the differential of the actions is invertible.
* `periodLattice_eq_closure_of_actionAngle`: the period lattice is spanned by the `p • da_j`.
* `injective_of_actionAngle`: the actions are injective on the base.
* `exists_lagrangian_section_of_actionAngle`: there is a smooth Lagrangian section.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 2 (the obstructions to global action–angle coordinates).
-/

public section

noncomputable section

open Bundle (TotalSpace)
open Function Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration

open CotangentBundle

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}
  {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) [Fact (0 < p)] {a : B → ι → ℝ}
  {Φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)}

variable (h : hσ.IsLagrangianTorusFibration J π) (hσc : σ.IsClosed)
  (hΦ : IsLocalDiffeomorph I
    ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ)
  (hΦσ : SmoothForm.mpullback Φ hΦ.contMDiff
    (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) =
      σ)
  (hΦa : ∀ y, torusActions p (Φ y) = a (π y))

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [FiniteDimensional ℝ F]
  [IsManifold J ∞ B] [T2Space B] in
include h hΦ hΦa in
/-- The actions `a` of global action–angle coordinates are smooth on the base, since `a ∘ π` is
the smooth map `I ∘ Φ` and `π` is a surjective submersion. -/
theorem contMDiff_of_actionAngle : ContMDiff J 𝓘(ℝ, ι → ℝ) ∞ a := by
  refine (h.isSubmersion.contMDiff_comp_iff h.surjective le_rfl).1 ?_
  rw [show a ∘ π = torusActions p ∘ Φ from funext fun y ↦ (hΦa y).symm]
  exact (contMDiff_torusActions p).comp hΦ.contMDiff

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [FiniteDimensional ℝ F] [IsManifold J ∞ B] [T2Space B] in
include h hΦa in
/-- In global action–angle coordinates with actions `a ∘ π`, the fibre over `b` has a point `x`,
and it has coordinates `κ(θ, a(b))` for some angles `θ`. -/
private theorem exists_apply_eq_actionAngleCover (b : B) :
    ∃ (x : π ⁻¹' {b}) (θ : ι → ℝ), Φ x = actionAngleCover p (θ, a b) := by
  obtain ⟨x⟩ := (h.isConnected_preimage_singleton b).nonempty.to_subtype
  obtain ⟨⟨θ, A⟩, hθ⟩ := surjective_actionAngleCover p (Φ x)
  refine ⟨x, θ, ?_⟩
  rw [← hθ, ← x.property, ← hΦa, ← hθ, torusActions_actionAngleCover]

/-- The covector `v ↦ c ⬝ᵥ v` on `ℝ^ι`, as a continuous linear map. -/
private def dotProductCLM (c : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (dotProductEquiv ℝ ι c)

private theorem dotProductCLM_apply (c v : ι → ℝ) : dotProductCLM c v = c ⬝ᵥ v := by
  simp [dotProductCLM, dotProductEquiv]

/-! ### The fibre action in action–angle coordinates -/

include hΦ hΦσ hΦa in
/-- **In global action–angle coordinates the fibre action translates the angles.** Let `Φ` be
global action–angle coordinates with actions `a ∘ π`, and let `α` be the covector
`v ↦ c ⬝ᵥ da_b(v)` at `b`. If a point `x` of the fibre over `b` has coordinates `κ(θ, a(b))`, then
the action of `α` moves it to the point with coordinates `κ(θ + c, a(b))`. -/
theorem apply_fiberAction_of_actionAngle (b : B) (c : ι → ℝ) {α : F →L[ℝ] ℝ}
    (hα : ∀ v, α v = c ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) a b v) (x : π ⁻¹' {b}) (θ : ι → ℝ)
    (hx : Φ x = actionAngleCover p (θ, a b)) :
    Φ (h.fiberAction hσc b α x) = actionAngleCover p (θ + c, a b) := by
  have ha := h.contMDiff_of_actionAngle p hΦ hΦa
  -- The function `g = c ⬝ᵥ a` on the base has differential `α` at `b`.
  set L : (ι → ℝ) →L[ℝ] ℝ := dotProductCLM c
  have hL (v : ι → ℝ) : L v = c ⬝ᵥ v := dotProductCLM_apply c v
  have hg : ContMDiff J 𝓘(ℝ) 2 (L ∘ a) := (L.contMDiff.comp ha).of_le (by simp)
  have hgα : mvfderiv J (L ∘ a) b = α := ContinuousLinearMap.ext fun v ↦ by
    rw [L.mvfderiv_comp_apply ((ha b).mdifferentiableAt (by simp)), hL,
      mvfderiv_apply_eq_mfderiv_apply]
    exact (hα v).symm
  -- On `M`, the function `g ∘ π` is the function `L ∘ I` of the actions read through `Φ`.
  have hcomp : (L ∘ a) ∘ π = (L ∘ torusActions p) ∘ Φ :=
    funext fun y ↦ by simp only [comp_apply, hΦa]
  have hX := h.isCompleteVectorField_hamiltonianVectorField_comp h.isProperMap hg
  rw [h.coe_fiberAction_eq_flowOf hσc b hg hgα x]
  rw [hcomp] at hX ⊢
  have hω := (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
    (M := ι → AddCircle p)).isNondegenerate
  have hLI : ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      𝓘(ℝ) ∞ (L ∘ torusActions p) := L.contMDiff.comp (contMDiff_torusActions p)
  -- `Φ` relates the two Hamiltonian vector fields, so it conjugates their flows.
  rw [(hΦ.contMDiff.mdifferentiable (by simp)).apply_flowOf
    (hω.contMDiff_hamiltonianVectorField (n := 1) (by simp) (hLI.of_le (by simp)))
    (fun z ↦ hσ.mfderiv_hamiltonianVectorField_comp hω hΦ.contMDiff hΦσ
      ((hΦ.isInvertible_mfderiv (by simp) z).surjective)
      ((hLI (Φ z)).mdifferentiableAt (by simp)))
    (hX.mem_flowDomain 1 x), hx]
  -- On `T*Tⁿ` the flow of `L ∘ I` turns the angles with the constant frequencies `c`.
  have hcurve := isMIntegralCurve_actionAngleCover_add_smul p θ (a b) (h := L) L.differentiableAt
  have hfreq : (fun j ↦ fderiv ℝ L (a b) (Pi.single j 1)) = c :=
    funext fun j ↦ by rw [L.fderiv, hL, dotProduct_single_one]
  rw [hfreq] at hcurve
  have h0 := flowOf_eq_of_isMIntegralCurve
    (hω.contMDiff_hamiltonianVectorField (n := 1) (by simp) (hLI.of_le (by simp))) hcurve 1
  simp only [zero_smul, add_zero, one_smul] at h0
  exact h0

include h hΦ hΦσ hΦa in
/-- **The fibres fill the tori of the actions.** For global action–angle coordinates with actions
`a ∘ π`, every point `κ(θ, a(b))` of the torus `{I = a(b)}` is the image of a point of the fibre
over `b`: translating the angles by the fibre action reaches it. -/
theorem exists_apply_eq_actionAngleCover_of_actionAngle (b : B) (θ : ι → ℝ) :
    ∃ y, π y = b ∧ Φ y = actionAngleCover p (θ, a b) := by
  -- `σ` is closed, as the pullback of the closed canonical form.
  have hσc : σ.IsClosed := hΦσ ▸ (isSymplectic_symplecticForm
    (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (M := ι → AddCircle p)).isClosed.mpullback Φ
    hΦ.contMDiff
  obtain ⟨x, θ₀, hθ₀⟩ := h.exists_apply_eq_actionAngleCover p hΦa b
  -- The covector `v ↦ (θ - θ₀) ⬝ᵥ da_b(v)` moves `x` to the point with angles `θ`.
  set α : F →L[ℝ] ℝ := (dotProductCLM (θ - θ₀)).comp (mfderiv J 𝓘(ℝ, ι → ℝ) a b)
  refine ⟨h.fiberAction hσc b α x, (h.fiberAction hσc b α x).property, ?_⟩
  rw [h.apply_fiberAction_of_actionAngle p hσc hΦ hΦσ hΦa b (θ - θ₀)
    (fun v ↦ dotProductCLM_apply _ _) x θ₀ hθ₀, add_sub_cancel]

/-! ### The differential of the actions -/

omit [T2Space M] [BoundarylessManifold I M] [IsManifold J ∞ B] [T2Space B] in
include h hΦ hΦa in
/-- **The differential of the actions is invertible.** For global action–angle coordinates with
actions `a ∘ π`, the differential `da_b : T_b B → ℝ^ι` is bijective at every point `b`: it is onto
since `a ∘ π = I ∘ Φ` is a submersion, and `B` has the dimension `|ι|` of the tori, half that of
`M`. -/
theorem bijective_mfderiv_of_actionAngle (b : B) :
    Bijective (mfderiv J 𝓘(ℝ, ι → ℝ) a b) := by
  obtain ⟨y, rfl⟩ : ∃ y, π y = b :=
    (h.isConnected_preimage_singleton b).nonempty.imp fun _ hy ↦ hy
  have : Nonempty M := ⟨y⟩
  have ha := h.contMDiff_of_actionAngle p hΦ hΦa
  have hcomp : a ∘ π = torusActions p ∘ Φ := funext fun y ↦ (hΦa y).symm
  -- The differential of `a ∘ π = I ∘ Φ` at `y` is onto, hence so is `da_(π y)`.
  have hsurj : Surjective (mfderiv J 𝓘(ℝ, ι → ℝ) a (π y)) := by
    intro w
    obtain ⟨u, hu⟩ := surjective_mfderiv_torusActions p (Φ y) w
    obtain ⟨v, rfl⟩ := (hΦ.isInvertible_mfderiv (by simp) y).surjective u
    refine ⟨mfderiv I J π y v, ?_⟩
    rw [← mfderiv_comp_apply y ((ha (π y)).mdifferentiableAt (by simp)) (h.mdifferentiableAt y),
      hcomp, mfderiv_comp_apply y
        ((contMDiff_torusActions p (Φ y)).mdifferentiableAt (by simp))
        ((hΦ.contMDiff y).mdifferentiableAt (by simp))]
    exact hu
  -- `B` has the dimension `|ι|`, half the dimension of `M`, which is that of `T*Tⁿ`.
  obtain ⟨e, -⟩ := hΦ.isInvertible_mfderiv (by simp) y
  have hE : Module.finrank ℝ E = Module.finrank ℝ ((ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) :=
    e.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod, ContinuousLinearMap.dual_finrank_eq, ← h.two_mul_finrank] at hE
  have hF : Module.finrank ℝ F = Module.finrank ℝ (ι → ℝ) := by omega
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hF).2 hsurj, hsurj⟩

/-! ### Exact periods -/

include hΦ hΦσ hΦa in
/-- **Global action–angle coordinates have exact periods.** For global action–angle coordinates
`Φ` with period `p` and actions `a ∘ π`, the period lattice at `b` is spanned by the covectors
`p • da_j(b)`. So the period lattice is framed by the exact one-forms `p • da_j`, and the linear
monodromy of the fibration is trivial. -/
theorem periodLattice_eq_closure_of_actionAngle (hΦi : Injective Φ) (b : B) :
    h.periodLattice hσc b = AddSubgroup.closure (range fun j ↦
      p • ((ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).comp
        (mfderiv J 𝓘(ℝ, ι → ℝ) a b) : F →L[ℝ] ℝ)) := by
  obtain ⟨x, θ, hθ⟩ := h.exists_apply_eq_actionAngleCover p hΦa b
  -- A covector `v ↦ c ⬝ᵥ da_b(v)` is a period exactly when `c ∈ p ℤ^ι`.
  have hmem (c : ι → ℝ) {α : F →L[ℝ] ℝ} (hα : ∀ v, α v = c ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) a b v) :
      α ∈ h.periodLattice hσc b ↔ ∃ m : ι → ℤ, c = fun i ↦ m i * p := by
    rw [h.mem_periodLattice_iff_fiberAction_eq hσc b x, Subtype.ext_iff, ← hΦi.eq_iff,
      h.apply_fiberAction_of_actionAngle p hσc hΦ hΦσ hΦa b c hα x θ hθ, hθ,
      actionAngleCover_eq_actionAngleCover_iff]
    constructor
    · rintro ⟨-, m, hm⟩
      refine ⟨-m, funext fun i ↦ ?_⟩
      have := congrFun hm i
      simp only [Pi.add_apply] at this
      simp only [Pi.neg_apply, Int.cast_neg]
      linarith
    · rintro ⟨m, hm⟩
      refine ⟨rfl, -m, funext fun i ↦ ?_⟩
      simp only [hm, Pi.add_apply, Pi.neg_apply, Int.cast_neg]
      ring
  refine le_antisymm (fun α hα ↦ ?_) ((AddSubgroup.closure_le _).2 ?_)
  · -- Every covector is `v ↦ c ⬝ᵥ da_b(v)`, since `da_b` is invertible.
    set D₀ : F →L[ℝ] ι → ℝ := mfderiv J 𝓘(ℝ, ι → ℝ) a b
    set D := LinearEquiv.ofBijective D₀.toLinearMap (h.bijective_mfderiv_of_actionAngle p hΦ hΦa b)
    set c : ι → ℝ := fun j ↦ α (D.symm (Pi.single j 1))
    have hα' (v : F) : α v = c ⬝ᵥ D₀ v := by
      calc α v = α (D.symm (∑ j, D₀ v j • Pi.single j (1 : ℝ))) := by
            rw [← pi_eq_sum_univ' (D₀ v)]
            exact congrArg α (LinearEquiv.ofBijective_symm_apply_apply D₀.toLinearMap v).symm
        _ = ∑ j, D₀ v j * c j := by simp only [map_sum, map_smul, smul_eq_mul, c]
        _ = c ⬝ᵥ D₀ v := by simp only [dotProduct, mul_comm]
    obtain ⟨m, hm⟩ := (hmem c hα').1 hα
    refine AddSubgroup.mem_closure_range_iff_of_fintype.2 ⟨m, ContinuousLinearMap.ext fun v ↦ ?_⟩
    rw [hα' v, hm]
    simp [dotProduct, zsmul_eq_mul, mul_assoc]
  · rintro _ ⟨j, rfl⟩
    refine (hmem (Pi.single j p) fun v ↦ ?_).2 ⟨Pi.single j 1, funext fun i ↦ ?_⟩
    · exact (single_dotProduct (v := (mfderiv J 𝓘(ℝ, ι → ℝ) a b v : ι → ℝ)) p j).symm
    · by_cases hij : i = j
      · subst hij; simp
      · simp [hij]

/-! ### Injective actions -/

include h hΦ hΦσ hΦa in
/-- **Global action–angle coordinates have injective actions.** For global action–angle
coordinates with actions `a ∘ π`, the developing map `a` is injective: translating the angles,
the fibre over `b` reaches every point of the torus `{I = a(b)}`, so two fibres with the same
actions have images meeting in a point, and coincide by injectivity of `Φ`. -/
theorem injective_of_actionAngle (hΦi : Injective Φ) : Injective a := by
  intro b b' hbb'
  obtain ⟨x', θ, hθ⟩ := h.exists_apply_eq_actionAngleCover p hΦa b'
  rw [← hbb'] at hθ
  -- The point of the fibre over `b` with the coordinates of `x'` is `x'`.
  obtain ⟨y, hy, hyθ⟩ := h.exists_apply_eq_actionAngleCover_of_actionAngle p hΦ hΦσ hΦa b θ
  rw [← hy, hΦi (hyθ.trans hθ.symm), x'.property]

/-! ### A Lagrangian section -/

include h hΦ hΦσ hΦa in
/-- **Global action–angle coordinates give a Lagrangian section.** For global action–angle
coordinates `Φ` with actions `a ∘ π`, the zero angles `θ = 0` define a smooth section `s` of `π`,
`Φ(s(b)) = κ(0, a(b))`, and `s^* σ = 0` because `κ(0, ·)` pulls the canonical form back to zero. -/
theorem exists_lagrangian_section_of_actionAngle (hΦi : Injective Φ) :
    ∃ (s : B → M) (hsm : ContMDiff J I ∞ s), (∀ b, π (s b) = b) ∧
      SmoothForm.mpullback s hsm σ = 0 := by
  rcases isEmpty_or_nonempty B with hB | ⟨⟨b₀⟩⟩
  · refine ⟨isEmptyElim, fun b ↦ isEmptyElim b, fun b ↦ isEmptyElim b, ?_⟩
    refine SmoothBundleForm.ext_eval₂ fun b ↦ isEmptyElim b
  have ha := h.contMDiff_of_actionAngle p hΦ hΦa
  -- The zero angles `κ(0, a(b))` are the coordinates of a point of the fibre over `b`.
  set g : B → (ι → ℝ) × (ι → ℝ) := fun b ↦ ((0 : ι → ℝ), a b)
  have hfib (b : B) : ∃ y, π y = b ∧ Φ y = actionAngleCover p (g b) :=
    h.exists_apply_eq_actionAngleCover_of_actionAngle p hΦ hΦσ hΦa b 0
  have : Nonempty M := ⟨(hfib b₀).choose⟩
  -- The section `s = Φ⁻¹ ∘ κ(0, a(·))`, smooth since `Φ` is an injective local diffeomorphism.
  set s : B → M := invFunOn Φ univ ∘ actionAngleCover p ∘ g
  have hΦs (b : B) : Φ (s b) = actionAngleCover p (g b) :=
    invFunOn_eq ⟨(hfib b).choose, mem_univ _, (hfib b).choose_spec.2⟩
  have hsm : ContMDiff J I ∞ s :=
    (IsLocalDiffeomorphOn.contMDiffOn_invFunOn (hΦ.isLocalDiffeomorphOn univ) isOpen_univ
      hΦi.injOn).comp_contMDiff
      ((contMDiff_actionAngleCover p).comp (contMDiff_const.prodMk_space ha))
      fun b ↦ ⟨(hfib b).choose, mem_univ _, (hfib b).choose_spec.2⟩
  refine ⟨s, hsm, fun b ↦ ?_, ?_⟩
  · obtain ⟨y, hy, hyg⟩ := hfib b
    rw [hΦi ((hΦs b).trans hyg.symm), hy]
  · -- `Φ ∘ s = κ(0, a(·))`, so `s^* σ` is the pullback of `ω` along the zero angles.
    rw [← hΦσ, SmoothForm.mpullback_mpullback_of_comp_eq hsm hΦ.contMDiff
      (contMDiff_const.prodMk_space ha) (contMDiff_actionAngleCover p) (funext hΦs),
      SmoothForm.mpullback_mpullback]
    exact mpullback_actionAngleCover_zero_comp_symplecticForm p ha

end TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration

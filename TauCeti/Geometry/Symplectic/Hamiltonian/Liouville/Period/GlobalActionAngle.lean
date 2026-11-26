/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Model
import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Compact
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle.Hamiltonian
import Mathlib.Algebra.Group.Subgroup.Finsupp
import TauCeti.Analysis.Calculus.FDeriv.Matrix
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LatticeQuotient.DevelopingMap
import TauCeti.Geometry.Manifold.Flow.Related
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
import TauCeti.LinearAlgebra.Matrix.TransposeLattice
import TauCeti.Topology.Algebra.Module.Matrix

/-!
# Global action–angle coordinates: Duistermaat's criterion and uniqueness

Let `σ` be a symplectic form on a boundaryless manifold `M`, let `π : M → B` be a regular
Lagrangian torus fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`)
and let `p > 0`. **Global action–angle coordinates** are an injective local diffeomorphism

`Φ : M → T*(ι → ℝ/pℤ)`

into the cotangent bundle of the torus which pulls the canonical form `ω = ∑ j, dθ_j ∧ dI_j` back
to `σ` and whose actions are functions on the base, `I ∘ Φ = a ∘ π` for a map `a : B → ℝ^ι`
(`TauCeti.CotangentBundle.torusActions`). This is the conclusion of
`IsLagrangianTorusFibration.exists_actionAngle_of_lagrangian_section`, the sufficiency half of
Duistermaat's criterion. This file proves the necessity half, and with it the criterion itself:
such a chart forces

* **exact periods**: the period lattice at `b` is spanned by the covectors `p • da_j(b)`
  (`IsLagrangianTorusFibration.periodLattice_eq_closure_of_actionAngle`), so the period forms are
  exact and globally framed, and the linear monodromy is trivial;
* **injective actions**: the developing map `a` is injective
  (`IsLagrangianTorusFibration.injective_of_actionAngle`);
* **a Lagrangian section**: the zero angles `θ = 0` give a smooth section `s` of `π` with
  `s^* σ = 0` (`IsLagrangianTorusFibration.exists_lagrangian_section_of_actionAngle`).

Together with `exists_actionAngle_of_lagrangian_section`, this characterizes the regular Lagrangian
torus fibrations admitting global action–angle coordinates, **Duistermaat's criterion**
(`IsLagrangianTorusFibration.exists_actionAngle_iff`): over a base of dimension `|ι|`, there are
global action–angle coordinates with actions `a ∘ π` exactly when `a` is smooth and injective, the
period lattice is spanned by the exact one-forms `p • da_j`, and `π` has a smooth Lagrangian
section. A globally framed period lattice has trivial linear monodromy, and conversely trivial
monodromy over a connected base gives a global frame of closed one-forms
(`IsLagrangianTorusFibration.exists_periodLattice_eq_closure_of_latticeMonodromyHom_eq_one`).

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

Such coordinates are **unique up to integral affine changes and an angle gauge**. If `Φ'` is a
second chart, with actions `a'`, over a preconnected base, then `a' = P a + b₀` for some
`P ∈ GL(ι, ℤ)` and `b₀ : ι → ℝ` (`IsLagrangianTorusFibration.exists_eq_mulVec_add_of_actionAngle`),
and in action–angle coordinates `Φ' ∘ Φ⁻¹` is `(θ, I) ↦ (P⁻ᵀ θ + g, P I + b₀)` for angles `g`,
smooth modulo `p ℤ^ι`, with `∑ i, dg_i ∧ da'_i = 0`
(`IsLagrangianTorusFibration.exists_eq_mulVec_add_and_apply_eq_actionAngleCover_of_actionAngle`).
So for local real lifts of `g` the one-form `∑ i, g_i dI'_i` in the actions `I' = a'` is closed, and
by the Poincaré lemma `g` is locally a gradient `∂S/∂I'` of a function of the actions: the angle
gauge of local action–angle coordinates.

The proof compares the period lattices. At each point both `p • da_j(b)` and `p • da'_j(b)` span
the period lattice, so `da' = N da` with `N ∈ GL(ι, ℤ)`
(`IsLagrangianTorusFibration.exists_mfderiv_eq_mulVec_of_actionAngle`). Read on the open set
`a(B)`, the map `a' ∘ a⁻¹` has these integer matrices as derivatives, so it is affine there
(`TauCeti.exists_eq_mulVec_add_of_forall_exists_fderiv_eq`). The covector `θ ⬝ᵥ da` then equals
`θ P⁻¹ ⬝ᵥ da'`, so the fibre action that moves the point `s(b)` with zero angles in `Φ` to the point
with angles `θ` translates the angles in `Φ'` by `θ P⁻¹`; the gauge `g(b)` is the angle of `s(b)`
in `Φ'`. Since `s` is Lagrangian, `Φ' ∘ s` pulls the canonical form back to zero, which in angle and
action differentials (`TauCeti.CotangentBundle.eval₂_symplecticForm_eq_dotProduct_sub`) is the
closedness of the gauge.

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`.

* `apply_fiberAction_of_actionAngle`: in global action–angle coordinates the covector
  `∑ j, c_j da_j(b)` translates the angles by `c`.
* `bijective_mfderiv_of_actionAngle`: the differential of the actions is invertible.
* `periodLattice_eq_closure_of_actionAngle`: the period lattice is spanned by the `p • da_j`.
* `injective_of_actionAngle`: the actions are injective on the base.
* `isOpen_range_and_exists_contMDiffOn_apply_eq_of_actionAngle`: the actions identify the base
  with the open set `a(B)`, with smooth inverse `c ↦ π(Φ⁻¹(κ(0, c)))`.
* `exists_lagrangian_section_of_actionAngle`: the zero angles give a smooth Lagrangian section.
* `exists_actionAngle_iff`: Duistermaat's criterion for global action–angle coordinates.
* `exists_mfderiv_eq_mulVec_of_actionAngle`: the differentials of the actions of two charts differ
  by an element of `GL(ι, ℤ)` at every point.
* `exists_eq_mulVec_add_of_actionAngle`: over a preconnected base, the actions of two charts differ
  by an integral affine change.
* `exists_eq_mulVec_add_and_apply_eq_actionAngleCover_of_actionAngle`: over a preconnected base,
  two charts differ by an integral affine change of the actions and an angle gauge.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Sections 1–2 (the integral affine structure of the actions, and the obstructions to
  global action–angle coordinates).
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

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [DecidableEq ι] in
include hΦσ in
/-- A symplectic form with global action–angle coordinates is closed, as the pullback of the closed
canonical form. -/
private theorem isClosed_of_actionAngle : σ.IsClosed :=
  hΦσ ▸ (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
    (M := ι → AddCircle p)).isClosed.mpullback Φ hΦ.contMDiff

include h hΦ hΦσ hΦa in
/-- **The fibres fill the tori of the actions.** For global action–angle coordinates with actions
`a ∘ π`, every point `κ(θ, a(b))` of the torus `{I = a(b)}` is the image of a point of the fibre
over `b`: translating the angles by the fibre action reaches it. -/
theorem exists_apply_eq_actionAngleCover_of_actionAngle (b : B) (θ : ι → ℝ) :
    ∃ y, π y = b ∧ Φ y = actionAngleCover p (θ, a b) := by
  have hσc := isClosed_of_actionAngle p hΦ hΦσ
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

include h hΦ hΦσ hΦa in
/-- **The actions identify the base with an open set of actions.** For global action–angle
coordinates `Φ` with actions `a ∘ π`, the set `a(B)` is open and the map `c ↦ π(Φ⁻¹(κ(0, c)))` is
smooth on `a(B)` and inverts `a`. -/
theorem isOpen_range_and_exists_contMDiffOn_apply_eq_of_actionAngle [Nonempty M]
    (hΦi : Injective Φ) :
    IsOpen (range a) ∧
      ∃ e : (ι → ℝ) → B, ContMDiffOn 𝓘(ℝ, ι → ℝ) J ∞ e (range a) ∧ ∀ b, e (a b) = b := by
  set k : (ι → ℝ) → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
    fun c ↦ actionAngleCover p ((0 : ι → ℝ), c)
  have hk : ContMDiff 𝓘(ℝ, ι → ℝ)
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ k :=
    (contMDiff_actionAngleCover p).comp (contMDiff_const.prodMk_space contMDiff_id)
  -- `a(B)` is the set of actions whose zero angles lie in the open image of `Φ`.
  have hV : range a = k ⁻¹' (Φ '' univ) := by
    ext c
    refine ⟨?_, fun ⟨y, _, hy⟩ ↦ ⟨π y, ?_⟩⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨y, -, hy⟩ := h.exists_apply_eq_actionAngleCover_of_actionAngle p hΦ hΦσ hΦa b 0
      exact ⟨y, mem_univ _, hy⟩
    · rw [← hΦa, hy, torusActions_actionAngleCover]
  refine ⟨by rw [hV, image_univ]; exact hΦ.isOpenMap.isOpen_range.preimage hk.continuous,
    π ∘ invFunOn Φ univ ∘ k, ?_, fun b ↦ ?_⟩
  · refine h.isSubmersion.contMDiff.comp_contMDiffOn
      ((IsLocalDiffeomorphOn.contMDiffOn_invFunOn (hΦ.isLocalDiffeomorphOn univ) isOpen_univ
        hΦi.injOn).comp hk.contMDiffOn fun c hc ↦ ?_)
    rwa [hV] at hc
  · -- `Φ⁻¹(κ(0, a b))` is the point with zero angles over `b`.
    obtain ⟨y, hyb, hy⟩ := h.exists_apply_eq_actionAngleCover_of_actionAngle p hΦ hΦσ hΦa b 0
    have hinv : invFunOn Φ univ (k (a b)) = y :=
      hΦi ((invFunOn_eq ⟨y, mem_univ _, hy⟩).trans hy.symm)
    simp only [Function.comp_apply, hinv, hyb]

/-! ### A Lagrangian section -/

include h hΦ hΦσ hΦa in
/-- **Global action–angle coordinates give a Lagrangian section.** For global action–angle
coordinates `Φ` with actions `a ∘ π`, the zero angles `θ = 0` define a smooth section `s` of `π`,
`Φ(s(b)) = κ(0, a(b))`, and `s^* σ = 0` because `κ(0, ·)` pulls the canonical form back to zero. -/
theorem exists_lagrangian_section_of_actionAngle (hΦi : Injective Φ) :
    ∃ (s : B → M) (hsm : ContMDiff J I ∞ s),
      (∀ b, π (s b) = b ∧ Φ (s b) = actionAngleCover p ((0 : ι → ℝ), a b)) ∧
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
  refine ⟨s, hsm, fun b ↦ ⟨?_, hΦs b⟩, ?_⟩
  · obtain ⟨y, hy, hyg⟩ := hfib b
    rw [hΦi ((hΦs b).trans hyg.symm), hy]
  · -- `Φ ∘ s = κ(0, a(·))`, so `s^* σ` is the pullback of `ω` along the zero angles.
    rw [← hΦσ, SmoothForm.mpullback_mpullback_of_comp_eq hsm hΦ.contMDiff
      (contMDiff_const.prodMk_space ha) (contMDiff_actionAngleCover p) (funext hΦs),
      SmoothForm.mpullback_mpullback]
    exact mpullback_actionAngleCover_zero_comp_symplecticForm p ha

/-! ### Duistermaat's criterion -/

include h in
/-- **Duistermaat's criterion for global action–angle coordinates.** Let `π` be a regular
Lagrangian torus fibration over a base of dimension `|ι|`. There are global action–angle
coordinates with period `p` and actions `a ∘ π` exactly when `a` is smooth and injective, the period
lattice is spanned at every point by the exact one-forms `p • da_j`, and `π` has a smooth Lagrangian
section. A period lattice spanned by a global frame has trivial linear monodromy
(`latticeMonodromyHom_eq_one_of_periodLattice_eq_closure_mvfderiv`), and conversely trivial
monodromy over a connected base gives a closed global frame
(`exists_periodLattice_eq_closure_of_latticeMonodromyHom_eq_one`); the period condition asks that
it can be chosen exact with an injective developing map. -/
theorem exists_actionAngle_iff [BoundarylessManifold J B]
    (hι : Fintype.card ι = Module.finrank ℝ F) :
    (∃ (Φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
        (hΦ : IsLocalDiffeomorph I
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ),
        Injective Φ ∧
          SmoothForm.mpullback Φ hΦ.contMDiff (CotangentBundle.symplecticForm
            (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) = σ ∧
          ∀ y, torusActions p (Φ y) = a (π y)) ↔
      ContMDiff J 𝓘(ℝ, ι → ℝ) ∞ a ∧ Injective a ∧
        (∀ b, h.periodLattice hσc b = AddSubgroup.closure (range fun j ↦
          p • ((ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).comp
            (mfderiv J 𝓘(ℝ, ι → ℝ) a b) : F →L[ℝ] ℝ))) ∧
        ∃ (s : B → M) (hsm : ContMDiff J I ∞ s), (∀ b, π (s b) = b) ∧
          SmoothForm.mpullback s hsm σ = 0 := by
  constructor
  · rintro ⟨Φ, hΦ, hΦi, hΦσ, hΦa⟩
    obtain ⟨s, hsm, hs, hsσ⟩ := h.exists_lagrangian_section_of_actionAngle p hΦ hΦσ hΦa hΦi
    exact ⟨h.contMDiff_of_actionAngle p hΦ hΦa, h.injective_of_actionAngle p hΦ hΦσ hΦa hΦi,
      h.periodLattice_eq_closure_of_actionAngle p hσc hΦ hΦσ hΦa hΦi, s, hsm, fun b ↦ (hs b).1,
      hsσ⟩
  · rintro ⟨ha, hinj, hΛ, s, hsm, hs, hsσ⟩
    -- The exact frame `α_j = p • da_j` spans the period lattice.
    let α : ι → SmoothForm J B ℝ 1 := CotangentBundle.developingForm p ⟨a, ha⟩
    have hα (j : ι) (b : B) (v : TangentSpace J b) :
        SmoothForm.degreeOneEquiv (α j) b v = p * mfderiv J 𝓘(ℝ, ι → ℝ) a b v j :=
      CotangentBundle.degreeOneEquiv_developingForm_apply p ⟨a, ha⟩ j b v
    have hαΛ (b : B) : (fun j ↦ (SmoothForm.degreeOneEquiv (α j) b : F →L[ℝ] ℝ)) =
        fun j ↦ p • ((ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).comp
          (mfderiv J 𝓘(ℝ, ι → ℝ) a b) : F →L[ℝ] ℝ) :=
      funext fun j ↦ ContinuousLinearMap.ext fun v ↦ by
        rw [hα]
        -- Both sides are `p * da_b(v)_j`, read through the definitional identification
        -- `TangentSpace J b = F`, which `simp` does not see through.
        rfl
    have hli (b : B) : LinearIndependent ℝ fun j ↦ SmoothForm.degreeOneEquiv (α j) b := by
      rw [hαΛ]
      exact h.linearIndependent_of_periodLattice_le_closure hσc hι.le (hΛ b).le
    have hframe : IsLocalFrameOn J (F →L[ℝ] ℝ) ∞
        (fun j b ↦ SmoothForm.degreeOneEquiv (α j) b) univ :=
      .of_linearIndependent_of_card_eq_finrank (by simp [hι, ContinuousLinearMap.dual_finrank_eq])
        (fun j ↦ (SmoothForm.degreeOneEquiv (α j)).contMDiff.contMDiffOn) fun b _ ↦ hli b
    obtain ⟨Φ, hΦ, hΦi, hΦσ, hΦa, -⟩ := h.exists_actionAngle_of_lagrangian_section hσc hs hframe
      -- The two spanning families agree up to the definitional identification
      -- `TangentSpace J b = F`.
      (fun b ↦ (hΛ b).trans (by rw [hαΛ]; rfl)) p hsm hsσ ha hα hinj
    exact ⟨Φ, hΦ, hΦi, hΦσ, hΦa⟩

/-! ### Uniqueness of global action–angle coordinates -/

section Uniqueness

open Matrix

variable {a' : B → ι → ℝ}
  {Φ' : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)}
  (hΦ' : IsLocalDiffeomorph I
    ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ')
  (hΦ'σ : SmoothForm.mpullback Φ' hΦ'.contMDiff
    (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) =
      σ)
  (hΦ'a : ∀ y, torusActions p (Φ' y) = a' (π y))

include h hΦ hΦσ hΦa hΦ' hΦ'σ hΦ'a in
/-- **The actions of two global action–angle charts differ by `GL(ι, ℤ)` to first order.** If `Φ`
and `Φ'` are global action–angle coordinates with period `p` for the same fibration, with actions
`a ∘ π` and `a' ∘ π`, then at every point `b` of the base `da'_b = N da_b` for an invertible
integer matrix `N`: the covectors `p • da_j(b)` and `p • da'_j(b)` are two bases of the period
lattice at `b`. -/
theorem exists_mfderiv_eq_mulVec_of_actionAngle (hΦi : Injective Φ) (hΦ'i : Injective Φ')
    (b : B) :
    ∃ N : GL ι ℤ, ∀ v, mfderiv J 𝓘(ℝ, ι → ℝ) a' b v =
      (N : Matrix ι ι ℤ).map (↑) *ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) a b v := by
  have hσc := isClosed_of_actionAngle p hΦ hΦσ
  -- The period lattice at `b` is spanned both by the `p • da_j(b)` and by the `p • da'_j(b)`;
  -- dividing by `p`, the `da_j(b)` and the `da'_j(b)` span the same subgroup of covectors.
  have hcl (D : F →L[ℝ] ι → ℝ) : AddSubgroup.closure (range fun j ↦
      p • ((ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).comp D : F →L[ℝ] ℝ)) =
      (AddSubgroup.closure (range fun j ↦
        (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).comp D)).map
        (DistribSMul.toAddMonoidHom (F →L[ℝ] ℝ) p) := by
    rw [AddMonoidHom.map_closure, ← range_comp]
    simp [Function.comp_def]
  have hL : AddSubgroup.closure (range fun j ↦
      (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).comp (mfderiv J 𝓘(ℝ, ι → ℝ) a b)) =
      AddSubgroup.closure (range fun j ↦
        (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).comp (mfderiv J 𝓘(ℝ, ι → ℝ) a' b)) := by
    refine AddSubgroup.map_injective (f := DistribSMul.toAddMonoidHom (F →L[ℝ] ℝ) p)
      (fun α β hαβ ↦ smul_right_injective _ (Fact.out : 0 < p).ne' (by simpa using hαβ)) ?_
    exact (hcl _).symm.trans
      (((h.periodLattice_eq_closure_of_actionAngle p hσc hΦ hΦσ hΦa hΦi b).symm.trans
        (h.periodLattice_eq_closure_of_actionAngle p hσc hΦ' hΦ'σ hΦ'a hΦ'i b)).trans (hcl _))
  exact ContinuousLinearMap.exists_generalLinearGroup_mulVec_eq_of_closure_range_proj_comp_eq
    (h.bijective_mfderiv_of_actionAngle p hΦ hΦa b).2 hL

include h hΦ hΦσ hΦa hΦ' hΦ'a in
/-- The actions `a` identify the base with the open set `a(B)`, on which `a' ∘ a⁻¹` is smooth. -/
private theorem exists_contDiffOn_apply_eq_of_actionAngle [Nonempty M] (hΦi : Injective Φ) :
    IsOpen (range a) ∧
      ∃ A' : (ι → ℝ) → ι → ℝ, ContDiffOn ℝ 1 A' (range a) ∧ ∀ b, A' (a b) = a' b := by
  obtain ⟨hVo, e, he, hea⟩ :=
    h.isOpen_range_and_exists_contMDiffOn_apply_eq_of_actionAngle p hΦ hΦσ hΦa hΦi
  refine ⟨hVo, a' ∘ e, ?_, fun b ↦ by simp [hea]⟩
  exact (contMDiffOn_iff_contDiffOn.1
    ((h.contMDiff_of_actionAngle p hΦ' hΦ'a).comp_contMDiffOn he)).of_le (by simp)

include h hΦ hΦσ hΦa hΦ' hΦ'σ hΦ'a in
/-- **Global actions are unique up to integral affine changes.** If `Φ` and `Φ'` are global
action–angle coordinates with period `p` for the same fibration over a preconnected base, with
actions `a ∘ π` and `a' ∘ π`, then `a' = P a + b₀` for some `P ∈ GL(ι, ℤ)` and `b₀ : ι → ℝ`, and
hence `da' = P da` at every point. -/
theorem exists_eq_mulVec_add_of_actionAngle [PreconnectedSpace B] (hΦi : Injective Φ)
    (hΦ'i : Injective Φ') :
    ∃ (P : GL ι ℤ) (b₀ : ι → ℝ), (∀ b, a' b = (P : Matrix ι ι ℤ).map (↑) *ᵥ a b + b₀) ∧
      ∀ b v, mfderiv J 𝓘(ℝ, ι → ℝ) a' b v =
        (P : Matrix ι ι ℤ).map (↑) *ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) a b v := by
  rcases isEmpty_or_nonempty B with hB | ⟨⟨b₁⟩⟩
  · exact ⟨1, 0, isEmptyElim, isEmptyElim⟩
  have : Nonempty M := (h.isConnected_preimage_singleton b₁).nonempty.to_subtype.map (↑)
  have ha := h.contMDiff_of_actionAngle p hΦ hΦa
  obtain ⟨hVo, A', hA', hA'a⟩ :=
    h.exists_contDiffOn_apply_eq_of_actionAngle p hΦ hΦσ hΦa hΦ' hΦ'a hΦi
  -- At `c = a b`, the derivative of `A' = a' ∘ a⁻¹` is the matrix relating `da'_b` and `da_b`.
  choose N hN using h.exists_mfderiv_eq_mulVec_of_actionAngle p hΦ hΦσ hΦa hΦ' hΦ'σ hΦ'a hΦi hΦ'i
  have hfd (b : B) (w : ι → ℝ) :
      fderiv ℝ A' (a b) w = ((N b : GL ι ℤ) : Matrix ι ι ℤ).map (↑) *ᵥ w := by
    have hdA : DifferentiableAt ℝ A' (a b) :=
      (hA'.differentiableOn one_ne_zero (a b) ⟨b, rfl⟩).differentiableAt
        (hVo.mem_nhds ⟨b, rfl⟩)
    obtain ⟨v, rfl⟩ := (h.bijective_mfderiv_of_actionAngle p hΦ hΦa b).2 w
    have hcomp := mfderiv_comp_apply (I' := 𝓘(ℝ, ι → ℝ)) b hdA.mdifferentiableAt
      ((ha b).mdifferentiableAt (by simp)) v
    -- The manifold derivative of a map between normed spaces is its Fréchet derivative.
    rw [show A' ∘ a = a' from funext hA'a, mfderiv_eq_fderiv] at hcomp
    exact hcomp.symm.trans (hN b v)
  obtain ⟨M₀, b₀, hMb⟩ := exists_eq_mulVec_add_of_forall_exists_fderiv_eq hVo
    (isPreconnected_range ha.continuous) contDiffOn_id hA'
    (fun c _ ↦ by simpa [fderiv_id] using injective_id)
    (by
      rintro _ ⟨b, rfl⟩
      exact ⟨N b, fun w ↦ by simpa [fderiv_id] using hfd b w⟩)
  -- The constant matrix is every `N b`, the derivative of `A' = M₀ c + b₀` at `a b`.
  have hM (b : B) : M₀ = N b := by
    have hd := (hasFDerivAt_id (a b)).of_eventuallyEq_mulVec_add
      (Filter.eventually_of_mem (hVo.mem_nhds ⟨b, rfl⟩) hMb)
    refine Matrix.map_injective (Int.cast_injective (α := ℝ))
      (Matrix.toLin'.injective (LinearMap.ext fun u ↦ ?_))
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← hfd b, hd.fderiv]
    simp
  refine ⟨N b₁, b₀, fun b ↦ by rw [← hA'a, hMb _ ⟨b, rfl⟩, hM, id], fun b v ↦ ?_⟩
  rw [hN b v, ← hM, hM b₁]

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [FiniteDimensional ℝ F] [T2Space B] in
include hΦ'σ hΦ'a in
/-- Along a Lagrangian section `s` of `π`, the angles `θ` of `Φ' ∘ s` and the actions `a'` satisfy
`dθ(v) ⬝ᵥ da'(w) = dθ(w) ⬝ᵥ da'(v)`, since `(Φ' ∘ s)^* ω = s^* σ = 0`. -/
private theorem mfderiv_proj_dotProduct_comm_of_lagrangian {s : B → M}
    (hsm : ContMDiff J I ∞ s) (hs : ∀ b, π (s b) = b) (hsσ : SmoothForm.mpullback s hsm σ = 0)
    (b : B) (v w : TangentSpace J b) :
    mfderiv J (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun b ↦ (Φ' (s b)).proj) b v ⬝ᵥ
        mfderiv J 𝓘(ℝ, ι → ℝ) a' b w =
      mfderiv J (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun b ↦ (Φ' (s b)).proj) b w ⬝ᵥ
        mfderiv J 𝓘(ℝ, ι → ℝ) a' b v := by
  have hΨ := ((hΦ'.contMDiff.comp hsm) b).mdifferentiableAt (n := ∞) (by simp)
  -- `(Φ' ∘ s)^* ω = s^* σ = 0`.
  have h0 : SmoothBundleForm.eval₂ (SmoothForm.mpullback s hsm σ) b v w = 0 := by
    rw [hsσ]
    simp
  simp only [← hΦ'σ, SmoothForm.mpullback_mpullback, SmoothForm.eval₂_mpullback] at h0
  rw [eval₂_symplecticForm_eq_dotProduct_sub, sub_eq_zero] at h0
  -- The angles and actions of `Φ' ∘ s` are `proj ∘ Φ' ∘ s` and `a'`.
  have hIΨ : torusActions p ∘ Φ' ∘ s = a' := funext fun b ↦ by simp [hΦ'a, hs]
  have hproj (u : TangentSpace J b) :
      mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) TotalSpace.proj (Φ' (s b))
          (mfderiv J _ (Φ' ∘ s) b u) =
        mfderiv J (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun b ↦ (Φ' (s b)).proj) b u :=
    (mfderiv_comp_apply b
      ((Bundle.contMDiff_proj (n := ∞) _ (Φ' (s b))).mdifferentiableAt (by simp)) hΨ u).symm
  have hI (u : TangentSpace J b) :
      mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          𝓘(ℝ, ι → ℝ) (torusActions p) (Φ' (s b)) (mfderiv J _ (Φ' ∘ s) b u) =
        mfderiv J 𝓘(ℝ, ι → ℝ) a' b u :=
    (mfderiv_comp_apply b ((contMDiff_torusActions p (Φ' (s b))).mdifferentiableAt (by simp)) hΨ
      u).symm.trans (congrArg (fun f ↦ mfderiv J 𝓘(ℝ, ι → ℝ) f b u) hIΨ)
  rwa [Function.comp_apply, hproj, hproj, hI, hI] at h0

include h hΦ hΦσ hΦa hΦ' hΦ'σ hΦ'a in
/-- **Uniqueness of global action–angle coordinates.** Let `Φ` and `Φ'` be global action–angle
coordinates with period `p` for the same fibration over a preconnected base, with actions `a ∘ π`
and `a' ∘ π`. Then they differ by an integral affine change of the actions together with the
corresponding change of the angles and an angle gauge: there are `P ∈ GL(ι, ℤ)`, `b₀ : ι → ℝ`
and angles `g : B → ι → ℝ`, smooth modulo `p ℤ^ι`, such that `a' = P a + b₀` and, at every point
with coordinates `Φ x = κ(θ, a(π x))`,

`Φ' x = κ(θ P⁻¹ + g(π x), P a(π x) + b₀)`,

that is, `(θ, I) ↦ (P⁻ᵀ θ + g, P I + b₀)` in action–angle coordinates: the integral affine change
`TauCeti.CotangentBundle.integralAffineDiffeomorph P⁻ᵀ b₀` followed by a translation of the angles
by `g`. The gauge `g(b)` is the angle in `Φ'` of the point with zero angles in `Φ` over `b`, and it
is closed in the actions: `dg(v) ⬝ᵥ da'(w) = dg(w) ⬝ᵥ da'(v)`, that is, `∑ i, dg_i ∧ da'_i = 0`. -/
theorem exists_eq_mulVec_add_and_apply_eq_actionAngleCover_of_actionAngle [PreconnectedSpace B]
    (hΦi : Injective Φ) (hΦ'i : Injective Φ') :
    ∃ (P : GL ι ℤ) (b₀ : ι → ℝ) (g : B → ι → ℝ),
      (∀ b, a' b = (P : Matrix ι ι ℤ).map (↑) *ᵥ a b + b₀) ∧
      ContMDiff J (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ (fun b i ↦ (g b i : AddCircle p)) ∧
      (∀ b v w,
        mfderiv J (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun b i ↦ (g b i : AddCircle p)) b v ⬝ᵥ
            mfderiv J 𝓘(ℝ, ι → ℝ) a' b w =
          mfderiv J (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun b i ↦ (g b i : AddCircle p)) b w ⬝ᵥ
            mfderiv J 𝓘(ℝ, ι → ℝ) a' b v) ∧
      ∀ x θ, Φ x = actionAngleCover p (θ, a (π x)) →
        Φ' x = actionAngleCover p
          (θ ᵥ* ((P⁻¹ : GL ι ℤ) : Matrix ι ι ℤ).map (↑) + g (π x), a' (π x)) := by
  have hσc := isClosed_of_actionAngle p hΦ hΦσ
  obtain ⟨P, b₀, hP, hdP⟩ :=
    h.exists_eq_mulVec_add_of_actionAngle p hΦ hΦσ hΦa hΦ' hΦ'σ hΦ'a hΦi hΦ'i
  -- The points `s b` with zero angles in `Φ`, and their angles `g b` in `Φ'`.
  obtain ⟨s, hsm, hs, hsσ⟩ := h.exists_lagrangian_section_of_actionAngle p hΦ hΦσ hΦa hΦi
  have hg (b : B) : ∃ θ : ι → ℝ, Φ' (s b) = actionAngleCover p (θ, a' b) := by
    obtain ⟨⟨θ, A⟩, hθ⟩ := surjective_actionAngleCover p (Φ' (s b))
    have hA : A = a' b := by
      rw [← (hs b).1, ← hΦ'a, ← hθ, torusActions_actionAngleCover]
    exact ⟨θ, hθ ▸ hA ▸ rfl⟩
  choose g hg using hg
  -- `[g b]` is the base point of `Φ'(s b)`.
  have hgs : (fun b i ↦ (g b i : AddCircle p)) = fun b ↦ (Φ' (s b)).proj :=
    funext fun b ↦ by rw [hg b, proj_actionAngleCover]
  refine ⟨P, b₀, g, hP, hgs ▸ (Bundle.contMDiff_proj _).comp (hΦ'.contMDiff.comp hsm),
    hgs ▸ mfderiv_proj_dotProduct_comm_of_lagrangian p hΦ' hΦ'σ hΦ'a hsm (fun b ↦ (hs b).1) hsσ,
    fun x θ hx ↦ ?_⟩
  -- The covector `α = θ ⬝ᵥ da` is `θ P⁻¹ ⬝ᵥ da'`, and moves `s b` to `x`.
  set b := π x
  set Q : Matrix ι ι ℝ := ((P⁻¹ : GL ι ℤ) : Matrix ι ι ℤ).map (↑)
  have hQP : Q * (P : Matrix ι ι ℤ).map (↑) = 1 :=
    congrArg Units.val (Matrix.GeneralLinearGroup.map_inv_mul_map (Int.castRingHom ℝ) P)
  set α : F →L[ℝ] ℝ := (dotProductCLM θ).comp (mfderiv J 𝓘(ℝ, ι → ℝ) a b)
  have hα (v : F) : α v = θ ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) a b v := dotProductCLM_apply _ _
  have hα' (v : F) : α v = (θ ᵥ* Q) ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) a' b v := by
    rw [hα, hdP b v]
    refine Eq.symm ((dotProduct_mulVec _ _ _).trans ?_)
    rw [vecMul_vecMul, hQP, vecMul_one]
  let x₀ : π ⁻¹' {b} := ⟨s b, (hs b).1⟩
  have h₁ := h.apply_fiberAction_of_actionAngle p hσc hΦ hΦσ hΦa b θ hα x₀ 0 (hs b).2
  have hx₀ : (h.fiberAction hσc b α x₀ : M) = x := hΦi (h₁.trans (by rw [zero_add, hx]))
  have h₂ := h.apply_fiberAction_of_actionAngle p hσc hΦ' hΦ'σ hΦ'a b (θ ᵥ* Q) hα' x₀ (g b)
    (hg b)
  rw [hx₀, add_comm] at h₂
  exact h₂

end Uniqueness

end TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Constant vector fields and translation loops of a torus

For a finite family of positive periods `p i`, the tangent space of the torus
`Tⁿ = ∀ i, AddCircle (p i)` at every point is `ι → ℝ`, read in its product charts. A vector
`c : ι → ℝ` therefore defines the constant vector field `x ↦ c` on the torus
(`TauCeti.torusConstVectorField p c`). It is analytic: through the covering map
`(ι → ℝ) → Tⁿ`, a surjective local diffeomorphism with derivative the identity
(`AddCircle.isLocalDiffeomorph_coe_pi`), it is the derivative of the covering map applied to the
constant vector `c`.

The integral curves of the constant field are the straight lines `t ↦ x + [t c]`, so its flow is
the translation flow of the torus with velocity `c`
(`TauCeti.flowOf_torusConstVectorField`), and it is complete. Running it for unit time gives the
diffeotopy `(t, x) ↦ x + [t c]`, `t ∈ [0, 1]`, of the torus, which ends at the translation by
`[c]`. This translation is the identity exactly when every coordinate `c i` is an integer multiple
of the period `p i` (`TauCeti.final_globalFlowDiffeotopy_torusConstVectorField_eq_refl_iff`). The
diffeotopies with such integral velocities are the translation loops of the torus. They are loops
of diffeomorphisms based at the identity, and their fluxes for an invariant area form are
computed in `TauCeti.Geometry.Symplectic.Flux.Torus`.

## Main definitions

* `TauCeti.torusConstVectorField p c`: the constant vector field `c` on the torus.

## Main results

* `TauCeti.isMIntegralCurve_torusConstVectorField`: its integral curves are the lines
  `t ↦ x + [t c]`.
* `TauCeti.isCompleteVectorField_torusConstVectorField`: it is complete.
* `TauCeti.flowOf_torusConstVectorField`: its flow is translation by `[t c]`.
* `TauCeti.final_globalFlowDiffeotopy_torusConstVectorField_eq_refl_iff`: its unit-time
  diffeotopy is a loop exactly when `c` lies in the period lattice.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 9 (flows and their infinitesimal generators).
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-- The lifted constant field `t ↦ ([t], c)` on the covering space `ι → ℝ` of the torus is
analytic. -/
private theorem contMDiff_totalSpaceMk_coe_pi (c : ι → ℝ) {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).tangent n
      (fun t : ι → ℝ ↦ (⟨fun i ↦ (t i : AddCircle (p i)), c⟩ :
        TangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))) := by
  -- The section `t ↦ ([t], d(↑)_t c)` of the derivative of the covering map is analytic, and
  -- `d(↑)_t` is the identity.
  refine (contMDiffOn_univ.1 (((AddCircle.contMDiff_coe_pi p ω).contMDiffOn (s := Set.univ)
    ).contMDiffOn_totalSpaceMk_mfderiv_apply (m := n) le_top isOpen_univ c)).congr fun t ↦ ?_
  rw [(AddCircle.hasMFDerivAt_coe_pi p t).mfderiv]
  -- Both sides are `⟨[t], c⟩`: `ContinuousLinearMap.id ℝ (ι → ℝ) c` is `c` by definition, but
  -- `simp` cannot rewrite it inside the tangent-bundle point, whose fibre is a `TangentSpace`.
  rfl

/-- The constant vector field `x ↦ c` on the torus `∀ i, AddCircle (p i)`, whose tangent spaces
are all `ι → ℝ`. It is the derivative of the covering map `(ι → ℝ) → ∀ i, AddCircle (p i)`
applied to the constant vector `c`, and it generates the translations `x ↦ x + [t c]`
(`TauCeti.flowOf_torusConstVectorField`). -/
def torusConstVectorField (c : ι → ℝ) :
    Cₛ^∞⟮ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ); ι → ℝ,
      TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (M := ∀ i, AddCircle (p i))⟯ where
  toFun _ := c
  contMDiff_toFun := by
    rw [← ((AddCircle.isLocalDiffeomorph_coe_pi p (n := ω) (by simp))
      ).contMDiff_comp_iff (AddCircle.coe_pi_surjective p) le_top]
    exact contMDiff_totalSpaceMk_coe_pi p c

/-- The constant vector field takes the value `c` at every point. -/
@[simp]
theorem torusConstVectorField_apply (c : ι → ℝ) (x : ∀ i, AddCircle (p i)) :
    torusConstVectorField p c x = c :=
  (rfl)

/-- The integral curves of the constant vector field `c` are the lines `t ↦ x + [t c]`, defined
for all time. -/
theorem isMIntegralCurve_torusConstVectorField (c : ι → ℝ) (x : ∀ i, AddCircle (p i)) :
    IsMIntegralCurve (fun t : ℝ ↦ x + fun i ↦ ((t * c i : ℝ) : AddCircle (p i)))
      (torusConstVectorField p c) := by
  obtain ⟨y, rfl⟩ := AddCircle.coe_pi_surjective p x
  intro t
  -- The line is the covering map composed with the real line `t ↦ y + t • c`, whose velocity is
  -- `c`, and the covering map has derivative the identity.
  have hline := (((hasDerivAt_id t).smul_const c).const_add y).hasFDerivAt.hasMFDerivAt
  have hfun : (fun t : ℝ ↦ (fun i ↦ (y i : AddCircle (p i))) +
      fun i ↦ ((t * c i : ℝ) : AddCircle (p i))) =
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) ∘ fun t : ℝ ↦ y + t • c := by
    funext t i
    simp
  rw [hfun]
  refine ((AddCircle.hasMFDerivAt_coe_pi p (y + t • c)).comp t hline).congr_mfderiv ?_
  have hd : (ContinuousLinearMap.id ℝ (ι → ℝ)).comp
      (ContinuousLinearMap.toSpanSingleton ℝ ((1 : ℝ) • c)) = (1 : ℝ →L[ℝ] ℝ).smulRight c := by
    rw [ContinuousLinearMap.id_comp, one_smul,
      ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  simp only [torusConstVectorField_apply]
  exact hd

/-- The constant vector field of the torus is complete. -/
theorem isCompleteVectorField_torusConstVectorField (c : ι → ℝ) :
    IsCompleteVectorField (torusConstVectorField p c) :=
  isCompleteVectorField_of_compactSpace ((torusConstVectorField p c).contMDiff.of_le (by simp))

/-- **The flow of a constant vector field.** The time-`t` map of the flow of the constant vector
field `c` on the torus is the translation `x ↦ x + [t c]`. -/
theorem flowOf_torusConstVectorField (c : ι → ℝ) (t : ℝ) (x : ∀ i, AddCircle (p i)) :
    flowOf (torusConstVectorField p c) t x = x + fun i ↦ ((t * c i : ℝ) : AddCircle (p i)) := by
  simpa [← Pi.zero_def] using flowOf_eq_of_isMIntegralCurve
    ((torusConstVectorField p c).contMDiff.of_le (by simp))
    (isMIntegralCurve_torusConstVectorField p c x) t

/-- **Translation loops of the torus.** The diffeotopy which runs the constant vector field `c` of
the torus for unit time, `(t, x) ↦ x + [t c]`, ends at the identity exactly when every coordinate
`c i` is an integer multiple of the period `p i`. -/
theorem final_globalFlowDiffeotopy_torusConstVectorField_eq_refl_iff (c : ι → ℝ) :
    (globalFlowDiffeotopy le_top (torusConstVectorField p c).contMDiff
        (isCompleteVectorField_torusConstVectorField p c) 1).final =
      Diffeomorph.refl (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ∞ ↔
      ∀ i, c i ∈ AddSubgroup.zmultiples (p i) := by
  rw [Diffeomorph.ext_iff]
  simp only [Diffeotopy.final_def, Diffeotopy.timeSlice_globalFlowDiffeotopy,
    flowOf_torusConstVectorField, Diffeomorph.coe_refl, id_eq, add_eq_left, Set.Icc.coe_one,
    mul_one, one_mul]
  -- The translation by `[c]` fixes every point exactly when `[c] = 0`.
  refine ⟨fun h i ↦ ?_, fun h _ ↦ funext fun i ↦ ?_⟩
  · have := congrFun (h 0) i
    rwa [Pi.zero_apply, AddCircle.coe_eq_zero_iff, ← AddSubgroup.mem_zmultiples_iff] at this
  · exact (AddCircle.coe_eq_zero_iff (p i)).2 (AddSubgroup.mem_zmultiples_iff.1 (h i))

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.OrderedFlow
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Stabilizer
public import TauCeti.Geometry.Symplectic.Flux.Flow
public import TauCeti.Geometry.Symplectic.Flux.Trans

/-!
# The flux of ordered symplectic flows

Let `σ` be a closed two-form on a boundaryless finite-dimensional manifold `M`, for instance a
symplectic form, and let `Y₀, …, Y_(k-1)` be complete smooth symplectic vector fields, those whose
contractions `ι_(Y i) σ` are closed (`TauCeti.SmoothTwoForm.symplecticVectorFields`). For smooth
time functions `A i : ℝ → ℝ` with `A i 0 = 0`, the **ordered symplectic flow**

`ψ_t = ψ^(Y 0)_(A 0 t) ∘ ⋯ ∘ ψ^(Y (k-1))_(A (k-1) t)`

(`TauCeti.orderedGlobalFlowDiffeotopy`) is a diffeotopy all of whose maps preserve `σ`
(`TauCeti.Diffeotopy.timeSlice_orderedGlobalFlowDiffeotopy_mem_diffeomorphStabilizer`). Its flux
is

`Flux(ψ) = ∑ i, A i 1 [ι_(Y i) σ]`

(`TauCeti.Diffeotopy.flux_orderedGlobalFlowDiffeotopy`): each factor running `Y i` along `A i` has
flux `A i 1 [ι_(Y i) σ]` (`TauCeti.Diffeotopy.flux_globalFlowDiffeotopyAlong`), whatever the
time function in between, and the flux is additive on pointwise composites
(`TauCeti.Diffeotopy.flux_trans`).

These are the flows that correct a symplectic isotopy `φ_t` whose instantaneous contraction
classes are `[ι_(X_t) σ] = ∑ i, a i t [ι_(Y i) σ]`: with `A i t = ∫₀ᵗ a i`, the isotopy
`ψ_t⁻¹ ∘ φ_t` then has exact contractions. If the flux of `φ` vanishes and the classes
`[ι_(Y i) σ]` are linearly independent, every total time `A i 1` vanishes. Then `ψ` is a loop,
and it contracts to the constant diffeotopy relative to both time ends through maps preserving
`σ`, by scaling all the time functions by `1 - s`
(`TauCeti.Diffeotopy.exists_homotopy_orderedGlobalFlowDiffeotopy_mem_diffeomorphStabilizer`).

## Main results

* `TauCeti.Diffeotopy.timeSlice_orderedGlobalFlowDiffeotopy_mem_diffeomorphStabilizer`: ordered
  symplectic flows are symplectic isotopies.
* `TauCeti.exists_mem_diffeomorphStabilizer_coe_eq_orderedFlowOf`: every ordered flow
  of complete symplectic fields preserves `σ`.
* `TauCeti.Diffeotopy.flux_orderedGlobalFlowDiffeotopy`: the flux of an ordered symplectic flow.
* `TauCeti.Diffeotopy.exists_homotopy_orderedGlobalFlowDiffeotopy_mem_diffeomorphStabilizer`: an
  ordered symplectic flow with vanishing total times contracts relative to both time ends through
  maps preserving `σ`.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the proof of Theorem 10.2.5).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Section 3.1.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {k : ℕ}

namespace Diffeotopy

/-- **Ordered symplectic flows are symplectic isotopies.** For a closed two-form `σ` and complete
smooth vector fields `Y i` with closed contractions `ι_(Y i) σ`, every map of the ordered flow
`ψ^(Y 0)_(A 0 t) ∘ ⋯ ∘ ψ^(Y (k-1))_(A (k-1) t)` preserves `σ`. -/
theorem timeSlice_orderedGlobalFlowDiffeotopy_mem_diffeomorphStabilizer {σ : SmoothTwoForm I M}
    (hσ : σ.IsClosed) {Y : Fin k → Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯}
    (hY : ∀ i, Y i ∈ σ.symplecticVectorFields) (hc : ∀ i, IsCompleteVectorField (Y i))
    (A : Fin k → ℝ → ℝ) (hA : ∀ i, ContDiff ℝ ∞ (A i)) (hA₀ : ∀ i, A i 0 = 0) (t : unitInterval) :
    (orderedGlobalFlowDiffeotopy le_top (fun i ↦ Y i) (fun i ↦ (Y i).contMDiff) hc A hA
      hA₀).timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ := by
  induction k generalizing t with
  | zero =>
    rw [orderedGlobalFlowDiffeotopy_of_fin_zero]
    exact SmoothForm.timeSlice_refl_mem_diffeomorphStabilizer t
  | succ k ih =>
    rw [orderedGlobalFlowDiffeotopy_succ]
    exact SmoothForm.timeSlice_trans_mem_diffeomorphStabilizer
      (ih (Y := fun i ↦ Y i.succ) (fun i ↦ hY i.succ) (fun i ↦ hc i.succ) _ _ _)
      (timeSlice_globalFlowDiffeotopyAlong_mem_diffeomorphStabilizer hσ (hY 0) (hc 0) _ _ _) t

end Diffeotopy

/-- **Ordered symplectic flows preserve the form.** For a closed two-form `σ`, complete smooth
vector fields `Y i` with closed contractions `ι_(Y i) σ` and any times `s i`, the ordered flow
`ψ^(Y 0)_(s 0) ∘ ⋯ ∘ ψ^(Y (k-1))_(s (k-1))` is a diffeomorphism preserving `σ`. -/
theorem exists_mem_diffeomorphStabilizer_coe_eq_orderedFlowOf {σ : SmoothTwoForm I M}
    (hσ : σ.IsClosed) {Y : Fin k → Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯}
    (hY : ∀ i, Y i ∈ σ.symplecticVectorFields) (hc : ∀ i, IsCompleteVectorField (Y i))
    (s : Fin k → ℝ) :
    ∃ f ∈ SmoothForm.diffeomorphStabilizer σ, ⇑f = orderedFlowOf (fun i ↦ Y i) s := by
  -- `f` is the final map of the ordered flow along the linear time functions `r ↦ s i * r`.
  have hA : ∀ i, ContDiff ℝ ∞ fun r : ℝ ↦ s i * r := fun i ↦ contDiff_const.mul contDiff_id
  have hA₀ : ∀ i, s i * 0 = 0 := fun i ↦ mul_zero (s i)
  refine ⟨(orderedGlobalFlowDiffeotopy le_top (fun i ↦ Y i) (fun i ↦ (Y i).contMDiff) hc
    (fun i r ↦ s i * r) hA hA₀).final,
    SmoothForm.final_mem_diffeomorphStabilizer
      (Diffeotopy.timeSlice_orderedGlobalFlowDiffeotopy_mem_diffeomorphStabilizer hσ hY hc _ hA
        hA₀), ?_⟩
  rw [Diffeotopy.final_def, Diffeotopy.timeSlice_orderedGlobalFlowDiffeotopy]
  simp

namespace Diffeotopy

/-- **The flux of an ordered symplectic flow.** For a closed two-form `σ`, complete smooth
symplectic vector fields `Y i` and smooth time functions `A i` with `A i 0 = 0`, the ordered flow
`ψ_t = ψ^(Y 0)_(A 0 t) ∘ ⋯ ∘ ψ^(Y (k-1))_(A (k-1) t)` has flux `∑ i, A i 1 [ι_(Y i) σ]`. -/
theorem flux_orderedGlobalFlowDiffeotopy (σ : closedForms I M 2)
    {Y : Fin k → Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯}
    (hY : ∀ i, Y i ∈ SmoothTwoForm.symplecticVectorFields σ.val)
    (hc : ∀ i, IsCompleteVectorField (Y i)) (A : Fin k → ℝ → ℝ) (hA : ∀ i, ContDiff ℝ ∞ (A i))
    (hA₀ : ∀ i, A i 0 = 0)
    (hΦ : (orderedGlobalFlowDiffeotopy le_top (fun i ↦ Y i) (fun i ↦ (Y i).contMDiff) hc A hA
      hA₀).final ∈ SmoothForm.diffeomorphStabilizer σ.val) :
    (orderedGlobalFlowDiffeotopy le_top (fun i ↦ Y i) (fun i ↦ (Y i).contMDiff) hc A hA hA₀).flux
      σ hΦ = ∑ i, A i 1 • SmoothTwoForm.interiorClass σ.val ⟨Y i, hY i⟩ := by
  have hσ : SmoothForm.IsClosed σ.val :=
    (SmoothForm.isClosed_def _).2 ((mem_closedForms I σ.val).1 σ.property)
  induction k with
  | zero =>
    rw [Fin.sum_univ_zero]
    simp_rw [orderedGlobalFlowDiffeotopy_of_fin_zero] at hΦ ⊢
    exact flux_refl σ hΦ
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    simp_rw [orderedGlobalFlowDiffeotopy_succ] at hΦ ⊢
    rw [flux_trans _ _ σ
      (SmoothForm.final_mem_diffeomorphStabilizer
        (timeSlice_orderedGlobalFlowDiffeotopy_mem_diffeomorphStabilizer hσ
          (Y := fun i ↦ Y i.succ) (fun i ↦ hY i.succ) (fun i ↦ hc i.succ) _ _ _))
      (SmoothForm.final_mem_diffeomorphStabilizer
        (timeSlice_globalFlowDiffeotopyAlong_mem_diffeomorphStabilizer hσ (hY 0) (hc 0) _ _ _)),
      flux_globalFlowDiffeotopyAlong, ih (Y := fun i ↦ Y i.succ) (fun i ↦ hY i.succ)]

/-- **Ordered symplectic flows with vanishing total times contract symplectically.** For a closed
two-form `σ`, complete smooth symplectic vector fields `Y i` and smooth time functions `A i` with
`A i 0 = 0 = A i 1`, the ordered flow `ψ_t = ψ^(Y 0)_(A 0 t) ∘ ⋯ ∘ ψ^(Y (k-1))_(A (k-1) t)` is a
loop, and it is homotopic to the constant diffeotopy relative to both time ends through maps
preserving `σ`: there is a smooth `G` with `G (·, 0)` the motion of `ψ`, `G (·, 1)` the constant
motion, `G ((x, 0), s) = G ((x, 1), s) = x`, and every map `x ↦ G ((x, t), s)` preserving `σ`. -/
theorem exists_homotopy_orderedGlobalFlowDiffeotopy_mem_diffeomorphStabilizer
    {σ : SmoothTwoForm I M} (hσ : σ.IsClosed) {Y : Fin k → Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯}
    (hY : ∀ i, Y i ∈ σ.symplecticVectorFields) (hc : ∀ i, IsCompleteVectorField (Y i))
    (A : Fin k → ℝ → ℝ) (hA : ∀ i, ContDiff ℝ ∞ (A i)) (hA₀ : ∀ i, A i 0 = 0)
    (h₁ : ∀ i, A i 1 = 0) :
    ∃ G : (M × unitInterval) × unitInterval → M,
      ContMDiff ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) I ∞ G ∧
      (∀ p, G (p, 0) = (orderedGlobalFlowDiffeotopy le_top (fun i ↦ Y i)
        (fun i ↦ (Y i).contMDiff) hc A hA hA₀).cylinderMap p) ∧
      (∀ p, G (p, 1) = p.1) ∧ (∀ x s, G ((x, 0), s) = x) ∧ (∀ x s, G ((x, 1), s) = x) ∧
      ∀ t s, ∃ f ∈ SmoothForm.diffeomorphStabilizer σ, ⇑f = fun x ↦ G ((x, t), s) := by
  obtain ⟨G, hG, hG₀, hG₁, h₀, h₁', hslice⟩ :=
    exists_homotopy_orderedGlobalFlowDiffeotopy le_top _ _ hc A hA hA₀ h₁
  refine ⟨G, hG, hG₀, hG₁, h₀, h₁', fun t s ↦ ?_⟩
  rw [hslice t s]
  exact exists_mem_diffeomorphStabilizer_coe_eq_orderedFlowOf hσ hY hc _

end Diffeotopy

end TauCeti

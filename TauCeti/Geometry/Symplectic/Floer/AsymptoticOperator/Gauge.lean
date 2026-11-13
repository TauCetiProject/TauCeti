/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
public import TauCeti.Geometry.Symplectic.AlmostComplex.UnitaryTransport

import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Normed.Module.ContinuousInverse

/-!
# The asymptotic operator in a complex frame

Let `A ζ = J_t (ζ' - S_t ζ)` be the asymptotic operator of a Hamiltonian orbit
(`TauCeti.Floer.asymptoticOperator`), acting on loops in a symplectic vector space `(V, ω)` with
complex structures `J_t`. Writing loops in a moving frame `Φ_t : U ≃ V`, `ζ = Φ η`, turns the
linear equation `ζ' = S_t ζ` into `η' = S^Φ_t η` for the **gauge transform**

`S^Φ_t = Φ_t⁻¹ (S_t Φ_t - Φ_t')`

(`TauCeti.Floer.gaugeTransform`, `TauCeti.Floer.deriv_comp_sub_apply`). If each `Φ_t` is complex
linear from `(U, J'_t)` to `(V, J_t)`, the asymptotic operator transforms in the same way
(`TauCeti.Floer.asymptoticOperator_comp_eq`):

`A_{J, S} (Φ η) = Φ (A_{J', S^Φ} η)`.

If moreover each `Φ_t` is symplectic from `(U, ω')` to `(V, ω)` and every `S_t` is
infinitesimally symplectic, as the linearized Hamiltonian vector field along an orbit is, then so
is every `S^Φ_t` (`TauCeti.Floer.symplecticForm_gaugeTransform_apply_add_eq_zero`). The kernel of
an asymptotic operator does not depend on its complex structures, and the frame preserves
periodicity, so a periodic frame identifies the periodic kernels of the two operators
(`TauCeti.Floer.forall_eq_zero_of_asymptoticOperator_gaugeTransform_eq_zero_iff`): one of them is
injective on periodic loops exactly when the other one is.

The canonical choice of frame is the unitary transport `T_{J_t}` of
`TauCeti.Geometry.Symplectic.AlmostComplex.UnitaryTransport`, a symplectic isomorphism from
`(E, ω, J₀)` to `(E, ω, J_t)` depending smoothly on `J_t`. For a differentiable one-periodic family
of compatible structures it is a differentiable one-periodic unitary frame, and it turns the
asymptotic operator of an orbit into an operator with the constant complex structure `J₀`
(`SymplecticForm.asymptoticOperator_unitaryTransport_eq`) whose periodic kernel is trivial exactly
when the orbit is nondegenerate (`SymplecticForm` theorem
`isNondegenerateFixedPt_iff_forall_eq_zero_of_asymptoticOperator_gaugeTransform_eq_zero`).
The coefficient `S^Φ_t` is infinitesimally symplectic, continuous and one-periodic by
`TauCeti.Floer.symplecticForm_gaugeTransform_apply_add_eq_zero`,
`TauCeti.Floer.continuous_gaugeTransform` and `TauCeti.Floer.periodic_gaugeTransform`, so the
transformed operator `J₀ (∂_t - S^Φ_t)` is symmetric for the fixed `L²` inner product of `E`
(`TauCeti.Floer.integral_associatedBilinForm_asymptoticOperator_comm`).

## Main definitions

* `TauCeti.Floer.gaugeTransform Φ S`: the coefficient `Φ_t⁻¹ (S_t Φ_t - Φ_t')`.

## Main results

* `TauCeti.Floer.asymptoticOperator_comp_eq`: the asymptotic operator in a complex frame.
* `TauCeti.Floer.symplecticForm_gaugeTransform_apply_add_eq_zero`: symplectic frames preserve
  infinitesimal symplecticity.
* `TauCeti.Floer.forall_eq_zero_of_asymptoticOperator_gaugeTransform_eq_zero_iff`: periodic
  frames identify the periodic kernels.
* `isNondegenerateFixedPt_iff_forall_eq_zero_of_asymptoticOperator_gaugeTransform_eq_zero`
  (in `TauCeti.SymplecticForm`): an orbit is nondegenerate exactly when the asymptotic operator
  in the unitary frame of a differentiable one-periodic family of compatible structures has
  trivial periodic kernel.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (the operator `J₀ ∂_t + S` in a unitary trivialization along an
  orbit).
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. 45 (1992), 1303–1360.
-/

public section

open Function

namespace TauCeti

namespace Floer

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {J' : ℝ → AlmostComplexStructure U} {J : ℝ → AlmostComplexStructure V}
  {S : ℝ → V →L[ℝ] V} {Φ : ℝ → U ≃L[ℝ] V} {ζ : ℝ → U} {t : ℝ}

/-- The **gauge transform** `Φ_t⁻¹ (S_t Φ_t - Φ_t')` of a family `S_t` of endomorphisms of `V` by
a family of isomorphisms `Φ_t : U ≃ V`. A loop `η` solves `η' = S^Φ_t η` exactly when `Φ η` solves
`ζ' = S_t ζ`, so this is the coefficient of the linear equation in the moving frame `Φ`. -/
noncomputable def gaugeTransform (Φ : ℝ → U ≃L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) : U →L[ℝ] U :=
  ((Φ t).symm : V →L[ℝ] U) ∘L
    (S t ∘L (Φ t : U →L[ℝ] V) - deriv (fun s ↦ (Φ s : U →L[ℝ] V)) t)

theorem gaugeTransform_apply (Φ : ℝ → U ≃L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) (u : U) :
    gaugeTransform Φ S t u =
      (Φ t).symm (S t (Φ t u) - deriv (fun s ↦ (Φ s : U →L[ℝ] V)) t u) :=
  (rfl)

theorem gaugeTransform_def (Φ : ℝ → U ≃L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) :
    gaugeTransform Φ S t = ((Φ t).symm : V →L[ℝ] U) ∘L
      (S t ∘L (Φ t : U →L[ℝ] V) - deriv (fun s ↦ (Φ s : U →L[ℝ] V)) t) :=
  (rfl)

/-- The frame carries the gauge transform back to `S_t` up to the derivative of the frame:
`Φ_t S^Φ_t = S_t Φ_t - Φ_t'`. -/
@[simp]
theorem apply_gaugeTransform_apply (u : U) :
    Φ t (gaugeTransform Φ S t u) = S t (Φ t u) - deriv (fun s ↦ (Φ s : U →L[ℝ] V)) t u := by
  rw [gaugeTransform_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- In the constant frame the gauge transform is conjugation. -/
@[simp]
theorem gaugeTransform_const (e : U ≃L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) :
    gaugeTransform (fun _ ↦ e) S t = (e.symm : V →L[ℝ] U) ∘L S t ∘L (e : U →L[ℝ] V) := by
  ext u
  simp [gaugeTransform_apply]

/-- **The linear equation in a moving frame.** For a frame `Φ` and a loop `ζ` differentiable at
`t`, `(Φ ζ)' - S_t (Φ ζ) = Φ_t (ζ' - S^Φ_t ζ)` at `t`. In particular `Φ ζ` solves `ζ' = S_t ζ` at
`t` exactly when `ζ` solves `ζ' = S^Φ_t ζ` there. -/
theorem deriv_comp_sub_apply (hΦ : DifferentiableAt ℝ (fun s ↦ (Φ s : U →L[ℝ] V)) t)
    (hζ : DifferentiableAt ℝ ζ t) :
    deriv (fun s ↦ Φ s (ζ s)) t - S t (Φ t (ζ t)) =
      Φ t (deriv ζ t - gaugeTransform Φ S t (ζ t)) := by
  have hd := hΦ.hasDerivAt.clm_apply hζ.hasDerivAt
  simp only [ContinuousLinearEquiv.coe_coe] at hd
  rw [hd.deriv, (Φ t).map_sub, apply_gaugeTransform_apply]
  abel

/-- **The asymptotic operator in a complex frame.** If `Φ_t` is complex linear from `(U, J'_t)` to
`(V, J_t)`, that is `Φ_t ∘ J'_t = J_t ∘ Φ_t`, and differentiable in `t`, then for a loop `ζ`
differentiable at `t`, `A_{J, S} (Φ ζ) = Φ (A_{J', S^Φ} ζ)` at `t`, for the gauge transform `S^Φ` of
`S` by `Φ`. -/
theorem asymptoticOperator_comp_eq (hΦ : DifferentiableAt ℝ (fun s ↦ (Φ s : U →L[ℝ] V)) t)
    (hΦJ : ∀ u, Φ t (J' t u) = J t (Φ t u)) (hζ : DifferentiableAt ℝ ζ t) :
    asymptoticOperator J S (fun s ↦ Φ s (ζ s)) t =
      Φ t (asymptoticOperator J' (gaugeTransform Φ S) ζ t) := by
  rw [asymptoticOperator_def, asymptoticOperator_def, deriv_comp_sub_apply hΦ hζ, hΦJ]

/-- A frame identifies the kernels of the two asymptotic operators pointwise, for any complex
structures `J_t` and `J'_t`. -/
theorem asymptoticOperator_comp_eq_zero_iff
    (hΦ : DifferentiableAt ℝ (fun s ↦ (Φ s : U →L[ℝ] V)) t) (hζ : DifferentiableAt ℝ ζ t) :
    asymptoticOperator J S (fun s ↦ Φ s (ζ s)) t = 0 ↔
      asymptoticOperator J' (gaugeTransform Φ S) ζ t = 0 := by
  rw [asymptoticOperator_def, asymptoticOperator_def, AlmostComplexStructure.map_eq_zero_iff,
    AlmostComplexStructure.map_eq_zero_iff, deriv_comp_sub_apply hΦ hζ, (Φ t).map_eq_zero_iff]

/-- **Symplectic frames preserve infinitesimal symplecticity.** If every `Φ_s` is symplectic from
`(U, ω')` to `(V, ω)`, the frame is differentiable at `t` and `S_t` is infinitesimally symplectic
for `ω`, then the gauge transform `S^Φ_t` is infinitesimally symplectic for `ω'`. -/
theorem symplecticForm_gaugeTransform_apply_add_eq_zero [FiniteDimensional ℝ V]
    {ω' : SymplecticForm U}
    {ω : SymplecticForm V} (hΦω : ∀ s u v, ω (Φ s u) (Φ s v) = ω' u v)
    (hΦ : DifferentiableAt ℝ (fun s ↦ (Φ s : U →L[ℝ] V)) t)
    (hS : ∀ v w, ω (S t v) w + ω v (S t w) = 0) (u v : U) :
    ω' (gaugeTransform Φ S t u) v + ω' u (gaugeTransform Φ S t v) = 0 := by
  set Φ' := deriv (fun s ↦ (Φ s : U →L[ℝ] V)) t
  -- Differentiating `ω (Φ_s u) (Φ_s v) = ω' u v` at `s = t`.
  have hd : ω (Φ' u) (Φ t v) + ω (Φ t u) (Φ' v) = 0 := by
    have h₁ := ω.hasDerivAt_apply_comp (hΦ.hasDerivAt.clm_apply (hasDerivAt_const t u))
      (hΦ.hasDerivAt.clm_apply (hasDerivAt_const t v))
    have h₂ : HasDerivAt (fun s ↦ ω (Φ s u) (Φ s v)) 0 t := by
      simp only [hΦω]
      exact hasDerivAt_const t _
    simpa using h₁.unique (by simpa using h₂)
  have key : ∀ a w, ω' ((Φ t).symm a) w = ω a (Φ t w) := fun a w ↦ by
    rw [← hΦω t, ContinuousLinearEquiv.apply_symm_apply]
  have e₁ := ω'.neg_eq ((Φ t).symm (S t (Φ t v) - Φ' v)) u
  have e₂ := ω.neg_eq (S t (Φ t v)) (Φ t u)
  have e₃ := ω.neg_eq (Φ' v) (Φ t u)
  rw [gaugeTransform_apply, gaugeTransform_apply, ← e₁, key, key]
  simp only [map_sub, LinearMap.sub_apply] at e₂ e₃ ⊢
  linear_combination hS (Φ t u) (Φ t v) - hd + e₂ - e₃

/-- A periodic frame and a periodic coefficient have a periodic gauge transform. -/
theorem periodic_gaugeTransform {c : ℝ} (hΦ : Periodic Φ c) (hS : Periodic S c) :
    Periodic (gaugeTransform Φ S) c := fun t ↦ by
  have hd : Periodic (deriv fun s ↦ (Φ s : U →L[ℝ] V)) c :=
    Periodic.deriv fun s ↦ by simp only [hΦ s]
  ext u
  simp only [gaugeTransform_apply, hΦ t, hS t, hd t]

/-- A `C¹` frame and a continuous coefficient have a continuous gauge transform. -/
theorem continuous_gaugeTransform (hΦ : ContDiff ℝ 1 fun s ↦ (Φ s : U →L[ℝ] V))
    (hS : Continuous S) : Continuous (gaugeTransform Φ S) := by
  have hinv : Continuous fun s ↦ ((Φ s).symm : V →L[ℝ] U) := by
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hΦ.continuous.clm_inverse fun _ ↦ ContinuousLinearMap.isInvertible_equiv
  have hd : Continuous (deriv fun s ↦ (Φ s : U →L[ℝ] V)) := hΦ.continuous_deriv le_rfl
  exact hinv.clm_comp ((hS.clm_comp hΦ.continuous).sub hd)

/-- **Periodic frames identify the periodic kernels.** For a differentiable `c`-periodic frame
`Φ_t` and any complex structures `J_t` and `J'_t`, the asymptotic operator `A_{J', S^Φ}` of the
gauge transform `S^Φ` has no nonzero differentiable `c`-periodic kernel element exactly when
`A_{J, S}` has none. -/
theorem forall_eq_zero_of_asymptoticOperator_gaugeTransform_eq_zero_iff [CompleteSpace U]
    {c : ℝ} (hΦd : Differentiable ℝ fun s ↦ (Φ s : U →L[ℝ] V)) (hΦp : Periodic Φ c) :
    (∀ ζ : ℝ → U, Differentiable ℝ ζ → Periodic ζ c →
        (∀ t, asymptoticOperator J' (gaugeTransform Φ S) ζ t = 0) → ζ = 0) ↔
      ∀ η : ℝ → V, Differentiable ℝ η → Periodic η c →
        (∀ t, asymptoticOperator J S η t = 0) → η = 0 := by
  constructor
  · intro h η hη hηp hA
    -- Pull `η` back to the loop `Φ⁻¹ η`, which is differentiable since inversion is smooth.
    have hinv : Differentiable ℝ fun s ↦ ((Φ s).symm : V →L[ℝ] U) := fun s ↦ by
      simpa only [ContinuousLinearMap.inverse_equiv] using
        (hΦd s).clm_inverse_of_completeSpace ⟨Φ s, rfl⟩
    set ζ : ℝ → U := fun s ↦ (Φ s).symm (η s)
    have hζ : Differentiable ℝ ζ := fun s ↦ ((hinv s).hasDerivAt.clm_apply
      (hη s).hasDerivAt).differentiableAt
    have hΦζ : (fun s ↦ Φ s (ζ s)) = η := funext fun s ↦ by simp [ζ]
    have h0 := h ζ hζ (fun s ↦ by simp only [ζ, hΦp s, hηp s]) fun t ↦
      (asymptoticOperator_comp_eq_zero_iff (hΦd t) (hζ t)).1 (hΦζ ▸ hA t)
    rw [← hΦζ, h0]
    funext s
    simp
  · intro h ζ hζ hζp hA
    have hη : Differentiable ℝ fun s ↦ Φ s (ζ s) := fun s ↦
      ((hΦd s).hasDerivAt.clm_apply (hζ s).hasDerivAt).differentiableAt
    have h0 := h _ hη (fun s ↦ by simp only [hΦp s, hζp s]) fun t ↦
      (asymptoticOperator_comp_eq_zero_iff (hΦd t) (hζ t)).2 (hA t)
    funext s
    simpa using congrFun h0 s

end Floer

namespace SymplecticForm

open Floer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ω : SymplecticForm E} {J₀ : AlmostComplexStructure E} {J : ℝ → AlmostComplexStructure E}

/-- **The asymptotic operator in the unitary frame.** For a family `J_t` of `ω`-compatible complex
structures that is differentiable at `t`, a complex structure `J₀` whose metric is the inner
product of `E`, and a loop `ζ` differentiable at `t`, the unitary transports `T_{J_t}` turn the
asymptotic operator `A_{J, S}` into the asymptotic operator with the constant complex structure
`J₀` and the gauge transform of `S`: `A_{J, S} (T_J ζ) = T_J (A_{J₀, S^Φ} ζ)` at `t`. -/
theorem asymptoticOperator_unitaryTransport_eq (hJ₀ : ∀ u v, ω u (J₀ v) = inner ℝ u v)
    (hJc : ∀ t, ω.Compatible (J t)) (S : ℝ → E →L[ℝ] E) {ζ : ℝ → E} {t : ℝ}
    (hJd : DifferentiableAt ℝ (fun t ↦ LinearMap.toContinuousLinearMap (J t).toLinearMap) t)
    (hζ : DifferentiableAt ℝ ζ t) :
    asymptoticOperator J S (fun s ↦ ω.unitaryTransport (J s) (ζ s)) t =
      ω.unitaryTransport (J t) (asymptoticOperator (fun _ ↦ J₀)
        (gaugeTransform (fun s ↦ unitaryTransportEquiv (hJc s)) S) ζ t) := by
  have h := asymptoticOperator_comp_eq (J := J) (S := S)
    (Φ := fun s ↦ unitaryTransportEquiv (hJc s)) (t := t) (J' := fun _ ↦ J₀) ?_
    (fun u ↦ by simpa using unitaryTransport_apply_eq_apply_unitaryTransport hJ₀ (hJc t) u) hζ
  · simpa using h
  · simpa using hJd.unitaryTransport hJc

/-- **The unitary gauge at a nondegenerate orbit.** Let `x` be a one-periodic orbit of a
one-periodic, jointly `C²` time-dependent Hamiltonian `H` whose suspended vector field is globally
Lipschitz, with linearized Hamiltonian vector field `S_t = dX_{H_t}(x(t))`. Let `J_t` be a
differentiable one-periodic family of `ω`-compatible complex structures. Then `x` is nondegenerate
exactly when, for any family `J'_t` of complex structures (for instance a constant complex
structure `J₀` whose metric is the inner product of `E`), the asymptotic operator with the complex
structures `J'_t` and the gauge transform `S^Φ` of `S` by the unitary transports `T_{J_t}` has no
nonzero differentiable one-periodic kernel element. -/
theorem isNondegenerateFixedPt_iff_forall_eq_zero_of_asymptoticOperator_gaugeTransform_eq_zero
    (ω : SymplecticForm E) {H : ℝ → E → ℝ} {K : NNReal}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → E}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hJc : ∀ t, ω.Compatible (J t))
    (hJd : Differentiable ℝ fun t ↦ LinearMap.toContinuousLinearMap (J t).toLinearMap)
    (hJp : Periodic J 1) (J' : ℝ → AlmostComplexStructure E) :
    IsNondegenerateFixedPt (modelWithCornersSelf ℝ E)
        (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) ↔
      ∀ ζ : ℝ → E, Differentiable ℝ ζ → Periodic ζ 1 →
        (∀ t, asymptoticOperator J'
          (gaugeTransform (fun s ↦ unitaryTransportEquiv (hJc s))
            fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ζ t = 0) → ζ = 0 := by
  have hΦp : Periodic (fun s ↦ unitaryTransportEquiv (hJc s)) 1 := fun s ↦ by
    ext v
    simp only [unitaryTransportEquiv_apply, hJp s]
  refine (isNondegenerateFixedPt_iff_forall_eq_zero_of_asymptoticOperator_eq_zero ω hX hH hHp hx
    hxp J).trans (forall_eq_zero_of_asymptoticOperator_gaugeTransform_eq_zero_iff ?_ hΦp).symm
  simpa using hJd.unitaryTransport hJc

end SymplecticForm

end TauCeti

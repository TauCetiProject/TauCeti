/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.Fuglede
public import Mathlib.Topology.UrysohnsLemma
public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.DominatedConvergence
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Representation.OfRepresentation

/-!
# The Borel functional calculus of a normal operator

Let `a` be a normal bounded operator on a complex Hilbert space `H`. Its continuous functional
calculus `cfcHom : C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)` is a unital star representation of the
continuous functions on the compact spectrum, so it has a projection-valued measure
`ProjValMeasure.ofRepresentation (cfcHom _)`. This is the **spectral measure** `P` of `a`, and
integration against it is the **Borel functional calculus**

`f ↦ f(a) = ∫ f dP`,

a unital star algebra homomorphism from the bounded Borel functions on the spectrum to the bounded
operators on `H` which extends the continuous functional calculus. Its value on the indicator of a
Borel set `B` is the spectral projection `P(B)`, and the coordinate function recovers `a` itself:
this is the spectral theorem for bounded normal operators in its projection-valued form.

The spectral measure is the only projection-valued measure on the spectrum that recovers the
continuous functional calculus (finite measures on the compact metrizable spectrum are regular,
so no regularity hypothesis is needed), and it charges every nonempty relatively open subset of
the spectrum. By the Fuglede–Putnam–Rosenblum theorem, an operator commutes with `a` iff it
commutes with every spectral projection, equivalently with every value of the Borel calculus.

## Main declarations

* `ContinuousLinearMap.spectralPVM a`: the spectral measure of a normal operator `a`.
* `ContinuousLinearMap.borelCalculus a`: the Borel functional calculus of `a`, the integral
  against `a.spectralPVM`.
* `ContinuousLinearMap.borelCalculus_ofContinuousMap`: the Borel calculus extends `cfcHom`.
* `ContinuousLinearMap.borelCalculus_restrict_id`: the coordinate function recovers `a`.
* `ContinuousLinearMap.borelCalculus_indicator`: indicators give the spectral projections.
* `ContinuousLinearMap.eq_spectralPVM_iff`: uniqueness of the spectral measure.
* `ContinuousLinearMap.spectralPVM_proj_eq_zero_iff`: the spectral measure has full support.
* `ContinuousLinearMap.forall_commute_borelCalculus_iff`,
  `ContinuousLinearMap.forall_commute_spectralPVM_proj_iff`: the spectral commutant.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.2.
* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill (1991), Theorems 12.23 and 12.24.
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (a : H →L[ℂ] H) [IsStarNormal a]

/-- The **spectral measure** of a normal operator `a`: the projection-valued measure on its
spectrum of the continuous functional calculus `cfcHom`. -/
def spectralPVM : ProjValMeasure (spectrum ℂ a) H :=
  ProjValMeasure.ofRepresentation (cfcHom (a := a) ‹_›)

/-- The **Borel functional calculus** `f ↦ f(a)` of a normal operator `a`: integration of bounded
Borel functions on the spectrum against the spectral measure of `a`. -/
def borelCalculus : BoundedBorelFunction (spectrum ℂ a) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  a.spectralPVM.integral

/-- Integration against the spectral measure is the Borel functional calculus. -/
@[simp]
theorem integral_spectralPVM : a.spectralPVM.integral = a.borelCalculus :=
  (rfl)

/-- The spectral measure is the projection-valued measure of `cfcHom`. -/
theorem spectralPVM_eq_ofRepresentation :
    a.spectralPVM = ProjValMeasure.ofRepresentation (cfcHom (a := a) ‹_›) :=
  (rfl)

/-- **The Borel calculus extends the continuous calculus.** On a continuous function on the
spectrum, the Borel functional calculus agrees with `cfcHom`. -/
@[simp]
theorem borelCalculus_ofContinuousMap (f : C(spectrum ℂ a, ℂ)) :
    a.borelCalculus (BoundedBorelFunction.ofContinuousMap f) = cfcHom ‹_› f :=
  ProjValMeasure.integral_ofRepresentation_ofContinuousMap _ f

/-- The diagonal measures of the spectral measure are the diagonal measures `μ_ξ` of `a`. -/
@[simp]
theorem spectralPVM_diag (ξ : H) : a.spectralPVM.diag ξ = a.diagMeasure ξ :=
  (a.eq_diagMeasure_iff ξ _).2 fun f => by
    simpa using a.spectralPVM.integral_diag_eq_inner_integral
      (BoundedBorelFunction.ofContinuousMap f) ξ

/-- The `cfc` form of `borelCalculus_ofContinuousMap`: for `f` continuous on the spectrum, the
Borel calculus of the restriction of `f` to the spectrum is `cfc f a`. -/
theorem borelCalculus_ofContinuousMap_domRestrict (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a) := by cfc_cont_tac) :
    a.borelCalculus (BoundedBorelFunction.ofContinuousMap
      ⟨(spectrum ℂ a).domRestrict f, hf.domRestrict⟩) = cfc f a := by
  rw [borelCalculus_ofContinuousMap, cfc_apply f a]

/-- **Spectral theorem for normal operators.** The Borel calculus of the coordinate function on
the spectrum is `a` itself, that is, `a = ∫ z dP(z)`. -/
theorem borelCalculus_restrict_id :
    a.borelCalculus (BoundedBorelFunction.ofContinuousMap
      ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))) = a := by
  rw [borelCalculus_ofContinuousMap, cfcHom_id]

/-- The Borel calculus of the indicator of a Borel set `B` is the spectral projection `P(B)`. -/
@[simp]
theorem borelCalculus_indicator {B : Set (spectrum ℂ a)} (hB : MeasurableSet B) :
    a.borelCalculus (BoundedBorelFunction.indicator B hB 1) = a.spectralPVM.proj B hB :=
  a.spectralPVM.integral_indicator hB

/-- Diagonal matrix elements of the Borel calculus are integrals against the diagonal measures:
`⟪ξ, f(a) ξ⟫ = ∫ f dμ_ξ`. -/
theorem inner_borelCalculus_self (f : BoundedBorelFunction (spectrum ℂ a)) (ξ : H) :
    ⟪ξ, a.borelCalculus f ξ⟫_ℂ = ∫ x, f x ∂(a.diagMeasure ξ) := by
  simpa using (a.spectralPVM.integral_diag_eq_inner_integral f ξ).symm

/-- **Vector norm identity** for the Borel calculus: `‖f(a) ξ‖² = ∫ |f|² dμ_ξ`. -/
theorem norm_sq_borelCalculus_apply (f : BoundedBorelFunction (spectrum ℂ a)) (ξ : H) :
    ‖a.borelCalculus f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(a.diagMeasure ξ) := by
  simpa using a.spectralPVM.norm_sq_integral_apply f ξ

/-- A bound `‖f x‖ ≤ M` on the spectrum bounds the operator norm of `f(a)` by `M`. -/
theorem norm_borelCalculus_le {f : BoundedBorelFunction (spectrum ℂ a)} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, ‖f x‖ ≤ M) : ‖a.borelCalculus f‖ ≤ M :=
  a.spectralPVM.norm_integral_le hM hf

/-- A bound `‖f x‖ ≤ M` on the spectrum gives `‖f(a) ξ‖ ≤ M ‖ξ‖` for every vector `ξ`. -/
theorem norm_borelCalculus_apply_le {f : BoundedBorelFunction (spectrum ℂ a)} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ x, ‖f x‖ ≤ M) (ξ : H) : ‖a.borelCalculus f ξ‖ ≤ M * ‖ξ‖ :=
  (le_opNorm _ ξ).trans (by gcongr; exact a.norm_borelCalculus_le hM hf)

/-- **Almost-everywhere invariance.** Bounded Borel functions that agree almost everywhere for
every diagonal measure `μ_ξ` of `a` have the same Borel calculus. -/
theorem borelCalculus_congr_ae {f g : BoundedBorelFunction (spectrum ℂ a)}
    (h : ∀ ξ, ⇑f =ᵐ[a.diagMeasure ξ] g) : a.borelCalculus f = a.borelCalculus g :=
  a.spectralPVM.integral_congr_ae ((a.spectralPVM.eventually_ae_iff _).2 fun ξ => by
    rw [spectralPVM_diag]
    exact h ξ)

/-- Any two values of the Borel calculus of `a` commute. -/
theorem commute_borelCalculus_borelCalculus (f g : BoundedBorelFunction (spectrum ℂ a)) :
    Commute (a.borelCalculus f) (a.borelCalculus g) :=
  (Commute.all f g).map a.borelCalculus

/-- **Spectral commutant.** An operator commutes with every spectral projection of a normal
operator `a` iff it commutes with `a`. One direction is the Fuglede–Putnam–Rosenblum theorem:
an operator commuting with `a` also commutes with `star a`, hence with the continuous functional
calculus of `a`. -/
theorem forall_commute_spectralPVM_proj_iff (b : H →L[ℂ] H) :
    (∀ B hB, Commute b (a.spectralPVM.proj B hB)) ↔ Commute b a := by
  rw [spectralPVM_eq_ofRepresentation, ProjValMeasure.forall_commute_proj_ofRepresentation_iff]
  refine ⟨fun h => cfcHom_id (R := ℂ) (a := a) ‹_› ▸ h _, fun h f => ?_⟩
  exact (h.symm.cfcHom ‹_› (IsStarNormal.commute_star_left ‹_› h.symm) f).symm

/-- **Spectral commutant.** An operator commutes with every value of the Borel calculus of a
normal operator `a` iff it commutes with `a`. -/
theorem forall_commute_borelCalculus_iff (b : H →L[ℂ] H) :
    (∀ f, Commute b (a.borelCalculus f)) ↔ Commute b a := by
  rw [← integral_spectralPVM, ProjValMeasure.forall_commute_integral_iff,
    forall_commute_spectralPVM_proj_iff]

/-- Every value of the Borel calculus of `a` commutes with `a`. -/
theorem commute_borelCalculus (f : BoundedBorelFunction (spectrum ℂ a)) :
    Commute a (a.borelCalculus f) :=
  (a.forall_commute_borelCalculus_iff a).2 (Commute.refl a) f

/-- **Uniqueness of the spectral measure.** A projection-valued measure on the spectrum of a
normal operator `a` is its spectral measure iff integrating continuous functions against it gives
the continuous functional calculus of `a`. -/
theorem eq_spectralPVM_iff (P : ProjValMeasure (spectrum ℂ a) H) :
    P = a.spectralPVM ↔
      ∀ f : C(spectrum ℂ a, ℂ), P.integral (BoundedBorelFunction.ofContinuousMap f) =
        cfcHom ‹_› f :=
  ProjValMeasure.eq_ofRepresentation_iff _ P fun _ => inferInstance

/-- **Full support of the spectral measure.** The spectral projection of a nonempty relatively
open subset of the spectrum of a normal operator is nonzero. -/
theorem spectralPVM_proj_ne_zero {U : Set (spectrum ℂ a)} (hU : IsOpen U) (hne : U.Nonempty) :
    a.spectralPVM.proj U hU.measurableSet ≠ 0 := by
  intro h0
  obtain ⟨x, hx⟩ := hne
  -- An Urysohn function `g` with `g x = 1` vanishing off `U` satisfies `g = g · 𝟙_U`.
  obtain ⟨g, hg0, hg1, -⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl
    isClosed_singleton (Set.disjoint_singleton_right.2 fun hx' => hx' hx)
  let gc : C(spectrum ℂ a, ℂ) := ⟨fun y => g y, by fun_prop⟩
  have hmul : BoundedBorelFunction.ofContinuousMap gc =
      BoundedBorelFunction.ofContinuousMap gc *
        BoundedBorelFunction.indicator U hU.measurableSet 1 := by
    ext y
    by_cases hy : y ∈ U
    · simp [hy]
    · simp [hy, gc, hg0 hy]
  -- Hence `cfcHom gc = cfcHom gc * P(U) = 0`, contradicting injectivity of `cfcHom`.
  have hzero : cfcHom (a := a) ‹_› gc = cfcHom (a := a) ‹_› (0 : C(spectrum ℂ a, ℂ)) := by
    rw [← borelCalculus_ofContinuousMap, hmul, map_mul, borelCalculus_indicator, h0, mul_zero,
      map_zero]
  have := congr($(cfcHom_injective (a := a) ‹_› hzero) x)
  simp [gc, hg1 rfl] at this

/-- The spectral projection of a relatively open subset of the spectrum of a normal operator
vanishes iff the subset is empty. -/
theorem spectralPVM_proj_eq_zero_iff {U : Set (spectrum ℂ a)} (hU : IsOpen U) :
    a.spectralPVM.proj U hU.measurableSet = 0 ↔ U = ∅ := by
  refine ⟨fun h => Set.not_nonempty_iff_eq_empty.1 fun hne => a.spectralPVM_proj_ne_zero hU hne h,
    ?_⟩
  rintro rfl
  exact a.spectralPVM.proj_empty

end ContinuousLinearMap

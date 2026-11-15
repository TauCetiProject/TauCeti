/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar
import Mathlib.Tactic.NoncommRing

/-!
# Norm paths of complex Hilbert-space operators

Every unitary operator on a complete complex inner-product space is joined to the identity
in the operator norm. Reflection in the kernel of the negative real part provides a
spectral cut using continuous functional calculus and orthogonal projection. The polar
decomposition then gives a norm-continuous path from any invertible operator to the identity
through invertible operators. No separability or dimension assumption is needed.

The reflection proof is adapted from
[AtiyahSinger/Analysis/FredholmPaths.lean][fredholm-paths] in Lean-Atiyah-Singer.
It is the source formalization's supplementary continuous-functional-calculus argument
for the invertible path connectedness used in *Spin Geometry*, Chapter III, §7, Lemma 7.7.
The polar deformation uses Tau Ceti's native polar factors.

## References

* H. B. Lawson, Jr., and M.-L. Michelsohn, *Spin Geometry*, Princeton Mathematical Series 38,
  Princeton University Press, 1989, Chapter III, §7, Lemma 7.7, p. 203,
  [DOI](https://doi.org/10.1515/9781400883912).

[fredholm-paths]: https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/FredholmPaths.lean
-/

public section

noncomputable section

open Complex
open scoped CStarAlgebra ComplexOrder ComplexStarModule unitInterval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The unitary group of a complete complex Hilbert space is path connected. -/
theorem Unitary.joined_one (u : unitary (E →L[ℂ] E)) :
    Joined (1 : unitary (E →L[ℂ] E)) u := by
  let : PartialOrder (E →L[ℂ] E) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (E →L[ℂ] E) := CStarAlgebra.spectralOrderedRing _
  -- The kernel of the negative part provides the required spectral cut using only
  -- continuous functional calculus and Hilbert-space orthogonal projection.
  let A : E →L[ℂ] E := ℜ (u : E →L[ℂ] E)
  let N : E →L[ℂ] E := A⁻
  let P : E →L[ℂ] E := N.ker.starProjection
  have hA : IsSelfAdjoint A := (realPart (u : E →L[ℂ] E)).property
  have hN : IsSelfAdjoint N := (CFC.negPart_nonneg A).isSelfAdjoint
  have hP : IsSelfAdjoint P := isSelfAdjoint_starProjection N.ker
  have hPproj : IsStarProjection P :=
    ⟨N.ker.isIdempotentElem_starProjection, hP⟩
  have hAU : Commute A (u : E →L[ℂ] E) := by
    dsimp [A]
    rw [realPart_apply_coe]
    exact ((Commute.refl _).add_left (commute_unitary_star_self u.property)).smul_left _
  have hNU : Commute N (u : E →L[ℂ] E) := hAU.cfcₙ_real (·⁻)
  have hNUstar : Commute N (star (u : E →L[ℂ] E)) := by
    simpa only [hN.star_eq] using hNU.star_star
  have hPU : Commute P (u : E →L[ℂ] E) :=
    hNU.starProjection_ker hNUstar
  -- The projection kills the negative part and fixes the positive part.
  have hNP : N * P = 0 := by
    ext x
    exact N.ker.starProjection_apply_mem x
  have hPN : P * N = 0 := by
    simpa only [star_mul, hN.star_eq, hP.star_eq, star_zero] using congrArg star hNP
  have hPpos : P * A⁺ = A⁺ := by
    ext x
    apply N.ker.starProjection_eq_self_iff.mpr
    have hzero : N * A⁺ = 0 := CFC.negPart_mul_posPart A
    exact congrArg (fun T : E →L[ℂ] E ↦ T x) hzero
  -- Reflection in ker(A⁻) turns the real part into the positive operator A⁺ + A⁻.
  let s : unitary (E →L[ℂ] E) := ⟨2 * P - 1, hPproj.two_mul_sub_one_mem_unitary⟩
  have hs : IsSelfAdjoint (s : E →L[ℂ] E) := by
    dsimp only [s, Subtype.coe_mk]
    rw [isSelfAdjoint_iff]
    simp only [star_sub, star_mul, star_ofNat, hP.star_eq, star_one]
    noncomm_ring
  have hsU : Commute (s : E →L[ℂ] E) (u : E →L[ℂ] E) :=
    ((Commute.ofNat_left 2 _).mul_left hPU).sub_left (Commute.one_left _)
  have hsA : (s : E →L[ℂ] E) * A = A⁺ + N := by
    nth_rw 1 [← CFC.posPart_sub_negPart A hA]
    dsimp only [s, Subtype.coe_mk]
    dsimp only [N] at hPN ⊢
    noncomm_ring [hPpos, hPN]
  have hreal : (ℜ ((s * u : unitary (E →L[ℂ] E)) : E →L[ℂ] E) : E →L[ℂ] E) =
      A⁺ + N := by
    rw [← hsA]
    simp only [Submonoid.coe_mul]
    dsimp only [A]
    rw [realPart_apply_coe, realPart_apply_coe, star_mul, hs.star_eq,
      mul_smul_comm, mul_add]
    congr 1
    have hsUstar : Commute (s : E →L[ℂ] E) (star (u : E →L[ℂ] E)) := by
      simpa only [hs.star_eq] using hsU.star_star
    rw [hsUstar.eq]
  have hsu : Joined (1 : unitary (E →L[ℂ] E)) (s * u) := by
    apply Unitary.joined_one_of_nonneg_realPart
    rw [hreal]
    exact add_nonneg (CFC.posPart_nonneg A) (CFC.negPart_nonneg A)
  have hsjoined : Joined (1 : unitary (E →L[ℂ] E)) s :=
    Unitary.joined_one_of_isSelfAdjoint s hs
  simpa using hsjoined.inv.mul hsu

/-- Every invertible operator on a complex Hilbert space is joined to the identity by an
operator-norm continuous path through invertible operators. -/
theorem ContinuousLinearMap.IsInvertible.exists_path_to_id {T : E →L[ℂ] E}
    (hT : T.IsInvertible) :
    ∃ γ : Path T (ContinuousLinearMap.id ℂ E), ∀ t, (γ t).IsInvertible := by
  let : PartialOrder (E →L[ℂ] E) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (E →L[ℂ] E) := CStarAlgebra.spectralOrderedRing _
  obtain ⟨e, he⟩ := hT
  let a := (ContinuousLinearEquiv.unitsEquiv ℂ E).symm e
  have ha : (a : E →L[ℂ] E) = e := by
    ext x
    rw [← ContinuousLinearEquiv.unitsEquiv_apply, MulEquiv.apply_symm_apply]
    simp only [ContinuousLinearEquiv.coe_coe]
  let u := a.polarUnitary
  let P := CFC.sqrt (star (a : E →L[ℂ] E) * a)
  have hP : IsStrictlyPositive P := a.isStrictlyPositive_sqrt_star_mul
  let γ : Path T (u : E →L[ℂ] E) :=
    ((Path.segment P 1).map (f := fun Q ↦ (u : E →L[ℂ] E) * Q)
      (continuous_const.mul continuous_id)).cast
      (by simpa only [u, P] using ((a.polarUnitary_mul_sqrt_star_mul.trans ha).trans he).symm)
      (by simp)
  have hγ : ∀ t, (γ t).IsInvertible := by
    intro t
    have hpos : IsUnit ((1 - (t : ℝ)) • P + (t : ℝ) • (1 : E →L[ℂ] E)) := by
      by_cases ht : (t : ℝ) = 1
      · simp [ht]
      · have htpos : 0 < 1 - (t : ℝ) := sub_pos.mpr (lt_of_le_of_ne t.property.2 ht)
        exact ((hP.smul htpos).add_nonneg (smul_nonneg t.property.1 zero_le_one)).isUnit
    obtain ⟨v, hv⟩ := (Unitary.isUnit_coe (U := u)).mul hpos
    refine ⟨ContinuousLinearEquiv.unitsEquiv ℂ E v, ?_⟩
    ext x
    simpa only [γ, Path.cast_coe, Path.map_coe, Function.comp_apply,
      Path.segment_apply, AffineMap.lineMap_apply_module,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquiv_apply] using
      DFunLike.congr_fun hv x
  -- Concatenate the polar deformation with a unitary path to the identity.
  have h₁ : JoinedIn {S : E →L[ℂ] E | S.IsInvertible} T (u : E →L[ℂ] E) := ⟨γ, hγ⟩
  obtain ⟨δ⟩ := (Unitary.joined_one u).symm
  have h₂ : JoinedIn {S : E →L[ℂ] E | S.IsInvertible} (u : E →L[ℂ] E) 1 := by
    refine ⟨δ.map continuous_subtype_val, fun t ↦ ?_⟩
    obtain ⟨v, hv⟩ := Unitary.isUnit_coe (U := δ t)
    refine ⟨ContinuousLinearEquiv.unitsEquiv ℂ E v, ?_⟩
    ext x
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquiv_apply,
      Path.map_coe, Function.comp_apply] using DFunLike.congr_fun hv x
  rw [ContinuousLinearMap.one_def] at h₂
  exact h₁.trans h₂

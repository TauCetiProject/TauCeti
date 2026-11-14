/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.CStarAlgebra.SelfAdjointSpectrumInterval
public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic
public import TauCeti.Analysis.Normed.Lp.BilateralShift
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Borel logarithms of unitary operators and global path-connectedness of `U(H)`

Every unitary operator `u` on a complex Hilbert space `H` is normal with spectrum contained in the
unit circle. Pulling the principal argument `Complex.arg : ℂ → (-π, π]` back to the spectrum and
integrating against the spectral measure of `u` via `ContinuousLinearMap.borelCalculus` produces a
bounded self-adjoint operator `Unitary.borelArgSelfAdjoint u : selfAdjoint (H →L[ℂ] H)` satisfying

* `‖Unitary.borelArgSelfAdjoint u‖ ≤ π` (`Unitary.norm_borelArgSelfAdjoint_le_pi`), and
* `selfAdjoint.expUnitary (Unitary.borelArgSelfAdjoint u) = u`
  (`Unitary.expUnitary_borelArgSelfAdjoint`).

In particular `selfAdjoint.expUnitary : selfAdjoint (H →L[ℂ] H) → unitary (H →L[ℂ] H)` is
surjective (`selfAdjoint.expUnitary_surjective`), and the single-exponential ray
`t ↦ selfAdjoint.expUnitary (t • Unitary.borelArgSelfAdjoint u)` (`Unitary.borelPathFromOne`)
connects `1` to `u` in the operator norm, making `unitary (H →L[ℂ] H)` globally path-connected
(`ContinuousLinearMap.instPathConnectedSpaceUnitary`). This strengthens Mathlib's C⋆-algebraic
local path-connectedness (`Unitary.instLocallyPathConnectedSpace`), where the identity component
is only described as finite products of exponential unitaries (`Unitary.mem_pathComponentOne_iff`).

## Comparison with `Unitary.argSelfAdjoint`

Mathlib's `Unitary.argSelfAdjoint` applies the continuous functional calculus `cfc` to
`Complex.arg`. Whenever `Complex.arg` is continuous on `spectrum ℂ (u : H →L[ℂ] H)` in the
subspace topology, `Unitary.borelArgSelfAdjoint u` agrees with `Unitary.argSelfAdjoint u`
(`Unitary.borelArgSelfAdjoint_eq_argSelfAdjoint_of_continuousOn`):

* This covers the open ball `‖(u - 1 : H →L[ℂ] H)‖ < 2`, where the spectrum avoids `-1` and lies
  in `Complex.slitPlane` (`Unitary.borelArgSelfAdjoint_eq_argSelfAdjoint`).
* It also covers `u = -1`, whose spectrum on a nontrivial space is the singleton `{-1}`: although
  `-1` lies outside `Complex.slitPlane` (so `‖(-1 : H →L[ℂ] H) - 1‖ = 2` falls outside the domain
  of `expUnitary_argSelfAdjoint`), every function on a one-point space is continuous in the
  subspace topology, and both `Unitary.borelArgSelfAdjoint (-1)` and `Unitary.argSelfAdjoint (-1)`
  equal `π • 1` (`Unitary.borelArgSelfAdjoint_neg_one`, `Unitary.argSelfAdjoint_neg_one`).

By contrast, whenever `Complex.arg` is not continuous on `spectrum ℂ u`, `cfc` returns its junk
value `0` (`Unitary.argSelfAdjoint_eq_zero_of_not_continuousOn`). Because `Circle` is compact while
its image `(-π, π]` under `Complex.arg` is not closed, `Complex.arg` is not continuous on the full
unit circle (`Complex.not_continuousOn_arg_sphere`). Thus for every unitary whose spectrum is the
entire unit circle — such as the bilateral shift on `ℓ²(ℤ, G)` for any nontrivial complex Hilbert
space `G` (`lp.spectrum_bilateralShift`) — `Unitary.argSelfAdjoint` collapses to `0`, whereas
`Unitary.borelArgSelfAdjoint` yields a genuine self-adjoint logarithm whose real spectrum is the
full interval `[-π, π]` (`Unitary.spectrum_borelArgSelfAdjoint_of_spectrum_eq_sphere`,
`lp.spectrum_borelArgSelfAdjoint_bilateralShift`).

## References

* C. R. Putnam and A. Wintner, *The orthogonal invariants of two subspaces of a Hilbert space*,
  Amer. J. Math. 74 (1952), 578–584; *The connectedness of the orthogonal group in Hilbert space*,
  Proc. Nat. Acad. Sci. U.S.A. 37 (1951), 110–112.
* J. B. Conway, *A Course in Functional Analysis*, second edition, Chapter IX, §2.
-/

public section

noncomputable section

open Complex Metric NormedSpace Set
open scoped Real ENNReal

namespace TauCeti.BoundedBorelFunction

/-- The principal argument `z ↦ (Complex.arg z : ℂ)` as a bounded Borel symbol on `ℂ`, bounded in
norm by `π`. -/
def arg : BoundedBorelFunction ℂ :=
  ofFunction (fun z : ℂ ↦ (z.arg : ℂ)) (measurable_ofReal.comp measurable_arg)
    ⟨π, Real.pi_nonneg, fun z ↦ by simpa using abs_arg_le_pi z⟩

/-- Evaluating `BoundedBorelFunction.arg` gives `Complex.arg`. -/
@[simp]
theorem arg_apply (z : ℂ) : arg z = z.arg := by
  simp [arg]

/-- The supremum norm of `BoundedBorelFunction.arg` is at most `π`. -/
theorem norm_arg_le_pi : ‖arg‖ ≤ π :=
  (norm_le Real.pi_nonneg).2 fun z ↦ by simpa using abs_arg_le_pi z

/-- `BoundedBorelFunction.arg` is real-valued, hence self-adjoint in `BoundedBorelFunction ℂ`. -/
theorem isSelfAdjoint_arg : IsSelfAdjoint arg := by
  rw [isSelfAdjoint_iff]
  ext z
  simp

/-- For any measurable map `g : X → ℂ` taking values on the unit circle, `exp(i · (arg ∘ g)) = g`
as bounded Borel symbols on `X`. -/
theorem exp_I_smul_comp_arg {X : Type*} [MeasurableSpace X] (g : X → ℂ) (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ = 1) :
    NormedSpace.exp (I • compStarAlgHom' g hg arg) =
      ofFunction g hg ⟨1, zero_le_one, fun x ↦ (hg1 x).le⟩ := by
  ext x
  rw [exp_apply, smul_apply, compStarAlgHom'_apply, arg_apply, ← exp_eq_exp_ℂ, ofFunction_apply]
  simpa [hg1 x, mul_comm I] using norm_mul_exp_arg_mul_I (g x)

end TauCeti.BoundedBorelFunction

/-- The principal argument `Complex.arg` is not continuous on the complex unit circle. -/
theorem Complex.not_continuousOn_arg_sphere :
    ¬ ContinuousOn Complex.arg (Metric.sphere (0 : ℂ) 1) := by
  intro hc
  have hf : Continuous fun z : Circle ↦ Complex.arg (z : ℂ) :=
    hc.comp_continuous continuous_subtype_val fun z ↦ z.coe_prop
  have hrange : range (fun z : Circle ↦ Complex.arg (z : ℂ)) = Ioc (-π) π := by
    ext θ
    refine ⟨?_, fun hθ ↦ ⟨Circle.exp θ, Circle.arg_exp hθ.1 hθ.2⟩⟩
    rintro ⟨z, rfl⟩
    exact ⟨neg_pi_lt_arg z, arg_le_pi z⟩
  have hclosed : IsClosed (Ioc (-π) π) := hrange ▸ (isCompact_range hf).isClosed
  have hmem : -π ∈ Ioc (-π) π := by
    rw [← hclosed.closure_eq, closure_Ioc (by linarith [Real.pi_pos])]
    exact left_mem_Icc.2 (by linarith [Real.pi_pos])
  exact lt_irrefl (-π) hmem.1

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A]

namespace selfAdjoint

/-- If `x : selfAdjoint A` satisfies `‖x‖ ≤ π` and `expUnitary x` has the full unit circle as its
complex spectrum, then the real spectrum of `x` is the entire interval `[-π, π]`. -/
theorem spectrum_eq_Icc_of_expUnitary_spectrum_eq_sphere {x : selfAdjoint A} (hx : ‖x‖ ≤ π)
    (hs : spectrum ℂ (expUnitary x : A) = sphere 0 1) :
    spectrum ℝ (x : A) = Icc (-π) π := by
  have hsub : spectrum ℝ (x : A) ⊆ Icc (-π) π :=
    (x.2.norm_le_iff_spectrum_subset_Icc Real.pi_nonneg).mp
      (by simpa [AddSubgroup.coe_norm] using hx)
  refine Subset.antisymm hsub ?_
  rw [← closure_Ioo (by linarith [Real.pi_pos] : (-π : ℝ) ≠ π)]
  refine closure_minimal (fun θ hθ ↦ ?_) (spectrum.isClosed (x : A))
  have hz : (Circle.exp θ : ℂ) ∈ spectrum ℂ (expUnitary x : A) := hs ▸ (Circle.exp θ).coe_prop
  simp only [expUnitary_coe] at hz
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← cfc_comp_smul I _ (x : A), cfc_map_spectrum ..,
    ← x.2.spectrumRestricts.algebraMap_image] at hz
  obtain ⟨_, ⟨t, ht, rfl⟩, h_eq⟩ := hz
  have ht_bounds : t ∈ Icc (-π) π := hsub ht
  have hexp : (Circle.exp t : ℂ) = Circle.exp θ := by
    simpa [Algebra.algebraMap_eq_smul_one, ← exp_eq_exp_ℂ, mul_comm I, Circle.coe_exp] using h_eq
  rcases eq_or_lt_of_le ht_bounds.1 with rfl | ht_gt
  · exfalso
    have hneg : (Circle.exp (-π) : ℂ) = -1 := by
      rw [Circle.coe_exp, ofReal_neg, neg_mul, Complex.exp_neg, exp_pi_mul_I, inv_neg, inv_one]
    have harg := congrArg Complex.arg (hneg ▸ hexp)
    rw [arg_neg_one, Circle.arg_exp hθ.1 hθ.2.le] at harg
    exact hθ.2.ne harg.symm
  · have harg := congrArg Complex.arg hexp
    rw [Circle.arg_exp ht_gt ht_bounds.2, Circle.arg_exp hθ.1 hθ.2.le] at harg
    exact harg ▸ ht

end selfAdjoint

namespace Unitary

/-- The continuous-calculus argument of `1` is `0`. -/
@[simp]
theorem argSelfAdjoint_one : argSelfAdjoint (1 : unitary A) = 0 := by
  ext
  simp [argSelfAdjoint_coe]

/-- The continuous-calculus argument of `-1` is `π • 1`. -/
theorem argSelfAdjoint_neg_one : argSelfAdjoint (-1 : unitary A) = π • 1 := by
  ext
  have hneg : ((-1 : unitary A) : A) = algebraMap ℂ A (-1) := by
    rw [Unitary.coe_neg, OneMemClass.coe_one, map_neg, map_one]
  rw [argSelfAdjoint_coe, hneg, cfc_algebraMap, arg_neg_one, Algebra.algebraMap_eq_smul_one,
    Complex.coe_smul, selfAdjoint.val_smul, selfAdjoint.val_one]

/-- When `Complex.arg` is not continuous on the spectrum of `u`, `Unitary.argSelfAdjoint u` takes
the junk value `0`. -/
theorem argSelfAdjoint_eq_zero_of_not_continuousOn {u : unitary A}
    (h : ¬ ContinuousOn Complex.arg (spectrum ℂ (u : A))) :
    argSelfAdjoint u = 0 := by
  ext
  rw [argSelfAdjoint_coe, cfc_apply_of_not_continuousOn]
  · rfl
  · intro hc
    exact h (by simpa [Function.comp_def] using continuous_re.comp_continuousOn hc)

/-- If the spectrum of `u` is the full unit circle, then `Unitary.argSelfAdjoint u = 0`. -/
theorem argSelfAdjoint_eq_zero_of_spectrum_eq_sphere {u : unitary A}
    (hs : spectrum ℂ (u : A) = sphere 0 1) :
    argSelfAdjoint u = 0 :=
  argSelfAdjoint_eq_zero_of_not_continuousOn (hs ▸ Complex.not_continuousOn_arg_sphere)

end Unitary

end CStarAlgebra

section Hilbert

open TauCeti

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Unitary

/-- The **Borel argument** of a unitary operator `u` on a complex Hilbert space `H`: the bounded
self-adjoint operator obtained by integrating `Complex.arg` against the spectral measure of `u`.
Unlike `Unitary.argSelfAdjoint`, this requires no spectral gap and satisfies
`selfAdjoint.expUnitary (borelArgSelfAdjoint u) = u` for every unitary `u`. -/
@[irreducible]
def borelArgSelfAdjoint (u : unitary (H →L[ℂ] H)) : selfAdjoint (H →L[ℂ] H) :=
  ⟨(u : H →L[ℂ] H).borelCalculus
      (BoundedBorelFunction.compStarAlgHom' Subtype.val measurable_subtype_coe
        BoundedBorelFunction.arg),
    (BoundedBorelFunction.isSelfAdjoint_arg.map _).map _⟩

/-- The underlying bounded operator of `Unitary.borelArgSelfAdjoint u` is the Borel calculus of
`Complex.arg` on `spectrum ℂ (u : H →L[ℂ] H)`. -/
theorem coe_borelArgSelfAdjoint (u : unitary (H →L[ℂ] H)) :
    (borelArgSelfAdjoint u : H →L[ℂ] H) =
      (u : H →L[ℂ] H).borelCalculus
        (BoundedBorelFunction.compStarAlgHom' Subtype.val measurable_subtype_coe
          BoundedBorelFunction.arg) := by
  unfold borelArgSelfAdjoint
  rfl

/-- Every Borel unitary argument has operator norm at most `π`. -/
theorem norm_borelArgSelfAdjoint_le_pi (u : unitary (H →L[ℂ] H)) :
    ‖borelArgSelfAdjoint u‖ ≤ π := by
  rw [AddSubgroup.coe_norm, coe_borelArgSelfAdjoint]
  exact (u : H →L[ℂ] H).norm_borelCalculus_le Real.pi_nonneg fun x ↦ by
    simpa using abs_arg_le_pi (x : ℂ)

/-- The real spectrum of `Unitary.borelArgSelfAdjoint u` lies in `[-π, π]`. -/
theorem spectrum_borelArgSelfAdjoint_subset_Icc (u : unitary (H →L[ℂ] H)) :
    spectrum ℝ (borelArgSelfAdjoint u : H →L[ℂ] H) ⊆ Icc (-π) π :=
  ((borelArgSelfAdjoint u).2.norm_le_iff_spectrum_subset_Icc Real.pi_nonneg).mp
    (by simpa [AddSubgroup.coe_norm] using norm_borelArgSelfAdjoint_le_pi u)

/-- **Exponential of the Borel argument.** For every unitary `u` on a complex Hilbert space,
`exp(i · borelArgSelfAdjoint u) = u`. -/
@[simp]
theorem expUnitary_borelArgSelfAdjoint (u : unitary (H →L[ℂ] H)) :
    selfAdjoint.expUnitary (borelArgSelfAdjoint u) = u := by
  ext1
  have h1 : ∀ x : spectrum ℂ (u : H →L[ℂ] H), ‖(x : ℂ)‖ = 1 :=
    fun x ↦ spectrum.norm_eq_one_of_unitary u.property x.property
  have hid :
      BoundedBorelFunction.ofFunction (Subtype.val : spectrum ℂ (u : H →L[ℂ] H) → ℂ)
        measurable_subtype_coe ⟨1, zero_le_one, fun x ↦ (h1 x).le⟩ =
      BoundedBorelFunction.ofContinuousMap
        ((ContinuousMap.id ℂ).restrict (spectrum ℂ (u : H →L[ℂ] H))) := by
    ext x
    simp
  rw [selfAdjoint.expUnitary_coe, coe_borelArgSelfAdjoint, ← map_smul,
    ← (u : H →L[ℂ] H).borelCalculus_exp,
    BoundedBorelFunction.exp_I_smul_comp_arg Subtype.val measurable_subtype_coe h1, hid,
    (u : H →L[ℂ] H).borelCalculus_restrict_id]

/-- Every unitary operator on a complex Hilbert space is of the form `expUnitary x` for a
self-adjoint operator `x` of norm at most `π`. -/
theorem exists_expUnitary_eq_and_norm_le_pi (u : unitary (H →L[ℂ] H)) :
    ∃ x : selfAdjoint (H →L[ℂ] H), selfAdjoint.expUnitary x = u ∧ ‖x‖ ≤ π :=
  ⟨borelArgSelfAdjoint u, expUnitary_borelArgSelfAdjoint u, norm_borelArgSelfAdjoint_le_pi u⟩

/-- The exponential map `selfAdjoint (H →L[ℂ] H) → unitary (H →L[ℂ] H)` is surjective. -/
theorem _root_.selfAdjoint.expUnitary_surjective :
    Function.Surjective (selfAdjoint.expUnitary : selfAdjoint (H →L[ℂ] H) → unitary (H →L[ℂ] H)) :=
  fun u ↦ ⟨borelArgSelfAdjoint u, expUnitary_borelArgSelfAdjoint u⟩

/-- Whenever `Complex.arg` is continuous on the spectrum of `u`, the Borel argument coincides with
Mathlib's continuous-calculus argument `Unitary.argSelfAdjoint u`. -/
theorem borelArgSelfAdjoint_eq_argSelfAdjoint_of_continuousOn {u : unitary (H →L[ℂ] H)}
    (h : ContinuousOn Complex.arg (spectrum ℂ (u : H →L[ℂ] H))) :
    borelArgSelfAdjoint u = argSelfAdjoint u := by
  ext1
  have hf : ContinuousOn (fun z : ℂ ↦ (z.arg : ℂ)) (spectrum ℂ (u : H →L[ℂ] H)) :=
    continuous_ofReal.comp_continuousOn h
  have hsym :
      BoundedBorelFunction.compStarAlgHom' Subtype.val measurable_subtype_coe
        BoundedBorelFunction.arg =
      BoundedBorelFunction.ofContinuousMap
        ⟨(spectrum ℂ (u : H →L[ℂ] H)).domRestrict (fun z : ℂ ↦ (z.arg : ℂ)), hf.domRestrict⟩ := by
    ext x
    simp
  rw [coe_borelArgSelfAdjoint, hsym, (u : H →L[ℂ] H).borelCalculus_ofContinuousMap_domRestrict _ hf,
    argSelfAdjoint_coe]

/-- On the open ball `‖u - 1‖ < 2`, `Unitary.borelArgSelfAdjoint` agrees with
`Unitary.argSelfAdjoint`. -/
theorem borelArgSelfAdjoint_eq_argSelfAdjoint {u : unitary (H →L[ℂ] H)}
    (hu : ‖(u - 1 : H →L[ℂ] H)‖ < 2) :
    borelArgSelfAdjoint u = argSelfAdjoint u :=
  borelArgSelfAdjoint_eq_argSelfAdjoint_of_continuousOn <|
    continuousOn_arg.mono <| (spectrum_subset_slitPlane_iff_norm_lt_two u.property).mpr hu

/-- For `‖x‖ < π`, `Unitary.borelArgSelfAdjoint` is a left inverse to `selfAdjoint.expUnitary`. -/
theorem borelArgSelfAdjoint_expUnitary {x : selfAdjoint (H →L[ℂ] H)} (hx : ‖x‖ < π) :
    borelArgSelfAdjoint (H := H) (selfAdjoint.expUnitary x) = x := by
  have hball : selfAdjoint.expUnitary x ∈ ball (1 : unitary (H →L[ℂ] H)) 2 :=
    openPartialHomeomorph.map_target (by simpa using hx)
  rw [borelArgSelfAdjoint_eq_argSelfAdjoint (by simpa [Subtype.dist_eq, dist_eq_norm] using hball),
    argSelfAdjoint_expUnitary (A := H →L[ℂ] H) hx]

/-- The Borel argument of `1` is `0`. -/
@[simp]
theorem borelArgSelfAdjoint_one : borelArgSelfAdjoint (1 : unitary (H →L[ℂ] H)) = 0 := by
  nontriviality H
  rw [borelArgSelfAdjoint_eq_argSelfAdjoint (by simp), argSelfAdjoint_one]

/-- The Borel argument of `-1` is `π • 1`. -/
theorem borelArgSelfAdjoint_neg_one :
    borelArgSelfAdjoint (-1 : unitary (H →L[ℂ] H)) = π • 1 := by
  nontriviality H
  have heq : spectrum ℂ ((-1 : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = {-1} := by
    have hneg : ((-1 : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = algebraMap ℂ (H →L[ℂ] H) (-1) := by
      rw [Unitary.coe_neg, OneMemClass.coe_one, map_neg, map_one]
    rw [hneg, CFC.spectrum_algebraMap_eq]
  have hcont : ContinuousOn Complex.arg (spectrum ℂ ((-1 : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) := by
    rw [heq]
    exact continuousOn_singleton Complex.arg (-1)
  rw [borelArgSelfAdjoint_eq_argSelfAdjoint_of_continuousOn hcont, argSelfAdjoint_neg_one]

/-- On a nontrivial Hilbert space, `Unitary.borelArgSelfAdjoint (-1)` attains the sharp bound
`π`. -/
theorem norm_borelArgSelfAdjoint_neg_one [Nontrivial H] :
    ‖borelArgSelfAdjoint (-1 : unitary (H →L[ℂ] H))‖ = π := by
  rw [borelArgSelfAdjoint_neg_one, AddSubgroup.coe_norm, selfAdjoint.val_smul, selfAdjoint.val_one,
    norm_smul, norm_one, mul_one, Real.norm_of_nonneg Real.pi_nonneg]

/-- When `u` has the full unit circle as its spectrum, `Unitary.borelArgSelfAdjoint u` has the full
interval `[-π, π]` as its real spectrum (whereas `Unitary.argSelfAdjoint u = 0`). -/
theorem spectrum_borelArgSelfAdjoint_of_spectrum_eq_sphere {u : unitary (H →L[ℂ] H)}
    (hs : spectrum ℂ (u : H →L[ℂ] H) = sphere 0 1) :
    spectrum ℝ (borelArgSelfAdjoint u : H →L[ℂ] H) = Icc (-π) π :=
  selfAdjoint.spectrum_eq_Icc_of_expUnitary_spectrum_eq_sphere (A := H →L[ℂ] H)
    (norm_borelArgSelfAdjoint_le_pi u)
    (by simpa [expUnitary_borelArgSelfAdjoint] using hs)

/-- The canonical norm-continuous path `t ↦ expUnitary (t • borelArgSelfAdjoint u)` from `1` to `u`
in `unitary (H →L[ℂ] H)` given by a single exponential. -/
def borelPathFromOne (u : unitary (H →L[ℂ] H)) : Path 1 u :=
  (selfAdjoint.expUnitaryPathToOne (A := H →L[ℂ] H) (borelArgSelfAdjoint u)).cast rfl
    (expUnitary_borelArgSelfAdjoint u).symm

/-- Evaluating `Unitary.borelPathFromOne u` at `t` gives `expUnitary (t • borelArgSelfAdjoint u)`.
-/
@[simp]
theorem borelPathFromOne_apply (u : unitary (H →L[ℂ] H)) (t : unitInterval) :
    borelPathFromOne u t = selfAdjoint.expUnitary ((t : ℝ) • borelArgSelfAdjoint u) := by
  simp [borelPathFromOne]

/-- Every unitary operator on a complex Hilbert space is joined to `1` in `unitary (H →L[ℂ] H)`. -/
theorem joined_one (u : unitary (H →L[ℂ] H)) : Joined 1 u :=
  ⟨borelPathFromOne u⟩

/-- **Global norm-path-connectedness of the unitary group** of a complex Hilbert space. -/
instance _root_.ContinuousLinearMap.instPathConnectedSpaceUnitary :
    PathConnectedSpace (unitary (H →L[ℂ] H)) :=
  PathConnectedSpace.mk ⟨1⟩ fun u v ↦ (joined_one u).symm.trans (joined_one v)

/-- As a subset of `H →L[ℂ] H`, the unitary operators form a path-connected set in the operator
norm. -/
theorem _root_.ContinuousLinearMap.isPathConnected_unitary :
    IsPathConnected (unitary (H →L[ℂ] H) : Set (H →L[ℂ] H)) :=
  isPathConnected_iff_pathConnectedSpace.mpr ContinuousLinearMap.instPathConnectedSpaceUnitary

end Unitary

end Hilbert

namespace lp

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] [Nontrivial G]

/-- Because the bilateral shift on `ℓ²(ℤ, G)` has the full unit circle as its spectrum, Mathlib's
continuous-calculus argument `Unitary.argSelfAdjoint` vanishes on it. -/
theorem argSelfAdjoint_bilateralShift :
    Unitary.argSelfAdjoint (A := lp (fun _ : ℤ ↦ G) 2 →L[ℂ] lp (fun _ : ℤ ↦ G) 2)
      (Unitary.linearIsometryEquiv.symm (bilateralShift 2 ℂ G)) = 0 :=
  Unitary.argSelfAdjoint_eq_zero_of_spectrum_eq_sphere spectrum_bilateralShift

/-- The Borel argument of the bilateral shift on `ℓ²(ℤ, G)` has the full interval `[-π, π]` as its
real spectrum. -/
theorem spectrum_borelArgSelfAdjoint_bilateralShift :
    spectrum ℝ
      (Unitary.borelArgSelfAdjoint (H := lp (fun _ : ℤ ↦ G) 2)
        (Unitary.linearIsometryEquiv.symm (bilateralShift 2 ℂ G)) :
        lp (fun _ : ℤ ↦ G) 2 →L[ℂ] lp (fun _ : ℤ ↦ G) 2) = Icc (-π) π :=
  Unitary.spectrum_borelArgSelfAdjoint_of_spectrum_eq_sphere spectrum_bilateralShift

end lp

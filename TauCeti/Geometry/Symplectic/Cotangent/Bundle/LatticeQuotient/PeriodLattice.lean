/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Localized
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LatticeQuotient.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.VerticalFlow
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Lattice
import Mathlib.Algebra.Group.Subgroup.Finsupp

/-!
# The period lattice of the torus bundle `T*B/Λ`

Let `α i` be closed one-forms on a manifold `B` forming a global frame of `T*B`, and let
`T*B/Λ = TauCeti.CotangentBundle.LatticeQuotient α hα` be the quotient of the cotangent bundle by
the lattice `Λ_x` of integer combinations of the `α i x`. With the descended canonical form, the
projection `T*B/Λ → B` is a regular Lagrangian torus fibration
(`TauCeti.CotangentBundle.LatticeQuotient.isLagrangianTorusFibration_proj`), so it has a period
lattice `Λ'_b ⊆ T*_b B` at every point
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration.periodLattice`). This file
proves that it is the lattice the quotient was built from:

`Λ'_b = Λ_b = {∑ i, k i • α i b | k : ι → ℤ}`

(`TauCeti.CotangentBundle.LatticeQuotient.periodLattice_eq_closure`). So `T*B/Λ` is the canonical
torus bundle of its own period lattice, as the classification of regular Lagrangian torus
fibrations by their period lattice and Lagrangian class requires of its model.

The proof computes the action of `T*_b B` on the fibre over `b`. On `T*B` the Hamiltonian flow of
`g ∘ π` translates each covector `p` over `x` to `p - t dg_x`
(`TauCeti.CotangentBundle.flowOf_hamiltonianVectorField_comp_proj`). The quotient map
`T*B → T*B/Λ` is a local diffeomorphism pulling the descended form back to the canonical one, so it
carries these trajectories to trajectories of the Hamiltonian flow of `g ∘ proj` on `T*B/Λ`
(`TauCeti.CotangentBundle.LatticeQuotient.flowOf_hamiltonianVectorField_comp_proj_mk`). Hence a
covector `β` at `b` acts on the fibre by `[b, p] ↦ [b, p - β]`
(`TauCeti.CotangentBundle.LatticeQuotient.coe_fiberAction_mk`), which fixes a point exactly when
`β ∈ Λ_b`.

## Main results

* `TauCeti.CotangentBundle.LatticeQuotient.flowOf_hamiltonianVectorField_comp_proj_mk`: the
  Hamiltonian flow of `g ∘ proj` on `T*B/Λ` is `[x, p] ↦ [x, p - t dg_x]`.
* `TauCeti.CotangentBundle.LatticeQuotient.coe_fiberAction_mk`: a covector `β` at `b` acts on the
  fibre over `b` by `[b, p] ↦ [b, p - β]`.
* `TauCeti.CotangentBundle.LatticeQuotient.mem_periodLattice_iff`,
  `TauCeti.CotangentBundle.LatticeQuotient.periodLattice_eq_closure`: the period lattice of
  `T*B/Λ → B` at `b` is the lattice spanned by the `α i b`.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1 (the period lattice and the torus bundle `T*B/Λ`).
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

namespace LatticeQuotient

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {B : Type*}
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B] [T2Space B] {ι : Type*} [Fintype ι]
  {α : ι → SmoothForm I B ℝ 1}
  (hα : IsLocalFrameOn I (E →L[ℝ] ℝ) ∞ (fun i x ↦ SmoothForm.degreeOneEquiv (α i) x) univ)
  (hclosed : ∀ i, (α i).IsClosed)

/-- **Hamiltonian flows of functions on the base of `T*B/Λ`.** For a `C²` function `g` on `B`, the
Hamiltonian flow of `g ∘ proj` for the descended symplectic form moves the class of a covector `p`
over `x` to the class of `p - t dg_x` at time `t`. -/
theorem flowOf_hamiltonianVectorField_comp_proj_mk {g : B → ℝ} (hg : ContMDiff I 𝓘(ℝ) 2 g)
    (t : ℝ) (z : CotangentBundle I B) :
    flowOf ((symplecticForm hα hclosed).hamiltonianVectorField (g ∘ proj hα)) t (mk hα z) =
      mk hα ⟨z.proj, z.snd - t • mvfderiv I g z.proj⟩ := by
  have hσ := (isSymplectic_symplecticForm hα hclosed).isNondegenerate
  have hgπ : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) 2 (g ∘ proj hα) :=
    hg.comp ((contMDiff_proj hα).of_le (by simp))
  -- The vertical line through `z` is a trajectory upstairs, and the quotient map carries it to a
  -- trajectory of the descended Hamiltonian vector field.
  have hγ := isMIntegralCurve_hamiltonianVectorField_comp_proj (M := B)
    ((hg z.proj).mdifferentiableAt (by simp)) z.snd
  rw [← congrArg (g ∘ ·) (proj_comp_mk hα)] at hγ
  have hγ' := (CotangentBundle.isSymplectic_symplecticForm (I := I) (M := B)).isNondegenerate
    |>.isMIntegralCurve_comp_hamiltonianVectorField hσ (contMDiff_mk hα)
      (mpullback_mk_symplecticForm hα hclosed)
    (fun s ↦ by
      obtain ⟨e, he⟩ := (isLocalDiffeomorph_mk hα).isInvertible_mfderiv (by simp)
        (⟨z.proj, z.snd - s • mvfderiv I g z.proj⟩ : CotangentBundle I B)
      rw [← he]
      exact e.surjective)
    (fun s ↦ ((hgπ _).mdifferentiableAt (by simp))) hγ
  have h := flowOf_eq_of_isMIntegralCurve
    ((isLagrangianTorusFibration_proj hα hclosed).contMDiff_hamiltonianVectorField_comp hg) hγ' t
  simpa using h

/-- **The action of `T*_b B` on a fibre of `T*B/Λ`.** A covector `β` at `b` acts on the fibre of
`T*B/Λ → B` over `b` by `[b, p] ↦ [b, p - β]`: this is the time-one map of the Hamiltonian flow of
`g ∘ proj` for any `C²` function `g` with `dg_b = β`. -/
@[simp]
theorem coe_fiberAction_mk {b : B} (β p : E →L[ℝ] ℝ)
    (hp : mk hα ⟨b, p⟩ ∈ proj hα ⁻¹' {b}) :
    ((isLagrangianTorusFibration_proj hα hclosed).fiberAction
        (isSymplectic_symplecticForm hα hclosed).isClosed b β ⟨mk hα ⟨b, p⟩, hp⟩ :
          LatticeQuotient α hα) =
      mk hα ⟨b, p - β⟩ := by
  obtain ⟨g, -, hgβ⟩ := exists_contMDiffMap_mvfderiv_eq (I := I) b (0 : ℝ) β
  rw [(isLagrangianTorusFibration_proj hα hclosed).coe_fiberAction_eq_flowOf _ b
      (g.contMDiff.of_le (by simp)) hgβ,
    flowOf_hamiltonianVectorField_comp_proj_mk hα hclosed (g.contMDiff.of_le (by simp)),
    one_smul]
  exact congrArg (fun q : E →L[ℝ] ℝ ↦ mk hα ⟨b, p - q⟩) hgβ

/-- **The period lattice of `T*B/Λ` is `Λ`.** A covector at `b` lies in the period lattice of the
fibration `T*B/Λ → B` exactly when it is an integer combination of the covectors `α i b`. -/
theorem mem_periodLattice_iff (b : B) {β : E →L[ℝ] ℝ} :
    β ∈ (isLagrangianTorusFibration_proj hα hclosed).periodLattice
        (isSymplectic_symplecticForm hα hclosed).isClosed b ↔
      ∃ k : ι → ℤ, β = ∑ i, (k i : ℝ) • SmoothForm.degreeOneEquiv (α i) b := by
  have hp : mk hα ⟨b, 0⟩ ∈ proj hα ⁻¹' {b} := proj_mk hα _
  -- `β` lies in the period lattice exactly when it fixes the class of the zero covector.
  have h₁ : β ∈ (isLagrangianTorusFibration_proj hα hclosed).periodLattice
      (isSymplectic_symplecticForm hα hclosed).isClosed b ↔
        mk hα ⟨b, (0 : E →L[ℝ] ℝ) - β⟩ = mk hα ⟨b, 0⟩ :=
    ((isLagrangianTorusFibration_proj hα hclosed).mem_periodLattice_iff_fiberAction_eq _ b
      ⟨_, hp⟩).trans (Subtype.ext_iff.trans (Eq.congr_left (coe_fiberAction_mk hα hclosed β 0 hp)))
  -- The covectors of the frame at `b`, as elements of the model dual `E →L[ℝ] ℝ`.
  let a : ι → E →L[ℝ] ℝ := fun i ↦ SmoothForm.degreeOneEquiv (α i) b
  have h₂ (k : ι → ℤ) : (0 : E →L[ℝ] ℝ) - β = 0 + ∑ i, (k i : ℝ) • a i ↔
      β = ∑ i, ((-k) i : ℝ) • a i := by
    simp [neg_eq_iff_eq_neg, neg_smul (M := E →L[ℝ] ℝ)]
  exact h₁.trans ((mk_mk_eq_mk_mk_iff hα).trans ((Equiv.neg (ι → ℤ)).exists_congr h₂))

/-- **The period lattice of `T*B/Λ` is `Λ`**, as the subgroup of `T*_b B` generated by the
covectors `α i b` of the frame. -/
theorem periodLattice_eq_closure (b : B) :
    (isLagrangianTorusFibration_proj hα hclosed).periodLattice
        (isSymplectic_symplecticForm hα hclosed).isClosed b =
      AddSubgroup.closure (range fun i ↦ (SmoothForm.degreeOneEquiv (α i) b : E →L[ℝ] ℝ)) := by
  ext β
  -- The covectors of the frame at `b`, as elements of the model dual `E →L[ℝ] ℝ`.
  let a : ι → E →L[ℝ] ℝ := fun i ↦ SmoothForm.degreeOneEquiv (α i) b
  have h := AddSubgroup.mem_closure_range_iff_of_fintype (f := a) (x := β)
  simp only [← Int.cast_smul_eq_zsmul ℝ] at h
  exact (mem_periodLattice_iff hα hclosed b).trans h.symm

end LatticeQuotient

end CotangentBundle

end TauCeti

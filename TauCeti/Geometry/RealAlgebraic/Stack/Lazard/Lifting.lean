/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Lazard.RealRoots
public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Local

/-!
# Analytic Lazard lifting for one polynomial

A polynomial in one distinguished variable has a global Lazard delineation over a connected
real analytic submanifold when its formal leading coefficient, constant coefficient, and
discriminant are nonzero and have constant Lazard valuation there. Ordinary fibers may vanish:
the sections enumerate the roots of the nonzero Lazard evaluations instead.

The construction applies the local Puiseux preparation theorem in analytic chart coordinates.
That theorem supplies ordered analytic roots, constant multiplicities, and a locally constant
vector of removed base exponents on one common neighborhood. These local Lazard delineations
then glue because their increasing root lists describe the same intrinsic fibers.

The nonzero constant-coefficient hypothesis excludes the distinguished-coordinate factor. In
family lifting that factor is separated and handled by
`TauCeti.nonempty_lazardDelineation_lastCoordinate`.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5.2,
  Theorem 5.1.
-/

public section

open Filter MvPolynomial Set Topology

namespace Polynomial

variable {n d : ℕ} {S : Set (Fin n → ℝ)}

/-- **Analytic Lazard lifting for one polynomial.** Let `p` be a polynomial in a distinguished
variable with coefficients in `ℝ[X₀, …, Xₙ₋₁]`. If its formal leading coefficient,
constant coefficient, and discriminant are nonzero and each has constant Lazard valuation on a
preconnected analytic submanifold `S`, then the corresponding polynomial in `n + 1` variables
has a Lazard delineation over `S`.

The conclusion concerns Lazard evaluations, so ordinary fibers may be zero and their degrees may
drop. Constant polynomials and polynomials without real Lazard roots are included. -/
theorem nonempty_lazardDelineation_of_lazardValuation_eq
    (p : Polynomial (MvPolynomial (Fin n) ℝ))
    (hS : TauCeti.IsAnalyticSubmanifold d S) (hconn : IsPreconnected S)
    (hlead : p.leadingCoeff ≠ 0) (hconst : p.coeff 0 ≠ 0) (hdiscr : p.discr ≠ 0)
    (hlead_eq : ∀ x ∈ S, ∀ y ∈ S,
      p.leadingCoeff.lazardValuation x = p.leadingCoeff.lazardValuation y)
    (hconst_eq : ∀ x ∈ S, ∀ y ∈ S,
      (p.coeff 0).lazardValuation x = (p.coeff 0).lazardValuation y)
    (hdiscr_eq : ∀ x ∈ S, ∀ y ∈ S,
      p.discr.lazardValuation x = p.discr.lazardValuation y) :
    Nonempty (TauCeti.LazardDelineation (fun _ : Unit ↦
      rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm p)) S) := by
  classical
  let F : MvPolynomial (Fin (n + 1)) ℝ :=
    rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm p)
  let q : MvPolynomial (Fin n) ℝ[X] :=
    optionEquivRight ℝ (Fin n) ((optionEquivLeft ℝ (Fin n)).symm p)
  have hswap : optionEquivRight ℝ (Fin n) (rename finSuccEquivLast F) = q := by
    simp only [F, q, rename_rename, Equiv.self_comp_symm, rename_id_apply]
  apply TauCeti.nonempty_lazardDelineation_of_locally hconn hS.nonempty
  intro x
  -- In chart coordinates the three global valuation hypotheses become the eventual
  -- finite-valuation hypotheses of the local Puiseux construction.
  obtain ⟨e, hxe, he⟩ := hS.exists_isAnalyticChart x x.2
  let a := TauCeti.firstCoords ℝ n d (e x)
  let φ := fun u ↦ e.symm (TauCeti.firstCoords ℝ d n u)
  have hφ : AnalyticAt ℝ φ a := he.analyticAt_symm_firstCoords hxe x.2
  have hφS : ∀ᶠ u in 𝓝 a, φ u ∈ S :=
    (he.eventually_symm_firstCoords_mem hxe x.2).mono fun _ hu ↦ hu.2
  let vLead := p.leadingCoeff.lazardExponent x
  let vConst := (p.coeff 0).lazardExponent x
  let vDiscr := p.discr.lazardExponent x
  have hlead' : ∀ᶠ u in 𝓝 a,
      p.leadingCoeff.lazardValuation (φ u) = toLex vLead := by
    filter_upwards [hφS] with u hu
    rw [hlead_eq (φ u) hu x x.2, lazardValuation_eq_lazardExponent hlead x]
  have hconst' : ∀ᶠ u in 𝓝 a,
      (p.coeff 0).lazardValuation (φ u) = toLex vConst := by
    filter_upwards [hφS] with u hu
    rw [hconst_eq (φ u) hu x x.2, lazardValuation_eq_lazardExponent hconst x]
  have hdiscr' : ∀ᶠ u in 𝓝 a,
      p.discr.lazardValuation (φ u) = toLex vDiscr := by
    filter_upwards [hφS] with u hu
    rw [hdiscr_eq (φ u) hu x x.2, lazardValuation_eq_lazardExponent hdiscr x]
  obtain ⟨k, t, V, hV, haV, _, hexponent, ht, hmono, hroots, hpos, hmult⟩ :=
    p.exists_analyticOnNhd_ordered_lazardEval_roots hφ vLead vConst vDiscr
      hlead' hconst' hdiscr'
  -- Pull the coordinate neighborhood back through the chart, retaining an ambient open set
  -- as required by local-to-global gluing.
  let C : S → Fin d → ℝ := fun y ↦ TauCeti.firstCoords ℝ n d (e y)
  let U : Set (Fin n → ℝ) := e.source ∩
    (fun y ↦ TauCeti.firstCoords ℝ n d (e y)) ⁻¹' V
  have hcoord : ContinuousOn (fun y ↦ TauCeti.firstCoords ℝ n d (e y)) e.source :=
    (TauCeti.firstCoords ℝ n d).continuous.comp_continuousOn e.continuousOn
  have hU : IsOpen U := hcoord.isOpen_inter_preimage e.open_source hV
  have hxU : x.1 ∈ U := by
    exact ⟨hxe, haV⟩
  let T : Set (Fin n → ℝ) := S ∩ U
  let ψ : T → V := fun y ↦ ⟨C ⟨y.1, y.2.1⟩, y.2.2.2⟩
  have hψ : Continuous ψ := by
    exact Continuous.subtype_mk ((TauCeti.firstCoords ℝ n d).continuous.comp
      (e.continuousOn.comp_continuous continuous_subtype_val fun y ↦ y.2.2.1)) _
  have hφψ (y : T) : φ (ψ y) = y :=
    he.symm_firstCoords_firstCoords_apply y.2.2.1 y.2.1
  -- The ordered chart roots and their common exponent and multiplicity data are exactly the
  -- fields of a local Lazard delineation.
  let D : TauCeti.LazardDelineation (fun _ : Unit ↦ F) T :=
    { nonempty := ⟨x, x.2, hxU⟩
      count := k
      root := fun i y ↦ t i (ψ y)
      continuous_root := fun i ↦
        (ht i).continuousOn.comp_continuous (continuous_subtype_val.comp hψ)
          fun y ↦ (ψ y).2
      strictMono_root := fun y ↦ hmono (ψ y) (ψ y).2
      exponent := fun _ ↦ q.lazardExponent (Polynomial.C ∘ φ a)
      lazardExponent_eq := fun _ y ↦ by
        rw [hswap, ← hφψ y]
        exact hexponent (ψ y) (ψ y).2
      multiplicity := fun _ i ↦
        (q.lazardEval (Polynomial.C ∘ φ a)).rootMultiplicity (t i a)
      rootMultiplicity_root := fun _ i y ↦ by
        rw [hswap, ← hφψ y]
        exact hmult (ψ y) (ψ y).2 i
      exists_root_eq := fun _ y _ z hz ↦ by
        rw [hswap, ← hφψ y] at hz
        exact (hroots (ψ y) (ψ y).2 z).1 hz
      exists_multiplicity_pos := fun i ↦ ⟨(), hpos i⟩ }
  exact ⟨U, hU, hxU, by simpa only [F] using Nonempty.intro D⟩

end Polynomial

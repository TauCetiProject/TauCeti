/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Lazard.RealRoots
public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Local
import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Coordinate
import TauCeti.RingTheory.Polynomial.Resultant.Product

/-!
# Analytic Lazard lifting for one polynomial

A nonzero polynomial in one distinguished variable has a global Lazard delineation over a
connected real analytic submanifold when its discriminant is nonzero and its formal leading
coefficient, trailing coefficient, and discriminant have constant Lazard valuation there.
Ordinary fibers may vanish: the sections enumerate the roots of the nonzero Lazard evaluations
instead.

The construction applies the local Puiseux preparation theorem in analytic chart coordinates.
That theorem supplies ordered analytic roots, constant multiplicities, and a locally constant
vector of removed base exponents on one common neighborhood. These local Lazard delineations
then glue because their increasing root lists describe the same intrinsic fibers.

The distinguished-coordinate factor is treated separately. Since the discriminant is nonzero,
the distinguished variable divides the polynomial at most once. If it does not divide it, the
trailing coefficient is the constant coefficient and the local construction applies directly.
Otherwise the polynomial is `X * q` with `q` of nonzero constant coefficient. The invariants of
`q` are constant because those of `X * q` are (`Polynomial.discr_X_mul`), and the delineation
of `q` extends to `X * q` by `TauCeti.nonempty_lazardDelineation_X_mul`.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5.2,
  Theorem 5.1.
-/

public section

open Filter MvPolynomial Set Topology

namespace Polynomial

variable {n d : ℕ} {S : Set (Fin n → ℝ)}

/-- Analytic Lazard lifting for a polynomial with nonzero formal constant coefficient. Here the
trailing coefficient is the constant coefficient, and no coordinate factor occurs. -/
private theorem nonempty_lazardDelineation_of_coeff_zero_ne_zero
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

/-- **Analytic Lazard lifting for one polynomial.** Let `p` be a nonzero polynomial in a
distinguished variable with coefficients in `ℝ[X₀, …, Xₙ₋₁]`. If its formal leading coefficient,
trailing coefficient, and discriminant each have constant Lazard valuation on a preconnected
analytic submanifold `S`, and its discriminant is nonzero, then the corresponding polynomial in
`n + 1` variables has a Lazard delineation over `S`.

The conclusion concerns Lazard evaluations, so ordinary fibers may be zero and their degrees may
drop. Constant polynomials, polynomials without real Lazard roots, and polynomials divisible by
the distinguished variable are included. -/
theorem nonempty_lazardDelineation_of_lazardValuation_eq
    (p : Polynomial (MvPolynomial (Fin n) ℝ))
    (hS : TauCeti.IsAnalyticSubmanifold d S) (hconn : IsPreconnected S)
    (hp : p ≠ 0) (hdiscr : p.discr ≠ 0)
    (hlead_eq : ∀ x ∈ S, ∀ y ∈ S,
      p.leadingCoeff.lazardValuation x = p.leadingCoeff.lazardValuation y)
    (htrail_eq : ∀ x ∈ S, ∀ y ∈ S,
      p.trailingCoeff.lazardValuation x = p.trailingCoeff.lazardValuation y)
    (hdiscr_eq : ∀ x ∈ S, ∀ y ∈ S,
      p.discr.lazardValuation x = p.discr.lazardValuation y) :
    Nonempty (TauCeti.LazardDelineation (fun _ : Unit ↦
      rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm p)) S) := by
  classical
  by_cases h0 : p.coeff 0 = 0
  swap
  · rw [trailingCoeff_eq_coeff_zero h0] at htrail_eq
    exact nonempty_lazardDelineation_of_coeff_zero_ne_zero p hS hconn
      (leadingCoeff_ne_zero.2 hp) h0 hdiscr hlead_eq htrail_eq hdiscr_eq
  -- Otherwise `p = X * q`, where `X ∤ q` because the discriminant of `p` is nonzero.
  obtain ⟨q, rfl⟩ := X_dvd_iff.2 h0
  have hq : q ≠ 0 := right_ne_zero_of_mul hp
  have hq0 : q.coeff 0 ≠ 0 := by
    intro hq0
    obtain ⟨r, rfl⟩ := X_dvd_iff.2 hq0
    apply hdiscr
    rw [discr_X_mul _ (by rw [natDegree_X_mul (right_ne_zero_of_mul hq)]; omega)]
    simp
  rw [leadingCoeff_mul, leadingCoeff_X, one_mul] at hlead_eq
  have hX : (X : Polynomial (MvPolynomial (Fin n) ℝ)).trailingCoeff = 1 := by
    rw [trailingCoeff, natTrailingDegree_X, coeff_X_one]
  rw [trailingCoeff_mul, hX, one_mul, trailingCoeff_eq_coeff_zero hq0] at htrail_eq
  -- The discriminant of `q` divides that of `X * q`, with a cofactor of constant valuation.
  have hdq : q.discr ≠ 0 ∧ ∀ x ∈ S, ∀ y ∈ S,
      q.discr.lazardValuation x = q.discr.lazardValuation y := by
    rcases Nat.eq_zero_or_pos q.natDegree with hd | hd
    · rw [eq_C_of_natDegree_eq_zero hd, discr_C]
      exact ⟨one_ne_zero, fun _ _ _ _ ↦ by rw [lazardValuation_one, lazardValuation_one]⟩
    rw [discr_X_mul _ hd] at hdiscr hdiscr_eq
    refine ⟨left_ne_zero_of_mul hdiscr, fun x hx y hy ↦ ?_⟩
    have h := hdiscr_eq x hx y hy
    rw [lazardValuation_mul, lazardValuation_mul, lazardValuation_pow, lazardValuation_pow,
      htrail_eq x hx y hy, lazardValuation_eq_lazardExponent hq0 y, ← WithTop.coe_nsmul] at h
    exact WithTop.add_right_cancel WithTop.coe_ne_top h
  obtain ⟨D⟩ := nonempty_lazardDelineation_of_coeff_zero_ne_zero q hS hconn
    (leadingCoeff_ne_zero.2 hq) hq0 hdq.1 hlead_eq htrail_eq hdq.2
  exact TauCeti.nonempty_lazardDelineation_X_mul hq D hconn htrail_eq

end Polynomial

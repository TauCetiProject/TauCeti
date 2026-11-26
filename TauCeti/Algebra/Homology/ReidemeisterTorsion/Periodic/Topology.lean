/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.SquareMinor
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Field

/-!
# Continuity of the torsion of a based two-periodic complex

Consider based two-periodic complexes over a topological field `F`, complexes for the shape
`ComplexShape.up (ZMod 2)` with ordered bases of fixed dimensions `n 0` and `n 1`. If the matrices
of their two differentials converge, and a fixed square-minor splitting
(`HomologicalComplex.parityTorsionMinor`) is invertible in the limit, then the same splitting is
eventually invertible. Consequently the complexes are eventually acyclic
(`HomologicalComplex.eventually_acyclic_of_tendsto_parityTorsionMinor`) and their torsions
`HomologicalComplex.parityTorsion` converge to the limiting torsion
(`HomologicalComplex.tendsto_parityTorsion_of_det_parityTorsionMinor_ne_zero`): by the square-minor
formula, near the limit the torsion is the rational function `det (A₁) · det (A₀)⁻¹` of the
coefficients of the differentials. The bases and the underlying vector spaces may vary: only their
coordinate matrices enter the convergence hypotheses.

This is a local statement on a nonvanishing minor chart, not continuity of the torsion, which is
`0` on complexes that are not acyclic, across a loss of acyclicity. It applies to nonarchimedean
fields, such as the fields of Novikov series in which the torsions of Floer–Novikov complexes take
their values, as well as to real and complex fields; neither completeness nor a norm is needed.
It is the two-periodic counterpart of
`HomologicalComplex.tendsto_reidemeisterTorsion_of_det_torsionMinor_ne_zero` for bounded
`ℤ`-graded complexes; with only two degrees, no boundedness hypothesis is needed.

## Main results

* `HomologicalComplex.eventually_det_parityTorsionMinor_ne_zero`: nonvanishing of the limiting
  square minors persists.
* `HomologicalComplex.eventually_acyclic_of_tendsto_parityTorsionMinor`: the complexes are
  eventually acyclic.
* `HomologicalComplex.tendsto_parityTorsion_of_det_parityTorsionMinor_ne_zero`: the torsions
  converge.
* `HomologicalComplex.continuousAt_parityTorsion_of_det_parityTorsionMinor_ne_zero`: the torsion of
  a continuous family is continuous on a nonvanishing minor chart.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Lemma 2.8 (continuity through nonvanishing minors).
* V. Turaev, *Introduction to Combinatorial Torsions*, Chapter I, Section 2.
-/

public section

noncomputable section

open CategoryTheory Module Filter Topology

namespace HomologicalComplex

universe u

variable {F α : Type*} [Field F] [TopologicalSpace F] {n q p : ZMod 2 → ℕ}
  {C : α → HomologicalComplex (ModuleCat.{u} F) (ComplexShape.up (ZMod 2))}
  {C₀ : HomologicalComplex (ModuleCat.{u} F) (ComplexShape.up (ZMod 2))}
  {c : ∀ a i, Basis (Fin (n i)) F ((C a).X i)} {c₀ : ∀ i, Basis (Fin (n i)) F (C₀.X i)}
  {hn : ∀ i, n i = q i + p i} {hpq : ∀ i, p (i + 1) = q i} {l : Filter α}

/-- Entrywise convergence of the differentials implies convergence of each square minor.
No topology on the chain modules or on their varying bases is required. -/
theorem tendsto_parityTorsionMinor
    (hd : ∀ i r k, Tendsto
      (fun a ↦ LinearMap.toMatrix (c a (i + 1)) (c a i) ((C a).d (i + 1) i).hom r k)
      l (𝓝 (LinearMap.toMatrix (c₀ (i + 1)) (c₀ i) (C₀.d (i + 1) i).hom r k)))
    (i : ZMod 2) : Tendsto (fun a ↦ parityTorsionMinor (c a) hn hpq i) l
      (𝓝 (parityTorsionMinor c₀ hn hpq i)) := by
  refine tendsto_pi_nhds.2 fun r ↦ tendsto_pi_nhds.2 fun k ↦ ?_
  simp only [parityTorsionMinor_apply, LinearMap.toMatrix_apply] at hd ⊢
  exact hd i _ _

variable [IsTopologicalRing F]

/-- The determinant of each square minor converges with the differential matrices. -/
theorem tendsto_det_parityTorsionMinor
    (hd : ∀ i r k, Tendsto
      (fun a ↦ LinearMap.toMatrix (c a (i + 1)) (c a i) ((C a).d (i + 1) i).hom r k)
      l (𝓝 (LinearMap.toMatrix (c₀ (i + 1)) (c₀ i) (C₀.d (i + 1) i).hom r k)))
    (i : ZMod 2) : Tendsto (fun a ↦ (parityTorsionMinor (c a) hn hpq i).det) l
      (𝓝 (parityTorsionMinor c₀ hn hpq i).det) :=
  (continuous_id.matrix_det.tendsto _).comp
    (tendsto_parityTorsionMinor (hn := hn) (hpq := hpq) hd i)

variable [T1Space F]

/-- If both limiting square minors are invertible, then both square minors are eventually
invertible. -/
theorem eventually_det_parityTorsionMinor_ne_zero
    (hd : ∀ i r k, Tendsto
      (fun a ↦ LinearMap.toMatrix (c a (i + 1)) (c a i) ((C a).d (i + 1) i).hom r k)
      l (𝓝 (LinearMap.toMatrix (c₀ (i + 1)) (c₀ i) (C₀.d (i + 1) i).hom r k)))
    (hA : ∀ i, (parityTorsionMinor c₀ hn hpq i).det ≠ 0) :
    ∀ᶠ a in l, ∀ i, (parityTorsionMinor (c a) hn hpq i).det ≠ 0 :=
  eventually_all.2 fun i ↦ (tendsto_det_parityTorsionMinor hd i).eventually_ne (hA i)

/-- A family of based two-periodic complexes with a nonvanishing limiting square-minor chart is
eventually acyclic. -/
theorem eventually_acyclic_of_tendsto_parityTorsionMinor
    (hd : ∀ i r k, Tendsto
      (fun a ↦ LinearMap.toMatrix (c a (i + 1)) (c a i) ((C a).d (i + 1) i).hom r k)
      l (𝓝 (LinearMap.toMatrix (c₀ (i + 1)) (c₀ i) (C₀.d (i + 1) i).hom r k)))
    (hA : ∀ i, (parityTorsionMinor c₀ hn hpq i).det ≠ 0) :
    ∀ᶠ a in l, (C a).Acyclic :=
  (eventually_det_parityTorsionMinor_ne_zero hd hA).mono fun _ ha ↦
    acyclic_of_det_parityTorsionMinor_ne_zero ha

variable [ContinuousInv₀ F]

/-- The torsion of a based two-periodic complex converges with the matrices of its differentials
on a nonvanishing square-minor chart. The approximating complexes need not be assumed acyclic:
this follows eventually from the limiting minors. -/
theorem tendsto_parityTorsion_of_det_parityTorsionMinor_ne_zero
    (hd : ∀ i r k, Tendsto
      (fun a ↦ LinearMap.toMatrix (c a (i + 1)) (c a i) ((C a).d (i + 1) i).hom r k)
      l (𝓝 (LinearMap.toMatrix (c₀ (i + 1)) (c₀ i) (C₀.d (i + 1) i).hom r k)))
    (hA : ∀ i, (parityTorsionMinor c₀ hn hpq i).det ≠ 0) :
    Tendsto (fun a ↦ (C a).parityTorsion (c a)) l (𝓝 (C₀.parityTorsion c₀)) := by
  rw [parityTorsion_eq_det_parityTorsionMinor_mul_inv hA]
  refine ((tendsto_det_parityTorsionMinor hd 1).mul
    ((tendsto_det_parityTorsionMinor hd 0).inv₀ (hA 0))).congr' ?_
  filter_upwards [eventually_det_parityTorsionMinor_ne_zero hd hA] with a ha
  rw [parityTorsion_eq_det_parityTorsionMinor_mul_inv ha]

/-- For a family with continuous differential coefficients, the torsion of a based two-periodic
complex is continuous at any point where a fixed square-minor chart is nonvanishing. -/
theorem continuousAt_parityTorsion_of_det_parityTorsionMinor_ne_zero [TopologicalSpace α]
    (a₀ : α)
    (hd : ∀ i r k, ContinuousAt
      (fun a ↦ LinearMap.toMatrix (c a (i + 1)) (c a i) ((C a).d (i + 1) i).hom r k) a₀)
    (hA : ∀ i, (parityTorsionMinor (c a₀) hn hpq i).det ≠ 0) :
    ContinuousAt (fun a ↦ (C a).parityTorsion (c a)) a₀ :=
  tendsto_parityTorsion_of_det_parityTorsionMinor_ne_zero hd hA

end HomologicalComplex

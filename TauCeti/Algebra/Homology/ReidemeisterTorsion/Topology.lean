/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.SquareMinor
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Field

/-!
# Continuity of based Reidemeister torsion

Consider bounded based chain complexes over a topological field, with fixed dimensions in
each degree. If their differential matrices converge and a fixed square-minor splitting is
invertible in the limit, the same splitting is eventually invertible. Consequently the
complexes are eventually acyclic and their torsions converge to the limiting torsion.
The bases and the underlying vector spaces may vary: only their coordinate matrices enter
the convergence hypotheses.

This is a local statement on a nonvanishing minor chart, not continuity of zero-extended
torsion across a loss of acyclicity. It applies to nonarchimedean fields as well as to real
and complex fields; neither completeness nor a norm is needed.

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

variable {F α : Type*} [Field F] [TopologicalSpace F]
  {n q p : ℤ → ℕ}
  {C : α → ChainComplex (ModuleCat.{u} F) ℤ} {C₀ : ChainComplex (ModuleCat.{u} F) ℤ}
  {c : ∀ a i, Basis (Fin (n i)) F ((C a).X i)}
  {c₀ : ∀ i, Basis (Fin (n i)) F (C₀.X i)}
  {hn : ∀ i, n i = q i + p i} {hpq : ∀ j, p (j + 1) = q j} {l : Filter α}

/-- Entrywise convergence of the differentials implies convergence of each square minor.
No topology on the chain modules or on their varying bases is required. -/
theorem tendsto_torsionMinor
    (hd : ∀ j r k, Tendsto
      (fun a ↦ LinearMap.toMatrix (c a (j + 1)) (c a j) ((C a).d (j + 1) j).hom r k)
      l (𝓝 (LinearMap.toMatrix (c₀ (j + 1)) (c₀ j) (C₀.d (j + 1) j).hom r k)))
    (j : ℤ) : Tendsto (fun a ↦ torsionMinor (c a) hn hpq j) l
      (𝓝 (torsionMinor c₀ hn hpq j)) := by
  refine tendsto_pi_nhds.2 fun r ↦ tendsto_pi_nhds.2 fun k ↦ ?_
  simp only [torsionMinor_apply, LinearMap.toMatrix_apply] at hd ⊢
  exact hd j _ _

variable [IsTopologicalRing F]

/-- The determinant of each square minor converges with the differential matrices. -/
theorem tendsto_det_torsionMinor
    (hd : ∀ j r k, Tendsto
      (fun a ↦ LinearMap.toMatrix (c a (j + 1)) (c a j) ((C a).d (j + 1) j).hom r k)
      l (𝓝 (LinearMap.toMatrix (c₀ (j + 1)) (c₀ j) (C₀.d (j + 1) j).hom r k)))
    (j : ℤ) : Tendsto (fun a ↦ (torsionMinor (c a) hn hpq j).det) l
      (𝓝 (torsionMinor c₀ hn hpq j).det) :=
  (continuous_id.matrix_det.tendsto _).comp (tendsto_torsionMinor (hn := hn) (hpq := hpq) hd j)

variable [T1Space F]

/-- In a uniformly bounded family, nonvanishing of all limiting square minors persists
simultaneously. Finiteness of the degree support is essential here. -/
theorem eventually_det_torsionMinor_ne_zero
    (hfin : {i | n i ≠ 0}.Finite)
    (hd : ∀ j r k, Tendsto
      (fun a ↦ LinearMap.toMatrix (c a (j + 1)) (c a j) ((C a).d (j + 1) j).hom r k)
      l (𝓝 (LinearMap.toMatrix (c₀ (j + 1)) (c₀ j) (C₀.d (j + 1) j).hom r k)))
    (hA : ∀ j, (torsionMinor c₀ hn hpq j).det ≠ 0) :
    ∀ᶠ a in l, ∀ j, (torsionMinor (c a) hn hpq j).det ≠ 0 := by
  classical
  have he := hfin.eventually_all.2 fun j _ ↦
    (tendsto_det_torsionMinor hd j).eventually_ne (hA j)
  filter_upwards [he] with a ha j
  by_cases hj : n j = 0
  · have hq : q j = 0 := by have := hn j; omega
    have : IsEmpty (Fin (q j)) := by rw [hq]; infer_instance
    simp
  · exact ha j hj

/-- A bounded family with a nonvanishing limiting square-minor chart is eventually acyclic. -/
theorem eventually_acyclic_of_tendsto_torsionMinor
    (hfin : {i | n i ≠ 0}.Finite)
    (hd : ∀ j r k, Tendsto
      (fun a ↦ LinearMap.toMatrix (c a (j + 1)) (c a j) ((C a).d (j + 1) j).hom r k)
      l (𝓝 (LinearMap.toMatrix (c₀ (j + 1)) (c₀ j) (C₀.d (j + 1) j).hom r k)))
    (hA : ∀ j, (torsionMinor c₀ hn hpq j).det ≠ 0) :
    ∀ᶠ a in l, (C a).Acyclic :=
  (eventually_det_torsionMinor_ne_zero hfin hd hA).mono fun _ ha ↦
    acyclic_of_det_torsionMinor_ne_zero ha

variable [ContinuousInv₀ F]

/-- Torsion converges with the differential matrices on a nonvanishing square-minor chart.
The approximating complexes need not be assumed acyclic: this follows eventually from the
limiting minors. Negative powers of determinants use inversion only at nonzero elements. -/
theorem tendsto_reidemeisterTorsion_of_det_torsionMinor_ne_zero
    (hfin : {i | n i ≠ 0}.Finite)
    (hd : ∀ j r k, Tendsto
      (fun a ↦ LinearMap.toMatrix (c a (j + 1)) (c a j) ((C a).d (j + 1) j).hom r k)
      l (𝓝 (LinearMap.toMatrix (c₀ (j + 1)) (c₀ j) (C₀.d (j + 1) j).hom r k)))
    (hA : ∀ j, (torsionMinor c₀ hn hpq j).det ≠ 0) :
    Tendsto (fun a ↦ (C a).reidemeisterTorsion (c a)) l
      (𝓝 (C₀.reidemeisterTorsion c₀)) := by
  classical
  -- Outside the fixed degree support the minors are empty, so their determinants are one.
  have hprod (D : ChainComplex (ModuleCat.{u} F) ℤ)
      (b : ∀ i, Basis (Fin (n i)) F (D.X i)) :
      (∏ᶠ j : ℤ, (torsionMinor b hn hpq j).det ^ ((j + 1).negOnePow : ℤ)) =
        ∏ j ∈ hfin.toFinset, (torsionMinor b hn hpq j).det ^ ((j + 1).negOnePow : ℤ) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro j hj
    by_contra h
    have hnj : n j = 0 := by simpa using h
    have hq : q j = 0 := by have := hn j; omega
    have : IsEmpty (Fin (q j)) := by rw [hq]; infer_instance
    exact hj (by simp)
  rw [reidemeisterTorsion_eq_finprod_det_torsionMinor hA hfin, hprod]
  have ht := tendsto_finsetProd hfin.toFinset fun j _ ↦
    (tendsto_det_torsionMinor hd j).zpow₀ ((j + 1).negOnePow : ℤ) (Or.inl (hA j))
  apply ht.congr'
  filter_upwards [eventually_det_torsionMinor_ne_zero hfin hd hA] with a ha
  rw [reidemeisterTorsion_eq_finprod_det_torsionMinor ha hfin, hprod (C a) (c a)]

/-- For a family with continuous differential coefficients, based torsion is continuous at
any point where a fixed square-minor chart is nonvanishing. -/
theorem continuousAt_reidemeisterTorsion_of_det_torsionMinor_ne_zero
    [TopologicalSpace α] (a₀ : α)
    (hfin : {i | n i ≠ 0}.Finite)
    (hd : ∀ j r k, ContinuousAt
      (fun a ↦ LinearMap.toMatrix (c a (j + 1)) (c a j) ((C a).d (j + 1) j).hom r k) a₀)
    (hA : ∀ j, (torsionMinor (c a₀) hn hpq j).det ≠ 0) :
    ContinuousAt (fun a ↦ (C a).reidemeisterTorsion (c a)) a₀ :=
  tendsto_reidemeisterTorsion_of_det_torsionMinor_ne_zero hfin hd hA

end HomologicalComplex

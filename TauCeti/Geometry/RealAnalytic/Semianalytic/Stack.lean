/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAnalytic.Semianalytic.PartiallySemialgebraic.SharedRoots
public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation
public import TauCeti.Geometry.RealAlgebraic.Stack.RootCount

/-!
# Semianalyticity of analytic-coefficient delineations

A delineation of a finite polynomial family over a semianalytic base has semianalytic
sections and sectors if the coefficients are analytic and the degrees are locally bounded
in ambient neighborhoods. No closure under differentiation, squarefreeness, or nonvanishing
assumption on the family is needed. Repeated and shared roots are counted once; nullified
members contribute no roots. Empty bases and empty families are included.

The ambient-neighborhood requirement includes all points of the closure of the base:
intrinsic analyticity on the base alone would not ensure semianalyticity at frontier points.
The description of each cell is its shared-root rank formula intersected with the cylinder over
the base. This gives the semianalyticity of root graphs and intervening bands used in local analytic
sign decompositions, independently of how the delineation was constructed.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore
di Pisa (3) 18 (1964), 449–474, §1 (semianalytic sections and sectors).
S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapters 10 and 11 (uniform shared-root descriptions).
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti.Delineation

variable {n : ℕ} {κ : Type*} [Finite κ] {S : Set (Fin n → ℝ)}
  {F : κ → (Fin n → ℝ) → ℝ[X]} (D : Delineation fun k (x : S) ↦ F k x)

/-- A section of a delineation is semianalytic at every height over a point where its base is
semianalytic and its polynomial family has analytic coefficients of locally bounded degree.
The coefficient assumptions hold in an ambient neighborhood, not merely on the base. -/
theorem semianalyticAt_image_cylinder_sectionSet {y : Fin (n + 1) → ℝ}
    (hS : SemianalyticAt S (Fin.tail y)) {d : κ → ℕ}
    (hF : ∀ k j, j ≤ d k → AnalyticAt ℝ (fun x ↦ (F k x).coeff j) (Fin.tail y))
    (hdeg : ∀ k, ∀ᶠ x in 𝓝 (Fin.tail y), (F k x).natDegree ≤ d k) (i : Fin D.count) :
    SemianalyticAt (cylinder S '' sectionSet D.root i) y := by
  classical
  cases nonempty_fintype κ
  have h := hS.partiallySemialgebraicAt_preimage_fst.inter
    (partiallySemialgebraicAt_setOf_mem_biUnion_roots_card_lt hF hdeg i.val)
  have ha : AnalyticAt ℝ
      (fun v : Fin (n + 1) → ℝ ↦ (Fin.tail v, fun _ : Unit ↦ v 0)) y :=
    (AnalyticAt.pi fun j : Fin n ↦
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) ↦ ℝ) j.succ).analyticAt y).prod
      (AnalyticAt.pi fun _ : Unit ↦
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) ↦ ℝ) 0).analyticAt y)
  convert (h.semianalyticAt (fun _ ↦ y 0)).preimage
    (g := fun v : Fin (n + 1) → ℝ ↦ (Fin.tail v, fun _ : Unit ↦ v 0)) (x := y) ha using 2
  ext v
  simp only [mem_image_cylinder, mem_preimage, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hv, hi⟩
    refine ⟨hv, ?_⟩
    rw [D.biUnion_roots_toFinset_eq ⟨Fin.tail v, hv⟩]
    exact (mem_sectionSet_iff_mem_image_card_lt i _ (D.strictMono_root _)).1 hi
  · rintro ⟨hv, hi⟩
    refine ⟨hv, ?_⟩
    rw [D.biUnion_roots_toFinset_eq ⟨Fin.tail v, hv⟩] at hi
    exact (mem_sectionSet_iff_mem_image_card_lt i _ (D.strictMono_root _)).2 hi

/-- A sector of a delineation is semianalytic at every height over a point with a semianalytic
base and analytic coefficients of locally bounded degree in an ambient neighborhood.
This includes the two unbounded sectors and the whole cylinder when there are no sections. -/
theorem semianalyticAt_image_cylinder_sectorSet {y : Fin (n + 1) → ℝ}
    (hS : SemianalyticAt S (Fin.tail y)) {d : κ → ℕ}
    (hF : ∀ k j, j ≤ d k → AnalyticAt ℝ (fun x ↦ (F k x).coeff j) (Fin.tail y))
    (hdeg : ∀ k, ∀ᶠ x in 𝓝 (Fin.tail y), (F k x).natDegree ≤ d k)
    (i : Fin (D.count + 1)) :
    SemianalyticAt (cylinder S '' sectorSet D.root i) y := by
  classical
  cases nonempty_fintype κ
  have h := hS.partiallySemialgebraicAt_preimage_fst.inter
    (partiallySemialgebraicAt_setOf_notMem_biUnion_roots_card_lt hF hdeg i.val)
  have ha : AnalyticAt ℝ
      (fun v : Fin (n + 1) → ℝ ↦ (Fin.tail v, fun _ : Unit ↦ v 0)) y :=
    (AnalyticAt.pi fun j : Fin n ↦
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) ↦ ℝ) j.succ).analyticAt y).prod
      (AnalyticAt.pi fun _ : Unit ↦
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) ↦ ℝ) 0).analyticAt y)
  convert (h.semianalyticAt (fun _ ↦ y 0)).preimage
    (g := fun v : Fin (n + 1) → ℝ ↦ (Fin.tail v, fun _ : Unit ↦ v 0)) (x := y) ha using 2
  ext v
  simp only [mem_image_cylinder, mem_preimage, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hv, hi⟩
    refine ⟨hv, ?_⟩
    rw [D.biUnion_roots_toFinset_eq ⟨Fin.tail v, hv⟩]
    exact (mem_sectorSet_iff_notMem_image_card_lt i _ (D.strictMono_root _)).1 hi
  · rintro ⟨hv, hi⟩
    refine ⟨hv, ?_⟩
    rw [D.biUnion_roots_toFinset_eq ⟨Fin.tail v, hv⟩] at hi
    exact (mem_sectorSet_iff_notMem_image_card_lt i _ (D.strictMono_root _)).2 hi

/-- All cells of an analytic-coefficient delineation over a semianalytic base are semianalytic.
Ambient analytic descriptions are needed only along the closure of the base. The local degree
bounds may depend on the base point and on the family member. -/
theorem isSemianalytic_of_mem_stackCells (hS : IsSemianalytic S)
    (hF : ∀ x ∈ closure S, ∃ d : κ → ℕ,
      (∀ k j, j ≤ d k → AnalyticAt ℝ (fun z ↦ (F k z).coeff j) x) ∧
      ∀ k, ∀ᶠ z in 𝓝 x, (F k z).natDegree ≤ d k)
    {T : Set (Fin (n + 1) → ℝ)} (hT : T ∈ stackCells S D.root) : IsSemianalytic T := by
  rw [isSemianalytic_iff]
  intro y
  by_cases hy : Fin.tail y ∈ closure S
  · obtain ⟨d, hcoeff, hdeg⟩ := hF (Fin.tail y) hy
    rcases mem_stackCells.mp hT with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact D.semianalyticAt_image_cylinder_sectionSet (hS.semianalyticAt _) hcoeff hdeg i
    · exact D.semianalyticAt_image_cylinder_sectorSet (hS.semianalyticAt _) hcoeff hdeg i
  · -- Away from the closure of the base every cell is locally empty.
    apply (semianalyticAt_empty (x := y)).congr
    have htail : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) := by fun_prop
    filter_upwards [htail.continuousAt.preimage_mem_nhds
      (isClosed_closure.isOpen_compl.mem_nhds hy)] with z hz
    simp only [mem_empty_iff_false, eq_iff_iff, false_iff]
    intro hzT
    have hzS : Fin.tail z ∈ S := by
      rw [← image_tail_of_mem_stackCells D.strictMono_root hT]
      exact mem_image_of_mem Fin.tail hzT
    exact hz (subset_closure hzS)

end TauCeti.Delineation

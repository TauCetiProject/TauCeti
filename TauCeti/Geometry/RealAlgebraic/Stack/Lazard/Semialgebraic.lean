/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Basic
public import TauCeti.Geometry.RealAlgebraic.CAD.Basic
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.SharedRoots
import TauCeti.FieldTheory.IsRealClosed.Real

/-!
# Semialgebraicity of Lazard stacks

Every Lazard delineation of a real polynomial family over a semialgebraic base
has semialgebraic sections and sectors. Its fixed removed base exponents express the Lazard
evaluations as specializations of polynomial families. Choose one witnessing member for each
section to obtain a finite family with exactly the same shared roots. The uniform descriptions
of shared ordered roots then describe each cell by its root membership and the number of roots
below it.

Ordinary fibers may be nullified, and the degrees of the Lazard evaluations need not be
constant. Neither connectedness nor an analytic submanifold hypothesis is needed here.
This supplies the semialgebraic cells required when lifting a cylindrical decomposition
using Lazard evaluations rather than ordinary specialization.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, Sections 2 and 5.
S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapters 10–11 (uniform sign descriptions of ordered roots).
-/

public section

open Function MvPolynomial Polynomial Set

namespace TauCeti.LazardDelineation

variable {ι : Type*} {n : ℕ} {F : ι → MvPolynomial (Fin (n + 1)) ℝ}
  {S : Set (Fin n → ℝ)}

-- A single polynomial family represents the evaluations on the fixed-exponent stratum.
private theorem exists_polynomial_shared_roots (D : LazardDelineation F S) :
    ∃ G : Finset (MvPolynomial (Fin n) ℝ)[X], ∀ x : S,
      (G.biUnion fun p ↦ (p.map (MvPolynomial.eval x.1)).roots.toFinset) =
        Finset.univ.image (fun i ↦ D.root i x) := by
  classical
  choose k hk using D.exists_multiplicity_pos
  let L (k : ι) (α : Fin n → ℝ) :=
    (optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardEval
      (Polynomial.C ∘ α)
  choose P hP using fun i ↦ (F (k i)).exists_polynomial_map_eq_lazardEval (D.exponent (k i))
  have hPL (i : Fin D.count) (x : S) :
      (P i).map (MvPolynomial.eval x.1) = L (k i) x.1 :=
    hP i x.1 (D.lazardExponent_eq (k i) x)
  let G := Finset.univ.image P
  -- The finite shared root set is exactly the increasing list of the Lazard delineation.
  refine ⟨G, fun x ↦ ?_⟩
  ext t
  simp only [G, Finset.image_biUnion, hPL, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_image, Multiset.mem_toFinset,
    Polynomial.mem_roots']
  constructor
  · rintro ⟨i, hi, ht⟩
    have hkF : F (k i) ≠ 0 := by
      rintro h
      simp [L, h] at hi
    exact D.exists_root_eq (k i) x hkF t ht
  · rintro ⟨i, rfl⟩
    exact ⟨i, Polynomial.rootMultiplicity_pos'.1
      (by rw [D.rootMultiplicity_root (k i) i x]; exact hk i)⟩

/-- A Lazard delineation over a semialgebraic base is a semialgebraic
stack, even where the ordinary fibers are nullified. Repeated and shared roots are counted
once, and zero members and an empty root list are allowed. The input family may be infinite:
one witnessing member per section suffices to describe the cells. -/
theorem isSemialgebraicStack (D : LazardDelineation F S)
    (hS : IsSemialgebraic S) : IsSemialgebraicStack S D.root := by
  classical
  obtain ⟨G, hG⟩ := exists_polynomial_shared_roots D
  let Z (x : S) := G.biUnion fun p ↦ (p.map (MvPolynomial.eval x.1)).roots.toFinset
  have hZ (x : S) : Z x = Finset.univ.image (fun i ↦ D.root i x) := hG x
  have hcard (x : S) (t : ℝ) :
      (Z x |>.filter (· < t)).card = (Finset.univ.filter (fun i ↦ D.root i x < t)).card := by
    rw [hZ, Finset.filter_image]
    exact Finset.card_image_of_injective _ (D.strictMono_root x).injective
  -- At a root, its rank is its index in the ordered list.
  have hsection (x : S) (t : ℝ) (i : Fin D.count) :
      D.root i x = t ↔ t ∈ Z x ∧ (Z x |>.filter (· < t)).card = i.val := by
    have hrank (j : Fin D.count) :
        (Z x |>.filter (· < D.root j x)).card = j.val := by
      rw [hcard]
      simpa only [(D.strictMono_root x).lt_iff_lt, Finset.filter_gt_eq_Iio] using Fin.card_Iio j
    constructor
    · rintro rfl
      exact ⟨by rw [hZ]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i), hrank i⟩
    · rintro ⟨ht, hc⟩
      rw [hZ] at ht
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 ht
      have hij : j = i := Fin.ext ((hrank j).symm.trans hc)
      rw [hij]
  -- Away from all roots, the number below the point identifies its sector.
  have hsector (x : S) (t : ℝ) (j : Fin (D.count + 1)) :
      (x, t) ∈ sectorSet D.root j ↔
        t ∉ Z x ∧ (Z x |>.filter (· < t)).card = j.val := by
    have hless (i : Fin D.count) :
        i.val < (Z x |>.filter (· < t)).card ↔ D.root i x < t := by
      rw [hcard]
      exact Fin.lt_card_filter_univ_iff_apply_of_imp _
        (fun a b hab ha ↦ ((D.strictMono_root x).monotone hab).trans_lt ha)
    constructor
    · intro ht
      have hnot : t ∉ Z x := by
        rw [hZ]
        rintro h
        obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h
        exact disjoint_left.1 (disjoint_sectionSet_sectorSet D.root i j)
          (mem_sectionSet.2 hi) ht
      refine ⟨hnot, ?_⟩
      rw [hcard]
      have heq : Finset.univ.filter (fun i ↦ D.root i x < t) =
          Finset.univ.filter (fun i : Fin D.count ↦ i.val < j.val) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun hi ↦ by
          by_contra h
          exact hi.not_gt ((mem_sectorSet.1 ht).2 i
            (by simpa only [Fin.le_def, Fin.val_castSucc] using le_of_not_gt h)),
          fun hi ↦ (mem_sectorSet.1 ht).1 i (by simpa only [Fin.lt_def, Fin.val_castSucc] using hi)⟩
      rw [heq, Fin.card_filter_val_lt, min_eq_right (by omega)]
    · rintro ⟨hnot, hc⟩
      rw [mem_sectorSet]
      constructor
      · intro i hi
        exact (hless i).1 (by simpa only [hc, Fin.lt_def, Fin.val_castSucc] using hi)
      · intro i hi
        have hne : D.root i x ≠ t := by
          intro h
          apply hnot
          rw [hZ, ← h]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
        exact lt_of_le_of_ne (le_of_not_gt fun h ↦
          (not_lt_of_ge hi)
            (by simpa only [hc, Fin.lt_def, Fin.val_castSucc] using (hless i).2 h)) hne.symm
  refine ⟨D.continuous_root, D.strictMono_root, fun i ↦ ?_, fun j ↦ ?_⟩
  · convert hS.preimage_tail.inter
      (G.isSemialgebraic_setOf_mem_biUnion_roots_card_lt i.val) using 1
    ext y
    simp only [mem_image_cylinder, mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_sectionSet]
    simpa only [Z, exists_prop] using
      (exists_congr fun hy ↦ hsection ⟨Fin.tail y, hy⟩ (y 0) i)
  · convert hS.preimage_tail.inter
      (G.isSemialgebraic_setOf_notMem_biUnion_roots_card_lt j.val) using 1
    ext y
    simp only [mem_image_cylinder, mem_inter_iff, mem_preimage, mem_ofPred_eq]
    simpa only [Z, exists_prop] using
      (exists_congr fun hy ↦ hsector ⟨Fin.tail y, hy⟩ (y 0) j)

end TauCeti.LazardDelineation

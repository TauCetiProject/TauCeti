/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Strip.Independence
import TauCeti.Probability.Independence.Conditional

/-!
# Conditional independence of visible array cells

For a separately exchangeable array, all cells whose row and column are outside two infinite
hidden index sets are conditionally independent given the crossing strips. This is the
simultaneous form of the local finite-block independence theorem and supplies the cell-noise
factorization in the Aldous--Hoover representation.

The statement uses Mathlib's conditional independence of an indexed family, so it controls every
finite collection of distinct visible cells at once.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
  {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]

/-- The visible cells are conditionally independent given all entries on the crossing hidden
strips. In particular this controls any finite set of distinct visible cells, not only
rectangular blocks. -/
theorem SeparatelyExchangeable.iCondIndepFun_visibleCells
    (hρ : SeparatelyExchangeable ρ fun p x => x p)
    {S T : Set ℕ} (hS : S.Infinite) (hT : T.Infinite) :
    let H : Set (ℕ × ℕ) := (Set.univ ×ˢ T) ∪ (S ×ˢ Set.univ)
    let V : Set (ℕ × ℕ) := Sᶜ ×ˢ Tᶜ
    iCondIndepFun (MeasurableSpace.comap H.domRestrict inferInstance)
      (Set.measurable_restrict H).comap_le
      (fun p : V => fun x : ℕ × ℕ → α => x p.1) ρ := by
  dsimp
  let H : Set (ℕ × ℕ) := (Set.univ ×ˢ T) ∪ (S ×ˢ Set.univ)
  let V : Set (ℕ × ℕ) := Sᶜ ×ˢ Tᶜ
  let Z : (ℕ × ℕ → α) → H → α := H.domRestrict
  let m' : MeasurableSpace (ℕ × ℕ → α) :=
    MeasurableSpace.comap Z (inferInstanceAs (MeasurableSpace (H → α)))
  let m : V → MeasurableSpace (ℕ × ℕ → α) :=
    fun p => MeasurableSpace.comap (fun x => x p.1)
      (inferInstanceAs (MeasurableSpace α))
  have hm' : m' ≤ (MeasurableSpace.pi : MeasurableSpace (ℕ × ℕ → α)) := by
    simpa only [m', Z] using
      (Set.measurable_restrict (X := fun _ : ℕ × ℕ => α) H).comap_le
  have hm (p : V) : m p ≤ (MeasurableSpace.pi : MeasurableSpace (ℕ × ℕ → α)) :=
    (measurable_pi_apply (X := fun _ : ℕ × ℕ => α) p.1).comap_le
  apply (iCondIndepFun_iff_iCondIndep (mΩ := MeasurableSpace.pi)
    m' hm' (fun _ : V => inferInstance)
    (fun p : V => fun x : ℕ × ℕ → α => x p.1) ρ).2
  apply iCondIndep_of_condIndep_compl (mΩ := MeasurableSpace.pi) hm' hm
  intro p
  let C : Set (ℕ × ℕ) := ({p.1.1} : Set ℕ) ×ˢ ({p.1.2} : Set ℕ)
  have hC : C = {p.1} := by ext q; simp [C, Prod.ext_iff]
  have hIS : Disjoint ({p.1.1} : Set ℕ) S :=
    Set.disjoint_singleton_left.mpr p.2.1
  have hJT : Disjoint ({p.1.2} : Set ℕ) T :=
    Set.disjoint_singleton_left.mpr p.2.2
  have hlocal := hρ.condIndepFun_visibleBlock_compl hS hT
    (Set.finite_singleton _) (Set.finite_singleton _) hIS hJT
  have hbase : CondIndep m'
      (MeasurableSpace.comap C.domRestrict inferInstance)
      (MeasurableSpace.comap Cᶜ.domRestrict inferInstance) hm' ρ := by
    exact (condIndepFun_iff_condIndep m' hm' C.domRestrict Cᶜ.domRestrict ρ).1 hlocal
  have hcoord (D : Set (ℕ × ℕ)) (r : D) :
      MeasurableSpace.comap (fun x : ℕ × ℕ → α => x r.1) inferInstance ≤
        MeasurableSpace.comap D.domRestrict inferInstance := by
    let F : (D → α) → α := fun y => y r
    have hF : Measurable F := measurable_pi_apply _
    have heq : (fun x : ℕ × ℕ → α => x r.1) = F ∘ D.domRestrict := by
      funext x
      simp only [Function.comp_apply, F, Set.domRestrict_apply]
    rw [heq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hF.comap_le
  have hleft : m p ≤ MeasurableSpace.comap C.domRestrict inferInstance := by
    simpa only [m] using hcoord C ⟨p.1, by simp [hC]⟩
  have hright : (⨆ q : {q : V // q ≠ p}, m q.1) ≤
      MeasurableSpace.comap Cᶜ.domRestrict inferInstance := by
    refine iSup_le fun q => ?_
    have hq : q.1.1 ∈ Cᶜ := by
      simp only [hC, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun heq => q.2 (Subtype.ext heq)
    simpa only [m] using hcoord Cᶜ ⟨q.1.1, hq⟩
  exact condIndep_of_condIndep_of_le_right
    (condIndep_of_condIndep_of_le_left hbase hleft) hright

end TauCeti.Probability

end

end

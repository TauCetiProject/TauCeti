/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Pi
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.RepresentationNumber

/-!
# The first shell of an orthogonal sum

If every nonzero vector in every summand has norm at least `r > 0`, a vector of norm `r`
in the orthogonal sum is supported in exactly one summand. Consequently the number of such
vectors is the sum of the representation numbers of the summands. In particular this counts
roots in orthogonal sums of positive definite even lattices.
-/

public section

namespace TauCeti.IntegralLattice

universe u v

variable {ι : Type v} [Fintype ι] {V : ι → Type u} [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℚ (V i)] (L : ∀ i, IntegralLattice (V i))

/-- If every nonzero vector of every summand has norm at least `r > 0`, then every vector
of norm `r` in the orthogonal sum lies in a single summand, where it has norm `r`. -/
theorem exists_eq_single_of_norm_pi_eq [DecidableEq ι] {r : ℚ} (hr : 0 < r)
    (hmin : ∀ i (x : L i), x ≠ 0 → r ≤ (L i).norm x)
    (x : pi L) (hx : (pi L).norm x = r) :
    ∃ i, ∃ y : L i, (L i).norm y = r ∧ (x : ∀ i, V i) = Pi.single i (y : V i) := by
  let y : ∀ i, L i := fun i ↦ ⟨x.val i, (mem_pi_carrier_iff L x).mp x.property i⟩
  have hnonneg (i : ι) : 0 ≤ (L i).norm (y i) := by
    by_cases h : y i = 0
    · simp [h]
    · exact hr.le.trans (hmin i (y i) h)
  have hsum : ∑ i, (L i).norm (y i) = r := (norm_pi_apply L x).symm.trans hx
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra! h
    have : r = 0 := by simpa [h] using hsum.symm
    exact hr.ne' this
  have hle := Finset.single_le_sum (fun j _ ↦ hnonneg j) (Finset.mem_univ i)
  have hnorm : (L i).norm (y i) = r := le_antisymm (hsum ▸ hle) (hmin i (y i) hi)
  have hzero (j : ι) (hji : j ≠ i) : y j = 0 := by
    by_contra hj
    have hpair := Finset.sum_le_sum_of_subset_of_nonneg
      (by simp : ({i, j} : Finset ι) ⊆ Finset.univ)
      (fun k _ _ ↦ hnonneg k)
    rw [Finset.sum_pair hji.symm, hsum, hnorm] at hpair
    have := hmin j (y j) hj
    linarith
  refine ⟨i, y i, hnorm, ?_⟩
  funext j
  by_cases hji : j = i
  · subst j; simp [y]
  · simpa [y, Pi.single_eq_of_ne hji] using congrArg Subtype.val (hzero j hji)

/-- The shell at a common positive lower bound for nonzero norms is the disjoint union of
the corresponding shells of the summands. -/
noncomputable def sigmaVectorsOfNormEquiv [DecidableEq ι] {r : ℚ} (hr : 0 < r)
    (hmin : ∀ i (x : L i), x ≠ 0 → r ≤ (L i).norm x) :
    (Σ i, (L i).vectorsOfNorm r) ≃ (pi L).vectorsOfNorm r := by
  let f : (Σ i, (L i).vectorsOfNorm r) → (pi L).vectorsOfNorm r := fun z ↦
    ⟨⟨Pi.single z.1 (z.2.val : V z.1), single_mem_pi_carrier L z.1 z.2.val.property⟩,
      mem_vectorsOfNorm.mpr ((norm_pi_single L z.1 _).trans (mem_vectorsOfNorm.mp z.2.property))⟩
  classical
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    have heq : Pi.single i (x.val : V i) = Pi.single j (y.val : V j) :=
      congrArg (fun z : (pi L).vectorsOfNorm r ↦ (z.val : ∀ i, V i)) h
    have hij : i = j := by
      by_contra hij
      have hx0 : (x.val : V i) = 0 := by simpa [hij] using congrFun heq i
      have := mem_vectorsOfNorm.mp x.property
      rw [hx0, map_zero] at this
      exact hr.ne this
    subst j
    have hxy : x = y := Subtype.ext (Subtype.ext (by simpa using congrFun heq i))
    subst y
    rfl
  · intro x
    obtain ⟨i, y, hy, hxy⟩ := exists_eq_single_of_norm_pi_eq L hr hmin x.val
      (mem_vectorsOfNorm.mp x.property)
    exact ⟨⟨i, ⟨y, mem_vectorsOfNorm.mpr hy⟩⟩, Subtype.ext (Subtype.ext hxy.symm)⟩

/-- The shell equivalence embeds a vector in its own summand. -/
@[simp]
theorem coe_sigmaVectorsOfNormEquiv_apply [DecidableEq ι] {r : ℚ} (hr : 0 < r)
    (hmin : ∀ i (x : L i), x ≠ 0 → r ≤ (L i).norm x)
    (x : Σ i, (L i).vectorsOfNorm r) :
    ((sigmaVectorsOfNormEquiv L hr hmin x).val : ∀ i, V i) =
      Pi.single x.1 (x.2.val : V x.1) := by
  classical
  rfl

/-- Representation numbers at a common positive lower bound add under finite orthogonal
sums, provided the summands' shells are finite. -/
theorem representationNumber_pi_of_le_norm {r : ℚ} (hr : 0 < r)
    (hmin : ∀ i (x : L i), x ≠ 0 → r ≤ (L i).norm x)
    (hfin : ∀ i, ((L i).vectorsOfNorm r).Finite) :
    (pi L).representationNumber r = ∑ i, (L i).representationNumber r := by
  classical
  have (i : ι) : Finite ((L i).vectorsOfNorm r) := (hfin i).to_subtype
  simpa only [representationNumber_def, Nat.card_coe_set_eq] using
    (Nat.card_congr (sigmaVectorsOfNormEquiv L hr hmin).symm).trans Nat.card_sigma

end TauCeti.IntegralLattice

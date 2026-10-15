/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.AldousHoover.Basic

/-!
# Assembling directed joint Aldous--Hoover codings

A jointly exchangeable directed array uses one cell variable for each *unordered* pair of
vertices.  A conditional cell coder naturally returns both directed entries at once.  This file
provides the deterministic bridge from that pair-valued coder to the scalar function used by
`AldousHoover.jointArray`.

Independent continuous vertex variables orient each off-diagonal pair: the smaller variable is
fed to the pair coder first, and reversing the two vertices reads the other component of the same
output.  The diagonal is supplied separately.  Thus a single scalar function simultaneously
produces

```text
X i i = d(U, U_i),
U_i < U_j  →  (X i j, X j i) = g(U, U_i, U_j, U_{\{i,j\}}),
U_j < U_i  →  (X j i, X i j) = g(U, U_j, U_i, U_{\{i,j\}}).
```

away from the null event `U_i = U_j`.  The characteristic lemmas below are pointwise and keep
that exceptional case explicit.  The accompanying almost-everywhere result proves that independent
continuous vertex marks avoid the exceptional case simultaneously for every pair of vertices.

## Main definitions

* `TauCeti.Probability.AldousHoover.orientPairCoding` canonically orients a pair-valued coder;
* `TauCeti.Probability.AldousHoover.assembleJointCoding` adds the diagonal and returns the scalar
  coding function used by `jointArray`.

## Main results

* `TauCeti.Probability.AldousHoover.ae_injective_vertexNoise` shows that the vertex coordinates of
  the canonical joint noise are almost surely pairwise distinct;
* `TauCeti.Probability.AldousHoover.assembleJointCoding_pair` shows that opposite directed entries
  read the two components of one oriented pair output.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.

No material is adapted from `cameronfreer/exchangeability`, which treats sequences rather than
exchangeable arrays.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti.Probability.AldousHoover

/-- Distinct vertices have distinct continuous marks almost surely under the canonical joint
Aldous--Hoover noise. -/
theorem ae_vertexNoise_ne_of_ne {i j : ℕ} (hij : i ≠ j) :
    ∀ᵐ u ∂noiseMeasure Unit (Sym2 ℕ), u (.vertex () i) ≠ u (.vertex () j) := by
  have hindex : (NoiseIndex.vertex () i : NoiseIndex Unit (Sym2 ℕ)) ≠ .vertex () j := by
    simpa using hij
  have hindep := (iIndepFun_eval_noiseMeasure Unit (Sym2 ℕ)).indepFun hindex
  have hpair : Measurable fun u : NoiseIndex Unit (Sym2 ℕ) → I =>
      (u (.vertex () i), u (.vertex () j)) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hmap := hindep.map_prod_eq_prod_map_map
    (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable
  simp only [map_eval_noiseMeasure] at hmap
  have hne : ∀ᵐ p ∂(volume : Measure I).prod volume, p.1 ≠ p.2 := by
    refine (Measure.ae_prod_iff_ae_ae ?_).2 ?_
    · exact (measurableSet_eq_fun measurable_fst measurable_snd).compl
    exact Filter.Eventually.of_forall fun a =>
      ((volume : Measure I).ae_ne a).mono fun b hba hab => hba hab.symm
  rw [← hmap] at hne
  exact (ae_map_iff hpair.aemeasurable
    (measurableSet_eq_fun measurable_fst measurable_snd).compl).1 hne

/-- Almost every canonical joint-noise sample assigns pairwise distinct marks to the countable
vertex family. -/
theorem ae_injective_vertexNoise :
    ∀ᵐ u ∂noiseMeasure Unit (Sym2 ℕ), Function.Injective fun i => u (.vertex () i) := by
  refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ _ => hij
  · exact (ae_vertexNoise_ne_of_ne hij).mono fun _ hne heq => (hne heq).elim

variable {α : Type*} [MeasurableSpace α]

/-- Orient a pair-valued cell coder by its two continuous vertex marks.  The output is ordered in
the same way as the input marks: when they arrive in decreasing order, both the inputs and the two
output coordinates are swapped. -/
def orientPairCoding (g : I → I → I → I → α × α) (z a b t : I) : α × α :=
  if a ≤ b then g z a b t else (g z b a t).swap

omit [MeasurableSpace α] in
/-- With increasing vertex marks, the oriented pair coder reads the supplied coder directly. -/
@[simp]
theorem orientPairCoding_of_le (g : I → I → I → I → α × α) (z a b t : I) (hab : a ≤ b) :
    orientPairCoding g z a b t = g z a b t := by
  simp [orientPairCoding, hab]

omit [MeasurableSpace α] in
/-- With decreasing vertex marks, the oriented pair coder swaps both inputs and outputs. -/
@[simp]
theorem orientPairCoding_of_lt (g : I → I → I → I → α × α) (z a b t : I) (hba : b < a) :
    orientPairCoding g z a b t = (g z b a t).swap := by
  simp [orientPairCoding, not_le_of_gt hba]

omit [MeasurableSpace α] in
/-- Reversing two distinct vertex marks swaps the output of the oriented pair coder. -/
theorem orientPairCoding_swap (g : I → I → I → I → α × α) (z t : I) {a b : I}
    (hab : a ≠ b) : orientPairCoding g z b a t = (orientPairCoding g z a b t).swap := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · simp [orientPairCoding, hab.le, not_le_of_gt hab]
  · simp [orientPairCoding, hba.le, not_le_of_gt hba]

/-- A measurable pair-valued coder remains measurable after orientation by its vertex marks. -/
theorem measurable_orientPairCoding {g : I → I → I → I → α × α}
    (hg : Measurable fun q : I × I × I × I => g q.1 q.2.1 q.2.2.1 q.2.2.2) :
    Measurable fun q : I × I × I × I =>
      orientPairCoding g q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  refine Measurable.ite (measurableSet_le
    (measurable_fst.comp measurable_snd)
    (measurable_fst.comp (measurable_snd.comp measurable_snd))) hg ?_
  exact measurable_swap.comp (hg.comp <| measurable_fst.prodMk <|
    (measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk <|
      (measurable_fst.comp measurable_snd).prodMk <|
        measurable_snd.comp (measurable_snd.comp measurable_snd))

/-- Assemble the scalar function used by `jointArray` from a diagonal coder and a pair-valued
off-diagonal coder.  Equality of the two vertex marks identifies the diagonal. -/
def assembleJointCoding (d : I → I → α) (g : I → I → I → I → α × α)
    (q : I × I × I × I) : α :=
  if q.2.1 = q.2.2.1 then d q.1 q.2.1
  else (orientPairCoding g q.1 q.2.1 q.2.2.1 q.2.2.2).1

omit [MeasurableSpace α] in
/-- On the diagonal, the assembled coding reads the designated diagonal coder and ignores the cell
variable. -/
@[simp]
theorem assembleJointCoding_diag (d : I → I → α) (g : I → I → I → I → α × α)
    (z a t : I) : assembleJointCoding d g (z, a, a, t) = d z a := by
  simp [assembleJointCoding]

omit [MeasurableSpace α] in
/-- At two distinct vertex marks, opposite orientations of the assembled scalar coding are the two
coordinates of one oriented pair output. -/
theorem assembleJointCoding_pair (d : I → I → α) (g : I → I → I → I → α × α)
    (z t : I) {a b : I} (hab : a ≠ b) :
    (assembleJointCoding d g (z, a, b, t), assembleJointCoding d g (z, b, a, t)) =
      orientPairCoding g z a b t := by
  have hba : b ≠ a := Ne.symm hab
  simp only [assembleJointCoding, hab, hba, ite_false]
  rw [orientPairCoding_swap g z t hab]
  exact Prod.eta _

/-- The scalar joint coding assembled from measurable diagonal and pair coders is measurable. -/
theorem measurable_assembleJointCoding {d : I → I → α} {g : I → I → I → I → α × α}
    (hd : Measurable (Function.uncurry d))
    (hg : Measurable fun q : I × I × I × I => g q.1 q.2.1 q.2.2.1 q.2.2.2) :
    Measurable (assembleJointCoding d g) := by
  refine Measurable.ite (measurableSet_eq_fun
    (measurable_fst.comp measurable_snd)
    (measurable_fst.comp (measurable_snd.comp measurable_snd))) ?_ ?_
  · exact hd.comp (measurable_fst.prodMk
      (measurable_fst.comp measurable_snd))
  · exact measurable_fst.comp (measurable_orientPairCoding hg)

omit [MeasurableSpace α] in
/-- For distinct vertex-noise coordinates, a `jointArray` built from `assembleJointCoding` reads
one oriented pair output at the two opposite directed positions. -/
theorem jointArray_assembleJointCoding_pair (d : I → I → α)
    (g : I → I → I → I → α × α) (u : NoiseIndex Unit (Sym2 ℕ) → I) {i j : ℕ}
    (hij : u (.vertex () i) ≠ u (.vertex () j)) :
    (jointArray (assembleJointCoding d g) (i, j) u,
        jointArray (assembleJointCoding d g) (j, i) u) =
      orientPairCoding g (u .global) (u (.vertex () i)) (u (.vertex () j))
        (u (.cell s(i, j))) := by
  rw [jointArray_apply, jointArray_apply_swap]
  exact assembleJointCoding_pair d g _ _ hij

end TauCeti.Probability.AldousHoover

end

end

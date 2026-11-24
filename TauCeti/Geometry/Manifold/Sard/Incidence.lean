/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IsManifold.Pi
public import TauCeti.Geometry.Manifold.Sard.Basic

/-!
# Generic points meet a family of maps in few points

Let `X` be a manifold of dimension `n`, and let `u : M → D → X` be a differentiable family of maps
from a manifold `D` of dimension `g` to `X`, parametrized by a manifold `M` of dimension `d`. A
tuple of points `x : P → X`, indexed by a finite type `P`, is *generic* for the family when it lies
outside a null set of the product manifold `P → X`. This file proves the dimension count behind
choosing generic point constraints: for a generic tuple, whenever the image of a single member
`u m` contains the points `x p` for `p` in a set `S` of labels,

`#S * n ≤ d + #S * g`.

The bad tuples for a fixed set `S` of labels are contained in the image of the incidence map

`M × (S → D) × (Sᶜ → X) → (P → X)`,  `(m, z, y) ↦ (p ↦ u m (z p) for p ∈ S, y p otherwise)`,

whose source has dimension `d + #S * g + #Sᶜ * n`. When `d + #S * g < #S * n` this is smaller than
the dimension `#P * n` of the target, and Sard's theorem for a source of smaller dimension
(`MDifferentiable.isNullSet_range_of_finrank_lt_finrank`) shows that the image is null
(`MDifferentiable.isNullSet_setOf_exists_forall_mem_range`). The union over the finitely many
sets of labels is again null (`MDifferentiable.isNullSet_setOf_exists_finset_forall_mem_range`).
Since null sets are closed under countable unions (`TauCeti.IsNullSet.iUnion`), a generic tuple is
generic for any countable collection of such families simultaneously, and its complement is dense
(`TauCeti.IsNullSet.dense_compl`).

The main application is to pseudoholomorphic curves in a closed symplectic four-manifold `X`
through generic points. There `D` is a closed surface, `n = 4` and `g = 2`. For an almost complex
structure that is regular for simple curves, the moduli space of simple curves of a given genus and
class is a manifold whose dimension is the index of the curves; for a curve with image in class
`C` and singularity number `δ` this index is `d(C) - 2 δ`, with `d(C) = C · C - κ · C`. It is
covered by countably many coordinate slices `M` over which the curves have a fixed domain `D`, and
there are countably many genera and classes. For generic points, a curve of index `d`
contains at most `d / 2` of the points
(`MDifferentiable.isNullSet_setOf_exists_finset_forall_mem_range_of_finrank_eq_four`), which is the
point-count inequality `2 k ≤ d(C) - 2 δ` that the numerical analysis of good cycles through
generic points takes as input (`TauCeti.IsGoodCycle`). In particular generic points avoid
every curve of index zero, for instance every embedded exceptional sphere and every embedded
square-zero torus orthogonal to the canonical class. Generic points are also distinct
(`TauCeti.isNullSet_setOf_not_injective`), an instance of the same count for the family of
constant maps parametrized by `X`.

## Main results

* `MDifferentiable.isNullSet_setOf_exists_forall_mem_range`: for a fixed set `S` of labels with
  `d + #S * g < #S * n`, the tuples whose points labelled by `S` all lie on one member of the family
  form a null set.
* `MDifferentiable.isNullSet_setOf_exists_finset_forall_mem_range`: the tuples for which some
  member of the family contains the points labelled by some set `S` with `d + #S * g < #S * n` form
  a null set.
* `MDifferentiable.isNullSet_setOf_exists_finset_forall_mem_range_of_finrank_eq_four`: the case of
  surfaces in a four-manifold, where the condition is `d < 2 * #S`.
* `TauCeti.isNullSet_setOf_not_injective`: the tuples with two equal points form a null set.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., American
  Mathematical Society Colloquium Publications 52, 2012, Chapter 6 (evaluation maps as
  pseudocycles and the dimension count for point constraints).
-/

public section

open Function Module Set
open scoped Manifold Finset

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]
  [SecondCountableTopology X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners ℝ F HF}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HF M] [IsManifold IF 1 M]
  [SecondCountableTopology M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ G HG}
  {D : Type*} [TopologicalSpace D] [ChartedSpace HG D] [IsManifold IG 1 D]
  [SecondCountableTopology D]
  {P : Type*} [Fintype P] {u : M → D → X}

/-- The incidence map of the family `u` for the labels in `S`: it places the points `u m (z p)`
at the labels `p ∈ S` and the free points `y p` at the other labels. -/
private def incidenceMap [DecidableEq P] (u : M → D → X) (S : Finset P) :
    M × (S → D) × ({p // p ∉ S} → X) → P → X :=
  fun w p ↦ if h : p ∈ S then u w.1 (w.2.1 ⟨p, h⟩) else w.2.2 ⟨p, h⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 X]
  [SecondCountableTopology X] [FiniteDimensional ℝ F] [IsManifold IF 1 M]
  [SecondCountableTopology M] [FiniteDimensional ℝ G] [IsManifold IG 1 D]
  [SecondCountableTopology D] in
private theorem mdifferentiable_incidenceMap [DecidableEq P]
    (hu : MDifferentiable (IF.prod IG) I (uncurry u)) (S : Finset P) :
    MDifferentiable (IF.prod ((ModelWithCorners.pi fun _ : S ↦ IG).prod
      (ModelWithCorners.pi fun _ : {p // p ∉ S} ↦ I))) (ModelWithCorners.pi fun _ : P ↦ I)
      (incidenceMap u S) := by
  refine mdifferentiable_pi_iff.2 fun p ↦ ?_
  by_cases h : p ∈ S
  · simp only [incidenceMap, h, ↓reduceDIte]
    exact hu.comp (mdifferentiable_fst.prodMk ((mdifferentiable_apply (i := ⟨p, h⟩)
      (Ii := fun _ : S ↦ IG)).comp (mdifferentiable_fst.comp mdifferentiable_snd)))
  · simp only [incidenceMap, h, ↓reduceDIte]
    exact (mdifferentiable_apply (i := ⟨p, h⟩) (Ii := fun _ : {p // p ∉ S} ↦ I)).comp
      (mdifferentiable_snd.comp mdifferentiable_snd)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 X]
  [SecondCountableTopology X] [FiniteDimensional ℝ F] [IsManifold IF 1 M]
  [SecondCountableTopology M] [FiniteDimensional ℝ G] [IsManifold IG 1 D]
  [SecondCountableTopology D] [Fintype P] [TopologicalSpace X] [TopologicalSpace M]
  [TopologicalSpace D] in
/-- Every tuple whose points labelled by `S` lie on one member of the family is a value of the
incidence map. -/
private theorem subset_range_incidenceMap [DecidableEq P] (S : Finset P) :
    {x : P → X | ∃ m, ∀ p ∈ S, x p ∈ range (u m)} ⊆ range (incidenceMap u S) := by
  rintro x ⟨m, hm⟩
  choose z hz using fun p : S ↦ hm p p.property
  refine ⟨(m, z, fun p ↦ x p), funext fun p ↦ ?_⟩
  by_cases h : p ∈ S
  · simp only [incidenceMap, h, ↓reduceDIte, hz]
  · simp only [incidenceMap, h, ↓reduceDIte]

/-- **The dimension count for point constraints.** Let `u` be a differentiable family of maps from
a manifold `D` of dimension `g` to a manifold `X` of dimension `n`, parametrized by a manifold `M`
of dimension `d`. For a set `S` of labels with `d + #S * g < #S * n`, the tuples `x : P → X` whose
points labelled by `S` all lie in the image of a single member `u m` form a null set. -/
theorem _root_.MDifferentiable.isNullSet_setOf_exists_forall_mem_range
    (hu : MDifferentiable (IF.prod IG) I (uncurry u)) {S : Finset P}
    (hdim : finrank ℝ F + #S * finrank ℝ G < #S * finrank ℝ E) :
    IsNullSet (ModelWithCorners.pi fun _ : P ↦ I)
      {x : P → X | ∃ m, ∀ p ∈ S, x p ∈ range (u m)} := by
  classical
  refine IsNullSet.mono ((mdifferentiable_incidenceMap hu S).isNullSet_range_of_finrank_lt_finrank
    ?_) (subset_range_incidenceMap S)
  have hcard : Fintype.card {p // p ∉ S} + #S = Fintype.card P := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
    exact Nat.sub_add_cancel (Finset.card_le_univ S)
  simp only [finrank_prod, finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, smul_eq_mul, ← hcard, add_mul]
  linarith

/-- **Generic points meet each member of a family in few points.** Let `u` be a differentiable
family of maps from a manifold `D` of dimension `g` to a manifold `X` of dimension `n`,
parametrized by a manifold `M` of dimension `d`. The tuples `x : P → X` for which some member
`u m` contains the points labelled by a set `S` with `d + #S * g < #S * n` form a null set. So for
a generic tuple, any set `S` of labels whose points lie on one member satisfies
`#S * n ≤ d + #S * g`. -/
theorem _root_.MDifferentiable.isNullSet_setOf_exists_finset_forall_mem_range
    (hu : MDifferentiable (IF.prod IG) I (uncurry u)) :
    IsNullSet (ModelWithCorners.pi fun _ : P ↦ I)
      {x : P → X | ∃ m, ∃ S : Finset P, (∀ p ∈ S, x p ∈ range (u m)) ∧
        finrank ℝ F + #S * finrank ℝ G < #S * finrank ℝ E} := by
  refine IsNullSet.mono (IsNullSet.iUnion fun S : {S : Finset P //
    finrank ℝ F + #S * finrank ℝ G < #S * finrank ℝ E} ↦
      hu.isNullSet_setOf_exists_forall_mem_range S.property) ?_
  rintro x ⟨m, S, hS, hdim⟩
  exact mem_iUnion.2 ⟨⟨S, hdim⟩, m, hS⟩

/-- **Generic points on curves in a four-manifold.** Let `u` be a differentiable family of maps
from a surface to a four-manifold `X`, parametrized by a manifold `M` of dimension `d`. For a
generic tuple of points of `X`, every member of the family contains at most `d / 2` of the points:
the tuples for which some member contains the points labelled by a set `S` with `d < 2 * #S` form a
null set. -/
theorem _root_.MDifferentiable.isNullSet_setOf_exists_finset_forall_mem_range_of_finrank_eq_four
    (hu : MDifferentiable (IF.prod IG) I (uncurry u)) (hE : finrank ℝ E = 4)
    (hG : finrank ℝ G = 2) :
    IsNullSet (ModelWithCorners.pi fun _ : P ↦ I)
      {x : P → X | ∃ m, ∃ S : Finset P, (∀ p ∈ S, x p ∈ range (u m)) ∧
        finrank ℝ F < 2 * #S} := by
  refine hu.isNullSet_setOf_exists_finset_forall_mem_range.mono ?_
  rintro x ⟨m, S, hS, hdim⟩
  exact ⟨m, S, hS, by rw [hE, hG]; omega⟩

/-- **Generic points are distinct.** On a manifold of positive dimension, the tuples of points with
two equal entries form a null set. -/
theorem isNullSet_setOf_not_injective [Nontrivial E] :
    IsNullSet (ModelWithCorners.pi fun _ : P ↦ I) {x : P → X | ¬ Injective x} := by
  classical
  -- Two equal points `x p = x q` lie on one member of the family of constant maps parametrized
  -- by `X`, whose domain `Fin 0 → ℝ` has dimension zero.
  refine (MDifferentiable.isNullSet_setOf_exists_finset_forall_mem_range (D := Fin 0 → ℝ)
    (IG := 𝓘(ℝ, Fin 0 → ℝ)) (u := fun (m : X) (_ : Fin 0 → ℝ) ↦ m) (IF := I)
    mdifferentiable_fst).mono ?_
  intro x hx
  obtain ⟨p, q, hpq, hne⟩ : ∃ p q, x p = x q ∧ p ≠ q := by
    simpa [Injective] using hx
  refine ⟨x p, {p, q}, ?_, ?_⟩
  · simp [hpq]
  · rw [Finset.card_pair hne, finrank_fin_fun]
    have := finrank_pos (R := ℝ) (M := E)
    omega

end TauCeti

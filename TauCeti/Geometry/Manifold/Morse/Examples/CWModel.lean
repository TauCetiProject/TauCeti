/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CWModel.Proper
public import TauCeti.Geometry.Manifold.Morse.Examples.QuadraticWell
public import TauCeti.Geometry.Manifold.Morse.CWModel.Projectivization
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
public import TauCeti.Topology.CWComplex.Classical.ComplexProjective
import TauCeti.Analysis.Calculus.Morse.NormSq
import TauCeti.Topology.Algebra.Polynomial.Basic

/-!
# Examples of the CW model of a Morse function

A manifold `M` with a proper Morse function `f` bounded below is homotopy equivalent to a Hausdorff
CW complex whose `m`-cells correspond to the critical points of `f` of index `m`
(`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`); for compact `M` the complex is finite
(`TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`). This file reads off the cells of the
model in five cases: two compact manifolds, a noncompact one, one with infinitely many critical
points, and the empty manifold.

* **The sphere.** The height function on `Sⁿ`, `n ≥ 1`, has a minimum of index `0` and a maximum
  of index `n` and no other critical point, so `Sⁿ` is homotopy equivalent to a finite CW complex
  with one `0`-cell, one `n`-cell and no other cells
  (`TauCeti.exists_cwComplex_homotopyEquiv_sphere`).
* **Complex projective space.** The moment function `[z] ↦ (∑ⱼ j |zⱼ|²) / ∑ⱼ |zⱼ|²` on `ℂℙⁿ` has
  one critical point of each even index `0, 2, …, 2n` and no others
  (`TauCeti.criticalCount_projectiveMomentFunction_complex`), so its CW model has one cell
  in each even dimension up to `2n` and no others
  (`TauCeti.exists_finite_cwComplex_homotopyEquiv_projectivization`). In every dimension it
  therefore has as many cells as the standard CW structure on `ℂℙⁿ`
  (`TauCeti.ComplexProjectiveSpace.cwComplex`), one in each even dimension up to `2n`
  (`TauCeti.exists_cwComplex_homotopyEquiv_projectivization_complex`).
* **The real line.** The function `x ↦ x²` on `ℝ` has the single critical point `0`, of index `0`,
  so `ℝ` is homotopy equivalent to a CW complex with one `0`-cell and no other cells, which is
  contractible (`TauCeti.exists_cwComplex_homotopyEquiv_real`).
* **A countable discrete manifold.** On a manifold modelled on a zero-dimensional space every
  function is Morse and every point is critical of index `0` (`TauCeti.isMorse_of_subsingleton`,
  `TauCeti.manifoldMorseIndex_eq_zero_of_subsingleton`). For the discrete manifold `ℕ` with the
  proper function `n ↦ n` the model therefore has one `0`-cell for each natural number and no
  other cells (`TauCeti.exists_cwComplex_homotopyEquiv_nat`): infinitely many critical points of
  one index give infinitely many cells of that dimension.
* **The empty manifold.** On an empty manifold every function is a proper Morse function, bounded
  below, with no critical points, so its CW model is empty and has no cells in any dimension
  (`TauCeti.exists_cwComplex_homotopyEquiv_empty`): in particular no `0`-cell, so the
  model is not a point.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and §4 (the example of `ℂℙⁿ`).
-/

public section

open Metric Module Set Topology
open scoped ContDiff ContinuousMap LinearAlgebra.Projectivization Manifold

universe u

namespace TauCeti

open Topology.RelCWComplex

/-! ### The sphere -/

section Sphere

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The critical points of index `m` of the height function on the sphere: the south pole when
`m = 0`, the north pole when `m = n`. -/
private theorem setOf_mem_criticalPoints_sphereHeight (v : sphere (0 : E) 1) (m : ℕ) :
    {x ∈ criticalPoints (𝓡 n) (sphereHeight v) | manifoldMorseIndex (𝓡 n) (sphereHeight v) x = m} =
      {x | (x = v ∧ n = m) ∨ (x = -v ∧ 0 = m)} := by
  ext x
  simp only [criticalPoints_sphereHeight, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨rfl | rfl, rfl⟩ <;> simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- **The CW model of the sphere.** For `n ≥ 1` the sphere `Sⁿ` is homotopy equivalent to a finite
Hausdorff CW complex with exactly one `0`-cell, exactly one `n`-cell and no cells in any other
dimension: the cells of the CW model of the height function, whose critical points are a minimum
of index `0` and a maximum of index `n`. -/
theorem exists_cwComplex_homotopyEquiv_sphere (hn : n ≠ 0) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.Finite (univ : Set X) ∧ Nonempty (X ≃ₕ sphere (0 : E) 1) ∧
        Nonempty (cell (univ : Set X) 0 ≃ Unit) ∧ Nonempty (cell (univ : Set X) n ≃ Unit) ∧
        ∀ m, m ≠ 0 → m ≠ n → IsEmpty (cell (univ : Set X) m) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : Nontrivial E :=
    nontrivial_of_finrank_pos (by rw [Fact.out (p := finrank ℝ E = n + 1)]; lia)
  obtain ⟨v⟩ : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  obtain ⟨X, _, _, _, hfin, he, hcell⟩ :=
    (isMorse_sphereHeight (n := n) v).exists_finite_cwComplex_homotopyEquiv
  refine ⟨X, _, ‹_›, ‹_›, hfin, he, ?_, ?_, fun m hm0 hmn ↦ ?_⟩
  · obtain ⟨e⟩ := hcell 0
    rw [setOf_mem_criticalPoints_sphereHeight] at e
    exact ⟨e.trans ((Set.equivOfEq (by ext; simp [hn])).trans (Equiv.Set.singleton (-v)))⟩
  · obtain ⟨e⟩ := hcell n
    rw [setOf_mem_criticalPoints_sphereHeight] at e
    exact ⟨e.trans ((Set.equivOfEq (by ext; simp [hn.symm])).trans (Equiv.Set.singleton v))⟩
  · obtain ⟨e⟩ := hcell m
    rw [setOf_mem_criticalPoints_sphereHeight] at e
    have : IsEmpty {x : sphere (0 : E) 1 | (x = v ∧ n = m) ∨ (x = -v ∧ 0 = m)} :=
      ⟨fun ⟨_, h⟩ ↦ h.elim (fun h ↦ hmn h.2.symm) fun h ↦ hm0 h.2.symm⟩
    exact e.isEmpty

end Sphere

/-! ### Complex projective space -/

/-- **The CW model of complex projective space.** `ℂℙⁿ` is homotopy equivalent to a finite
Hausdorff CW complex whose cells in each dimension correspond to those of the standard CW structure
on `ℂℙⁿ`, one in each even dimension up to `2n` and none in other dimensions: the cells of the CW
model of the moment function with weights `0, 1, …, n`, whose critical points have the even
indices `0, 2, …, 2n`, one of each. -/
theorem exists_cwComplex_homotopyEquiv_projectivization_complex (n : ℕ) :
    letI := ComplexProjectiveSpace.cwComplex n
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.Finite (univ : Set X) ∧ Nonempty (X ≃ₕ ℙ ℂ (Fin (n + 1) → ℂ)) ∧
        ∀ m, Nonempty (cell (univ : Set X) m ≃ cell (univ : Set (ComplexProjectiveSpace n)) m) := by
  let := ComplexProjectiveSpace.cwComplex n
  obtain ⟨X, _, _, _, hfin, he, hcell⟩ := exists_finite_cwComplex_homotopyEquiv_projectivization ℂ n
  refine ⟨X, _, ‹_›, ‹_›, hfin, he, fun m ↦ ?_⟩
  obtain ⟨c⟩ := hcell m
  have := hfin.finite_cell m
  have := (ComplexProjectiveSpace.finite_cwComplex (n := n)).finite_cell m
  -- Both cell types are finite, with one element in each even dimension up to `2n`.
  refine Finite.card_eq.1 ?_
  rw [ComplexProjectiveSpace.nat_card_cell_cwComplex,
    Nat.card_congr (c.trans (projectiveMomentFunctionNatCastCriticalPointsEquiv ℂ n m)),
    natCard_sep_criticalPoints_manifoldMorseIndex_eq_toNat_criticalCount,
    criticalCount_projectiveMomentFunction_complex (w := fun i : Fin (n + 1) ↦ ((i : ℕ) : ℝ))
      (Nat.cast_injective.comp Fin.val_injective)]
  split_ifs <;> simp

/-! ### The real line -/

/-- **The CW model of the real line.** The real line is homotopy equivalent to a Hausdorff CW
complex with exactly one `0`-cell and no cells of positive dimension, which is therefore
contractible: the cells of the CW model of `x ↦ x²`, whose only critical point is the minimum `0`,
of index `0`. -/
theorem exists_cwComplex_homotopyEquiv_real :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      ContractibleSpace X ∧ Nonempty (ℝ ≃ₕ X) ∧ Nonempty (cell (univ : Set X) 0 ≃ Unit) ∧
        ∀ m, IsEmpty (cell (univ : Set X) (m + 1)) := by
  have hp : IsProperMap fun x : ℝ ↦ x ^ 2 := isProperMap_pow two_ne_zero
  have hbdd : BddBelow (range fun x : ℝ ↦ x ^ 2) := ⟨0, by rintro _ ⟨x, rfl⟩; positivity⟩
  have h0 : morseIndex (fun x : ℝ ↦ x ^ 2) 0 = 0 := by simpa using morseIndex_norm_sq (0 : ℝ)
  obtain ⟨X, _, _, _, ⟨e⟩, hcell⟩ := isMorse_sq_real.exists_cwComplex_homotopyEquiv hp hbdd
  refine ⟨X, _, ‹_›, ‹_›, e.symm.contractibleSpace, ⟨e⟩, ?_, fun m ↦ ?_⟩
  · obtain ⟨c⟩ := hcell 0
    refine ⟨c.trans ((Set.equivOfEq ?_).trans (Equiv.Set.singleton (0 : ℝ)))⟩
    ext x
    simp +contextual [criticalPoints_sq_real, h0]
  · obtain ⟨c⟩ := hcell (m + 1)
    have : IsEmpty {x ∈ criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) |
        manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) x = m + 1} :=
      ⟨fun ⟨x, hx, h⟩ ↦ by simp_all [criticalPoints_sq_real]⟩
    exact c.isEmpty

/-! ### A countable discrete manifold -/

attribute [local instance] ChartedSpace.ofDiscreteTopology in
/-- **The CW model of a countable discrete manifold.** The natural numbers form a discrete manifold
modelled on the zero space `Fin 0 → ℝ`, and `n ↦ n` is a proper function on it, bounded below.
Every function on a zero-dimensional manifold is Morse with all its points critical of index `0`,
so the CW model of `n ↦ n` has one `0`-cell for each natural number and no cells of positive
dimension: infinitely many critical points of one index give infinitely many cells of that
dimension. -/
theorem exists_cwComplex_homotopyEquiv_nat :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (ℕ ≃ₕ X) ∧ Nonempty (cell (univ : Set X) 0 ≃ ℕ) ∧
        ∀ m, IsEmpty (cell (univ : Set X) (m + 1)) := by
  have : IsManifold 𝓘(ℝ, Fin 0 → ℝ) ∞ ℕ := .of_discreteTopology _
  have hp : IsProperMap ((↑) : ℕ → ℝ) := Nat.isClosedEmbedding_coe_real.isProperMap
  have hf : IsMorse 𝓘(ℝ, Fin 0 → ℝ) ((↑) : ℕ → ℝ) := isMorse_of_subsingleton
  obtain ⟨X, _, _, _, he, hcell⟩ :=
    hf.exists_cwComplex_homotopyEquiv hp ⟨0, by rintro _ ⟨k, rfl⟩; exact k.cast_nonneg⟩
  refine ⟨X, _, ‹_›, ‹_›, he, ?_, fun m ↦ ?_⟩
  · obtain ⟨c⟩ := hcell 0
    exact ⟨c.trans ((Set.equivOfEq (by ext; simp)).trans (Equiv.Set.univ ℕ))⟩
  · obtain ⟨c⟩ := hcell (m + 1)
    have : IsEmpty {x ∈ criticalPoints 𝓘(ℝ, Fin 0 → ℝ) ((↑) : ℕ → ℝ) |
        manifoldMorseIndex 𝓘(ℝ, Fin 0 → ℝ) ((↑) : ℕ → ℝ) x = m + 1} :=
      ⟨fun ⟨x, _, h⟩ ↦ by simp at h⟩
    exact c.isEmpty

/-! ### The empty manifold -/

attribute [local instance] ChartedSpace.empty in
/-- **The CW model of the empty manifold.** The empty type is a manifold modelled on `ℝ`, and every
function on it is a proper Morse function, bounded below, with no critical points. So its CW model
is an empty CW complex with no cells in any dimension; in particular it has no `0`-cell, so it is
not a point. -/
theorem exists_cwComplex_homotopyEquiv_empty :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      IsEmpty X ∧ Nonempty (Empty ≃ₕ X) ∧ ∀ m, IsEmpty (cell (univ : Set X) m) := by
  have hf : IsMorse 𝓘(ℝ, ℝ) (Empty.elim : Empty → ℝ) := isMorse_iff.2 ⟨isEmptyElim, isEmptyElim⟩
  obtain ⟨X, _, _, _, ⟨e⟩, hcell⟩ :=
    hf.exists_cwComplex_homotopyEquiv continuous_of_discreteTopology.isProperMap (by simp)
  exact ⟨X, _, ‹_›, ‹_›, ⟨fun x ↦ (e.invFun x).elim⟩, ⟨e⟩, fun m ↦ (hcell m).some.isEmpty⟩

end TauCeti

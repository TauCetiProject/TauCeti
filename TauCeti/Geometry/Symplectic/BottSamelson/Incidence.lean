/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.CoordinateSubspace
public import TauCeti.Geometry.Symplectic.BottSamelson.FixedMoment

/-!
# The torus-fixed flags of the word `121` Bott–Samelson manifold

The Bott–Samelson manifold of the word `121` is the incidence variety

`X = {(L₁, P, L) : L₁ ⊆ span(e₁, e₂), L₁ ⊆ P, L ⊆ P}`

of triples of complex subspaces of `ℂ³` with `L₁` and `L` lines and `P` a plane
(`TauCeti.BottSamelson.incidence`). The diagonal torus `T = (S¹)³` acts on `ℂ³` coordinatewise,
on its subspaces, and on triples of subspaces componentwise; it preserves `X`, since it fixes the
coordinate plane `span(e₁, e₂)` and preserves dimensions and inclusions.

This file proves that `X` has exactly eight `T`-fixed points. A subspace is fixed by `T` exactly
when it is a coordinate subspace (`TauCeti.mem_fixedPoints_iff_exists_eq_spanIndices`), and
coordinate subspaces have the dimension and inclusions of their index sets. So the fixed points of
`X` are the triples of coordinate subspaces whose index sets `(s₁, s₂, s₃)` satisfy `|s₁| = 1`,
`|s₂| = 2`, `|s₃| = 1`, `s₁ ⊆ {1, 2}`, `s₁ ⊆ s₂` and `s₃ ⊆ s₂`. Writing `ij` for `span(e_i, e_j)`,
these are the eight flags

| row | `(L₁, P, L)` |
| --- | --- |
| 1 | `(e₁, 12, e₁)` |
| 2 | `(e₁, 12, e₂)` |
| 3 | `(e₁, 13, e₁)` |
| 4 | `(e₁, 13, e₃)` |
| 5 | `(e₂, 12, e₁)` |
| 6 | `(e₂, 12, e₂)` |
| 7 | `(e₂, 23, e₂)` |
| 8 | `(e₂, 23, e₃)` |

(`TauCeti.BottSamelson.fixedFlag`, so that row `k + 1` is `fixedFlag k`;
`TauCeti.BottSamelson.incidence_inter_fixedPoints`). They are pairwise distinct
(`TauCeti.BottSamelson.fixedFlag_injective`). They are listed in the order of the rows of
`TauCeti.BottSamelson.fixedMoment`, whose row `k + 1` is the value at the flag of row `k + 1` of
the moment map `(L₁, P, L) ↦ diag(a Π_L₁ + b Π_P + c Π_L)`, with `Π_V` the orthogonal projector
onto `V`; that evaluation is not carried out here. Exchanging `e₁` and `e₂` relabels the fixed
flags by the involution `TauCeti.BottSamelson.fixedSwap`, which also relabels the rows of
`fixedMoment` (`TauCeti.BottSamelson.map_fixedFlag_fixedSwap`).

## Main definitions

* `TauCeti.BottSamelson.incidence`: the word `121` Bott–Samelson manifold, as a set of triples of
  subspaces of `ℂ³`.
* `TauCeti.BottSamelson.fixedFlagIndex`: the coordinate index sets of the eight fixed flags.
* `TauCeti.BottSamelson.fixedFlag`: the eight fixed flags.

## Main results

* `TauCeti.BottSamelson.smul_mem_incidence`: the torus preserves the incidence variety.
* `TauCeti.BottSamelson.incidence_inter_fixedPoints`: the torus-fixed points of the incidence
  variety are exactly the eight flags `fixedFlag k`.
* `TauCeti.BottSamelson.fixedFlag_injective`,
  `TauCeti.BottSamelson.ncard_incidence_inter_fixedPoints`: there are exactly eight of them.
* `TauCeti.BottSamelson.map_fixedFlag_fixedSwap`: exchanging `e₁` and `e₂` permutes them by
  `fixedSwap`.

## References

* L. Escobar, *Brick manifolds and toric varieties of brick polytopes*, Electronic Journal of
  Combinatorics 23(2) (2016), #P2.25, Sections 3.2 and 4.1 (Bott–Samelson manifolds as incidence
  varieties in products of Grassmannians, and their torus-fixed points).
* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bulletin of the London Mathematical
  Society 14 (1982), 1–15, Section 3 (the torus-fixed points of Grassmannians and flag manifolds
  are the coordinate flags).
-/

public section

noncomputable section

open Module (finrank)
open scoped Pointwise

namespace TauCeti.BottSamelson

/-- The word `121` Bott–Samelson manifold: the triples `(L₁, P, L)` of complex subspaces of `ℂ³`
with `L₁` and `L` lines and `P` a plane, such that `L₁ ⊆ span(e₁, e₂)`, `L₁ ⊆ P` and `L ⊆ P`. -/
def incidence : Set (Submodule ℂ (EuclideanSpace ℂ (Fin 3)) ×
    Submodule ℂ (EuclideanSpace ℂ (Fin 3)) × Submodule ℂ (EuclideanSpace ℂ (Fin 3))) :=
  {x | finrank ℂ x.1 = 1 ∧ finrank ℂ x.2.1 = 2 ∧ finrank ℂ x.2.2 = 1 ∧
    x.1 ≤ (EuclideanSpace.basisFun (Fin 3) ℂ).spanIndices ↑({0, 1} : Finset (Fin 3)) ∧
    x.1 ≤ x.2.1 ∧ x.2.2 ≤ x.2.1}

/-- Membership in the incidence variety, componentwise. -/
@[simp]
theorem mem_incidence {L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3))} :
    (L₁, P, L) ∈ incidence ↔ finrank ℂ L₁ = 1 ∧ finrank ℂ P = 2 ∧ finrank ℂ L = 1 ∧
      L₁ ≤ (EuclideanSpace.basisFun (Fin 3) ℂ).spanIndices ↑({0, 1} : Finset (Fin 3)) ∧
      L₁ ≤ P ∧ L ≤ P :=
  Iff.rfl

/-- The diagonal torus preserves the incidence variety. -/
theorem smul_mem_incidence (t : Fin 3 → Circle) {L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3))}
    (hx : (L₁, P, L) ∈ incidence) : t • (L₁, P, L) ∈ incidence := by
  obtain ⟨h₁, h₂, h₃, h₀, h₁₂, h₃₂⟩ := hx
  have hrank (V : Submodule ℂ (EuclideanSpace ℂ (Fin 3))) :
      finrank ℂ (V.map (DistribSMul.toLinearMap ℂ _ t)) = finrank ℂ V :=
    (V.equivMapOfInjective _ (MulAction.injective t)).finrank_eq.symm
  simp only [Prod.smul_mk, mem_incidence, Submodule.pointwise_smul_def, hrank]
  refine ⟨h₁, h₂, h₃, ?_, Submodule.map_mono h₁₂, Submodule.map_mono h₃₂⟩
  rw [← smul_spanIndices t, Submodule.pointwise_smul_def]
  exact Submodule.map_mono h₀

/-- The coordinate index sets `(s₁, s₂, s₃)` of the eight torus-fixed flags of the word `121`
Bott–Samelson manifold, in the order of the rows of `TauCeti.BottSamelson.fixedMoment`. -/
def fixedFlagIndex : Fin 8 → Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) :=
  ![({0}, {0, 1}, {0}), ({0}, {0, 1}, {1}), ({0}, {0, 2}, {0}), ({0}, {0, 2}, {2}),
    ({1}, {0, 1}, {0}), ({1}, {0, 1}, {1}), ({1}, {1, 2}, {1}), ({1}, {1, 2}, {2})]

/-- The index sets of the fixed flags, as an explicit vector. -/
theorem fixedFlagIndex_def :
    fixedFlagIndex =
      ![({0}, {0, 1}, {0}), ({0}, {0, 1}, {1}), ({0}, {0, 2}, {0}), ({0}, {0, 2}, {2}),
        ({1}, {0, 1}, {0}), ({1}, {0, 1}, {1}), ({1}, {1, 2}, {1}), ({1}, {1, 2}, {2})] :=
  (rfl)

/-- The eight torus-fixed flags `(L₁, P, L)` of the word `121` Bott–Samelson manifold: the triples
of coordinate subspaces with index sets `fixedFlagIndex k`. Row `k + 1` of the table in the module
docstring is `fixedFlag k`. -/
def fixedFlag (k : Fin 8) : Submodule ℂ (EuclideanSpace ℂ (Fin 3)) ×
    Submodule ℂ (EuclideanSpace ℂ (Fin 3)) × Submodule ℂ (EuclideanSpace ℂ (Fin 3)) :=
  ((EuclideanSpace.basisFun (Fin 3) ℂ).spanIndices (fixedFlagIndex k).1,
    (EuclideanSpace.basisFun (Fin 3) ℂ).spanIndices (fixedFlagIndex k).2.1,
    (EuclideanSpace.basisFun (Fin 3) ℂ).spanIndices (fixedFlagIndex k).2.2)

/-- The fixed flags, componentwise. -/
theorem fixedFlag_def (k : Fin 8) :
    fixedFlag k =
      ((EuclideanSpace.basisFun (Fin 3) ℂ).spanIndices (fixedFlagIndex k).1,
        (EuclideanSpace.basisFun (Fin 3) ℂ).spanIndices (fixedFlagIndex k).2.1,
        (EuclideanSpace.basisFun (Fin 3) ℂ).spanIndices (fixedFlagIndex k).2.2) :=
  (rfl)

/-- The combinatorial core of the classification: the index sets of three coordinate subspaces
with the dimensions and incidences of the Bott–Samelson manifold are those of a fixed flag. -/
private theorem exists_fixedFlagIndex_eq :
    ∀ s₁ s₂ s₃ : Finset (Fin 3), s₁.card = 1 → s₂.card = 2 → s₃.card = 1 → s₁ ⊆ {0, 1} →
      s₁ ⊆ s₂ → s₃ ⊆ s₂ → ∃ k, fixedFlagIndex k = (s₁, s₂, s₃) := by
  decide

/-- The triple of coordinate subspaces with index sets `(s₁, s₂, s₃)` lies in the incidence
variety exactly when the index sets have the corresponding sizes and inclusions. -/
private theorem spanIndices_mem_incidence_iff {s₁ s₂ s₃ : Finset (Fin 3)} :
    ((EuclideanSpace.basisFun (Fin 3) ℂ).spanIndices s₁,
        (EuclideanSpace.basisFun (Fin 3) ℂ).spanIndices s₂,
        (EuclideanSpace.basisFun (Fin 3) ℂ).spanIndices s₃) ∈ incidence ↔
      s₁.card = 1 ∧ s₂.card = 2 ∧ s₃.card = 1 ∧ s₁ ⊆ {0, 1} ∧ s₁ ⊆ s₂ ∧ s₃ ⊆ s₂ := by
  simp only [mem_incidence, OrthonormalBasis.finrank_spanIndices,
    OrthonormalBasis.spanIndices_le_spanIndices_iff, Finset.coe_subset]

/-- Each fixed flag lies in the incidence variety. -/
theorem fixedFlag_mem_incidence (k : Fin 8) : fixedFlag k ∈ incidence := by
  rw [fixedFlag_def, spanIndices_mem_incidence_iff]
  revert k
  decide

/-- Each fixed flag is fixed by the diagonal torus. -/
theorem fixedFlag_mem_fixedPoints (k : Fin 8) :
    fixedFlag k ∈ MulAction.fixedPoints (Fin 3 → Circle) (Submodule ℂ (EuclideanSpace ℂ (Fin 3)) ×
      Submodule ℂ (EuclideanSpace ℂ (Fin 3)) × Submodule ℂ (EuclideanSpace ℂ (Fin 3))) := by
  intro t
  simp [fixedFlag_def]

/-- **The torus-fixed points of the word `121` Bott–Samelson manifold** are exactly the eight
flags `fixedFlag k`. -/
theorem incidence_inter_fixedPoints :
    incidence ∩ MulAction.fixedPoints (Fin 3 → Circle) (Submodule ℂ (EuclideanSpace ℂ (Fin 3)) ×
      Submodule ℂ (EuclideanSpace ℂ (Fin 3)) × Submodule ℂ (EuclideanSpace ℂ (Fin 3))) =
      Set.range fixedFlag := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro ⟨L₁, P, L⟩ ⟨hX, hfix⟩
    obtain ⟨s₁, rfl⟩ := mem_fixedPoints_iff_exists_eq_spanIndices.1 fun t ↦
      congrArg Prod.fst (hfix t)
    obtain ⟨s₂, rfl⟩ := mem_fixedPoints_iff_exists_eq_spanIndices.1 fun t ↦
      congrArg (·.2.1) (hfix t)
    obtain ⟨s₃, rfl⟩ := mem_fixedPoints_iff_exists_eq_spanIndices.1 fun t ↦
      congrArg (·.2.2) (hfix t)
    obtain ⟨h₁, h₂, h₃, h₀, h₁₂, h₃₂⟩ := spanIndices_mem_incidence_iff.1 hX
    obtain ⟨k, hk⟩ := exists_fixedFlagIndex_eq s₁ s₂ s₃ h₁ h₂ h₃ h₀ h₁₂ h₃₂
    exact ⟨k, by rw [fixedFlag_def, hk]⟩
  · rintro _ ⟨k, rfl⟩
    exact ⟨fixedFlag_mem_incidence k, fixedFlag_mem_fixedPoints k⟩

/-- The eight fixed flags are pairwise distinct. -/
theorem fixedFlag_injective : Function.Injective fixedFlag := by
  intro k l h
  simp only [fixedFlag_def, Prod.mk.injEq, OrthonormalBasis.spanIndices_inj,
    Finset.coe_inj] at h
  revert k l
  decide

/-- The word `121` Bott–Samelson manifold has exactly eight torus-fixed points. -/
theorem ncard_incidence_inter_fixedPoints :
    (incidence ∩ MulAction.fixedPoints (Fin 3 → Circle) (Submodule ℂ (EuclideanSpace ℂ (Fin 3)) ×
      Submodule ℂ (EuclideanSpace ℂ (Fin 3)) × Submodule ℂ (EuclideanSpace ℂ (Fin 3)))).ncard =
      8 := by
  rw [incidence_inter_fixedPoints, Set.ncard_range_of_injective fixedFlag_injective,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Exchanging the coordinates `e₁` and `e₂` of `ℂ³` carries each fixed flag to the fixed flag
relabeled by `fixedSwap`, componentwise. -/
theorem map_fixedFlag_fixedSwap (k : Fin 8) :
    let σ : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) :=
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.swap (0 : Fin 3) 1)
    ((fixedFlag k).1.map σ, (fixedFlag k).2.1.map σ, (fixedFlag k).2.2.map σ) =
      fixedFlag (fixedSwap k) := by
  intro σ
  simp only [σ, fixedFlag_def, map_piLpCongrLeft_spanIndices_basisFun, ← Finset.coe_image,
    Prod.mk.injEq, OrthonormalBasis.spanIndices_inj, Finset.coe_inj]
  fin_cases k <;>
    simp [fixedFlagIndex_def, fixedSwap_apply, Finset.pair_comm, Equiv.swap_apply_of_ne_of_ne]

end TauCeti.BottSamelson

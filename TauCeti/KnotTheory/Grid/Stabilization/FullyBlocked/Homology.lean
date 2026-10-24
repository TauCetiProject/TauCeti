/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bigraded.Stabilization
public import TauCeti.KnotTheory.Grid.Homology.FullyBlockedBigraded
public import TauCeti.KnotTheory.Grid.SmallGrid.Homology
public import TauCeti.KnotTheory.Grid.Stabilization.FullyBlocked.Grading

/-!
# The bigraded fully blocked stabilization factor

Let `G'` be the stabilization of a grid diagram `G` with an odd number of components that splits
the `X`-marking of column `s`. The fully blocked stabilization comparison
`TauCeti.GridDiagram.fullyBlockedHomologyStabilizeXEquivProd` identifies `GH~(G')` with two
copies of `GH~(G)`. Its first component, the center part, raises the bidegree by `(1, 1)`, and its
second component, the reduced off-center homotopy, preserves the bidegree. Hence it commutes with
the homogeneous projections of fully blocked homology and restricts, in every bidegree `g`, to an
equivalence

`GH~(G')_g ≃ GH~(G)_{g + (1, 1)} × GH~(G)_g`.

So `GH~(G') ≅ GH~(G) ⊗ W` as bigraded vector spaces, with `W` the two-dimensional space with
generators in bidegrees `(0, 0)` and `(-1, -1)`: the Poincaré series of fully blocked homology is
multiplied by `TauCeti.Bigraded.W`. Its class modulo `⊗ W`-stabilization is therefore unchanged by
this stabilization. Starting from the standard `2 × 2` grid, whose series is `W`, the resulting
`3 × 3` unknot grid has series `W ^ 2`, so the dependence of fully blocked homology on the grid
size is visible in the bigrading.

## Main definitions

* `TauCeti.OddComponentGridDiagram.fullyBlockedStabilizeXHomologyPieceEquiv`: the equivalence
  `GH~(G')_g ≃ GH~(G)_{g + (1, 1)} × GH~(G)_g`.

## Main results

* `fullyBlockedHomologyStabilizeXEquivProd_bigradedFullyBlockedHomologyProjection`:
  the stabilization comparison intertwines the homogeneous projections, with the shift `(1, 1)` on
  the center component.
* `TauCeti.OddComponentGridDiagram.finrank_bigradedFullyBlockedHomologyPiece_stabilizeX`: the
  dimension of a piece of `GH~(G')` is the sum of the dimensions of two pieces of `GH~(G)`.
* `TauCeti.OddComponentGridDiagram.fullyBlockedHomologySeries_stabilizeX`: stabilization
  multiplies the Poincaré series by `W`.
* `TauCeti.OddComponentGridDiagram.isStablyEquiv_fullyBlockedHomologySeries_stabilizeX`: the
  stable class of the Poincaré series is unchanged by stabilization.

## References

* Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2, for the bigraded
  identification `GH~(G') ≅ GH~(G) ⊗ W`.
* Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.2.
-/

public section

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (s : Fin n)

local notation "F" => ZMod 2

/-- The center component of the chain comparison sends the part of bidegree `g` of a stabilized
chain to the part of bidegree `g + (1, 1)` of its image. -/
private theorem fst_fullyBlockedStabilizeXMap_bigradedChainInclusion (g : ℤ × ℤ)
    (c : GridChain F (n + 1)) :
    (G.1.fullyBlockedStabilizeXMap s ((G.stabilizeX s).bigradedChainInclusion F g
        ((G.stabilizeX s).bigradedChainProjection F g c))).1 =
      G.bigradedChainInclusion F (g + (1, 1))
        (G.bigradedChainProjection F (g + (1, 1)) (G.1.fullyBlockedStabilizeXMap s c).1) := by
  refine (G.stabilizeX s).map_bigradedChainInclusion_bigradedChainProjection G
    (LinearMap.fst F _ _ ∘ₗ G.1.fullyBlockedStabilizeXMap s) (1, 1) (fun x y hy => ?_) g c
  have h := G.fullyBlockedStabilizeXMap_fst_bigradedChainInclusion_eq_zero_of_ne s
    ((G.stabilizeX s).bidegree x)
    ((G.stabilizeX s).bigradedChainProjection F ((G.stabilizeX s).bidegree x) (Finsupp.single x 1))
    hy
  simpa only [bigradedChainInclusion_bigradedChainProjection_single, ↓reduceIte,
    LinearMap.comp_apply, LinearMap.fst_apply] using h

/-- The off-center component of the chain comparison preserves homogeneous parts. -/
private theorem snd_fullyBlockedStabilizeXMap_bigradedChainInclusion (g : ℤ × ℤ)
    (c : GridChain F (n + 1)) :
    (G.1.fullyBlockedStabilizeXMap s ((G.stabilizeX s).bigradedChainInclusion F g
        ((G.stabilizeX s).bigradedChainProjection F g c))).2 =
      G.bigradedChainInclusion F g
        (G.bigradedChainProjection F g (G.1.fullyBlockedStabilizeXMap s c).2) := by
  have h := (G.stabilizeX s).map_bigradedChainInclusion_bigradedChainProjection G
    (LinearMap.snd F _ _ ∘ₗ G.1.fullyBlockedStabilizeXMap s) 0 (fun x y hy => ?_) g c
  · rw [add_zero] at h
    simpa only [LinearMap.comp_apply, LinearMap.snd_apply] using h
  have h := G.fullyBlockedStabilizeXMap_snd_bigradedChainInclusion_eq_zero_of_ne s
    ((G.stabilizeX s).bidegree x)
    ((G.stabilizeX s).bigradedChainProjection F ((G.stabilizeX s).bidegree x) (Finsupp.single x 1))
    (x := y) (by rwa [← add_zero ((G.stabilizeX s).bidegree x)])
  simpa only [bigradedChainInclusion_bigradedChainProjection_single, ↓reduceIte,
    LinearMap.comp_apply, LinearMap.snd_apply] using h

/-- The center cycle of the comparison is the center component of the chain comparison. -/
private theorem coe_fst_fullyBlockedStabilizeXCycles (z : (G.stabilizeX s).1.fullyBlockedCycles) :
    ((G.1.fullyBlockedStabilizeXCycles s z).1 : GridChain F n) =
      (G.1.fullyBlockedStabilizeXMap s z).1 :=
  (G.1.fullyBlockedStabilizeXCycles_fst s z).trans (G.1.fullyBlockedStabilizeXMap_fst s z).symm

/-- The off-center cycle of the comparison is the off-center component of the chain
comparison. -/
private theorem coe_snd_fullyBlockedStabilizeXCycles (z : (G.stabilizeX s).1.fullyBlockedCycles) :
    ((G.1.fullyBlockedStabilizeXCycles s z).2 : GridChain F n) =
      (G.1.fullyBlockedStabilizeXMap s z).2 :=
  (G.1.fullyBlockedStabilizeXCycles_snd s z).trans (G.1.fullyBlockedStabilizeXMap_snd s z).symm

/-- The stabilization comparison intertwines the homogeneous projections of fully blocked
homology: the center component shifts the bidegree by `(1, 1)` and the off-center component
preserves it. -/
theorem fullyBlockedHomologyStabilizeXEquivProd_bigradedFullyBlockedHomologyProjection (g : ℤ × ℤ)
    (y : (G.stabilizeX s).1.fullyBlockedHomology) :
    G.1.fullyBlockedHomologyStabilizeXEquivProd s
        ((G.stabilizeX s).bigradedFullyBlockedHomologyProjection g y) =
      (G.bigradedFullyBlockedHomologyProjection (g + (1, 1))
          (G.1.fullyBlockedHomologyStabilizeXEquivProd s y).1,
        G.bigradedFullyBlockedHomologyProjection g
          (G.1.fullyBlockedHomologyStabilizeXEquivProd s y).2) := by
  induction y using Submodule.Quotient.induction_on with
  | H z =>
    -- The ascription states the computation lemma at `(G.stabilizeX s).1`, the diagram `z` lives
    -- over; it is only definitionally the one in the lemma, so `rw` cannot match it unannotated.
    rw [bigradedFullyBlockedHomologyProjection_mk,
      show G.1.fullyBlockedHomologyStabilizeXEquivProd s
          (Submodule.Quotient.mk z : (G.stabilizeX s).1.fullyBlockedHomology) = _ from
        G.1.fullyBlockedHomologyStabilizeXEquivProd_mk s z]
    refine (G.1.fullyBlockedHomologyStabilizeXEquivProd_mk s _).trans ?_
    simp only [bigradedFullyBlockedHomologyProjection_mk, Prod.mk.injEq]
    constructor <;> congr 1 <;> ext1
    · simp only [coe_fst_fullyBlockedStabilizeXCycles]
      exact G.fst_fullyBlockedStabilizeXMap_bigradedChainInclusion s g z
    · simp only [coe_snd_fullyBlockedStabilizeXCycles]
      exact G.snd_fullyBlockedStabilizeXMap_bigradedChainInclusion s g z

/-- The center component of the stabilization comparison sends the bidegree-`g` piece into the
bidegree-`(g + (1, 1))` piece. -/
theorem fst_fullyBlockedHomologyStabilizeXEquivProd_mem {g : ℤ × ℤ}
    {y : (G.stabilizeX s).1.fullyBlockedHomology}
    (hy : y ∈ (G.stabilizeX s).bigradedFullyBlockedHomologyPiece g) :
    (G.1.fullyBlockedHomologyStabilizeXEquivProd s y).1 ∈
      G.bigradedFullyBlockedHomologyPiece (g + (1, 1)) := by
  rw [← (mem_bigradedFullyBlockedHomologyPiece_iff _).mp hy,
    fullyBlockedHomologyStabilizeXEquivProd_bigradedFullyBlockedHomologyProjection]
  exact G.bigradedFullyBlockedHomologyProjection_mem _ _

/-- The off-center component of the stabilization comparison preserves the bidegree-`g`
piece. -/
theorem snd_fullyBlockedHomologyStabilizeXEquivProd_mem {g : ℤ × ℤ}
    {y : (G.stabilizeX s).1.fullyBlockedHomology}
    (hy : y ∈ (G.stabilizeX s).bigradedFullyBlockedHomologyPiece g) :
    (G.1.fullyBlockedHomologyStabilizeXEquivProd s y).2 ∈
      G.bigradedFullyBlockedHomologyPiece g := by
  rw [← (mem_bigradedFullyBlockedHomologyPiece_iff _).mp hy,
    fullyBlockedHomologyStabilizeXEquivProd_bigradedFullyBlockedHomologyProjection]
  exact G.bigradedFullyBlockedHomologyProjection_mem _ _

/-- The restriction of the stabilization comparison to the bidegree-`g` piece. -/
private noncomputable def fullyBlockedStabilizeXHomologyPieceMap (g : ℤ × ℤ) :
    (G.stabilizeX s).bigradedFullyBlockedHomologyPiece g →ₗ[F]
      G.bigradedFullyBlockedHomologyPiece (g + (1, 1)) × G.bigradedFullyBlockedHomologyPiece g :=
  (((LinearMap.fst F _ _ ∘ₗ (G.1.fullyBlockedHomologyStabilizeXEquivProd s).toLinearMap) ∘ₗ
      ((G.stabilizeX s).bigradedFullyBlockedHomologyPiece g).subtype).codRestrict _ fun y =>
      G.fst_fullyBlockedHomologyStabilizeXEquivProd_mem s y.2).prod
    (((LinearMap.snd F _ _ ∘ₗ (G.1.fullyBlockedHomologyStabilizeXEquivProd s).toLinearMap) ∘ₗ
      ((G.stabilizeX s).bigradedFullyBlockedHomologyPiece g).subtype).codRestrict _ fun y =>
      G.snd_fullyBlockedHomologyStabilizeXEquivProd_mem s y.2)

private theorem fullyBlockedStabilizeXHomologyPieceMap_bijective (g : ℤ × ℤ) :
    Function.Bijective (G.fullyBlockedStabilizeXHomologyPieceMap s g) := by
  constructor
  · intro y y' h
    have h₁ := congrArg (fun p => (p.1 : G.1.fullyBlockedHomology)) h
    have h₂ := congrArg (fun p => (p.2 : G.1.fullyBlockedHomology)) h
    exact Subtype.ext ((G.1.fullyBlockedHomologyStabilizeXEquivProd s).injective (Prod.ext h₁ h₂))
  · rintro ⟨u, v⟩
    let y := (G.1.fullyBlockedHomologyStabilizeXEquivProd s).symm (u, v)
    refine ⟨⟨(G.stabilizeX s).bigradedFullyBlockedHomologyProjection g y,
      bigradedFullyBlockedHomologyProjection_mem _ _ _⟩, ?_⟩
    have h := G.fullyBlockedHomologyStabilizeXEquivProd_bigradedFullyBlockedHomologyProjection s g y
    rw [LinearEquiv.apply_symm_apply, (mem_bigradedFullyBlockedHomologyPiece_iff G).mp u.2,
      (mem_bigradedFullyBlockedHomologyPiece_iff G).mp v.2] at h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

/-- **The bigraded stabilization factor.** The fully blocked stabilization comparison identifies
the bidegree-`g` piece of the homology of the stabilized diagram with the product of the pieces of
bidegrees `g + (1, 1)` and `g` of the homology of the original diagram. These are the two summands
of `GH~(G) ⊗ W` in bidegree `g`. -/
noncomputable def fullyBlockedStabilizeXHomologyPieceEquiv (g : ℤ × ℤ) :
    (G.stabilizeX s).bigradedFullyBlockedHomologyPiece g ≃ₗ[F]
      G.bigradedFullyBlockedHomologyPiece (g + (1, 1)) × G.bigradedFullyBlockedHomologyPiece g :=
  LinearEquiv.ofBijective _ (G.fullyBlockedStabilizeXHomologyPieceMap_bijective s g)

/-- The first component of the piece equivalence is the center component of the stabilization
comparison. -/
@[simp]
theorem coe_fst_fullyBlockedStabilizeXHomologyPieceEquiv_apply (g : ℤ × ℤ)
    (y : (G.stabilizeX s).bigradedFullyBlockedHomologyPiece g) :
    ((G.fullyBlockedStabilizeXHomologyPieceEquiv s g y).1 : G.1.fullyBlockedHomology) =
      (G.1.fullyBlockedHomologyStabilizeXEquivProd s
        (y : (G.stabilizeX s).1.fullyBlockedHomology)).1 :=
  (rfl)

/-- The second component of the piece equivalence is the off-center component of the
stabilization comparison. -/
@[simp]
theorem coe_snd_fullyBlockedStabilizeXHomologyPieceEquiv_apply (g : ℤ × ℤ)
    (y : (G.stabilizeX s).bigradedFullyBlockedHomologyPiece g) :
    ((G.fullyBlockedStabilizeXHomologyPieceEquiv s g y).2 : G.1.fullyBlockedHomology) =
      (G.1.fullyBlockedHomologyStabilizeXEquivProd s
        (y : (G.stabilizeX s).1.fullyBlockedHomology)).2 :=
  (rfl)

/-- The dimension of a homogeneous piece of the fully blocked homology of the stabilized diagram
is the sum of the dimensions of the pieces of bidegrees `g + (1, 1)` and `g` of the original
homology. -/
theorem finrank_bigradedFullyBlockedHomologyPiece_stabilizeX (g : ℤ × ℤ) :
    Module.finrank F ((G.stabilizeX s).bigradedFullyBlockedHomologyPiece g) =
      Module.finrank F (G.bigradedFullyBlockedHomologyPiece (g + (1, 1))) +
        Module.finrank F (G.bigradedFullyBlockedHomologyPiece g) := by
  rw [(G.fullyBlockedStabilizeXHomologyPieceEquiv s g).finrank_eq, Module.finrank_prod]

/-- **Stabilization multiplies the Poincaré series by `W`.** The Poincaré series of the fully
blocked homology of the stabilization splitting an `X`-marking is that of the original diagram
times the series `W` of the stabilization factor. -/
theorem fullyBlockedHomologySeries_stabilizeX :
    (G.stabilizeX s).fullyBlockedHomologySeries = G.fullyBlockedHomologySeries * Bigraded.W := by
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun g => ?_)
  rw [Bigraded.coeff_mul_W, coeff_fullyBlockedHomologySeries, coeff_fullyBlockedHomologySeries,
    coeff_fullyBlockedHomologySeries, finrank_bigradedFullyBlockedHomologyPiece_stabilizeX,
    add_comm]

/-- The class of the Poincaré series of fully blocked homology modulo `⊗ W`-stabilization is
unchanged by the stabilization splitting an `X`-marking. -/
theorem isStablyEquiv_fullyBlockedHomologySeries_stabilizeX :
    Bigraded.IsStablyEquiv (G.stabilizeX s).fullyBlockedHomologySeries
      G.fullyBlockedHomologySeries := by
  rw [fullyBlockedHomologySeries_stabilizeX, ← pow_one Bigraded.W]
  exact Bigraded.isStablyEquiv_mul_W_pow _ 1

/-- The `3 × 3` unknot grids obtained by stabilizing the standard `2 × 2` grid have Poincaré
series `W ^ 2`: their fully blocked homology is `W ⊗ W`. -/
theorem fullyBlockedHomologySeries_twoByTwo_stabilizeX (s : Fin 2) :
    (twoByTwo.stabilizeX s).fullyBlockedHomologySeries = Bigraded.W ^ 2 := by
  rw [fullyBlockedHomologySeries_stabilizeX, fullyBlockedHomologySeries_twoByTwo, sq]

end TauCeti.OddComponentGridDiagram

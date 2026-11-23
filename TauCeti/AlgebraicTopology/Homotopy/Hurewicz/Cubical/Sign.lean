/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Cube.Generator

/-!
# Signs of the cubical Hurewicz map

The Hurewicz class of a generalized loop `p : (Iⁿ⁺¹, ∂Iⁿ⁺¹) → (X, x)` is the image under `p` of
the selected generator of `Hₙ₊₁(Iⁿ⁺¹, ∂Iⁿ⁺¹)` (`GenLoop.hurewicz`), while its cubical Hurewicz
class is the class of the singular cube `p` itself (`GenLoop.cubicalHurewicz`). The two agree up
to a universal sign (`HomotopyGroup.exists_hurewicz_eq_units_smul_cubicalHurewicz`). The identity
cube of `Iⁿ⁺¹` has coordinate `(-1)^(n(n+1)/2)` against the selected generator
(`TauCeti.singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle`), so that sign is
`(-1)^(n(n+1)/2)`, over every ring:

`hurewicz p = (-1)^(n(n+1)/2) • cubicalHurewicz p`

(`GenLoop.hurewicz_hom_one_eq_neg_one_pow_smul_cubicalHurewicz`, and
`HomotopyGroup.hurewicz_hom_one_eq_neg_one_pow_smul_cubicalHurewicz` on homotopy classes). In degree
`m = n + 1` the two maps agree when `m ≡ 0, 1 mod 4` and differ by a sign when `m ≡ 2, 3 mod 4`; in
particular they differ by a sign on `π₂`.

Transposing the two coordinates of a generalized loop of `X` in dimension two negates its cubical
Hurewicz class (`GenLoop.cubicalHurewicz_congr_swap`). At the level of chains, the boundary of the
transposed square is minus the boundary of the square
(`TauCeti.NormalizedCubicalChain.boundary_ofCube_comp_squareSwap`). On the cube pair
`(I², ∂I²)` the connecting morphism to `H₁(∂I²)` is injective, so the transposed identity square is
minus the identity square in relative homology, and every generalized loop is the image of these
two under its map of pairs.

These signs compare classes built with different coordinate conventions: for instance the torus
swept out by a loop of based loops, whose first coordinate is the loop parameter, with the class
of the corresponding double loop, whose first coordinate is the family parameter.

## Main results

* `GenLoop.hurewicz_hom_one_eq_neg_one_pow_smul_cubicalHurewicz`,
  `HomotopyGroup.hurewicz_hom_one_eq_neg_one_pow_smul_cubicalHurewicz`: the Hurewicz class is
  `(-1)^(n(n+1)/2)` times the cubical Hurewicz class, read in simplicial singular homology.
* `GenLoop.cubicalHurewicz_congr_swap`: transposing the coordinates of a generalized loop in
  dimension two negates its cubical Hurewicz class.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, the Hurewicz map defined by a generator of `Hₙ(Dⁿ, ∂Dⁿ)`.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II, for the
  boundary of a singular cube.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Set
open scoped unitInterval Topology Topology.Homotopy

universe u

/-! ### The Hurewicz sign -/

namespace GenLoop

open TauCeti

variable (k : Type u) [Ring k] {X : Type u} [TopologicalSpace X] {x : X}

/-- **The Hurewicz class is `(-1)^(n(n+1)/2)` times the cubical Hurewicz class.** Over every ring
`k`, the Hurewicz class of a generalized loop `p : (Iⁿ⁺¹, ∂Iⁿ⁺¹) → (X, x)` is `(-1)^(n(n+1)/2)`
times its cubical Hurewicz class, read in simplicial singular homology. -/
theorem hurewicz_hom_one_eq_neg_one_pow_smul_cubicalHurewicz {n : ℕ}
    (p : Ω^ (Fin (n + 1)) X x) :
    (GenLoop.hurewicz (ModuleCat.of k k) p).hom 1 =
      (-1 : k) ^ (n * (n + 1) / 2) •
        (singularCubicalHomologyIso k (TopCat.of X) (n + 1)).inv (GenLoop.cubicalHurewicz k p) := by
  set ε : k := (-1 : k) ^ (n * (n + 1) / 2) with hε
  have hεε : ε * ε = 1 := by
    rw [hε, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  -- `p` carries the identity cube, which is `ε` times the selected generator, to the image of its
  -- cubical Hurewicz class in `Hₙ₊₁(X, {x})`
  have h := singularHomologyMap_toCubeBoundaryPairHom_cubeBoundaryPairCycle k p
  rw [singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle, map_smul] at h
  have hdef := ConcreteCategory.congr_hom
    (hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom (ModuleCat.of k k) p) (1 : k)
  have h2 : ε • (GenLoop.hurewicz (ModuleCat.of k k) p).hom 1 =
      (singularCubicalHomologyIso k (TopCat.of X) (n + 1)).inv (GenLoop.cubicalHurewicz k p) := by
    apply (singularHomologyIsoOfSubsetSingleton (ModuleCat.of k k) n x).toLinearEquiv.injective
    refine ((map_smul _ ε _).trans ?_).trans (h.trans ?_)
    · exact congrArg (ε • ·) hdef
    · exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (singularHomologyIsoOfSubsetSingleton_hom (ModuleCat.of k k) n x)) _).symm
  -- multiply `h2` by `ε` and use `ε * ε = 1`
  have h3 := congrArg (ε • ·) h2
  simp only [smul_smul, hεε, one_smul] at h3
  exact h3

end GenLoop

namespace HomotopyGroup

open TauCeti

variable (k : Type u) [Ring k] {X : Type u} [TopologicalSpace X] {x : X}

/-- **The Hurewicz map is `(-1)^(n(n+1)/2)` times the cubical Hurewicz map**, over every ring `k`:
the Hurewicz class of `a ∈ πₙ₊₁(X, x)` is `(-1)^(n(n+1)/2)` times its cubical Hurewicz class, read
in simplicial singular homology. This determines the universal sign of
`HomotopyGroup.exists_hurewicz_eq_units_smul_cubicalHurewicz`. -/
theorem hurewicz_hom_one_eq_neg_one_pow_smul_cubicalHurewicz (n : ℕ)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    (hurewicz (ModuleCat.of k k) n a).hom 1 =
      (-1 : k) ^ (n * (n + 1) / 2) •
        (singularCubicalHomologyIso k (TopCat.of X) (n + 1)).inv (cubicalHurewicz k n a) :=
  Quotient.inductionOn a fun p ↦ by
    rw [hurewicz_mk, cubicalHurewicz_mk]
    exact GenLoop.hurewicz_hom_one_eq_neg_one_pow_smul_cubicalHurewicz k p

end HomotopyGroup

/-! ### Transposing the coordinates of a square -/

namespace TauCeti

/-- The transposed identity square of the cube pair `(I², ∂I²)`. -/
private def cubeSwap : SingularCube (cubeBoundaryPair.{u} 2).fst 2 :=
  (upCube.{u} 2 : SingularCube (cubeBoundaryPair.{u} 2).fst 2).comp SingularCube.squareSwap

private theorem mapsTo_cubeSwap_boundary :
    MapsTo (cubeSwap.{u}) (Cube.boundary (Fin 2)) (range (cubeBoundaryPair.{u} 2).map) := by
  rintro z ⟨i, hi⟩
  refine ⟨⟨ULift.up (SingularCube.squareSwap z), ⟨Equiv.swap 0 1 i, ?_⟩⟩, rfl⟩
  simpa using hi

variable (k : Type u) [Ring k]

/-- In the relative homology of `(I², ∂I²)` the transposed identity square is minus the identity
square: the connecting morphism to `H₁(∂I²)` is injective and sends them to their boundaries. -/
private theorem homologyπ_cubicalCycleOfCube_cubeSwap :
    ((cubeBoundaryPair.{u} 2).cubicalChainComplex k).homologyπ (1 + 1)
        (TopPair.cubicalCycleOfCube k _ mapsTo_cubeSwap_boundary) =
      -((cubeBoundaryPair.{u} 2).cubicalChainComplex k).homologyπ (1 + 1)
        (cubeBoundaryPairCycle k 1) := by
  apply injective_cubicalHomologyδ_cubeBoundaryPair k 1
  rw [map_neg, cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle,
    TopPair.cubicalHomologyδ_homologyπ_cubicalCycleOfCube, ← map_neg]
  congr 1
  apply ((normalizedCubicalChainComplex k).obj
    (cubeBoundaryPair.{u} 2).snd).moduleCat_iCycles_injective
  rw [map_neg, iCycles_cubeBoundaryCycle, TopPair.iCycles_cubicalBoundaryCycleOfCube]
  -- the inclusion of `∂I²` is injective on chains and carries both chains to the boundaries of
  -- the two squares
  apply NormalizedCubicalChain.map_injective k (cubeBoundaryPair.{u} 2).map.hom
    (cubeBoundaryPair.{u} 2).isEmbedding_map.injective 1
  refine ((TopPair.map_cubicalBoundaryChainOfCube k _ _).trans ?_).trans
    (LinearMap.map_neg _ _).symm
  exact (NormalizedCubicalChain.boundary_ofCube_comp_squareSwap k _).trans
    (congrArg Neg.neg (TopPair.map_cubicalBoundaryChainOfCube k _ _).symm)

end TauCeti

namespace GenLoop

open TauCeti

variable (k : Type u) [Ring k] {X : Type u} [TopologicalSpace X] {x : X}

/-- The map of pairs of a transposed generalized loop is the transposed identity square followed
by the map of pairs of the loop. -/
private theorem toCubeBoundaryPairHom_congr_swap (p : Ω^ (Fin 2) X x) :
    toCubeBoundaryPairHom.{u} (GenLoop.congr x (Equiv.swap 0 1) p) =
      cubeBoundaryPairHom cubeSwap mapsTo_cubeSwap_boundary ≫ toCubeBoundaryPairHom p := by
  apply TopPair.hom_ext_of_fst
  ext z
  refine (toCubeBoundaryPairHom_fst_apply _ z).trans ?_
  -- the ambient map of a composite of maps of pairs is the composite of the ambient maps
  rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply, cubeBoundaryPairHom_fst_apply,
    toCubeBoundaryPairHom_fst_apply, GenLoop.congr_apply]
  -- `cubeSwap` is `squareSwap` followed by `upCube = ULift.up`
  exact congrArg p (SingularCube.squareSwap_apply z.down).symm

/-- **Transposing the coordinates of a square negates its cubical Hurewicz class**: for a
generalized loop `p : (I², ∂I²) → (X, x)`, the cubical Hurewicz class of `(s, t) ↦ p (t, s)` is
minus that of `p`. -/
@[simp]
theorem cubicalHurewicz_congr_swap (p : Ω^ (Fin 2) X x) :
    GenLoop.cubicalHurewicz k (GenLoop.congr x (Equiv.swap 0 1) p) =
      -GenLoop.cubicalHurewicz k p := by
  -- the transposed identity square is minus the identity square, read in relative singular
  -- homology
  have hσ := ConcreteCategory.congr_hom (TopPair.singularCubicalHomologyIso_inv_naturality k
    (cubeBoundaryPairHom cubeSwap mapsTo_cubeSwap_boundary) 2)
      (((cubeBoundaryPair.{u} 2).cubicalChainComplex k).homologyπ 2 (cubeBoundaryPairCycle k 1))
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
    homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle,
    homologyπ_cubicalCycleOfCube_cubeSwap] at hσ
  -- so the image of the transposed loop in `H₂(X, {x})` is minus that of `p`
  have hq := singularHomologyMap_toCubeBoundaryPairHom_cubeBoundaryPairCycle k
    (GenLoop.congr x (Equiv.swap 0 1) p)
  rw [toCubeBoundaryPairHom_congr_swap, TopPair.singularHomologyMap_comp, ModuleCat.comp_apply,
    ← hσ, map_neg, map_neg, singularHomologyMap_toCubeBoundaryPairHom_cubeBoundaryPairCycle] at hq
  apply (ModuleCat.mono_iff_injective (singularCubicalHomologyIso k (TopCat.of X) 2).inv).1
    inferInstance
  have hπ : Function.Injective ((TopPair.ofSubset ({x} : Set (TopCat.of X))).singularHomologyπ
      (ModuleCat.of k k) 2).hom := by
    rw [← singularHomologyIsoOfSubsetSingleton_hom]
    exact (singularHomologyIsoOfSubsetSingleton (ModuleCat.of k k) 1 x).toLinearEquiv.injective
  apply hπ
  -- `singularHomologyπ` and the comparison isomorphism commute with negation. The homology of `X`
  -- and the homology of the ambient space of `(X, {x})` agree only up to unfolding, so `rw` and
  -- `simp` cannot rewrite under these maps and the step is taken in term mode
  exact hq.symm.trans ((map_neg _ _).symm.trans (congrArg _ (map_neg _ _).symm))

end GenLoop

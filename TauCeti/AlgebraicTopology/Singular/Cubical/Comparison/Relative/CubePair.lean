/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Cubical.Relative
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Excision
public import TauCeti.AlgebraicTopology.Singular.IntervalGenerator

/-!
# The fundamental cycles of the cube pair and of the boundary of the cube

The identity cube `upCube (m + 1)` of `Iᵐ⁺¹` sends the boundary of the cube into `∂Iᵐ⁺¹`, so it is
a relative cycle of the normalized cubical chains of the cube pair `(Iᵐ⁺¹, ∂Iᵐ⁺¹)`
(`TauCeti.cubeBoundaryPairCycle`). A singular cube `c` of a pair `P` sending the boundary of the
cube into the subspace is a map of pairs `c : (Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ P` (`TauCeti.cubeBoundaryPairHom`),
and it sends the class of this fundamental cycle to the class of `c` in relative cubical homology
(`TauCeti.homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle`).

With integer coefficients the class of the fundamental cycle is a generator in every dimension
`m + 1 ≥ 1`: `a ↦ a • [Iᵐ⁺¹]` is an isomorphism from `ℤ` onto the relative cubical homology of the
cube pair (`TauCeti.cubicalHomologyCubeBoundaryPairEquiv`). In dimension `n + 2 ≥ 2`, read in
relative singular homology, it is `±` the generator `TauCeti.singularHomologyCubeBoundaryPairIso`
of `Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; ℤ) ≅ ℤ`
(`TauCeti.exists_singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_eq_units_smul`).
The proof compares both classes in the homology of the sphere `Sⁿ⁺² = Iⁿ⁺²/∂Iⁿ⁺²`. The collapse
`TauCeti.sphereGenLoop (n + 2) : (Iⁿ⁺², ∂Iⁿ⁺²) → (Sⁿ⁺², N)` sends the singular generator to the
Hurewicz class of the tautological loop, which generates `Hₙ₊₂(Sⁿ⁺²; ℤ)`
(`TauCeti.isIso_hurewicz_sphereGenLoop`), so it induces an isomorphism on relative singular
homology. It sends the fundamental cycle to the relative class of the tautological loop, which is
the cubical Hurewicz class of that loop (`GenLoop.homologyMap_π_cubicalHurewicz`). The two
Hurewicz maps differ by a universal sign
(`HomotopyGroup.exists_hurewicz_eq_units_smul_cubicalHurewicz`), and the comparison isomorphisms
of absolute and relative homology are compatible
(`TopPair.homologyMap_π_comp_singularCubicalHomologyIso_inv`).

The boundary of the identity cube is the signed sum `Σᵢ (-1)ⁱ ([face i 0] - [face i 1])` of its
faces, each of which lies in `∂Iᵐ⁺¹`. As a chain of `∂Iᵐ⁺¹` it is the **fundamental cycle of the
boundary** (`TauCeti.cubeBoundaryChain`, `TauCeti.cubeBoundaryCycle`), and the connecting
morphism `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ Hₘ(∂Iᵐ⁺¹)` sends the fundamental class of the cube pair to its class
(`TauCeti.cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle`), over every ring. This is the
statement that the connecting morphism of a manifold with boundary carries the fundamental class
relative to the boundary to the fundamental class of the boundary, for the cube with its
oriented faces. Since the cube is contractible, the connecting morphism is injective
(`TauCeti.injective_cubicalHomologyδ_cubeBoundaryPair`) and, in dimension `m + 2 ≥ 2`, an
isomorphism (`TauCeti.isIso_cubicalHomologyδ_cubeBoundaryPair`), over every ring. So the
fundamental cycle of `∂Iᵐ⁺²` generates `Hₘ₊₁(∂Iᵐ⁺²; ℤ) ≅ ℤ`
(`TauCeti.bijective_zsmul_homologyπ_cubeBoundaryCycle`).

In dimension one this identifies the fundamental cycle with the singular generator over every
ring `k`, with no sign
(`TauCeti.singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_zero`): the connecting
morphisms are injective, and both classes have boundary `[0] - [1]` in `H₀(∂I¹; k)`,
read through the comparison of point classes in degree zero
(`TauCeti.singularCubicalHomologyIso_hom_singularHomology₀Section`). So `[I¹]` generates
`H₁(I¹, ∂I¹; k)` (`TauCeti.bijective_smul_homologyπ_cubeBoundaryPairCycle_zero`).

## Main declarations

* `TauCeti.mapsTo_upCube_boundary`: the identity cube sends the boundary of the cube into the
  subspace of the cube pair.
* `TauCeti.cubeBoundaryPairCycle`: the fundamental relative cycle of the cube pair.
* `TauCeti.homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle`: `c_*[Iᵐ⁺¹] = [c]` in relative
  cubical homology.
* `TauCeti.exists_singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_eq_units_smul`:
  the fundamental cycle is `±` the singular generator of `Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; ℤ)`.
* `TauCeti.cubicalHomologyCubeBoundaryPairEquiv`: the isomorphism `ℤ ≃ₗ[ℤ] Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; ℤ)`,
  `a ↦ a • [Iᵐ⁺¹]`, of relative cubical homology.
* `TauCeti.cubeBoundaryChain`, `TauCeti.cubeBoundaryCycle`: the fundamental cycle of `∂Iᵐ⁺¹`,
  whose image in `Iᵐ⁺¹` is the boundary of the identity cube (`TauCeti.map_cubeBoundaryChain`).
* `TauCeti.cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle`: `δ[Iᵐ⁺¹, ∂Iᵐ⁺¹] = [∂Iᵐ⁺¹]`.
* `TauCeti.isIso_cubicalHomologyδ_cubeBoundaryPair`: the connecting morphism
  `Hₘ₊₂(Iᵐ⁺², ∂Iᵐ⁺²) ⟶ Hₘ₊₁(∂Iᵐ⁺²)` is an isomorphism.
* `TauCeti.bijective_zsmul_homologyπ_cubeBoundaryCycle`: `[∂Iᵐ⁺²]` generates `Hₘ₊₁(∂Iᵐ⁺²; ℤ)`.
* `TauCeti.singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_zero`,
  `TauCeti.bijective_smul_homologyπ_cubeBoundaryPairCycle_zero`: in dimension one, `[I¹]` is the
  singular generator of `H₁(I¹, ∂I¹; k)` over every ring `k`.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, the Hurewicz map defined by a generator of `Hₙ(Dⁿ, ∂Dⁿ)`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Metric Set
open scoped unitInterval Topology.Homotopy

universe u

namespace TauCeti

variable (k : Type u) [Ring k]

/-- The identity cube `upCube m` sends the boundary of `Iᵐ` into the subspace `∂Iᵐ` of the cube
pair. -/
lemma mapsTo_upCube_boundary (m : ℕ) :
    MapsTo (upCube.{u} m : SingularCube (cubeBoundaryPair.{u} m).fst m) (Cube.boundary (Fin m))
      (range (cubeBoundaryPair.{u} m).map) :=
  fun y hy ↦ ⟨⟨ULift.up y, hy⟩, rfl⟩

/-- The fundamental relative cycle of the cube pair `(Iᵐ⁺¹, ∂Iᵐ⁺¹)`: the identity cube `upCube`,
as a relative cycle of the normalized cubical chains with coefficients in `k`. -/
def cubeBoundaryPairCycle (m : ℕ) :
    ((cubeBoundaryPair.{u} (m + 1)).cubicalChainComplex k).cycles (m + 1) :=
  TopPair.cubicalCycleOfCube k _ (mapsTo_upCube_boundary (m + 1))

/-- The map of pairs `c : (Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ P` given by a cube `c` sends the class of the fundamental
cycle of the cube pair to the class of `c` in relative cubical homology. -/
theorem homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle {P : TopPair.{u}} {m : ℕ}
    (c : SingularCube P.fst (m + 1)) (hc : MapsTo c (Cube.boundary (Fin (m + 1))) (range P.map)) :
    HomologicalComplex.homologyMap
        (TopPair.cubicalChainComplexMap k (cubeBoundaryPairHom c hc)) (m + 1)
        (((cubeBoundaryPair.{u} (m + 1)).cubicalChainComplex k).homologyπ (m + 1)
          (cubeBoundaryPairCycle k m)) =
      (P.cubicalChainComplex k).homologyπ (m + 1) (TopPair.cubicalCycleOfCube k c hc) := by
  -- The cube `c ∘ upCube` is `c`.
  have hcid : (TopPair.Hom.fst (cubeBoundaryPairHom c hc)).hom.comp
      (upCube.{u} (m + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1)).fst (m + 1)) = c :=
    ContinuousMap.ext fun y ↦ cubeBoundaryPairHom_fst_apply c hc _
  rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]
  exact congrArg _ ((TopPair.cyclesMap_cubicalCycleOfCube k _ _ _ (by rw [hcid]; exact hc)).trans
    (by simp only [hcid]))

/-! ### The fundamental cycle generates -/

/-- The collapse `TauCeti.sphereGenLoop (n + 2) : (Iⁿ⁺², ∂Iⁿ⁺²) → (Sⁿ⁺², N)` carries the class of
the fundamental cycle, read in relative singular homology, to the cubical Hurewicz class of the
tautological loop, read in singular homology and then in the relative homology of `(Sⁿ⁺², N)`. -/
private lemma singularHomologyMap_sphereGenLoop_cubeBoundaryPairCycle (n : ℕ) :
    TopPair.singularHomologyMap (GenLoop.toCubeBoundaryPairHom (sphereGenLoop (n + 2)))
        (ModuleCat.of ℤ ℤ) (n + 2)
        ((TopPair.singularCubicalHomologyIso ℤ (cubeBoundaryPair.{0} (n + 2)) (n + 2)).inv
          (((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex ℤ).homologyπ (n + 2)
            (cubeBoundaryPairCycle ℤ (n + 1)))) =
      (TopPair.ofSubset ({sphereNorthPole (n + 2)} :
        Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)))).singularHomologyπ
          (ModuleCat.of ℤ ℤ) (n + 2) ((singularCubicalHomologyIso ℤ _ (n + 2)).inv
            (GenLoop.cubicalHurewicz ℤ (sphereGenLoop (n + 2)))) := by
  let γ := sphereGenLoop (n + 2)
  let Q := TopPair.ofSubset
    ({sphereNorthPole (n + 2)} : Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)))
  have ha := ConcreteCategory.congr_hom (TopPair.singularCubicalHomologyIso_inv_naturality ℤ
    (GenLoop.toCubeBoundaryPairHom γ) (n + 2))
      (((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex ℤ).homologyπ (n + 2)
        (cubeBoundaryPairCycle ℤ (n + 1)))
  -- In relative cubical homology, `γ` carries the fundamental cycle to its own class, which is the
  -- image of its cubical Hurewicz class.
  have hb : HomologicalComplex.homologyMap
      (TopPair.cubicalChainComplexMap ℤ (GenLoop.toCubeBoundaryPairHom γ)) (n + 2)
        (((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex ℤ).homologyπ (n + 2)
          (cubeBoundaryPairCycle ℤ (n + 1))) =
      HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex ℤ).map Q.map))
        (n + 2) (GenLoop.cubicalHurewicz ℤ γ) := by
    rw [GenLoop.toCubeBoundaryPairHom_eq_cubeBoundaryPairHom]
    exact (homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle ℤ _ _).trans
      (GenLoop.homologyMap_π_cubicalHurewicz ℤ γ).symm
  have hd := ConcreteCategory.congr_hom
    (TopPair.homologyMap_π_comp_singularCubicalHomologyIso_inv ℤ Q (n + 2))
      (GenLoop.cubicalHurewicz ℤ γ)
  simp only [ConcreteCategory.comp_apply] at ha hd
  -- Chain the naturality square of the comparison, `hb` and the compatibility square `hd`; the
  -- ambient spaces of the pairs agree only up to unfolding, so `hd` closes the goal by `exact`.
  rw [← ha, hb]
  exact hd

/-- **The fundamental cycle of the cube pair is a generator, in singular homology.** There is a
sign `ε` such that the class of the fundamental cycle `TauCeti.cubeBoundaryPairCycle` of
`(Iⁿ⁺², ∂Iⁿ⁺²)`, read in relative singular homology, is `ε` times the generator
`TauCeti.singularHomologyCubeBoundaryPairIso` of `Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; ℤ) ≅ ℤ`. -/
theorem exists_singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_eq_units_smul
    (n : ℕ) :
    ∃ ε : ℤˣ, (TopPair.singularCubicalHomologyIso ℤ (cubeBoundaryPair.{0} (n + 2)) (n + 2)).inv
        (((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex ℤ).homologyπ (n + 2)
          (cubeBoundaryPairCycle ℤ (n + 1))) =
      (ε : ℤ) • (singularHomologyCubeBoundaryPairIso (ModuleCat.of ℤ ℤ) (n + 2)).inv (1 : ℤ) := by
  obtain ⟨ε, hε⟩ := HomotopyGroup.exists_hurewicz_eq_units_smul_cubicalHurewicz n
  let γ := sphereGenLoop (n + 2)
  let Q := TopPair.ofSubset
    ({sphereNorthPole (n + 2)} : Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)))
  -- The collapse `γ` induces an isomorphism `φ` on relative singular homology, and the two
  -- classes are compared through their images in `(Sⁿ⁺², N)`.
  let φ := TopPair.singularHomologyMap (GenLoop.toCubeBoundaryPairHom γ) (ModuleCat.of ℤ ℤ) (n + 2)
  -- `γ` carries the singular generator to the Hurewicz class of `γ`, read in `(Sⁿ⁺², N)`.
  have hg : φ ((singularHomologyCubeBoundaryPairIso (ModuleCat.of ℤ ℤ) (n + 2)).inv (1 : ℤ)) =
      Q.singularHomologyπ (ModuleCat.of ℤ ℤ) (n + 2)
        ((GenLoop.hurewicz (ModuleCat.of ℤ ℤ) γ).hom 1) := by
    rw [← ModuleCat.comp_apply,
      ← GenLoop.hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom, ModuleCat.comp_apply,
      singularHomologyIsoOfSubsetSingleton_hom]
    -- The sides differ only in the spellings `ConcreteCategory.hom`/`ModuleCat.Hom.hom` of the
    -- application, the degree `n + 1 + 1`/`n + 2` and the abbreviation `Q`.
    rfl
  -- The two Hurewicz classes of `γ` differ by the sign `ε`.
  have h : Q.singularHomologyπ (ModuleCat.of ℤ ℤ) (n + 2)
      ((GenLoop.hurewicz (ModuleCat.of ℤ ℤ) γ).hom 1) =
        (ε : ℤ) • Q.singularHomologyπ (ModuleCat.of ℤ ℤ) (n + 2)
          ((singularCubicalHomologyIso ℤ _ (n + 2)).inv (GenLoop.cubicalHurewicz ℤ γ)) := by
    have h := hε _ _ (⟦γ⟧ : HomotopyGroup (Fin (n + 2)) _ _)
    rw [HomotopyGroup.hurewicz_mk, HomotopyGroup.cubicalHurewicz_mk] at h
    rw [h]
    exact map_zsmul _ _ _
  refine ⟨ε⁻¹, (ConcreteCategory.bijective_of_isIso φ).1 ?_⟩
  rw [singularHomologyMap_sphereGenLoop_cubeBoundaryPairCycle, map_zsmul, hg, h, smul_smul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-- Over `ℤ` and in dimension `n + 2 ≥ 2`, `a ↦ a • [Iⁿ⁺²]` is bijective onto
`Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; ℤ)`; `TauCeti.bijective_zsmul_homologyπ_cubeBoundaryPairCycle` adds dimension
one. -/
private lemma bijective_zsmul_homologyπ_cubeBoundaryPairCycle_add_two (n : ℕ) :
    Function.Bijective fun a : ℤ ↦ a • ((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex
      ℤ).homologyπ (n + 2) (cubeBoundaryPairCycle ℤ (n + 1)) := by
  obtain ⟨ε, hε⟩ :=
    exists_singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_eq_units_smul n
  let e := TopPair.singularCubicalHomologyIso ℤ (cubeBoundaryPair.{0} (n + 2)) (n + 2)
  let g := singularHomologyCubeBoundaryPairIso (ModuleCat.of ℤ ℤ) (n + 2)
  -- The map is `a ↦ e.hom (g.inv (ε * a))`, a composite of bijections.
  have key (a : ℤ) : a • ((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex ℤ).homologyπ
      (n + 2) (cubeBoundaryPairCycle ℤ (n + 1)) = e.hom (g.inv ((ε : ℤ) * a)) := by
    apply (ConcreteCategory.bijective_of_isIso e.inv).1
    rw [Iso.hom_inv_id_apply, map_zsmul, hε, smul_smul, ← map_zsmul, smul_eq_mul, mul_one,
      mul_comm]
  rw [funext key]
  exact (ConcreteCategory.bijective_of_isIso e.hom).comp
    ((ConcreteCategory.bijective_of_isIso g.inv).comp (Units.mulLeft ε).bijective)

/-! ### The fundamental cycle of the boundary -/

/-- A face of the identity cube of `Iᵐ⁺¹` at a parameter `t ∈ {0, 1}` takes its values in the
boundary `∂Iᵐ⁺¹`. -/
lemma face_upCube_mem_range_cubeBoundaryPair_map {m : ℕ} (i : Fin (m + 1)) {t : I}
    (ht : t = 0 ∨ t = 1) (x : Fin m → I) :
    SingularCube.face i t
        (upCube.{u} (m + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1)).fst (m + 1)) x ∈
      range (cubeBoundaryPair.{u} (m + 1)).map := by
  rw [TopPair.range_ofSubset_map]
  exact ⟨i, by simpa [upCube] using ht⟩

/-- The face `SingularCube.face i t` of the identity cube of `Iᵐ⁺¹`, for `t ∈ {0, 1}`, as a
singular cube of the boundary `∂Iᵐ⁺¹`. -/
def cubeBoundaryFace {m : ℕ} (i : Fin (m + 1)) {t : I} (ht : t = 0 ∨ t = 1) :
    SingularCube (cubeBoundaryPair.{u} (m + 1)).snd m :=
  (cubeBoundaryPair.{u} (m + 1)).liftSnd _ (face_upCube_mem_range_cubeBoundaryPair_map i ht)

/-- Read in `Iᵐ⁺¹`, the cube `TauCeti.cubeBoundaryFace i ht` is the face `SingularCube.face i t`
of the identity cube. -/
theorem map_comp_cubeBoundaryFace {m : ℕ} (i : Fin (m + 1)) {t : I} (ht : t = 0 ∨ t = 1) :
    (cubeBoundaryPair.{u} (m + 1)).map.hom.comp (cubeBoundaryFace i ht) =
      SingularCube.face i t
        (upCube.{u} (m + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1)).fst (m + 1)) :=
  ContinuousMap.ext fun x ↦
    TopPair.map_liftSnd _ (face_upCube_mem_range_cubeBoundaryPair_map i ht) x

/-- The **fundamental chain of the boundary** `∂Iᵐ⁺¹`: the signed sum
`Σᵢ (-1)ⁱ ([face i 0] - [face i 1])` of the faces of the identity cube, as a normalized cubical
chain of `∂Iᵐ⁺¹`. -/
def cubeBoundaryChain (m : ℕ) : NormalizedCubicalChain (cubeBoundaryPair.{u} (m + 1)).snd k m :=
  ∑ i : Fin (m + 1), (-1 : k) ^ (i : ℕ) •
    (NormalizedCubicalChain.ofCube _ k (cubeBoundaryFace i (Or.inl rfl)) -
      NormalizedCubicalChain.ofCube _ k (cubeBoundaryFace i (Or.inr rfl)))

theorem cubeBoundaryChain_def (m : ℕ) :
    cubeBoundaryChain k m = ∑ i : Fin (m + 1), (-1 : k) ^ (i : ℕ) •
      (NormalizedCubicalChain.ofCube _ k (cubeBoundaryFace.{u} i (Or.inl rfl)) -
        NormalizedCubicalChain.ofCube _ k (cubeBoundaryFace.{u} i (Or.inr rfl))) :=
  (rfl)

/-- Read in `Iᵐ⁺¹`, the fundamental chain of `∂Iᵐ⁺¹` is the boundary of the identity cube. -/
theorem map_cubeBoundaryChain (m : ℕ) :
    NormalizedCubicalChain.map k (cubeBoundaryPair.{u} (m + 1)).map.hom m (cubeBoundaryChain k m) =
      NormalizedCubicalChain.boundary _ k m
        (NormalizedCubicalChain.ofCube _ k
          (upCube.{u} (m + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1)).fst (m + 1))) := by
  simp only [cubeBoundaryChain, map_sum, map_smul, map_sub, NormalizedCubicalChain.map_ofCube,
    map_comp_cubeBoundaryFace, NormalizedCubicalChain.boundary_ofCube]
  -- The two sides differ only in the spelling `P.fst`/`ULift (Iᵐ⁺¹)` of the ambient space.
  rfl

/-- The fundamental chain of `∂Iᵐ⁺²` is a cycle. -/
theorem boundary_cubeBoundaryChain (m : ℕ) :
    NormalizedCubicalChain.boundary _ k m (cubeBoundaryChain k (m + 1)) = 0 := by
  apply NormalizedCubicalChain.map_injective k (cubeBoundaryPair.{u} (m + 2)).map.hom
    (cubeBoundaryPair.{u} (m + 2)).isEmbedding_map.injective m
  rw [map_zero, ← LinearMap.comp_apply, NormalizedCubicalChain.map_boundary, LinearMap.comp_apply,
    map_cubeBoundaryChain]
  exact LinearMap.congr_fun (NormalizedCubicalChain.boundary_boundary _ m) _

/-- The fundamental chain of `∂Iᵐ⁺¹` is killed by every differential of the normalized cubical
chain complex, in every degree. -/
private lemma d_cubeBoundaryChain (m j : ℕ) :
    ((normalizedCubicalChainComplex k).obj (cubeBoundaryPair.{u} (m + 1)).snd).d m j
      ((normalizedCubicalChainComplexXEquiv _ m).symm (cubeBoundaryChain k m)) = 0 := by
  cases m with
  | zero =>
    rw [HomologicalComplex.shape _ _ _ (by simp)]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
  | succ m =>
    by_cases hj : j = m
    · subst hj
      apply (normalizedCubicalChainComplexXEquiv _ j).injective
      rw [normalizedCubicalChainComplexXEquiv_d_apply, LinearEquiv.apply_symm_apply,
        boundary_cubeBoundaryChain, map_zero]
    · rw [HomologicalComplex.shape _ _ _ (by simpa using hj)]
      simp only [ModuleCat.hom_zero, LinearMap.zero_apply]

/-- The **fundamental cycle of the boundary** `∂Iᵐ⁺¹`: the fundamental chain
`TauCeti.cubeBoundaryChain`, as a cycle of the normalized cubical chains of `∂Iᵐ⁺¹`. -/
def cubeBoundaryCycle (m : ℕ) :
    ((normalizedCubicalChainComplex k).obj (cubeBoundaryPair.{u} (m + 1)).snd).cycles m :=
  HomologicalComplex.moduleCatCyclesMk _
    ((normalizedCubicalChainComplexXEquiv _ m).symm (cubeBoundaryChain k m)) _ rfl
    (d_cubeBoundaryChain k m _)

@[simp]
theorem iCycles_cubeBoundaryCycle (m : ℕ) :
    ((normalizedCubicalChainComplex k).obj (cubeBoundaryPair.{u} (m + 1)).snd).iCycles m
        (cubeBoundaryCycle k m) =
      (normalizedCubicalChainComplexXEquiv _ m).symm (cubeBoundaryChain k m) :=
  HomologicalComplex.iCycles_moduleCatCyclesMk ..

/-- **The connecting morphism sends the fundamental class of the cube to that of its boundary.**
The connecting morphism `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ Hₘ(∂Iᵐ⁺¹)` of relative cubical homology sends the
class of the fundamental cycle `TauCeti.cubeBoundaryPairCycle` of the cube pair to the class of
the fundamental cycle `TauCeti.cubeBoundaryCycle` of the boundary. -/
theorem cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle (m : ℕ) :
    ((cubeBoundaryPair.{u} (m + 1)).cubicalHomologyδ k (m + 1) m).hom
        (((cubeBoundaryPair.{u} (m + 1)).cubicalChainComplex k).homologyπ (m + 1)
          (cubeBoundaryPairCycle k m)) =
      ((normalizedCubicalChainComplex k).obj (cubeBoundaryPair.{u} (m + 1)).snd).homologyπ m
        (cubeBoundaryCycle k m) := by
  rw [TopPair.cubicalHomologyδ_def k _ (m + 1) m]
  refine ShortComplex.ShortExact.moduleCat_δ_homologyπ
    (TopPair.shortExact_cubicalChainComplexShortComplex k _) (m + 1) m rfl _
    ((normalizedCubicalChainComplexXEquiv (cubeBoundaryPair.{u} (m + 1)).fst (m + 1)).symm
      (NormalizedCubicalChain.ofCube (cubeBoundaryPair.{u} (m + 1)).fst k (upCube.{u} (m + 1))))
    ?_ _ ?_
  · rw [cubeBoundaryPairCycle]
    exact (TopPair.cubicalChainOfCube_def k _).symm.trans
      (TopPair.iCycles_cubicalCycleOfCube k _ _).symm
  · rw [iCycles_cubeBoundaryCycle]
    exact (normalizedCubicalChainComplex_map_f_apply _ m _).trans
      ((map_cubeBoundaryChain k m).trans (normalizedCubicalChainComplex_obj_d_apply _ m _).symm)

/-- The normalized cubical homology of the cube `Iᵐ⁺¹` vanishes in positive degrees, since the
cube is contractible. -/
private lemma isZero_homology_cubeBoundaryPair_fst (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    IsZero (((normalizedCubicalChainComplex k).obj (cubeBoundaryPair.{u} (m + 1)).fst).homology
      n) :=
  (isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of k k) _ hn).of_iso
    (singularCubicalHomologyIso k _ n).symm

/-- The connecting morphism `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ Hₘ(∂Iᵐ⁺¹)` of relative cubical homology is
injective, since the cube is contractible. -/
theorem injective_cubicalHomologyδ_cubeBoundaryPair (m : ℕ) :
    Function.Injective ((cubeBoundaryPair.{u} (m + 1)).cubicalHomologyδ k (m + 1) m).hom :=
  (ModuleCat.mono_iff_injective _).1
    (((cubeBoundaryPair.{u} (m + 1)).cubicalHomology_exact_relative k (m + 1) m).mono_g
      ((isZero_homology_cubeBoundaryPair_fst k m (Nat.succ_ne_zero m)).eq_of_src _ _))

/-- The connecting morphism `Hₘ₊₂(Iᵐ⁺², ∂Iᵐ⁺²) ⟶ Hₘ₊₁(∂Iᵐ⁺²)` of relative cubical homology is
surjective, since the cube is contractible. -/
theorem surjective_cubicalHomologyδ_cubeBoundaryPair (m : ℕ) :
    Function.Surjective
      ((cubeBoundaryPair.{u} (m + 2)).cubicalHomologyδ k (m + 2) (m + 1)).hom :=
  (ModuleCat.epi_iff_surjective _).1
    (((cubeBoundaryPair.{u} (m + 2)).cubicalHomology_exact_subspace k (m + 2) (m + 1)).epi_f
      ((isZero_homology_cubeBoundaryPair_fst k (m + 1) (Nat.succ_ne_zero m)).eq_of_tgt _ _))

/-- The connecting morphism `Hₘ₊₂(Iᵐ⁺², ∂Iᵐ⁺²) ⟶ Hₘ₊₁(∂Iᵐ⁺²)` of relative cubical homology is an
isomorphism, since the cube is contractible. -/
theorem isIso_cubicalHomologyδ_cubeBoundaryPair (m : ℕ) :
    IsIso ((cubeBoundaryPair.{u} (m + 2)).cubicalHomologyδ k (m + 2) (m + 1)) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ⟨injective_cubicalHomologyδ_cubeBoundaryPair k (m + 1),
      surjective_cubicalHomologyδ_cubeBoundaryPair k m⟩

/-! ### Dimension one -/

/-- In dimension one, the face `TauCeti.cubeBoundaryFace 0 ht` of the identity cube of `I¹` is the
point cube at the endpoint `TauCeti.cubeEnd t ht`. -/
private lemma cubeBoundaryFace_zero {t : I} (ht : t = 0 ∨ t = 1) :
    cubeBoundaryFace.{u} (m := 0) 0 ht = SingularCube.point (cubeEnd.{u} t ht) := by
  refine ContinuousMap.ext fun x ↦ (TopPair.liftSnd_apply_eq_iff _ _ x _).2 ?_
  rw [SingularCube.point_apply, map_cubeEnd]
  -- The face is spelled on `(cubeBoundaryPair 1).fst` rather than `cubeModel 1`, so
  -- `SingularCube.face_apply` is applied by unification rather than by rewriting.
  refine (SingularCube.face_apply 0 t (upCube 1) x).trans (ULift.ext (funext fun i ↦ ?_))
  obtain rfl : i = 0 := Fin.fin_one_eq_zero i
  simp [cubePoint_down, upCube]

/-- **In dimension one the fundamental cycle of the cube pair is the singular generator**, over
every ring `k`: the class of `TauCeti.cubeBoundaryPairCycle k 0` in `H₁(I¹, ∂I¹; k)`, read in
relative singular homology, is the generator `TauCeti.singularHomologyCubeBoundaryPairIso` of
`H₁(I¹, ∂I¹; k) ≅ k`, with no sign. Both classes have boundary `[0] - [1]` in `H₀(∂I¹; k)`. -/
theorem singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_zero :
    (TopPair.singularCubicalHomologyIso k (cubeBoundaryPair.{u} 1) 1).inv
        (((cubeBoundaryPair.{u} 1).cubicalChainComplex k).homologyπ 1 (cubeBoundaryPairCycle k 0)) =
      (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) 1).inv (1 : k) := by
  let P := cubeBoundaryPair.{u} 1
  apply (ConcreteCategory.bijective_of_isIso (TopPair.singularCubicalHomologyIso k P 1).hom).1
  rw [Iso.inv_hom_id_apply]
  apply injective_cubicalHomologyδ_cubeBoundaryPair k 0
  have key : (TopPair.singularCubicalHomologyIso k P 1).hom ≫ P.cubicalHomologyδ k 1 0 =
      P.singularHomologyδ (ModuleCat.of k k) 1 0 ≫ (singularCubicalHomologyIso k P.snd 0).hom :=
    TopPair.singularCubicalHomologyIso_hom_cubicalHomologyδ k P 1 0
  -- The singular connecting morphism sends the generator to `[0] - [1]`.
  have hδ : (singularCubicalHomologyIso k P.snd 0).hom
      ((P.singularHomologyδ (ModuleCat.of k k) 1 0).hom
        ((singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) 1).inv (1 : k))) =
        (singularCubicalHomologyIso k P.snd 0).hom
            ((singularHomology₀Section (ModuleCat.of k k) (cubeEnd.{u} 0 (Or.inl rfl))).hom 1) -
          (singularCubicalHomologyIso k P.snd 0).hom
            ((singularHomology₀Section (ModuleCat.of k k) (cubeEnd.{u} 1 (Or.inr rfl))).hom 1) :=
    (congrArg (singularCubicalHomologyIso k P.snd 0).hom.hom (ConcreteCategory.congr_hom
      (singularHomologyCubeBoundaryPairIso_one_inv_singularHomologyδ.{u} (ModuleCat.of k k))
        (1 : k))).trans (map_sub _ _ _)
  rw [cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle, ← ModuleCat.comp_apply, key]
  refine Eq.trans ?_ hδ.symm
  rw [singularCubicalHomologyIso_hom_singularHomology₀Section,
    singularCubicalHomologyIso_hom_singularHomology₀Section, ← map_sub]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_cubeBoundaryCycle, map_sub, iCycles_cubicalCycleOfPoint, iCycles_cubicalCycleOfPoint]
  simp only [cubeBoundaryChain, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero, Fin.val_zero, pow_zero, one_smul, cubeBoundaryFace_zero, map_sub]

/-- **The fundamental cycle of `I¹` generates `H₁(I¹, ∂I¹; k)`**, over every ring `k`:
`a ↦ a • [I¹]` is bijective, where `[I¹]` is the class of `TauCeti.cubeBoundaryPairCycle k 0`. -/
theorem bijective_smul_homologyπ_cubeBoundaryPairCycle_zero :
    Function.Bijective fun a : k ↦
      a • ((cubeBoundaryPair.{u} 1).cubicalChainComplex k).homologyπ 1
        (cubeBoundaryPairCycle k 0) := by
  let e := TopPair.singularCubicalHomologyIso k (cubeBoundaryPair.{u} 1) 1
  let g := singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) 1
  -- The map is `a ↦ e.hom (g.inv a)`, a composite of bijections.
  have key (a : k) : a • ((cubeBoundaryPair.{u} 1).cubicalChainComplex k).homologyπ 1
      (cubeBoundaryPairCycle k 0) = e.hom (g.inv a) := by
    apply (ConcreteCategory.bijective_of_isIso e.inv).1
    rw [Iso.hom_inv_id_apply, map_smul,
      singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_zero, ← map_smul, smul_eq_mul,
      mul_one]
  rw [funext key]
  exact (ConcreteCategory.bijective_of_isIso e.hom).comp
    (ConcreteCategory.bijective_of_isIso g.inv)

/-- **The fundamental cycle generates the relative cubical homology of the cube pair.** Over `ℤ`
and in every dimension `m + 1 ≥ 1`, `a ↦ a • [Iᵐ⁺¹]` is bijective onto `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; ℤ)`,
where `[Iᵐ⁺¹]` is the class of the fundamental cycle `TauCeti.cubeBoundaryPairCycle`. -/
theorem bijective_zsmul_homologyπ_cubeBoundaryPairCycle (m : ℕ) :
    Function.Bijective fun a : ℤ ↦ a • ((cubeBoundaryPair.{0} (m + 1)).cubicalChainComplex
      ℤ).homologyπ (m + 1) (cubeBoundaryPairCycle ℤ m) := by
  cases m with
  | zero =>
    convert bijective_smul_homologyπ_cubeBoundaryPairCycle_zero ℤ using 2 with a
    rw [← Int.cast_smul_eq_zsmul ℤ, Int.cast_id]
  | succ n => exact bijective_zsmul_homologyπ_cubeBoundaryPairCycle_add_two n

/-- **The relative cubical homology of the cube pair is free on the fundamental cycle**: the
isomorphism `ℤ ≃ₗ[ℤ] Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; ℤ)` of relative normalized cubical homology sending `a` to
`a • [Iᵐ⁺¹]` (`TauCeti.cubicalHomologyCubeBoundaryPairEquiv_apply`). -/
def cubicalHomologyCubeBoundaryPairEquiv (m : ℕ) :
    ℤ ≃ₗ[ℤ] ((cubeBoundaryPair.{0} (m + 1)).cubicalChainComplex ℤ).homology (m + 1) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ
    (((cubeBoundaryPair.{0} (m + 1)).cubicalChainComplex ℤ).homology (m + 1))
    (((cubeBoundaryPair.{0} (m + 1)).cubicalChainComplex ℤ).homologyπ (m + 1)
      (cubeBoundaryPairCycle ℤ m)))
    (by
      convert bijective_zsmul_homologyπ_cubeBoundaryPairCycle m using 1
      funext a
      rw [LinearMap.toSpanSingleton_apply, ← Int.cast_smul_eq_zsmul ℤ, Int.cast_id])

@[simp]
theorem cubicalHomologyCubeBoundaryPairEquiv_apply (m : ℕ) (a : ℤ) :
    cubicalHomologyCubeBoundaryPairEquiv m a =
      a • ((cubeBoundaryPair.{0} (m + 1)).cubicalChainComplex ℤ).homologyπ (m + 1)
        (cubeBoundaryPairCycle ℤ m) := by
  rw [cubicalHomologyCubeBoundaryPairEquiv, LinearEquiv.ofBijective_apply,
    LinearMap.toSpanSingleton_apply, ← Int.cast_smul_eq_zsmul ℤ, Int.cast_id]

/-! ### The fundamental cycle of the boundary generates -/

/-- **The fundamental cycle of the boundary of the cube generates its homology.** Over `ℤ` and
in dimension `m + 2 ≥ 2`, `a ↦ a • [∂Iᵐ⁺²]` is bijective onto `Hₘ₊₁(∂Iᵐ⁺²; ℤ)`, where `[∂Iᵐ⁺²]`
is the class of the fundamental cycle `TauCeti.cubeBoundaryCycle`. -/
theorem bijective_zsmul_homologyπ_cubeBoundaryCycle (m : ℕ) :
    Function.Bijective fun a : ℤ ↦ a • ((normalizedCubicalChainComplex ℤ).obj
      (cubeBoundaryPair.{0} (m + 2)).snd).homologyπ (m + 1) (cubeBoundaryCycle ℤ (m + 1)) := by
  let δ := ((cubeBoundaryPair.{0} (m + 2)).cubicalHomologyδ ℤ (m + 2) (m + 1)).hom
  have key (a : ℤ) : a • ((normalizedCubicalChainComplex ℤ).obj
      (cubeBoundaryPair.{0} (m + 2)).snd).homologyπ (m + 1) (cubeBoundaryCycle ℤ (m + 1)) =
        δ (a • ((cubeBoundaryPair.{0} (m + 2)).cubicalChainComplex ℤ).homologyπ (m + 2)
          (cubeBoundaryPairCycle ℤ (m + 1))) := by
    rw [map_zsmul, cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle]
  rw [funext key]
  exact Function.Bijective.comp ⟨injective_cubicalHomologyδ_cubeBoundaryPair ℤ (m + 1),
    surjective_cubicalHomologyδ_cubeBoundaryPair ℤ m⟩
      (bijective_zsmul_homologyπ_cubeBoundaryPairCycle (m + 1))

end TauCeti

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
cube pair (`TauCeti.cubicalHomologyCubeBoundaryPairEquiv`). This is what makes the identity cube a
fundamental chain of the cube relative to its boundary. In dimension `n + 2 ≥ 2`, read in relative
singular homology, it is `±` the generator `TauCeti.singularHomologyCubeBoundaryPairIso` of
`Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; ℤ) ≅ ℤ`
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

The boundary of the identity cube, the signed sum of the faces of `Iᵐ⁺¹`, is a cycle of `∂Iᵐ⁺¹`
(`TauCeti.cubeBoundaryCycle`), and the connecting morphism of the pair sends `[Iᵐ⁺¹]` to its class
(`TauCeti.cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle`). Since the cube is contractible, the
connecting morphism `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ Hₘ(∂Iᵐ⁺¹)` is injective
(`TauCeti.injective_cubicalHomologyδ_cubeBoundaryPair`) and, in dimension `n + 2 ≥ 2`, an
isomorphism, so over `ℤ` the class of this cycle generates `Hₙ₊₁(∂Iⁿ⁺²; ℤ) ≅ ℤ`
(`TauCeti.cubicalHomologyCubeBoundaryEquiv`): the boundary of the fundamental chain of the cube is
a fundamental cycle of its boundary, the sphere `∂Iⁿ⁺²`.

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
* `TauCeti.cubeBoundaryCycle`: the fundamental cycle of `∂Iᵐ⁺¹`, the boundary of the identity cube.
* `TauCeti.cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle`: `δ[Iᵐ⁺¹] = [∂Iᵐ⁺¹]`.
* `TauCeti.injective_cubicalHomologyδ_cubeBoundaryPair`: the connecting morphism
  `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ Hₘ(∂Iᵐ⁺¹)` is injective.
* `TauCeti.cubicalHomologyCubeBoundaryEquiv`: the isomorphism `ℤ ≃ₗ[ℤ] Hₙ₊₁(∂Iⁿ⁺²; ℤ)`,
  `a ↦ a • [∂Iⁿ⁺²]`, of cubical homology.
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

/-- The **fundamental cycle of the boundary of the cube** `∂Iᵐ⁺¹`: the boundary of the identity
cube, the signed sum `∑ᵢ (-1)ⁱ (∂ᵢ⁰ - ∂ᵢ¹)` of the faces of `Iᵐ⁺¹`, as a normalized cubical
`m`-cycle of `∂Iᵐ⁺¹` with coefficients in `k`. -/
def cubeBoundaryCycle (m : ℕ) :
    ((normalizedCubicalChainComplex k).obj (cubeBoundaryPair.{u} (m + 1)).snd).cycles m :=
  TopPair.cubicalBoundaryCycleOfCube k _ (mapsTo_upCube_boundary (m + 1))

/-- The underlying chain of the fundamental cycle of `∂Iᵐ⁺¹` is the boundary of the identity
cube, read in `∂Iᵐ⁺¹`. -/
@[simp]
theorem iCycles_cubeBoundaryCycle (m : ℕ) :
    (((normalizedCubicalChainComplex k).obj (cubeBoundaryPair.{u} (m + 1)).snd).iCycles m).hom
        (cubeBoundaryCycle k m) =
      TopPair.cubicalBoundaryChainOfCube k _ (mapsTo_upCube_boundary.{u} (m + 1)) :=
  TopPair.iCycles_cubicalBoundaryCycleOfCube ..

/-- The connecting morphism `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ Hₘ(∂Iᵐ⁺¹)` sends the class of the fundamental
cycle of the cube pair to the class of the fundamental cycle of the boundary. -/
theorem cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle (m : ℕ) :
    ((cubeBoundaryPair.{u} (m + 1)).cubicalHomologyδ k (m + 1) m).hom
        (((cubeBoundaryPair.{u} (m + 1)).cubicalChainComplex k).homologyπ (m + 1)
          (cubeBoundaryPairCycle k m)) =
      ((normalizedCubicalChainComplex k).obj (cubeBoundaryPair.{u} (m + 1)).snd).homologyπ m
        (cubeBoundaryCycle k m) :=
  TopPair.cubicalHomologyδ_homologyπ_cubicalCycleOfCube k _ _

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

/-! ### Dimension one -/

/-- In dimension one, the face `SingularCube.face 0 t` of the identity cube of `I¹`, for
`t ∈ {0, 1}` and read in `∂I¹`, is the point cube at the endpoint `TauCeti.cubeEnd t ht`. -/
private lemma liftSnd_face_upCube_zero {t : I} (ht : t = 0 ∨ t = 1)
    (h : ∀ x, SingularCube.face 0 t
      (upCube.{u} 1 : SingularCube (cubeBoundaryPair.{u} 1).fst 1) x ∈
        range (cubeBoundaryPair.{u} 1).map) :
    (cubeBoundaryPair.{u} 1).liftSnd _ h = SingularCube.point (cubeEnd.{u} t ht) := by
  refine ContinuousMap.ext fun x ↦ (TopPair.liftSnd_apply_eq_iff _ _ x _).2 ?_
  rw [SingularCube.point_apply, map_cubeEnd]
  -- The face is spelled on `(cubeBoundaryPair 1).fst` rather than `cubeModel 1`, so
  -- `SingularCube.face_apply` is applied by unification rather than by rewriting.
  refine (SingularCube.face_apply 0 t (upCube 1) x).trans (ULift.ext (funext fun i ↦ ?_))
  obtain rfl : i = 0 := Fin.fin_one_eq_zero i
  simp [cubePoint_down, upCube]

/-- In dimension one, the fundamental cycle of `∂I¹` is `[0] - [1]`, the difference of the point
cubes at the two endpoints. -/
private lemma cubicalBoundaryChainOfCube_upCube_one :
    TopPair.cubicalBoundaryChainOfCube k
        (upCube.{u} 1 : SingularCube (cubeBoundaryPair.{u} 1).fst 1) (mapsTo_upCube_boundary 1) =
      NormalizedCubicalChain.ofCube _ k (SingularCube.point (cubeEnd.{u} 0 (Or.inl rfl))) -
        NormalizedCubicalChain.ofCube _ k (SingularCube.point (cubeEnd.{u} 1 (Or.inr rfl))) := by
  refine (TopPair.cubicalBoundaryChainOfCube_def k _ _).trans ?_
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.val_zero,
    pow_zero, one_smul]
  -- The faces are spelled with the dimension `0 + 1` rather than `1`, which defeats rewriting.
  exact congrArg₂ (· - ·) (congrArg _ (liftSnd_face_upCube_zero _ _))
    (congrArg _ (liftSnd_face_upCube_zero _ _))

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
  exact cubicalBoundaryChainOfCube_upCube_one k

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

/-- **The fundamental cycle of the boundary of the cube generates its homology.** Over `ℤ`,
`a ↦ a • [∂Iⁿ⁺²]` is bijective onto `Hₙ₊₁(∂Iⁿ⁺²; ℤ)`, where `[∂Iⁿ⁺²]` is the class of
`TauCeti.cubeBoundaryCycle`. -/
theorem bijective_zsmul_homologyπ_cubeBoundaryCycle (n : ℕ) :
    Function.Bijective fun a : ℤ ↦ a • ((normalizedCubicalChainComplex ℤ).obj
      (cubeBoundaryPair.{0} (n + 2)).snd).homologyπ (n + 1) (cubeBoundaryCycle ℤ (n + 1)) := by
  -- The connecting morphism is an isomorphism, since the cube is contractible, and it carries
  -- `a • [Iⁿ⁺²]` to `a • [∂Iⁿ⁺²]`.
  let δ := (cubeBoundaryPair.{0} (n + 2)).cubicalHomologyδ ℤ (n + 2) (n + 1)
  have key (a : ℤ) : a • ((normalizedCubicalChainComplex ℤ).obj
      (cubeBoundaryPair.{0} (n + 2)).snd).homologyπ (n + 1) (cubeBoundaryCycle ℤ (n + 1)) =
      δ.hom (a • ((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex ℤ).homologyπ (n + 2)
        (cubeBoundaryPairCycle ℤ (n + 1))) := by
    rw [map_zsmul, cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle]
  rw [funext key]
  exact (ConcreteCategory.bijective_of_isIso δ).comp
    (bijective_zsmul_homologyπ_cubeBoundaryPairCycle (n + 1))

/-- **The homology of the boundary of the cube is free on its fundamental cycle**: the isomorphism
`ℤ ≃ₗ[ℤ] Hₙ₊₁(∂Iⁿ⁺²; ℤ)` of normalized cubical homology sending `a` to `a • [∂Iⁿ⁺²]`
(`TauCeti.cubicalHomologyCubeBoundaryEquiv_apply`). -/
def cubicalHomologyCubeBoundaryEquiv (n : ℕ) :
    ℤ ≃ₗ[ℤ] ((normalizedCubicalChainComplex ℤ).obj (cubeBoundaryPair.{0} (n + 2)).snd).homology
      (n + 1) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ _
    (((normalizedCubicalChainComplex ℤ).obj (cubeBoundaryPair.{0} (n + 2)).snd).homologyπ (n + 1)
      (cubeBoundaryCycle ℤ (n + 1))))
    (by
      convert bijective_zsmul_homologyπ_cubeBoundaryCycle n using 1
      funext a
      rw [LinearMap.toSpanSingleton_apply, ← Int.cast_smul_eq_zsmul ℤ, Int.cast_id])

@[simp]
theorem cubicalHomologyCubeBoundaryEquiv_apply (n : ℕ) (a : ℤ) :
    cubicalHomologyCubeBoundaryEquiv n a =
      a • ((normalizedCubicalChainComplex ℤ).obj (cubeBoundaryPair.{0} (n + 2)).snd).homologyπ
        (n + 1) (cubeBoundaryCycle ℤ (n + 1)) := by
  rw [cubicalHomologyCubeBoundaryEquiv, LinearEquiv.ofBijective_apply,
    LinearMap.toSpanSingleton_apply, ← Int.cast_smul_eq_zsmul ℤ, Int.cast_id]

end TauCeti

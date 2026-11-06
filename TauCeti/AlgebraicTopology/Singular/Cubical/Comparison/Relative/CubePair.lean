/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Cubical.Relative
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
import TauCeti.Algebra.Homology.Kronecker
import TauCeti.Algebra.Homology.PrincipalIdealRing

/-!
# The fundamental cycle of the cube pair

The identity cube `upCube (m + 1)` of `Iᵐ⁺¹` sends the boundary of the cube into `∂Iᵐ⁺¹`, so it is
a relative cycle of the normalized cubical chains of the cube pair `(Iᵐ⁺¹, ∂Iᵐ⁺¹)`
(`TauCeti.cubeBoundaryPairCycle`). A singular cube `c` of a pair `P` sending the boundary of the
cube into the subspace is a map of pairs `c : (Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ P` (`TauCeti.cubeBoundaryPairHom`),
and it sends the class of this fundamental cycle to the class of `c` in relative cubical homology
(`TauCeti.homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle`).

In dimension `n + 2 ≥ 2` the class of the fundamental cycle is a generator. With integer
coefficients, read in relative singular homology it is `±` the generator
`TauCeti.singularHomologyCubeBoundaryPairIso` of `Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; ℤ) ≅ ℤ`
(`TauCeti.exists_singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_eq_units_smul`).
Over every commutative ring `k`, `a ↦ a • [Iⁿ⁺²]` is an isomorphism from `k` onto the relative
cubical homology `Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; k)` (`TauCeti.cubicalHomologyCubeBoundaryPairEquiv`), for
instance over `𝔽₂` as well as over `ℤ`. This is what makes the identity cube a fundamental chain
of the cube relative to its boundary, for every choice of coefficients.

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

For a commutative ring `k`, the integral result produces an integral cocycle `φ` on the relative
chains with `φ [Iⁿ⁺²] = 1`: the relative chains are projective, so over the principal ideal domain
`ℤ` the relative cycles split off them. Reading the values of `φ` on cubes in `k` gives a `k`-valued
cocycle taking the value `1` on `[Iⁿ⁺²]`, because the boundary of a cube has integer coefficients.
Since `Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; k) ≅ k`, a functional to `k` with value `1` on `[Iⁿ⁺²]` forces `[Iⁿ⁺²]` to
correspond to a unit of `k`.

## Main declarations

* `TauCeti.mapsTo_upCube_boundary`: the identity cube sends the boundary of the cube into the
  subspace of the cube pair.
* `TauCeti.cubeBoundaryPairCycle`: the fundamental relative cycle of the cube pair.
* `TauCeti.homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle`: `c_*[Iᵐ⁺¹] = [c]` in relative
  cubical homology.
* `TauCeti.exists_singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_eq_units_smul`:
  the fundamental cycle is `±` the singular generator of `Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; ℤ)`.
* `TauCeti.bijective_smul_homologyπ_cubeBoundaryPairCycle`,
  `TauCeti.cubicalHomologyCubeBoundaryPairEquiv`: the isomorphism
  `k ≃ₗ[k] Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; k)`, `a ↦ a • [Iⁿ⁺²]`, of relative cubical homology over a commutative
  ring `k`.

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

/-! ### The fundamental cycle generates over every commutative ring -/

/-- An integral cocycle detecting the fundamental class of the cube pair: a homomorphism from the
relative integral `(n + 2)`-chains to `ℤ` that vanishes on boundaries and takes the value `1` on the
identity cube. -/
private lemma exists_intCocycle (n : ℕ) :
    ∃ φ : ((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex ℤ).X (n + 2) →ₗ[ℤ] ℤ,
      (∀ x, φ (((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex ℤ).d (n + 3) (n + 2) x) = 0) ∧
        φ (TopPair.cubicalChainOfCube ℤ
          (upCube.{0} (n + 2) : SingularCube (cubeBoundaryPair.{0} (n + 2)).fst (n + 2))) = 1 := by
  obtain ⟨ε, hε⟩ :=
    exists_singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_eq_units_smul n
  let K := (cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex ℤ
  -- Read in relative singular homology `≅ ℤ`, the fundamental class is `ε`, so `τ = ε • (e⁻¹ ≫ g)`
  -- sends it to `ε * ε = 1`.
  let τ : K.homology (n + 2) →ₗ[ℤ] ℤ := (ε : ℤ) •
    ((TopPair.singularCubicalHomologyIso ℤ (cubeBoundaryPair.{0} (n + 2)) (n + 2)).inv ≫
      (singularHomologyCubeBoundaryPairIso (ModuleCat.of ℤ ℤ) (n + 2)).hom).hom
  have hτ : τ (K.homologyπ (n + 2) (cubeBoundaryPairCycle ℤ (n + 1))) = 1 := by
    rw [LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply, hε, map_zsmul,
      Iso.inv_hom_id_apply, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
      one_smul]
  -- The relative cycles split off the relative chains.
  let ρ := retraction (K.iCycles (n + 2))
  have hρ (z : K.cycles (n + 2)) : ρ (K.iCycles (n + 2) z) = z := by
    rw [← ModuleCat.comp_apply, IsSplitMono.id, ModuleCat.id_apply]
  refine ⟨τ ∘ₗ (K.homologyπ (n + 2)).hom ∘ₗ ρ.hom, fun y ↦ ?_, ?_⟩
  · -- A boundary is the image of a cycle whose class vanishes.
    have hd : K.d (n + 3) (n + 2) y = K.iCycles (n + 2) (K.toCycles (n + 3) (n + 2) y) := by
      rw [← ModuleCat.comp_apply, K.toCycles_i]
    have hπ : K.homologyπ (n + 2) (K.toCycles (n + 3) (n + 2) y) = 0 := by
      rw [← ModuleCat.comp_apply, K.toCycles_comp_homologyπ]
      simp
    rw [hd, LinearMap.comp_apply, LinearMap.comp_apply, hρ, hπ, map_zero]
  · have hc : TopPair.cubicalChainOfCube ℤ
          (upCube.{0} (n + 2) : SingularCube (cubeBoundaryPair.{0} (n + 2)).fst (n + 2)) =
        K.iCycles (n + 2) (cubeBoundaryPairCycle ℤ (n + 1)) :=
      (TopPair.iCycles_cubicalCycleOfCube ℤ _ _).symm
    rw [hc, LinearMap.comp_apply, LinearMap.comp_apply, hρ, hτ]

variable (k : Type) [CommRing k]

/-- A `k`-valued cocycle detecting the fundamental class of the cube pair: a morphism from the
relative `(n + 2)`-chains with coefficients in `k` to `k` that vanishes on boundaries and takes the
value `1` on the identity cube. On a cube it takes the value in `k` of the integral cocycle of
`exists_intCocycle`. -/
private lemma exists_cocycle (n : ℕ) :
    ∃ ψ : ((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex k).X (n + 2) ⟶ ModuleCat.of k k,
      ((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex k).d (n + 3) (n + 2) ≫ ψ = 0 ∧
        ψ (TopPair.cubicalChainOfCube k
          (upCube.{0} (n + 2) : SingularCube (cubeBoundaryPair.{0} (n + 2)).fst (n + 2))) = 1 := by
  obtain ⟨φ, hφd, hφ⟩ := exists_intCocycle n
  -- The integer values of `φ` on cubes, read in `k`.
  let g : SingularCube (cubeBoundaryPair.{0} (n + 2)).fst (n + 2) → k :=
    fun c ↦ (φ (TopPair.cubicalChainOfCube ℤ c) : k)
  have hg (c : SingularCube (cubeBoundaryPair.{0} (n + 2)).fst (n + 2))
      (hc : SingularCube.IsDegenerate c) : g c = 0 := by
    simp only [g, TopPair.cubicalChainOfCube_eq_zero ℤ hc, map_zero, Int.cast_zero]
  let ψ₀ : NormalizedCubicalChain (cubeBoundaryPair.{0} (n + 2)).fst k (n + 2) →ₗ[k] k :=
    NormalizedCubicalChain.desc g hg
  have hψ₀ : ψ₀ ∘ₗ NormalizedCubicalChain.map k (cubeBoundaryPair.{0} (n + 2)).map.hom (n + 2) =
      0 :=
    NormalizedCubicalChain.linearMap_ext fun c ↦ by
      simp only [ψ₀, g, LinearMap.comp_apply, NormalizedCubicalChain.map_ofCube,
        NormalizedCubicalChain.desc_ofCube, TopPair.cubicalChainOfCube_comp_map, map_zero,
        Int.cast_zero, LinearMap.zero_apply]
  -- `ψ₀` vanishes on boundaries: on the boundary of a cube it is the cocycle condition of `φ`, read
  -- in `k`.
  have hψ₀d (y : NormalizedCubicalChain (cubeBoundaryPair.{0} (n + 2)).fst k (n + 3)) :
      ψ₀ (NormalizedCubicalChain.boundary _ k (n + 2) y) = 0 := by
    induction y using NormalizedCubicalChain.induction_on with
    | zero => rw [map_zero, map_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
    | smul r a ha => rw [map_smul, map_smul, ha, smul_zero]
    | ofCube c =>
      have h := congrArg (fun z : ℤ ↦ (z : k)) (hφd (TopPair.cubicalChainOfCube ℤ c))
      simp only [TopPair.d_cubicalChainOfCube_eq_sum, map_sum, map_sub, map_smul, smul_eq_mul,
        Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_sub,
        Int.cast_zero] at h
      simpa [ψ₀, g, NormalizedCubicalChain.boundary_ofCube] using h
  refine ⟨ModuleCat.ofHom (TopPair.cubicalChainComplexXDesc k ψ₀ hψ₀), ?_, ?_⟩
  · -- The relative chains are a quotient of the chains of the cube.
    rw [← cancel_epi ((cokernel.π ((normalizedCubicalChainComplex k).map
      (cubeBoundaryPair.{0} (n + 2)).map)).f (n + 3)), comp_zero, HomologicalComplex.Hom.comm_assoc]
    ext y
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.ofHom_apply,
      TopPair.cubicalChainComplexXDesc_π]
    exact (congrArg ψ₀ (normalizedCubicalChainComplex_obj_d_apply _ _ y)).trans (hψ₀d y)
  · -- The identity cube is typed in the cube model, so the evaluation lemmas are applied directly.
    rw [ModuleCat.ofHom_apply]
    refine (TopPair.cubicalChainComplexXDesc_cubicalChainOfCube k ψ₀ hψ₀ _).trans ?_
    refine (NormalizedCubicalChain.desc_ofCube g hg _).trans ?_
    exact (congrArg (fun z : ℤ ↦ (z : k)) hφ).trans Int.cast_one

/-- **The fundamental cycle generates the relative cubical homology of the cube pair**, over every
commutative ring `k`: `a ↦ a • [Iⁿ⁺²]` is bijective onto `Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; k)`, where `[Iⁿ⁺²]` is
the class of the fundamental cycle `TauCeti.cubeBoundaryPairCycle`. -/
theorem bijective_smul_homologyπ_cubeBoundaryPairCycle (n : ℕ) :
    Function.Bijective fun a : k ↦ a • ((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex
      k).homologyπ (n + 2) (cubeBoundaryPairCycle k (n + 1)) := by
  obtain ⟨ψ, hψd, hψ⟩ := exists_cocycle k n
  let K := (cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex k
  let x := K.homologyπ (n + 2) (cubeBoundaryPairCycle k (n + 1))
  -- The morphism `Ψ : Hₙ₊₂ ⟶ k` induced by the cocycle `ψ`, with `Ψ x = 1`.
  have hψd' : K.d ((ComplexShape.up ℕ).next (n + 2)) (n + 2) ≫ ψ = 0 := by
    rwa [CochainComplex.next]
  let Ψ := ChainComplex.kronecker k K (ModuleCat.of k k) (n + 2)
    (ChainComplex.homologyClassOfComp k (ModuleCat.of k k) ψ hψd' (𝟙 _))
  have hΨ : Ψ x = 1 := by
    have h := ConcreteCategory.congr_hom
      (ChainComplex.homologyπ_kronecker_homologyClassOfComp (k := k) ψ hψd'
        (𝟙 (ModuleCat.of k k)))
      (cubeBoundaryPairCycle k (n + 1))
    have hc : K.iCycles (n + 2) (cubeBoundaryPairCycle k (n + 1)) =
        TopPair.cubicalChainOfCube k
          (upCube.{0} (n + 2) : SingularCube (cubeBoundaryPair.{0} (n + 2)).fst (n + 2)) :=
      TopPair.iCycles_cubicalCycleOfCube k _ _
    rw [Category.comp_id, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hc, hψ] at h
    exact h
  -- `Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; k) ≅ k` through relative singular homology.
  let e : K.homology (n + 2) ≃ₗ[k] k :=
    ((TopPair.singularCubicalHomologyIso k _ (n + 2)).symm ≪≫
      singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (n + 2)).toLinearEquiv
  -- `e x` is a unit of `k`, with inverse `Ψ (e⁻¹ 1)`.
  have hu : e x * Ψ (e.symm 1) = 1 := by
    rw [← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply,
      hΨ]
  let u : kˣ := ⟨e x, Ψ (e.symm 1), hu, by rw [mul_comm, hu]⟩
  have hux : (u : k) = e x := rfl
  -- So `a ↦ a • x` is `a ↦ e⁻¹ (a * u)`, a composite of bijections.
  convert e.symm.bijective.comp (Units.mulRight u).bijective using 1
  funext a
  simp only [Function.comp_apply, Units.mulRight_apply, hux, ← smul_eq_mul, map_smul,
    LinearEquiv.symm_apply_apply, x, K]

/-- **The relative cubical homology of the cube pair is free on the fundamental cycle**: the
isomorphism `k ≃ₗ[k] Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; k)` of relative normalized cubical homology sending `a` to
`a • [Iⁿ⁺²]` (`TauCeti.cubicalHomologyCubeBoundaryPairEquiv_apply`), for every commutative ring
`k`. -/
def cubicalHomologyCubeBoundaryPairEquiv (n : ℕ) :
    k ≃ₗ[k] ((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex k).homology (n + 2) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton k
    (((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex k).homology (n + 2))
    (((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex k).homologyπ (n + 2)
      (cubeBoundaryPairCycle k (n + 1))))
    (bijective_smul_homologyπ_cubeBoundaryPairCycle k n)

@[simp]
theorem cubicalHomologyCubeBoundaryPairEquiv_apply (n : ℕ) (a : k) :
    cubicalHomologyCubeBoundaryPairEquiv k n a =
      a • ((cubeBoundaryPair.{0} (n + 2)).cubicalChainComplex k).homologyπ (n + 2)
        (cubeBoundaryPairCycle k (n + 1)) := by
  exact LinearEquiv.ofBijective_apply _ _

end TauCeti

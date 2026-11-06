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
# The fundamental cycle of the cube pair

The identity cube `upCube (m + 1)` of `Iᵐ⁺¹` sends the boundary of the cube into `∂Iᵐ⁺¹`, so it is
a relative cycle of the normalized cubical chains of the cube pair `(Iᵐ⁺¹, ∂Iᵐ⁺¹)`
(`TauCeti.cubeBoundaryPairCycle`). A singular cube `c` of a pair `P` sending the boundary of the
cube into the subspace is a map of pairs `c : (Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ P` (`TauCeti.cubeBoundaryPairHom`),
and it sends the class of this fundamental cycle to the class of `c` in relative cubical homology
(`TauCeti.homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle`).

In dimension one the class of the fundamental cycle is a generator over every coefficient ring
`k`: read in relative singular homology it is the generator
`TauCeti.singularHomologyCubeBoundaryPairIso` of `H₁(I¹, ∂I¹; k) ≅ k`
(`TauCeti.singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_zero`), so `a ↦ a • [I¹]`
is an isomorphism from `k` onto the relative cubical homology of `(I¹, ∂I¹)`
(`TauCeti.cubicalHomologyCubeBoundaryPairOneEquiv`). Both classes are detected by the connecting
morphism to `H₀(∂I¹)`, which is injective because `I¹` is contractible: the boundary of the
identity `1`-cube is `[0] - [1]`, and the generator is sent to `[0] - [1]` too
(`TauCeti.singularHomologyCubeBoundaryPairIso_one_inv_singularHomologyδ`).

With integer coefficients the class of the fundamental cycle is a generator in every dimension
`m + 1 ≥ 1`: read in relative singular homology it is `±` the generator of
`Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; ℤ) ≅ ℤ`
(`TauCeti.exists_singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_eq_units_smul`),
so `a ↦ a • [Iᵐ⁺¹]` is an isomorphism from `ℤ` onto the relative cubical homology of the cube pair
(`TauCeti.cubicalHomologyCubeBoundaryPairEquiv`). This is what makes the identity cube a
fundamental chain of the cube relative to its boundary.

In dimension `n + 2 ≥ 2` the proof compares both classes in the homology of the sphere
`Sⁿ⁺² = Iⁿ⁺²/∂Iⁿ⁺²`. The collapse
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
connecting morphism `Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²) ⟶ Hₙ₊₁(∂Iⁿ⁺²)` is an isomorphism, so over `ℤ` the class of
this cycle generates `Hₙ₊₁(∂Iⁿ⁺²; ℤ) ≅ ℤ` (`TauCeti.cubicalHomologyCubeBoundaryEquiv`): the boundary
of the fundamental chain of the cube is a fundamental cycle of its boundary, the sphere `∂Iⁿ⁺²`.

## Main declarations

* `TauCeti.mapsTo_upCube_boundary`: the identity cube sends the boundary of the cube into the
  subspace of the cube pair.
* `TauCeti.cubeBoundaryPairCycle`: the fundamental relative cycle of the cube pair.
* `TauCeti.homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle`: `c_*[Iᵐ⁺¹] = [c]` in relative
  cubical homology.
* `TauCeti.singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_zero`: over any ring
  `k`, the fundamental cycle of `(I¹, ∂I¹)` is the singular generator of `H₁(I¹, ∂I¹; k)`.
* `TauCeti.cubicalHomologyCubeBoundaryPairOneEquiv`: the isomorphism `k ≃ₗ[k] H₁(I¹, ∂I¹; k)`,
  `a ↦ a • [I¹]`, of relative cubical homology.
* `TauCeti.exists_singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_eq_units_smul`:
  the fundamental cycle is `±` the singular generator of `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; ℤ)`.
* `TauCeti.cubicalHomologyCubeBoundaryPairEquiv`: the isomorphism `ℤ ≃ₗ[ℤ] Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; ℤ)`,
  `a ↦ a • [Iᵐ⁺¹]`, of relative cubical homology.
* `TauCeti.cubeBoundaryCycle`: the fundamental cycle of `∂Iᵐ⁺¹`, the boundary of the identity cube.
* `TauCeti.cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle`: `δ[Iᵐ⁺¹] = [∂Iᵐ⁺¹]`.
* `TauCeti.cubicalHomologyCubeBoundaryEquiv`: the isomorphism `ℤ ≃ₗ[ℤ] Hₙ₊₁(∂Iⁿ⁺²; ℤ)`,
  `a ↦ a • [∂Iⁿ⁺²]`, of cubical homology.

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

/-! ### The fundamental cycle in dimension one -/

/-- The `0`-cycle `[0] - [1]` of the boundary `∂I¹` of the interval. -/
private def cubeEndsCycle :
    ((normalizedCubicalChainComplex k).obj (cubeBoundaryPair.{u} 1).snd).cycles 0 :=
  ((normalizedCubicalChainComplex k).obj (cubeBoundaryPair.{u} 1).snd).cycles₀Iso.inv
    ((normalizedCubicalChainComplexXEquiv _ 0).symm
      (NormalizedCubicalChain.ofCube _ k (SingularCube.point (cubeEnd.{u} 0 (Or.inl rfl))) -
        NormalizedCubicalChain.ofCube _ k (SingularCube.point (cubeEnd.{u} 1 (Or.inr rfl)))))

/-- The face of the identity cube of `I¹` at an endpoint `t` is the point `t` of `I¹`. -/
private lemma face_upCube_one (t : I) :
    SingularCube.face 0 t (upCube.{u} 1 : SingularCube (cubeBoundaryPair.{u} 1).fst 1) =
      SingularCube.point (cubePoint t) := by
  refine ContinuousMap.ext fun y ↦ (SingularCube.face_apply _ _ _ y).trans
    (Eq.trans ?_ (SingularCube.point_apply (cubePoint t) y).symm)
  refine ULift.ext ((funext fun i ↦ ?_).trans (cubePoint_down t).symm)
  obtain rfl := Subsingleton.elim i 0
  exact Fin.insertNth_apply_same (α := fun _ ↦ I) 0 t y

/-- The endpoint `t` of `∂I¹`, as a point cube of `I¹`, is the point `t` of `I¹`. -/
private lemma comp_point_cubeEnd (t : I) (ht : t = 0 ∨ t = 1) :
    (cubeBoundaryPair.{u} 1).map.hom.comp (SingularCube.point (cubeEnd t ht)) =
      SingularCube.point (cubePoint t) :=
  ContinuousMap.ext fun _ ↦ by
    rw [ContinuousMap.comp_apply, SingularCube.point_apply, SingularCube.point_apply]
    -- The inclusion of the subspace `∂I¹` of the cube pair is the subtype coercion.
    exact coe_cubeEnd t ht

/-- The connecting morphism sends the class of the fundamental cycle of `(I¹, ∂I¹)` to the class
of `[0] - [1]`: the boundary of the identity `1`-cube is its face at `0` minus its face at `1`. -/
private lemma cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle_zero :
    ((cubeBoundaryPair.{u} 1).cubicalHomologyδ k 1 0).hom
        (((cubeBoundaryPair.{u} 1).cubicalChainComplex k).homologyπ 1
          (cubeBoundaryPairCycle k 0)) =
      ((normalizedCubicalChainComplex k).obj (cubeBoundaryPair.{u} 1).snd).homologyπ 0
        (cubeEndsCycle k) := by
  rw [TopPair.cubicalHomologyδ_def k _ 1 0]
  refine (TopPair.shortExact_cubicalChainComplexShortComplex k _).moduleCat_δ_homologyπ 1 0 rfl _
    ((normalizedCubicalChainComplexXEquiv _ 1).symm (NormalizedCubicalChain.ofCube _ k
      (upCube.{u} 1 : SingularCube (cubeBoundaryPair.{u} 1).fst 1))) ?_ _ ?_
  · exact (TopPair.cubicalChainOfCube_def k _).symm.trans
      (TopPair.iCycles_cubicalCycleOfCube k _ (mapsTo_upCube_boundary 1)).symm
  · rw [cubeEndsCycle, ← ModuleCat.comp_apply
      ((normalizedCubicalChainComplex k).obj _).cycles₀Iso.inv,
      HomologicalComplex.iCyclesIso_inv_hom_id]
    refine (normalizedCubicalChainComplex_map_f_apply _ 0 _).trans
      (Eq.trans ?_ (normalizedCubicalChainComplex_obj_d_apply _ 0 _).symm)
    refine Eq.trans ?_ (NormalizedCubicalChain.boundary_ofCube (X := (cubeBoundaryPair.{u} 1).fst)
      (R := k) (upCube.{u} 1)).symm
    rw [ModuleCat.id_apply, normalizedCubicalChainComplexXEquiv_symm_apply, map_sub,
      Fin.sum_univ_one]
    simp only [NormalizedCubicalChain.map_ofCube, Fin.val_zero, pow_zero, one_smul,
      comp_point_cubeEnd]
    exact congrArg₂ (fun a b ↦ NormalizedCubicalChain.ofCube _ k a -
      NormalizedCubicalChain.ofCube _ k b) (face_upCube_one 0).symm (face_upCube_one 1).symm

/-- **The fundamental cycle of the interval is the generator, in singular homology.** Over any
ring `k`, the class of the fundamental cycle `TauCeti.cubeBoundaryPairCycle` of `(I¹, ∂I¹)`, read
in relative singular homology, is the generator `TauCeti.singularHomologyCubeBoundaryPairIso` of
`H₁(I¹, ∂I¹; k) ≅ k`. -/
theorem singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_zero :
    (TopPair.singularCubicalHomologyIso k (cubeBoundaryPair.{u} 1) 1).inv
        (((cubeBoundaryPair.{u} 1).cubicalChainComplex k).homologyπ 1
          (cubeBoundaryPairCycle k 0)) =
      (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) 1).inv (1 : k) := by
  let P := cubeBoundaryPair.{u} 1
  let z := (P.cubicalChainComplex k).homologyπ 1 (cubeBoundaryPairCycle k 0)
  let e := TopPair.singularCubicalHomologyIso k P 1
  let eA := singularCubicalHomologyIso k P.snd 0
  -- The singular connecting morphism is injective, as `I¹` is contractible.
  refine (ModuleCat.mono_iff_injective _).1
    (mono_cubeBoundaryPair_singularHomologyδ.{u} (ModuleCat.of k k)) ?_
  -- Read through the comparisons, the singular connecting morphism is the cubical one.
  have h : P.singularHomologyδ (ModuleCat.of k k) 1 0 rfl (e.inv z) =
      eA.inv (P.cubicalHomologyδ k 1 0 rfl z) := by
    have h := ConcreteCategory.congr_hom
      (TopPair.singularCubicalHomologyIso_hom_cubicalHomologyδ k P 1 0) (e.inv z)
    rw [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at h
    rw [h]
    exact (eA.hom_inv_id_apply _).symm
  have hpt (t : I) (ht : t = 0 ∨ t = 1) :=
    singularCubicalHomologyIso_inv_homologyπ_ofCube_point k (cubeEnd.{u} t ht)
  refine h.trans (Eq.trans ?_ (ConcreteCategory.congr_hom
    (singularHomologyCubeBoundaryPairIso_one_inv_singularHomologyδ (ModuleCat.of k k)) 1).symm)
  rw [cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle_zero, cubeEndsCycle, map_sub, map_sub,
    map_sub, map_sub, hpt, hpt]
  -- Both sides are `s₀[0] 1 - s₀[1] 1`, the right one written as a difference of morphisms.
  exact (LinearMap.sub_apply _ _ _).symm

/-- **The fundamental cycle generates the relative cubical homology of the interval.** Over any
ring `k`, `a ↦ a • [I¹]` is bijective onto `H₁(I¹, ∂I¹; k)`, where `[I¹]` is the class of the
fundamental cycle `TauCeti.cubeBoundaryPairCycle`. -/
theorem bijective_smul_homologyπ_cubeBoundaryPairCycle_zero :
    Function.Bijective fun a : k ↦ a • ((cubeBoundaryPair.{u} 1).cubicalChainComplex k).homologyπ 1
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
  exact (ConcreteCategory.bijective_of_isIso e.hom).comp (ConcreteCategory.bijective_of_isIso g.inv)

/-- **The relative cubical homology of the interval is free on the fundamental cycle**: over any
ring `k`, the isomorphism `k ≃ₗ[k] H₁(I¹, ∂I¹; k)` of relative normalized cubical homology sending
`a` to `a • [I¹]` (`TauCeti.cubicalHomologyCubeBoundaryPairOneEquiv_apply`). -/
def cubicalHomologyCubeBoundaryPairOneEquiv :
    k ≃ₗ[k] ((cubeBoundaryPair.{u} 1).cubicalChainComplex k).homology 1 :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton k
    (((cubeBoundaryPair.{u} 1).cubicalChainComplex k).homology 1)
    (((cubeBoundaryPair.{u} 1).cubicalChainComplex k).homologyπ 1 (cubeBoundaryPairCycle k 0)))
    (bijective_smul_homologyπ_cubeBoundaryPairCycle_zero k)

@[simp]
theorem cubicalHomologyCubeBoundaryPairOneEquiv_apply (a : k) :
    cubicalHomologyCubeBoundaryPairOneEquiv k a =
      a • ((cubeBoundaryPair.{u} 1).cubicalChainComplex k).homologyπ 1
        (cubeBoundaryPairCycle k 0) :=
  (LinearEquiv.ofBijective_apply _ _).trans (LinearMap.toSpanSingleton_apply _ _ _ _)

/-! ### The fundamental cycle generates over the integers -/

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

/-- The case `n + 2 ≥ 2` of
`TauCeti.exists_singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_eq_units_smul`,
through the sphere `Sⁿ⁺² = Iⁿ⁺²/∂Iⁿ⁺²`. -/
private lemma exists_singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_add_two
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

/-- **The fundamental cycle of the cube pair is a generator, in singular homology.** There is a
sign `ε` such that the class of the fundamental cycle `TauCeti.cubeBoundaryPairCycle` of
`(Iᵐ⁺¹, ∂Iᵐ⁺¹)`, read in relative singular homology, is `ε` times the generator
`TauCeti.singularHomologyCubeBoundaryPairIso` of `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; ℤ) ≅ ℤ`. In dimension one
the sign is `1`, over any ring
(`TauCeti.singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_zero`). -/
theorem exists_singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_eq_units_smul
    (m : ℕ) :
    ∃ ε : ℤˣ, (TopPair.singularCubicalHomologyIso ℤ (cubeBoundaryPair.{0} (m + 1)) (m + 1)).inv
        (((cubeBoundaryPair.{0} (m + 1)).cubicalChainComplex ℤ).homologyπ (m + 1)
          (cubeBoundaryPairCycle ℤ m)) =
      (ε : ℤ) • (singularHomologyCubeBoundaryPairIso (ModuleCat.of ℤ ℤ) (m + 1)).inv (1 : ℤ) := by
  cases m with
  | zero =>
    refine ⟨1, ?_⟩
    rw [Units.val_one, one_smul]
    exact singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_zero ℤ
  | succ n =>
    exact exists_singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_add_two n

/-- **The fundamental cycle generates the relative cubical homology of the cube pair.** Over `ℤ`,
`a ↦ a • [Iᵐ⁺¹]` is bijective onto `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; ℤ)`, where `[Iᵐ⁺¹]` is the class of the
fundamental cycle `TauCeti.cubeBoundaryPairCycle`. -/
theorem bijective_zsmul_homologyπ_cubeBoundaryPairCycle (m : ℕ) :
    Function.Bijective fun a : ℤ ↦ a • ((cubeBoundaryPair.{0} (m + 1)).cubicalChainComplex
      ℤ).homologyπ (m + 1) (cubeBoundaryPairCycle ℤ m) := by
  obtain ⟨ε, hε⟩ :=
    exists_singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_eq_units_smul m
  let e := TopPair.singularCubicalHomologyIso ℤ (cubeBoundaryPair.{0} (m + 1)) (m + 1)
  let g := singularHomologyCubeBoundaryPairIso (ModuleCat.of ℤ ℤ) (m + 1)
  -- The map is `a ↦ e.hom (g.inv (ε * a))`, a composite of bijections.
  have key (a : ℤ) : a • ((cubeBoundaryPair.{0} (m + 1)).cubicalChainComplex ℤ).homologyπ
      (m + 1) (cubeBoundaryPairCycle ℤ m) = e.hom (g.inv ((ε : ℤ) * a)) := by
    apply (ConcreteCategory.bijective_of_isIso e.inv).1
    rw [Iso.hom_inv_id_apply, map_zsmul, hε, smul_smul, ← map_zsmul, smul_eq_mul, mul_one,
      mul_comm]
  rw [funext key]
  exact (ConcreteCategory.bijective_of_isIso e.hom).comp
    ((ConcreteCategory.bijective_of_isIso g.inv).comp (Units.mulLeft ε).bijective)

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

/-! ### The boundary of the fundamental cycle -/

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

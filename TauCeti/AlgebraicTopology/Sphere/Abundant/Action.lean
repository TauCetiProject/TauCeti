/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.Abundant.Basic
public import TauCeti.Topology.MappingSpace.Action
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
import TauCeti.Algebra.Group.ZMultiples
import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.FirstHomology
import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Hurewicz
import TauCeti.AlgebraicTopology.Singular.ModuleChains.HomologyCross
import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
import TauCeti.Topology.MappingSpace.Sphere.PathComponent

/-!
# Abundance with 2-spheres from a group action

Let a topological group `G` act continuously on a compact oriented `d`-manifold `M`, and let
`x₀ ∈ M`. The action map

`Φ : G × Map_*(B, M) → Map(B, M)`, `(g, u) ↦ g • u`

(`TauCeti.BasedMap.actionMap`) lies over the orbit map `π : G → M`, `g ↦ g • x₀`, for evaluation
`Map(B, M) → M` at the base point of `B`. Suppose that the orbit map has continuous local sections
around every point, and that the stabilizer of `x₀` is path connected. If a class
`A ∈ H_d(G; ℤ)` satisfies `π_* A = ℓ • [M]` and a class `α` of the based mapping space satisfies
`ℓ • α ≠ 0`, then `Φ_*(A × α)` lives over the fundamental class of `M` at `x₀`
(`TauCeti.HomologicalOrientation.livesOverFundamentalClass_actionMap_singularHomologyCross`). For
`B = S²` and `α` of positive degree, `M` is therefore abundant with 2-spheres
(`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_ne_zero`).

In degree zero the second condition of Definition 6.11 asks more: the localization of `Φ_*(A × α)`
must not be that of a class of constant spheres. The self-map `f ↦ const (f(b₀))` of `Map(S², M)`
lies over `M` and fixes the constant spheres, and it sends `Φ_*(A × α)` to `Φ_*(A × c_* α)`, where
`c` is the constant self-map of `Map_*(S², M)` at the constant sphere: `g • u` and `g • const x₀`
take the same value `g • x₀` at `b₀`. So if the localization of `Φ_*(A × α)` came from the
constant spheres, `Φ_*(A × (α - c_* α))` would not live over the fundamental class
(`TauCeti.isAbundantWithTwoSpheres_of_livesOverFundamentalClass_sub`). Hence a class
`α ∈ H₀(Map_*(S², M); ℤ)` with `ℓ • (α - c_* α) ≠ 0` is a witness of abundance
(`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_sub_homologyMap_const_ne_zero`).

This gives both cases of Proposition 6.33 of the source, for a group action. If `π₂(M, x₀)` is
nontrivial, the class of a based sphere outside the path component of the constant sphere is a
witness of degree zero, for every `ℓ ≠ 0`
(`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_nontrivial_homotopyGroup_two`). If
`π₂(M, x₀)` vanishes and the first nontrivial higher homotopy group `π_k(M, x₀)`, `k ≥ 3`, has an
element `g` with `g ^ ℓ ≠ 1`, the Hurewicz image of `g` in `H_{k-2}(Ω²M; ℤ)` is a witness of
positive degree (`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_zpow_ne_one`). For
`ℓ = 1` one of the two applies as soon as some higher homotopy group `π_{k}(M, x₀)`, `k ≥ 2`, is
nontrivial, for instance when the path-connected manifold `M` is not aspherical, which is
Proposition 6.29
(`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_exists_nontrivial_homotopyGroup`).

This is the argument of Propositions 6.29 and 6.33 of Barraud–Damian–Humilière–Oancea, for
classes of diffeomorphisms coming from a group action. There the group is the identity component
of `Diff(M)`, and the source uses that its stabilizer acts trivially on the homology of `Ω²M`.
This can fail when `π₁(M)` acts nontrivially on `π₂(M)`: an isotopy from the identity to a
diffeomorphism fixing `x₀` moves `x₀` around a loop, and the diffeomorphism acts on
`π₀(Ω²M) = π₂(M)` through that loop. Here the proof uses the path-connected stabilizer only as the
fibre `π⁻¹(x₀)` of the orbit map, which makes the local homology `H_d(G, G ∖ π⁻¹(x₀))` infinite
cyclic (see below). For comparison with the source: a path-connected stabilizer also acts on the
based mapping space through maps homotopic to the identity, but the proof does not use this.

## The computation

Localizing at the fibre over `x₀` commutes with `Φ`, a map over `M`, and localizing a cross product
`A × α` for the projection `G × Map_*(B, M) → M` gives the relative cross product of the
localization of `A` with `α` (`TauCeti.fiberLocalization_singularHomologyCross_tmul`).

* **The class of `A`.** Let `s : U → G` be a section of the orbit map over an open neighbourhood
  `U` of `x₀`, and `o_U ∈ H_d(U, U ∖ {x₀})` the local orientation at `x₀`, read in `U`. The orbit
  map is a Serre fibration with path-connected fibre, so the local homology
  `H_d(G, G ∖ π⁻¹(x₀))` is infinite cyclic
  (`TauCeti.TopCat.singularHomologyComplFiberIsoOfPathConnectedSpace`). The orbit map sends it to
  `H_d(M, M ∖ {x₀})`, and sends `s_* o_U` to the local orientation at `x₀`, which has infinite
  order; so it is injective there, and the localization of `A` is `ℓ • s_* o_U`.
* **The class of `Φ_*(A × α)`.** The composite `Θ = Φ ∘ (s × id) : U × Map_*(B, M) → Map(B, M)`,
  `(x, u) ↦ s(x) • u`, is an open embedding onto the maps sending the base point into `U`, the
  inverse of the local trivialization of evaluation given by `s`
  (`TauCeti.mappingSpaceEvalTrivialization`). By excision it induces an isomorphism on local
  homology along the fibre over `x₀` (`TauCeti.isIso_localHomologyMap`), and the localization of
  `Φ_*(A × α)` is its image of the relative cross product of `o_U` with `ℓ • α`. That relative
  cross product is nonzero, since its image in `M × Map_*(B, M)` is the relative cross product of
  the local orientation, a free generator, with `ℓ • α ≠ 0`.

## Main declarations

* `TauCeti.BasedMap.actionClass`: the class `Φ_*(A × α)` with its coefficients identified with
  `ℤ`. The self-map `f ↦ const (f(b₀))` sends it to `Φ_*(A × c_* α)`
  (`TauCeti.BasedMap.homologyMap_const'_comp_mappingSpaceEval_actionClass`).

## Main results

* `TauCeti.HomologicalOrientation.livesOverFundamentalClass_actionMap_singularHomologyCross`:
  `Φ_*(A × α)` lives over the fundamental class at `x₀`.
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_ne_zero`: a manifold with such
  an action, a class `A` with `π_* A = ℓ • [M]` and a class `α` of positive degree of
  `Map_*(S², M)` with `ℓ • α ≠ 0` is abundant with 2-spheres.
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_sub_homologyMap_const_ne_zero`:
  the same for a class `α` of degree zero with `ℓ • (α - c_* α) ≠ 0`.
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_nontrivial_homotopyGroup_two`,
  `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_zpow_ne_one`: Proposition 6.33, when
  `π₂(M) ≠ 0`, or when the first nontrivial higher homotopy group is not `ℓ`-torsion.
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_exists_nontrivial_homotopyGroup`:
  Proposition 6.29, a non-aspherical manifold covered by such an action is abundant with
  2-spheres.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, Propositions 6.29 and 6.33.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory TensorProduct Module Set Topology
open scoped Topology.Homotopy

namespace TauCeti

namespace BasedMap

variable (G : Type) [TopologicalSpace G] [Group G] {M : Type} [TopologicalSpace M] [MulAction G M]
  [ContinuousSMul G M] {B : Type} [TopologicalSpace B] (b₀ : B) (x₀ : M) {d : ℕ}

/-- The class `Φ_*(A × α)` of `Map(B, M)` carried by `A ∈ H_d(G; ℤ)` and a class `α` of the based
mapping space `Map_*(B, M)` under the action map `Φ : G × Map_*(B, M) → Map(B, M)`
(`TauCeti.BasedMap.actionMap`), with the coefficients `ℤ ⊗ ℤ` of the cross product identified
with `ℤ`. For a group acting on itself, `x₀ = 1` and `A = [G]` it is the class of Example 6.30 of
Barraud–Damian–Humilière–Oancea. -/
def actionClass
    (A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)) {k : ℕ}
    (α : ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)) :
    ((TopCat.toSSet.obj (TopCat.of C(B, M))).homology (ModuleCat.of ℤ (ULift.{0} ℤ))
      (d + k) : ModuleCat.{0} ℤ) :=
  (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (actionMap (G := G) b₀ x₀)))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k)).hom
    ((HomologicalComplex.homologyMap (((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map
      (ModuleCat.uliftTensorSelfIso ℤ).hom).app
        (TopCat.toSSet.obj (TopCat.of (G × BasedMap B M b₀ x₀)))) (d + k)).hom
      ((TopCat.singularHomologyCross (TopCat.of G) (TopCat.of (BasedMap B M b₀ x₀))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
          (A ⊗ₜ α)))

/-- Unfold `TauCeti.BasedMap.actionClass`: the action map applied to the cross product `A × α`,
with the coefficients `ℤ ⊗ ℤ` identified with `ℤ`. -/
theorem actionClass_def
    (A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)) {k : ℕ}
    (α : ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)) :
    actionClass G b₀ x₀ A α =
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (actionMap (G := G) b₀ x₀)))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k)).hom
        ((HomologicalComplex.homologyMap (((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map
          (ModuleCat.uliftTensorSelfIso ℤ).hom).app
            (TopCat.toSSet.obj (TopCat.of (G × BasedMap B M b₀ x₀)))) (d + k)).hom
          ((TopCat.singularHomologyCross (TopCat.of G) (TopCat.of (BasedMap B M b₀ x₀))
            (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
              (A ⊗ₜ α))) :=
  (rfl)

/-- `Φ_*(A × α)` is additive in `α`. -/
theorem actionClass_sub
    (A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)) {k : ℕ}
    (α β : ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)) :
    actionClass G b₀ x₀ A (α - β) = actionClass G b₀ x₀ A α - actionClass G b₀ x₀ A β := by
  exact (congrArg _ ((congrArg _ (singularHomologyCross_tmul_sub _ _ rfl A α β)).trans
    (map_sub _ _ _))).trans (map_sub _ _ _)

/-- The constant maps at the values at the base point, `f ↦ const (f b₀)`, send `Φ_*(A × α)` to
`Φ_*(A × c_* α)`, where `c` is the constant self-map of `Map_*(B, M)` at the constant map at `x₀`:
both `g • u ↦ const (g • x₀)` and `(g, u) ↦ g • const x₀` agree. -/
theorem homologyMap_const'_comp_mappingSpaceEval_actionClass
    (A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)) {k : ℕ}
    (α : ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)) :
    (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
      (ContinuousMap.const'.comp (mappingSpaceEval (X := M) b₀))))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k)).hom (actionClass G b₀ x₀ A α) =
      actionClass G b₀ x₀ A ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
        (ContinuousMap.const (BasedMap B M b₀ x₀) ⟨ContinuousMap.const B x₀, rfl⟩)))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom α) := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let Y := BasedMap B M b₀ x₀
  let c : C(Y, Y) := ContinuousMap.const Y ⟨ContinuousMap.const B x₀, rfl⟩
  let Φ : C(G × Y, C(B, M)) := actionMap b₀ x₀
  let ρ : C(C(B, M), C(B, M)) := ContinuousMap.const'.comp (mappingSpaceEval b₀)
  let γ : C(G × Y, G × Y) := (ContinuousMap.id G).prodMap c
  have hΦ : ρ.comp Φ = Φ.comp γ := by
    ext ⟨g, y⟩ s
    simp only [ρ, Φ, γ, c, ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
      ContinuousMap.coe_id, ContinuousMap.const_apply, ContinuousMap.coe_const']
    rw [actionMap_apply, actionMap_apply]
    simp [y.property]
  -- The cross product with `A` is natural in the second factor: `γ_*(A × α) = A × c_* α`.
  have hcross := homologyMap_prodMap_singularHomologyCross_tmul R R (ContinuousMap.id G) c rfl A α
  simp only [TopCat.ofHom_id, CategoryTheory.Functor.map_id, SSet.homologyMap_id,
    ModuleCat.id_apply] at hcross
  -- Identify the coefficients before the maps, then commute the square `ρ ∘ Φ = Φ ∘ γ`.
  rw [actionClass, actionClass, ← hcross, homologyMap_chainComplexFunctor_map_apply _ γ
    ((TopCat.singularHomologyCross (TopCat.of G) (TopCat.of Y) R R d k (d + k) rfl).hom (A ⊗ₜ α))]
  exact ConcreteCategory.congr_hom (homologyMap_toSSet_ofHom_comp_comm R _ hΦ) _

end BasedMap

namespace HomologicalOrientation

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace V M]
  (o : HomologicalOrientation M V d) (hd : finrank ℝ V = d)
  {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [MulAction G M]
  [ContinuousSMul G M]

omit [CompactSpace M] in
include hd in
/-- **The orbit map on local homology along the stabilizer.** If the orbit map `π : G → M`,
`g ↦ g • x₀`, has continuous local sections around every point and the stabilizer of `x₀` is path
connected, then `H_d(G, G ∖ π⁻¹(x₀); ℤ)` is infinite cyclic, so the map it induces to
`H_d(M, M ∖ {x₀}; ℤ)` is injective as soon as it sends some element to an element of infinite
order. -/
private theorem injective_localHomologyMap_orbitMap {x₀ : M} (π : C(G, M))
    (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z)
    (hstab : IsPathConnected {g : G | g • x₀ = x₀})
    (z₀ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (π ⁻¹' {x₀}) d)
    (hz₀ : Function.Injective fun c : ℤ ↦ c • (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) π
      (subset_refl (π ⁻¹' {x₀})) d).hom z₀) :
    Function.Injective (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) π
      (subset_refl (π ⁻¹' {x₀})) d).hom := by
  have hπ' : TopCat.ofHom π = TopCat.ofHom ⟨fun g : G ↦ g • x₀, by fun_prop⟩ :=
    TopCat.hom_ext (ContinuousMap.ext hπ)
  have hp := hπ' ▸ orbitMap_mem_serreFibrations (G := G) x₀ hloc
  have hfib : (TopCat.ofHom π : G → M) ⁻¹' {x₀} = {g : G | g • x₀ = x₀} := by
    ext g
    simp [hπ]
  have : PathConnectedSpace ((TopCat.ofHom π : G → M) ⁻¹' {x₀}) :=
    isPathConnected_iff_pathConnectedSpace.1 (hfib ▸ hstab)
  let e := chartAt V x₀
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e x₀) (e.map_source
    (mem_chart_source V x₀))
  -- `H_d(G, G ∖ π⁻¹(x₀); ℤ) ≅ H₀(π⁻¹(x₀); ℤ) ≅ ℤ`, after replacing the coefficients `ULift ℤ`
  -- by `ℤ`.
  let φ : ModuleCat.of ℤ (ULift.{0} ℤ) ≅ ModuleCat.of ℤ ℤ :=
    (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso
  let eD : localHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) (π ⁻¹' {x₀}) d ≅ ModuleCat.of ℤ ℤ :=
    HomologicalComplex.homologyMapIso (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).mapIso
      φ).app (TopPair.toSSetPair.obj
        (TopPair.ofSubset ((π ⁻¹' {x₀})ᶜ : Set (TopCat.of G))))) d ≪≫
      eqToIso (by rw [hd]) ≪≫
      TopCat.singularHomologyComplFiberIsoOfPathConnectedSpace ℤ e (mem_chart_source V x₀) hε hε₀ hp
  exact AddMonoidHom.injective_of_addEquiv_int
    (localHomologyMap (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) π
      (subset_refl (π ⁻¹' {x₀})) d).hom.toAddMonoidHom eD.toLinearEquiv.toAddEquiv hz₀

include o hd in
/-- **The localization of a class covering `ℓ • [M]`.** In the setting of the module docstring, with
the base point `x₀` in the open set `U`, the localization of `A` at the fibre of the orbit map over
`x₀` is `ℓ • s_* o_U`, where `o_U` is the local orientation at `x₀` read in `U`. -/
private theorem fiberLocalization_orbitMap_eq {U : Set M} (hU : IsOpen U) (x₀ : U)
    (π : C(G, M)) (hπ : ∀ g, π g = g • (x₀ : M))
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • (x₀ : M) = z)
    (hstab : IsPathConnected {g : G | g • (x₀ : M) = x₀}) (s : C(U, G))
    (hs : ∀ z : U, s z • (x₀ : M) = z) (hsU : s ⁻¹' (π ⁻¹' {(x₀ : M)}) ⊆ {x₀}) {ℓ : ℤ}
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = ℓ • o.fundamentalClass hd) :
    (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) π x₀ d).hom A =
      ℓ • (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) s hsU d).hom
        ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
          hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom (o x₀).val) := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  -- The orbit map on local homology along the fibre over `x₀`.
  let πD := localHomologyMap R π (subset_refl (π ⁻¹' {(x₀ : M)})) d
  have h₁ : πD.hom ((fiberLocalization R π x₀ d).hom A) = ℓ • (o x₀).val := by
    have h := ConcreteCategory.congr_hom
      (homologyMap_comp_fiberLocalization R π (p := π) (p' := id) rfl x₀ d) A
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hA, map_zsmul,
      o.fiberLocalization_id_fundamentalClass hd] at h
    exact h.symm
  have hπs : π.comp s = ⟨Subtype.val, continuous_subtypeVal⟩ :=
    ContinuousMap.ext fun z ↦ by simp [hπ, hs]
  -- `s_* o_U`, the image of the local orientation at `x₀` under the section.
  let z₀ := (localHomologyMap R s hsU d).hom
    ((localHomologyIsoOfIsOpenEmbedding R hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom (o x₀).val)
  have h₂ : πD.hom z₀ = (o x₀).val := by
    have hc : localHomologyMap R s hsU d ≫ πD =
        localHomologyMap R ⟨Subtype.val, continuous_subtypeVal⟩
          (by rw [← hπs, ContinuousMap.coe_comp, preimage_comp]; exact hsU) d := by
      simp only [πD, localHomologyMap_comp]
      exact localHomologyMap_congr R hπs _ d
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, hc]
    exact ConcreteCategory.congr_hom (localHomologyIsoOfIsOpenEmbedding_inv_comp_localHomologyMap
      R hU.isOpenEmbedding_subtypeVal x₀ _ d) (o x₀).val
  -- The local homology of `G` along the fibre is infinite cyclic, so `πD` is injective.
  have hinj := injective_localHomologyMap_orbitMap hd π hπ hloc hstab z₀ (by
    rw [h₂]
    exact o.zsmul_left_injective hd x₀)
  have h : πD.hom ((fiberLocalization R π x₀ d).hom A) = πD.hom (ℓ • z₀) := by
    rw [map_zsmul, h₁, h₂]
  exact hinj h

omit [T2Space M] [CompactSpace M] [ChartedSpace V M] in
/-- **The translation chart of evaluation.** Let `s : U → G` be a section of the orbit map over an
open set `U ∋ x₀`. Then `Θ : U × Map_*(B, M) → Map(B, M)`, `(x, u) ↦ s(x) • u`, is an open
embedding onto the maps sending `b₀` into `U`, the inverse of the local trivialization of
evaluation given by `s` (`TauCeti.mappingSpaceEvalTrivialization`). By excision it induces an
isomorphism from the local homology along `{x₀} × Map_*(B, M)` to the local homology along the
fibre of evaluation over `x₀`. -/
private theorem isIso_localHomologyMap_actionMap_comp_prodMap [T1Space M] {B : Type}
    [TopologicalSpace B] (b₀ : B) {U : Set M} (hU : IsOpen U) (x₀ : U) (s : M → G)
    (hs : ContinuousOn s U) (hsec : ∀ z ∈ U, s z • (x₀ : M) = z) (R : ModuleCat.{0} ℤ) (n : ℕ) :
    ∃ h : ((BasedMap.actionMap (G := G) b₀ (x₀ : M)).comp
        ((⟨U.domRestrict s, hs.domRestrict⟩ : C(U, G)).prodMap
          (ContinuousMap.id (BasedMap B M b₀ (x₀ : M))))) ⁻¹' (mappingSpaceEval b₀ ⁻¹' {(x₀ : M)}) ⊆
        Prod.fst ⁻¹' {x₀},
      IsIso (localHomologyMap R ((BasedMap.actionMap (G := G) b₀ (x₀ : M)).comp
        ((⟨U.domRestrict s, hs.domRestrict⟩ : C(U, G)).prodMap
          (ContinuousMap.id (BasedMap B M b₀ (x₀ : M))))) h n) := by
  let sU : C(U, G) := ⟨U.domRestrict s, hs.domRestrict⟩
  have hsU : ∀ z : U, sU z • (x₀ : M) = z := fun z ↦ hsec z z.property
  let F := BasedMap B M b₀ (x₀ : M)
  let Θ : C(U × F, C(B, M)) := (BasedMap.actionMap (G := G) b₀ (x₀ : M)).comp
    (sU.prodMap (ContinuousMap.id F))
  have hΘapply : ∀ p : U × F, Θ p = sU p.1 • p.2.val := fun _ ↦ by simp [Θ]
  let τ := mappingSpaceEvalTrivialization b₀ (x₀ : M) U hU s hs hsec
  have hτ : U ⊆ τ.baseSet := by simp [τ]
  have hΘτ : (Θ : U × F → C(B, M)) = Subtype.val ∘ (τ.preimageHomeomorph hτ).symm :=
    funext fun p ↦ by simp [hΘapply, τ, sU]
  have hΘ : IsOpenEmbedding Θ := by
    rw [hΘτ]
    exact (hU.preimage (mappingSpaceEval b₀).continuous).isOpenEmbedding_subtypeVal.comp
      (τ.preimageHomeomorph hτ).symm.isOpenEmbedding
  have hΘF : Θ ⁻¹' (mappingSpaceEval b₀ ⁻¹' {(x₀ : M)}) = Prod.fst ⁻¹' {x₀} := by
    ext p
    simp [hΘapply, p.2.property, hsU, Subtype.ext_iff]
  have hFΘ : mappingSpaceEval b₀ ⁻¹' {(x₀ : M)} ⊆ range Θ := fun f hf ↦ by
    have hf' : f b₀ = x₀ := by simpa using hf
    refine ⟨(x₀, ⟨(sU x₀)⁻¹ • f, by
      rw [ContinuousMap.smul_apply, hf', inv_smul_eq_iff, hsU]⟩), ?_⟩
    simp [hΘapply]
  exact ⟨hΘF.subset, isIso_localHomologyMap R Θ hΘ hΘF
    (isClosed_singleton.preimage (mappingSpaceEval b₀).continuous) hFΘ n⟩

omit [CompactSpace M] in
include o hd in
/-- **The relative cross product with the local orientation is injective.** For `x₀` in an open set
`U ⊆ M` and a nonzero class `β` of a space `N`, the relative cross product of the local orientation
at `x₀`, read in `U`, with `β` is nonzero: its image in `M × N` is the relative cross product of
the local orientation of `M`, a free generator, with `β`. -/
private theorem singularHomologyCrossRel_localOrientation_ne_zero {U : Set M} (hU : IsOpen U)
    (x₀ : U) {N : Type} [TopologicalSpace N] {k : ℕ}
    {β : ((TopCat.toSSet.obj (TopCat.of N)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) k :
      ModuleCat.{0} ℤ)} (hβ : β ≠ 0) :
    (TopCat.singularHomologyCrossRel (TopCat.of U) (TopCat.of N) {x₀}ᶜ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
        ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
          hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom (o x₀).val ⊗ₜ β) ≠ 0 := by
  intro hX0
  let incl : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  have h₁ : incl ⁻¹' {(x₀ : M)} ⊆ {x₀} := fun _ hz ↦ Subtype.ext hz
  have hincl := singularHomologyCrossRel_localHomologyMap_tmul _ _ incl h₁ rfl
    ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
      hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom (o x₀).val) β
  have hoU := ConcreteCategory.congr_hom
    (localHomologyIsoOfIsOpenEmbedding_inv_comp_localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
      hU.isOpenEmbedding_subtypeVal x₀ h₁ d) (o x₀).val
  rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hoU
  rw [hoU] at hincl
  exact (map_ne_zero_iff _ ((ModuleCat.mono_iff_injective _).1 inferInstance)).2
    (o.apply_tmul_ne_zero hd x₀ hβ) (hincl.trans ((congrArg _ hX0).trans (map_zero _)))

include o hd in
/-- **Classes of the action map living over the fundamental class** (the argument of
Barraud–Damian–Humilière–Oancea, Propositions 6.29 and 6.33, for a group action). Let a
topological group `G` act on a compact oriented `d`-manifold `M` with orbit map
`π : G → M`, `g ↦ g • x₀`, which has continuous local sections around every point, and with
path-connected stabilizer of `x₀`. Let `A ∈ H_d(G; ℤ)` satisfy `π_* A = ℓ • [M]`, and let `α` be a
class of the based mapping space `Map_*(B, M)` with `ℓ • α ≠ 0`. Then the image of `A × α` under
the action map `G × Map_*(B, M) → Map(B, M)` lives over the fundamental class of `M` at `x₀`,
for evaluation at the base point `b₀` of `B`. -/
theorem livesOverFundamentalClass_actionMap_singularHomologyCross {B : Type}
    [TopologicalSpace B] (b₀ : B) {x₀ : M} (π : C(G, M)) (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z)
    (hstab : IsPathConnected {g : G | g • x₀ = x₀}) {ℓ : ℤ}
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = ℓ • o.fundamentalClass hd) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)} (hα : ℓ • α ≠ 0) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ))
      (mappingSpaceEval b₀) x₀
      ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (BasedMap.actionMap (G := G) b₀ x₀)))
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k)).hom
        ((TopCat.singularHomologyCross (TopCat.of G) (TopCat.of (BasedMap B M b₀ x₀))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
            (A ⊗ₜ α))) := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  obtain ⟨U, hU, hx₀U, s, hs, hsec⟩ := hloc x₀
  -- Work with the base point as a point of `U`.
  obtain ⟨x₀, rfl⟩ : ∃ x₀' : U, (x₀' : M) = x₀ := ⟨⟨x₀, hx₀U⟩, rfl⟩
  let sU : C(U, G) := ⟨U.domRestrict s, hs.domRestrict⟩
  have hsU : ∀ z : U, sU z • (x₀ : M) = z := fun z ↦ hsec z z.property
  have hsU' : sU ⁻¹' (π ⁻¹' {(x₀ : M)}) ⊆ {x₀} := fun z hz ↦
    Subtype.ext ((hsU z).symm.trans ((hπ _).symm.trans hz))
  let F := BasedMap B M b₀ (x₀ : M)
  let Φ := BasedMap.actionMap (G := G) b₀ (x₀ : M)
  have hΦ : mappingSpaceEval b₀ ∘ Φ = π ∘ Prod.fst := funext fun p ↦ by simp [Φ, hπ, p.2.property]
  -- `Θ = Φ ∘ (s × id)`, `(x, u) ↦ s(x) • u`, induces an isomorphism on local homology.
  let Θ : C(U × F, C(B, M)) := Φ.comp (sU.prodMap (ContinuousMap.id F))
  obtain ⟨hΘF, hΘiso⟩ := isIso_localHomologyMap_actionMap_comp_prodMap (G := G) b₀ hU x₀ s hs hsec
    (R ⊗ R : ModuleCat ℤ) (d + k)
  -- The local orientation `o_U` at `x₀`, read in `U`, and the relative cross product `X` of
  -- `o_U` with `ℓ • α`, which is nonzero.
  let oU := (localHomologyIsoOfIsOpenEmbedding R hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom
    (o x₀).val
  let X := (TopCat.singularHomologyCrossRel (TopCat.of U) (TopCat.of F) {x₀}ᶜ R R d k (d + k)
    rfl).hom (oU ⊗ₜ (ℓ • α))
  have hX : X ≠ 0 := o.singularHomologyCrossRel_localOrientation_ne_zero hd hU x₀ hα
  -- Localizing `Φ_*(A × α)` gives `Θ_* X`, and `Θ_*` is injective by excision.
  have hΦS : Φ ⁻¹' (mappingSpaceEval b₀ ⁻¹' {(x₀ : M)}) ⊆ (π ∘ Prod.fst) ⁻¹' {(x₀ : M)} := by
    rw [← preimage_comp, hΦ]
  have hsF : sU.prodMap (ContinuousMap.id F) ⁻¹' (Prod.fst ⁻¹' (π ⁻¹' {(x₀ : M)})) ⊆
      Prod.fst ⁻¹' {x₀} := fun _ hz ↦ hsU' hz
  let c := (TopCat.singularHomologyCross (TopCat.of G) (TopCat.of F) R R d k (d + k) rfl).hom
    (A ⊗ₜ α)
  have key : (fiberLocalization (R ⊗ R : ModuleCat ℤ) (mappingSpaceEval b₀) (x₀ : M) (d + k)).hom
      ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom Φ)) (R ⊗ R : ModuleCat ℤ)
        (d + k)).hom c) =
      (localHomologyMap (R ⊗ R : ModuleCat ℤ) Θ hΘF (d + k)).hom X := by
    calc _ = (localHomologyMap (R ⊗ R : ModuleCat ℤ) Φ hΦS (d + k)).hom
          ((TopCat.singularHomologyCrossRel (TopCat.of G) (TopCat.of F) (π ⁻¹' {(x₀ : M)})ᶜ R R d
            k (d + k) rfl).hom ((fiberLocalization R π (x₀ : M) d).hom A ⊗ₜ α)) :=
          (ConcreteCategory.congr_hom (homologyMap_comp_fiberLocalization (R ⊗ R : ModuleCat ℤ) Φ
            hΦ (x₀ : M) (d + k)) c).trans
              (congrArg _ (fiberLocalization_singularHomologyCross_tmul R R π (x₀ : M) rfl A α))
      _ = (localHomologyMap (R ⊗ R : ModuleCat ℤ) Φ hΦS (d + k)).hom
          ((TopCat.singularHomologyCrossRel (TopCat.of G) (TopCat.of F) (π ⁻¹' {(x₀ : M)})ᶜ R R d
            k (d + k) rfl).hom ((localHomologyMap R sU hsU' d).hom oU ⊗ₜ (ℓ • α))) := by
          rw [o.fiberLocalization_orbitMap_eq hd hU x₀ π hπ hloc hstab sU hsU hsU' hA]
          -- The `ℤ`-action on these carriers is `zsmul`, so name Mathlib's instance for it.
          exact congrArg _ (congrArg _ ((CompatibleSMul.int (R := ℤ)).smul_tmul ℓ _ α))
      _ = (localHomologyMap (R ⊗ R : ModuleCat ℤ) Φ hΦS (d + k)).hom
          ((localHomologyMap (R ⊗ R : ModuleCat ℤ) (sU.prodMap (ContinuousMap.id F)) hsF
            (d + k)).hom X) :=
          congrArg _ (singularHomologyCrossRel_localHomologyMap_tmul R R sU hsU' rfl oU (ℓ • α))
      _ = _ := ConcreteCategory.congr_hom (localHomologyMap_comp (R ⊗ R : ModuleCat ℤ)
          (sU.prodMap (ContinuousMap.id F)) Φ hsF hΦS (d + k)) X
  have hΘinj : Function.Injective (localHomologyMap (R ⊗ R : ModuleCat ℤ) Θ hΘF (d + k)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact (livesOverFundamentalClass_iff _ _ _ _).2 fun h0 ↦
    hX (hΘinj ((key.symm.trans h0).trans (map_zero _).symm))

include o hd in
/-- `Φ_*(A × α)`, with its coefficients identified with `ℤ`, lives over the fundamental class at
`x₀` when `π_* A = ℓ • [M]` and `ℓ • α ≠ 0`. -/
private theorem livesOverFundamentalClass_actionClass {x₀ : M} (π : C(G, M))
    (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z)
    (hstab : IsPathConnected {g : G | g • x₀ = x₀}) {ℓ : ℤ}
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = ℓ • o.fundamentalClass hd) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 M Sphere2.north x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)} (hα : ℓ • α ≠ 0) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval Sphere2.north) x₀
      (BasedMap.actionClass G Sphere2.north x₀ A α) := by
  have h := (livesOverFundamentalClass_homologyMap_coefficient_iff _
    (ModuleCat.uliftTensorSelfIso ℤ)).2
      (o.livesOverFundamentalClass_actionMap_singularHomologyCross hd Sphere2.north π hπ hloc
        hstab hA hα)
  -- Identify the coefficients before the action map, as in `BasedMap.actionClass`.
  rwa [homologyMap_chainComplexFunctor_map_apply _ _
    ((TopCat.singularHomologyCross (TopCat.of G) (TopCat.of (BasedMap Sphere2 M Sphere2.north x₀))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
        (A ⊗ₜ α))] at h

include o hd in
/-- **Abundance with 2-spheres from a group action, above the dimension**: a criterion for
abundance (Barraud–Damian–Humilière–Oancea, Definition 6.11) by a witness of degree above `d`,
coming from a group action. Propositions 6.29 and 6.33 of the source follow from it and from its
degree-zero counterpart
`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_sub_homologyMap_const_ne_zero`;
see `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_nontrivial_homotopyGroup_two`,
`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_zpow_ne_one` and
`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_exists_nontrivial_homotopyGroup`.

Let a topological group `G` act on a compact oriented `d`-manifold `M`, with orbit map
`π : G → M`, `g ↦ g • x₀`, having continuous local sections around every point, and with
path-connected stabilizer of `x₀`. If some `A ∈ H_d(G; ℤ)` satisfies `π_* A = ℓ • [M]` and some
class `α` of positive degree of the based mapping space `Map_*(S², M)` satisfies `ℓ • α ≠ 0`, then
`M` is abundant with 2-spheres at `x₀`. -/
theorem isAbundantWithTwoSpheres_of_smul_ne_zero {x₀ : M} (π : C(G, M))
    (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z)
    (hstab : IsPathConnected {g : G | g • x₀ = x₀}) {ℓ : ℤ}
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = ℓ • o.fundamentalClass hd) {k : ℕ} (hk : 0 < k)
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 M Sphere2.north x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)} (hα : ℓ • α ≠ 0) :
    IsAbundantWithTwoSpheres M d x₀ :=
  isAbundantWithTwoSpheres_of_lt
    (o.livesOverFundamentalClass_actionClass hd π hπ hloc hstab hA hα) (by omega)

include o hd in
/-- **Abundance with 2-spheres from a group action, in the dimension**: a criterion for abundance
(Barraud–Damian–Humilière–Oancea, Definition 6.11) by a witness of degree `d`, coming from a group
action, used for the case `π₂(M) ≠ 0` of Propositions 6.29 and 6.33. In the
setting of `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_ne_zero`, let
`α ∈ H₀(Map_*(S², M); ℤ)` be a class such that `ℓ • (α - c_* α) ≠ 0`, where `c` is the constant
self-map of `Map_*(S², M)` at the constant sphere at `x₀`. For `ℓ = 1` this says that `α` is not
a multiple of the class of the constant sphere, that is, it is nonzero in `H₀(Ω²M, pt)`. Then
`Φ_*(A × α)` lives over the fundamental class of `M` and its localization at the fibre over `x₀` is
not that of a class of constant spheres, so `M` is abundant with 2-spheres at `x₀`. -/
theorem isAbundantWithTwoSpheres_of_smul_sub_homologyMap_const_ne_zero {x₀ : M} (π : C(G, M))
    (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z)
    (hstab : IsPathConnected {g : G | g • x₀ = x₀}) {ℓ : ℤ}
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = ℓ • o.fundamentalClass hd)
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 M Sphere2.north x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) 0 : ModuleCat.{0} ℤ)}
    (hα : ℓ • (α - (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const
      (BasedMap Sphere2 M Sphere2.north x₀) ⟨ContinuousMap.const Sphere2 x₀, rfl⟩)))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) 0).hom α) ≠ 0) :
    IsAbundantWithTwoSpheres M d x₀ := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let c := (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const
    (BasedMap Sphere2 M Sphere2.north x₀)
      (⟨ContinuousMap.const Sphere2 x₀, rfl⟩ : BasedMap Sphere2 M Sphere2.north x₀)))) R 0).hom
  have hℓα : ℓ • α ≠ 0 := fun h ↦ hα <|
    calc ℓ • (α - c α) = ℓ • α - ℓ • c α := zsmul_sub _ _ _
      _ = 0 := by rw [← map_zsmul, h, map_zero, sub_zero]
  refine isAbundantWithTwoSpheres_of_livesOverFundamentalClass_sub
    (α := BasedMap.actionClass G Sphere2.north x₀ A α)
    (o.livesOverFundamentalClass_actionClass hd π hπ hloc hstab hA hℓα) ?_
  -- The self-map `f ↦ const (f(north))` sends `Φ_*(A × α)` to `Φ_*(A × c_* α)`, and
  -- `ℓ • (α - c_* α) ≠ 0`.
  have h := o.livesOverFundamentalClass_actionClass hd π hπ hloc hstab hA hα
  rwa [BasedMap.actionClass_sub,
    ← BasedMap.homologyMap_const'_comp_mappingSpaceEval_actionClass] at h

include o hd in
/-- **A manifold covered by a group action with `π₂ ≠ 0` is abundant with 2-spheres**
(Barraud–Damian–Humilière–Oancea, Proposition 6.33, the case `π₂(M) ≠ 0`). Let a topological group
`G` act on a compact oriented `d`-manifold `M`, with orbit map `π : G → M`, `g ↦ g • x₀`, having
continuous local sections around every point, and with path-connected stabilizer of `x₀`. If some
`A ∈ H_d(G; ℤ)` satisfies `π_* A = ℓ • [M]` with `ℓ ≠ 0`, and `π₂(M, x₀)` is nontrivial, then `M`
is abundant with 2-spheres at `x₀`: the class of a based sphere outside the path component of the
constant sphere is a witness of degree zero. -/
theorem isAbundantWithTwoSpheres_of_nontrivial_homotopyGroup_two {x₀ : M} (π : C(G, M))
    (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z)
    (hstab : IsPathConnected {g : G | g • x₀ = x₀}) {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = ℓ • o.fundamentalClass hd) [Nontrivial (π_ 2 M x₀)] :
    IsAbundantWithTwoSpheres M d x₀ := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let Y := BasedMap Sphere2 M Sphere2.north x₀
  let y₀ : Y := ⟨ContinuousMap.const Sphere2 x₀, rfl⟩
  -- `Map_*(S², M) ≃ₜ Ω²M` is not path connected, so some `y₁` is not joined to the constant
  -- sphere `y₀`.
  obtain ⟨y₁, hy₁⟩ := exists_not_joined_of_nontrivial_homotopyGroup 2 x₀ Sphere2.north y₀
  refine o.isAbundantWithTwoSpheres_of_smul_sub_homologyMap_const_ne_zero hd π hπ hloc hstab hA
    (α := (singularHomology₀Section R (X := TopCat.of Y) y₁).hom (ULift.up 1)) ?_
  -- `c_* [y₁] = [y₀]`, and `ℓ • ([y₁] - [y₀]) ≠ 0`.
  have key := smul_sub_singularHomology₀Section_apply_ne_zero (M := R) (X := TopCat.of Y)
    (r := ULift.up 1) hy₁ (c := ℓ) fun h ↦ hℓ <| by
      simpa [R, ULift.smul_down] using congrArg ULift.down h
  rw [homologyMap_singularHomology₀Section_apply]
  simp only [TopCat.hom_ofHom, ContinuousMap.const_apply]
  -- `key` uses the module scalar multiplication, the goal `zsmul`.
  intro h0
  rw [← Int.cast_smul_eq_zsmul ℤ, Int.cast_id] at h0
  exact key h0

include o hd in
/-- **A manifold covered by a group action whose first nontrivial higher homotopy group is not
`ℓ`-torsion is abundant with 2-spheres** (Barraud–Damian–Humilière–Oancea, Proposition 6.33, the
case `π₂(M) = 0`). Let a topological group `G` act on a compact oriented `d`-manifold `M`, with
orbit map `π : G → M`, `g ↦ g • x₀`, having continuous local sections around every point, and
with path-connected stabilizer of `x₀`. Suppose that some `A ∈ H_d(G; ℤ)` satisfies
`π_* A = ℓ • [M]`, that `π_j(M, x₀)` vanishes for `2 ≤ j ≤ n + 2`, and that some
`g ∈ π_{n+3}(M, x₀)` satisfies `g ^ ℓ ≠ 1`. Then `M` is abundant with 2-spheres at `x₀`: the
Hurewicz image of `g` in `H_{n+1}(Ω²M; ℤ)` is a witness of positive degree. -/
theorem isAbundantWithTwoSpheres_of_zpow_ne_one {x₀ : M} (π : C(G, M))
    (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z)
    (hstab : IsPathConnected {g : G | g • x₀ = x₀}) {ℓ : ℤ}
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = ℓ • o.fundamentalClass hd) (n : ℕ)
    (hlow : ∀ j < n + 1, Subsingleton (π_ (j + 2) M x₀)) (g : π_ (n + 3) M x₀) (hg : g ^ ℓ ≠ 1) :
    IsAbundantWithTwoSpheres M d x₀ := by
  -- The Hurewicz isomorphism `π_{n+3}(M) ≅ H_{n+1}(Ω²M; ℤ)`: in degree one for `n = 0`, through
  -- the loop-space shift `π₃(M) ≅ π₂(ΩM)`.
  obtain ⟨h⟩ : Nonempty (Additive (π_ (n + 3) M x₀) ≃+
      ((singularChains ℤ).obj (TopCat.of (Ω (Ω M x₀) (Path.refl x₀)))).homology (n + 1)) := by
    cases n with
    | zero =>
      have : Subsingleton (π_ 2 M x₀) := hlow 0 (by omega)
      have := (pathConnectedSpace_doubleLoopSpace_iff x₀).2 this
      exact ⟨(HomotopyGroup.pathLoopSpaceMulEquiv 1).symm.toAdditive.trans
        (pathLoopSpaceFirstHomologyAddEquiv (Path.refl x₀))⟩
    | succ m => exact ⟨doubleLoopSpaceHomologyAddEquiv x₀ m hlow⟩
  -- Carry `H_{n+1}(Ω²M; ℤ)` to `Map_*(S², M)`, with coefficients `ULift ℤ`.
  let ι := doubleLoopSpaceHomologyIsoBasedMap x₀ (n + 1)
  refine o.isAbundantWithTwoSpheres_of_smul_ne_zero hd π hπ hloc hstab hA (Nat.succ_pos n)
    (α := ι.hom (h (Additive.ofMul g))) ?_
  rw [← map_zsmul, ← map_zsmul, ← ofMul_zpow]
  intro h0
  have hι : Function.Injective ι.hom := (ModuleCat.mono_iff_injective ι.hom).1 inferInstance
  have h₁ : h (Additive.ofMul (g ^ ℓ)) = 0 := hι (h0.trans (map_zero _).symm)
  exact hg (Additive.ofMul.injective (h.injective (h₁.trans (map_zero h).symm)))

include o hd in
/-- **A non-aspherical manifold covered by a group action is abundant with 2-spheres**
(Barraud–Damian–Humilière–Oancea, Proposition 6.29, for a group action). Let a topological group
`G` act on a compact oriented `d`-manifold `M`, with orbit map `π : G → M`, `g ↦ g • x₀`, having
continuous local sections around every point, and with path-connected stabilizer of `x₀`. If some
`A ∈ H_d(G; ℤ)` satisfies `π_* A = [M]` and some higher homotopy group `π_{n+2}(M, x₀)` is
nontrivial, then `M` is abundant with 2-spheres at `x₀`. For path-connected `M` the latter says
that `M` is not aspherical (`TauCeti.IsAspherical`). -/
theorem isAbundantWithTwoSpheres_of_exists_nontrivial_homotopyGroup
    {x₀ : M} (π : C(G, M)) (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z)
    (hstab : IsPathConnected {g : G | g • x₀ = x₀})
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = o.fundamentalClass hd) (hM : ∃ n, Nontrivial (π_ (n + 2) M x₀)) :
    IsAbundantWithTwoSpheres M d x₀ := by
  have hA' : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = (1 : ℤ) • o.fundamentalClass hd := by
    rw [one_zsmul, hA]
  -- The first nontrivial homotopy group `π_{n₀+2}(M, x₀)` above the fundamental group.
  classical
  obtain ⟨n₀, hn₀, hmin⟩ : ∃ n₀, Nontrivial (π_ (n₀ + 2) M x₀) ∧
      ∀ j < n₀, Subsingleton (π_ (j + 2) M x₀) :=
    ⟨Nat.find hM, Nat.find_spec hM,
      fun j hj ↦ not_nontrivial_iff_subsingleton.1 (Nat.find_min hM hj)⟩
  cases n₀ with
  | zero =>
    exact o.isAbundantWithTwoSpheres_of_nontrivial_homotopyGroup_two hd π hπ hloc hstab one_ne_zero
      hA'
  | succ n =>
    obtain ⟨g, hg⟩ := exists_ne (1 : π_ (n + 3) M x₀)
    exact o.isAbundantWithTwoSpheres_of_zpow_ne_one hd π hπ hloc hstab hA' n hmin g
      (by rwa [zpow_one])

end HomologicalOrientation

end TauCeti

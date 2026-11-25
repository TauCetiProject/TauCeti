/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.Abundant.Basic
public import TauCeti.Topology.MappingSpace.Action
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
import TauCeti.Algebra.Category.ModuleCat.Monoidal.TensorMk
import TauCeti.AlgebraicTopology.Singular.Homotopy.BasedMapStabilizer
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
around every point. If a class `A ∈ H_d(G; ℤ)` satisfies `π_* A = ℓ • [M]` and a class `α` of the
based mapping space satisfies `ℓ • α ≠ 0` and is fixed by every element of the stabilizer of `x₀`,
then `Φ_*(A × α)` lives over the fundamental class of `M` at `x₀`
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
of `Diff(M)`, and the source uses that its stabilizer acts trivially on the homology of `Ω²M`; the
hypothesis here asks this only of the class `α`. Every element joined to `1` by a path in the
stabilizer fixes `α` (`JoinedIn.homologyMap_stabilizer_smul_apply`, in
`TauCeti.AlgebraicTopology.Singular.Homotopy.BasedMapStabilizer`), so the hypothesis holds when the
stabilizer is path connected. It can fail for the identity component of `Diff(M)` when `π₁(M)` acts
nontrivially on `π₂(M)`: an isotopy from the identity to a diffeomorphism fixing `x₀` moves `x₀`
around a loop, and the diffeomorphism acts on `π₀(Ω²M) = π₂(M)` through that loop.

## The computation

Localizing at the fibre over `x₀` commutes with `Φ`, a map over `M`, and localizing a cross product
`A × α` for the projection `G × Map_*(B, M) → M` gives the relative cross product of the
localization of `A` with `α` (`TauCeti.fiberLocalization_singularHomologyCross_tmul`).

* **The class of `A`.** The orbit map is a Serre fibration whose fibre over `x₀` is the stabilizer
  `H`, so the local homology `H_d(G, G ∖ H)` is the zeroth homology of `H`
  (`TauCeti.TopCat.singularHomologyComplFiberIso`), spanned by the classes of the points of `H`.
  Right translation by `h ∈ H` lies over `M` and carries the class of the point `1` to that of `h`.
  It changes `c × α` into `c × h_* α = c × α`, since `(g h) • u = g • (h • u)`. So the maps
  `c ↦ Φ_*(c × α)` and `c ↦ π_* c` are both determined by their values on the class of `1`. Let
  `s : U → G` be a section of the orbit map over an open neighbourhood `U` of `x₀`, and
  `o_U ∈ H_d(U, U ∖ {x₀})` the local orientation at `x₀`, read in `U`. Comparing `A` with `s_* o_U`,
  which the orbit map sends to the local orientation, a generator of infinite order, gives
  `Φ_*(loc(A) × α) = Φ_*(ℓ • s_* o_U × α)`.
* **The class of `Φ_*(A × α)`.** The composite `Θ = Φ ∘ (s × id) : U × Map_*(B, M) → Map(B, M)`,
  `(x, u) ↦ s(x) • u`, is an open embedding onto the maps sending the base point into `U`, the
  inverse of the local trivialization of evaluation given by `s`
  (`TauCeti.mappingSpaceEvalTrivialization`). By excision it induces an isomorphism on local
  homology along the fibre over `x₀` (`TauCeti.isIso_localHomologyMap`), and the localization of
  `Φ_*(A × α)` is its image of the relative cross product of `o_U` with `ℓ • α`. That relative
  cross product is nonzero, since its image in `M × Map_*(B, M)` is the relative cross product of
  the local orientation, a free generator, with `ℓ • α ≠ 0`.

## Main declarations

* `TauCeti.BasedMap.actionClass`: the `R`-linear map `α ↦ Φ_*(A × α)` over a commutative ring `R`,
  with its coefficients `ULift R ⊗ ULift R` identified with `ULift R`. The self-map
  `f ↦ const (f(b₀))` sends it to `Φ_*(A × c_* α)`
  (`TauCeti.BasedMap.homologyMap_const'_comp_mappingSpaceEval_actionClass`).

## Main results

* `TauCeti.HomologicalOrientation.livesOverFundamentalClass_actionMap_singularHomologyCross`,
  `TauCeti.HomologicalOrientation.livesOverFundamentalClass_actionClass`: `Φ_*(A × α)` lives over
  the fundamental class at `x₀`, both with coefficients `ℤ ⊗ ℤ` and via
  `TauCeti.BasedMap.actionClass` with coefficients identified with `ℤ`.
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_ne_zero`: a manifold with such
  an action, a class `A` with `π_* A = ℓ • [M]` and a class `α` of positive degree of
  `Map_*(S², M)` with `ℓ • α ≠ 0`, fixed by the stabilizer, is abundant with 2-spheres.
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_sub_homologyMap_const_ne_zero`:
  the same for a class `α` of degree zero with `ℓ • (α - c_* α) ≠ 0`, fixed by
  the stabilizer.
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

/-! ### Action classes in singular homology -/

namespace BasedMap

section ActionClass

universe u

variable {R : Type u} [CommRing R] {G M B : Type u} [TopologicalSpace G] [Group G]
  [TopologicalSpace M] [MulAction G M] [ContinuousSMul G M] [TopologicalSpace B]
  (b₀ : B) (x₀ : M) {d : ℕ}

/-- The `R`-linear map `α ↦ Φ_*(A × α)` carrying a class `α` of the based mapping space
`Map_*(B, M)` to a class of `Map(B, M)` using `A ∈ H_d(G; R)` and the action map
`Φ : G × Map_*(B, M) → Map(B, M)` (`TauCeti.BasedMap.actionMap`), with the coefficients
`ULift R ⊗ ULift R` of the cross product identified with `ULift R`. For a group acting on itself,
`R = ℤ`, `x₀ = 1` and `A = [G]` it gives the class of Example 6.30 of
Barraud–Damian–Humilière–Oancea. -/
def actionClass
    (A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of R (ULift.{u} R)) d :
      ModuleCat.{u} R)) {k : ℕ} :
    ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ x₀))).homology
      (ModuleCat.of R (ULift.{u} R)) k : ModuleCat.{u} R) →ₗ[R]
    ((TopCat.toSSet.obj (TopCat.of C(B, M))).homology (ModuleCat.of R (ULift.{u} R))
      (d + k) : ModuleCat.{u} R) :=
  (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (actionMap (G := G) b₀ x₀)))
    (ModuleCat.of R (ULift.{u} R)) (d + k)).hom ∘ₗ
  (HomologicalComplex.homologyMap (((SSet.chainComplexFunctor (ModuleCat.{u} R)).map
    (ModuleCat.uliftTensorSelfIso R).hom).app
      (TopCat.toSSet.obj (TopCat.of (G × BasedMap B M b₀ x₀)))) (d + k)).hom ∘ₗ
  (TopCat.singularHomologyCross (TopCat.of G) (TopCat.of (BasedMap B M b₀ x₀))
    (ModuleCat.of R (ULift.{u} R)) (ModuleCat.of R (ULift.{u} R)) d k (d + k) rfl).hom ∘ₗ
  TensorProduct.mk R
    ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of R (ULift.{u} R)) d :
      ModuleCat.{u} R)
    ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ x₀))).homology
      (ModuleCat.of R (ULift.{u} R)) k : ModuleCat.{u} R) A

/-- Evaluate `TauCeti.BasedMap.actionClass` at a class `α`: the action map applied to the cross
product `A × α`, with the coefficients `ULift R ⊗ ULift R` identified with `ULift R`. -/
theorem actionClass_apply
    (A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of R (ULift.{u} R)) d :
      ModuleCat.{u} R)) {k : ℕ}
    (α : ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ x₀))).homology
      (ModuleCat.of R (ULift.{u} R)) k : ModuleCat.{u} R)) :
    actionClass b₀ x₀ A α =
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (actionMap (G := G) b₀ x₀)))
          (ModuleCat.of R (ULift.{u} R)) (d + k)).hom
        ((HomologicalComplex.homologyMap (((SSet.chainComplexFunctor (ModuleCat.{u} R)).map
          (ModuleCat.uliftTensorSelfIso R).hom).app
            (TopCat.toSSet.obj (TopCat.of (G × BasedMap B M b₀ x₀)))) (d + k)).hom
          ((TopCat.singularHomologyCross (TopCat.of G) (TopCat.of (BasedMap B M b₀ x₀))
            (ModuleCat.of R (ULift.{u} R)) (ModuleCat.of R (ULift.{u} R)) d k (d + k) rfl).hom
              (A ⊗ₜ α))) :=
  (rfl)

/-- The constant maps at the values at the base point, `f ↦ const (f b₀)`, send `Φ_*(A × α)` to
`Φ_*(A × c_* α)`, where `c` is the constant self-map of `Map_*(B, M)` at the constant map at `x₀`:
both `g • u ↦ const (g • x₀)` and `(g, u) ↦ g • const x₀` agree. -/
theorem homologyMap_const'_comp_mappingSpaceEval_actionClass
    (A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of R (ULift.{u} R)) d :
      ModuleCat.{u} R)) {k : ℕ}
    (α : ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ x₀))).homology
      (ModuleCat.of R (ULift.{u} R)) k : ModuleCat.{u} R)) :
    (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
      ((ContinuousMap.const' : C(M, C(B, M))).comp (mappingSpaceEval b₀))))
        (ModuleCat.of R (ULift.{u} R)) (d + k)).hom (actionClass b₀ x₀ A α) =
      actionClass b₀ x₀ A ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
        (ContinuousMap.const (BasedMap B M b₀ x₀) ⟨ContinuousMap.const B x₀, rfl⟩)))
          (ModuleCat.of R (ULift.{u} R)) k).hom α) := by
  let S := ModuleCat.of R (ULift.{u} R)
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
  have hcross := homologyMap_prodMap_singularHomologyCross_tmul S S (ContinuousMap.id G) c rfl A α
  simp only [TopCat.ofHom_id, CategoryTheory.Functor.map_id, SSet.homologyMap_id,
    ModuleCat.id_apply] at hcross
  -- Identify the coefficients before the maps, then commute the square `ρ ∘ Φ = Φ ∘ γ`.
  rw [actionClass_apply, actionClass_apply, ← hcross, homologyMap_chainComplexFunctor_map_apply _ γ
    ((TopCat.singularHomologyCross (TopCat.of G) (TopCat.of Y) S S d k (d + k) rfl).hom (A ⊗ₜ α))]
  exact ConcreteCategory.congr_hom (homologyMap_toSSet_ofHom_comp_comm S _ hΦ) _

end ActionClass

end BasedMap

/-! ### Local homology along the stabilizer fibre -/

section LocalHomologyHelpers

/-- **Right translation along the stabilizer, on the fibre.** The orbit map `π`, `g ↦ g • x₀`, is
a Serre fibration whose fibre over `x₀` is the stabilizer `H`. For `y ∈ H`, the identification
`H₀(H) ≅ H_d(G, G ∖ H)` (`TauCeti.TopCat.singularHomologyComplFiberIso`) carries the class of the
point `y` to the image of the class of `1` under right translation by `y`, which lies over `M`. -/
private theorem singularHomology₀Section_comp_singularHomologyComplFiberIso_inv {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ} {M : Type}
    [TopologicalSpace M] [T1Space M] [ChartedSpace V M] {G : Type} [TopologicalSpace G] [Group G]
    [ContinuousMul G] [MulAction G M] {x₀ : M} (π : C(G, M)) (hπ : ∀ g, π g = g • x₀)
    (hp : TopCat.serreFibrations (TopCat.ofHom π)) {ε : ℝ}
    (hε : Metric.ball (chartAt V x₀ x₀) ε ⊆ (chartAt V x₀).target) (hε₀ : 0 < ε)
    (h0 : 0 + finrank ℝ V = d)
    (y : TopCat.of ((TopCat.ofHom π : TopCat.of G ⟶ TopCat.of M) ⁻¹' {x₀}))
    (hyS : ContinuousMap.mulRight (y : G) ⁻¹' (π ⁻¹' {x₀}) ⊆ π ⁻¹' {x₀}) :
    singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ)) y ≫
        (TopCat.singularHomologyComplFiberIso _ (chartAt V x₀) (mem_chart_source V x₀) hε hε₀ hp
          0 d h0).inv =
      singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ))
          (X := TopCat.of ((TopCat.ofHom π : TopCat.of G ⟶ TopCat.of M) ⁻¹' {x₀}))
          ⟨1, by simp [hπ]⟩ ≫
        (TopCat.singularHomologyComplFiberIso _ (chartAt V x₀) (mem_chart_source V x₀) hε hε₀ hp
          0 d h0).inv ≫
        localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.mulRight (y : G)) hyS d := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let p : TopCat.of G ⟶ TopCat.of M := TopCat.ofHom π
  let fib := TopCat.singularHomologyComplFiberIso R (chartAt V x₀) (mem_chart_source V x₀) hε hε₀
    hp 0 d h0
  let one : p ⁻¹' {x₀} := ⟨1, by simp [p, hπ]⟩
  let f : TopCat.of G ⟶ TopCat.of G := TopCat.ofHom (ContinuousMap.mulRight (y : G))
  have hy : (y : G) ∈ MulAction.stabilizer G x₀ :=
    MulAction.mem_stabilizer_iff.2 ((hπ _).symm.trans y.property)
  have hf : f ≫ p = p := TopCat.hom_ext (π.comp_mulRight_eq_of_mem_stabilizer hπ hy)
  -- Right translation by `y` on the fibre carries the point `1` to `y`.
  have hsec : singularHomology₀Section R y = singularHomology₀Section R one ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj R).map
        (f.preimageMap hf {x₀}) := by
    rw [singularHomology₀Section_naturality]
    congr 1
    refine Subtype.ext ?_
    rw [TopCat.Hom.coe_preimageMap_apply]
    simp [f, one]
  have hnat : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj R).map
      (f.preimageMap hf {x₀}) ≫ fib.inv =
      fib.inv ≫ localHomologyMap R (ContinuousMap.mulRight (y : G)) hyS d := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← TopCat.singularHomologyComplFiberIso_hom_naturality
      R (chartAt V x₀) (mem_chart_source V x₀) hε hε₀ hp hp hf 0 d _, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, localHomologyMap_def]
  rw [hsec, Category.assoc, hnat]

/-- **Maps out of the local homology along the stabilizer that are invariant under right
translations.** Let the orbit map `π : G → M`, `g ↦ g • x₀`, have continuous local sections
around every point. There are a function `χ` on `H_d(G, G ∖ π⁻¹(x₀); ℤ)` and a class `c₁` of it
such that every map `Q` out of this local homology that is invariant under right translation by
the elements of the stabilizer of `x₀` satisfies `Q c = χ c • Q c₁`.

The orbit map is a Serre fibration whose fibre over `x₀` is the stabilizer, so the local
homology is the zeroth homology of the stabilizer, and right translation by `h` acts on it through
the right translation of the fibre (`TauCeti.TopCat.singularHomologyComplFiberIso` and its
naturality). Right translation by `h` carries the class of the point `1` to that of `h`, so `Q`
takes the same value on the classes of all points, and is therefore the augmentation followed by
its value on the class of `1`. Here `χ` is the augmentation and `c₁` the class of `1`. -/
private theorem exists_forall_apply_eq_zsmul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {d : ℕ} (hd : finrank ℝ V = d) {M : Type} [TopologicalSpace M]
    [T1Space M] [ChartedSpace V M] {G : Type} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [MulAction G M] [ContinuousSMul G M] {x₀ : M} (π : C(G, M))
    (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z) :
    ∃ (χ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (π ⁻¹' {x₀}) d →
        ℤ) (c₁ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
          (π ⁻¹' {x₀}) d),
      ∀ (T : ModuleCat.{0} ℤ)
        (Q : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (π ⁻¹' {x₀}) d ⟶
          T),
        (∀ (h : MulAction.stabilizer G x₀) (hh : ContinuousMap.mulRight (h : G) ⁻¹' (π ⁻¹' {x₀}) ⊆
          π ⁻¹' {x₀}),
          localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.mulRight (h : G)) hh d ≫
            Q = Q) →
        ∀ c, Q c = χ c • Q c₁ := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let p : TopCat.of G ⟶ TopCat.of M := TopCat.ofHom π
  have hπ' : p = TopCat.ofHom ⟨fun g : G ↦ g • x₀, by fun_prop⟩ :=
    TopCat.hom_ext (ContinuousMap.ext hπ)
  have hp : TopCat.serreFibrations p := hπ' ▸ orbitMap_mem_serreFibrations (G := G) x₀ hloc
  let e := chartAt V x₀
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e x₀) (e.map_source
    (mem_chart_source V x₀))
  -- `H_d(G, G ∖ π⁻¹(x₀)) ≅ H₀(π⁻¹(x₀))`.
  let fib := TopCat.singularHomologyComplFiberIso R e (mem_chart_source V x₀) hε hε₀ hp 0 d
    (by rw [zero_add, hd])
  let ε₀ := (TopCat.of (p ⁻¹' {x₀})).singularHomology₀ε R
  let one : p ⁻¹' {x₀} := ⟨1, by simp [p, hπ]⟩
  let c₁ := fib.inv (singularHomology₀Section R one (ULift.up 1))
  refine ⟨fun c ↦ (ε₀ (fib.hom c)).down, c₁, fun T Q hQ c ↦ ?_⟩
  -- On zeroth homology, `Q` is the augmentation followed by multiplication by `Q c₁`.
  have key : fib.inv ≫ Q = ε₀ ≫ ModuleCat.ofHom ((LinearMap.toSpanSingleton ℤ T (Q c₁)).comp
      (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toLinearMap) := by
    refine singularHomology₀_hom_ext R fun y ↦ ?_
    have hy : (y : G) ∈ MulAction.stabilizer G x₀ :=
      MulAction.mem_stabilizer_iff.2 ((hπ _).symm.trans y.property)
    have hyS : ContinuousMap.mulRight (y : G) ⁻¹' (π ⁻¹' {x₀}) ⊆ π ⁻¹' {x₀} := by
      rw [← preimage_comp, ← ContinuousMap.coe_comp, π.comp_mulRight_eq_of_mem_stabilizer hπ hy]
    have hsec : singularHomology₀Section R y ≫ fib.inv = singularHomology₀Section R one ≫
        fib.inv ≫ localHomologyMap R (ContinuousMap.mulRight (y : G)) hyS d :=
      singularHomology₀Section_comp_singularHomologyComplFiberIso_inv π hπ hp hε hε₀
        (by rw [zero_add, hd]) y hyS
    rw [singularHomology₀Section_singularHomology₀ε_assoc, reassoc_of% hsec, hQ ⟨y, hy⟩]
    ext ⟨r⟩
    have hr : (ULift.up r : ULift.{0} ℤ) = r • ULift.up 1 := ULift.ext (by simp)
    simp only [R, c₁, hr, map_zsmul, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearEquiv.coe_coe, ULift.moduleEquiv_apply, LinearMap.toSpanSingleton_apply_one]
  have := ConcreteCategory.congr_hom key (fib.hom c)
  rw [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply] at this
  rw [this, ConcreteCategory.comp_apply]
  exact int_smul_eq_zsmul _ _ _

/-- **The translation chart of evaluation.** Let `s : U → G` be a section of the orbit map over an
open set `U ∋ x₀`. Then `Θ : U × Map_*(B, M) → Map(B, M)`, `(x, u) ↦ s(x) • u`, is an open
embedding onto the maps sending `b₀` into `U`, the inverse of the local trivialization of
evaluation given by `s` (`TauCeti.mappingSpaceEvalTrivialization`). By excision it induces an
isomorphism from the local homology along `{x₀} × Map_*(B, M)` to the local homology along the
fibre of evaluation over `x₀`. -/
private theorem isIso_localHomologyMap_actionMap_comp_prodMap {G M B : Type} [TopologicalSpace G]
    [Group G] [ContinuousInv G] [TopologicalSpace M] [T1Space M] [MulAction G M]
    [ContinuousSMul G M] [TopologicalSpace B] (b₀ : B) {U : Set M} (hU : IsOpen U) (x₀ : U)
    (s : M → G) (hs : ContinuousOn s U) (hsec : ∀ z ∈ U, s z • (x₀ : M) = z)
    (R : ModuleCat.{0} ℤ) (n : ℕ) :
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

/-- **Right translation by the stabilizer under the action map.** For `h` in the stabilizer of
`x₀` fixing the class `α` of the based mapping space, the action map sends the relative cross
products `(c h) × α` and `c × α` to the same class: `(g h) • u = g • (h • u)`, so the first is the
image of `c × h_* α = c × α`. -/
private theorem localHomologyMap_actionMap_singularHomologyCrossRel_mulRight {G M B : Type}
    [TopologicalSpace G] [Group G] [ContinuousMul G] [TopologicalSpace M] [MulAction G M]
    [ContinuousSMul G M] [TopologicalSpace B] (b₀ : B) {x₀ : M} (π : C(G, M))
    (h : MulAction.stabilizer G x₀) {d k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)}
    (hfix : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨(h • · : BasedMap B M b₀ x₀ →
      BasedMap B M b₀ x₀), continuous_const_smul h⟩)) (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom α =
        α)
    (hΦS : BasedMap.actionMap (G := G) b₀ x₀ ⁻¹' (mappingSpaceEval b₀ ⁻¹' {x₀}) ⊆
      (π ∘ Prod.fst) ⁻¹' {x₀})
    (hh : ContinuousMap.mulRight (h : G) ⁻¹' (π ⁻¹' {x₀}) ⊆ π ⁻¹' {x₀})
    (c : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (π ⁻¹' {x₀}) d) :
    let R := ModuleCat.of ℤ (ULift.{0} ℤ)
    let cross := TopCat.singularHomologyCrossRel (TopCat.of G)
      (TopCat.of (BasedMap B M b₀ x₀)) (π ⁻¹' {x₀})ᶜ R R d k (d + k) rfl
    let Φloc := localHomologyMap (R ⊗ R : ModuleCat ℤ) (BasedMap.actionMap (G := G) b₀ x₀) hΦS
      (d + k)
    Φloc.hom (cross.hom ((localHomologyMap R (ContinuousMap.mulRight (h : G)) hh d).hom c ⊗ₜ α)) =
      Φloc.hom (cross.hom (c ⊗ₜ α)) := by
  intro R cross Φloc
  let F := BasedMap B M b₀ x₀
  let act : C(F, F) := ⟨(h • ·), continuous_const_smul h⟩
  have hΦ : (BasedMap.actionMap (G := G) b₀ x₀).comp
      ((ContinuousMap.mulRight (h : G)).prodMap (ContinuousMap.id F)) =
      (BasedMap.actionMap (G := G) b₀ x₀).comp ((ContinuousMap.id G).prodMap act) :=
    ContinuousMap.ext fun q ↦ BasedMap.actionMap_mul_stabilizer q.1 h q.2
  have h₁ : (ContinuousMap.mulRight (h : G)).prodMap (ContinuousMap.id F) ⁻¹'
      (Prod.fst ⁻¹' (π ⁻¹' {x₀})) ⊆ Prod.fst ⁻¹' (π ⁻¹' {x₀}) := fun _ hz ↦ hh hz
  have h₂ : (ContinuousMap.id G).prodMap act ⁻¹' (Prod.fst ⁻¹' (π ⁻¹' {x₀})) ⊆
      Prod.fst ⁻¹' (π ⁻¹' {x₀}) := fun _ hz ↦ hz
  have e := (localHomologyMap_comp (R ⊗ R : ModuleCat ℤ) _ _ h₁ hΦS (d + k)).trans
    ((localHomologyMap_congr (R ⊗ R : ModuleCat ℤ) hΦ _ (d + k)).trans
      (localHomologyMap_comp (R ⊗ R : ModuleCat ℤ) _ _ h₂ hΦS (d + k)).symm)
  exact (congrArg Φloc.hom
    (singularHomologyCrossRel_localHomologyMap_tmul R R _ hh rfl c α)).trans
    ((ConcreteCategory.congr_hom e _).trans
      ((congrArg Φloc.hom (singularHomologyCrossRel_tmul_homologyMap R R act rfl c α)).symm.trans
        (congrArg (fun a ↦ Φloc.hom (cross.hom (c ⊗ₜ a))) hfix)))

end LocalHomologyHelpers

/-! ### Classes of the action map living over the fundamental class -/

namespace HomologicalOrientation

section OrientationHelpers

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace V M]
  (o : HomologicalOrientation M V d)

/-- **The image of `c × α` for a class `c` of the stabilizer covering `ℓ • [M]`.** Let `s : U → G`
be a section of the orbit map over an open set `U ∋ x₀`, and `o_U` the local orientation at `x₀`
read in `U`. If every element of the stabilizer of `x₀` fixes the class `α` of the based mapping
space, then for a class `c` of `H_d(G, G ∖ π⁻¹(x₀))` sent by the orbit map to `ℓ` times the local
orientation, the action map sends the relative cross product `c × α` to `ℓ` times the image of
`s_* o_U × α`.

Right translation by an element `h` of the stabilizer changes `c × α` into `c × h_* α`, since
`(g h) • u = g • (h • u)`; so `c ↦ Φ_*(c × α)` is invariant under these translations, as is the
orbit map, and both are multiples of one function `χ` of `c`
(`exists_forall_apply_eq_zsmul`). Comparing the orbit map on `c` and on `s_* o_U`, whose image is
the local orientation, determines `χ c` in terms of `χ (s_* o_U)` and `ℓ`. -/
private theorem localHomologyMap_actionMap_singularHomologyCrossRel_eq_zsmul
    (hd : finrank ℝ V = d) {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MulAction G M] [ContinuousSMul G M] {B : Type} [TopologicalSpace B] (b₀ : B) {U : Set M}
    (hU : IsOpen U) (x₀ : U) (π : C(G, M)) (hπ : ∀ g, π g = g • (x₀ : M))
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • (x₀ : M) = z) (s : C(U, G))
    (hs : ∀ z : U, s z • (x₀ : M) = z) (hsU : s ⁻¹' (π ⁻¹' {(x₀ : M)}) ⊆ {x₀}) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ (x₀ : M)))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)}
    (hfix : ∀ h : MulAction.stabilizer G (x₀ : M),
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨(h • · : BasedMap B M b₀ (x₀ : M) →
        BasedMap B M b₀ (x₀ : M)), continuous_const_smul h⟩)) (ModuleCat.of ℤ (ULift.{0} ℤ))
          k).hom α = α)
    (hΦS : BasedMap.actionMap (G := G) b₀ (x₀ : M) ⁻¹' (mappingSpaceEval b₀ ⁻¹' {(x₀ : M)}) ⊆
      (π ∘ Prod.fst) ⁻¹' {(x₀ : M)})
    {ℓ : ℤ} {c : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
      (π ⁻¹' {(x₀ : M)}) d}
    (hc : (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) π subset_rfl d).hom c =
      ℓ • (o x₀).val) :
    let R := ModuleCat.of ℤ (ULift.{0} ℤ)
    let cross := TopCat.singularHomologyCrossRel (TopCat.of G)
      (TopCat.of (BasedMap B M b₀ (x₀ : M))) (π ⁻¹' {(x₀ : M)})ᶜ R R d k (d + k) rfl
    let Φloc := localHomologyMap (R ⊗ R : ModuleCat ℤ) (BasedMap.actionMap (G := G) b₀ (x₀ : M))
      hΦS (d + k)
    Φloc.hom (cross.hom (c ⊗ₜ α)) = Φloc.hom (cross.hom ((ℓ • (localHomologyMap R s hsU d).hom
      ((localHomologyIsoOfIsOpenEmbedding R hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom
        (o x₀).val)) ⊗ₜ α)) := by
  intro R cross Φloc
  obtain ⟨χ, c₁, hχ⟩ := exists_forall_apply_eq_zsmul hd π hπ hloc
  let F := BasedMap B M b₀ (x₀ : M)
  let Lπ := localHomologyMap R π (subset_refl (π ⁻¹' {(x₀ : M)})) d
  -- `c ↦ Φ_*(c × α)` as a morphism out of the local homology along the stabilizer.
  let αmap : 𝟙_ (ModuleCat.{0} ℤ) ⟶ (TopCat.toSSet.obj (TopCat.of F)).homology R k :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ α)
  let P : localHomology (A := ModuleCat.{0} ℤ) R (π ⁻¹' {(x₀ : M)}) d ⟶ _ :=
    ((ρ_ _).inv ≫ (_ ◁ αmap)) ≫ cross ≫ Φloc
  have hPapply : ∀ c, P c = Φloc.hom (cross.hom (c ⊗ₜ α)) := fun c ↦
    (ConcreteCategory.comp_apply _ (cross ≫ Φloc) c).trans
      ((congrArg (cross ≫ Φloc)
        (ModuleCat.rightUnitor_inv_whiskerLeft_toSpanSingleton_apply α c)).trans
          (ConcreteCategory.comp_apply cross Φloc _))
  have hLπ : ∀ (h : MulAction.stabilizer G (x₀ : M)) hh,
      localHomologyMap R (ContinuousMap.mulRight (h : G)) hh d ≫ Lπ = Lπ :=
    fun h hh ↦ (localHomologyMap_comp R _ π hh _ d).trans
      (localHomologyMap_congr R (π.comp_mulRight_eq_of_mem_stabilizer hπ h.property) _ d)
  have hP : ∀ (h : MulAction.stabilizer G (x₀ : M)) hh,
      localHomologyMap R (ContinuousMap.mulRight (h : G)) hh d ≫ P = P := by
    intro h hh
    ext c
    rw [ModuleCat.comp_apply, hPapply, hPapply]
    exact localHomologyMap_actionMap_singularHomologyCrossRel_mulRight b₀ π h (hfix h) hΦS hh c
  let sO := (localHomologyMap R s hsU d).hom
    ((localHomologyIsoOfIsOpenEmbedding R hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom (o x₀).val)
  have hPc := hχ _ P hP c
  have hPz := hχ _ P hP sO
  have hLc := hχ _ Lπ hLπ c
  have hLz := hχ _ Lπ hLπ sO
  -- The orbit map sends `s_* o_U` to the local orientation.
  rw [localHomologyIsoOfIsOpenEmbedding_inv_comp_localHomologyMap_comp_apply R
    hU.isOpenEmbedding_subtypeVal x₀ π s (fun z ↦ (hπ _).trans (hs z)) hsU subset_rfl d] at hLz
  rw [hc] at hLc
  -- The local orientation generates the local homology, so `Lπ c₁ = m • o` with
  -- `χ (s_* o_U) * m = 1` and `ℓ = χ c * m`.
  obtain ⟨m, hm⟩ := (isLocalOrientation_iff _ _ _).1 (o x₀).property (Lπ c₁)
  rw [← hm, smul_smul] at hLc hLz
  have h₁ := o.zsmul_left_injective hd x₀ ((one_smul ℤ _).trans hLz)
  have h₂ := o.zsmul_left_injective hd x₀ hLc
  -- Hence `χ c = χ c * χ (s_* o_U) * m = ℓ * χ (s_* o_U)`.
  have hχc : χ c = ℓ * χ sO := by grind
  rw [← hPapply, ← hPapply, map_zsmul, hPc, hPz, smul_smul, hχc]

end OrientationHelpers

section LivesOver

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace V M]
  (o : HomologicalOrientation M V d) (hd : finrank ℝ V = d)
  {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [MulAction G M]
  [ContinuousSMul G M]

/-- **Classes of the action map living over the fundamental class** (the argument of
Barraud–Damian–Humilière–Oancea, Propositions 6.29 and 6.33, for a group action). Let a
topological group `G` act on a compact oriented `d`-manifold `M` with orbit map
`π : G → M`, `g ↦ g • x₀`, which has continuous local sections around every point. Let
`A ∈ H_d(G; ℤ)` satisfy `π_* A = ℓ • [M]`, and let `α` be a class of the based mapping space
`Map_*(B, M)` with `ℓ • α ≠ 0` which every element of the stabilizer of `x₀` fixes. Then the image
of `A × α` under the action map `G × Map_*(B, M) → Map(B, M)` lives over the fundamental class of
`M` at `x₀`, for evaluation at the base point `b₀` of `B`. -/
theorem livesOverFundamentalClass_actionMap_singularHomologyCross {B : Type}
    [TopologicalSpace B] (b₀ : B) {x₀ : M} (π : C(G, M)) (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z) {ℓ : ℤ}
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = ℓ • o.fundamentalClass hd) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)} (hα : ℓ • α ≠ 0)
    (hfix : ∀ h : MulAction.stabilizer G x₀,
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨(h • · : BasedMap B M b₀ x₀ →
        BasedMap B M b₀ x₀), continuous_const_smul h⟩)) (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom α =
          α) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ))
      (mappingSpaceEval b₀) x₀
      ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (BasedMap.actionMap (G := G) b₀ x₀)))
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k)).hom
        ((TopCat.singularHomologyCross (TopCat.of G) (TopCat.of (BasedMap B M b₀ x₀))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
            (A ⊗ₜ α))) := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let R₂ : ModuleCat.{0} ℤ := R ⊗ R
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
    R₂ (d + k)
  let oU := (localHomologyIsoOfIsOpenEmbedding R hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom
    (o x₀).val
  let X := (TopCat.singularHomologyCrossRel (TopCat.of U) (TopCat.of F) {x₀}ᶜ R R d k (d + k)
    rfl).hom (oU ⊗ₜ (ℓ • α))
  have hΦS : Φ ⁻¹' (mappingSpaceEval b₀ ⁻¹' {(x₀ : M)}) ⊆ (π ∘ Prod.fst) ⁻¹' {(x₀ : M)} := by
    rw [← preimage_comp, hΦ]
  have hsF : sU.prodMap (ContinuousMap.id F) ⁻¹' (Prod.fst ⁻¹' (π ⁻¹' {(x₀ : M)})) ⊆
      Prod.fst ⁻¹' {x₀} := fun _ hz ↦ hsU' hz
  let crossG := TopCat.singularHomologyCrossRel (TopCat.of G) (TopCat.of F) (π ⁻¹' {(x₀ : M)})ᶜ
    R R d k (d + k) rfl
  -- Localizing `Φ_*(A × α)` gives `Θ_* X`, and `Θ_*` is injective by excision.
  have key : (fiberLocalization R₂ (mappingSpaceEval b₀) (x₀ : M) (d + k)).hom
      ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom Φ)) R₂ (d + k)).hom
        ((TopCat.singularHomologyCross (TopCat.of G) (TopCat.of F) R R d k (d + k) rfl).hom
          (A ⊗ₜ α))) =
      (localHomologyMap R₂ Θ hΘF (d + k)).hom X :=
    calc _ = (localHomologyMap R₂ Φ hΦS (d + k)).hom
            (crossG.hom ((fiberLocalization R π (x₀ : M) d).hom A ⊗ₜ α)) :=
          (ConcreteCategory.congr_hom (homologyMap_comp_fiberLocalization R₂ Φ hΦ (x₀ : M) (d + k))
            _).trans
              (congrArg _ (fiberLocalization_singularHomologyCross_tmul R R π (x₀ : M) rfl A α))
      _ = (localHomologyMap R₂ Φ hΦS (d + k)).hom
            (crossG.hom ((localHomologyMap R sU hsU' d).hom oU ⊗ₜ (ℓ • α))) := by
          refine (o.localHomologyMap_actionMap_singularHomologyCrossRel_eq_zsmul hd b₀ hU x₀ π hπ
            hloc sU hsU hsU' hfix hΦS
            (o.localHomologyMap_fiberLocalization_of_homologyMap_eq_zsmul hd π hA x₀)).trans ?_
          -- The `ℤ`-action on these carriers is `zsmul`, so name Mathlib's instance for it.
          exact congrArg _ (congrArg _ ((CompatibleSMul.int (R := ℤ)).smul_tmul ℓ _ α))
      _ = _ :=
          (congrArg _ (singularHomologyCrossRel_localHomologyMap_tmul R R sU hsU' rfl oU
            (ℓ • α))).trans (ConcreteCategory.congr_hom
              (localHomologyMap_comp R₂ (sU.prodMap (ContinuousMap.id F)) Φ hsF hΦS (d + k)) X)
  rw [livesOverFundamentalClass_iff, key]
  exact (map_ne_zero_iff _ ((ModuleCat.mono_iff_injective _).1 inferInstance)).2
    (o.singularHomologyCrossRel_localHomologyIsoOfIsOpenEmbedding_inv_ne_zero hd
      hU.isOpenEmbedding_subtypeVal x₀ rfl hα)

/-- **Action classes living over the fundamental class.** Under the hypotheses of
`TauCeti.HomologicalOrientation.livesOverFundamentalClass_actionMap_singularHomologyCross` (the
orbit map `π : G → M`, `g ↦ g • x₀`, has continuous local sections around every point,
`π_* A = ℓ • [M]`, `ℓ • α ≠ 0`, and `α` is fixed by the stabilizer of `x₀`), the class
`TauCeti.BasedMap.actionClass b₀ x₀ A α`, with coefficients identified with `ℤ`, lives over the
fundamental class of `M` at `x₀` for evaluation at `b₀`. -/
theorem livesOverFundamentalClass_actionClass {B : Type} [TopologicalSpace B] (b₀ : B)
    {x₀ : M} (π : C(G, M)) (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z) {ℓ : ℤ}
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = ℓ • o.fundamentalClass hd) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)} (hα : ℓ • α ≠ 0)
    (hfix : ∀ h : MulAction.stabilizer G x₀,
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨(h • · : BasedMap B M b₀ x₀ →
        BasedMap B M b₀ x₀), continuous_const_smul h⟩)) (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom α =
          α) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval b₀) x₀
      (BasedMap.actionClass b₀ x₀ A α) := by
  have h := (livesOverFundamentalClass_homologyMap_coefficient_iff _
    (ModuleCat.uliftTensorSelfIso ℤ)).2
      (o.livesOverFundamentalClass_actionMap_singularHomologyCross hd b₀ π hπ hloc hA hα hfix)
  -- Identify the coefficients before the action map, as in `BasedMap.actionClass`.
  rwa [homologyMap_chainComplexFunctor_map_apply _ _
    ((TopCat.singularHomologyCross (TopCat.of G) (TopCat.of (BasedMap B M b₀ x₀))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
        (A ⊗ₜ α))] at h

/-! ### Abundance criteria from a group action -/

/-- **Abundance with 2-spheres from a group action, above the dimension**: a criterion for
abundance (Barraud–Damian–Humilière–Oancea, Definition 6.11) by a witness of degree above `d`,
coming from a group action. Propositions 6.29 and 6.33 of the source follow from it and from its
degree-zero counterpart
`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_sub_homologyMap_const_ne_zero`;
see `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_nontrivial_homotopyGroup_two`,
`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_zpow_ne_one` and
`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_exists_nontrivial_homotopyGroup`.

Let a topological group `G` act on a compact oriented `d`-manifold `M`, with orbit map
`π : G → M`, `g ↦ g • x₀`, having continuous local sections around every point. If some
`A ∈ H_d(G; ℤ)` satisfies `π_* A = ℓ • [M]` and some class `α` of positive degree of the based
mapping space `Map_*(S², M)` satisfies `ℓ • α ≠ 0` and is fixed by every element of the stabilizer
of `x₀`, then `M` is abundant with 2-spheres at `x₀`. When the stabilizer is path connected, every
class is fixed (`JoinedIn.homologyMap_stabilizer_smul_apply`). -/
theorem isAbundantWithTwoSpheres_of_smul_ne_zero {x₀ : M} (π : C(G, M))
    (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z) {ℓ : ℤ}
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = ℓ • o.fundamentalClass hd) {k : ℕ} (hk : 0 < k)
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 M Sphere2.north x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)} (hα : ℓ • α ≠ 0)
    (hfix : ∀ h : MulAction.stabilizer G x₀,
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨(h • · : BasedMap Sphere2 M
        Sphere2.north x₀ → BasedMap Sphere2 M Sphere2.north x₀), continuous_const_smul h⟩))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom α = α) :
    IsAbundantWithTwoSpheres M d x₀ :=
  isAbundantWithTwoSpheres_of_lt
    (o.livesOverFundamentalClass_actionClass hd Sphere2.north π hπ hloc hA hα hfix) (by omega)

/-- **Abundance with 2-spheres from a group action, in the dimension**: a criterion for abundance
(Barraud–Damian–Humilière–Oancea, Definition 6.11) by a witness of degree `d`, coming from a group
action, used for the case `π₂(M) ≠ 0` of Propositions 6.29 and 6.33. In the
setting of `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_ne_zero`, let
`α ∈ H₀(Map_*(S², M); ℤ)` be a class such that `ℓ • (α - c_* α) ≠ 0`, where `c` is the constant
self-map of `Map_*(S², M)` at the constant sphere at `x₀`. For `ℓ = 1` this says that `α` is not
a multiple of the class of the constant sphere, that is, it is nonzero in `H₀(Ω²M, pt)`. If `α`
is fixed by every element of the stabilizer of `x₀`, then `Φ_*(A × α)` lives over the fundamental
class of `M` and its localization at the fibre over `x₀` is not that of a class of constant
spheres, so `M` is abundant with 2-spheres at `x₀`. -/
theorem isAbundantWithTwoSpheres_of_smul_sub_homologyMap_const_ne_zero {x₀ : M} (π : C(G, M))
    (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z) {ℓ : ℤ}
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = ℓ • o.fundamentalClass hd)
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 M Sphere2.north x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) 0 : ModuleCat.{0} ℤ)}
    (hα : ℓ • (α - (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const
      (BasedMap Sphere2 M Sphere2.north x₀) ⟨ContinuousMap.const Sphere2 x₀, rfl⟩)))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) 0).hom α) ≠ 0)
    (hfix : ∀ h : MulAction.stabilizer G x₀,
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨(h • · : BasedMap Sphere2 M
        Sphere2.north x₀ → BasedMap Sphere2 M Sphere2.north x₀), continuous_const_smul h⟩))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) 0).hom α = α) :
    IsAbundantWithTwoSpheres M d x₀ := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let c := (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const
    (BasedMap Sphere2 M Sphere2.north x₀)
      (⟨ContinuousMap.const Sphere2 x₀, rfl⟩ : BasedMap Sphere2 M Sphere2.north x₀)))) R 0).hom
  have hℓα : ℓ • α ≠ 0 := fun h ↦ hα <|
    calc ℓ • (α - c α) = ℓ • α - ℓ • c α := zsmul_sub _ _ _
      _ = 0 := by rw [← map_zsmul, h, map_zero, sub_zero]
  refine isAbundantWithTwoSpheres_of_livesOverFundamentalClass_sub
    (α := BasedMap.actionClass Sphere2.north x₀ A α)
    (o.livesOverFundamentalClass_actionClass hd Sphere2.north π hπ hloc hA hℓα hfix) ?_
  -- The stabilizer fixes the constant sphere, hence `c_* α`, hence `α - c_* α`.
  have hfix' : ∀ h : MulAction.stabilizer G x₀,
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨(h • · : BasedMap Sphere2 M
        Sphere2.north x₀ → BasedMap Sphere2 M Sphere2.north x₀), continuous_const_smul h⟩))
          R 0).hom (α - c α) = α - c α := fun h ↦ by
    let Y := BasedMap Sphere2 M Sphere2.north x₀
    have hc : (⟨(h • · : Y → Y), continuous_const_smul h⟩ : C(Y, Y)).comp
        (ContinuousMap.const Y (⟨ContinuousMap.const Sphere2 x₀, rfl⟩ : Y)) =
        ContinuousMap.const Y (⟨ContinuousMap.const Sphere2 x₀, rfl⟩ : Y) :=
      ContinuousMap.ext fun _ ↦ Subtype.ext (ContinuousMap.ext fun _ ↦ h.property)
    rw [map_sub, hfix h]
    congr 1
    simp only [c]
    rw [← ConcreteCategory.comp_apply, ← SSet.homologyMap_comp, ← Functor.map_comp,
      ← TopCat.ofHom_comp, hc]
  -- The self-map `f ↦ const (f(north))` sends `Φ_*(A × α)` to `Φ_*(A × c_* α)`, and
  -- `ℓ • (α - c_* α) ≠ 0`.
  have h := o.livesOverFundamentalClass_actionClass hd Sphere2.north π hπ hloc hA hα hfix'
  rwa [map_sub, ← BasedMap.homologyMap_const'_comp_mappingSpaceEval_actionClass] at h

/-! ### Abundance from higher homotopy groups (Propositions 6.29 and 6.33) -/

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
  refine o.isAbundantWithTwoSpheres_of_smul_sub_homologyMap_const_ne_zero hd π hπ hloc hA
    (α := (singularHomology₀Section R (X := TopCat.of Y) y₁).hom (ULift.up 1)) ?_
    fun h ↦ (hstab.joinedIn 1 (one_smul _ _) h h.property).homologyMap_stabilizer_smul_apply _ _ _
  -- `c_* [y₁] = [y₀]`, and `ℓ • ([y₁] - [y₀]) ≠ 0`.
  have key := smul_sub_singularHomology₀Section_apply_ne_zero (M := R) (X := TopCat.of Y)
    (r := ULift.up 1) hy₁ (c := ℓ) fun h ↦ hℓ <| by
      simpa [R, ULift.smul_down] using congrArg ULift.down h
  rw [homologyMap_singularHomology₀Section_apply]
  simp only [TopCat.hom_ofHom, ContinuousMap.const_apply, ← int_smul_eq_zsmul]
  exact key

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
  refine o.isAbundantWithTwoSpheres_of_smul_ne_zero hd π hπ hloc hA (Nat.succ_pos n)
    (α := ι.hom (h (Additive.ofMul g))) ?_
    fun s ↦ (hstab.joinedIn 1 (one_smul _ _) s s.property).homologyMap_stabilizer_smul_apply _ _ _
  rw [← map_zsmul, ← map_zsmul, ← ofMul_zpow]
  intro h0
  have hι : Function.Injective ι.hom := (ModuleCat.mono_iff_injective ι.hom).1 inferInstance
  have h₁ : h (Additive.ofMul (g ^ ℓ)) = 0 := hι (h0.trans (map_zero _).symm)
  exact hg (Additive.ofMul.injective (h.injective (h₁.trans (map_zero h).symm)))

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

end LivesOver

end HomologicalOrientation

end TauCeti

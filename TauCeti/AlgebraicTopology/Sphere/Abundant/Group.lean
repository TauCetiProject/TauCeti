/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Aspherical
public import TauCeti.AlgebraicTopology.Sphere.Abundant.Basic
public import TauCeti.Topology.MappingSpace.Group
public import TauCeti.Topology.MappingSpace.Sphere.Basic
public import Mathlib.Analysis.Quaternion
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected

/-!
# Topological groups abundant with two-spheres

Let `G` be a compact oriented `n`-manifold which is a topological group, such as a compact
connected Lie group. Maps of the sphere into `G` split off their value at the north pole: the
homeomorphism `G × Map_*(S², G) ≃ₜ Map(S², G)`, `(g, f) ↦ g · f`
(`TauCeti.mappingSpaceGroupHomeomorph`), lies over `G`, where `Map_*(S², G)` consists of the maps
sending the north pole to `1`, a model of `Ω²G`. Barraud, Damian, Humilière and Oancea observe
(their Example 6.30) that for every nonzero class `α` of the reduced homology of `Ω²G`, the image
of the cross product `[G] × α` under this homeomorphism witnesses that `G` is abundant with
2-spheres.

For a class of positive degree
(`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_ne_zero`) the cross product `[G] × α`
lives over the fundamental class of `G` for the projection `G × Ω²G → G`
(`HomologicalOrientation.livesOverFundamentalClass_singularHomologyCross_fundamentalClass_iff`),
its coefficients `ℤ ⊗ ℤ` are identified with `ℤ`
(`TauCeti.livesOverFundamentalClass_homologyMap_coefficient_iff`), and it is carried to
`Map(S², G)` by a homeomorphism over `G`
(`TauCeti.livesOverFundamentalClass_homologyMap_iff_of_comp_eq_id`). Its degree is `n + deg α`,
above the dimension.

A class `α` of degree zero is nonzero in `H₀(Ω²G, pt)`, the reduced zeroth homology, exactly
when it is not an integral multiple of the class `[1]` of the constant map; such classes exist
exactly when `π₂(G)` is nontrivial. Then `[G] × α` has degree `n`, and the second condition of
Definition 6.11 asks that its localization at the fibre over `b` not be that of a class of the
constant spheres `G → Map(S², G)`. The constant sphere at `g` is the image of `(g, 1)`, and by the
unit law for the cross product with the class of a point
(`TopCat.singularHomologyCross_singularHomology₀Section`) the image of the fundamental class under
the constant spheres is the image of `[G] × [1]`. Every class of the local homology of `G` at `b`
is a multiple `m • [G]_b` of the local orientation, so a coincidence of localizations would make
`[G] × (α - m • [1])` fail to live over the fundamental class, although `α - m • [1] ≠ 0`
(`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_forall_ne_zsmul`).

By Lemma 3.41 of the source (`TauCeti.isAspherical_iff_doubleLoopSpace_singularHomology`), a
path-connected space is aspherical exactly when its double loop space is path connected with
vanishing positive-degree integral homology. If `G` is not aspherical, then either `Ω²G` has a
nonzero class of positive degree, or it is not path connected, and the class of a double loop
which is not joined to the constant one is not a multiple of `[1]`. Either way `G` is abundant with
2-spheres (`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_not_isAspherical`). This
applies to every compact connected Lie group which is not aspherical, with no hypothesis on
`π₂(G)`.

The unit quaternions `S³ = SU(2)` are simply connected, hence orientable, with `π₃(S³) ≅ ℤ`, so
they are not aspherical and are abundant with 2-spheres
(`TauCeti.isAbundantWithTwoSpheres_sphere_quaternion`).

## Main results

* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_ne_zero`: a nonzero class of
  positive degree of `Ω²G` makes `G` abundant with 2-spheres.
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_forall_ne_zsmul`: so does a class of
  degree zero which is not a multiple of the class of the constant map.
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_not_isAspherical`: a
  path-connected `G` which is not aspherical is abundant with 2-spheres.
* `TauCeti.isAbundantWithTwoSpheres_sphere_quaternion`: the unit quaternions `S³` are abundant
  with 2-spheres.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 6.11, Lemma 3.41,
  Example 6.30 and Proposition 6.31.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory TensorProduct Metric Module
open scoped Topology Quaternion

namespace TauCeti

namespace HomologicalOrientation

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {n : ℕ}
  {G : Type} [TopologicalSpace G] [T2Space G] [CompactSpace G] [ChartedSpace V G] [Group G]
  [IsTopologicalGroup G] (o : HomologicalOrientation G V n) (hn : Module.finrank ℝ V = n)

/-- The identification `ℤ ⊗ ℤ ≅ ℤ` of the coefficients of a cross product of integral classes,
by multiplication. -/
private def uliftTensorIso :
    ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ) ≅ ModuleCat.of ℤ (ULift.{0} ℤ) :=
  let e : ModuleCat.of ℤ (ULift.{0} ℤ) ≅ 𝟙_ (ModuleCat.{0} ℤ) :=
    (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso
  tensorIso e e ≪≫ λ_ (𝟙_ _) ≪≫ e.symm

/-- The class `Ψ_*([G] × α) ∈ Hₘ(Map(S², G); ℤ)` of a class `α ∈ Hₖ(Map_*(S², G); ℤ)`, for
`n + k = m`: the cross product with the fundamental class, with its coefficients `ℤ ⊗ ℤ`
identified with `ℤ`, carried along `Ψ : G × Map_*(S², G) ≃ₜ Map(S², G)`. -/
private def sphereCrossClass {k m : ℕ} (h : n + k = m) :
    ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 G Sphere2.north 1))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ) →ₗ[ℤ]
      ((TopCat.toSSet.obj (TopCat.of C(Sphere2, G))).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) m :
        ModuleCat.{0} ℤ) :=
  (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
      (mappingSpaceGroupHomeomorph (G := G) Sphere2.north :
        C(G × BasedMap Sphere2 G Sphere2.north 1, C(Sphere2, G)))))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) m).hom ∘ₗ
    (HomologicalComplex.homologyMap (((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map
      uliftTensorIso.hom).app (TopCat.toSSet.obj
        (TopCat.of (G × BasedMap Sphere2 G Sphere2.north 1)))) m).hom ∘ₗ
    (TopCat.singularHomologyCross (TopCat.of G) (TopCat.of (BasedMap Sphere2 G Sphere2.north 1))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) n k m h).hom ∘ₗ
    TensorProduct.mk ℤ
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of G))
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of (BasedMap Sphere2 G Sphere2.north 1)))
      (o.fundamentalClass hn)

/-- The class `Ψ_*([G] × α)` lives over the fundamental class of `G` exactly when `α ≠ 0`. -/
private theorem livesOverFundamentalClass_sphereCrossClass_iff (b : G) {k m : ℕ} (h : n + k = m)
    (α : ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 G Sphere2.north 1))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval Sphere2.north) b
        (sphereCrossClass o hn h α) ↔ α ≠ 0 := by
  let Ψ := mappingSpaceGroupHomeomorph (G := G) Sphere2.north
  have hτ : (Ψ.symm : C(C(Sphere2, G), G × BasedMap Sphere2 G Sphere2.north 1)).comp Ψ =
      ContinuousMap.id _ :=
    Ψ.symm_comp_toContinuousMap
  have h₁ : mappingSpaceEval Sphere2.north ∘ Ψ = id ∘ Prod.fst := funext fun x ↦ by
    simp [Ψ, x.2.2]
  have h₂ : (id ∘ Prod.fst) ∘ Ψ.symm = mappingSpaceEval Sphere2.north := funext fun f ↦ by
    simp [Ψ]
  -- Carry the class back along the homeomorphism over `G`, identify the coefficients `ℤ ⊗ ℤ`
  -- with `ℤ`, and use that `[G] × α` lives over the fundamental class exactly when `α ≠ 0`.
  exact (livesOverFundamentalClass_homologyMap_iff_of_comp_eq_id (ModuleCat.of ℤ (ULift.{0} ℤ))
    (Ψ : C(G × BasedMap Sphere2 G Sphere2.north 1, C(Sphere2, G)))
    (Ψ.symm : C(C(Sphere2, G), G × BasedMap Sphere2 G Sphere2.north 1)) hτ h₁ h₂).trans <|
      (livesOverFundamentalClass_homologyMap_coefficient_iff
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) uliftTensorIso).trans <|
        o.livesOverFundamentalClass_singularHomologyCross_fundamentalClass_iff hn b h

include o hn in
/-- **A topological group with a nonzero class of positive degree in its double loop space is
abundant with 2-spheres** (Barraud–Damian–Humilière–Oancea, Example 6.30). Let `G` be a compact
oriented `n`-manifold which is a topological group, and let `α` be a nonzero class of positive
degree `k` of the based mapping space `Map_*(S², G)` of maps sending the north pole to `1`, a
model of `Ω²G`. Then the image of `[G] × α` under `G × Map_*(S², G) ≃ₜ Map(S², G)` lives over the
fundamental class of `G` at every point `b`, so `G` is abundant with 2-spheres at `b`. -/
theorem isAbundantWithTwoSpheres_of_ne_zero (b : G) {k : ℕ} (hk : 0 < k)
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 G Sphere2.north 1))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)} (hα : α ≠ 0) :
    IsAbundantWithTwoSpheres G n b :=
  isAbundantWithTwoSpheres_of_lt
    ((livesOverFundamentalClass_sphereCrossClass_iff o hn b (m := n + k) rfl α).2 hα) (by omega)

/-- The class of the constant spheres: `Ψ_*([G] × [1])` is the image of the fundamental class
under the constant spheres `G → Map(S², G)`. -/
private theorem sphereCrossClass_singularHomology₀Section :
    sphereCrossClass o hn (add_zero n) ((singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ))
      (X := TopCat.of (BasedMap Sphere2 G Sphere2.north 1)) ⟨1, rfl⟩).hom (ULift.up 1)) =
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
        (ContinuousMap.const' : C(G, C(Sphere2, G))))) (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom
        (o.fundamentalClass hn) := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let e : R ≅ 𝟙_ (ModuleCat.{0} ℤ) := (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso
  let i : TopCat.of G ⟶ TopCat.of G ⊗ TopCat.of (BasedMap Sphere2 G Sphere2.north 1) :=
    CartesianMonoidalCategory.lift (𝟙 _) (TopCat.ofHom (ContinuousMap.const G ⟨1, rfl⟩))
  let Ψ : C(G × BasedMap Sphere2 G Sphere2.north 1, C(Sphere2, G)) :=
    mappingSpaceGroupHomeomorph (G := G) Sphere2.north
  -- The coefficient map `r ↦ r ⊗ 1` followed by `ℤ ⊗ ℤ ≅ ℤ` is the identity.
  have hcoef : ((ρ_ R).inv ≫ R ◁ e.inv) ≫ uliftTensorIso.hom = 𝟙 R := by
    ext ⟨r⟩
    simp [uliftTensorIso, e, ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
      ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
  -- `Ψ (g, 1)` is the constant map at `g`.
  have hΨ : i ≫ TopCat.ofHom Ψ = TopCat.ofHom ContinuousMap.const' := by
    refine TopCat.hom_ext (ContinuousMap.ext fun g ↦ ?_)
    -- `i ≫ ofHom Ψ` is well typed only after unfolding `G ⊗ Y` to `of (G × Y)`, so neither
    -- `TopCat.hom_comp` nor `TopCat.lift_apply` rewrites it. The composite sends `g` to
    -- `Ψ (g, 1)` by these two (`rfl`) lemmas, which we state with `change`.
    change Ψ (g, ⟨1, rfl⟩) = ContinuousMap.const' g
    simp [Ψ, ContinuousMap.coe_const']
  -- The cross product with the class of the constant map `1` is the inclusion `g ↦ (g, 1)`,
  -- with the coefficient map `r ↦ r ⊗ 1`.
  have hF : (ρ_ _).inv ≫ (_ ◁ (e.inv ≫ singularHomology₀Section R
      (X := TopCat.of (BasedMap Sphere2 G Sphere2.north 1)) ⟨1, rfl⟩)) ≫
      TopCat.singularHomologyCross (TopCat.of G) (TopCat.of (BasedMap Sphere2 G Sphere2.north 1))
        R R n 0 n (add_zero n) ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).map
        uliftTensorIso.hom).app _ ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj R).map
        (TopCat.ofHom Ψ) =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj R).map
        (TopCat.ofHom ContinuousMap.const') := by
    rw [TopCat.singularHomologyCross_singularHomology₀Section_assoc (TopCat.of G)
      (TopCat.of (BasedMap Sphere2 G Sphere2.north 1)) R R n ⟨1, rfl⟩ e.inv,
      ← NatTrans.naturality_assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp, hcoef,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
    exact (CategoryTheory.Functor.map_comp _ i (TopCat.ofHom Ψ)).symm.trans (congrArg _ hΨ)
  -- At `[G]`, the left side of `hF` is `Ψ_*([G] × [1])` definitionally: the unitor and the
  -- whiskering send `[G]` to `[G] ⊗ₜ [1]` (`ModuleCat.MonoidalCategory.rightUnitor_inv_apply`,
  -- `ModuleCat.MonoidalCategory.whiskerLeft_apply`), the space maps are `SSet.homologyMap`
  -- (`singularHomologyFunctor_obj_map`), all `rfl`, and by definition of `singularHomologyFunctor`
  -- its coefficient map is the homology map of `(SSet.chainComplexFunctor _).map`. None of these
  -- rewrites in `hF`, whose composite with `ofHom Ψ` is well typed only up to `G ⊗ Y = of (G × Y)`.
  exact ConcreteCategory.congr_hom hF (o.fundamentalClass hn)

include o hn in
/-- **A topological group with a class of degree zero in its double loop space which is not a
multiple of the class of the constant sphere is abundant with 2-spheres**
(Barraud–Damian–Humilière–Oancea, Example 6.30, in degree zero). Let `G` be a compact oriented
`n`-manifold which is a topological group, and let `α ∈ H₀(Map_*(S², G); ℤ)` not be an integral
multiple of the class of the constant map `1`, that is, `α` is nonzero in `H₀(Ω²G, pt; ℤ)`. Then
the image of `[G] × α` under `G × Map_*(S², G) ≃ₜ Map(S², G)` lives over the fundamental class of
`G` at every point `b`, and its localization at the fibre over `b` is not that of a class of the
constant spheres, so `G` is abundant with 2-spheres at `b`. -/
theorem isAbundantWithTwoSpheres_of_forall_ne_zsmul (b : G)
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 G Sphere2.north 1))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) 0 : ModuleCat.{0} ℤ)}
    (hα : ∀ m : ℤ, α ≠ m • (singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ))
      (X := TopCat.of (BasedMap Sphere2 G Sphere2.north 1)) ⟨1, rfl⟩).hom (ULift.up 1)) :
    IsAbundantWithTwoSpheres G n b := by
  let u : ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 G Sphere2.north 1))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) 0 : ModuleCat.{0} ℤ) :=
    (singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ))
      (X := TopCat.of (BasedMap Sphere2 G Sphere2.north 1)) ⟨1, rfl⟩).hom (ULift.up 1)
  have hα₀ : α ≠ 0 := fun h ↦ hα 0 (h.trans (zero_smul ℤ _).symm)
  refine isAbundantWithTwoSpheres_of_eq
    ((livesOverFundamentalClass_sphereCrossClass_iff o hn b (add_zero n) α).2 hα₀) fun β hβ ↦ ?_
  -- A class of the local homology of `G` at `b` is a multiple `m • o b` of the local orientation,
  -- and its image under the constant spheres is the localization of `m • Ψ_*([G] × [1])`.
  obtain ⟨m, rfl⟩ := (isLocalOrientation_iff b n _).1 (o b).2 β
  have hconst : (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ContinuousMap.const'
      (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north b) n).hom (o b).val =
      (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval Sphere2.north) b n).hom
        (sphereCrossClass o hn (add_zero n) u) := by
    rw [sphereCrossClass_singularHomology₀Section, ← o.fiberLocalization_id_fundamentalClass hn b,
      ← ModuleCat.comp_apply, ← ModuleCat.comp_apply]
    exact congrArg (fun f ↦ f.hom (o.fundamentalClass hn))
      (homologyMap_comp_fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) ContinuousMap.const'
        (congrArg DFunLike.coe (mappingSpaceEval_comp_const' Sphere2.north)) b n).symm
  rw [map_zsmul, hconst, ← map_zsmul, ← map_zsmul] at hβ
  -- So `Ψ_*([G] × (α - m • [1]))` would not live over the fundamental class.
  refine (livesOverFundamentalClass_iff _ _ _ _).1
    ((livesOverFundamentalClass_sphereCrossClass_iff o hn b (add_zero n) (α - m • u)).2
      (sub_ne_zero.2 (hα m))) ?_
  rw [map_sub, map_sub, hβ, sub_self]

include o hn in
/-- **A non-aspherical topological group is abundant with 2-spheres**
(Barraud–Damian–Humilière–Oancea, Example 6.30). Let `G` be a path-connected compact oriented
`n`-manifold which is a topological group, for instance a compact connected Lie group. If `G` is
not aspherical, then `G` is abundant with 2-spheres at every point. -/
theorem isAbundantWithTwoSpheres_of_not_isAspherical [PathConnectedSpace G] (b : G)
    (hG : ¬IsAspherical G 1) :
    IsAbundantWithTwoSpheres G n b := by
  -- By Lemma 3.41 of the source, either the double loop space of `G` is not path connected, or it
  -- has a nonzero integral homology class of positive degree.
  rw [isAspherical_iff_doubleLoopSpace_singularHomology] at hG
  push Not at hG
  let e := BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2 ⟨G, 1⟩
    Sphere2.north
  by_cases hpc : PathConnectedSpace (LoopSpace (LoopSpace G 1) (Path.refl 1))
  · obtain ⟨m, hm₀, hm⟩ := hG hpc
    -- Transport the nonzero homology group of the double loop space to `Map_*(S², G)`, with
    -- coefficients `ULift ℤ`.
    have hY : ¬IsZero ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 G Sphere2.north 1))).homology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) m) := fun h ↦ hm (h.of_iso
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) m).mapIso
        (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso.symm).app _ ≪≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) m).obj
          (ModuleCat.of ℤ (ULift.{0} ℤ))).mapIso (TopCat.isoOfHomeo e.symm)))
    rw [ModuleCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial] at hY
    obtain ⟨α, hα⟩ := exists_ne (0 : ((TopCat.toSSet.obj
      (TopCat.of (BasedMap Sphere2 G Sphere2.north 1))).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) m :
        ModuleCat ℤ))
    exact o.isAbundantWithTwoSpheres_of_ne_zero hn b (Nat.pos_of_ne_zero hm₀) hα
  · -- Some based map `γ` is not joined to the constant map `1`, so its class is not a multiple of
    -- the class of `1`.
    obtain ⟨γ, hγ⟩ : ∃ γ : BasedMap Sphere2 G Sphere2.north 1, ¬Joined γ ⟨1, rfl⟩ := by
      by_contra! h
      have : PathConnectedSpace (BasedMap Sphere2 G Sphere2.north 1) :=
        ⟨⟨⟨1, rfl⟩⟩, fun x y ↦ (h x).trans (h y).symm⟩
      exact hpc (Homeomorph.pathConnectedSpace e)
    refine o.isAbundantWithTwoSpheres_of_forall_ne_zsmul hn b
      (α := (singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ))
        (X := TopCat.of (BasedMap Sphere2 G Sphere2.north 1)) γ).hom (ULift.up 1)) fun m h ↦ ?_
    refine singularHomology₀Section_apply_ne_smul_of_not_joined (k := ℤ)
      (M := ModuleCat.of ℤ (ULift.{0} ℤ)) (X := TopCat.of (BasedMap Sphere2 G Sphere2.north 1))
      hγ (r := ULift.up 1) (fun h ↦ one_ne_zero (congrArg ULift.down h)) m ?_
    -- the `ℤ`-action of the module structure is the `ℤ`-action of the additive group
    exact h.trans (int_smul_eq_zsmul _ _ _).symm

end HomologicalOrientation

/-- **The unit quaternions are abundant with 2-spheres.** The sphere `S³ ⊆ ℍ`, the group `SU(2)`,
is a compact simply connected `3`-manifold and a topological group with `π₃(S³) ≠ 0`, so it is
not aspherical and is abundant with 2-spheres at every point. -/
theorem isAbundantWithTwoSpheres_sphere_quaternion (b : sphere (0 : ℍ) 1) :
    IsAbundantWithTwoSpheres (sphere (0 : ℍ) 1) 3 b := by
  have : Fact (finrank ℝ ℍ = 3 + 1) := ⟨Quaternion.finrank_eq_four⟩
  have hrank : 2 < Module.rank ℝ ℍ := by
    rw [← Module.finrank_eq_rank, Quaternion.finrank_eq_four]
    norm_num
  have : SimplyConnectedSpace (sphere (0 : ℍ) 1) := simplyConnectedSpace_sphere hrank 0 zero_le_one
  -- A simply connected manifold is orientable.
  obtain ⟨o⟩ := HomologicalOrientation.nonempty_of_simplyConnectedSpace
    (M := sphere (0 : ℍ) 1) (finrank_euclideanSpace_fin (n := 3))
  refine o.isAbundantWithTwoSpheres_of_not_isAspherical (finrank_euclideanSpace_fin (n := 3)) b
    fun h ↦ ?_
  -- `π₃(S³)` is nontrivial, so `S³` is not aspherical.
  have := nontrivial_homotopyGroup_sphere (n := 1) Quaternion.finrank_eq_four
    (1 : sphere (0 : ℍ) 1)
  exact not_subsingleton _ ((isAspherical_iff.1 h).2 1)

end TauCeti

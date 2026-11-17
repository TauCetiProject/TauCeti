/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.ProductBase
public import TauCeti.AlgebraicTopology.Sphere.Abundant.Basic
import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit

/-!
# Products of manifolds abundant with two-spheres

Barraud, Damian, Humilière and Oancea show (their Proposition 6.13) that if `M` is abundant with
2-spheres (`TauCeti.IsAbundantWithTwoSpheres`), then so is `M × N` for every closed oriented
manifold `N` (`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_prod_right`). Their proof
uses `Map(S², M × N) ≅ Map(S², M) × Map(S², N)` and the class `α × [N]`; here `N` is carried by its
constant spheres.

A point `y` of `N` and a map `f : S² → M` give the map `(const y, f) : S² → N × M`. This defines a
map `N × Map(S², M) → Map(S², N × M)` over `N × M` with a left inverse over `N × M`, sending `g` to
the first coordinate of its value at the north pole and its second component. So a class of
`N × Map(S², M)` lives over the fundamental class of `N × M` exactly when its image does. For a
witness `α` of abundance of `M`, the cross product `[N] × α` lives over the fundamental class of
`N × M` because `α` lives over that of `M`
(`livesOverFundamentalClass_prodMap_singularHomologyCross_fundamentalClass_iff`).
Its degree exceeds `n + m` exactly when that of `α` exceeds `m`. In degree `m`, the second condition
of abundance says that `α - ρ_* α` lives over the fundamental class, where `ρ` sends a map to the
constant map at its value at the north pole
(`TauCeti.fiberLocalization_mem_range_localHomologyMap_const'_iff`), and `ρ` commutes with the
construction.

This proves abundance of `N × M`
(`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_prod_left`),
and abundance of `M × N` follows by invariance under homeomorphisms
(`TauCeti.IsAbundantWithTwoSpheres.homeomorph`). Only the separation axiom `T₁` is assumed of `M`,
which enters through the closedness of the fibres of evaluation; the definition of abundance does
not otherwise refer to a manifold structure on `M`.

## Main results

* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_prod_right`: `M × N` is abundant with
  2-spheres when `M` is, for a compact oriented manifold `N`.
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_prod_left`: the same for `N × M`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 6.11 and Proposition 6.13.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory TensorProduct

namespace TauCeti

variable {N M : Type} [TopologicalSpace N] [TopologicalSpace M]

/-- A point of `N` and a map `S² → M` give the map `S² → N × M` which is constant in the first
factor. -/
private def constProdSphereMap : C(N × C(Sphere2, M), C(Sphere2, N × M)) :=
  ⟨fun q ↦ (ContinuousMap.const Sphere2 q.1).prodMk q.2, ContinuousMap.continuous_prodMk_const⟩

/-- A map `S² → N × M` gives the first coordinate of its value at the north pole and its second
component; this is a left inverse of `constProdSphereMap`. -/
private def sphereMapSplit : C(C(Sphere2, N × M), N × C(Sphere2, M)) :=
  ⟨fun g ↦ ((g Sphere2.north).1, ContinuousMap.snd.comp g),
    (continuous_fst.comp (continuous_eval_const _)).prodMk
      (ContinuousMap.continuous_postcomp _)⟩

private theorem sphereMapSplit_comp_constProdSphereMap :
    (sphereMapSplit (N := N) (M := M)).comp constProdSphereMap = ContinuousMap.id _ :=
  ContinuousMap.ext fun _ ↦ rfl

private theorem mappingSpaceEval_comp_constProdSphereMap :
    mappingSpaceEval Sphere2.north ∘ constProdSphereMap (N := N) (M := M) =
      Prod.map id (mappingSpaceEval Sphere2.north) :=
  funext fun _ ↦ by simp [constProdSphereMap, Prod.map]

private theorem prodMap_comp_sphereMapSplit :
    Prod.map id (mappingSpaceEval Sphere2.north) ∘ sphereMapSplit (N := N) (M := M) =
      mappingSpaceEval Sphere2.north :=
  funext fun _ ↦ by simp [sphereMapSplit, Prod.map]

/-- Sending a map to the constant map at its value at the north pole commutes with
`constProdSphereMap`. -/
private theorem constProdSphereMap_comp_prodMap :
    constProdSphereMap.comp (ContinuousMap.prodMap (ContinuousMap.id N)
      (ContinuousMap.const'.comp (mappingSpaceEval (X := M) Sphere2.north))) =
      (ContinuousMap.const'.comp (mappingSpaceEval Sphere2.north)).comp constProdSphereMap :=
  ContinuousMap.ext fun _ ↦ ContinuousMap.ext fun _ ↦ by simp [constProdSphereMap]

namespace HomologicalOrientation

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {n : ℕ}
  [T2Space N] [CompactSpace N] [ChartedSpace V N] (o : HomologicalOrientation N V n)
  (hn : Module.finrank ℝ V = n)

/-- The map sending a class `α` of `Map(S², M)` to a class of `Map(S², N × M)`: the cross product
`[N] × α`, with coefficients `ℤ ⊗ ℤ` identified with `ℤ`, carried to `Map(S², N × M)` along
`constProdSphereMap`. -/
private def prodClass (k : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of C(Sphere2, M))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ) →ₗ[ℤ]
    ((TopCat.toSSet.obj (TopCat.of C(Sphere2, N × M))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + k) : ModuleCat.{0} ℤ) :=
  (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom constProdSphereMap))
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + k)).hom ∘ₗ
  (HomologicalComplex.homologyMap (((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map
    (ModuleCat.uliftTensorSelfIso ℤ).hom).app
      (TopCat.toSSet.obj (TopCat.of (N × C(Sphere2, M))))) (n + k)).hom ∘ₗ
  (TopCat.singularHomologyCross (TopCat.of N) (TopCat.of C(Sphere2, M))
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) n k (n + k) rfl).hom ∘ₗ
  TensorProduct.mk ℤ ((TopCat.toSSet.obj (TopCat.of N)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
    ModuleCat.{0} ℤ) ((TopCat.toSSet.obj (TopCat.of C(Sphere2, M))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ) (o.fundamentalClass hn)

include hn in
/-- The class `prodClass k α` lives over the fundamental class of `N × M` at `(b', b)` exactly when
`α` lives over the fundamental class of `M` at `b`. -/
private theorem livesOverFundamentalClass_prodClass_iff [T1Space M] {k : ℕ} (b' : N) (b : M)
    (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, M))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval Sphere2.north)
        (b', b) (o.prodClass hn k α) ↔
      LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval Sphere2.north)
        b α :=
  (livesOverFundamentalClass_homologyMap_iff_of_comp_eq_id _ constProdSphereMap sphereMapSplit
    sphereMapSplit_comp_constProdSphereMap mappingSpaceEval_comp_constProdSphereMap
    prodMap_comp_sphereMapSplit).trans <|
  (livesOverFundamentalClass_homologyMap_coefficient_iff _
    (ModuleCat.uliftTensorSelfIso ℤ)).trans <|
  o.livesOverFundamentalClass_prodMap_singularHomologyCross_fundamentalClass_iff hn
    (isClosed_singleton.preimage (mappingSpaceEval Sphere2.north).continuous) rfl

include hn in
/-- Sending maps to constant maps at their values at the north pole commutes with `prodClass`. -/
private theorem homologyMap_prodClass {k : ℕ}
    (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, M))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)) :
    (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
      (ContinuousMap.const'.comp (mappingSpaceEval (X := N × M) Sphere2.north))))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + k)).hom (o.prodClass hn k α) =
      o.prodClass hn k ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
        ((ContinuousMap.const' : C(M, C(Sphere2, M))).comp (mappingSpaceEval Sphere2.north))))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom α) := by
  -- `ρ ∘ Ψ = Ψ ∘ (id × ρ_M)`, the coefficient change is natural, and the cross product is natural.
  have h₁ : SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom constProdSphereMap))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + k) ≫
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
        (ContinuousMap.const'.comp (mappingSpaceEval (X := N × M) Sphere2.north))))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + k) =
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.prodMap
        (ContinuousMap.id N)
          ((ContinuousMap.const' : C(M, C(Sphere2, M))).comp (mappingSpaceEval Sphere2.north)))))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + k) ≫
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom constProdSphereMap))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + k) :=
    homologyMap_toSSet_ofHom_comp_comm _ _ constProdSphereMap_comp_prodMap.symm
  have h₂ := congrArg (fun g ↦ HomologicalComplex.homologyMap g (n + k))
    (((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map
      (ModuleCat.uliftTensorSelfIso ℤ).hom).naturality
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.prodMap (ContinuousMap.id N)
        ((ContinuousMap.const' : C(M, C(Sphere2, M))).comp (mappingSpaceEval Sphere2.north))))))
  simp only [HomologicalComplex.homologyMap_comp] at h₂
  have h₃ := ConcreteCategory.congr_hom (TopCat.singularHomologyCross_naturality
    (𝟙 (TopCat.of N)) (TopCat.ofHom ((ContinuousMap.const' : C(M, C(Sphere2, M))).comp
      (mappingSpaceEval Sphere2.north))) (ModuleCat.of ℤ (ULift.{0} ℤ))
    (ModuleCat.of ℤ (ULift.{0} ℤ)) n k (n + k) rfl) (o.fundamentalClass hn ⊗ₜ α)
  rw [CategoryTheory.Functor.map_id] at h₃
  -- `prodClass` is the composite of the linear maps it is built from, so the composite of the
  -- naturality squares `h₃`, `h₂`, `h₁` proves the claim definitionally.
  exact (ConcreteCategory.congr_hom h₁ _).trans (congrArg (SSet.homologyMap (TopCat.toSSet.map
    (TopCat.ofHom constProdSphereMap)) (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + k)).hom
    ((ConcreteCategory.congr_hom h₂ _).symm.trans (congrArg (HomologicalComplex.homologyMap
      (((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).hom).app
          (TopCat.toSSet.obj (TopCat.of (N × C(Sphere2, M))))) (n + k)).hom h₃.symm)))

include o hn in
/-- **Products with a manifold abundant with 2-spheres**, with the oriented factor on the left
(Barraud–Damian–Humilière–Oancea, Proposition 6.13). If `M` is abundant with 2-spheres at `b` in
dimension `m`, then for every compact oriented `n`-manifold `N` and every point `b'` of `N`, the
product `N × M` is abundant with 2-spheres at `(b', b)` in dimension `n + m`. A witness is the cross
product of the fundamental class of `N`, carried by the constant spheres of `N`, with a witness for
`M`. -/
theorem isAbundantWithTwoSpheres_prod_left [T1Space M] {m : ℕ} {b : M}
    (h : IsAbundantWithTwoSpheres M m b) (b' : N) :
    IsAbundantWithTwoSpheres (N × M) (n + m) (b', b) := by
  obtain ⟨k, α, hα, hk⟩ := (isAbundantWithTwoSpheres_iff M m b).1 h
  have hcl := (o.livesOverFundamentalClass_prodClass_iff hn b' b α).2 hα
  rcases hk with hk | ⟨rfl, hk⟩
  · exact isAbundantWithTwoSpheres_of_lt hcl (by omega)
  · -- The localization of `[N] × α` is not that of a class of constant spheres: by
    -- `fiberLocalization_mem_range_localHomologyMap_const'_iff` this says that
    -- `[N] × (α - ρ_* α)` lives over the fundamental class, which it does since `α - ρ_* α` does.
    refine (isAbundantWithTwoSpheres_iff _ _ _).2 ⟨n + k, o.prodClass hn k α, hcl,
      Or.inr ⟨rfl, ?_⟩⟩
    rw [fiberLocalization_mem_range_localHomologyMap_const'_iff, not_not, homologyMap_prodClass,
      ← map_sub, livesOverFundamentalClass_prodClass_iff]
    rwa [fiberLocalization_mem_range_localHomologyMap_const'_iff, not_not] at hk

include o hn in
/-- **Products with a manifold abundant with 2-spheres** (Barraud–Damian–Humilière–Oancea,
Proposition 6.13). If `M` is abundant with 2-spheres at `b` in dimension `m`, then for every compact
oriented `n`-manifold `N` and every point `b'` of `N`, the product `M × N` is abundant with
2-spheres at `(b, b')` in dimension `m + n`. -/
theorem isAbundantWithTwoSpheres_prod_right [T1Space M] {m : ℕ} {b : M}
    (h : IsAbundantWithTwoSpheres M m b) (b' : N) :
    IsAbundantWithTwoSpheres (M × N) (m + n) (b, b') :=
  add_comm n m ▸ (o.isAbundantWithTwoSpheres_prod_left hn h b').homeomorph
    (Homeomorph.prodComm N M)

end HomologicalOrientation

end TauCeti

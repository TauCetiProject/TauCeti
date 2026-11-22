/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic

/-!
# The action of homeomorphisms on singular homology

A homeomorphism `φ` of a topological space `X` induces an automorphism `φ_*` of each singular
homology group `Hₘ(X; R)`, by functoriality of singular homology. Since `(φ ∘ ψ)_* = φ_* ∘ ψ_*`,
this is a group homomorphism from the homeomorphism group to the group of `k`-linear automorphisms
of `Hₘ(X; R)` (`Homeomorph.singularHomologyAction`), for coefficients `R` in a module category over
a ring `k`; with `R = ℤ` it is the action of `X ≃ₜ X` on integral homology.

Homotopic maps induce the same map on singular homology, so a homeomorphism homotopic to the
identity acts trivially (`Homeomorph.singularHomologyAction_eq_one_of_homotopic`): the action of
`φ` depends only on the homotopy class of `φ`.

The factor swap `(x, y) ↦ (y, x)` of `X × X` (`Homeomorph.prodComm`) does not act trivially on
`Hₘ(X × X; R)` in a positive degree `m` in which `Hₘ(X; R)` is nontrivial
(`Homeomorph.singularHomologyAction_prodComm_ne_one`). For a base point `x₀`, the swap exchanges the
images `A = i₁_* a` and `B = i₂_* a` of a nonzero class `a` under the inclusions
`i₁ = (·, x₀)` and `i₂ = (x₀, ·)` of the two factors, and these images differ: the first projection
sends `A` to `a`, while it sends `B` to zero, since `pr₁ ∘ i₂` is constant and factors through a
point, whose homology vanishes in positive degrees. For `X = S²` and `m = 2`, `A` and `B` are the
classes of the two rulings of `S² × S²`, which the swap exchanges.

## Main definitions

* `Homeomorph.singularHomologyAction R m`: the action `φ ↦ φ_*` of `X ≃ₜ X` on `Hₘ(X; R)`.

## Main results

* `Homeomorph.singularHomologyAction_apply`: the action of `φ` is the map induced by `φ`.
* `Homeomorph.singularHomologyMap_symm_apply_apply`,
  `Homeomorph.singularHomologyMap_apply_symm_apply`: the maps induced by a homeomorphism and by its
  inverse are mutually inverse.
* `Homeomorph.singularHomologyAction_eq_one_of_homotopic`: homeomorphisms homotopic to the identity
  act trivially.
* `Homeomorph.singularHomologyAction_prodComm_ne_one`: the factor swap of `X × X` acts nontrivially
  in every positive degree in which `X` has nontrivial homology.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 2.1 (functoriality
  and homotopy invariance of singular homology).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe u

namespace Homeomorph

variable {X : Type u} [TopologicalSpace X] {k : Type u} [Ring k] (R : ModuleCat.{u} k) (m : ℕ)

/-- **The action of homeomorphisms on singular homology.** A homeomorphism `φ` of `X` acts on
`Hₘ(X; R)` by the induced map `φ_*`; this is a group homomorphism from `X ≃ₜ X` to the
`k`-linear automorphisms of `Hₘ(X; R)`. -/
def singularHomologyAction :
    (X ≃ₜ X) →* (((singularHomologyFunctor (ModuleCat.{u} k) m).obj R).obj (TopCat.of X) ≃ₗ[k]
      ((singularHomologyFunctor (ModuleCat.{u} k) m).obj R).obj (TopCat.of X)) where
  toFun φ := (((singularHomologyFunctor (ModuleCat.{u} k) m).obj R).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of X) φ)).toLinearEquiv
  map_one' := by
    ext x
    -- The identity homeomorphism is the identity morphism of `TopCat.of X`.
    have h : TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of X) 1 =
        Iso.refl (TopCat.of X) := by ext; rfl
    simp [h]
  map_mul' φ ψ := by
    ext x
    -- `φ * ψ` is `ψ` followed by `φ`, the composite `ψ ≫ φ` in `TopCat`.
    have h : TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of X) (φ * ψ) =
        TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of X) ψ ≪≫
          TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of X) φ := by
      ext; rfl
    simp [h]

/-- The action of `φ` on `Hₘ(X; R)` is the map induced by `φ` as a morphism of `TopCat`. -/
@[simp]
theorem singularHomologyAction_apply (φ : X ≃ₜ X)
    (x : ((singularHomologyFunctor (ModuleCat.{u} k) m).obj R).obj (TopCat.of X)) :
    singularHomologyAction R m φ x =
      (((singularHomologyFunctor (ModuleCat.{u} k) m).obj R).map
        (TopCat.ofHom (φ : C(X, X)))).hom x :=
  (rfl)

variable {m} in
/-- The map induced on singular homology by the inverse of a homeomorphism `e` undoes the map
induced by `e`. -/
@[simp]
theorem singularHomologyMap_symm_apply_apply {Y : Type u} [TopologicalSpace Y] (e : X ≃ₜ Y)
    (x : ((TauCeti.singularChains k).obj (TopCat.of X)).homology m) :
    ContinuousMap.singularHomologyMap k m (e.symm : C(Y, X))
      (ContinuousMap.singularHomologyMap k m (e : C(X, Y)) x) = x := by
  rw [← ContinuousMap.singularHomologyMap_comp, symm_comp_toContinuousMap,
    ContinuousMap.singularHomologyMap_id]

variable {m} in
/-- The map induced on singular homology by a homeomorphism `e` undoes the map induced by its
inverse. -/
@[simp]
theorem singularHomologyMap_apply_symm_apply {Y : Type u} [TopologicalSpace Y] (e : X ≃ₜ Y)
    (y : ((TauCeti.singularChains k).obj (TopCat.of Y)).homology m) :
    ContinuousMap.singularHomologyMap k m (e : C(X, Y))
      (ContinuousMap.singularHomologyMap k m (e.symm : C(Y, X)) y) = y := by
  rw [← ContinuousMap.singularHomologyMap_comp, toContinuousMap_comp_symm,
    ContinuousMap.singularHomologyMap_id]

variable {R m} in
/-- **Homeomorphisms homotopic to the identity act trivially on singular homology.** -/
theorem singularHomologyAction_eq_one_of_homotopic {φ : X ≃ₜ X}
    (h : (ContinuousMap.id X).Homotopic (φ : C(X, X))) : singularHomologyAction R m φ = 1 := by
  ext x
  have hmap := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (f := 𝟙 (TopCat.of X)) (g := TopCat.ofHom (φ : C(X, X))) h.some R m
  rw [singularHomologyAction_apply, FunLike.coe_one_eq_id, id_eq]
  -- The map induced on singular homology is the homology map of the induced chain map.
  change (HomologicalComplex.homologyMap
    (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map (TopCat.ofHom (φ : C(X, X))))
      m).hom x = x
  rw [← hmap, CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id, ModuleCat.hom_id]
  rfl

/-- **The factor swap acts nontrivially on homology.** If `Hₘ(X; R)` is nontrivial in a positive
degree `m`, the swap `(x, y) ↦ (y, x)` of `X × X` does not act trivially on `Hₘ(X × X; R)`: it
exchanges the images of a nonzero class under the inclusions of the two factors through a base
point, which the first projection separates. -/
theorem singularHomologyAction_prodComm_ne_one [Nonempty X] (hm : m ≠ 0)
    [Nontrivial (((singularHomologyFunctor (ModuleCat.{u} k) m).obj R).obj (TopCat.of X))] :
    singularHomologyAction R m (Homeomorph.prodComm X X) ≠ 1 := by
  intro h
  obtain ⟨x₀⟩ := ‹Nonempty X›
  let F := (singularHomologyFunctor (ModuleCat.{u} k) m).obj R
  obtain ⟨a, ha⟩ := exists_ne (0 : F.obj (TopCat.of X))
  -- The inclusions of the two factors through `x₀` and the first projection.
  let i₁ : C(X, X × X) := ⟨fun x ↦ (x, x₀), by fun_prop⟩
  let i₂ : C(X, X × X) := ⟨fun x ↦ (x₀, x), by fun_prop⟩
  let p₁ : C(X × X, X) := ContinuousMap.fst
  have hswap : TopCat.ofHom i₁ ≫ TopCat.ofHom (Homeomorph.prodComm X X : C(X × X, X × X)) =
      TopCat.ofHom i₂ := rfl
  have hp₁ : TopCat.ofHom i₁ ≫ TopCat.ofHom p₁ = 𝟙 (TopCat.of X) := rfl
  have hp₂ : TopCat.ofHom i₂ ≫ TopCat.ofHom p₁ = TopCat.ofHom (ContinuousMap.const X x₀) := rfl
  -- The swap fixes `A = i₁_* a`, so `i₁_* a = i₂_* a`.
  have hAB : (F.map (TopCat.ofHom i₁)).hom a = (F.map (TopCat.ofHom i₂)).hom a := by
    have := congrArg (fun e ↦ e ((F.map (TopCat.ofHom i₁)).hom a)) h
    simp only [singularHomologyAction_apply, FunLike.coe_one_eq_id, id_eq] at this
    rw [← this, ← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp, hswap]
  -- Applying the first projection gives `a = 0`.
  apply ha
  have := congrArg (F.map (TopCat.ofHom p₁)).hom hAB
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, hp₁, hp₂, CategoryTheory.Functor.map_id,
    TauCeti.singularHomologyFunctor_map_const_eq_zero R x₀ hm] at this
  simpa using this

end Homeomorph

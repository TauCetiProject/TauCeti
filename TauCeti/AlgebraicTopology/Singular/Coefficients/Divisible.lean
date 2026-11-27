/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import TauCeti.Algebra.Group.Equiv.Pow
import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
import TauCeti.AlgebraicTopology.Singular.Coefficients.ULift
import TauCeti.AlgebraicTopology.Singular.Contractible

/-!
# Singular homology with coefficients annihilated by an integer

If `X` is a path-connected space on whose positive-degree integral singular homology
multiplication by `m : ℤ` is bijective, then the singular homology of `X` with coefficients in any
`ℤ`-module `M` annihilated by `m` vanishes in all positive degrees
(`TauCeti.isZero_singularHomology_of_bijective_zsmul_int`).

The proof passes to the universe-lifted ring `ULift.{u} ℤ` (so that `ModuleCat.{u} (ULift.{u} ℤ)`
is monoidal in the universe `u` of `X` and `M`) and considers the chain endomorphism
`m • id + (1 - m) • (π ≫ ι)` of the integral singular chain complex `C_*(X; ULift.{u} ℤ)`, where
`π : X ⟶ PUnit` and `ι : PUnit ⟶ X` factor through a chosen basepoint. On `H₀`, `π ≫ ι` acts as
the identity, so the endomorphism acts as `m + (1 - m) = 1`; on `H_{q + 1}`, the point homology
vanishes, so it acts as multiplication by `m`, which is bijective by assumption. Since
`C_*(X; ULift.{u} ℤ)` is degreewise projective, this quasi-isomorphism is a chain homotopy
equivalence, so it remains a quasi-isomorphism after tensoring with `M`. On the other hand,
tensoring with `M` kills the `m • id` summand (since `m` annihilates `M`) and kills the
point-factorization summand on positive-degree homology (since `PUnit` is contractible), so the
induced isomorphism on `H_{n + 1}(X; M)` is zero and `H_{n + 1}(X; M)` vanishes.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped MonoidalCategory

universe u

namespace TauCeti

/-- The chain endomorphism `m • id + (1 - m) • (π ≫ ι)` of the lifted integral singular chain
complex `C_*(X; ULift.{u} ℤ)`, where `π : X ⟶ PUnit` is the terminal map and `ι : PUnit ⟶ X`
picks out `x : X`. -/
private def zsmulAddProjEndo {X : Type u} [TopologicalSpace X] (x : X) (m : ℤ) :
    ((singularChainComplexFunctor (ModuleCat.{u} (ULift.{u} ℤ))).obj
        (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))).obj (TopCat.of X) ⟶
      ((singularChainComplexFunctor (ModuleCat.{u} (ULift.{u} ℤ))).obj
        (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))).obj (TopCat.of X) :=
  m • 𝟙 _ + (1 - m) •
    (((singularChainComplexFunctor (ModuleCat.{u} (ULift.{u} ℤ))).obj
        (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))).map
          (_root_.TopCat.isTerminalPUnit.from (TopCat.of X)) ≫
      ((singularChainComplexFunctor (ModuleCat.{u} (ULift.{u} ℤ))).obj
        (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))).map
          (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x)))

/-- For a path-connected space `X` whose positive integral homology is uniquely `m`-divisible, the
endomorphism `zsmulAddProjEndo x m` of the lifted integral singular chain complex is a chain
homotopy equivalence. -/
private lemma homotopyEquivalences_zsmul_add_proj {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) (m : ℤ)
    (hX : ∀ q : ℕ, Function.Bijective fun y :
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) (q + 1)).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of X) ↦ m • y) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} (ULift.{u} ℤ)) (.down ℕ)
      (zsmulAddProjEndo x m) := by
  let C := (singularChainComplexFunctor (ModuleCat.{u} (ULift.{u} ℤ))).obj
    (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))
  let p : TopCat.of X ⟶ TopCat.of PUnit.{u + 1} := _root_.TopCat.isTerminalPUnit.from (TopCat.of X)
  let s : TopCat.of PUnit.{u + 1} ⟶ TopCat.of X :=
    TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x)
  have hqi : QuasiIso (zsmulAddProjEndo x m) := (quasiIso_iff _).2 fun q ↦
    (quasiIsoAt_iff_isIso_homologyMap _ q).2 <| by
      let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} (ULift.{u} ℤ)) (.down ℕ) q
      rw [← HomologicalComplex.homologyFunctor_map, zsmulAddProjEndo, H.map_add,
        H.map_zsmul, H.map_zsmul, H.map_id]
      cases q with
      | zero =>
        have hps : H.map (C.map p ≫ C.map s) = 𝟙 _ := by
          rw [← C.map_comp]
          exact singularHomology₀_map_eq_id_of_pathConnectedSpace
            (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ)) (p ≫ s)
        rw [hps, ← add_zsmul, add_sub_cancel, one_zsmul]
        infer_instance
      | succ q =>
        have hP : Limits.IsZero (H.obj (C.obj (TopCat.of PUnit.{u + 1}))) :=
          isZero_singularHomologyFunctor_of_contractibleSpace
            (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ)) (TopCat.of PUnit.{u + 1}) q.succ_ne_zero
        rw [H.map_comp, hP.eq_of_tgt (H.map (C.map p)) 0, Limits.zero_comp, smul_zero, add_zero]
        exact (ConcreteCategory.isIso_iff_bijective _).2
          ((((TopCat.of X).singularHomologyUliftAddEquiv ℤ (q + 1)).bijective_zsmul_iff m).1
            (hX q))
  have (q : ℕ) : Projective ((C.obj (TopCat.of X)).X q) := by
    -- `singularChainComplexFunctor` is definitionally `SSet.chainComplexFunctor` composed with
    -- `TopCat.toSSet`.
    dsimp only [C, singularChainComplexFunctor, SSet.chainComplexFunctor, Functor.comp_obj,
      Functor.whiskeringLeft_obj_obj]
    exact SSet.projective_chainComplex_X_of_projective (TopCat.toSSet.obj (TopCat.of X))
      (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ)) q
  exact (ChainComplex.quasiIso_iff_of_projective (zsmulAddProjEndo x m)).1 hqi

/-- Tensoring `zsmulAddProjEndo x m` with a `ULift.{u} ℤ`-module `M'` annihilated by `m` induces
zero on `(n + 1)`-st homology. -/
private lemma homologyMap_zsmulAddProjEndo_eq_zero {X : Type u} [TopologicalSpace X] (x : X)
    (m : ℤ) (M' : ModuleCat.{u} (ULift.{u} ℤ)) (hmM' : ∀ a : M', m • a = 0) (n : ℕ) :
    HomologicalComplex.homologyMap
      (((MonoidalCategory.tensorLeft M').mapHomologicalComplex (.down ℕ)).map
        (zsmulAddProjEndo x m)) (n + 1) = 0 := by
  let C := (singularChainComplexFunctor (ModuleCat.{u} (ULift.{u} ℤ))).obj
    (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))
  let p : TopCat.of X ⟶ TopCat.of PUnit.{u + 1} := _root_.TopCat.isTerminalPUnit.from (TopCat.of X)
  let s : TopCat.of PUnit.{u + 1} ⟶ TopCat.of X :=
    TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x)
  let F := MonoidalCategory.tensorLeft M'
  let FCh := F.mapHomologicalComplex (.down ℕ)
  -- Multiplication by `m` kills `M'`, hence kills every tensor product `M' ⊗ Y`.
  have hM0 : m • 𝟙 M' = 0 := by ext a; exact hmM' a
  have hkill : m • 𝟙 (FCh.obj (C.obj (TopCat.of X))) = 0 := by
    ext q : 1
    let Y := (C.obj (TopCat.of X)).X q
    have hw : m • 𝟙 (M' ⊗ Y) = (m • 𝟙 M') ▷ Y := by
      rw [← MonoidalCategory.id_whiskerRight, ← MonoidalCategory.curriedTensor_map_app,
        ← Functor.flip_obj_map, ← Functor.map_zsmul, Functor.flip_obj_map,
        MonoidalCategory.curriedTensor_map_app]
    simp [F, FCh, Y, hw, hM0]
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} (ULift.{u} ℤ)) (.down ℕ) (n + 1)
  have hP : Limits.IsZero (H.obj (FCh.obj (C.obj (TopCat.of PUnit.{u + 1})))) :=
    (isZero_singularHomologyFunctor_of_contractibleSpace
      (F.obj (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))) (TopCat.of PUnit.{u + 1})
      n.succ_ne_zero).of_iso
        (H.mapIso ((Functor.singularChainComplexFunctorObjCompMapIso F
          (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))).app (TopCat.of PUnit.{u + 1})))
  have hscalar : H.map (FCh.map (m • 𝟙 (C.obj (TopCat.of X)))) = 0 := by
    rw [FCh.map_zsmul, FCh.map_id, hkill, H.map_zero]
  have hpt : H.map (FCh.map ((1 - m) • (C.map p ≫ C.map s))) = 0 := by
    rw [FCh.map_zsmul, FCh.map_comp, H.map_zsmul, H.map_comp,
      hP.eq_of_tgt (H.map (FCh.map (C.map p))) 0, Limits.zero_comp, smul_zero]
  rw [← HomologicalComplex.homologyFunctor_map, zsmulAddProjEndo, FCh.map_add, H.map_add,
    hscalar, hpt, zero_add]

/-- Vanishing of singular homology with coefficients in the lifted `ℤ`-module
`ModuleCat.of (ULift.{u} ℤ) M` implies vanishing of singular homology with coefficients in `M`. -/
private lemma isZero_singularHomology_of_isZero_ulift {X : Type u} [TopologicalSpace X]
    (M : ModuleCat.{u} ℤ) (k : ℕ)
    (hM' : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{u} (ULift.{u} ℤ)) k).obj
      (ModuleCat.of (ULift.{u} ℤ) M)).obj (TopCat.of X))) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) k).obj M).obj (TopCat.of X)) := by
  let Res := ModuleCat.restrictScalars.{u}
    ((ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm : ℤ →+* ULift.{u} ℤ)
  exact ((Res.isZero_singularHomologyFunctor_iff (ModuleCat.of (ULift.{u} ℤ) M)
    k (TopCat.of X)).2 hM').of_iso
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) k).mapIso
      (ModuleCat.restrictScalarsUliftIso.{u} (R := ℤ) M)).app (TopCat.of X)).symm

/-- If `X` is path-connected and multiplication by `m` is bijective on every positive lifted
integral singular homology group of `X`, then `H_{n + 1}(X; M) = 0` for every `ℤ`-module `M`
annihilated by `m`. -/
theorem isZero_singularHomology_of_bijective_zsmul_int {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] {m : ℤ}
    (hX : ∀ q : ℕ, Function.Bijective fun y :
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) (q + 1)).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of X) ↦ m • y)
    (M : ModuleCat.{u} ℤ) (hmM : ∀ a : M, m • a = 0) (n : ℕ) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 1)).obj M).obj
      (TopCat.of X)) := by
  obtain ⟨x⟩ := PathConnectedSpace.nonempty (X := X)
  let M' : ModuleCat.{u} (ULift.{u} ℤ) := ModuleCat.of (ULift.{u} ℤ) M
  let C := (singularChainComplexFunctor (ModuleCat.{u} (ULift.{u} ℤ))).obj
    (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))
  let F := MonoidalCategory.tensorLeft M'
  let FCh := F.mapHomologicalComplex (.down ℕ)
  have hqi : QuasiIso (FCh.map (zsmulAddProjEndo x m)) :=
    (HomologicalComplex.mem_quasiIso_iff _).1 <|
      homotopyEquivalences_le_quasiIso _ _ _
        (F.homotopyEquivalences_mapHomologicalComplex_map (zsmulAddProjEndo x m)
          (homotopyEquivalences_zsmul_add_proj x m hX))
  have hiso : IsIso (HomologicalComplex.homologyMap (FCh.map (zsmulAddProjEndo x m)) (n + 1)) :=
    (quasiIsoAt_iff_isIso_homologyMap _ (n + 1)).1 ((quasiIso_iff _).1 hqi (n + 1))
  have hzero : HomologicalComplex.homologyMap (FCh.map (zsmulAddProjEndo x m)) (n + 1) = 0 :=
    homologyMap_zsmulAddProjEndo_eq_zero x m M' hmM n
  have hFzero : Limits.IsZero ((FCh.obj (C.obj (TopCat.of X))).homology (n + 1)) :=
    Limits.IsZero.of_epi_eq_zero _ hzero
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} (ULift.{u} ℤ)) (.down ℕ) (n + 1)
  have hM'zero : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{u} (ULift.{u} ℤ))
      (n + 1)).obj M').obj (TopCat.of X)) :=
    (hFzero.of_iso
      (H.mapIso ((Functor.singularChainComplexFunctorObjCompMapIso F
        (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))).app (TopCat.of X))).symm).of_iso
        (((singularHomologyFunctor (ModuleCat.{u} (ULift.{u} ℤ)) (n + 1)).mapIso
          (MonoidalCategory.rightUnitor M')).app (TopCat.of X)).symm
  exact isZero_singularHomology_of_isZero_ulift M (n + 1) hM'zero

end TauCeti

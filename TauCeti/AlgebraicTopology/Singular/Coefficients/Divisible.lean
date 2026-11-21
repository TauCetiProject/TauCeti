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
import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
import TauCeti.AlgebraicTopology.Singular.Contractible

/-!
# Singular homology with coefficients annihilated by an integer

If `X` is a path-connected space on whose positive-degree integral singular homology
multiplication by `m : ℤ` is bijective, then the singular homology of `X` with coefficients in any
`ℤ`-module `M` annihilated by `m` vanishes in all positive degrees
(`TauCeti.isZero_singularHomology_of_bijective_zsmul_int`).

The proof considers the chain endomorphism `m • id + (1 - m) • (π ≫ ι)` of the integral singular
chain complex `C_*(X; ℤ)`, where `π : X ⟶ PUnit` and `ι : PUnit ⟶ X` factor through a chosen
basepoint. On `H₀`, `π ≫ ι` acts as the identity, so the endomorphism acts as `m + (1 - m) = 1`;
on `H_{q + 1}`, the point homology vanishes, so it acts as multiplication by `m`, which is
bijective by assumption. Since `C_*(X; ℤ)` is degreewise projective, this quasi-isomorphism is a
chain homotopy equivalence, so it remains a quasi-isomorphism after tensoring with `M`. On the
other hand, tensoring with `M` kills the `m • id` summand (since `m` annihilates `M`) and kills the
point-factorization summand on positive-degree homology (since `PUnit` is contractible), so the
induced isomorphism on `H_{n + 1}(X; M)` is zero and `H_{n + 1}(X; M)` vanishes.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace TauCeti

/-- The chain endomorphism `m • id + (1 - m) • (π ≫ ι)` of the integral singular chain complex
`C_*(X; ℤ)`, where `π : X ⟶ PUnit` is the terminal map and `ι : PUnit ⟶ X` picks out `x : X`. -/
private def zsmulAddProjEndo {X : Type} [TopologicalSpace X] (x : X) (m : ℤ) :
    (singularChains ℤ).obj (TopCat.of X) ⟶ (singularChains ℤ).obj (TopCat.of X) :=
  m • 𝟙 _ + (1 - m) • ((singularChains ℤ).map (_root_.TopCat.isTerminalPUnit.from (TopCat.of X)) ≫
    (singularChains ℤ).map (TopCat.ofHom (ContinuousMap.const PUnit x)))

/-- For a path-connected space `X` whose positive integral homology is uniquely `m`-divisible, the
endomorphism `zsmulAddProjEndo x m` of the integral singular chain complex is a chain homotopy
equivalence. -/
private lemma homotopyEquivalences_zsmul_add_proj {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) (m : ℤ)
    (hX : ∀ q : ℕ, Function.Bijective fun y :
      ((singularChains ℤ).obj (TopCat.of X)).homology (q + 1) ↦ m • y) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{0} ℤ) (.down ℕ) (zsmulAddProjEndo x m) := by
  let p : TopCat.of X ⟶ TopCat.of PUnit := _root_.TopCat.isTerminalPUnit.from (TopCat.of X)
  let s : TopCat.of PUnit ⟶ TopCat.of X := TopCat.ofHom (ContinuousMap.const PUnit x)
  have hqi : QuasiIso (zsmulAddProjEndo x m) := (quasiIso_iff _).2 fun q ↦
    (quasiIsoAt_iff_isIso_homologyMap _ q).2 <| by
      let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (.down ℕ) q
      rw [← HomologicalComplex.homologyFunctor_map, zsmulAddProjEndo, H.map_add,
        H.map_zsmul, H.map_zsmul, H.map_id]
      cases q with
      | zero =>
        have hps : H.map ((singularChains ℤ).map p ≫ (singularChains ℤ).map s) = 𝟙 _ := by
          rw [← (singularChains ℤ).map_comp]
          exact singularHomology₀_map_eq_id_of_pathConnectedSpace (ModuleCat.of ℤ ℤ) (p ≫ s)
        rw [hps, ← add_zsmul, add_sub_cancel, one_zsmul]
        infer_instance
      | succ q =>
        have hP : Limits.IsZero (H.obj ((singularChains ℤ).obj (TopCat.of PUnit))) :=
          isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of ℤ ℤ)
            (TopCat.of PUnit) q.succ_ne_zero
        rw [H.map_comp, hP.eq_of_tgt (H.map ((singularChains ℤ).map p)) 0, Limits.zero_comp,
          smul_zero, add_zero]
        exact (ConcreteCategory.isIso_iff_bijective _).2 (hX q)
  have (q : ℕ) : Projective (((singularChains ℤ).obj (TopCat.of X)).X q) := by
    -- `singularChains ℤ` on `TopCat.of X` is definitionally `SSet.chainComplex` on
    -- `TopCat.toSSet.obj (TopCat.of X)` with projective coefficients `ModuleCat.of ℤ ℤ`.
    change Projective (((TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℤ ℤ)).X q)
    exact SSet.projective_chainComplex_X_of_projective (TopCat.toSSet.obj (TopCat.of X))
      (ModuleCat.of ℤ ℤ) q
  exact (ChainComplex.quasiIso_iff_of_projective (zsmulAddProjEndo x m)).1 hqi

/-- If `X` is path-connected and multiplication by `m` is bijective on every positive integral
singular homology group of `X`, then `H_{n + 1}(X; M) = 0` for every `ℤ`-module `M` annihilated by
`m`. -/
theorem isZero_singularHomology_of_bijective_zsmul_int {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] {m : ℤ}
    (hX : ∀ q : ℕ, Function.Bijective fun y :
      ((singularChains ℤ).obj (TopCat.of X)).homology (q + 1) ↦ m • y)
    (M : ModuleCat.{0} ℤ) (hmM : ∀ a : M, m • a = 0) (n : ℕ) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj M).obj
      (TopCat.of X)) := by
  obtain ⟨x⟩ := PathConnectedSpace.nonempty (X := X)
  let p : TopCat.of X ⟶ TopCat.of PUnit := _root_.TopCat.isTerminalPUnit.from (TopCat.of X)
  let s : TopCat.of PUnit ⟶ TopCat.of X := TopCat.ofHom (ContinuousMap.const PUnit x)
  let F := MonoidalCategory.tensorLeft M
  let FCh := F.mapHomologicalComplex (.down ℕ)
  have hqi : QuasiIso (FCh.map (zsmulAddProjEndo x m)) :=
    (HomologicalComplex.mem_quasiIso_iff _).1 <|
      homotopyEquivalences_le_quasiIso _ _ _
        (F.homotopyEquivalences_mapHomologicalComplex_map (zsmulAddProjEndo x m)
          (homotopyEquivalences_zsmul_add_proj x m hX))
  have hiso : IsIso (HomologicalComplex.homologyMap (FCh.map (zsmulAddProjEndo x m)) (n + 1)) :=
    (quasiIsoAt_iff_isIso_homologyMap _ (n + 1)).1 ((quasiIso_iff _).1 hqi (n + 1))
  -- Multiplication by `m` kills `M`, hence kills every tensor product `M ⊗ N`.
  have hM0 : m • 𝟙 M = 0 := by ext a; exact hmM a
  have hkill : m • 𝟙 (FCh.obj ((singularChains ℤ).obj (TopCat.of X))) = 0 := by
    ext q : 1
    let G := MonoidalCategory.tensorRight (((singularChains ℤ).obj (TopCat.of X)).X q)
    -- `(FCh.obj C).X q = M ⊗ C.X q = G.obj M` by definition of `mapHomologicalComplex` and
    -- `tensorLeft`/`tensorRight`.
    change m • 𝟙 (G.obj M) = 0
    rw [← G.map_id, ← G.map_zsmul, hM0, G.map_zero]
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (.down ℕ) (n + 1)
  have hP : Limits.IsZero (H.obj (FCh.obj ((singularChains ℤ).obj (TopCat.of PUnit)))) :=
    (isZero_singularHomologyFunctor_of_contractibleSpace (F.obj (ModuleCat.of ℤ ℤ))
      (TopCat.of PUnit) n.succ_ne_zero).of_iso
        (H.mapIso ((Functor.singularChainComplexFunctorObjCompMapIso F (ModuleCat.of ℤ ℤ)).app
          (TopCat.of PUnit)))
  have hscalar : H.map (FCh.map (m • 𝟙 ((singularChains ℤ).obj (TopCat.of X)))) = 0 := by
    rw [FCh.map_zsmul, FCh.map_id, hkill, H.map_zero]
  have hpt : H.map (FCh.map ((1 - m) • ((singularChains ℤ).map p ≫
      (singularChains ℤ).map s))) = 0 := by
    rw [FCh.map_zsmul, FCh.map_comp, H.map_zsmul, H.map_comp,
      hP.eq_of_tgt (H.map (FCh.map ((singularChains ℤ).map p))) 0, Limits.zero_comp, smul_zero]
  have hzero : HomologicalComplex.homologyMap (FCh.map (zsmulAddProjEndo x m)) (n + 1) = 0 := by
    rw [← HomologicalComplex.homologyFunctor_map, zsmulAddProjEndo, FCh.map_add, H.map_add,
      hscalar, hpt, zero_add]
  have hFzero : Limits.IsZero
      ((FCh.obj ((singularChains ℤ).obj (TopCat.of X))).homology (n + 1)) :=
    Limits.IsZero.of_epi_eq_zero _ hzero
  exact (hFzero.of_iso
    (H.mapIso ((Functor.singularChainComplexFunctorObjCompMapIso F (ModuleCat.of ℤ ℤ)).app
      (TopCat.of X))).symm).of_iso
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).mapIso
        (MonoidalCategory.rightUnitor M)).app (TopCat.of X)).symm

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Pi

/-!
# Coordinate morphisms, strata, and constant-rank comparison for bundle atlases

On each clopen joint rank stratum `StratumPair A D m n = {x : X // A.rank x = m ∧ D.rank x = n}`,
restricting `A.charts m` and `D.charts n` yields constant-rank cores (`FiniteRankAtlas.stratumCore`)
whose coordinate morphisms assemble via `FiniteRankAtlas.coordinateHomAddEquiv` into an additive
presentation of morphisms in `TauCeti.FiniteRankAtlas 𝕜 X` without completeness of `𝕜`. From this
and Cramer's-rule inversion we deduce fibrewise-bijectivity reflection of isomorphisms
(`FiniteRankAtlas.isIso_iff_bijective`), the full, faithful, additive constant-rank embedding
`FiniteRankAtlas.ofCoreFunctor` with essential image characterized by globally constant rank
(`FiniteRankAtlas.essImage_ofCoreFunctor_iff`), and `HasZeroObject (FiniteRankAtlas 𝕜 X)`.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits Set Topology VectorBundleCore

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

/-- Including a single fibre into the reconstructed total space of a variable-rank atlas is
inducing. -/
theorem isInducing_mk (A : FiniteRankAtlas 𝕜 X) (x : X) :
    IsInducing (fun v : A.Fiber x ↦ (⟨x, v⟩ : TotalSpace Unit A.Fiber)) := by
  rw [← A.totalSpaceHomeomorph.symm.isInducing.of_comp_iff]
  have hcomp :
      A.totalSpaceHomeomorph.symm ∘ (fun v : A.Fiber x ↦ (⟨x, v⟩ : TotalSpace Unit A.Fiber)) =
        Sigma.mk (A.rank x) ∘
          fun v : A.Fiber x ↦ (⟨⟨x, rfl⟩, v⟩ : (A.charts (A.rank x)).TotalSpace) :=
    funext fun v ↦ A.totalSpaceHomeomorph_symm_apply ⟨x, v⟩
  rw [hcomp]
  exact IsEmbedding.sigmaMk.isInducing.comp
    (FiberBundle.totalSpaceMk_isInducing (Fin (A.rank x) → 𝕜) (A.charts (A.rank x)).Fiber ⟨x, rfl⟩)

namespace Hom

variable {A D : FiniteRankAtlas 𝕜 X}

/-- Every fibre map of an atlas morphism is continuous, without assuming completeness of `𝕜`. -/
@[continuity, fun_prop]
theorem continuous_fiberMap (f : A ⟶ D) (x : X) : Continuous (f.fiberMap x) :=
  (D.isInducing_mk x).continuous_iff.2 <|
    f.continuous_totalSpaceMap.comp (A.isInducing_mk x).continuous

/-- The continuous linear map on the fibre at `x` induced by an atlas morphism. -/
def fiberCLM (f : A ⟶ D) (x : X) : A.Fiber x →L[𝕜] D.Fiber x :=
  ⟨f.fiberMap x, f.continuous_fiberMap x⟩

@[simp] theorem coe_fiberCLM (f : A ⟶ D) (x : X) :
    (f.fiberCLM x : A.Fiber x →ₗ[𝕜] D.Fiber x) = f.fiberMap x := (rfl)

@[simp] theorem fiberCLM_apply (f : A ⟶ D) (x : X) (v : A.Fiber x) :
    f.fiberCLM x v = f.fiberMap x v := (rfl)

end Hom

@[simp] theorem fiberCLM_id (A : FiniteRankAtlas 𝕜 X) (x : X) :
    Hom.fiberCLM (𝟙 A) x = ContinuousLinearMap.id 𝕜 (A.Fiber x) := (rfl)

@[simp] theorem fiberCLM_comp {A D C : FiniteRankAtlas 𝕜 X} (f : A ⟶ D) (g : D ⟶ C) (x : X) :
    Hom.fiberCLM (f ≫ g) x = (g.fiberCLM x).comp (f.fiberCLM x) := (rfl)

@[simp] theorem fiberCLM_zero {A D : FiniteRankAtlas 𝕜 X} (x : X) :
    Hom.fiberCLM (0 : A ⟶ D) x = 0 := (rfl)

@[simp] theorem fiberCLM_add {A D : FiniteRankAtlas 𝕜 X} (f g : A ⟶ D) (x : X) :
    Hom.fiberCLM (f + g) x = f.fiberCLM x + g.fiberCLM x := (rfl)

@[simp] theorem fiberCLM_neg {A D : FiniteRankAtlas 𝕜 X} (f : A ⟶ D) (x : X) :
    Hom.fiberCLM (-f) x = -f.fiberCLM x := (rfl)

/-! ### Clopen-stratum cores and coordinate morphisms -/

/-- The constant-rank point-indexed core of `A` on its `n`th clopen rank stratum. -/
@[expose, implicit_reducible]
def stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    FiniteRankBundleCore 𝕜 {x : X // A.rank x = n} :=
  ⟨n, A.charts n, A.indexAt_eq n⟩

@[simp] theorem rank_stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (A.stratumCore n).rank = n := (rfl)

@[simp] theorem core_stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (A.stratumCore n).core = A.charts n := (rfl)

/-- The clopen locus where `A` has rank `m` and `D` has rank `n`. -/
abbrev StratumPair (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) : Type u :=
  {x : X // A.rank x = m ∧ D.rank x = n}

/-- Inclusion of the `(m, n)` joint rank stratum into the `m`th rank stratum of `A`. -/
def stratumPairFst (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    C(StratumPair A D m n, {x : X // A.rank x = m}) :=
  ⟨fun x ↦ ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

@[simp] theorem stratumPairFst_apply (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ)
    (x : StratumPair A D m n) : stratumPairFst A D m n x = ⟨x.1, x.2.1⟩ := (rfl)

/-- Inclusion of the `(m, n)` joint rank stratum into the `n`th rank stratum of `D`. -/
def stratumPairSnd (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    C(StratumPair A D m n, {x : X // D.rank x = n}) :=
  ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩

@[simp] theorem stratumPairSnd_apply (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ)
    (x : StratumPair A D m n) : stratumPairSnd A D m n x = ⟨x.1, x.2.2⟩ := (rfl)

/-- A coordinate morphism on the `(m, n)` joint rank stratum. -/
abbrev StratumCoordinateHom (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :=
  (A.stratumCore m).pullback (stratumPairFst A D m n) ⟶
    (D.stratumCore n).pullback (stratumPairSnd A D m n)

private theorem continuous_stratum_totalSpaceMap {A D : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ D) (m n : ℕ) :
    Continuous fun p : ((A.stratumCore m).pullback (stratumPairFst A D m n)).core.TotalSpace ↦
      (⟨p.proj, ((ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n ↦ 𝕜)
          (finCongr p.proj.2.2)).toContinuousLinearMap.comp
        ((f.fiberCLM p.proj.1).comp (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin m ↦ 𝕜)
          (finCongr p.proj.2.1)).symm.toContinuousLinearMap)) p.2⟩ :
        ((D.stratumCore n).pullback (stratumPairSnd A D m n)).core.TotalSpace) := by
  let Z := ((A.stratumCore m).pullback (stratumPairFst A D m n)).core
  have hlift := (A.stratumCore m).continuous_pullbackLift (stratumPairFst A D m n)
  have hZin : Continuous fun p : Z.TotalSpace ↦
      (⟨p.proj.1, (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin m ↦ 𝕜)
        (finCongr p.proj.2.1)).symm p.2⟩ : TotalSpace Unit A.Fiber) :=
    (A.totalSpaceHomeomorph.continuous.comp
      (continuous_sigmaMk (σ := fun k ↦ (A.charts k).TotalSpace).comp hlift)).congr fun ⟨_, _⟩ ↦ by
      simp only [Function.comp_apply, FiniteRankBundleCore.pullbackLift_mk,
        totalSpaceHomeomorph_apply]; rfl
  have hD := (D.continuous_mk_iff_rankStrata (continuous_subtype_val.comp Z.continuous_proj)
    fun p ↦ f.fiberMap p.proj.1 ((ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin m ↦ 𝕜)
      (finCongr p.proj.2.1)).symm p.2)).1 (f.continuous_totalSpaceMap.comp hZin) n
  exact ((D.stratumCore n).continuous_core_pullback_iff (stratumPairSnd A D m n)).2
    ⟨Z.continuous_proj, (hD.comp (continuous_id.subtype_mk fun p : Z.TotalSpace ↦ p.proj.2.2)).congr
      fun p ↦ ((D.stratumCore n).pullbackLift_mk (stratumPairSnd A D m n) p.proj _).symm⟩

/-- Extract the compatible chart operators of an atlas morphism on the `(m, n)` stratum. -/
def toStratumCoordinateHom {A D : FiniteRankAtlas 𝕜 X} (f : A ⟶ D) (m n : ℕ) :
    StratumCoordinateHom A D m n :=
  CoordinateHom.ofContinuousTotalSpacePi _ _
    (fun x ↦ (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n ↦ 𝕜)
        (finCongr x.2.2)).toContinuousLinearMap.comp
      ((f.fiberCLM x.1).comp (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin m ↦ 𝕜)
        (finCongr x.2.1)).symm.toContinuousLinearMap))
    (continuous_stratum_totalSpaceMap f m n)

@[simp] theorem fiberMap_toStratumCoordinateHom {A D : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ D) (m n : ℕ) (x : StratumPair A D m n) :
    (toStratumCoordinateHom f m n).fiberMap x =
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n ↦ 𝕜)
        (finCongr x.2.2)).toContinuousLinearMap.comp
        ((f.fiberCLM x.1).comp (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin m ↦ 𝕜)
          (finCongr x.2.1)).symm.toContinuousLinearMap) :=
  CoordinateHom.fiberMap_ofContinuousTotalSpacePi _ _ _ _ x

private theorem continuous_ofStratumCoordinateHom {A D : FiniteRankAtlas 𝕜 X}
    (c : ∀ m n : ℕ, StratumCoordinateHom A D m n) :
    Continuous fun p : TotalSpace Unit A.Fiber ↦
      (⟨p.proj, (c (A.rank p.proj) (D.rank p.proj)).fiberMap ⟨p.proj, rfl, rfl⟩ p.2⟩ :
        TotalSpace Unit D.Fiber) := by
  refine (D.continuous_mk_iff_rankStrata A.continuous_proj _).2 fun n ↦ ?_
  refine continuous_of_cover_nhds (s := fun m : ℕ ↦
      {q : {p : TotalSpace Unit A.Fiber // D.rank p.proj = n} | A.rank q.1.proj = m})
    (fun q ↦ ⟨A.rank q.1.proj, ((A.rank.isLocallyConstant.isOpen_fiber _).preimage
      (A.continuous_proj.comp continuous_subtype_val)).mem_nhds rfl⟩) fun m ↦ ?_
  rw [continuousOn_iff_continuous_domRestrict]
  let U := {q : {p : TotalSpace Unit A.Fiber // D.rank p.proj = n} // A.rank q.1.proj = m}
  have hA := (A.continuous_mk_iff_rankStrata A.continuous_proj (fun p ↦ p.2)).1 continuous_id m
  have hZ : Continuous fun q : U ↦
      (⟨⟨q.1.1.proj, q.2, q.1.2⟩, fun i ↦ q.1.1.2 (Fin.cast q.2.symm i)⟩ :
        ((A.stratumCore m).pullback (stratumPairFst A D m n)).core.TotalSpace) :=
    ((A.stratumCore m).continuous_core_pullback_iff (stratumPairFst A D m n)).2
      ⟨(A.continuous_proj.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _,
        (hA.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk
          fun q : U ↦ q.2)).congr fun q ↦
            ((A.stratumCore m).pullbackLift_eq_mk (stratumPairFst A D m n)
              ⟨⟨q.1.1.proj, q.2, q.1.2⟩, _⟩ rfl rfl).symm⟩
  have hW := (D.stratumCore n).continuous_pullbackLift (stratumPairSnd A D m n)
  refine (hW.comp ((c m n).continuous_totalSpaceMap.comp hZ)).congr fun ⟨⟨⟨x, v⟩, hDn⟩, hAm⟩ ↦ ?_
  cases hAm; cases hDn
  simp only [Function.comp_apply, CoordinateHom.totalSpaceMap_def, Set.domRestrict_apply]
  exact (D.stratumCore (D.rank x)).pullbackLift_eq_mk _ _ rfl rfl

/-- Assemble coordinate morphisms on the `(m, n)` joint rank strata into an atlas morphism. -/
def ofStratumCoordinateHom {A D : FiniteRankAtlas 𝕜 X}
    (c : ∀ m n : ℕ, StratumCoordinateHom A D m n) : A ⟶ D :=
  ⟨fun x ↦ ((c (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩).toLinearMap,
    continuous_ofStratumCoordinateHom c⟩

@[simp] theorem fiberMap_ofStratumCoordinateHom {A D : FiniteRankAtlas 𝕜 X}
    (c : ∀ m n : ℕ, StratumCoordinateHom A D m n) (x : X) :
    (ofStratumCoordinateHom c).fiberMap x =
      ((c (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩).toLinearMap := (rfl)

/-- Morphisms of variable-rank bundle atlases correspond additively to families of compatible
finite-matrix coordinate morphisms across the clopen `(m, n)` joint rank strata. -/
def coordinateHomAddEquiv (A D : FiniteRankAtlas 𝕜 X) :
    (A ⟶ D) ≃+ ∀ m n : ℕ, StratumCoordinateHom A D m n where
  toFun := toStratumCoordinateHom
  invFun := ofStratumCoordinateHom
  left_inv f := hom_ext fun x ↦ LinearMap.ext fun v ↦ funext fun i ↦ by
    simp only [fiberMap_ofStratumCoordinateHom, ContinuousLinearMap.coe_coe,
      fiberMap_toStratumCoordinateHom, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, finCongr_refl, Hom.fiberCLM_apply]; rfl
  right_inv c := funext fun m ↦ funext fun n ↦ FiniteRankBundleCore.hom_ext
    fun ⟨x, hx₁, hx₂⟩ ↦ ContinuousLinearMap.ext fun v ↦ by
      subst hx₁; subst hx₂; ext i
      simp only [fiberMap_toStratumCoordinateHom, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, finCongr_refl, Hom.fiberCLM_apply,
        fiberMap_ofStratumCoordinateHom, ContinuousLinearMap.coe_coe]; rfl
  map_add' f g := funext fun m ↦ funext fun n ↦
    FiniteRankBundleCore.hom_ext fun x ↦ ContinuousLinearMap.ext fun v ↦ by simp

@[simp] theorem coordinateHomAddEquiv_apply {A D : FiniteRankAtlas 𝕜 X} (f : A ⟶ D) (m n : ℕ) :
    coordinateHomAddEquiv A D f m n = toStratumCoordinateHom f m n := (rfl)

@[simp] theorem coordinateHomAddEquiv_symm_apply {A D : FiniteRankAtlas 𝕜 X}
    (c : ∀ m n : ℕ, StratumCoordinateHom A D m n) :
    (coordinateHomAddEquiv A D).symm c = ofStratumCoordinateHom c := (rfl)

/-! ### Invertibility of atlas morphisms -/

private theorem continuous_inv_of_bijective {A D : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ D) (hf : ∀ x, Function.Bijective (f.fiberMap x)) :
    Continuous fun p : TotalSpace Unit D.Fiber ↦
      (⟨p.proj, (LinearEquiv.ofBijective (f.fiberMap p.proj) (hf p.proj)).symm p.2⟩ :
        TotalSpace Unit A.Fiber) := by
  let swap (m n : ℕ) : C(StratumPair D A m n, StratumPair A D n m) :=
    ⟨fun x ↦ ⟨x.1, x.2.2, x.2.1⟩, continuous_subtype_val.subtype_mk fun x ↦ ⟨x.2.2, x.2.1⟩⟩
  let fwd (m n : ℕ) : (A.stratumCore n).pullback (stratumPairSnd D A m n) ⟶
      (D.stratumCore m).pullback (stratumPairFst D A m n) :=
    FiniteRankBundleCore.pullbackMap (toStratumCoordinateHom f n m) (swap m n)
  have hfwd (m n : ℕ) (y : StratumPair D A m n) : (fwd m n).fiberMap y =
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin m ↦ 𝕜)
        (finCongr y.2.1)).toContinuousLinearMap.comp
        ((f.fiberCLM y.1).comp (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n ↦ 𝕜)
          (finCongr y.2.2)).symm.toContinuousLinearMap) :=
    (FiniteRankBundleCore.fiberMap_pullbackMap _ (swap m n) y).trans
      (fiberMap_toStratumCoordinateHom f n m ⟨y.1, y.2.2, y.2.1⟩)
  have hbij (m n : ℕ) (y : StratumPair D A m n) : Function.Bijective ((fwd m n).fiberMap y) := by
    rw [hfwd]
    exact (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr y.2.1)).bijective.comp
      ((hf y.1).comp
        (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr y.2.2)).symm.bijective)
  refine (ofStratumCoordinateHom fun m n ↦
      CoordinateHom.invOfBijectivePi _ _ (fwd m n) (hbij m n)).continuous_totalSpaceMap.congr
    fun p ↦ congrArg (TotalSpace.mk p.proj) ?_
  apply (LinearEquiv.ofBijective (f.fiberMap p.proj) (hf p.proj)).injective
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply, fiberMap_ofStratumCoordinateHom,
    ContinuousLinearMap.coe_coe, CoordinateHom.fiberMap_invOfBijectivePi]
  have hdiag : (fwd (D.rank p.proj) (A.rank p.proj)).fiberMap ⟨p.proj, rfl, rfl⟩ =
      f.fiberCLM p.proj := by
    rw [hfwd]; ext v i
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, finCongr_refl,
      Hom.fiberCLM_apply]; rfl
  rw [hdiag]
  exact ((f.fiberCLM p.proj).isInvertible_of_bijective_pi (hf p.proj)).self_apply_inverse p.2

/-- A morphism in `FiniteRankAtlas 𝕜 X` is an isomorphism iff it is bijective on every fibre. -/
theorem isIso_iff_bijective {A D : FiniteRankAtlas 𝕜 X} (f : A ⟶ D) :
    IsIso f ↔ ∀ x, Function.Bijective (f.fiberMap x) := by
  refine ⟨fun _ x ↦ ((fiberFunctor x).mapIso (asIso f)).toLinearEquiv.bijective, fun hf ↦ ?_⟩
  let e := isoMk (fun x ↦ LinearEquiv.ofBijective (f.fiberMap x) (hf x))
    f.continuous_totalSpaceMap (continuous_inv_of_bijective f hf)
  have he : e.hom = f := hom_ext fun x ↦
    (fiberMap_isoMk_hom _ _ _ x).trans (LinearMap.ext fun _ ↦ rfl)
  exact he ▸ e.isIso_hom

/-! ### Full and faithful embedding of constant-rank cores -/

/-- Embed a constant-rank point-indexed core as a variable-rank atlas of constant rank. -/
@[expose]
def ofCore (C : FiniteRankBundleCore 𝕜 X) : FiniteRankAtlas 𝕜 X where
  rank := LocallyConstant.const X C.rank
  charts m := if h : C.rank = m then h ▸ (C.pullback ⟨Subtype.val, continuous_subtype_val⟩).core
    else (FiniteRankBundleCore.trivial 𝕜 {x : X // (LocallyConstant.const X C.rank) x = m} m).core
  indexAt_eq m := fun ⟨y, hy⟩ ↦ by
    have hy' : C.rank = m := hy; subst hy'; simp only [↓reduceDIte]
    exact (C.pullback ⟨Subtype.val, continuous_subtype_val⟩).indexAt_eq ⟨y, hy⟩

@[simp] theorem rank_ofCore (C : FiniteRankBundleCore 𝕜 X) :
    (ofCore C).rank = LocallyConstant.const X C.rank := (rfl)

@[simp] theorem charts_ofCore_self (C : FiniteRankBundleCore 𝕜 X) :
    (ofCore C).charts C.rank = (C.pullback (⟨Subtype.val, continuous_subtype_val⟩ :
      C({x : X // (ofCore C).rank x = C.rank}, X))).core := by
  simp only [ofCore, ↓reduceDIte]; rfl

/-- The reconstructed total space of `ofCore C` is homeomorphic over `X` to `C.core.TotalSpace`. -/
def ofCoreHomeomorph (C : FiniteRankBundleCore 𝕜 X) :
    TotalSpace Unit (ofCore C).Fiber ≃ₜ C.core.TotalSpace where
  toFun p := ⟨p.proj, p.2⟩
  invFun p := ⟨p.proj, p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  continuous_toFun := by
    let inc : C({x : X // (ofCore C).rank x = C.rank}, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hsigma : Continuous fun q : (ofCore C).GluedTotalSpace ↦
        (⟨q.2.proj.1, fun i ↦ q.2.2 (Fin.cast q.2.proj.2 i)⟩ : C.core.TotalSpace) :=
      continuous_sigma fun m ↦ by
        by_cases hm : C.rank = m
        · subst hm; rw [charts_ofCore_self]
          exact (C.continuous_pullbackLift inc).congr fun ⟨x, v⟩ ↦ C.pullbackLift_mk inc x v
        · have : IsEmpty (((ofCore C).charts m).TotalSpace) := ⟨fun q ↦ hm q.proj.2⟩
          exact continuous_iff_continuousAt.2 isEmptyElim
    exact (hsigma.comp (ofCore C).totalSpaceHomeomorph.symm.continuous).congr fun p ↦ by
      rw [Function.comp_apply, (ofCore C).totalSpaceHomeomorph_symm_apply]; rfl
  continuous_invFun := by
    let inc : C({x : X // (ofCore C).rank x = C.rank}, X) := ⟨Subtype.val, continuous_subtype_val⟩
    refine ((ofCore C).continuous_mk_iff_rankStrata C.core.continuous_proj
      (fun p : C.core.TotalSpace ↦ (p.2 : (ofCore C).Fiber p.proj))).2 fun m ↦ ?_
    by_cases hm : C.rank = m
    · subst hm; rw [charts_ofCore_self]
      exact (C.continuous_core_pullback_iff inc).2
        ⟨(C.core.continuous_proj.comp continuous_subtype_val).subtype_mk _,
          continuous_subtype_val.congr fun ⟨⟨x, v⟩, hx⟩ ↦ (C.pullbackLift_mk inc ⟨x, hx⟩ v).symm⟩
    · have : IsEmpty {p : C.core.TotalSpace // (ofCore C).rank p.proj = m} := ⟨fun q ↦ hm q.2⟩
      exact continuous_iff_continuousAt.2 isEmptyElim

@[simp] theorem ofCoreHomeomorph_apply (C : FiniteRankBundleCore 𝕜 X)
    (p : TotalSpace Unit (ofCore C).Fiber) : ofCoreHomeomorph C p = ⟨p.proj, p.2⟩ := (rfl)

@[simp] theorem ofCoreHomeomorph_symm_apply (C : FiniteRankBundleCore 𝕜 X)
    (p : C.core.TotalSpace) : (ofCoreHomeomorph C).symm p = ⟨p.proj, p.2⟩ := (rfl)

variable (𝕜 X) in
/-- Embed constant-rank point-indexed bundle cores into variable-rank bundle atlases. -/
@[expose]
def ofCoreFunctor : FiniteRankBundleCore 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj := ofCore
  map {C₁ C₂} f :=
    { fiberMap x := (f.fiberMap x).toLinearMap
      continuous_totalSpaceMap := ((ofCoreHomeomorph C₂).symm.continuous.comp
        (f.continuous_totalSpaceMap.comp (ofCoreHomeomorph C₁).continuous)).congr fun _ ↦ by
        simp only [Function.comp_apply, ofCoreHomeomorph_apply, CoordinateHom.totalSpaceMap_def,
          ofCoreHomeomorph_symm_apply]; rfl }
  map_id C := hom_ext (A := ofCore C) (D := ofCore C) fun x ↦ LinearMap.ext fun v ↦
    congrFun (congrArg DFunLike.coe (CoordinateHom.fiberMap_id C.core x)) v
  map_comp {C₁ _ C₃} f g := hom_ext (A := ofCore C₁) (D := ofCore C₃) fun x ↦ LinearMap.ext fun v ↦
    congrFun (congrArg DFunLike.coe (CoordinateHom.fiberMap_comp g f x)) v

@[simp] theorem ofCoreFunctor_obj (C : FiniteRankBundleCore 𝕜 X) :
    (ofCoreFunctor 𝕜 X).obj C = ofCore C := (rfl)

@[simp] theorem fiberMap_ofCoreFunctor_map {C₁ C₂ : FiniteRankBundleCore 𝕜 X}
    (f : C₁ ⟶ C₂) (x : X) :
    ((ofCoreFunctor 𝕜 X).map f).fiberMap x = (f.fiberMap x).toLinearMap := (rfl)

instance : (ofCoreFunctor 𝕜 X).Additive where
  map_add {C₁ C₂} f g := hom_ext (A := ofCore C₁) (D := ofCore C₂) fun x ↦ LinearMap.ext fun v ↦
    congrFun (congrArg DFunLike.coe (CoordinateHom.fiberMap_add f g x)) v

instance : (ofCoreFunctor 𝕜 X).Faithful where
  map_injective {C₁ C₂} _ _ h := FiniteRankBundleCore.hom_ext fun x ↦
    ContinuousLinearMap.ext fun v ↦ congrArg (fun k : ofCore C₁ ⟶ ofCore C₂ ↦ k.fiberMap x v) h

instance : (ofCoreFunctor 𝕜 X).Full where
  map_surjective {C₁ C₂} g := by
    let g' : ofCore C₁ ⟶ ofCore C₂ := g
    refine ⟨CoordinateHom.ofContinuousTotalSpacePi C₁.core C₂.core (fun x ↦ g'.fiberCLM x)
      (((ofCoreHomeomorph C₂).continuous.comp
        (g'.continuous_totalSpaceMap.comp (ofCoreHomeomorph C₁).symm.continuous)).congr
        fun _ ↦ by simp only [Function.comp_apply, ofCoreHomeomorph_apply]; rfl),
      hom_ext (A := ofCore C₁) (D := ofCore C₂) fun x ↦ LinearMap.ext fun v ↦
        congrFun (congrArg DFunLike.coe
          (CoordinateHom.fiberMap_ofContinuousTotalSpacePi C₁.core C₂.core _ _ x)) v⟩

/-- An atlas of constant rank `n` is canonically isomorphic to an image of `ofCoreFunctor`. -/
def ofCoreStratumIso (A : FiniteRankAtlas 𝕜 X) (n : ℕ) (hn : ∀ x, A.rank x = n) :
    (ofCoreFunctor 𝕜 X).obj ((A.stratumCore n).pullback ⟨fun x ↦ ⟨x, hn x⟩,
      continuous_id.subtype_mk hn⟩) ≅ A := by
  let s : C(X, {x : X // A.rank x = n}) := ⟨fun x ↦ ⟨x, hn x⟩, continuous_id.subtype_mk hn⟩
  let C := (A.stratumCore n).pullback s
  refine isoMk (fun x ↦ (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜)
      (finCongr (hn x))).symm.toLinearEquiv) ?_ ?_
  · refine (A.continuous_mk_iff_rankStrata (ofCore C).continuous_proj _).2 fun m ↦ ?_
    by_cases hmn : m = n
    · subst hmn
      have hZ := (A.stratumCore m).continuous_pullbackLift s
      refine (hZ.comp ((ofCoreHomeomorph C).continuous.comp continuous_subtype_val)).congr
        fun ⟨⟨x, v⟩, hxm⟩ ↦ ?_
      cases Subsingleton.elim (hn x) hxm
      exact (A.stratumCore m).pullbackLift_eq_mk s _ rfl rfl
    · have : IsEmpty {p : TotalSpace Unit (ofCore C).Fiber // A.rank p.proj = m} :=
        ⟨fun q ↦ hmn (q.2.symm.trans (hn q.1.proj))⟩
      exact continuous_iff_continuousAt.2 isEmptyElim
  · have hA := (A.continuous_mk_iff_rankStrata A.continuous_proj (fun p ↦ p.2)).1 continuous_id n
    have hC : Continuous fun p : TotalSpace Unit A.Fiber ↦
        (⟨p.proj, fun i ↦ p.2 (Fin.cast (hn p.proj).symm i)⟩ : C.core.TotalSpace) :=
      ((A.stratumCore n).continuous_core_pullback_iff s).2
        ⟨A.continuous_proj, (hA.comp (continuous_id.subtype_mk fun p ↦ hn p.proj)).congr
          fun p ↦ ((A.stratumCore n).pullbackLift_mk s p.proj _).symm⟩
    exact ((ofCoreHomeomorph C).symm.continuous.comp hC).congr fun _ ↦ by
      simp only [Function.comp_apply, ofCoreHomeomorph_symm_apply]; rfl

/-- `A` lies in `(ofCoreFunctor 𝕜 X).essImage` iff `A.rank` is globally constant. -/
theorem essImage_ofCoreFunctor_iff (A : FiniteRankAtlas 𝕜 X) :
    (ofCoreFunctor 𝕜 X).essImage A ↔ ∃ n : ℕ, ∀ x : X, A.rank x = n :=
  ⟨fun ⟨C, ⟨e⟩⟩ ↦ ⟨C.rank, fun x ↦ DFunLike.congr_fun e.finiteRankAtlas_rank_eq.symm x⟩,
   fun ⟨n, hn⟩ ↦ ⟨_, ⟨ofCoreStratumIso A n hn⟩⟩⟩

/-- Every atlas of globally zero rank is a zero object in `FiniteRankAtlas 𝕜 X`. -/
theorem isZero_of_rank_eq_zero (A : FiniteRankAtlas 𝕜 X) (h : ∀ x, A.rank x = 0) : IsZero A := by
  have hsub (x : X) : Subsingleton (A.Fiber x) := by dsimp only [Fiber]; rw [h x]; infer_instance
  refine ⟨fun D ↦ ⟨⟨⟨0⟩, fun f ↦ hom_ext fun x ↦ LinearMap.ext fun v ↦ ?_⟩⟩,
    fun D ↦ ⟨⟨⟨0⟩, fun f ↦ hom_ext fun x ↦ LinearMap.ext fun v ↦ Subsingleton.elim _ _⟩⟩⟩
  rw [Subsingleton.elim v 0, map_zero, map_zero]

instance : HasZeroObject (FiniteRankAtlas 𝕜 X) :=
  ⟨⟨ofCore (FiniteRankBundleCore.trivial 𝕜 X 0), isZero_of_rank_eq_zero _ fun _ ↦ rfl⟩⟩

end TauCeti.FiniteRankAtlas

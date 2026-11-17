/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import Mathlib.CategoryTheory.EssentialImage
public import TauCeti.Topology.Algebra.Module.Equiv.Pi
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Pi

/-!
# Coordinate morphisms, strata, and constant-rank comparison for bundle atlases

Each rank stratum `{x : X // A.rank x = m}` of `A : FiniteRankAtlas 𝕜 X` carries a constant-rank
point-indexed core `A.stratumCore m`. Pulling `A.stratumCore m` and `D.stratumCore n` back to the
clopen joint rank strata `StratumPair A D m n = {x : X // A.rank x = m ∧ D.rank x = n}` and
reading atlas morphisms via `FiniteRankAtlas.Hom.fiberCLM` and
`FiniteRankAtlas.continuous_mk_iff_rankStrata` yields an additive equivalence
`FiniteRankAtlas.coordinateHomAddEquiv` between `A ⟶ D` and families of compatible
`VectorBundleCore.CoordinateHom` morphisms across `(m, n) : ℕ × ℕ`, without assuming
`CompleteSpace 𝕜`.

Pointwise bijectivity on fibres reflects isomorphisms in `FiniteRankAtlas 𝕜 X`
(`FiniteRankAtlas.isIso_iff_bijective`, generalizing `FiniteRankBundleCore.isIso_iff_bijective`;
see Hatcher, *Vector Bundles and K-Theory*, §1.1). Separately, `FiniteRankAtlas.ofCoreFunctor`
gives a full, faithful, additive embedding of constant-rank `FiniteRankBundleCore 𝕜 X` into
`FiniteRankAtlas 𝕜 X` (acting on morphisms via `FiniteRankAtlas.ofCoreMap`) whose essential image
consists of the atlases of globally constant rank (`FiniteRankAtlas.essImage_ofCoreFunctor_iff`),
and `FiniteRankAtlas 𝕜 X` admits a zero object (`FiniteRankAtlas.isZero_of_rank_eq_zero`,
`HasZeroObject (FiniteRankAtlas 𝕜 X)`).
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits Set Topology VectorBundleCore

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

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
        totalSpaceHomeomorph_apply]
      congr 1
  have hD := (D.continuous_mk_iff_rankStrata (continuous_subtype_val.comp Z.continuous_proj)
    fun p ↦ f.fiberMap p.proj.1 ((ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin m ↦ 𝕜)
      (finCongr p.proj.2.1)).symm p.2)).1 (f.continuous_totalSpaceMap.comp hZin) n
  refine ((D.stratumCore n).continuous_core_pullback_iff (stratumPairSnd A D m n)).2
    ⟨Z.continuous_proj, (hD.comp (continuous_id.subtype_mk fun p : Z.TotalSpace ↦ p.proj.2.2)).congr
      fun p ↦ (congrArg (TotalSpace.mk (stratumPairSnd A D m n p.proj)) (funext fun i ↦
        (congrFun (f.fiberCLM_apply p.proj.1
          ((ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin m ↦ 𝕜)
            (finCongr p.proj.2.1)).symm p.2)) (Fin.cast p.proj.2.2.symm i)).symm)).trans
        ((D.stratumCore n).pullbackLift_mk (stratumPairSnd A D m n) p.proj _).symm⟩

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
  left_inv f := hom_ext fun x ↦ LinearMap.ext fun v ↦ funext fun i ↦ by simp
  right_inv c := funext fun m ↦ funext fun n ↦ FiniteRankBundleCore.hom_ext
    fun ⟨x, hx₁, hx₂⟩ ↦ ContinuousLinearMap.ext fun v ↦ by
      subst hx₁; subst hx₂
      ext i
      simp only [fiberMap_toStratumCoordinateHom, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, finCongr_refl, ContinuousLinearEquiv.piCongrLeft_refl,
        ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply]
      exact congrFun ((Hom.fiberCLM_apply (ofStratumCoordinateHom c) x v).trans
        (congrFun (congrArg DFunLike.coe (fiberMap_ofStratumCoordinateHom c x)) v)) i
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
  have hf' (x : X) : Function.Bijective (f.fiberCLM x) :=
    (funext (f.fiberCLM_apply x)).symm ▸ hf x
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
      ((hf' y.1).comp
        (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr y.2.2)).symm.bijective)
  refine (ofStratumCoordinateHom fun m n ↦
      CoordinateHom.invOfBijectivePi _ _ (fwd m n) (hbij m n)).continuous_totalSpaceMap.congr
    fun p ↦ congrArg (TotalSpace.mk p.proj) ?_
  apply (LinearEquiv.ofBijective (f.fiberMap p.proj) (hf p.proj)).injective
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply, fiberMap_ofStratumCoordinateHom,
    ContinuousLinearMap.coe_coe, CoordinateHom.fiberMap_invOfBijectivePi]
  have hdiag : (fwd (D.rank p.proj) (A.rank p.proj)).fiberMap ⟨p.proj, rfl, rfl⟩ =
      f.fiberCLM p.proj := by
    rw [hfwd]; ext v i; simp
  rw [hdiag]
  exact (f.fiberCLM_apply p.proj _).symm.trans
    (((f.fiberCLM p.proj).isInvertible_of_bijective_pi (hf' p.proj)).self_apply_inverse p.2)

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
      dsimp only [Function.comp_apply]
      rw [(ofCore C).totalSpaceHomeomorph_symm_apply]
      simp only [Fin.cast_refl]
      rfl
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

/-- Transport a morphism of constant-rank point-indexed cores to a morphism of variable-rank
bundle atlases via `ofCore`. -/
def ofCoreMap {C₁ C₂ : FiniteRankBundleCore 𝕜 X} (f : C₁ ⟶ C₂) : ofCore C₁ ⟶ ofCore C₂ where
  fiberMap x := (f.fiberMap x).toLinearMap
  continuous_totalSpaceMap := ((ofCoreHomeomorph C₂).symm.continuous.comp
    (f.continuous_totalSpaceMap.comp (ofCoreHomeomorph C₁).continuous)).congr fun p ↦ by
      dsimp only [Function.comp_apply]
      rw [ofCoreHomeomorph_apply, CoordinateHom.totalSpaceMap_def, ofCoreHomeomorph_symm_apply]
      exact congrArg (TotalSpace.mk p.proj)
        (congrFun (ContinuousLinearMap.coe_coe (f.fiberMap p.proj)).symm p.2)

@[simp] theorem fiberMap_ofCoreMap {C₁ C₂ : FiniteRankBundleCore 𝕜 X} (f : C₁ ⟶ C₂) (x : X) :
    (ofCoreMap f).fiberMap x = (f.fiberMap x).toLinearMap := (rfl)

@[simp] theorem ofCoreMap_id (C : FiniteRankBundleCore 𝕜 X) :
    ofCoreMap (𝟙 C) = 𝟙 (ofCore C) :=
  hom_ext fun x ↦
    congrArg ContinuousLinearMap.toLinearMap (FiniteRankBundleCore.fiberMap_id C x)

@[simp] theorem ofCoreMap_comp {C₁ C₂ C₃ : FiniteRankBundleCore 𝕜 X}
    (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) :
    ofCoreMap (f ≫ g) = ofCoreMap f ≫ ofCoreMap g :=
  hom_ext fun x ↦
    congrArg ContinuousLinearMap.toLinearMap (FiniteRankBundleCore.fiberMap_comp f g x)

@[simp] theorem ofCoreMap_add {C₁ C₂ : FiniteRankBundleCore 𝕜 X} (f g : C₁ ⟶ C₂) :
    ofCoreMap (f + g) = ofCoreMap f + ofCoreMap g :=
  hom_ext fun x ↦
    congrArg ContinuousLinearMap.toLinearMap (FiniteRankBundleCore.fiberMap_add f g x)

variable (𝕜 X) in
/-- Embed constant-rank point-indexed bundle cores into variable-rank bundle atlases. -/
def ofCoreFunctor : FiniteRankBundleCore 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj := ofCore
  map := ofCoreMap
  map_id := ofCoreMap_id
  map_comp := ofCoreMap_comp

@[simp] theorem ofCoreFunctor_obj (C : FiniteRankBundleCore 𝕜 X) :
    (ofCoreFunctor 𝕜 X).obj C = ofCore C := (rfl)

@[simp] theorem ofCoreFunctor_map {C₁ C₂ : FiniteRankBundleCore 𝕜 X} (f : C₁ ⟶ C₂) :
    (ofCoreFunctor 𝕜 X).map f =
      eqToHom (ofCoreFunctor_obj C₁) ≫ ofCoreMap f ≫ eqToHom (ofCoreFunctor_obj C₂).symm :=
  (rfl)

/-- `ofCoreFunctor` preserves addition of coordinate morphisms. -/
instance : (ofCoreFunctor 𝕜 X).Additive where
  map_add {C₁ C₂ f g} := by
    simp only [ofCoreFunctor_map, ofCoreMap_add, Preadditive.comp_add, Preadditive.add_comp]

/-- `ofCoreFunctor` is faithful since morphisms are determined by their fibre maps. -/
instance : (ofCoreFunctor 𝕜 X).Faithful where
  map_injective {C₁ C₂} f₁ f₂ h := by
    rw [ofCoreFunctor_map, ofCoreFunctor_map] at h
    have h' : ofCoreMap f₁ = ofCoreMap f₂ :=
      (cancel_mono (eqToHom (ofCoreFunctor_obj C₂).symm)).1 <|
        (cancel_epi (eqToHom (ofCoreFunctor_obj C₁))).1 h
    exact FiniteRankBundleCore.hom_ext fun x ↦ by
      have hx := congrArg (fun k : ofCore C₁ ⟶ ofCore C₂ ↦ k.fiberMap x) h'
      rw [fiberMap_ofCoreMap, fiberMap_ofCoreMap] at hx
      exact ContinuousLinearMap.coe_inj.mp hx

/-- `ofCoreFunctor` is full by descending continuous linear bundle maps to coordinate morphisms. -/
instance : (ofCoreFunctor 𝕜 X).Full where
  map_surjective {C₁ C₂} g := by
    let g' : ofCore C₁ ⟶ ofCore C₂ :=
      eqToHom (ofCoreFunctor_obj C₁).symm ≫ g ≫ eqToHom (ofCoreFunctor_obj C₂)
    let f : C₁ ⟶ C₂ :=
      CoordinateHom.ofContinuousTotalSpacePi C₁.core C₂.core (fun x ↦ g'.fiberCLM x)
        (((ofCoreHomeomorph C₂).continuous.comp
          (g'.continuous_totalSpaceMap.comp (ofCoreHomeomorph C₁).symm.continuous)).congr
          fun p ↦ by
            dsimp only [Function.comp_apply]
            rw [ofCoreHomeomorph_symm_apply, ofCoreHomeomorph_apply]
            exact congrArg (TotalSpace.mk p.proj) (g'.fiberCLM_apply p.proj p.2).symm)
    refine ⟨f, ?_⟩
    have hg : ofCoreMap f = g' := hom_ext fun x ↦
      (fiberMap_ofCoreMap f x).trans <| (congrArg ContinuousLinearMap.toLinearMap
        (CoordinateHom.fiberMap_ofContinuousTotalSpacePi C₁.core C₂.core
          (fun x ↦ g'.fiberCLM x) _ x)).trans (g'.coe_fiberCLM x)
    rw [ofCoreFunctor_map, hg]
    simp [g']

/-- An atlas of constant rank `n` is canonically isomorphic to `ofCore` of its pulled-back `n`th
stratum core. -/
def ofCoreStratumIso (A : FiniteRankAtlas 𝕜 X) (n : ℕ) (hn : ∀ x, A.rank x = n) :
    ofCore ((A.stratumCore n).pullback ⟨fun x ↦ ⟨x, hn x⟩,
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
      simp only [Function.comp_apply, ofCoreHomeomorph_symm_apply]
      congr 1

@[simp] theorem fiberMap_ofCoreStratumIso_hom (A : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (hn : ∀ x, A.rank x = n) (x : X) :
    (ofCoreStratumIso A n hn).hom.fiberMap x =
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr (hn x))).symm.toLinearMap := by
  unfold ofCoreStratumIso
  exact fiberMap_isoMk_hom _ _ _ x

@[simp] theorem fiberMap_ofCoreStratumIso_inv (A : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (hn : ∀ x, A.rank x = n) (x : X) :
    (ofCoreStratumIso A n hn).inv.fiberMap x =
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr (hn x))).toLinearMap := by
  unfold ofCoreStratumIso
  exact fiberMap_isoMk_inv _ _ _ x

/-- `A` lies in `(ofCoreFunctor 𝕜 X).essImage` iff `A.rank` is globally constant. -/
theorem essImage_ofCoreFunctor_iff (A : FiniteRankAtlas 𝕜 X) :
    (ofCoreFunctor 𝕜 X).essImage A ↔ ∃ n : ℕ, ∀ x : X, A.rank x = n :=
  ⟨fun ⟨C, ⟨e⟩⟩ ↦ ⟨C.rank, fun x ↦ DFunLike.congr_fun
      (eqToIso (ofCoreFunctor_obj C).symm ≪≫ e).finiteRankAtlas_rank_eq.symm x⟩,
   fun ⟨n, hn⟩ ↦ ⟨_, ⟨eqToIso (ofCoreFunctor_obj _) ≪≫ ofCoreStratumIso A n hn⟩⟩⟩

/-- Every atlas of globally zero rank is a zero object in `FiniteRankAtlas 𝕜 X`. -/
theorem isZero_of_rank_eq_zero (A : FiniteRankAtlas 𝕜 X) (h : ∀ x, A.rank x = 0) : IsZero A := by
  have (x : X) : Subsingleton (A.Fiber x) := by dsimp only [Fiber]; rw [h x]; infer_instance
  exact (Limits.IsZero.iff_id_eq_zero _).2
    (hom_ext fun _ ↦ LinearMap.ext fun _ ↦ Subsingleton.elim _ _)

/-- `FiniteRankAtlas 𝕜 X` has a zero object, namely the rank-zero trivial atlas. -/
instance : HasZeroObject (FiniteRankAtlas 𝕜 X) :=
  ⟨⟨(ofCoreFunctor 𝕜 X).obj (FiniteRankBundleCore.trivial 𝕜 X 0),
    (ofCoreFunctor 𝕜 X).map_isZero FiniteRankBundleCore.isZero_trivial_zero⟩⟩

end TauCeti.FiniteRankAtlas

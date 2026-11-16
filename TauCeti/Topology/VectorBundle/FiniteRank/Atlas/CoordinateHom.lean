/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Stratum
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Instances.Matrix

/-!
# Coordinate morphisms and fixed-rank comparison for bundle atlases

Between variable-rank atlases `A` and `D` over `X` (`TauCeti.FiniteRankAtlas`), restricting charts
to the clopen joint rank strata `{x : X // A.rank x = m ∧ D.rank x = n}` yields cores
`A.jointSourceCore D m n` and `A.jointTargetCore D m n`. Compatible chart operators glue via
`ofCoordinateHoms` and are extracted via `toCoordinateHom`, identifying `A ⟶ D` additively without
completeness assumptions on `𝕜` (`coordinateHomEquiv`) and characterizing isomorphisms by fibrewise
bijectivity (`isIso_iff_bijective`). We also construct the fully faithful additive constant-rank
embedding `ofCore`, which is an equivalence over any preconnected base.
-/

public section

open Bundle CategoryTheory Matrix Set Topology VectorBundleCore

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

private theorem continuousOn_clm_pi {B G : Type*} [TopologicalSpace B] [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {m : ℕ} {s : Set B} {ψ : B → (Fin m → 𝕜) →L[𝕜] G}
    (hψ : ∀ v : Fin m → 𝕜, ContinuousOn (fun x => ψ x v) s) : ContinuousOn ψ s := by
  have hsum : ψ = fun x => ∑ k : Fin m, ContinuousLinearMap.smulRightL 𝕜 (Fin m → 𝕜) G
      (ContinuousLinearMap.proj k) (ψ x fun l => if k = l then 1 else 0) := by
    ext x v; simpa [ContinuousLinearMap.smulRightL_apply_apply] using
      (ψ x).toLinearMap.pi_apply_eq_sum_univ v
  exact hsum ▸ continuousOn_finsetSum Finset.univ fun k _ => (ContinuousLinearMap.smulRightL 𝕜
    (Fin m → 𝕜) G (ContinuousLinearMap.proj k)).continuous.comp_continuousOn (hψ _)

private def coordinateHomOfTotalSpace {B : Type*} [TopologicalSpace B]
    {C₁ C₂ : FiniteRankBundleCore 𝕜 B} (f : B → (Fin C₁.rank → 𝕜) →ₗ[𝕜] (Fin C₂.rank → 𝕜))
    (hf : Continuous fun p : C₁.core.TotalSpace => (⟨p.proj, f p.proj p.2⟩ : C₂.core.TotalSpace)) :
    C₁ ⟶ C₂ :=
  let g (x : B) : (Fin C₁.rank → 𝕜) →L[𝕜] (Fin C₂.rank → 𝕜) := ⟨f x, (f x).continuous_on_pi⟩
  CoordinateHom.ofContinuous g <| continuous_hom_bundle_iff_forall_continuousOn.2 fun i j =>
    continuousOn_clm_pi fun v => by
      have hsymm : ContinuousOn (fun x => (⟨x, (C₁.core.localTriv i).symm x v⟩ :
          C₁.core.TotalSpace)) (C₁.core.baseSet i) :=
        (C₁.core.localTriv i).continuousOn_symm.comp
          (continuous_id.prodMk continuous_const).continuousOn fun _ hx => ⟨hx, mem_univ v⟩
      refine (continuous_snd.comp_continuousOn <| (C₂.core.localTriv j).continuousOn.comp
        ((hf.comp_continuousOn hsymm).mono inter_subset_left)
          fun _ hx => (C₂.core.localTriv j).mem_source.2 hx.2).congr fun x hx => ?_
      exact (congrArg (· v) (inChartCoordinates_eq_localTriv_comp hx.1 hx.2 (g x))).trans <|
        ((C₂.core.localTriv j).continuousLinearMapAt_apply_of_mem 𝕜 hx.2 _).trans <|
          congrArg (fun w => (C₂.core.localTriv j ⟨x, f x w⟩).2)
            ((C₁.core.localTriv i).symmL_apply hx.1 v)

private theorem fiberMap_coordinateHomOfTotalSpace {B : Type*} [TopologicalSpace B]
    {C₁ C₂ : FiniteRankBundleCore 𝕜 B} (f : B → (Fin C₁.rank → 𝕜) →ₗ[𝕜] (Fin C₂.rank → 𝕜))
    (hf : Continuous fun p : C₁.core.TotalSpace => (⟨p.proj, f p.proj p.2⟩ : C₂.core.TotalSpace))
    (x : B) (v : Fin C₁.rank → 𝕜) : (coordinateHomOfTotalSpace f hf).fiberMap x v = f x v :=
  congrArg (fun S : (Fin C₁.rank → 𝕜) →L[𝕜] (Fin C₂.rank → 𝕜) => S v)
    (congrFun (CoordinateHom.fiberMap_ofContinuous _ _) x)

section CoordinateHom
private def subStratumHomeomorph (A : FiniteRankAtlas 𝕜 X) (m : ℕ) (P : X → Prop)
    (hP : ∀ x, P x → A.rank x = m) :
    {p : TotalSpace Unit A.Fiber // P p.proj} ≃ₜ ((A.stratumCore m).pullback
      ⟨fun x : {x : X // P x} => ⟨x.1, hP x.1 x.2⟩,
        continuous_subtype_val.subtype_mk _⟩).core.TotalSpace :=
  let inc : C({x : X // P x}, {x : X // A.rank x = m}) :=
    ⟨fun x => ⟨x.1, hP x.1 x.2⟩, continuous_subtype_val.subtype_mk _⟩
  { toFun p := ⟨⟨p.1.proj, p.2⟩, fun i => p.1.2 (Fin.cast (hP p.1.proj p.2).symm i)⟩
    invFun q := ⟨⟨q.proj.1, fun i => q.2 (Fin.cast (hP q.proj.1 q.proj.2) i)⟩, q.proj.2⟩
    left_inv _ := Subtype.ext <| TotalSpace.mk_inj.2 <| funext fun _ => by simp
    right_inv _ := TotalSpace.mk_inj.2 <| funext fun _ => by simp
    continuous_toFun := by
      rw [(A.stratumCore m).continuous_core_pullback_iff inc]
      have hm := (A.continuous_mk_iff_rankStrata A.continuous_proj (fun p => p.2)).1 continuous_id m
      exact ⟨(A.continuous_proj.comp continuous_subtype_val).subtype_mk _,
        (hm.comp (continuous_subtype_val.subtype_mk fun p => hP p.1.proj p.2)).congr
          fun ⟨⟨x, _⟩, hp⟩ => ((A.stratumCore m).pullbackLift_mk inc ⟨x, hp⟩ _).symm⟩
    continuous_invFun := Continuous.subtype_mk ((A.totalSpaceHomeomorph.continuous.comp
      (continuous_sigmaMk.comp ((A.stratumCore m).continuous_pullbackLift inc))).congr
        fun ⟨⟨_, _⟩, _⟩ => by
          dsimp only [Function.comp_apply]
          rw [(A.stratumCore m).pullbackLift_mk, totalSpaceHomeomorph_apply]; rfl) _ }

section JointStrata
variable (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ)

/-- The clopen subset of base points where `A` has rank `m` and `D` has rank `n`. -/
abbrev JointStratum : Type u := {x : X // A.rank x = m ∧ D.rank x = n}

/-- Inclusion of a joint rank stratum into the rank-`m` stratum of the source atlas. -/
-- Expose the continuous map so pulled-back stratum cores unify with `subStratumHomeomorph`.
@[expose] def jointFst : C(JointStratum A D m n, {x : X // A.rank x = m}) :=
  ⟨fun x => ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- Inclusion of a joint rank stratum into the rank-`n` stratum of the target atlas. -/
-- Expose the continuous map so pulled-back stratum cores unify with `subStratumHomeomorph`.
@[expose] def jointSnd : C(JointStratum A D m n, {x : X // D.rank x = n}) :=
  ⟨fun x => ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The point-indexed source core over the `(m, n)` joint rank stratum. -/
abbrev jointSourceCore : FiniteRankBundleCore 𝕜 (JointStratum A D m n) :=
  (A.stratumCore m).pullback (jointFst A D m n)

/-- The point-indexed target core over the `(m, n)` joint rank stratum. -/
abbrev jointTargetCore : FiniteRankBundleCore 𝕜 (JointStratum A D m n) :=
  (D.stratumCore n).pullback (jointSnd A D m n)

/-- Homeomorphism of the part of `TotalSpace Unit A.Fiber` over `JointStratum A D m n` with the
total space of `A.jointSourceCore D m n`. -/
def jointSourceHomeomorph : {p : TotalSpace Unit A.Fiber // A.rank p.proj = m ∧ D.rank p.proj = n}
    ≃ₜ (A.jointSourceCore D m n).core.TotalSpace :=
  subStratumHomeomorph A m (fun x => A.rank x = m ∧ D.rank x = n) fun _ h => h.1

@[simp] theorem jointSourceHomeomorph_apply
    (p : {p : TotalSpace Unit A.Fiber // A.rank p.proj = m ∧ D.rank p.proj = n}) :
    jointSourceHomeomorph A D m n p = ⟨⟨p.1.proj, p.2⟩, fun i => p.1.2 (Fin.cast p.2.1.symm i)⟩ :=
  (rfl)
@[simp] theorem jointSourceHomeomorph_symm_apply (q : (A.jointSourceCore D m n).core.TotalSpace) :
    (jointSourceHomeomorph A D m n).symm q =
      ⟨⟨q.proj.1, fun i => q.2 (Fin.cast q.proj.2.1 i)⟩, q.proj.2⟩ := (rfl)

/-- Homeomorphism of the part of `TotalSpace Unit D.Fiber` over `JointStratum A D m n` with the
total space of `A.jointTargetCore D m n`. -/
def jointTargetHomeomorph : {p : TotalSpace Unit D.Fiber // A.rank p.proj = m ∧ D.rank p.proj = n}
    ≃ₜ (A.jointTargetCore D m n).core.TotalSpace :=
  subStratumHomeomorph D n (fun x => A.rank x = m ∧ D.rank x = n) fun _ h => h.2

@[simp] theorem jointTargetHomeomorph_apply
    (p : {p : TotalSpace Unit D.Fiber // A.rank p.proj = m ∧ D.rank p.proj = n}) :
    jointTargetHomeomorph A D m n p = ⟨⟨p.1.proj, p.2⟩, fun i => p.1.2 (Fin.cast p.2.2.symm i)⟩ :=
  (rfl)
@[simp] theorem jointTargetHomeomorph_symm_apply (q : (A.jointTargetCore D m n).core.TotalSpace) :
    (jointTargetHomeomorph A D m n).symm q =
      ⟨⟨q.proj.1, fun i => q.2 (Fin.cast q.proj.2.2 i)⟩, q.proj.2⟩ := (rfl)
end JointStrata

/-- Glue coordinate morphisms on all joint rank strata into a variable-rank atlas morphism. -/
def ofCoordinateHoms {A D : FiniteRankAtlas 𝕜 X}
    (a : ∀ m n : ℕ, A.jointSourceCore D m n ⟶ A.jointTargetCore D m n) : A ⟶ D where
  fiberMap x := ((a (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩).toLinearMap
  continuous_totalSpaceMap := by
    refine continuous_of_cover_nhds (s := fun mn : ℕ × ℕ =>
      {p : TotalSpace Unit A.Fiber | A.rank p.proj = mn.1 ∧ D.rank p.proj = mn.2}) (fun p =>
        ⟨(A.rank p.proj, D.rank p.proj), (((A.rank.isLocallyConstant.isOpen_fiber _).inter
          (D.rank.isLocallyConstant.isOpen_fiber _)).preimage A.continuous_proj).mem_nhds
            ⟨rfl, rfl⟩⟩) fun ⟨m, n⟩ => ?_
    rw [continuousOn_iff_continuous_domRestrict]
    refine (continuous_subtype_val.comp <| (jointTargetHomeomorph A D m n).symm.continuous.comp <|
      (a m n).continuous_totalSpaceMap.comp (jointSourceHomeomorph A D m n).continuous).congr ?_
    rintro ⟨⟨x, v⟩, hm, hn⟩; cases hm; cases hn
    simp only [Function.comp_apply, Set.domRestrict_apply, jointSourceHomeomorph_apply,
      CoordinateHom.totalSpaceMap_def, jointTargetHomeomorph_symm_apply, Fin.cast_refl]; rfl

@[simp] theorem fiberMap_ofCoordinateHoms {A D : FiniteRankAtlas 𝕜 X}
    (a : ∀ m n : ℕ, A.jointSourceCore D m n ⟶ A.jointTargetCore D m n) (x : X) :
    (ofCoordinateHoms a).fiberMap x =
      ((a (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩).toLinearMap := (rfl)

/-- Extract the coordinate morphism on the `(m, n)` joint rank stratum from an atlas morphism. -/
def toCoordinateHom {A D : FiniteRankAtlas 𝕜 X} (f : A ⟶ D) (m n : ℕ) :
    A.jointSourceCore D m n ⟶ A.jointTargetCore D m n :=
  let lin (x : JointStratum A D m n) : (Fin m → 𝕜) →ₗ[𝕜] (Fin n → 𝕜) :=
    (LinearEquiv.funCongrLeft 𝕜 𝕜 (Fin.castOrderIso x.2.2.symm).toEquiv).toLinearMap.comp
      ((f.fiberMap x.1).comp
        (LinearEquiv.funCongrLeft 𝕜 𝕜 (Fin.castOrderIso x.2.1).toEquiv).toLinearMap)
  coordinateHomOfTotalSpace lin <| ((jointTargetHomeomorph A D m n).continuous.comp <|
    ((f.continuous_totalSpaceMap.comp continuous_subtype_val).subtype_mk fun p => p.2).comp
      (jointSourceHomeomorph A D m n).symm.continuous).congr fun ⟨⟨_, hm, hn⟩, _⟩ => by
        cases hm; cases hn; simp only [Function.comp_apply, jointTargetHomeomorph_apply, lin]; rfl

@[simp] theorem fiberMap_toCoordinateHom_self {A D : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ D) (x : X) (v : A.Fiber x) :
    (toCoordinateHom f (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩ v = f.fiberMap x v := by
  dsimp only [toCoordinateHom]; rw [fiberMap_coordinateHomOfTotalSpace]; rfl
theorem fiberMap_toCoordinateHom {A D : FiniteRankAtlas 𝕜 X} (f : A ⟶ D) {m n : ℕ}
    (y : JointStratum A D m n) (v : Fin m → 𝕜) :
    (toCoordinateHom f m n).fiberMap y v =
      f.fiberMap y.1 (v ∘ Fin.cast y.2.1) ∘ Fin.cast y.2.2.symm := by
  rcases y with ⟨x, rfl, rfl⟩; exact fiberMap_toCoordinateHom_self f x v

/-- Gluing the joint-stratum coordinate morphisms of an atlas morphism recovers it. -/
@[simp] theorem ofCoordinateHoms_toCoordinateHom {A D : FiniteRankAtlas 𝕜 X} (f : A ⟶ D) :
    ofCoordinateHoms (toCoordinateHom f) = f :=
  hom_ext fun x => LinearMap.ext (fiberMap_toCoordinateHom_self f x)

/-- Extracting joint-stratum coordinate morphisms after `ofCoordinateHoms` recovers each piece. -/
@[simp] theorem toCoordinateHom_ofCoordinateHoms {A D : FiniteRankAtlas 𝕜 X}
    (a : ∀ m n : ℕ, A.jointSourceCore D m n ⟶ A.jointTargetCore D m n) (m n : ℕ) :
    toCoordinateHom (ofCoordinateHoms a) m n = a m n := by
  refine FiniteRankBundleCore.hom_ext fun ⟨x, hm, hn⟩ => ?_
  cases hm; cases hn; exact ContinuousLinearMap.ext (fiberMap_toCoordinateHom_self _ x)

/-- Atlas morphisms correspond additively to coordinate morphisms on clopen joint rank strata. -/
def coordinateHomEquiv (A D : FiniteRankAtlas 𝕜 X) :
    (A ⟶ D) ≃+ ∀ m n : ℕ, (A.jointSourceCore D m n ⟶ A.jointTargetCore D m n) where
  toFun := toCoordinateHom; invFun := ofCoordinateHoms
  left_inv := ofCoordinateHoms_toCoordinateHom
  right_inv a := funext fun m => funext (toCoordinateHom_ofCoordinateHoms a m)
  map_add' _ _ := funext fun _ => funext fun _ => FiniteRankBundleCore.hom_ext fun ⟨_, hm, hn⟩ => by
    cases hm; cases hn
    exact ContinuousLinearMap.ext fun _ => by simp [fiberMap_toCoordinateHom_self]

@[simp] theorem coordinateHomEquiv_apply (A D : FiniteRankAtlas 𝕜 X) (f : A ⟶ D) :
    coordinateHomEquiv A D f = toCoordinateHom f := (rfl)
@[simp] theorem coordinateHomEquiv_symm_apply (A D : FiniteRankAtlas 𝕜 X)
    (a : ∀ m n : ℕ, A.jointSourceCore D m n ⟶ A.jointTargetCore D m n) :
    (coordinateHomEquiv A D).symm a = ofCoordinateHoms a := (rfl)

/-- An atlas morphism is an isomorphism if and only if it is bijective on every fibre. -/
theorem isIso_iff_bijective {A D : FiniteRankAtlas 𝕜 X} (f : A ⟶ D) :
    IsIso f ↔ ∀ x : X, Function.Bijective (f.fiberMap x) := by
  refine ⟨fun _ x => ((fiberFunctor (𝕜 := 𝕜) x).mapIso (asIso f)).toLinearEquiv.bijective,
    fun hbij => ?_⟩
  let e (x : X) : A.Fiber x ≃ₗ[𝕜] D.Fiber x := LinearEquiv.ofBijective (f.fiberMap x) (hbij x)
  have hrank (x : X) : A.rank x = D.rank x :=
    (Module.finrank_fin_fun 𝕜).symm.trans <| (e x).finrank_eq.trans (Module.finrank_fin_fun 𝕜)
  have hinv : Continuous fun p : TotalSpace Unit D.Fiber =>
      (⟨p.proj, (e p.proj).symm p.2⟩ : TotalSpace Unit A.Fiber) := by
    refine continuous_of_cover_nhds
      (s := fun n : ℕ => {p : TotalSpace Unit D.Fiber | A.rank p.proj = n ∧ D.rank p.proj = n})
      (fun p => ⟨D.rank p.proj, (((A.rank.isLocallyConstant.isOpen_fiber _).inter
        (D.rank.isLocallyConstant.isOpen_fiber _)).preimage D.continuous_proj).mem_nhds
          ⟨hrank p.proj, rfl⟩⟩) fun n => ?_
    let φ := toCoordinateHom f n n
    let Z := (A.jointSourceCore D n n).core; let W := (A.jointTargetCore D n n).core
    have hφ (y : JointStratum A D n n) : Function.Bijective (φ.fiberMap y) := by
      have hcomp : (φ.fiberMap y : (Fin n → 𝕜) → (Fin n → 𝕜)) =
          (Equiv.arrowCongr (Fin.castOrderIso y.2.2).toEquiv (Equiv.refl 𝕜)) ∘ (f.fiberMap y.1) ∘
            (Equiv.arrowCongr (Fin.castOrderIso y.2.1.symm).toEquiv (Equiv.refl 𝕜)) :=
        funext (fiberMap_toCoordinateHom f y)
      exact hcomp ▸ (Equiv.bijective _).comp ((hbij y.1).comp (Equiv.bijective _))
    let eφ (y : JointStratum A D n n) : (Fin n → 𝕜) ≃ₗ[𝕜] (Fin n → 𝕜) :=
      LinearEquiv.ofBijective (φ.fiberMap y).toLinearMap (hφ y)
    have hcore : Continuous fun q : W.TotalSpace =>
        (⟨q.proj, (eφ q.proj).symm q.2⟩ : Z.TotalSpace) := by
      refine continuous_iff_continuousAt.2 fun q₀ => ?_
      let y₀ := q₀.proj; rw [FiberBundle.continuousAt_totalSpace]
      refine ⟨W.continuous_proj.continuousAt, ?_⟩
      let s : Set (JointStratum A D n n) := Z.baseSet y₀ ∩ W.baseSet y₀
      have hy₀ : y₀ ∈ s := ⟨Z.mem_baseSet_at y₀, W.mem_baseSet_at y₀⟩
      let V₀ : Set W.TotalSpace := {q | q.proj ∈ s}
      have hV₀ : V₀ ∈ 𝓝 q₀ := (((Z.isOpen_baseSet y₀).inter (W.isOpen_baseSet y₀)).preimage
        W.continuous_proj).mem_nhds hy₀
      apply (continuousWithinAt_iff_continuousAt hV₀).1
      apply (continuousWithinAt_iff_continuousAt_domRestrict _ (x := q₀) (s := V₀) hy₀).2
      let T : C(↥s, (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜)) := φ.operator y₀ y₀
      let M (u : ↥s) : Matrix (Fin n) (Fin n) 𝕜 := LinearMap.toMatrix' (T u).toLinearMap
      have hM : Continuous M := continuous_matrix fun r c => (continuous_apply r).comp <|
        ((ContinuousLinearMap.apply 𝕜 (Fin n → 𝕜) (Pi.single c 1)).continuous).comp T.continuous
      let u₀ : ↥s := ⟨y₀, hy₀⟩
      have hTu₀ : T u₀ = φ.fiberMap y₀ :=
        (φ.operator_eq y₀ y₀ u₀).trans (Z.inChartCoordinates_indexAt W y₀ (φ.fiberMap y₀))
      have hM₀ : M u₀ * LinearMap.toMatrix' (eφ y₀).symm.toLinearMap = 1 := by
        rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
        exact congrArg LinearMap.toMatrix' <| LinearMap.ext fun v =>
          (congrArg (fun S : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜) => S ((eφ y₀).symm v)) hTu₀).trans
            ((eφ y₀).apply_symm_apply v)
      have hdet₀ : (M u₀).det ≠ 0 := fun h0 => (one_ne_zero : (1 : 𝕜) ≠ 0) <| by
        rw [← Matrix.det_one (n := Fin n), ← hM₀, Matrix.det_mul, h0, zero_mul]
      let u (q : ↥V₀) : ↥s := ⟨q.1.proj, q.2⟩
      have hu : Continuous u := (W.continuous_proj.comp continuous_subtype_val).subtype_mk _
      have hMinv : ContinuousAt (fun q : ↥V₀ => (M (u q))⁻¹) ⟨q₀, hy₀⟩ :=
        ContinuousAt.comp (f := u) (ContinuousAt.comp (f := M) (continuousAt_matrix_inv (M u₀)
          ((Ring.inverse_eq_inv' (G₀ := 𝕜)).symm ▸ continuousAt_inv₀ hdet₀)) hM.continuousAt)
            hu.continuousAt
      have hw : ContinuousAt (fun q : ↥V₀ => (W.localTriv y₀ q.1).2) ⟨q₀, hy₀⟩ :=
        (((W.localTriv y₀).continuousOn.continuousAt ((W.localTriv y₀).open_source.mem_nhds
          ((W.mem_localTriv_source y₀ q₀).2 hy₀.2))).comp continuous_subtype_val.continuousAt).snd
      refine ((continuous_fst.matrix_mulVec continuous_snd).continuousAt.comp
        (hMinv.prodMk_nhds hw)).congr_of_eventuallyEq ?_
      filter_upwards [((hM.matrix_det.comp hu).continuousAt.eventually_ne hdet₀)] with q hq
      let p : Z.TotalSpace := ⟨q.1.proj, (eφ q.1.proj).symm q.1.2⟩
      have hpq : φ.totalSpaceMap p = q.1 := by
        rw [CoordinateHom.totalSpaceMap_def]
        exact TotalSpace.ext rfl (heq_of_eq ((eφ q.1.proj).apply_symm_apply q.1.2))
      have htriv : (W.localTriv y₀ q.1).2 = M (u q) *ᵥ (Z.localTriv y₀ p).2 := by
        rw [← hpq, φ.localTriv_fiberMap y₀ y₀ p q.2.1 q.2.2]
        exact (LinearMap.toMatrix'_mulVec (T (u q)).toLinearMap ((Z.localTriv y₀ p).2)).symm
      have hinv_vec : (M (u q))⁻¹ *ᵥ (W.localTriv y₀ q.1).2 = (Z.localTriv y₀ p).2 := by
        rw [htriv, Matrix.mulVec_mulVec, (M (u q)).nonsing_inv_mul hq.isUnit, Matrix.one_mulVec]
      exact (congrArg (fun t => (t p).2) (Z.trivializationAt y₀)).trans hinv_vec.symm
    rw [continuousOn_iff_continuous_domRestrict]
    refine (continuous_subtype_val.comp <| (jointSourceHomeomorph A D n n).symm.continuous.comp <|
      hcore.comp (jointTargetHomeomorph A D n n).continuous).congr fun ⟨⟨x, w⟩, hm, hn⟩ => ?_
    have hsymm : (eφ ⟨x, hm, hn⟩).symm (fun j => w (Fin.cast hn.symm j)) =
        fun j => (e x).symm w (Fin.cast hm.symm j) := by
      apply (eφ ⟨x, hm, hn⟩).injective
      refine ((eφ ⟨x, hm, hn⟩).apply_symm_apply _).trans ?_
      symm; refine (LinearEquiv.ofBijective_apply _ _).trans ?_
      rw [ContinuousLinearMap.coe_coe, fiberMap_toCoordinateHom f ⟨x, hm, hn⟩]
      have harg : ((fun k => (e x).symm w (Fin.cast hm.symm k)) ∘ Fin.cast hm) = (e x).symm w :=
        funext fun _ => by simp
      rw [harg]
      exact congrArg (· ∘ Fin.cast hn.symm)
        ((LinearEquiv.ofBijective_apply _ _).symm.trans ((e x).apply_symm_apply w))
    dsimp only [Function.comp_apply, Set.domRestrict_apply]
    rw [jointTargetHomeomorph_apply]; dsimp only; rw [jointSourceHomeomorph_symm_apply]
    exact congrArg (TotalSpace.mk x) <| funext fun i =>
      (congrFun hsymm (Fin.cast hm i)).trans (by simp)
  have heq : (isoMk e f.continuous_totalSpaceMap hinv).hom = f :=
    hom_ext fun x => (fiberMap_isoMk_hom e _ _ x).trans (LinearMap.ext fun _ => rfl)
  exact heq ▸ (isoMk e f.continuous_totalSpaceMap hinv).isIso_hom

end CoordinateHom

section FixedRankComparison

/-- View a constant-rank core as a variable-rank atlas with constant rank. -/
-- Expose the rank projection so reconstructed coordinate fibres reduce to `Fin C.rank → 𝕜`.
@[expose, implicit_reducible]
def ofCoreObj (C : FiniteRankBundleCore 𝕜 X) : FiniteRankAtlas 𝕜 X where
  rank := LocallyConstant.const X C.rank
  charts m :=
    if h : C.rank = m then h ▸ (C.pullback ⟨Subtype.val, continuous_subtype_val⟩).core
    else (FiniteRankBundleCore.trivial 𝕜 {x : X // LocallyConstant.const X C.rank x = m} m).core
  indexAt_eq m x :=
    if h : C.rank = m then by
      cases h; exact congrArg (fun Z : VectorBundleCore 𝕜 _ (Fin C.rank → 𝕜) _ => Z.indexAt x)
        (dite_eq_left_iff.2 fun h' => (h' rfl).elim)
    else congrArg (fun Z : VectorBundleCore 𝕜 _ (Fin m → 𝕜) _ => Z.indexAt x)
      (dite_eq_right_iff.2 fun h' => (h h').elim)

@[simp] theorem rank_ofCoreObj (C : FiniteRankBundleCore 𝕜 X) :
    (ofCoreObj C).rank = LocallyConstant.const X C.rank := (rfl)

@[simp] theorem charts_ofCoreObj_self (C : FiniteRankBundleCore 𝕜 X) :
    (ofCoreObj C).charts C.rank = (C.pullback ⟨Subtype.val, continuous_subtype_val⟩).core :=
  dite_eq_left_iff.2 fun h => (h rfl).elim

/-- Homeomorphism between `C.core.TotalSpace` and `TotalSpace Unit (ofCoreObj C).Fiber`. -/
def ofCoreHomeomorph (C : FiniteRankBundleCore 𝕜 X) :
    C.core.TotalSpace ≃ₜ TotalSpace Unit (ofCoreObj C).Fiber :=
  let inc : C({x : X // LocallyConstant.const X C.rank x = C.rank}, X) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  { toFun p := ⟨p.proj, p.2⟩
    invFun p := ⟨p.proj, p.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := ((ofCoreObj C).continuous_mk_iff_rankStrata C.core.continuous_proj
      (fun p : C.core.TotalSpace => p.2)).2 fun m => by
        by_cases hm : C.rank = m
        · subst hm
          have hc : Continuous fun y :
              {y : C.core.TotalSpace // (ofCoreObj C).rank y.proj = C.rank} =>
              (⟨⟨y.1.proj, y.2⟩, y.1.2⟩ : (C.pullback inc).core.TotalSpace) :=
            (C.continuous_core_pullback_iff inc).2
              ⟨(C.core.continuous_proj.comp continuous_subtype_val).subtype_mk fun y => y.2,
                continuous_subtype_val.congr fun y =>
                  (C.pullbackLift_mk inc ⟨y.1.proj, y.2⟩ y.1.2).symm⟩
          exact (charts_ofCoreObj_self C ▸ hc).congr fun _ => rfl
        · have : IsEmpty {p : C.core.TotalSpace // (ofCoreObj C).rank p.proj = m} :=
            ⟨fun p => hm ((congrFun (LocallyConstant.coe_const C.rank) p.1.proj).symm.trans p.2)⟩
          exact continuous_of_discreteTopology
    continuous_invFun := by
      have hglued : Continuous fun q : (ofCoreObj C).GluedTotalSpace => (⟨q.2.proj.1, fun i => q.2.2
          (Fin.cast ((congrFun (LocallyConstant.coe_const C.rank) q.2.proj.1).symm.trans q.2.proj.2)
            i)⟩ : C.core.TotalSpace) := continuous_sigma fun m => by
        by_cases hm : C.rank = m
        · subst hm
          have hc : Continuous fun p : (C.pullback inc).core.TotalSpace =>
              (⟨p.proj.1, fun i => p.2 (Fin.cast ((congrFun (LocallyConstant.coe_const C.rank)
                p.proj.1).symm.trans p.proj.2) i)⟩ : C.core.TotalSpace) :=
            (C.continuous_pullbackLift inc).congr fun ⟨_, _⟩ => by
              rw [C.pullbackLift_mk]; exact congrArg (TotalSpace.mk _) (funext fun _ => by simp)
          exact (charts_ofCoreObj_self C ▸ hc).congr fun _ => rfl
        · have : IsEmpty (((ofCoreObj C).charts m).TotalSpace) := ⟨fun p =>
            hm ((congrFun (LocallyConstant.coe_const C.rank) p.proj.1).symm.trans p.proj.2)⟩
          exact continuous_of_discreteTopology
      refine (hglued.comp (ofCoreObj C).totalSpaceHomeomorph.symm.continuous).congr fun p => ?_
      dsimp only [Function.comp_apply]; rw [totalSpaceHomeomorph_symm_apply]; rfl }

@[simp] theorem ofCoreHomeomorph_apply (C : FiniteRankBundleCore 𝕜 X) (p : C.core.TotalSpace) :
    ofCoreHomeomorph C p = ⟨p.proj, p.2⟩ := (rfl)

@[simp] theorem ofCoreHomeomorph_symm_apply (C : FiniteRankBundleCore 𝕜 X)
    (p : TotalSpace Unit (ofCoreObj C).Fiber) : (ofCoreHomeomorph C).symm p = ⟨p.proj, p.2⟩ := (rfl)

variable (𝕜 X) in
/-- The embedding of constant-rank point-indexed cores into variable-rank bundle atlases. -/
-- Expose the object assignment so morphism types reduce to `ofCoreObj`.
@[expose, reducible]
def ofCore : FiniteRankBundleCore 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj := ofCoreObj
  map {C D} f :=
    { fiberMap x := (f.fiberMap x).toLinearMap
      continuous_totalSpaceMap := ((ofCoreHomeomorph D).continuous.comp <|
        f.continuous_totalSpaceMap.comp (ofCoreHomeomorph C).symm.continuous).congr fun _ => by
          simp only [Function.comp_apply, ofCoreHomeomorph_symm_apply,
            CoordinateHom.totalSpaceMap_def, ofCoreHomeomorph_apply]; rfl }
  map_id _ := hom_ext fun _ => LinearMap.ext fun _ => by
    simp only [FiniteRankBundleCore.fiberMap_id]; rfl
  map_comp _ _ := hom_ext fun _ => LinearMap.ext fun _ => by
    simp only [FiniteRankBundleCore.fiberMap_comp]; rfl

@[simp] theorem ofCore_obj (C : FiniteRankBundleCore 𝕜 X) : (ofCore 𝕜 X).obj C = ofCoreObj C :=
  (rfl)
@[simp] theorem fiberMap_ofCore_map {C D : FiniteRankBundleCore 𝕜 X} (f : C ⟶ D) (x : X) :
    ((ofCore 𝕜 X).map f).fiberMap x = (f.fiberMap x).toLinearMap := (rfl)

instance : (ofCore 𝕜 X).Additive where
  map_add := by
    intros; exact hom_ext fun _ => LinearMap.ext fun _ => by
      simp only [FiniteRankBundleCore.fiberMap_add]; rfl

instance : (ofCore 𝕜 X).Faithful where
  map_injective {C D _ _} h := FiniteRankBundleCore.hom_ext fun x => ContinuousLinearMap.ext
    fun v => congrArg (fun φ : ofCoreObj C ⟶ ofCoreObj D => φ.fiberMap x v) h

instance : (ofCore 𝕜 X).Full where
  map_surjective {C D} φ := ⟨coordinateHomOfTotalSpace φ.fiberMap <|
    ((ofCoreHomeomorph D).symm.continuous.comp <|
      φ.continuous_totalSpaceMap.comp (ofCoreHomeomorph C).continuous).congr fun _ => by
        simp only [Function.comp_apply, ofCoreHomeomorph_symm_apply]; rfl,
    hom_ext fun x => LinearMap.ext (fiberMap_coordinateHomOfTotalSpace φ.fiberMap _ x)⟩

/-- Pulling back the `n`th stratum core of a constant-rank-`n` atlas recovers it up to iso. -/
def ofCorePullbackIso (A : FiniteRankAtlas 𝕜 X) (n : ℕ) (hn : ∀ x, A.rank x = n) :
    (ofCore 𝕜 X).obj ((A.stratumCore n).pullback ⟨fun x => ⟨x, hn x⟩,
      continuous_id.subtype_mk hn⟩) ≅ A := by
  let s : C(X, {x : X // A.rank x = n}) := ⟨fun x => ⟨x, hn x⟩, continuous_id.subtype_mk hn⟩
  let C := (A.stratumCore n).pullback s
  let e (x : X) : ((ofCore 𝕜 X).obj C).Fiber x ≃ₗ[𝕜] A.Fiber x := LinearEquiv.funCongrLeft 𝕜 𝕜
    (finCongr ((hn x).trans (congrFun (LocallyConstant.coe_const C.rank) x).symm))
  refine isoMk e ((A.continuous_mk_iff_rankStrata (ofCoreObj C).continuous_proj _).2 fun m => ?_) ?_
  · by_cases hm : n = m
    · subst hm
      refine ((((A.stratumCore n).continuous_pullbackLift s).comp
        (ofCoreHomeomorph C).symm.continuous).comp continuous_subtype_val).congr
        fun ⟨⟨x, v⟩, _⟩ => ?_
      dsimp only [Function.comp_apply, e]; rw [ofCoreHomeomorph_symm_apply]
      exact (A.stratumCore n).pullbackLift_eq_mk s _ rfl (funext fun _ => congrArg v (Fin.ext rfl))
    · have : IsEmpty {p : TotalSpace Unit ((ofCore 𝕜 X).obj C).Fiber // A.rank p.proj = m} :=
        ⟨fun p => hm ((hn p.1.proj).symm.trans p.2)⟩
      exact continuous_of_discreteTopology
  · have hcore : Continuous fun p : TotalSpace Unit A.Fiber =>
        (⟨p.proj, (e p.proj).symm p.2⟩ : C.core.TotalSpace) :=
      ((A.stratumCore n).continuous_core_pullback_iff s).2 ⟨A.continuous_proj,
        (((A.continuous_mk_iff_rankStrata A.continuous_proj (fun p => p.2)).1 continuous_id n).comp
          (continuous_id.subtype_mk fun p => hn p.proj)).congr fun ⟨x, v⟩ => by
            dsimp only [Function.comp_apply, id_eq, e]
            exact (TotalSpace.ext rfl (heq_of_eq <| funext fun _ => congrArg v (Fin.ext rfl))).trans
              ((A.stratumCore n).pullbackLift_mk s x _).symm⟩
    exact ((ofCoreHomeomorph C).continuous.comp hcore).congr fun p => by
      dsimp only [Function.comp_apply]; rw [ofCoreHomeomorph_apply]

/-- An atlas lies in the essential image of `ofCore` iff its rank takes at most one value. -/
theorem exists_ofCore_iso_iff (A : FiniteRankAtlas 𝕜 X) :
    (∃ C : FiniteRankBundleCore 𝕜 X, Nonempty ((ofCore 𝕜 X).obj C ≅ A)) ↔
      (Set.range A.rank).Subsingleton := by
  constructor
  · rintro ⟨C, ⟨e⟩⟩ _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have hr := e.finiteRankAtlas_rank_eq
    exact ((congrFun (LocallyConstant.coe_const C.rank) x).symm.trans
      (congrArg (· x) hr)).symm.trans
      ((congrFun (LocallyConstant.coe_const C.rank) y).symm.trans (congrArg (· y) hr))
  · intro hsub; rcases isEmpty_or_nonempty X with hX | hX
    · let Z₀ := FiniteRankBundleCore.trivial 𝕜 X 0
      have : IsEmpty (TotalSpace Unit ((ofCore 𝕜 X).obj Z₀).Fiber) := ⟨fun p => isEmptyElim p.proj⟩
      have : IsEmpty (TotalSpace Unit A.Fiber) := ⟨fun p => isEmptyElim p.proj⟩
      exact ⟨Z₀, ⟨isoMk isEmptyElim continuous_of_discreteTopology continuous_of_discreteTopology⟩⟩
    · exact ⟨_, ⟨ofCorePullbackIso A (A.rank hX.some) fun x => hsub ⟨x, rfl⟩ ⟨hX.some, rfl⟩⟩⟩

instance [PreconnectedSpace X] : (ofCore 𝕜 X).EssSurj where
  mem_essImage A := (exists_ofCore_iso_iff A).2 fun _ ⟨x, hx⟩ _ ⟨y, hy⟩ =>
    hx ▸ hy ▸ A.rank.apply_eq_of_preconnectedSpace x y

instance [PreconnectedSpace X] : (ofCore 𝕜 X).IsEquivalence where

end FixedRankComparison

end TauCeti.FiniteRankAtlas

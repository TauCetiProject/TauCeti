/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.Logic.Small.Basic

/-!
# Coordinate morphisms, pullbacks, and fixed-rank comparison for bundle atlases

Between variable-rank atlases `A` and `D` over `X` (`TauCeti.FiniteRankAtlas`), restricting charts
to the clopen joint rank strata `{x : X // A.rank x = m ∧ D.rank x = n}` yields cores
`A.jointSourceCore D m n` and `A.jointTargetCore D m n`. Compatible chart operators glue via
`ofCoordinateHoms`, identifying `A ⟶ D` additively over a complete field (`coordinateHomEquiv`) and
characterizing isomorphisms by fibrewise bijectivity (`isIso_iff_bijective`). We also construct
`pullbackFunctor`, trivial/zero atlases, the constant-rank embedding `ofCore`, and
`EssentiallySmall.{u} (FiniteRankAtlas 𝕜 X)` under `[Small.{u} 𝕜]`.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits Set Topology VectorBundleCore

namespace TauCeti.FiniteRankAtlas

universe u v w z

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

/-- Extract the point-indexed core on the rank-`n` clopen stratum of an atlas. -/
-- Expose rank and core projections so stratum total spaces and model fibres reduce.
@[expose, implicit_reducible]
def stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    FiniteRankBundleCore 𝕜 {x : X // A.rank x = n} where
  rank := n
  core := A.charts n
  indexAt_eq := A.indexAt_eq n

@[simp] theorem rank_stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (A.stratumCore n).rank = n := (rfl)

@[simp] theorem core_stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (A.stratumCore n).core = A.charts n := (rfl)

section TrivialAndZero

variable (𝕜) in
/-- The trivial variable-rank atlas with prescribed locally constant rank `r`. -/
-- Expose the rank projection so reconstructed coordinate fibres reduce to `Fin (r x) → 𝕜`.
@[expose, implicit_reducible]
def trivialOfRank (r : LocallyConstant X ℕ) : FiniteRankAtlas 𝕜 X where
  rank := r
  charts n := (FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n).core
  indexAt_eq _ _ := rfl

@[simp] theorem rank_trivialOfRank (r : LocallyConstant X ℕ) :
    (trivialOfRank 𝕜 r).rank = r := (rfl)

variable (𝕜 X) in
/-- The constant-rank trivial atlas of rank `n`. -/
-- Expose the rank projection so reconstructed coordinate fibres reduce to `Fin n → 𝕜`.
@[expose, implicit_reducible]
def trivial (n : ℕ) : FiniteRankAtlas 𝕜 X :=
  trivialOfRank 𝕜 (LocallyConstant.const X n)

@[simp] theorem rank_trivial (n : ℕ) :
    (trivial 𝕜 X n).rank = LocallyConstant.const X n := (rfl)

/-- The rank-zero trivial atlas is a zero object, including over an empty or disconnected base. -/
theorem isZero_trivial_zero : IsZero (trivial 𝕜 X 0) := by
  rw [IsZero.iff_id_eq_zero]; apply hom_ext; intro x; ext v i; exact Fin.elim0 i

instance : HasZeroObject (FiniteRankAtlas 𝕜 X) :=
  ⟨⟨trivial 𝕜 X 0, isZero_trivial_zero⟩⟩

/-- Over an empty base every variable-rank atlas is equal to the rank-zero trivial atlas. -/
instance [IsEmpty X] : Unique (FiniteRankAtlas 𝕜 X) where
  default := trivial 𝕜 X 0
  uniq := fun ⟨r, _, _⟩ => by
    obtain rfl : r = LocallyConstant.const X 0 := LocallyConstant.ext isEmptyElim
    congr; funext _; exact VectorBundleCore.ext isEmptyElim isEmptyElim isEmptyElim

end TrivialAndZero

section Pullback

variable {Y : Type w} {Z : Type z} [TopologicalSpace Y] [TopologicalSpace Z]

/-- Pull back a variable-rank atlas along a continuous map of bases. -/
-- Expose the rank projection so pulled-back coordinate fibres reduce to `A.Fiber (f x)`.
@[expose, implicit_reducible]
def pullback (A : FiniteRankAtlas 𝕜 Y) (f : C(X, Y)) : FiniteRankAtlas 𝕜 X where
  rank := A.rank.comap f
  charts n := ((A.stratumCore n).pullback
    ⟨fun x : {x : X // A.rank.comap f x = n} => ⟨f x.1, x.2⟩,
      (f.continuous.comp continuous_subtype_val).subtype_mk _⟩).core
  indexAt_eq _ _ := rfl

@[simp] theorem rank_pullback (A : FiniteRankAtlas 𝕜 Y) (f : C(X, Y)) :
    (A.pullback f).rank = A.rank.comap f := (rfl)

@[simp] theorem pullback_trivialOfRank (r : LocallyConstant Y ℕ) (f : C(X, Y)) :
    (trivialOfRank 𝕜 r).pullback f = trivialOfRank 𝕜 (r.comap f) := (rfl)

@[simp] theorem pullback_trivial (f : C(X, Y)) (n : ℕ) :
    (trivial 𝕜 Y n).pullback f = trivial 𝕜 X n := (rfl)

/-- Induction principle assuming `(A.charts n).indexAt` is definitionally `id` for all `n`. -/
@[elab_as_elim] theorem induction_on {Y : Type*} [TopologicalSpace Y]
    {motive : FiniteRankAtlas 𝕜 Y → Prop} (A : FiniteRankAtlas 𝕜 Y)
    (h : ∀ (r : LocallyConstant Y ℕ)
      (c : ∀ n, VectorBundleCore 𝕜 {y : Y // r y = n} (Fin n → 𝕜) {y : Y // r y = n})
      (hc : ∀ n y, (c n).indexAt y = y),
      motive ⟨r, fun n =>
        { c n with
          indexAt := id
          mem_baseSet_at := fun y => by simpa only [id_eq, hc n y] using (c n).mem_baseSet_at y },
        fun _ _ => rfl⟩) : motive A := by
  rcases A with ⟨r, c, hc⟩
  suffices (⟨r, fun n =>
      { c n with
        indexAt := id
        mem_baseSet_at := fun y => by simpa only [id_eq, hc n y] using (c n).mem_baseSet_at y },
      fun _ _ => rfl⟩ : FiniteRankAtlas 𝕜 Y) = ⟨r, c, hc⟩ from this ▸ h r c hc
  congr; funext n
  exact VectorBundleCore.ext (fun _ => rfl) (fun y => (hc n y).symm) fun _ _ _ => rfl

/-- Pullback along the identity map recovers the original variable-rank atlas. -/
@[simp] theorem pullback_id (A : FiniteRankAtlas 𝕜 Y) :
    A.pullback (ContinuousMap.id Y) = A := by
  induction A using induction_on; rfl

/-- Iterated pullback of variable-rank atlases agrees strictly with composite pullback. -/
@[simp] theorem pullback_comp (A : FiniteRankAtlas 𝕜 Z) (f : C(X, Y)) (g : C(Y, Z)) :
    (A.pullback g).pullback f = A.pullback (g.comp f) := (rfl)

private theorem continuous_corePullback_iff {Y' Z' : Type*} [TopologicalSpace Y']
    [TopologicalSpace Z'] (C : FiniteRankBundleCore 𝕜 Y') (f : C(Z', Y'))
    {M : Type*} [TopologicalSpace M] (g : M → (C.pullback f).core.TotalSpace) :
    Continuous g ↔
      Continuous (fun m => (g m).proj) ∧
        Continuous (fun m => (⟨f (g m).proj, (g m).2⟩ : C.core.TotalSpace)) := by
  rw [← (C.pullbackHomeomorph f).comp_continuous_iff,
    (inducing_pullbackTotalSpaceEmbedding (Fin C.rank → 𝕜) C.core.Fiber f).continuous_iff]
  simp only [Function.comp_def, pullbackTotalSpaceEmbedding,
    FiniteRankBundleCore.pullbackHomeomorph_apply, continuous_prodMk]

private theorem continuous_corePullback_lift {Y' Z' : Type*} [TopologicalSpace Y']
    [TopologicalSpace Z'] (C : FiniteRankBundleCore 𝕜 Y') (f : C(Z', Y')) :
    Continuous (fun p : (C.pullback f).core.TotalSpace =>
      (⟨f p.proj, p.2⟩ : C.core.TotalSpace)) :=
  ((continuous_corePullback_iff C f id).1 continuous_id).2

/-- Canonical continuous total-space map from a pulled-back atlas covering `f`. -/
def pullbackLift (A : FiniteRankAtlas 𝕜 Y) (f : C(X, Y)) :
    C(TotalSpace Unit (A.pullback f).Fiber, TotalSpace Unit A.Fiber) where
  toFun p := ⟨f p.proj, p.2⟩
  continuous_toFun := by
    apply (A.continuous_mk_iff_rankStrata (f.continuous.comp (A.pullback f).continuous_proj)
      (fun p => p.2)).2 fun m => ?_
    have hm := ((A.pullback f).continuous_mk_iff_rankStrata
      (A.pullback f).continuous_proj (fun p => p.2)).1 continuous_id m
    exact ((continuous_corePullback_lift (A.stratumCore m)
      ⟨fun x : {x : X // A.rank.comap f x = m} => ⟨f x.1, x.2⟩,
        (f.continuous.comp continuous_subtype_val).subtype_mk _⟩).comp hm).congr
      fun ⟨⟨_, _⟩, hx⟩ => by cases hx; rfl

@[simp] theorem pullbackLift_mk (A : FiniteRankAtlas 𝕜 Y) (f : C(X, Y))
    (x : X) (v : (A.pullback f).Fiber x) :
    pullbackLift A f ⟨x, v⟩ = ⟨f x, v⟩ := (rfl)

/-- Pull back a morphism of variable-rank atlases along a continuous base map. -/
def pullbackMap {A D : FiniteRankAtlas 𝕜 Y} (φ : A ⟶ D) (f : C(X, Y)) :
    A.pullback f ⟶ D.pullback f where
  fiberMap x := φ.fiberMap (f x)
  continuous_totalSpaceMap := by
    apply ((D.pullback f).continuous_mk_iff_rankStrata (A.pullback f).continuous_proj _).2
    intro n
    rw [continuous_corePullback_iff (D.stratumCore n)
      ⟨fun x : {x : X // D.rank.comap f x = n} => ⟨f x.1, x.2⟩,
        (f.continuous.comp continuous_subtype_val).subtype_mk _⟩]
    have hφ := (D.continuous_mk_iff_rankStrata A.continuous_proj
      (fun q : TotalSpace Unit A.Fiber => φ.fiberMap q.proj q.2)).1 φ.continuous_totalSpaceMap n
    exact ⟨((A.pullback f).continuous_proj.comp continuous_subtype_val).subtype_mk _,
      (hφ.comp (((pullbackLift A f).continuous.comp continuous_subtype_val).subtype_mk
        fun p => p.2)).congr fun _ => rfl⟩

@[simp] theorem fiberMap_pullbackMap {A D : FiniteRankAtlas 𝕜 Y} (φ : A ⟶ D)
    (f : C(X, Y)) (x : X) :
    (pullbackMap φ f).fiberMap x = φ.fiberMap (f x) := (rfl)

@[simp] theorem pullbackMap_id (A : FiniteRankAtlas 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (𝟙 A) f = 𝟙 (A.pullback f) := hom_ext fun _ => rfl

@[simp] theorem pullbackMap_comp {A D E : FiniteRankAtlas 𝕜 Y} (φ : A ⟶ D) (ψ : D ⟶ E)
    (f : C(X, Y)) :
    pullbackMap (φ ≫ ψ) f = pullbackMap φ f ≫ pullbackMap ψ f := hom_ext fun _ => rfl

/-- Contravariant pullback functor on variable-rank bundle atlases. -/
-- Expose the object assignment so morphism types act on `A.pullback f`.
@[expose, reducible]
def pullbackFunctor (f : C(X, Y)) : FiniteRankAtlas 𝕜 Y ⥤ FiniteRankAtlas 𝕜 X where
  obj A := A.pullback f
  map φ := pullbackMap φ f

@[simp] theorem pullbackFunctor_obj (f : C(X, Y)) (A : FiniteRankAtlas 𝕜 Y) :
    (pullbackFunctor f).obj A = A.pullback f := (rfl)

@[simp] theorem pullbackFunctor_map (f : C(X, Y)) {A D : FiniteRankAtlas 𝕜 Y} (φ : A ⟶ D) :
    (pullbackFunctor f).map φ = pullbackMap φ f := (rfl)

instance (f : C(X, Y)) : (pullbackFunctor (𝕜 := 𝕜) f).Additive where
  map_add := by intros; exact hom_ext fun _ => rfl

/-- Pullback along the identity continuous map is strictly the identity functor. -/
@[simp] theorem pullbackFunctor_id :
    pullbackFunctor (𝕜 := 𝕜) (ContinuousMap.id Y) = 𝟭 (FiniteRankAtlas 𝕜 Y) :=
  Functor.hext pullback_id fun A D _ => by
    induction A using induction_on; induction D using induction_on
    exact heq_of_eq (hom_ext fun _ => rfl)

/-- Pullback of variable-rank atlases is strictly contravariant under composition. -/
@[simp] theorem pullbackFunctor_comp (f : C(X, Y)) (g : C(Y, Z)) :
    pullbackFunctor (𝕜 := 𝕜) g ⋙ pullbackFunctor f = pullbackFunctor (g.comp f) :=
  Functor.hext (fun A => pullback_comp A f g) fun _ _ _ => heq_of_eq (hom_ext fun _ => rfl)

end Pullback

section CoordinateHom

/-- Restrict the total space of `A` to a subtype of its rank-`m` stratum. -/
private def subStratumHomeomorph (A : FiniteRankAtlas 𝕜 X) (m : ℕ) (P : X → Prop)
    (hP : ∀ x, P x → A.rank x = m) :
    {p : TotalSpace Unit A.Fiber // P p.proj} ≃ₜ
      ((A.stratumCore m).pullback
        ⟨fun x : {x : X // P x} => ⟨x.1, hP x.1 x.2⟩,
          continuous_subtype_val.subtype_mk _⟩).core.TotalSpace :=
  let inc : C({x : X // P x}, {x : X // A.rank x = m}) :=
    ⟨fun x => ⟨x.1, hP x.1 x.2⟩, continuous_subtype_val.subtype_mk _⟩
  { toFun p := ⟨⟨p.1.proj, p.2⟩, fun i => p.1.2 (Fin.cast (hP p.1.proj p.2).symm i)⟩
    invFun q := ⟨⟨q.proj.1, fun i => q.2 (Fin.cast (hP q.proj.1 q.proj.2) i)⟩, q.proj.2⟩
    left_inv p := Subtype.ext <| TotalSpace.mk_inj.2 <| funext fun i => by simp
    right_inv q := TotalSpace.mk_inj.2 <| funext fun i => by simp
    continuous_toFun := by
      rw [continuous_corePullback_iff (A.stratumCore m) inc]
      have hm := (A.continuous_mk_iff_rankStrata A.continuous_proj (fun p => p.2)).1
        continuous_id m
      exact ⟨(A.continuous_proj.comp continuous_subtype_val).subtype_mk _,
        (hm.comp (continuous_subtype_val.subtype_mk fun p => hP p.1.proj p.2)).congr fun _ => rfl⟩
    continuous_invFun := by
      refine Continuous.subtype_mk ?_ _
      exact (A.totalSpaceHomeomorph.continuous.comp
        (continuous_sigmaMk.comp (continuous_corePullback_lift (A.stratumCore m) inc))).congr
        fun _ => by simp only [Function.comp_apply, totalSpaceHomeomorph_apply]; rfl }

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
def jointSourceHomeomorph :
    {p : TotalSpace Unit A.Fiber // A.rank p.proj = m ∧ D.rank p.proj = n} ≃ₜ
      (A.jointSourceCore D m n).core.TotalSpace :=
  subStratumHomeomorph A m (fun x => A.rank x = m ∧ D.rank x = n) fun _ h => h.1

@[simp] theorem jointSourceHomeomorph_apply
    (p : {p : TotalSpace Unit A.Fiber // A.rank p.proj = m ∧ D.rank p.proj = n}) :
    jointSourceHomeomorph A D m n p =
      ⟨⟨p.1.proj, p.2⟩, fun i => p.1.2 (Fin.cast p.2.1.symm i)⟩ := (rfl)

@[simp] theorem jointSourceHomeomorph_symm_apply (q : (A.jointSourceCore D m n).core.TotalSpace) :
    (jointSourceHomeomorph A D m n).symm q =
      ⟨⟨q.proj.1, fun i => q.2 (Fin.cast q.proj.2.1 i)⟩, q.proj.2⟩ := (rfl)

/-- Homeomorphism of the part of `TotalSpace Unit D.Fiber` over `JointStratum A D m n` with the
total space of `A.jointTargetCore D m n`. -/
def jointTargetHomeomorph :
    {p : TotalSpace Unit D.Fiber // A.rank p.proj = m ∧ D.rank p.proj = n} ≃ₜ
      (A.jointTargetCore D m n).core.TotalSpace :=
  subStratumHomeomorph D n (fun x => A.rank x = m ∧ D.rank x = n) fun _ h => h.2

@[simp] theorem jointTargetHomeomorph_apply
    (p : {p : TotalSpace Unit D.Fiber // A.rank p.proj = m ∧ D.rank p.proj = n}) :
    jointTargetHomeomorph A D m n p =
      ⟨⟨p.1.proj, p.2⟩, fun i => p.1.2 (Fin.cast p.2.2.symm i)⟩ := (rfl)

@[simp] theorem jointTargetHomeomorph_symm_apply (q : (A.jointTargetCore D m n).core.TotalSpace) :
    (jointTargetHomeomorph A D m n).symm q =
      ⟨⟨q.proj.1, fun i => q.2 (Fin.cast q.proj.2.2 i)⟩, q.proj.2⟩ := (rfl)

/-- Symmetry of joint rank strata identifies `JointStratum D A n m` with `JointStratum A D m n`. -/
-- Expose the continuous map so pulled-back coordinate morphisms reduce on fibres.
@[expose] def jointSwap : C(JointStratum D A n m, JointStratum A D m n) :=
  ⟨fun x => ⟨x.1, x.2.2, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

end JointStrata

/-- Glue coordinate morphisms on all joint rank strata into a variable-rank atlas morphism. -/
def ofCoordinateHoms {A D : FiniteRankAtlas 𝕜 X}
    (a : ∀ m n : ℕ, A.jointSourceCore D m n ⟶ A.jointTargetCore D m n) : A ⟶ D where
  fiberMap x := ((a (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩).toLinearMap
  continuous_totalSpaceMap := by
    apply continuous_of_cover_nhds (s := fun mn : ℕ × ℕ =>
      {p : TotalSpace Unit A.Fiber | A.rank p.proj = mn.1 ∧ D.rank p.proj = mn.2})
    · intro p
      exact ⟨(A.rank p.proj, D.rank p.proj),
        (((A.rank.isLocallyConstant.isOpen_fiber _).inter
          (D.rank.isLocallyConstant.isOpen_fiber _)).preimage A.continuous_proj).mem_nhds
          ⟨rfl, rfl⟩⟩
    · rintro ⟨m, n⟩
      rw [continuousOn_iff_continuous_domRestrict]
      refine (continuous_subtype_val.comp <| (jointTargetHomeomorph A D m n).symm.continuous.comp <|
        (a m n).continuous_totalSpaceMap.comp (jointSourceHomeomorph A D m n).continuous).congr ?_
      rintro ⟨⟨x, v⟩, hm, hn⟩; cases hm; cases hn
      simp only [Function.comp_apply, Set.domRestrict_apply, jointSourceHomeomorph_apply,
        CoordinateHom.totalSpaceMap_def, jointTargetHomeomorph_symm_apply, Fin.cast_refl]
      rfl

@[simp] theorem fiberMap_ofCoordinateHoms {A D : FiniteRankAtlas 𝕜 X}
    (a : ∀ m n : ℕ, A.jointSourceCore D m n ⟶ A.jointTargetCore D m n) (x : X) :
    (ofCoordinateHoms a).fiberMap x =
      ((a (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩).toLinearMap := (rfl)

section Complete

variable [CompleteSpace 𝕜]

/-- Extract the coordinate morphism on the `(m, n)` joint rank stratum from an atlas morphism. -/
def toCoordinateHom {A D : FiniteRankAtlas 𝕜 X} (f : A ⟶ D) (m n : ℕ) :
    A.jointSourceCore D m n ⟶ A.jointTargetCore D m n :=
  let lin (x : JointStratum A D m n) : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜) :=
    ((LinearEquiv.funCongrLeft 𝕜 𝕜 (Fin.castOrderIso x.2.2.symm).toEquiv).toLinearMap.comp
      ((f.fiberMap x.1).comp
        (LinearEquiv.funCongrLeft 𝕜 𝕜 (Fin.castOrderIso x.2.1).toEquiv).toLinearMap))
      |>.toContinuousLinearMap
  CoordinateHom.ofContinuous lin <|
    (continuous_hom_bundle_iff (E₁ := (A.jointSourceCore D m n).core.Fiber)
      (E₂ := (A.jointTargetCore D m n).core.Fiber) lin).2 <| by
      refine ((jointTargetHomeomorph A D m n).continuous.comp <|
        ((f.continuous_totalSpaceMap.comp continuous_subtype_val).subtype_mk fun p => p.2).comp
          (jointSourceHomeomorph A D m n).symm.continuous).congr ?_
      rintro ⟨⟨x, hm, hn⟩, v⟩; cases hm; cases hn
      simp only [Function.comp_apply, jointTargetHomeomorph_apply, lin]
      rfl

@[simp] theorem fiberMap_toCoordinateHom_self {A D : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ D) (x : X) (v : A.Fiber x) :
    (toCoordinateHom f (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩ v = f.fiberMap x v := by
  dsimp only [toCoordinateHom]; rw [CoordinateHom.fiberMap_ofContinuous]; rfl

/-- Over a complete scalar field, atlas morphisms correspond additively to coordinate morphisms on
the clopen joint rank strata. -/
def coordinateHomEquiv (A D : FiniteRankAtlas 𝕜 X) :
    (A ⟶ D) ≃+ ∀ m n : ℕ, (A.jointSourceCore D m n ⟶ A.jointTargetCore D m n) where
  toFun f m n := toCoordinateHom f m n
  invFun := ofCoordinateHoms
  left_inv f := hom_ext fun x => LinearMap.ext (fiberMap_toCoordinateHom_self f x)
  right_inv a := by
    funext m n; apply FiniteRankBundleCore.hom_ext
    rintro ⟨x, hm, hn⟩; cases hm; cases hn
    exact ContinuousLinearMap.ext (fiberMap_toCoordinateHom_self (ofCoordinateHoms a) x)
  map_add' f g := by
    funext m n; apply FiniteRankBundleCore.hom_ext
    rintro ⟨x, hm, hn⟩; cases hm; cases hn
    exact ContinuousLinearMap.ext fun v => by simp [fiberMap_toCoordinateHom_self]

/-- Over a complete scalar field, an atlas morphism is an isomorphism iff bijective on fibres. -/
theorem isIso_iff_bijective {A D : FiniteRankAtlas 𝕜 X} (f : A ⟶ D) :
    IsIso f ↔ ∀ x : X, Function.Bijective (f.fiberMap x) := by
  refine ⟨fun hf x => ((fiberFunctor (𝕜 := 𝕜) x).mapIso (asIso f)).toLinearEquiv.bijective,
    fun hbij => ?_⟩
  have hiso (m n : ℕ) : IsIso (toCoordinateHom f m n) := by
    rw [FiniteRankBundleCore.isIso_iff_bijective]
    rintro ⟨x, hm, hn⟩; cases hm; cases hn
    simpa [funext (fiberMap_toCoordinateHom_self f x)] using hbij x
  let g : D ⟶ A := ofCoordinateHoms fun n m =>
    FiniteRankBundleCore.pullbackMap (inv (toCoordinateHom f m n)) (jointSwap A D m n)
  have hg (x : X) (v : D.Fiber x) :
      g.fiberMap x v = (inv (toCoordinateHom f (A.rank x) (D.rank x))).fiberMap ⟨x, rfl, rfl⟩ v :=
    congrArg (· v) (FiniteRankBundleCore.fiberMap_pullbackMap
      (inv (toCoordinateHom f (A.rank x) (D.rank x)))
      (jointSwap A D (A.rank x) (D.rank x)) ⟨x, rfl, rfl⟩)
  refine ⟨g, hom_ext fun x => LinearMap.ext fun v => ?_, hom_ext fun x => LinearMap.ext fun v => ?_⟩
  · have h := congrArg (fun k => k.fiberMap ⟨x, rfl, rfl⟩ v)
      (IsIso.hom_inv_id (toCoordinateHom f (A.rank x) (D.rank x)))
    simp only [FiniteRankBundleCore.fiberMap_comp, FiniteRankBundleCore.fiberMap_id,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      fiberMap_toCoordinateHom_self] at h
    exact (hg x (f.fiberMap x v)).trans h
  · have h := congrArg (fun k => k.fiberMap ⟨x, rfl, rfl⟩ v)
      (IsIso.inv_hom_id (toCoordinateHom f (A.rank x) (D.rank x)))
    simp only [FiniteRankBundleCore.fiberMap_comp, FiniteRankBundleCore.fiberMap_id,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      fiberMap_toCoordinateHom_self] at h
    exact (congrArg (f.fiberMap x) (hg x v)).trans h

end Complete

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
      cases h
      exact congrArg
        (fun Z : VectorBundleCore 𝕜 {x : X // LocallyConstant.const X C.rank x = C.rank}
          (Fin C.rank → 𝕜) {x : X // LocallyConstant.const X C.rank x = C.rank} => Z.indexAt x)
        (dite_eq_left_iff.2 fun h' => (h' rfl).elim)
    else
      congrArg
        (fun Z : VectorBundleCore 𝕜 {x : X // LocallyConstant.const X C.rank x = m}
          (Fin m → 𝕜) {x : X // LocallyConstant.const X C.rank x = m} => Z.indexAt x)
        (dite_eq_right_iff.2 fun h' => (h h').elim)

@[simp] theorem rank_ofCoreObj (C : FiniteRankBundleCore 𝕜 X) :
    (ofCoreObj C).rank = LocallyConstant.const X C.rank := (rfl)

@[simp] theorem charts_ofCoreObj_self (C : FiniteRankBundleCore 𝕜 X) :
    (ofCoreObj C).charts C.rank =
      (C.pullback ⟨Subtype.val, continuous_subtype_val⟩).core :=
  dite_eq_left_iff.2 fun h => (h rfl).elim

/-- Homeomorphism between `C.core.TotalSpace` and `TotalSpace Unit (ofCoreObj C).Fiber`. -/
def ofCoreHomeomorph (C : FiniteRankBundleCore 𝕜 X) :
    C.core.TotalSpace ≃ₜ TotalSpace Unit (ofCoreObj C).Fiber where
  toFun p := ⟨p.proj, p.2⟩
  invFun p := ⟨p.proj, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply ((ofCoreObj C).continuous_mk_iff_rankStrata C.core.continuous_proj
      (fun p : C.core.TotalSpace => p.2)).2 fun m => ?_
    by_cases hm : C.rank = m
    · subst hm
      let inc : C({x : X // LocallyConstant.const X C.rank x = C.rank}, X) :=
        ⟨Subtype.val, continuous_subtype_val⟩
      have hcont : Continuous fun y :
          {y : C.core.TotalSpace // (ofCoreObj C).rank y.proj = C.rank} =>
          (⟨⟨y.1.proj, y.2⟩, y.1.2⟩ : (C.pullback inc).core.TotalSpace) := by
        rw [continuous_corePullback_iff C inc]
        exact ⟨(C.core.continuous_proj.comp continuous_subtype_val).subtype_mk fun y => y.2,
          continuous_subtype_val⟩
      exact (charts_ofCoreObj_self C ▸ hcont).congr fun _ => rfl
    · have : IsEmpty {p : C.core.TotalSpace // (ofCoreObj C).rank p.proj = m} :=
        ⟨fun p => hm ((congrFun (LocallyConstant.coe_const C.rank) p.1.proj).symm.trans p.2)⟩
      exact continuous_of_discreteTopology
  continuous_invFun := by
    have hglued : Continuous fun q : (ofCoreObj C).GluedTotalSpace =>
        (⟨q.2.proj.1, fun i => q.2.2 (Fin.cast
          ((congrFun (LocallyConstant.coe_const C.rank) q.2.proj.1).symm.trans q.2.proj.2) i)⟩ :
          C.core.TotalSpace) := by
      refine continuous_sigma fun m => ?_
      by_cases hm : C.rank = m
      · subst hm
        exact (charts_ofCoreObj_self C ▸
          continuous_corePullback_lift C ⟨Subtype.val, continuous_subtype_val⟩).congr fun _ => rfl
      · have : IsEmpty (((ofCoreObj C).charts m).TotalSpace) :=
          ⟨fun p => hm ((congrFun (LocallyConstant.coe_const C.rank) p.proj.1).symm.trans p.proj.2)⟩
        exact continuous_of_discreteTopology
    refine (hglued.comp (ofCoreObj C).totalSpaceHomeomorph.symm.continuous).congr fun p => ?_
    dsimp only [Function.comp_apply]
    rw [totalSpaceHomeomorph_symm_apply]; rfl

@[simp] theorem ofCoreHomeomorph_apply (C : FiniteRankBundleCore 𝕜 X) (p : C.core.TotalSpace) :
    ofCoreHomeomorph C p = ⟨p.proj, p.2⟩ := (rfl)

@[simp] theorem ofCoreHomeomorph_symm_apply (C : FiniteRankBundleCore 𝕜 X)
    (p : TotalSpace Unit (ofCoreObj C).Fiber) :
    (ofCoreHomeomorph C).symm p = ⟨p.proj, p.2⟩ := (rfl)

variable (𝕜 X) in
/-- The embedding of constant-rank point-indexed cores into variable-rank bundle atlases. -/
-- Expose the object assignment so morphism types reduce to `ofCoreObj`.
@[expose, reducible]
def ofCore : FiniteRankBundleCore 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj := ofCoreObj
  map {C D} f :=
    { fiberMap x := (f.fiberMap x).toLinearMap
      continuous_totalSpaceMap := ((ofCoreHomeomorph D).continuous.comp <|
        f.continuous_totalSpaceMap.comp (ofCoreHomeomorph C).symm.continuous).congr fun p => by
        simp only [Function.comp_apply, ofCoreHomeomorph_symm_apply,
          CoordinateHom.totalSpaceMap_def, ofCoreHomeomorph_apply]; rfl }
  map_id _ := hom_ext fun _ => LinearMap.ext fun _ => by
    simp only [FiniteRankBundleCore.fiberMap_id]; rfl
  map_comp _ _ := hom_ext fun _ => LinearMap.ext fun _ => by
    simp only [FiniteRankBundleCore.fiberMap_comp]; rfl

@[simp] theorem ofCore_obj (C : FiniteRankBundleCore 𝕜 X) :
    (ofCore 𝕜 X).obj C = ofCoreObj C := (rfl)

@[simp] theorem fiberMap_ofCore_map {C D : FiniteRankBundleCore 𝕜 X} (f : C ⟶ D) (x : X) :
    ((ofCore 𝕜 X).map f).fiberMap x = (f.fiberMap x).toLinearMap := (rfl)

instance : (ofCore 𝕜 X).Additive where
  map_add := by
    intros; exact hom_ext fun _ => LinearMap.ext fun _ => by
      simp only [FiniteRankBundleCore.fiberMap_add]; rfl

instance : (ofCore 𝕜 X).Faithful where
  map_injective {C D _ _} h := FiniteRankBundleCore.hom_ext fun x => ContinuousLinearMap.ext
    fun v => congrArg (fun φ : ofCoreObj C ⟶ ofCoreObj D => φ.fiberMap x v) h

instance [CompleteSpace 𝕜] : (ofCore 𝕜 X).Full where
  map_surjective {C D} φ := by
    let g (x : X) : (Fin C.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜) :=
      (φ.fiberMap x).toContinuousLinearMap
    have hg := (continuous_hom_bundle_iff (E₁ := C.core.Fiber) (E₂ := D.core.Fiber) g).2 <|
      ((ofCoreHomeomorph D).symm.continuous.comp <|
        φ.continuous_totalSpaceMap.comp (ofCoreHomeomorph C).continuous).congr fun p => by
        simp only [Function.comp_apply, ofCoreHomeomorph_symm_apply]; rfl
    exact ⟨CoordinateHom.ofContinuous g hg, hom_ext fun x => LinearMap.ext fun v =>
      congrArg (fun S : (Fin C.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜) => S v)
        (congrFun (CoordinateHom.fiberMap_ofContinuous g hg) x)⟩

/-- Pulling back the `n`th stratum core of a constant-rank-`n` atlas recovers it up to iso. -/
def ofCorePullbackIso (A : FiniteRankAtlas 𝕜 X) (n : ℕ) (hn : ∀ x, A.rank x = n) :
    (ofCore 𝕜 X).obj ((A.stratumCore n).pullback ⟨fun x => ⟨x, hn x⟩,
      continuous_id.subtype_mk hn⟩) ≅ A := by
  let s : C(X, {x : X // A.rank x = n}) := ⟨fun x => ⟨x, hn x⟩, continuous_id.subtype_mk hn⟩
  let C := (A.stratumCore n).pullback s
  let e (x : X) : ((ofCore 𝕜 X).obj C).Fiber x ≃ₗ[𝕜] A.Fiber x :=
    LinearEquiv.funCongrLeft 𝕜 𝕜
      (finCongr ((hn x).trans (congrFun (LocallyConstant.coe_const C.rank) x).symm))
  refine isoMk e ?_ ?_
  · apply (A.continuous_mk_iff_rankStrata (ofCoreObj C).continuous_proj
      (fun p : TotalSpace Unit ((ofCore 𝕜 X).obj C).Fiber => e p.proj p.2)).2 fun m => ?_
    by_cases hm : n = m
    · subst hm
      exact (((continuous_corePullback_lift (A.stratumCore n) s).comp
        (ofCoreHomeomorph C).symm.continuous).comp continuous_subtype_val).congr fun ⟨⟨_, _⟩, _⟩ =>
        by dsimp only [Function.comp_apply, e]; rw [ofCoreHomeomorph_symm_apply]; congr 1
    · have : IsEmpty {p : TotalSpace Unit ((ofCore 𝕜 X).obj C).Fiber // A.rank p.proj = m} :=
        ⟨fun p => hm ((hn p.1.proj).symm.trans p.2)⟩
      exact continuous_of_discreteTopology
  · have hcore : Continuous fun p : TotalSpace Unit A.Fiber =>
        (⟨p.proj, (e p.proj).symm p.2⟩ : C.core.TotalSpace) := by
      rw [continuous_corePullback_iff (A.stratumCore n) s]
      exact ⟨A.continuous_proj, (((A.continuous_mk_iff_rankStrata A.continuous_proj
        (fun p => p.2)).1 continuous_id n).comp
        (continuous_id.subtype_mk fun p => hn p.proj)).congr fun ⟨_, _⟩ => by
        dsimp only [Function.comp_apply, id_eq, e]; congr 1⟩
    exact ((ofCoreHomeomorph C).continuous.comp hcore).congr fun p => by
      dsimp only [Function.comp_apply]; rw [ofCoreHomeomorph_apply]

/-- An atlas lies in the essential image of `ofCore` iff its rank takes at most one value. -/
theorem exists_ofCore_iso_iff (A : FiniteRankAtlas 𝕜 X) :
    (∃ C : FiniteRankBundleCore 𝕜 X, Nonempty ((ofCore 𝕜 X).obj C ≅ A)) ↔
      (Set.range A.rank).Subsingleton := by
  constructor
  · rintro ⟨C, ⟨e⟩⟩ _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have hr := e.finiteRankAtlas_rank_eq
    have hx : C.rank = A.rank x := (congrFun (LocallyConstant.coe_const C.rank) x).symm.trans
      (congrArg (fun r : LocallyConstant X ℕ => r x) hr)
    have hy : C.rank = A.rank y := (congrFun (LocallyConstant.coe_const C.rank) y).symm.trans
      (congrArg (fun r : LocallyConstant X ℕ => r y) hr)
    exact hx.symm.trans hy
  · intro hsub
    rcases isEmpty_or_nonempty X with hX | hX
    · have : IsEmpty (TotalSpace Unit ((ofCore 𝕜 X).obj
          (FiniteRankBundleCore.trivial 𝕜 X 0)).Fiber) := ⟨fun p => isEmptyElim p.proj⟩
      have : IsEmpty (TotalSpace Unit A.Fiber) := ⟨fun p => isEmptyElim p.proj⟩
      exact ⟨FiniteRankBundleCore.trivial 𝕜 X 0,
        ⟨isoMk isEmptyElim continuous_of_discreteTopology continuous_of_discreteTopology⟩⟩
    · let x₀ := hX.some
      exact ⟨_, ⟨ofCorePullbackIso A (A.rank x₀) fun x => hsub ⟨x, rfl⟩ ⟨x₀, rfl⟩⟩⟩

/-- Over a preconnected space, every variable-rank atlas is in the essential image of `ofCore`. -/
instance [PreconnectedSpace X] : (ofCore 𝕜 X).EssSurj where
  mem_essImage A :=
    (exists_ofCore_iso_iff A).2 fun _ ⟨x, hx⟩ _ ⟨y, hy⟩ =>
      hx ▸ hy ▸ A.rank.apply_eq_of_preconnectedSpace x y

instance [PreconnectedSpace X] [CompleteSpace 𝕜] : (ofCore 𝕜 X).IsEquivalence where

end FixedRankComparison

section Small

instance [Small.{u} 𝕜] : LocallySmall.{u} (FiniteRankAtlas 𝕜 X) where
  hom_small A D :=
    small_of_injective
      (f := fun (φ : A ⟶ D) (x : X) (v : Fin (A.rank x) → 𝕜) => φ.fiberMap x v)
      fun _ _ h => hom_ext fun x => LinearMap.ext (congrFun (congrFun h x))

instance [Small.{u} 𝕜] : Small.{u} (FiniteRankAtlas 𝕜 X) := by
  let code (A : FiniteRankAtlas 𝕜 X) :
      Σ r : LocallyConstant X ℕ, ∀ n : ℕ,
        ({x : X // r x = n} → Set {x : X // r x = n}) ×
        ({x : X // r x = n} → {x : X // r x = n} → {x : X // r x = n} →
          (Fin n → Shrink.{u} 𝕜) → (Fin n → Shrink.{u} 𝕜)) :=
    ⟨A.rank, fun n => ((A.charts n).baseSet, fun b c x v i =>
      equivShrink.{u} 𝕜 ((A.charts n).coordChange b c x
        (fun j => (equivShrink.{u} 𝕜).symm (v j)) i))⟩
  refine small_of_injective (f := code) fun ⟨r₁, c₁, h₁⟩ ⟨r₂, c₂, h₂⟩ h => ?_
  obtain rfl : r₁ = r₂ := congrArg Sigma.fst h
  have hc := eq_of_heq (Sigma.mk.inj h).2
  congr; funext n
  have hcn := congrFun hc n
  dsimp only [code] at hcn
  refine VectorBundleCore.ext (congrFun (congrArg Prod.fst hcn))
    (fun x => (h₁ n x).trans (h₂ n x).symm) fun b c x => ContinuousLinearMap.ext fun v =>
      funext fun j => ?_
  simpa only [Equiv.symm_apply_apply] using (equivShrink.{u} 𝕜).injective <| congrFun
    (congrFun (congrFun (congrFun (congrFun (congrArg Prod.snd hcn) b) c) x)
      (fun k => equivShrink.{u} 𝕜 (v k))) j

/-- Whenever `[Small.{u} 𝕜]`, `FiniteRankAtlas 𝕜 X` is essentially small in `Type u`. -/
instance [Small.{u} 𝕜] : EssentiallySmall.{u} (FiniteRankAtlas 𝕜 X) :=
  essentiallySmall_of_small_of_locallySmall (FiniteRankAtlas 𝕜 X)

end Small

end TauCeti.FiniteRankAtlas

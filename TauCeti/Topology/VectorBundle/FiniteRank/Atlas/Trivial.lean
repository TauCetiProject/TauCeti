/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Variable-rank trivial atlases and zero objects

`TauCeti.FiniteRankAtlas.trivial 𝕜 r` constructs the variable-rank trivial atlas with locally
constant fibre dimension `r : LocallyConstant X ℕ`, using `TauCeti.FiniteRankBundleCore.trivial`
on each clopen rank stratum. A map into its reconstructed total space is continuous precisely when
its base projection is continuous and its coordinate vectors are continuous on each rank stratum
(`continuous_trivial_iff`). When the rank along the base projection is constantly `n`, continuity
reduces to continuity of the base map and the `Fin n → 𝕜` coordinate vector
(`continuous_mk_trivial_iff_of_rank_eq`, `continuous_trivial_iff_of_rank_eq`), and when `r` takes
constant value `n` on `X` the reconstructed total space is homeomorphic to `X × (Fin n → 𝕜)`
(`trivialHomeomorphOfRankEq`, `trivialConstHomeomorph`).

An object of `FiniteRankAtlas 𝕜 X` is a categorical zero object if and only if its locally
constant rank vanishes identically (`isZero_iff_rank_eq_zero`). In particular,
`trivial 𝕜 (0 : LocallyConstant X ℕ)` supplies `HasZeroObject (FiniteRankAtlas 𝕜 X)`, and over an
empty base every atlas is a zero object (`isZero_of_isEmpty`).

## References

* M. F. Atiyah, *K-Theory*, §1.1.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits ZeroObject

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

variable (𝕜) in
/-- The variable-rank trivial atlas with locally constant fibre dimension `r`. -/
-- Expose the rank projection so `(trivial 𝕜 r).Fiber x` reduces to `Fin (r x) → 𝕜`.
@[expose] def trivial (r : LocallyConstant X ℕ) : FiniteRankAtlas 𝕜 X where
  rank := r
  charts n := (FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n).core
  indexAt_eq n := (FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n).indexAt_eq

@[simp] theorem rank_trivial (r : LocallyConstant X ℕ) : (trivial 𝕜 r).rank = r := (rfl)

@[simp] theorem charts_trivial (r : LocallyConstant X ℕ) (n : ℕ) :
    (trivial 𝕜 r).charts n = (FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n).core := (rfl)

@[simp] theorem localTriv_baseSet_trivial (r : LocallyConstant X ℕ) (n : ℕ)
    (x : {x : X // r x = n}) :
    (((trivial 𝕜 r).charts n).localTriv x).baseSet = Set.univ := (rfl)

/-- The preferred chart domain at `z` of a trivial variable-rank atlas is the entire rank fiber of
`z`. -/
@[simp] theorem chartBaseSet_trivial (r : LocallyConstant X ℕ) (z : X) :
    (trivial 𝕜 r).chartBaseSet z = {x : X | r x = r z} := by
  ext x
  simp [mem_chartBaseSet_iff, trivial]

/-- A map into the reconstructed total space of `trivial 𝕜 r` is continuous if and only if its
base projection is continuous and its coordinate vectors are continuous on each rank stratum. -/
theorem continuous_trivial_iff {Y : Type*} [TopologicalSpace Y] {r : LocallyConstant X ℕ}
    {f : Y → TotalSpace Unit (trivial 𝕜 r).Fiber} :
    Continuous f ↔
      Continuous (fun y => (f y).proj) ∧
        ∀ n : ℕ, Continuous (fun y : {y : Y // r (f y).proj = n} =>
          (fun i => (f y.1).2 (Fin.cast y.2.symm i) : Fin n → 𝕜)) := by
  constructor
  · intro hf
    have hb : Continuous fun y => (f y).proj := (trivial 𝕜 r).continuous_proj.comp hf
    refine ⟨hb, fun n => ?_⟩
    have hn := ((trivial 𝕜 r).continuous_mk_iff_rankStrata hb (fun y => (f y).2)).1 hf n
    exact (FiniteRankBundleCore.continuous_trivial_iff.1 hn).2
  · rintro ⟨hb, hs⟩
    exact ((trivial 𝕜 r).continuous_mk_iff_rankStrata hb (fun y => (f y).2)).2 fun n =>
      FiniteRankBundleCore.continuous_trivial_iff.2
        ⟨(hb.comp continuous_subtype_val).subtype_mk _, hs n⟩

/-- Assembling a map into `TotalSpace Unit (trivial 𝕜 r).Fiber` whose base points all have rank `n`
is continuous if and only if both the base map and the `Fin n → 𝕜` coordinate map are continuous. -/
theorem continuous_mk_trivial_iff_of_rank_eq {Y : Type*} [TopologicalSpace Y]
    {r : LocallyConstant X ℕ} {n : ℕ} {b : Y → X} {v : Y → Fin n → 𝕜}
    (hr : ∀ y, r (b y) = n) :
    Continuous (fun y =>
      (⟨b y, fun i => v y (Fin.cast (hr y) i)⟩ : TotalSpace Unit (trivial 𝕜 r).Fiber)) ↔
      Continuous b ∧ Continuous v := by
  rw [continuous_trivial_iff]
  refine and_congr_right fun _ => ⟨fun hs => ?_, fun hv m => ?_⟩
  · exact ((hs n).comp (continuous_id.subtype_mk hr)).congr fun y =>
      funext fun _ => congrArg (v y) (Fin.ext rfl)
  · by_cases hnm : n = m
    · subst hnm
      exact (hv.comp continuous_subtype_val).congr fun y =>
        funext fun _ => congrArg (v y.1) (Fin.ext rfl)
    · exact continuous_iff_continuousAt.2 fun y => False.elim (hnm ((hr y.1).symm.trans y.2))

/-- A map into `TotalSpace Unit (trivial 𝕜 r).Fiber` whose base projection has constant rank `n`
is continuous if and only if both its base point and its `Fin n → 𝕜` coordinate vector are
continuous. -/
theorem continuous_trivial_iff_of_rank_eq {Y : Type*} [TopologicalSpace Y]
    {r : LocallyConstant X ℕ} {n : ℕ} {f : Y → TotalSpace Unit (trivial 𝕜 r).Fiber}
    (hr : ∀ y, r (f y).proj = n) :
    Continuous f ↔
      Continuous (fun y => (f y).proj) ∧
        Continuous (fun y (i : Fin n) => (f y).2 (Fin.cast (hr y).symm i)) := by
  have hf : f = fun y => ⟨(f y).proj, fun i =>
      (fun y (j : Fin n) => (f y).2 (Fin.cast (hr y).symm j)) y (Fin.cast (hr y) i)⟩ :=
    funext fun y =>
      congrArg (TotalSpace.mk' Unit (f y).proj) (funext fun _ => congrArg (f y).2 (Fin.ext rfl))
  exact (congrArg Continuous hf).to_iff.trans
    (continuous_mk_trivial_iff_of_rank_eq (b := fun y => (f y).proj)
      (v := fun y (i : Fin n) => (f y).2 (Fin.cast (hr y).symm i)) hr)

/-- A map into the reconstructed total space of a constant-rank trivial atlas is continuous if and
only if both its base point and its coordinate vector in `Fin n → 𝕜` are continuous. -/
theorem continuous_trivial_const_iff {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    {f : Y → TotalSpace Unit (trivial 𝕜 (.const X n)).Fiber} :
    Continuous f ↔
      Continuous (fun y => (f y).proj) ∧ Continuous (fun y (i : Fin n) => (f y).2 i) :=
  continuous_trivial_iff_of_rank_eq (f := f) fun _ => rfl

variable (𝕜) in
/-- When `r : LocallyConstant X ℕ` takes the constant value `n` everywhere, the reconstructed total
space of `trivial 𝕜 r` is homeomorphic to `X × (Fin n → 𝕜)`. -/
def trivialHomeomorphOfRankEq {r : LocallyConstant X ℕ} {n : ℕ} (hr : ∀ x, r x = n) :
    TotalSpace Unit (trivial 𝕜 r).Fiber ≃ₜ X × (Fin n → 𝕜) where
  toFun p := (p.proj, fun i => p.2 (Fin.cast (hr p.proj).symm i))
  invFun q := ⟨q.1, fun i => q.2 (Fin.cast (hr q.1) i)⟩
  left_inv p := by
    rcases p with ⟨x, v⟩
    exact congrArg (TotalSpace.mk' Unit x) (funext fun _ => congrArg v (Fin.ext rfl))
  right_inv q := by
    rcases q with ⟨x, v⟩
    exact Prod.ext rfl (funext fun _ => congrArg v (Fin.ext rfl))
  continuous_toFun :=
    ((continuous_trivial_iff_of_rank_eq fun p => hr p.proj).1 continuous_id).1.prodMk
      ((continuous_trivial_iff_of_rank_eq fun p => hr p.proj).1 continuous_id).2
  continuous_invFun :=
    (continuous_mk_trivial_iff_of_rank_eq fun q : X × (Fin n → 𝕜) => hr q.1).2
      ⟨continuous_fst, continuous_snd⟩

@[simp] theorem trivialHomeomorphOfRankEq_apply {r : LocallyConstant X ℕ} {n : ℕ}
    (hr : ∀ x, r x = n) (p : TotalSpace Unit (trivial 𝕜 r).Fiber) :
    trivialHomeomorphOfRankEq 𝕜 hr p =
      (p.proj, fun i => p.2 (Fin.cast (hr p.proj).symm i)) := (rfl)

@[simp] theorem trivialHomeomorphOfRankEq_symm_apply {r : LocallyConstant X ℕ} {n : ℕ}
    (hr : ∀ x, r x = n) (q : X × (Fin n → 𝕜)) :
    (trivialHomeomorphOfRankEq 𝕜 hr).symm q =
      ⟨q.1, fun i => q.2 (Fin.cast (hr q.1) i)⟩ := (rfl)

variable (𝕜 X) in
/-- For constant rank `n`, the reconstructed total space of `trivial 𝕜 (.const X n)` is
homeomorphic to `X × (Fin n → 𝕜)`. -/
def trivialConstHomeomorph (n : ℕ) :
    TotalSpace Unit (trivial 𝕜 (.const X n)).Fiber ≃ₜ X × (Fin n → 𝕜) :=
  trivialHomeomorphOfRankEq 𝕜 fun _ => rfl

@[simp] theorem trivialConstHomeomorph_apply (n : ℕ)
    (p : TotalSpace Unit (trivial 𝕜 (.const X n)).Fiber) :
    trivialConstHomeomorph 𝕜 X n p = (p.proj, p.2) := (rfl)

@[simp] theorem trivialConstHomeomorph_symm_apply (n : ℕ) (q : X × (Fin n → 𝕜)) :
    (trivialConstHomeomorph 𝕜 X n).symm q = ⟨q.1, q.2⟩ := (rfl)

/-- Any atlas whose locally constant rank is identically zero is a zero object. -/
theorem isZero_of_rank_eq_zero {A : FiniteRankAtlas 𝕜 X} (h : A.rank = 0) : IsZero A :=
  (IsZero.iff_id_eq_zero A).2 <| hom_ext fun x => LinearMap.ext fun _ =>
    funext fun i => (Fin.cast (DFunLike.congr_fun h x) i).elim0

/-- The trivial rank-zero atlas is a zero object. -/
theorem isZero_trivial_zero : IsZero (trivial 𝕜 (0 : LocallyConstant X ℕ)) :=
  isZero_of_rank_eq_zero (rank_trivial 0)

/-- Every zero object in `FiniteRankAtlas 𝕜 X` has identically zero locally constant rank. -/
theorem rank_eq_zero_of_isZero {A : FiniteRankAtlas 𝕜 X} (hA : IsZero A) : A.rank = 0 :=
  (hA.iso isZero_trivial_zero).finiteRankAtlas_rank_eq.trans (rank_trivial 0)

/-- An atlas in `FiniteRankAtlas 𝕜 X` is a categorical zero object if and only if its locally
constant rank is `0`. -/
theorem isZero_iff_rank_eq_zero (A : FiniteRankAtlas 𝕜 X) : IsZero A ↔ A.rank = 0 :=
  ⟨rank_eq_zero_of_isZero, isZero_of_rank_eq_zero⟩

/-- `trivial 𝕜 (0 : LocallyConstant X ℕ)` provides a zero object for `FiniteRankAtlas 𝕜 X`. -/
instance : HasZeroObject (FiniteRankAtlas 𝕜 X) :=
  ⟨⟨trivial 𝕜 (0 : LocallyConstant X ℕ), isZero_trivial_zero⟩⟩

/-- The categorical zero object of `FiniteRankAtlas 𝕜 X` has rank `0`. -/
@[simp] theorem rank_zero : (0 : FiniteRankAtlas 𝕜 X).rank = 0 :=
  rank_eq_zero_of_isZero (Limits.isZero_zero _)

/-- Over an empty base space, every variable-rank atlas is a zero object. -/
theorem isZero_of_isEmpty [IsEmpty X] (A : FiniteRankAtlas 𝕜 X) : IsZero A :=
  isZero_of_rank_eq_zero (LocallyConstant.ext isEmptyElim)

end TauCeti.FiniteRankAtlas

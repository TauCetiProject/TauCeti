/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Trivial variable-rank bundle atlases and categorical zero objects

Given a locally constant rank function `r : LocallyConstant X ℕ`, `FiniteRankAtlas.trivial 𝕜 X r`
places the constant-rank trivial core on each clopen rank stratum `{x : X // r x = n}`, with
identity transition maps everywhere. `FiniteRankAtlas.continuous_mk_trivial_iff` characterizes
continuity of maps into its reconstructed total space in terms of continuity of coordinate vectors
on each clopen rank stratum, and `FiniteRankAtlas.trivialConstTotalSpaceHomeomorph` identifies the
reconstructed total space of a constant-rank trivial atlas with `X × (Fin n → 𝕜)`.

`FiniteRankAtlas.isZero_iff_rank_eq_zero` proves unconditionally (including when `X` is empty) that
a variable-rank atlas `A` is a categorical zero object in `FiniteRankAtlas 𝕜 X` if and only if
`A.rank = 0`, supplying `HasZeroObject (FiniteRankAtlas 𝕜 X)`.

Over a base with at most one point every atlas is trivial:
`FiniteRankAtlas.isoTrivialOfSubsingleton` identifies it with the trivial atlas of its rank.

## References

* M. F. Atiyah, *K-Theory*, W. A. Benjamin (1967), §1.1.
* D. Husemoller, *Fibre Bundles*, 3rd ed., Springer GTM 20 (1994), Chapter 3.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

variable (𝕜 X) in
/-- The trivial variable-rank atlas of locally constant rank `r`, with identity coordinate changes
on each clopen rank stratum. -/
-- Expose the rank projection so `(trivial 𝕜 X r).Fiber x` reduces to `Fin (r x) → 𝕜`.
@[expose]
def trivial (r : LocallyConstant X ℕ) : FiniteRankAtlas 𝕜 X where
  rank := r
  charts n := (FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n).core
  indexAt_eq _ _ := rfl

/-- Rank function of `trivial 𝕜 X r`. -/
@[simp]
theorem rank_trivial (r : LocallyConstant X ℕ) :
    (trivial 𝕜 X r).rank = r := (rfl)

/-- Rank-`n` stratum coordinate core of `trivial 𝕜 X r`. -/
@[simp]
theorem charts_trivial (r : LocallyConstant X ℕ) (n : ℕ) :
    (trivial 𝕜 X r).charts n = (FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n).core := (rfl)

/-- Packaged rank-`n` `FiniteRankBundleCore` of `trivial 𝕜 X r`. -/
@[simp]
theorem stratumCore_trivial (r : LocallyConstant X ℕ) (n : ℕ) :
    (trivial 𝕜 X r).stratumCore n = FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n := (rfl)

/-- A map into the reconstructed total space of `trivial 𝕜 X r` over a continuous base map `b` is
continuous if and only if its coordinate vector is continuous on every clopen rank stratum. -/
theorem continuous_mk_trivial_iff {Y : Type*} [TopologicalSpace Y]
    {r : LocallyConstant X ℕ} {b : Y → X} (hb : Continuous b)
    (s : ∀ y, (trivial 𝕜 X r).Fiber (b y)) :
    Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit (trivial 𝕜 X r).Fiber)) ↔
      ∀ n : ℕ, Continuous (fun y : {y : Y // r (b y) = n} =>
        fun i : Fin n => s y.val (Fin.cast y.property.symm i)) := by
  rw [(trivial 𝕜 X r).continuous_mk_iff_rankStrata hb s]
  refine forall_congr' fun n => ?_
  exact (FiniteRankBundleCore.continuous_trivial_iff
    (𝕜 := 𝕜) (B := {x : X // r x = n}) (n := n)).trans
    (and_iff_right ((hb.comp continuous_subtypeVal).subtype_mk _))

/-- A map into the reconstructed total space of a constant-rank trivial atlas is continuous if and
only if its base map and coordinate vector are continuous. -/
theorem continuous_mk_trivial_const_iff {Y : Type*} [TopologicalSpace Y]
    {n : ℕ} {b : Y → X} {s : Y → Fin n → 𝕜} :
    Continuous (fun y =>
        (⟨b y, s y⟩ : TotalSpace Unit (trivial 𝕜 X (LocallyConstant.const X n)).Fiber)) ↔
      Continuous b ∧ Continuous s := by
  constructor
  · intro hs
    have hb : Continuous b := (trivial 𝕜 X (LocallyConstant.const X n)).continuous_proj.comp hs
    refine ⟨hb, ?_⟩
    exact ((continuous_mk_trivial_iff (r := LocallyConstant.const X n) hb s).1 hs n).comp
      (Continuous.subtype_mk continuous_id fun _ => rfl)
  · rintro ⟨hb, hs⟩
    refine (continuous_mk_trivial_iff (r := LocallyConstant.const X n) hb s).2 fun m => ?_
    by_cases hnm : n = m
    · subst hnm
      exact hs.comp continuous_subtypeVal
    · have : IsEmpty {y : Y // (LocallyConstant.const X n) (b y) = m} := ⟨fun y => hnm y.property⟩
      exact continuous_of_discreteTopology

/-- The reconstructed total space of a constant-rank trivial atlas is homeomorphic to
`X × (Fin n → 𝕜)`. -/
def trivialConstTotalSpaceHomeomorph (n : ℕ) :
    TotalSpace Unit (trivial 𝕜 X (LocallyConstant.const X n)).Fiber ≃ₜ X × (Fin n → 𝕜) where
  toFun p := (p.proj, p.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  continuous_toFun := by
    have h := (continuous_mk_trivial_const_iff (𝕜 := 𝕜) (X := X) (n := n)
      (b := fun p : TotalSpace Unit (trivial 𝕜 X (LocallyConstant.const X n)).Fiber => p.proj)
      (s := fun p => p.snd)).1 continuous_id
    exact h.1.prodMk h.2
  continuous_invFun :=
    (continuous_mk_trivial_const_iff (𝕜 := 𝕜) (X := X) (n := n)).2 ⟨continuous_fst, continuous_snd⟩

/-- Forward evaluation of `trivialConstTotalSpaceHomeomorph`. -/
@[simp]
theorem trivialConstTotalSpaceHomeomorph_apply (n : ℕ)
    (p : TotalSpace Unit (trivial 𝕜 X (LocallyConstant.const X n)).Fiber) :
    trivialConstTotalSpaceHomeomorph (𝕜 := 𝕜) (X := X) n p = (p.proj, p.snd) := (rfl)

/-- Inverse evaluation of `trivialConstTotalSpaceHomeomorph`. -/
@[simp]
theorem trivialConstTotalSpaceHomeomorph_symm_apply (n : ℕ) (p : X × (Fin n → 𝕜)) :
    (trivialConstTotalSpaceHomeomorph (𝕜 := 𝕜) (X := X) n).symm p = ⟨p.1, p.2⟩ := (rfl)

/-- A variable-rank bundle atlas is a categorical zero object if and only if its locally constant
rank vanishes identically. This holds unconditionally, including when `X` is empty. -/
theorem isZero_iff_rank_eq_zero {A : FiniteRankAtlas 𝕜 X} :
    IsZero A ↔ A.rank = 0 := by
  rw [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    ext x
    by_contra hx
    have hpos : 0 < A.rank x := Nat.pos_of_ne_zero hx
    have hid := congrArg (fun f : A ⟶ A => f.fiberMap x (fun _ => (1 : 𝕜)) ⟨0, hpos⟩) h
    exact one_ne_zero hid
  · intro h
    apply hom_ext
    intro x
    have hx : A.rank x = 0 := congrFun (congrArg DFunLike.coe h) x
    ext v i
    exact (Fin.cast hx i).elim0

/-- The trivial atlas of rank zero is a zero object. -/
theorem isZero_trivial_zero : IsZero (trivial 𝕜 X 0) :=
  isZero_iff_rank_eq_zero.2 rfl

/-- Over an empty base space every variable-rank atlas is a zero object. -/
theorem isZero_of_isEmpty [IsEmpty X] (A : FiniteRankAtlas 𝕜 X) : IsZero A :=
  isZero_iff_rank_eq_zero.2 (LocallyConstant.ext isEmptyElim)

/-- Variable-rank bundle atlases have a categorical zero object given by `trivial 𝕜 X 0`. -/
instance : HasZeroObject (FiniteRankAtlas 𝕜 X) :=
  ⟨⟨trivial 𝕜 X 0, isZero_trivial_zero⟩⟩

open ZeroObject in
/-- The categorical zero object in `FiniteRankAtlas 𝕜 X` has rank zero. -/
@[simp]
theorem rank_zero : (0 : FiniteRankAtlas 𝕜 X).rank = 0 :=
  isZero_iff_rank_eq_zero.1 (isZero_zero _)

section Subsingleton

variable [Subsingleton X]

/-- Over a subsingleton base, the coordinate vector of a point of a stratum core total space is
continuous: the chart at the only base point covers the whole stratum, with identity transition. -/
private theorem continuous_snd_charts_of_subsingleton (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    Continuous (fun p : (A.charts n).TotalSpace => (p.snd : Fin n → 𝕜)) := by
  rcases isEmpty_or_nonempty {x : X // A.rank x = n} with h | hne
  · exact continuous_of_const fun p => (h.false p.proj).elim
  obtain ⟨i⟩ := hne
  have hsrc : ((A.charts n).localTrivAt i).source = Set.univ :=
    Set.eq_univ_of_forall fun ⟨b, _⟩ => by
      obtain rfl : b = i := Subsingleton.elim _ _
      exact (A.charts n).mem_source_at _ _
  have hc := ((A.charts n).localTrivAt i).continuousOn
  rw [hsrc, continuousOn_univ] at hc
  refine (continuous_snd.comp hc).congr fun p => ?_
  rw [Function.comp_apply, Subsingleton.elim i p.proj, (A.charts n).localTrivAt_apply p]

/-- Over a subsingleton base, a map into a stratum core total space is continuous exactly when its
coordinate vector is: every point lies over the only base point, so the map factors through the
fibre inclusion `FiberBundle.totalSpaceMk` there. -/
private theorem continuous_charts_iff_of_subsingleton (A : FiniteRankAtlas 𝕜 X) (n : ℕ)
    {Y : Type*} [TopologicalSpace Y] {f : Y → (A.charts n).TotalSpace} :
    Continuous f ↔ Continuous (fun y => ((f y).snd : Fin n → 𝕜)) := by
  refine ⟨(continuous_snd_charts_of_subsingleton A n).comp, fun hf => ?_⟩
  rcases isEmpty_or_nonempty {x : X // A.rank x = n} with h | hne
  · exact continuous_of_const fun y => (h.false (f y).proj).elim
  obtain ⟨i⟩ := hne
  refine ((FiberBundle.continuous_totalSpaceMk (Fin n → 𝕜) (A.charts n).Fiber i).comp hf).congr
    fun y => ?_
  -- `Function.comp_apply` cannot rewrite here: the composite only typechecks after unfolding
  -- `VectorBundleCore.Fiber`, since `(f y).snd` lies in the fibre over `(f y).proj` while
  -- `TotalSpace.mk i` expects the fibre over `i`. Every fibre of the core is by definition
  -- `Fin n → 𝕜`, so `change` states the goal with that fibre and the composite applied to `y`.
  change TotalSpace.mk' (Fin n → 𝕜) i (f y).snd = f y
  generalize f y = p
  obtain ⟨b, v⟩ := p
  obtain rfl : i = b := Subsingleton.elim _ _
  -- both sides are the point `⟨i, v⟩` of the fibre over `i`
  rfl

/-- Over a subsingleton base, every variable-rank atlas is isomorphic to the trivial atlas of the
same rank, by the identity on every fibre. -/
def isoTrivialOfSubsingleton (A : FiniteRankAtlas 𝕜 X) : A ≅ trivial 𝕜 X A.rank :=
  isoMk (fun x => LinearEquiv.refl 𝕜 (A.Fiber x))
    ((continuous_mk_trivial_iff A.continuous_proj fun p => p.snd).2 fun n =>
      (continuous_snd_charts_of_subsingleton A n).comp
        ((A.continuous_mk_iff_rankStrata A.continuous_proj fun p => p.snd).1 continuous_id n))
    ((A.continuous_mk_iff_rankStrata (trivial 𝕜 X A.rank).continuous_proj fun p => p.snd).2
      fun n => (continuous_charts_iff_of_subsingleton A n).2
        ((continuous_mk_trivial_iff (trivial 𝕜 X A.rank).continuous_proj fun p => p.snd).1
          continuous_id n))

@[simp] theorem fiberMap_isoTrivialOfSubsingleton_hom (A : FiniteRankAtlas 𝕜 X) (x : X) :
    (isoTrivialOfSubsingleton A).hom.fiberMap x = LinearMap.id :=
  fiberMap_isoMk_hom _ _ _ x

@[simp] theorem fiberMap_isoTrivialOfSubsingleton_inv (A : FiniteRankAtlas 𝕜 X) (x : X) :
    (isoTrivialOfSubsingleton A).inv.fiberMap x = LinearMap.id :=
  fiberMap_isoMk_inv _ _ _ x

end Subsingleton

end TauCeti.FiniteRankAtlas

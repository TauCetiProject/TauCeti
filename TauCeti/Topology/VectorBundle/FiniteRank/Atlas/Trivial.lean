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
# Trivial variable-rank atlases and zero objects

Each rank stratum of a variable-rank bundle atlas `A : FiniteRankAtlas 𝕜 X` packages into a
point-indexed constant-rank core `A.stratumCore n`. Dual to `continuous_mk_iff_rankStrata`, a map
out of the reconstructed total space `TotalSpace Unit A.Fiber` is continuous if and only if its
restrictions to all stratum core total spaces are continuous
(`continuous_totalSpace_iff_rankStrata`).

Given any locally constant rank function `r : LocallyConstant X ℕ`, `FiniteRankAtlas.trivial 𝕜 r`
equips each clopen rank stratum `{x : X // r x = n}` with `FiniteRankBundleCore.trivial`. A map into
its total space over a continuous base map is continuous precisely when its coordinate vectors are
continuous on each rank stratum (`continuous_mk_trivial_iff`), and for constant rank `n` its total
space is homeomorphic over `X` to `X × (Fin n → 𝕜)` (`trivialConstTotalSpaceHomeomorph`).

Finally, `isZero_iff_rank_eq_zero` characterizes the categorical zero objects of
`FiniteRankAtlas 𝕜 X` as the atlases of identically zero rank, and `trivial 𝕜 0` provides the
`HasZeroObject (FiniteRankAtlas 𝕜 X)` instance with no compactness, separation, or nonemptiness
assumptions on `X`.

The construction builds on `TauCeti.FiniteRankAtlas` and `TauCeti.FiniteRankBundleCore.trivial`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* M. F. Atiyah, *K-Theory*, §1.1.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits Topology

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

/-- Package the `n`th rank-stratum chart core of an atlas as a point-indexed
`FiniteRankBundleCore`. -/
-- Reduce the rank also during implicit-argument matching of coordinate-map simp lemmas.
@[expose, implicit_reducible]
def stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    FiniteRankBundleCore 𝕜 {x : X // A.rank x = n} where
  rank := n
  core := A.charts n
  indexAt_eq := A.indexAt_eq n

@[simp]
theorem rank_stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (A.stratumCore n).rank = n := (rfl)

@[simp]
theorem core_stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (A.stratumCore n).core = A.charts n := (rfl)

/-- A map out of a reconstructed variable-rank total space is continuous if and only if its
restrictions to the native core total spaces on all rank strata are continuous. -/
theorem continuous_totalSpace_iff_rankStrata (A : FiniteRankAtlas 𝕜 X)
    {Z : Type*} [TopologicalSpace Z] {g : TotalSpace Unit A.Fiber → Z} :
    Continuous g ↔
      ∀ n : ℕ, Continuous (fun p : (A.charts n).TotalSpace =>
        g (A.totalSpaceHomeomorph ⟨n, p⟩)) := by
  rw [← A.totalSpaceHomeomorph.comp_continuous_iff', continuous_sigma_iff]
  rfl

variable (𝕜) in
/-- The trivial variable-rank atlas of locally constant rank `r : LocallyConstant X ℕ`, with a
single global chart on each clopen rank stratum `{x : X // r x = n}`. -/
-- Reduce the rank projection so the dependent coordinate fibre at `x` reduces to `Fin (r x) → 𝕜`.
@[expose, implicit_reducible]
def trivial (r : LocallyConstant X ℕ) : FiniteRankAtlas 𝕜 X where
  rank := r
  charts n := (FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n).core
  indexAt_eq n := (FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n).indexAt_eq

@[simp]
theorem rank_trivial (r : LocallyConstant X ℕ) :
    (trivial 𝕜 r).rank = r := (rfl)

@[simp]
theorem charts_trivial (r : LocallyConstant X ℕ) (n : ℕ) :
    (trivial 𝕜 r).charts n = (FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n).core := (rfl)

@[simp]
theorem stratumCore_trivial (r : LocallyConstant X ℕ) (n : ℕ) :
    (trivial 𝕜 r).stratumCore n = FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n := (rfl)

/-- A map into the total space of `trivial 𝕜 r` over a continuous base map `b : Y → X` is continuous
if and only if on each rank stratum `{y : Y // r (b y) = n}` its coordinate vector in `Fin n → 𝕜`
is continuous. -/
theorem continuous_mk_trivial_iff {Y : Type*} [TopologicalSpace Y] {b : Y → X}
    (hb : Continuous b) (r : LocallyConstant X ℕ) (s : ∀ y, Fin (r (b y)) → 𝕜) :
    Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit (trivial 𝕜 r).Fiber)) ↔
      ∀ n : ℕ, Continuous (fun y : {y : Y // r (b y) = n} =>
        (fun i : Fin n => s y.1 (Fin.cast y.2.symm i))) :=
  ((trivial 𝕜 r).continuous_mk_iff_rankStrata hb s).trans <|
    forall_congr' fun n =>
      (FiniteRankBundleCore.continuous_trivial_iff
        (𝕜 := 𝕜) (B := {x : X // r x = n}) (n := n)).trans
        (and_iff_right ((hb.comp continuous_subtype_val).subtype_mk _))

variable (𝕜 X) in
/-- For constant rank `n`, the reconstructed total space of `trivial 𝕜 (LocallyConstant.const X n)`
is homeomorphic over `X` to the Cartesian product `X × (Fin n → 𝕜)`. -/
def trivialConstTotalSpaceHomeomorph (n : ℕ) :
    TotalSpace Unit (trivial 𝕜 (LocallyConstant.const X n)).Fiber ≃ₜ X × (Fin n → 𝕜) where
  toFun p := (p.proj, p.2)
  invFun q := ⟨q.1, q.2⟩
  left_inv p := by cases p; rfl
  right_inv q := by cases q; rfl
  continuous_toFun := by
    let sndFn : TotalSpace Unit (trivial 𝕜 (LocallyConstant.const X n)).Fiber → Fin n → 𝕜 :=
      fun p => p.2
    have hsnd : Continuous sndFn := by
      refine (continuous_totalSpace_iff_rankStrata
        (trivial 𝕜 (LocallyConstant.const X n)) (g := sndFn)).2 fun m => ?_
      by_cases hnm : n = m
      · subst hnm
        exact (FiniteRankBundleCore.continuous_trivial_snd
          (𝕜 := 𝕜) (B := {x : X // LocallyConstant.const X n x = n}) (n := n)).congr fun p => by
            ext i
            exact (congrFun (congrArg sndFn
              ((trivial 𝕜 (LocallyConstant.const X n)).totalSpaceHomeomorph_apply ⟨n, p⟩)) i).symm
      · have : IsEmpty ((trivial 𝕜 (LocallyConstant.const X n)).charts m).TotalSpace :=
          ⟨fun p => hnm p.proj.2⟩
        exact continuous_of_discreteTopology
    exact (trivial 𝕜 (LocallyConstant.const X n)).continuous_proj.prodMk hsnd
  continuous_invFun := by
    refine (continuous_mk_trivial_iff (b := Prod.fst) continuous_fst
      (LocallyConstant.const X n)
      (fun q : X × (Fin n → 𝕜) => (q.2 : Fin ((LocallyConstant.const X n) q.1) → 𝕜))).2
      fun m => ?_
    by_cases hnm : n = m
    · subst hnm
      exact (continuous_snd.comp continuous_subtype_val).congr fun q => by
        ext i
        rfl
    · have : IsEmpty {q : X × (Fin n → 𝕜) // LocallyConstant.const X n q.1 = m} :=
        ⟨fun q => hnm q.2⟩
      exact continuous_of_discreteTopology

@[simp]
theorem trivialConstTotalSpaceHomeomorph_apply (n : ℕ)
    (p : TotalSpace Unit (trivial 𝕜 (LocallyConstant.const X n)).Fiber) :
    trivialConstTotalSpaceHomeomorph 𝕜 X n p = (p.proj, p.2) := (rfl)

@[simp]
theorem trivialConstTotalSpaceHomeomorph_symm_apply (n : ℕ) (q : X × (Fin n → 𝕜)) :
    (trivialConstTotalSpaceHomeomorph 𝕜 X n).symm q = ⟨q.1, q.2⟩ := (rfl)

/-- An atlas of identically zero rank is a categorical zero object. -/
theorem isZero_of_rank_eq_zero (A : FiniteRankAtlas 𝕜 X) (h : A.rank = 0) : IsZero A where
  unique_to D := ⟨⟨⟨0⟩, fun f => by
    apply hom_ext
    intro x
    apply LinearMap.ext
    intro v
    have hx : A.rank x = 0 := DFunLike.congr_fun h x
    have hv : v = 0 := funext fun i => (Fin.cast hx i).elim0
    simp [hv]⟩⟩
  unique_from D := ⟨⟨⟨0⟩, fun f => by
    apply hom_ext
    intro x
    ext v i
    have hx : A.rank x = 0 := DFunLike.congr_fun h x
    exact (Fin.cast hx i).elim0⟩⟩

/-- Every categorical zero object in `FiniteRankAtlas 𝕜 X` has identically zero rank. -/
theorem rank_eq_zero_of_isZero {A : FiniteRankAtlas 𝕜 X} (h : IsZero A) : A.rank = 0 := by
  ext x
  simp only [LocallyConstant.coe_zero, Pi.zero_apply]
  by_contra hx
  have hid : (𝟙 A : A ⟶ A) = 0 := h.eq_of_src _ _
  have eval := congrFun
    (DFunLike.congr_fun (congrArg (fun f : A ⟶ A => f.fiberMap x) hid) (fun _ => (1 : 𝕜)))
    ⟨0, Nat.pos_of_ne_zero hx⟩
  exact one_ne_zero eval

/-- A variable-rank bundle atlas is a categorical zero object if and only if its locally constant
rank is identically zero. -/
theorem isZero_iff_rank_eq_zero {A : FiniteRankAtlas 𝕜 X} : IsZero A ↔ A.rank = 0 :=
  ⟨rank_eq_zero_of_isZero, isZero_of_rank_eq_zero A⟩

/-- The trivial rank-zero atlas is a zero object. -/
theorem isZero_trivial_zero : IsZero (trivial 𝕜 (0 : LocallyConstant X ℕ)) :=
  isZero_of_rank_eq_zero _ rfl

/-- The trivial rank-zero atlas supplies the zero object of `FiniteRankAtlas 𝕜 X`. -/
instance : HasZeroObject (FiniteRankAtlas 𝕜 X) :=
  ⟨⟨trivial 𝕜 (0 : LocallyConstant X ℕ), isZero_trivial_zero⟩⟩

end TauCeti.FiniteRankAtlas

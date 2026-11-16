/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Basic

/-!
# Stratum cores and trivial variable-rank bundle atlases

Each clopen rank stratum `{x : X // A.rank x = n}` of a `TauCeti.FiniteRankAtlas` carries a
constant-rank point-indexed core `A.stratumCore n` (`TauCeti.FiniteRankBundleCore`). Assembling
trivial stratum cores along any locally constant rank defines `trivialOfRank` and `trivial`,
supplying `HasZeroObject (FiniteRankAtlas 𝕜 X)` and uniqueness over an empty base, alongside the
preferred-chart normalization principle `induction_on`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

/-- Extract the point-indexed core on the rank-`n` clopen stratum of an atlas. -/
-- Expose rank and core projections so stratum total spaces and model fibres reduce.
@[expose, implicit_reducible]
def stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    FiniteRankBundleCore 𝕜 {x : X // A.rank x = n} :=
  ⟨n, A.charts n, A.indexAt_eq n⟩

@[simp] theorem rank_stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (A.stratumCore n).rank = n := (rfl)

@[simp] theorem core_stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (A.stratumCore n).core = A.charts n := (rfl)

/-- Induction principle assuming `(A.charts n).indexAt` is definitionally `id` for all `n`. -/
@[elab_as_elim] theorem induction_on {Y : Type*} [TopologicalSpace Y]
    {motive : FiniteRankAtlas 𝕜 Y → Prop} (A : FiniteRankAtlas 𝕜 Y)
    (h : ∀ (r : LocallyConstant Y ℕ)
      (c : ∀ n, VectorBundleCore 𝕜 {y : Y // r y = n} (Fin n → 𝕜) {y : Y // r y = n})
      (hc : ∀ n y, (c n).indexAt y = y),
      motive ⟨r, fun n => { c n with indexAt := id, mem_baseSet_at := fun y =>
        (by simpa only [id_eq, hc n y] using (c n).mem_baseSet_at y) }, fun _ _ => rfl⟩) :
    motive A := by
  rcases A with ⟨r, c, hc⟩
  suffices (⟨r, fun n => { c n with indexAt := id, mem_baseSet_at := fun y =>
      (by simpa only [id_eq, hc n y] using (c n).mem_baseSet_at y) }, fun _ _ => rfl⟩ :
      FiniteRankAtlas 𝕜 Y) = ⟨r, c, hc⟩ from this ▸ h r c hc
  congr; funext n
  exact VectorBundleCore.ext (fun _ => rfl) (fun y => (hc n y).symm) fun _ _ _ => rfl

variable (𝕜) in
/-- The trivial variable-rank atlas with prescribed locally constant rank `r`. -/
-- Expose the rank projection so reconstructed coordinate fibres reduce to `Fin (r x) → 𝕜`.
@[expose, implicit_reducible]
def trivialOfRank (r : LocallyConstant X ℕ) : FiniteRankAtlas 𝕜 X :=
  ⟨r, fun n => (FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n).core, fun _ _ => rfl⟩

@[simp] theorem rank_trivialOfRank (r : LocallyConstant X ℕ) :
    (trivialOfRank 𝕜 r).rank = r := (rfl)

variable (𝕜 X) in
/-- The constant-rank trivial atlas of rank `n`. -/
-- Expose the rank projection so reconstructed coordinate fibres reduce to `Fin n → 𝕜`.
@[expose, implicit_reducible]
def trivial (n : ℕ) : FiniteRankAtlas 𝕜 X := trivialOfRank 𝕜 (LocallyConstant.const X n)

@[simp] theorem rank_trivial (n : ℕ) : (trivial 𝕜 X n).rank = LocallyConstant.const X n := (rfl)

/-- The rank-zero trivial atlas is a zero object, including over an empty or disconnected base. -/
theorem isZero_trivial_zero : IsZero (trivial 𝕜 X 0) := by
  rw [IsZero.iff_id_eq_zero]; apply hom_ext; intro x; ext v i; exact Fin.elim0 i

instance : HasZeroObject (FiniteRankAtlas 𝕜 X) := ⟨⟨trivial 𝕜 X 0, isZero_trivial_zero⟩⟩

instance [IsEmpty X] : Unique (FiniteRankAtlas 𝕜 X) where
  default := trivial 𝕜 X 0
  uniq := fun ⟨r, _, _⟩ => by
    obtain rfl : r = LocallyConstant.const X 0 := LocallyConstant.ext isEmptyElim
    congr; funext _; exact VectorBundleCore.ext isEmptyElim isEmptyElim isEmptyElim

end TauCeti.FiniteRankAtlas

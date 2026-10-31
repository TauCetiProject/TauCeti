/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import TauCeti.FieldTheory.Galois.Profinite
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Galois
public import TauCeti.RingTheory.LaurentSeries.RamificationIndex

/-!
# The Galois group of the Puiseux field as a limit over the levels

Let `K` be a field containing a primitive `n`-th root of unity for every `n > 0`, and let
`P = puiseuxField K`. Each level `K⸨t ^ (1 / n)⸩` is a finite Galois extension of `K⸨X⸩`, and the
levels exhaust `P`, so `P` is Galois over `K⸨X⸩`. Mathlib identifies the Galois group of any
Galois extension, with its Krull topology, with the limit of the finite Galois groups `Gal(L/K⸨X⸩)`
over the finite Galois intermediate fields `L`, ordered by reverse inclusion
(`InfiniteGalois.continuousMulEquivToLimit`).

This file shows that the levels are cofinal among the finite Galois intermediate fields of `P`:
every such field lies in some level, so the functor `n ↦ K⸨t ^ (1 / n)⸩` from ramification indices
ordered by divisibility is final. Consequently a point of Mathlib's limit is determined by its
components at the levels. Through the Kummer isomorphisms `Gal(level n/K⸨X⸩) ≃* μₙ(K)`, these
components form a point of the Tate module `lim_n μₙ(K)`, and this identifies Mathlib's limit with
the Tate module as topological groups, compatibly with
`TauCeti.puiseuxField.galEquivTateModule`.

## Main definitions

* `TauCeti.puiseuxField.levelFiniteGalois K n`: level `n` as a finite Galois intermediate field
  of `P` over `K⸨X⸩`.
* `TauCeti.puiseuxField.levelFunctor K`: the levels, as a functor from ramification indices to
  finite Galois intermediate fields.
* `TauCeti.puiseuxField.limitEquivTateModule K`: the isomorphism of topological groups between
  Mathlib's limit `lim_L Gal(L/K⸨X⸩)` and the Tate module `lim_n μₙ(K)`.

## Main results

* `TauCeti.puiseuxField.isGalois`: the Puiseux field is Galois over `K⸨X⸩`.
* `TauCeti.puiseuxField.exists_le_levelFiniteGalois`: every finite Galois intermediate field lies
  in a level.
* `TauCeti.puiseuxField.final_levelFunctor`: the levels are cofinal.
* `TauCeti.puiseuxField.limit_ext`: a point of the limit is determined by its level components.
* `TauCeti.puiseuxField.proj_limitEquivTateModule`: the level-`n` component of the image of a
  point is the root of unity of its level-`n` component.
* `TauCeti.puiseuxField.limitEquivTateModule_continuousMulEquivToLimit`: composed with Mathlib's
  `InfiniteGalois.continuousMulEquivToLimit`, the isomorphism is `galEquivTateModule`.
-/

public section

open CategoryTheory IntermediateField InfiniteGalois Opposite
open scoped LaurentSeries

namespace TauCeti.puiseuxField

variable {K : Type*} [Field K]

variable (K) in
/-- The level `K⸨t ^ (1 / n)⸩`, as a finite Galois intermediate field of the Puiseux field over
`K⸨X⸩`, when `K` contains a primitive `n`-th root of unity. -/
-- The body is exposed so that `Gal(levelFiniteGalois K n/K⸨X⸩)`, the component type of the Galois
-- limit, is `Gal(level K n/K⸨X⸩)` by definition, the domain of `levelGalEquivRootsOfUnity`.
@[expose] noncomputable def levelFiniteGalois (n : ℕ+) [HasEnoughRootsOfUnity K n] :
    FiniteGaloisIntermediateField K⸨X⸩ (puiseuxField K) where
  toIntermediateField := level K n
  finiteDimensional := (levelPowerBasis K n).finite

/-- The underlying intermediate field of `levelFiniteGalois K n` is level `n`. -/
@[simp]
theorem toIntermediateField_levelFiniteGalois (n : ℕ+) [HasEnoughRootsOfUnity K n] :
    (levelFiniteGalois K n).toIntermediateField = level K n :=
  (rfl)

/-- Level `n` lies in level `m` exactly when `n ∣ m`. -/
theorem levelFiniteGalois_le_levelFiniteGalois_iff {n m : ℕ+} [HasEnoughRootsOfUnity K n]
    [HasEnoughRootsOfUnity K m] :
    levelFiniteGalois K n ≤ levelFiniteGalois K m ↔ n ∣ m := by
  rw [FiniteGaloisIntermediateField.le_iff, toIntermediateField_levelFiniteGalois,
    toIntermediateField_levelFiniteGalois, level_le_level_iff]

variable [∀ n : ℕ+, HasEnoughRootsOfUnity K n]

/-- The Puiseux field is Galois over `K⸨X⸩` when `K` contains a primitive `n`-th root of unity for
every `n > 0`: it is the union of the levels, each of which is Galois over `K⸨X⸩`. -/
instance isGalois : IsGalois K⸨X⸩ (puiseuxField K) := by
  have : IsGalois K⸨X⸩ (⊤ : IntermediateField K⸨X⸩ (puiseuxField K)) := by
    have (d : ℕ+) : Algebra.IsSeparable K⸨X⸩ (level K d) := (isGalois_level K d).to_isSeparable
    rw [← iSup_level K]
    exact isGalois_iff.mpr ⟨isSeparable_iSup .., normal_iSup _ _ _⟩
  exact IsGalois.of_algEquiv topEquiv

/-- **Cofinality of the levels.** Every finite Galois intermediate field of the Puiseux field over
`K⸨X⸩` lies in some level. -/
theorem exists_le_levelFiniteGalois (L : FiniteGaloisIntermediateField K⸨X⸩ (puiseuxField K)) :
    ∃ n : ℕ+, L ≤ levelFiniteGalois K n :=
  L.toIntermediateField.exists_le_level

variable (K) in
/-- The levels as a functor from ramification indices, ordered by divisibility, to the finite
Galois intermediate fields of the Puiseux field over `K⸨X⸩`. -/
noncomputable def levelFunctor :
    RamificationIndex ⥤ FiniteGaloisIntermediateField K⸨X⸩ (puiseuxField K) :=
  Monotone.functor (f := fun n ↦ levelFiniteGalois K n.toPNat) fun _ _ h ↦
    levelFiniteGalois_le_levelFiniteGalois_iff.mpr h

/-- The functor `levelFunctor K` sends a ramification index to its level. -/
@[simp]
theorem levelFunctor_obj (n : RamificationIndex) :
    (levelFunctor K).obj n = levelFiniteGalois K n.toPNat :=
  (rfl)

/-- **The levels are cofinal.** The functor `levelFunctor K` is final, so limits over the opposite
of the finite Galois intermediate fields may be computed over the levels alone. -/
instance final_levelFunctor : (levelFunctor K).Final :=
  Functor.final_of_exists_of_isFiltered _
    (fun L ↦ (exists_le_levelFiniteGalois L).elim fun n h ↦ ⟨⟨n⟩, ⟨homOfLE h⟩⟩)
    fun _ _ ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩

/-- A point of the limit `lim_L Gal(L/K⸨X⸩)` over the finite Galois intermediate fields `L` is
determined by its components at the levels. -/
theorem limit_ext {g g' : ProfiniteGrp.limit (asProfiniteGaloisGroupFunctor K⸨X⸩ (puiseuxField K))}
    (h : ∀ n : ℕ+, proj (levelFiniteGalois K n) g = proj (levelFiniteGalois K n) g') : g = g' := by
  -- Both points come from Galois automorphisms, which agree on every level and hence everywhere,
  -- since the levels exhaust the Puiseux field.
  obtain ⟨σ, rfl⟩ := (continuousMulEquivToLimit K⸨X⸩ (puiseuxField K)).surjective g
  obtain ⟨σ', rfl⟩ := (continuousMulEquivToLimit K⸨X⸩ (puiseuxField K)).surjective g'
  refine congrArg _ (AlgEquiv.ext fun x ↦ ?_)
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
  have hx : x ∈ (levelFiniteGalois K n).toIntermediateField := by
    rwa [toIntermediateField_levelFiniteGalois, mem_level_iff]
  have := congrArg (fun τ ↦ (τ ⟨x, hx⟩ : puiseuxField K)) (h n)
  rw [continuousMulEquivToLimit_apply, continuousMulEquivToLimit_apply, proj_algEquivToLimit,
    proj_algEquivToLimit] at this
  simpa only [AlgEquiv.restrictNormalHom_apply] using this

variable (K) in
/-- **The Galois limit is the Tate module.** Mathlib's limit `lim_L Gal(L/K⸨X⸩)` over the finite
Galois intermediate fields `L` of the Puiseux field is isomorphic, as a topological group, to the
Tate module `lim_n μₙ(K)`. The level-`n` component of the image of a point is the root of unity of
its level-`n` component (`TauCeti.puiseuxField.proj_limitEquivTateModule`). -/
noncomputable def limitEquivTateModule :
    ProfiniteGrp.limit (asProfiniteGaloisGroupFunctor K⸨X⸩ (puiseuxField K)) ≃ₜ*
      PrimeToPTateModule 1 K :=
  (continuousMulEquivToLimit K⸨X⸩ (puiseuxField K)).symm.trans (galEquivTateModule K)

/-- Composed with Mathlib's isomorphism `Gal(P/K⸨X⸩) ≃ₜ* lim_L Gal(L/K⸨X⸩)`, the isomorphism
`limitEquivTateModule` is `galEquivTateModule`. -/
theorem limitEquivTateModule_continuousMulEquivToLimit (σ : Gal(puiseuxField K/K⸨X⸩)) :
    limitEquivTateModule K (continuousMulEquivToLimit K⸨X⸩ (puiseuxField K) σ) =
      galEquivTateModule K σ := by
  rw [limitEquivTateModule, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.symm_apply_apply]

/-- The inverse of `limitEquivTateModule` sends `ζ` to the point of the limit given by the Kummer
automorphism of `ζ`. -/
theorem limitEquivTateModule_symm_apply (ζ : PrimeToPTateModule 1 K) :
    (limitEquivTateModule K).symm ζ =
      continuousMulEquivToLimit K⸨X⸩ (puiseuxField K) (kummer K ζ) := by
  rw [ContinuousMulEquiv.symm_apply_eq, limitEquivTateModule_continuousMulEquivToLimit,
    galEquivTateModule_kummer]

/-- The level-`n` component of the image of a point of the limit under `limitEquivTateModule` is
the root of unity attached by `levelGalEquivRootsOfUnity` to its level-`n` component. -/
theorem proj_limitEquivTateModule
    (g : ProfiniteGrp.limit (asProfiniteGaloisGroupFunctor K⸨X⸩ (puiseuxField K))) (n : ℕ+) :
    PrimeToPTateModule.proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ (limitEquivTateModule K g) =
      levelGalEquivRootsOfUnity K n (proj (levelFiniteGalois K n) g) := by
  obtain ⟨σ, rfl⟩ := (continuousMulEquivToLimit K⸨X⸩ (puiseuxField K)).surjective g
  rw [limitEquivTateModule_continuousMulEquivToLimit, proj_galEquivTateModule,
    continuousMulEquivToLimit_apply, proj_algEquivToLimit]
  -- `levelFiniteGalois K n` is level `n` by definition.
  rfl

end TauCeti.puiseuxField

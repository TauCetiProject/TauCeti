/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.UnionLift
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Linear maps out of directed unions of submodules

This file gives the universal property of a directed union of submodules. A compatible family of
semilinear maps on the members of a directed family glues to a semilinear map on any submodule of
their supremum.

The construction `Submodule.iSupLift` is the linear analogue of
`Subalgebra.iSupLift`. It uses `Set.iUnionLift` and the directedness of the family to prove that the
local maps agree on overlaps. Unlike `Subalgebra.iSupLift`, it does not require the index type to
be nonempty: over an empty index type the supremum is `⊥`, and the glued map is zero.

## Main declarations

* `Submodule.iSupLift`: glue compatible semilinear maps on a directed family of submodules.
* `Submodule.iSupLift_inclusion` and `Submodule.iSupLift_of_mem`: pointwise
  evaluation rules for the glued map.
* `Submodule.iSupLift_mk`: the glued map agrees with each prescribed map.
* `Submodule.iSupLift_comp_inclusion`: restricting the glued map recovers each prescribed
  map.
* `Submodule.iSupLift_unique`: the restriction property characterizes the glued map.
-/

public section

namespace Submodule

variable {R R₂ M P ι : Type*}
variable [Semiring R] [Semiring R₂] {σ : R →+* R₂}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid P] [Module R₂ P]

/-- The glued map on the whole directed supremum, for a nonempty index type. -/
private noncomputable def iSupLiftAux [Nonempty ι] (K : ι → Submodule R M)
    (dir : Directed (· ≤ ·) K) (f : ∀ i, K i →ₛₗ[σ] P)
    (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)) :
    (iSup K : Submodule R M) →ₛₗ[σ] P where
  toFun :=
    Set.iUnionLift (fun i => (K i : Set M)) (fun i => f i)
      (fun i j m hmi hmj => by
        obtain ⟨k, hik, hjk⟩ := dir i j
        simp [hf i k hik, hf j k hjk, inclusion_apply])
      (iSup K : Submodule R M) (coe_iSup_of_directed K dir).le
  map_add' := by
    apply Set.iUnionLift_binary (coe_iSup_of_directed K dir) dir _ (fun _ => (· + ·))
    all_goals simp
  map_smul' r := by
    apply Set.iUnionLift_unary (coe_iSup_of_directed K dir) _ (fun _ m => r • m)
    all_goals simp

/-- Define a semilinear map on a submodule of a directed supremum by defining it compatibly on
each member of the directed family. Over an empty index type the map is zero. -/
noncomputable def iSupLift (K : ι → Submodule R M) (dir : Directed (· ≤ ·) K)
    (f : ∀ i, K i →ₛₗ[σ] P)
    (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
    (T : Submodule R M) (hT : T ≤ iSup K) : T →ₛₗ[σ] P := by
  classical
  exact if _ : Nonempty ι then (iSupLiftAux K dir f hf).comp (inclusion hT) else 0

/-- The map glued on a directed supremum agrees with a prescribed map on each member of the
family. -/
@[simp]
theorem iSupLift_mk {K : ι → Submodule R M} {dir : Directed (· ≤ ·) K}
    {f : ∀ i, K i →ₛₗ[σ] P}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Submodule R M} {hT : T ≤ iSup K} {i : ι} (m : K i) (hm : (m : M) ∈ T) :
    iSupLift K dir f hf T hT ⟨m, hm⟩ = f i m := by
  rw [iSupLift, dite_eq_left ⟨i⟩]
  dsimp [iSupLiftAux]
  rw [inclusion_apply, Set.iUnionLift_mk]

/-- The map glued on a directed supremum agrees with a prescribed map after inclusion into its
domain. -/
@[simp]
theorem iSupLift_inclusion {K : ι → Submodule R M} {dir : Directed (· ≤ ·) K}
    {f : ∀ i, K i →ₛₗ[σ] P}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Submodule R M} {hT : T ≤ iSup K} {i : ι} (m : K i) (h : K i ≤ T) :
    iSupLift K dir f hf T hT (inclusion h m) = f i m :=
  iSupLift_mk m (h m.2)

/-- Evaluate the map glued on a directed supremum at an element known to lie in one member of the
family. -/
theorem iSupLift_of_mem {K : ι → Submodule R M} {dir : Directed (· ≤ ·) K}
    {f : ∀ i, K i →ₛₗ[σ] P}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Submodule R M} {hT : T ≤ iSup K} {i : ι} (m : T) (hm : (m : M) ∈ K i) :
    iSupLift K dir f hf T hT m = f i ⟨m, hm⟩ :=
  iSupLift_mk (⟨m, hm⟩ : K i) m.2

/-- Restricting the map glued on a directed supremum to a member of the family recovers the
prescribed map. -/
@[simp]
theorem iSupLift_comp_inclusion {K : ι → Submodule R M}
    {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₛₗ[σ] P}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Submodule R M} {hT : T ≤ iSup K} {i : ι} (h : K i ≤ T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by
  ext
  simp

/-- A semilinear map on a submodule of a directed supremum is determined by its values on the
members of the directed family. -/
theorem iSupLift_unique {K : ι → Submodule R M} {dir : Directed (· ≤ ·) K}
    {f : ∀ i, K i →ₛₗ[σ] P}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Submodule R M} {hT : T ≤ iSup K} (g : T →ₛₗ[σ] P)
    (hg : ∀ (i : ι) (m : K i) (hm : (m : M) ∈ T), g ⟨m, hm⟩ = f i m) :
    g = iSupLift K dir f hf T hT := by
  ext m
  rcases isEmpty_or_nonempty ι with hι | hι
  · obtain rfl : m = 0 := by simpa using hT m.2
    simp
  obtain ⟨i, hi⟩ := (mem_iSup_of_directed K dir).1 (hT m.2)
  rw [iSupLift_of_mem m hi]
  exact hg i ⟨m, hi⟩ m.2

end Submodule

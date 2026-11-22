/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import TauCeti.Algebra.Group.AddChar.Basic

/-!
# The annihilator of an additive subgroup under a character pairing

Let `R` be a commutative semiring, `V` and `W` additive groups which are `R`-modules,
`L : V →ₗ[R] W →ₗ[R] R` a bilinear pairing and `ψ : AddChar R M` an additive character. For an
additive subgroup `U` of `V`, the *character annihilator*
`U.characterAnnihilator ψ L = {w ∈ W | ψ (L u w) = 1 for all u ∈ U}`
is an additive subgroup of `W`. This is the annihilator that appears in Fourier analysis on a
locally compact module: the Fourier transform of the indicator of `U` for the character pairing
`(v, w) ↦ ψ (L v w)` is a multiple of the indicator of `U.characterAnnihilator ψ L`. For a local
field, `ψ` a nontrivial additive character and `L` a nondegenerate pairing, the annihilator of a
lattice is its dual lattice.

The annihilator is in general not an `R`-submodule: for the real character `x ↦ exp (2πix)` and
the multiplication pairing on `ℝ`, the annihilator of `ℤ` is `ℤ`. No topology, nontriviality or
nondegeneracy enters this file; the codomain `M` of the character is an arbitrary monoid.

## Main definitions

* `AddSubgroup.characterAnnihilator`: the annihilator of `U` for the pairing `ψ ∘ L`.

## Main results

* `AddSubgroup.mem_characterAnnihilator`: the membership criterion.
* `AddSubgroup.characterAnnihilator_bot`, `AddSubgroup.characterAnnihilator_zero`,
  `AddSubgroup.characterAnnihilator_one`: the trivial subgroup, the zero pairing and the trivial
  character have the whole group as annihilator.
* `AddSubgroup.characterAnnihilator_anti`: the annihilator is antitone in the subgroup.
* `AddSubgroup.characterAnnihilator_compl₂`: precomposing the pairing with a linear map in the
  second variable pulls the annihilator back along that map.
* `AddSubgroup.mem_characterAnnihilator_zmultiples`: the annihilator of the multiples of `v` is
  the set where `ψ (L v ·)` is trivial.
* `AddSubgroup.le_characterAnnihilator_iff`,
  `AddSubgroup.le_characterAnnihilator_characterAnnihilator_flip`: the annihilators for `L` and
  for the transposed pairing `L.flip` form a Galois connection, so each subgroup lies in its
  double annihilator.
-/

public section

variable {R V W W' M : Type*} [CommSemiring R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W'] [Monoid M]

namespace AddSubgroup

/-- The annihilator `{w | ψ (L u w) = 1 for all u ∈ U}` of an additive subgroup `U` of `V` for the
character pairing `(v, w) ↦ ψ (L v w)`, as an additive subgroup of `W`. -/
def characterAnnihilator (U : AddSubgroup V) (ψ : AddChar R M) (L : V →ₗ[R] W →ₗ[R] R) :
    AddSubgroup W where
  carrier := {w | ∀ u ∈ U, ψ (L u w) = 1}
  add_mem' {w w'} hw hw' u hu := by
    rw [map_add, AddChar.map_add_eq_mul, hw u hu, hw' u hu, one_mul]
  zero_mem' u _ := by rw [map_zero, AddChar.map_zero_eq_one]
  neg_mem' {w} hw u hu :=
    ψ.map_eq_one_of_add_eq_zero (hw u hu) (by rw [← map_add, neg_add_cancel, map_zero])

variable {U U' : AddSubgroup V} {ψ : AddChar R M} {L : V →ₗ[R] W →ₗ[R] R} {w : W}

@[simp]
theorem mem_characterAnnihilator :
    w ∈ U.characterAnnihilator ψ L ↔ ∀ u ∈ U, ψ (L u w) = 1 :=
  Iff.rfl

theorem coe_characterAnnihilator :
    (U.characterAnnihilator ψ L : Set W) = {w | ∀ u ∈ U, ψ (L u w) = 1} :=
  Set.ext fun _ ↦ mem_characterAnnihilator

/-- The annihilator of the trivial subgroup is everything. -/
@[simp]
theorem characterAnnihilator_bot : (⊥ : AddSubgroup V).characterAnnihilator ψ L = ⊤ := by
  ext w
  simp

/-- For the zero pairing every subgroup has the whole group as annihilator. -/
@[simp]
theorem characterAnnihilator_zero : U.characterAnnihilator ψ (0 : V →ₗ[R] W →ₗ[R] R) = ⊤ := by
  ext w
  simp

/-- For the trivial character every subgroup has the whole group as annihilator. -/
@[simp]
theorem characterAnnihilator_one : U.characterAnnihilator (1 : AddChar R M) L = ⊤ := by
  ext w
  simp

/-- The annihilator is antitone: a larger subgroup has a smaller annihilator. -/
theorem characterAnnihilator_anti (h : U ≤ U') :
    U'.characterAnnihilator ψ L ≤ U.characterAnnihilator ψ L :=
  fun _ hw u hu ↦ hw u (h hu)

/-- Precomposing the pairing with a linear map `T` in the second variable pulls the annihilator
back along `T`. -/
theorem characterAnnihilator_compl₂ (U : AddSubgroup V) (ψ : AddChar R M)
    (L : V →ₗ[R] W →ₗ[R] R) (T : W' →ₗ[R] W) :
    U.characterAnnihilator ψ (L.compl₂ T) =
      (U.characterAnnihilator ψ L).comap T.toAddMonoidHom := by
  ext w
  simp

/-- The annihilator of the multiples of `v` is the set where `ψ (L v ·)` is trivial. This is
tagged `simp high` so that it fires before the general `mem_characterAnnihilator`. -/
@[simp high]
theorem mem_characterAnnihilator_zmultiples {v : V} :
    w ∈ (zmultiples v).characterAnnihilator ψ L ↔ ψ (L v w) = 1 := by
  refine ⟨fun h ↦ h v (mem_zmultiples v), fun h ↦ ?_⟩
  have hnat (n : ℕ) : ψ (L (n • v) w) = 1 := by
    rw [map_nsmul, LinearMap.smul_apply, AddChar.map_nsmul_eq_pow, h, one_pow]
  intro u hu
  -- Write `u = n • v` or `u = -(n • v)`; the negative multiple cancels against `n • v`.
  obtain ⟨n, rfl | rfl⟩ : ∃ n : ℕ, u = n • v ∨ u = -(n • v) := by
    obtain ⟨k, rfl⟩ := mem_zmultiples_iff.mp hu
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k <;> exact ⟨n, by simp⟩
  · exact hnat n
  · refine ψ.map_eq_one_of_add_eq_zero (hnat n) ?_
    rw [← LinearMap.add_apply, ← map_add, neg_add_cancel, map_zero, LinearMap.zero_apply]

/-- A subgroup `A` of `W` lies in the annihilator of `U` for `L` exactly when `U` lies in the
annihilator of `A` for the transposed pairing `L.flip`. -/
theorem le_characterAnnihilator_iff {A : AddSubgroup W} :
    A ≤ U.characterAnnihilator ψ L ↔ U ≤ A.characterAnnihilator ψ L.flip :=
  ⟨fun h _ hu _ ha ↦ h ha _ hu, fun h _ ha _ hu ↦ h hu _ ha⟩

/-- Every subgroup lies in its double annihilator, taken first for `L` and then for the
transposed pairing `L.flip`. -/
theorem le_characterAnnihilator_characterAnnihilator_flip (U : AddSubgroup V) (ψ : AddChar R M)
    (L : V →ₗ[R] W →ₗ[R] R) :
    U ≤ (U.characterAnnihilator ψ L).characterAnnihilator ψ L.flip :=
  le_characterAnnihilator_iff.mp le_rfl

end AddSubgroup

namespace Submodule

variable {S : Type*} [CommRing S] [Algebra S R] [Module S V] [IsScalarTower S R V] [Module S W]
  [IsScalarTower S R W]

/-- The annihilator `{w | ψ (L u w) = 1 for all u ∈ U}` of an `S`-submodule `U` of `V` for the
character pairing `(v, w) ↦ ψ (L v w)`, where `R` is an `S`-algebra, as an `S`-submodule of `W`.
Its underlying additive subgroup is `AddSubgroup.characterAnnihilator`. -/
def characterAnnihilator (U : Submodule S V) (ψ : AddChar R M) (L : V →ₗ[R] W →ₗ[R] R) :
    Submodule S W where
  toAddSubmonoid := (U.toAddSubgroup.characterAnnihilator ψ L).toAddSubmonoid
  smul_mem' s w hw u hu := by
    have h : L u (s • w) = L (s • u) w := by
      rw [← algebraMap_smul R s w, ← algebraMap_smul R s u, map_smul, map_smul,
        LinearMap.smul_apply]
    exact h ▸ hw (s • u) (U.smul_mem s hu)

variable {U : Submodule S V} {ψ : AddChar R M} {L : V →ₗ[R] W →ₗ[R] R} {w : W}

@[simp]
theorem mem_characterAnnihilator :
    w ∈ U.characterAnnihilator ψ L ↔ ∀ u ∈ U, ψ (L u w) = 1 :=
  Iff.rfl

@[simp]
theorem toAddSubgroup_characterAnnihilator :
    (U.characterAnnihilator ψ L).toAddSubgroup = U.toAddSubgroup.characterAnnihilator ψ L :=
  AddSubgroup.ext fun _ ↦ Iff.rfl

end Submodule

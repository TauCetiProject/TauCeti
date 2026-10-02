/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.frobeniusFixedSubring`, its membership criterion and its behaviour under divisibility
-- of the exponent; this module also supplies Mathlib's `iterateFrobenius`.
public import TauCeti.Algebra.CharP.Frobenius.Fixed
-- `TauCeti.fixedSubgroup` and `TauCeti.fixedSubgroup_eq_top_iff`.
public import TauCeti.GroupTheory.FixedSubgroup
-- The `GL` notation, `Matrix.GeneralLinearGroup.map` and its entrywise description.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Invertible matrices fixed by the entrywise Frobenius

Let `A` be a commutative ring of exponential characteristic `p`. Raising every entry to the
`p ^ k`-th power is a group endomorphism `Matrix.GeneralLinearGroup.map (iterateFrobenius A p k)`
of `GL ι A`, and this file describes its fixed points: an invertible matrix is fixed exactly when
all of its entries lie in `TauCeti.frobeniusFixedSubring A p k`. In the motivating case, `p` prime,
`0 < k`, `A` an algebraic closure of `ZMod p` and `q = p ^ k`, the fixed subgroup is `GLₙ(𝔽_q)`
inside `GLₙ(A)`, and the divisibility statement below is the inclusion
`GLₙ(𝔽_{p ^ m}) ⊆ GLₙ(𝔽_{p ^ l})`.

Nothing here needs `A` to be a field, algebraically closed, or finite, and no coordinate ring or
Hopf-algebra theory is involved; the group-scheme reading of these statements is
`TauCeti/Algebra/AlgebraicGroup/Frobenius/GeneralLinear.lean`.

## Main results

* `Matrix.GeneralLinearGroup.mem_range_map_val_iff`: an invertible matrix comes from a subalgebra
  exactly when its entries and those of its inverse lie in it.
* `Matrix.GeneralLinearGroup.map_eq_self_iff_mem_equalizer` and
  `Matrix.GeneralLinearGroup.range_map_val_equalizer`: the invertible matrices fixed by an
  arbitrary entrywise algebra endomorphism are those with entries in, respectively those coming
  from, its equalizer subalgebra. These are the characteristic-free statements behind the two
  below, and the ones an algebra over a finite field needs, where `iterateFrobenius` is
  unavailable because the zero ring has no exponential characteristic `p`.
* `Matrix.GeneralLinearGroup.map_iterateFrobenius_eq_self_iff`: an invertible matrix is
  fixed by the entrywise Frobenius exactly when all of its entries are.
* `Matrix.GeneralLinearGroup.fixedSubgroup_map_iterateFrobenius_zero`: the zeroth iterate
  fixes everything.
* `Matrix.GeneralLinearGroup.fixedSubgroup_map_iterateFrobenius_le_of_dvd`: the fixed
  subgroups grow along divisibility of the exponent.

## References

These are the matrix-coordinate form of the Frobenius-fixed points used to construct the finite
groups of Lie type; see R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex
Characters*, §1.17.
-/

public section

open TauCeti

namespace Matrix.GeneralLinearGroup

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

section Subalgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **Which invertible matrices come from a subalgebra**: those whose entries, and whose inverse's
entries, all lie in it. Over a subalgebra invertibility is a condition on the inverse rather than
a consequence of the determinant being a unit of the ambient algebra, so the second clause cannot
be dropped. -/
@[simp]
theorem mem_range_map_val_iff (S : Subalgebra R A) (g : Matrix.GeneralLinearGroup ι A) :
    (∃ h, Matrix.GeneralLinearGroup.map (n := ι) (S.val : ↥S →+* A) h = g) ↔
      (∀ i j, (g : Matrix ι ι A) i j ∈ S) ∧
        ∀ i j, ((g⁻¹ : Matrix.GeneralLinearGroup ι A) : Matrix ι ι A) i j ∈ S := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Matrix.GeneralLinearGroup.map_apply]
      exact ((h : Matrix ι ι ↥S) i j).2
    · rw [← map_inv, Matrix.GeneralLinearGroup.map_apply]
      exact (((h⁻¹ : Matrix.GeneralLinearGroup ι ↥S) : Matrix ι ι ↥S) i j).2
  · rintro ⟨hg, hg'⟩
    obtain ⟨M, hM⟩ : ∃ M : Matrix ι ι ↥S, M.map (S.val : ↥S →+* A) = (g : Matrix ι ι A) :=
      ⟨fun i j => ⟨_, hg i j⟩, rfl⟩
    obtain ⟨N, hN⟩ : ∃ N : Matrix ι ι ↥S,
        N.map (S.val : ↥S →+* A) = ((g⁻¹ : Matrix.GeneralLinearGroup ι A) : Matrix ι ι A) :=
      ⟨fun i j => ⟨_, hg' i j⟩, rfl⟩
    have hone : (1 : Matrix ι ι ↥S).map (S.val : ↥S →+* A) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    -- `M` and `N` are mutually inverse because they are so after the injective inclusion of `S`.
    have h₁ : (M * N).map (S.val : ↥S →+* A) = (1 : Matrix ι ι ↥S).map (S.val : ↥S →+* A) := by
      rw [Matrix.map_mul, hM, hN, hone]
      exact congrArg Units.val (mul_inv_cancel g)
    have h₂ : (N * M).map (S.val : ↥S →+* A) = (1 : Matrix ι ι ↥S).map (S.val : ↥S →+* A) := by
      rw [Matrix.map_mul, hN, hM, hone]
      exact congrArg Units.val (inv_mul_cancel g)
    refine ⟨⟨M, N, Matrix.map_injective Subtype.val_injective h₁,
      Matrix.map_injective Subtype.val_injective h₂⟩,
      Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact congrFun (congrFun hM i) j

/-- An invertible matrix is fixed by an entrywise algebra endomorphism exactly when every one of
its entries lies in the equalizer of that endomorphism with the identity. -/
@[simp]
theorem map_eq_self_iff_mem_equalizer (φ : A →ₐ[R] A) (g : Matrix.GeneralLinearGroup ι A) :
    Matrix.GeneralLinearGroup.map (n := ι) (φ : A →+* A) g = g ↔
      ∀ i j, (g : Matrix ι ι A) i j ∈ AlgHom.equalizer φ (AlgHom.id R A) := by
  simp only [AlgHom.mem_equalizer, AlgHom.coe_id, id_eq]
  constructor
  · intro hg i j
    simpa using congrArg (fun M : Matrix.GeneralLinearGroup ι A => (M : Matrix ι ι A) i j) hg
  · intro hg
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Matrix.GeneralLinearGroup.map_apply]
    simpa using hg i j

/-- **The invertible matrices fixed by an entrywise algebra endomorphism are exactly the ones
coming from its equalizer subalgebra.** The entries of a fixed matrix are fixed, and so are those
of its inverse because the entrywise map is a group homomorphism, so a fixed matrix descends.

No characteristic hypothesis is used, so this also covers the `q`-power endomorphism of an
arbitrary algebra over a finite field, where `iterateFrobenius` is unavailable because the zero
ring has no exponential characteristic `p`. -/
theorem range_map_val_equalizer (φ : A →ₐ[R] A) :
    (Matrix.GeneralLinearGroup.map (n := ι)
        ((AlgHom.equalizer φ (AlgHom.id R A)).val :
          ↥(AlgHom.equalizer φ (AlgHom.id R A)) →+* A)).range =
      fixedSubgroup (Matrix.GeneralLinearGroup.map (n := ι) (φ : A →+* A)) := by
  ext g
  simp only [MonoidHom.mem_range]
  rw [mem_range_map_val_iff, mem_fixedSubgroup, map_eq_self_iff_mem_equalizer]
  refine ⟨fun h => h.1, fun h => ⟨h, (map_eq_self_iff_mem_equalizer φ g⁻¹).mp ?_⟩⟩
  rw [map_inv, (map_eq_self_iff_mem_equalizer φ g).mpr h]

end Subalgebra

variable (p : ℕ) {A : Type*} [CommRing A] [ExpChar A p]

/-- An invertible matrix is fixed by the entrywise `p ^ k`-power Frobenius exactly when every one
of its entries lies in the Frobenius-fixed subring.

Stated as the equation `Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g = g` rather than
as membership in `TauCeti.fixedSubgroup`, because the generic equality-locus simplifier rewrites
such a membership to this equation; this is the form `simp` reaches, matching
`TauCeti.Bialgebra.iterateFrobeniusPoints_eq_self_iff`. -/
@[simp]
theorem map_iterateFrobenius_eq_self_iff (k : ℕ) (g : Matrix.GeneralLinearGroup ι A) :
    Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g = g ↔
      ∀ i j, (g : Matrix ι ι A) i j ∈ frobeniusFixedSubring A p k := by
  constructor
  · intro hg i j
    rw [mem_frobeniusFixedSubring, ← iterateFrobenius_def,
      ← Matrix.GeneralLinearGroup.map_apply, hg]
  · intro hg
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]
    exact mem_frobeniusFixedSubring.mp (hg i j)

/-- The zeroth Frobenius iterate fixes every invertible matrix.

Deliberately not `@[simp]`: `iterateFrobenius_zero` already rewrites the ring homomorphism to the
identity, after which `Matrix.GeneralLinearGroup.map_id` and `TauCeti.fixedSubgroup_eq_top_iff`
close the goal, so a `simp` attribute here would be redundant. -/
theorem fixedSubgroup_map_iterateFrobenius_zero :
    fixedSubgroup (Matrix.GeneralLinearGroup.map (n := ι) (iterateFrobenius A p 0)) = ⊤ := by
  rw [iterateFrobenius_zero, Matrix.GeneralLinearGroup.map_id]
  exact fixedSubgroup_eq_top_iff.mpr rfl

/-- The subgroups of entrywise Frobenius-fixed matrices grow along divisibility of the exponent.
In the motivating case this is the inclusion `GLₙ(𝔽_{p ^ m}) ⊆ GLₙ(𝔽_{p ^ l})`. -/
theorem fixedSubgroup_map_iterateFrobenius_le_of_dvd {m l : ℕ} (hml : m ∣ l) :
    fixedSubgroup (Matrix.GeneralLinearGroup.map (n := ι) (iterateFrobenius A p m)) ≤
      fixedSubgroup (Matrix.GeneralLinearGroup.map (n := ι) (iterateFrobenius A p l)) :=
  fun g hg =>
  mem_fixedSubgroup.mpr ((map_iterateFrobenius_eq_self_iff p l g).mpr fun i j =>
    frobeniusFixedSubring_le_of_dvd hml
      ((map_iterateFrobenius_eq_self_iff p m g).mp (mem_fixedSubgroup.mp hg) i j))

end Matrix.GeneralLinearGroup

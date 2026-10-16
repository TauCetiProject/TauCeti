/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedSubgroup
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Invertible matrices over subalgebras

An invertible matrix over a commutative algebra comes from a subalgebra exactly when its entries
and those of its inverse lie in that subalgebra. This distinguishes invertibility over the
subalgebra from invertibility over the ambient algebra.

For the equalizer of an algebra endomorphism with the identity, the inverse-entry condition follows
from the entry condition: an entrywise map is a group homomorphism, so it fixes the inverse of every
matrix it fixes. Thus the general linear group over that equalizer maps onto the fixed subgroup of
the endomorphism. These characteristic-free statements apply in particular to Frobenius
endomorphisms of algebras over finite fields, including the zero ring.

## Main results

* `Matrix.GeneralLinearGroup.mem_range_map_val_iff`: descent to a subalgebra is equivalent to
  membership of the entries of the matrix and its inverse.
* `Matrix.GeneralLinearGroup.map_eq_self_iff_mem_equalizer`: a matrix is fixed by an entrywise
  algebra endomorphism exactly when its entries lie in its equalizer with the identity. The base
  may be a commutative semiring.
* `Matrix.GeneralLinearGroup.range_map_val_equalizer`: the image of the general linear group over
  the equalizer subalgebra is the fixed subgroup of the entrywise endomorphism. A commutative ring
  base ensures that subalgebras carry the ring structure used by the entrywise map.
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
    let M : Matrix ι ι S := fun i j => ⟨g i j, hg i j⟩
    let N : Matrix ι ι S := fun i j => ⟨g⁻¹ i j, hg' i j⟩
    have hM : M.map (S.val : S →+* A) = (g : Matrix ι ι A) := rfl
    have hN : N.map (S.val : S →+* A) =
        ((g⁻¹ : Matrix.GeneralLinearGroup ι A) : Matrix ι ι A) := rfl
    refine ⟨⟨M, N, ?_, ?_⟩, Units.ext rfl⟩
    -- Check the inverse equations after the injective inclusion of the subalgebra.
    · apply Matrix.map_injective (f := (S.val : S →+* A)) Subtype.val_injective
      simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one, hM, hN] using g.mul_inv
    · apply Matrix.map_injective (f := (S.val : S →+* A)) Subtype.val_injective
      simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one, hM, hN] using g.inv_mul

end Subalgebra

section Equalizer

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- An invertible matrix is fixed by an entrywise algebra endomorphism exactly when every one of
its entries lies in the equalizer of that endomorphism with the identity. -/
@[simp]
theorem map_eq_self_iff_mem_equalizer (φ : A →ₐ[R] A) (g : Matrix.GeneralLinearGroup ι A) :
    Matrix.GeneralLinearGroup.map (n := ι) (φ : A →+* A) g = g ↔
      ∀ i j, (g : Matrix ι ι A) i j ∈ AlgHom.equalizer φ (AlgHom.id R A) := by
  simp only [ext_iff, Matrix.GeneralLinearGroup.map_apply, AlgHom.mem_equalizer,
    AlgHom.coe_toRingHom, AlgHom.id_apply]

end Equalizer

section Subalgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

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

end Matrix.GeneralLinearGroup

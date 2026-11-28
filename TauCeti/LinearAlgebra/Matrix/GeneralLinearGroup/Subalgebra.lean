/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedSubgroup
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Invertible matrices over subalgebras

An invertible matrix over a commutative algebra comes from a subalgebra exactly when its entries
and those of its inverse lie in that subalgebra. This distinguishes invertibility over the
subalgebra from invertibility over the ambient algebra. Such a matrix carries the vectors with
entries in the subalgebra onto themselves, and membership in the image of a subgroup cut out by a
condition on the entries is again a condition on the entries.

For the equalizer of an algebra endomorphism with the identity, the inverse-entry condition follows
from the entry condition: an entrywise map is a group homomorphism, so it fixes the inverse of every
matrix it fixes. Thus the general linear group over that equalizer maps onto the fixed subgroup of
the endomorphism. These characteristic-free statements apply in particular to Frobenius
endomorphisms of algebras over finite fields, including the zero ring.

## Main results

* `Matrix.GeneralLinearGroup.mem_range_map_val_iff`: descent to a subalgebra is equivalent to
  membership of the entries of the matrix and its inverse.
* `Matrix.GeneralLinearGroup.forall_mulVec_mem_iff`: a matrix coming from the subalgebra carries a
  vector to a vector with entries in the subalgebra exactly when the vector has entries in it.
* `Matrix.GeneralLinearGroup.mem_map_map_val_iff`: entrywise membership in the image of a subgroup
  of the general linear group over the subalgebra.
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
  have hS (a : A) : a ∈ (S.val : ↥S →+* A).range ↔ a ∈ S :=
    ⟨fun ⟨b, hb⟩ ↦ hb ▸ b.property, fun h ↦ ⟨⟨a, h⟩, rfl⟩⟩
  simpa only [MonoidHom.mem_range, hS] using
    mem_range_map_iff_of_injective (n := ι) (f := (S.val : ↥S →+* A)) Subtype.val_injective (g := g)

/-- **Matrices over a subalgebra preserve the vectors over it.** For `g` coming from the
subalgebra `S`, the vector `g v` has its entries in `S` exactly when `v` does, as the entries of
`g` and of `g⁻¹` lie in `S`. -/
theorem forall_mulVec_mem_iff {S : Subalgebra R A} {g : Matrix.GeneralLinearGroup ι A}
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := ι) (S.val : ↥S →+* A)).range) {v : ι → A} :
    (∀ i, ((g : Matrix ι ι A) *ᵥ v) i ∈ S) ↔ ∀ i, v i ∈ S := by
  -- A matrix with entries in `S` carries vectors over `S` to vectors over `S`.
  have key {M : Matrix ι ι A} (hM : ∀ i j, M i j ∈ S) {w : ι → A} (hw : ∀ i, w i ∈ S) (i : ι) :
      (M *ᵥ w) i ∈ S :=
    Subalgebra.sum_mem _ fun j _ ↦ Subalgebra.mul_mem _ (hM i j) (hw j)
  obtain ⟨hg, hg'⟩ := (MonoidHom.mem_range.trans (mem_range_map_val_iff S g)).1 hg
  refine ⟨fun h i ↦ ?_, fun h ↦ key hg h⟩
  have h' := key hg' h i
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] at h'

/-- **Entrywise membership in the image of a subgroup** `H` of the general linear group over a
subalgebra `S`, when membership in `H` is a condition `P` on the matrix entries: entries and
inverse entries in `S`, and `P` for the matrix of entries viewed in `S`. -/
theorem mem_map_map_val_iff {S : Subalgebra R A} {H : Subgroup (Matrix.GeneralLinearGroup ι S)}
    {P : Matrix ι ι S → Prop} (hH : ∀ h, h ∈ H ↔ P h) {g : Matrix.GeneralLinearGroup ι A} :
    g ∈ H.map (Matrix.GeneralLinearGroup.map (n := ι) (S.val : ↥S →+* A)) ↔
      ∃ (hg : ∀ i j, (g : Matrix ι ι A) i j ∈ S),
        (∀ i j, ((g⁻¹ : Matrix.GeneralLinearGroup ι A) : Matrix ι ι A) i j ∈ S) ∧
          P (Matrix.of fun i j ↦ ⟨_, hg i j⟩) := by
  -- Reading the entries of the image of `h ∈ GL_n(S)` back in `S` recovers `h`.
  have hof (h : Matrix.GeneralLinearGroup ι S)
      (hh : ∀ i j, (Matrix.GeneralLinearGroup.map (S.val : ↥S →+* A) h : Matrix ι ι A) i j ∈ S) :
      (Matrix.of fun i j ↦ (⟨_, hh i j⟩ : S)) = h :=
    Matrix.ext fun i j ↦ Subtype.ext (Matrix.GeneralLinearGroup.map_apply _ i j h)
  rw [Subgroup.mem_map]
  refine ⟨?_, fun ⟨hg, hg', h⟩ ↦ ?_⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.map_apply]
      exact ((g : Matrix ι ι S) i j).property
    · rw [← map_inv, Matrix.GeneralLinearGroup.map_apply]
      exact (((g⁻¹ : Matrix.GeneralLinearGroup ι S) : Matrix ι ι S) i j).property
    · rw [hof]
      exact (hH g).mp hg
  · obtain ⟨g, rfl⟩ := (mem_range_map_val_iff S g).2 ⟨hg, hg'⟩
    rw [hof] at h
    exact ⟨g, (hH g).mpr h, rfl⟩

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

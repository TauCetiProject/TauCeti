/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.Fintype
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Root enumerations

Let `f` be a polynomial over a commutative ring `R` and let `L` be an `R`-algebra that is a domain.
A family `x : ι → L` indexed by a finite type is a *root enumeration* of `f` when it lists the
roots of `f` in `L` with multiplicity: the multiset of roots of the image of `f` in `L[X]` is the
image of `x`.

Resolvents, discriminants and the elementary symmetric functions of the roots are all computed
from such a listing, and two facts are implicit whenever the roots are indexed by a finite set of
the size of the degree. Both are stated here.

* *Splitting.* If `ι` has at least as many elements as the degree of the image of `f` in `L`
  (in particular, if it has at least `f.natDegree` elements), then `f` splits in `L`. The finite
  indexing is not available before this: a listing of all roots of a polynomial that does not
  split in `L` has fewer entries than its degree.
* *Separability.* When `L` is a field and the image of `f` in `L` is nonzero, such an enumeration
  is injective if and only if the image of `f` in `L` is separable; over a base field `K`, for a
  nonzero `f`, this is the separability of `f` itself. Without separability a listing repeats a
  root, and a permutation of the indices is then no longer determined by the permutation of the
  roots that it induces.

Conversely, a polynomial that splits in `L` has a root enumeration indexed by any finite type
whose size is the degree of the image of `f` in `L`. Reading Vieta's formulas through an
enumeration expresses the elementary symmetric polynomials evaluated at `x` through the
coefficients of `f`.

## Main definitions

* `Polynomial.IsRootEnumeration f x`: `x` lists the roots of `f` in `L`, with multiplicity.

## Main results

* `Polynomial.IsRootEnumeration.splits`: an enumeration with at least as many entries as the
  degree of the image of `f` in `L` makes `f` split in `L`.
* `Polynomial.exists_isRootEnumeration_iff_splits`: a polynomial has an enumeration indexed by a
  type whose size is the degree of its image in `L` if and only if it splits in `L`.
* `Polynomial.IsRootEnumeration.injective_iff_separable_map`: an enumeration in a field `E` with
  as many entries as the degree of the nonzero image of `f` in `E` is injective if and only if
  that image is separable.
* `Polynomial.IsRootEnumeration.injective_iff_separable`: over a base field, an enumeration of
  the roots of a nonzero `g` with `g.natDegree` entries is injective if and only if `g` is
  separable.
* `Polynomial.IsRootEnumeration.range_eq_rootSet`: the entries of an enumeration are the roots.
* `Polynomial.IsRootEnumeration.aeval_esymm_eq_coeff`: Vieta's formulas, read through an
  enumeration of the roots of a monic polynomial.
-/

public section

open Finset

namespace Polynomial

variable {R L M ι κ : Type*} [CommRing R] [CommRing L] [IsDomain L] [Algebra R L]
  [Fintype ι] [Fintype κ]

/-- `x` is a **root enumeration** of `f` in `L`: it lists the roots of `f` in `L` with
multiplicity, so that the multiset of roots of the image of `f` in `L[X]` is the image of `x`. -/
def IsRootEnumeration (f : R[X]) (x : ι → L) : Prop :=
  (f.map (algebraMap R L)).roots = univ.val.map x

variable {f : R[X]} {x : ι → L}

/-- The defining property of a root enumeration. -/
theorem isRootEnumeration_iff : IsRootEnumeration f x ↔
    (f.map (algebraMap R L)).roots = univ.val.map x :=
  Iff.rfl

/-- Reindexing an enumeration along a bijection gives an enumeration. -/
@[simp]
theorem isRootEnumeration_comp_equiv_iff (e : κ ≃ ι) :
    IsRootEnumeration f (x ∘ e) ↔ IsRootEnumeration f x := by
  rw [isRootEnumeration_iff, isRootEnumeration_iff, ← Multiset.map_map,
    Multiset.map_univ_val_equiv]

namespace IsRootEnumeration

/-- The number of entries of an enumeration is the number of roots of `f` in `L`. -/
theorem card_roots (hx : IsRootEnumeration f x) :
    Multiset.card (f.map (algebraMap R L)).roots = Fintype.card ι := by
  rw [isRootEnumeration_iff.mp hx, Multiset.card_map, card_val, card_univ]

/-- An enumeration has at most `f.natDegree` entries. -/
theorem card_le_natDegree (hx : IsRootEnumeration f x) : Fintype.card ι ≤ f.natDegree :=
  hx.card_roots ▸ (card_roots' _).trans natDegree_map_le

/-- The entries of an enumeration are exactly the roots of `f` in `L`. -/
theorem range_eq_rootSet (hx : IsRootEnumeration f x) : Set.range x = f.rootSet L := by
  ext a
  rw [mem_rootSet', ← mem_aroots', aroots_def, isRootEnumeration_iff.mp hx]
  simp

/-- An enumeration with at least as many entries as the degree of the image of `f` in `L` has
exactly that many entries, since the number of roots never exceeds the degree. This applies in
particular when the enumeration has at least `f.natDegree` entries, by `natDegree_map_le`. -/
theorem natDegree_map_eq_card (hx : IsRootEnumeration f x)
    (hdeg : (f.map (algebraMap R L)).natDegree ≤ Fintype.card ι) :
    (f.map (algebraMap R L)).natDegree = Fintype.card ι :=
  le_antisymm hdeg (hx.card_roots ▸ card_roots' _)

/-- **An enumeration forces splitting.** If `x` enumerates the roots of `f` in `L` and has at
least as many entries as the degree of the image of `f` in `L` (for instance, at least
`f.natDegree` entries), then `f` splits in `L`. -/
theorem splits (hx : IsRootEnumeration f x)
    (hdeg : (f.map (algebraMap R L)).natDegree ≤ Fintype.card ι) :
    (f.map (algebraMap R L)).Splits :=
  splits_iff_card_roots.mpr (hx.card_roots.trans (hx.natDegree_map_eq_card hdeg).symm)

/-- An enumeration with at least as many entries as the degree of the image of `f` in `L` is
carried by an injective algebra morphism to an enumeration in the target. -/
theorem map [CommRing M] [IsDomain M] [Algebra R M] (hx : IsRootEnumeration f x)
    (hdeg : (f.map (algebraMap R L)).natDegree ≤ Fintype.card ι) (φ : L →ₐ[R] M)
    (hφ : Function.Injective φ) :
    IsRootEnumeration f (φ ∘ x) := by
  rw [isRootEnumeration_iff, ← φ.comp_algebraMap, ← Polynomial.map_map,
    (hx.splits hdeg).roots_map_of_injective (i := (φ : L →+* M)) hφ, isRootEnumeration_iff.mp hx,
    Multiset.map_map, RingHom.coe_coe]

end IsRootEnumeration

/-- **Root enumerations exist exactly for split polynomials.** If the image of `f` in `L` has
degree `Fintype.card ι`, then `f` has a root enumeration in `L` indexed by `ι` if and only if `f`
splits in `L`. -/
theorem exists_isRootEnumeration_iff_splits
    (hdeg : (f.map (algebraMap R L)).natDegree = Fintype.card ι) :
    (∃ x : ι → L, IsRootEnumeration f x) ↔ (f.map (algebraMap R L)).Splits := by
  classical
  refine ⟨fun ⟨x, hx⟩ ↦ splits_iff_card_roots.mpr (hx.card_roots.trans hdeg.symm), fun hs ↦ ?_⟩
  have hcard : Fintype.card ι = Fintype.card (f.map (algebraMap R L)).roots.ToType := by
    rw [Multiset.card_coe, ← hdeg, hs.natDegree_eq_card_roots]
  let e := Fintype.equivOfCardEq hcard
  refine ⟨fun i ↦ (e i : L), ?_⟩
  have h := Multiset.map_univ_coe (f.map (algebraMap R L)).roots
  rw [← Multiset.map_univ_val_equiv e, Multiset.map_map] at h
  exact h.symm

namespace IsRootEnumeration

/-- **Vieta's formulas, read through a root enumeration.** If `x` enumerates the roots in `L` of
the monic polynomial `f` of degree `Fintype.card ι`, then for every `k ≤ Fintype.card ι` the
`k`-th elementary symmetric polynomial evaluated at `x` is `(-1) ^ k` times the coefficient of `f`
in degree `Fintype.card ι - k`. -/
theorem aeval_esymm_eq_coeff (hx : IsRootEnumeration f x) (hf : f.Monic)
    (hdeg : f.natDegree ≤ Fintype.card ι) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    MvPolynomial.aeval x (MvPolynomial.esymm ι R k) =
      (-1) ^ k * algebraMap R L (f.coeff (Fintype.card ι - k)) := by
  set g := f.map (algebraMap R L)
  have hdegg : g.natDegree = Fintype.card ι :=
    hx.natDegree_map_eq_card (natDegree_map_le.trans hdeg)
  have hvieta := coeff_eq_esymm_roots_of_card (hx.card_roots.trans hdegg.symm)
    (k := Fintype.card ι - k) (hdegg ▸ Nat.sub_le _ _)
  rw [(hf.map (algebraMap R L)).leadingCoeff, one_mul, hdegg, Nat.sub_sub_self hk,
    isRootEnumeration_iff.mp hx, coeff_map] at hvieta
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, hvieta]
  simp [← mul_assoc, ← mul_pow]

end IsRootEnumeration

section Field

variable {K E : Type*} [Field K] [Field E] [Algebra R E] [Algebra K E] {y : ι → E}

namespace IsRootEnumeration

/-- **An enumeration is injective exactly when the polynomial is separable.** If `y` enumerates
the roots in the field `E` of a polynomial `f` whose image in `E` is nonzero, and has at least as
many entries as the degree of that image, then `y` is injective if and only if the image of `f` in
`E` is separable. -/
theorem injective_iff_separable_map (hy : IsRootEnumeration f y)
    (hdeg : (f.map (algebraMap R E)).natDegree ≤ Fintype.card ι)
    (hf : f.map (algebraMap R E) ≠ 0) :
    Function.Injective y ↔ (f.map (algebraMap R E)).Separable := by
  rw [← nodup_roots_iff_of_splits hf (hy.splits hdeg), isRootEnumeration_iff.mp hy,
    Multiset.nodup_map_iff_inj_on univ.nodup]
  simp [Function.Injective]

/-- **An enumeration is injective exactly when the polynomial is separable**, over a base field:
if `y` enumerates the roots of the nonzero polynomial `g` over `K` and has at least `g.natDegree`
entries, then `y` is injective if and only if `g` is separable. -/
theorem injective_iff_separable {g : K[X]} (hy : IsRootEnumeration g y)
    (hdeg : g.natDegree ≤ Fintype.card ι) (hg : g ≠ 0) :
    Function.Injective y ↔ g.Separable := by
  rw [hy.injective_iff_separable_map (natDegree_map_le.trans hdeg) (map_ne_zero hg), separable_map]

end IsRootEnumeration

end Field

end Polynomial

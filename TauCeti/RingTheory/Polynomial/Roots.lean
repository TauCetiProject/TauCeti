/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.UnionInter
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable

/-!
# Root sets and multiplicities

This file records several facts about the roots of a polynomial, either in its coefficient field
or after base change to a domain `E`.

First, an explicit numbering of the root set of a separable polynomial enumerates its full root
multiset: separability makes the roots simple, so the multiset is the image of the numbering.
This lets root-product formulas be expressed as finite products indexed by `Fin f.natDegree`,
without choosing a global order on the root set.

Second, the root set of a product of polynomials whose base changes to `E` are nonzero is the
union of the root sets of the factors. This is the lemma that decomposes the roots of a
polynomial along a factorisation, for instance the roots of a monic integer polynomial along its
monic irreducible factors. The same holds for the distinct roots of a finite product.

Third, dividing a polynomial by the linear factor of a simple root removes exactly that root
from the root set. Here `a` only has to be a simple root in `E`: `f a` vanishes and `f' a` does
not vanish after mapping to `E`, so the map `F → E` need not be injective.

Fourth, translating the variable moves the roots: the roots of `f(X + t)` are the points `x`
with `x + t` a root of `f`, so `x ↦ x + t` is a bijection between the two root sets, and
`f(X + t)` is separable exactly when `f` is.

Fifth, if every root of a nonzero polynomial is among a family of points `θ i`, then its roots
are exactly the `θ i` in which it has positive multiplicity.

Finally, the roots of a polynomial gcd form the multiset intersection of the roots of its
inputs. In characteristic zero this identifies the degree lost to the gcd with the derivative as
the number of distinct roots.

## Main results

* `Polynomial.Separable.roots_map_eq_map_numbering`: for a separable polynomial, a numbering of
  its root set enumerates its full root multiset after base change.
* `Polynomial.rootSet_mul`: the root set of a product of polynomials whose base changes to `E` are
  nonzero is the union of the root sets of the factors.
* `Polynomial.aroots_prod_toFinset`: the distinct roots of a finite product of polynomials whose
  base changes to `E` are nonzero are those of the factors together.
* `Polynomial.rootSet_divByMonic_X_sub_C`: if `f a = 0` and `f' a ≠ 0` in `E`, then the roots of
  `f /ₘ (X - C a)` are the roots of `f` other than `a`.
* `Polynomial.rootSet_comp_X_add_C`: the roots of `f(X + t)` are the roots of `f` moved by `-t`.
* `Polynomial.rootSetCompXAddCEquiv`: the bijection `x ↦ x + t` from the roots of `f(X + t)` to
  the roots of `f`.
* `Polynomial.separable_comp_X_add_C_iff`: `f(X + t)` is separable exactly when `f` is.
* `Polynomial.isRoot_iff_of_rootMultiplicity`: if every root of a nonzero polynomial is among
  the `θ i`, then its roots are the `θ i` in which it has positive multiplicity.
* `Polynomial.rootMultiplicity_gcd`: a root's multiplicity in a gcd is the minimum of its
  multiplicities in the two inputs.
* `Polynomial.natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset`: over an
  algebraically closed field of characteristic zero, degree minus the degree of the derivative
  gcd counts distinct roots.
-/

public section

namespace TauCeti

open Finset Polynomial

variable {F : Type*} [CommRing F] {E : Type*} [CommRing E] [IsDomain E] [Algebra F E] {f : F[X]}

/-- A numbering of the root set of a separable polynomial enumerates the whole root multiset:
separability makes the roots simple, so the multiset is the image of the numbering. -/
theorem _root_.Polynomial.Separable.roots_map_eq_map_numbering (hsep : f.Separable)
    (e : Fin f.natDegree ≃ f.rootSet E) :
    (f.map (algebraMap F E)).roots = Multiset.map (fun i ↦ ((e i : E))) univ.val := by
  have hmem : ∀ {a : E}, a ∈ (f.map (algebraMap F E)).roots ↔ a ∈ f.rootSet E := fun {_} ↦
    Polynomial.mem_aroots'.trans Polynomial.mem_rootSet'.symm
  refine (Multiset.Nodup.ext (nodup_roots hsep.map) ?_).mpr ?_
  · exact univ.nodup.map fun i j h ↦ e.injective (Subtype.ext h)
  · intro a
    simp only [Multiset.mem_map, Finset.mem_val, mem_univ, true_and]
    exact ⟨fun ha ↦ ⟨e.symm ⟨a, hmem.mp ha⟩, by simp⟩, fun ⟨i, hi⟩ ↦ hi ▸ hmem.mpr (e i).2⟩

/-- The root set of a product of polynomials is the union of the root sets of the factors,
provided neither factor vanishes after base change to `E`. -/
@[simp]
theorem _root_.Polynomial.rootSet_mul {g : F[X]} (hf : f.map (algebraMap F E) ≠ 0)
    (hg : g.map (algebraMap F E) ≠ 0) : (f * g).rootSet E = f.rootSet E ∪ g.rootSet E := by
  ext x
  simp only [Set.mem_union, mem_rootSet', Polynomial.map_mul, map_mul, mul_eq_zero, ne_eq, hf, hg,
    or_self, not_false_eq_true, true_and]

/-- The distinct roots in `E` of a finite product of polynomials are those of the factors together,
provided no factor vanishes after base change to `E`. -/
theorem _root_.Polynomial.aroots_prod_toFinset [DecidableEq E] {ι : Type*} (s : Finset ι)
    (f : ι → F[X]) (hf : ∀ k ∈ s, (f k).map (algebraMap F E) ≠ 0) :
    ((∏ k ∈ s, f k).aroots E).toFinset = s.biUnion fun k ↦ ((f k).aroots E).toFinset := by
  ext z
  simp only [Multiset.mem_toFinset, Finset.mem_biUnion, mem_aroots', Polynomial.map_prod,
    Finset.prod_ne_zero_iff.2 hf, ne_eq, not_false_eq_true, true_and, map_prod,
    Finset.prod_eq_zero_iff]
  exact ⟨fun ⟨k, hk, h⟩ ↦ ⟨k, hk, hf k hk, h⟩, fun ⟨k, hk, _, h⟩ ↦ ⟨k, hk, h⟩⟩

/-- Removing the linear factor of a simple root `a` removes exactly that root: if, in `E`, `f a`
vanishes and `f' a` does not, then the roots of `f /ₘ (X - C a)` in `E` are the roots of `f`
other than `a`. -/
@[simp]
theorem _root_.Polynomial.rootSet_divByMonic_X_sub_C {a : F} (ha : algebraMap F E (f.eval a) = 0)
    (ha' : algebraMap F E (f.derivative.eval a) ≠ 0) :
    (f /ₘ (X - C a)).rootSet E = f.rootSet E \ {algebraMap F E a} := by
  -- `a` is not a root of the quotient in `E`: the quotient takes the value `f' a` there.
  have hq := congrArg (eval a) (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f a)
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at hq
  have hq0 : aeval (algebraMap F E a) (f /ₘ (X - C a)) ≠ 0 := by
    rwa [aeval_algebraMap_apply_eq_algebraMap_eval, hq]
  -- In `E`, `f = (X - C a) * (f /ₘ (X - C a))`, since the remainder `f a` vanishes there.
  have hmap : ((X - C a) * (f /ₘ (X - C a))).map (algebraMap F E) = f.map (algebraMap F E) := by
    rw [X_sub_C_mul_divByMonic_eq_sub_modByMonic, modByMonic_X_sub_C_eq_C_eval,
      Polynomial.map_sub, map_C, ha, C_0, sub_zero]
  -- So the roots of `f` are those of the two factors.
  have hsplit : f.rootSet E = (X - C a).rootSet E ∪ (f /ₘ (X - C a)).rootSet E := by
    rw [← rootSet_map E E f, ← hmap, rootSet_map, rootSet_mul ((monic_X_sub_C a).map _).ne_zero
      fun h ↦ hq0 (by rw [← eval_map_algebraMap, h, eval_zero])]
  -- The linear factor contributes only `a`, which is not a root of the quotient.
  ext x
  rw [hsplit]
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff, (monic_X_sub_C a).mem_rootSet,
    map_sub, aeval_X, aeval_C, sub_eq_zero]
  constructor
  · exact fun hx ↦ ⟨Or.inr hx, fun hxa ↦ hq0 (hxa ▸ aeval_eq_zero_of_mem_rootSet hx)⟩
  · rintro ⟨hxa | hx, hxa'⟩
    · exact absurd hxa hxa'
    · exact hx

/-- The roots of `f(X + t)` are the points `x` with `x + t` a root of `f`. -/
theorem _root_.Polynomial.rootSet_comp_X_add_C (f : F[X]) (t : F) :
    (f.comp (X + C t)).rootSet E = (· + algebraMap F E t) ⁻¹' f.rootSet E := by
  ext x
  simp [mem_rootSet', Polynomial.map_comp, comp_X_add_C_ne_zero_iff, aeval_comp]

/-- The bijection `x ↦ x + t` from the roots of `f(X + t)` to the roots of `f`. -/
def _root_.Polynomial.rootSetCompXAddCEquiv (f : F[X]) (t : F) (E : Type*) [CommRing E]
    [IsDomain E] [Algebra F E] :
    (f.comp (X + C t)).rootSet E ≃ f.rootSet E :=
  (Equiv.addRight (algebraMap F E t)).subtypeEquiv fun x => by
    rw [rootSet_comp_X_add_C, Set.mem_preimage, Equiv.coe_addRight]

/-- The bijection `Polynomial.rootSetCompXAddCEquiv` adds `t`. -/
@[simp]
theorem _root_.Polynomial.coe_rootSetCompXAddCEquiv_apply (f : F[X]) (t : F)
    (x : (f.comp (X + C t)).rootSet E) :
    (rootSetCompXAddCEquiv f t E x : E) = x + algebraMap F E t :=
  (rfl)

/-- The inverse of `Polynomial.rootSetCompXAddCEquiv` subtracts `t`. -/
@[simp]
theorem _root_.Polynomial.coe_rootSetCompXAddCEquiv_symm_apply (f : F[X]) (t : F)
    (x : f.rootSet E) :
    ((rootSetCompXAddCEquiv f t E).symm x : E) = x - algebraMap F E t := by
  obtain ⟨y, rfl⟩ := (rootSetCompXAddCEquiv f t E).surjective x
  simp

/-- Translating the variable preserves separability. -/
theorem _root_.Polynomial.Separable.comp_X_add_C (hf : f.Separable) (t : F) :
    (f.comp (X + C t)).Separable := by
  rw [Separable, derivative_comp, derivative_X_add_C, one_mul]
  exact IsCoprime.map hf (compRingHom (X + C t))

/-- `f(X + t)` is separable exactly when `f` is. -/
@[simp]
theorem _root_.Polynomial.separable_comp_X_add_C_iff {t : F} :
    (f.comp (X + C t)).Separable ↔ f.Separable := by
  refine ⟨fun h => ?_, fun h => h.comp_X_add_C t⟩
  simpa [comp_assoc, add_assoc] using h.comp_X_add_C (-t)

/-- If every root of a nonzero polynomial `p` is some `θ i`, and the multiplicity of each `θ i`
as a root of `p` is `m i`, then the roots of `p` are the `θ i` with `0 < m i`. -/
theorem _root_.Polynomial.isRoot_iff_of_rootMultiplicity {ι : Type*} {p : F[X]} {θ : ι → F}
    {m : ι → ℕ} (hm : ∀ i, p.rootMultiplicity (θ i) = m i)
    (hθ : ∀ t, p.IsRoot t → ∃ i, θ i = t) (hp : p ≠ 0) (t : F) :
    p.IsRoot t ↔ ∃ i, θ i = t ∧ 0 < m i := by
  refine ⟨fun ht ↦ ?_, fun ⟨i, hi, hpos⟩ ↦ ?_⟩
  · obtain ⟨i, rfl⟩ := hθ t ht
    exact ⟨i, rfl, hm i ▸ (rootMultiplicity_pos hp).2 ht⟩
  · rw [← hi, ← rootMultiplicity_pos hp, hm i]
    exact hpos

section GCD

variable {K : Type*} [Field K] [DecidableEq K]

/-- The multiplicity of a root in the gcd of two nonzero polynomials is the minimum of its
multiplicities in the two polynomials. -/
theorem _root_.Polynomial.rootMultiplicity_gcd (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (x : K) :
    (EuclideanDomain.gcd p q).rootMultiplicity x =
      min (p.rootMultiplicity x) (q.rootMultiplicity x) := by
  have hg : EuclideanDomain.gcd p q ≠ 0 := by
    intro h
    exact hp (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  apply le_antisymm
  · exact le_min
      (rootMultiplicity_le_rootMultiplicity_of_dvd hp (EuclideanDomain.gcd_dvd_left p q) x)
      (rootMultiplicity_le_rootMultiplicity_of_dvd hq (EuclideanDomain.gcd_dvd_right p q) x)
  · rw [le_rootMultiplicity_iff hg]
    apply EuclideanDomain.dvd_gcd
    · exact (le_rootMultiplicity_iff hp).mp (min_le_left _ _)
    · exact (le_rootMultiplicity_iff hq).mp (min_le_right _ _)

/-- The roots of the gcd of two nonzero polynomials are the multiset intersection of their roots.
Thus a common root occurs with the minimum of its two input multiplicities. -/
theorem _root_.Polynomial.roots_gcd (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    (EuclideanDomain.gcd p q).roots = p.roots ∩ q.roots := by
  ext x
  simp [count_roots, rootMultiplicity_gcd p q hp hq]

section CharZero

variable [CharZero K]

/-- In characteristic zero, the roots of a polynomial's derivative gcd, together with one copy
of each distinct root, recover all roots with multiplicity. -/
theorem _root_.Polynomial.roots_gcd_derivative_add_dedup (p : K[X]) :
    (EuclideanDomain.gcd p p.derivative).roots + p.roots.dedup = p.roots := by
  by_cases hdeg : p.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdeg, roots_C, Multiset.dedup_zero, add_zero]
    simp
  · have hp : p ≠ 0 := fun h ↦ hdeg (h ▸ natDegree_zero)
    have hd : p.derivative ≠ 0 := derivative_ne_zero.mpr hdeg
    ext x
    rw [Multiset.count_add, count_roots, rootMultiplicity_gcd p p.derivative hp hd,
      count_roots]
    by_cases hx : p.IsRoot x
    · rw [derivative_rootMultiplicity_of_root hx]
      have hm : 0 < p.rootMultiplicity x := (rootMultiplicity_pos hp).mpr hx
      rw [Multiset.count_dedup, ite_eq_left ((mem_roots hp).mpr hx)]
      omega
    · have hm : p.rootMultiplicity x = 0 := rootMultiplicity_eq_zero hx
      have hmem : x ∉ p.roots := fun h => hx ((mem_roots hp).mp h)
      rw [hm, zero_min, Multiset.count_dedup, ite_eq_right hmem]

/-- For a split polynomial in characteristic zero, the number of distinct roots of a nonzero
polynomial is its degree minus the degree of its gcd with its derivative. -/
theorem _root_.Polynomial.natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset_of_splits
    {p : K[X]} (hp : p ≠ 0) (hsplit : p.Splits) :
    p.natDegree - (EuclideanDomain.gcd p p.derivative).natDegree = p.roots.toFinset.card := by
  by_cases hdeg : p.natDegree = 0
  · have hpC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
    rw [hdeg, hpC, roots_C]
    simp
  · have hsplitg : (EuclideanDomain.gcd p p.derivative).Splits :=
      hsplit.of_dvd hp (EuclideanDomain.gcd_dvd_left p p.derivative)
    have hcard := congrArg Multiset.card (roots_gcd_derivative_add_dedup p)
    rw [Multiset.card_add] at hcard
    rw [hsplit.natDegree_eq_card_roots, hsplitg.natDegree_eq_card_roots,
      Multiset.card_toFinset]
    omega

end CharZero

section IsAlgClosed

variable [CharZero K] [IsAlgClosed K]

/-- Over an algebraically closed field of characteristic zero, the number of distinct roots of a
nonzero polynomial is its degree minus the degree of its gcd with its derivative. -/
theorem _root_.Polynomial.natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset
    {p : K[X]} (hp : p ≠ 0) :
    p.natDegree - (EuclideanDomain.gcd p p.derivative).natDegree = p.roots.toFinset.card :=
  natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset_of_splits hp
    (IsAlgClosed.splits p)

end IsAlgClosed

end GCD

end TauCeti

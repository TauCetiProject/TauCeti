/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PushoutI.Reduced
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers of elements of a factor of an amalgamated product

Let `φ i : H →* G i` be a family of injective group homomorphisms, with amalgamated product
`Monoid.PushoutI φ`. If an element `g` of a factor `G i` is not conjugate in `G i` into the
amalgamated subgroup `φ i H`, then every element of the amalgamated product commuting with `g`
lies in `G i`: the centralizer of `g` in the amalgamated product is its centralizer in `G i`.
In the action of the amalgamated product on its Bass–Serre tree, such a `g` fixes the vertex
`G i` and no edge at it, so it fixes no other vertex, and an element commuting with `g`
preserves its fixed point set.

## Main results

* `Monoid.PushoutI.centralizer_of_eq_map`: the centralizer of an element of a factor that is not
  conjugate in that factor into the amalgamated subgroup.

## Implementation notes

The proof uses normal forms rather than the Bass–Serre tree: write an element `x` commuting with
`g` as `a * w` with `a ∈ G i` and `w` a reduced word not starting in `G i`
(`Monoid.PushoutI.exists_eq_of_mul_list_prod`). If `w` is nonempty, then
`x⁻¹ * g * x = w⁻¹ * (a⁻¹ * g * a) * w` lies in no factor
(`Monoid.PushoutI.list_prod_inv_mul_of_mul_list_prod_notMem_range_of`), but it equals `g`.

## References

* W. Magnus, A. Karrass, D. Solitar, *Combinatorial group theory*, Theorem 4.5 (commuting
  elements of an amalgamated product), as used in G. Baumslag, A. Myasnikov, V. Remeslennikov,
  *Algebraic geometry over groups I: Algebraic sets and ideal theory*, J. Algebra 219 (1999),
  proof of Theorem A2.
* J.-P. Serre, *Trees*, Chapter I, §1.2, Theorem 1 (the normal form theorem).
-/

public section

namespace Monoid.PushoutI

open Function Subgroup

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **Centralizers of factor elements away from the amalgamated subgroup.** If an element `g` of
a factor `G i` of an amalgamated product of groups is not conjugate in `G i` into the amalgamated
subgroup, then its centralizer in the amalgamated product is its centralizer in `G i`. -/
theorem centralizer_of_eq_map (hφ : ∀ i, Injective (φ i)) {i : ι} {g : G i}
    (hg : ∀ k : G i, k * g * k⁻¹ ∉ (φ i).range) :
    centralizer {of (φ := φ) i g} = (centralizer {g}).map (of i) := by
  refine le_antisymm (fun x hx => ?_) (map_le_iff_le_comap.2 fun k hk => ?_)
  · obtain ⟨a, L, hc, hred, hhead, rfl⟩ := exists_eq_of_mul_list_prod i x
    have hx' : (of (φ := φ) i a * (L.map fun l => of l.1 l.2).prod)⁻¹ * of i g *
        (of i a * (L.map fun l => of l.1 l.2).prod) = of i g := by
      rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hx, inv_mul_cancel_left]
    rcases eq_or_ne L [] with rfl | hL
    · refine ⟨a, mem_centralizer_singleton_iff.2 (of_injective hφ i ?_), by simp⟩
      simpa using (mem_centralizer_singleton_iff.1 hx).eq
    · -- Otherwise `x⁻¹ * g * x` is a reduced word of length at least three.
      refine (list_prod_inv_mul_of_mul_list_prod_notMem_range_of hφ hL hc hred (hg a⁻¹) hhead
        ⟨g, ?_⟩).elim
      rw [← hx']
      simp [mul_assoc]
  · rw [mem_comap, mem_centralizer_singleton_iff, commute_iff_eq, ← map_mul, ← map_mul,
      (mem_centralizer_singleton_iff.1 hk).eq]

end Monoid.PushoutI

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.BacktrackRelator
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Grading

/-!
# The Koszul complex of a vertex module of a preprojective algebra

Let `Q` be a finite quiver and `Π = Π_k(Q)` its preprojective algebra over a commutative ring `k`.
For a vertex `v`, the right ideal `e_v Π` is the projective right `Π`-module at `v`, spanned by the
classes of the paths of the doubled quiver ending at `v`. The vertex augmentation module `S_v` at
`v` is its quotient by its part of positive degree, a copy of `k` on which every arrow acts by zero;
it is the simple right module at `v` when `k` is a field. The Koszul complex of `S_v` is

```text
0 ⟶ e_v Π ⟶ ⨁_{b : i ⟶ v} e_i Π ⟶ e_v Π ⟶ S_v ⟶ 0,
       y ↦ (ε_b b* y)_b,   (z_b) ↦ ∑_b b z_b,
```

the sum running over the arrows `b` of the doubled quiver `Quiver.Symmetrify Q` into `v`, with
`b*` the formal reverse of `b` and `ε_b = 1` when `b` is an arrow of `Q` and `-1` when it is the
reverse of one (`TauCeti.doubledArrowSign`). Both maps are left multiplications, so they are maps of
right modules. The signs are those of the local relator: in Tau Ceti's later-factor-first
convention

```text
ρ_v = ∑_{b : i ⟶ v} ε_b b b*
```

(`TauCeti.localPreprojectiveRelator_eq_sum_ofArrow_mul`), which makes the two maps compose to zero.

This file proves that the complex is exact at its two right-hand terms:

* `TauCeti.mem_iSup_preprojectiveGrade_add_one_iff_exists_eq_sum`: an element of `e_v Π` has
  positive degree exactly when it is a sum `∑_b b z_b`, so the right-hand map has image the kernel
  of `e_v Π ⟶ S_v`;
* `TauCeti.sum_preprojectiveMk_ofArrow_mul_eq_zero_iff`: a family `z_b ∈ e_i Π` has `∑_b b z_b = 0`
  exactly when `z_b = ε_b b* y` for one `y ∈ e_v Π`.

These hold for every finite quiver and every commutative ring `k`. What is left is the left-hand
map: the complex is a linear projective resolution of `S_v` exactly when that map is injective,
that is, when the only `y ∈ e_v Π` with `b* y = 0` for every arrow `b` into `v` is `0`. Over a
field, counting dimensions degree by degree, this injectivity in every degree amounts to equality
in the Anick-type inequality `TauCeti.PathAlgebra.sum_card_mul_finrank_map_pathsInto_le_add`.
It fails whenever `Π` is finite-dimensional and nonzero, as for a Dynkin quiver: a nonzero element
of `e_v Π` of top degree is killed by every arrow.

That the two maps compose to zero and exactness at the middle term are the instances, for the signs
`ε_b`, of the results for weighted backtrack relators in
`TauCeti.RepresentationTheory.Quiver.PathAlgebra.BacktrackRelator`.

## Main results

* `TauCeti.sum_preprojectiveMk_ofArrow_mul_doubledArrowSign_smul_eq_zero`: the two maps compose
  to zero.
* `TauCeti.sum_preprojectiveMk_ofArrow_mul_eq_zero_iff`: **exactness at the middle term.**
* `TauCeti.mem_iSup_preprojectiveGrade_add_one_iff_exists_eq_sum`: **exactness at `e_v Π`.**

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3, for this complex and the Koszulity of preprojective
  algebras of non-Dynkin quivers.
* S. Brenner, M. C. R. Butler and A. D. King, *Periodic algebras which are almost Koszul*,
  Algebr. Represent. Theory 5 (2002), for the Dynkin case.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **The Koszul complex is a complex**: the composite `y ↦ ∑_b b (ε_b b* y)` is left
multiplication by the local relator `ρ_v`, which vanishes in the preprojective algebra. -/
theorem sum_preprojectiveMk_ofArrow_mul_doubledArrowSign_smul_eq_zero (v : Q)
    (y : preprojectiveAlgebra k Q) :
    ∑ i : Symmetrify Q, ∑ b : i ⟶ Symmetrify.of.obj v, preprojectiveMk k Q (ofArrow b) *
      (doubledArrowSign k b • (preprojectiveMk k Q (ofArrow (Quiver.reverse b)) * y)) = 0 :=
  sum_map_ofArrow_mul_smul_map_ofArrow_reverse_mul_eq_zero (R := Symmetrify Q) k
    (r := localPreprojectiveRelator k (Q := Q))
    (fun u => localPreprojectiveRelator_eq_sum_ofArrow_mul (Q := Q) k u)
    (fun f => by
      rw [preprojectiveMk_eq_zero_iff, preprojectiveIdeal_eq_span_range_localPreprojectiveRelator]
      -- The two ranges differ only in reading the vertex type `Q` as `Symmetrify Q`.
      exact Iff.rfl)
    (Symmetrify.of.obj (V := Q) v) y

/-- **Exactness of the Koszul complex at its middle term.** Let `z_b ∈ e_i Π` for the arrows
`b : i ⟶ v` of the doubled quiver. Then `∑_b b z_b = 0` exactly when there is one `y ∈ e_v Π` with
`z_b = ε_b b* y` for every `b`. -/
theorem sum_preprojectiveMk_ofArrow_mul_eq_zero_iff (v : Q)
    {z : (i : Symmetrify Q) → (i ⟶ Symmetrify.of.obj v) → preprojectiveAlgebra k Q}
    (hz : ∀ i b, preprojectiveMk k Q (vertexIdempotent k i) * z i b = z i b) :
    ∑ i, ∑ b, preprojectiveMk k Q (ofArrow b) * z i b = 0 ↔
      ∃ y, preprojectiveMk k Q (doubledVertexIdempotent k v) * y = y ∧ ∀ i b,
        z i b = doubledArrowSign k b • (preprojectiveMk k Q (ofArrow (Quiver.reverse b)) * y) := by
  rw [doubledVertexIdempotent_def]
  exact sum_map_ofArrow_mul_eq_zero_iff (R := Symmetrify Q) k
    (r := localPreprojectiveRelator k (Q := Q))
    (fun u => localPreprojectiveRelator_eq_sum_ofArrow_mul (Q := Q) k u)
    (fun f => by
      rw [preprojectiveMk_eq_zero_iff, preprojectiveIdeal_eq_span_range_localPreprojectiveRelator]
      -- The two ranges differ only in reading the vertex type `Q` as `Symmetrify Q`.
      exact Iff.rfl)
    (preprojectiveMk_surjective k Q)
    (Symmetrify.of.obj (V := Q) v) hz

/-- **Exactness of the Koszul complex at `e_v Π`.** An element `x ∈ e_v Π` has positive degree,
so maps to zero in the vertex augmentation module `S_v`, exactly when `x = ∑_b b z_b` for some
`z_b ∈ e_i Π`, the sum over the arrows `b : i ⟶ v` of the doubled quiver. -/
theorem mem_iSup_preprojectiveGrade_add_one_iff_exists_eq_sum (v : Q)
    {x : preprojectiveAlgebra k Q}
    (hx : preprojectiveMk k Q (doubledVertexIdempotent k v) * x = x) :
    x ∈ ⨆ n, preprojectiveGrade k Q (n + 1) ↔
      ∃ z : (i : Symmetrify Q) → (i ⟶ Symmetrify.of.obj v) → preprojectiveAlgebra k Q,
        (∀ i b, preprojectiveMk k Q (vertexIdempotent k i) * z i b = z i b) ∧
          x = ∑ i, ∑ b, preprojectiveMk k Q (ofArrow b) * z i b := by
  refine ⟨fun h => ?_, ?_⟩
  · -- Cut every homogeneous piece of positive degree down to the corner of `v`.
    obtain ⟨z, hz, hxz⟩ : ∃ z : (i : Symmetrify Q) → (i ⟶ Symmetrify.of.obj v) →
        preprojectiveAlgebra k Q,
        (∀ i b, preprojectiveMk k Q (vertexIdempotent k i) * z i b = z i b) ∧
          preprojectiveMk k Q (doubledVertexIdempotent k v) * x =
            ∑ i, ∑ b, preprojectiveMk k Q (ofArrow b) * z i b := by
      refine Submodule.iSup_induction (motive := fun x => ∃ z : (i : Symmetrify Q) →
          (i ⟶ Symmetrify.of.obj v) → preprojectiveAlgebra k Q,
          (∀ i b, preprojectiveMk k Q (vertexIdempotent k i) * z i b = z i b) ∧
            preprojectiveMk k Q (doubledVertexIdempotent k v) * x =
              ∑ i, ∑ b, preprojectiveMk k Q (ofArrow b) * z i b) _ h (fun n x hx' => ?_)
        ⟨0, fun _ _ => mul_zero _, by simp⟩ fun x x' hx hx' => ?_
      · obtain ⟨y, hy, rfl⟩ := (mem_preprojectiveGrade_iff k Q).1 hx'
        obtain ⟨w, hw, hwy⟩ := exists_eq_sum_ofArrow_mul
          (vertexIdempotent_mul_mem_pathsInto (Symmetrify.of.obj v) hy)
        refine ⟨fun i b => preprojectiveMk k Q (w i b), fun i b => ?_, ?_⟩
        · rw [← map_mul, vertexIdempotent_mul_of_mem_pathsInto (hw i b)]
        · rw [← map_mul, doubledVertexIdempotent_def, hwy]
          simp only [map_sum, map_mul]
      · obtain ⟨z, hz, hxz⟩ := hx
        obtain ⟨z', hz', hxz'⟩ := hx'
        refine ⟨z + z', fun i b => ?_, ?_⟩
        · rw [Pi.add_apply, Pi.add_apply, mul_add, hz, hz']
        · simp only [mul_add, hxz, hxz', Pi.add_apply, Finset.sum_add_distrib]
    exact ⟨z, hz, hx.symm.trans hxz⟩
  · rintro ⟨z, -, rfl⟩
    exact sum_mem fun i _ => sum_mem fun b _ => preprojectiveMk_ofArrow_mul_mem_iSup k b (z i b)

end TauCeti

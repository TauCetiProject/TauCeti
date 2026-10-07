/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.RelationIdeal
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

## Main definitions

* `TauCeti.doubledArrowSign`: the sign `ε_b` of an arrow of the doubled quiver.

## Main results

* `TauCeti.localPreprojectiveRelator_eq_sum_ofArrow_mul`: the local relator decomposed along the
  last arrow of its paths.
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

section Sign

variable (k : Type w) {Q : Type u} [One k] [Neg k] [Quiver.{v} Q]

/-- The sign `ε_b` of an arrow `b` of the doubled quiver in the preprojective relator: `1` on an
arrow of `Q` and `-1` on the formal reverse of one. The arrows `i ⟶ j` of `Quiver.Symmetrify Q`
are by definition `(i ⟶ j) ⊕ (j ⟶ i)`. -/
def doubledArrowSign {i j : Symmetrify Q} (b : i ⟶ j) : k :=
  Sum.elim (fun _ => 1) (fun _ => -1) b

/-- An arrow of `Q` has sign `1`. This is the `simp`-normal form, `Symmetrify.of.map a` being
`Sum.inl a` by `Quiver.Symmetrify.of_map`. -/
@[simp]
theorem doubledArrowSign_inl {i j : Q} (a : i ⟶ j) :
    doubledArrowSign k (Sum.inl a : Symmetrify.of.obj i ⟶ Symmetrify.of.obj j) = 1 := (rfl)

/-- The formal reverse of an arrow of `Q` has sign `-1`. This is the `simp`-normal form,
`Quiver.reverse (Sum.inl a)` being `Sum.inr a` by `Quiver.symmetrify_reverse`. -/
@[simp]
theorem doubledArrowSign_inr {i j : Q} (a : j ⟶ i) :
    doubledArrowSign k (Sum.inr a : Symmetrify.of.obj i ⟶ Symmetrify.of.obj j) = -1 := (rfl)

end Sign

section SignReverse

variable (k : Type w) {Q : Type u} [One k] [InvolutiveNeg k] [Quiver.{v} Q]

/-- Swapping the two summands of an arrow of the doubled quiver negates its sign. This is the
`simp`-normal form of `TauCeti.doubledArrowSign_reverse`, `Quiver.reverse b` being `Sum.swap b` by
`Quiver.symmetrify_reverse`. -/
@[simp]
theorem doubledArrowSign_swap {i j : Symmetrify Q} (b : i ⟶ j) :
    doubledArrowSign k (i := j) (j := i) (Sum.swap b) = -doubledArrowSign k b := by
  rcases b with a | a
  · rfl
  · exact (neg_neg (1 : k)).symm

/-- **Reversing an arrow of the doubled quiver negates its sign**: `ε_{b*} = -ε_b`. -/
theorem doubledArrowSign_reverse {i j : Symmetrify Q} (b : i ⟶ j) :
    doubledArrowSign k (Quiver.reverse b) = -doubledArrowSign k b :=
  doubledArrowSign_swap k b

end SignReverse

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **The local relator along the last arrow of its paths**: in the later-factor-first convention
`ρ_v = ∑_{b : i ⟶ v} ε_b b b*`, the sum over the arrows of the doubled quiver into `v`. An arrow `a`
of `Q` into `v` contributes its head backtrack `a a*`, and the reverse `a*` of an arrow `a` of `Q`
out of `v` contributes `-a* a`, minus its tail backtrack. -/
theorem localPreprojectiveRelator_eq_sum_ofArrow_mul (v : Q) :
    localPreprojectiveRelator k v = ∑ i : Symmetrify Q, ∑ b : i ⟶ Symmetrify.of.obj v,
      ofArrow b * (doubledArrowSign k b • ofArrow (Quiver.reverse b)) := by
  rw [localPreprojectiveRelator_def, ← Finset.sum_sub_distrib]
  -- The vertices of the doubled quiver are those of `Q`; at each of them, the arrows into `v` are
  -- the arrows of `Q` into `v` and the reverses of the arrows of `Q` out of `v`.
  refine Fintype.sum_equiv (Equiv.ofBijective _ symmetrify_of_obj_bijective) _ _ fun i => ?_
  rw [Equiv.ofBijective_apply, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  refine Eq.trans ?_ (Fintype.sum_sum_type (α₁ := i ⟶ v) (α₂ := v ⟶ i) _).symm
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    exact (ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem k a).symm.trans
      (congrArg (_ * ·) (one_smul k _).symm)
  · refine Finset.sum_congr rfl fun a _ => ?_
    exact (congrArg Neg.neg (ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem k a)).symm.trans
      ((neg_one_smul k _).symm.trans (mul_smul_comm _ _ _).symm)

/-- **The Koszul complex is a complex**: the composite `y ↦ ∑_b b (ε_b b* y)` is left
multiplication by the local relator `ρ_v`, which vanishes in the preprojective algebra. -/
theorem sum_preprojectiveMk_ofArrow_mul_doubledArrowSign_smul_eq_zero (v : Q)
    (y : preprojectiveAlgebra k Q) :
    ∑ i : Symmetrify Q, ∑ b : i ⟶ Symmetrify.of.obj v, preprojectiveMk k Q (ofArrow b) *
      (doubledArrowSign k b • (preprojectiveMk k Q (ofArrow (Quiver.reverse b)) * y)) = 0 := by
  calc _ = preprojectiveMk k Q (localPreprojectiveRelator k v) * y := by
        simp only [localPreprojectiveRelator_eq_sum_ofArrow_mul, map_sum, Finset.sum_mul,
          map_mul, map_smul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = 0 := by rw [preprojectiveMk_localPreprojectiveRelator, zero_mul]

/-- **Exactness of the Koszul complex at its middle term.** Let `z_b ∈ e_i Π` for the arrows
`b : i ⟶ v` of the doubled quiver. Then `∑_b b z_b = 0` exactly when there is one `y ∈ e_v Π` with
`z_b = ε_b b* y` for every `b`. -/
theorem sum_preprojectiveMk_ofArrow_mul_eq_zero_iff (v : Q)
    {z : (i : Symmetrify Q) → (i ⟶ Symmetrify.of.obj v) → preprojectiveAlgebra k Q}
    (hz : ∀ i b, preprojectiveMk k Q (vertexIdempotent k i) * z i b = z i b) :
    ∑ i, ∑ b, preprojectiveMk k Q (ofArrow b) * z i b = 0 ↔
      ∃ y, preprojectiveMk k Q (doubledVertexIdempotent k v) * y = y ∧ ∀ i b,
        z i b = doubledArrowSign k b • (preprojectiveMk k Q (ofArrow (Quiver.reverse b)) * y) := by
  classical
  refine ⟨fun h => ?_, ?_⟩
  · choose w hw using fun i b => preprojectiveMk_surjective k Q (z i b)
    have hI : ∑ i, ∑ b : i ⟶ Symmetrify.of.obj v, ofArrow b * w i b ∈
        TwoSidedIdeal.span (Set.range (localPreprojectiveRelator k (Q := Q))) := by
      rw [← preprojectiveIdeal_eq_span_range_localPreprojectiveRelator,
        ← preprojectiveMk_eq_zero_iff, ← h]
      simp only [map_sum, map_mul, hw]
    have hl : ∀ u : Q, vertexIdempotent k (Symmetrify.of.obj u) * localPreprojectiveRelator k u =
        localPreprojectiveRelator k u := fun u => by
      rw [← doubledVertexIdempotent_def]
      exact doubledVertexIdempotent_mul_localPreprojectiveRelator k u
    obtain ⟨Y, hY⟩ := exists_sub_mul_mem_span_of_sum_ofArrow_mul_mem_span (R := Symmetrify Q)
      (r := localPreprojectiveRelator k (Q := Q)) (j := Symmetrify.of.obj v)
      (c := fun _ b => doubledArrowSign k b • ofArrow (Quiver.reverse b)) hl
      (localPreprojectiveRelator_eq_sum_ofArrow_mul k v) hI
    refine ⟨preprojectiveMk k Q (doubledVertexIdempotent k v) * preprojectiveMk k Q Y, ?_,
      fun i b => ?_⟩
    · rw [← mul_assoc, ← map_mul, doubledVertexIdempotent_def,
        vertexIdempotent_mul_self]
    · have hb : vertexIdempotent k i * ofArrow (Quiver.reverse b) = ofArrow (Quiver.reverse b) := by
        rw [ofArrow_eq_ofPath, vertexIdempotent_mul_ofPath]
      have hb' : ofArrow (Quiver.reverse b) * vertexIdempotent k (Symmetrify.of.obj v) =
          ofArrow (Quiver.reverse b) := by
        rw [ofArrow_eq_ofPath, ofPath_mul_vertexIdempotent]
      have h := (preprojectiveMk_eq_zero_iff k Q).2
        ((preprojectiveIdeal_eq_span_range_localPreprojectiveRelator k Q).symm ▸ hY i b)
      -- Read in `Π`, `hY` says `z_b = e_i z_b = e_i (ε_b b*) Y = ε_b b* Y`.
      rw [map_sub, sub_eq_zero, map_mul, hw, hz, mul_smul_comm, hb, map_mul, map_smul] at h
      rw [h, doubledVertexIdempotent_def, ← mul_assoc, ← map_mul, hb', smul_mul_assoc]
  · rintro ⟨y, -, hy⟩
    simp only [hy]
    exact sum_preprojectiveMk_ofArrow_mul_doubledArrowSign_smul_eq_zero k v y

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

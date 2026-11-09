/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.Corner.Local
public import TauCeti.RingTheory.Idempotents.Primitive.Decomposition
public import TauCeti.RingTheory.Jacobson.Semiperfect

/-!
# Local idempotents of a semiperfect ring

A ring `A` is semiperfect when its radical quotient `A ⧸ J(A)` is semisimple and idempotents lift
modulo `J(A)` (`TauCeti.IsSemiperfectRing`). This file proves that in a semiperfect ring, `1` is a
sum of pairwise orthogonal idempotents whose corners `eᵢAeᵢ` are local rings; equivalently, `A`
decomposes as a direct sum of left ideals `Aeᵢ` with local endomorphism rings.

The proof lifts idempotents one at a time, as the definition of semiperfectness allows, and does
not need to lift a whole orthogonal family.

* Write `1 = ē₁ + ⋯ + ēₙ` in `A ⧸ J(A)` with orthogonal primitive idempotents, and lift each `ēᵢ`
  to an idempotent `eᵢ`. The corner `eᵢAeᵢ` is local
  (`IsIdempotentElem.isLocalRing_corner_of_isPrimitiveIdempotent_mk`).
* The lifts need not be orthogonal, but the sum map `⨁ Aeᵢ ⟶ A` is an isomorphism. It is onto, as
  its image contains `∑ eᵢ`, which is `1` modulo the radical and so a unit. Its kernel `K` is a
  finitely generated direct summand, as `A` is projective, and every element of `K` has components
  in the radical, so `K = J(A) K` and `K = 0` by Nakayama's lemma
  (`Submodule.FG.eq_bot_of_le_jacobson_smul`).
* The idempotents of the decomposition `A = ⨁ Aeᵢ` are orthogonal, and generate the same left
  ideals, so their images modulo the radical are again primitive and their corners local.

## Main results

* `TauCeti.IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_corner`: **in a
  semiperfect ring, `1` is a sum of orthogonal idempotents with local corners.**

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., GTM 131, Springer (2001),
  Theorem (23.6), the "only if" direction: in a semiperfect ring `1` is a sum of mutually
  orthogonal local idempotents. The proof here replaces the lifting of orthogonal families by
  Nakayama's lemma.
-/

public section

namespace TauCeti

open scoped DirectSum

universe u

variable {A : Type u} [Ring A]

/-- **In a semiperfect ring, `1` is a sum of orthogonal idempotents with local corners.**
Primitive idempotents of the semisimple radical quotient are lifted one at a time; the lifts need
not be orthogonal, but the left ideals they generate decompose the ring by Nakayama's lemma, and
the idempotents of that decomposition are orthogonal with local corners. -/
theorem IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_corner
    [IsSemiperfectRing A] :
    ∃ (n : ℕ) (f : Fin n → A) (hf : CompleteOrthogonalIdempotents f),
      ∀ i, IsLocalRing (hf.idem i).Corner := by
  classical
  let π := Ideal.Quotient.mk (Ring.jacobson A)
  -- Primitive idempotents of the radical quotient, lifted one at a time.
  obtain ⟨n, ē, hē, hprim⟩ :=
    exists_completeOrthogonalIdempotents_isPrimitiveIdempotent (A := A ⧸ Ring.jacobson A)
  choose e he hπe using fun i ↦ IsSemiperfectRing.exists_isIdempotentElem_eq (ē i) (hē.idem i)
  let L : Fin n → Ideal A := fun i ↦ Ideal.span {e i}
  let F := DirectSum.coeLinearMap L
  -- `F` is onto: its image contains `∑ eᵢ`, a unit since it is `1` modulo the radical.
  have hsurj : Function.Surjective F := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap]
    have hmem : ∑ i, e i ∈ ⨆ i, L i :=
      Submodule.sum_mem _ fun i _ ↦ Submodule.mem_iSup_of_mem i (Ideal.mem_span_singleton_self _)
    have hunit : IsUnit (∑ i, e i) :=
      isUnit_of_map_unit π _ (by simp [π, map_sum, hπe, hē.complete])
    exact Ideal.eq_top_of_isUnit_mem _ hmem hunit
  -- The components of an element of the kernel lie in the radical.
  have hcomp (x : ⨁ i, L i) (hx : F x = 0) (j : Fin n) : ((x j : L j) : A) ∈ Ring.jacobson A := by
    have hx' : ∑ i, ((x i : L i) : A) = 0 := by
      rw [← hx]
      conv_rhs => rw [← DirectSum.sum_univ_of x]
      simp [F, map_sum]
    have hfix (i : Fin n) : π (x i : A) = π (x i : A) * ē i := by
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (x i).2
      rw [← ha, map_mul]
      simp only [π, hπe, mul_assoc, (hē.idem i).eq]
    have h := congrArg (fun y ↦ π y * ē j) hx'
    simp only [map_sum, Finset.sum_mul, map_zero, zero_mul] at h
    rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [hfix i, mul_assoc, hē.ortho hij, mul_zero])
      (by simp), ← hfix j] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  -- Nakayama: the kernel `K` of `F` is a finitely generated direct summand with `K = J K`.
  obtain ⟨s, hs⟩ := Module.projective_lifting_property F LinearMap.id hsurj
  let p := LinearMap.id - s ∘ₗ F
  have hFp (y : ⨁ i, L i) : F (p y) = 0 := by
    simp [p, ← LinearMap.comp_apply F s, hs]
  have hpK {x : ⨁ i, L i} (hx : F x = 0) : p x = x := by simp [p, hx]
  have hK : LinearMap.ker F = LinearMap.range p :=
    le_antisymm (fun x hx ↦ ⟨x, hpK hx⟩) (by rintro _ ⟨y, rfl⟩; exact hFp y)
  have hker : LinearMap.ker F = ⊥ := by
    have : ∀ i, Module.Finite A (L i) := fun i ↦
      Module.Finite.iff_fg.mpr (Submodule.fg_span_singleton (e i))
    have : Module.Finite A (⨁ i, L i) :=
      Module.Finite.equiv (DirectSum.linearEquivFunOnFintype A (Fin n) fun i ↦ L i).symm
    refine Submodule.FG.eq_bot_of_le_jacobson_smul ?_ fun x hx ↦ ?_
    · rw [hK, LinearMap.range_eq_map]
      exact (Module.Finite.fg_top).map p
    · have hxJ : x ∈ Ring.jacobson A • (⊤ : Submodule A (⨁ i, L i)) := by
        rw [← DirectSum.sum_univ_of x]
        refine Submodule.sum_mem _ fun i _ ↦ ?_
        obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (x i).2
        have hxi : DirectSum.of (fun i ↦ L i) i (x i) =
            ((x i : L i) : A) • DirectSum.lof A (Fin n) (fun i ↦ L i) i
              ⟨e i, Ideal.mem_span_singleton_self _⟩ := by
          rw [← map_smul, DirectSum.lof_eq_of]
          congr 1
          exact Subtype.ext (by simp [← ha, mul_assoc, (he i).eq])
        rw [hxi]
        exact Submodule.smul_mem_smul (hcomp x hx i) Submodule.mem_top
      rw [← hpK hx, hK, LinearMap.range_eq_map, ← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem hxJ
  have hint : DirectSum.IsInternal L := ⟨LinearMap.ker_eq_bot.mp hker, hsurj⟩
  -- The idempotents of the decomposition `A = ⨁ Aeᵢ`.
  let := hint.chooseDecomposition
  have hf := DirectSum.completeOrthogonalIdempotents_idempotent L
  refine ⟨n, DirectSum.idempotent L, hf, fun i ↦ ?_⟩
  -- Its image modulo the radical generates `(A ⧸ J) ēᵢ`, so it is primitive.
  have hspan : (Ideal.span {π (DirectSum.idempotent L i)} : Ideal (A ⧸ Ring.jacobson A)) =
      Ideal.span {ē i} := by
    have hmap (x : A) : Ideal.map π (Ideal.span {x}) = Ideal.span {π x} := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [← hmap, DirectSum.span_singleton_idempotent, hmap]
    exact congrArg (fun y ↦ Ideal.span {y}) (hπe i)
  refine (hf.idem i).isLocalRing_corner_of_isPrimitiveIdempotent_mk
    ((isPrimitiveIdempotent_iff_isIndecomposableModule ((hf.idem i).map π)).2 ?_)
  rw [hspan]
  exact (hprim i).isIndecomposableModule

end TauCeti

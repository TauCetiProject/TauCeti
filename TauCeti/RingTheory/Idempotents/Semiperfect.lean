/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.Hom
public import TauCeti.RingTheory.Idempotents.Primitive.Decomposition
public import TauCeti.RingTheory.Idempotents.Corner.Jacobson
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
  to an idempotent `eᵢ`. The corner `eᵢAeᵢ` is local: its radical quotient is the corner
  `ēᵢ(A ⧸ J(A))ēᵢ` (`IsIdempotentElem.cornerQuotientJacobsonEquiv`), which is local by Fitting's
  lemma, and a ring is local when its radical quotient is, since units lift modulo the radical.
* The lifts need not be orthogonal, but the sum map `⨁ Aeᵢ ⟶ A` is an isomorphism. It is onto, as
  its image contains `∑ eᵢ`, which is `1` modulo the radical and so a unit. Its kernel `K` is a
  finitely generated direct summand, as `A` is projective, and every element of `K` has components
  in the radical, so `K = J(A) K` and `K = 0` by Nakayama's lemma
  (`Submodule.FG.eq_bot_of_le_jacobson_smul`).
* The idempotents of the decomposition `A = ⨁ Aeᵢ` are orthogonal, and generate the same left
  ideals, so their images modulo the radical are again primitive and their corners local.

## Main definitions

* `TauCeti.endSpanSingletonRingEquiv`: the endomorphism ring of `Ae` is the opposite of `eAe`.

## Main results

* `TauCeti.isLocalHom_mk_jacobson`: units lift modulo the Jacobson radical.
* `TauCeti.IsPrimitiveIdempotent.isLocalRing_corner`: a primitive idempotent of an Artinian and
  Noetherian ring has a local corner.
* `TauCeti.isLocalRing_corner_of_isPrimitiveIdempotent_mk`: an idempotent whose image modulo the
  radical is primitive has a local corner, when the radical quotient is semisimple.
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

open MulOpposite
open scoped DirectSum

universe u

variable {A : Type u} [Ring A]

/-- The endomorphism ring of the left ideal `Ae` is the opposite of the corner `eAe`: an
endomorphism is right multiplication by its value at `e`. -/
noncomputable def endSpanSingletonRingEquiv {e : A} (he : IsIdempotentElem e) :
    Module.End A (Ideal.span {e} : Ideal A) ≃+* he.Cornerᵐᵒᵖ where
  toFun φ := op ⟨(φ (spanSingletonGenerator e) : A), (Subsemigroup.mem_corner_iff he).2
    ⟨by simpa using (coe_apply_eq_mul_apply_generator he φ (spanSingletonGenerator e)).symm,
      by
        obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (φ (spanSingletonGenerator e)).2
        rw [← ha, mul_assoc, he.eq]⟩⟩
  invFun c :=
    { toFun y := ⟨(y : A) * (unop c).1, by
        rw [← IsIdempotentElem.corner_val_mul he (unop c), ← mul_assoc]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self e)⟩
      map_add' y z := Subtype.ext (add_mul (y : A) (z : A) _)
      map_smul' a y := Subtype.ext (mul_assoc a (y : A) _) }
  left_inv φ := LinearMap.ext fun y ↦ Subtype.ext
    (coe_apply_eq_mul_apply_generator he φ y).symm
  -- The value of right multiplication by `c` at the generator `e` is `e c = c`.
  right_inv c := unop_injective <| Subtype.ext <| by simp; rfl
  map_mul' φ ψ := by
    apply unop_injective
    apply Subtype.ext
    exact coe_apply_eq_mul_apply_generator he φ (ψ (spanSingletonGenerator e))
  map_add' _ _ := (rfl)

/-- **Units lift modulo the Jacobson radical**: the quotient map `A → A ⧸ J(A)` is a local
homomorphism. -/
instance isLocalHom_mk_jacobson : IsLocalHom (Ideal.Quotient.mk (Ring.jacobson A)) where
  map_nonunit a ha := by
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (↑ha.unit⁻¹ : A ⧸ Ring.jacobson A)
    -- `ab ≡ 1` and `ba ≡ 1` modulo the radical, so `ab` and `ba` are units.
    have hunit {x : A} (hx : Ideal.Quotient.mk (Ring.jacobson A) x = 1) : IsUnit x := by
      have hmem : x - 1 ∈ Ring.jacobson A := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hx, map_one, sub_self]
      simpa using (Ring.mem_jacobson_iff_isUnit_one_add_mul_left.1 hmem) 1
    obtain ⟨u, hu⟩ := hunit (x := a * b) (by simp [hb])
    obtain ⟨v, hv⟩ := hunit (x := b * a) (by simp [hb])
    -- A right inverse `b u⁻¹` and a left inverse `v⁻¹ b` of `a` agree.
    have hr : a * (b * ↑u⁻¹) = 1 := by rw [← mul_assoc, ← hu, Units.mul_inv]
    have hl : (↑v⁻¹ * b) * a = 1 := by rw [mul_assoc, ← hv, Units.inv_mul]
    have hlr : ↑v⁻¹ * b = b * ↑u⁻¹ := by
      calc ↑v⁻¹ * b = (↑v⁻¹ * b) * (a * (b * ↑u⁻¹)) := by rw [hr, mul_one]
        _ = ((↑v⁻¹ * b) * a) * (b * ↑u⁻¹) := by simp only [mul_assoc]
        _ = b * ↑u⁻¹ := by rw [hl, one_mul]
    exact isUnit_iff_exists.2 ⟨b * ↑u⁻¹, hr, by rw [← hlr, hl]⟩

/-- A ring is local when its opposite ring is, the converse of Mathlib's instance on `Rᵐᵒᵖ`. -/
theorem isLocalRing_of_isLocalRing_op (R : Type*) [Ring R] [IsLocalRing Rᵐᵒᵖ] : IsLocalRing R :=
  have : Nontrivial R := unop_injective.nontrivial
  IsLocalRing.of_surjective' (RingEquiv.opOp R).symm.toRingHom (RingEquiv.opOp R).symm.surjective

/-- The corner `eAe` is local when the endomorphism ring of the left ideal `Ae` is. -/
theorem isLocalRing_corner_of_isLocalRing_end {e : A} (he : IsIdempotentElem e)
    [IsLocalRing (Module.End A (Ideal.span {e} : Ideal A))] : IsLocalRing he.Corner :=
  have : Nontrivial he.Cornerᵐᵒᵖ := (endSpanSingletonRingEquiv he).injective.nontrivial
  have : IsLocalRing he.Cornerᵐᵒᵖ := IsLocalRing.of_surjective'
    (endSpanSingletonRingEquiv he).toRingHom (endSpanSingletonRingEquiv he).surjective
  isLocalRing_of_isLocalRing_op _

/-- **A primitive idempotent of an Artinian and Noetherian ring has a local corner**, by Fitting's
lemma for the left ideal `Ae`, which has finite length. -/
theorem IsPrimitiveIdempotent.isLocalRing_corner [IsArtinianRing A] [IsNoetherianRing A] {e : A}
    (he : IsPrimitiveIdempotent e) : IsLocalRing he.isIdempotentElem.Corner := by
  have hfin : IsFiniteLength A (Ideal.span {e} : Ideal A) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have := (isPrimitiveIdempotent_iff_isLocalRing_end he.isIdempotentElem hfin).1 he
  exact isLocalRing_corner_of_isLocalRing_end he.isIdempotentElem

/-- **An idempotent whose image modulo the Jacobson radical is primitive has a local corner**, when
the radical quotient is semisimple: the radical quotient of the corner `eAe` is the corner of the
image of `e`, which is local, and a ring is local when its radical quotient is. -/
theorem isLocalRing_corner_of_isPrimitiveIdempotent_mk [IsSemisimpleRing (A ⧸ Ring.jacobson A)]
    {e : A} (he : IsIdempotentElem e)
    (hp : IsPrimitiveIdempotent (Ideal.Quotient.mk (Ring.jacobson A) e)) :
    IsLocalRing he.Corner := by
  have : IsLocalRing (he.map (Ideal.Quotient.mk (Ring.jacobson A))).Corner := hp.isLocalRing_corner
  have : Nontrivial (he.Corner ⧸ Ring.jacobson he.Corner) :=
    he.cornerQuotientJacobsonEquiv.symm.injective.nontrivial
  have : IsLocalRing (he.Corner ⧸ Ring.jacobson he.Corner) := IsLocalRing.of_surjective'
    he.cornerQuotientJacobsonEquiv.symm.toRingHom he.cornerQuotientJacobsonEquiv.symm.surjective
  exact (Ideal.Quotient.mk (Ring.jacobson he.Corner)).domain_isLocalRing

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
  refine isLocalRing_corner_of_isPrimitiveIdempotent_mk _
    ((isPrimitiveIdempotent_iff_isIndecomposableModule ((hf.idem i).map π)).2 ?_)
  rw [hspan]
  exact (hprim i).isIndecomposableModule

end TauCeti

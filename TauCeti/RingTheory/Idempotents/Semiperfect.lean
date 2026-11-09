/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.Corner.Local
public import TauCeti.RingTheory.Idempotents.Primitive.Decomposition
public import TauCeti.RingTheory.Jacobson.Semiperfect
public import TauCeti.RingTheory.Idempotents.Projective
public import TauCeti.Algebra.Module.Projective.Local
public import TauCeti.RingTheory.Idempotents.Conjugate
public import TauCeti.Algebra.Group.Idempotent

/-!
# Semiperfect rings and local idempotents

A ring `A` is semiperfect when its radical quotient `A ⧸ J(A)` is semisimple and idempotents lift
modulo `J(A)` (`TauCeti.IsSemiperfectRing`). This file proves Lam's characterization (23.6): `A` is
semiperfect exactly when `1` is a sum of pairwise orthogonal idempotents whose corners `eᵢAeᵢ` are
local rings; equivalently, `A` is a finite direct sum of left ideals `Aeᵢ` with local endomorphism
rings.

**Only if.** The proof lifts idempotents one at a time, as the definition of semiperfectness
allows, and does not need to lift a whole orthogonal family.

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

**If.** Each `Aeᵢ` is projective with local endomorphism ring, so it has a unique maximal
submodule, its radical `J(A) eᵢ` (`Module.Projective.isCoatom_jacobson_of_isLocalRing_end`), and
the left ideal of `ēᵢ` in `A ⧸ J(A)` is simple. Hence `A ⧸ J(A)` is semisimple. An idempotent `x`
of `A ⧸ J(A)` is conjugate by a unit to a partial sum of the `ēᵢ`
(`CompleteOrthogonalIdempotents.exists_units_mul_mul_eq_sum`), and that unit lifts to a unit of `A`
(`TauCeti.Ring.isLocalHom_mk_jacobson`), which conjugates the corresponding partial sum of the `eᵢ`
to an idempotent lifting `x`.

## Main results

* `TauCeti.IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_corner`: **in a
  semiperfect ring, `1` is a sum of orthogonal idempotents with local corners.**
* `IsIdempotentElem.isSimpleModule_span_singleton_mk_jacobson`: a local idempotent generates a
  simple left ideal modulo the radical.
* `TauCeti.isSemisimpleRing_quotient_jacobson_of_isLocalRing_corner`: if `1` is a sum of orthogonal
  idempotents with local corners, the radical quotient is semisimple.
* `TauCeti.IsSemiperfectRing.of_isLocalRing_corner`: **such a ring is semiperfect.**
* `TauCeti.isSemiperfectRing_iff_exists_completeOrthogonalIdempotents_isLocalRing_corner`: Lam's
  characterization.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., GTM 131, Springer (2001),
  (21.18) and Theorem (23.6). The proof of the "only if" direction here replaces the lifting of
  orthogonal families by Nakayama's lemma.
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

section Converse

/-- **A local idempotent is simple modulo the radical**: if the corner `eAe` is local, the left
ideal of `ē` in `A ⧸ J(A)` is simple. The left ideal `Ae` is projective with local endomorphism
ring, so its radical is its unique maximal submodule
(`Module.Projective.isCoatom_jacobson_of_isLocalRing_end`); that radical is `Ae ∩ J(A)`, the
kernel of `Ae ⟶ A ⧸ J(A)`. -/
theorem _root_.IsIdempotentElem.isSimpleModule_span_singleton_mk_jacobson {e : A}
    (he : IsIdempotentElem e) [IsLocalRing he.Corner] :
    IsSimpleModule (A ⧸ Ring.jacobson A)
      (Ideal.span {Ideal.Quotient.mk (Ring.jacobson A) e} : Ideal (A ⧸ Ring.jacobson A)) := by
  set J := Ring.jacobson A
  set L : Ideal A := Ideal.span {e}
  have := he.isLocalRing_end_of_isLocalRing_corner
  have := he.projective_span_singleton
  have : Module.Finite A L := Module.Finite.iff_fg.mpr (Submodule.fg_span_singleton _)
  have hne : e ≠ 0 := fun h ↦ one_ne_zero (α := he.Corner) (Subtype.ext (by simp [h]))
  have : Nontrivial L :=
    ⟨⟨spanSingletonGenerator e, 0, fun h ↦ hne (by simpa using congrArg Subtype.val h)⟩⟩
  -- The kernel of `Ae ⟶ A ⧸ J` is the radical of `Ae`, a maximal submodule.
  have hker : LinearMap.ker (J.mkQ ∘ₗ L.subtype) = Module.jacobson A L := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    refine le_antisymm (fun x hx ↦ ?_) ?_
    · have : x = (x : A) • spanSingletonGenerator e := (smul_spanSingletonGenerator he x).symm
      rw [this]
      exact Ring.jacobson_smul_top_le A L
        (Submodule.smul_mem_smul (Submodule.mem_comap.mp hx) Submodule.mem_top)
    · exact Submodule.map_le_iff_le_comap.mp (Module.map_jacobson_le L.subtype)
  have : IsSimpleModule A (L ⧸ LinearMap.ker (J.mkQ ∘ₗ L.subtype)) :=
    isSimpleModule_iff_isCoatom.mpr (hker ▸ Module.Projective.isCoatom_jacobson_of_isLocalRing_end)
  have hrange : LinearMap.range (J.mkQ ∘ₗ L.subtype) = Submodule.map J.mkQ L := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hM : IsSimpleModule A (Submodule.map J.mkQ L) :=
    IsSimpleModule.congr ((J.mkQ ∘ₗ L.subtype).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ hrange)).symm
  -- The image of `Ae` is the left ideal of `ē`, and its `A`-submodules are its left ideals.
  have hsmul (a : A) (z : A ⧸ J) : a • z = Ideal.Quotient.mk J a * z := by
    induction z using Submodule.Quotient.induction_on
    rfl
  have hmem (z : A ⧸ J) :
      z ∈ Submodule.map J.mkQ L ↔ z ∈ (Ideal.span {Ideal.Quotient.mk J e} : Ideal (A ⧸ J)) := by
    rw [Submodule.mem_map, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      exact ⟨Ideal.Quotient.mk J c, (map_mul (Ideal.Quotient.mk J) c e).symm⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact ⟨c * e, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self e),
        map_mul (Ideal.Quotient.mk J) c e⟩
  have : RingHomSurjective (Ideal.Quotient.mk J) := ⟨Ideal.Quotient.mk_surjective⟩
  let l : Submodule.map J.mkQ L →ₛₗ[Ideal.Quotient.mk J]
      (Ideal.span {Ideal.Quotient.mk J e} : Ideal (A ⧸ J)) :=
    { toFun z := ⟨z, (hmem z).1 z.2⟩
      map_add' _ _ := rfl
      map_smul' a z := Subtype.ext (hsmul a z) }
  have hl : Function.Bijective l :=
    ⟨fun z z' h ↦ by
      have := congrArg Subtype.val h
      exact Subtype.ext this,
      fun z ↦ ⟨⟨z, (hmem z).2 z.2⟩, rfl⟩⟩
  exact (LinearMap.isSimpleModule_iff_of_bijective l hl).1 hM

variable {ι : Type*} [Fintype ι] {e : ι → A}

/-- **The radical quotient is semisimple** when `1` is a sum of orthogonal idempotents with local
corners: it is the sum of the simple left ideals of the images `ēᵢ`
(`IsIdempotentElem.isSimpleModule_span_singleton_mk_jacobson`). -/
theorem isSemisimpleRing_quotient_jacobson_of_isLocalRing_corner
    (he : CompleteOrthogonalIdempotents e) (hloc : ∀ i, IsLocalRing (he.idem i).Corner) :
    IsSemisimpleRing (A ⧸ Ring.jacobson A) := by
  have hē := he.map (Ideal.Quotient.mk (Ring.jacobson A))
  have hsimple (i : ι) : IsSimpleModule (A ⧸ Ring.jacobson A)
      (Ideal.span {Ideal.Quotient.mk (Ring.jacobson A) (e i)} : Ideal (A ⧸ Ring.jacobson A)) :=
    have := hloc i
    (he.idem i).isSimpleModule_span_singleton_mk_jacobson
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun i ↦ (Ideal.span {Ideal.Quotient.mk (Ring.jacobson A) (e i)} : Ideal _))
    (fun i ↦ inferInstance) ?_
  -- The left ideals of the `ēᵢ` add up to the left ideal of `∑ ēᵢ = 1`.
  have hsum := hē.toOrthogonalIdempotents.span_singleton_sum_eq_sup Finset.univ
  simp only [Function.comp_apply] at hsum
  rw [← Finset.sup_univ_eq_iSup, ← hsum]
  simpa using congrArg (fun y ↦ (Ideal.span {y} : Ideal _)) hē.complete

/-- **A ring in which `1` is a sum of orthogonal idempotents with local corners is
semiperfect** (Lam (23.6), the "if" direction). The radical quotient is semisimple
(`TauCeti.isSemisimpleRing_quotient_jacobson_of_isLocalRing_corner`). An idempotent `x` of it is
conjugate to a partial sum `∑ i ∈ t, ēᵢ` by a unit
(`CompleteOrthogonalIdempotents.exists_units_mul_mul_eq_sum`); lifting that unit to a unit `w` of
`A` (`TauCeti.Ring.isLocalHom_mk_jacobson`) gives the idempotent `w⁻¹ (∑ i ∈ t, eᵢ) w` lifting
`x`. -/
theorem IsSemiperfectRing.of_isLocalRing_corner (he : CompleteOrthogonalIdempotents e)
    (hloc : ∀ i, IsLocalRing (he.idem i).Corner) : IsSemiperfectRing A where
  isSemisimpleRing := isSemisimpleRing_quotient_jacobson_of_isLocalRing_corner he hloc
  exists_isIdempotentElem_eq x hx := by
    set π := Ideal.Quotient.mk (Ring.jacobson A)
    have hē := he.map π
    have hsimple (i : ι) : IsSimpleModule (A ⧸ Ring.jacobson A)
        (Ideal.span {(π ∘ e) i} : Ideal (A ⧸ Ring.jacobson A)) :=
      have := hloc i
      (he.idem i).isSimpleModule_span_singleton_mk_jacobson
    obtain ⟨t, v, hv⟩ := hē.exists_units_mul_mul_eq_sum hsimple hx
    -- Lift the unit `v` to a unit `w` of `A`.
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (v : A ⧸ Ring.jacobson A)
    obtain ⟨w, rfl⟩ := isUnit_of_map_unit π u (hu ▸ v.isUnit)
    have hw : Units.map π.toMonoidHom w = v := Units.ext hu
    refine ⟨(↑w⁻¹ : A) * (∑ i ∈ t, e i) * w,
      IsIdempotentElem.mul_mul_of_mul_eq_one
        (he.toOrthogonalIdempotents.isIdempotentElem_sum (s := t)) w.mul_inv, ?_⟩
    rw [← hv, ← hw, map_mul, map_mul, map_sum]
    simp [π]

end Converse

/-- **Lam (23.6)**: a ring is semiperfect exactly when `1` is a sum of orthogonal idempotents with
local corners, that is, when the ring is a finite direct sum of left ideals with local
endomorphism rings. -/
theorem isSemiperfectRing_iff_exists_completeOrthogonalIdempotents_isLocalRing_corner :
    IsSemiperfectRing A ↔ ∃ (n : ℕ) (f : Fin n → A) (hf : CompleteOrthogonalIdempotents f),
      ∀ i, IsLocalRing (hf.idem i).Corner :=
  ⟨fun _ ↦ IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_corner,
    fun ⟨_, _, hf, hloc⟩ ↦ IsSemiperfectRing.of_isLocalRing_corner hf hloc⟩

end TauCeti

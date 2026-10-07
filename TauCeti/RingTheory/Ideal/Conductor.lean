/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Extension and contraction away from an ideal contained in a subring

Let `S` be a subring of a commutative ring `R`, and let `C` be an ideal of `R` contained
in `S`. Extension and contraction are inverse for ideals coprime to `C`, and the inclusion
induces isomorphisms of their quotient rings. In particular, extension preserves primality
on this restricted family. Taking `C` to be the conductor compares ideals and residue rings
of an order with those of its normalization.

The argument generalizes the monogenic conductor calculation in Mathlib's
`comap_map_eq_map_adjoin_of_coprime_conductor` and `quotAdjoinEquivQuotMap` to arbitrary
subrings. No integrality or finiteness assumption is needed.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §12.
* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] {S : Subring R} {C : Ideal R}

/-- Multiplying an extended ideal by an element of an ideal contained in the subring
lands back in the original ideal. -/
theorem mul_mem_image_of_mem_map_of_le
    (hC : (C : Set R) ⊆ S) {I : Ideal S} {c : R} (hc : c ∈ C)
    {x : R} (hx : x ∈ I.map S.subtype) : c * x ∈ S.subtype '' (I : Set S) := by
  -- Induct on the span defining ideal extension, keeping all scalar multiples in the generators.
  rw [Ideal.map, Ideal.span] at hx
  induction hx using Submodule.span_induction generalizing c with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨⟨c, hC hc⟩ * a, I.mul_mem_left _ ha, rfl⟩
  | zero => exact ⟨0, I.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨a, ha, heqa⟩ := hx hc
      obtain ⟨b, hb, heqb⟩ := hy hc
      exact ⟨a + b, I.add_mem ha hb,
        by simpa only [map_add, mul_add] using congrArg₂ (· + ·) heqa heqb⟩
  | smul r x hx ih =>
      -- Apply the induction hypothesis with `r*c`, which is still in the ideal `C`.
      simpa only [smul_eq_mul, mul_left_comm, mul_assoc] using ih (C.mul_mem_left r hc)

/-- Contracting an extended ideal recovers it when it is coprime to the contraction of an
ambient ideal contained in the subring. -/
theorem comap_map_of_coprime_comap (hC : (C : Set R) ⊆ S)
    {I : Ideal S} (hI : I ⊔ C.comap S.subtype = ⊤) :
    (I.map S.subtype).comap S.subtype = I := by
  apply le_antisymm ?_ Ideal.le_comap_map
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hI)
  obtain ⟨y, hy, heq⟩ := mul_mem_image_of_mem_map_of_le hC
    (Ideal.mem_comap.mp hb) (Ideal.mem_comap.mp hx)
  have hxy : y = b * x := Subtype.ext heq
  have hbx : b * x ∈ I := hxy ▸ hy
  simpa [← add_mul, hab] using I.add_mem (I.mul_mem_right x ha) hbx

/-- Extension preserves coprimality to an ambient ideal if the original ideal is coprime
to its contraction. -/
theorem map_sup_eq_top_of_coprime_comap
    {I : Ideal S} (hI : I ⊔ C.comap S.subtype = ⊤) :
    I.map S.subtype ⊔ C = ⊤ := by
  have h := congrArg (Ideal.map S.subtype) hI
  rw [Ideal.map_sup, Ideal.map_top] at h
  exact top_unique (h ▸ sup_le_sup_left Ideal.map_comap_le _)

/-- Contraction preserves coprimality to an ideal contained in the subring. -/
theorem comap_sup_eq_top_of_le (hC : (C : Set R) ⊆ S)
    {J : Ideal R} (hJ : J ⊔ C = ⊤) :
    J.comap S.subtype ⊔ C.comap S.subtype = ⊤ := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hJ)
  let b' : S := ⟨b, hC hb⟩
  have ha' : ((1 - b' : S) : R) = a := by
    simpa [b'] using (eq_sub_iff_add_eq.mpr hab).symm
  apply (Ideal.eq_top_iff_one _).mpr
  exact Submodule.mem_sup.mpr ⟨1 - b',
    by simpa only [Ideal.mem_comap, Subring.subtype_apply, ha'] using ha,
    b', hb, sub_add_cancel _ _⟩

/-- Extending a contracted ideal recovers it when it is coprime to an ideal contained
in the subring. -/
theorem map_comap_of_coprime (hC : (C : Set R) ⊆ S)
    {J : Ideal R} (hJ : J ⊔ C = ⊤) :
    (J.comap S.subtype).map S.subtype = J := by
  apply le_antisymm Ideal.map_comap_le
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hJ)
  let a' : S := ⟨a, by
    have : a = 1 - b := eq_sub_iff_add_eq.mpr hab
    rw [this]
    exact S.sub_mem S.one_mem (hC hb)⟩
  let bx : S := ⟨b * x, hC (C.mul_mem_right x hb)⟩
  have ha' : a' ∈ J.comap S.subtype := ha
  have hbx : bx ∈ J.comap S.subtype := J.mul_mem_left b hx
  have h := Ideal.add_mem ((J.comap S.subtype).map S.subtype)
    (((J.comap S.subtype).map S.subtype).mul_mem_right x
      (Ideal.mem_map_of_mem S.subtype ha'))
    (Ideal.mem_map_of_mem S.subtype hbx)
  simpa only [Subring.subtype_apply, a', bx, ← add_mul, hab, one_mul] using h

/-- Every residue class modulo an ideal coprime to an ideal contained in the subring
has a representative in the subring. -/
theorem surjective_quotient_mk_comp_of_coprime (hC : (C : Set R) ⊆ S)
    {J : Ideal R} (hJ : J ⊔ C = ⊤) :
    Function.Surjective ((Ideal.Quotient.mk J).comp S.subtype) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hJ)
  refine ⟨⟨b * x, hC (C.mul_mem_right x hb)⟩, ?_⟩
  have ha0 : Ideal.Quotient.mk J a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hb1 : Ideal.Quotient.mk J b = 1 := by
    simpa [ha0] using congrArg (Ideal.Quotient.mk J) hab
  simp only [RingHom.comp_apply, Subring.subtype_apply, map_mul, hb1, one_mul]

/-- Inclusion induces an isomorphism on quotient rings for an ideal coprime to an ideal
contained in the subring. -/
noncomputable def quotientComapEquivOfCoprime (hC : (C : Set R) ⊆ S)
    {J : Ideal R} (hJ : J ⊔ C = ⊤) :
    S ⧸ J.comap S.subtype ≃+* R ⧸ J :=
  RingEquiv.ofBijective (Ideal.quotientMap J S.subtype le_rfl)
    ⟨Ideal.quotientMap_injective,
      Ideal.Quotient.lift_surjective_of_surjective _ _
        (surjective_quotient_mk_comp_of_coprime hC hJ)⟩

/-- The quotient-ring equivalence sends the residue class of a subring element to the
residue class of the same element in the ambient ring. -/
@[simp]
theorem quotientComapEquivOfCoprime_apply_mk (hC : (C : Set R) ⊆ S)
    {J : Ideal R} (hJ : J ⊔ C = ⊤) (x : S) :
    quotientComapEquivOfCoprime hC hJ
      (Ideal.Quotient.mk (J.comap S.subtype) x) = Ideal.Quotient.mk J (x : R) :=
  (rfl)

/-- Extension preserves and reflects primality for ideals coprime to the contraction of an
ambient ideal contained in the subring. -/
theorem isPrime_map_iff_of_coprime_comap (hC : (C : Set R) ⊆ S)
    {I : Ideal S} (hI : I ⊔ C.comap S.subtype = ⊤) :
    (I.map S.subtype).IsPrime ↔ I.IsPrime := by
  constructor
  · intro h
    have := Ideal.comap_isPrime S.subtype (I.map S.subtype)
    rwa [comap_map_of_coprime_comap hC hI] at this
  · intro h
    have hcomap : ((I.map S.subtype).comap S.subtype).IsPrime := by
      rwa [comap_map_of_coprime_comap hC hI]
    let := hcomap
    let e := quotientComapEquivOfCoprime hC (map_sup_eq_top_of_coprime_comap hI)
    let : IsDomain (R ⧸ I.map S.subtype) := e.symm.toMulEquiv.isDomain _
    exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.Algebra.Module.Submodule.Map

/-!
# Submodule intervals and quotients

This file records the generic order correspondence between a submodule interval and submodules of
the associated quotient, and the identifications of *subquotients* `↥B ⧸ A` that a linear map
induces when it is injective or surjective.  The submodule-map facts behind these,
`Submodule.mapIic_symm_apply` and `LinearMap.map_equivMapOfInjective_comap_subtype`, live in
`TauCeti.Algebra.Module.Submodule.Map`.

## Main declarations

* `Submodule.iccOrderIsoQuotientOfMapEq`: the interval/quotient correspondence for a
  specified copy of the lower endpoint inside the upper endpoint.
* `LinearMap.mapSubquotientEquivOfInjective`: an injective linear map identifies the subquotient of
  the images of two submodules with the subquotient of the two submodules themselves.
* `LinearMap.comapSubquotientEquivOfSurjective`: a surjective linear map identifies the subquotient
  of the preimages of two submodules with the subquotient of the two submodules themselves.
* `LinearMap.quotientEquivRangeQuotientMap`: a linear map whose kernel lies below a submodule
  identifies the quotient by that submodule with the corresponding quotient of its range, and
  `LinearMap.ker_mkQ_comp_rangeRestrict` is the kernel computation behind it.
* `Submodule.mem_iff_dvd_repr_of_diagonal_basis` and `Submodule.map_equivFun_eq_pi_span`:
  a submodule with a specified diagonal basis consists of the vectors whose ambient coordinates
  are divisible by the diagonal coefficients, so the ambient coordinate isomorphism carries it
  onto the product of the principal ideals of those coefficients.
* `Submodule.quotientEquivPiSpanOfBasis`: a quotient by a submodule with a specified diagonal
  basis is a product of quotients of the ring by the principal ideals of the diagonal
  coefficients.
* `Submodule.quotientEquivPiZModOfBasis`: over `ℤ`, such a quotient is a product of cyclic groups
  with the specified diagonal orders.

## References

The diagonal quotient construction follows Mathlib's
`Submodule.quotientEquivPiSpan` and `Submodule.quotientEquivPiZMod`, with the bases and diagonal
coefficients made explicit so an externally normalized Smith form can be retained.
-/

public section

namespace Submodule

/-- Transport a subquotient across equalities of its ambient and denominator submodules. -/
noncomputable def subquotientEquivOfEq
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (A B A' B' : Submodule R M) (hA : A = A') (hB : B = B') :
    (↥B ⧸ Submodule.comap B.subtype A) ≃ₗ[R]
      (↥B' ⧸ Submodule.comap B'.subtype A') := by
  subst hA hB
  exact LinearEquiv.refl R _

/-- Forward transport preserves the ambient representative. -/
@[simp] theorem subquotientEquivOfEq_mk
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (A B A' B' : Submodule R M) (hA : A = A') (hB : B = B') (x : B) :
    subquotientEquivOfEq A B A' B' hA hB (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (⟨x, hB ▸ x.property⟩ : B') := by
  subst hA hB
  rfl

/-- The inverse transport takes quotient representatives to the same ambient vector. -/
@[simp] theorem subquotientEquivOfEq_symm_mk
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (A B A' B' : Submodule R M) (hA : A = A') (hB : B = B') (x : B') :
    (subquotientEquivOfEq A B A' B' hA hB).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (⟨x, hB ▸ x.property⟩ : B) := by
  subst hA hB
  rfl

section QuotientInterval

section Order

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Submodules of `q` containing a submodule whose ambient image is `p` are the same as ambient
submodules in the interval from `p` to `q`. -/
private def iciSubmoduleOrderIsoIcc {p q : Submodule R M} (r : Submodule R q)
    (hr : r.map q.subtype = p) : Set.Ici r ≃o Set.Icc p q where
  toFun N := ⟨(q.mapIic N.1 : Submodule R M), by
    refine ⟨?_, (q.mapIic N.1).2⟩
    rw [coe_mapIic_apply, ← hr]
    exact map_mono N.2⟩
  invFun N := ⟨q.mapIic.symm ⟨N.1, N.2.2⟩, by
    rw [mapIic_symm_apply]
    exact (le_comap_map q.subtype r).trans (comap_mono (hr.le.trans N.2.1))⟩
  left_inv N := Subtype.ext (q.mapIic.symm_apply_apply N.1)
  right_inv N := Subtype.ext <| congrArg (fun P : Set.Iic q ↦ (P : Submodule R M))
    (q.mapIic.apply_symm_apply ⟨N.1, N.2.2⟩)
  map_rel_iff' := Subtype.coe_le_coe.trans q.mapIic.le_iff_le

private theorem coe_iciSubmoduleOrderIsoIcc_symm_apply {p q : Submodule R M}
    (r : Submodule R q) (hr : r.map q.subtype = p) (N : Set.Icc p q) :
    (((iciSubmoduleOrderIsoIcc r hr).symm N).1 : Submodule R q) =
      N.1.comap q.subtype :=
  mapIic_symm_apply q ⟨N.1, N.2.2⟩

end Order

section Quotient

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The interval correspondence for a specified copy `r` of the lower endpoint inside `q`. -/
def iccOrderIsoQuotientOfMapEq {p q : Submodule R M} (r : Submodule R q)
    (hr : r.map q.subtype = p) : Set.Icc p q ≃o Submodule R (q ⧸ r) :=
  (iciSubmoduleOrderIsoIcc r hr).symm.trans (comapMkQRelIso r).symm

/-- A representative belongs to the quotient submodule in the interval correspondence exactly
when its underlying ambient element belongs to the corresponding interval submodule. -/
@[simp]
theorem mk_mem_iccOrderIsoQuotientOfMapEq_iff {p q : Submodule R M} (r : Submodule R q)
    (hr : r.map q.subtype = p) (N : Set.Icc p q) (x : q) :
    Submodule.Quotient.mk x ∈ iccOrderIsoQuotientOfMapEq r hr N ↔
      (x : M) ∈ N.1 := by
  rw [iccOrderIsoQuotientOfMapEq, OrderIso.trans_apply]
  have hcomap : ((comapMkQRelIso r).symm ((iciSubmoduleOrderIsoIcc r hr).symm N)).comap r.mkQ =
      (((iciSubmoduleOrderIsoIcc r hr).symm N).1 : Submodule R q) :=
    congrArg Subtype.val
      ((comapMkQRelIso r).apply_symm_apply ((iciSubmoduleOrderIsoIcc r hr).symm N))
  rw [← r.mkQ_apply, ← mem_comap, hcomap, coe_iciSubmoduleOrderIsoIcc_symm_apply, mem_comap,
    subtype_apply]

/-- An ambient representative belongs to the interval submodule corresponding to `Q` exactly
when its quotient class belongs to `Q`. -/
@[simp]
theorem mem_iccOrderIsoQuotientOfMapEq_symm_apply_iff {p q : Submodule R M}
    (r : Submodule R q)
    (hr : r.map q.subtype = p) (Q : Submodule R (q ⧸ r)) (x : q) :
    (x : M) ∈ ((iccOrderIsoQuotientOfMapEq r hr).symm Q).1 ↔
      Submodule.Quotient.mk x ∈ Q := by
  simpa only [OrderIso.apply_symm_apply] using
    (mk_mem_iccOrderIsoQuotientOfMapEq_iff r hr
      ((iccOrderIsoQuotientOfMapEq r hr).symm Q) x).symm

end Quotient

end QuotientInterval

end Submodule

namespace LinearMap

section Subquotient

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **An injective linear map identifies subquotients.**  For arbitrary submodules `A`, `B` of `M`
the subquotient cut out by the images `A.map f`, `B.map f` is the subquotient cut out by `A` and
`B` themselves; for `A ≤ B` this reads `B.map f ⧸ A.map f ≃ₗ[R] B ⧸ A`. -/
noncomputable def mapSubquotientEquivOfInjective (f : M →ₗ[R] N) (hf : Function.Injective f)
    (A B : Submodule R M) :
    (↥(B.map f) ⧸ Submodule.comap (B.map f).subtype (A.map f)) ≃ₗ[R]
      (↥B ⧸ Submodule.comap B.subtype A) :=
  (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf B)
    (f.map_equivMapOfInjective_comap_subtype hf A B)).symm

/-- `LinearMap.mapSubquotientEquivOfInjective` read on representatives: its inverse is induced by
the restriction `Submodule.equivMapOfInjective` of `f` to `B`. -/
@[simp]
theorem mapSubquotientEquivOfInjective_symm_apply (f : M →ₗ[R] N) (hf : Function.Injective f)
    (A B : Submodule R M) (x : ↥B) :
    (mapSubquotientEquivOfInjective f hf A B).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.equivMapOfInjective f hf B x) := by
  rw [mapSubquotientEquivOfInjective, LinearEquiv.symm_symm, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply, LinearEquiv.coe_coe]

/-- `LinearMap.mapSubquotientEquivOfInjective` read on representatives, in the forward direction:
it undoes the restriction `Submodule.equivMapOfInjective` of `f` to `B`. -/
@[simp]
theorem mapSubquotientEquivOfInjective_apply (f : M →ₗ[R] N) (hf : Function.Injective f)
    (A B : Submodule R M) (x : ↥B) :
    mapSubquotientEquivOfInjective f hf A B
        (Submodule.Quotient.mk (Submodule.equivMapOfInjective f hf B x)) =
      Submodule.Quotient.mk x := by
  rw [← mapSubquotientEquivOfInjective_symm_apply f hf A B x,
    LinearEquiv.apply_symm_apply]

/-- The kernel of `x ↦ f x mod A`, on the preimage of `B`, is the trace of the preimage of `A`. -/
theorem ker_mkQ_comp_submoduleComap (f : M →ₗ[R] N) (A B : Submodule R N) :
    LinearMap.ker ((Submodule.comap B.subtype A).mkQ ∘ₗ f.submoduleComap B)
      = Submodule.comap (B.comap f).subtype (A.comap f) := by
  ext x
  simp

/-- **A surjective linear map identifies subquotients.**  For arbitrary submodules `A`, `B` of `N`
the subquotient cut out by the preimages `A.comap f`, `B.comap f` is the subquotient cut out by `A`
and `B` themselves; for `A ≤ B` this reads `B.comap f ⧸ A.comap f ≃ₗ[R] B ⧸ A`. -/
noncomputable def comapSubquotientEquivOfSurjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (A B : Submodule R N) :
    (↥(B.comap f) ⧸ Submodule.comap (B.comap f).subtype (A.comap f)) ≃ₗ[R]
      (↥B ⧸ Submodule.comap B.subtype A) :=
  (Submodule.quotEquivOfEq _ _ (f.ker_mkQ_comp_submoduleComap A B).symm).trans
    (LinearMap.quotKerEquivOfSurjective _
      ((Submodule.mkQ_surjective _).comp
        (LinearMap.submoduleComap_surjective_of_surjective f B hf)))

/-- `LinearMap.comapSubquotientEquivOfSurjective` read on representatives: it is induced by the
restriction `LinearMap.submoduleComap` of `f` to the preimage of `B`. -/
@[simp]
theorem comapSubquotientEquivOfSurjective_apply (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (A B : Submodule R N) (x : ↥(B.comap f)) :
    comapSubquotientEquivOfSurjective f hf A B (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.submoduleComap B x) := by
  rw [comapSubquotientEquivOfSurjective, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, LinearMap.comp_apply, Submodule.mkQ_apply]

/-- `LinearMap.comapSubquotientEquivOfSurjective` read on representatives, in the inverse direction:
it undoes the restriction `LinearMap.submoduleComap` of `f` to the preimage of `B`. -/
@[simp]
theorem comapSubquotientEquivOfSurjective_symm_apply (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (A B : Submodule R N) (x : ↥(B.comap f)) :
    (comapSubquotientEquivOfSurjective f hf A B).symm
        (Submodule.Quotient.mk (f.submoduleComap B x)) = Submodule.Quotient.mk x := by
  rw [← comapSubquotientEquivOfSurjective_apply f hf A B x,
    LinearEquiv.symm_apply_apply]

/-- The kernel of the map from `M` to the quotient of the range of `f` by the image of `I` is
exactly `I`, provided that `I` contains the kernel of `f`. -/
theorem ker_mkQ_comp_rangeRestrict (f : M →ₗ[R] N) (I : Submodule R M)
    (hker : LinearMap.ker f ≤ I) :
    LinearMap.ker ((I.map f.rangeRestrict).mkQ.comp f.rangeRestrict) = I := by
  rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  exact Submodule.comap_map_eq_self (by simpa using hker)

/-- **A quotient above the kernel is the corresponding quotient of the range.**

If `ker f ≤ I`, the map `x ↦ f x` identifies `M / I` with the range of `f` modulo the
image of `I`. This form of the first isomorphism theorem is useful when `f` is a representation
with a controlled kernel. -/
noncomputable def quotientEquivRangeQuotientMap (f : M →ₗ[R] N)
    (I : Submodule R M)
    (hker : LinearMap.ker f ≤ I) :
    (M ⧸ I) ≃ₗ[R] (LinearMap.range f ⧸ I.map f.rangeRestrict) :=
  (Submodule.quotEquivOfEq _ _ (LinearMap.ker_mkQ_comp_rangeRestrict f I hker).symm).trans
    (LinearMap.quotKerEquivOfSurjective _
      ((Submodule.mkQ_surjective _).comp f.surjective_rangeRestrict))

/-- `LinearMap.quotientEquivRangeQuotientMap` sends the class of `x` to the class of `f x` in the
range quotient. -/
@[simp]
theorem quotientEquivRangeQuotientMap_apply_mk (f : M →ₗ[R] N)
    (I : Submodule R M) (hker : LinearMap.ker f ≤ I) (x : M) :
    f.quotientEquivRangeQuotientMap I hker (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.rangeRestrict x) := by
  rw [LinearMap.quotientEquivRangeQuotientMap, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    LinearMap.comp_apply, Submodule.mkQ_apply]

/-- `LinearMap.quotientEquivRangeQuotientMap` read in the inverse direction: the class of
`f.rangeRestrict x` in the range quotient comes from the class of `x`. -/
@[simp]
theorem quotientEquivRangeQuotientMap_symm_apply_mk (f : M →ₗ[R] N)
    (I : Submodule R M) (hker : LinearMap.ker f ≤ I) (x : M) :
    (f.quotientEquivRangeQuotientMap I hker).symm (Submodule.Quotient.mk (f.rangeRestrict x)) =
      Submodule.Quotient.mk x := by
  rw [← LinearMap.quotientEquivRangeQuotientMap_apply_mk f I hker x,
    LinearEquiv.symm_apply_apply]

end Subquotient

end LinearMap

namespace Submodule

section DiagonalQuotient

open Module

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite ι]

omit [Finite ι] in
/-- A submodule with a diagonal basis relative to an ambient basis is cut out by divisibility
of the ambient coordinates. -/
theorem mem_iff_dvd_repr_of_diagonal_basis (N : Submodule R M)
    (b : Basis ι R M) (bN : Basis ι R N) {a : ι → R}
    (hdiag : ∀ i, (bN i : M) = a i • b i) (x : M) :
    x ∈ N ↔ ∀ i, a i ∣ b.repr x i := by
  rw [bN.mem_submodule_iff]
  simp_rw [hdiag]
  classical
  have hrepr : ∀ (c : ι →₀ R) (i),
      b.repr (c.sum fun j r ↦ r • a j • b j) i = a i * c i := by
    intro c i
    rw [Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
    simp only [← mul_smul, map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finsupp.mem_support_iff]
    split_ifs with h
    · exact mul_comm _ _
    · simp [not_not.mp h]
  constructor
  · rintro ⟨c, rfl⟩ i
    exact ⟨c i, hrepr c i⟩
  · intro ha
    choose c hc using ha
    refine ⟨Finsupp.indicator (b.repr x).support fun i _ ↦ c i, b.ext_elem fun i ↦ ?_⟩
    rw [hrepr, Finsupp.indicator_apply]
    by_cases h : i ∈ (b.repr x).support
    · simp [h, hc i]
    · simp [h, Finsupp.notMem_support_iff.mp h]

/-- The coordinate isomorphism of an ambient basis carries a submodule with a diagonal basis onto
the product of the principal ideals generated by the diagonal coefficients. -/
theorem map_equivFun_eq_pi_span (N : Submodule R M)
    (b : Basis ι R M) (bN : Basis ι R N) (a : ι → R)
    (hdiag : ∀ i, (bN i : M) = a i • b i) :
    map (b.equivFun : M →ₗ[R] ι → R) N = pi Set.univ fun i ↦ Ideal.span ({a i} : Set R) := by
  let _ := Fintype.ofFinite ι
  ext x
  simp only [mem_map, mem_pi, N.mem_iff_dvd_repr_of_diagonal_basis b bN hdiag,
    Set.mem_univ, Ideal.mem_span_singleton, forall_true_left, LinearEquiv.coe_coe,
    Basis.equivFun_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · refine fun hdvd ↦ ⟨∑ i, x i • b i, fun i ↦ ?_, ?_⟩ <;> rw [b.repr_sum_self]
    exact hdvd i

/-- A quotient by a submodule with a specified diagonal basis is a product of quotients of the
ring by the principal ideals generated by the diagonal coefficients.

Unlike `Submodule.quotientEquivPiSpan`, this construction takes both bases and their diagonal
coefficients as input. -/
noncomputable def quotientEquivPiSpanOfBasis (N : Submodule R M)
    (b : Basis ι R M) (bN : Basis ι R N) (a : ι → R)
    (hdiag : ∀ i, (bN i : M) = a i • b i) :
    (M ⧸ N) ≃ₗ[R] ∀ i, R ⧸ Ideal.span ({a i} : Set R) :=
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  (Quotient.equiv N _ b.equivFun (map_equivFun_eq_pi_span N b bN a hdiag)).trans
    (quotientPi fun i ↦ Ideal.span ({a i} : Set R))

/-- The diagonal quotient equivalence sends a representative to the classes of its coordinates
modulo the corresponding diagonal coefficients. -/
@[simp]
theorem quotientEquivPiSpanOfBasis_mk_apply (N : Submodule R M)
    (b : Basis ι R M) (bN : Basis ι R N) (a : ι → R)
    (hdiag : ∀ i, (bN i : M) = a i • b i) (x : M) (i : ι) :
    N.quotientEquivPiSpanOfBasis b bN a hdiag (Quotient.mk x) i =
      Ideal.Quotient.mk _ (b.repr x i) := by
  simp [quotientEquivPiSpanOfBasis]

/-- A quotient by a submodule with a specified diagonal basis is a product of cyclic groups.

Unlike `Submodule.quotientEquivPiZMod`, this construction takes both bases and their diagonal
coefficients as input. This lets a caller retain a normalized choice of Smith invariant factors
rather than using the coefficients selected internally by Mathlib's basis-level Smith form. -/
noncomputable def quotientEquivPiZModOfBasis (N : Submodule ℤ M)
    (b : Basis ι ℤ M) (bN : Basis ι ℤ N) (a : ι → ℤ)
    (hdiag : ∀ i, (bN i : M) = a i • b i) :
    M ⧸ N ≃+ ∀ i, ZMod (a i).natAbs :=
  (N.quotientEquivPiSpanOfBasis b bN a hdiag).toAddEquiv.trans
    (AddEquiv.piCongrRight fun i ↦ (Int.quotientSpanEquivZMod (a i) : _ ≃+ _))

/-- The diagonal quotient equivalence sends a representative to its coordinates modulo the
corresponding diagonal coefficients. -/
@[simp]
theorem quotientEquivPiZModOfBasis_mk_apply (N : Submodule ℤ M)
    (b : Basis ι ℤ M) (bN : Basis ι ℤ N) (a : ι → ℤ)
    (hdiag : ∀ i, (bN i : M) = a i • b i) (x : M) (i : ι) :
    N.quotientEquivPiZModOfBasis b bN a hdiag (Quotient.mk x) i =
      ((b.repr x i : ℤ) : ZMod (a i).natAbs) := by
  -- `simp` rewrites with `quotientEquivPiSpanOfBasis_mk_apply`; then `eq_intCast` identifies
  -- `Ideal.Quotient.mk` on `ℤ` with the integer cast, and `map_intCast` moves the ring
  -- equivalence `Int.quotientSpanEquivZMod` past that cast. Nothing is unfolded.
  simp [quotientEquivPiZModOfBasis]

end DiagonalQuotient

end Submodule

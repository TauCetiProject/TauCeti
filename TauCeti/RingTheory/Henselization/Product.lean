/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Map
public import TauCeti.RingTheory.Henselian.Idempotent
public import TauCeti.RingTheory.Henselian.Quotient

/-!
# Henselization along disjoint closed subsets

For a finite pairwise coprime family of ideals, henselization along their intersection is
canonically the product of the individual henselizations, as an algebra over the original
ring. The coordinate maps are the functorial maps induced by the inclusions of ideals.
This separates henselian neighbourhoods of disjoint closed subsets without Noetherian or
locality assumptions; the empty family and unit ideals are allowed.

The proof lifts the coordinate idempotents of the Chinese remainder decomposition of the
closed fibre, splits the henselization by those idempotents, and identifies each summand
using the universal property. It uses Mathlib's `CompleteOrthogonalIdempotents.bijective_pi`
and `Ideal.quotientInfRingEquivPiQuotient`, and Tau Ceti's henselization universal property
and unique lifting of complete orthogonal idempotents.

## References

* Stacks Project, Lemma 15.12.8 (Tag 0H7Q).
-/

public section

open Function

namespace TauCeti.Henselization

variable {R : Type*} [CommRing R] {ι : Type*} (I : ι → Ideal R)

private noncomputable def toFactor (i : ι) : algebra (⨅ j, I j) →ₐ[R] algebra (I i) :=
  lift (J := extended (I i)) (Ideal.map_mono (iInf_le I i))

private noncomputable def coprimeResidueEquiv [Finite ι] (hI : Pairwise (IsCoprime on I)) :
    (algebra (⨅ i, I i) ⧸ extended (⨅ i, I i)) ≃+* ∀ i, R ⧸ I i :=
  (RingEquiv.ofBijective _ (quotient_bijective (⨅ i, I i))).symm.trans
    (Ideal.quotientInfRingEquivPiQuotient I hI)

private theorem coprimeResidueEquiv_mk [Finite ι] (hI : Pairwise (IsCoprime on I)) (r : R) (i : ι) :
    coprimeResidueEquiv I hI
        (Ideal.Quotient.mk _ (algebraMap R (algebra (⨅ i, I i)) r)) i =
      Ideal.Quotient.mk (I i) r := by
  have h := (RingEquiv.ofBijective _ (quotient_bijective (⨅ i, I i))).symm_apply_apply
    (Ideal.Quotient.mk (⨅ i, I i) r)
  simp only [RingEquiv.ofBijective_apply, reducedMap_mk] at h
  simp only [coprimeResidueEquiv, RingEquiv.trans_apply, h,
    Ideal.quotientInfRingEquivPiQuotient_mk_apply]

private theorem exists_coprime_idempotents [Fintype ι] (hI : Pairwise (IsCoprime on I)) :
    ∃ e : ι → algebra (⨅ i, I i), CompleteOrthogonalIdempotents e ∧
      (∀ i r, r ∈ I i → algebraMap R _ r * e i ∈ extended (⨅ i, I i)) ∧
      ∀ i, toFactor I i (e i) = 1 := by
  classical
  let E := coprimeResidueEquiv I hI
  have ht : CompleteOrthogonalIdempotents (fun i ↦ E.symm (Pi.single i 1)) :=
    (CompleteOrthogonalIdempotents.single (R := fun i ↦ R ⧸ I i)).map E.symm.toRingHom
  obtain ⟨e, ⟨he, hqe⟩, -⟩ := ht.existsUnique_lift_of_henselianRing
  have hcoord (i j : ι) : E (Ideal.Quotient.mk _ (e i)) j = (Pi.single i 1 : ∀ j, R ⧸ I j) j := by
    rw [hqe, E.apply_symm_apply]
  have hmul (i : ι) (r : R) (hr : r ∈ I i) :
      algebraMap R (algebra (⨅ i, I i)) r * e i ∈ extended (⨅ i, I i) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply E.injective
    ext j
    simp only [map_mul, map_zero, Pi.mul_apply, Pi.zero_apply]
    rw [coprimeResidueEquiv_mk, hcoord]
    by_cases hij : i = j
    · subst j
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    · simp [Pi.single_eq_of_ne (Ne.symm hij)]
  refine ⟨e, he, hmul, fun i ↦ ?_⟩
  -- Choose a representative of the lifted idempotent in the original closed fibre.
  obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_map_of_reducedMap_surjective
    (⨅ i, I i) (quotient_bijective _).surjective (e i)
  have hrmod : Ideal.Quotient.mk (I i) r = 1 := by
    have h := congrArg (fun x ↦ E x i) (Ideal.Quotient.eq.mpr hr)
    dsimp only [E] at h
    rw [coprimeResidueEquiv_mk] at h
    exact h.symm.trans ((hcoord i i).trans (Pi.single_eq_same i 1))
  apply Ideal.injOn_quotient_mk_isIdempotentElem (extended_le_jacobson (I i))
    ((he.idem i).map (toFactor I i)) .one
  have hmem : toFactor I i (e i) - algebraMap R _ r ∈ extended (I i) := by
    simpa only [map_sub, AlgHom.commutes] using
      (map_extended (⨅ i, I i) (toFactor I i)).le.trans
        (Ideal.map_mono (iInf_le I i)) (Ideal.mem_map_of_mem (toFactor I i) hr)
  have hrI : r - 1 ∈ I i := Ideal.Quotient.eq.mp (by simpa using hrmod)
  apply Ideal.Quotient.eq.mpr
  convert (extended (I i)).add_mem hmem (Ideal.mem_map_of_mem (algebraMap R _) hrI) using 1
  simp

private noncomputable def factorEquiv {e : algebra (⨅ i, I i)} (i : ι)
    (hmul : ∀ r ∈ I i, algebraMap R (algebra (⨅ i, I i)) r * e ∈ extended (⨅ i, I i))
    (hfe : toFactor I i e = 1) :
    (algebra (⨅ i, I i) ⧸ Ideal.span {1 - e}) ≃ₐ[R] algebra (I i) :=
  let L : Ideal (algebra (⨅ i, I i)) := Ideal.span {1 - e}
  let C := algebra (⨅ i, I i) ⧸ L
  let J := (extended (⨅ i, I i)).map (Ideal.Quotient.mk L)
  let heq : Ideal.Quotient.mk L e = 1 := by
    have h : Ideal.Quotient.mk L (1 - e) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h.symm
  let hIJ : (I i).map (algebraMap R C) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap]
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk L) (hmul r hr)
    simpa only [map_mul, heq, mul_one, Ideal.Quotient.mk_algebraMap] using h
  let f : C →ₐ[R] algebra (I i) := Ideal.Quotient.liftₐ L (toFactor I i) (by
    have hker : L ≤ RingHom.ker (toFactor I i).toRingHom := by
      rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      simp [hfe]
    exact fun a ha ↦ RingHom.mem_ker.mp (hker ha))
  let g : algebra (I i) →ₐ[R] C := lift hIJ
  AlgEquiv.ofAlgHom f g (algHom_ext_of_map_le_jacobson (extended_le_jacobson (I i))) (by
    apply Ideal.Quotient.algHom_ext
    apply algHom_ext_of_map_le_jacobson
    exact (Ideal.map_mono (iInf_le I i)).trans
      (hIJ.trans (by simpa only [Ideal.jacobson_bot] using (HenselianRing.jac (I := J)))))

private theorem factorEquiv_mk {e : algebra (⨅ i, I i)} (i : ι)
    (hmul : ∀ r ∈ I i, algebraMap R (algebra (⨅ i, I i)) r * e ∈ extended (⨅ i, I i))
    (hfe : toFactor I i e = 1) (x : algebra (⨅ i, I i)) :
    factorEquiv I i hmul hfe (Ideal.Quotient.mk _ x) = toFactor I i x := by
  dsimp only [factorEquiv]
  rw [AlgEquiv.ofAlgHom_apply, Ideal.Quotient.liftₐ_apply]
  exact Ideal.Quotient.lift_mk _ _ _

private theorem bijective_pi_toFactor [Finite ι] (hI : Pairwise (IsCoprime on I)) :
    Function.Bijective (AlgHom.pi (toFactor I)) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨e, he, hmul, hfe⟩ := exists_coprime_idempotents I hI
  let E := fun i ↦ factorEquiv I i (hmul i) (hfe i)
  have hcomp : (fun x i ↦ E i (Ideal.Quotient.mk (Ideal.span {1 - e i}) x)) =
      AlgHom.pi (toFactor I) := by
    funext x i
    exact (factorEquiv_mk I i (hmul i) (hfe i) x).trans (AlgHom.pi_apply _ x i).symm
  rw [← hcomp]
  exact (Function.Bijective.piMap (fun i ↦ (E i).bijective)).comp he.bijective_pi

/-- Henselizing along the intersection of finitely many pairwise coprime ideals gives the
product of their henselizations. Each coordinate is induced by the identity of the base ring.
The statement includes the empty family and unit ideals. -/
@[stacks 0H7Q]
noncomputable def coprimeEquiv [Finite ι] (hI : Pairwise (IsCoprime on I)) :
    algebra (⨅ i, I i) ≃ₐ[R] ∀ i, algebra (I i) :=
  AlgEquiv.ofBijective (AlgHom.pi (toFactor I)) (bijective_pi_toFactor I hI)

/-- The coordinate of the product comparison is the functorial map induced by the inclusion
of the intersection in the corresponding ideal. -/
@[simp]
theorem coprimeEquiv_apply [Finite ι] (hI : Pairwise (IsCoprime on I))
    (x : algebra (⨅ i, I i)) (i : ι) :
    coprimeEquiv I hI x i = map (RingHom.id R) (by simpa using iInf_le I i) x := by
  rw [coprimeEquiv, AlgEquiv.ofBijective_apply, AlgHom.pi_apply]
  have h : (toFactor I i).toRingHom = map (RingHom.id R) (by simpa using iInf_le I i) :=
    map_unique _ _ _ (by ext r; simp)
  exact DFunLike.congr_fun h x

end TauCeti.Henselization

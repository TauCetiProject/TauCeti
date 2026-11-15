/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
public import TauCeti.LinearAlgebra.RootSystem.NumberOfRoots
public import TauCeti.LinearAlgebra.RootSystem.Positive
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Root counts of bases of a given Cartan type

Any root pairing `P` over a characteristic-zero domain carries the `ℤ`-basis `b.toWeightBasisInt`
of `P.rootSpan ℤ`, and simple reflections preserve `P.rootSpan ℤ` with the same Cartan-integer
formula regardless of the ambient ring or `[IsRootSystem]`. This file constructs the resulting
root-index bijection `RootPairing.Base.indexEquivOfCartanMatrixEq` across arbitrary
characteristic-zero domains without `[IsRootSystem]`, and compares any finite reduced
crystallographic root pairing of valid Cartan type `t` with `t.simplyConnectedRootDatum` to deduce
that it has `t.numRoots` roots and `t.numRoots / 2` positive roots.

## Main definitions and results

* `RootPairing.Base.indexEquivOfCartanMatrixEq`: bijection `ι ≃ ι₂` induced by a
  Cartan-matrix-preserving bijection of simple roots, without `[IsRootSystem]` or equal base rings.
* `TauCeti.HasCartanType.natCard_eq_numRoots` and `TauCeti.HasCartanType.two_mul_ncard_posRoots`.
* `TauCeti.natCard_eq_numRoots_classifiedDynkinType` and
  `TauCeti.two_mul_ncard_posRoots_eq_numRoots_classifiedDynkinType`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.5 and §4.
-/

public section

namespace RootPairing.Base

section IndexEquiv

variable {ι R M N ι₂ R₂ M₂ N₂ : Type*}
  [CommRing R] [IsDomain R] [CharZero R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [CommRing R₂] [IsDomain R₂] [CharZero R₂]
  [AddCommGroup M₂] [Module R₂ M₂] [AddCommGroup N₂] [Module R₂ N₂]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  {P₂ : RootPairing ι₂ R₂ M₂ N₂} [P₂.IsCrystallographic]

omit [IsDomain R] [CharZero R] [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
private lemma rootSpanMem_int_injective (P : RootPairing ι R M N) :
    Function.Injective (P.rootSpanMem ℤ) := fun _ _ h =>
  P.root.injective (congrArg Subtype.val h)

omit [IsDomain R] [CharZero R] [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
private def reflectionRootSpanInt (P : RootPairing ι R M N) (k : ι) :
    P.rootSpan ℤ →ₗ[ℤ] P.rootSpan ℤ :=
  ((P.reflection k).toLinearMap.restrictScalars ℤ).restrict fun x hx => by
    refine Submodule.span_induction ?_ (by simp)
      (fun u v _ _ hu hv => by simpa using (P.rootSpan ℤ).add_mem hu hv)
      (fun a u _ hu => by simpa using (P.rootSpan ℤ).smul_mem a hu) hx
    rintro _ ⟨j, rfl⟩
    simpa only [LinearEquiv.coe_coe, LinearMap.restrictScalars_apply,
      ← root_reflectionPerm] using (P.rootSpanMem ℤ (P.reflectionPerm k j)).property

omit [IsDomain R] [CharZero R] [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
private lemma reflectionRootSpanInt_apply_rootSpanMem (P : RootPairing ι R M N) (k j : ι) :
    reflectionRootSpanInt P k (P.rootSpanMem ℤ j) = P.rootSpanMem ℤ (P.reflectionPerm k j) :=
  Subtype.ext (P.root_reflectionPerm (i := k) j).symm

omit [IsDomain R₂] [CharZero R₂] in
private lemma apply_rootSpanMem_mem_range_of_cartanMatrixEq
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (f : P.rootSpan ℤ ≃ₗ[ℤ] P₂.rootSpan ℤ)
    (hf : ∀ i : b.support, f (P.rootSpanMem ℤ i) = P₂.rootSpanMem ℤ (e i))
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) (i : ι) :
    f (P.rootSpanMem ℤ i) ∈ Set.range (P₂.rootSpanMem ℤ) := by
  have hcomm : ∀ k : b.support,
      f.toLinearMap.comp (reflectionRootSpanInt P k) =
        (reflectionRootSpanInt P₂ (e k)).comp f.toLinearMap := fun k =>
    b.toWeightBasisInt.ext fun j => by
      have hj1 : b.toWeightBasisInt j = P.rootSpanMem ℤ j :=
        Subtype.ext (b.coe_toWeightBasisInt_apply j)
      have hrefl1 : reflectionRootSpanInt P k (P.rootSpanMem ℤ j) =
          P.rootSpanMem ℤ j - b.cartanMatrix j k • P.rootSpanMem ℤ k :=
        Subtype.ext <| by
          simpa [reflectionRootSpanInt_apply_rootSpanMem, cartanMatrixIn_def] using
            P.reflection_apply_root' ℤ (i := k) (j := j)
      have hrefl2 : reflectionRootSpanInt P₂ (e k) (P₂.rootSpanMem ℤ (e j)) =
          P₂.rootSpanMem ℤ (e j) - b₂.cartanMatrix (e j) (e k) • P₂.rootSpanMem ℤ (e k) :=
        Subtype.ext <| by
          simpa [reflectionRootSpanInt_apply_rootSpanMem, cartanMatrixIn_def] using
            P₂.reflection_apply_root' ℤ (i := e k) (j := e j)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hj1, hrefl1, map_sub, map_zsmul,
        hf, hrefl2, he]
  refine b.induction_reflect i
    (p := fun idx => f (P.rootSpanMem ℤ idx) ∈ Set.range (P₂.rootSpanMem ℤ)) ?_
    (fun j hj => ⟨e ⟨j, hj⟩, (hf ⟨j, hj⟩).symm⟩) ?_
  · rintro j ⟨l, hl⟩
    exact ⟨P₂.reflectionPerm l l, by
      rw [show P.rootSpanMem ℤ (P.reflectionPerm j j) = -P.rootSpanMem ℤ j from
            Subtype.ext (by simp),
          map_neg, ← hl,
          show P₂.rootSpanMem ℤ (P₂.reflectionPerm l l) = -P₂.rootSpanMem ℤ l from
            Subtype.ext (by simp)]⟩
  · rintro j k ⟨l, hl⟩ hk
    have hstep := LinearMap.congr_fun (hcomm ⟨k, hk⟩) (P.rootSpanMem ℤ j)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      reflectionRootSpanInt_apply_rootSpanMem, ← hl] at hstep
    exact ⟨P₂.reflectionPerm (e ⟨k, hk⟩) l, hstep.symm⟩

/-- **A Cartan-matrix-preserving bijection between the simple roots of two finite reduced
crystallographic root pairings extends to a bijection between their root index types**, without
requiring `[IsRootSystem]` or equal ambient scalar rings. -/
noncomputable def indexEquivOfCartanMatrixEq [Finite ι₂] [P₂.IsReduced]
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) : ι ≃ ι₂ :=
  let f : P.rootSpan ℤ ≃ₗ[ℤ] P₂.rootSpan ℤ := b.toWeightBasisInt.equiv b₂.toWeightBasisInt e
  have hf_supp : ∀ i : b.support, f (P.rootSpanMem ℤ i) = P₂.rootSpanMem ℤ (e i) := fun i => by
    rw [show P.rootSpanMem ℤ i = b.toWeightBasisInt i from
          Subtype.ext (b.coe_toWeightBasisInt_apply i).symm,
        show P₂.rootSpanMem ℤ (e i) = b₂.toWeightBasisInt (e i) from
          Subtype.ext (b₂.coe_toWeightBasisInt_apply (e i)).symm,
        Module.Basis.equiv_apply]
  have hbij : Set.BijOn f (Set.range (P.rootSpanMem ℤ)) (Set.range (P₂.rootSpanMem ℤ)) :=
    ⟨by rintro _ ⟨i, rfl⟩
        exact apply_rootSpanMem_mem_range_of_cartanMatrixEq b b₂ e f hf_supp he i,
     f.injective.injOn,
     by rintro y ⟨j, rfl⟩
        obtain ⟨i, hi⟩ := apply_rootSpanMem_mem_range_of_cartanMatrixEq b₂ b e.symm f.symm
          (fun i => f.injective (by simp [hf_supp])) (fun u v => by simp [(he _ _).symm]) j
        exact ⟨P.rootSpanMem ℤ i, Set.mem_range_self i, by rw [hi, f.apply_symm_apply]⟩⟩
  (Equiv.ofInjective (P.rootSpanMem ℤ) (rootSpanMem_int_injective P)).trans <|
    hbij.equiv.trans (Equiv.ofInjective (P₂.rootSpanMem ℤ) (rootSpanMem_int_injective P₂)).symm

/-- `RootPairing.Base.indexEquivOfCartanMatrixEq` intertwines `rootSpanMem ℤ` with the linear
equivalence `b.toWeightBasisInt.equiv b₂.toWeightBasisInt e` of root lattices. -/
@[simp]
theorem rootSpanMem_indexEquivOfCartanMatrixEq [Finite ι₂] [P₂.IsReduced]
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) (i : ι) :
    P₂.rootSpanMem ℤ (b.indexEquivOfCartanMatrixEq b₂ e he i) =
      b.toWeightBasisInt.equiv b₂.toWeightBasisInt e (P.rootSpanMem ℤ i) := by
  simp only [indexEquivOfCartanMatrixEq, Equiv.trans_apply]
  exact Equiv.apply_ofInjective_symm (rootSpanMem_int_injective P₂) _

/-- `RootPairing.Base.indexEquivOfCartanMatrixEq` extends `e` on simple-root indices. -/
@[simp]
theorem indexEquivOfCartanMatrixEq_apply_support [Finite ι₂] [P₂.IsReduced]
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) (i : b.support) :
    b.indexEquivOfCartanMatrixEq b₂ e he i = e i := by
  apply rootSpanMem_int_injective P₂
  rw [rootSpanMem_indexEquivOfCartanMatrixEq,
    show P.rootSpanMem ℤ i = b.toWeightBasisInt i from
      Subtype.ext (b.coe_toWeightBasisInt_apply i).symm,
    Module.Basis.equiv_apply]
  exact Subtype.ext (b₂.coe_toWeightBasisInt_apply (e i))

end IndexEquiv

end RootPairing.Base

namespace TauCeti

section HasCartanType

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- **Any finite reduced crystallographic root pairing carrying a base of valid Cartan type `t` has
root index type in bijection with `Fin t.numRoots`.** -/
theorem HasCartanType.nonempty_equiv_fin_numRoots {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) : Nonempty (ι ≃ Fin t.numRoots) := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  obtain ⟨e₁, he₁⟩ := (hasCartanType_iff b t).mp h
  obtain ⟨e₂, he₂⟩ := (hasCartanType_iff (t.simplyConnectedBase ht) t).mp
    (t.hasCartanType_simplyConnectedRootDatum ht)
  exact ⟨b.indexEquivOfCartanMatrixEq (t.simplyConnectedBase ht) (e₁.trans e₂.symm) fun i j => by
    simp only [Equiv.trans_apply, he₂, he₁, Equiv.apply_symm_apply]⟩

/-- **A finite reduced crystallographic root pairing with a base of valid Cartan type `t` has
`t.numRoots` roots.** -/
theorem HasCartanType.natCard_eq_numRoots {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) : Nat.card ι = t.numRoots := by
  obtain ⟨e⟩ := h.nonempty_equiv_fin_numRoots ht; simpa using Nat.card_congr e

/-- **Twice the number of positive roots of a base of valid Cartan type `t` is `t.numRoots`.** -/
theorem HasCartanType.two_mul_ncard_posRoots {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) : 2 * (posRoots P b).ncard = t.numRoots :=
  (TauCeti.two_mul_ncard_posRoots P b).trans (h.natCard_eq_numRoots ht)

/-- **A base of valid Cartan type `t` has `t.numRoots / 2` positive roots.** -/
theorem HasCartanType.ncard_posRoots_eq_numRoots_div_two {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) : (posRoots P b).ncard = t.numRoots / 2 := by
  rw [ncard_posRoots_eq_natCard_div_two, h.natCard_eq_numRoots ht]

end HasCartanType

section Classified

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]

/-- **The number of roots of an irreducible reduced crystallographic finite root system is the root
count of its classified Dynkin type.** -/
theorem natCard_eq_numRoots_classifiedDynkinType (b : P.Base) :
    Nat.card ι = (classifiedDynkinType b).numRoots :=
  (hasCartanType_classifiedDynkinType b).natCard_eq_numRoots (valid_classifiedDynkinType b)

/-- **Twice the number of positive roots of an irreducible reduced crystallographic finite root
system is the root count of its classified Dynkin type.** -/
theorem two_mul_ncard_posRoots_eq_numRoots_classifiedDynkinType (b : P.Base) :
    2 * (posRoots P b).ncard = (classifiedDynkinType b).numRoots :=
  (hasCartanType_classifiedDynkinType b).two_mul_ncard_posRoots (valid_classifiedDynkinType b)

/-- **An irreducible reduced crystallographic finite root system has `numRoots / 2` positive
roots.** -/
theorem ncard_posRoots_eq_numRoots_classifiedDynkinType_div_two (b : P.Base) :
    (posRoots P b).ncard = (classifiedDynkinType b).numRoots / 2 :=
  (hasCartanType_classifiedDynkinType b).ncard_posRoots_eq_numRoots_div_two
    (valid_classifiedDynkinType b)

end Classified

end TauCeti

end

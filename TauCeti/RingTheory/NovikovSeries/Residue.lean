/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Grading
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The energy-zero residue of the nonnegative Novikov subring

Let `H` be an additive group, `N : H →+ ℝ` a period homomorphism, and `R` a ring. A series `a` in
`TauCeti.NovikovSeries.nonnegSubring R N` vanishes on negative periods and has only finitely many
nonzero coefficients at period `0`. Restricting its coefficients to the period kernel `N.ker`
therefore produces an element of the group ring `AddMonoidAlgebra R N.ker`.

Because two nonnegative real periods sum to `0` only when both vanish, restriction to `N.ker` is a
unital ring homomorphism (`TauCeti.NovikovSeries.residueRingHom`) with right inverse given by the
inclusion of `AddMonoidAlgebra R N.ker` (`TauCeti.NovikovSeries.ofKerAddMonoidAlgebra`) and kernel
equal to the strictly positive ideal `TauCeti.NovikovSeries.posIdeal R N`. Thus the energy-zero
residue ring `(nonnegSubring R N) ⧸ (posIdeal R N)` is canonically isomorphic to
`AddMonoidAlgebra R N.ker` (`TauCeti.NovikovSeries.quotientPosIdealEquiv`), compatibly with scalar
algebras and exponent gradings.

Completeness of the nonnegative subring makes the residue map a local homomorphism
(`IsLocalHom (residueRingHom R N)` and `TauCeti.NovikovSeries.isUnit_residueRingHom_iff`): if the
energy-zero part of `a` is invertible in `AddMonoidAlgebra R N.ker` with inverse `v`, lifting `v`
via `ofKerAddMonoidAlgebra` reduces `a * b` and `b * a` to `1` modulo `posIdeal R N`, where
geometric series invert them. In particular, over a nontrivial coefficient ring no element of
`posIdeal R N` is a unit of `nonnegSubring R N`, and when `N` is injective a series in
`nonnegSubring R N` is a unit if and only if its constant coefficient at `0` is a unit of `R`.

## Main definitions

* `TauCeti.NovikovSeries.ofKerAddMonoidAlgebra R N`: the ring embedding of
  `AddMonoidAlgebra R N.ker` into `nonnegSubring R N`.
* `TauCeti.NovikovSeries.residueRingHom R N` and `TauCeti.NovikovSeries.residueAlgHom S R N`:
  the energy-zero residue homomorphism from `nonnegSubring R N` onto `AddMonoidAlgebra R N.ker`.
* `TauCeti.NovikovSeries.quotientPosIdealEquiv R N` and
  `TauCeti.NovikovSeries.quotientPosIdealAlgEquiv S R N`: the canonical isomorphism
  `(nonnegSubring R N ⧸ posIdeal R N) ≃+* AddMonoidAlgebra R N.ker` (and `S`-algebra variant).
* `TauCeti.NovikovSeries.quotientPosIdealEquivOfInjective`: when `N` is injective, the canonical
  isomorphism `(nonnegSubring R N ⧸ posIdeal R N) ≃+* R`.

## Main results

* `TauCeti.NovikovSeries.isClosed_posIdeal`: `posIdeal R N` is closed in `nonnegSubring R N`.
* `TauCeti.NovikovSeries.ker_residueRingHom`: the kernel of `residueRingHom R N` is
  `posIdeal R N`.
* `TauCeti.NovikovSeries.residueRingHom_mem_gradeBy`: the residue map preserves exponent degrees.
* `IsLocalHom (residueRingHom R N)` and `TauCeti.NovikovSeries.isUnit_residueRingHom_iff`: an
  element of `nonnegSubring R N` is a unit if and only if its energy-zero residue in
  `AddMonoidAlgebra R N.ker` is a unit.
* `TauCeti.NovikovSeries.not_isUnit_of_mem_posIdeal`: over a nontrivial ring, no element of
  `posIdeal R N` is a unit of `nonnegSubring R N`.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta, and K. Ono, *Lagrangian Intersection Floer Theory: Anomaly and
  Obstruction*, AMS/IP Studies in Advanced Mathematics 46, 2009, Chapter 2.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
-/

public section

noncomputable section

open Function Set

namespace TauCeti.NovikovSeries

variable {S R H ι : Type*}

section Ring

variable [Ring R] [AddGroup H] {N : H →+ ℝ}

/-- The strictly positive ideal is closed in the subspace topology on `nonnegSubring R N`. -/
theorem isClosed_posIdeal : IsClosed (posIdeal R N : Set (nonnegSubring R N)) := by
  have hset : (posIdeal R N : Set (nonnegSubring R N)) =
      ⋂ h ∈ {h : H | N h ≤ 0},
        Subtype.val ⁻¹' {a : NovikovSeries R H N | a.coeff h = 0} := by
    ext a
    simp [mem_posIdeal]
  rw [hset]
  exact isClosed_biInter fun h _ =>
    ((isLocallyConstant_coeff (R := R) (N := N) h).isClosed_fiber (0 : R)).preimage
      continuous_subtype_val

/-- Restricting a series in `nonnegSubring R N` to the period kernel `N.ker` yields a finitely
supported function. -/
theorem finite_support_comp_ker_subtype (a : nonnegSubring R N) :
    (Function.support fun k : N.ker => (a : NovikovSeries R H N).coeff k).Finite := by
  refine ((a : NovikovSeries R H N).finite_le 0).preimage Subtype.val_injective.injOn |>.subset ?_
  intro k hk
  exact ⟨hk, k.2.le⟩

variable (R N) in
/-- The ring homomorphism embedding the group ring of the period kernel `N.ker` into the
nonnegative Novikov subring. -/
def ofKerAddMonoidAlgebra : AddMonoidAlgebra R N.ker →+* nonnegSubring R N :=
  (ofAddMonoidAlgebra.comp (AddMonoidAlgebra.mapDomainRingHom R N.ker.subtype)).codRestrict
    (nonnegSubring R N) fun x => mem_nonnegSubring.2 fun h hh => by
      rw [RingHom.comp_apply, coeff_ofAddMonoidAlgebra, AddMonoidAlgebra.mapDomainRingHom_apply,
        AddMonoidAlgebra.coeff_mapDomain, Finsupp.mapDomain_of_notMem_range]
      rintro ⟨k, rfl⟩
      exact hh.ne k.2

@[simp]
theorem coeff_ofKerAddMonoidAlgebra_ker (x : AddMonoidAlgebra R N.ker) (k : N.ker) :
    ((ofKerAddMonoidAlgebra R N x : nonnegSubring R N) : NovikovSeries R H N).coeff k =
      x.coeff k := by
  simp only [ofKerAddMonoidAlgebra, RingHom.codRestrict_apply, RingHom.comp_apply,
    coeff_ofAddMonoidAlgebra, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective N.ker.subtype_injective x.coeff k

theorem coeff_ofKerAddMonoidAlgebra_of_period_ne_zero (x : AddMonoidAlgebra R N.ker) {h : H}
    (hh : N h ≠ 0) :
    ((ofKerAddMonoidAlgebra R N x : nonnegSubring R N) : NovikovSeries R H N).coeff h = 0 := by
  simp only [ofKerAddMonoidAlgebra, RingHom.codRestrict_apply, RingHom.comp_apply,
    coeff_ofAddMonoidAlgebra, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.coeff_mapDomain]
  refine Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨k, rfl⟩
  exact hh k.2

@[simp]
theorem ofKerAddMonoidAlgebra_single (k : N.ker) (r : R) :
    ofKerAddMonoidAlgebra R N (AddMonoidAlgebra.single k r) =
      ⟨single k r, single_mem_nonnegSubring k.2.ge r⟩ := by
  ext1
  simp [ofKerAddMonoidAlgebra, AddMonoidAlgebra.mapDomain_single]

theorem ofKerAddMonoidAlgebra_injective : Injective (ofKerAddMonoidAlgebra R N) := by
  intro x y hxy
  ext k
  simpa using congrArg
    (fun z : nonnegSubring R N => (z : NovikovSeries R H N).coeff k) hxy

/-- Auxiliary additive restriction to the period kernel, upgraded to `residueRingHom` below. -/
private def residueAddHom : nonnegSubring R N →+ AddMonoidAlgebra R N.ker where
  toFun a := .ofCoeff <|
    Finsupp.ofSupportFinite (fun k : N.ker => (a : NovikovSeries R H N).coeff k)
      (finite_support_comp_ker_subtype a)
  map_zero' := by ext _k; simp [Finsupp.ofSupportFinite_coe]
  map_add' a b := by ext _k; simp [Finsupp.ofSupportFinite_coe, coeff_add]

private theorem coeff_residueAddHom (a : nonnegSubring R N) (k : N.ker) :
    (residueAddHom a).coeff k = (a : NovikovSeries R H N).coeff k := by
  simp [residueAddHom, Finsupp.ofSupportFinite_coe]

private theorem residueAddHom_ofKer (x : AddMonoidAlgebra R N.ker) :
    residueAddHom (ofKerAddMonoidAlgebra R N x) = x := by
  ext k
  rw [coeff_residueAddHom, coeff_ofKerAddMonoidAlgebra_ker]

private theorem residueAddHom_eq_zero_iff {a : nonnegSubring R N} :
    residueAddHom a = 0 ↔ a ∈ posIdeal R N := by
  rw [← AddMonoidAlgebra.coeff_inj, Finsupp.ext_iff, mem_posIdeal]
  simp only [coeff_residueAddHom, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  refine ⟨fun ha h hh => ?_, fun ha k => ha k k.2.le⟩
  rcases hh.lt_or_eq with hlt | heq
  · exact mem_nonnegSubring.1 a.2 h hlt
  · exact ha ⟨h, heq⟩

private theorem sub_ofKer_residueAddHom_mem_posIdeal (a : nonnegSubring R N) :
    a - ofKerAddMonoidAlgebra R N (residueAddHom a) ∈ posIdeal R N := by
  rw [← residueAddHom_eq_zero_iff, map_sub, residueAddHom_ofKer, sub_self]

variable (R N) in
/-- The energy-zero residue homomorphism from `nonnegSubring R N` onto the group ring
`AddMonoidAlgebra R N.ker` of the period kernel, reading off the coefficients of period `0`. -/
def residueRingHom : nonnegSubring R N →+* AddMonoidAlgebra R N.ker where
  __ := residueAddHom (R := R) (N := N)
  map_one' := show residueAddHom 1 = 1 by
    rw [← map_one (ofKerAddMonoidAlgebra R N), residueAddHom_ofKer]
  map_mul' a b := by
    set u := ofKerAddMonoidAlgebra R N (residueAddHom a)
    set v := ofKerAddMonoidAlgebra R N (residueAddHom b)
    have hu : a - u ∈ posIdeal R N := sub_ofKer_residueAddHom_mem_posIdeal a
    have hv : b - v ∈ posIdeal R N := sub_ofKer_residueAddHom_mem_posIdeal b
    have hdiff : a * b - u * v ∈ posIdeal R N := by
      have heq : a * b - u * v = (a - u) * b + u * (b - v) := by
        rw [sub_mul, mul_sub, sub_add_sub_cancel]
      rw [heq]
      exact add_mem (Ideal.mul_mem_right b _ hu) (Ideal.mul_mem_left _ u hv)
    have hz : residueAddHom (a * b - u * v) = 0 := residueAddHom_eq_zero_iff.2 hdiff
    rw [map_sub, sub_eq_zero] at hz
    change residueAddHom (a * b) = residueAddHom a * residueAddHom b
    rw [hz, ← map_mul, residueAddHom_ofKer]

@[simp]
theorem coeff_residueRingHom (a : nonnegSubring R N) (k : N.ker) :
    (residueRingHom R N a).coeff k = (a : NovikovSeries R H N).coeff k :=
    coeff_residueAddHom a k

@[simp]
theorem residueRingHom_ofKerAddMonoidAlgebra (x : AddMonoidAlgebra R N.ker) :
    residueRingHom R N (ofKerAddMonoidAlgebra R N x) = x :=
  residueAddHom_ofKer x

theorem residueRingHom_comp_ofKerAddMonoidAlgebra :
    (residueRingHom R N).comp (ofKerAddMonoidAlgebra R N) = RingHom.id _ :=
  RingHom.ext residueRingHom_ofKerAddMonoidAlgebra

theorem residueRingHom_surjective : Surjective (residueRingHom R N) :=
  RightInverse.surjective (residueRingHom_ofKerAddMonoidAlgebra (R := R) (N := N))

@[simp]
theorem residueRingHom_single_of_period_eq_zero {h : H} (hh : N h = 0) (r : R) :
    residueRingHom R N ⟨single h r, single_mem_nonnegSubring hh.ge r⟩ =
      AddMonoidAlgebra.single ⟨h, hh⟩ r := by
  rw [← ofKerAddMonoidAlgebra_single ⟨h, hh⟩ r, residueRingHom_ofKerAddMonoidAlgebra]

@[simp]
theorem residueRingHom_single_of_pos {h : H} (hh : 0 < N h) (r : R) :
    residueRingHom R N ⟨single h r, single_mem_nonnegSubring hh.le r⟩ = 0 :=
  residueAddHom_eq_zero_iff.2 (single_mem_posIdeal hh r)

/-- The kernel of the energy-zero residue homomorphism is `posIdeal R N`. -/
@[simp]
theorem ker_residueRingHom : RingHom.ker (residueRingHom R N) = posIdeal R N := by
  ext a
  exact residueAddHom_eq_zero_iff

/-- Every series in `nonnegSubring R N` differs from the lift of its energy-zero residue by an
element of `posIdeal R N`. -/
theorem sub_ofKerAddMonoidAlgebra_residueRingHom_mem_posIdeal (a : nonnegSubring R N) :
    a - ofKerAddMonoidAlgebra R N (residueRingHom R N a) ∈ posIdeal R N :=
  sub_ofKer_residueAddHom_mem_posIdeal a

variable (R N) in
/-- **Energy-zero residue isomorphism.** Quotienting the nonnegative Novikov subring by its
strictly positive ideal gives the group ring `AddMonoidAlgebra R N.ker` of the period kernel. -/
def quotientPosIdealEquiv :
    (nonnegSubring R N ⧸ posIdeal R N) ≃+* AddMonoidAlgebra R N.ker :=
  (Ideal.quotientEquivAlgOfEq ℕ (ker_residueRingHom (R := R) (N := N)).symm).toRingEquiv.trans
    (RingHom.quotientKerEquivOfRightInverse
      (residueRingHom_ofKerAddMonoidAlgebra (R := R) (N := N)))

@[simp]
theorem quotientPosIdealEquiv_mk (a : nonnegSubring R N) :
    quotientPosIdealEquiv R N (Ideal.Quotient.mk (posIdeal R N) a) = residueRingHom R N a :=
  (rfl)

@[simp]
theorem quotientPosIdealEquiv_symm_apply (x : AddMonoidAlgebra R N.ker) :
    (quotientPosIdealEquiv R N).symm x =
      Ideal.Quotient.mk (posIdeal R N) (ofKerAddMonoidAlgebra R N x) :=
  (rfl)

@[simp]
theorem residueRingHom_eq_zero_iff {a : nonnegSubring R N} :
    residueRingHom R N a = 0 ↔ a ∈ posIdeal R N :=
  residueAddHom_eq_zero_iff

/-- **Zero-energy unit reflection.** Completeness of `nonnegSubring R N` makes the energy-zero
residue map a local ring homomorphism: if `residueRingHom R N a` is a unit of
`AddMonoidAlgebra R N.ker`, then `a` is already a unit of `nonnegSubring R N`. -/
instance : IsLocalHom (residueRingHom R N) where
  map_nonunit a hu := by
    obtain ⟨v, hrv, hlv⟩ := isUnit_iff_exists.1 hu
    obtain ⟨b, hb⟩ := residueRingHom_surjective (R := R) (N := N) v
    have hright : 1 - a * b ∈ posIdeal R N := by
      rw [← residueRingHom_eq_zero_iff, map_sub, map_one, map_mul, hb, hrv, sub_self]
    have hleft : 1 - b * a ∈ posIdeal R N := by
      rw [← residueRingHom_eq_zero_iff, map_sub, map_one, map_mul, hb, hlv, sub_self]
    have hu_ab : IsUnit (a * b) := by
      simpa only [sub_sub_cancel] using isUnit_one_sub_of_mem_posIdeal hright
    have hu_ba : IsUnit (b * a) := by
      simpa only [sub_sub_cancel] using isUnit_one_sub_of_mem_posIdeal hleft
    obtain ⟨r, hr, _⟩ := isUnit_iff_exists.1 hu_ab
    obtain ⟨l, _, hl⟩ := isUnit_iff_exists.1 hu_ba
    exact isUnit_iff_exists_and_exists.2
      ⟨⟨b * r, by rwa [← mul_assoc]⟩, ⟨l * b, by rwa [mul_assoc]⟩⟩

/-- An element of `nonnegSubring R N` is a unit if and only if its energy-zero residue in
`AddMonoidAlgebra R N.ker` is a unit. -/
theorem isUnit_residueRingHom_iff {a : nonnegSubring R N} :
    IsUnit (residueRingHom R N a) ↔ IsUnit a :=
  isUnit_map_iff (residueRingHom R N) a

/-- The quotient map modulo `posIdeal R N` reflects units. -/
instance : IsLocalHom (Ideal.Quotient.mk (posIdeal R N)) where
  map_nonunit a hu :=
    isUnit_residueRingHom_iff.1 <|
      quotientPosIdealEquiv_mk a ▸ hu.map (quotientPosIdealEquiv R N)

/-- Over a nontrivial coefficient ring, no element of `posIdeal R N` is a unit of
`nonnegSubring R N`. -/
theorem not_isUnit_of_mem_posIdeal [Nontrivial R] {a : nonnegSubring R N}
    (ha : a ∈ posIdeal R N) : ¬ IsUnit a := by
  rw [← isUnit_residueRingHom_iff, residueRingHom_eq_zero_iff.2 ha]
  exact not_isUnit_zero

/-- Over a nontrivial coefficient ring, a monomial of strictly positive period is not a unit of
`nonnegSubring R N`. -/
theorem not_isUnit_single_nonnegSubring_of_pos [Nontrivial R] {h : H} (hh : 0 < N h) (r : R) :
    ¬ IsUnit (⟨single h r, single_mem_nonnegSubring hh.le r⟩ : nonnegSubring R N) :=
  not_isUnit_of_mem_posIdeal (single_mem_posIdeal hh r)

section InjectivePeriod

/-- When the period homomorphism `N` is injective, `N.ker` is trivial and the energy-zero residue
quotient `(nonnegSubring R N) ⧸ (posIdeal R N)` is canonically isomorphic to `R`. -/
def quotientPosIdealEquivOfInjective (hN : Injective N) :
    (nonnegSubring R N ⧸ posIdeal R N) ≃+* R :=
  haveI : Subsingleton N.ker :=
    ⟨fun x y => Subtype.ext <| hN <| x.2.trans y.2.symm⟩
  (quotientPosIdealEquiv R N).trans (AddMonoidAlgebra.uniqueRingEquiv N.ker)

@[simp]
theorem quotientPosIdealEquivOfInjective_mk (hN : Injective N) (a : nonnegSubring R N) :
    quotientPosIdealEquivOfInjective hN (Ideal.Quotient.mk (posIdeal R N) a) =
      (a : NovikovSeries R H N).coeff 0 := by
  simp [quotientPosIdealEquivOfInjective]

/-- When the period homomorphism `N` is injective, a series in `nonnegSubring R N` is a unit if
and only if its coefficient at `0` is a unit of `R`. -/
theorem isUnit_nonnegSubring_iff_coeff_zero (hN : Injective N) {a : nonnegSubring R N} :
    IsUnit a ↔ IsUnit ((a : NovikovSeries R H N).coeff 0) := by
  rw [← quotientPosIdealEquivOfInjective_mk hN a, MulEquiv.isUnit_map,
    isUnit_map_iff (Ideal.Quotient.mk (posIdeal R N)) a]

end InjectivePeriod

end Ring

section Algebra

variable [CommSemiring S] [Ring R] [Algebra S R] [AddGroup H] {N : H →+ ℝ}

variable (S R N) in
/-- The `S`-algebra embedding of `AddMonoidAlgebra R N.ker` into `nonnegSubring R N`. -/
def ofKerAddMonoidAlgebraAlgHom : AddMonoidAlgebra R N.ker →ₐ[S] nonnegSubring R N where
  __ := ofKerAddMonoidAlgebra R N
  commutes' s := by
    ext1
    simp [ofKerAddMonoidAlgebra, AddMonoidAlgebra.coe_algebraMap, algebraMap_apply]

@[simp]
theorem coe_ofKerAddMonoidAlgebraAlgHom :
    (ofKerAddMonoidAlgebraAlgHom S R N : AddMonoidAlgebra R N.ker →+* nonnegSubring R N) =
      ofKerAddMonoidAlgebra R N :=
  (rfl)

variable (S R N) in
/-- The energy-zero residue map as an `S`-algebra homomorphism. -/
def residueAlgHom : nonnegSubring R N →ₐ[S] AddMonoidAlgebra R N.ker where
  __ := residueRingHom R N
  commutes' s := by
    rw [← (ofKerAddMonoidAlgebraAlgHom S R N).commutes s]
    exact residueRingHom_ofKerAddMonoidAlgebra _

@[simp]
theorem coe_residueAlgHom :
    (residueAlgHom S R N : nonnegSubring R N →+* AddMonoidAlgebra R N.ker) =
      residueRingHom R N :=
  (rfl)

variable (S R N) in
/-- The energy-zero residue isomorphism as an `S`-algebra equivalence. -/
def quotientPosIdealAlgEquiv :
    (nonnegSubring R N ⧸ posIdeal R N) ≃ₐ[S] AddMonoidAlgebra R N.ker :=
  (Ideal.quotientEquivAlgOfEq S (ker_residueRingHom (R := R) (N := N)).symm).trans
    (Ideal.quotientKerAlgEquivOfRightInverse
      (f := residueAlgHom S R N) (g := ofKerAddMonoidAlgebraAlgHom S R N)
      (residueRingHom_ofKerAddMonoidAlgebra (R := R) (N := N)))

@[simp]
theorem quotientPosIdealAlgEquiv_mk (a : nonnegSubring R N) :
    quotientPosIdealAlgEquiv S R N (Ideal.Quotient.mk (posIdeal R N) a) =
      residueRingHom R N a :=
  (rfl)

variable (S) in
/-- When the period homomorphism `N` is injective, the energy-zero residue quotient is canonically
isomorphic to `R` as an `S`-algebra. -/
def quotientPosIdealAlgEquivOfInjective (hN : Injective N) :
    (nonnegSubring R N ⧸ posIdeal R N) ≃ₐ[S] R :=
  haveI : Subsingleton N.ker :=
    ⟨fun x y => Subtype.ext <| hN <| x.2.trans y.2.symm⟩
  (quotientPosIdealAlgEquiv S R N).trans (AddMonoidAlgebra.uniqueAlgEquiv S N.ker)

@[simp]
theorem quotientPosIdealAlgEquivOfInjective_mk (hN : Injective N) (a : nonnegSubring R N) :
    quotientPosIdealAlgEquivOfInjective S hN (Ideal.Quotient.mk (posIdeal R N) a) =
      (a : NovikovSeries R H N).coeff 0 := by
  simp [quotientPosIdealAlgEquivOfInjective, AddMonoidAlgebra.uniqueAlgEquiv]

end Algebra

section Grading

variable [CommRing R] [AddGroup H] {N : H →+ ℝ}

/-- The energy-zero residue map sends a homogeneous series of degree `i` in `nonnegSubring R N`
into the homogeneous piece of degree `i` of `AddMonoidAlgebra R N.ker`. -/
theorem residueRingHom_mem_gradeBy {f : H → ι} {i : ι} {a : nonnegSubring R N}
    (ha : a ∈ nonnegGradeBy R R N f i) :
    residueRingHom R N a ∈ AddMonoidAlgebra.gradeBy R (f ∘ N.ker.subtype) i := by
  rw [AddMonoidAlgebra.mem_gradeBy_iff]
  intro k hk
  rw [Finset.mem_coe, Finsupp.mem_support_iff, coeff_residueRingHom] at hk
  exact mem_nonnegGradeBy_iff.1 ha (mem_support.2 hk)

/-- The lift `ofKerAddMonoidAlgebra` preserves and reflects homogeneity. -/
theorem ofKerAddMonoidAlgebra_mem_nonnegGradeBy_iff {f : H → ι} {i : ι}
    {x : AddMonoidAlgebra R N.ker} :
    ofKerAddMonoidAlgebra R N x ∈ nonnegGradeBy R R N f i ↔
      x ∈ AddMonoidAlgebra.gradeBy R (f ∘ N.ker.subtype) i := by
  rw [mem_nonnegGradeBy_iff, AddMonoidAlgebra.mem_gradeBy_iff]
  refine ⟨fun hx k hk => ?_, fun hx h hh => ?_⟩
  · rw [Finset.mem_coe, Finsupp.mem_support_iff, ← coeff_ofKerAddMonoidAlgebra_ker] at hk
    exact hx (mem_support.2 hk)
  · by_cases hN : N h = 0
    · change f (N.ker.subtype ⟨h, hN⟩) = i
      refine hx ?_
      rw [Finset.mem_coe, Finsupp.mem_support_iff, ← coeff_ofKerAddMonoidAlgebra_ker]
      exact mem_support.1 hh
    · exact absurd (coeff_ofKerAddMonoidAlgebra_of_period_ne_zero x hN) (mem_support.1 hh)

end Grading

end TauCeti.NovikovSeries

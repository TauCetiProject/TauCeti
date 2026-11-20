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

Let `H` be an additive monoid (or additive group), `N : H →+ ℝ` a period homomorphism, and `R` a
ring. Completeness of `TauCeti.NovikovSeries.nonnegSubring R N` makes
`Ideal.Quotient.mk (posIdeal R N)` a local ring homomorphism: lifting an inverse modulo
`posIdeal R N` reduces `a * b` and `b * a` to `1` modulo `posIdeal R N`, where geometric series
invert them. When `N` is injective, `(nonnegSubring R N) ⧸ (posIdeal R N) ≃+* R` via the constant
coefficient at `0` (`TauCeti.NovikovSeries.quotientPosIdealEquivOfInjective`).

When `H` is an additive group, restricting coefficients to `N.ker` defines a unital ring
homomorphism `TauCeti.NovikovSeries.residueRingHom : nonnegSubring R N →+* AddMonoidAlgebra R N.ker`
with right inverse `TauCeti.NovikovSeries.ofKerAddMonoidAlgebra` and kernel `posIdeal R N`, giving
`(nonnegSubring R N) ⧸ (posIdeal R N) ≃+* AddMonoidAlgebra R N.ker`
(`TauCeti.NovikovSeries.quotientPosIdealEquiv`), compatibly with scalar algebras, unit reflection,
and exponent gradings.

## Main definitions

* `TauCeti.NovikovSeries.quotientPosIdealEquivOfInjective`,
  `TauCeti.NovikovSeries.quotientPosIdealAlgEquivOfInjective`: for injective `N`, the isomorphism
  `(nonnegSubring R N ⧸ posIdeal R N) ≃+* R` (and `S`-algebra variant).
* `TauCeti.NovikovSeries.ofKerAddMonoidAlgebra R N`, `TauCeti.NovikovSeries.residueRingHom R N`,
  `TauCeti.NovikovSeries.residueAlgHom S R N`: the kernel group-ring inclusion and residue map.
* `TauCeti.NovikovSeries.quotientPosIdealEquiv R N`,
  `TauCeti.NovikovSeries.quotientPosIdealAlgEquiv S R N`: the isomorphism
  `(nonnegSubring R N ⧸ posIdeal R N) ≃+* AddMonoidAlgebra R N.ker` (and `S`-algebra variant).

## Main results

* `IsLocalHom (Ideal.Quotient.mk (posIdeal R N))`,
  `TauCeti.NovikovSeries.isUnit_nonnegSubring_iff_coeff_zero`: unit reflection modulo
  `posIdeal R N` and its constant-coefficient form for injective periods.
* `TauCeti.NovikovSeries.ker_residueRingHom`, `IsLocalHom (residueRingHom R N)`,
  `TauCeti.NovikovSeries.isUnit_residueRingHom_iff`: kernel and unit reflection of `residueRingHom`.
* `TauCeti.NovikovSeries.residueRingHom_mem_gradeBy`,
  `TauCeti.NovikovSeries.ofKerAddMonoidAlgebra_mem_nonnegGradeBy_iff`: grading compatibility.

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

section AddMonoid

variable [Ring R] [AddMonoid H] {N : H →+ ℝ}

/-- **Zero-energy unit reflection.** Completeness of `nonnegSubring R N` makes the quotient map
modulo `posIdeal R N` a local ring homomorphism: if the residue class of `a` modulo `posIdeal R N`
is a unit, then `a` is already a unit of `nonnegSubring R N`. -/
instance : IsLocalHom (Ideal.Quotient.mk (posIdeal R N)) where
  map_nonunit a hu := by
    obtain ⟨v, hrv, hlv⟩ := isUnit_iff_exists.1 hu
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hunit : ∀ c : nonnegSubring R N, Ideal.Quotient.mk (posIdeal R N) c = 1 → IsUnit c :=
      fun c hc => by
        have hmem : 1 - c ∈ posIdeal R N := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_sub, RingHom.map_one, hc, sub_self]
        simpa only [sub_sub_cancel] using isUnit_one_sub_of_mem_posIdeal hmem
    obtain ⟨r, hr, _⟩ := isUnit_iff_exists.1 (hunit (a * b) (by rw [RingHom.map_mul, hrv]))
    obtain ⟨l, _, hl⟩ := isUnit_iff_exists.1 (hunit (b * a) (by rw [RingHom.map_mul, hlv]))
    exact isUnit_iff_exists_and_exists.2
      ⟨⟨b * r, by rwa [← mul_assoc]⟩, ⟨l * b, by rwa [mul_assoc]⟩⟩

section InjectivePeriod

private def coeffZeroNonnegRingHom (hN : Injective N) : nonnegSubring R N →+* R where
  toFun a := (a : NovikovSeries R H N).coeff 0
  map_one' := by rw [OneMemClass.coe_one, one_def, coeff_single_same]
  map_zero' := by rw [ZeroMemClass.coe_zero, coeff_zero]
  map_add' _ _ := by rw [AddMemClass.coe_add, coeff_add]
  map_mul' a b := by
    rw [MulMemClass.coe_mul, coeff_mul_eq_sum (s := {(0, 0)})
      (fun _ hp => by rw [Finset.mem_singleton.1 hp, add_zero])
      (fun u v huv hu hv => ?_), Finset.sum_singleton]
    have hu0 : 0 ≤ N u := not_lt.1 fun hlt => hu (mem_nonnegSubring.1 a.2 u hlt)
    have hv0 : 0 ≤ N v := not_lt.1 fun hlt => hv (mem_nonnegSubring.1 b.2 v hlt)
    have huv0 : N u + N v = 0 := by rw [← map_add, huv, map_zero]
    rw [Finset.mem_singleton, hN (by rw [map_zero]; linarith : N u = N 0),
      hN (by rw [map_zero]; linarith : N v = N 0)]

private def ofConstNonnegRingHom : R →+* nonnegSubring R N where
  toFun r := ⟨single 0 r, single_mem_nonnegSubring (map_zero N).ge r⟩
  map_one' := Subtype.ext single_zero_one
  map_mul' _ _ := Subtype.ext <| by simp [single_mul_single]
  map_zero' := Subtype.ext (single_zero 0)
  map_add' _ _ := Subtype.ext <| by simp [single_add]

private theorem coeffZeroNonnegRingHom_ofConst (hN : Injective N) (r : R) :
    coeffZeroNonnegRingHom hN (ofConstNonnegRingHom r) = r :=
  coeff_single_same 0 r

private theorem ker_coeffZeroNonnegRingHom (hN : Injective N) :
    RingHom.ker (coeffZeroNonnegRingHom (R := R) hN) = posIdeal R N := by
  ext a
  rw [RingHom.mem_ker, mem_posIdeal]
  refine ⟨fun ha h hh => ?_, fun ha => ha 0 (map_zero N).le⟩
  rcases hh.lt_or_eq with hlt | heq
  · exact mem_nonnegSubring.1 a.2 h hlt
  · exact (hN (heq.trans (map_zero N).symm)).symm ▸ ha

variable (R) in
/-- When the period homomorphism `N` is injective, the energy-zero residue quotient
`(nonnegSubring R N) ⧸ (posIdeal R N)` is canonically isomorphic to `R` via the coefficient at
`0`. -/
def quotientPosIdealEquivOfInjective (hN : Injective N) :
    (nonnegSubring R N ⧸ posIdeal R N) ≃+* R :=
  (Ideal.quotientEquivAlgOfEq ℕ (ker_coeffZeroNonnegRingHom (R := R) hN).symm).toRingEquiv.trans
    (RingHom.quotientKerEquivOfRightInverse (coeffZeroNonnegRingHom_ofConst (R := R) hN))

@[simp]
theorem quotientPosIdealEquivOfInjective_mk (hN : Injective N) (a : nonnegSubring R N) :
    quotientPosIdealEquivOfInjective R hN (Ideal.Quotient.mk (posIdeal R N) a) =
      (a : NovikovSeries R H N).coeff 0 := (rfl)

@[simp]
theorem quotientPosIdealEquivOfInjective_symm_apply (hN : Injective N) (r : R) :
    (quotientPosIdealEquivOfInjective R hN).symm r =
      Ideal.Quotient.mk (posIdeal R N) ⟨single 0 r, single_mem_nonnegSubring (map_zero N).ge r⟩ :=
  (rfl)

/-- When the period homomorphism `N` is injective, a series in `nonnegSubring R N` is a unit if
and only if its coefficient at `0` is a unit of `R`. -/
theorem isUnit_nonnegSubring_iff_coeff_zero (hN : Injective N) {a : nonnegSubring R N} :
    IsUnit a ↔ IsUnit ((a : NovikovSeries R H N).coeff 0) := by
  rw [← quotientPosIdealEquivOfInjective_mk hN a, MulEquiv.isUnit_map,
    isUnit_map_iff (Ideal.Quotient.mk (posIdeal R N)) a]

section Algebra

variable [CommSemiring S] [Algebra S R]

private def coeffZeroNonnegAlgHom (hN : Injective N) : nonnegSubring R N →ₐ[S] R where
  __ := coeffZeroNonnegRingHom hN
  commutes' s := by rw [RingHom.toFun_eq_coe]; exact coeff_single_same 0 (algebraMap S R s)

private def ofConstNonnegAlgHom : R →ₐ[S] nonnegSubring R N where
  __ := ofConstNonnegRingHom (R := R) (N := N)
  commutes' _ := Subtype.ext <| by simp [ofConstNonnegRingHom, algebraMap_apply]

variable (S R) in
/-- When the period homomorphism `N` is injective, the energy-zero residue quotient is canonically
isomorphic to `R` as an `S`-algebra. -/
def quotientPosIdealAlgEquivOfInjective (hN : Injective N) :
    (nonnegSubring R N ⧸ posIdeal R N) ≃ₐ[S] R :=
  (Ideal.quotientEquivAlgOfEq S (ker_coeffZeroNonnegRingHom (R := R) hN).symm).trans
    (Ideal.quotientKerAlgEquivOfRightInverse (f := coeffZeroNonnegAlgHom (S := S) hN)
      (g := ofConstNonnegAlgHom (S := S) (R := R) (N := N))
      (coeffZeroNonnegRingHom_ofConst (R := R) hN))

@[simp]
theorem quotientPosIdealAlgEquivOfInjective_apply (hN : Injective N)
    (q : nonnegSubring R N ⧸ posIdeal R N) :
    quotientPosIdealAlgEquivOfInjective S R hN q = quotientPosIdealEquivOfInjective R hN q := by
  obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective q; rfl

@[simp]
theorem toRingEquiv_quotientPosIdealAlgEquivOfInjective (hN : Injective N) :
    (quotientPosIdealAlgEquivOfInjective S R hN).toRingEquiv =
      quotientPosIdealEquivOfInjective R hN :=
  RingEquiv.ext (quotientPosIdealAlgEquivOfInjective_apply (S := S) hN)

theorem quotientPosIdealAlgEquivOfInjective_mk (hN : Injective N) (a : nonnegSubring R N) :
    quotientPosIdealAlgEquivOfInjective S R hN (Ideal.Quotient.mk (posIdeal R N) a) =
      (a : NovikovSeries R H N).coeff 0 := (rfl)

@[simp]
theorem quotientPosIdealAlgEquivOfInjective_symm_apply (hN : Injective N) (r : R) :
    (quotientPosIdealAlgEquivOfInjective S R hN).symm r =
      Ideal.Quotient.mk (posIdeal R N) ⟨single 0 r, single_mem_nonnegSubring (map_zero N).ge r⟩ :=
  (rfl)

end Algebra

end InjectivePeriod

end AddMonoid

section AddGroup

variable [Ring R] [AddGroup H] {N : H →+ ℝ}

/-- Restricting a series in `nonnegSubring R N` to the period kernel `N.ker` yields a finitely
supported function. -/
theorem finite_support_comp_ker_subtype (a : nonnegSubring R N) :
    (Function.support fun k : N.ker => (a : NovikovSeries R H N).coeff k).Finite :=
  ((a : NovikovSeries R H N).finite_le 0).preimage Subtype.val_injective.injOn |>.subset
    fun k hk => ⟨hk, k.2.le⟩

variable (R N) in
/-- The ring homomorphism embedding the group ring of the period kernel `N.ker` into the
nonnegative Novikov subring. -/
def ofKerAddMonoidAlgebra : AddMonoidAlgebra R N.ker →+* nonnegSubring R N :=
  (ofAddMonoidAlgebra.comp (AddMonoidAlgebra.mapDomainRingHom R N.ker.subtype)).codRestrict
    (nonnegSubring R N) fun x => mem_nonnegSubring.2 fun h hh => by
      simp only [RingHom.comp_apply, coeff_ofAddMonoidAlgebra,
        AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
      exact Finsupp.mapDomain_of_notMem_range _ _ fun ⟨k, hk⟩ => hh.ne (hk ▸ k.2)

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
  exact Finsupp.mapDomain_of_notMem_range _ _ fun ⟨k, hk⟩ => hh (hk ▸ k.2)

@[simp]
theorem ofKerAddMonoidAlgebra_single (k : N.ker) (r : R) :
    ofKerAddMonoidAlgebra R N (AddMonoidAlgebra.single k r) =
      ⟨single k r, single_mem_nonnegSubring k.2.ge r⟩ :=
  Subtype.ext <| by simp [ofKerAddMonoidAlgebra, AddMonoidAlgebra.mapDomain_single]

theorem ofKerAddMonoidAlgebra_injective : Injective (ofKerAddMonoidAlgebra R N) := fun _ _ hxy => by
  ext k
  simpa using congrArg (fun z : nonnegSubring R N => (z : NovikovSeries R H N).coeff k) hxy

/-- Auxiliary additive restriction to the period kernel, upgraded to `residueRingHom` below. -/
private def residueAddHom : nonnegSubring R N →+ AddMonoidAlgebra R N.ker where
  toFun a := .ofCoeff <|
    Finsupp.ofSupportFinite (fun k : N.ker => (a : NovikovSeries R H N).coeff k)
      (finite_support_comp_ker_subtype a)
  map_zero' := by ext _k; simp [Finsupp.ofSupportFinite_coe]
  map_add' _ _ := by ext _k; simp [Finsupp.ofSupportFinite_coe, coeff_add]

private theorem coeff_residueAddHom (a : nonnegSubring R N) (k : N.ker) :
    (residueAddHom a).coeff k = (a : NovikovSeries R H N).coeff k := by
  simp [residueAddHom, Finsupp.ofSupportFinite_coe]

private theorem residueAddHom_ofKer (x : AddMonoidAlgebra R N.ker) :
    residueAddHom (ofKerAddMonoidAlgebra R N x) = x := by
  ext k; rw [coeff_residueAddHom, coeff_ofKerAddMonoidAlgebra_ker]

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
  map_one' := by
    rw [AddMonoidHom.toFun_eq_coe, ← map_one (ofKerAddMonoidAlgebra R N), residueAddHom_ofKer]
  map_mul' a b := by
    set u := ofKerAddMonoidAlgebra R N (residueAddHom a)
    set v := ofKerAddMonoidAlgebra R N (residueAddHom b)
    have heq : a * b - u * v = (a - u) * b + u * (b - v) := by
      rw [sub_mul, mul_sub, sub_add_sub_cancel]
    have hz := residueAddHom_eq_zero_iff.2 <| heq ▸ add_mem
      (Ideal.mul_mem_right b _ (sub_ofKer_residueAddHom_mem_posIdeal a))
      (Ideal.mul_mem_left _ u (sub_ofKer_residueAddHom_mem_posIdeal b))
    rw [map_sub, sub_eq_zero] at hz
    rw [AddMonoidHom.toFun_eq_coe, hz, ← map_mul, residueAddHom_ofKer]

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
  ext a; exact residueAddHom_eq_zero_iff

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
    quotientPosIdealEquiv R N (Ideal.Quotient.mk (posIdeal R N) a) = residueRingHom R N a := (rfl)

@[simp]
theorem quotientPosIdealEquiv_symm_apply (x : AddMonoidAlgebra R N.ker) :
    (quotientPosIdealEquiv R N).symm x =
      Ideal.Quotient.mk (posIdeal R N) (ofKerAddMonoidAlgebra R N x) := (rfl)

@[simp]
theorem residueRingHom_eq_zero_iff {a : nonnegSubring R N} :
    residueRingHom R N a = 0 ↔ a ∈ posIdeal R N :=
  residueAddHom_eq_zero_iff

/-- Completeness of `nonnegSubring R N` makes the energy-zero residue map a local ring
homomorphism: if `residueRingHom R N a` is a unit of `AddMonoidAlgebra R N.ker`, then `a` is
already a unit of `nonnegSubring R N`. -/
instance : IsLocalHom (residueRingHom R N) where
  map_nonunit a hu := by
    rwa [← quotientPosIdealEquiv_mk, MulEquiv.isUnit_map,
      isUnit_map_iff (Ideal.Quotient.mk (posIdeal R N)) a] at hu

/-- An element of `nonnegSubring R N` is a unit if and only if its energy-zero residue in
`AddMonoidAlgebra R N.ker` is a unit. -/
theorem isUnit_residueRingHom_iff {a : nonnegSubring R N} :
    IsUnit (residueRingHom R N a) ↔ IsUnit a :=
  isUnit_map_iff (residueRingHom R N) a

section Algebra

variable [CommSemiring S] [Algebra S R]

variable (S R N) in
/-- The `S`-algebra embedding of `AddMonoidAlgebra R N.ker` into `nonnegSubring R N`. -/
def ofKerAddMonoidAlgebraAlgHom : AddMonoidAlgebra R N.ker →ₐ[S] nonnegSubring R N where
  __ := ofKerAddMonoidAlgebra R N
  commutes' _ := Subtype.ext <| by
    simp [ofKerAddMonoidAlgebra, AddMonoidAlgebra.coe_algebraMap, algebraMap_apply]

@[simp]
theorem coe_ofKerAddMonoidAlgebraAlgHom :
    (ofKerAddMonoidAlgebraAlgHom S R N : AddMonoidAlgebra R N.ker →+* nonnegSubring R N) =
      ofKerAddMonoidAlgebra R N := (rfl)

@[simp]
theorem ofKerAddMonoidAlgebraAlgHom_apply (x : AddMonoidAlgebra R N.ker) :
    ofKerAddMonoidAlgebraAlgHom S R N x = ofKerAddMonoidAlgebra R N x := (rfl)

variable (S R N) in
/-- The energy-zero residue map as an `S`-algebra homomorphism. -/
def residueAlgHom : nonnegSubring R N →ₐ[S] AddMonoidAlgebra R N.ker where
  __ := residueRingHom R N
  commutes' s := by
    rw [RingHom.toFun_eq_coe, ← (ofKerAddMonoidAlgebraAlgHom S R N).commutes s,
      ofKerAddMonoidAlgebraAlgHom_apply, residueRingHom_ofKerAddMonoidAlgebra]

@[simp]
theorem coe_residueAlgHom :
    (residueAlgHom S R N : nonnegSubring R N →+* AddMonoidAlgebra R N.ker) =
      residueRingHom R N := (rfl)

@[simp]
theorem residueAlgHom_apply (a : nonnegSubring R N) :
    residueAlgHom S R N a = residueRingHom R N a := (rfl)

variable (S R N) in
/-- The energy-zero residue isomorphism as an `S`-algebra equivalence. -/
def quotientPosIdealAlgEquiv :
    (nonnegSubring R N ⧸ posIdeal R N) ≃ₐ[S] AddMonoidAlgebra R N.ker :=
  (Ideal.quotientEquivAlgOfEq S (ker_residueRingHom (R := R) (N := N)).symm).trans
    (Ideal.quotientKerAlgEquivOfRightInverse
      (f := residueAlgHom S R N) (g := ofKerAddMonoidAlgebraAlgHom S R N)
      (residueRingHom_ofKerAddMonoidAlgebra (R := R) (N := N)))

@[simp]
theorem quotientPosIdealAlgEquiv_apply (q : nonnegSubring R N ⧸ posIdeal R N) :
    quotientPosIdealAlgEquiv S R N q = quotientPosIdealEquiv R N q := by
  obtain ⟨_, rfl⟩ := Ideal.Quotient.mk_surjective q; rfl

@[simp]
theorem toRingEquiv_quotientPosIdealAlgEquiv :
    (quotientPosIdealAlgEquiv S R N).toRingEquiv = quotientPosIdealEquiv R N :=
  RingEquiv.ext (quotientPosIdealAlgEquiv_apply (S := S))

theorem quotientPosIdealAlgEquiv_mk (a : nonnegSubring R N) :
    quotientPosIdealAlgEquiv S R N (Ideal.Quotient.mk (posIdeal R N) a) =
      residueRingHom R N a := (rfl)

@[simp]
theorem quotientPosIdealAlgEquiv_symm_apply (x : AddMonoidAlgebra R N.ker) :
    (quotientPosIdealAlgEquiv S R N).symm x =
      Ideal.Quotient.mk (posIdeal R N) (ofKerAddMonoidAlgebra R N x) := (rfl)

end Algebra

end AddGroup

section Grading

variable [CommSemiring S] [CommRing R] [Algebra S R] [AddGroup H] {N : H →+ ℝ}

/-- The energy-zero residue map sends a homogeneous series of degree `i` in `nonnegSubring R N`
into the homogeneous piece of degree `i` of `AddMonoidAlgebra R N.ker`. -/
theorem residueRingHom_mem_gradeBy {f : H → ι} {i : ι} {a : nonnegSubring R N}
    (ha : a ∈ nonnegGradeBy S R N f i) :
    residueRingHom R N a ∈ AddMonoidAlgebra.gradeBy R (f ∘ N.ker.subtype) i := by
  rw [AddMonoidAlgebra.mem_gradeBy_iff]
  intro k hk
  rw [Finset.mem_coe, Finsupp.mem_support_iff, coeff_residueRingHom] at hk
  exact mem_nonnegGradeBy_iff.1 ha (mem_support.2 hk)

/-- The lift `ofKerAddMonoidAlgebra` preserves and reflects homogeneity. -/
theorem ofKerAddMonoidAlgebra_mem_nonnegGradeBy_iff {f : H → ι} {i : ι}
    {x : AddMonoidAlgebra R N.ker} :
    ofKerAddMonoidAlgebra R N x ∈ nonnegGradeBy S R N f i ↔
      x ∈ AddMonoidAlgebra.gradeBy R (f ∘ N.ker.subtype) i := by
  rw [mem_nonnegGradeBy_iff, AddMonoidAlgebra.mem_gradeBy_iff]
  refine ⟨fun hx k hk => hx <| mem_support.2 <| by
      rwa [Finset.mem_coe, Finsupp.mem_support_iff, ← coeff_ofKerAddMonoidAlgebra_ker] at hk,
    fun hx h hh => ?_⟩
  by_cases hN : N h = 0
  · exact hx (by
      rw [Finset.mem_coe, Finsupp.mem_support_iff, ← coeff_ofKerAddMonoidAlgebra_ker]
      exact mem_support.1 hh : (⟨h, hN⟩ : N.ker) ∈ (x.coeff.support : Set N.ker))
  · exact absurd (coeff_ofKerAddMonoidAlgebra_of_period_ne_zero x hN) (mem_support.1 hh)

end Grading

end TauCeti.NovikovSeries

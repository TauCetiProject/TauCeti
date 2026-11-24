/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Prod
public import TauCeti.RingTheory.NovikovSeries.Functoriality
public import TauCeti.RingTheory.NovikovSeries.Grading
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The residue ring of the nonnegative Novikov subring

Let `N : H →+ ℝ` be a period homomorphism. The Novikov series supported in nonnegative periods
form the subring `Λ₀ = nonnegSubring R N`, and those supported in strictly positive periods form
its two-sided ideal `Λ₊ = posIdeal R N`. A Novikov series has only finitely many nonzero
coefficients of period zero, and these form an element of the group ring `R[ker N]` of the period
kernel `AddMonoidHom.mker N`. On `Λ₀`, two exponents whose periods add up to zero both have period
zero, so taking the period-zero coefficients is a ring homomorphism, the *residue*
`TauCeti.NovikovSeries.residue R N : Λ₀ →+* R[ker N]`.

The group ring `R[ker N]` embeds into `Λ₀` (`TauCeti.NovikovSeries.ofMker`) as a right inverse of
the residue, and the kernel of the residue is exactly `Λ₊`. Hence every series of `Λ₀` is the
image of its residue plus a series of positive periods, and the residue ring is the group ring of
the period kernel:

`Λ₀ ⧸ Λ₊ ≃+* R[ker N]`   (`TauCeti.NovikovSeries.residueEquiv`).

Since `Λ₀` is complete and the series of `Λ₊` are topologically nilpotent, a series of `Λ₀` is a
unit exactly when its residue is a unit of `R[ker N]`. Neither injectivity nor discreteness of
`N` is assumed. When `N` is injective the residue ring is `R`, as for power series, while a
nontrivial period kernel survives in the residue. The residue and its section preserve degrees
for every degree function on the exponents, so the residue ring of a graded Novikov ring is the
graded group ring of the period kernel. The residue commutes with the pushforward along a ring
homomorphism of coefficients and a period-rescaling map of exponents, which restricts to the period
kernels (`TauCeti.NovikovSeries.mkerMap`).

The main example is the *action-weighted extension* of period data `E : G →+ ℝ`: the exponent
monoid `G × ℝ` with the period `(g, r) ↦ E g + r`, which is `E.coprod (AddMonoidHom.id ℝ)`. Its
period kernel is identified with `G` through `g ↦ (g, -E g)`
(`AddMonoidHom.mkerCoprodIdEquiv`), so the residue ring after the extension is the whole group
ring `R[G]` (`TauCeti.NovikovSeries.residueEquivCoprodId`), whereas before the extension it is
only `R[ker E]`. The coefficient inclusion `g ↦ (g, 0)` carries the residue before the extension
to the residue after it along the inclusion `ker E ⊆ G`
(`TauCeti.NovikovSeries.residueEquivCoprodId_mk_mapNonnegSubring_inl`), so a statement about
residues proved before the extension transports to it.

## Main definitions

* `TauCeti.NovikovSeries.ofMker R N`: the group ring of the period kernel as a subring of `Λ₀`.
* `TauCeti.NovikovSeries.residue R N`: the residue `Λ₀ →+* R[ker N]`.
* `TauCeti.NovikovSeries.residueEquiv R N`: the residue ring `Λ₀ ⧸ Λ₊ ≃+* R[ker N]`.
* `TauCeti.NovikovSeries.mkerMap φ hφ`: the restriction of a period-rescaling map of exponents to
  the period kernels.
* `TauCeti.NovikovSeries.residueEquivCoprodId R E`: the residue ring of the action-weighted
  extension, `Λ₀ ⧸ Λ₊ ≃+* R[G]`.

## Main results

* `TauCeti.NovikovSeries.residue_ofMker`: the residue is a left inverse of `ofMker`.
* `TauCeti.NovikovSeries.ker_residue`: the kernel of the residue is the positive ideal.
* `TauCeti.NovikovSeries.sub_ofMker_residue_mem_posIdeal`: every series of `Λ₀` differs from the
  image of its residue by a series of positive periods.
* `TauCeti.NovikovSeries.isUnit_residue_iff`: a series of `Λ₀` is a unit exactly when its residue
  is.
* `TauCeti.NovikovSeries.residue_mem_gradeBy`, `TauCeti.NovikovSeries.ofMker_mem_gradeBy`: the
  residue and its section preserve degrees.
* `TauCeti.NovikovSeries.residue_mapNonnegSubring`: the residue commutes with pushforward.
* `TauCeti.NovikovSeries.coeff_residueEquivCoprodId_mk`: the coefficient of the residue at `g`
  after the action-weighted extension is the coefficient at `(g, -E g)`.
* `TauCeti.NovikovSeries.residueEquivCoprodId_mk_mapNonnegSubring_inl`: compatibility of the
  residues before and after the action-weighted extension.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction*, AMS/IP Studies in Advanced Mathematics 46, Amer. Math. Soc. and International
  Press, 2009, for the universal Novikov ring `Λ₀,nov` and its reduction to energy zero.
-/

public section

noncomputable section

open Function

namespace TauCeti

namespace NovikovSeries

open AddMonoidHom (mker mem_mker)

variable {R H : Type*}

section Semiring

variable [Semiring R] [AddZeroClass H] {N : H →+ ℝ}

/-- A Novikov series has only finitely many nonzero coefficients of period zero. -/
private theorem finite_support_coeff_mker (a : NovikovSeries R H N) :
    (Function.support fun k : mker N => a.coeff k).Finite :=
  ((a.finite_lt 1).preimage Subtype.val_injective.injOn).subset fun k hk =>
    ⟨hk, by rw [mem_mker.1 k.property]; exact one_pos⟩

/-- The coefficients of period zero of a Novikov series, as an element of the group ring of the
period kernel. On the nonnegative subring this is the ring homomorphism `residue`. -/
private def zeroPeriodPart : NovikovSeries R H N →+ AddMonoidAlgebra R (mker N) where
  toFun a := .ofCoeff (Finsupp.ofSupportFinite _ (finite_support_coeff_mker a))
  map_zero' := by ext; simp [Finsupp.ofSupportFinite_coe]
  map_add' _ _ := by ext; simp [Finsupp.ofSupportFinite_coe]

private theorem coeff_zeroPeriodPart (a : NovikovSeries R H N) (k : mker N) :
    (zeroPeriodPart a).coeff k = a.coeff k := by
  simp [zeroPeriodPart, Finsupp.ofSupportFinite_coe]

/-- Pushing coefficients on the period kernel forward to `H` gives zero at every exponent of
nonzero period. -/
private theorem mapDomain_subtype_mker_of_ne_zero (v : mker N →₀ R) {h : H} (hh : N h ≠ 0) :
    Finsupp.mapDomain (mker N).subtype v h = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ fun ⟨k, hk⟩ => hh (hk ▸ mem_mker.1 k.property)

end Semiring

section Ring

variable [Ring R] [AddMonoid H] {N : H →+ ℝ}

variable (R N) in
/-- The group ring of the period kernel as a subring of the nonnegative Novikov subring: an element
of `R[ker N]` is sent to the series with the same coefficients at the exponents of period zero, and
zero coefficients elsewhere. -/
def ofMker : AddMonoidAlgebra R (mker N) →+* nonnegSubring R N :=
  (ofAddMonoidAlgebra.comp (AddMonoidAlgebra.mapDomainRingHom R (mker N).subtype)).codRestrict _
    fun x => mem_nonnegSubring.2 fun h hh => by
      rw [RingHom.comp_apply, coeff_ofAddMonoidAlgebra, AddMonoidAlgebra.mapDomainRingHom_apply,
        AddMonoidAlgebra.coeff_mapDomain]
      exact mapDomain_subtype_mker_of_ne_zero _ hh.ne

/-- The coefficient of `ofMker R N x` at an exponent of period zero is the coefficient of `x`. -/
@[simp]
theorem coeff_ofMker_coe (x : AddMonoidAlgebra R (mker N)) (k : mker N) :
    (ofMker R N x : NovikovSeries R H N).coeff k = x.coeff k := by
  simp [ofMker, AddMonoidAlgebra.mapDomainRingHom_apply]

/-- The series `ofMker R N x` vanishes at every exponent of nonzero period. -/
theorem coeff_ofMker_of_ne_zero (x : AddMonoidAlgebra R (mker N)) {h : H} (hh : N h ≠ 0) :
    (ofMker R N x : NovikovSeries R H N).coeff h = 0 := by
  simp only [ofMker, RingHom.codRestrict_apply, RingHom.comp_apply, coeff_ofAddMonoidAlgebra,
    AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
  exact mapDomain_subtype_mker_of_ne_zero _ hh

/-- `ofMker R N` sends a monomial of the period kernel to the same monomial. -/
@[simp]
theorem coe_ofMker_single (k : mker N) (r : R) :
    (ofMker R N (AddMonoidAlgebra.single k r) : NovikovSeries R H N) = single (k : H) r := by
  simp [ofMker]

private theorem zeroPeriodPart_ofMker (x : AddMonoidAlgebra R (mker N)) :
    zeroPeriodPart (ofMker R N x : NovikovSeries R H N) = x := by
  ext k
  rw [coeff_zeroPeriodPart, coeff_ofMker_coe]

private theorem zeroPeriodPart_eq_zero_of_mem_posIdeal {a : nonnegSubring R N}
    (ha : a ∈ posIdeal R N) : zeroPeriodPart (a : NovikovSeries R H N) = 0 := by
  ext k
  rw [coeff_zeroPeriodPart, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact mem_posIdeal.1 ha k (mem_mker.1 k.property).le

private theorem sub_ofMker_zeroPeriodPart_mem_posIdeal (a : nonnegSubring R N) :
    a - ofMker R N (zeroPeriodPart (a : NovikovSeries R H N)) ∈ posIdeal R N := by
  refine mem_posIdeal.2 fun h hh => ?_
  rw [AddSubgroupClass.coe_sub, coeff_sub]
  rcases hh.lt_or_eq with hh | hh
  · rw [mem_nonnegSubring.1 a.property h hh, coeff_ofMker_of_ne_zero _ hh.ne, sub_zero]
  · lift h to mker N using mem_mker.2 hh
    rw [coeff_ofMker_coe, coeff_zeroPeriodPart, sub_self]

variable (R N) in
/-- The residue of a series of nonnegative periods: its coefficients at the exponents of period
zero, as an element of the group ring of the period kernel. -/
def residue : nonnegSubring R N →+* AddMonoidAlgebra R (mker N) where
  toFun a := zeroPeriodPart (a : NovikovSeries R H N)
  map_zero' := map_zero zeroPeriodPart
  map_add' a b := map_add zeroPeriodPart (a : NovikovSeries R H N) b
  map_one' := by
    rw [← _root_.map_one (ofMker R N), zeroPeriodPart_ofMker]
  map_mul' a b := by
    -- `a * b` differs from the image of the product of the two residues by a positive series.
    have hab : a * b - ofMker R N (zeroPeriodPart (a : NovikovSeries R H N) *
        zeroPeriodPart (b : NovikovSeries R H N)) ∈ posIdeal R N := by
      rw [_root_.map_mul, show ∀ x y x' y' : nonnegSubring R N,
        x * y - x' * y' = (x - x') * y + x' * (y - y') by
          intros; simp only [sub_mul, mul_sub]; abel]
      exact add_mem (Ideal.mul_mem_right _ _ (sub_ofMker_zeroPeriodPart_mem_posIdeal a))
        (Ideal.mul_mem_left _ _ (sub_ofMker_zeroPeriodPart_mem_posIdeal b))
    have := zeroPeriodPart_eq_zero_of_mem_posIdeal hab
    rwa [AddSubgroupClass.coe_sub, _root_.map_sub, zeroPeriodPart_ofMker, sub_eq_zero] at this

/-- The coefficient of the residue at an exponent of period zero is the coefficient of the
series. -/
@[simp]
theorem coeff_residue (a : nonnegSubring R N) (k : mker N) :
    (residue R N a).coeff k = (a : NovikovSeries R H N).coeff k :=
  coeff_zeroPeriodPart _ k

/-- The residue is a left inverse of the inclusion of the group ring of the period kernel. -/
@[simp]
theorem residue_ofMker (x : AddMonoidAlgebra R (mker N)) : residue R N (ofMker R N x) = x :=
  zeroPeriodPart_ofMker x

variable (R N) in
/-- The residue is a left inverse of `ofMker R N`, as an identity of ring homomorphisms. -/
theorem residue_comp_ofMker : (residue R N).comp (ofMker R N) = RingHom.id _ :=
  RingHom.ext residue_ofMker

variable (R N) in
/-- Every element of the group ring of the period kernel is the residue of a series of nonnegative
periods. -/
theorem residue_surjective : Surjective (residue R N) :=
  fun x => ⟨ofMker R N x, residue_ofMker x⟩

variable (R N) in
/-- The group ring of the period kernel embeds into the nonnegative subring. -/
theorem ofMker_injective : Injective (ofMker R N) :=
  LeftInverse.injective residue_ofMker

/-- The residue of a series of nonnegative periods vanishes exactly when the series lies in the
positive ideal. -/
theorem residue_eq_zero_iff {a : nonnegSubring R N} : residue R N a = 0 ↔ a ∈ posIdeal R N := by
  refine ⟨fun ha => mem_posIdeal.2 fun h hh => ?_, zeroPeriodPart_eq_zero_of_mem_posIdeal⟩
  rcases hh.lt_or_eq with hh | hh
  · exact mem_nonnegSubring.1 a.property h hh
  · lift h to mker N using mem_mker.2 hh
    rw [← coeff_residue, ha, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]

variable (R N) in
/-- The kernel of the residue is the positive ideal. -/
theorem ker_residue : RingHom.ker (residue R N) = posIdeal R N :=
  Ideal.ext fun _ => residue_eq_zero_iff

/-- Every series of nonnegative periods differs from the image of its residue by a series of
positive periods. -/
theorem sub_ofMker_residue_mem_posIdeal (a : nonnegSubring R N) :
    a - ofMker R N (residue R N a) ∈ posIdeal R N :=
  sub_ofMker_zeroPeriodPart_mem_posIdeal a

/-- A series of nonnegative periods is a unit of the nonnegative subring exactly when its residue
is a unit of the group ring of the period kernel. -/
theorem isUnit_residue_iff {a : nonnegSubring R N} : IsUnit (residue R N a) ↔ IsUnit a := by
  refine ⟨fun ha => ?_, fun ha => ha.map _⟩
  obtain ⟨u, hu⟩ := ha
  -- With `b` the image of the inverse residue, both `a * b` and `b * a` have residue `1`, so they
  -- are `1` minus a series of positive periods, hence units.
  have hunit : ∀ c : nonnegSubring R N, residue R N c = 1 → IsUnit c := fun c hc => by
    have hc' : 1 - c ∈ posIdeal R N := by
      rw [← residue_eq_zero_iff, _root_.map_sub, hc, _root_.map_one, sub_self]
    simpa using isUnit_one_sub_of_mem_posIdeal hc'
  obtain ⟨v, hv⟩ := (hunit (a * ofMker R N ↑u⁻¹) (by simp [← hu])).exists_right_inv
  obtain ⟨w, hw⟩ := (hunit (ofMker R N ↑u⁻¹ * a) (by simp [← hu])).exists_left_inv
  exact isUnit_iff_exists_and_exists.2
    ⟨⟨_, by rw [← mul_assoc, hv]⟩, ⟨_, by rw [mul_assoc, hw]⟩⟩

variable (R N) in
/-- The residue ring of the nonnegative Novikov subring is the group ring of the period kernel:
`Λ₀ ⧸ Λ₊ ≃+* R[ker N]`. -/
def residueEquiv : nonnegSubring R N ⧸ posIdeal R N ≃+* AddMonoidAlgebra R (mker N) :=
  (Ideal.quotEquivOfEq (ker_residue R N).symm).trans
    ((residue R N).quotientKerEquivOfRightInverse residue_ofMker)

/-- The residue ring isomorphism sends the class of a series to its residue. -/
@[simp]
theorem residueEquiv_mk (a : nonnegSubring R N) :
    residueEquiv R N (Ideal.Quotient.mk _ a) = residue R N a := by
  simp [residueEquiv]

/-- The inverse of the residue ring isomorphism sends an element of the group ring of the period
kernel to the class of its image in the nonnegative subring. -/
@[simp]
theorem residueEquiv_symm_apply (x : AddMonoidAlgebra R (mker N)) :
    (residueEquiv R N).symm x = Ideal.Quotient.mk _ (ofMker R N x) := by
  simp [residueEquiv]

section Map

variable {S H' : Type*} [Ring S] [AddMonoid H'] {N' : H' →+ ℝ}

/-- A period-rescaling map of exponents restricts to a map of period kernels. -/
def mkerMap (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) : mker N →+ mker N' :=
  (φ.comp (mker N).subtype).codRestrict (mker N') fun k => mem_mker.2 <| by
    obtain ⟨c, -, hcφ⟩ := hφ
    rw [AddMonoidHom.comp_apply, hcφ, AddSubmonoid.coe_subtype, mem_mker.1 k.property, mul_zero]

/-- The restriction `mkerMap φ hφ` acts as `φ` on the period kernel. -/
@[simp]
theorem coe_mkerMap_apply (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) (k : mker N) :
    (mkerMap φ hφ k : H') = φ k :=
  (rfl)

variable (ρ : R →+* S) (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)

/-- The residue commutes with pushforward: the residue of the image of a series under
`mapNonnegSubring ρ φ hφ` is the image of its residue under `ρ` on coefficients and the restriction
of `φ` to the period kernels. -/
theorem residue_mapNonnegSubring (a : nonnegSubring R N) :
    residue S N' (mapNonnegSubring ρ φ hφ a) =
      AddMonoidAlgebra.mapDomainRingHom S (mkerMap φ hφ)
        (AddMonoidAlgebra.mapRingHom (mker N) ρ (residue R N a)) := by
  -- On the image of the group ring of the period kernel both sides agree monomial by monomial.
  have hofMker (x : AddMonoidAlgebra R (mker N)) :
      residue S N' (mapNonnegSubring ρ φ hφ (ofMker R N x)) =
        AddMonoidAlgebra.mapDomainRingHom S (mkerMap φ hφ)
          (AddMonoidAlgebra.mapRingHom (mker N) ρ x) := by
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [_root_.map_add, hx, hy]
    | single k r =>
      rw [AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapDomainRingHom_apply,
        AddMonoidAlgebra.mapDomain_single, ← residue_ofMker (AddMonoidAlgebra.single _ (ρ r))]
      congr 1
      ext1
      simp
  -- The rest of `a` has positive periods, so its image has residue zero.
  rw [← hofMker, ← sub_eq_zero, ← _root_.map_sub, ← _root_.map_sub, residue_eq_zero_iff]
  exact mapNonnegSubring_mem_posIdeal ρ φ hφ (sub_ofMker_residue_mem_posIdeal a)

/-- The residue commutes with pushforward, as an identity of ring homomorphisms. -/
theorem residue_comp_mapNonnegSubring :
    (residue S N').comp (mapNonnegSubring ρ φ hφ) =
      ((AddMonoidAlgebra.mapDomainRingHom S (mkerMap φ hφ)).comp
        (AddMonoidAlgebra.mapRingHom (mker N) ρ)).comp (residue R N) :=
  RingHom.ext (residue_mapNonnegSubring ρ φ hφ)

end Map

section ActionWeight

variable {G : Type*} [AddMonoid G] (E : G →+ ℝ)

variable (R) in
/-- After the action-weighted extension `G × ℝ` of the period data `E`, with period
`(g, r) ↦ E g + r`, the residue ring of the nonnegative subring is the group ring of `G`: the
coefficient at `g` is the coefficient at the exponent `(g, -E g)` of period zero. -/
def residueEquivCoprodId :
    nonnegSubring R (E.coprod (AddMonoidHom.id ℝ)) ⧸ posIdeal R (E.coprod (AddMonoidHom.id ℝ)) ≃+*
      AddMonoidAlgebra R G :=
  (residueEquiv R (E.coprod (AddMonoidHom.id ℝ))).trans
    (AddMonoidAlgebra.mapDomainRingEquiv R E.mkerCoprodIdEquiv.symm)

variable {E}

/-- The coefficient at `g` of the residue after the action-weighted extension is the coefficient of
the series at the exponent `(g, -E g)`. -/
@[simp]
theorem coeff_residueEquivCoprodId_mk (a : nonnegSubring R (E.coprod (AddMonoidHom.id ℝ)))
    (g : G) :
    (residueEquivCoprodId R E (Ideal.Quotient.mk _ a)).coeff g =
      (a : NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))).coeff (g, -E g) := by
  simp [residueEquivCoprodId]

/-- The inverse of the residue ring isomorphism after the action-weighted extension sends the
monomial at `g` to the class of the monomial at the exponent `(g, -E g)` of period zero. -/
@[simp]
theorem residueEquivCoprodId_symm_single (g : G) (r : R) :
    (residueEquivCoprodId R E).symm (AddMonoidAlgebra.single g r) =
      Ideal.Quotient.mk _ (ofMker R _ (AddMonoidAlgebra.single (E.mkerCoprodIdEquiv g) r)) := by
  simp [residueEquivCoprodId]

/-- The inclusion `g ↦ (g, 0)` of exponents into the action-weighted extension preserves
periods. -/
theorem exists_period_rescale_inl :
    ∃ c > 0, ∀ g, E.coprod (AddMonoidHom.id ℝ) (AddMonoidHom.inl G ℝ g) = c * E g :=
  ⟨1, one_pos, fun g => by simp⟩

/-- The residues before and after the action-weighted extension are compatible: the coefficient
inclusion `g ↦ (g, 0)` sends the residue in `R[ker E]` to its image under the inclusion
`ker E ⊆ G`. -/
theorem residueEquivCoprodId_mk_mapNonnegSubring_inl (a : nonnegSubring R E) :
    residueEquivCoprodId R E (Ideal.Quotient.mk _
        (mapNonnegSubring (RingHom.id R) (AddMonoidHom.inl G ℝ) exists_period_rescale_inl a)) =
      AddMonoidAlgebra.mapDomain (mker E).subtype (residue R E a) := by
  rw [residueEquivCoprodId, RingEquiv.trans_apply, residueEquiv_mk, residue_mapNonnegSubring,
    AddMonoidAlgebra.mapRingHom_id, RingHom.id_apply]
  -- The restriction of `g ↦ (g, 0)` to `ker E`, followed by `(g, -E g) ↦ g`, is the inclusion.
  induction residue R E a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [_root_.map_add, AddMonoidAlgebra.mapDomain_add, hx, hy]
  | single k r => simp

end ActionWeight

end Ring

section Grading

variable [CommRing R] [AddMonoid H] {N : H →+ ℝ} {ι : Type*} {f : H → ι} {i : ι}

/-- The residue of a homogeneous series of degree `i` is homogeneous of degree `i` in the group
ring of the period kernel. -/
theorem residue_mem_gradeBy {a : nonnegSubring R N}
    (ha : (a : NovikovSeries R H N) ∈ gradeBy R N f i) :
    residue R N a ∈ AddMonoidAlgebra.gradeBy R (fun k : mker N => f k) i := by
  rw [AddMonoidAlgebra.mem_gradeBy_iff]
  intro k hk
  rw [Finset.mem_coe, Finsupp.mem_support_iff, coeff_residue] at hk
  exact mem_gradeBy_iff.1 ha (mem_support.2 hk)

/-- The image of a homogeneous element of the group ring of the period kernel is a homogeneous
series of the same degree. -/
theorem ofMker_mem_gradeBy {x : AddMonoidAlgebra R (mker N)}
    (hx : x ∈ AddMonoidAlgebra.gradeBy R (fun k : mker N => f k) i) :
    (ofMker R N x : NovikovSeries R H N) ∈ gradeBy R N f i := by
  rw [mem_gradeBy_iff]
  intro h hh
  rw [mem_support] at hh
  by_cases hN : N h = 0
  · lift h to mker N using mem_mker.2 hN
    rw [coeff_ofMker_coe] at hh
    rw [AddMonoidAlgebra.mem_gradeBy_iff] at hx
    exact hx (Finsupp.mem_support_iff.2 hh)
  · exact absurd (coeff_ofMker_of_ne_zero x hN) hh

/-- After the action-weighted extension, the residue of a homogeneous series of degree `i`, for
a degree `μ` of the first component, is homogeneous of degree `i` in `R[G]`. -/
theorem residueEquivCoprodId_mk_mem_gradeBy {G : Type*} [AddMonoid G] {E : G →+ ℝ}
    {μ : G → ι} {a : nonnegSubring R (E.coprod (AddMonoidHom.id ℝ))}
    (ha : (a : NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))) ∈
      gradeBy R (E.coprod (AddMonoidHom.id ℝ)) (fun p => μ p.1) i) :
    residueEquivCoprodId R E (Ideal.Quotient.mk _ a) ∈ AddMonoidAlgebra.gradeBy R μ i := by
  rw [AddMonoidAlgebra.mem_gradeBy_iff]
  intro g hg
  rw [Finset.mem_coe, Finsupp.mem_support_iff, coeff_residueEquivCoprodId_mk] at hg
  exact mem_gradeBy_iff.1 ha (mem_support.2 hg)

end Grading

end NovikovSeries

end TauCeti

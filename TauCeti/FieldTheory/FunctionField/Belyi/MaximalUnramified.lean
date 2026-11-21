/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.FieldTheory.FunctionField.Belyi.Basic
public import TauCeti.FieldTheory.Galois.Quotient
public import TauCeti.FieldTheory.RatFunc.Map
public import TauCeti.FieldTheory.RatFunc.Mobius
-- Proof-only: branch-point permutation transport, semilinear conjugation, radical Belyi pairs,
-- and integral closedness of algebraically closed constant fields.
import TauCeti.FieldTheory.FunctionField.Belyi.BranchPoints
import TauCeti.FieldTheory.FunctionField.Belyi.Conjugation
import TauCeti.FieldTheory.FunctionField.Belyi.Radical
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The maximal extension unramified outside `0`, `1` and `∞` and the geometric fundamental group

For a characteristic-zero field `k` and extension `M / k(t)`, `TauCeti.maximalBelyiExtension k M`
is the compositum in `M` of all finite intermediate fields `E / k(t)` that are algebraic Belyi
pairs over `k`. When `k` is algebraically closed, finite Belyi subextensions are closed under
composita and normal closures (`TauCeti.isIntegrallyClosedIn_of_isAlgClosed`), forming a directed
system. Over any characteristic-zero `k`, `maximalBelyiExtension k M / k(t)` is Galois whenever
`M / k(t)` is normal, has infinite degree when `M` is algebraically closed, and is invariant under
semilinear coefficient isomorphisms and `S₃` branch-point permutations.

For `M = AlgebraicClosure (RatFunc k)`, `TauCeti.BelyiGeometricFundamentalGroup k` is the profinite
Krull Galois group `Gal(maximalBelyiExtension k M / k(t))` — over algebraically closed `k`, the
étale geometric fundamental group `π₁^ét(ℙ¹_k \ {0, 1, ∞})`, whose open (normal) subgroups
correspond to finite (Galois) algebraic Belyi extensions of `k(t)`.

## Main definitions

* `TauCeti.maximalBelyiExtension`, `TauCeti.liftMaximalBelyiExtension`: maximal Belyi extension in
  `M` and lifting embeddings of finite algebraic Belyi pairs into it.
* `TauCeti.BelyiGeometricFundamentalGroup`, `fixingOpenSubgroup`, `restrictNormalHom`,
  `restrictNormalOpenNormalSubgroup`, `quotientKerRestrictNormalHomEquiv`: `π₁^ét(ℙ¹_k \ {0, 1, ∞})`
  and its open (normal) subgroups and finite Galois quotients.

## Main results

* `TauCeti.mem_maximalBelyiExtension_iff`, `TauCeti.le_maximalBelyiExtension_iff`,
  `TauCeti.IsAlgebraicBelyiPair.of_algHom_maximalBelyiExtension`,
  `TauCeti.isAlgebraicBelyiPair_intermediateField_maximalBelyiExtension`: characterization over
  algebraically closed `k`.
* `TauCeti.normal_maximalBelyiExtension`, `TauCeti.isGalois_maximalBelyiExtension`: normality and
  Galoisness over `RatFunc k` when `M / RatFunc k` is normal.
* `TauCeti.mem_maximalBelyiExtension_of_pow_eq`, `not_finiteDimensional_maximalBelyiExtension`,
  `BelyiGeometricFundamentalGroup.instInfinite`: radical elements, infinite degree, infinite order.
* `TauCeti.map_maximalBelyiExtension_of_mapRingEquiv`,
  `TauCeti.map_maximalBelyiExtension_of_branchPointAut`: semilinear and `S₃` invariance.
* `BelyiGeometricFundamentalGroup.fixedField_fixingOpenSubgroup`,
  `BelyiGeometricFundamentalGroup.fixedField_restrictNormalOpenNormalSubgroup`,
  `BelyiGeometricFundamentalGroup.restrictNormalHom_restrictNormalHom`,
  `BelyiGeometricFundamentalGroup.exists_fixingOpenSubgroup_eq`,
  `BelyiGeometricFundamentalGroup.exists_restrictNormalOpenNormalSubgroup_eq`: fixed-field
  recovery, tower compatibility, and open (normal) subgroup correspondence.

## References

* A. Grothendieck, *Esquisse d'un Programme* (1984), LMS Lecture Note Series 242, 1997, pp. 5–48.
* T. Szamuely, *Galois Groups and Fundamental Groups*, Cambridge Studies in Advanced Mathematics
  117, Cambridge University Press, 2009, §4.6–4.7.
-/

public section

open Polynomial
open scoped IntermediateField

namespace TauCeti

/-! ### The maximal Belyi extension inside an ambient overfield -/

section MaximalBelyiExtension

variable (k M : Type*) [Field k] [CharZero k] [Field M] [Algebra k M] [Algebra (RatFunc k) M]
  [IsScalarTower k (RatFunc k) M]

/-- The **maximal Belyi extension** of `k(t)` inside `M`: the compositum of all finite intermediate
fields of `M / k(t)` that are algebraic Belyi pairs over `k`. -/
noncomputable def maximalBelyiExtension : IntermediateField (RatFunc k) M :=
  ⨆ (E : IntermediateField (RatFunc k) M) (_ : FiniteDimensional (RatFunc k) E)
    (_ : IsAlgebraicBelyiPair k E), E

theorem maximalBelyiExtension_def :
    maximalBelyiExtension k M = ⨆ (E : IntermediateField (RatFunc k) M)
      (_ : FiniteDimensional (RatFunc k) E) (_ : IsAlgebraicBelyiPair k E), E := (rfl)

private abbrev BelyiSubextension :=
  {E : IntermediateField (RatFunc k) M //
    ∃ _ : FiniteDimensional (RatFunc k) E, IsAlgebraicBelyiPair k E}

private instance : Nonempty (BelyiSubextension k M) :=
  ⟨⟨⊥, inferInstance, isAlgebraicBelyiPair_bot k M⟩⟩

private theorem maximalBelyiExtension_eq_iSup_belyiSubextension :
    maximalBelyiExtension k M = ⨆ i : BelyiSubextension k M, i.val :=
  le_antisymm
    (iSup_le fun E ↦ iSup_le fun hfin ↦ iSup_le fun hB ↦
      le_iSup (fun i : BelyiSubextension k M ↦ i.val) ⟨E, hfin, hB⟩)
    (iSup_le fun ⟨E, hfin, hB⟩ ↦ le_iSup_of_le E (le_iSup_of_le hfin (le_iSup_of_le hB le_rfl)))

variable {k M}

/-- Every finite Belyi subextension of `M` lies inside `maximalBelyiExtension k M`. -/
theorem le_maximalBelyiExtension {E : IntermediateField (RatFunc k) M}
    [hfin : FiniteDimensional (RatFunc k) E] (hE : IsAlgebraicBelyiPair k E) :
    E ≤ maximalBelyiExtension k M :=
  le_iSup_of_le E (le_iSup_of_le hfin (le_iSup_of_le hE le_rfl))

@[simp]
theorem maximalBelyiExtension_le_iff {L : IntermediateField (RatFunc k) M} :
    maximalBelyiExtension k M ≤ L ↔
      ∀ (E : IntermediateField (RatFunc k) M) (_ : FiniteDimensional (RatFunc k) E),
        IsAlgebraicBelyiPair k E → E ≤ L := by
  rw [maximalBelyiExtension_def]; simp only [iSup_le_iff]

section Lift

variable {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FiniteDimensional (RatFunc k) F] (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] M)
include hF f

/-- The image in `M` of any `k(t)`-embedding of an algebraic Belyi pair `F` lies in
`maximalBelyiExtension k M`. -/
theorem fieldRange_le_maximalBelyiExtension : f.fieldRange ≤ maximalBelyiExtension k M :=
  have := Module.Finite.equiv f.equivFieldRange.toLinearEquiv
  le_maximalBelyiExtension (hF.of_algEquiv f.equivFieldRange)

/-- Lift a `k(t)`-embedding `f : F →ₐ[RatFunc k] M` of an algebraic Belyi pair `F` into
`maximalBelyiExtension k M`. -/
noncomputable def liftMaximalBelyiExtension : F →ₐ[RatFunc k] ↥(maximalBelyiExtension k M) :=
  f.codRestrict (maximalBelyiExtension k M).toSubalgebra fun x ↦
    fieldRange_le_maximalBelyiExtension hF f ⟨x, rfl⟩

@[simp]
theorem coe_liftMaximalBelyiExtension_apply (x : F) :
    (liftMaximalBelyiExtension hF f x : M) = f x := (rfl)

@[simp]
theorem val_comp_liftMaximalBelyiExtension :
    (maximalBelyiExtension k M).val.comp (liftMaximalBelyiExtension hF f) = f :=
  AlgHom.ext fun _ ↦ rfl

end Lift

instance isAlgebraic_maximalBelyiExtension :
    Algebra.IsAlgebraic (RatFunc k) ↥(maximalBelyiExtension k M) :=
  have := IntermediateField.isAlgebraic_iSup (t := fun i : BelyiSubextension k M ↦ i.val)
    fun i ↦ have := i.property.1; inferInstance
  let e := IntermediateField.equivOfEq (maximalBelyiExtension_eq_iSup_belyiSubextension k M)
  Algebra.IsAlgebraic.of_injective e.toAlgHom e.injective

instance isSeparable_maximalBelyiExtension :
    Algebra.IsSeparable (RatFunc k) ↥(maximalBelyiExtension k M) :=
  have : CharZero (RatFunc k) := charZero_of_injective_algebraMap (algebraMap k _).injective
  inferInstance

section IsAlgClosed

variable [IsAlgClosed k]

instance isIntegrallyClosedIn_maximalBelyiExtension :
    IsIntegrallyClosedIn k ↥(maximalBelyiExtension k M) := isIntegrallyClosedIn_of_isAlgClosed

private theorem directed_belyiSubextension :
    Directed (· ≤ ·) (fun i : BelyiSubextension k M ↦ i.val) := fun ⟨E₁, _, hB₁⟩ ⟨E₂, _, hB₂⟩ ↦
  ⟨⟨E₁ ⊔ E₂, inferInstance, (isAlgebraicBelyiPair_sup_iff E₁ E₂).mpr ⟨hB₁, hB₂⟩⟩,
    le_sup_left, le_sup_right⟩

/-- Over algebraically closed `k`, `x ∈ maximalBelyiExtension k M` iff `x` belongs to some finite
Belyi subextension of `M`. -/
theorem mem_maximalBelyiExtension_iff {x : M} :
    x ∈ maximalBelyiExtension k M ↔
      ∃ E : IntermediateField (RatFunc k) M,
        ∃ _ : FiniteDimensional (RatFunc k) E, IsAlgebraicBelyiPair k E ∧ x ∈ E := by
  rw [← SetLike.mem_coe, maximalBelyiExtension_eq_iSup_belyiSubextension,
    IntermediateField.coe_iSup_of_directed directed_belyiSubextension, Set.mem_iUnion]
  exact ⟨fun ⟨⟨E, hfin, hB⟩, hx⟩ ↦ ⟨E, hfin, hB, hx⟩, fun ⟨E, hfin, hB, hx⟩ ↦ ⟨⟨E, hfin, hB⟩, hx⟩⟩

/-- Over algebraically closed `k`, a finite intermediate field of `M / k(t)` lies in
`maximalBelyiExtension k M` iff it is an algebraic Belyi pair. -/
@[simp]
theorem le_maximalBelyiExtension_iff (E : IntermediateField (RatFunc k) M)
    [FiniteDimensional (RatFunc k) E] :
    E ≤ maximalBelyiExtension k M ↔ IsAlgebraicBelyiPair k E := by
  refine ⟨fun hle ↦ ?_, le_maximalBelyiExtension⟩
  let b := Module.finBasis (RatFunc k) E
  choose F hfin hBF hmem using fun i ↦ mem_maximalBelyiExtension_iff.mp (hle (b i).property)
  refine IsAlgebraicBelyiPair.of_le (E₂ := ⨆ i, F i) (fun y hy ↦ ?_)
    ((isAlgebraicBelyiPair_iSup_iff F).mpr hBF)
  have hy' := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩).symm
  push_cast at hy'
  rw [hy']
  exact (⨆ i, F i).sum_mem fun i _ ↦ (⨆ j, F j).smul_mem (le_iSup F i (hmem i))

/-- Over algebraically closed `k`, any finite extension `F / k(t)` admitting a `k(t)`-embedding into
`maximalBelyiExtension k M` is an algebraic Belyi pair. -/
theorem IsAlgebraicBelyiPair.of_algHom_maximalBelyiExtension {F : Type*} [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (f : F →ₐ[RatFunc k] ↥(maximalBelyiExtension k M)) : IsAlgebraicBelyiPair k F :=
  let g : F →ₐ[RatFunc k] M := (maximalBelyiExtension k M).val.comp f
  have := g.equivFieldRange.toLinearEquiv.finiteDimensional
  ((le_maximalBelyiExtension_iff g.fieldRange).mp fun _ ⟨x, hx⟩ ↦ hx ▸ (f x).property).of_algEquiv
    g.equivFieldRange.symm

/-- Over algebraically closed `k`, every finite intermediate field of `maximalBelyiExtension k M`
over `k(t)` is an algebraic Belyi pair. -/
theorem isAlgebraicBelyiPair_intermediateField_maximalBelyiExtension
    (E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M))
    [FiniteDimensional (RatFunc k) E] : IsAlgebraicBelyiPair k E :=
  .of_algHom_maximalBelyiExtension E.val

/-- Over algebraically closed `k`, `maximalBelyiExtension k M` is the compositum of the normal
closures in `M` of all finite Belyi subextensions of `M`. -/
theorem maximalBelyiExtension_eq_iSup_normalClosure :
    maximalBelyiExtension k M =
      ⨆ (E : IntermediateField (RatFunc k) M) (_ : FiniteDimensional (RatFunc k) E)
        (_ : IsAlgebraicBelyiPair k E), IntermediateField.normalClosure (RatFunc k) E M :=
  le_antisymm
    (iSup_le fun E ↦ iSup_le fun hfin ↦ iSup_le fun hB ↦
      le_iSup_of_le E (le_iSup_of_le hfin (le_iSup_of_le hB fun x hx ↦
        E.val.fieldRange_le_normalClosure ⟨⟨x, hx⟩, rfl⟩)))
    (iSup_le fun E ↦ iSup_le fun _ ↦ iSup_le fun hB ↦
      le_maximalBelyiExtension ((isAlgebraicBelyiPair_normalClosure_iff E).mpr hB))

/-! ### Radical elements and infinite degree -/

/-- Over algebraically closed `k`, every `n`-th root (`n ≠ 0`) in `M` of `u ∈ k(t)` with
`n ∣ P.ord u` at every unmarked place belongs to `maximalBelyiExtension k M`. -/
theorem mem_maximalBelyiExtension_of_pow_eq {y : M} {n : ℕ} {u : RatFunc k} (hn : n ≠ 0)
    (hy : y ^ n = algebraMap (RatFunc k) M u)
    (hdvd : ∀ P ∉ Place.zeroOneInfty k, (n : ℤ) ∣ P.ord u) : y ∈ maximalBelyiExtension k M := by
  obtain ⟨_, hB⟩ := isAlgebraicBelyiPair_adjoin_of_pow_eq hn hy hdvd
  exact le_maximalBelyiExtension hB (IntermediateField.mem_adjoin_simple_self (RatFunc k) y)

/-- Over algebraically closed `k`, every `n`-th root (`n ≠ 0`) of `c t ^ a (t - 1) ^ b` (`c ≠ 0`)
belongs to `maximalBelyiExtension k M`. -/
theorem mem_maximalBelyiExtension_of_pow_eq_X_zpow_mul_X_sub_one_zpow
    {y : M} {n : ℕ} {c : k} (hn : n ≠ 0) (hc : c ≠ 0) (a b : ℤ)
    (hy : y ^ n = algebraMap (RatFunc k) M
      (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b)) :
    y ∈ maximalBelyiExtension k M :=
  mem_maximalBelyiExtension_of_pow_eq hn hy fun _ hP ↦ by
    rw [Place.ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow_of_notMem_zeroOneInfty hP hc]
    exact dvd_zero _

/-- Over algebraically closed `k`, every `n`-th root (`n ≠ 0`) of `t` lies in
`maximalBelyiExtension k M`. -/
theorem mem_maximalBelyiExtension_of_pow_eq_X {y : M} {n : ℕ} (hn : n ≠ 0)
    (hy : y ^ n = algebraMap (RatFunc k) M RatFunc.X) : y ∈ maximalBelyiExtension k M :=
  mem_maximalBelyiExtension_of_pow_eq_X_zpow_mul_X_sub_one_zpow hn one_ne_zero 1 0 (by simpa)

/-- Over algebraically closed `k`, every `n`-th root (`n ≠ 0`) of `t - 1` lies in
`maximalBelyiExtension k M`. -/
theorem mem_maximalBelyiExtension_of_pow_eq_X_sub_one {y : M} {n : ℕ} (hn : n ≠ 0)
    (hy : y ^ n = algebraMap (RatFunc k) M (RatFunc.X - 1)) : y ∈ maximalBelyiExtension k M :=
  mem_maximalBelyiExtension_of_pow_eq_X_zpow_mul_X_sub_one_zpow hn one_ne_zero 0 1
    (by simpa [map_sub, map_one] using hy)

end IsAlgClosed

/-- When `M` is algebraically closed, `maximalBelyiExtension k M` has infinite degree over `k(t)`
for every field `k` of characteristic zero. -/
theorem not_finiteDimensional_maximalBelyiExtension [IsAlgClosed M] :
    ¬ FiniteDimensional (RatFunc k) ↥(maximalBelyiExtension k M) := fun _ ↦ by
  set n := Module.finrank (RatFunc k) ↥(maximalBelyiExtension k M) + 1
  have : NeZero n := ⟨Nat.succ_ne_zero _⟩
  let φ : AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k)) →ₐ[RatFunc k] M := IsAlgClosed.lift
  have hle := fieldRange_le_maximalBelyiExtension
    (isAlgebraicBelyiPair_adjoinRoot_X_pow_sub_C_X k n) φ
  have h1 := LinearMap.finrank_le_finrank_of_injective
    (f := (IntermediateField.inclusion hle).toLinearMap) (IntermediateField.inclusion hle).injective
  have h2 := (LinearEquiv.finrank_eq φ.equivFieldRange.toLinearEquiv.symm).trans
    (finrank_adjoinRoot_X_pow_sub_C_X k n)
  omega

end MaximalBelyiExtension

/-! ### Symmetries: coefficient conjugation and branch-point permutations -/

section Symmetries

private theorem map_maximalBelyiExtension_le_of_ringEquiv
    {k k' M M' : Type*} [Field k] [CharZero k] [Field k'] [CharZero k']
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [Field M'] [Algebra k' M'] [Algebra (RatFunc k') M'] [IsScalarTower k' (RatFunc k') M']
    (φ : RatFunc k ≃+* RatFunc k') (τ : M ≃+* M')
    (hτ : ∀ x, τ (algebraMap (RatFunc k) M x) = algebraMap (RatFunc k') M' (φ x))
    (hB : ∀ {E : IntermediateField (RatFunc k) M} {E' : IntermediateField (RatFunc k') M'}
      [FiniteDimensional (RatFunc k) E] [FiniteDimensional (RatFunc k') E']
      (e : E ≃+* E'), (∀ x : E, (e x : M') = τ x) →
      IsAlgebraicBelyiPair k E → IsAlgebraicBelyiPair k' E') :
    (maximalBelyiExtension k M).toSubfield.map τ.toRingHom ≤
      (maximalBelyiExtension k' M').toSubfield := by
  let P : IntermediateField (RatFunc k) M :=
    ((maximalBelyiExtension k' M').toSubfield.comap τ.toRingHom).toIntermediateField fun x ↦ by
      rw [Subfield.mem_comap, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hτ]
      exact (maximalBelyiExtension k' M').algebraMap_mem _
  have hle : maximalBelyiExtension k M ≤ P := maximalBelyiExtension_le_iff.mpr fun E hfin hE ↦ by
    let E' : IntermediateField (RatFunc k') M' :=
      (E.toSubfield.map τ.toRingHom).toIntermediateField fun x' ↦
        Subfield.mem_map.mpr ⟨algebraMap (RatFunc k) M (φ.symm x'),
          (E.mem_toSubfield _).mpr (E.algebraMap_mem _), by
            rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hτ, φ.apply_symm_apply]⟩
    let τE : E ≃+* E' := τ.restrict E E' fun x ↦ by
      dsimp only [E']
      rw [← IntermediateField.mem_toSubfield, ← IntermediateField.mem_toSubfield (s := _),
        Subfield.toIntermediateField_toSubfield, RingEquiv.toRingHom_eq_coe, ← RingHom.coe_coe,
        Subfield.map_mem_map]
    have : FiniteDimensional (RatFunc k') E' :=
      .of_equiv_equiv φ τE (RingHom.ext fun x ↦ (Subtype.ext (hτ x)).symm)
    exact fun y hy ↦ le_maximalBelyiExtension (hB τE (fun _ ↦ rfl) hE) ⟨y, hy, rfl⟩
  exact Subfield.map_le_iff_le_comap.mpr fun x hx ↦ hle hx

section MapRingEquiv

variable {k k' M M' : Type*} [Field k] [CharZero k] [Field k'] [CharZero k']
  [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
  [Field M'] [Algebra k' M'] [Algebra (RatFunc k') M'] [IsScalarTower k' (RatFunc k') M']
  (σ : k ≃+* k') (τ : M ≃+* M')
  (hτ : ∀ x, τ (algebraMap (RatFunc k) M x) =
    algebraMap (RatFunc k') M' (RatFunc.mapRingEquiv σ x))
include hτ

private theorem map_maximalBelyiExtension_le_of_mapRingEquiv :
    (maximalBelyiExtension k M).toSubfield.map τ.toRingHom ≤
      (maximalBelyiExtension k' M').toSubfield :=
  map_maximalBelyiExtension_le_of_ringEquiv (RatFunc.mapRingEquiv σ) τ hτ fun e he hE ↦
    hE.of_mapRingEquiv σ e fun x ↦ Subtype.ext ((he _).trans (hτ x))

/-- **Semilinear invariance of the maximal Belyi extension**: if `τ : M ≃+* M'` lifts
`RatFunc.mapRingEquiv σ`, then `τ` carries `maximalBelyiExtension k M` onto
`maximalBelyiExtension k' M'`. -/
theorem map_maximalBelyiExtension_of_mapRingEquiv :
    (maximalBelyiExtension k M).toSubfield.map τ.toRingHom =
      (maximalBelyiExtension k' M').toSubfield := by
  refine le_antisymm (map_maximalBelyiExtension_le_of_mapRingEquiv σ τ hτ) fun z hz ↦ ?_
  have hle := map_maximalBelyiExtension_le_of_mapRingEquiv σ.symm τ.symm fun x' ↦
    τ.symm_apply_eq.mpr (by rw [hτ, ← RatFunc.mapRingEquiv_symm, RingEquiv.apply_symm_apply])
  exact ⟨τ.symm z, hle ⟨z, hz, rfl⟩, τ.apply_symm_apply z⟩

/-- Elementwise form of `TauCeti.map_maximalBelyiExtension_of_mapRingEquiv`. -/
theorem apply_mem_maximalBelyiExtension_iff_of_mapRingEquiv {y : M} :
    τ y ∈ maximalBelyiExtension k' M' ↔ y ∈ maximalBelyiExtension k M := by
  rw [← IntermediateField.mem_toSubfield, ← map_maximalBelyiExtension_of_mapRingEquiv σ τ hτ,
    RingEquiv.toRingHom_eq_coe, ← RingHom.coe_coe, Subfield.map_mem_map,
    IntermediateField.mem_toSubfield]

end MapRingEquiv

/-- When `M / k(t)` is normal (over any characteristic-zero field `k`), `maximalBelyiExtension k M`
is normal over `k(t)`. -/
instance normal_maximalBelyiExtension {k M : Type*} [Field k] [CharZero k]
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [Normal (RatFunc k) M] : Normal (RatFunc k) ↥(maximalBelyiExtension k M) :=
  IntermediateField.normal_iff_forall_map_le'.mpr fun τ _ ⟨_, hx, h⟩ ↦ h ▸
    (apply_mem_maximalBelyiExtension_iff_of_mapRingEquiv (RingEquiv.refl k) τ.toRingEquiv
      fun z ↦ by rw [RatFunc.mapRingEquiv_refl, RingEquiv.refl_apply]; exact τ.commutes z).mpr hx

/-- When `M / k(t)` is normal (over any characteristic-zero field `k`), `maximalBelyiExtension k M`
is a Galois extension of `k(t)`. -/
instance isGalois_maximalBelyiExtension {k M : Type*} [Field k] [CharZero k]
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [Normal (RatFunc k) M] : IsGalois (RatFunc k) ↥(maximalBelyiExtension k M) :=
  have : CharZero (RatFunc k) := charZero_of_injective_algebraMap (algebraMap k _).injective
  ⟨⟩

section BranchPointAut

variable {k M M' : Type*} [Field k] [CharZero k]
  [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
  [Field M'] [Algebra k M'] [Algebra (RatFunc k) M'] [IsScalarTower k (RatFunc k) M']
  (ρ : Equiv.Perm (Fin 3)) (e : M ≃ₐ[k] M')
  (he : ∀ x, e (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
    algebraMap (RatFunc k) M' x)
include he

private theorem map_maximalBelyiExtension_le_of_branchPointAut :
    (maximalBelyiExtension k M).toSubfield.map e.toRingHom ≤
      (maximalBelyiExtension k M').toSubfield := by
  have he_inv (x : RatFunc k) :
      e (algebraMap (RatFunc k) M x) =
        algebraMap (RatFunc k) M' (RatFunc.branchPointAut k ρ⁻¹ x) := by
    rw [← he, ← AlgEquiv.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, AlgEquiv.one_apply]
  refine map_maximalBelyiExtension_le_of_ringEquiv
    (RatFunc.branchPointAut k ρ⁻¹).toRingEquiv e.toRingEquiv he_inv fun {E} {E'} _ _ e' he' hE ↦ ?_
  let eE : E ≃ₐ[k] E' := AlgEquiv.ofRingEquiv (f := e') fun c ↦ Subtype.ext <| by
    rw [he', AlgEquiv.coe_toRingEquiv, IsScalarTower.algebraMap_apply k (RatFunc k) E,
      IntermediateField.coe_algebraMap_apply, ← IsScalarTower.algebraMap_apply k (RatFunc k) M,
      e.commutes, IsScalarTower.algebraMap_apply k (RatFunc k) M',
      IsScalarTower.algebraMap_apply k (RatFunc k) E', IntermediateField.coe_algebraMap_apply]
  exact hE.of_branchPointAut ρ eE fun x ↦ Subtype.ext ((he' _).trans (he x))

/-- **Branch-point permutation invariance of the maximal Belyi extension**: if `e : M ≃ₐ[k] M'`
intertwines `RatFunc.branchPointAut k ρ` (`ρ ∈ S₃`) with the `k(t)`-algebra structures, then `e`
carries `maximalBelyiExtension k M` onto `maximalBelyiExtension k M'`. -/
theorem map_maximalBelyiExtension_of_branchPointAut :
    (maximalBelyiExtension k M).toSubfield.map e.toRingHom =
      (maximalBelyiExtension k M').toSubfield := by
  refine le_antisymm (map_maximalBelyiExtension_le_of_branchPointAut ρ e he) fun z hz ↦ ?_
  have hle := map_maximalBelyiExtension_le_of_branchPointAut ρ⁻¹ e.symm fun x ↦
    e.symm_apply_eq.mpr <| by
      rw [← he, ← AlgEquiv.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, AlgEquiv.one_apply]
  exact ⟨e.symm z, hle ⟨z, hz, rfl⟩, e.apply_symm_apply z⟩

/-- Elementwise form of `TauCeti.map_maximalBelyiExtension_of_branchPointAut`. -/
theorem apply_mem_maximalBelyiExtension_iff_of_branchPointAut {y : M} :
    e y ∈ maximalBelyiExtension k M' ↔ y ∈ maximalBelyiExtension k M := by
  rw [← IntermediateField.mem_toSubfield, ← map_maximalBelyiExtension_of_branchPointAut ρ e he,
    RingEquiv.toRingHom_eq_coe, ← AlgEquiv.coe_toRingEquiv, ← RingHom.coe_coe,
    Subfield.map_mem_map, IntermediateField.mem_toSubfield]

end BranchPointAut

end Symmetries

/-! ### The algebraic geometric fundamental group of `ℙ¹_k \ {0, 1, ∞}` -/

/-- The Galois group `Gal(maximalBelyiExtension k (AlgebraicClosure (RatFunc k)) / RatFunc k)` with
its Krull topology. When `k` is algebraically closed of characteristic zero, this is the étale
**geometric fundamental group** `π₁^ét(ℙ¹_k \ {0, 1, ∞})`; over a general characteristic-zero field
`F`, the geometric fundamental group is `BelyiGeometricFundamentalGroup (AlgebraicClosure F)`
(acted on by `Field.absoluteGaloisGroup F` via `TauCeti.belyiAbsoluteGaloisGroupOuterAction F`). -/
-- `[IsAlgClosed k]` is documented rather than assumed here: `maximalBelyiExtension` consumes no
-- such argument, so carrying it on the `abbrev` is rejected by `unusedArguments`.
abbrev BelyiGeometricFundamentalGroup (k : Type*) [Field k] [CharZero k] :=
  Gal(↥(maximalBelyiExtension k (AlgebraicClosure (RatFunc k)))/RatFunc k)

namespace BelyiGeometricFundamentalGroup

variable {k : Type*} [Field k] [CharZero k]

local notation "Ωk" => maximalBelyiExtension k (AlgebraicClosure (RatFunc k))
local notation "BelyiG" => BelyiGeometricFundamentalGroup k

section FiniteBelyi

variable {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FiniteDimensional (RatFunc k) F] (hF : IsAlgebraicBelyiPair k F)
  (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k))
include hF f

local notation "liftF" => liftMaximalBelyiExtension hF f

/-- The open subgroup of `BelyiGeometricFundamentalGroup k` cut out by an embedding
`f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)` of a finite algebraic Belyi pair `F`. -/
noncomputable def fixingOpenSubgroup : OpenSubgroup BelyiG where
  toSubgroup := (liftF).fieldRange.fixingSubgroup
  isOpen' :=
    have := (liftF).equivFieldRange.toLinearEquiv.finiteDimensional
    (liftF).fieldRange.fixingSubgroup_isOpen

/-- The carrier subgroup of `fixingOpenSubgroup hF f` is the fixing subgroup of the lifted image. -/
@[simp]
theorem fixingOpenSubgroup_toSubgroup :
    (fixingOpenSubgroup hF f).toSubgroup = (liftF).fieldRange.fixingSubgroup := (rfl)

/-- An element of `BelyiGeometricFundamentalGroup k` lies in `fixingOpenSubgroup hF f` iff it fixes
the lifted image of every `x : F`. -/
@[simp]
theorem mem_fixingOpenSubgroup_iff {γ : BelyiG} :
    γ ∈ fixingOpenSubgroup hF f ↔ ∀ x : F, γ (liftF x) = liftF x := by
  rw [← OpenSubgroup.mem_toSubgroup, fixingOpenSubgroup_toSubgroup,
    IntermediateField.mem_fixingSubgroup_iff]; simp

/-- The fixed field of `fixingOpenSubgroup hF f` in
`maximalBelyiExtension k (AlgebraicClosure (RatFunc k))` is the field range of
`liftMaximalBelyiExtension hF f`. -/
theorem fixedField_fixingOpenSubgroup :
    IntermediateField.fixedField (fixingOpenSubgroup hF f).toSubgroup = (liftF).fieldRange := by
  rw [fixingOpenSubgroup_toSubgroup, InfiniteGalois.fixedField_fixingSubgroup]

section Normal

variable [Normal (RatFunc k) F]

/-- Continuous surjective restriction homomorphism `BelyiGeometricFundamentalGroup k →*
Gal(F/RatFunc k)` induced by an embedding `f` of a finite normal algebraic Belyi pair `F`. -/
noncomputable def restrictNormalHom : BelyiG →* Gal(F/RatFunc k) := (liftF).restrictNormalHom

@[simp]
theorem restrictNormalHom_commutes (γ : BelyiG) (x : F) :
    f (restrictNormalHom hF f γ x) = (γ (liftF x) : AlgebraicClosure (RatFunc k)) :=
  congrArg Subtype.val ((liftF).restrictNormalHom_commutes γ x)

/-- Restriction `restrictNormalHom hF f` onto `Gal(F/RatFunc k)` is surjective. -/
theorem restrictNormalHom_surjective : Function.Surjective (restrictNormalHom hF f) :=
  (liftF).restrictNormalHom_surjective

/-- The kernel of `restrictNormalHom hF f` is the fixing subgroup of the lifted image of `F`. -/
theorem ker_restrictNormalHom :
    (restrictNormalHom hF f).ker = (liftF).fieldRange.fixingSubgroup :=
  (liftF).ker_restrictNormalHom

/-- Restriction `restrictNormalHom hF f` is continuous for the Krull topologies. -/
theorem continuous_restrictNormalHom : Continuous (restrictNormalHom hF f) :=
  (liftF).continuous_restrictNormalHom

/-- The kernel of `restrictNormalHom hF f` is open in `BelyiGeometricFundamentalGroup k`. -/
theorem isOpen_ker_restrictNormalHom : IsOpen ((restrictNormalHom hF f).ker : Set BelyiG) :=
  (liftF).isOpen_ker_restrictNormalHom

/-- The open normal subgroup of `BelyiGeometricFundamentalGroup k` cut out by an embedded finite
normal algebraic Belyi pair `F`, namely `(restrictNormalHom hF f).ker`. -/
noncomputable def restrictNormalOpenNormalSubgroup : OpenNormalSubgroup BelyiG where
  toSubgroup := (restrictNormalHom hF f).ker
  isOpen' := isOpen_ker_restrictNormalHom hF f
  isNormal' := (restrictNormalHom hF f).normal_ker

/-- The underlying subgroup of `restrictNormalOpenNormalSubgroup hF f` is
`(restrictNormalHom hF f).ker`. -/
@[simp]
theorem restrictNormalOpenNormalSubgroup_toSubgroup :
    (restrictNormalOpenNormalSubgroup hF f).toSubgroup = (restrictNormalHom hF f).ker := (rfl)

/-- The fixed field of `restrictNormalOpenNormalSubgroup hF f` in
`maximalBelyiExtension k (AlgebraicClosure (RatFunc k))` is the field range of
`liftMaximalBelyiExtension hF f`. -/
theorem fixedField_restrictNormalOpenNormalSubgroup :
    IntermediateField.fixedField (restrictNormalOpenNormalSubgroup hF f).toSubgroup =
      (liftF).fieldRange := by
  rw [restrictNormalOpenNormalSubgroup_toSubgroup, ker_restrictNormalHom,
    InfiniteGalois.fixedField_fixingSubgroup]

/-- Precomposing the base-point embedding `f` with `τ ∈ Gal(F/RatFunc k)` conjugates
`restrictNormalHom hF f` by `τ`. -/
theorem restrictNormalHom_comp (τ : Gal(F/RatFunc k)) (γ : BelyiG) :
    restrictNormalHom hF (f.comp (τ : F →ₐ[RatFunc k] F)) γ =
      τ⁻¹ * restrictNormalHom hF f γ * τ := (liftF).restrictNormalHom_comp τ γ

/-- **Restriction is transitive along composed embeddings of finite normal Belyi extensions**:
restricting `γ` along `f : F → AlgebraicClosure (RatFunc k)` and then along `h : E → F` is
restricting `γ` along `f ∘ h`. -/
@[simp]
theorem restrictNormalHom_restrictNormalHom {E : Type*} [Field E] [Algebra k E]
    [Algebra (RatFunc k) E] [IsScalarTower k (RatFunc k) E] [FiniteDimensional (RatFunc k) E]
    [Normal (RatFunc k) E] (h : E →ₐ[RatFunc k] F) (γ : BelyiG) :
    h.restrictNormalHom (restrictNormalHom hF f γ) =
      restrictNormalHom (hF.of_algHom h) (f.comp h) γ := by
  have hcomp : liftMaximalBelyiExtension (hF.of_algHom h) (f.comp h) = (liftF).comp h :=
    AlgHom.ext fun _ ↦ Subtype.ext rfl
  rw [restrictNormalHom, restrictNormalHom, hcomp, AlgHom.restrictNormalHom_restrictNormalHom]

/-- Topological quotient isomorphism
`BelyiGeometricFundamentalGroup k ⧸ (restrictNormalHom hF f).ker ≃ₜ* Gal(F/RatFunc k)`. -/
noncomputable def quotientKerRestrictNormalHomEquiv :
    BelyiG ⧸ (restrictNormalHom hF f).ker ≃ₜ* Gal(F/RatFunc k) :=
  (liftF).quotientKerRestrictNormalHomEquiv

@[simp]
theorem quotientKerRestrictNormalHomEquiv_mk (γ : BelyiG) :
    quotientKerRestrictNormalHomEquiv hF f (γ : BelyiG ⧸ (restrictNormalHom hF f).ker) =
      restrictNormalHom hF f γ := (liftF).quotientKerRestrictNormalHomEquiv_mk γ

/-- The inverse of `quotientKerRestrictNormalHomEquiv hF f` sends `restrictNormalHom hF f γ` back
to the quotient class of `γ`. -/
@[simp]
theorem quotientKerRestrictNormalHomEquiv_symm_restrictNormalHom (γ : BelyiG) :
    (quotientKerRestrictNormalHomEquiv hF f).symm (restrictNormalHom hF f γ) =
      (γ : BelyiG ⧸ (restrictNormalHom hF f).ker) :=
  (liftF).quotientKerRestrictNormalHomEquiv_symm_restrictNormalHom γ

end Normal

end FiniteBelyi

/-- **Galois correspondence for open subgroups of `BelyiGeometricFundamentalGroup k`**: over
algebraically closed `k`, every open subgroup `U` is `fixingOpenSubgroup` of its fixed field, a
finite algebraic Belyi subextension of `maximalBelyiExtension k (AlgebraicClosure (RatFunc k))`. -/
theorem exists_fixingOpenSubgroup_eq [IsAlgClosed k] (U : OpenSubgroup BelyiG) :
    ∃ (E : IntermediateField (RatFunc k) ↥Ωk) (_ : FiniteDimensional (RatFunc k) E)
      (hE : IsAlgebraicBelyiPair k E), fixingOpenSubgroup hE ((Ωk).val.comp E.val) = U := by
  let E : IntermediateField (RatFunc k) ↥Ωk := IntermediateField.fixedField U.toSubgroup
  have hE_fix : E.fixingSubgroup = U.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩
  have : FiniteDimensional (RatFunc k) E :=
    (InfiniteGalois.isOpen_iff_finite E).mp (hE_fix.symm ▸ U.isOpen)
  have hB : IsAlgebraicBelyiPair k E :=
    isAlgebraicBelyiPair_intermediateField_maximalBelyiExtension E
  have hlift : liftMaximalBelyiExtension hB ((Ωk).val.comp E.val) = E.val :=
    AlgHom.ext fun _ ↦ (Ωk).val.injective rfl
  refine ⟨E, inferInstance, hB, OpenSubgroup.toSubgroup_injective ?_⟩
  rw [fixingOpenSubgroup_toSubgroup, hlift, IntermediateField.fieldRange_val, hE_fix]

/-- **Galois correspondence for open normal subgroups of `BelyiGeometricFundamentalGroup k`**: over
algebraically closed `k`, every open normal subgroup `U` is `restrictNormalOpenNormalSubgroup` of
its fixed field, a finite Galois Belyi subextension. -/
theorem exists_restrictNormalOpenNormalSubgroup_eq [IsAlgClosed k] (U : OpenNormalSubgroup BelyiG) :
    ∃ (E : IntermediateField (RatFunc k) ↥Ωk) (_ : FiniteDimensional (RatFunc k) E)
      (_ : IsGalois (RatFunc k) E) (hE : IsAlgebraicBelyiPair k E),
      restrictNormalOpenNormalSubgroup hE ((Ωk).val.comp E.val) = U := by
  obtain ⟨E, _, hB, hU⟩ := exists_fixingOpenSubgroup_eq U.toOpenSubgroup
  have hlift : liftMaximalBelyiExtension hB ((Ωk).val.comp E.val) = E.val :=
    AlgHom.ext fun _ ↦ (Ωk).val.injective rfl
  have hfix : E.fixingSubgroup = U.toSubgroup := by
    have h := congrArg OpenSubgroup.toSubgroup hU
    rwa [fixingOpenSubgroup_toSubgroup, hlift, IntermediateField.fieldRange_val] at h
  have : IsGalois (RatFunc k) E :=
    (InfiniteGalois.normal_iff_isGalois E).mp (hfix.symm ▸ U.isNormal')
  refine ⟨E, inferInstance, inferInstance, hB, OpenNormalSubgroup.toSubgroup_injective ?_⟩
  dsimp only
  rw [restrictNormalOpenNormalSubgroup_toSubgroup, ker_restrictNormalHom, hlift,
    IntermediateField.fieldRange_val, hfix]

/-- `BelyiGeometricFundamentalGroup k` is infinite for every field `k` of characteristic zero. -/
instance instInfinite : Infinite BelyiG :=
  not_finite_iff_infinite.mp fun _ ↦
    not_finiteDimensional_maximalBelyiExtension
      (IsGalois.finiteDimensional_of_finite (RatFunc k) ↥Ωk)

end BelyiGeometricFundamentalGroup

end TauCeti

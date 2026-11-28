/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Basic
public import TauCeti.FieldTheory.RatFunc.Map
-- Proof-only: semilinear conjugation, radical Belyi pairs, and integral closedness of
-- algebraically closed constant fields.
import TauCeti.FieldTheory.FunctionField.Belyi.Conjugation
import TauCeti.FieldTheory.FunctionField.Belyi.Radical
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The maximal extension unramified outside `0`, `1` and `∞`

For a characteristic-zero field `k` and any overfield `M / k(t)`,
`TauCeti.maximalBelyiExtension k M` is the compositum in `M` of all finite intermediate fields
`E / k(t)` that are algebraic Belyi pairs over `k`. It generalizes
`TauCeti.maximalUnramifiedOutside` (whose open-normal-subgroup correspondence for algebraic `M` is
`TauCeti.maximalUnramifiedOutside.openNormalSubgroupEquiv`) in two ways: it works over an arbitrary
characteristic-zero constant field `k` by indexing over `TauCeti.IsAlgebraicBelyiPair k` (exact
constant field `k` plus unramifiedness outside `0`, `1`, `∞`), and it requires no algebraicity
assumption on the ambient field `M / k(t)`. When `k` is algebraically closed and `M / k(t)` is
algebraic, `maximalBelyiExtension k M` coincides with
`maximalUnramifiedOutside M (Place.zeroOneInfty k)`
(`TauCeti.FieldTheory.FunctionField.Belyi.FundamentalGroup`).

When `k` is algebraically closed, finite Belyi subextensions are closed under composita and normal
closures inside `M` (`TauCeti.isAlgebraicBelyiPair_sup_iff` and
`TauCeti.isAlgebraicBelyiPair_normalClosure_iff`), forming a directed system. Over any
characteristic-zero `k`, `maximalBelyiExtension k M` is Galois over `k(t)` when `M / k(t)` is normal
(`TauCeti.normal_maximalBelyiExtension`, `TauCeti.isGalois_maximalBelyiExtension`), has infinite
degree over `k(t)` when `M` is algebraically closed
(`TauCeti.not_finiteDimensional_maximalBelyiExtension`), and is invariant under semilinear
coefficient isomorphisms (`TauCeti.map_maximalBelyiExtension_of_mapRingEquiv`). The
Galois-theoretic fundamental group and open-subgroup correspondences live in
`TauCeti.FieldTheory.FunctionField.Belyi.FundamentalGroup`.

## Main definitions

* `TauCeti.maximalBelyiExtension`, `TauCeti.liftMaximalBelyiExtension`: maximal Belyi extension in
  `M` and lifting embeddings of finite algebraic Belyi pairs into it.

## Main results

* `TauCeti.mem_maximalBelyiExtension_iff`, `TauCeti.le_maximalBelyiExtension_iff`,
  `AlgHom.isAlgebraicBelyiPair_of_maximalBelyiExtension`,
  `TauCeti.isAlgebraicBelyiPair_intermediateField_maximalBelyiExtension`: characterization over
  algebraically closed `k`.
* `TauCeti.normal_maximalBelyiExtension`, `TauCeti.isGalois_maximalBelyiExtension`: normality and
  Galoisness over `RatFunc k` when `M / RatFunc k` is normal.
* `TauCeti.mem_maximalBelyiExtension_of_pow_eq`,
  `TauCeti.not_finiteDimensional_maximalBelyiExtension`: radical elements and infinite degree over
  algebraically closed `M`.
* `TauCeti.map_maximalBelyiExtension_of_mapRingEquiv`: semilinear invariance.

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

/-- Lifting `f ∘ h` into `maximalBelyiExtension k M` is composing the lift of `f` with `h`. -/
@[simp]
theorem liftMaximalBelyiExtension_comp {E : Type*} [Field E] [Algebra k E]
    [Algebra (RatFunc k) E] [IsScalarTower k (RatFunc k) E] (h : E →ₐ[RatFunc k] F) :
    letI : FiniteDimensional (RatFunc k) E :=
      Module.Finite.of_injective h.toLinearMap h.injective
    liftMaximalBelyiExtension (hF.of_algHom h) (f.comp h) =
      (liftMaximalBelyiExtension hF f).comp h :=
  AlgHom.ext fun _ ↦ Subtype.ext rfl

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
theorem _root_.AlgHom.isAlgebraicBelyiPair_of_maximalBelyiExtension {F : Type*} [Field F]
    [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FiniteDimensional (RatFunc k) F] (f : F →ₐ[RatFunc k] ↥(maximalBelyiExtension k M)) :
    IsAlgebraicBelyiPair k F :=
  let g : F →ₐ[RatFunc k] M := (maximalBelyiExtension k M).val.comp f
  have := g.equivFieldRange.toLinearEquiv.finiteDimensional
  ((le_maximalBelyiExtension_iff g.fieldRange).mp fun _ ⟨x, hx⟩ ↦ hx ▸ (f x).property).of_algEquiv
    g.equivFieldRange.symm

/-- Over algebraically closed `k`, every finite intermediate field of `maximalBelyiExtension k M`
over `k(t)` is an algebraic Belyi pair. -/
theorem isAlgebraicBelyiPair_intermediateField_maximalBelyiExtension
    (E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M))
    [FiniteDimensional (RatFunc k) E] : IsAlgebraicBelyiPair k E :=
  E.val.isAlgebraicBelyiPair_of_maximalBelyiExtension

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
    y ∈ maximalBelyiExtension k M := by
  obtain ⟨_, hB⟩ := isAlgebraicBelyiPair_adjoin_of_pow_eq_X_zpow_mul_X_sub_one_zpow hn hc a b hy
  exact le_maximalBelyiExtension hB (IntermediateField.mem_adjoin_simple_self (RatFunc k) y)

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

/-! ### Coefficient-conjugation invariance and normality -/

/-- General ring-equivalence inclusion for `maximalBelyiExtension`: if `τ : M ≃+* M'` lifts
`φ : RatFunc k ≃+* RatFunc k'` and carries finite Belyi subextensions to Belyi subextensions,
then `τ` maps `maximalBelyiExtension k M` into `maximalBelyiExtension k' M'`. -/
theorem map_maximalBelyiExtension_le_of_ringEquiv
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

end TauCeti

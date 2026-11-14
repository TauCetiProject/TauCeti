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

Let `k` be a field of characteristic zero and `M` an extension field of the rational function field
`k(t)`. Inside `M`, the finite subextensions `E / k(t)` that are algebraic Belyi pairs generate an
intermediate field `TauCeti.maximalBelyiExtension k M`.

Over a general field `k`, being an algebraic Belyi pair requires both unramifiedness away from the
three marked places `t = 0`, `t = 1` and `t = ∞` and exactness of the constant field `k`, and the
compositum of two Belyi pairs over `k` can enlarge the field of constants (for instance adjoining
`√t` and `√(c t)` adjoins `√c`). When `k` is algebraically closed, `k` is automatically integrally
closed in every domain extension (`TauCeti.isIntegrallyClosedIn_of_isAlgClosed`), so being an
algebraic Belyi pair reduces to unramifiedness outside `0`, `1` and `∞`
(`TauCeti.isAlgebraicBelyiPair_iff_of_isAlgClosed`). Consequently, over an algebraically closed
field `k`:

* finite Belyi subextensions of `M` are closed under binary and finite composita and under taking
  normal closures (`TauCeti.isAlgebraicBelyiPair_sup_iff`,
  `TauCeti.isAlgebraicBelyiPair_iSup_iff`, `TauCeti.isAlgebraicBelyiPair_normalClosure_iff`);
* finite Belyi subextensions form a directed system, so an element of `M` belongs to
  `maximalBelyiExtension k M` precisely when it lies in some finite Belyi subextension, and a
  finite subextension lies in `maximalBelyiExtension k M` precisely when it is itself a Belyi pair
  (`TauCeti.mem_maximalBelyiExtension_iff`, `TauCeti.le_maximalBelyiExtension_iff`,
  `TauCeti.IsAlgebraicBelyiPair.of_algHom_maximalBelyiExtension`);
* it coincides with the compositum of the normal closures of all finite Belyi subextensions of `M`
  (`TauCeti.maximalBelyiExtension_eq_iSup_normalClosure`).

Over any field `k` of characteristic zero, `maximalBelyiExtension k M` is a Galois extension of
`k(t)` whenever `M / k(t)` is normal (`TauCeti.normal_maximalBelyiExtension`,
`TauCeti.isGalois_maximalBelyiExtension`), and has infinite degree over `k(t)` whenever `M` is
algebraically closed (`TauCeti.not_finiteDimensional_maximalBelyiExtension`).

Taking `M = AlgebraicClosure (RatFunc k)` for an algebraically closed field `k` of characteristic
zero, the Galois group `Gal(maximalBelyiExtension k (AlgebraicClosure (RatFunc k)) / k(t))` is the
algebraic **geometric fundamental group** `TauCeti.BelyiGeometricFundamentalGroup k` of
`ℙ¹_k \ {0, 1, ∞}`: a profinite group of infinite order whose open subgroups and open normal
subgroups correspond to finite and finite Galois algebraic Belyi extensions of `k(t)`.

Both symmetries of the Belyi locus act on `maximalBelyiExtension`: semilinear ring isomorphisms of
`M` lifting coefficient isomorphisms `σ : k ≃+* k'` carry `maximalBelyiExtension k M` onto
`maximalBelyiExtension k' M'` (`TauCeti.map_maximalBelyiExtension_of_mapRingEquiv`), and
`k`-algebra isomorphisms permuting the three marked places via `RatFunc.branchPointAut` preserve it
(`TauCeti.map_maximalBelyiExtension_of_branchPointAut`). The former is what induces the arithmetic
outer Galois action in `TauCeti.FieldTheory.FunctionField.Belyi.OuterAction`.

## Main definitions

* `TauCeti.maximalBelyiExtension`: the compositum in `M` of all finite subextensions over `k(t)`
  that are algebraic Belyi pairs over `k`.
* `TauCeti.liftMaximalBelyiExtension`: lifting a `k(t)`-embedding `F →ₐ[RatFunc k] M` of an
  algebraic Belyi pair `F` into `maximalBelyiExtension k M`.
* `TauCeti.BelyiGeometricFundamentalGroup`: the Galois group of
  `maximalBelyiExtension k (AlgebraicClosure (RatFunc k))` over `RatFunc k` (for algebraically
  closed `k` of characteristic zero, `π₁^ét(ℙ¹_k \ {0, 1, ∞})`).
* `TauCeti.BelyiGeometricFundamentalGroup.fixingOpenSubgroup`,
  `TauCeti.BelyiGeometricFundamentalGroup.restrictNormalHom`,
  `TauCeti.BelyiGeometricFundamentalGroup.restrictNormalOpenNormalSubgroup`,
  `TauCeti.BelyiGeometricFundamentalGroup.quotientKerRestrictNormalHomEquiv`: open (normal)
  subgroups and finite Galois quotients cut out by embedded finite Belyi pairs.

## Main results

* `TauCeti.mem_maximalBelyiExtension_iff`, `TauCeti.le_maximalBelyiExtension_iff`,
  `TauCeti.IsAlgebraicBelyiPair.of_algHom_maximalBelyiExtension`,
  `TauCeti.isAlgebraicBelyiPair_intermediateField_maximalBelyiExtension`: elementwise and
  subextension characterizations of `maximalBelyiExtension` over algebraically closed `k`.
* `TauCeti.normal_maximalBelyiExtension`, `TauCeti.isGalois_maximalBelyiExtension`: normality and
  Galoisness of `maximalBelyiExtension k M` over `RatFunc k` when `M / RatFunc k` is normal.
* `TauCeti.mem_maximalBelyiExtension_of_pow_eq`,
  `TauCeti.mem_maximalBelyiExtension_of_pow_eq_X_zpow_mul_X_sub_one_zpow`,
  `TauCeti.not_finiteDimensional_maximalBelyiExtension`,
  `TauCeti.BelyiGeometricFundamentalGroup.instInfinite`: radical elements in
  `maximalBelyiExtension` and infinite degree / infinite order.
* `TauCeti.map_maximalBelyiExtension_of_mapRingEquiv`,
  `TauCeti.map_maximalBelyiExtension_of_branchPointAut`: invariance under coefficient conjugation
  and `S₃` branch-point permutations.
* `TauCeti.BelyiGeometricFundamentalGroup.exists_fixingOpenSubgroup_eq`,
  `TauCeti.BelyiGeometricFundamentalGroup.exists_restrictNormalOpenNormalSubgroup_eq`: every open
  (normal) subgroup of `BelyiGeometricFundamentalGroup k` over algebraically closed `k` comes from
  a finite (Galois) Belyi subextension.

## References

* A. Grothendieck, *Esquisse d'un Programme* (1984), in *Geometric Galois Actions*, Vol. 1, LMS
  Lecture Note Series 242, Cambridge University Press, 1997, pp. 5–48.
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

/-- The **maximal Belyi extension** of `k(t)` inside an overfield `M`: the compositum of all
finite intermediate fields of `M / k(t)` that are algebraic Belyi pairs over `k`.

When `k` is algebraically closed and `M` is an algebraic closure of `k(t)`, this is the maximal
algebraic extension of `k(t)` in `M` unramified outside `t = 0`, `t = 1` and `t = ∞`. -/
noncomputable def maximalBelyiExtension : IntermediateField (RatFunc k) M :=
  ⨆ (E : IntermediateField (RatFunc k) M) (_ : FiniteDimensional (RatFunc k) E)
    (_ : IsAlgebraicBelyiPair k E), E

theorem maximalBelyiExtension_def :
    maximalBelyiExtension k M =
      ⨆ (E : IntermediateField (RatFunc k) M) (_ : FiniteDimensional (RatFunc k) E)
        (_ : IsAlgebraicBelyiPair k E), E :=
  (rfl)

/-- Packaging the index of `maximalBelyiExtension` as a single `Type*` so that
`IntermediateField.coe_iSup_of_directed` and `IntermediateField.isAlgebraic_iSup` apply. -/
private abbrev BelyiSubextension :=
  {E : IntermediateField (RatFunc k) M //
    ∃ _ : FiniteDimensional (RatFunc k) E, IsAlgebraicBelyiPair k E}

private instance : Nonempty (BelyiSubextension k M) :=
  ⟨⟨⊥, inferInstance, isAlgebraicBelyiPair_bot k M⟩⟩

private theorem maximalBelyiExtension_eq_iSup_belyiSubextension :
    maximalBelyiExtension k M = ⨆ i : BelyiSubextension k M, i.1 := by
  apply le_antisymm
  · rw [maximalBelyiExtension_def]
    exact iSup_le fun E ↦ iSup_le fun hfin ↦ iSup_le fun hB ↦
      le_iSup (fun i : BelyiSubextension k M ↦ i.1) ⟨E, hfin, hB⟩
  · refine iSup_le fun ⟨E, hfin, hB⟩ ↦ ?_
    rw [maximalBelyiExtension_def]
    exact le_iSup_of_le E (le_iSup_of_le hfin (le_iSup_of_le hB le_rfl))

variable {k M}

/-- Every finite Belyi subextension of `M` lies inside `maximalBelyiExtension k M`. -/
theorem le_maximalBelyiExtension {E : IntermediateField (RatFunc k) M}
    [hfin : FiniteDimensional (RatFunc k) E] (hE : IsAlgebraicBelyiPair k E) :
    E ≤ maximalBelyiExtension k M := by
  rw [maximalBelyiExtension_def]
  exact le_iSup_of_le E (le_iSup_of_le hfin (le_iSup_of_le hE le_rfl))

@[simp]
theorem maximalBelyiExtension_le_iff {L : IntermediateField (RatFunc k) M} :
    maximalBelyiExtension k M ≤ L ↔
      ∀ (E : IntermediateField (RatFunc k) M) (_ : FiniteDimensional (RatFunc k) E),
        IsAlgebraicBelyiPair k E → E ≤ L := by
  rw [maximalBelyiExtension_def]
  simp only [iSup_le_iff]

/-- The image in `M` of any `k(t)`-embedding of an algebraic Belyi pair `F` lies in
`maximalBelyiExtension k M`. -/
theorem fieldRange_le_maximalBelyiExtension {F : Type*} [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] M) :
    f.fieldRange ≤ maximalBelyiExtension k M := by
  have : FiniteDimensional (RatFunc k) f.fieldRange :=
    Module.Finite.equiv f.equivFieldRange.toLinearEquiv
  exact le_maximalBelyiExtension (hF.of_algEquiv f.equivFieldRange)

/-- Lift a `k(t)`-embedding `f : F →ₐ[RatFunc k] M` of an algebraic Belyi pair `F` to an embedding
into `maximalBelyiExtension k M`. When `F / k(t)` is normal, `(liftMaximalBelyiExtension hF f)`
induces continuous Galois restriction `(liftMaximalBelyiExtension hF f).restrictNormalHom` and, for
`M / k(t)` normal, the topological quotient isomorphism
`(liftMaximalBelyiExtension hF f).quotientKerRestrictNormalHomEquiv`. -/
noncomputable def liftMaximalBelyiExtension {F : Type*} [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] M) :
    F →ₐ[RatFunc k] ↥(maximalBelyiExtension k M) :=
  f.codRestrict (maximalBelyiExtension k M).toSubalgebra fun x ↦
    fieldRange_le_maximalBelyiExtension hF f ⟨x, rfl⟩

@[simp]
theorem coe_liftMaximalBelyiExtension_apply {F : Type*} [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] M) (x : F) :
    (liftMaximalBelyiExtension hF f x : M) = f x :=
  (rfl)

@[simp]
theorem val_comp_liftMaximalBelyiExtension {F : Type*} [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] M) :
    (maximalBelyiExtension k M).val.comp (liftMaximalBelyiExtension hF f) = f :=
  AlgHom.ext fun _ ↦ rfl

instance isAlgebraic_maximalBelyiExtension :
    Algebra.IsAlgebraic (RatFunc k) ↥(maximalBelyiExtension k M) := by
  have halg (i : BelyiSubextension k M) : Algebra.IsAlgebraic (RatFunc k) i.1 := by
    obtain ⟨hfin, -⟩ := i.2
    infer_instance
  have := IntermediateField.isAlgebraic_iSup halg
  let e := IntermediateField.equivOfEq (maximalBelyiExtension_eq_iSup_belyiSubextension k M)
  exact Algebra.IsAlgebraic.of_injective e.toAlgHom e.injective

instance isSeparable_maximalBelyiExtension :
    Algebra.IsSeparable (RatFunc k) ↥(maximalBelyiExtension k M) :=
  have : CharZero (RatFunc k) := charZero_of_injective_algebraMap (algebraMap k _).injective
  inferInstance

section IsAlgClosed

variable [IsAlgClosed k]

instance isIntegrallyClosedIn_maximalBelyiExtension :
    IsIntegrallyClosedIn k ↥(maximalBelyiExtension k M) :=
  isIntegrallyClosedIn_of_isAlgClosed

private theorem directed_belyiSubextension :
    Directed (· ≤ ·) (fun i : BelyiSubextension k M ↦ i.1) := by
  rintro ⟨E₁, hfin₁, hB₁⟩ ⟨E₂, hfin₂, hB₂⟩
  exact ⟨⟨E₁ ⊔ E₂, inferInstance, (isAlgebraicBelyiPair_sup_iff E₁ E₂).mpr ⟨hB₁, hB₂⟩⟩,
    le_sup_left, le_sup_right⟩

/-- Over an algebraically closed field `k`, an element of `M` lies in `maximalBelyiExtension k M`
precisely when it belongs to some finite Belyi subextension of `M`. -/
theorem mem_maximalBelyiExtension_iff {x : M} :
    x ∈ maximalBelyiExtension k M ↔
      ∃ E : IntermediateField (RatFunc k) M,
        ∃ _ : FiniteDimensional (RatFunc k) E, IsAlgebraicBelyiPair k E ∧ x ∈ E := by
  rw [← SetLike.mem_coe, maximalBelyiExtension_eq_iSup_belyiSubextension,
    IntermediateField.coe_iSup_of_directed directed_belyiSubextension, Set.mem_iUnion]
  exact ⟨fun ⟨⟨E, hfin, hB⟩, hx⟩ ↦ ⟨E, hfin, hB, hx⟩,
    fun ⟨E, hfin, hB, hx⟩ ↦ ⟨⟨E, hfin, hB⟩, hx⟩⟩

/-- Over an algebraically closed field `k`, a finite intermediate field of `M / k(t)` lies in
`maximalBelyiExtension k M` precisely when it is an algebraic Belyi pair. -/
@[simp]
theorem le_maximalBelyiExtension_iff (E : IntermediateField (RatFunc k) M)
    [FiniteDimensional (RatFunc k) E] :
    E ≤ maximalBelyiExtension k M ↔ IsAlgebraicBelyiPair k E := by
  refine ⟨fun hle ↦ ?_, le_maximalBelyiExtension⟩
  let b := Module.finBasis (RatFunc k) E
  have hb (i : Fin (Module.finrank (RatFunc k) E)) :
      ∃ F : IntermediateField (RatFunc k) M,
        ∃ _ : FiniteDimensional (RatFunc k) F, IsAlgebraicBelyiPair k F ∧ (b i : M) ∈ F :=
    mem_maximalBelyiExtension_iff.mp (hle (b i).2)
  choose F hfin hBF hmem using hb
  have hEL : E ≤ ⨆ i, F i := by
    intro y hy
    have hy' := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩).symm
    push_cast at hy'
    rw [hy']
    refine (⨆ i, F i).sum_mem fun i _ ↦ (⨆ j, F j).smul_mem ?_
    exact (le_iSup F i) (hmem i)
  exact IsAlgebraicBelyiPair.of_le hEL ((isAlgebraicBelyiPair_iSup_iff F).mpr hBF)

/-- Over an algebraically closed field `k`, any finite extension `F / k(t)` admitting a
`k(t)`-embedding into `maximalBelyiExtension k M` is an algebraic Belyi pair. -/
theorem IsAlgebraicBelyiPair.of_algHom_maximalBelyiExtension {F : Type*} [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (f : F →ₐ[RatFunc k] ↥(maximalBelyiExtension k M)) :
    IsAlgebraicBelyiPair k F := by
  let g : F →ₐ[RatFunc k] M := (maximalBelyiExtension k M).val.comp f
  have : FiniteDimensional (RatFunc k) g.fieldRange :=
    g.equivFieldRange.toLinearEquiv.finiteDimensional
  have hle : g.fieldRange ≤ maximalBelyiExtension k M := by
    rintro _ ⟨x, rfl⟩
    exact (f x).2
  exact ((le_maximalBelyiExtension_iff g.fieldRange).mp hle).of_algEquiv g.equivFieldRange.symm

/-- Over an algebraically closed field `k`, every finite intermediate field of
`maximalBelyiExtension k M / k(t)` is an algebraic Belyi pair. -/
theorem isAlgebraicBelyiPair_intermediateField_maximalBelyiExtension
    (E : IntermediateField (RatFunc k) ↥(maximalBelyiExtension k M))
    [FiniteDimensional (RatFunc k) E] :
    IsAlgebraicBelyiPair k E :=
  .of_algHom_maximalBelyiExtension E.val

/-- Over an algebraically closed field `k`, `maximalBelyiExtension k M` coincides with the
compositum of the normal closures in `M` of all finite Belyi subextensions of `M`. -/
theorem maximalBelyiExtension_eq_iSup_normalClosure :
    maximalBelyiExtension k M =
      ⨆ (E : IntermediateField (RatFunc k) M) (_ : FiniteDimensional (RatFunc k) E)
        (_ : IsAlgebraicBelyiPair k E),
        IntermediateField.normalClosure (RatFunc k) E M := by
  apply le_antisymm
  · rw [maximalBelyiExtension_def]
    refine iSup_le fun E ↦ iSup_le fun hfin ↦ iSup_le fun hB ↦ ?_
    refine le_iSup_of_le E (le_iSup_of_le hfin (le_iSup_of_le hB ?_))
    intro x hx
    exact E.val.fieldRange_le_normalClosure ⟨⟨x, hx⟩, rfl⟩
  · refine iSup_le fun E ↦ iSup_le fun hfin ↦ iSup_le fun hB ↦ ?_
    exact le_maximalBelyiExtension ((isAlgebraicBelyiPair_normalClosure_iff E).mpr hB)

/-! ### Radical elements and infinite degree -/

/-- Over an algebraically closed field `k`, every `n`-th root (`n ≠ 0`) in `M` of a rational
function `u ∈ k(t)` whose order at every unmarked place is divisible by `n` belongs to
`maximalBelyiExtension k M`. -/
theorem mem_maximalBelyiExtension_of_pow_eq {y : M} {n : ℕ} {u : RatFunc k} (hn : n ≠ 0)
    (hy : y ^ n = algebraMap (RatFunc k) M u)
    (hdvd : ∀ P ∉ Place.zeroOneInfty k, (n : ℤ) ∣ P.ord u) :
    y ∈ maximalBelyiExtension k M := by
  obtain ⟨hfin, hB⟩ := isAlgebraicBelyiPair_adjoin_of_pow_eq hn hy hdvd
  exact le_maximalBelyiExtension hB (IntermediateField.mem_adjoin_simple_self (RatFunc k) y)

/-- Over an algebraically closed field `k`, every `n`-th root (`n ≠ 0`) in `M` of
`c t ^ a (t - 1) ^ b` (`c ≠ 0`) belongs to `maximalBelyiExtension k M`. -/
theorem mem_maximalBelyiExtension_of_pow_eq_X_zpow_mul_X_sub_one_zpow
    {y : M} {n : ℕ} {c : k} (hn : n ≠ 0) (hc : c ≠ 0) (a b : ℤ)
    (hy : y ^ n = algebraMap (RatFunc k) M
      (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b)) :
    y ∈ maximalBelyiExtension k M :=
  mem_maximalBelyiExtension_of_pow_eq hn hy fun _ hP ↦ by
    rw [Place.ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow_of_notMem_zeroOneInfty hP hc]
    exact dvd_zero _

/-- Over an algebraically closed field `k`, every `n`-th root (`n ≠ 0`) of `t` in `M` belongs to
`maximalBelyiExtension k M`. -/
theorem mem_maximalBelyiExtension_of_pow_eq_X {y : M} {n : ℕ} (hn : n ≠ 0)
    (hy : y ^ n = algebraMap (RatFunc k) M RatFunc.X) :
    y ∈ maximalBelyiExtension k M :=
  mem_maximalBelyiExtension_of_pow_eq_X_zpow_mul_X_sub_one_zpow hn one_ne_zero 1 0 (by simpa)

/-- Over an algebraically closed field `k`, every `n`-th root (`n ≠ 0`) of `t - 1` in `M` belongs
to `maximalBelyiExtension k M`. -/
theorem mem_maximalBelyiExtension_of_pow_eq_X_sub_one {y : M} {n : ℕ} (hn : n ≠ 0)
    (hy : y ^ n = algebraMap (RatFunc k) M (RatFunc.X - 1)) :
    y ∈ maximalBelyiExtension k M :=
  mem_maximalBelyiExtension_of_pow_eq_X_zpow_mul_X_sub_one_zpow hn one_ne_zero 0 1
    (by simpa [map_sub, map_one] using hy)

end IsAlgClosed

/-- When `M` is algebraically closed, `maximalBelyiExtension k M` has infinite degree over `k(t)`
for every field `k` of characteristic zero, since it contains the power-map extensions
`k(t)[Y] / (Y ^ n - t)` of every positive degree `n`. -/
theorem not_finiteDimensional_maximalBelyiExtension [IsAlgClosed M] :
    ¬ FiniteDimensional (RatFunc k) ↥(maximalBelyiExtension k M) := by
  intro hfin
  set n := Module.finrank (RatFunc k) ↥(maximalBelyiExtension k M) + 1
  have : NeZero n := ⟨Nat.succ_ne_zero _⟩
  let A := AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k))
  let φ : A →ₐ[RatFunc k] M := IsAlgClosed.lift
  have hle : φ.fieldRange ≤ maximalBelyiExtension k M :=
    fieldRange_le_maximalBelyiExtension (isAlgebraicBelyiPair_adjoinRoot_X_pow_sub_C_X k n) φ
  have : FiniteDimensional (RatFunc k) φ.fieldRange :=
    Module.Finite.equiv φ.equivFieldRange.toLinearEquiv
  have hdim_le :
      Module.finrank (RatFunc k) φ.fieldRange ≤
        Module.finrank (RatFunc k) ↥(maximalBelyiExtension k M) :=
    LinearMap.finrank_le_finrank_of_injective (f := (IntermediateField.inclusion hle).toLinearMap)
      (IntermediateField.inclusion hle).injective
  have hdim_eq : Module.finrank (RatFunc k) φ.fieldRange = n :=
    (LinearEquiv.finrank_eq φ.equivFieldRange.toLinearEquiv.symm).trans
      (finrank_adjoinRoot_X_pow_sub_C_X k n)
  omega

end MaximalBelyiExtension

/-! ### Symmetries: coefficient conjugation and branch-point permutations -/

section Symmetries

private theorem map_maximalBelyiExtension_le_of_mapRingEquiv
    {k k' M M' : Type*} [Field k] [CharZero k] [Field k'] [CharZero k']
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [Field M'] [Algebra k' M'] [Algebra (RatFunc k') M'] [IsScalarTower k' (RatFunc k') M']
    (σ : k ≃+* k') (τ : M ≃+* M')
    (hτ : ∀ x, τ (algebraMap (RatFunc k) M x) =
      algebraMap (RatFunc k') M' (RatFunc.mapRingEquiv σ x)) :
    (maximalBelyiExtension k M).toSubfield.map τ.toRingHom ≤
      (maximalBelyiExtension k' M').toSubfield := by
  let P : IntermediateField (RatFunc k) M :=
    ((maximalBelyiExtension k' M').toSubfield.comap τ.toRingHom).toIntermediateField fun x ↦ by
      rw [Subfield.mem_comap, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hτ]
      exact (maximalBelyiExtension k' M').algebraMap_mem _
  suffices hleP : maximalBelyiExtension k M ≤ P from Subfield.map_le_iff_le_comap.mpr hleP
  refine maximalBelyiExtension_le_iff.mpr fun E hfin hE ↦ ?_
  let E' : IntermediateField (RatFunc k') M' :=
    (E.toSubfield.map τ.toRingHom).toIntermediateField fun x' ↦
      Subfield.mem_map.mpr ⟨algebraMap (RatFunc k) M (RatFunc.mapRingEquiv σ.symm x'),
        (E.mem_toSubfield _).mpr (E.algebraMap_mem _), by
          rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hτ, ← RatFunc.mapRingEquiv_symm,
            RingEquiv.apply_symm_apply]⟩
  let τE : E ≃+* E' :=
    τ.restrict E E' fun x ↦ by
      dsimp only [E']
      rw [← IntermediateField.mem_toSubfield, ← IntermediateField.mem_toSubfield (s := _),
        Subfield.toIntermediateField_toSubfield, RingEquiv.toRingHom_eq_coe, ← RingHom.coe_coe,
        Subfield.map_mem_map]
  have hτE (x : RatFunc k) :
      τE (algebraMap (RatFunc k) E x) = algebraMap (RatFunc k') E' (RatFunc.mapRingEquiv σ x) :=
    Subtype.ext (hτ x)
  have : FiniteDimensional (RatFunc k') E' :=
    .of_equiv_equiv (RatFunc.mapRingEquiv σ) τE (RingHom.ext fun x ↦ (hτE x).symm)
  have hle' : E' ≤ maximalBelyiExtension k' M' :=
    le_maximalBelyiExtension (hE.of_mapRingEquiv σ τE hτE)
  exact fun y hy ↦ hle' ⟨y, hy, rfl⟩

/-- **Semilinear invariance of the maximal Belyi extension**: if `τ : M ≃+* M'` lifts the
coefficient map of `σ : k ≃+* k'` on `k(t)`, then `τ` carries `maximalBelyiExtension k M` onto
`maximalBelyiExtension k' M'`. -/
theorem map_maximalBelyiExtension_of_mapRingEquiv
    {k k' M M' : Type*} [Field k] [CharZero k] [Field k'] [CharZero k']
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [Field M'] [Algebra k' M'] [Algebra (RatFunc k') M'] [IsScalarTower k' (RatFunc k') M']
    (σ : k ≃+* k') (τ : M ≃+* M')
    (hτ : ∀ x, τ (algebraMap (RatFunc k) M x) =
      algebraMap (RatFunc k') M' (RatFunc.mapRingEquiv σ x)) :
    (maximalBelyiExtension k M).toSubfield.map τ.toRingHom =
      (maximalBelyiExtension k' M').toSubfield := by
  refine le_antisymm (map_maximalBelyiExtension_le_of_mapRingEquiv σ τ hτ) ?_
  have hτ_symm (x' : RatFunc k') :
      τ.symm (algebraMap (RatFunc k') M' x') =
        algebraMap (RatFunc k) M (RatFunc.mapRingEquiv σ.symm x') :=
    τ.symm_apply_eq.mpr (by rw [hτ, ← RatFunc.mapRingEquiv_symm, RingEquiv.apply_symm_apply])
  have hle := map_maximalBelyiExtension_le_of_mapRingEquiv σ.symm τ.symm hτ_symm
  intro z hz
  have hz' : τ.symm z ∈ maximalBelyiExtension k M := hle ⟨z, hz, rfl⟩
  exact ⟨τ.symm z, hz', τ.apply_symm_apply z⟩

/-- Elementwise form of `TauCeti.map_maximalBelyiExtension_of_mapRingEquiv`. -/
theorem apply_mem_maximalBelyiExtension_iff_of_mapRingEquiv
    {k k' M M' : Type*} [Field k] [CharZero k] [Field k'] [CharZero k']
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [Field M'] [Algebra k' M'] [Algebra (RatFunc k') M'] [IsScalarTower k' (RatFunc k') M']
    (σ : k ≃+* k') (τ : M ≃+* M')
    (hτ : ∀ x, τ (algebraMap (RatFunc k) M x) =
      algebraMap (RatFunc k') M' (RatFunc.mapRingEquiv σ x))
    {y : M} :
    τ y ∈ maximalBelyiExtension k' M' ↔ y ∈ maximalBelyiExtension k M := by
  rw [← IntermediateField.mem_toSubfield, ← map_maximalBelyiExtension_of_mapRingEquiv σ τ hτ,
    RingEquiv.toRingHom_eq_coe, ← RingHom.coe_coe, Subfield.map_mem_map,
    IntermediateField.mem_toSubfield]

/-- When `M / k(t)` is normal (over any field `k` of characteristic zero),
`maximalBelyiExtension k M` is normal over `k(t)`, since `Gal(M/k(t))` permutes the finite
algebraic Belyi subextensions of `M`. -/
instance normal_maximalBelyiExtension {k M : Type*} [Field k] [CharZero k]
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [Normal (RatFunc k) M] :
    Normal (RatFunc k) ↥(maximalBelyiExtension k M) := by
  refine IntermediateField.normal_iff_forall_map_le'.mpr ?_
  rintro τ _ ⟨x, hx, rfl⟩
  exact (apply_mem_maximalBelyiExtension_iff_of_mapRingEquiv (RingEquiv.refl k) τ.toRingEquiv
    fun z ↦ by rw [RatFunc.mapRingEquiv_refl, RingEquiv.refl_apply]; exact τ.commutes z).mpr hx

/-- When `M / k(t)` is normal (over any field `k` of characteristic zero),
`maximalBelyiExtension k M` is a Galois extension of `k(t)`. -/
instance isGalois_maximalBelyiExtension {k M : Type*} [Field k] [CharZero k]
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [Normal (RatFunc k) M] :
    IsGalois (RatFunc k) ↥(maximalBelyiExtension k M) :=
  have : CharZero (RatFunc k) := charZero_of_injective_algebraMap (algebraMap k _).injective
  ⟨⟩

private theorem map_maximalBelyiExtension_le_of_branchPointAut
    {k M M' : Type*} [Field k] [CharZero k]
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [Field M'] [Algebra k M'] [Algebra (RatFunc k) M'] [IsScalarTower k (RatFunc k) M']
    (ρ : Equiv.Perm (Fin 3)) (e : M ≃ₐ[k] M')
    (he : ∀ x, e (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M' x) :
    (maximalBelyiExtension k M).toSubfield.map e.toRingHom ≤
      (maximalBelyiExtension k M').toSubfield := by
  have he_inv (x : RatFunc k) :
      e (algebraMap (RatFunc k) M x) =
        algebraMap (RatFunc k) M' (RatFunc.branchPointAut k ρ⁻¹ x) := by
    rw [← he, ← AlgEquiv.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, AlgEquiv.one_apply]
  let P : IntermediateField (RatFunc k) M :=
    ((maximalBelyiExtension k M').toSubfield.comap e.toRingHom).toIntermediateField fun x ↦ by
      rw [Subfield.mem_comap, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgEquiv.coe_toRingEquiv, he_inv]
      exact (maximalBelyiExtension k M').algebraMap_mem _
  suffices hleP : maximalBelyiExtension k M ≤ P from Subfield.map_le_iff_le_comap.mpr hleP
  refine maximalBelyiExtension_le_iff.mpr fun E hfin hE ↦ ?_
  let E' : IntermediateField (RatFunc k) M' :=
    (E.toSubfield.map e.toRingHom).toIntermediateField fun x' ↦
      Subfield.mem_map.mpr ⟨algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x'),
        (E.mem_toSubfield _).mpr (E.algebraMap_mem _), by
          rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, he]⟩
  let eE : E ≃ₐ[k] E' :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv.restrict E E' fun x ↦ by
      dsimp only [E']
      rw [← IntermediateField.mem_toSubfield, ← IntermediateField.mem_toSubfield (s := _),
        Subfield.toIntermediateField_toSubfield, RingEquiv.toRingHom_eq_coe, ← RingHom.coe_coe,
        Subfield.map_mem_map]) fun c ↦ Subtype.ext <| by
      rw [RingEquiv.restrict_apply_coe, AlgEquiv.coe_toRingEquiv,
        IsScalarTower.algebraMap_apply k (RatFunc k) E, IntermediateField.coe_algebraMap_apply,
        ← IsScalarTower.algebraMap_apply k (RatFunc k) M, e.commutes,
        IsScalarTower.algebraMap_apply k (RatFunc k) M',
        IsScalarTower.algebraMap_apply k (RatFunc k) E', IntermediateField.coe_algebraMap_apply]
  have heE (x : RatFunc k) :
      eE (algebraMap (RatFunc k) E (RatFunc.branchPointAut k ρ x)) = algebraMap (RatFunc k) E' x :=
    Subtype.ext (he x)
  have heE_inv (x : RatFunc k) :
      eE (algebraMap (RatFunc k) E x) =
        algebraMap (RatFunc k) E' (RatFunc.branchPointAut k ρ⁻¹ x) :=
    Subtype.ext (he_inv x)
  have : FiniteDimensional (RatFunc k) E' :=
    .of_equiv_equiv (RatFunc.branchPointAut k ρ⁻¹).toRingEquiv eE.toRingEquiv
      (RingHom.ext fun x ↦ (heE_inv x).symm)
  have hle' : E' ≤ maximalBelyiExtension k M' :=
    le_maximalBelyiExtension (hE.of_branchPointAut ρ eE heE)
  exact fun y hy ↦ hle' ⟨y, hy, rfl⟩

/-- **Branch-point permutation invariance of the maximal Belyi extension**: if `e : M ≃ₐ[k] M'`
intertwines the substitution `RatFunc.branchPointAut k ρ` (`ρ ∈ S₃`) with the `k(t)`-algebra
structures on `M` and `M'`, then `e` carries `maximalBelyiExtension k M` onto
`maximalBelyiExtension k M'`. -/
theorem map_maximalBelyiExtension_of_branchPointAut
    {k M M' : Type*} [Field k] [CharZero k]
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [Field M'] [Algebra k M'] [Algebra (RatFunc k) M'] [IsScalarTower k (RatFunc k) M']
    (ρ : Equiv.Perm (Fin 3)) (e : M ≃ₐ[k] M')
    (he : ∀ x, e (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M' x) :
    (maximalBelyiExtension k M).toSubfield.map e.toRingHom =
      (maximalBelyiExtension k M').toSubfield := by
  refine le_antisymm (map_maximalBelyiExtension_le_of_branchPointAut ρ e he) ?_
  have he_symm (x : RatFunc k) :
      e.symm (algebraMap (RatFunc k) M' (RatFunc.branchPointAut k ρ⁻¹ x)) =
        algebraMap (RatFunc k) M x :=
    e.symm_apply_eq.mpr (by
      rw [← he, ← AlgEquiv.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one,
        AlgEquiv.one_apply])
  have hle := map_maximalBelyiExtension_le_of_branchPointAut ρ⁻¹ e.symm he_symm
  intro z hz
  have hz' : e.symm z ∈ maximalBelyiExtension k M := hle ⟨z, hz, rfl⟩
  exact ⟨e.symm z, hz', e.apply_symm_apply z⟩

/-- Elementwise form of `TauCeti.map_maximalBelyiExtension_of_branchPointAut`. -/
theorem apply_mem_maximalBelyiExtension_iff_of_branchPointAut
    {k M M' : Type*} [Field k] [CharZero k]
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [Field M'] [Algebra k M'] [Algebra (RatFunc k) M'] [IsScalarTower k (RatFunc k) M']
    (ρ : Equiv.Perm (Fin 3)) (e : M ≃ₐ[k] M')
    (he : ∀ x, e (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M' x)
    {y : M} :
    e y ∈ maximalBelyiExtension k M' ↔ y ∈ maximalBelyiExtension k M := by
  rw [← IntermediateField.mem_toSubfield, ← map_maximalBelyiExtension_of_branchPointAut ρ e he,
    RingEquiv.toRingHom_eq_coe, ← AlgEquiv.coe_toRingEquiv, ← RingHom.coe_coe,
    Subfield.map_mem_map, IntermediateField.mem_toSubfield]

end Symmetries

/-! ### The algebraic geometric fundamental group of `ℙ¹_k \ {0, 1, ∞}` -/

/-- The Galois group `Gal(maximalBelyiExtension k (AlgebraicClosure (RatFunc k)) / RatFunc k)` with
its Krull topology.

When `k` is algebraically closed of characteristic zero (such as `ℂ` or `AlgebraicClosure F`),
`maximalBelyiExtension k (AlgebraicClosure (RatFunc k))` is the maximal algebraic extension of
`k(t)` unramified outside `0`, `1` and `∞` (`TauCeti.mem_maximalBelyiExtension_iff`,
`TauCeti.le_maximalBelyiExtension_iff`), so `BelyiGeometricFundamentalGroup k` is the étale
**geometric fundamental group** `π₁^ét(ℙ¹_k \ {0, 1, ∞})`. Over a general field `F` of
characteristic zero, the geometric fundamental group is
`BelyiGeometricFundamentalGroup (AlgebraicClosure F)` (whose outer `Gal(F̄/F)`-action is
`TauCeti.belyiAbsoluteGaloisGroupOuterAction F`).

As an `abbrev` for `Gal(...)`, it inherits its profinite topological group structure directly from
`Gal`. -/
-- `[IsAlgClosed k]` is documented rather than assumed here: `maximalBelyiExtension` consumes no
-- such argument, so carrying it on the `abbrev` is rejected by `unusedArguments`.
abbrev BelyiGeometricFundamentalGroup (k : Type*) [Field k] [CharZero k] :=
  Gal(↥(maximalBelyiExtension k (AlgebraicClosure (RatFunc k)))/RatFunc k)

namespace BelyiGeometricFundamentalGroup

variable {k : Type*} [Field k] [CharZero k]

/-- The open subgroup of `BelyiGeometricFundamentalGroup k` cut out by a `k(t)`-embedding
`f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)` of a finite algebraic Belyi pair `F`: the
automorphisms fixing the image of `F` in `maximalBelyiExtension k (AlgebraicClosure (RatFunc k))`.
-/
noncomputable def fixingOpenSubgroup {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    OpenSubgroup (BelyiGeometricFundamentalGroup k) where
  toSubgroup := (liftMaximalBelyiExtension hF f).fieldRange.fixingSubgroup
  isOpen' := by
    let g := liftMaximalBelyiExtension hF f
    have : FiniteDimensional (RatFunc k) g.fieldRange :=
      g.equivFieldRange.toLinearEquiv.finiteDimensional
    exact g.fieldRange.fixingSubgroup_isOpen

/-- The carrier subgroup of `fixingOpenSubgroup hF f` is the fixing subgroup of the lifted image of
`f`. -/
@[simp]
theorem fixingOpenSubgroup_toSubgroup {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    (fixingOpenSubgroup hF f).toSubgroup =
      (liftMaximalBelyiExtension hF f).fieldRange.fixingSubgroup :=
  (rfl)

/-- An element of `BelyiGeometricFundamentalGroup k` lies in `fixingOpenSubgroup hF f` precisely
when it fixes `liftMaximalBelyiExtension hF f x` for every `x : F`. -/
@[simp]
theorem mem_fixingOpenSubgroup_iff {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k))
    {γ : BelyiGeometricFundamentalGroup k} :
    γ ∈ fixingOpenSubgroup hF f ↔
      ∀ x : F, γ (liftMaximalBelyiExtension hF f x) = liftMaximalBelyiExtension hF f x := by
  rw [← OpenSubgroup.mem_toSubgroup, fixingOpenSubgroup_toSubgroup,
    IntermediateField.mem_fixingSubgroup_iff]
  simp

/-- Choosing a `k(t)`-embedding `f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)` of a finite
normal algebraic Belyi pair `F` induces a continuous surjective restriction homomorphism from
`BelyiGeometricFundamentalGroup k` onto `Gal(F/RatFunc k)`. For a general ambient overfield `M`, see
`(liftMaximalBelyiExtension hF f).restrictNormalHom`. -/
noncomputable def restrictNormalHom {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    BelyiGeometricFundamentalGroup k →* Gal(F/RatFunc k) :=
  (liftMaximalBelyiExtension hF f).restrictNormalHom

@[simp]
theorem restrictNormalHom_commutes {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k))
    (γ : BelyiGeometricFundamentalGroup k) (x : F) :
    f (restrictNormalHom hF f γ x) =
      (γ (liftMaximalBelyiExtension hF f x) : AlgebraicClosure (RatFunc k)) :=
  congrArg Subtype.val ((liftMaximalBelyiExtension hF f).restrictNormalHom_commutes γ x)

/-- Restriction `restrictNormalHom hF f` onto the Galois group `Gal(F/RatFunc k)` of any finite
normal algebraic Belyi pair `F` is surjective. -/
theorem restrictNormalHom_surjective {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    Function.Surjective (restrictNormalHom hF f) :=
  (liftMaximalBelyiExtension hF f).restrictNormalHom_surjective

/-- The kernel of `restrictNormalHom hF f` is the fixing subgroup of the image of `F` in
`maximalBelyiExtension k (AlgebraicClosure (RatFunc k))`. -/
theorem ker_restrictNormalHom {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    (restrictNormalHom hF f).ker = (liftMaximalBelyiExtension hF f).fieldRange.fixingSubgroup :=
  (liftMaximalBelyiExtension hF f).ker_restrictNormalHom

/-- Restriction `restrictNormalHom hF f` to the Galois group of a finite normal algebraic Belyi
pair is continuous for the Krull topologies. -/
theorem continuous_restrictNormalHom {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    Continuous (restrictNormalHom hF f) :=
  (liftMaximalBelyiExtension hF f).continuous_restrictNormalHom

/-- The kernel of `restrictNormalHom hF f` is an open subgroup of
`BelyiGeometricFundamentalGroup k` in the Krull topology. -/
theorem isOpen_ker_restrictNormalHom {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    IsOpen ((restrictNormalHom hF f).ker : Set (BelyiGeometricFundamentalGroup k)) :=
  (liftMaximalBelyiExtension hF f).isOpen_ker_restrictNormalHom

/-- The open normal subgroup of `BelyiGeometricFundamentalGroup k` cut out by an embedded finite
normal algebraic Belyi pair `F`, namely the kernel of `restrictNormalHom hF f`. -/
noncomputable def restrictNormalOpenNormalSubgroup {F : Type*} [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    [Normal (RatFunc k) F] (hF : IsAlgebraicBelyiPair k F)
    (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    OpenNormalSubgroup (BelyiGeometricFundamentalGroup k) where
  toSubgroup := (restrictNormalHom hF f).ker
  isOpen' := isOpen_ker_restrictNormalHom hF f
  isNormal' := (restrictNormalHom hF f).normal_ker

/-- The underlying subgroup of `restrictNormalOpenNormalSubgroup hF f` is
`(restrictNormalHom hF f).ker`. -/
@[simp]
theorem restrictNormalOpenNormalSubgroup_toSubgroup {F : Type*} [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    [Normal (RatFunc k) F] (hF : IsAlgebraicBelyiPair k F)
    (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    (restrictNormalOpenNormalSubgroup hF f).toSubgroup = (restrictNormalHom hF f).ker :=
  (rfl)

/-- Precomposing the base-point embedding `f` with `τ ∈ Gal(F/RatFunc k)` conjugates the finite
quotient projection `restrictNormalHom hF f` by `τ`. -/
theorem restrictNormalHom_comp {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k))
    (τ : Gal(F/RatFunc k)) (γ : BelyiGeometricFundamentalGroup k) :
    restrictNormalHom hF (f.comp (τ : F →ₐ[RatFunc k] F)) γ =
      τ⁻¹ * restrictNormalHom hF f γ * τ :=
  (liftMaximalBelyiExtension hF f).restrictNormalHom_comp τ γ

/-- For any finite normal algebraic Belyi pair `F` and base-point embedding
`f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)`, the quotient of
`BelyiGeometricFundamentalGroup k` by `(restrictNormalHom hF f).ker` is topologically isomorphic to
`Gal(F/RatFunc k)`. For an arbitrary normal overfield `M`, see
`(liftMaximalBelyiExtension hF f).quotientKerRestrictNormalHomEquiv`. -/
noncomputable def quotientKerRestrictNormalHomEquiv {F : Type*} [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    [Normal (RatFunc k) F] (hF : IsAlgebraicBelyiPair k F)
    (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    BelyiGeometricFundamentalGroup k ⧸ (restrictNormalHom hF f).ker ≃ₜ* Gal(F/RatFunc k) :=
  (liftMaximalBelyiExtension hF f).quotientKerRestrictNormalHomEquiv

@[simp]
theorem quotientKerRestrictNormalHomEquiv_mk {F : Type*} [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    [Normal (RatFunc k) F] (hF : IsAlgebraicBelyiPair k F)
    (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) (γ : BelyiGeometricFundamentalGroup k) :
    quotientKerRestrictNormalHomEquiv hF f
        (γ : BelyiGeometricFundamentalGroup k ⧸ (restrictNormalHom hF f).ker) =
      restrictNormalHom hF f γ :=
  (liftMaximalBelyiExtension hF f).quotientKerRestrictNormalHomEquiv_mk γ

/-- The inverse of `quotientKerRestrictNormalHomEquiv hF f` sends `restrictNormalHom hF f γ` back
to the quotient class of `γ`. -/
@[simp]
theorem quotientKerRestrictNormalHomEquiv_symm_restrictNormalHom {F : Type*} [Field F]
    [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F] (hF : IsAlgebraicBelyiPair k F)
    (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) (γ : BelyiGeometricFundamentalGroup k) :
    (quotientKerRestrictNormalHomEquiv hF f).symm (restrictNormalHom hF f γ) =
      (γ : BelyiGeometricFundamentalGroup k ⧸ (restrictNormalHom hF f).ker) :=
  (liftMaximalBelyiExtension hF f).quotientKerRestrictNormalHomEquiv_symm_restrictNormalHom γ

/-- **Galois correspondence for open subgroups of `BelyiGeometricFundamentalGroup k`**: over an
algebraically closed field `k`, every open subgroup `U` is `fixingOpenSubgroup` of its fixed field,
a finite intermediate field of `maximalBelyiExtension k (AlgebraicClosure (RatFunc k)) / k(t)` that
is an algebraic Belyi pair. -/
theorem exists_fixingOpenSubgroup_eq [IsAlgClosed k]
    (U : OpenSubgroup (BelyiGeometricFundamentalGroup k)) :
    ∃ (E : IntermediateField (RatFunc k)
        ↥(maximalBelyiExtension k (AlgebraicClosure (RatFunc k))))
      (_ : FiniteDimensional (RatFunc k) E) (hE : IsAlgebraicBelyiPair k E),
      fixingOpenSubgroup hE
        ((maximalBelyiExtension k (AlgebraicClosure (RatFunc k))).val.comp E.val) = U := by
  let Ω := maximalBelyiExtension k (AlgebraicClosure (RatFunc k))
  let E : IntermediateField (RatFunc k) ↥Ω := IntermediateField.fixedField U.toSubgroup
  have hE_fix : E.fixingSubgroup = U.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩
  have : FiniteDimensional (RatFunc k) E := by
    rw [← InfiniteGalois.isOpen_iff_finite, hE_fix]
    exact U.isOpen
  have hB : IsAlgebraicBelyiPair k E :=
    isAlgebraicBelyiPair_intermediateField_maximalBelyiExtension E
  have hlift : liftMaximalBelyiExtension hB (Ω.val.comp E.val) = E.val :=
    AlgHom.ext fun _ ↦ Ω.val.injective rfl
  refine ⟨E, inferInstance, hB, OpenSubgroup.toSubgroup_injective ?_⟩
  rw [fixingOpenSubgroup_toSubgroup, hlift, IntermediateField.fieldRange_val, hE_fix]

/-- **Galois correspondence for open normal subgroups of `BelyiGeometricFundamentalGroup k`**: over
an algebraically closed field `k`, every open normal subgroup `U` is
`restrictNormalOpenNormalSubgroup` of its fixed field, a finite Galois Belyi subextension of
`maximalBelyiExtension k (AlgebraicClosure (RatFunc k)) / k(t)`. -/
theorem exists_restrictNormalOpenNormalSubgroup_eq [IsAlgClosed k]
    (U : OpenNormalSubgroup (BelyiGeometricFundamentalGroup k)) :
    ∃ (E : IntermediateField (RatFunc k)
        ↥(maximalBelyiExtension k (AlgebraicClosure (RatFunc k))))
      (_ : FiniteDimensional (RatFunc k) E) (_ : IsGalois (RatFunc k) E)
      (hE : IsAlgebraicBelyiPair k E),
      restrictNormalOpenNormalSubgroup hE
        ((maximalBelyiExtension k (AlgebraicClosure (RatFunc k))).val.comp E.val) = U := by
  let Ω := maximalBelyiExtension k (AlgebraicClosure (RatFunc k))
  let E : IntermediateField (RatFunc k) ↥Ω := IntermediateField.fixedField U.toSubgroup
  have hE_fix : E.fixingSubgroup = U.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩
  have : FiniteDimensional (RatFunc k) E := by
    rw [← InfiniteGalois.isOpen_iff_finite, hE_fix]
    exact U.isOpen
  have : IsGalois (RatFunc k) E := by
    rw [← InfiniteGalois.normal_iff_isGalois, hE_fix]
    exact U.isNormal'
  have hB : IsAlgebraicBelyiPair k E :=
    isAlgebraicBelyiPair_intermediateField_maximalBelyiExtension E
  have hlift : liftMaximalBelyiExtension hB (Ω.val.comp E.val) = E.val :=
    AlgHom.ext fun _ ↦ Ω.val.injective rfl
  refine ⟨E, inferInstance, inferInstance, hB, OpenNormalSubgroup.toSubgroup_injective ?_⟩
  dsimp only
  rw [restrictNormalOpenNormalSubgroup_toSubgroup, ker_restrictNormalHom, hlift,
    IntermediateField.fieldRange_val, hE_fix]

/-- `BelyiGeometricFundamentalGroup k` is infinite for every field `k` of characteristic zero. -/
instance instInfinite : Infinite (BelyiGeometricFundamentalGroup k) :=
  not_finite_iff_infinite.mp fun _ ↦
    not_finiteDimensional_maximalBelyiExtension
      (IsGalois.finiteDimensional_of_finite (RatFunc k)
        ↥(maximalBelyiExtension k (AlgebraicClosure (RatFunc k))))

end BelyiGeometricFundamentalGroup

end TauCeti

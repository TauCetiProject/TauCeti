/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Perm.Fin
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
(`TauCeti.isAlgebraicBelyiPair_of_isAlgClosed_iff`). Consequently, over an algebraically closed
field `k`:

* finite Belyi subextensions of `M` are closed under binary and finite composita and under taking
  normal closures (`TauCeti.isAlgebraicBelyiPair_sup_iff`,
  `TauCeti.isAlgebraicBelyiPair_iSup_iff`, `TauCeti.isAlgebraicBelyiPair_normalClosure_iff`);
* finite Belyi subextensions form a directed system, so an element of `M` belongs to
  `maximalBelyiExtension k M` precisely when it lies in some finite Belyi subextension, and a
  finite subextension lies in `maximalBelyiExtension k M` precisely when it is itself a Belyi pair
  (`TauCeti.mem_maximalBelyiExtension_iff`, `TauCeti.le_maximalBelyiExtension_iff`);
* it coincides with the compositum of the normal closures of all finite Belyi subextensions of `M`
  (`TauCeti.maximalBelyiExtension_eq_iSup_normalClosure`).

Over any field `k` of characteristic zero, when `M / k(t)` is normal, `maximalBelyiExtension k M` is
an infinite-degree Galois extension of `k(t)` (`TauCeti.normal_maximalBelyiExtension`,
`TauCeti.isGalois_maximalBelyiExtension`, `TauCeti.not_finiteDimensional_maximalBelyiExtension`).

Taking `M = AlgebraicClosure (RatFunc k)` for an algebraically closed field `k` of characteristic
zero, the Galois group `Gal(maximalBelyiExtension k (AlgebraicClosure (RatFunc k)) / k(t))` is the
algebraic **geometric fundamental group** `TauCeti.GeometricFundamentalGroup k` of
`ℙ¹_k \ {0, 1, ∞}`: a profinite group of infinite order whose finite quotients along base-point
embeddings classify finite Galois Belyi covers.

Both symmetries of the Belyi locus act on `maximalBelyiExtension`: semilinear ring isomorphisms of
`M` lifting coefficient isomorphisms `σ : k ≃+* k'` carry `maximalBelyiExtension k M` onto
`maximalBelyiExtension k' M'` (`TauCeti.map_maximalBelyiExtension_of_mapRingEquiv`), and
`k`-algebra isomorphisms permuting the three marked places via `RatFunc.branchPointAut` preserve it
(`TauCeti.map_maximalBelyiExtension_of_branchPointAut`). The former is what induces the arithmetic
outer Galois action in `TauCeti.FieldTheory.FunctionField.Belyi.OuterAction`.

## Main definitions

* `TauCeti.maximalBelyiExtension`: the compositum in `M` of all finite subextensions over `k(t)`
  that are algebraic Belyi pairs over `k`.
* `TauCeti.GeometricFundamentalGroup`: the Galois group of
  `maximalBelyiExtension k (AlgebraicClosure (RatFunc k))` over `RatFunc k`, for algebraically
  closed `k` of characteristic zero.
* `TauCeti.liftMaximalBelyiExtension`: lifting a `k(t)`-embedding `F →ₐ[RatFunc k] M` of an
  algebraic Belyi pair `F` into `maximalBelyiExtension k M`.

## Main results

* `TauCeti.IsAlgebraicBelyiPair.tower_bot`, `TauCeti.IsAlgebraicBelyiPair.of_le`: subextensions of
  algebraic Belyi pairs are algebraic Belyi pairs.
* `TauCeti.isAlgebraicBelyiPair_of_isAlgClosed_iff`, `TauCeti.isAlgebraicBelyiPair_sup_iff`,
  `TauCeti.isAlgebraicBelyiPair_iSup_iff`, `TauCeti.isAlgebraicBelyiPair_normalClosure_iff`:
  lattice and Galois-closure stability over an algebraically closed constant field.
* `TauCeti.mem_maximalBelyiExtension_iff`, `TauCeti.le_maximalBelyiExtension_iff`: elementwise and
  subextension characterizations of `maximalBelyiExtension`.
* `TauCeti.normal_maximalBelyiExtension`, `TauCeti.isGalois_maximalBelyiExtension`: normality and
  Galoisness of `maximalBelyiExtension k M` over `RatFunc k` when `M / RatFunc k` is normal.
* `TauCeti.mem_maximalBelyiExtension_of_pow_eq_X_zpow_mul_X_sub_one_zpow`,
  `TauCeti.not_finiteDimensional_maximalBelyiExtension`, `GeometricFundamentalGroup.instInfinite`:
  radical elements in `maximalBelyiExtension` and infinite degree / infinite order.
* `TauCeti.map_maximalBelyiExtension_of_mapRingEquiv`,
  `TauCeti.map_maximalBelyiExtension_of_branchPointAut`: invariance under coefficient conjugation
  and `S₃` branch-point permutations.

## References

* A. Grothendieck, *Esquisse d'un Programme* (1984), in *Geometric Galois Actions*, Vol. 1, LMS
  Lecture Note Series 242, Cambridge University Press, 1997, pp. 5–48.
* J. Szamuely, *Galois Groups and Fundamental Groups*, Cambridge Studies in Advanced Mathematics
  117, Cambridge University Press, 2009, §4.6–4.7.
-/

public section

open Polynomial
open scoped IntermediateField

namespace TauCeti

/-! ### Subextensions, composita, and Galois closures of algebraic Belyi pairs -/

section Subextensions

variable {k : Type*} [Field k] [CharZero k]

/-- **A subextension of an algebraic Belyi pair is an algebraic Belyi pair**: in a tower
`k(t) ⊆ E ⊆ F` of finite extensions, if `F / k(t)` is an algebraic Belyi pair over `k`, then so is
`E / k(t)`. Both exactness of the constant field and unramifiedness away from `0`, `1` and `∞`
descend from `F` to `E`. -/
theorem IsAlgebraicBelyiPair.tower_bot {E F : Type*} [Field E] [Field F] [Algebra k E]
    [Algebra k F] [Algebra (RatFunc k) E] [Algebra (RatFunc k) F] [Algebra E F]
    [IsScalarTower k (RatFunc k) E] [IsScalarTower k (RatFunc k) F]
    [IsScalarTower k E F] [IsScalarTower (RatFunc k) E F]
    [FiniteDimensional (RatFunc k) E] [FiniteDimensional (RatFunc k) F]
    (h : IsAlgebraicBelyiPair k F) : IsAlgebraicBelyiPair k E := by
  obtain ⟨hF, hbr, -⟩ := (isAlgebraicBelyiPair_iff_of_isScalarTower (E := E) (F := F)).mp h
  exact isAlgebraicBelyiPair_iff_branchPlaces_subset.mpr
    ⟨(IsScalarTower.toAlgHom k E F).isIntegrallyClosedIn (algebraMap E F).injective hF, hbr⟩

/-- Over an algebraically closed field `k` of characteristic zero, exactness of the constant field
is automatic, so a finite extension `F / k(t)` is an algebraic Belyi pair precisely when every
place of `k(t)` outside `0`, `1` and `∞` is unramified in `F`. -/
theorem isAlgebraicBelyiPair_of_isAlgClosed_iff [IsAlgClosed k] {F : Type*} [Field F]
    [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FiniteDimensional (RatFunc k) F] :
    IsAlgebraicBelyiPair k F ↔
      ∀ P ∉ Place.zeroOneInfty k, P.IsUnramified (k' := k) (F' := F) := by
  rw [isAlgebraicBelyiPair_iff, and_iff_right isIntegrallyClosedIn_of_isAlgClosed]

variable {M : Type*} [Field M] [Algebra k M] [Algebra (RatFunc k) M]
  [IsScalarTower k (RatFunc k) M]

variable (k M) in
/-- The bottom intermediate field `⊥` of `M / k(t)` is an algebraic Belyi pair over `k`. -/
theorem isAlgebraicBelyiPair_bot :
    IsAlgebraicBelyiPair k ↥(⊥ : IntermediateField (RatFunc k) M) :=
  (isAlgebraicBelyiPair_ratFunc k).of_algEquiv (IntermediateField.botEquiv (RatFunc k) M).symm

/-- An intermediate field below a finite algebraic Belyi subextension is itself an algebraic Belyi
pair. -/
theorem IsAlgebraicBelyiPair.of_le {E₁ E₂ : IntermediateField (RatFunc k) M}
    [FiniteDimensional (RatFunc k) E₁] [FiniteDimensional (RatFunc k) E₂]
    (hle : E₁ ≤ E₂) (hE₂ : IsAlgebraicBelyiPair k E₂) : IsAlgebraicBelyiPair k E₁ :=
  letI : Algebra E₁ E₂ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc k) E₁ E₂ := .of_algebraMap_eq' rfl
  haveI : IsScalarTower k E₁ E₂ := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k (RatFunc k) E₁,
      IsScalarTower.algebraMap_apply k (RatFunc k) E₂]
    exact (IntermediateField.inclusion hle).commutes _
  hE₂.tower_bot

/-- Over an algebraically closed field `k`, the compositum of two finite intermediate fields of
`M / k(t)` is an algebraic Belyi pair precisely when each of them is. -/
@[simp]
theorem isAlgebraicBelyiPair_sup_iff [IsAlgClosed k]
    (E₁ E₂ : IntermediateField (RatFunc k) M)
    [FiniteDimensional (RatFunc k) E₁] [FiniteDimensional (RatFunc k) E₂] :
    IsAlgebraicBelyiPair k ↥(E₁ ⊔ E₂) ↔
      IsAlgebraicBelyiPair k E₁ ∧ IsAlgebraicBelyiPair k E₂ := by
  have : CharZero (RatFunc k) := charZero_of_injective_algebraMap (algebraMap k _).injective
  simp only [isAlgebraicBelyiPair_of_isAlgClosed_iff,
    Place.isUnramified_sup_iff (IsFunctionField.ratFunc k), forall_and]

/-- Over an algebraically closed field `k`, the supremum of finitely many finite intermediate
fields of `M / k(t)` is an algebraic Belyi pair precisely when each of them is. -/
@[simp]
theorem isAlgebraicBelyiPair_iSup_iff [IsAlgClosed k] {ι : Type*} [Finite ι]
    (t : ι → IntermediateField (RatFunc k) M) [∀ i, FiniteDimensional (RatFunc k) (t i)] :
    IsAlgebraicBelyiPair k ↥(⨆ i, t i) ↔ ∀ i, IsAlgebraicBelyiPair k (t i) := by
  have : CharZero (RatFunc k) := charZero_of_injective_algebraMap (algebraMap k _).injective
  simp only [isAlgebraicBelyiPair_of_isAlgClosed_iff,
    Place.isUnramified_iSup_iff (IsFunctionField.ratFunc k)]
  exact ⟨fun h i P hP ↦ h P hP i, fun h P hP i ↦ h i P hP⟩

/-- Over an algebraically closed field `k`, the normal closure in `M` of a finite intermediate
field `E` of `M / k(t)` is an algebraic Belyi pair precisely when `E` is. -/
@[simp]
theorem isAlgebraicBelyiPair_normalClosure_iff [IsAlgClosed k]
    (E : IntermediateField (RatFunc k) M) [FiniteDimensional (RatFunc k) E] :
    IsAlgebraicBelyiPair k (IntermediateField.normalClosure (RatFunc k) E M) ↔
      IsAlgebraicBelyiPair k E := by
  have : CharZero (RatFunc k) := charZero_of_injective_algebraMap (algebraMap k _).injective
  simp only [isAlgebraicBelyiPair_of_isAlgClosed_iff,
    Place.isUnramified_normalClosure_iff (IsFunctionField.ratFunc k)]

end Subextensions

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
into `maximalBelyiExtension k M`. -/
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

/-- Over an algebraically closed field `k`, adjoining any `n`-th root `y` (`n ≠ 0`) of a rational
function `c t ^ a (t - 1) ^ b` (`c ≠ 0`) produces a finite algebraic Belyi pair. Unlike
`TauCeti.IsAlgebraicBelyiPair.of_pow_eq_X_zpow_mul_X_sub_one_zpow` over a general base field, no
coprimality hypothesis on `(n, a, b)` is needed because `k` cannot gain algebraic constants. -/
theorem isAlgebraicBelyiPair_adjoin_of_pow_eq_X_zpow_mul_X_sub_one_zpow
    {y : M} {n : ℕ} {c : k} (hn : n ≠ 0) (hc : c ≠ 0) (a b : ℤ)
    (hy : y ^ n = algebraMap (RatFunc k) M
      (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b)) :
    ∃ _ : FiniteDimensional (RatFunc k) ↥(RatFunc k)⟮y⟯,
      IsAlgebraicBelyiPair k ↥(RatFunc k)⟮y⟯ := by
  set u : RatFunc k := algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b
  have hy_int : IsIntegral (RatFunc k) y :=
    ⟨X ^ n - C u, monic_X_pow_sub_C u hn, by simp [hy, u]⟩
  have hfin : FiniteDimensional (RatFunc k) ↥(RatFunc k)⟮y⟯ :=
    IntermediateField.adjoin.finiteDimensional hy_int
  let E : IntermediateField (RatFunc k) M := (RatFunc k)⟮y⟯
  let y₀ : E := IntermediateField.AdjoinSimple.gen (RatFunc k) y
  have hgen : (RatFunc k)⟮y₀⟯ = (⊤ : IntermediateField (RatFunc k) E) := by
    have hmap : ((RatFunc k)⟮y₀⟯).map E.val = E := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
      rfl
    refine eq_top_iff.mpr fun z _ ↦ ?_
    have hz : (z : M) ∈ ((RatFunc k)⟮y₀⟯).map E.val := hmap.symm ▸ z.2
    obtain ⟨w, hw, hwz⟩ := hz
    exact E.val.injective hwz ▸ hw
  have hy₀ : y₀ ^ n = algebraMap (RatFunc k) E u := Subtype.ext hy
  refine ⟨hfin, IsAlgebraicBelyiPair.of_pow_eq isIntegrallyClosedIn_of_isAlgClosed hgen hy₀ hn
    fun P hP ↦ ?_⟩
  rw [Place.ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow_of_notMem_zeroOneInfty hP hc]
  exact dvd_zero _

/-- Over an algebraically closed field `k`, every `n`-th root (`n ≠ 0`) in `M` of
`c t ^ a (t - 1) ^ b` (`c ≠ 0`) belongs to `maximalBelyiExtension k M`. -/
theorem mem_maximalBelyiExtension_of_pow_eq_X_zpow_mul_X_sub_one_zpow
    {y : M} {n : ℕ} {c : k} (hn : n ≠ 0) (hc : c ≠ 0) (a b : ℤ)
    (hy : y ^ n = algebraMap (RatFunc k) M
      (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b)) :
    y ∈ maximalBelyiExtension k M := by
  obtain ⟨hfin, hB⟩ :=
    isAlgebraicBelyiPair_adjoin_of_pow_eq_X_zpow_mul_X_sub_one_zpow hn hc a b hy
  exact le_maximalBelyiExtension hB (IntermediateField.mem_adjoin_simple_self (RatFunc k) y)

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
    { __ := (maximalBelyiExtension k' M').toSubfield.comap τ.toRingHom
      algebraMap_mem' := fun x ↦ by
        change τ (algebraMap (RatFunc k) M x) ∈ maximalBelyiExtension k' M'
        rw [hτ]
        exact (maximalBelyiExtension k' M').algebraMap_mem _ }
  suffices hleP : maximalBelyiExtension k M ≤ P from Subfield.map_le_iff_le_comap.mpr hleP
  refine maximalBelyiExtension_le_iff.mpr fun E hfin hE ↦ ?_
  let E' : IntermediateField (RatFunc k') M' :=
    { __ := E.toSubfield.map τ.toRingHom
      algebraMap_mem' := fun x' ↦
        ⟨algebraMap (RatFunc k) M (RatFunc.mapRingEquiv σ.symm x'), E.algebraMap_mem _, by
          rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hτ, ← RatFunc.mapRingEquiv_symm,
            RingEquiv.apply_symm_apply]⟩ }
  let τE : E ≃+* E' :=
    { toFun := fun y ↦ ⟨τ y, y, y.2, rfl⟩
      invFun := fun z ↦
        ⟨τ.symm z, by
          obtain ⟨y, hy, hyz⟩ := z.2
          have : τ.symm z = y := τ.symm_apply_eq.mpr hyz.symm
          exact this ▸ hy⟩
      left_inv := fun y ↦ Subtype.ext (τ.symm_apply_apply y)
      right_inv := fun z ↦ Subtype.ext (τ.apply_symm_apply z)
      map_mul' := fun x y ↦ Subtype.ext (map_mul τ (x : M) (y : M))
      map_add' := fun x y ↦ Subtype.ext (map_add τ (x : M) (y : M)) }
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
theorem mem_maximalBelyiExtension_mapRingEquiv_iff
    {k k' M M' : Type*} [Field k] [CharZero k] [Field k'] [CharZero k']
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [Field M'] [Algebra k' M'] [Algebra (RatFunc k') M'] [IsScalarTower k' (RatFunc k') M']
    (σ : k ≃+* k') (τ : M ≃+* M')
    (hτ : ∀ x, τ (algebraMap (RatFunc k) M x) =
      algebraMap (RatFunc k') M' (RatFunc.mapRingEquiv σ x))
    {y : M} :
    τ y ∈ maximalBelyiExtension k' M' ↔ y ∈ maximalBelyiExtension k M := by
  change τ y ∈ (maximalBelyiExtension k' M').toSubfield ↔ y ∈ (maximalBelyiExtension k M).toSubfield
  rw [← map_maximalBelyiExtension_of_mapRingEquiv σ τ hτ]
  exact ⟨fun ⟨x, hx, hxy⟩ ↦ τ.injective hxy ▸ hx, fun hy ↦ ⟨y, hy, rfl⟩⟩

/-- When `M / k(t)` is normal (over any field `k` of characteristic zero),
`maximalBelyiExtension k M` is normal over `k(t)`, since `Gal(M/k(t))` permutes the finite
algebraic Belyi subextensions of `M`. -/
instance normal_maximalBelyiExtension {k M : Type*} [Field k] [CharZero k]
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [hNM : Normal (RatFunc k) M] :
    Normal (RatFunc k) ↥(maximalBelyiExtension k M) where
  toIsAlgebraic := isAlgebraic_maximalBelyiExtension
  splits' x := by
    let Ω := maximalBelyiExtension k M
    have hmin : minpoly (RatFunc k) (x : M) = minpoly (RatFunc k) x :=
      minpoly.algHom_eq Ω.val Ω.val.injective x
    have hpM : ((minpoly (RatFunc k) x).map (algebraMap (RatFunc k) M)).Splits :=
      hmin ▸ hNM.splits (x : M)
    refine IntermediateField.splits_of_splits hpM fun y hy ↦ ?_
    have hint : IsIntegral (RatFunc k) x := Algebra.IsIntegral.isIntegral x
    have hminy : minpoly (RatFunc k) y = minpoly (RatFunc k) (x : M) := by
      rw [hmin]
      exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint)
        (Polynomial.mem_rootSet.mp hy).2 (minpoly.monic hint)).symm
    obtain ⟨τ, hτ : τ y = x⟩ := (Normal.minpoly_eq_iff_mem_orbit M).mp hminy.symm
    refine (mem_maximalBelyiExtension_mapRingEquiv_iff (RingEquiv.refl k) τ.toRingEquiv
      (fun z ↦ ?_)).mp (hτ ▸ x.2)
    rw [RatFunc.mapRingEquiv_refl, RingEquiv.refl_apply]
    exact τ.commutes z

/-- When `M / k(t)` is normal (over any field `k` of characteristic zero),
`maximalBelyiExtension k M` is a Galois extension of `k(t)`. -/
instance isGalois_maximalBelyiExtension {k M : Type*} [Field k] [CharZero k]
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [Normal (RatFunc k) M] :
    IsGalois (RatFunc k) ↥(maximalBelyiExtension k M) :=
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
    { __ := (maximalBelyiExtension k M').toSubfield.comap e.toRingHom
      algebraMap_mem' := fun x ↦ by
        change e (algebraMap (RatFunc k) M x) ∈ maximalBelyiExtension k M'
        rw [he_inv]
        exact (maximalBelyiExtension k M').algebraMap_mem _ }
  suffices hleP : maximalBelyiExtension k M ≤ P from Subfield.map_le_iff_le_comap.mpr hleP
  refine maximalBelyiExtension_le_iff.mpr fun E hfin hE ↦ ?_
  let E' : IntermediateField (RatFunc k) M' :=
    { __ := E.toSubfield.map e.toRingHom
      algebraMap_mem' := fun x' ↦
        ⟨algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x'), E.algebraMap_mem _, he x'⟩ }
  let eE : E ≃ₐ[k] E' :=
    { toFun := fun y ↦ ⟨e y, y, y.2, rfl⟩
      invFun := fun z ↦
        ⟨e.symm z, by
          obtain ⟨y, hy, hyz⟩ := z.2
          have : e.symm z = y := e.symm_apply_eq.mpr hyz.symm
          exact this ▸ hy⟩
      left_inv := fun y ↦ Subtype.ext (e.symm_apply_apply y)
      right_inv := fun z ↦ Subtype.ext (e.apply_symm_apply z)
      map_mul' := fun x y ↦ Subtype.ext (map_mul e (x : M) (y : M))
      map_add' := fun x y ↦ Subtype.ext (map_add e (x : M) (y : M))
      commutes' := fun c ↦ Subtype.ext (by
        change e (algebraMap k M c) = algebraMap k M' c
        exact e.commutes c) }
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
theorem mem_maximalBelyiExtension_branchPointAut_iff
    {k M M' : Type*} [Field k] [CharZero k]
    [Field M] [Algebra k M] [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M]
    [Field M'] [Algebra k M'] [Algebra (RatFunc k) M'] [IsScalarTower k (RatFunc k) M']
    (ρ : Equiv.Perm (Fin 3)) (e : M ≃ₐ[k] M')
    (he : ∀ x, e (algebraMap (RatFunc k) M (RatFunc.branchPointAut k ρ x)) =
      algebraMap (RatFunc k) M' x)
    {y : M} :
    e y ∈ maximalBelyiExtension k M' ↔ y ∈ maximalBelyiExtension k M := by
  change e y ∈ (maximalBelyiExtension k M').toSubfield ↔ y ∈ (maximalBelyiExtension k M).toSubfield
  rw [← map_maximalBelyiExtension_of_branchPointAut ρ e he]
  exact ⟨fun ⟨x, hx, hxy⟩ ↦ e.injective hxy ▸ hx, fun hy ↦ ⟨y, hy, rfl⟩⟩

end Symmetries

/-! ### The algebraic geometric fundamental group of `ℙ¹_k \ {0, 1, ∞}` -/

/-- The algebraic **geometric fundamental group** of `ℙ¹_k \ {0, 1, ∞}`: the Krull-topologized
Galois group `Gal(maximalBelyiExtension k (AlgebraicClosure (RatFunc k)) / RatFunc k)`.

When `k` is algebraically closed of characteristic zero (such as `ℂ` or `AlgebraicClosure F`),
`maximalBelyiExtension k (AlgebraicClosure (RatFunc k))` is the maximal algebraic extension of
`k(t)` unramified outside `0`, `1` and `∞` (`TauCeti.mem_maximalBelyiExtension_iff`,
`TauCeti.le_maximalBelyiExtension_iff`), so `GeometricFundamentalGroup k` is the étale geometric
fundamental group `π₁^ét(ℙ¹_k \ {0, 1, ∞})`. Over a general field `F`, pass to
`GeometricFundamentalGroup (AlgebraicClosure F)` (as in `TauCeti.absoluteGaloisGroupOuterAction`),
just as `Field.absoluteGaloisGroup` omits `[PerfectField]`.

As an `abbrev` for `Gal(...)`, it inherits its profinite topological group structure directly from
`Gal`. -/
-- `[IsAlgClosed k]` is documented rather than assumed here: `maximalBelyiExtension` consumes no
-- such argument, so carrying it on the `abbrev` is rejected by `unusedArguments`.
abbrev GeometricFundamentalGroup (k : Type*) [Field k] [CharZero k] :=
  Gal(↥(maximalBelyiExtension k (AlgebraicClosure (RatFunc k)))/RatFunc k)

namespace GeometricFundamentalGroup

variable {k : Type*} [Field k] [CharZero k]

/-- Choosing a `k(t)`-embedding `f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)` of a finite
normal algebraic Belyi pair `F` induces a continuous surjective restriction homomorphism from
`GeometricFundamentalGroup k` onto `Gal(F/RatFunc k)`. -/
noncomputable def restrictNormalHom {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    GeometricFundamentalGroup k →* Gal(F/RatFunc k) :=
  (liftMaximalBelyiExtension hF f).restrictNormalHom

@[simp]
theorem restrictNormalHom_commutes {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k))
    (γ : GeometricFundamentalGroup k) (x : F) :
    f (restrictNormalHom hF f γ x) =
      (γ (liftMaximalBelyiExtension hF f x) : AlgebraicClosure (RatFunc k)) :=
  congrArg Subtype.val ((liftMaximalBelyiExtension hF f).restrictNormalHom_commutes γ x)

theorem restrictNormalHom_surjective {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    Function.Surjective (restrictNormalHom hF f) :=
  (liftMaximalBelyiExtension hF f).restrictNormalHom_surjective

theorem ker_restrictNormalHom {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    (restrictNormalHom hF f).ker = (liftMaximalBelyiExtension hF f).fieldRange.fixingSubgroup :=
  (liftMaximalBelyiExtension hF f).ker_restrictNormalHom

theorem continuous_restrictNormalHom {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    Continuous (restrictNormalHom hF f) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr fun U hU ↦ ?_)
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E₀, _, hE₀U⟩ := hU
  rw [krullTopology_mem_nhds_one_iff]
  let g := liftMaximalBelyiExtension hF f
  have : FiniteDimensional (RatFunc k) g.fieldRange :=
    Module.Finite.equiv g.equivFieldRange.toLinearEquiv
  refine ⟨g.fieldRange, inferInstance, fun γ hγ ↦ hE₀U ?_⟩
  have h1 : restrictNormalHom hF f γ = 1 := by
    rwa [← MonoidHom.mem_ker, ker_restrictNormalHom]
  rw [h1]
  exact one_mem _

/-- Precomposing the base-point embedding `f` with `τ ∈ Gal(F/RatFunc k)` conjugates the finite
quotient projection `restrictNormalHom hF f` by `τ`. -/
theorem restrictNormalHom_comp {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Normal (RatFunc k) F]
    (hF : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k))
    (τ : Gal(F/RatFunc k)) (γ : GeometricFundamentalGroup k) :
    restrictNormalHom hF (f.comp (τ : F →ₐ[RatFunc k] F)) γ =
      τ⁻¹ * restrictNormalHom hF f γ * τ :=
  (liftMaximalBelyiExtension hF f).restrictNormalHom_comp τ γ

private noncomputable def quotientKerRestrictNormalHomMulEquiv {F : Type*} [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    [Normal (RatFunc k) F] (hF : IsAlgebraicBelyiPair k F)
    (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    GeometricFundamentalGroup k ⧸ (restrictNormalHom hF f).ker ≃* Gal(F/RatFunc k) :=
  QuotientGroup.liftEquiv _ (restrictNormalHom_surjective hF f) rfl

/-- For any finite normal algebraic Belyi pair `F` and base-point embedding
`f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)`, the quotient of `GeometricFundamentalGroup k`
by the kernel of `restrictNormalHom hF f` is topologically isomorphic to `Gal(F/RatFunc k)`. -/
noncomputable def quotientKerRestrictNormalHomEquiv {F : Type*} [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    [Normal (RatFunc k) F] (hF : IsAlgebraicBelyiPair k F)
    (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) :
    GeometricFundamentalGroup k ⧸ (restrictNormalHom hF f).ker ≃ₜ* Gal(F/RatFunc k) where
  __ := quotientKerRestrictNormalHomMulEquiv hF f
  __ := Continuous.homeoOfEquivCompactToT2
    (f := (quotientKerRestrictNormalHomMulEquiv hF f).toEquiv)
    ((QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (continuous_restrictNormalHom hF f))

@[simp]
theorem quotientKerRestrictNormalHomEquiv_mk {F : Type*} [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    [Normal (RatFunc k) F] (hF : IsAlgebraicBelyiPair k F)
    (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)) (γ : GeometricFundamentalGroup k) :
    quotientKerRestrictNormalHomEquiv hF f
        (γ : GeometricFundamentalGroup k ⧸ (restrictNormalHom hF f).ker) =
      restrictNormalHom hF f γ :=
  (rfl)

/-- `GeometricFundamentalGroup k` is infinite for every field `k` of characteristic zero. -/
instance instInfinite : Infinite (GeometricFundamentalGroup k) := by
  have : CharZero (RatFunc k) := charZero_of_injective_algebraMap (algebraMap k _).injective
  rw [← not_finite_iff_infinite]
  intro hfin
  let Ω := maximalBelyiExtension k (AlgebraicClosure (RatFunc k))
  set n := Nat.card (GeometricFundamentalGroup k) + 1
  have : NeZero n := ⟨Nat.succ_ne_zero _⟩
  let A := AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k))
  let φ : A →ₐ[RatFunc k] ↥Ω :=
    liftMaximalBelyiExtension (isAlgebraicBelyiPair_adjoinRoot_X_pow_sub_C_X k n) IsAlgClosed.lift
  have : FiniteDimensional (RatFunc k) φ.fieldRange :=
    Module.Finite.equiv φ.equivFieldRange.toLinearEquiv
  let N := IntermediateField.normalClosure (RatFunc k) φ.fieldRange ↥Ω
  have : IsGalois (RatFunc k) N := ⟨⟩
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom ↥N :
      GeometricFundamentalGroup k →* Gal(↥N/RatFunc k)) :=
    AlgEquiv.restrictNormalHom_surjective ↥Ω
  have hcard_le : Nat.card Gal(↥N/RatFunc k) ≤ Nat.card (GeometricFundamentalGroup k) :=
    Nat.card_le_card_of_surjective _ hsurj
  have hcard_eq : Nat.card Gal(↥N/RatFunc k) = Module.finrank (RatFunc k) N :=
    IsGalois.card_aut_eq_finrank (RatFunc k) N
  have hle : φ.fieldRange ≤ N := fun x hx ↦
    φ.fieldRange.val.fieldRange_le_normalClosure ⟨⟨x, hx⟩, rfl⟩
  have hdim_le : Module.finrank (RatFunc k) φ.fieldRange ≤ Module.finrank (RatFunc k) N :=
    LinearMap.finrank_le_finrank_of_injective (f := (IntermediateField.inclusion hle).toLinearMap)
      (IntermediateField.inclusion hle).injective
  have hdim_eq : Module.finrank (RatFunc k) φ.fieldRange = n :=
    (LinearEquiv.finrank_eq φ.equivFieldRange.toLinearEquiv.symm).trans
      (finrank_adjoinRoot_X_pow_sub_C_X k n)
  omega

end GeometricFundamentalGroup

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.FieldTheory.FunctionField.Belyi.Basic
public import TauCeti.FieldTheory.FunctionField.Belyi.MaximalUnramified
public import TauCeti.FieldTheory.FunctionField.Place.Extension.MaximalUnramified
public import TauCeti.FieldTheory.Galois.FixedField
public import TauCeti.FieldTheory.Galois.Quotient
public import TauCeti.FieldTheory.KrullTopology
import TauCeti.FieldTheory.FunctionField.Belyi.Radical
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The Galois group of the maximal extension of `k(t)` unramified outside `0`, `1`, `∞`

Fix an algebraic closure `A` of the rational function field `k(t)`. The compositum `Ω` of the
finite separable subextensions of `A / k(t)` unramified outside the three marked places `t = 0`,
`t = 1` and `t = ∞` is a Galois extension of `k(t)`
(`TauCeti.maximalUnramifiedOutside`, `TauCeti.instIsGaloisMaximalUnramifiedOutside`). Its Galois
group with the Krull topology, `TauCeti.threePointGaloisGroup k`, is a profinite group. For `k`
algebraically closed of characteristic zero, such as an algebraic closure of `ℚ`, this is the
Galois-theoretic model of the étale geometric fundamental group `π₁^ét(ℙ¹_k \ {0, 1, ∞})` (by
Riemann's existence theorem and Grothendieck's specialization, SGA 1), defined field-theoretically
without étale fundamental groups of schemes.

Over an algebraically closed field `k` of characteristic zero, being unramified outside the three
marked places is the same as being an algebraic Belyi pair: the constant field of a finite
extension of `k(t)` is automatically `k`, and the extension and its residue extensions are
automatically separable (`IntermediateField.isUnramifiedOutside_zeroOneInfty_iff`; over a general
field of characteristic zero exactness of constants is the only additional condition,
`IntermediateField.isAlgebraicBelyiPair_iff_isUnramifiedOutside`). Consequently, over an
algebraically closed field `k` of characteristic zero, `TauCeti.maximalBelyiExtension k K` coincides
with `maximalUnramifiedOutside K (Place.zeroOneInfty k)`
(`TauCeti.maximalBelyiExtension_eq_maximalUnramifiedOutside`), giving a topological isomorphism
`TauCeti.maximalBelyiGaloisGroupEquivThreePoint`:
`TauCeti.MaximalBelyiGaloisGroup k ≃ₜ* TauCeti.threePointGaloisGroup k`.
Over a general field `k` of characteristic zero, `TauCeti.maximalBelyiExtension k K` is
contained in `maximalUnramifiedOutside K (Place.zeroOneInfty k)`
(`TauCeti.maximalBelyiExtension_le_maximalUnramifiedOutside`), because `IsAlgebraicBelyiPair k`
additionally enforces exact constant field `k`; by Galois restriction,
`TauCeti.MaximalBelyiGaloisGroup k` is therefore a quotient of `TauCeti.threePointGaloisGroup k`.
Through `InfiniteGalois.intermediateFieldEquivOpenSubgroup` and
`InfiniteGalois.intermediateFieldEquivOpenNormalSubgroup` (as well as
`TauCeti.maximalUnramifiedOutside.openNormalSubgroupEquiv`), open (normal) subgroups correspond
order-reversingly to embedded finite (Galois) subextensions, and forgetting the base-point
embedding passes to subgroup conjugacy classes.

## Main definitions

* `TauCeti.threePointGaloisGroup k`: the Galois group of the maximal subextension of an algebraic
  closure of `k(t)` unramified outside `0`, `1` and `∞`.
* `TauCeti.MaximalBelyiGaloisGroup k`: the Galois group of `TauCeti.maximalBelyiExtension k` inside
  `AlgebraicClosure (RatFunc k)` with its Krull topology.
* `TauCeti.maximalBelyiGaloisGroupEquivThreePoint k`: canonical topological group isomorphism
  `MaximalBelyiGaloisGroup k ≃ₜ* threePointGaloisGroup k` when `[IsAlgClosed k]`.
* `TauCeti.MaximalBelyiGaloisGroup.fixingOpenSubgroup` and
  `TauCeti.MaximalBelyiGaloisGroup.restrictNormalOpenNormalSubgroup`: open (normal) subgroups cut
  out by an embedded finite (normal) algebraic Belyi pair.

## Main results

* `IntermediateField.isAlgebraicBelyiPair_iff_isUnramifiedOutside`: in characteristic zero, a
  finite subextension is an algebraic Belyi pair exactly when it has exact constants and is
  unramified outside the three marked places.
* `IntermediateField.isUnramifiedOutside_zeroOneInfty_iff`: over an algebraically closed field of
  characteristic zero, a finite subextension is unramified outside the three marked places exactly
  when it is an algebraic Belyi pair.
* `TauCeti.maximalBelyiExtension_eq_maximalUnramifiedOutside`: identification of
  `maximalBelyiExtension k K` and `maximalUnramifiedOutside K (Place.zeroOneInfty k)` when `k` is
  algebraically closed.
* `TauCeti.IsAlgebraicBelyiPair.le_maximalUnramifiedOutside`: in characteristic zero, an
  algebraic Belyi pair inside `A` lies in `Ω`.
* `TauCeti.le_maximalUnramifiedOutside_zeroOneInfty_iff`: over an algebraically closed `k` of
  characteristic zero, the finite subextensions of `Ω` are the algebraic Belyi pairs.
* `TauCeti.IsAlgebraicBelyiPair.normalClosure`: over an algebraically closed `k` of characteristic
  zero, the normal closure of an algebraic Belyi pair (its Galois closure in an algebraic closure
  of `k(t)`) is an algebraic Belyi pair.
* `TauCeti.adjoin_simple_le_maximalUnramifiedOutside_zeroOneInfty_of_pow_eq`: in characteristic
  zero, the radical extensions `y ^ n = c t ^ a (t - 1) ^ b` lie in `Ω`.
* `TauCeti.MaximalBelyiGaloisGroup.fixingOpenSubgroup_le_of_comp`: functoriality of
  `fixingOpenSubgroup` along embeddings of nonnormal finite covers.

## References

* T. Szamuely, *Galois Groups and Fundamental Groups*, Cambridge Studies in Advanced Mathematics
  117, Cambridge University Press, 2009, Section 4.6, for the fundamental group of a curve minus
  finitely many points as the Galois group of the maximal extension of its function field
  unramified outside them.
-/

public noncomputable section

open IntermediateField

variable (k : Type*) [Field k]

namespace TauCeti

/-- The **Galois group of the maximal extension of `k(t)` unramified outside `0`, `1` and `∞`**,
inside a fixed algebraic closure of `k(t)`, with its Krull topology; it is a profinite group. For
`k` algebraically closed of characteristic zero, such as an algebraic closure of `ℚ`, this is the
geometric fundamental group `π₁ᵍᵉᵒ` of the projective line minus the three points `0`, `1`
and `∞`. -/
abbrev threePointGaloisGroup : Type _ :=
  Gal(maximalUnramifiedOutside (AlgebraicClosure (RatFunc k)) (Place.zeroOneInfty k)/RatFunc k)

/-- The Krull topology on `TauCeti.threePointGaloisGroup k` is Hausdorff. Together with the
compactness of the Galois group of a Galois extension and the total disconnectedness of the Krull
topology, found by instance search, this makes it a profinite group. -/
instance : T2Space (threePointGaloisGroup k) :=
  krullTopology_t2

end TauCeti

section

variable {k} [CharZero k] {K : Type*} [Field K] [Algebra (RatFunc k) K]
  [Algebra k K] [IsScalarTower k (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K]

/-- **In characteristic zero, a finite extension of `k(t)` is an algebraic Belyi pair exactly
when its constant field is `k` and it is unramified outside `0`, `1` and `∞`.** The extension and
its residue extensions are separable because the characteristic is zero. -/
theorem IntermediateField.isAlgebraicBelyiPair_iff_isUnramifiedOutside
    (E : IntermediateField (RatFunc k) K) [FiniteDimensional (RatFunc k) E] :
    TauCeti.IsAlgebraicBelyiPair k E ↔
      IsIntegrallyClosedIn k E ∧ E.IsUnramifiedOutside (TauCeti.Place.zeroOneInfty k) := by
  rw [TauCeti.isAlgebraicBelyiPair_iff_branchPlaces_subset]
  exact and_congr_right fun _ ↦
    ⟨fun h ↦ ⟨inferInstance, inferInstance, h⟩, IsUnramifiedOutside.branchPlaces_subset⟩

namespace TauCeti

/-- **In characteristic zero, an algebraic Belyi pair inside `K` lies in the maximal extension of
`k(t)` unramified outside `0`, `1` and `∞`.** -/
theorem IsAlgebraicBelyiPair.le_maximalUnramifiedOutside {E : IntermediateField (RatFunc k) K}
    [FiniteDimensional (RatFunc k) E] (h : IsAlgebraicBelyiPair k E) :
    E ≤ maximalUnramifiedOutside K (Place.zeroOneInfty k) :=
  ((isAlgebraicBelyiPair_iff_isUnramifiedOutside E).mp h).right.le_maximalUnramifiedOutside

/-- **The superelliptic extensions lie in the maximal extension of `k(t)` unramified outside `0`,
`1` and `∞`**, over a field `k` of characteristic zero: if `y ^ n = c t ^ a (t - 1) ^ b` with
`n ≠ 0` and `c ≠ 0`, then `k(t)(y)` is unramified outside the three marked places. With `c = 1`
and `(a, b)` equal to `(1, 0)`, `(0, 1)` or `(-1, 0)`, these are the Kummer extensions generated
by an `n`-th root of `t`, of `t - 1` and of `1 / t`. -/
theorem adjoin_simple_le_maximalUnramifiedOutside_zeroOneInfty_of_pow_eq {y : K} {n : ℕ} {c : k}
    {a b : ℤ}
    (hy : y ^ n = algebraMap (RatFunc k) K
      (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b))
    (hn : n ≠ 0) (hc : c ≠ 0) :
    (RatFunc k)⟮y⟯ ≤ maximalUnramifiedOutside K (Place.zeroOneInfty k) :=
  (isUnramifiedOutside_adjoin_simple_of_pow_eq (IsFunctionField.ratFunc k) hy
    (Nat.cast_ne_zero.mpr hn) fun _ hP ↦ by
    rw [Place.ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow_of_notMem_zeroOneInfty hP hc]
    exact dvd_zero _).le_maximalUnramifiedOutside

section Embedding

variable {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- **Every embedding of an algebraic Belyi pair over `k(t)` lands in the maximal extension
unramified outside `0`, `1` and `∞`**, over a field `k` of characteristic zero. -/
theorem IsAlgebraicBelyiPair.fieldRange_le_maximalUnramifiedOutside
    (h : IsAlgebraicBelyiPair k F) (f : F →ₐ[RatFunc k] K) :
    f.fieldRange ≤ maximalUnramifiedOutside K (Place.zeroOneInfty k) := by
  have : FiniteDimensional (RatFunc k) f.fieldRange :=
    (AlgEquiv.ofInjectiveField f).toLinearEquiv.finiteDimensional
  exact (h.of_algEquiv (AlgEquiv.ofInjectiveField f)).le_maximalUnramifiedOutside

/-- **The normal closure of an algebraic Belyi pair in `K` lies in the maximal extension
unramified outside `0`, `1` and `∞`**: it is the compositum of the images of the embeddings of
the pair into `K`. When `K / k(t)` is normal and the pair embeds into `K`, for instance when `K` is
an algebraic closure of `k(t)`, it is the Galois closure of the pair. -/
theorem IsAlgebraicBelyiPair.normalClosure_le_maximalUnramifiedOutside
    (h : IsAlgebraicBelyiPair k F) :
    normalClosure (RatFunc k) F K ≤ maximalUnramifiedOutside K (Place.zeroOneInfty k) := by
  rw [normalClosure_def]
  exact iSup_le h.fieldRange_le_maximalUnramifiedOutside

end Embedding

end TauCeti

variable [IsAlgClosed k]

/-- **Over an algebraically closed field of characteristic zero, the finite extensions of `k(t)`
unramified outside `0`, `1` and `∞` are the algebraic Belyi pairs.** The constant field of a
finite extension of `k(t)` is `k` because `k` is algebraically closed. -/
theorem IntermediateField.isUnramifiedOutside_zeroOneInfty_iff (E : IntermediateField (RatFunc k) K)
    [FiniteDimensional (RatFunc k) E] :
    E.IsUnramifiedOutside (TauCeti.Place.zeroOneInfty k) ↔ TauCeti.IsAlgebraicBelyiPair k E := by
  rw [isAlgebraicBelyiPair_iff_isUnramifiedOutside]
  exact ⟨fun h ↦ ⟨TauCeti.isIntegrallyClosedIn_of_isAlgClosed, h⟩, And.right⟩

namespace TauCeti

/-- **The finite subextensions of the maximal extension of `k(t)` unramified outside `0`, `1` and
`∞` are exactly the algebraic Belyi pairs**, over an algebraically closed field `k` of
characteristic zero. -/
theorem le_maximalUnramifiedOutside_zeroOneInfty_iff {E : IntermediateField (RatFunc k) K}
    [FiniteDimensional (RatFunc k) E] :
    E ≤ maximalUnramifiedOutside K (Place.zeroOneInfty k) ↔ IsAlgebraicBelyiPair k E :=
  ⟨fun hE ↦ (isUnramifiedOutside_zeroOneInfty_iff E).mp
    ((le_maximalUnramifiedOutside_iff (IsFunctionField.ratFunc k)).mp hE),
    IsAlgebraicBelyiPair.le_maximalUnramifiedOutside⟩

variable {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- **The normal closure of an algebraic Belyi pair is an algebraic Belyi pair**, over an
algebraically closed field `k` of characteristic zero: the normal closure of `F / k(t)` in an
algebraic extension `K` of `k(t)`, the compositum of the images of `F` in `K`, is again
unramified outside `0`, `1` and `∞`. When `K / k(t)` is normal and `F` embeds into `K`, for
instance when `K` is an algebraic closure of `k(t)`, this normal closure is the Galois closure of
`F`, a finite Galois extension of `k(t)`, so it is the fixed field of an open normal subgroup of the
Galois group of the maximal extension unramified outside `0`, `1` and `∞`
(`TauCeti.maximalUnramifiedOutside.openNormalSubgroupEquiv`). -/
theorem IsAlgebraicBelyiPair.normalClosure (h : IsAlgebraicBelyiPair k F) :
    IsAlgebraicBelyiPair k (normalClosure (RatFunc k) F K) :=
  le_maximalUnramifiedOutside_zeroOneInfty_iff.mp h.normalClosure_le_maximalUnramifiedOutside

/-- Over an algebraically closed field `k` of characteristic zero and an algebraic extension
`K / k(t)`, `maximalBelyiExtension k K` coincides with
`maximalUnramifiedOutside K (Place.zeroOneInfty k)`. -/
theorem maximalBelyiExtension_eq_maximalUnramifiedOutside :
    maximalBelyiExtension k K = maximalUnramifiedOutside K (Place.zeroOneInfty k) :=
  le_antisymm
    (maximalBelyiExtension_le_iff.mpr fun _ _ hB ↦ hB.le_maximalUnramifiedOutside)
    (by
      rw [maximalUnramifiedOutside_def]
      exact iSup_le fun E ↦
        have := E.property.finiteDimensional
        le_maximalBelyiExtension ((isUnramifiedOutside_zeroOneInfty_iff _).mp E.property))

end TauCeti

end

namespace TauCeti

section MaximalBelyiGroup

/-- Over any characteristic-zero field `k` and algebraic extension `K / k(t)`,
`maximalBelyiExtension k K` is contained in `maximalUnramifiedOutside K (Place.zeroOneInfty k)`. -/
theorem maximalBelyiExtension_le_maximalUnramifiedOutside {k K : Type*} [Field k] [CharZero k]
    [Field K] [Algebra (RatFunc k) K] [Algebra k K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsAlgebraic (RatFunc k) K] :
    maximalBelyiExtension k K ≤ maximalUnramifiedOutside K (Place.zeroOneInfty k) :=
  maximalBelyiExtension_le_iff.mpr fun _ _ hB ↦ hB.le_maximalUnramifiedOutside

/-- `TauCeti.threePointGaloisGroup k` is infinite for every field `k` of characteristic zero. -/
instance instInfinite_threePointGaloisGroup {k : Type*} [Field k] [CharZero k] :
    Infinite (threePointGaloisGroup k) :=
  not_finite_iff_infinite.mp fun _ ↦
    have : FiniteDimensional (RatFunc k)
        ↥(maximalUnramifiedOutside (AlgebraicClosure (RatFunc k)) (Place.zeroOneInfty k)) :=
      IsGalois.finiteDimensional_of_finite (RatFunc k) _
    have hle : maximalBelyiExtension k (AlgebraicClosure (RatFunc k)) ≤
        maximalUnramifiedOutside (AlgebraicClosure (RatFunc k)) (Place.zeroOneInfty k) :=
      maximalBelyiExtension_le_maximalUnramifiedOutside
    have := Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
    not_finiteDimensional_maximalBelyiExtension this

/-- The Galois group `Gal(maximalBelyiExtension k (AlgebraicClosure (RatFunc k)) / RatFunc k)` with
its Krull topology, for any field `k` of characteristic zero. When `k` is algebraically closed, it
is topologically isomorphic to `TauCeti.threePointGaloisGroup k`
(`TauCeti.maximalBelyiGaloisGroupEquivThreePoint`), the Galois-theoretic model of
`π₁^ét(ℙ¹_k \ {0, 1, ∞})`. -/
abbrev MaximalBelyiGaloisGroup (k : Type*) [Field k] [CharZero k] :=
  Gal(↥(maximalBelyiExtension k (AlgebraicClosure (RatFunc k)))/RatFunc k)

/-- Over an algebraically closed field `k` of characteristic zero, `MaximalBelyiGaloisGroup k` is
topologically isomorphic to `TauCeti.threePointGaloisGroup k`. -/
def maximalBelyiGaloisGroupEquivThreePoint (k : Type*) [Field k] [CharZero k] [IsAlgClosed k] :
    MaximalBelyiGaloisGroup k ≃ₜ* threePointGaloisGroup k :=
  (IntermediateField.equivOfEq
    (maximalBelyiExtension_eq_maximalUnramifiedOutside (k := k)
      (K := AlgebraicClosure (RatFunc k)))).autCongrContinuousMulEquiv

/-- Definitional unfolding of `TauCeti.maximalBelyiGaloisGroupEquivThreePoint`. -/
theorem maximalBelyiGaloisGroupEquivThreePoint_def (k : Type*) [Field k] [CharZero k]
    [IsAlgClosed k] :
    maximalBelyiGaloisGroupEquivThreePoint k =
      (IntermediateField.equivOfEq
        (maximalBelyiExtension_eq_maximalUnramifiedOutside (k := k)
          (K := AlgebraicClosure (RatFunc k)))).autCongrContinuousMulEquiv :=
  (rfl)

/-- Evaluating `maximalBelyiGaloisGroupEquivThreePoint` on `γ` gives conjugation by `equivOfEq`. -/
theorem maximalBelyiGaloisGroupEquivThreePoint_apply {k : Type*} [Field k] [CharZero k]
    [IsAlgClosed k] (γ : MaximalBelyiGaloisGroup k) :
    maximalBelyiGaloisGroupEquivThreePoint k γ =
      (IntermediateField.equivOfEq
        (maximalBelyiExtension_eq_maximalUnramifiedOutside (k := k)
          (K := AlgebraicClosure (RatFunc k)))).autCongr γ :=
  AlgEquiv.autCongrContinuousMulEquiv_apply _ γ

/-- Evaluating the inverse of `maximalBelyiGaloisGroupEquivThreePoint` on `γ` gives conjugation by
`(equivOfEq _).symm`. -/
theorem maximalBelyiGaloisGroupEquivThreePoint_symm_apply {k : Type*} [Field k] [CharZero k]
    [IsAlgClosed k] (γ : threePointGaloisGroup k) :
    (maximalBelyiGaloisGroupEquivThreePoint k).symm γ =
      (IntermediateField.equivOfEq
        (maximalBelyiExtension_eq_maximalUnramifiedOutside (k := k)
          (K := AlgebraicClosure (RatFunc k)))).symm.autCongr γ := by
  rw [maximalBelyiGaloisGroupEquivThreePoint_def, AlgEquiv.autCongrContinuousMulEquiv_symm,
    AlgEquiv.autCongrContinuousMulEquiv_apply]

namespace MaximalBelyiGaloisGroup

variable {k : Type*} [Field k] [CharZero k]

local notation "Ωk" => maximalBelyiExtension k (AlgebraicClosure (RatFunc k))
local notation "BelyiG" => MaximalBelyiGaloisGroup k

section FiniteBelyi

variable {F : Type*} [Field F] [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FiniteDimensional (RatFunc k) F] (hF : IsAlgebraicBelyiPair k F)
  (f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k))
include hF f

local notation "liftF" => liftMaximalBelyiExtension hF f

/-- The open subgroup of `MaximalBelyiGaloisGroup k` cut out by an embedding
`f : F →ₐ[RatFunc k] AlgebraicClosure (RatFunc k)` of a finite algebraic Belyi pair `F`. -/
def fixingOpenSubgroup : OpenSubgroup BelyiG where
  toSubgroup := (liftF).fieldRange.fixingSubgroup
  isOpen' :=
    have := (liftF).equivFieldRange.toLinearEquiv.finiteDimensional
    (liftF).fieldRange.fixingSubgroup_isOpen

/-- The carrier subgroup of `fixingOpenSubgroup hF f` is the fixing subgroup of the lifted image. -/
@[simp]
theorem fixingOpenSubgroup_toSubgroup :
    (fixingOpenSubgroup hF f).toSubgroup = (liftF).fieldRange.fixingSubgroup := (rfl)

/-- An element of `MaximalBelyiGaloisGroup k` lies in `fixingOpenSubgroup hF f` iff it fixes
the lifted image of every `x : F`. -/
@[simp]
theorem mem_fixingOpenSubgroup_iff {γ : BelyiG} :
    γ ∈ fixingOpenSubgroup hF f ↔ ∀ x : F, γ (liftF x) = liftF x := by
  rw [← OpenSubgroup.mem_toSubgroup, fixingOpenSubgroup_toSubgroup,
    IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x ↦ h (liftF x) ⟨x, rfl⟩, fun h _ ⟨x, hx⟩ ↦ hx ▸ h x⟩

/-- The fixed field of `fixingOpenSubgroup hF f` in
`maximalBelyiExtension k (AlgebraicClosure (RatFunc k))` is the field range of
`liftMaximalBelyiExtension hF f`. -/
theorem fixedField_fixingOpenSubgroup :
    IntermediateField.fixedField (fixingOpenSubgroup hF f).toSubgroup = (liftF).fieldRange := by
  rw [fixingOpenSubgroup_toSubgroup, InfiniteGalois.fixedField_fixingSubgroup]

/-- **Cover functoriality for nonnormal finite Belyi pairs**: precomposing an embedding `f` with
`h : E →ₐ[RatFunc k] F` enlarges the fixing open subgroup (reverse inclusion). -/
theorem fixingOpenSubgroup_le_of_comp {E : Type*} [Field E] [Algebra k E]
    [Algebra (RatFunc k) E] [IsScalarTower k (RatFunc k) E] (h : E →ₐ[RatFunc k] F) :
    letI : FiniteDimensional (RatFunc k) E :=
      Module.Finite.of_injective h.toLinearMap h.injective
    fixingOpenSubgroup hF f ≤ fixingOpenSubgroup (hF.of_algHom h) (f.comp h) := by
  let _ : FiniteDimensional (RatFunc k) E :=
    Module.Finite.of_injective h.toLinearMap h.injective
  intro γ hγ
  rw [mem_fixingOpenSubgroup_iff] at hγ ⊢
  intro x
  rw [liftMaximalBelyiExtension_comp, AlgHom.comp_apply]
  exact hγ (h x)

/-- The open normal subgroup of `MaximalBelyiGaloisGroup k` cut out by an embedded finite
normal algebraic Belyi pair `F`, namely `(liftMaximalBelyiExtension hF f).restrictNormalHom.ker`. -/
def restrictNormalOpenNormalSubgroup [Normal (RatFunc k) F] : OpenNormalSubgroup BelyiG where
  toSubgroup := (liftF).restrictNormalHom.ker
  isOpen' := (liftF).isOpen_ker_restrictNormalHom
  isNormal' := (liftF).restrictNormalHom.normal_ker

/-- The underlying subgroup of `restrictNormalOpenNormalSubgroup hF f` is
`(liftMaximalBelyiExtension hF f).restrictNormalHom.ker`. -/
@[simp]
theorem restrictNormalOpenNormalSubgroup_toSubgroup [Normal (RatFunc k) F] :
    (restrictNormalOpenNormalSubgroup hF f).toSubgroup = (liftF).restrictNormalHom.ker := (rfl)

/-- As an open subgroup of `MaximalBelyiGaloisGroup k`, `restrictNormalOpenNormalSubgroup hF f`
coincides with `fixingOpenSubgroup hF f`. -/
theorem restrictNormalOpenNormalSubgroup_toOpenSubgroup [Normal (RatFunc k) F] :
    (restrictNormalOpenNormalSubgroup hF f).toOpenSubgroup = fixingOpenSubgroup hF f := by
  apply OpenSubgroup.toSubgroup_injective
  rw [restrictNormalOpenNormalSubgroup_toSubgroup, AlgHom.ker_restrictNormalHom,
    fixingOpenSubgroup_toSubgroup]

/-- The fixed field of `restrictNormalOpenNormalSubgroup hF f` in
`maximalBelyiExtension k (AlgebraicClosure (RatFunc k))` is the field range of
`liftMaximalBelyiExtension hF f`. -/
theorem fixedField_restrictNormalOpenNormalSubgroup [Normal (RatFunc k) F] :
    IntermediateField.fixedField (restrictNormalOpenNormalSubgroup hF f).toSubgroup =
      (liftF).fieldRange := by
  rw [restrictNormalOpenNormalSubgroup_toSubgroup, AlgHom.ker_restrictNormalHom,
    InfiniteGalois.fixedField_fixingSubgroup]

end FiniteBelyi

/-- Lifting the ambient inclusion of a finite intermediate field `E ≤ Ωk` gives back `E.val`. -/
theorem liftMaximalBelyiExtension_val_comp_val
    {E : IntermediateField (RatFunc k) ↥Ωk} [FiniteDimensional (RatFunc k) E]
    (hE : IsAlgebraicBelyiPair k E) :
    liftMaximalBelyiExtension hE ((Ωk).val.comp E.val) = E.val :=
  AlgHom.ext fun x ↦ (Ωk).val.injective (coe_liftMaximalBelyiExtension_apply hE _ x)

/-- Over algebraically closed `k`, the fixed field of any open subgroup `U` of
`MaximalBelyiGaloisGroup k` is an algebraic Belyi pair. -/
theorem isAlgebraicBelyiPair_fixedField [IsAlgClosed k] (U : OpenSubgroup BelyiG) :
    have := IntermediateField.finiteDimensional_fixedField_of_isOpen U.isOpen
    IsAlgebraicBelyiPair k (IntermediateField.fixedField U.toSubgroup) :=
  have := IntermediateField.finiteDimensional_fixedField_of_isOpen U.isOpen
  isAlgebraicBelyiPair_intermediateField_maximalBelyiExtension _

/-- `MaximalBelyiGaloisGroup k` is infinite for every field `k` of characteristic zero. -/
instance instInfinite : Infinite BelyiG :=
  not_finite_iff_infinite.mp fun _ ↦
    not_finiteDimensional_maximalBelyiExtension
      (IsGalois.finiteDimensional_of_finite (RatFunc k) ↥Ωk)

end MaximalBelyiGaloisGroup

end MaximalBelyiGroup

end TauCeti

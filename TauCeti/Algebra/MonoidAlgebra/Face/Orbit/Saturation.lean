/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import TauCeti.Algebra.MonoidAlgebra.Face.Orbit.Basic
public import TauCeti.FieldTheory.IsAlgClosed.Units
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Orbit saturation comparison for semigroup algebras

For an additive submonoid `S` of an abelian group `G` and a face `F : SaturatedAddSubmonoid S`,
write:

* `S_sat = S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid`,
* `F_sat = (S.nsmulSaturationInfClosureFaceOrderIso).symm F`,
* `Q_F =`
  `F.faceSubgroup.nsmulSaturation ⧸ F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation`.

This file compares field-valued points of `R[S_sat]` lying over a fixed `K`-point
`x : R[S] →ₐ[R] K` (under precomposition with the saturation inclusion) with characters extending
along `F.orbitSaturationCharHom Kˣ`:

* **Point-to-character dictionary:**
  `pointOfChar_comp_mapDomainAlgHom_inclusion_nsmulSaturation` and
  `fiberMapDomainAlgHomEquivOrbitSaturationCharHom` show that precomposing `K`-points of
  `R[S_sat]` with the saturation inclusion corresponds to restricting `Kˣ`-valued characters along
  `F.orbitSaturationCharHom Kˣ`. When `Kˣ` is divisible (`[RootableBy Kˣ ℕ]`),
  `orbitSaturationCharHom_surjective` lifts every `K`-point of `R[S]` to `R[S_sat]`
  (`AddSubmonoid.exists_comp_mapDomainAlgHom_inclusion_nsmulSaturation`).
* **Kernel and fiber cardinality:** `orbitSaturationCharHomKerEquiv` identifies the kernel with
  `Multiplicative Q_F →* U`. When `Q_F` is finite and `M` has enough `exp(Multiplicative Q_F)`-th
  roots of unity, `(F.orbitSaturationCharHom Mˣ).ker` has cardinality `Nat.card Q_F`
  (`card_orbitSaturationCharHom_ker_of_hasEnoughRootsOfUnity`), specializing to algebraically closed
  fields `K` with `NeZero ((Nat.card Q_F : ℕ) : K)` (`card_orbitSaturationCharHom_ker`,
  `card_fiber_orbitSaturationCharHom`, and `card_fiber_mapDomainAlgHom_inclusion_nsmulSaturation`).
* **Uniqueness criteria:** over a char-`0` algebraically closed field `K` with `[Finite Q_F]`,
  `F.orbitSaturationCharHom Kˣ` is injective iff `F.faceSubgroup` is saturated
  (`orbitSaturationCharHom_injective_iff_of_charZero`). In char `p`, if `[RootableBy Kˣ ℕ]` and
  `Q_F` is `p`-primary, `F.orbitSaturationCharHom Kˣ` is bijective
  (`orbitSaturationCharHom_bijective_of_charP_of_pPrimary`).

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Chapter 4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.3 and §3.2.
-/

public section

open AddMonoidAlgebra

namespace SaturatedAddSubmonoid

variable {G : Type*} [AddCommGroup G] {S : AddSubmonoid G}

/-- Precomposing an `A`-point of `R[S_sat]` with the saturation inclusion pulls `pointSupport`
back via `S.nsmulSaturationInfClosureFaceOrderIso`. -/
@[simp]
theorem _root_.AddSubmonoid.pointSupport_comp_mapDomainAlgHom_inclusion_nsmulSaturation
    {R A : Type*} [CommSemiring R] [CommSemiring A] [NoZeroDivisors A] [Nontrivial A] [Algebra R A]
    (y : AddMonoidAlgebra R
      ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] A) :
    S.pointSupport (y.comp (mapDomainAlgHom R R
      (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure)))) =
      S.nsmulSaturationInfClosureFaceOrderIso ((S.nsmulSaturation ⊓
        (AddSubgroup.closure (S : Set G)).toAddSubmonoid).pointSupport y) :=
  SetLike.ext fun _ ↦ by simp [SaturatedAddSubmonoid.mem_comap]

/-- Restriction of `U`-valued characters from `F.faceSubgroup.nsmulSaturation` to
`F.faceSubgroup`. -/
def orbitSaturationCharHom (F : SaturatedAddSubmonoid S) (U : Type*) [CommGroup U] :
    (Multiplicative F.faceSubgroup.nsmulSaturation →* U) →* (Multiplicative F.faceSubgroup →* U) :=
  MonoidHom.compHom' (AddSubgroup.inclusion F.faceSubgroup.le_nsmulSaturation).toMultiplicative

/-- Evaluating `orbitSaturationCharHom` restricts along
`F.faceSubgroup ≤ F.faceSubgroup.nsmulSaturation`. -/
@[simp]
theorem orbitSaturationCharHom_apply (F : SaturatedAddSubmonoid S) {U : Type*} [CommGroup U]
    (ψ : Multiplicative F.faceSubgroup.nsmulSaturation →* U) (g : F.faceSubgroup) :
    F.orbitSaturationCharHom U ψ (.ofAdd g) =
      ψ (.ofAdd (AddSubgroup.inclusion F.faceSubgroup.le_nsmulSaturation g)) := (rfl)

/-- Under `faceSubgroupNSMulSaturationEquiv`, precomposition with the saturation inclusion on
`A`-points of `Spec R[F_sat.faceSubgroup]` corresponds to `F.orbitSaturationCharHom Aˣ`. -/
theorem pointOfChar_comp_mapDomainAlgHom_inclusion_nsmulSaturation (F : SaturatedAddSubmonoid S)
    (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A]
    (ψ : Multiplicative F.faceSubgroup.nsmulSaturation →* Aˣ) :
    (((S.nsmulSaturationInfClosureFaceOrderIso).symm F).pointOfChar R
      (ψ.comp F.faceSubgroupNSMulSaturationEquiv.toAddMonoidHom.toMultiplicative)).comp
      (mapDomainAlgHom R R
        (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) =
      F.pointOfChar R (F.orbitSaturationCharHom Aˣ ψ) := by
  rw [pointOfChar_def, AlgHom.comp_assoc,
    F.orbitMap_comp_mapDomainAlgHom_inclusion_nsmulSaturation R, ← AlgHom.comp_assoc,
    pointOfChar_def]
  congr 1; ext g; simp [AddMonoidHom.toMultiplicative]

/-- Under `[RootableBy U ℕ]`, `F.orbitSaturationCharHom U` is surjective. -/
theorem orbitSaturationCharHom_surjective (F : SaturatedAddSubmonoid S) (U : Type*)
    [CommGroup U] [RootableBy U ℕ] : Function.Surjective (F.orbitSaturationCharHom U) :=
  fun ψ ↦ TauCeti.exists_monoidHom_comp_toMultiplicative_eq_of_rootableBy
    (AddSubgroup.inclusion_injective F.faceSubgroup.le_nsmulSaturation) ψ

/-- The kernel of `F.orbitSaturationCharHom U` is isomorphic to `U`-valued characters of `Q_F`. -/
def orbitSaturationCharHomKerEquiv (F : SaturatedAddSubmonoid S) (U : Type*) [CommGroup U] :
    (F.orbitSaturationCharHom U).ker ≃*
      (Multiplicative (F.faceSubgroup.nsmulSaturation ⧸
        F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) →* U) :=
  AddSubgroup.kerCompHomInclusionMulEquiv F.faceSubgroup.le_nsmulSaturation U

/-- `orbitSaturationCharHomKerEquiv` evaluates on the class of `x` as `ψ.val (.ofAdd x)`. -/
@[simp]
theorem orbitSaturationCharHomKerEquiv_apply (F : SaturatedAddSubmonoid S) (U : Type*)
    [CommGroup U] (ψ : (F.orbitSaturationCharHom U).ker) (x : F.faceSubgroup.nsmulSaturation) :
    F.orbitSaturationCharHomKerEquiv U ψ (.ofAdd (QuotientAddGroup.mk x)) = ψ.val (.ofAdd x) :=
  AddSubgroup.kerCompHomInclusionMulEquiv_apply F.faceSubgroup.le_nsmulSaturation U ψ x

/-- The inverse of `orbitSaturationCharHomKerEquiv` precomposes with the quotient map. -/
@[simp]
theorem orbitSaturationCharHomKerEquiv_symm_apply_coe (F : SaturatedAddSubmonoid S) (U : Type*)
    [CommGroup U] (η : Multiplicative (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) →* U) :
    ((F.orbitSaturationCharHomKerEquiv U).symm η :
      Multiplicative F.faceSubgroup.nsmulSaturation →* U) = η.comp (QuotientAddGroup.mk'
        (F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation)).toMultiplicative :=
  AddSubgroup.kerCompHomInclusionMulEquiv_symm_apply_coe F.faceSubgroup.le_nsmulSaturation U η

/-- When `Q_F` is finite and `M` has enough `Monoid.exponent (Multiplicative Q_F)`-th roots of
unity, `(F.orbitSaturationCharHom Mˣ).ker` has cardinality `Nat.card Q_F`. -/
theorem card_orbitSaturationCharHom_ker_of_hasEnoughRootsOfUnity (F : SaturatedAddSubmonoid S)
    (M : Type*) [CommMonoid M]
    [Finite (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation)]
    [HasEnoughRootsOfUnity M (Monoid.exponent (Multiplicative (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation)))] :
    Nat.card (F.orbitSaturationCharHom Mˣ).ker = Nat.card (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) := by
  let Q := F.faceSubgroup.nsmulSaturation ⧸
    F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation
  have : Finite (Multiplicative Q) := Finite.of_equiv Q Multiplicative.ofAdd
  rw [Nat.card_congr (F.orbitSaturationCharHomKerEquiv Mˣ).toEquiv,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative Q) M,
    Nat.card_congr (Multiplicative.ofAdd (α := Q)).symm]

/-- When `Q_F` is finite and `Nat.card Q_F` is invertible in an algebraically closed field `K`,
`(F.orbitSaturationCharHom Kˣ).ker` has cardinality `Nat.card Q_F`. -/
theorem card_orbitSaturationCharHom_ker (F : SaturatedAddSubmonoid S) (K : Type*)
    [Field K] [IsAlgClosed K]
    [Finite (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation)]
    [NeZero ((Nat.card (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) : ℕ) : K)] :
    Nat.card (F.orbitSaturationCharHom Kˣ).ker = Nat.card (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) := by
  let Q := F.faceSubgroup.nsmulSaturation ⧸
    F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation
  have : Finite (Multiplicative Q) := Finite.of_equiv Q Multiplicative.ofAdd
  have hcard : Nat.card (Multiplicative Q) = Nat.card Q := Nat.card_congr Multiplicative.ofAdd
  have hdvd : Monoid.exponent (Multiplicative Q) ∣ Nat.card (Multiplicative Q) := by
    have := Fintype.ofFinite (Multiplicative Q)
    simpa [Nat.card_eq_fintype_card] using Group.exponent_dvd_card (G := Multiplicative Q)
  have : HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative Q)) :=
    HasEnoughRootsOfUnity.of_dvd K (hcard ▸ hdvd)
  exact F.card_orbitSaturationCharHom_ker_of_hasEnoughRootsOfUnity K

/-- Under the hypotheses of `card_orbitSaturationCharHom_ker`, every fiber of
`F.orbitSaturationCharHom Kˣ` has cardinality `Nat.card Q_F`. -/
theorem card_fiber_orbitSaturationCharHom (F : SaturatedAddSubmonoid S) (K : Type*)
    [Field K] [IsAlgClosed K]
    [Finite (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation)]
    [NeZero ((Nat.card (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) : ℕ) : K)]
    (ψ : Multiplicative F.faceSubgroup →* Kˣ) :
    Nat.card ((F.orbitSaturationCharHom Kˣ) ⁻¹' {ψ}) = Nat.card (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) := by
  obtain ⟨ψ₀, rfl⟩ := F.orbitSaturationCharHom_surjective Kˣ ψ
  rw [Nat.card_congr (MonoidHom.fiberEquivKer (F.orbitSaturationCharHom Kˣ) ψ₀),
    F.card_orbitSaturationCharHom_ker K]

/-- Over a char-`0` algebraically closed field `K` with `[Finite Q_F]`,
`F.orbitSaturationCharHom Kˣ` is injective iff `F.faceSubgroup = F.faceSubgroup.nsmulSaturation`. -/
theorem orbitSaturationCharHom_injective_iff_of_charZero (F : SaturatedAddSubmonoid S)
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    [Finite (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation)] :
    Function.Injective (F.orbitSaturationCharHom Kˣ) ↔
      F.faceSubgroup = F.faceSubgroup.nsmulSaturation := by
  let Q := F.faceSubgroup.nsmulSaturation ⧸
    F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation
  have : NeZero ((Nat.card Q : ℕ) : K) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  rw [← MonoidHom.ker_eq_bot_iff, ← F.faceSubgroup.subsingleton_quotient_nsmulSaturation_iff,
    ← Finite.card_le_one_iff_subsingleton]
  refine ⟨fun hbot ↦ by rw [← F.card_orbitSaturationCharHom_ker K, hbot, Nat.card_unique],
    fun h1 ↦ eq_bot_iff.2 fun ψ hψ ↦ MonoidHom.ext fun g ↦ ?_⟩
  have heq := F.faceSubgroup.subsingleton_quotient_nsmulSaturation_iff.1
    (Finite.card_le_one_iff_subsingleton.1 h1)
  exact ofAdd_toAdd g ▸ DFunLike.congr_fun hψ (.ofAdd ⟨g.toAdd.val, heq.ge g.toAdd.property⟩)

/-- In char `p`, if `Q_F` is `p`-primary, then `F.orbitSaturationCharHom Kˣ` is bijective over any
char-`p` field `K` with `[RootableBy Kˣ ℕ]`. -/
theorem orbitSaturationCharHom_bijective_of_charP_of_pPrimary (F : SaturatedAddSubmonoid S)
    (K : Type*) [Field K] [RootableBy Kˣ ℕ] (p : ℕ) [Fact p.Prime] [CharP K p] (hp : ∀ q :
      F.faceSubgroup.nsmulSaturation ⧸ F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation,
      ∃ e : ℕ, (p ^ e) • q = 0) :
    Function.Bijective (F.orbitSaturationCharHom Kˣ) := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).1 (eq_bot_iff.2 fun ψ hψ ↦ ?_),
    F.orbitSaturationCharHom_surjective Kˣ⟩
  let η := F.orbitSaturationCharHomKerEquiv Kˣ ⟨ψ, hψ⟩
  have hη : η = 1 := MonoidHom.ext fun q ↦ by
    obtain ⟨e, he⟩ := hp q.toAdd
    have hpow : (η q : K) ^ p ^ e = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, ← ofAdd_toAdd q, ← ofAdd_nsmul, he, ofAdd_zero,
        map_one, Units.val_one]
    have hsub : ((η q : K) - 1) ^ p ^ e = 0 := by rw [sub_pow_char_pow, hpow, one_pow, sub_self]
    exact Units.ext (sub_eq_zero.1 (eq_zero_of_pow_eq_zero hsub))
  exact congrArg Subtype.val
    ((F.orbitSaturationCharHomKerEquiv Kˣ).injective (hη.trans (map_one _).symm))

/-- If `y : R[S_sat] →ₐ[R] K` restricts to `x : R[S] →ₐ[R] K` with support `F`, then `y` has
support `F_sat`. -/
theorem pointSupport_eq_of_comp_mapDomainAlgHom_inclusion_nsmulSaturation
    (F : SaturatedAddSubmonoid S) {R K : Type*} [CommSemiring R] [Field K] [Algebra R K]
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F)
    {y : AddMonoidAlgebra R
      ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] K}
    (hy : y.comp (mapDomainAlgHom R R
      (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) = x) :
    (S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid).pointSupport y =
      (S.nsmulSaturationInfClosureFaceOrderIso).symm F :=
  S.nsmulSaturationInfClosureFaceOrderIso.injective <| by
    rw [S.nsmulSaturationInfClosureFaceOrderIso.apply_symm_apply,
      ← S.pointSupport_comp_mapDomainAlgHom_inclusion_nsmulSaturation y, hy, hx]

private theorem comp_faceSubgroupNSMulSaturationEquiv_symm_comp (F : SaturatedAddSubmonoid S)
    {U : Type*} [CommGroup U]
    (ψ : Multiplicative ((S.nsmulSaturationInfClosureFaceOrderIso).symm F).faceSubgroup →* U) :
    (ψ.comp F.faceSubgroupNSMulSaturationEquiv.symm.toAddMonoidHom.toMultiplicative).comp
      F.faceSubgroupNSMulSaturationEquiv.toAddMonoidHom.toMultiplicative = ψ := by ext g; simp

/-- Equivalence between the fiber of lifts `y : R[S_sat] →ₐ[R] K` of a fixed `K`-point `x`
(with `S.pointSupport x = F`) under precomposition with the saturation inclusion and the fiber of
`F.orbitSaturationCharHom Kˣ` over `F.pointSupportSubtypeEquivChar R K ⟨x, hx⟩`. -/
noncomputable def fiberMapDomainAlgHomEquivOrbitSaturationCharHom
    (F : SaturatedAddSubmonoid S) (R K : Type*) [CommSemiring R] [Field K] [Algebra R K]
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F) :
    {y : AddMonoidAlgebra R
        ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] K //
      y.comp (mapDomainAlgHom R R
        (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) = x} ≃
      ((F.orbitSaturationCharHom Kˣ) ⁻¹' {F.pointSupportSubtypeEquivChar R K ⟨x, hx⟩}) :=
  let Fsat := (S.nsmulSaturationInfClosureFaceOrderIso).symm F
  let eG := F.faceSubgroupNSMulSaturationEquiv.toAddMonoidHom.toMultiplicative
  let eG' := F.faceSubgroupNSMulSaturationEquiv.symm.toAddMonoidHom.toMultiplicative
  { toFun := fun y ↦ ⟨(Fsat.pointSupportSubtypeEquivChar R K
      ⟨y.val, F.pointSupport_eq_of_comp_mapDomainAlgHom_inclusion_nsmulSaturation hx
        y.property⟩).comp eG', by
      apply F.pointOfChar_injective R K
      rw [← F.pointOfChar_comp_mapDomainAlgHom_inclusion_nsmulSaturation R _,
        F.comp_faceSubgroupNSMulSaturationEquiv_symm_comp,
        Fsat.pointOfChar_pointSupportSubtypeEquivChar R K, y.property,
        F.pointOfChar_pointSupportSubtypeEquivChar R K ⟨x, hx⟩]⟩
    invFun := fun ψ ↦ ⟨Fsat.pointOfChar R (ψ.val.comp eG), by
      rw [F.pointOfChar_comp_mapDomainAlgHom_inclusion_nsmulSaturation R ψ.val, ψ.property,
        F.pointOfChar_pointSupportSubtypeEquivChar R K ⟨x, hx⟩]⟩
    left_inv := fun y ↦ Subtype.ext <| by
      dsimp only; rw [F.comp_faceSubgroupNSMulSaturationEquiv_symm_comp]
      exact Fsat.pointOfChar_pointSupportSubtypeEquivChar R K _
    right_inv := fun ψ ↦ Subtype.ext <| by
      have hsub : Subtype.mk (Fsat.pointOfChar R (ψ.val.comp eG))
          (Fsat.pointSupport_pointOfChar R _) =
          (Fsat.pointSupportSubtypeEquivChar R K).symm (ψ.val.comp eG) :=
        Subtype.ext (Fsat.coe_pointSupportSubtypeEquivChar_symm_apply R K (ψ.val.comp eG)).symm
      dsimp only
      rw [hsub, (Fsat.pointSupportSubtypeEquivChar R K).apply_symm_apply]
      ext g; simp [eG, eG'] }

/-- Evaluating `fiberMapDomainAlgHomEquivOrbitSaturationCharHom` restricts along
`F.faceSubgroupNSMulSaturationEquiv.symm`. -/
@[simp]
theorem coe_fiberMapDomainAlgHomEquivOrbitSaturationCharHom_apply
    (F : SaturatedAddSubmonoid S) (R K : Type*) [CommSemiring R] [Field K] [Algebra R K]
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F)
    (y : {y : AddMonoidAlgebra R
        ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] K //
      y.comp (mapDomainAlgHom R R
        (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) = x}) :
    (F.fiberMapDomainAlgHomEquivOrbitSaturationCharHom R K hx y :
        Multiplicative F.faceSubgroup.nsmulSaturation →* Kˣ) =
      (((S.nsmulSaturationInfClosureFaceOrderIso).symm F).pointSupportSubtypeEquivChar R K
        ⟨y.val, F.pointSupport_eq_of_comp_mapDomainAlgHom_inclusion_nsmulSaturation hx
          y.property⟩).comp
        F.faceSubgroupNSMulSaturationEquiv.symm.toAddMonoidHom.toMultiplicative := (rfl)

/-- The inverse of `fiberMapDomainAlgHomEquivOrbitSaturationCharHom` sends `ψ` to
`F_sat.pointOfChar`. -/
@[simp]
theorem coe_fiberMapDomainAlgHomEquivOrbitSaturationCharHom_symm_apply
    (F : SaturatedAddSubmonoid S) (R K : Type*) [CommSemiring R] [Field K] [Algebra R K]
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F)
    (ψ : (F.orbitSaturationCharHom Kˣ) ⁻¹' {F.pointSupportSubtypeEquivChar R K ⟨x, hx⟩}) :
    ((F.fiberMapDomainAlgHomEquivOrbitSaturationCharHom R K hx).symm ψ : AddMonoidAlgebra R
        ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] K) =
      ((S.nsmulSaturationInfClosureFaceOrderIso).symm F).pointOfChar R
        (ψ.val.comp F.faceSubgroupNSMulSaturationEquiv.toAddMonoidHom.toMultiplicative) := (rfl)

/-- When `Q_F` is finite and `Nat.card Q_F` is invertible in an algebraically closed field `K`,
the fiber of lifts `y : R[S_sat] →ₐ[R] K` of a fixed `K`-point `x` (with `S.pointSupport x = F`)
under precomposition with the saturation inclusion has cardinality `Nat.card Q_F`. -/
theorem card_fiber_mapDomainAlgHom_inclusion_nsmulSaturation
    (F : SaturatedAddSubmonoid S) (R K : Type*) [CommSemiring R] [Field K] [IsAlgClosed K]
    [Algebra R K]
    [Finite (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation)]
    [NeZero ((Nat.card (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) : ℕ) : K)]
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F) :
    Nat.card {y : AddMonoidAlgebra R
        ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] K //
      y.comp (mapDomainAlgHom R R
        (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) = x} =
      Nat.card (F.faceSubgroup.nsmulSaturation ⧸
        F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) := by
  rw [Nat.card_congr (F.fiberMapDomainAlgHomEquivOrbitSaturationCharHom R K hx),
    F.card_fiber_orbitSaturationCharHom K]

/-- Over a field `K` with `[RootableBy Kˣ ℕ]`, every `K`-point of `R[S]` lifts to `R[S_sat]`. -/
theorem _root_.AddSubmonoid.exists_comp_mapDomainAlgHom_inclusion_nsmulSaturation
    (S : AddSubmonoid G) (R K : Type*) [CommSemiring R] [Field K] [RootableBy Kˣ ℕ] [Algebra R K]
    (x : AddMonoidAlgebra R S →ₐ[R] K) :
    ∃ y : AddMonoidAlgebra R
        ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] K,
      y.comp (mapDomainAlgHom R R
        (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) = x :=
  let F := S.pointSupport x
  have ⟨ψ, hψ⟩ :=
    F.orbitSaturationCharHom_surjective Kˣ (F.pointSupportSubtypeEquivChar R K ⟨x, rfl⟩)
  ⟨_, ((F.fiberMapDomainAlgHomEquivOrbitSaturationCharHom R K rfl).symm ⟨ψ, hψ⟩).property⟩

end SaturatedAddSubmonoid

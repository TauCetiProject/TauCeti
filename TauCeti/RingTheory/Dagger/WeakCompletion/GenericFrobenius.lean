/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.CompletedGenericField.Lift
public import TauCeti.RingTheory.Dagger.WeakCompletion.Quotient
import TauCeti.RingTheory.AdicCompletion.AlgHom
import TauCeti.RingTheory.Ideal.Maps

/-!
# Weak-completion Frobenius on the completed generic field

The Monsky–Washnitzer weak completion maps canonically to the ring of integers of the
completed generic field. A Frobenius lift on the weak completion induces a Frobenius on
the completed generic field, with the prescribed power map on its residue field.

## References

* [N. Tsuzuki, *Minimal slope conjecture of F-isocrystals*](https://arxiv.org/abs/1910.03871v3),
  §3.1.
-/

public section

open IsLocalRing
open scoped WithZero

namespace TauCeti.Dagger.weakCompletion

open TauCeti.AdicCompletion

variable {O A : Type*} [CommRing O] [CommRing A] [Algebra O A]
  (ϖ : O) [Algebra.FiniteType O A] [(Ideal.span {algebraMap O A ϖ}).IsPrime]

local notation "π" => algebraMap O A ϖ
local notation "C" => completedGenericIntegers π
local notation "W" => Dagger.weakCompletion ϖ A

omit [Algebra.FiniteType O A] in
private theorem parameter_le_comap_genericLocalRing :
    Ideal.span {π} ≤ (maximalIdeal (genericLocalRing π)).comap
      (IsScalarTower.toAlgHom O A (genericLocalRing π)) := by
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (genericLocalRing π) (Ideal.span {π}) π).mpr (Ideal.subset_span rfl)

/-- The canonical map from the weak completion of an affine lift to the ring of integers
of the completed generic field. -/
noncomputable def toCompletedGenericIntegers : W →ₐ[O] C :=
  (_root_.AdicCompletion.mapₐ (IsScalarTower.toAlgHom O A (genericLocalRing π))
    (parameter_le_comap_genericLocalRing ϖ)).comp (Dagger.weakCompletion ϖ A).val

/-- The affine restriction of a weak-completion endomorphism, valued in the generic integers. -/
noncomputable def affineRestriction (φ : W →+* W) : A →+* C :=
  (toCompletedGenericIntegers ϖ).toRingHom.comp
    (φ.comp (Dagger.weakCompletion.of ϖ A).toRingHom)

/-- The affine restriction is evaluated through the weak-completion endomorphism. -/
@[simp]
theorem affineRestriction_apply (φ : W →+* W) (a : A) :
    affineRestriction ϖ φ a =
      toCompletedGenericIntegers ϖ (φ (Dagger.weakCompletion.of ϖ A a)) :=
  RingHom.comp_apply _ _ _

private theorem affineRestriction_parameter (φ : W →+* W) :
    affineRestriction ϖ φ π =
      toCompletedGenericIntegers ϖ (φ (algebraMap O W ϖ)) := by
  rw [affineRestriction_apply, AlgHom.commutes]

/-- The canonical weak-completion map agrees with the structural map on the affine algebra. -/
@[simp]
theorem toCompletedGenericIntegers_of (a : A) :
    toCompletedGenericIntegers ϖ (Dagger.weakCompletion.of ϖ A a) =
      algebraMap A C a := by
  simp [toCompletedGenericIntegers, Dagger.weakCompletion.coe_of,
    _root_.AdicCompletion.mapₐ_of, _root_.AdicCompletion.algebraMap_apply]

/-- Reduction of a weakly completed element in the generic residue field is the inclusion of
its reduction modulo the parameter into the special-fibre function field. -/
theorem completedGenericResidueEquiv_residue_toCompletedGenericIntegers (z : W) :
    completedGenericResidueEquiv π (residue C (toCompletedGenericIntegers ϖ z)) =
      algebraMap (A ⧸ Ideal.span {π}) (FractionRing (A ⧸ Ideal.span {π}))
        (Ideal.quotEquivOfEq (pow_one (Ideal.span {π}))
          (Dagger.weakCompletion.eval ϖ 1 z)) := by
  obtain ⟨a, ha⟩ := Dagger.weakCompletion.exists_sub_mem_span_pow ϖ z 1
  have hmap : toCompletedGenericIntegers ϖ (z - Dagger.weakCompletion.of ϖ A a) ∈
      maximalIdeal C := by
    rw [maximalIdeal_completedGenericIntegers]
    apply Ideal.apply_mem_span_algebraMap_pow (toCompletedGenericIntegers ϖ) at ha
    simpa only [pow_one, IsScalarTower.algebraMap_apply O A C] using ha
  have hres : residue C (toCompletedGenericIntegers ϖ z) =
      residue C (algebraMap A C a) := by
    apply sub_eq_zero.mp
    rw [← map_sub, ← toCompletedGenericIntegers_of, ← map_sub]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmap
  have heval : Dagger.weakCompletion.eval ϖ 1 z = Ideal.Quotient.mk _ a := by
    have hz : Dagger.weakCompletion.eval ϖ 1
        (z - Dagger.weakCompletion.of ϖ A a) = 0 := by
      apply RingHom.mem_ker.mp
      rw [Dagger.weakCompletion.ker_eval]
      exact ha
    simpa only [map_sub, Dagger.weakCompletion.eval_of, sub_eq_zero] using hz
  rw [hres, completedGenericResidueEquiv_residue_algebraMap, heval,
    Ideal.quotEquivOfEq_mk]

/-- The canonical map detects reduction modulo the parameter through the generic residue
field. -/
theorem toCompletedGenericIntegers_mem_maximalIdeal_iff (z : W) :
    toCompletedGenericIntegers ϖ z ∈ maximalIdeal C ↔
      Dagger.weakCompletion.eval ϖ 1 z = 0 := by
  rw [← IsLocalRing.residue_eq_zero_iff,
    ← (completedGenericResidueEquiv π).map_eq_zero_iff,
    completedGenericResidueEquiv_residue_toCompletedGenericIntegers]
  rw [map_eq_zero_iff _ (IsFractionRing.injective (A ⧸ Ideal.span {π})
    (FractionRing (A ⧸ Ideal.span {π})))]
  exact (Ideal.quotEquivOfEq (pow_one (Ideal.span {π}))).map_eq_zero_iff

/-- A weak-completion Frobenius lift contracts the generic maximal ideal to the affine
special fibre, without requiring preservation of the affine algebra. -/
theorem comap_maximalIdeal_affineRestriction
    (φ : W →+* W) (q : ℕ) (hq : q ≠ 0)
    (hφ : ∀ z : W, Dagger.weakCompletion.eval ϖ 1 (φ z) =
      Dagger.weakCompletion.eval ϖ 1 z ^ q) :
    (maximalIdeal C).comap (affineRestriction ϖ φ) = Ideal.span {π} := by
  let : (Ideal.span {π} ^ 1).IsPrime := by simpa only [pow_one] using
    (inferInstance : (Ideal.span {π}).IsPrime)
  ext a
  simp only [Ideal.mem_comap, affineRestriction_apply,
    toCompletedGenericIntegers_mem_maximalIdeal_iff, hφ,
    Dagger.weakCompletion.eval_of, pow_eq_zero_iff hq, Ideal.Quotient.eq_zero_iff_mem,
    pow_one]

/-- A parameter-adically continuous map of the weak completion agrees everywhere with the
extension constructed from its restriction to the affine algebra. -/
theorem completedGenericIntegersLift_toCompletedGenericIntegers (φ : W →+* W)
    (hf : (maximalIdeal C).comap (affineRestriction ϖ φ) = Ideal.span {π})
    (hφ : φ (algebraMap O W ϖ) ∈ Ideal.span {algebraMap O W ϖ}) (z : W) :
    completedGenericIntegersLift π
      (affineRestriction ϖ φ) hf
      (toCompletedGenericIntegers ϖ z) = toCompletedGenericIntegers ϖ (φ z) := by
  let f := affineRestriction ϖ φ
  let F := completedGenericIntegersLift π f hf
  have := isAdicComplete_completedGenericIntegers π
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {algebraMap A C π})).mpr
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  obtain ⟨a, ha⟩ := Dagger.weakCompletion.exists_sub_mem_span_pow ϖ z n
  have hi := Ideal.apply_mem_span_algebraMap_pow (toCompletedGenericIntegers ϖ) ha
  have hF : Ideal.span {algebraMap O C ϖ} ≤
      (Ideal.span {algebraMap O C ϖ}).comap F := by
    simpa only [IsScalarTower.algebraMap_apply O A C,
      ← maximalIdeal_completedGenericIntegers] using
      (Ideal.map_le_iff_le_comap.mp (IsLocalRing.map_maximalIdeal_le F))
  have hleft := Ideal.map_mem_pow_of_le_comap F hF hi
  have hφle : Ideal.span {algebraMap O W ϖ} ≤
      (Ideal.span {algebraMap O W ϖ}).comap φ := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hφ
  have hright := Ideal.apply_mem_span_algebraMap_pow (toCompletedGenericIntegers ϖ)
    (Ideal.map_mem_pow_of_le_comap φ hφle ha)
  have h := Ideal.sub_mem _ hleft hright
  have hbase : F (toCompletedGenericIntegers ϖ (Dagger.weakCompletion.of ϖ A a)) =
      toCompletedGenericIntegers ϖ (φ (Dagger.weakCompletion.of ϖ A a)) := by
    rw [toCompletedGenericIntegers_of, completedGenericIntegersLift_algebraMap]
    exact affineRestriction_apply ϖ φ a
  simpa only [map_sub, hbase, sub_sub_sub_cancel_right,
    IsScalarTower.algebraMap_apply O A C] using h

/-- A Frobenius lift on the weak completion extends canonically to the completed generic
integers. Its restriction to the affine algebra need only take values in the weak completion. -/
noncomputable def completedGenericIntegersFrobenius (φ : W →+* W) (q : ℕ) (hq : q ≠ 0)
    (hφ : ∀ z : W, Dagger.weakCompletion.eval ϖ 1 (φ z) =
      Dagger.weakCompletion.eval ϖ 1 z ^ q) : C →+* C :=
  completedGenericIntegersLift π (affineRestriction ϖ φ)
    (comap_maximalIdeal_affineRestriction ϖ φ q hq hφ)

/-- The weak-completion Frobenius extension is a local homomorphism. -/
instance completedGenericIntegersFrobenius_isLocalHom (φ : W →+* W) (q : ℕ) (hq : q ≠ 0)
    (hφ : ∀ z : W, Dagger.weakCompletion.eval ϖ 1 (φ z) =
      Dagger.weakCompletion.eval ϖ 1 z ^ q) :
    IsLocalHom (completedGenericIntegersFrobenius ϖ φ q hq hφ) := by
  unfold completedGenericIntegersFrobenius
  infer_instance

/-- The generic integral Frobenius agrees with the given map on the whole weak completion. -/
@[simp]
theorem completedGenericIntegersFrobenius_toCompletedGenericIntegers
    (φ : W →+* W) (q : ℕ) (hq : q ≠ 0)
    (hφ : ∀ z : W, Dagger.weakCompletion.eval ϖ 1 (φ z) =
      Dagger.weakCompletion.eval ϖ 1 z ^ q) (z : W) :
    completedGenericIntegersFrobenius ϖ φ q hq hφ (toCompletedGenericIntegers ϖ z) =
      toCompletedGenericIntegers ϖ (φ z) := by
  apply completedGenericIntegersLift_toCompletedGenericIntegers
  rw [← pow_one (Ideal.span {algebraMap O W ϖ}),
    ← Dagger.weakCompletion.ker_eval ϖ 1, RingHom.mem_ker, hφ]
  have hparam := Dagger.weakCompletion.eval_parameter_pow ϖ (S := A) 1
  simp only [pow_one] at hparam
  rw [hparam, zero_pow hq]

/-- On the affine algebra the generic integral Frobenius is computed through the weak lift. -/
@[simp]
theorem completedGenericIntegersFrobenius_algebraMap (φ : W →+* W) (q : ℕ) (hq : q ≠ 0)
    (hφ : ∀ z : W, Dagger.weakCompletion.eval ϖ 1 (φ z) =
      Dagger.weakCompletion.eval ϖ 1 z ^ q) (a : A) :
    completedGenericIntegersFrobenius ϖ φ q hq hφ (algebraMap A C a) =
      toCompletedGenericIntegers ϖ (φ (Dagger.weakCompletion.of ϖ A a)) := by
  simp only [completedGenericIntegersFrobenius, completedGenericIntegersLift_algebraMap,
    affineRestriction_apply]

/-- A local endomorphism of the generic integers agreeing with the weak Frobenius on the
affine algebra is the generic integral Frobenius. -/
theorem completedGenericIntegersFrobenius_unique (φ : W →+* W) (q : ℕ) (hq : q ≠ 0)
    (hφ : ∀ z : W, Dagger.weakCompletion.eval ϖ 1 (φ z) =
      Dagger.weakCompletion.eval ϖ 1 z ^ q)
    (g : C →+* C) [IsLocalHom g]
    (haffine : ∀ a : A, g (algebraMap A C a) =
      toCompletedGenericIntegers ϖ (φ (Dagger.weakCompletion.of ϖ A a))) :
    g = completedGenericIntegersFrobenius ϖ φ q hq hφ := by
  apply completedGenericIntegersLift_unique
  intro a
  simpa only [affineRestriction_apply] using haffine a

/-- The generic integral Frobenius acts as the q-th power on the residue function field. -/
theorem completedGenericResidueEquiv_residue_completedGenericIntegersFrobenius
    (φ : W →+* W) (q : ℕ) (hq : q ≠ 0)
    (hφ : ∀ z : W, Dagger.weakCompletion.eval ϖ 1 (φ z) =
      Dagger.weakCompletion.eval ϖ 1 z ^ q) (x : C) :
    completedGenericResidueEquiv π
      (residue C (completedGenericIntegersFrobenius ϖ φ q hq hφ x)) =
        completedGenericResidueEquiv π (residue C x) ^ q := by
  rw [← map_pow]
  apply congrArg (completedGenericResidueEquiv π)
  apply residue_completedGenericIntegersLift
  intro a
  apply (completedGenericResidueEquiv π).injective
  simp only [affineRestriction_apply,
    completedGenericResidueEquiv_residue_toCompletedGenericIntegers, hφ,
    Dagger.weakCompletion.eval_of, map_pow, Ideal.quotEquivOfEq_mk,
    completedGenericResidueEquiv_residue_algebraMap]

variable [IsNoetherianRing A]

/-- A weak-completion Frobenius lift whose parameter has nonzero generic image extends to
the completed generic field. -/
noncomputable def completedGenericFieldFrobenius (φ : W →+* W) (q : ℕ) (hq : q ≠ 0)
    (hφ : ∀ z : W, Dagger.weakCompletion.eval ϖ 1 (φ z) =
      Dagger.weakCompletion.eval ϖ 1 z ^ q)
    (hπ : π ∈ nonZeroDivisors A)
    (hzero : toCompletedGenericIntegers ϖ
      (φ (algebraMap O W ϖ)) ≠ 0) :
    completedGenericField π hπ →+* completedGenericField π hπ :=
  completedGenericFieldLift π (affineRestriction ϖ φ)
    (comap_maximalIdeal_affineRestriction ϖ φ q hq hφ) hπ hπ
    (by simpa only [affineRestriction_parameter] using hzero)

/-- The generic-field Frobenius restricts to the integral Frobenius on the valuation ring. -/
@[simp]
theorem completedGenericFieldFrobenius_algebraMap_completedGenericIntegers
    (φ : W →+* W) (q : ℕ) (hq : q ≠ 0)
    (hφ : ∀ z : W, Dagger.weakCompletion.eval ϖ 1 (φ z) =
      Dagger.weakCompletion.eval ϖ 1 z ^ q)
    (hπ : π ∈ nonZeroDivisors A)
    (hzero : toCompletedGenericIntegers ϖ
      (φ (algebraMap O W ϖ)) ≠ 0) (x : C) :
    completedGenericFieldFrobenius ϖ φ q hq hφ hπ hzero
      (algebraMap C (completedGenericField π hπ) x) =
        algebraMap C (completedGenericField π hπ)
          (completedGenericIntegersFrobenius ϖ φ q hq hφ x) := by
  simp only [completedGenericFieldFrobenius,
    completedGenericFieldLift_algebraMap_completedGenericIntegers,
    completedGenericIntegersFrobenius]

/-- On the affine algebra the generic-field Frobenius is computed through the weak lift. -/
@[simp]
theorem completedGenericFieldFrobenius_algebraMap (φ : W →+* W) (q : ℕ) (hq : q ≠ 0)
    (hφ : ∀ z : W, Dagger.weakCompletion.eval ϖ 1 (φ z) =
      Dagger.weakCompletion.eval ϖ 1 z ^ q)
    (hπ : π ∈ nonZeroDivisors A)
    (hzero : toCompletedGenericIntegers ϖ
      (φ (algebraMap O W ϖ)) ≠ 0) (a : A) :
    completedGenericFieldFrobenius ϖ φ q hq hφ hπ hzero
      (algebraMap A (completedGenericField π hπ) a) =
        algebraMap C (completedGenericField π hπ)
          (toCompletedGenericIntegers ϖ (φ (Dagger.weakCompletion.of ϖ A a))) := by
  simp only [completedGenericFieldFrobenius, completedGenericFieldLift_algebraMap,
    affineRestriction_apply]

/-- If the Frobenius image of the parameter is a uniformizer of the generic integers, the
field extension preserves the normalized generic-field valuation. -/
theorem valuation_completedGenericFieldFrobenius (φ : W →+* W) (q : ℕ) (hq : q ≠ 0)
    (hφ : ∀ z : W, Dagger.weakCompletion.eval ϖ 1 (φ z) =
      Dagger.weakCompletion.eval ϖ 1 z ^ q)
    (hπ : π ∈ nonZeroDivisors A)
    (hzero : toCompletedGenericIntegers ϖ
      (φ (algebraMap O W ϖ)) ≠ 0)
    (hassoc : Associated (toCompletedGenericIntegers ϖ
      (φ (algebraMap O W ϖ))) (algebraMap A C π))
    (x : completedGenericField π hπ) :
    Valued.v (completedGenericFieldFrobenius ϖ φ q hq hφ hπ hzero x) = Valued.v x :=
  valuation_completedGenericFieldLift π _ _ hπ hπ
    (by simpa only [affineRestriction_parameter] using hzero)
    (by simpa only [affineRestriction_parameter] using hassoc) x

variable (φ : Dagger.weakCompletion ϖ A →+* Dagger.weakCompletion ϖ A) (q : ℕ) (hq : q ≠ 0)
  (hφ : ∀ z : Dagger.weakCompletion ϖ A, Dagger.weakCompletion.eval ϖ 1 (φ z) =
    Dagger.weakCompletion.eval ϖ 1 z ^ q)
  (hπ : algebraMap O A ϖ ∈ nonZeroDivisors A)
  (hzero : toCompletedGenericIntegers ϖ
    (φ (algebraMap O (Dagger.weakCompletion ϖ A) ϖ)) ≠ 0)

local notation "E" => completedGenericField π hπ

/-- The generic Frobenius preserves the valuation ring. -/
theorem valuation_completedGenericFieldFrobenius_le_one {x : E} (hx : Valued.v x ≤ 1) :
    Valued.v (completedGenericFieldFrobenius ϖ φ q hq hφ hπ hzero x) ≤ 1 :=
  valuation_completedGenericFieldLift_le_one π _ _ hπ hπ
    (by simpa only [affineRestriction_parameter] using hzero) hx

/-- The generic Frobenius extends the coefficient-field endomorphism induced by its action
on the coefficient ring. -/
theorem completedGenericFieldFrobenius_completedGenericFieldScalarHom {K : Type*} [CommRing K]
    [Algebra O K] [IsLocalization.Away ϖ K] (σ₀ : O →+* O) (σ : K →+* K)
    (hσ₀ : ∀ a : O, σ (algebraMap O K a) = algebraMap O K (σ₀ a))
    (hφ₀ : ∀ a : O, φ (algebraMap O W a) = algebraMap O W (σ₀ a))
    (x : K) :
    completedGenericFieldFrobenius ϖ φ q hq hφ hπ hzero
      (completedGenericFieldScalarHom ϖ hπ x) = completedGenericFieldScalarHom ϖ hπ (σ x) := by
  let F := completedGenericFieldFrobenius ϖ φ q hq hφ hπ hzero
  let s : K →ₐ[O] E := completedGenericFieldScalarHom ϖ hπ
  let j := toCompletedGenericIntegers ϖ (A := A)
  have hcoeff (a : O) : algebraMap C E (j (algebraMap O W a)) = s (algebraMap O K a) := by
    rw [j.commutes, ← IsScalarTower.algebraMap_apply, s.commutes]
  have h : F.comp s.toRingHom = s.toRingHom.comp σ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers ϖ) (RingHom.ext fun a ↦ ?_)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← hcoeff a, hσ₀]
    simp only [F, j, completedGenericFieldFrobenius_algebraMap_completedGenericIntegers,
      completedGenericIntegersFrobenius_toCompletedGenericIntegers, hφ₀, ← hcoeff]
  exact DFunLike.congr_fun h x

/-- The generic Frobenius is continuous for the valuation topology. -/
theorem continuous_completedGenericFieldFrobenius :
    Continuous (completedGenericFieldFrobenius ϖ φ q hq hφ hπ hzero) :=
  continuous_completedGenericFieldLift π _ _ hπ hπ
    (by simpa only [affineRestriction_parameter] using hzero)

/-- A field endomorphism preserving the valuation ring and agreeing with the weak Frobenius
on the affine algebra is the generic Frobenius. -/
theorem completedGenericFieldFrobenius_unique (g : E →+* E)
    (hint : ∀ x, Valued.v x ≤ 1 → Valued.v (g x) ≤ 1)
    (haffine : ∀ a : A, g (algebraMap A E a) =
      algebraMap C E
        (toCompletedGenericIntegers ϖ (φ (Dagger.weakCompletion.of ϖ A a)))) :
    g = completedGenericFieldFrobenius ϖ φ q hq hφ hπ hzero := by
  unfold completedGenericFieldFrobenius
  apply completedGenericFieldLift_unique _ _ _ _ _ _ g hint
  intro a
  simpa only [affineRestriction_apply] using haffine a

end TauCeti.Dagger.weakCompletion

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Lift
public import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.AdicCompletion.Nilpotent

/-!
# Infinitesimal neighbourhoods of a henselization

Henselization preserves every quotient by a power of the defining ideal. The canonical
isomorphisms commute with reduction between powers, and therefore identify the adic completions.
No Noetherianity or finite generation hypothesis on the ideal is needed.

The quotient comparison is the infinitesimal-neighbourhood assertion of Stacks Project,
Lemma 15.12.2 (Tag 0AGU). Its inverse uses `Henselization.lift`, the universal property of
henselization: the image of `I` in `R ⧸ I ^ n` is nilpotent, so this quotient is a henselian
pair. Mathlib's `AdicCompletion.liftAlgHom` assembles the compatible finite-level maps.
-/

public section

universe u

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The canonical map from `R ⧸ I ^ n` to the corresponding quotient of its henselization
is bijective, including at `n = 0`. -/
@[stacks 0AGU "the quotient assertion"]
theorem quotient_pow_bijective (n : ℕ) :
    Function.Bijective (reducedMap (I ^ n) (algebra I)) := by
  let J := I.map (algebraMap R (R ⧸ I ^ n))
  have hJ : J ^ n = ⊥ := by
    simp [J, ← Ideal.map_pow, Ideal.Quotient.algebraMap_eq]
  have : IsAdicComplete J (R ⧸ I ^ n) :=
    isAdicComplete_of_pow_smul_eq_bot (by rw [hJ, Submodule.bot_smul])
  let f : algebra I →ₐ[R] R ⧸ I ^ n := lift (J := J) le_rfl
  have hf : (I ^ n).map (algebraMap R (algebra I)) ≤ RingHom.ker f := by
    rw [RingHom.ker_eq_comap_bot, ← Ideal.map_le_iff_le_comap, Ideal.map_pow, ← extended,
      Ideal.map_pow, map_extended, hJ]
  let g := Ideal.Quotient.liftₐ ((I ^ n).map (algebraMap R (algebra I))) f
    (fun a ha ↦ hf ha)
  have hleft : g.toRingHom.comp (reducedMap (I ^ n) (algebra I)) = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    simp [g]
  have hright : (reducedMap (I ^ n) (algebra I)).comp g.toRingHom = RingHom.id _ := by
    let K := I.map (algebraMap R (algebra I ⧸ (I ^ n).map (algebraMap R (algebra I))))
    have hK : K ^ n = ⊥ := by
      rw [← Ideal.map_pow, IsScalarTower.algebraMap_eq R (algebra I)
        (algebra I ⧸ (I ^ n).map (algebraMap R (algebra I))), ← Ideal.map_map,
        Ideal.Quotient.algebraMap_eq, Ideal.map_quotient_self]
    have : IsAdicComplete K (algebra I ⧸ (I ^ n).map (algebraMap R (algebra I))) :=
      isAdicComplete_of_pow_smul_eq_bot (by rw [hK, Submodule.bot_smul])
    apply Ideal.Quotient.ringHom_ext
    apply ringHom_ext_of_map_le_jacobson (I := I)
    · ext r
      simp [g]
    · have heq : (((reducedMap (I ^ n) (algebra I)).comp g.toRingHom).comp
          (Ideal.Quotient.mk ((I ^ n).map (algebraMap R (algebra I))))).comp
          (algebraMap R (algebra I)) =
            algebraMap R (algebra I ⧸ (I ^ n).map (algebraMap R (algebra I))) := by
        ext r
        simp [g]
      rw [heq]
      exact IsAdicComplete.le_jacobson_bot K
  have hl : Function.LeftInverse g (reducedMap (I ^ n) (algebra I)) :=
    fun x ↦ DFunLike.congr_fun hleft x
  exact ⟨hl.injective,
    fun x ↦ ⟨g x, DFunLike.congr_fun hright x⟩⟩

/-- Henselization preserves the quotient by every power of the defining ideal. -/
noncomputable def quotientPowEquiv (n : ℕ) :
    (R ⧸ I ^ n) ≃ₐ[R] (algebra I ⧸ extended I ^ n) :=
  (AlgEquiv.ofBijective
    { toRingHom := reducedMap (I ^ n) (algebra I)
      commutes' r := reducedMap_mk (I ^ n) (algebra I) r }
    (quotient_pow_bijective I n)).trans
      (Ideal.quotientEquivAlgOfEq R (Ideal.map_pow _ _ _))

/-- The quotient comparison is induced by the structure map of the henselization. -/
@[simp]
theorem quotientPowEquiv_mk (n : ℕ) (r : R) :
    quotientPowEquiv I n (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk (extended I ^ n) (algebraMap R (algebra I) r) := by
  simp [quotientPowEquiv]

/-- The quotient comparisons commute with reduction to a smaller power. -/
@[simp]
theorem factorPow_quotientPowEquiv {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n) :
    Ideal.Quotient.factorPow (extended I) h (quotientPowEquiv I n x) =
      quotientPowEquiv I m (Ideal.Quotient.factorPow I h x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [quotientPowEquiv_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

/-- The inverse quotient comparisons also commute with reduction. -/
@[simp]
theorem factorPow_quotientPowEquiv_symm {m n : ℕ} (h : m ≤ n)
    (x : algebra I ⧸ extended I ^ n) :
    Ideal.Quotient.factorPow I h ((quotientPowEquiv I n).symm x) =
      (quotientPowEquiv I m).symm (Ideal.Quotient.factorPow (extended I) h x) := by
  apply (quotientPowEquiv I m).injective
  simp only [← factorPow_quotientPowEquiv, AlgEquiv.apply_symm_apply]

private theorem completionForward_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)).comp
        ((quotientPowEquiv I n).toAlgHom.comp (_root_.AdicCompletion.evalₐ I n)) =
      (quotientPowEquiv I m).toAlgHom.comp (_root_.AdicCompletion.evalₐ I m) := by
  apply AlgHom.ext
  intro x
  exact (factorPow_quotientPowEquiv I h _).trans
    (congrArg (quotientPowEquiv I m) (factorPow_adicCompletion_evalₐ I h x))

private theorem completionBackward_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)).comp
        ((quotientPowEquiv I n).symm.toAlgHom.comp
          ((_root_.AdicCompletion.evalₐ (extended I) n).restrictScalars R)) =
      (quotientPowEquiv I m).symm.toAlgHom.comp
        ((_root_.AdicCompletion.evalₐ (extended I) m).restrictScalars R) := by
  apply AlgHom.ext
  intro x
  exact (factorPow_quotientPowEquiv_symm I h _).trans
    (congrArg (quotientPowEquiv I m).symm
      (factorPow_adicCompletion_evalₐ (extended I) h x))

private noncomputable def completionForward :
    AdicCompletion I R →ₐ[R] AdicCompletion (extended I) (algebra I) :=
  _root_.AdicCompletion.liftAlgHom (extended I)
    (fun n ↦ (quotientPowEquiv I n).toAlgHom.comp (_root_.AdicCompletion.evalₐ I n))
    (completionForward_compatible I)

private noncomputable def completionBackward :
    AdicCompletion (extended I) (algebra I) →ₐ[R] AdicCompletion I R :=
  _root_.AdicCompletion.liftAlgHom I
    (fun n ↦ (quotientPowEquiv I n).symm.toAlgHom.comp
      ((_root_.AdicCompletion.evalₐ (extended I) n).restrictScalars R))
    (completionBackward_compatible I)

@[simp]
private theorem eval_completionForward (n : ℕ) (x : AdicCompletion I R) :
    _root_.AdicCompletion.evalₐ (extended I) n (completionForward I x) =
      quotientPowEquiv I n (_root_.AdicCompletion.evalₐ I n x) :=
  _root_.AdicCompletion.evalₐ_liftAlgHom _ _ (completionForward_compatible I) n x

@[simp]
private theorem eval_completionBackward (n : ℕ)
    (x : AdicCompletion (extended I) (algebra I)) :
    _root_.AdicCompletion.evalₐ I n (completionBackward I x) =
      (quotientPowEquiv I n).symm (_root_.AdicCompletion.evalₐ (extended I) n x) :=
  _root_.AdicCompletion.evalₐ_liftAlgHom _ _ (completionBackward_compatible I) n x

/-- The `I`-adic completion of `R` agrees with the completion of its henselization
along the extended ideal. -/
noncomputable def completionEquiv :
    AdicCompletion I R ≃ₐ[R] AdicCompletion (extended I) (algebra I) :=
  AlgEquiv.ofAlgHom (completionForward I) (completionBackward I)
    (by
      apply AlgHom.ext
      intro x
      apply _root_.AdicCompletion.ext_evalₐ
      intro n
      simp)
    (by
      apply AlgHom.ext
      intro x
      apply _root_.AdicCompletion.ext_evalₐ
      intro n
      simp)

/-- The completion comparison induces the canonical comparison at each finite level. -/
@[simp]
theorem eval_completionEquiv (n : ℕ) (x : AdicCompletion I R) :
    _root_.AdicCompletion.evalₐ (extended I) n (completionEquiv I x) =
      quotientPowEquiv I n (_root_.AdicCompletion.evalₐ I n x) :=
  eval_completionForward I n x

/-- The inverse completion comparison induces the inverse finite-level comparison. -/
@[simp]
theorem eval_completionEquiv_symm (n : ℕ)
    (x : AdicCompletion (extended I) (algebra I)) :
    _root_.AdicCompletion.evalₐ I n ((completionEquiv I).symm x) =
      (quotientPowEquiv I n).symm (_root_.AdicCompletion.evalₐ (extended I) n x) :=
  eval_completionBackward I n x

/-- The completion comparison commutes with the canonical maps from the original ring. -/
@[simp]
theorem completionEquiv_of (r : R) :
    completionEquiv I (_root_.AdicCompletion.of I R r) =
      _root_.AdicCompletion.of (extended I) (algebra I) (algebraMap R (algebra I) r) := by
  apply _root_.AdicCompletion.ext_evalₐ
  intro n
  simp

end TauCeti.Henselization

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Frobenius.Iterate
import Mathlib.AlgebraicGeometry.ResidueField
import TauCeti.FieldTheory.Finite.FrobeniusFixed

/-!
# Rational points of schemes with trivial Frobenius

If the `q`-power Frobenius of an `𝔽_q`-scheme is the identity, its residue fields are
all equal to the base field. In particular every point is in the image of a rational point.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
  {a : ℕ} {X : Scheme.{u}}

/-- Every point of a scheme on which the finite-field Frobenius is the identity is rational
over the base field. -/
theorem exists_section_of_qPowerFrobenius_eq_id (f : X ⟶ Spec (.of k))
    (ha : Nat.card k = p ^ a) (hF : qPowerFrobenius k f a ha = 𝟙 X) (x : X) :
    ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ ∀ y, s y = x := by
  have : Finite k := Nat.finite_of_card_ne_zero (ha ▸ pow_ne_zero a (Fact.out : p.Prime).ne_zero)
  let R := X.residueField x
  let e := X.fromSpecResidueField x
  have he : qPowerFrobenius k (e ≫ f) a ha = 𝟙 (Spec R) := by
    apply (cancel_mono e).mp
    rw [qPowerFrobenius_naturality k (e ≫ f) f e a ha, hF, Category.comp_id,
      Category.id_comp]
  let ι : CommRingCat.of k ⟶ R := Spec.preimage (e ≫ f)
  let := ι.hom.toAlgebra
  have hpow (t : R) : t ^ Nat.card k = t := by
    have h := congrArg (fun F : Spec R ⟶ Spec R ↦ F.appTop ((ΓSpecIso R).inv t)) he
    apply (ConcreteCategory.bijective_of_isIso (ΓSpecIso R).inv).injective
    simpa only [qPowerFrobenius_appTop_apply, Hom.id_appTop, CommRingCat.id_apply,
      ← map_pow] using h
  let j : k ≃+* R := RingEquiv.ofBijective ι.hom
    ⟨ι.hom.injective, fun t ↦
      (TauCeti.FiniteField.pow_natCard_eq_self_iff_mem_range_algebraMap t).mp (hpow t)⟩
  refine ⟨Spec.map (CommRingCat.ofHom j.symm.toRingHom) ≫ e, ?_,
    fun _ ↦ X.fromSpecResidueField_apply x _⟩
  rw [Category.assoc, ← Spec.map_preimage (e ≫ f), ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext t
  exact j.symm_apply_apply t

end AlgebraicGeometry.Scheme.Hom

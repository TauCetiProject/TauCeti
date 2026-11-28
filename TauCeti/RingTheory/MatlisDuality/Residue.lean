/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.Algebra.Module.Injective.Envelope.Basic
public import TauCeti.RingTheory.MatlisDuality.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.Algebra.Module.Injective.SelfInjective
import TauCeti.RingTheory.LocalRing.Socle

/-!
# The dual of an augmented local algebra

For a finite-dimensional commutative local algebra `A` over a field `k`, an augmentation
`ε : A →ₐ[k] k` identifies the residue field with `k`. The dual of the regular module is its
injective envelope. The embedding sends the class of `a` to the functional
`b ↦ ε (b * a)`, and its image is precisely the socle of the dual.

## References

* M. Auslander, I. Reiten and S. O. Smalø, *Representation Theory of Artin Algebras*,
  Propositions II.3.5 and II.4.6.
-/

public section

open TauCeti TauCeti.MatlisDual
open Submodule

namespace AlgHom

section Algebra

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- The augmentation quotient of an augmented algebra maps to the dual of the regular module by
sending the class of `a` to the functional `b ↦ ε (b * a)`. -/
noncomputable def quotientKerToMatlisDual (ε : A →ₐ[k] k) :
    (A ⧸ RingHom.ker ε) →ₗ[A] MatlisDual k k A :=
  equivLinearMapDualRegular
    ((equivLinearMap k k _).symm (Ideal.quotientKerAlgEquivOfRightInverse
      (fun a ↦ ε.commutes a)).toLinearMap)

/-- On a representative of an augmentation class, the embedding is given by multiplication
followed by the augmentation. -/
@[simp]
theorem quotientKerToMatlisDual_mk_apply (ε : A →ₐ[k] k) (a b : A) :
    equivLinearMap k k A (ε.quotientKerToMatlisDual (Ideal.Quotient.mk _ a)) b =
      ε (b * a) := by
  rw [quotientKerToMatlisDual, equivLinearMapDualRegular_apply_apply,
    LinearEquiv.apply_symm_apply, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
    smul_eq_mul]
  rfl

/-- The augmentation quotient embeds in the regular dual. Evaluation at `1` recovers the
value of the augmentation on a representative. -/
theorem quotientKerToMatlisDual_injective (ε : A →ₐ[k] k) :
    Function.Injective ε.quotientKerToMatlisDual := by
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  simpa only [quotientKerToMatlisDual_mk_apply, one_mul, LinearEquiv.map_zero,
    LinearMap.zero_apply, Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker] using
    congrArg (fun f : MatlisDual k k A ↦ equivLinearMap k k A f 1) ha

/-- The image in the regular dual is the submodule killed by the augmentation ideal. -/
theorem range_quotientKerToMatlisDual (ε : A →ₐ[k] k) :
    LinearMap.range ε.quotientKerToMatlisDual =
      torsionBySet A (MatlisDual k k A) (RingHom.ker ε) := by
  ext φ
  rw [LinearMap.mem_range, mem_torsionBySet_iff]
  constructor
  · rintro ⟨a, rfl⟩ ⟨r, hr⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    ext b
    simp [map_mul, RingHom.mem_ker.mp hr]
  · intro h
    refine ⟨Ideal.Quotient.mk _ (algebraMap k A (equivLinearMap k k A φ 1)), ?_⟩
    ext b
    let c := b - algebraMap k A (ε b)
    have hc : c ∈ RingHom.ker ε := by simp [c, RingHom.mem_ker]
    have hz := congrArg (fun f : MatlisDual k k A ↦ equivLinearMap k k A f 1) (h ⟨c, hc⟩)
    have hsmul : algebraMap k A (ε b) = ε b • (1 : A) := by simp [Algebra.smul_def]
    have hφ : equivLinearMap k k A φ b = ε b * equivLinearMap k k A φ 1 := by
      simpa only [MatlisDual.smul_apply, op_smul_eq_mul, one_mul, LinearEquiv.map_zero,
        LinearMap.zero_apply, c, map_sub, hsmul, map_smul, smul_eq_mul, sub_eq_zero] using hz
    simpa only [quotientKerToMatlisDual_mk_apply, map_mul, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply] using hφ.symm

end Algebra

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- For a finite-dimensional local algebra with residue field identified with the base field,
the regular dual is an injective envelope of the residue field. -/
theorem isInjectiveEnvelope_quotientKerToMatlisDual [IsLocalRing A] [Module.Finite k A]
    (ε : A →ₐ[k] k) : IsInjectiveEnvelope ε.quotientKerToMatlisDual := by
  have hε : Function.Surjective ε := fun a ↦ ⟨algebraMap k A a, by simp⟩
  have hk : RingHom.ker ε = IsLocalRing.maximalIdeal A :=
    IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hε
  have : Module.Finite k (MatlisDual k k A) :=
    Module.Finite.equiv (equivLinearMap k k A).symm
  have : IsArtinian A (MatlisDual k k A) := isArtinian_of_tower k inferInstance
  have := moduleInjective_self_of_isSemisimpleRing k
  refine ⟨inferInstance, ε.quotientKerToMatlisDual_injective, ?_⟩
  rw [range_quotientKerToMatlisDual, hk]
  exact TauCeti.IsLocalRing.isEssential_torsionBySet_maximalIdeal

end AlgHom

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.RingHom.Unramified
public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap

/-!
# Differentials of formally smooth and formally unramified morphisms

A formally smooth morphism of affine monoid schemes induces a surjection on tangent spaces
at the identity, with values in any commutative coefficient algebra, and a formally unramified
one induces an injection (`TauCeti.derivationComp_injective_of_formallyUnramified`); an étale
morphism therefore induces a bijection. No finite presentation, field, or smoothness assumption
on either monoid is needed.

For affine groups, this supplies the surjectivity term of the tangent sequence of a smooth
morphism, and hence the dimension formula for its scheme-theoretic kernel.

## References

* J. S. Milne, *Algebraic Groups* (2017), §1.e, Proposition 1.63, for the relation between
  smoothness, differential surjectivity, and kernel dimensions for group varieties;
  §10.b, 10.6, and Appendix A.51 for the dual-number description of Lie and tangent spaces.
-/

public section

namespace TauCeti

open TrivSqZeroExt

variable {R A A' B : Type*} [CommSemiring R] [CommRing A] [Bialgebra R A]
  [CommRing A'] [Bialgebra R A'] [CommRing B] [Algebra R B]

/-- A formally smooth coordinate morphism induces a surjection on counit-valued derivations.
This is surjectivity of the differential of the corresponding affine monoid morphism. -/
theorem derivationComp_surjective_of_formallySmooth (φ : A' →ₐc[R] A)
    (hφ : φ.toAlgHom.toRingHom.FormallySmooth) :
    Function.Surjective (derivationComp (B := B) φ) := by
  intro d
  -- Give the dual numbers the source-coordinate action defined by the tangent vector.
  let ψ : A' →ₐ[R] DualNumber B := (derivationToTrivSqZeroExtEquivLift R A'
    (Bialgebra.CounitAlgebra R A' B) d).val
  let : Algebra A' A := φ.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R A' A := IsScalarTower.of_algHom φ.toAlgHom
  let : Algebra.FormallySmooth A' A := hφ
  let : Algebra A' (DualNumber B) := ψ.toRingHom.toAlgebra
  let : IsScalarTower R A' (DualNumber B) := IsScalarTower.of_algHom ψ
  let : Algebra A' B :=
    inferInstanceAs (Algebra A' (Bialgebra.CounitAlgebra R A' B))
  let f : A →ₐ[A'] B :=
    { IsScalarTower.toAlgHom R A (Bialgebra.CounitAlgebra R A B) with
      commutes' a := by
        simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe]
        exact congrArg (algebraMap R B) (CoalgHomClass.counit_comp_apply φ a) }
  let g : DualNumber B →ₐ[A'] B :=
    { fstHom R B B with
      commutes' a := by
        exact
          derivationToTrivSqZeroExtEquivLift_apply_fst (B := Bialgebra.CounitAlgebra R A' B) d a }
  have hg : Function.Surjective g := fun b => ⟨inl b, rfl⟩
  have hnil : IsNilpotent (RingHom.ker g.toRingHom) :=
    ⟨2, kerIdeal_sq B B⟩
  -- Formal smoothness lifts the counit through the square-zero reduction.
  let l := Algebra.FormallySmooth.liftOfSurjective f g hg hnil
  let lR : A →ₐ[R] DualNumber B := l.restrictScalars R
  have hl : (fstHom R B B).comp lR =
      IsScalarTower.toAlgHom R A (Bialgebra.CounitAlgebra R A B) := by
    ext a
    exact Algebra.FormallySmooth.liftOfSurjective_apply f g hg hnil a
  -- Taking the infinitesimal part returns a tangent vector above the prescribed one.
  let e := (derivationToTrivSqZeroExtEquivLift R A (Bialgebra.CounitAlgebra R A B)
    (M := Bialgebra.CounitAlgebra R A B)).symm ⟨lR, hl⟩
  refine ⟨e, ?_⟩
  ext a
  rw [derivationComp_apply]
  rw [derivationToTrivSqZeroExtEquivLift_symm_apply]
  have hla : lR (φ a) = ψ a := by
    simpa only [lR, AlgHom.restrictScalars_apply, RingHom.algebraMap_toAlgebra,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, BialgHom.coe_toAlgHom] using l.commutes a
  exact (congrArg snd hla).trans
    (derivationToTrivSqZeroExtEquivLift_apply_snd (B := Bialgebra.CounitAlgebra R A' B) d a)

/-- A formally unramified coordinate morphism induces an injection on counit-valued
derivations. This is injectivity of the differential of the corresponding affine monoid
morphism. -/
theorem derivationComp_injective_of_formallyUnramified (φ : A' →ₐc[R] A)
    (hφ : φ.toAlgHom.toRingHom.FormallyUnramified) :
    Function.Injective (derivationComp (B := B) φ) := by
  intro d₁ d₂ h
  -- The two tangent vectors give two points of the dual numbers over the counit of `A`.
  let l₁ := (derivationToTrivSqZeroExtEquivLift R A (Bialgebra.CounitAlgebra R A B) d₁).val
  let l₂ := (derivationToTrivSqZeroExtEquivLift R A (Bialgebra.CounitAlgebra R A B) d₂).val
  let : Algebra A' A := φ.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R A' A := IsScalarTower.of_algHom φ.toAlgHom
  let : Algebra.FormallyUnramified A' A := hφ
  let : Algebra A' (TrivSqZeroExt (Bialgebra.CounitAlgebra R A B)
    (Bialgebra.CounitAlgebra R A B)) := (l₁.comp (φ : A' →ₐ[R] A)).toRingHom.toAlgebra
  -- They agree on the image of `A'`, since the two tangent vectors have the same differential.
  have h₁₂ (a : A') : l₂ (φ a) = l₁ (φ a) := by
    have h' := (DFunLike.congr_fun h a).symm
    rw [derivationComp_apply, derivationComp_apply] at h'
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (derivationToTrivSqZeroExtEquivLift_apply_fst d₂ _).trans
        (derivationToTrivSqZeroExtEquivLift_apply_fst d₁ _).symm
    · exact (derivationToTrivSqZeroExtEquivLift_apply_snd d₂ _).trans
        (h'.trans (derivationToTrivSqZeroExtEquivLift_apply_snd d₁ _).symm)
  let L₁ : A →ₐ[A'] TrivSqZeroExt (Bialgebra.CounitAlgebra R A B)
      (Bialgebra.CounitAlgebra R A B) := { toRingHom := l₁.toRingHom, commutes' := fun _ ↦ rfl }
  let L₂ : A →ₐ[A'] TrivSqZeroExt (Bialgebra.CounitAlgebra R A B)
      (Bialgebra.CounitAlgebra R A B) := { toRingHom := l₂.toRingHom, commutes' := h₁₂ }
  -- Both reduce to the counit modulo the square-zero ideal, so formal unramifiedness identifies
  -- them.
  have hL : L₁ = L₂ := by
    refine Algebra.FormallyUnramified.ext' (fstHom R (Bialgebra.CounitAlgebra R A B)
      (Bialgebra.CounitAlgebra R A B)).toRingHom ⟨2, kerIdeal_sq _ _⟩ L₁ L₂ fun a ↦ ?_
    exact (derivationToTrivSqZeroExtEquivLift_apply_fst d₁ a).trans
      (derivationToTrivSqZeroExtEquivLift_apply_fst d₂ a).symm
  ext a
  have hsnd : snd (l₁ a) = snd (l₂ a) := congrArg snd (DFunLike.congr_fun hL a)
  exact (derivationToTrivSqZeroExtEquivLift_apply_snd d₁ a).symm.trans
    (hsnd.trans (derivationToTrivSqZeroExtEquivLift_apply_snd d₂ a))

end TauCeti

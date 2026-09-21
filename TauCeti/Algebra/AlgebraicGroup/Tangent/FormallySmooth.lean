/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.RingTheory.RingHom.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap

/-!
# Surjectivity of the differential of a formally smooth morphism

A formally smooth morphism of affine monoid schemes induces a surjection on tangent spaces
at the identity, with values in any commutative coefficient algebra. No finite presentation,
field, or smoothness assumption on either monoid is needed.

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

variable {R A A' B : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
  [CommRing A'] [Bialgebra R A'] [CommRing B] [Algebra R B]

/-- A formally smooth coordinate morphism induces a surjection on counit-valued derivations.
This is surjectivity of the differential of the corresponding affine monoid morphism. -/
theorem derivationComp_surjective_of_formallySmooth (φ : A' →ₐc[R] A)
    (hφ : φ.toAlgHom.toRingHom.FormallySmooth) :
    Function.Surjective (derivationComp (B := B) φ) := by
  intro d
  -- Give the dual numbers the source-coordinate action defined by the tangent vector.
  let ψ : A' →ₐ[R] DualNumber B := (derivationToDualNumberEquivLift R A'
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
        exact derivationToDualNumberEquivLift_apply_fst d a }
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
  let e := (derivationToDualNumberEquivLift R A (Bialgebra.CounitAlgebra R A B)).symm ⟨lR, hl⟩
  refine ⟨e, ?_⟩
  ext a
  rw [derivationComp_apply]
  rw [derivationToDualNumberEquivLift_symm_apply]
  have hla := l.commutes a
  exact (congrArg snd hla).trans (derivationToDualNumberEquivLift_apply_snd d a)

end TauCeti

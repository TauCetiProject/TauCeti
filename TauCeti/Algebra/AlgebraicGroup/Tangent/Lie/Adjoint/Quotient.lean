/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Ideal
public import TauCeti.Algebra.Coalgebra.Subcomodule.Quotient
public import TauCeti.Algebra.Coalgebra.Comodule.Transport
public import TauCeti.Algebra.AlgebraicGroup.Representation.Kernel
public import TauCeti.Algebra.Lie.Solvable.Basic

/-!
# The adjoint representation modulo a Lie ideal

For a connected affine group over an algebraically closed field of characteristic zero,
every Lie ideal is an adjoint subrepresentation. The quotient therefore carries a rational
representation whose differential is the induced Lie bracket. If the quotient Lie algebra
has zero center, the scheme-theoretic kernel of this representation has precisely the given
Lie ideal as its Lie algebra. In particular this applies to the solvable radical.

This realizes the Lie radical by a closed normal subgroup before taking its identity
component, allowing comparison with the solvable radical of the algebraic group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 22.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.

The construction uses `LieIdeal.toAdjointSubcomodule` and the quotient-comodule construction.
The radical case uses `LieAlgebra.hasTrivialRadical_quotient_radical`.
-/

public section

open TauCeti

namespace LieIdeal

universe u

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]

attribute [local instance] Derivation.adjointComodule

/-- The rational adjoint action on the quotient of the tangent Lie algebra by a Lie ideal.
Connectedness and characteristic zero ensure that the ideal is an adjoint subcomodule. -/
noncomputable instance quotientAdjointComodule
    (I : LieIdeal k (Module.Dual k (Bialgebra.CotangentSpace k H))) :
    Comodule k H (Module.Dual k (Bialgebra.CotangentSpace k H) ⧸ I) :=
  Comodule.Transport (C := H) (Submodule.quotEquivOfEq _ _
    (I.toAdjointSubcomodule_toSubmodule (H := H)))

/-- Projection to a Lie-ideal quotient is a morphism for the rational adjoint action. -/
noncomputable def quotientAdjointMkQ
    (I : LieIdeal k (Module.Dual k (Bialgebra.CotangentSpace k H))) :
    Comodule.Hom k H (Module.Dual k (Bialgebra.CotangentSpace k H))
      (Module.Dual k (Bialgebra.CotangentSpace k H) ⧸ I) :=
  (Comodule.transportToHom (C := H)
    (N := Module.Dual k (Bialgebra.CotangentSpace k H) ⧸ I) (Submodule.quotEquivOfEq _ _
    (I.toAdjointSubcomodule_toSubmodule (H := H)))).comp
      (I.toAdjointSubcomodule (H := H)).mkQ

/-- The adjoint-comodule projection is the usual Lie-algebra quotient map. -/
@[simp]
theorem quotientAdjointMkQ_apply
    (I : LieIdeal k (Module.Dual k (Bialgebra.CotangentSpace k H)))
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    I.quotientAdjointMkQ (H := H) x = I.mkQ x := by
  simp only [quotientAdjointMkQ, Comodule.Hom.comp_apply, Comodule.transportToHom_apply,
    Subcomodule.mkQ_apply]
  exact Submodule.quotEquivOfEq_mk _ _ _ x

/-- The differential of the quotient adjoint representation is the Lie bracket modulo the
ideal. -/
@[simp↓]
theorem differential_quotientAdjointComodule
    (I : LieIdeal k (Module.Dual k (Bialgebra.CotangentSpace k H)))
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k))
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    Comodule.differential (R := k) (H := H) d (I.mkQ x) =
      I.mkQ ⁅Derivation.cotangentDualLieEquiv.symm d, x⁆ := by
  simpa only [quotientAdjointMkQ_apply, Derivation.differential_adjointComodule] using
    (I.quotientAdjointMkQ.map_differential d x).symm

/-- The tangent vectors acting trivially on the quotient adjoint representation are exactly
the inverse image of the center of the quotient Lie algebra. -/
theorem differential_quotientAdjointComodule_eq_zero_iff
    (I : LieIdeal k (Module.Dual k (Bialgebra.CotangentSpace k H)))
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    Comodule.differential (R := k) (H := H)
        (M := Module.Dual k (Bialgebra.CotangentSpace k H) ⧸ I) d = 0 ↔
      I.mkQ (Derivation.cotangentDualLieEquiv.symm d) ∈
        LieAlgebra.center k (Module.Dual k (Bialgebra.CotangentSpace k H) ⧸ I) := by
  rw [← LieAlgebra.self_module_ker_eq_center, LieModule.mem_ker]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := I.surjective_mkQ y
    rw [← LieHom.map_lie, ← differential_quotientAdjointComodule, h, LinearMap.zero_apply]
  · intro h
    ext y
    obtain ⟨x, rfl⟩ := I.surjective_mkQ y
    rw [differential_quotientAdjointComodule, LieHom.map_lie, h, LinearMap.zero_apply]

/-- If the quotient Lie algebra has zero center, the kernel of its rational adjoint quotient
representation has Lie algebra exactly the original ideal. The basis only specifies the
coordinate morphism to the general linear group. -/
theorem mem_lieSubalgebra_kernel_quotientAdjoint_iff
    (I : LieIdeal k (Module.Dual k (Bialgebra.CotangentSpace k H)))
    (hI : LieAlgebra.center k (Module.Dual k (Bialgebra.CotangentSpace k H) ⧸ I) = ⊥)
    {n : ℕ}
    (b : Module.Basis (Fin n) k (Module.Dual k (Bialgebra.CotangentSpace k H) ⧸ I))
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    d ∈ (CommHopfAlgCat.kernelHopfIdeal
      (CommHopfAlgCat.ofHom (Comodule.coordinateBialgHom (H := H) b))).lieSubalgebra
        (B := k) ↔ Derivation.cotangentDualLieEquiv.symm d ∈ I := by
  rw [Derivation.mem_lieSubalgebra_kernel_coordinateBialgHom_iff,
    differential_quotientAdjointComodule_eq_zero_iff, hI, LieSubmodule.mem_bot,
    I.mkQ_eq_zero]

end LieIdeal

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]

/-- The solvable radical of the tangent Lie algebra of a connected affine group in
characteristic zero is the Lie algebra of a closed normal subgroup. The subgroup can be
chosen as the kernel of the adjoint representation modulo the Lie radical. -/
theorem exists_isNormal_lieSubalgebra_eq_radical
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) [ConnectedSpace (PrimeSpectrum H)] :
    ∃ I : HopfIdeal k H, I.IsNormal ∧
      I.lieSubalgebra (B := k) =
        (LieAlgebra.radical k (Module.Dual k (Bialgebra.CotangentSpace k H))).toLieSubalgebra.comap
          Derivation.cotangentDualLieEquiv.symm.toLieHom := by
  let L := Module.Dual k (Bialgebra.CotangentSpace k H)
  let Q := L ⧸ LieAlgebra.radical k L
  let b := Module.finBasis k Q
  let f := CommHopfAlgCat.ofHom (Comodule.coordinateBialgHom (H := H) b)
  refine ⟨CommHopfAlgCat.kernelHopfIdeal f,
    CommHopfAlgCat.isNormal_kernelHopfIdeal f, ?_⟩
  ext d
  exact LieIdeal.mem_lieSubalgebra_kernel_quotientAdjoint_iff
    (LieAlgebra.radical k L) (LieAlgebra.center_eq_bot _ _) b d

end TauCeti.FiniteTypeCommHopfAlgCat

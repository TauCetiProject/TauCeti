/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.LinearAlgebra.Eigenspace.Semisimple

/-!
# Differentiated actions of diagonalizable groups

Let `π : H →ₐc[R] R[X]` be the coordinate morphism of a homomorphism `D(X) → G`, and let
`V` be a representation of `G`. A tangent vector `d` of `D(X)` acts on the `x`-weight space
of `V` by the scalar `d(x)`. Thus, over a field, every tangent vector coming from `D(X)`
acts diagonally, and in particular semisimply, on `V`.

These results apply to the differentiated action of a split central torus on a rational
representation. They require neither finite dimension nor characteristic zero. The weight
formula works over any commutative ring and even for a commutative monoid `X`, without an
antipode. In positive characteristic distinct characters can have the same differential;
the weight-space inclusion in an eigenspace need not be an equality.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and I.7.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 12 and 22.
-/

public section

open scoped TensorProduct

namespace TauCeti.DiagonalizableGroup

variable {R H X V : Type*} [CommRing R] [CommRing H] [Bialgebra R H]
variable [CommMonoid X] [AddCommGroup V] [Module R V] [Comodule R H V]

variable (V)

/-- A tangent vector from a diagonalizable group acts on a character space by the
differential of that character. -/
theorem differential_of_mem_weightSpace (π : H →ₐc[R] MonoidAlgebra R X)
    (d : Derivation R (MonoidAlgebra R X)
      (Bialgebra.CounitAlgebra R (MonoidAlgebra R X) R))
    {x : X} {v : V} (hv : v ∈ weightSpace V π.toCoalgHom x) :
    Comodule.differential (R := R) (H := H) (M := V) (derivationComp π d) v =
      Bialgebra.CounitAlgebra.algEquivSelf R (MonoidAlgebra R X) R
        (d (MonoidAlgebra.single x 1)) • v := by
  rw [← Comodule.differential_corestrict V π d v]
  let _ : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict π.toCoalgHom
  simp only [Comodule.differential_apply, Comodule.corestrict_coact_apply, mem_weightSpace.mp hv]
  simp

/-- Character spaces lie in the corresponding eigenspaces of the differentiated action.
Different character spaces may have the same eigenvalue. -/
theorem weightSpace_le_eigenspace_differential (π : H →ₐc[R] MonoidAlgebra R X)
    (d : Derivation R (MonoidAlgebra R X)
      (Bialgebra.CounitAlgebra R (MonoidAlgebra R X) R)) (x : X) :
    weightSpace V π.toCoalgHom x ≤
      Module.End.eigenspace
        (Comodule.differential (R := R) (H := H) (M := V) (derivationComp π d))
        (Bialgebra.CounitAlgebra.algEquivSelf R (MonoidAlgebra R X) R
          (d (MonoidAlgebra.single x 1))) := by
  intro v hv
  exact Module.End.mem_eigenspace_iff.mpr (differential_of_mem_weightSpace V π d hv)

/-- The eigenspaces of any tangent vector from a diagonalizable group span the representation.
No finiteness or algebraic-closure assumption is needed. -/
theorem iSup_eigenspace_differential_eq_top (π : H →ₐc[R] MonoidAlgebra R X)
    (d : Derivation R (MonoidAlgebra R X)
      (Bialgebra.CounitAlgebra R (MonoidAlgebra R X) R)) :
    ⨆ μ : R, Module.End.eigenspace
      (Comodule.differential (R := R) (H := H) (M := V) (derivationComp π d)) μ = ⊤ := by
  classical
  apply top_unique
  rw [← (isInternal_weightSpace V π.toCoalgHom).submodule_iSup_eq_top]
  refine iSup_le fun x ↦ (weightSpace_le_eigenspace_differential V π d x).trans ?_
  exact le_iSup _ _

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Bialgebra k A]
variable [Module k V] [Comodule k A V]

/-- Every tangent vector from a diagonalizable group acts semisimply in every rational
representation, including representations of infinite dimension. -/
theorem isSemisimple_differential (π : A →ₐc[k] MonoidAlgebra k X)
    (d : Derivation k (MonoidAlgebra k X)
      (Bialgebra.CounitAlgebra k (MonoidAlgebra k X) k)) :
    Module.End.IsSemisimple
      (Comodule.differential (R := k) (H := A) (M := V) (derivationComp π d)) :=
  isSemisimple_of_iSup_eigenspace_eq_top (iSup_eigenspace_differential_eq_top V π d)

end TauCeti.DiagonalizableGroup

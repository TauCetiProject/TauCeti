/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.VectorStabilizer
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Fixed

/-!
# The centralizer of a Lie algebra element

Let `G = Spec H` be an affine group over a field `k` whose Lie algebra `𝔤` is finite-dimensional.
The centralizer `C_G(x)` of `x ∈ 𝔤` is the stabilizer of `x` under the adjoint representation:
the closed subgroup whose points fix `x` under `Ad`. Its points with values in any commutative
`k`-algebra are the points whose adjoint action fixes the constant extension of `x`, so this is
the scheme-theoretic centralizer.

The main result identifies its Lie algebra with the kernel of `ad x`
(`TauCeti.lieSubalgebra_centralizerHopfIdeal`). The proof differentiates the adjoint
representation, whose differential is the adjoint action of `𝔤` on itself. No smoothness,
connectedness or characteristic assumption is needed. For a connected group over an
algebraically closed field of characteristic zero, the centralizer is the whole group exactly when
`x` is central in `𝔤`.

The Lie algebra `𝔤` is modelled as the dual of the augmentation cotangent space, which carries
the adjoint comodule; `Derivation.cotangentDualLieEquiv` identifies it with the counit-valued
derivations, where closed subgroups have their Lie subalgebras.

## Main declarations

* `TauCeti.centralizerHopfIdeal`: the Hopf ideal of the centralizer of `x ∈ 𝔤`.
* `TauCeti.centralizerHopfIdeal_le_ker_iff`: its algebra-valued points are the points whose
  adjoint action fixes `x`.
* `TauCeti.mem_lieSubalgebra_centralizerHopfIdeal_iff` and
  `TauCeti.lieSubalgebra_centralizerHopfIdeal`: its Lie algebra is the kernel of `ad x`.
* `TauCeti.centralizerHopfIdeal_eq_bot_iff_mem_center`: for a connected group over an
  algebraically closed field of characteristic zero, the centralizer is the whole group exactly
  when `x` is central.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 10, in particular the Lie algebra of a
  stabilizer.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §1.3, for centralizers of elements of `𝔤`.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti

universe u

section Basic

variable {k : Type u} [Field k] (H : Type u) [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

attribute [local instance] Derivation.adjointComodule

/-- The Hopf ideal of the centralizer of an element `x` of the Lie algebra, the stabilizer of `x`
under the adjoint representation. Contravariantly, it cuts out the closed subgroup of `Spec H`
fixing `x` under `Ad`. -/
noncomputable def centralizerHopfIdeal (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    HopfIdeal k H :=
  Comodule.stabilizerHopfIdeal k H x

/-- The centralizer of `x` is the stabilizer of `x` under the adjoint comodule. Rewriting with this
transfers the defining equations and universal property of `Comodule.stabilizerHopfIdeal`. -/
theorem centralizerHopfIdeal_def (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    centralizerHopfIdeal H x = Comodule.stabilizerHopfIdeal k H x :=
  (rfl)

variable {H}

/-- An algebra-valued point lies in the centralizer of `x` exactly when its adjoint action fixes
the constant extension of `x`. The value algebra may be nonreduced. -/
theorem centralizerHopfIdeal_le_ker_iff (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    {A : Type u} [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)) :
    (centralizerHopfIdeal H x).toIdeal ≤ RingHom.ker g.ofConv ↔
      Derivation.adDerivation A (Derivation.pointInCounitAlgebra A g)
          (Derivation.mapValue (Algebra.ofId k A)
            (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) x)) =
        Derivation.mapValue (Algebra.ofId k A)
          (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) x) := by
  rw [centralizerHopfIdeal_def, Comodule.stabilizerHopfIdeal_le_ker_iff,
    ← (Derivation.tangentScalarExtensionEquiv (R := k) (A := H) (B := A)).injective.eq_iff,
    Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint (CommAlgCat.of k A) g,
    Derivation.tangentScalarExtensionEquiv_tmul, one_smul]

/-- The centralizer of `x` is the whole group exactly when `x` is fixed by the adjoint
coaction. -/
theorem centralizerHopfIdeal_eq_bot_iff (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    centralizerHopfIdeal H x = ⊥ ↔ Comodule.coact (R := k) (C := H) x = x ⊗ₜ[k] (1 : H) :=
  Comodule.stabilizerHopfIdeal_eq_bot_iff x

/-- The centralizer of `0` is the whole group. -/
@[simp]
theorem centralizerHopfIdeal_zero :
    centralizerHopfIdeal H (0 : Module.Dual k (Bialgebra.CotangentSpace k H)) = ⊥ :=
  Comodule.stabilizerHopfIdeal_zero

/-- A tangent vector lies in the Lie algebra of the centralizer of `x` exactly when it commutes
with `x`. -/
theorem mem_lieSubalgebra_centralizerHopfIdeal_iff
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    d ∈ (centralizerHopfIdeal H x).lieSubalgebra (B := k) ↔
      ⁅Derivation.cotangentDualLieEquiv (R := k) (H := H) x, d⁆ = 0 := by
  rw [centralizerHopfIdeal_def, Comodule.mem_lieSubalgebra_stabilizerHopfIdeal_iff,
    Derivation.differential_adjointComodule, ← lie_skew, neg_eq_zero]
  -- Transport `⁅x, e.symm d⁆ = 0` along the Lie algebra isomorphism `e`.
  rw [← (Derivation.cotangentDualLieEquiv (R := k) (H := H)).injective.eq_iff]
  simp

/-- **The Lie algebra of a centralizer.** The Lie algebra of the centralizer of `x` is the kernel
of `ad x`. -/
theorem lieSubalgebra_centralizerHopfIdeal (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    ((centralizerHopfIdeal H x).lieSubalgebra (B := k)).toSubmodule =
      LinearMap.ker (LieAlgebra.ad k (Derivation k H (Bialgebra.CounitAlgebra k H k))
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)) := by
  ext d
  rw [LieSubalgebra.mem_toSubmodule, mem_lieSubalgebra_centralizerHopfIdeal_iff,
    LinearMap.mem_ker, LieAlgebra.ad_apply]

/-- An element of the Lie algebra lies in the Lie algebra of its own centralizer. -/
theorem cotangentDualLieEquiv_mem_lieSubalgebra_centralizerHopfIdeal
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    Derivation.cotangentDualLieEquiv (R := k) (H := H) x ∈
      (centralizerHopfIdeal H x).lieSubalgebra (B := k) :=
  (mem_lieSubalgebra_centralizerHopfIdeal_iff x _).mpr (lie_self _)

end Basic

section Connected

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]

/-- For a connected affine group over an algebraically closed field of characteristic zero, the
centralizer of `x` is the whole group exactly when `x` is central in the Lie algebra. -/
theorem centralizerHopfIdeal_eq_bot_iff_mem_center
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    centralizerHopfIdeal H x = ⊥ ↔
      x ∈ LieAlgebra.center k (Module.Dual k (Bialgebra.CotangentSpace k H)) := by
  rw [centralizerHopfIdeal_eq_bot_iff,
    FiniteTypeCommHopfAlgCat.coact_adjointComodule_eq_tmul_one_iff_mem_center]

end Connected

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.NumberTheory.HeckeRing.Commutativity
public import TauCeti.NumberTheory.HeckeRing.GLn.FractionRing
public import TauCeti.RingTheory.DiscreteValuationRing.Basic

import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Cartan.DiscreteValuationRing
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transpose

/-!
# Commutativity of the local Hecke ring of `GL_n`

Let `R` be a discrete valuation ring with fraction field `K` and finite residue field. The Hecke
ring of `(GL_n(K), GL_n(R))` is commutative over every commutative coefficient semiring. This is
Gelfand's argument, in the form of Shimura's Proposition 3.8: transposition `g ↦ gᵀ` is an
anti-automorphism of `GL_n(K)` preserving `GL_n(R)`, so it induces an anti-involution of the Hecke
datum. By the Cartan decomposition (`TauCeti.exists_monotone_mem_doubleCoset_diagGL_zpow`) every
double coset has a diagonal representative `diag(π^{a₀}, …, π^{a_{n-1}})`, which transposition
fixes, so the induced involution of `GL_n(R) \ GL_n(K) / GL_n(R)` is the identity.

## Main definitions

* `HeckeRing.GLn.transposeAntiInvolutionIntegralGL R K n`: transposition as an anti-involution of
  the Hecke datum `(GL_n(K), GL_n(R))`.
* `HeckeRing.GLn.commSemiringIntegralGLHeckeRing`: the local Hecke ring as a commutative semiring.

## Main results

* `HeckeRing.GLn.transposeAntiInvolutionIntegralGL_onHeckeCoset_eq_self`: transposition fixes
  every double coset.
* `HeckeRing.GLn.mul_comm_integralGLHeckeRing`: the local Hecke ring is commutative.

## References

* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, Princeton
  University Press (1971), Proposition 3.8.
* I. G. Macdonald, *Spherical Functions on a Group of p-adic Type*, Ramanujan Institute (1971),
  Chapter V, §1.
-/

public section

open Matrix HeckeCosetModule TauCeti

namespace HeckeRing.GLn

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K] (n : ℕ)

/-- Transposition as an anti-involution of the Hecke datum `(GL_n(K), GL_n(R))`. -/
noncomputable def transposeAntiInvolutionIntegralGL :
    HeckeAntiInvolution (⊤ : Submonoid (GL (Fin n) K)) (integralGL R K (Fin n)) :=
  HeckeAntiInvolution.ofAmbient (GeneralLinearGroup.transposeMulEquiv (R := K) (Fin n)).toMonoidHom
    GeneralLinearGroup.transposeMulEquiv_transposeMulEquiv
    (fun _ hg ↦ transposeMulEquiv_mem_integralGL hg) (fun _ _ ↦ Submonoid.mem_top _)

/-- The anti-involution acts as transposition. -/
@[simp]
theorem transposeAntiInvolutionIntegralGL_bar {x : GL (Fin n) K} (hx : x ∈ (⊤ : Submonoid _)) :
    (transposeAntiInvolutionIntegralGL R K n).bar x hx =
      (GeneralLinearGroup.transposeMulEquiv (Fin n) x).unop :=
  HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx

variable [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
  [IsFractionRing R K]

/-- **Transposition fixes every double coset** of `GL_n(R)` in `GL_n(K)`: by the Cartan
decomposition each double coset has a diagonal representative, and transposition fixes diagonal
matrices. -/
theorem transposeAntiInvolutionIntegralGL_onHeckeCoset_eq_self
    (D : HeckeCoset (⊤ : Submonoid (GL (Fin n) K)) (integralGL R K (Fin n))
      (integralGL R K (Fin n))) :
    (transposeAntiInvolutionIntegralGL R K n).onHeckeCoset D = D := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ0 : algebraMap R K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hϖ.ne_zero
  induction D using HeckeCoset.induction with
  | h g =>
    obtain ⟨a, -, hga⟩ := exists_monotone_mem_doubleCoset_diagGL_zpow (K := K) hϖ
      (π := Units.mk0 _ hϖ0) rfl (g : GL (Fin n) K)
    set d : GL (Fin n) K := diagGL fun i ↦ Units.mk0 _ hϖ0 ^ a i
    have hgd : HeckeCoset.mk (integralGL R K (Fin n)) (integralGL R K (Fin n)) g =
        HeckeCoset.mk _ _ ⟨d, Submonoid.mem_top _⟩ :=
      HeckeCoset.mk_eq_mk_of_mem hga
    rw [hgd, HeckeAntiInvolution.onHeckeCoset_mk]
    refine congrArg (HeckeCoset.mk _ _) (Subtype.ext ?_)
    exact (transposeAntiInvolutionIntegralGL_bar R K n _).trans
      (Units.ext (by simp [d, diagGL_coe]))

/-- **The local Hecke ring of `GL_n` is commutative** over every commutative coefficient
semiring. -/
theorem mul_comm_integralGLHeckeRing (S : Type*) [CommSemiring S]
    (f g : 𝕋 (⊤ : Submonoid (GL (Fin n) K)) (integralGL R K (Fin n)) S) : f * g = g * f :=
  mul_comm_of_antiInvolution S (transposeAntiInvolutionIntegralGL R K n)
    (transposeAntiInvolutionIntegralGL_onHeckeCoset_eq_self R K n) f g

/-- The local Hecke ring of `GL_n` over a commutative semiring, as a commutative semiring. -/
@[instance_reducible]
noncomputable def commSemiringIntegralGLHeckeRing (S : Type*) [CommSemiring S] :
    CommSemiring (𝕋 (⊤ : Submonoid (GL (Fin n) K)) (integralGL R K (Fin n)) S) :=
  commSemiringOfAntiInvolution S (transposeAntiInvolutionIntegralGL R K n)
    (transposeAntiInvolutionIntegralGL_onHeckeCoset_eq_self R K n)

end HeckeRing.GLn

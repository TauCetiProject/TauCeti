/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Adjoint
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Infinitesimal
public import Mathlib.Algebra.Lie.Ideal

/-!
# The Lie ideal of a normal closed subgroup

The Lie algebra of a normal closed subgroup of an affine group scheme is an ideal in the
ambient Lie algebra. First, scheme-theoretic normality makes its tangent space stable under
conjugation by every algebra-valued point. Applying this to a dual-number point gives stability
under the Lie bracket. This works over commutative rings, without smoothness, reducedness, or
finite-type assumptions, and retains infinitesimal normal subgroups in positive characteristic.

The resulting `HopfIdeal.IsNormal.lieIdeal` has the same underlying submodule as the existing
closed-subgroup Lie subalgebra: its elements are exactly the counit-valued derivations vanishing
on the defining Hopf ideal. It allows normal subgroup constructions to be used in the ideal
and quotient APIs for Lie algebras.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10, the Lie algebra and adjoint representation.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.7.
-/

public section

namespace TauCeti.HopfIdeal

open WithConv TrivSqZeroExt

variable {R H B : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [CommRing B] [Algebra R B] {I : HopfIdeal R H}

/-- The Lie algebra of a normal closed subgroup is stable under the adjoint action of every
algebra-valued point of the ambient group. -/
theorem IsNormal.adDerivation_mem_lieSubalgebra (hI : I.IsNormal)
    (g : WithConv (H →ₐ[R] Bialgebra.CounitAlgebra R H B))
    {d : Derivation R H (Bialgebra.CounitAlgebra R H B)}
    (hd : d ∈ I.lieSubalgebra (B := B)) :
    Derivation.adDerivation B g d ∈ I.lieSubalgebra (B := B) := by
  rw [mem_lieSubalgebra_iff] at hd ⊢
  let C := Bialgebra.CounitAlgebra R H B
  let p := (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val
  let q := AlgHom.mapValue (H := H) (inlAlgHom R C C) g
  let N := CommHopfAlgCat.quotientPointsSubgroup
    (_root_.CommHopfAlgCat.of R H) I (CommAlgCat.of R (DualNumber C))
  have hp : p ∈ N := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro x hx
    apply TrivSqZeroExt.ext
    · rw [derivationMulEquivTangentKer_apply_fst]
      simp [I.counit_eq_zero hx]
      rfl
    · rw [derivationMulEquivTangentKer_apply_snd]
      exact hd x (mem_toIdeal.mpr hx)
  have hn := CommHopfAlgCat.quotientPointsSubgroup_normal
    (_root_.CommHopfAlgCat.of R H) I hI (CommAlgCat.of R (DualNumber C))
  have hc := hn.conj_mem p hp q
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hc
  intro x hx
  have hz := congrArg snd (hc x (mem_toIdeal.mp hx))
  rw [Derivation.snd_conjugate_tangentPoint] at hz
  exact hz

/-- Bracketing an ambient tangent vector with a tangent vector of a normal closed subgroup
again gives a tangent vector of that subgroup. -/
theorem IsNormal.lie_mem_lieSubalgebra (hI : I.IsNormal)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B))
    {e : Derivation R H (Bialgebra.CounitAlgebra R H B)}
    (he : e ∈ I.lieSubalgebra (B := B)) :
    ⁅d, e⁆ ∈ I.lieSubalgebra (B := B) := by
  let C := Bialgebra.CounitAlgebra R H B
  let φ := (inlAlgHom R C C).comp (Bialgebra.CounitAlgebra.algEquivSelf R H B).symm.toAlgHom
  have he' : Derivation.mapValue φ e ∈ I.lieSubalgebra (B := DualNumber C) := by
    rw [mem_lieSubalgebra_iff] at he ⊢
    intro x hx
    rw [Derivation.mapValue_apply, he x hx]
    exact map_zero φ
  let g := (Bialgebra.CounitAlgebra.pointsMulEquiv R H (DualNumber C)).symm
    (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val
  have ha := hI.adDerivation_mem_lieSubalgebra g he'
  rw [mem_lieSubalgebra_iff] at ha ⊢
  intro x hx
  have hz := congrArg (fun z ↦ snd
    (Bialgebra.CounitAlgebra.algEquivSelf R H (DualNumber C) z)) (ha x hx)
  rw [Derivation.adDerivation_dualNumber_apply] at hz
  simpa only [snd_add, snd_inl, snd_inr, zero_add, map_zero, snd_zero] using hz

/-- The Lie ideal of the normal closed subgroup defined by `I`, inside the ambient tangent
Lie algebra with coefficients in `B`. -/
noncomputable def IsNormal.lieIdeal (hI : I.IsNormal) :
    LieIdeal B (Derivation R H (Bialgebra.CounitAlgebra R H B)) where
  __ := (I.lieSubalgebra (B := B)).toSubmodule
  lie_mem := hI.lie_mem_lieSubalgebra _

/-- The underlying Lie subalgebra of the normal-subgroup Lie ideal is the closed-subgroup
Lie subalgebra. To identify their underlying submodules, use
`rw [← LieIdeal.toLieSubalgebra_toSubmodule, hI.lieIdeal_toLieSubalgebra]`. -/
@[simp]
theorem IsNormal.lieIdeal_toLieSubalgebra (hI : I.IsNormal) :
    LieIdeal.toLieSubalgebra B _ (hI.lieIdeal (B := B)) = I.lieSubalgebra (B := B) := by
  ext d
  rfl

/-- Membership in the normal-subgroup Lie ideal is vanishing on its defining Hopf ideal. -/
@[simp]
theorem IsNormal.mem_lieIdeal_iff (hI : I.IsNormal)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    d ∈ hI.lieIdeal (B := B) ↔ ∀ x ∈ I.toIdeal, d x = 0 :=
  I.mem_lieSubalgebra_iff d

end TauCeti.HopfIdeal

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.CrossedHom
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Cocycle
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.CompatibleSystem

/-!
# The prescription property for free pro-`p` groups

Every continuous character `χ : F →ₜ* ℤ_pˣ` of a free pro-`p` group `F = freeProP p X` has the
prescription property (`TauCeti.HasPrescriptionProperty`): every reduction
`H¹(F, I(χ)/pⁱ) → H¹(F, I(χ)/p)` is surjective. This is the free case of Labute's condition on the
orientation of a Demushkin group. It is an instance of the general fact that a surjective
coefficient map induces a surjection on `H¹` of a free pro-`p` group
(`TauCeti.freeProP.explicitCoeff1_surjective`): a continuous `1`-cocycle on `F` is determined by
its values on the generators and takes any prescribed values there, so lifting a cocycle is lifting
its values on the generators.

Read through Labute's third formulation of the property, this says that for a free pro-`p` group
of finite rank and any continuous character `χ`, every tuple of `p`-adic integers is the tuple of
values on the generators of a continuous crossed homomorphism `F → ℤ_p` for `χ`, a continuous `F`
with `F (x * y) = χ x * F y + F x` (`TauCeti.IsCrossedHom`).

## Main results

* `TauCeti.freeProP.hasPrescriptionProperty`: every continuous character of a free pro-`p` group
  has the prescription property.
* `TauCeti.freeProP.exists_continuous_isCrossedHom_forall_apply_of_eq`: on a free pro-`p` group of
  finite rank, a continuous crossed homomorphism to `ℤ_p` for any continuous character takes any
  prescribed values on the generators.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2
  and Theorem 4.
* J.-P. Serre, *Structure de certains pro-p-groupes*, Séminaire Bourbaki 252 (1962/63).
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime] {X : Type u}

/-- **Every continuous character of a free pro-`p` group has the prescription property.** The
reductions `I(χ)/pⁱ → I(χ)/p` are surjective, and a surjective coefficient map induces a
surjection on `H¹` of a free pro-`p` group. -/
theorem freeProP.hasPrescriptionProperty (χ : freeProP p X →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty χ :=
  (hasPrescriptionProperty_iff χ).2 fun i hi ↦
    freeProP.explicitCoeff1_surjective (ZModTwist.isProP_multiplicative χ i) _ _
      (ZModTwist.reduce_surjective χ hi)

/-- **Continuous crossed homomorphisms of a free pro-`p` group of finite rank take prescribed
values on the generators.** For `F = freeProP p X` with `X` finite, a continuous character
`χ : F →ₜ* ℤ_pˣ` and any `c : X → ℤ_p`, there is a continuous `F : freeProP p X → ℤ_p` with
`F (x * y) = χ x * F y + F x` and `F (of x) = c x`. -/
theorem freeProP.exists_continuous_isCrossedHom_forall_apply_of_eq [Finite X]
    (χ : freeProP p X →ₜ* ℤ_[p]ˣ) (c : X → ℤ_[p]) :
    ∃ F : freeProP p X → ℤ_[p], Continuous F ∧ IsCrossedHom χ F ∧ ∀ x, F (freeProP.of x) = c x := by
  obtain ⟨F, hFc, hFmul, hFv⟩ :=
    (freeProP.hasPrescriptionProperty χ).exists_continuous_forall_mul_eq_and_apply_eq
      (isProP_freeProP p X) (isTopologicallyFinitelyGenerated_freeProP p X)
      (freeProP.linearIndependent_frattiniQuotient_of p X) c
  exact ⟨F, hFc, isCrossedHom_iff.2 hFmul, hFv⟩

end TauCeti

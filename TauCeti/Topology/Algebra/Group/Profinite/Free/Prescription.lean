/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Cocycle
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription

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

## Main results

* `TauCeti.freeProP.hasPrescriptionProperty`: every continuous character of a free pro-`p` group
  has the prescription property.

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

end TauCeti

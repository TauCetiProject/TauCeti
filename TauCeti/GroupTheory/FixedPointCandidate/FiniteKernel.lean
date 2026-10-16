/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.FixedSubgroup.FiniteKernel

/-!
# Fixed-point candidates through a finite kernel

The fixed-subgroup isomorphism induced by an equivariant surjection with finite, fixed-point-free
kernel transports the derived subgroup modulo its own centre. This extends the existing
`TauCeti.FixedPointCandidate.congr` to homomorphisms that need not be injective. It asserts neither
finiteness nor simplicity of the candidates.
-/

public section

namespace TauCeti.FixedPointCandidate

variable {G H : Type*} [Group G] [Group H] {F : G →* G} {F' : H →* H}

/-- Transport the candidate through an equivariant surjection with finite kernel whose only
fixed point is the identity. -/
noncomputable def congrOfFiniteKer (ψ : G →* H) [Finite ψ.ker]
    (hψ : ψ.comp F = F'.comp ψ) (hsurj : Function.Surjective ψ)
    (hker : Disjoint ψ.ker (fixedSubgroup F)) :
    FixedPointCandidate F ≃* FixedPointCandidate F' :=
  DerivedCentralQuotient.congr (ψ.fixedSubgroupCongrOfFiniteKer hψ hsurj hker)

@[simp]
theorem congrOfFiniteKer_mk (ψ : G →* H) [Finite ψ.ker]
    (hψ : ψ.comp F = F'.comp ψ) (hsurj : Function.Surjective ψ)
    (hker : Disjoint ψ.ker (fixedSubgroup F)) (x : ↥(commutator ↥(fixedSubgroup F))) :
    congrOfFiniteKer ψ hψ hsurj hker (x : FixedPointCandidate F) =
      (MulEquiv.commutatorCongr (ψ.fixedSubgroupCongrOfFiniteKer hψ hsurj hker) x :
        FixedPointCandidate F') := by
  simp only [congrOfFiniteKer, DerivedCentralQuotient.congr_mk]

end TauCeti.FixedPointCandidate

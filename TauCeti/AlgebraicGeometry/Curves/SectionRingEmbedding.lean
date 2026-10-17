/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.SectionRing
public import TauCeti.LinearAlgebra.SymmetricAlgebra.GradedMap

/-!
# Embedding `Proj` of a section ring into the projective space of `L(D)`

Let `F / k` be an algebraic function field and `D` a divisor of `F`. The functions `s ∈ L(D)`
are the elements `s X` of degree one of the section ring `⨁ₙ L(nD)` of `D`, so the symmetric
algebra `Sym_k L(D)`, the homogeneous coordinate ring of the projective space `ℙ(L(D))`, maps to
the section ring by a graded `k`-algebra homomorphism. When the section ring is generated in
degree one, that is when `L(nD) = L(D)ⁿ` for every `n`, this homomorphism is surjective, and so
`Proj` of the section ring is a closed subscheme of `ℙ(L(D)) = Proj (Sym_k L(D))`.

So `Proj` of a section ring generated in degree one is a projective scheme over `k`: a closed
subscheme of a projective space of dimension `ℓ(D) - 1`, as `L(D)` is finite-dimensional.

## Main results

* `TauCeti.Divisor.gradedLift_sectionRingGradeOneEquiv_surjective`: if `L(nD) ⊆ L(D)ⁿ` for every
  `n`, then `Sym_k L(D)` maps onto the section ring of `D`.
* `TauCeti.Divisor.isClosedImmersion_map_gradedLift_sectionRingGradeOneEquiv`: under the same
  hypothesis, `Proj` of the section ring of `D` is a closed subscheme of `Proj (Sym_k L(D))`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Exercise II.3.12 and Section IV.3.
-/

public section

open AlgebraicGeometry

namespace TauCeti.Divisor

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F] {D : Divisor k F}

/-- If every function in `L(nD)` is a sum of products of `n` functions in `L(D)`, then the graded
homomorphism `Sym_k L(D) → ⨁ₙ L(nD)` sending `s ∈ L(D)` to `s X` is surjective. -/
theorem gradedLift_sectionRingGradeOneEquiv_surjective
    (hD : ∀ n : ℕ, riemannRochSpace (n • D) ≤ riemannRochSpace D ^ n) :
    Function.Surjective (SymmetricAlgebra.gradedLift k (sectionRingGrade D)
      (sectionRingGradeOneEquiv D).toLinearMap) :=
  SymmetricAlgebra.gradedLift_surjective k _ <| by
    have h : Set.range (fun s ↦ ((sectionRingGradeOneEquiv D).toLinearMap s : sectionRing D)) =
        sectionRingGrade D 1 :=
      ((sectionRingGradeOneEquiv D).surjective.range_comp Subtype.val).trans Subtype.range_coe
    rw [h]
    exact adjoin_sectionRingGrade_one_eq_top_iff.mpr hD

/-- **`Proj` of a section ring generated in degree one is a closed subscheme of a projective
space.** If every function in `L(nD)` is a sum of products of `n` functions in `L(D)`, then the
morphism `Proj (⨁ₙ L(nD)) ⟶ Proj (Sym_k L(D))` induced by `s ↦ s X` is a closed immersion. -/
theorem isClosedImmersion_map_gradedLift_sectionRingGradeOneEquiv
    (hD : ∀ n : ℕ, riemannRochSpace (n • D) ≤ riemannRochSpace D ^ n) :
    IsClosedImmersion (Proj.map (SymmetricAlgebra.gradedLift k (sectionRingGrade D)
        (sectionRingGradeOneEquiv D).toLinearMap)
      (HomogeneousIdeal.irrelevant_le_map_of_surjective _
        (gradedLift_sectionRingGradeOneEquiv_surjective hD))) :=
  Proj.isClosedImmersion_map _ _ (gradedLift_sectionRingGradeOneEquiv_surjective hD)

end TauCeti.Divisor

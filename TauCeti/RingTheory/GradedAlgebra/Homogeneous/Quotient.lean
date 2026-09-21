/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import TauCeti.RingTheory.GradedAlgebra.Quotient

/-!
# The grading induced on a quotient by a homogeneous ideal

A homogeneous two-sided ideal `I` in an `R`-algebra `A` graded by `𝒜` descends that grading to
`A ⧸ I`. Its degree-`i` piece is `TauCeti.GradedAlgebra.quotientPiece 𝒜 I i`, the image of `𝒜 i`
under the quotient map. The scalar base `R` can be a commutative semiring.

The graded pieces are submodules of the quotient itself. Homogeneity lets the additive degree
projections descend to the quotient, where they recover each coordinate of a finite sum. Thus the
pieces form an internal direct sum, giving `TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece`.
This structure is a definition rather than a global instance: callers choose the grading locally
with `letI`.

The construction follows Antoine Chambert-Loir's
[Mathlib PR #36501](https://github.com/leanprover-community/mathlib4/pull/36501): the degree-`i`
piece as the image of `𝒜 i` under the quotient map, separation of the pieces via
`GradedRing.proj`, and the induced `GradedAlgebra` assembled from `DirectSum.IsInternal`.

## References

Assem--Simson--Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti.GradedAlgebra

open scoped DirectSum

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Ring A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (I : Ideal A) [I.IsTwoSided]

/-- The quotient by a homogeneous ideal is the internal direct sum of its descended pieces. -/
theorem isInternal_quotientPiece (hI : I.IsHomogeneous 𝒜) :
    DirectSum.IsInternal (quotientPiece 𝒜 I) := by
  -- Homogeneity lets each additive projection descend to the quotient.
  let p (i : ι) : A ⧸ I →+ A ⧸ I :=
    QuotientAddGroup.map I.toAddSubgroup I.toAddSubgroup (GradedRing.proj 𝒜 i)
      (fun x hx => hI.mem_iff.mp hx i)
  have hp_mk (i : ι) (a : A) :
      p i (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (GradedRing.proj 𝒜 i a) :=
    QuotientAddGroup.map_mk I.toAddSubgroup I.toAddSubgroup (GradedRing.proj 𝒜 i) _ a
  have hp (i j : ι) (x : quotientPiece 𝒜 I j) :
      p i x = if i = j then (x : A ⧸ I) else 0 := by
    obtain ⟨a, ha, hqa⟩ := (mem_quotientPiece_iff 𝒜 I).mp x.property
    rw [← hqa, hp_mk, GradedRing.proj_apply, DirectSum.decompose_of_mem 𝒜 ha]
    split_ifs with hij
    · subst j
      simp
    · simp [DirectSum.of_eq_of_ne _ _ _ hij]
  -- These descended projections recover every coordinate of the direct sum.
  have hleft (x : ⨁ i, quotientPiece 𝒜 I i) (i : ι) :
      p i (DirectSum.coeAddMonoidHom (quotientPiece 𝒜 I) x) = (x i : A ⧸ I) := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j x =>
      rw [DirectSum.coeAddMonoidHom_of, hp]
      split_ifs with hij
      · subst j
        simp
      · simp [DirectSum.of_eq_of_ne _ _ _ hij]
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  constructor
  · intro x y hxy
    ext i
    rw [← hleft x i, ← hleft y i, hxy]
  · exact (LinearMap.range_eq_top).mp (DirectSum.range_coeLinearMap.trans
      (iSup_quotientPiece_eq_top 𝒜 I (DirectSum.Decomposition.isInternal 𝒜).submodule_iSup_eq_top))

/-- The images of the graded pieces are independent modulo a homogeneous ideal. -/
theorem iSupIndep_quotientPiece (hI : I.IsHomogeneous 𝒜) : iSupIndep (quotientPiece 𝒜 I) :=
  (isInternal_quotientPiece 𝒜 I hI).submodule_iSupIndep

/-- The induced grading on the quotient by a homogeneous ideal. This is a definition rather than
an instance so that callers choose when to introduce the grading. -/
@[instance_reducible]
noncomputable def gradedAlgebraQuotientPiece (hI : I.IsHomogeneous 𝒜) :
    GradedAlgebra (quotientPiece 𝒜 I) :=
  DirectSum.IsInternal.gradedAlgebra (isInternal_quotientPiece 𝒜 I hI)

end TauCeti.GradedAlgebra

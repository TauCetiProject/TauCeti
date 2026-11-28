/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Grassmannian.StableLocus
public import TauCeti.RingTheory.Spectrum.Prime.LocallyConstant
public import TauCeti.RingTheory.Spectrum.Prime.Rank.Surjective

/-!
# Quotient Grassmannian points on the clopen rank factors

For a submodule with finite projective quotient, the clopen rank fibres cut out coefficient
rings over which scalar extension gives native constant-rank Grassmannian points. Stability
under an endomorphism is preserved. A bound on the quotient stalk ranks makes the finitely
many rank factors reconstruct the coefficient ring as a product.

These points supply the affine pieces of the classifying morphism to the finite coproduct of
stable Grassmannians, including for nonreduced coefficient algebras.

## References

* The Stacks Project, Tags 00EE and 089R, for clopen decompositions and quotient Grassmannians.
-/

public section

universe u v w

open TensorProduct PrimeSpectrum Module.Grassmannian
open scoped Module.Grassmannian

attribute [local instance] Module.finitePresentation_of_projective

namespace Submodule

variable {R : Type u} {M : Type v} {A : Type w} [CommRing R] [AddCommGroup M] [Module R M]
  [CommRing A] [Algebra R A]

section RankFactors

variable {P : Type*} [AddCommGroup P] [Module A P]
  (N : Submodule A P) [Module.Finite A (P ⧸ N)] [Module.Projective A (P ⧸ N)]

/-- The coefficient ring of the clopen locus where the quotient by `N` has rank `r`. -/
noncomputable abbrev quotientRankRing (r : ℕ) : Type w :=
  LocallyConstant.fiberRing
    ⟨_, Module.isLocallyConstant_rankAtStalk (R := A) (M := P ⧸ N)⟩ r

/-- Scalar extension of the quotient to its rank-`r` factor has constant stalk rank `r`. -/
@[simp]
theorem rankAtStalk_quotientRankRing_tensor_quotient (r : ℕ)
    (p : PrimeSpectrum (quotientRankRing N r)) :
    Module.rankAtStalk (quotientRankRing N r ⊗[A] (P ⧸ N)) p = r := by
  rw [Module.rankAtStalk_baseChange]
  exact (Set.ext_iff.mp (LocallyConstant.range_comap_fiberRing
    ⟨_, Module.isLocallyConstant_rankAtStalk (R := A) (M := P ⧸ N)⟩ r) _).mp ⟨p, rfl⟩

end RankFactors

section RankPoints

variable (N : Submodule A (A ⊗[R] M)) [Module.Finite A ((A ⊗[R] M) ⧸ N)]
  [Module.Projective A ((A ⊗[R] M) ⧸ N)]

/-- The fixed-rank quotient on the canonical rank-`r` factor. Its kernel is the scalar
extension of `N`, defined using the native quotient map `baseChangeMkQ`. -/
noncomputable def quotientRankPoint (r : ℕ) :
    G(r, quotientRankRing N r ⊗[R] M; quotientRankRing N r) :=
  ofSurjective (baseChangeMkQ (quotientRankRing N r) N)
    (baseChangeMkQ_surjective N) (rankAtStalk_quotientRankRing_tensor_quotient N r)

/-- The kernel on a rank factor is the kernel of the scalar-extended quotient map. -/
@[simp]
theorem quotientRankPoint_toSubmodule (r : ℕ) :
    (quotientRankPoint N r).toSubmodule =
      (baseChangeMkQ (quotientRankRing N r) N).ker :=
  toSubmodule_ofSurjective _ _ _

/-- A stable kernel remains stable on each of its quotient-rank factors. -/
theorem quotientRankPoint_mem_invtSubmodule {t : Module.End R M}
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A)) (r : ℕ) :
    (quotientRankPoint N r).toSubmodule ∈
      Module.End.invtSubmodule (t.baseChange (quotientRankRing N r)) := by
  rw [quotientRankPoint_toSubmodule]
  exact invtSubmodule_ker_baseChangeMkQ hN

end RankPoints

section BoundedRank

variable [Module.Finite R M] (N : Submodule A (A ⊗[R] M))
  [Module.Projective A ((A ⊗[R] M) ⧸ N)] [Module.Flat R M]

omit [Module.Projective A ((A ⊗[R] M) ⧸ N)] in
/-- Quotients of scalar extensions of a finite flat module have stalk rank bounded by any
bound on the ambient stalk ranks, even when the quotient is not flat. -/
theorem rankAtStalk_quotient_tensorProduct_le {d : ℕ}
    (hd : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p ≤ d) (p : PrimeSpectrum A) :
    Module.rankAtStalk ((A ⊗[R] M) ⧸ N) p ≤ d := by
  have h := N.mkQ.rankAtStalk_le_of_surjective N.mkQ_surjective p
  rw [Module.rankAtStalk_baseChange] at h
  exact h.trans (hd _)

end BoundedRank

end Submodule

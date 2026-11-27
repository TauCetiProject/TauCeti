/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Grassmannian.StableLocus
public import TauCeti.RingTheory.Spectrum.Prime.LocallyConstant

/-!
# Quotient Grassmannian points on the clopen rank factors

For a submodule with finite projective quotient, the clopen rank fibres cut out coefficient
rings over which scalar extension gives native constant-rank Grassmannian points. Stability
under an endomorphism is preserved. For a finite flat ambient module of bounded stalk rank,
the finitely many rank factors reconstruct the coefficient ring as a product.

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

variable (N : Submodule A (A ⊗[R] M)) [Module.Finite A ((A ⊗[R] M) ⧸ N)]
  [Module.Projective A ((A ⊗[R] M) ⧸ N)]

/-- The coefficient ring of the clopen locus where the quotient by `N` has rank `r`. -/
noncomputable abbrev quotientRankRing (r : ℕ) : Type w :=
  A ⧸ Ideal.span {(1 - fiberIdempotent
    (Module.isLocallyConstant_rankAtStalk (R := A) (M := (A ⊗[R] M) ⧸ N)) r)}

/-- The fixed-rank quotient on the canonical rank-`r` factor. Its kernel is the scalar
extension of `N`, defined using the native quotient map `baseChangeMkQ`. -/
noncomputable def quotientRankPoint (r : ℕ) :
    G(r, quotientRankRing N r ⊗[R] M; quotientRankRing N r) :=
  ofSurjective (baseChangeMkQ (quotientRankRing N r) N)
    (baseChangeMkQ_surjective N) fun p ↦ by
      let e := fiberIdempotent
        (Module.isLocallyConstant_rankAtStalk (R := A) (M := (A ⊗[R] M) ⧸ N)) r
      have he : algebraMap A (quotientRankRing N r) e = 1 := by
        apply Ideal.Quotient.eq.2
        simpa only [neg_sub] using
          (Ideal.span {1 - e}).neg_mem (Ideal.subset_span (Set.mem_singleton (1 - e)))
      have hne : e ∉ (p.comap (algebraMap A (quotientRankRing N r))).asIdeal := by
        simpa only [comap_asIdeal, Ideal.mem_comap, he] using p.isPrime.one_notMem
      rw [Module.rankAtStalk_baseChange]
      exact not_ne_iff.1 (mt (fiberIdempotent_mem_iff
        (Module.isLocallyConstant_rankAtStalk (R := A) (M := (A ⊗[R] M) ⧸ N))).2 hne)

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

end RankFactors

section BoundedRank

variable [Module.Finite R M] (N : Submodule A (A ⊗[R] M))
  [Module.Projective A ((A ⊗[R] M) ⧸ N)] [Module.Flat R M]

omit [Module.Projective A ((A ⊗[R] M) ⧸ N)] in
/-- Quotients of scalar extensions of a finite flat module have stalk rank bounded by any
bound on the ambient stalk ranks, even when the quotient is not flat. -/
theorem rankAtStalk_quotient_tensorProduct_le {d : ℕ}
    (hd : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p ≤ d) (p : PrimeSpectrum A) :
    Module.rankAtStalk ((A ⊗[R] M) ⧸ N) p ≤ d := by
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := N.mkQ.baseChange (Localization.AtPrime p.asIdeal))
    (LinearMap.lTensor_surjective _ N.mkQ_surjective)
  rw [← Module.rankAtStalk_eq_finrank_tensorProduct, ← Module.rankAtStalk_eq_finrank_tensorProduct,
    Module.rankAtStalk_baseChange] at h
  exact h.trans (hd _)

/-- The finite family of quotient-rank factors reconstructs the coefficient ring. -/
theorem bijective_pi_quotientRankRing {d : ℕ}
    (hd : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p ≤ d) :
    Function.Bijective (RingHom.pi fun r : ULift.{w} (Fin (d + 1)) ↦
      algebraMap A (quotientRankRing N r.down)) := by
  classical
  have hc := completeOrthogonalIdempotents_fiberIdempotent
    (Module.isLocallyConstant_rankAtStalk (R := A) (M := (A ⊗[R] M) ⧸ N))
    (s := Finset.range (d + 1)) (by
      rintro _ ⟨p, rfl⟩
      exact Finset.mem_range.2 (Nat.lt_succ_of_le (rankAtStalk_quotient_tensorProduct_le N hd p)))
  let e : Fin (d + 1) ≃ ↥(Finset.range (d + 1)) :=
    { toFun := fun r ↦ ⟨r, Finset.mem_range.2 r.isLt⟩
      invFun := fun r ↦ ⟨r, Finset.mem_range.1 r.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hc' := (CompleteOrthogonalIdempotents.equiv (Equiv.ulift.trans e)).2 hc
  exact hc'.bijective_pi

end BoundedRank

end Submodule

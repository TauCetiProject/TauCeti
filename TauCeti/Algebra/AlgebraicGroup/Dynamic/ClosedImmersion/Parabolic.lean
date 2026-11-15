/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.ClosedImmersion.Basic
import TauCeti.Algebra.Polynomial.Laurent.Polynomial

/-!
# Dynamic parabolics under closed immersions

A closed immersion identifies the dynamic parabolic and dynamic unipotent subgroup of a
cocharacter with the inverse images of the corresponding ambient subgroups. These identities
hold on points over every commutative value algebra, including nonreduced algebras. Thus a
faithful matrix representation can be used to compute these subgroups scheme-theoretically.

The dynamic limit commutes with every homomorphism of affine groups. For a closed immersion,
the polynomial extension of an ambient conjugation family factors through the closed subgroup:
its defining equations vanish after passage to Laurent polynomials, hence already vanish as
polynomials. The factorization uses the negative-coefficient extension criterion from
`TauCeti.Algebra.Polynomial.Laurent.Polynomial`.

This extends the Levi compatibility in `Dynamic.ClosedImmersion.Basic`. No smoothness,
reductivity, finite-type, or field hypothesis is needed.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.
-/

public section

open WithConv TauCeti.Cocharacter

namespace BialgHom

variable {R H K A : Type*} [CommSemiring R] [Semiring H] [Semiring K]
variable [HopfAlgebra R H] [HopfAlgebra R K] [CommSemiring A] [Algebra R A]

/-- A group homomorphism carries the dynamic parabolic into the induced dynamic parabolic. -/
theorem mapDomain_mem_parabolic (φ : H →ₐc[R] K)
    (l : K →ₐc[R] LaurentPolynomial R) {g : WithConv (K →ₐ[R] A)}
    (hg : g ∈ parabolic A l) : BialgHom.mapDomain φ g ∈ parabolic A (l.comp φ) := by
  obtain ⟨F, hF⟩ := mem_parabolic_iff.mp hg
  exact mem_parabolic_of_eq (F := BialgHom.mapDomain φ F) (by
    rw [← mapDomain_ofPolyPoint, hF, mapDomain_conjugate])

/-- The polynomial extension of the conjugation family commutes with a group homomorphism. -/
theorem mapDomain_extend (φ : H →ₐc[R] K)
    (l : K →ₐc[R] LaurentPolynomial R) (g : parabolic A l) :
    BialgHom.mapDomain φ (extend A l g) =
      extend A (l.comp φ) ⟨BialgHom.mapDomain φ g.1, mapDomain_mem_parabolic φ l g.2⟩ := by
  apply Eq.symm
  apply extend_unique
  rw [← mapDomain_ofPolyPoint, ofPolyPoint_extend, mapDomain_conjugate]

/-- The dynamic limit commutes with every homomorphism of affine groups. -/
theorem mapDomain_limit (φ : H →ₐc[R] K)
    (l : K →ₐc[R] LaurentPolynomial R) (g : parabolic A l) :
    BialgHom.mapDomain φ (limit A l g) =
      limit A (l.comp φ) ⟨BialgHom.mapDomain φ g.1, mapDomain_mem_parabolic φ l g.2⟩ := by
  rw [limit_apply, mapDomain_evalZeroPoint, mapDomain_extend, limit_apply]

/-- A group homomorphism carries the dynamic unipotent subgroup into its induced counterpart. -/
theorem mapDomain_mem_unipotent (φ : H →ₐc[R] K)
    (l : K →ₐc[R] LaurentPolynomial R) {g : WithConv (K →ₐ[R] A)}
    (hg : g ∈ unipotent A l) : BialgHom.mapDomain φ g ∈ unipotent A (l.comp φ) := by
  obtain ⟨hgP, hg1⟩ := mem_unipotent_iff.mp hg
  refine mem_unipotent_iff.mpr ⟨mapDomain_mem_parabolic φ l hgP, ?_⟩
  rw [← mapDomain_limit φ l ⟨g, hgP⟩, hg1, map_one]

/-- A closed immersion detects dynamic parabolic membership over every commutative value
algebra. The extending conjugation family factors through the closed subgroup. -/
theorem mem_parabolic_iff_of_surjective (φ : H →ₐc[R] K) (hφ : Function.Surjective φ)
    (l : K →ₐc[R] LaurentPolynomial R) (g : WithConv (K →ₐ[R] A)) :
    g ∈ parabolic A l ↔ BialgHom.mapDomain φ g ∈ parabolic A (l.comp φ) := by
  refine ⟨mapDomain_mem_parabolic φ l, fun hg ↦ ?_⟩
  obtain ⟨F, hF⟩ := mem_parabolic_iff.mp hg
  have hvalue (x : H) : Polynomial.toLaurent (F.ofConv x) =
      (conjugate A l g).ofConv (φ x) := by
    have hv := congrArg (fun p : WithConv (H →ₐ[R] LaurentPolynomial A) ↦ p.ofConv x) hF
    rw [← mapDomain_conjugate] at hv
    simpa only [ofPolyPoint_apply, ofConv_toConv, AlgHom.comp_apply,
      AlgHom.restrictScalars_apply, Polynomial.toLaurentAlg_apply,
      BialgHom.mapDomain_apply_apply] using hv
  have hcoeff (y : K) (n : ℤ) (hn : n < 0) :
      ((conjugate A l g).ofConv y).coeff n = 0 := by
    obtain ⟨x, rfl⟩ := hφ y
    rw [← hvalue x]
    exact TauCeti.exists_toLaurent_eq_iff.mp ⟨F.ofConv x, rfl⟩ n hn
  exact mem_parabolic_iff_forall_coeff_conjugate_eq_zero.mpr hcoeff

/-- The dynamic parabolic of a closed subgroup is its intersection with the ambient dynamic
parabolic, as a subgroup functor on all commutative value algebras. -/
theorem parabolic_eq_comap_of_surjective (φ : H →ₐc[R] K) (hφ : Function.Surjective φ)
    (l : K →ₐc[R] LaurentPolynomial R) :
    parabolic A l = (parabolic A (l.comp φ)).comap (BialgHom.mapDomain φ) := by
  ext g
  exact mem_parabolic_iff_of_surjective φ hφ l g

/-- A closed immersion detects dynamic unipotent membership, including over nonreduced
value algebras. -/
theorem mem_unipotent_iff_of_surjective (φ : H →ₐc[R] K) (hφ : Function.Surjective φ)
    (l : K →ₐc[R] LaurentPolynomial R) (g : WithConv (K →ₐ[R] A)) :
    g ∈ unipotent A l ↔ BialgHom.mapDomain φ g ∈ unipotent A (l.comp φ) := by
  refine ⟨mapDomain_mem_unipotent φ l, fun hg ↦ ?_⟩
  obtain ⟨hgP, hg1⟩ := mem_unipotent_iff.mp hg
  have hgK := (mem_parabolic_iff_of_surjective φ hφ l g).mpr hgP
  refine mem_unipotent_iff.mpr ⟨hgK, ?_⟩
  apply BialgHom.mapDomain_injective_of_surjective φ hφ
  rw [mapDomain_limit, map_one]
  exact hg1

/-- The dynamic unipotent subgroup of a closed subgroup is its intersection with the ambient
dynamic unipotent subgroup, on every commutative value algebra. -/
theorem unipotent_eq_comap_of_surjective (φ : H →ₐc[R] K) (hφ : Function.Surjective φ)
    (l : K →ₐc[R] LaurentPolynomial R) :
    unipotent A l = (unipotent A (l.comp φ)).comap (BialgHom.mapDomain φ) := by
  ext g
  exact mem_unipotent_iff_of_surjective φ hφ l g

end BialgHom

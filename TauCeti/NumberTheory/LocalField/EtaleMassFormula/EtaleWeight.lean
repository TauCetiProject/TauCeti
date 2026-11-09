/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.OrbitWeight
public import TauCeti.FieldTheory.Normal.Embeddings
import TauCeti.Algebra.Algebra.Pi

/-!
# Discriminant weights of étale algebras

The discriminant weight of a `K`-algebra is the orbit weight of its embeddings into
`SeparableClosure K`, with the Galois group acting by postcomposition. For a finite étale
algebra, its orbits correspond to its field factors. Accordingly, the weight of a finite
product of finite subextensions is the sum of their discriminant exponents.

`TauCeti.etaleDiscriminantExponent` is defined for arbitrary algebras, using the same
finite-support and infinite-extension conventions as `TauCeti.orbitDiscriminantExponent`.
It is invariant under algebra isomorphism. On a subextension of the separable closure it
agrees with `IntermediateField.discriminantExponent`, including its infinite-extension junk
value. The empty product has weight zero, as does the base field.

The action itself is the existing `AlgEquiv.mulActionAlgHom`; no new action is installed.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The discriminant weight of an algebra is the orbit discriminant weight of its maps into
the separable closure, acted on by postcomposition. -/
def etaleDiscriminantExponent (A : Type*) [Semiring A] [Algebra K A] : ℕ :=
  orbitDiscriminantExponent K (A →ₐ[K] SeparableClosure K)

/-- The étale discriminant weight is computed on the Galois action on algebra maps. -/
theorem etaleDiscriminantExponent_def (A : Type*) [Semiring A] [Algebra K A] :
    etaleDiscriminantExponent K A =
      orbitDiscriminantExponent K (A →ₐ[K] SeparableClosure K) :=
  (rfl)

/-- Isomorphic algebras have the same discriminant weight. -/
theorem etaleDiscriminantExponent_eq_of_algEquiv {A B : Type*}
    [Semiring A] [Algebra K A] [Semiring B] [Algebra K B] (e : A ≃ₐ[K] B) :
    etaleDiscriminantExponent K A = etaleDiscriminantExponent K B := by
  apply orbitDiscriminantExponent_eq_of_equiv K
    (e.arrowCongr (AlgEquiv.refl : SeparableClosure K ≃ₐ[K] SeparableClosure K))
  intro σ φ
  ext a
  -- Unfolding arrowCongr, AlgHom.comp and the postcomposition action, both sides are
  -- σ (φ (e.symm a)).
  rfl

/-- On a subextension, the embedding action recovers its discriminant exponent. This also
holds for infinite subextensions, whose discriminant exponent is totalized to zero. -/
@[simp]
theorem etaleDiscriminantExponent_intermediateField
    (L : IntermediateField K (SeparableClosure K)) :
    etaleDiscriminantExponent K L = L.discriminantExponent := by
  rw [etaleDiscriminantExponent_def,
    orbitDiscriminantExponent_of_isPretransitive K L.val,
    FieldTheory.stabilizer_algHom_eq_fixingSubgroup, IntermediateField.fieldRange_val,
    InfiniteGalois.fixedField_fixingSubgroup]

/-- A finite product of subextensions has the sum of their discriminant exponents.
For finite subextensions this is the discriminant weight of their finite étale product;
the empty product is allowed. -/
@[simp]
theorem etaleDiscriminantExponent_pi {ι : Type*} [Fintype ι]
    (L : ι → IntermediateField K (SeparableClosure K)) :
    etaleDiscriminantExponent K (Π i, L i) = ∑ i, (L i).discriminantExponent := by
  have (i : ι) : Finite (MulAction.orbitRel.Quotient
      Gal(SeparableClosure K/K) (L i →ₐ[K] SeparableClosure K)) := by
    have := (MulAction.pretransitive_iff_subsingleton_quotient
      Gal(SeparableClosure K/K) (L i →ₐ[K] SeparableClosure K)).mp inferInstance
    exact Finite.of_subsingleton
  rw [etaleDiscriminantExponent_def,
    ← orbitDiscriminantExponent_eq_of_equiv K
      (AlgHom.sigmaEquivPi (fun i ↦ L i) (SeparableClosure K)) (by
        intro σ φ
        rcases φ with ⟨i, φ⟩
        ext a
        simp), orbitDiscriminantExponent_sigma]
  exact Finset.sum_congr rfl fun i _ ↦ etaleDiscriminantExponent_intermediateField K (L i)

/-- The base field has discriminant weight zero. -/
@[simp]
theorem etaleDiscriminantExponent_self : etaleDiscriminantExponent K K = 0 := by
  exact orbitDiscriminantExponent_of_subsingleton K

end TauCeti

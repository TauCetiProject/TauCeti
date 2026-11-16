/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet.Etale
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.EtaleWeight
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Relabelling
import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.RingTheory.Etale.Splitting

/-!
# The étale mass as a sum over étale algebras

For a nonarchimedean local field `K` with residue field of cardinality `q`, Bhargava's mass of
étale `K`-algebras of degree `n` is `∑_[A] 1 / (#Aut_K(A) · q ^ v(Disc A))`, summed over the
isomorphism classes. This file identifies it with the étale mass `TauCeti.etaleMass K n`, defined
as `1 / n!` times a sum over labelled Galois sets of size `n`
(`TauCeti.tsum_etaleDiscriminantExponent`).

The labelled Galois set of an étale algebra `A` has the discriminant weight of `A`
(`TauCeti.GaloisSet.discriminantExponent_ofAlgebra`). The relabelling orbits of labelled Galois
sets are the isomorphism classes of étale algebras, and the stabilizer of the Galois set of `A` has
`#Aut_K(A)` elements (`TauCeti.GaloisSet.ofAlgebra_mem_orbit_ofAlgebra_iff`,
`TauCeti.GaloisSet.natCard_stabilizer_ofAlgebra`), so the orbit–stabilizer form of the étale mass
`TauCeti.etaleMass_eq_tsum_orbitRelQuotient` is the sum over isomorphism classes.

The isomorphism classes are given by a family of étale algebras of degree `n` in the universe of
`K`, with exactly one member in each class. In equal characteristic there are infinitely many
classes as soon as `n` is at least the characteristic, so the sum is a `tsum` in `ℝ≥0∞`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, Theorem 1.1 and §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

open ValuativeRel
open scoped ENNReal

namespace TauCeti

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The labelled Galois set of an étale algebra has the discriminant weight of the algebra. -/
@[simp]
theorem GaloisSet.discriminantExponent_ofAlgebra {n : ℕ} (A : Type*) [CommRing A] [Algebra K A]
    [Algebra.Etale K A] (ℓ : Fin n ≃ (A →ₐ[K] SeparableClosure K)) :
    (GaloisSet.ofAlgebra A ℓ).discriminantExponent = etaleDiscriminantExponent K A := by
  let := (GaloisSet.ofAlgebra A ℓ).mulAction
  rw [GaloisSet.discriminantExponent_def, etaleDiscriminantExponent_def]
  exact orbitDiscriminantExponent_eq_of_equiv K ℓ fun σ i ↦ by simp

variable (K) in
/-- **Bhargava's mass of étale algebras is the étale mass.** For a family `A` of étale
`K`-algebras of degree `n` containing exactly one member of each `K`-isomorphism class of étale
algebras of degree `n`, `∑ 1 / (#Aut_K(A i) · q ^ d(A i)) = M_n(K)`, where `q` is the residue
cardinality and `d` the discriminant weight. -/
theorem tsum_etaleDiscriminantExponent (n : ℕ) {ι : Type*} (A : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, Algebra.Etale K (A i)]
    (hdeg : ∀ i, Module.finrank K (A i) = n)
    (hinj : ∀ i j, Nonempty (A i ≃ₐ[K] A j) → i = j)
    (hsurj : ∀ (B : Type u) [CommRing B] [Algebra K B] [Algebra.Etale K B],
      Module.finrank K B = n → ∃ i, Nonempty (B ≃ₐ[K] A i)) :
    ∑' i, 1 / ((Nat.card (A i ≃ₐ[K] A i) : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ etaleDiscriminantExponent K (A i)) =
      etaleMass K n := by
  -- Label the `n` points of each `A i`, and send `i` to the orbit of the resulting Galois set.
  have hℓ (i : ι) : Nonempty (Fin n ≃ (A i →ₐ[K] SeparableClosure K)) := by
    have : Module.Finite K (A i) := Algebra.FormallyUnramified.finite_of_free K (A i)
    exact ⟨(Finite.equivFinOfCardEq
      ((Algebra.Etale.card_algHom_eq_finrank K (A i) _).trans (hdeg i))).symm⟩
  let ℓ (i : ι) := (hℓ i).some
  let Φ (i : ι) : MulAction.orbitRel.Quotient (Equiv.Perm (Fin n)) (GaloisSet K n) :=
    Quotient.mk'' (GaloisSet.ofAlgebra (A i) (ℓ i))
  have hΦ : Function.Bijective Φ := by
    refine ⟨fun i j h ↦ (hinj j i ((GaloisSet.ofAlgebra_mem_orbit_ofAlgebra_iff _ _).1
      (Quotient.exact' h))).symm, fun ω ↦ ?_⟩
    obtain ⟨B, _, _, _, ℓB, hB⟩ := GaloisSet.exists_eq_ofAlgebra ω.out
    have hBdeg : Module.finrank K B = n := by
      rw [← Algebra.Etale.card_algHom_eq_finrank K B (SeparableClosure K), ← Nat.card_congr ℓB,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    obtain ⟨i, hi⟩ := hsurj B hBdeg
    refine ⟨i, (Quotient.sound' ?_).trans ω.out_eq'⟩
    rw [MulAction.orbitRel_apply, hB]
    exact (GaloisSet.ofAlgebra_mem_orbit_ofAlgebra_iff _ _).2 hi
  rw [etaleMass_eq_tsum_orbitRelQuotient, ← (Equiv.ofBijective Φ hΦ).tsum_eq]
  refine tsum_congr fun i ↦ ?_
  -- The chosen representative of the orbit of `i` is a relabelling of the Galois set of `A i`.
  obtain ⟨e, he⟩ := MulAction.exists_smul_out_eq (rfl : Φ i = Φ i)
  rw [Equiv.ofBijective_apply, eq_inv_smul_iff.2 he, GaloisSet.smul_ofAlgebra,
    GaloisSet.natCard_stabilizer_ofAlgebra, GaloisSet.discriminantExponent_ofAlgebra]

end TauCeti

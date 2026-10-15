/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import TauCeti.RingTheory.KrullDimension.FiniteType
public import TauCeti.RingTheory.KrullDimension.Quotient
import TauCeti.RingTheory.Ideal.MinimalPrime.Finite

/-!
# Dimension of finitely presented algebras over a field

Let `A = k[x₁, …, x_m] ⧸ (f₁, …, f_c)` be a finitely presented algebra over a field `k`. Every
maximal ideal of `k[x₁, …, x_m]` has height `m`, and by Krull's height theorem cutting by the `c`
relations lowers the height by at most `c`. So every maximal ideal of `A` has height at least
`m - c`: each closed point of `Spec A` has local dimension at least the number of generators minus
the number of relations.

If moreover `dim A ≤ m - c`, so that `A` is a global complete intersection over `k`, then every
nonzero localization `A[1/g]` still has dimension `m - c`. Indeed `A` is Jacobson, so some maximal
ideal avoids `g`, and its height is preserved by the localization. This is the algebraic input for
the stability of relative global complete intersections, and hence of standard syntomic algebras,
under localization on the source.

Such an `A` is moreover equidimensional: for every minimal prime `Q`, the quotient `A ⧸ Q` has
dimension `m - c`. Choose `g ∉ Q` lying in every other minimal prime. Then every prime of `A[1/g]`
contains `Q`, so `dim A[1/g] ≤ dim (A ⧸ Q)`, while `A[1/g]` is nonzero and so has dimension `m - c`.

## Main results

* `Algebra.Presentation.dimension_le_height_of_isMaximal`: every maximal ideal of a finitely
  presented algebra over a field has height at least the dimension `m - c` of the presentation.
* `Algebra.Presentation.ringKrullDim_eq_of_isLocalization_away`: if `dim A ≤ m - c`, every nonzero
  localization `A[1/g]` has Krull dimension `m - c`.
* `Algebra.Presentation.ringKrullDim_quotient_of_mem_minimalPrimes` and
  `Algebra.Presentation.isPureDimensional_primeSpectrum`: if `dim A ≤ m - c`, every irreducible
  component of `Spec A` has dimension `m - c`.

## References

* The Stacks Project, Commutative Algebra, Section *Syntomic morphisms*: global complete
  intersections over a field, and the stability of relative global complete intersections under
  localization `S → S_g`.
-/

public section

namespace Algebra.Presentation

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
variable {ι σ : Type*} [Finite ι] [Finite σ] (P : Presentation k A ι σ)

/-- Every maximal ideal of an algebra over a field with a finite presentation by `m` generators and
`c` relations has height at least `m - c`, the dimension of the presentation. -/
theorem dimension_le_height_of_isMaximal (m : Ideal A) [m.IsMaximal] :
    (P.dimension : ℕ∞) ≤ m.height := by
  have hφ := P.algebraMap_surjective
  let φ := algebraMap P.Ring A
  let M := m.comap φ
  have : M.IsMaximal := Ideal.comap_isMaximal_of_surjective φ hφ
  -- The contraction `M` of `m` to `k[x₁, …, x_m]` has height `m`, and cutting by the `c`
  -- relations lowers the height by at most `c` (Krull's height theorem).
  have hM : M.height ≤ (M.map (Ideal.Quotient.mk (RingHom.ker φ))).height + Nat.card σ := by
    have hle : Set.range P.relation ⊆ M := by
      rintro _ ⟨i, rfl⟩
      simp [M, φ, Generators.algebraMap_apply]
    have h := Ideal.height_le_height_add_encard_of_subset _ hle
    rw [P.span_range_relation_eq_ker] at h
    refine h.trans (add_le_add le_rfl ?_)
    rw [← Set.image_univ]
    exact (Set.encard_image_le _ _).trans (by simp [Set.encard_univ, ENat.card_eq_coe_natCard])
  -- The image of `M` in `k[x₁, …, x_m] ⧸ ker φ ≅ A` is `m`.
  have hm : (M.map (Ideal.Quotient.mk (RingHom.ker φ))).height = m.height := by
    let e := RingHom.quotientKerEquivOfSurjective hφ
    have he : (e : _ →+* A).comp (Ideal.Quotient.mk (RingHom.ker φ)) = φ := by
      refine RingHom.ext fun x ↦ ?_
      exact RingHom.quotientKerEquivOfSurjective_apply_mk hφ x
    rw [← e.height_map, ← Ideal.map_coe, Ideal.map_map, he, Ideal.map_comap_of_surjective φ hφ]
  rw [hm, MvPolynomial.height_eq_natCard_of_isMaximal] at hM
  -- Conclude by arithmetic in `ℕ∞`.
  rcases eq_or_ne m.height ⊤ with h | h
  · simp [h]
  · lift m.height to ℕ using h with d
    norm_cast at hM ⊢
    simp only [dimension]
    omega

/-- Let `A` be an algebra over a field with a finite presentation by `m` generators and `c`
relations, such that `dim A ≤ m - c`. Then every nonzero localization `A[1/g]` has Krull dimension
exactly `m - c`. -/
theorem ringKrullDim_eq_of_isLocalization_away (hA : ringKrullDim A ≤ P.dimension) (g : A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization.Away g B] [Nontrivial B] :
    ringKrullDim B = P.dimension := by
  have := P.finitePresentation_of_isFinite
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  refine le_antisymm (le_trans ?_ hA) ?_
  · -- The spectrum of `B` embeds into that of `A`, compatibly with the order.
    have hmono : Monotone (PrimeSpectrum.comap (algebraMap A B)) := fun _ _ h ↦ Ideal.comap_mono h
    exact Order.krullDim_le_of_strictMono _
      (hmono.strictMono_of_injective (PrimeSpectrum.localization_comap_injective B (.powers g)))
  · -- As `B ≠ 0`, the element `g` is not nilpotent; since `A` is Jacobson, some maximal ideal `m`
    -- avoids `g`, and `m B` is a prime of `B` of the same height as `m`.
    have hg : g ∉ (⊥ : Ideal A).jacobson := by
      rw [← Ideal.radical_eq_jacobson]
      rintro ⟨n, hn⟩
      have h := (IsLocalization.Away.algebraMap_isUnit (S := B) g).pow n
      rw [← map_pow, Ideal.mem_bot.mp hn, map_zero, isUnit_zero_iff] at h
      exact zero_ne_one h
    obtain ⟨m, ⟨-, hm⟩, hgm⟩ : ∃ m : Ideal A, (⊥ ≤ m ∧ m.IsMaximal) ∧ g ∉ m := by
      simpa [Ideal.jacobson, Ideal.mem_sInf] using hg
    have hdisj : Disjoint (Submonoid.powers g : Set A) m :=
      (Ideal.disjoint_powers_iff_notMem g hm.isPrime.isRadical).mpr hgm
    have : (m.map (algebraMap A B)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint _ B m hm.isPrime hdisj
    calc (P.dimension : WithBot ℕ∞) ≤ m.height := by
          exact_mod_cast P.dimension_le_height_of_isMaximal m
      _ = (m.map (algebraMap A B)).height := by
        rw [IsLocalization.height_map_of_disjoint (.powers g) m hdisj]
      _ ≤ ringKrullDim B := Ideal.height_le_ringKrullDim_of_isPrime

/-- Let `A` be an algebra over a field with a finite presentation by `m` generators and `c`
relations, such that `dim A ≤ m - c`. Then for every minimal prime `Q` of `A`, the quotient `A ⧸ Q`
has Krull dimension exactly `m - c`. -/
theorem ringKrullDim_quotient_of_mem_minimalPrimes (hA : ringKrullDim A ≤ P.dimension)
    {Q : Ideal A} (hQ : Q ∈ minimalPrimes A) : ringKrullDim (A ⧸ Q) = P.dimension := by
  have := P.finitePresentation_of_isFinite
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hQp : Q.IsPrime := hQ.1.1
  refine le_antisymm ((ringKrullDim_quotient_le Q).trans hA) ?_
  -- Some `g ∉ Q` lies in every other minimal prime, so every prime of `A[1/g]` contains `Q`.
  obtain ⟨g, hgQ, hg⟩ := (⊥ : Ideal A).exists_notMem_forall_le_of_mem_minimalPrimes
    (minimalPrimes.finite_of_isNoetherianRing A) hQ
  let B := Localization.Away g
  have hdisj : Disjoint (Submonoid.powers g : Set A) Q :=
    (Ideal.disjoint_powers_iff_notMem g hQp.isRadical).mpr hgQ
  have hQB : (Q.map (algebraMap A B)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ B Q hQp hdisj
  have : Nontrivial B := by
    obtain _ | _ := subsingleton_or_nontrivial B
    · exact absurd (Subsingleton.elim _ _) hQB.ne_top
    · assumption
  rw [← P.ringKrullDim_eq_of_isLocalization_away hA g B, ringKrullDim_quotient]
  -- Contracting primes of `A[1/g]` is a strictly monotone map into `V(Q)`.
  have hmono : Monotone (PrimeSpectrum.comap (algebraMap A B)) := fun _ _ h ↦ Ideal.comap_mono h
  refine Order.krullDim_le_of_strictMono
    (fun q ↦ ⟨PrimeSpectrum.comap (algebraMap A B) q, hg _ inferInstance bot_le fun h ↦ ?_⟩)
    fun _ _ h ↦ hmono.strictMono_of_injective
      (PrimeSpectrum.localization_comap_injective B (.powers g)) h
  -- The image of `g` is a unit of `A[1/g]`, so it lies in no prime.
  exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit g))

/-- Let `A` be an algebra over a field with a finite presentation by `m` generators and `c`
relations, such that `dim A ≤ m - c`. Then `Spec A` is pure-dimensional of dimension `m - c`. -/
theorem isPureDimensional_primeSpectrum (hA : ringKrullDim A ≤ P.dimension) :
    TauCeti.IsPureDimensional P.dimension (PrimeSpectrum A) :=
  TauCeti.isPureDimensional_primeSpectrum_iff.mpr fun _ hQ ↦
    P.ringKrullDim_quotient_of_mem_minimalPrimes hA hQ

end Algebra.Presentation

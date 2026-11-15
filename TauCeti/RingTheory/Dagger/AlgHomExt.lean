/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.MaximalSpectrum
public import TauCeti.RingTheory.Dagger.NoetherNormalization

import TauCeti.RingTheory.Affinoid.FiniteQuotient
import TauCeti.RingTheory.Ideal.KrullIntersection
import TauCeti.RingTheory.Ideal.Quotient.Radical

/-!
# Uniqueness of algebra homomorphisms out of Monsky–Washnitzer algebras

Let `K` be a complete ultrametric normed field and `W = K⟨X₁, …, Xₙ⟩†` the Monsky–Washnitzer
algebra in finitely many variables. Any two `K`-algebra homomorphisms from `W` into a noetherian
commutative `K`-algebra `B` with `K`-finite residue fields at all maximal ideals are equal as soon
as they agree on every coordinate `Xᵢ`. No topology or continuity hypothesis on `B`, no
reducedness assumption, and no nontriviality of the valuation of `K` enters.

For each maximal ideal `m` of `B` and `n > 0`, the quotient `B ⧸ m ^ n` is finite-dimensional,
hence integral, over `K`. Overconvergent Weierstrass division makes polynomials surject onto
every integral quotient of `W`, so the two homomorphisms agree modulo `m ^ n`
(`TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isIntegral`). Krull intersection over all maximal
ideals (`Ideal.iInf_isMaximal_pow_eq_bot`) then forces equality in `B`. Both dagger algebras and
affinoid algebras satisfy the hypothesis on `B`.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_forall_isMaximal`: `K`-algebra maps from `W`
  into a noetherian `K`-algebra with finite residue fields are determined on the variables.
* `TauCeti.Dagger.IsDaggerAlgebra.algHom_ext_washnitzerAlgebra`: specialization to dagger targets.
* `TauCeti.IsAffinoidAlgebra.algHom_ext_washnitzerAlgebra`: specialization to affinoid targets,
  without choosing a norm or topology on the target.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.5 and Theorem 1.7.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.3.
-/

public section

namespace TauCeti

variable {K σ : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Finite σ]

namespace Dagger.washnitzerAlgebra

/-- **`K`-algebra homomorphisms out of `K⟨X₁, …, Xₙ⟩†` are determined on the variables**, for any
noetherian target whose residue fields at maximal ideals are finite over `K`. No topology or
continuity is assumed. -/
theorem algHom_ext_of_forall_isMaximal {B : Type*} [CommRing B] [Algebra K B] [IsNoetherianRing B]
    (hB : ∀ m : Ideal B, [m.IsMaximal] → Module.Finite K (B ⧸ m))
    {φ ψ : washnitzerAlgebra σ K →ₐ[K] B}
    (h : ∀ i, φ (X σ K i) = ψ (X σ K i)) : φ = ψ := by
  ext f
  suffices φ f - ψ f ∈ (⊥ : Ideal B) from sub_eq_zero.mp (Ideal.mem_bot.mp this)
  rw [← Ideal.iInf_isMaximal_pow_eq_bot]
  simp only [Ideal.mem_iInf]
  intro m hm n hn
  let _ := hm
  have hrad : (m ^ n).radical = m := (Ideal.radical_pow m hn.ne').trans hm.isPrime.radical
  have : Module.Finite K (B ⧸ (m ^ n).radical) := hrad.symm ▸ hB m
  have : Module.Finite K (B ⧸ m ^ n) :=
    (m ^ n).moduleFinite_quotient_of_radical (IsNoetherian.noetherian _)
  let q := Ideal.Quotient.mkₐ K (m ^ n)
  have hq : q.comp φ = q.comp ψ :=
    algHom_ext_of_isIntegral fun i ↦ by simp [q, h i]
  exact Ideal.Quotient.eq.mp (by simpa [q] using AlgHom.congr_fun hq f)

/-- Two `K`-algebra homomorphisms out of a presented algebra `A` into a noetherian `K`-algebra with
finite residue fields are equal if they agree on the images of the variables of a surjective
presentation `W ↠ A`. -/
theorem algHom_ext_of_surjective_of_forall_isMaximal {A B : Type*} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] [IsNoetherianRing B]
    (hB : ∀ m : Ideal B, [m.IsMaximal] → Module.Finite K (B ⧸ m))
    {π : washnitzerAlgebra σ K →ₐ[K] A} (hπ : Function.Surjective π) {φ ψ : A →ₐ[K] B}
    (h : ∀ i, φ (π (X σ K i)) = ψ (π (X σ K i))) : φ = ψ := by
  have hcomp : φ.comp π = ψ.comp π := algHom_ext_of_forall_isMaximal hB h
  ext a
  obtain ⟨f, rfl⟩ := hπ a
  exact AlgHom.congr_fun hcomp f

end Dagger.washnitzerAlgebra

namespace Dagger.IsDaggerAlgebra

/-- **`K`-algebra homomorphisms from `K⟨X₁, …, Xₙ⟩†` to a dagger algebra are determined on the
variables.** -/
theorem algHom_ext_washnitzerAlgebra {B : Type*} [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]
    {φ ψ : Dagger.washnitzerAlgebra σ K →ₐ[K] B}
    (h : ∀ i, φ (Dagger.washnitzerAlgebra.X σ K i) = ψ (Dagger.washnitzerAlgebra.X σ K i)) :
    φ = ψ := by
  have := isNoetherianRing (K := K) (A := B)
  exact Dagger.washnitzerAlgebra.algHom_ext_of_forall_isMaximal (finite_quotient_of_isMaximal K) h

/-- Two `K`-algebra homomorphisms into a dagger algebra agree as soon as they agree on the images
of the variables of a surjective presentation `W ↠ A`. -/
theorem algHom_ext_of_surjective {A B : Type*} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] [IsDaggerAlgebra K B] {π : Dagger.washnitzerAlgebra σ K →ₐ[K] A}
    (hπ : Function.Surjective π) {φ ψ : A →ₐ[K] B}
    (h : ∀ i, φ (π (Dagger.washnitzerAlgebra.X σ K i)) =
      ψ (π (Dagger.washnitzerAlgebra.X σ K i))) : φ = ψ := by
  have := isNoetherianRing (K := K) (A := B)
  exact Dagger.washnitzerAlgebra.algHom_ext_of_surjective_of_forall_isMaximal
    (finite_quotient_of_isMaximal K) hπ h

end Dagger.IsDaggerAlgebra

namespace IsAffinoidAlgebra

/-- **`K`-algebra homomorphisms from `K⟨X₁, …, Xₙ⟩†` to an affinoid algebra are determined on the
variables.** No norm or topology on the affinoid algebra is required. -/
theorem algHom_ext_washnitzerAlgebra {B : Type*} [CommRing B] [Algebra K B]
    (hB : IsAffinoidAlgebra K B) {φ ψ : Dagger.washnitzerAlgebra σ K →ₐ[K] B}
    (h : ∀ i, φ (Dagger.washnitzerAlgebra.X σ K i) = ψ (Dagger.washnitzerAlgebra.X σ K i)) :
    φ = ψ := by
  have := hB.isNoetherianRing
  exact Dagger.washnitzerAlgebra.algHom_ext_of_forall_isMaximal hB.finite_quotient_of_isMaximal h

/-- Two `K`-algebra homomorphisms into an affinoid algebra agree as soon as they agree on the
images of the variables of a surjective overconvergent presentation `W ↠ A`. -/
theorem algHom_ext_of_surjective_washnitzerAlgebra {A B : Type*} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] (hB : IsAffinoidAlgebra K B)
    {π : Dagger.washnitzerAlgebra σ K →ₐ[K] A} (hπ : Function.Surjective π) {φ ψ : A →ₐ[K] B}
    (h : ∀ i, φ (π (Dagger.washnitzerAlgebra.X σ K i)) =
      ψ (π (Dagger.washnitzerAlgebra.X σ K i))) : φ = ψ := by
  have := hB.isNoetherianRing
  exact Dagger.washnitzerAlgebra.algHom_ext_of_surjective_of_forall_isMaximal
    hB.finite_quotient_of_isMaximal hπ h

end IsAffinoidAlgebra

end TauCeti

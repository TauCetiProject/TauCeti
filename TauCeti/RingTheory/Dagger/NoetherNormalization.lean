/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Noetherian
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import TauCeti.RingTheory.Ideal.Quotient.Radical

/-!
# Noether normalisation and residue fields of overconvergent algebras

A nonzero algebra finite over a finite-variable Monsky–Washnitzer algebra admits a finite
injective algebra map from another Monsky–Washnitzer algebra, with no more variables.
In particular this applies to every nonzero quotient of an overconvergent algebra, retaining
nilpotents. The residue fields of such an algebra at its maximal ideals are finite over the
coefficient field, as are its quotients by ideals with maximal radical. No characteristic or
nontrivial valuation assumption is needed.

A distinguished relation in the kernel lets one remove a variable while retaining finiteness.
Together with the distinguishing automorphisms, this gives an induction on the number of variables.
This is the algebraic normalisation used to study residue fields and morphisms of dagger algebras.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.exists_finite_injective`: Noether normalisation. A nonzero
  algebra finite over the Monsky–Washnitzer algebra `K⟨X⟩†` in finitely many variables `X` is
  finite over an injectively embedded `K⟨Y_1, …, Y_n⟩†` with `n` at most the number of
  variables `X`.
* `TauCeti.Dagger.washnitzerAlgebra.finite_of_isField`: a field finite over such a `K⟨X⟩†` is
  finite-dimensional over `K`.
* `TauCeti.Dagger.washnitzerAlgebra.finite_quotient_of_isMaximal`: an algebra finite over such a
  `K⟨X⟩†` has residue fields at its maximal ideals finite-dimensional over `K`.
* `TauCeti.Dagger.washnitzerAlgebra.finite_quotient_of_isMaximal_radical`: its quotients by ideals
  with maximal radical are finite-dimensional over `K`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.3(iii), §1.4(2)–(3).
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §6.1.2.

The induction adapts `TauCeti.IsAffinoidAlgebra.exists_finite_injective` in
`TauCeti.RingTheory.Affinoid.NoetherNormalization`. Here division and changes of variables
are performed in the overconvergent algebra itself, without passing to its completion.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries
open washnitzerAlgebra

universe u v w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "W " σ:max => washnitzerAlgebra σ K

/-- A noninjective finite map admits a finite map from the algebra in one fewer variable,
after a change of variables. -/
private theorem exists_finite_map_of_not_injective {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] {π : W (Option σ) →ₐ[K] A}
    (hπ : π.Finite) (hne : ¬ Function.Injective π) :
    ∃ γ : W σ →ₐ[K] A, γ.Finite := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (mt (RingHom.injective_iff_ker_eq_bot (f := π.toRingHom)).mpr hne)
  obtain ⟨α, hα, s, hd, hu⟩ := exists_triangularEquiv_isDistinguished_isUnit f hf0
  let e := triangularEquiv (R := K) α hα
  let ψ := π.comp e.symm.toAlgHom
  have hψ : ψ.Finite := hπ.comp (AlgHom.Finite.of_surjective _ e.symm.surjective)
  have hz : ψ (e f) = 0 := by simpa [ψ] using (RingHom.mem_ker.mp hf)
  exact ⟨ψ.comp (washnitzerAlgebra.optionC (R := K)),
    finite_comp_optionC_of_isDistinguished hd hu hψ hz⟩

omit [CompleteSpace K] in
/-- An injective finite map already gives a normalisation, after indexing the variables by
`Fin`. -/
private theorem exists_finite_injective_of_injective {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] {π : W σ →ₐ[K] A}
    (hπ : π.Finite) (hinj : Function.Injective π) :
    ∃ (n : ℕ) (g : W (Fin n) →ₐ[K] A),
      n ≤ Nat.card σ ∧ Function.Injective g ∧ g.Finite := by
  let := Fintype.ofFinite σ
  let r := washnitzerAlgebra.renameAlgEquiv (R := K) (Fintype.equivFin σ).symm
  exact ⟨_, π.comp r.toAlgHom, by simp [Nat.card_eq_fintype_card],
    hinj.comp r.injective, hπ.comp (AlgHom.Finite.of_surjective _ r.surjective)⟩

/-- **Noether normalisation.** If a nonzero `K`-algebra is finite over a Monsky–Washnitzer
algebra in finitely many variables, it is finite over an injectively embedded Monsky–Washnitzer
algebra with no more variables. In particular a surjective presentation suffices, by
`AlgHom.Finite.of_surjective`. Finiteness uses the algebra structure induced by the
displayed map. -/
theorem washnitzerAlgebra.exists_finite_injective {σ : Type v} [Finite σ]
    {A : Type w} [CommRing A] [Algebra K A] [Nontrivial A]
    {π : W σ →ₐ[K] A} (hπ : π.Finite) :
    ∃ (n : ℕ) (g : W (Fin n) →ₐ[K] A),
      n ≤ Nat.card σ ∧ Function.Injective g ∧ g.Finite := by
  suffices H : ∀ (B : Type w) [CommRing B] [Algebra K B] [Nontrivial B]
      (π : W σ →ₐ[K] B), π.Finite →
      ∃ (n : ℕ) (g : W (Fin n) →ₐ[K] B),
        n ≤ Nat.card σ ∧ Function.Injective g ∧ g.Finite by
    exact H A π hπ
  refine Finite.induction_empty_option
    (P := fun σ ↦ ∀ (A : Type w) [CommRing A] [Algebra K A] [Nontrivial A]
      (π : W σ →ₐ[K] A), π.Finite →
      ∃ (n : ℕ) (g : W (Fin n) →ₐ[K] A),
        n ≤ Nat.card σ ∧ Function.Injective g ∧ g.Finite)
    (fun {α β} e ih A _ _ _ π hπ ↦ ?_) (fun A _ _ _ π hπ ↦ ?_)
    (fun {σ} _ ih A _ _ _ π hπ ↦ ?_) σ
  · let r := washnitzerAlgebra.renameAlgEquiv (R := K) e
    obtain ⟨n, g, hn, hg, hfin⟩ := ih A (π.comp r.toAlgHom)
      (hπ.comp (AlgHom.Finite.of_surjective _ r.surjective))
    exact ⟨n, g, hn.trans_eq (Nat.card_congr e), hg, hfin⟩
  · -- In zero variables the source is the coefficient field, so the map is injective.
    have hinj : Function.Injective π := by
      intro a b hab
      obtain ⟨x, ha⟩ := washnitzerAlgebra.algebraMap_surjective a
      obtain ⟨y, hb⟩ := washnitzerAlgebra.algebraMap_surjective b
      rw [← ha, ← hb, π.commutes, π.commutes] at hab
      rw [← ha, ← hb, (FaithfulSMul.algebraMap_injective K A) hab]
    exact exists_finite_injective_of_injective hπ hinj
  · by_cases h : Function.Injective π
    · exact exists_finite_injective_of_injective hπ h
    · obtain ⟨γ, hγ⟩ := exists_finite_map_of_not_injective hπ h
      obtain ⟨n, g, hn, hg, hfin⟩ := ih A γ hγ
      exact ⟨n, g, hn.trans (by simp), hg, hfin⟩

/-- A field finite over a finite-variable Monsky–Washnitzer algebra is finite-dimensional over
the coefficient field `K`. The field is given as a commutative ring `A` with `IsField A`. -/
theorem washnitzerAlgebra.finite_of_isField {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] {π : W σ →ₐ[K] A}
    (hπ : π.Finite) (hA : IsField A) : Module.Finite K A := by
  have := hA.nontrivial
  obtain ⟨n, g, _, hg, hfin⟩ := washnitzerAlgebra.exists_finite_injective hπ
  let : Algebra (W (Fin n)) A := g.toRingHom.toAlgebra
  have : Module.Finite (W (Fin n)) A := hfin
  have : Algebra.IsIntegral (W (Fin n)) A := Algebra.IsIntegral.of_finite _ _
  have hf : IsField (W (Fin n)) := isField_of_isIntegral_of_isField hg hA
  have hn : n = 0 := by
    by_contra hn
    let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    obtain ⟨y, hy⟩ := hf.mul_inv_cancel (washnitzerAlgebra.X_ne_zero (R := K) i)
    exact washnitzerAlgebra.not_isUnit_X i (IsUnit.of_mul_eq_one y hy)
  subst n
  have : Module.Finite K (W (Fin 0)) :=
    Module.Finite.of_surjective (Algebra.linearMap K (W (Fin 0)))
      washnitzerAlgebra.algebraMap_surjective
  have : IsScalarTower K (W (Fin 0)) A := IsScalarTower.of_algebraMap_eq fun k ↦ (g.commutes k).symm
  exact Module.Finite.trans (W (Fin 0)) A

/-- **Finiteness of residue fields.** Every maximal-ideal quotient of an algebra finite over
a finite-variable Monsky–Washnitzer algebra is finite-dimensional over the coefficient field. -/
theorem washnitzerAlgebra.finite_quotient_of_isMaximal {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] {π : W σ →ₐ[K] A}
    (hπ : π.Finite) (m : Ideal A) [m.IsMaximal] : Module.Finite K (A ⧸ m) := by
  exact finite_of_isField
    ((AlgHom.Finite.of_surjective (Ideal.Quotient.mkₐ K m) Ideal.Quotient.mk_surjective).comp hπ)
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp ‹_›)

/-- If `A` is finite over a finite-variable Monsky–Washnitzer algebra and the radical of `q` is
maximal, then `A ⧸ q` is finite-dimensional over the coefficient field `K`. This covers the
nilpotent thickenings `A ⧸ m ^ n` of a residue field, for `m` maximal and `0 < n`. Such an ideal
`q` is automatically primary, by `Ideal.isPrimary_of_isMaximal_radical`. -/
theorem washnitzerAlgebra.finite_quotient_of_isMaximal_radical {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] {π : W σ →ₐ[K] A}
    (hπ : π.Finite) (q : Ideal A) [q.radical.IsMaximal] : Module.Finite K (A ⧸ q) := by
  let : Algebra (W σ) A := π.toRingHom.toAlgebra
  have : Module.Finite (W σ) A := hπ
  have : IsNoetherianRing A := IsNoetherianRing.of_finite (W σ) A
  have : Module.Finite K (A ⧸ q.radical) := finite_quotient_of_isMaximal hπ q.radical
  exact q.moduleFinite_quotient_of_radical (IsNoetherian.noetherian _)

end TauCeti.Dagger

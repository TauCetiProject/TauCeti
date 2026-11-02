/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WashnitzerAlgebra

/-!
# Dagger algebras

Let `K` be an ultrametric normed field. A `K`-*dagger algebra* is a commutative `K`-algebra `A`
admitting a surjective `K`-algebra homomorphism `W_n ↠ A` from the Monsky–Washnitzer algebra
`W_n = K⟨X₁, …, Xₙ⟩†` of overconvergent power series, equivalently `A ≅ W_n ⧸ I` for an ideal
`I`. Dagger algebras are to Grosse-Klönne's dagger spaces what affinoid algebras are to rigid
spaces. Like `TauCeti.IsAffinoidAlgebra`, the predicate is algebraic: it fixes neither a norm nor
a topology on `A`, and it includes nonreduced algebras and the zero algebra.

Every element `a` of a dagger algebra over a complete field has bounded spectrum in the following
sense: `1 + c • a` is a unit for every sufficiently small scalar `c`. Over a nontrivially normed
field this rules out the polynomial ring `K[X]`, whose element `1 + c • X` is a unit only for
`c = 0`; so a dagger algebra is not merely a finitely generated `K`-algebra.

## Main definitions

* `TauCeti.Dagger.IsDaggerAlgebra K A`: `A` is a quotient of some `W_n`.
* `TauCeti.Dagger.presentationDim K A`: the least number of variables of a presentation
  `W_n ↠ A`, and `TauCeti.Dagger.presentation K A`: a chosen presentation in that many variables.

## Main results

* `TauCeti.Dagger.IsDaggerAlgebra.of_surjective`: surjective images, in particular quotients
  (`TauCeti.Dagger.IsDaggerAlgebra.quotient`), of dagger algebras are dagger algebras.
* `TauCeti.Dagger.isDaggerAlgebra_iff_exists_ideal`: `A` is a dagger algebra iff it is isomorphic
  to `W_n ⧸ I` for some `n` and some ideal `I`.
* `TauCeti.Dagger.IsDaggerAlgebra.of_surjective_washnitzerAlgebra`: a quotient of the
  Monsky–Washnitzer algebra in any finite type of variables is a dagger algebra.
* `TauCeti.Dagger.presentationDim_eq_zero_iff`: a dagger algebra has a presentation in zero
  variables iff it is spanned by the scalars; so `K` has presentation dimension `0` and `W_1` has
  presentation dimension `1`.
* `TauCeti.Dagger.IsDaggerAlgebra.eventually_isUnit_one_add_smul`: in a dagger algebra over a
  complete field, `1 + c • a` is a unit for all `c` near `0`, and
  `TauCeti.Dagger.not_isDaggerAlgebra_polynomial`: over a complete nontrivially normed field,
  `K[X]` is not a dagger algebra.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.2.
-/

public section

namespace TauCeti.Dagger

open Filter Topology _root_.MvPowerSeries

section Defs

variable (K : Type*) [NormedField K] [IsUltrametricDist K] (A : Type*) [CommRing A] [Algebra K A]

/-- A `K`-**dagger algebra** is a commutative `K`-algebra which is a quotient of the
Monsky–Washnitzer algebra `W_n = K⟨X₁, …, Xₙ⟩†` for some `n`. -/
class IsDaggerAlgebra : Prop where
  exists_surjective :
    ∃ (n : ℕ) (φ : washnitzerAlgebra (Fin n) K →ₐ[K] A), Function.Surjective φ

variable {K A}

namespace IsDaggerAlgebra

/-- A surjective image of a dagger algebra is a dagger algebra. -/
theorem of_surjective [IsDaggerAlgebra K A] {B : Type*} [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (hf : Function.Surjective f) : IsDaggerAlgebra K B := by
  obtain ⟨n, φ, hφ⟩ := exists_surjective (K := K) (A := A)
  exact ⟨n, f.comp φ, hf.comp hφ⟩

/-- A quotient of a dagger algebra is a dagger algebra. -/
instance quotient [IsDaggerAlgebra K A] (I : Ideal A) : IsDaggerAlgebra K (A ⧸ I) :=
  of_surjective (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mkₐ_surjective K I)

/-- A quotient of the Monsky–Washnitzer algebra in finitely many variables is a dagger
algebra. -/
theorem of_surjective_washnitzerAlgebra {σ : Type*} [Finite σ]
    (φ : washnitzerAlgebra σ K →ₐ[K] A) (hφ : Function.Surjective φ) : IsDaggerAlgebra K A := by
  let := Fintype.ofFinite σ
  let e := washnitzerAlgebra.renameEquiv (R := K) (Fintype.equivFin σ).symm
  exact ⟨_, φ.comp e.toAlgHom, hφ.comp e.surjective⟩

/-- The Monsky–Washnitzer algebra in finitely many variables is a dagger algebra. -/
instance washnitzerAlgebra {σ : Type*} [Finite σ] :
    IsDaggerAlgebra K (washnitzerAlgebra σ K) :=
  of_surjective_washnitzerAlgebra (AlgHom.id K _) Function.surjective_id

variable (K) in
/-- The coefficient field is a dagger algebra, presented by the constant coefficient
`W_0 → K`. -/
instance self : IsDaggerAlgebra K K :=
  ⟨0, (washnitzerAlgebra.isEmptyAlgEquiv (Fin 0) K).toAlgHom,
    (washnitzerAlgebra.isEmptyAlgEquiv (Fin 0) K).surjective⟩

end IsDaggerAlgebra

/-- **The presentation criterion.** A `K`-algebra is a dagger algebra iff it is isomorphic to a
quotient `W_n ⧸ I` of a Monsky–Washnitzer algebra. -/
theorem isDaggerAlgebra_iff_exists_ideal : IsDaggerAlgebra K A ↔
    ∃ (n : ℕ) (I : Ideal (washnitzerAlgebra (Fin n) K)),
      Nonempty ((washnitzerAlgebra (Fin n) K ⧸ I) ≃ₐ[K] A) := by
  refine ⟨fun ⟨n, φ, hφ⟩ ↦ ⟨n, RingHom.ker φ, ⟨Ideal.quotientKerAlgEquivOfSurjective hφ⟩⟩, ?_⟩
  rintro ⟨n, I, ⟨e⟩⟩
  exact IsDaggerAlgebra.of_surjective (A := washnitzerAlgebra (Fin n) K ⧸ I) e.toAlgHom
    e.surjective

end Defs

section Presentation

variable (K : Type*) [NormedField K] [IsUltrametricDist K] (A : Type*) [CommRing A] [Algebra K A]
  [IsDaggerAlgebra K A]

open scoped Classical in
/-- The **presentation dimension** of a dagger algebra `A`: the least `n` for which there is a
surjection `W_n ↠ A`. It is not the Krull dimension: the dual numbers `K[ε] ⧸ (ε²)` have Krull
dimension `0` but need one variable. -/
noncomputable def presentationDim : ℕ :=
  Nat.find (IsDaggerAlgebra.exists_surjective (K := K) (A := A))

open scoped Classical in
/-- A chosen presentation `W_n ↠ A` in the least possible number `n = presentationDim K A` of
variables. -/
noncomputable def presentation : washnitzerAlgebra (Fin (presentationDim K A)) K →ₐ[K] A :=
  (Nat.find_spec (IsDaggerAlgebra.exists_surjective (K := K) (A := A))).choose

/-- The chosen presentation is surjective. -/
theorem presentation_surjective : Function.Surjective (presentation K A) := by
  classical
  exact (Nat.find_spec (IsDaggerAlgebra.exists_surjective (K := K) (A := A))).choose_spec

variable {K A}

/-- Any presentation `W_n ↠ A` has at least `presentationDim K A` variables. -/
theorem presentationDim_le {n : ℕ} (φ : washnitzerAlgebra (Fin n) K →ₐ[K] A)
    (hφ : Function.Surjective φ) : presentationDim K A ≤ n := by
  classical
  exact Nat.find_min' _ ⟨φ, hφ⟩

/-- **Dagger algebras of presentation dimension zero.** A dagger algebra has a presentation in
zero variables iff every element is a scalar. -/
theorem presentationDim_eq_zero_iff :
    presentationDim K A = 0 ↔ Function.Surjective (algebraMap K A) := by
  constructor
  · intro h
    obtain ⟨φ, hφ⟩ : ∃ φ : washnitzerAlgebra (Fin 0) K →ₐ[K] A, Function.Surjective φ :=
      h ▸ ⟨presentation K A, presentation_surjective K A⟩
    refine fun a ↦ ?_
    obtain ⟨f, rfl⟩ := hφ a
    obtain ⟨r, rfl⟩ := algebraMap_washnitzerAlgebra_surjective f
    exact ⟨r, (φ.commutes r).symm⟩
  · intro h
    let e := washnitzerAlgebra.isEmptyAlgEquiv (Fin 0) K
    exact Nat.le_zero.1 <| presentationDim_le ((Algebra.ofId K A).comp e.toAlgHom)
      (h.comp e.surjective)

variable (K) in
/-- The coefficient field has a presentation in zero variables. -/
@[simp]
theorem presentationDim_self : presentationDim K K = 0 :=
  presentationDim_eq_zero_iff.2 Function.surjective_id

variable (K) in
/-- The Monsky–Washnitzer algebra `W_1` in one variable needs exactly one variable: the variable
`X` is not a scalar. -/
@[simp]
theorem presentationDim_washnitzerAlgebra_fin_one :
    presentationDim K (washnitzerAlgebra (Fin 1) K) = 1 := by
  refine (presentationDim_le (AlgHom.id K _) Function.surjective_id).antisymm
    (Nat.one_le_iff_ne_zero.2 fun h ↦ ?_)
  obtain ⟨r, hr⟩ := presentationDim_eq_zero_iff.1 h (washnitzerAlgebra.X (Fin 1) K 0)
  have := congrArg (fun f : washnitzerAlgebra (Fin 1) K ↦
    coeff (Finsupp.single 0 1) (f : MvPowerSeries (Fin 1) K)) hr
  simp [MvPowerSeries.algebraMap_apply, coeff_C, coeff_X] at this

end Presentation

section Units

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IsDaggerAlgebra

variable {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- **Elements of dagger algebras have bounded spectrum.** Over a complete ultrametric normed
field, for every element `a` of a dagger algebra, `1 + c • a` is a unit for all scalars `c` near
`0`. -/
theorem eventually_isUnit_one_add_smul (a : A) : ∀ᶠ c in 𝓝 (0 : K), IsUnit (1 + c • a) := by
  obtain ⟨n, φ, hφ⟩ := exists_surjective (K := K) (A := A)
  obtain ⟨f, rfl⟩ := hφ a
  filter_upwards [washnitzerAlgebra.eventually_isUnit_one_add_smul f] with c hc
  simpa using hc.map φ

end IsDaggerAlgebra

end Units

/-- **The polynomial ring is not a dagger algebra.** Over a complete nontrivially normed
ultrametric field, `1 + c • X` is a unit of `K[X]` only for `c = 0`, so `K[X]` is not a quotient
of any Monsky–Washnitzer algebra. -/
theorem not_isDaggerAlgebra_polynomial {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : ¬ IsDaggerAlgebra K (Polynomial K) := by
  intro h
  obtain ⟨c, hc, hc0⟩ := ((IsDaggerAlgebra.eventually_isUnit_one_add_smul (K := K)
    (Polynomial.X : Polynomial K)).filter_mono nhdsWithin_le_nhds |>.and
      (self_mem_nhdsWithin (s := {0}ᶜ))).exists
  have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hc
  simp_all [Polynomial.smul_eq_C_mul]

end TauCeti.Dagger

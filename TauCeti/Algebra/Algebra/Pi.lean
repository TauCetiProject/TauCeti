/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: `Pi.evalAlgHom` and `AlgHom.eq_piEvalAlgHom` both occur in the statements below.
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The algebra homomorphisms out of a finite power of the base ring

Let `R` be a nontrivial commutative semiring without zero divisors and `ι` a finite index type.
Mathlib's `AlgHom.eq_piEvalAlgHom` says that every `R`-algebra homomorphism `(ι → R) →ₐ[R] R` is a
coordinate evaluation `Pi.evalAlgHom R _ s`. Distinct coordinates give distinct evaluations, since
they disagree on `Pi.single s 1`, so the evaluations enumerate those homomorphisms **without
repetition**: `Pi.evalAlgHomEquiv` packages that as an equivalence `ι ≃ ((ι → R) →ₐ[R] R)`.

The injectivity half, `Pi.evalAlgHom_injective`, is what Mathlib does not record, and it is what
makes the equivalence useful for counting: a split commutative algebra has exactly as many
characters as it has factors. The Burnside--Dixon--Schneider algorithm consumes it in that form, to
count the central characters of a group algebra whose centre has been split into coordinates.

For any algebra over a field, `AlgHom.surjective_pi_of_injective` supplies finite
interpolation at distinct augmentations, without commutativity or finite generation. It follows
from Mathlib's `linearIndependent_monoidHom` (Dedekind independence) and
`span_flip_eq_top_iff_linearIndependent` (finite duality). This supplies polynomial interpolation
on finite Weyl orbits for the Harish-Chandra central-character theorem.

For a finite-dimensional algebra over a field, `TauCeti.AlgHom.pi_bijective_of_injective`
identifies evaluation at a finite family of distinct characters with the function algebra,
provided those characters separate elements. The same evaluation, at all characters, is bijective
as soon as there are at least as many characters as the dimension
(`TauCeti.AlgHom.pi_id_bijective_of_finrank_le_card`): such an algebra is split, a finite product
of copies of the base field. This is how a finite scheme over a field with as many rational points
as its degree is shown to be étale.

## Main definitions

* `AlgHom.surjective_pi_of_injective`: distinct finitely many augmentations admit arbitrary
  simultaneous values.
* `Pi.evalAlgHom_injective`: distinct coordinates give distinct evaluation homomorphisms.
* `Pi.evalAlgHomEquiv`: the coordinates of `ι → R` are exactly the `R`-algebra homomorphisms
  `(ι → R) →ₐ[R] R`.
* `TauCeti.AlgHom.pi_id_bijective_of_finrank_le_card`: a finite-dimensional algebra over a field
  with at least as many characters as its dimension is the algebra of functions on its characters.
-/

public section

namespace Pi

variable (R ι : Type*) [CommSemiring R]

/-- Distinct coordinates give distinct evaluation homomorphisms out of a power of a nontrivial
commutative semiring. -/
theorem evalAlgHom_injective [Nontrivial R] :
    Function.Injective (Pi.evalAlgHom R fun _ : ι => R) := by
  classical
  intro s t hst
  by_contra hne
  have h := DFunLike.congr_fun hst (Pi.single s 1)
  rw [evalAlgHom_apply, evalAlgHom_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Ne.symm hne)] at h
  exact one_ne_zero h

variable [NoZeroDivisors R] [Nontrivial R] [Finite ι]

/-- **The `R`-algebra homomorphisms out of `ι → R` are the coordinate evaluations, each occurring
once.** Surjectivity is Mathlib's `AlgHom.eq_piEvalAlgHom`; injectivity holds because the
evaluations at two distinct coordinates take the values `1` and `0` on `Pi.single`. -/
noncomputable def evalAlgHomEquiv : ι ≃ ((ι → R) →ₐ[R] R) :=
  Equiv.ofBijective (Pi.evalAlgHom R fun _ => R)
    ⟨evalAlgHom_injective R ι,
      fun φ => φ.eq_piEvalAlgHom.imp fun _ hs => hs.symm⟩

@[simp]
theorem evalAlgHomEquiv_apply (s : ι) :
    evalAlgHomEquiv R ι s = Pi.evalAlgHom R (fun _ => R) s :=
  (rfl)

end Pi

namespace AlgHom

/-- Distinct finitely many augmentations to the ground field admit arbitrary simultaneous
values: their product algebra homomorphism is surjective. -/
theorem surjective_pi_of_injective {K A ι : Type*} [Field K] [Semiring A] [Algebra K A]
    [_root_.Finite ι] (f : ι → A →ₐ[K] K) (hf : Function.Injective f) :
    Function.Surjective (AlgHom.pi f) := by
  have hli : LinearIndependent K (fun i : ι ↦ (f i : A → K)) :=
    (linearIndependent_monoidHom A K).comp
      (fun i ↦ (f i).toRingHom.toMonoidHom)
      (fun i j hij ↦ hf <| AlgHom.ext fun x ↦ congrArg (fun m : A →* K ↦ m x) hij)
  have hspan : Submodule.span K (Set.range (AlgHom.pi f).toLinearMap) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hli
  have hr : LinearMap.range (AlgHom.pi f).toLinearMap = ⊤ := by
    simpa only [← LinearMap.coe_range, Submodule.span_eq] using hspan
  exact LinearMap.range_eq_top.mp hr

end AlgHom

namespace TauCeti

variable {K A ι : Type*} [Field K] [Ring A] [Algebra K A]
  [Module.Finite K A]

/-- Evaluation at distinct characters that separate elements identifies a finite-dimensional
algebra with the algebra of functions on the character index set. -/
theorem AlgHom.pi_bijective_of_injective (χ : ι → A →ₐ[K] K)
    (hχ : Function.Injective χ) (hinj : Function.Injective (AlgHom.pi χ)) :
    Function.Bijective (AlgHom.pi χ) := by
  classical
  let := Finite.algHom K A K
  let := Finite.of_injective χ hχ
  let := Fintype.ofFinite ι
  have hle : Module.finrank K (ι → K) ≤ Module.finrank K A := by
    have h := (Nat.card_le_card_of_injective χ hχ).trans
      (card_algHom_le_finrank K A K)
    simpa [Module.finrank_pi] using h
  have hdim : Module.finrank K A = Module.finrank K (ι → K) :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective
      (f := (AlgHom.pi χ).toLinearMap) hinj) hle
  exact ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (AlgHom.pi χ).toLinearMap) hdim).mp hinj⟩

/-- **A finite-dimensional algebra with as many characters as its dimension is split.** If a
finite-dimensional algebra `A` over a field `K` has at least `finrank K A` characters
`A →ₐ[K] K`, then evaluation at all of them identifies `A` with the algebra of `K`-valued functions
on its characters. -/
theorem AlgHom.pi_id_bijective_of_finrank_le_card
    (h : Module.finrank K A ≤ Nat.card (A →ₐ[K] K)) :
    Function.Bijective (AlgHom.pi fun χ : A →ₐ[K] K ↦ χ) := by
  classical
  let := Finite.algHom K A K
  let := Fintype.ofFinite (A →ₐ[K] K)
  have hsurj := _root_.AlgHom.surjective_pi_of_injective (fun χ : A →ₐ[K] K ↦ χ)
    Function.injective_id
  have hdim : Module.finrank K A = Module.finrank K ((A →ₐ[K] K) → K) :=
    le_antisymm (by simpa [Module.finrank_pi] using h)
      (LinearMap.finrank_le_finrank_of_surjective
        (f := (AlgHom.pi fun χ : A →ₐ[K] K ↦ χ).toLinearMap) hsurj)
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (AlgHom.pi fun χ : A →ₐ[K] K ↦ χ).toLinearMap) hdim).mpr hsurj, hsurj⟩

end TauCeti

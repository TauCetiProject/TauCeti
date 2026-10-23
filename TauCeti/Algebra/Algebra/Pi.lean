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
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.TensorProduct.Pi
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

Over any nontrivial commutative semiring, an algebra map `φ : (ι → T) →ₐ[T] (κ → T)` whose matrix
entries `φ (Pi.single i 1) j` are all `0` or `1` is induced by a map of index sets `κ → ι`
(`AlgHom.exists_apply_eq_comp_of_entries`). This computes equalizers of algebra maps between split
algebras.

For a finite-dimensional algebra over a field, `TauCeti.AlgHom.pi_bijective_of_injective`
identifies evaluation at a finite family of distinct characters with the function algebra,
provided those characters separate elements. The same evaluation, at all characters, is bijective
as soon as there are at least as many characters as the dimension
(`TauCeti.AlgHom.pi_id_bijective_of_finrank_le_card`): such an algebra is split, a finite product
of copies of the base field. This is how a finite scheme over a field with as many rational points
as its degree is shown to be étale.

When a family of characters `χ` of `C` and a finite family `ψ` of characters of `D` identify `C`
and `D` with function algebras, `Algebra.TensorProduct.eq_of_pi_bijective` says that the products
`Algebra.TensorProduct.lift (χ i) (ψ j)` separate the elements of `C ⊗[R] D`: they are the
coordinates of `C ⊗[R] D ≅ (ι → R) ⊗[R] (κ → R) ≅ (κ → ι → R)`.

## Main definitions

* `AlgHom.surjective_pi_of_injective`: distinct finitely many augmentations admit arbitrary
  simultaneous values.
* `AlgHom.exists_apply_eq_comp_of_entries`: an algebra map `(ι → T) →ₐ[T] (κ → T)` whose matrix
  entries are all `0` or `1` is induced by a map `κ → ι`.
* `Pi.evalAlgHom_injective`: distinct coordinates give distinct evaluation homomorphisms.
* `Pi.evalAlgHomEquiv`: the coordinates of `ι → R` are exactly the `R`-algebra homomorphisms
  `(ι → R) →ₐ[R] R`.
* `Algebra.TensorProduct.eq_of_pi_bijective`: characters identifying `C` and `D` with function
  algebras give separating characters of `C ⊗[R] D`.
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

/-- An algebra map between function algebras whose matrix entries `φ (Pi.single i 1) j` are all `0`
or `1` is induced by a map of the index sets. -/
theorem exists_apply_eq_comp_of_entries {T ι κ : Type*} [CommSemiring T] [Nontrivial T]
    [_root_.Finite ι] [DecidableEq ι] (φ : (ι → T) →ₐ[T] (κ → T))
    (hφ : ∀ i j, φ (Pi.single i 1) j = 0 ∨ φ (Pi.single i 1) j = 1) :
    ∃ u : κ → ι, ∀ s j, φ s j = s (u j) := by
  have := Fintype.ofFinite ι
  have hsum (j : κ) : ∑ i, φ (Pi.single i 1) j = 1 := by
    have h1 : ∑ i, (Pi.single i 1 : ι → T) = 1 := by
      simpa using Finset.univ_sum_single (1 : ι → T)
    rw [← Finset.sum_apply, ← map_sum, h1, map_one, Pi.one_apply]
  have hone (j : κ) : ∃ i, φ (Pi.single i 1) j = 1 := by
    by_contra! h
    have h0 (i : ι) : φ (Pi.single i 1) j = 0 := (hφ i j).resolve_right (h i)
    exact one_ne_zero ((hsum j).symm.trans (by simp [h0]))
  choose u hu using hone
  refine ⟨u, fun s j ↦ ?_⟩
  have hs : s = ∑ i, s i • (Pi.single i 1 : ι → T) := by
    conv_lhs => rw [← Finset.univ_sum_single s]
    simp [← Pi.single_smul']
  have hφs : φ s j = ∑ i, s i * φ (Pi.single i 1) j := by
    conv_lhs => rw [hs]
    rw [map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [hφs, Finset.sum_eq_single (u j) (fun i _ hi ↦ ?_) (by simp), hu j, mul_one]
  have hprod : (Pi.single i 1 : ι → T) * Pi.single (u j) 1 = 0 := by
    ext k
    by_cases hk : k = i
    · subst hk
      simp [hi]
    · simp [Pi.single_apply, hk]
  have h0 := congrFun (congrArg φ hprod) j
  simp [hu j] at h0
  simp [h0]

end AlgHom

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {R C D ι κ : Type*} [CommSemiring R] [Semiring C] [Algebra R C] [Semiring D]
  [Algebra R D] [_root_.Finite κ]

/-- If a family of characters `χ` of `C` and a finite family `ψ` of characters of `D`
identify `C` and `D` with the function algebras `ι → R` and `κ → R`, then the characters
`lift (χ i) (ψ j)` separate the elements of `C ⊗[R] D`: through
`C ⊗[R] D ≅ (ι → R) ⊗[R] (κ → R) ≅ (κ → ι → R)` they are the coordinates. -/
theorem eq_of_pi_bijective {χ : ι → C →ₐ[R] R} {ψ : κ → D →ₐ[R] R}
    (hχ : Function.Bijective (AlgHom.pi χ)) (hψ : Function.Bijective (AlgHom.pi ψ))
    {x y : C ⊗[R] D}
    (h : ∀ i j,
      lift (χ i) (ψ j) (fun _ _ ↦ .all _ _) x = lift (χ i) (ψ j) (fun _ _ ↦ .all _ _) y) :
    x = y := by
  classical
  have := Fintype.ofFinite κ
  let F := (_root_.TensorProduct.congr (AlgEquiv.ofBijective _ hχ).toLinearEquiv
    (AlgEquiv.ofBijective _ hψ).toLinearEquiv).trans
      (_root_.TensorProduct.piScalarRight R R (ι → R) κ)
  have hF (z : C ⊗[R] D) (i : ι) (j : κ) :
      F z j i = lift (χ i) (ψ j) (fun _ _ ↦ .all _ _) z := by
    induction z using _root_.TensorProduct.inductionOn with
    | tmul c d => simp [F, _root_.TensorProduct.piScalarRightHom_tmul, mul_comm]
    | add z z' hz hz' =>
        simp only [map_add, Pi.add_apply] at hz hz' ⊢
        rw [hz, hz']
  exact F.injective <| funext fun j ↦ funext fun i ↦ by rw [hF, hF, h]

end Algebra.TensorProduct

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

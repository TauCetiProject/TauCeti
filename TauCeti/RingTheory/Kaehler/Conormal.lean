/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.RingTheory.LocalRing.MaximalIdeal.Square

/-!
# The conormal sequence of a formally smooth quotient

Let `P → S` be a surjection of `R`-algebras with kernel `I`. The conormal sequence

`I/I² → S ⊗[P] Ω[P⁄R] → Ω[S⁄R] → 0`

is exact (`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`). If `S` is formally
smooth over `R`, the identity of `S` lifts along the square-zero extension `P/I² → S`, and such a
section is the same as a retraction of `I/I² → S ⊗[P] Ω[P⁄R]`
(`retractionKerCotangentToTensorEquivSection`). So the first map is injective, and the sequence is
exact on the left as well. If `S` is moreover formally unramified, then `Ω[S⁄R] = 0` and the
conormal module `I/I²` is identified with `S ⊗[P] Ω[P⁄R]`.

For a closed point of a scheme over a field whose residue field is separable over the base, this
identifies the Zariski cotangent space `𝔪/𝔪²` with the fibre of the differentials. In
particular, if `A` is a local `k`-algebra whose residue field `κ` is formally smooth over `k`, the
differentials `1 ⊗ d t_j` of any minimal generating set of `𝔪_A` are `κ`-linearly independent in
`κ ⊗[A] Ω[A⁄k]`.

## Main results

* `KaehlerDifferential.kerCotangentToTensor_injective_of_formallySmooth`: the conormal map
  `I/I² → S ⊗[P] Ω[P⁄R]` is injective when `S` is formally smooth over `R`.
* `KaehlerDifferential.kerCotangentToTensor_bijective_of_formallyEtale`: it is bijective when `S`
  is formally étale over `R`.
* `KaehlerDifferential.linearIndependent_tmul_D`: when the residue field `κ` of a local
  `k`-algebra `A` is formally smooth over `k`, the differentials `1 ⊗ d t_j` of a minimal
  generating set of `𝔪_A` are `κ`-linearly independent in `κ ⊗[A] Ω[A⁄k]`.

## References

* [Stacks Project, Tag 031I](https://stacks.math.columbia.edu/tag/031I): a quotient `P/I` is
  formally smooth exactly when the conormal sequence is split exact on the left, given `P`
  formally smooth. Only the implication from formal smoothness to injectivity is used here, and it
  needs no hypothesis on `P`.
-/

public section

noncomputable section

open Function IsLocalRing TensorProduct

namespace KaehlerDifferential

variable {R P S : Type*} [CommRing R] [CommRing P] [CommRing S] [Algebra R P] [Algebra P S]
  [Algebra R S] [IsScalarTower R P S]

/-- For a surjection `P → S` with kernel `I` onto a formally smooth `R`-algebra, the conormal map
`I/I² → S ⊗[P] Ω[P⁄R]` is injective. -/
theorem kerCotangentToTensor_injective_of_formallySmooth [Algebra.FormallySmooth R S]
    (hf : Surjective (algebraMap P S)) :
    Injective (kerCotangentToTensor R P S) := by
  let f := IsScalarTower.toAlgHom R P S
  -- The kernel of `P/I² → S` is `I/I²`, which squares to zero.
  have hnil : IsNilpotent (RingHom.ker f.kerSquareLift) :=
    ⟨2, (congrArg (· ^ 2) f.ker_kerSquareLift).trans (Ideal.cotangentIdeal_square _)⟩
  have hsurj : Surjective f.kerSquareLift := by
    intro s
    obtain ⟨p, rfl⟩ := hf s
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  -- Formal smoothness lifts the identity of `S` to a section of `P/I² → S`.
  let g := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R S) f.kerSquareLift hsurj hnil
  have hg : f.kerSquareLift.comp g = AlgHom.id R S :=
    AlgHom.ext <| Algebra.FormallySmooth.liftOfSurjective_apply _ _ hsurj hnil
  -- A section gives a retraction of the conormal map.
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := R) hf).symm ⟨g, hg⟩
  exact LeftInverse.injective (g := l) fun x ↦ congr($hl x)

/-- For a surjection `P → S` with kernel `I` onto a formally étale `R`-algebra, the conormal map
`I/I² → S ⊗[P] Ω[P⁄R]` is bijective. -/
theorem kerCotangentToTensor_bijective_of_formallyEtale [Algebra.FormallyEtale R S]
    (hf : Surjective (algebraMap P S)) :
    Bijective (kerCotangentToTensor R P S) := by
  refine ⟨kerCotangentToTensor_injective_of_formallySmooth hf, fun x ↦ ?_⟩
  exact (exact_kerCotangentToTensor_mapBaseChange R P S hf x).1 (Subsingleton.elim _ _)

/-- For a minimal system of generators `t : Fin r → A` of the maximal ideal of a local ring `A`
whose residue field `κ` is formally smooth over `k`, the tensors `1 ⊗ d(t j)` are `κ`-linearly
independent in `κ ⊗[A] Ω[A⁄k]`. -/
theorem linearIndependent_tmul_D {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [Algebra.FormallySmooth k (ResidueField A)]
    {r : ℕ} {t : Fin r → A} (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hr : (maximalIdeal A).spanFinrank = r) :
    LinearIndependent (ResidueField A)
      (fun j : Fin r ↦ (1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t j)) := by
  set κ := ResidueField A
  have hker : RingHom.ker (algebraMap A κ) = maximalIdeal A := by
    rw [ResidueField.algebraMap_eq, ker_residue]
  have hsurj : Function.Surjective (algebraMap A κ) := by
    rw [ResidueField.algebraMap_eq]
    exact residue_surjective
  have hinj := kerCotangentToTensor_injective_of_formallySmooth (R := k) (P := A) (S := κ) hsurj
  let e := Ideal.Cotangent.equivOfEq (maximalIdeal A) (RingHom.ker (algebraMap A κ)) hker.symm
  let φ : (maximalIdeal A).Cotangent →ₗ[κ] κ ⊗[A] Ω[A⁄k] :=
    (kerCotangentToTensor k A κ ∘ₗ e.toLinearMap).extendScalarsOfSurjective hsurj
  have hli := (TauCeti.IsLocalRing.linearIndependent_toCotangent ht hr).map' φ
    (LinearMap.ker_eq_bot.mpr (hinj.comp e.injective))
  convert hli using 1
  ext j
  simp [φ, e, LinearMap.extendScalarsOfSurjective_apply, Ideal.Cotangent.equivOfEq]

end KaehlerDifferential

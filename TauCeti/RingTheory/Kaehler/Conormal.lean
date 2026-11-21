/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient

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

The surjectivity half needs only `Ω[S⁄R] = 0`. For an ideal `J` of `P` with `R → P ⧸ J`
surjective, for instance the kernel of a section `P → R ⧸ I` of `Spec P → Spec R` over `V(I)`,
it says that every class in `Ω[P⁄R] ⧸ J • Ω[P⁄R]` is the class of `D x` for some `x ∈ J`.

For a closed point of a scheme over a field whose residue field is separable over the base, this
identifies the Zariski cotangent space `𝔪/𝔪²` with the fibre of the differentials.

## Main results

* `KaehlerDifferential.kerCotangentToTensor_injective_of_formallySmooth`: the conormal map
  `I/I² → S ⊗[P] Ω[P⁄R]` is injective when `S` is formally smooth over `R`.
* `KaehlerDifferential.kerCotangentToTensor_bijective_of_formallyEtale`: it is bijective when `S`
  is formally étale over `R`.
* `KaehlerDifferential.exists_mem_and_mk_D_eq`: if `R → P ⧸ J` is surjective, every class in
  `Ω[P⁄R] ⧸ J • Ω[P⁄R]` is the class of `D x` for some `x ∈ J`.

## References

* [Stacks Project, Tag 031I](https://stacks.math.columbia.edu/tag/031I): a quotient `P/I` is
  formally smooth exactly when the conormal sequence is split exact on the left, given `P`
  formally smooth. Only the implication from formal smoothness to injectivity is used here, and it
  needs no hypothesis on `P`.
-/

public section

noncomputable section

open Function

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

/-- If `R → P ⧸ J` is surjective, then every class in `Ω[P⁄R] ⧸ J • Ω[P⁄R]` is the class of the
differential of an element of `J`: the conormal map `J/J² → (P ⧸ J) ⊗[P] Ω[P⁄R]` is surjective,
as `Ω[(P ⧸ J)⁄R] = 0`. -/
theorem exists_mem_and_mk_D_eq (J : Ideal P) (hJ : Surjective (algebraMap R (P ⧸ J)))
    (q : Ω[P⁄R] ⧸ J • (⊤ : Submodule P Ω[P⁄R])) :
    ∃ x ∈ J, Submodule.Quotient.mk (D R P x) = q := by
  have : Algebra.FormallyUnramified R (P ⧸ J) := .of_surjective (Algebra.ofId R (P ⧸ J)) hJ
  obtain ⟨y, hy⟩ := (exact_kerCotangentToTensor_mapBaseChange R P (P ⧸ J)
    Ideal.Quotient.mk_surjective ((TensorProduct.quotTensorEquivQuotSMul _ J).symm q)).mp
    (Subsingleton.elim _ _)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ y
  refine ⟨x, by simpa using hx, ?_⟩
  rwa [kerCotangentToTensor_toCotangent, LinearEquiv.eq_symm_apply,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul] at hy

end KaehlerDifferential

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.SkewHermitian
public import TauCeti.NumberTheory.NumberField.CMField.AddChar

/-!
# The adelic Heisenberg datum of a CM field

Let `E` be a CM field with complex conjugation `x ↦ conj x`, `E_∞` its infinite adeles, `𝔸_f` its
finite adeles, with the conjugation transported to both, and let `ψ_∞`, `ψ_f` be the standard
additive characters of `E_∞` and `𝔸_f` (`TauCeti.GlobalNumberFields.infiniteAdeleAddChar`,
`TauCeti.GlobalNumberFields.finiteAdeleAddChar`), whose product is the standard character `ψ` of
`𝔸 = E_∞ × 𝔸_f`.

Both characters are invariant under conjugation: at an infinite place, conjugation is complex
conjugation in `E_w ≅ ℂ` and preserves the real part, and on `𝔸_f` it is the transport of finite
adeles along an automorphism of `E`, which preserves `Tr_{E/ℚ}` and `Ô`. Hence both are trivial on
the skew-adjoint adeles (`conj t = -t`), and for a skew-adjoint `t` and signs `s ∈ {±1}^n`,

* `β_∞ (x, y) = ψ_∞ (t · y* ε_s x)` on `E_∞^n`, with `ε_s = diag(s)`, and
* `β_f (x, y) = ψ_f (t · y* x)` on `𝔸_f^n`

are Heisenberg data (`TauCeti.HeisenbergDatum.ofSkewHermitian`). For `t ∈ E` with
`conj t = -t`, the **adelic Heisenberg datum** of signature `s` is their product,

`β_s ((x_∞, x_f), (y_∞, y_f)) = ψ_∞ (t · y_∞* ε_s x_∞) · ψ_f (t · y_f* x_f)`,

that is `β_s (x, y) = ψ (t · y* ε_s x)` on `𝔸^n = E_∞^n × 𝔸_f^n`, where `ε_s` is `diag(s)` at the
infinite places and `1` at the finite places. For `t = ½ j` with `j ∈ E` purely imaginary, this is
the Heisenberg datum `ψ (½ j · y* ε_s x)` of the reproducing model on which the adelic Weil
representation of a hermitian space of signature `s` acts.

In finite coordinates `x_f = α z` for a finite adele `α`, the finite datum of `t` becomes the
finite datum of `α t (conj α)` (`TauCeti.finiteHeisenbergDatum_smul_smul`); for `t = ½ j`, this
is the datum `ψ_f (½ j α (conj α) · y* x)` on `𝔸_f^n`.

## Main definitions

* `TauCeti.infiniteHeisenbergDatum ι t s`: the datum `ψ_∞ (t · y* ε_s x)` on `E_∞^ι`.
* `TauCeti.finiteHeisenbergDatum ι t`: the datum `ψ_f (t · y* x)` on `𝔸_f^ι`.
* `TauCeti.adelicHeisenbergDatum ι t s`: the adelic Heisenberg datum `ψ (t · y* ε_s x)` on
  `E_∞^ι × 𝔸_f^ι`.

## Main results

* `TauCeti.GlobalNumberFields.finiteAdeleAddChar_star`,
  `TauCeti.GlobalNumberFields.infiniteAdeleAddChar_star`: the standard characters are invariant
  under conjugation, and
  `TauCeti.GlobalNumberFields.finiteAdeleAddChar_eq_one_of_mem_skewAdjoint`,
  `TauCeti.GlobalNumberFields.infiniteAdeleAddChar_eq_one_of_mem_skewAdjoint`: they are trivial on
  the skew-adjoint adeles (see `TauCeti.NumberTheory.NumberField.CMField.AddChar`).
* `TauCeti.finiteHeisenbergDatum_smul_smul`: the finite datum in finite coordinates.

## Provenance

The adelic Heisenberg datum corresponds to `New.adelicHeisenberg` in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Weil/Construction/WeilData.lean`. The construction here, through the Heisenberg datum of
a skew-hermitian matrix and the conjugation invariance of the standard characters, was written
independently.

## References

* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), 143–211.
-/

public section

noncomputable section

open IsDedekindDomain NumberField Matrix
open scoped NumberField.AdeleRing

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

namespace TauCeti

open GlobalNumberFields

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-! ### The infinite and finite data -/

/-- The Heisenberg datum `β (x, y) = ψ_∞ (t · y* ε_s x)` on `E_∞^ι` of a skew-adjoint infinite
adele `t` and signs `s`, with `ε_s = diag(s)`. -/
def infiniteHeisenbergDatum (t : InfiniteAdeleRing E) (ht : t ∈ skewAdjoint (InfiniteAdeleRing E))
    (s : ι → ℤˣ) : HeisenbergDatum (ι → InfiniteAdeleRing E) :=
  HeisenbergDatum.ofSkewHermitian (infiniteAdeleAddChar E) continuous_infiniteAdeleAddChar
    (fun _ ↦ infiniteAdeleAddChar_eq_one_of_mem_skewAdjoint)
    (t • diagonal fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E))
    ((isHermitian_iff_isSelfAdjoint.1 (isHermitian_diagonal_of_self_adjoint _
      (funext fun i ↦ IsSelfAdjoint.intCast (s i : ℤ)))).smul_mem_skewAdjoint ht)

variable {ι}

@[simp]
theorem infiniteHeisenbergDatum_apply (t : InfiniteAdeleRing E)
    (ht : t ∈ skewAdjoint (InfiniteAdeleRing E)) (s : ι → ℤˣ) (x y : ι → InfiniteAdeleRing E) :
    infiniteHeisenbergDatum ι t ht s x y =
      infiniteAdeleAddChar E (t * (star y ⬝ᵥ diagonal (fun i ↦ ((s i : ℤ) : _)) *ᵥ x)) := by
  rw [infiniteHeisenbergDatum, HeisenbergDatum.ofSkewHermitian_apply, smul_mulVec,
    dotProduct_smul, smul_eq_mul]

variable (ι) in
/-- The Heisenberg datum `β (x, y) = ψ_f (t · y* x)` on `𝔸_f^ι` of a skew-adjoint finite adele
`t`. -/
def finiteHeisenbergDatum (t : 𝔸ᶠ[E]) (ht : t ∈ skewAdjoint 𝔸ᶠ[E]) :
    HeisenbergDatum (ι → 𝔸ᶠ[E]) :=
  HeisenbergDatum.ofSkewHermitian (finiteAdeleAddChar E) continuous_finiteAdeleAddChar
    (fun _ ↦ finiteAdeleAddChar_eq_one_of_mem_skewAdjoint) (t • 1)
    (IsSelfAdjoint.one _ |>.smul_mem_skewAdjoint ht)

@[simp]
theorem finiteHeisenbergDatum_apply (t : 𝔸ᶠ[E]) (ht : t ∈ skewAdjoint 𝔸ᶠ[E])
    (x y : ι → 𝔸ᶠ[E]) :
    finiteHeisenbergDatum ι t ht x y = finiteAdeleAddChar E (t * (star y ⬝ᵥ x)) := by
  rw [finiteHeisenbergDatum, HeisenbergDatum.ofSkewHermitian_apply, smul_mulVec, one_mulVec,
    dotProduct_smul, smul_eq_mul]

/-- In finite coordinates `x = c z`, the finite datum of `t` is the finite datum of
`c t (conj c)`: `β_t (c x, c y) = β_{c t (conj c)} (x, y)`. -/
theorem finiteHeisenbergDatum_smul_smul (t : 𝔸ᶠ[E]) (ht : t ∈ skewAdjoint 𝔸ᶠ[E]) (c : 𝔸ᶠ[E])
    (x y : ι → 𝔸ᶠ[E]) :
    finiteHeisenbergDatum ι t ht (c • x) (c • y) =
      finiteHeisenbergDatum ι (c * t * star c) (skewAdjoint.conjugate ht c) x y := by
  rw [finiteHeisenbergDatum_apply, finiteHeisenbergDatum_apply, star_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul]
  congr 2
  ring

/-! ### The adelic Heisenberg datum -/

variable (ι) in
/-- The **adelic Heisenberg datum** of signature `s` attached to `t ∈ E` with `conj t = -t`: the
Heisenberg datum `β_s (x, y) = ψ (t · y* ε_s x)` on `𝔸^ι = E_∞^ι × 𝔸_f^ι`, where `ψ` is the
standard character of the adeles and `ε_s` is `diag(s)` at the infinite places and `1` at the
finite places. It is the product of the infinite datum and the finite datum of `t`. For a purely
imaginary `j ∈ E`, the datum `ψ (½ j · y* ε_s x)` is the case `t = ½ j`. -/
def adelicHeisenbergDatum (t : E) (ht : t ∈ skewAdjoint E) (s : ι → ℤˣ) :
    HeisenbergDatum ((ι → InfiniteAdeleRing E) × (ι → 𝔸ᶠ[E])) :=
  (infiniteHeisenbergDatum ι (algebraMap E _ t) (by
      rw [Algebra.algebraMap_eq_smul_one]
      exact (IsSelfAdjoint.one _).smul_mem_skewAdjoint ht) s).prod
    (finiteHeisenbergDatum ι (algebraMap E _ t) (by
      rw [Algebra.algebraMap_eq_smul_one]
      exact (IsSelfAdjoint.one _).smul_mem_skewAdjoint ht))

@[simp]
theorem adelicHeisenbergDatum_apply (t : E) (ht : t ∈ skewAdjoint E) (s : ι → ℤˣ)
    (x y : (ι → InfiniteAdeleRing E) × (ι → 𝔸ᶠ[E])) :
    adelicHeisenbergDatum ι t ht s x y =
      infiniteAdeleAddChar E (algebraMap E _ t *
        (star y.1 ⬝ᵥ diagonal (fun i ↦ ((s i : ℤ) : _)) *ᵥ x.1)) *
      finiteAdeleAddChar E (algebraMap E _ t * (star y.2 ⬝ᵥ x.2)) := by
  rw [adelicHeisenbergDatum, HeisenbergDatum.prod_apply, infiniteHeisenbergDatum_apply,
    finiteHeisenbergDatum_apply]

end TauCeti

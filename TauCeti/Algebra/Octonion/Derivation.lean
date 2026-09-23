/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.Algebra.Lie.GeneralLinear.Finrank
public import TauCeti.Algebra.Octonion.Basic
public import TauCeti.LinearAlgebra.CrossProduct

/-!
# Derivations of the split octonions

`G₂` is the derivation algebra of the split octonions, and its fundamental representation is
supposed to be the `7`-dimensional space of imaginary octonions. Neither statement can even be made
until one knows that a derivation of `𝕆` lands in the imaginary octonions and respects the norm
form; that is what this file proves.

Let `D` be a derivation of `TauCeti.Octonion R`. Applying `D` to the rank-two equation
`x² = tr x · x - N x · 1` and to the polarization
`x * conj y + y * conj x = ⟨x, y⟩ · 1` of the norm gives one
identity in `𝕆`,

`tr (D x) · x = ⟨x, D x⟩ · 1`,

and everything follows from it. Evaluated at the diagonal idempotent `e = ⟨1, 0, 0, 0⟩` — an
element whose existence is exactly the splitness of `𝕆` — its two diagonal entries read
`tr (D e) = ⟨e, D e⟩` and `0 = ⟨e, D e⟩`. Polarizing it and feeding `e` into the second slot forces
`tr (D x) = 0` for **every** `x`, and with the trace gone the identity itself collapses to
`⟨x, D x⟩ = 0`: a derivation is skew for the norm form.

So `D` maps all of `𝕆` into the imaginary octonions, commutes with conjugation, and lies in the
orthogonal Lie algebra of the norm: `Der 𝕆 ≤ 𝔰𝔬(N)`
(`TauCeti.Octonion.derivationLieAlgebra_le_skewAdjointLieSubalgebra`). In particular the imaginary
octonions are a Lie submodule (`TauCeti.Octonion.imaginaryLieSubmodule`) — this is the candidate
`7`-dimensional fundamental representation — and, when scalar multiplication by `2` on `𝕆` is
regular, `Der 𝕆` acts faithfully on it, since `𝕆 = R · 1 ⊕ Im 𝕆` and a derivation kills `1`.

In the other direction the file exhibits `14` independent derivations. The Zorn model grades `𝕆`
by `ℤ/3`, with the two scalar entries in degree `0`, the top-right vector entry in degree `1` and
the bottom-left one in degree `2`, and three families of derivations match those degrees: the
`𝔰𝔩₃` acting on the vector entries in degree `0`, and a copy of `R³` in each off-diagonal degree.
Evaluation at the diagonal idempotent `⟨1, 0, 0, 0⟩` separates the two off-diagonal families, which
the `𝔰𝔩₃` family kills; evaluation on the vector entries then separates the `𝔰𝔩₃` family itself. So
the three are independent and `14 ≤ finrank (Der 𝕆)` over a field. The reverse inequality is not
proved here.

## Main definitions

* `TauCeti.Octonion.imaginaryLieSubmodule`: the imaginary octonions as a Lie submodule of `𝕆` over
  `Der 𝕆`, so that `Im 𝕆` is a representation of `Der 𝕆`.
* `TauCeti.Octonion.slDerivation`: `𝔰𝔩₃ → Der 𝕆`, the derivations coming from the `SL₃` acting on
  the vector entries of a Zorn vector matrix, as a homomorphism of Lie algebras.
* `TauCeti.Octonion.vectorDerivation` and `TauCeti.Octonion.covectorDerivation`: the two
  off-diagonal families of derivations, of degrees `1` and `2` for the `ℤ/3`-grading of `𝕆`.
* `TauCeti.Octonion.gradedDerivation`: the three families assembled into a map of `R`-modules
  `𝔰𝔩₃ ⊕ R³ ⊕ R³ → Der 𝕆`.

## Main results

* `TauCeti.Octonion.trace_derivation_apply_eq_zero`: a derivation of `𝕆` has values of trace `0`, so
  (`TauCeti.Octonion.derivation_apply_mem_imaginary`) its image lies in the imaginary octonions.
* `TauCeti.Octonion.derivation_apply_conj`: a derivation commutes with conjugation.
* `TauCeti.Octonion.polar_derivation_apply_self_eq_zero` and
  `TauCeti.Octonion.polar_derivation_apply_left_eq_neg`: a derivation is **skew** for the symmetric
  bilinear form of the norm, `⟨D x, y⟩ = -⟨x, D y⟩`.
* `TauCeti.Octonion.derivationLieAlgebra_le_skewAdjointLieSubalgebra`: `Der 𝕆 ≤ 𝔰𝔬(N)`, the
  previous item as an inclusion of Lie subalgebras of `Module.End R 𝕆`.
* `TauCeti.Octonion.isFaithful_imaginaryLieSubmodule`: when scalar multiplication by `2` on `𝕆` is
  regular, `Der 𝕆` acts faithfully on `Im 𝕆`; `TauCeti.Octonion.instIsFaithfulImaginaryLieSubmodule`
  is the instance form of that, under `[NoZeroSMulDivisors R (Octonion R)]` and `[NeZero (2 : R)]`.
* `TauCeti.Octonion.gradedDerivation_injective`: the three explicit families are independent, so
  `Der 𝕆` contains `8 + 3 + 3` independent derivations; in particular
  `TauCeti.Octonion.instNontrivialDerivationLieAlgebra`, `Der 𝕆` is not the zero Lie algebra and
  none of the above is vacuous. `TauCeti.Octonion.slDerivation_injective`,
  `TauCeti.Octonion.vectorDerivation_injective` and
  `TauCeti.Octonion.covectorDerivation_injective` are the one-family corollaries.
* `TauCeti.Octonion.fourteen_le_finrank_derivationLieAlgebra`: over a field,
  `14 ≤ finrank (Der 𝕆)`.

## Implementation notes

Everything is stated over a commutative ring except the dimension bound
`TauCeti.Octonion.fourteen_le_finrank_derivationLieAlgebra`, whose `finrank` count needs a field.
The faithfulness result is stated for the exact hypothesis its proof uses,
`IsSMulRegular (Octonion R) (2 : R)`, which is not a class; the instance form of it therefore asks
for the two classes `[NoZeroSMulDivisors R (Octonion R)]` and `[NeZero (2 : R)]`, which imply it
but are strictly stronger. Some such hypothesis is necessary (over `𝔽₂` conjugation is the
identity, so `Im 𝕆` contains `1` and the argument that `Im 𝕆` complements `R · 1` breaks down).

The two coordinate extractions the argument needs — reading the `a` and `b` entries of an equation
between multiples of `⟨1, 0, 0, 0⟩` and of `1` — are isolated in a private lemma, so no public
statement here is about entries of a vector matrix.

Derivations are taken in the bundled form `D : TauCeti.derivationLieAlgebra R (Octonion R)` of
`TauCeti/Algebra/Lie/Derivation/Basic.lean`, and are applied through the coercion
`(D : Module.End R (Octonion R))`, which is the simp-normal form of their action there.

## References

Of the count `finrank (Der 𝕆) = 14` only the lower bound is proved here; the matching upper bound,
the type-`G₂` Killing-simplicity, and the identification with `LieAlgebra.g₂` are not.

* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*, §2.
* R. D. Schafer, *An Introduction to Nonassociative Algebras*, Ch. III, where the skewness of a
  derivation of a composition algebra for its norm form is Lemma 3.4.
-/

public section

namespace TauCeti

namespace Octonion

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} [CommRing R] (D : derivationLieAlgebra R (Octonion R))

/-! ### The key identity -/

/-- Conjugation as a reflection in the trace: `conj x = tr x · 1 - x`, the form of
`TauCeti.Octonion.add_conj` a derivation is applied to. -/
private theorem conj_eq_trace_smul_one_sub (x : Octonion R) :
    conj x = trace x • (1 : Octonion R) - x := by
  rw [← add_conj]
  abel

/-- **A derivation negates conjugated inputs.** It kills `1` and conjugation is the reflection
`x ↦ tr x · 1 - x`, so `D (conj x) = -D x`. Once the values of `D` are known to have vanishing
trace this
upgrades to `TauCeti.Octonion.derivation_apply_conj`, the statement that `D` commutes with
conjugation; that is the form to use, and this one is what proves it. -/
theorem derivation_apply_conj_eq_neg (x : Octonion R) :
    (D : Module.End R (Octonion R)) (conj x) = -(D : Module.End R (Octonion R)) x := by
  rw [conj_eq_trace_smul_one_sub, map_sub, map_smul,
    derivationLieAlgebra.apply_one_eq_zero, smul_zero, zero_sub]

/-- **The identity everything below comes from**: `tr (D x) · x = ⟨x, D x⟩ · 1`.

Applying `D` to the rank-two equation `x² = tr x · x - N x · 1` gives
`D x · x + x · D x = tr x · D x`,
and the polarization `x * conj y + y * conj x = ⟨x, y⟩ · 1` of the norm at `y = D x`, with both
conjugates
rewritten as reflections in the trace, gives
`tr (D x) · x + tr x · D x - (x · D x + D x · x) = ⟨x, D x⟩ · 1`. Substituting the first into the
second is the statement. -/
private theorem trace_derivation_smul_eq_polar_smul_one (x : Octonion R) :
    trace ((D : Module.End R (Octonion R)) x) • x
      = QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) x) •
        (1 : Octonion R) := by
  set d := (D : Module.End R (Octonion R)) x with hd
  have h₁ : d * x + x * d = trace x • d := by
    have h := derivationLieAlgebra.leibniz D x x
    rw [mul_self, map_sub, map_smul, map_smul, derivationLieAlgebra.apply_one_eq_zero, smul_zero,
      sub_zero, ← hd] at h
    exact h.symm
  have h₂ := mul_conj_add_mul_conj x d
  rw [conj_eq_trace_smul_one_sub d, conj_eq_trace_smul_one_sub x, mul_sub, mul_sub,
    mul_smul_comm, mul_one, mul_smul_comm, mul_one] at h₂
  have h₃ : trace d • x + (trace x • d - (d * x + x * d))
      = QuadraticMap.polar (normQuadraticForm R) x d • (1 : Octonion R) := by
    rw [← h₂]; abel
  rwa [h₁, sub_self, add_zero] at h₃

/-- The polarization of `TauCeti.Octonion.trace_derivation_smul_eq_polar_smul_one`: the identity is
quadratic in `x`, and this is its associated bilinear form. -/
private theorem trace_derivation_smul_add_smul (x y : Octonion R) :
    trace ((D : Module.End R (Octonion R)) x) • y + trace ((D : Module.End R (Octonion R)) y) • x
      = (QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) y) +
          QuadraticMap.polar (normQuadraticForm R) y ((D : Module.End R (Octonion R)) x)) •
        (1 : Octonion R) := by
  have hx := trace_derivation_smul_eq_polar_smul_one D x
  have hy := trace_derivation_smul_eq_polar_smul_one D y
  have h := trace_derivation_smul_eq_polar_smul_one D (x + y)
  have hL : trace ((D : Module.End R (Octonion R)) (x + y)) • (x + y)
      = trace ((D : Module.End R (Octonion R)) x) • x +
          trace ((D : Module.End R (Octonion R)) y) • y +
          (trace ((D : Module.End R (Octonion R)) x) • y +
            trace ((D : Module.End R (Octonion R)) y) • x) := by
    rw [map_add, map_add]
    module
  have hR : QuadraticMap.polar (normQuadraticForm R) (x + y)
        ((D : Module.End R (Octonion R)) (x + y))
      = QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) x) +
          QuadraticMap.polar (normQuadraticForm R) y ((D : Module.End R (Octonion R)) y) +
          (QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) y) +
            QuadraticMap.polar (normQuadraticForm R) y ((D : Module.End R (Octonion R)) x)) := by
    rw [map_add, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_add_right]
    ring
  rw [hL, hR, hx, hy] at h
  have h' : trace ((D : Module.End R (Octonion R)) x) • y +
        trace ((D : Module.End R (Octonion R)) y) • x
      = (QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) x) +
          QuadraticMap.polar (normQuadraticForm R) y ((D : Module.End R (Octonion R)) y) +
          (QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) y) +
            QuadraticMap.polar (normQuadraticForm R) y ((D : Module.End R (Octonion R)) x))) •
          (1 : Octonion R)
        - QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) x) •
          (1 : Octonion R)
        - QuadraticMap.polar (normQuadraticForm R) y ((D : Module.End R (Octonion R)) y) •
          (1 : Octonion R) := by
    rw [← h]; abel
  rw [h']
  module

/-- The two coordinate extractions the argument needs. The diagonal idempotent `⟨1, 0, 0, 0⟩` and
the unit `1 = ⟨1, 1, 0, 0⟩` differ in their second diagonal entry, so an equation between multiples
of them forces both multipliers to vanish. -/
private theorem eq_zero_and_eq_zero_of_smul_diagIdempotent {r c : R}
    (h : r • (⟨1, 0, 0, 0⟩ : Octonion R) = c • (1 : Octonion R)) : r = 0 ∧ c = 0 := by
  have ha := congrArg Octonion.a h
  have hb := congrArg Octonion.b h
  simp only [smul_a, smul_b, one_a, one_b, smul_eq_mul, mul_one, mul_zero] at ha hb
  exact ⟨ha.trans hb.symm, hb.symm⟩

/-! ### Derivations are imaginary-valued and skew -/

/-- **A derivation of `𝕆` has values of trace `0`.**

Evaluating the key identity `tr (D x) · x = ⟨x, D x⟩ · 1` at the diagonal idempotent `e` gives
`tr (D e) = 0`, because the two sides have different second diagonal entries; polarizing the
identity and putting `e` in the second slot then gives `tr (D x) · e = ⟨x, D e⟩ + ⟨e, D x⟩ · 1` for
arbitrary `x`, and the same entry comparison finishes. Not a `simp` lemma, because
`TauCeti.Octonion.trace_apply` already takes its left-hand side apart. -/
theorem trace_derivation_apply_eq_zero (x : Octonion R) :
    trace ((D : Module.End R (Octonion R)) x) = 0 := by
  obtain ⟨he, -⟩ := eq_zero_and_eq_zero_of_smul_diagIdempotent
    (trace_derivation_smul_eq_polar_smul_one D ⟨1, 0, 0, 0⟩)
  have h := trace_derivation_smul_add_smul D x ⟨1, 0, 0, 0⟩
  rw [he, zero_smul, add_zero] at h
  exact (eq_zero_and_eq_zero_of_smul_diagIdempotent h).1

/-- **A derivation of `𝕆` takes imaginary values**, that is
`TauCeti.Octonion.trace_derivation_apply_eq_zero` read through the definition of the imaginary
octonions as the kernel of the trace. In particular the imaginary octonions are stable under `D`;
that is `TauCeti.Octonion.imaginaryLieSubmodule`. Not a `simp` lemma, because
`TauCeti.Octonion.mem_imaginary` and `TauCeti.Octonion.trace_apply` already take its left-hand side
apart, for the same reason as `TauCeti.Octonion.trace_derivation_apply_eq_zero`. -/
theorem derivation_apply_mem_imaginary (x : Octonion R) :
    (D : Module.End R (Octonion R)) x ∈ imaginary R :=
  mem_imaginary.mpr (trace_derivation_apply_eq_zero D x)

/-- **A derivation commutes with conjugation.** Conjugation negates the imaginary octonions and the
values of `D` are imaginary, so the sign in
`TauCeti.Octonion.derivation_apply_conj_eq_neg` is the one conjugation itself supplies. -/
@[simp]
theorem derivation_apply_conj (x : Octonion R) :
    (D : Module.End R (Octonion R)) (conj x) = conj ((D : Module.End R (Octonion R)) x) := by
  rw [derivation_apply_conj_eq_neg,
    mem_imaginary_iff_conj_eq_neg.mp (derivation_apply_mem_imaginary D x)]

/-- **A derivation is skew for the norm form**, in the quadratic form of that statement:
`⟨x, D x⟩ = 0`. This is the key identity once its left-hand side is known to vanish, and it is the
infinitesimal norm-preservation statement `d/dt|₀ N (x + t • D x) = 0`. -/
@[simp]
theorem polar_derivation_apply_self_eq_zero (x : Octonion R) :
    QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) x) = 0 := by
  have h := trace_derivation_smul_eq_polar_smul_one D x
  rw [trace_derivation_apply_eq_zero, zero_smul] at h
  have ha := congrArg Octonion.a h.symm
  simpa using ha

/-- **A derivation is skew for the norm form**: `⟨D x, y⟩ = -⟨x, D y⟩`, the bilinear form of
`TauCeti.Octonion.polar_derivation_apply_self_eq_zero`. Packaged as an inclusion of Lie subalgebras
this is `TauCeti.Octonion.derivationLieAlgebra_le_skewAdjointLieSubalgebra`. -/
theorem polar_derivation_apply_left_eq_neg (x y : Octonion R) :
    QuadraticMap.polar (normQuadraticForm R) ((D : Module.End R (Octonion R)) x) y
      = -QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) y) := by
  have h := polar_derivation_apply_self_eq_zero D (x + y)
  rw [map_add, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
    QuadraticMap.polar_add_right, polar_derivation_apply_self_eq_zero,
    polar_derivation_apply_self_eq_zero, zero_add, add_zero] at h
  rw [QuadraticMap.polar_comm]
  exact eq_neg_of_add_eq_zero_right h

/-- **`Der 𝕆 ≤ 𝔰𝔬(N)`**: every derivation of the split octonions is skew-adjoint for the symmetric
bilinear form of the norm, so the derivation algebra is a Lie subalgebra of the orthogonal Lie
algebra of that form. This is the inclusion `Der 𝕆 ↪ 𝔰𝔬(N)` that the dimension count of `Der 𝕆`
runs through; once `Der 𝕆` is identified with `G₂` — which is not done here — it becomes the
familiar `G₂ ↪ 𝔰𝔬₈`. -/
theorem derivationLieAlgebra_le_skewAdjointLieSubalgebra (R : Type*) [CommRing R] :
    derivationLieAlgebra R (Octonion R)
      ≤ skewAdjointLieSubalgebra (QuadraticMap.polarBilin (normQuadraticForm R)) := by
  intro D hD
  -- Membership in the bundled Lie subalgebra is membership in the skew-adjoint submodule it is
  -- built from; crossing that wrapper is what lets the membership lemma below rewrite.
  change D ∈ (QuadraticMap.polarBilin (normQuadraticForm R)).skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro x y
  simpa using polar_derivation_apply_left_eq_neg ⟨D, hD⟩ x y

/-! ### The imaginary octonions as a representation of `Der 𝕆` -/

/-- **The imaginary octonions as a Lie submodule of `𝕆` over `Der 𝕆`.** A derivation takes
imaginary values on all of `𝕆`, so in particular it preserves the imaginary octonions. This is the
carrier of the candidate `7`-dimensional fundamental representation of `G₂`; its dimension is
`TauCeti.Octonion.finrank_imaginary`, reached through
`TauCeti.Octonion.toSubmodule_imaginaryLieSubmodule`. -/
def imaginaryLieSubmodule (R : Type*) [CommRing R] :
    LieSubmodule R (derivationLieAlgebra R (Octonion R)) (Octonion R) where
  __ := imaginary R
  lie_mem {D _} _ := derivation_apply_mem_imaginary D _

@[simp]
theorem toSubmodule_imaginaryLieSubmodule (R : Type*) [CommRing R] :
    (imaginaryLieSubmodule R).toSubmodule = imaginary R :=
  (rfl)

@[simp]
theorem mem_imaginaryLieSubmodule {x : Octonion R} :
    x ∈ imaginaryLieSubmodule R ↔ trace x = 0 :=
  mem_imaginary

/-- **`Der 𝕆` acts faithfully on the imaginary octonions**, so no information is lost by restricting
the derivation algebra to its candidate fundamental representation.

A derivation kills `1`, and `x - conj x` is imaginary with `D (x - conj x) = 2 · D x`, so a
derivation vanishing on the imaginary octonions vanishes outright as soon as scalar multiplication
by `2` on `𝕆` is regular. That regularity is the exact hypothesis the proof uses; the instance
`TauCeti.Octonion.instIsFaithfulImaginaryLieSubmodule` supplies it from typeclasses. -/
theorem isFaithful_imaginaryLieSubmodule (h2 : IsSMulRegular (Octonion R) (2 : R)) :
    LieModule.IsFaithful R (derivationLieAlgebra R (Octonion R))
      (imaginaryLieSubmodule R) := by
  rw [LieModule.isFaithful_iff']
  intro D hD
  refine derivationLieAlgebra.ext fun x => ?_
  have hx : x - conj x ∈ imaginaryLieSubmodule R := by simp
  have h := congrArg (Subtype.val) (hD ⟨x - conj x, hx⟩)
  rw [LieSubmodule.coe_bracket] at h
  simp only [LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply, map_sub,
    derivation_apply_conj_eq_neg, sub_neg_eq_add, ZeroMemClass.coe_zero] at h
  have h₂ : (2 : R) • (D : Module.End R (Octonion R)) x = 0 := by
    rw [two_smul]
    exact h
  simp [h2.right_eq_zero_of_smul h₂]

/-- **`Der 𝕆` acts faithfully on the imaginary octonions** over a base for which `2` is a nonzero
scalar acting without zero divisors, the typeclass form of
`TauCeti.Octonion.isFaithful_imaginaryLieSubmodule`. -/
instance instIsFaithfulImaginaryLieSubmodule [NoZeroSMulDivisors R (Octonion R)]
    [NeZero (2 : R)] :
    LieModule.IsFaithful R (derivationLieAlgebra R (Octonion R))
      (imaginaryLieSubmodule R) :=
  isFaithful_imaginaryLieSubmodule <| IsSMulRegular.of_right_eq_zero_of_smul fun _ h =>
    (eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left (NeZero.ne (2 : R))

/-! ### An explicit `14`-dimensional family of derivations

Everything above is a statement about an arbitrary derivation, so it is worth knowing that there
are some, and knowing enough of them to see the expected dimension `14` from below. Three families
are built here, and they match the three degrees of the `ℤ/3`-grading that the Zorn model puts on
`𝕆`: writing `V = R³` for the top-right vector entry and `V*` for the bottom-left one,
`𝕆 = (R e ⊕ R f) ⊕ V ⊕ V*` with `V · V ⊆ V*`, `V* · V* ⊆ V` and `V · V* ⊆ R e`, and `Der 𝕆` is
expected to inherit that grading as `𝔰𝔩₃ ⊕ V ⊕ V*`, of dimension `8 + 3 + 3 = 14`. Only the three
embeddings are built here, not the decomposition.

* `SL₃` acts on the Zorn vector matrices by `⟨a, b, v, w⟩ ↦ ⟨a, b, A v, (Aᵀ)⁻¹ w⟩`; differentiating
  at the identity along a traceless `A` gives `TauCeti.Octonion.slDerivation`, a homomorphism of
  Lie algebras `𝔰𝔩₃ → Der 𝕆` in degree `0`.
* `TauCeti.Octonion.vectorDerivation` and `TauCeti.Octonion.covectorDerivation` are the two
  off-diagonal families. Their formulas are not a choice but the outcome of a computation: a
  derivation of degree `1` is pinned by its value `c ∈ V` on the idempotent `e = ⟨1, 0, 0, 0⟩`,
  because `D f = -D e` and the products `e v = v`, `f w = w`, `v w' = (v ⬝ᵥ w') e` then read off
  `D` on `V` and on `V*` in turn; the same computation in degree `2` gives `covectorDerivation`.

That computation is how the formulas were found and is not itself formalized. What is proved here
is that the three families do consist of derivations, and that they are independent. Evaluation at
`e` settles the two off-diagonal families at once, since `slDerivation A` vanishes at `e` while
`vectorDerivation c` and `covectorDerivation d` give `⟨0, 0, c, 0⟩` and `⟨0, 0, 0, -d⟩`; for the
same reason it says nothing about `A`, which a second evaluation, on the vector entries, then
pins down. That the three families *exhaust* `Der 𝕆`, which is the other half of
`finrank (Der 𝕆) = 14`, is not proved here. -/

section Matrices

open Matrix

/-- The endomorphism underlying `TauCeti.Octonion.slDerivation`: a matrix acts on the top-right
vector entry and minus its transpose on the bottom-left one. -/
private def slDerivationEnd (A : Matrix (Fin 3) (Fin 3) R) : Module.End R (Octonion R) where
  toFun x := ⟨0, 0, A *ᵥ x.v, -(Aᵀ *ᵥ x.w)⟩
  map_add' x y := by
    refine Octonion.ext ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [mulVec_add]
    · simp [mulVec_add]
      abel
  map_smul' c x := by
    refine Octonion.ext ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [mulVec_smul]
    · simp [mulVec_smul]

/-- **A traceless matrix acts by a derivation.** On the two scalar entries the Leibniz rule is
`Matrix.dotProduct_transpose_mulVec`, and on the two vector entries it is the traceless
Cauchy--Binet relation `TauCeti.transpose_mulVec_crossProduct`; tracelessness is used exactly
there, and nowhere else. -/
private theorem slDerivationEnd_mem {A : Matrix (Fin 3) (Fin 3) R} (hA : A.trace = 0) :
    slDerivationEnd A ∈ derivationLieAlgebra R (Octonion R) := by
  rw [mem_derivationLieAlgebra]
  intro x y
  have hv := transpose_mulVec_crossProduct (B := Aᵀ) (by rwa [trace_transpose]) x.w y.w
  rw [transpose_transpose] at hv
  have hw := transpose_mulVec_crossProduct hA x.v y.v
  refine Octonion.ext ?_ ?_ ?_ ?_ <;>
    simp only [slDerivationEnd, LinearMap.coe_mk, AddHom.coe_mk, add_a, add_b, add_v, add_w,
      mul_a, mul_b, mul_v, mul_w, mulVec_add, mulVec_sub, mulVec_smul,
      map_neg, LinearMap.neg_apply, zero_mul, mul_zero, zero_add, add_zero,
      zero_smul, dotProduct_neg, neg_dotProduct, neg_add_rev]
  · rw [dotProduct_comm (A *ᵥ x.v) y.w, ← dotProduct_transpose_mulVec]; ring
  · rw [dotProduct_comm (Aᵀ *ᵥ x.w) y.v, dotProduct_transpose_mulVec]; ring
  · rw [hv]; module
  · rw [hw]; module

/-- **`𝔰𝔩₃` acts on the split octonions by derivations**, the degree-`0` family in `Der 𝕆`: a
traceless `3 × 3` matrix acts on the top-right vector entry of a Zorn vector matrix and minus its
transpose on the bottom-left one, and this is a homomorphism of Lie algebras. It is injective
(`TauCeti.Octonion.slDerivation_injective`), so `Der 𝕆` contains a copy of `𝔰𝔩₃`. -/
def slDerivation :
    LieAlgebra.SpecialLinear.sl (Fin 3) R →ₗ⁅R⁆ derivationLieAlgebra R (Octonion R) where
  toFun A := ⟨slDerivationEnd (A : Matrix (Fin 3) (Fin 3) R), slDerivationEnd_mem A.2⟩
  map_add' A B := Subtype.ext <| LinearMap.ext fun x => by
    refine Octonion.ext ?_ ?_ ?_ ?_
    · simp [slDerivationEnd]
    · simp [slDerivationEnd]
    · simp [slDerivationEnd, add_mulVec]
    · simp [slDerivationEnd, transpose_add, add_mulVec]
      abel
  map_smul' r A := Subtype.ext <| LinearMap.ext fun x => by
    refine Octonion.ext ?_ ?_ ?_ ?_
    · simp [slDerivationEnd]
    · simp [slDerivationEnd]
    · simp [slDerivationEnd, smul_mulVec]
    · simp [slDerivationEnd, smul_mulVec]
  map_lie' {A B} := Subtype.ext <| LinearMap.ext fun x => by
    refine Octonion.ext ?_ ?_ ?_ ?_
    · simp [slDerivationEnd]
    · simp [slDerivationEnd]
    · simp [slDerivationEnd, Ring.lie_def, sub_mulVec]
    · simp [slDerivationEnd, Ring.lie_def, sub_mulVec, transpose_sub, transpose_mul, mulVec_neg]

@[simp]
theorem slDerivation_apply (A : LieAlgebra.SpecialLinear.sl (Fin 3) R) (x : Octonion R) :
    (slDerivation A : Module.End R (Octonion R)) x =
      ⟨0, 0, (A : Matrix (Fin 3) (Fin 3) R) *ᵥ x.v, -((A : Matrix (Fin 3) (Fin 3) R)ᵀ *ᵥ x.w)⟩ :=
  (rfl)

/-- The endomorphism underlying `TauCeti.Octonion.vectorDerivation`. -/
private def vectorDerivationEnd (c : Fin 3 → R) : Module.End R (Octonion R) where
  toFun x := ⟨-(c ⬝ᵥ x.w), c ⬝ᵥ x.w, (x.a - x.b) • c, c ⨯₃ x.v⟩
  map_add' x y := by
    refine Octonion.ext ?_ ?_ ?_ ?_
    · simp
      ring
    · simp
    · simp
      module
    · simp
  map_smul' r x := by
    refine Octonion.ext ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
      module
    · simp

/-- The action of `TauCeti.Octonion.vectorDerivationEnd`, so that its Leibniz-rule proof can name
the four entries instead of reshaping the goal by definitional equality. -/
private theorem vectorDerivationEnd_apply (c : Fin 3 → R) (x : Octonion R) :
    vectorDerivationEnd c x = ⟨-(c ⬝ᵥ x.w), c ⬝ᵥ x.w, (x.a - x.b) • c, c ⨯₃ x.v⟩ :=
  (rfl)

/-- The endomorphism underlying `TauCeti.Octonion.covectorDerivation`. Its top-right entry is
written `x.w ⨯₃ d` rather than the more symmetric `-(d ⨯₃ x.w)` because Mathlib's
`Matrix.cross_anticomm` normalizes it that way. -/
private def covectorDerivationEnd (d : Fin 3 → R) : Module.End R (Octonion R) where
  toFun x := ⟨d ⬝ᵥ x.v, -(d ⬝ᵥ x.v), x.w ⨯₃ d, (x.b - x.a) • d⟩
  map_add' x y := by
    refine Octonion.ext ?_ ?_ ?_ ?_
    · simp
    · simp
      ring
    · simp
    · simp
      module
  map_smul' r x := by
    refine Octonion.ext ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp
      module

/-- The action of `TauCeti.Octonion.covectorDerivationEnd`, the mirror of
`TauCeti.Octonion.vectorDerivationEnd_apply`. -/
private theorem covectorDerivationEnd_apply (d : Fin 3 → R) (x : Octonion R) :
    covectorDerivationEnd d x = ⟨d ⬝ᵥ x.v, -(d ⬝ᵥ x.v), x.w ⨯₃ d, (x.b - x.a) • d⟩ :=
  (rfl)

end Matrices

section Coordinates

open Matrix

attribute [local simp] vec3_dotProduct cross_apply Matrix.vecHead Matrix.vecTail

/-- **The degree-`1` endomorphisms are derivations.** Every entry of the Leibniz rule is a
polynomial identity in the eight coordinates of each factor and the three of `c`; the scalar
entries turn on the antisymmetry `v ⬝ᵥ (c ⨯₃ v') = -c ⬝ᵥ (v ⨯₃ v')` of the triple product and the
vector entries on the Grassmann expansion of an iterated cross product. -/
private theorem vectorDerivationEnd_mem (c : Fin 3 → R) :
    vectorDerivationEnd c ∈ derivationLieAlgebra R (Octonion R) := by
  rw [mem_derivationLieAlgebra]
  intro x y
  refine Octonion.ext ?_ ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp [vectorDerivationEnd_apply]
    ring
  · simp [vectorDerivationEnd_apply]
    ring
  · fin_cases i <;> (simp [vectorDerivationEnd_apply]; ring)
  · fin_cases i <;> (simp [vectorDerivationEnd_apply]; ring)

/-- **The degree-`2` endomorphisms are derivations**, by the computation of
`TauCeti.Octonion.vectorDerivationEnd_mem` with the two vector entries exchanged. -/
private theorem covectorDerivationEnd_mem (d : Fin 3 → R) :
    covectorDerivationEnd d ∈ derivationLieAlgebra R (Octonion R) := by
  rw [mem_derivationLieAlgebra]
  intro x y
  refine Octonion.ext ?_ ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp [covectorDerivationEnd_apply]
    ring
  · simp [covectorDerivationEnd_apply]
    ring
  · fin_cases i <;> (simp [covectorDerivationEnd_apply]; ring)
  · fin_cases i <;> (simp [covectorDerivationEnd_apply]; ring)

end Coordinates

section Graded

open Matrix

/-- **The degree-`1` derivations of `𝕆`**, indexed by their value `c` on the diagonal idempotent
`e = ⟨1, 0, 0, 0⟩`: the derivation sending `e` to `⟨0, 0, c, 0⟩`, the top-right vector entry into
the bottom-left one by `v ↦ c ⨯₃ v`, and the bottom-left entry back to the diagonal by
`w ↦ (c ⬝ᵥ w) • (f - e)`. It is injective
(`TauCeti.Octonion.vectorDerivation_injective`). -/
def vectorDerivation : (Fin 3 → R) →ₗ[R] derivationLieAlgebra R (Octonion R) where
  toFun c := ⟨vectorDerivationEnd c, vectorDerivationEnd_mem c⟩
  map_add' c c' := Subtype.ext <| LinearMap.ext fun x => by
    refine Octonion.ext ?_ ?_ ?_ ?_
    · simp [vectorDerivationEnd]
      ring
    · simp [vectorDerivationEnd]
    · simp [vectorDerivationEnd]
    · simp [vectorDerivationEnd]
  map_smul' r c := Subtype.ext <| LinearMap.ext fun x => by
    refine Octonion.ext ?_ ?_ ?_ ?_
    · simp [vectorDerivationEnd]
    · simp [vectorDerivationEnd]
    · simp [vectorDerivationEnd]
      module
    · simp [vectorDerivationEnd]

/-- **The degree-`2` derivations of `𝕆`**, the mirror image of `TauCeti.Octonion.vectorDerivation`
across the diagonal of a Zorn vector matrix: the derivation sending `e` to `⟨0, 0, 0, -d⟩`. It is
injective (`TauCeti.Octonion.covectorDerivation_injective`). -/
def covectorDerivation : (Fin 3 → R) →ₗ[R] derivationLieAlgebra R (Octonion R) where
  toFun d := ⟨covectorDerivationEnd d, covectorDerivationEnd_mem d⟩
  map_add' d d' := Subtype.ext <| LinearMap.ext fun x => by
    refine Octonion.ext ?_ ?_ ?_ ?_
    · simp [covectorDerivationEnd]
    · simp [covectorDerivationEnd]
      ring
    · simp [covectorDerivationEnd]
    · simp [covectorDerivationEnd]
  map_smul' r d := Subtype.ext <| LinearMap.ext fun x => by
    refine Octonion.ext ?_ ?_ ?_ ?_
    · simp [covectorDerivationEnd]
    · simp [covectorDerivationEnd]
    · simp [covectorDerivationEnd]
    · simp [covectorDerivationEnd]
      module

@[simp]
theorem vectorDerivation_apply (c : Fin 3 → R) (x : Octonion R) :
    (vectorDerivation c : Module.End R (Octonion R)) x =
      ⟨-(c ⬝ᵥ x.w), c ⬝ᵥ x.w, (x.a - x.b) • c, c ⨯₃ x.v⟩ :=
  (rfl)

@[simp]
theorem covectorDerivation_apply (d : Fin 3 → R) (x : Octonion R) :
    (covectorDerivation d : Module.End R (Octonion R)) x =
      ⟨d ⬝ᵥ x.v, -(d ⬝ᵥ x.v), x.w ⨯₃ d, (x.b - x.a) • d⟩ :=
  (rfl)

/-- **The three graded families together**, `𝔰𝔩₃ ⊕ V ⊕ V* → Der 𝕆`. It is a map of `R`-modules and
not of Lie algebras: the source is a direct sum of modules, carrying no bracket that pairs its two
off-diagonal summands with each other. Its injectivity
(`TauCeti.Octonion.gradedDerivation_injective`) is what bounds `Der 𝕆` from below. -/
def gradedDerivation :
    (LieAlgebra.SpecialLinear.sl (Fin 3) R × (Fin 3 → R) × (Fin 3 → R)) →ₗ[R]
      derivationLieAlgebra R (Octonion R) :=
  (slDerivation (R := R) : LieAlgebra.SpecialLinear.sl (Fin 3) R →ₗ⁅R⁆
      derivationLieAlgebra R (Octonion R)).toLinearMap.coprod
    (vectorDerivation.coprod covectorDerivation)

@[simp]
theorem gradedDerivation_apply (A : LieAlgebra.SpecialLinear.sl (Fin 3) R) (c d : Fin 3 → R) :
    gradedDerivation (A, c, d) = slDerivation A + (vectorDerivation c + covectorDerivation d) :=
  (rfl)

/-- **The three graded families are independent.** Evaluating at the diagonal idempotent
`e = ⟨1, 0, 0, 0⟩` reads off `c` from the top-right entry and `-d` from the bottom-left one, since
`slDerivation A` kills `e`; with those gone, evaluating `slDerivation A` at `⟨0, 0, u, 0⟩` says
`A u = 0` for every `u`. -/
theorem gradedDerivation_injective : Function.Injective (gradedDerivation (R := R)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨A, c, d⟩ h
  have key : ∀ x : Octonion R,
      (slDerivation A : Module.End R (Octonion R)) x
        + ((vectorDerivation c : Module.End R (Octonion R)) x
          + (covectorDerivation d : Module.End R (Octonion R)) x) = 0 := by
    intro x
    have hx := congrArg (fun D : derivationLieAlgebra R (Octonion R) =>
      (D : Module.End R (Octonion R)) x) h
    simpa using hx
  have he := key ⟨1, 0, 0, 0⟩
  have hc : c = 0 := by simpa using congrArg Octonion.v he
  have hd : d = 0 := by simpa using congrArg Octonion.w he
  subst hc
  subst hd
  have hA : A = 0 := by
    refine Subtype.ext (Matrix.ext_of_mulVec_single fun j => ?_)
    rw [ZeroMemClass.coe_zero, Matrix.zero_mulVec]
    simpa using congrArg Octonion.v (key ⟨0, 0, Pi.single j 1, 0⟩)
  simp [hA]

/-- **`Der 𝕆` contains a copy of `𝔰𝔩₃`**, the one-family case of
`TauCeti.Octonion.gradedDerivation_injective`. -/
theorem slDerivation_injective :
    Function.Injective (slDerivation (R := R)) := fun A B h =>
  congrArg Prod.fst <| gradedDerivation_injective (a₁ := (A, 0, 0)) (a₂ := (B, 0, 0)) <| by
    simp [h]

/-- **`Der 𝕆` contains the degree-`1` copy of `R³`**, the one-family case of
`TauCeti.Octonion.gradedDerivation_injective`. -/
theorem vectorDerivation_injective :
    Function.Injective (vectorDerivation (R := R)) := fun c c' h =>
  congrArg (fun p => p.2.1) <|
    gradedDerivation_injective (a₁ := (0, c, 0)) (a₂ := (0, c', 0)) <| by simp [h]

/-- **`Der 𝕆` contains the degree-`2` copy of `R³`**, the one-family case of
`TauCeti.Octonion.gradedDerivation_injective`. -/
theorem covectorDerivation_injective :
    Function.Injective (covectorDerivation (R := R)) := fun d d' h =>
  congrArg (fun p => p.2.2) <|
    gradedDerivation_injective (a₁ := (0, 0, d)) (a₂ := (0, 0, d')) <| by simp [h]

/-- **`Der 𝕆` is at least `14`-dimensional** over a field, the half of `finrank (Der 𝕆) = 14` that
an explicit supply of derivations gives: `8 = 3 ^ 2 - 1` from `𝔰𝔩₃` (`TauCeti.finrank_sl`) and
`3 + 3` from the two off-diagonal families. The matching upper bound — that these `14` derivations
are *all* of them — is not proved here. -/
theorem fourteen_le_finrank_derivationLieAlgebra (K : Type*) [Field K] :
    14 ≤ Module.finrank K (derivationLieAlgebra K (Octonion K)) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := gradedDerivation (R := K)) gradedDerivation_injective
  rw [Module.finrank_prod, Module.finrank_prod, finrank_sl, Fintype.card_fin,
    Module.finrank_fin_fun] at h
  omega

/-- **`𝕆` has nonzero derivations**, so the derivation algebra whose skewness the rest of this file
establishes is not the zero Lie algebra. The witness is the degree-`1` derivation attached to
`(1, 0, 0)`, which sends the diagonal idempotent `⟨1, 0, 0, 0⟩` to `⟨0, 0, (1, 0, 0), 0⟩`. -/
instance instNontrivialDerivationLieAlgebra [Nontrivial R] :
    Nontrivial (derivationLieAlgebra R (Octonion R)) := by
  refine ⟨vectorDerivation ![1, 0, 0], 0, fun h => ?_⟩
  have h₁ := congrArg (fun D : derivationLieAlgebra R (Octonion R) =>
    ((D : Module.End R (Octonion R)) ⟨1, 0, 0, 0⟩).v 0) h
  simp at h₁

end Graded

end Octonion

end TauCeti

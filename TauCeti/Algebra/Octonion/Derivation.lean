/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.SkewAdjoint
public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.Algebra.Octonion.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Lie.GeneralLinear.Finrank
import TauCeti.LinearAlgebra.Matrix.CrossProduct

/-!
# Derivations of the split octonions

`G₂` is the derivation algebra of the split octonions, and its fundamental representation is
supposed to be the `7`-dimensional space of imaginary octonions. Neither statement can even be made
until one knows that a derivation of `𝕆` lands in the imaginary octonions and respects the norm
form; that is what this file proves first. It then writes down fourteen independent derivations
and shows that there are no others, so that `Der 𝕆 ≅ 𝔰𝔩₃ × R³ × R³` and `finrank (Der 𝕆) = 14`.

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
octonions are a Lie submodule (`TauCeti.Octonion.imaginaryLieSubmodule`) — over a field in which
`2` is nonzero this is the `7`-dimensional fundamental representation — and `Der 𝕆` acts faithfully
on it over every commutative ring. Indeed, the diagonal idempotent `e` is a product of two
imaginary vector matrices, and `𝕆 = R · e ⊕ Im 𝕆`, so a derivation vanishing on `Im 𝕆` vanishes on
all of `𝕆`.

The derivations exhibited here come from the action of `SL₃` on a Zorn vector matrix,
`⟨a, b, v, w⟩ ↦ ⟨a, b, A v, (Aᵀ)⁻¹ w⟩`, differentiated at the identity: a trace-zero matrix `M`
acts by `M` on the upper vector entry and by `-Mᵀ` on the lower one
(`TauCeti.Octonion.slDerivation`), and this is a homomorphism of Lie algebras `𝔰𝔩₃ → Der 𝕆`. The
Leibniz rule for it is the identity `(M u) ⨯₃ w + u ⨯₃ (M w) = -(Mᵀ (u ⨯₃ w))`, valid exactly
because `M` has trace zero
(`Matrix.mulVec_cross_add_cross_mulVec_of_trace_eq_zero`). Two further three-parameter families
(`TauCeti.Octonion.upperDerivation` and `TauCeti.Octonion.lowerDerivation`) are attached to a
vector `u`, are read off the idempotent `⟨1, 0, 0, 0⟩`, and exchange the two vector entries; there
they are the two nonzero pieces of the `ℤ/3`-grading of `𝕆` by scalar diagonal, upper vector and
lower vector. That grading is visible in the five brackets between the three families: `𝔰𝔩₃` acts
on the upper family by its defining representation and on the lower one by the dual, two upper or
two lower derivations bracket into the opposite vector family by twice the cross product, and an
upper against a lower one brackets back into `𝔰𝔩₃` through `TauCeti.Octonion.slOfVectors`.
Together the three families depend on `8 + 3 + 3 = 14` independent parameters, so
`14 ≤ finrank (Der 𝕆)`.

Conversely every derivation `D` is in the family, over any commutative ring. Its value at the
idempotent `e = ⟨1, 0, 0, 0⟩` has vanishing diagonal entries, so subtracting the upper and the lower
derivation attached to its two vector entries leaves a derivation `E` that kills `e`. Such an `E`
respects the Peirce decomposition of `𝕆` relative to `e`: differentiating `e x = x` and `x e = 0`
for an upper vector matrix `x` (and their mirrors for a lower one) shows that `E` acts on the upper
entry by some matrix `M`, on the lower entry by some matrix `N`, and kills the diagonal. The product
of an upper and a lower vector matrix is diagonal, which forces `N = -Mᵀ`, and the product of two
upper ones is the lower cross product, which by `Matrix.mulVec_cross_add_cross_mulVec` forces
`trace M = 0`. So `E = slDerivation M`, and `TauCeti.Octonion.tripleEquivDerivationLieAlgebra`
packages `TauCeti.Octonion.derivationOfTriple` as a linear equivalence.

## Main definitions

* `TauCeti.Octonion.imaginaryLieSubmodule`: the imaginary octonions as a Lie submodule of `𝕆` over
  `Der 𝕆`, so that `Im 𝕆` is a representation of `Der 𝕆`.
* `TauCeti.Octonion.slDerivation`: the homomorphism of Lie algebras `𝔰𝔩₃ → Der 𝕆`, the
  differentiated action of `SL₃` on the vector entries of a Zorn vector matrix.
* `TauCeti.Octonion.upperDerivation` and `TauCeti.Octonion.lowerDerivation`: the two
  three-parameter families of derivations attached to a vector.
* `TauCeti.Octonion.derivationOfTriple`: the three families assembled into one linear map out of
  `𝔰𝔩₃ × R³ × R³`.
* `TauCeti.Octonion.slOfVectors`: the trace-zero matrix through which an upper and a lower vector
  derivation bracket back into `𝔰𝔩₃`.
* `TauCeti.Octonion.tripleEquivDerivationLieAlgebra`: the linear equivalence
  `𝔰𝔩₃ × R³ × R³ ≃ Der 𝕆` given by the three families.

## Main results

* `TauCeti.Octonion.trace_derivation_apply_eq_zero`: a derivation of `𝕆` has values of trace `0`, so
  (`TauCeti.Octonion.derivation_apply_mem_imaginary`) its image lies in the imaginary octonions.
* `TauCeti.Octonion.derivation_apply_conj`: a derivation commutes with conjugation.
* `TauCeti.Octonion.polar_derivation_apply_self_eq_zero` and
  `TauCeti.Octonion.polar_derivation_apply_left_eq_neg`: a derivation is **skew** for the symmetric
  bilinear form of the norm, `⟨D x, y⟩ = -⟨x, D y⟩`.
* `TauCeti.Octonion.derivationLieAlgebra_le_skewAdjointLieSubalgebra`: `Der 𝕆 ≤ 𝔰𝔬(N)`, the
  previous item as an inclusion of Lie subalgebras of `Module.End R 𝕆`.
* `TauCeti.Octonion.isFaithful_imaginaryLieSubmodule`: `Der 𝕆` acts faithfully on `Im 𝕆` over
  every commutative ring; `TauCeti.Octonion.instIsFaithfulImaginaryLieSubmodule` is its instance
  form.
* `TauCeti.Octonion.lie_slDerivation_upperDerivation`,
  `TauCeti.Octonion.lie_slDerivation_lowerDerivation`,
  `TauCeti.Octonion.lie_upperDerivation_upperDerivation`,
  `TauCeti.Octonion.lie_lowerDerivation_lowerDerivation` and
  `TauCeti.Octonion.lie_upperDerivation_lowerDerivation`: the brackets of the three families with
  one another, the relations of the `ℤ/3`-grading.
* `TauCeti.Octonion.derivationOfTriple_injective`: the fourteen parameters are independent.
  In particular `Der 𝕆` is not the zero Lie algebra
  (`TauCeti.Octonion.instNontrivialDerivationLieAlgebra`), so none of the above is vacuous.
* `TauCeti.Octonion.derivationOfTriple_surjective`: every derivation of `𝕆` is in the
  fourteen-parameter family, over any commutative ring.
* `TauCeti.Octonion.finrank_derivationLieAlgebra`: **`finrank (Der 𝕆) = 14`**, the dimension of
  `G₂`, over any commutative ring with the strong rank condition; `Der 𝕆` is moreover free and
  finite as a module.

## Implementation notes

Everything is stated over a commutative ring. The rank count `finrank (Der 𝕆) = 14` asks in
addition for the strong rank condition. Faithfulness needs no further hypothesis on the base ring:
the imaginary vector matrices generate the diagonal idempotent by multiplication. In characteristic
`2`, the imaginary octonions
contain the unit, so its line is a trivial subrepresentation; this obstructs irreducibility but
does not affect faithfulness.

The two coordinate extractions the argument needs — reading the `a` and `b` entries of an equation
between multiples of `⟨1, 0, 0, 0⟩` and of `1` — are isolated in a private lemma, so none of the
public skewness statements is about entries of a vector matrix.

Derivations are taken in the bundled form `D : TauCeti.derivationLieAlgebra R (Octonion R)` of
`TauCeti/Algebra/Lie/Derivation/Basic.lean`, and are applied through the coercion
`(D : Module.End R (Octonion R))`, which is the simp-normal form of their action there.

## References

The type-`G₂` Killing-simplicity of `Der 𝕆` and its identification with `LieAlgebra.g₂` are not
proved here.

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
  linear_combination (norm := module) h₂ + h₁

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
  simp only [map_add, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right] at h
  linear_combination (norm := module) h - hx - hy

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
carrier of the `7`-dimensional fundamental representation of `G₂`; its dimension is
`TauCeti.Octonion.finrank_imaginary`, reached through
`TauCeti.Octonion.toSubmodule_imaginaryLieSubmodule`, and its irreducibility over a field in which
`2` is nonzero is `TauCeti.Octonion.isIrreducible_imaginaryLieSubmodule` in
`TauCeti/Algebra/Octonion/Fundamental.lean`. -/
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

/-- **`Der 𝕆` acts faithfully on the imaginary octonions over every commutative ring**, so no
information is lost by restricting the derivation algebra to its candidate fundamental
representation, including in characteristic `2`. -/
theorem isFaithful_imaginaryLieSubmodule :
    LieModule.IsFaithful R (derivationLieAlgebra R (Octonion R))
      (imaginaryLieSubmodule R) := by
  rw [LieModule.isFaithful_iff']
  intro D hD
  have hzero (x : Octonion R) (hx : x ∈ imaginaryLieSubmodule R) :
      (D : Module.End R (Octonion R)) x = 0 := by
    simpa only [LieSubmodule.coe_bracket, LieSubalgebra.coe_bracket_of_module,
      Module.End.lie_apply, ZeroMemClass.coe_zero] using congrArg Subtype.val (hD ⟨x, hx⟩)
  -- The diagonal idempotent is a product of two imaginary vector matrices.
  have he : (D : Module.End R (Octonion R)) ⟨1, 0, 0, 0⟩ = 0 := by
    have heq : (⟨1, 0, 0, 0⟩ : Octonion R) =
        ⟨0, 0, Pi.single 0 1, 0⟩ * ⟨0, 0, 0, Pi.single 0 1⟩ := by
      ext <;> simp
    rw [heq]
    exact derivationLieAlgebra.apply_mul_eq_zero (hzero _ (by simp)) (hzero _ (by simp))
  refine derivationLieAlgebra.ext fun x => ?_
  -- Subtracting the trace component leaves an imaginary octonion in any characteristic.
  have hx : x - trace x • (⟨1, 0, 0, 0⟩ : Octonion R) ∈ imaginaryLieSubmodule R := by
    simp
  simpa [map_sub, map_smul, he] using hzero _ hx

/-- **`Der 𝕆` acts faithfully on the imaginary octonions** over every commutative ring, the
typeclass form of `TauCeti.Octonion.isFaithful_imaginaryLieSubmodule`. -/
instance instIsFaithfulImaginaryLieSubmodule :
    LieModule.IsFaithful R (derivationLieAlgebra R (Octonion R))
      (imaginaryLieSubmodule R) :=
  isFaithful_imaginaryLieSubmodule

section SpecialLinear

open Matrix

/-! ### The special linear derivations -/

/-- The endomorphism underlying `TauCeti.Octonion.slDerivation`. -/
private def slDerivationEnd (M : Matrix (Fin 3) (Fin 3) R) : Module.End R (Octonion R) where
  toFun x := ⟨0, 0, M *ᵥ x.v, -(Mᵀ *ᵥ x.w)⟩
  map_add' x y := by
    refine Octonion.ext (by simp) (by simp) ?_ ?_ <;>
      simp [Matrix.mulVec_add, add_comm]
  map_smul' c x := by
    refine Octonion.ext (by simp) (by simp) ?_ ?_ <;>
      simp [Matrix.mulVec_smul]

@[simp] private theorem slDerivationEnd_apply_a (M : Matrix (Fin 3) (Fin 3) R) (x : Octonion R) :
    (slDerivationEnd M x).a = 0 := (rfl)

@[simp] private theorem slDerivationEnd_apply_b (M : Matrix (Fin 3) (Fin 3) R) (x : Octonion R) :
    (slDerivationEnd M x).b = 0 := (rfl)

@[simp] private theorem slDerivationEnd_apply_v (M : Matrix (Fin 3) (Fin 3) R) (x : Octonion R) :
    (slDerivationEnd M x).v = M *ᵥ x.v := (rfl)

@[simp] private theorem slDerivationEnd_apply_w (M : Matrix (Fin 3) (Fin 3) R) (x : Octonion R) :
    (slDerivationEnd M x).w = -(Mᵀ *ᵥ x.w) := (rfl)

private theorem slDerivationEnd_mem {M : Matrix (Fin 3) (Fin 3) R} (hM : M.trace = 0) :
    slDerivationEnd M ∈ derivationLieAlgebra R (Octonion R) := by
  rw [mem_derivationLieAlgebra]
  intro x y
  have hMt : Mᵀ.trace = 0 := by rwa [Matrix.trace_transpose]
  have hdot : ∀ (N : Matrix (Fin 3) (Fin 3) R) (u w : Fin 3 → R),
      (N *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Nᵀ *ᵥ w) := fun N u w => by
    rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  have hv : M *ᵥ (x.w ⨯₃ y.w) = -((Mᵀ *ᵥ x.w) ⨯₃ y.w + x.w ⨯₃ (Mᵀ *ᵥ y.w)) := by
    rw [Matrix.mulVec_cross_add_cross_mulVec_of_trace_eq_zero Mᵀ hMt, Matrix.transpose_transpose,
      neg_neg]
  have hw : Mᵀ *ᵥ (x.v ⨯₃ y.v) = -((M *ᵥ x.v) ⨯₃ y.v + x.v ⨯₃ (M *ᵥ y.v)) := by
    rw [Matrix.mulVec_cross_add_cross_mulVec_of_trace_eq_zero M hM, neg_neg]
  refine Octonion.ext ?_ ?_ ?_ ?_
  · simp [hdot M x.v y.w]
  · simp [hdot Mᵀ x.w y.v]
  · simp only [slDerivationEnd_apply_v, slDerivationEnd_apply_a, slDerivationEnd_apply_b,
      slDerivationEnd_apply_w, mul_v, add_v, Matrix.mulVec_sub, Matrix.mulVec_add,
      Matrix.mulVec_smul, zero_smul, map_neg, LinearMap.neg_apply, hv]
    abel
  · simp only [slDerivationEnd_apply_v, slDerivationEnd_apply_a, slDerivationEnd_apply_b,
      slDerivationEnd_apply_w, mul_w, add_w, Matrix.mulVec_add, Matrix.mulVec_smul, zero_smul,
      smul_neg, hw]
    abel

/-! ### The two vector families of derivations -/

section Vector

/- The vector `simp` set, as in `TauCeti/Algebra/Octonion/Basic.lean`: dot and cross products are
pushed through the linear combinations that make up an entry of a product, dot products are
normalised by commutativity, and the compound products that survive are reduced by Mathlib's own
identities -- `Matrix.cross_dot_cross` for a dot product of two cross products,
`Matrix.cross_cross_eq_smul_sub_smul` and its primed form for an iterated one. What is left is a
polynomial in the dot products, which `ring` closes, or a linear combination of the entries and
their cross products, which `module` closes; the triple products that neither identity reaches are
rotated by `Matrix.triple_product_permutation` and `Matrix.cross_anticomm`. -/
attribute [local simp] LinearMap.map_add₂ LinearMap.map_sub₂ LinearMap.map_smul₂
  dotProduct_comm cross_dot_cross cross_cross_eq_smul_sub_smul cross_cross_eq_smul_sub_smul'

/-- The endomorphism underlying `TauCeti.Octonion.upperDerivation`. -/
private def upperDerivationEnd (u : Fin 3 → R) : Module.End R (Octonion R) where
  toFun x := ⟨-(u ⬝ᵥ x.w), u ⬝ᵥ x.w, (x.a - x.b) • u, u ⨯₃ x.v⟩
  map_add' x y := by
    refine Octonion.ext (by simp [add_comm]) (by simp) (funext fun i => ?_) (by simp)
    simp
    ring
  map_smul' c x := by
    refine Octonion.ext (by simp) (by simp) (funext fun i => ?_) (by simp)
    simp
    ring

@[simp] private theorem upperDerivationEnd_apply_a (u : Fin 3 → R) (x : Octonion R) :
    (upperDerivationEnd u x).a = -(u ⬝ᵥ x.w) := (rfl)

@[simp] private theorem upperDerivationEnd_apply_b (u : Fin 3 → R) (x : Octonion R) :
    (upperDerivationEnd u x).b = u ⬝ᵥ x.w := (rfl)

@[simp] private theorem upperDerivationEnd_apply_v (u : Fin 3 → R) (x : Octonion R) :
    (upperDerivationEnd u x).v = (x.a - x.b) • u := (rfl)

@[simp] private theorem upperDerivationEnd_apply_w (u : Fin 3 → R) (x : Octonion R) :
    (upperDerivationEnd u x).w = u ⨯₃ x.v := (rfl)

/-- The endomorphism underlying `TauCeti.Octonion.lowerDerivation`. -/
private def lowerDerivationEnd (t : Fin 3 → R) : Module.End R (Octonion R) where
  toFun x := ⟨-(t ⬝ᵥ x.v), t ⬝ᵥ x.v, t ⨯₃ x.w, (x.a - x.b) • t⟩
  map_add' x y := by
    refine Octonion.ext (by simp [add_comm]) (by simp) (by simp) (funext fun i => ?_)
    simp
    ring
  map_smul' c x := by
    refine Octonion.ext (by simp) (by simp) (by simp) (funext fun i => ?_)
    simp
    ring

@[simp] private theorem lowerDerivationEnd_apply_a (t : Fin 3 → R) (x : Octonion R) :
    (lowerDerivationEnd t x).a = -(t ⬝ᵥ x.v) := (rfl)

@[simp] private theorem lowerDerivationEnd_apply_b (t : Fin 3 → R) (x : Octonion R) :
    (lowerDerivationEnd t x).b = t ⬝ᵥ x.v := (rfl)

@[simp] private theorem lowerDerivationEnd_apply_v (t : Fin 3 → R) (x : Octonion R) :
    (lowerDerivationEnd t x).v = t ⨯₃ x.w := (rfl)

@[simp] private theorem lowerDerivationEnd_apply_w (t : Fin 3 → R) (x : Octonion R) :
    (lowerDerivationEnd t x).w = (x.a - x.b) • t := (rfl)

private theorem upperDerivationEnd_mem (u : Fin 3 → R) :
    upperDerivationEnd u ∈ derivationLieAlgebra R (Octonion R) := by
  rw [mem_derivationLieAlgebra]
  intro x y
  have hdot : x.v ⬝ᵥ (u ⨯₃ y.v) = -(u ⬝ᵥ (x.v ⨯₃ y.v)) := by
    rw [triple_product_permutation, ← cross_anticomm, dotProduct_neg]
  refine Octonion.ext ?_ ?_ ?_ ?_
  · simp [hdot]
    ring
  · simp [triple_product_permutation y.v u x.v]
    ring
  · simp
    module
  · simp
    linear_combination (norm := module) (y.b - y.a) • cross_anticomm' u x.v

private theorem lowerDerivationEnd_mem (t : Fin 3 → R) :
    lowerDerivationEnd t ∈ derivationLieAlgebra R (Octonion R) := by
  rw [mem_derivationLieAlgebra]
  intro x y
  have hdot : x.w ⬝ᵥ (t ⨯₃ y.w) = -(t ⬝ᵥ (x.w ⨯₃ y.w)) := by
    rw [triple_product_permutation, ← cross_anticomm, dotProduct_neg]
  refine Octonion.ext ?_ ?_ ?_ ?_
  · simp [triple_product_permutation y.w t x.w]
    ring
  · simp [hdot]
    ring
  · simp
    linear_combination (norm := module) (y.a - y.b) • cross_anticomm' t x.w
  · simp
    module

/-! ### The three families, bundled -/

/-- **The special linear derivations of `𝕆`**: the homomorphism of Lie algebras
`𝔰𝔩₃ → Der 𝕆` that sends a trace-zero matrix `M` to the derivation acting by `M` on the
upper vector entry of a Zorn vector matrix and by `-Mᵀ` on the lower one. -/
def slDerivation :
    LieAlgebra.SpecialLinear.sl (Fin 3) R →ₗ⁅R⁆ derivationLieAlgebra R (Octonion R) where
  -- `𝔰𝔩₃` is the kernel of the trace, so membership in it is exactly the hypothesis of
  -- `slDerivationEnd_mem`.
  toFun M := ⟨slDerivationEnd M.1, slDerivationEnd_mem (LinearMap.mem_ker.mp M.2)⟩
  map_add' M N := derivationLieAlgebra.ext fun x => by
    refine Octonion.ext (by simp) (by simp) (by simp [Matrix.add_mulVec]) ?_
    simp [Matrix.transpose_add, Matrix.add_mulVec, add_comm]
  map_smul' c M := derivationLieAlgebra.ext fun x => by
    refine Octonion.ext (by simp) (by simp) (by simp [Matrix.smul_mulVec]) ?_
    simp [Matrix.transpose_smul, Matrix.smul_mulVec]
  map_lie' {M N} := derivationLieAlgebra.ext fun x => by
    refine Octonion.ext (by simp) (by simp) ?_ ?_
    · simp [Ring.lie_def, Matrix.sub_mulVec]
    · simp [Ring.lie_def, Matrix.transpose_sub, Matrix.sub_mulVec, Matrix.mulVec_neg]

@[simp] theorem slDerivation_apply_a (M : LieAlgebra.SpecialLinear.sl (Fin 3) R) (x : Octonion R) :
    ((slDerivation M : Module.End R (Octonion R)) x).a = 0 := (rfl)

@[simp] theorem slDerivation_apply_b (M : LieAlgebra.SpecialLinear.sl (Fin 3) R) (x : Octonion R) :
    ((slDerivation M : Module.End R (Octonion R)) x).b = 0 := (rfl)

@[simp] theorem slDerivation_apply_v (M : LieAlgebra.SpecialLinear.sl (Fin 3) R) (x : Octonion R) :
    ((slDerivation M : Module.End R (Octonion R)) x).v = (M : Matrix (Fin 3) (Fin 3) R) *ᵥ x.v :=
  (rfl)

@[simp] theorem slDerivation_apply_w (M : LieAlgebra.SpecialLinear.sl (Fin 3) R) (x : Octonion R) :
    ((slDerivation M : Module.End R (Octonion R)) x).w =
      -((M : Matrix (Fin 3) (Fin 3) R)ᵀ *ᵥ x.w) := (rfl)

/-- **The upper vector derivations of `𝕆`**: the linear map sending `u : R³` to the derivation
that takes the idempotent `⟨1, 0, 0, 0⟩` to the vector matrix with upper entry `u`. -/
def upperDerivation : (Fin 3 → R) →ₗ[R] derivationLieAlgebra R (Octonion R) where
  toFun u := ⟨upperDerivationEnd u, upperDerivationEnd_mem u⟩
  map_add' u u' := derivationLieAlgebra.ext fun x => by
    refine Octonion.ext (by simp [add_comm]) (by simp) ?_ (by simp)
    simp [smul_add]
  map_smul' c u := derivationLieAlgebra.ext fun x => by
    refine Octonion.ext (by simp) (by simp) ?_ (by simp)
    simp [smul_smul, mul_comm]

@[simp] theorem upperDerivation_apply_a (u : Fin 3 → R) (x : Octonion R) :
    ((upperDerivation u : Module.End R (Octonion R)) x).a = -(u ⬝ᵥ x.w) := (rfl)

@[simp] theorem upperDerivation_apply_b (u : Fin 3 → R) (x : Octonion R) :
    ((upperDerivation u : Module.End R (Octonion R)) x).b = u ⬝ᵥ x.w := (rfl)

@[simp] theorem upperDerivation_apply_v (u : Fin 3 → R) (x : Octonion R) :
    ((upperDerivation u : Module.End R (Octonion R)) x).v = (x.a - x.b) • u := (rfl)

@[simp] theorem upperDerivation_apply_w (u : Fin 3 → R) (x : Octonion R) :
    ((upperDerivation u : Module.End R (Octonion R)) x).w = u ⨯₃ x.v := (rfl)

/-- **The lower vector derivations of `𝕆`**: the linear map sending `t : R³` to the derivation
that takes the idempotent `⟨1, 0, 0, 0⟩` to the vector matrix with lower entry `t`. -/
def lowerDerivation : (Fin 3 → R) →ₗ[R] derivationLieAlgebra R (Octonion R) where
  toFun t := ⟨lowerDerivationEnd t, lowerDerivationEnd_mem t⟩
  map_add' t t' := derivationLieAlgebra.ext fun x => by
    refine Octonion.ext (by simp [add_comm]) (by simp) (by simp) ?_
    simp [smul_add]
  map_smul' c t := derivationLieAlgebra.ext fun x => by
    refine Octonion.ext (by simp) (by simp) (by simp) ?_
    simp [smul_smul, mul_comm]

@[simp] theorem lowerDerivation_apply_a (t : Fin 3 → R) (x : Octonion R) :
    ((lowerDerivation t : Module.End R (Octonion R)) x).a = -(t ⬝ᵥ x.v) := (rfl)

@[simp] theorem lowerDerivation_apply_b (t : Fin 3 → R) (x : Octonion R) :
    ((lowerDerivation t : Module.End R (Octonion R)) x).b = t ⬝ᵥ x.v := (rfl)

@[simp] theorem lowerDerivation_apply_v (t : Fin 3 → R) (x : Octonion R) :
    ((lowerDerivation t : Module.End R (Octonion R)) x).v = t ⨯₃ x.w := (rfl)

@[simp] theorem lowerDerivation_apply_w (t : Fin 3 → R) (x : Octonion R) :
    ((lowerDerivation t : Module.End R (Octonion R)) x).w = (x.a - x.b) • t := (rfl)

/-! ### The brackets of the three families -/

/-- **The `𝔰𝔩₃` parameter of the bracket of an upper and a lower vector derivation**: the matrix
`⟨u, t⟩ • 1 - 3 • u tᵀ`, whose trace vanishes because the rank-one matrix `u tᵀ` has trace
`⟨u, t⟩`.  See `TauCeti.Octonion.lie_upperDerivation_lowerDerivation`. -/
def slOfVectors (u t : Fin 3 → R) : LieAlgebra.SpecialLinear.sl (Fin 3) R :=
  ⟨(u ⬝ᵥ t) • 1 - (3 : R) • Matrix.vecMulVec u t,
    LinearMap.mem_ker.mpr (by simp [Matrix.trace_sub, mul_comm])⟩

@[simp] theorem coe_slOfVectors (u t : Fin 3 → R) :
    (slOfVectors u t : Matrix (Fin 3) (Fin 3) R) =
      (u ⬝ᵥ t) • 1 - (3 : R) • Matrix.vecMulVec u t := (rfl)

/-- **The upper vector derivations carry the defining representation of `𝔰𝔩₃`**:
`⁅slDerivation M, upperDerivation u⁆ = upperDerivation (M u)`, the degree `0` piece of the
`ℤ/3`-grading acting on the degree `1` piece. -/
@[simp] theorem lie_slDerivation_upperDerivation (M : LieAlgebra.SpecialLinear.sl (Fin 3) R)
    (u : Fin 3 → R) :
    ⁅slDerivation M, upperDerivation u⁆ =
      upperDerivation ((M : Matrix (Fin 3) (Fin 3) R) *ᵥ u) := by
  have hM : (M : Matrix (Fin 3) (Fin 3) R).trace = 0 := LinearMap.mem_ker.mp M.2
  refine derivationLieAlgebra.ext fun x => Octonion.ext ?_ ?_ ?_ ?_
  · simp [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  · simp [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  · simp [Matrix.mulVec_smul]
  · simp only [LieSubalgebra.coe_bracket, LieHom.lie_apply, Module.End.lie_apply, sub_w,
      slDerivation_apply_w, upperDerivation_apply_w, slDerivation_apply_v]
    exact (eq_sub_of_add_eq (Matrix.mulVec_cross_add_cross_mulVec_of_trace_eq_zero
      (M : Matrix (Fin 3) (Fin 3) R) hM u x.v)).symm

/-- **The lower vector derivations carry the dual of the defining representation of `𝔰𝔩₃`**:
`⁅slDerivation M, lowerDerivation t⁆ = lowerDerivation (-(Mᵀ t))`, the degree `0` piece of the
`ℤ/3`-grading acting on the degree `2` piece. -/
@[simp] theorem lie_slDerivation_lowerDerivation (M : LieAlgebra.SpecialLinear.sl (Fin 3) R)
    (t : Fin 3 → R) :
    ⁅slDerivation M, lowerDerivation t⁆ =
      lowerDerivation (-((M : Matrix (Fin 3) (Fin 3) R)ᵀ *ᵥ t)) := by
  have hM : (M : Matrix (Fin 3) (Fin 3) R)ᵀ.trace = 0 := by
    rw [Matrix.trace_transpose]
    exact LinearMap.mem_ker.mp M.2
  refine derivationLieAlgebra.ext fun x => Octonion.ext ?_ ?_ ?_ ?_
  · simp [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  · simp [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  · have h := Matrix.mulVec_cross_add_cross_mulVec_of_trace_eq_zero
      (M : Matrix (Fin 3) (Fin 3) R)ᵀ hM x.w t
    rw [Matrix.transpose_transpose, ← cross_anticomm t x.w, Matrix.mulVec_neg, neg_neg] at h
    simp only [LieSubalgebra.coe_bracket, LieHom.lie_apply, Module.End.lie_apply, sub_v,
      slDerivation_apply_v, lowerDerivation_apply_v, slDerivation_apply_w, map_neg, cross_anticomm,
      NegMemClass.coe_neg, LinearMap.neg_apply, neg_v]
    exact (eq_sub_of_add_eq' h).symm
  · simp [Matrix.mulVec_smul]

/-- **Two upper vector derivations bracket into the lower family**, by twice the cross product:
`⁅upperDerivation u, upperDerivation u'⁆ = lowerDerivation (2 (u ⨯₃ u'))`.  In the `ℤ/3`-grading
this is `1 + 1 = 2`. -/
@[simp] theorem lie_upperDerivation_upperDerivation (u u' : Fin 3 → R) :
    ⁅upperDerivation u, upperDerivation u'⁆ = lowerDerivation ((2 : R) • (u ⨯₃ u')) := by
  have hdot : ∀ v : Fin 3 → R, u' ⬝ᵥ (u ⨯₃ v) = -(u ⬝ᵥ (u' ⨯₃ v)) := fun v => by
    rw [triple_product_permutation, ← cross_anticomm, dotProduct_neg]
  refine derivationLieAlgebra.ext fun x => Octonion.ext ?_ ?_ ?_ ?_
  · simp [hdot, triple_product_permutation x.v u u']
    ring
  · simp [hdot, triple_product_permutation x.v u u']
    ring
  · simp
    module
  · simp
    linear_combination (norm := module) (x.b - x.a) • cross_anticomm' u u'

/-- **Two lower vector derivations bracket into the upper family**, by twice the cross product:
`⁅lowerDerivation t, lowerDerivation t'⁆ = upperDerivation (2 (t ⨯₃ t'))`.  In the `ℤ/3`-grading
this is `2 + 2 = 1`. -/
@[simp] theorem lie_lowerDerivation_lowerDerivation (t t' : Fin 3 → R) :
    ⁅lowerDerivation t, lowerDerivation t'⁆ = upperDerivation ((2 : R) • (t ⨯₃ t')) := by
  have hdot : ∀ v : Fin 3 → R, t' ⬝ᵥ (t ⨯₃ v) = -(t ⬝ᵥ (t' ⨯₃ v)) := fun v => by
    rw [triple_product_permutation, ← cross_anticomm, dotProduct_neg]
  refine derivationLieAlgebra.ext fun x => Octonion.ext ?_ ?_ ?_ ?_
  · simp [hdot, triple_product_permutation x.w t t']
    ring
  · simp [hdot, triple_product_permutation x.w t t']
    ring
  · simp
    linear_combination (norm := module) (x.b - x.a) • cross_anticomm' t t'
  · simp
    module

/-- **An upper and a lower vector derivation bracket back into `𝔰𝔩₃`**:
`⁅upperDerivation u, lowerDerivation t⁆ = slDerivation (slOfVectors u t)`.  In the `ℤ/3`-grading
this is `1 + 2 = 0`, the bracket that makes the fourteen derivations a Lie subalgebra. -/
@[simp] theorem lie_upperDerivation_lowerDerivation (u t : Fin 3 → R) :
    ⁅upperDerivation u, lowerDerivation t⁆ = slDerivation (slOfVectors u t) := by
  refine derivationLieAlgebra.ext fun x => Octonion.ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
    module
  · simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
    module

end Vector

/-! ### Fourteen independent derivations -/

/-- **The fourteen-parameter family of derivations of `𝕆`**: a trace-zero matrix together with an
upper and a lower vector.  The three summands are `TauCeti.Octonion.slDerivation`,
`TauCeti.Octonion.upperDerivation` and `TauCeti.Octonion.lowerDerivation`. -/
def derivationOfTriple :
    (LieAlgebra.SpecialLinear.sl (Fin 3) R × (Fin 3 → R) × (Fin 3 → R)) →ₗ[R]
      derivationLieAlgebra R (Octonion R) :=
  (slDerivation (R := R)).toLinearMap.coprod (upperDerivation.coprod lowerDerivation)

@[simp]
theorem derivationOfTriple_apply (M : LieAlgebra.SpecialLinear.sl (Fin 3) R)
    (u t : Fin 3 → R) :
    derivationOfTriple (M, u, t) = slDerivation M + (upperDerivation u + lowerDerivation t) :=
  (rfl)

/-- **The fourteen-parameter family is faithful in its parameters.**  Applying a derivation in the
family to the idempotent `⟨1, 0, 0, 0⟩` reads off the upper and the lower vector, and applying it
to a vector matrix with upper entry `v` and nothing else then reads off `M v`. -/
theorem derivationOfTriple_injective :
    Function.Injective (derivationOfTriple (R := R)) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  rintro ⟨M, u, t⟩ h
  have hx : ∀ x : Octonion R,
      ((derivationOfTriple (M, u, t) : derivationLieAlgebra R (Octonion R)) :
        Module.End R (Octonion R)) x = 0 := fun x => by rw [h]; simp
  have hu : u = 0 := by
    have hv := congrArg Octonion.v (hx ⟨1, 0, 0, 0⟩)
    simpa using hv
  have ht : t = 0 := by
    have hw := congrArg Octonion.w (hx ⟨1, 0, 0, 0⟩)
    simpa using hw
  have hM : (M : Matrix (Fin 3) (Fin 3) R) = 0 := by
    ext i j
    have hv := congrArg (fun z => Octonion.v z i) (hx ⟨0, 0, Pi.single j 1, 0⟩)
    simpa [hu, ht, Matrix.mulVec_single] using hv
  simp [Prod.ext_iff, hu, ht, Subtype.ext_iff, hM]

/-! ### Every derivation lies in the fourteen-parameter family -/

section Surjective

/-- The vector matrix `⟨0, 0, v, 0⟩` with upper entry `v` and nothing else, as a linear map. -/
private def upperVec : (Fin 3 → R) →ₗ[R] Octonion R where
  toFun v := ⟨0, 0, v, 0⟩
  map_add' _ _ := by refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp
  map_smul' _ _ := by refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp

/-- The upper vector entry of a vector matrix, as a linear map. -/
private def vEntry : Octonion R →ₗ[R] (Fin 3 → R) where
  toFun x := x.v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A derivation sends the diagonal idempotent `e = ⟨1, 0, 0, 0⟩` to a vector matrix with vanishing
bottom-right entry: that entry is the norm-form pairing `⟨e, D e⟩`, which vanishes by skewness. -/
private theorem derivation_apply_diagIdempotent_b (D : derivationLieAlgebra R (Octonion R)) :
    ((D : Module.End R (Octonion R)) ⟨1, 0, 0, 0⟩).b = 0 := by
  simpa [polar_normQuadraticForm] using polar_derivation_apply_self_eq_zero D ⟨1, 0, 0, 0⟩

/-- A derivation sends the diagonal idempotent `e = ⟨1, 0, 0, 0⟩` to a vector matrix with vanishing
top-left entry: the trace of `D e` vanishes, and so does its bottom-right entry. -/
private theorem derivation_apply_diagIdempotent_a (D : derivationLieAlgebra R (Octonion R)) :
    ((D : Module.End R (Octonion R)) ⟨1, 0, 0, 0⟩).a = 0 := by
  simpa [derivation_apply_diagIdempotent_b] using trace_derivation_apply_eq_zero D ⟨1, 0, 0, 0⟩

variable {E : derivationLieAlgebra R (Octonion R)}
  (hE : (E : Module.End R (Octonion R)) ⟨1, 0, 0, 0⟩ = 0)
include hE

/-- A derivation killing `⟨1, 0, 0, 0⟩` kills every diagonal vector matrix, these being the
combinations of `⟨1, 0, 0, 0⟩` and `1`. -/
private theorem apply_diag_eq_zero (a b : R) :
    (E : Module.End R (Octonion R)) ⟨a, b, 0, 0⟩ = 0 := by
  have hx : (⟨a, b, 0, 0⟩ : Octonion R) = (a - b) • ⟨1, 0, 0, 0⟩ + b • (1 : Octonion R) := by
    refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp
  rw [hx, map_add, map_smul, map_smul, hE, derivationLieAlgebra.apply_one_eq_zero, smul_zero,
    smul_zero, add_zero]

/-- A derivation killing `e = ⟨1, 0, 0, 0⟩` maps an upper vector matrix `x = ⟨0, 0, v, 0⟩` to
another one. Differentiating `e * x = x` and `x * e = 0` gives `D x = e * D x` and `D x * e = 0`,
which kill the three other entries of `D x`. -/
private theorem apply_upperVec (v : Fin 3 → R) :
    (E : Module.End R (Octonion R)) ⟨0, 0, v, 0⟩ =
      ⟨0, 0, ((E : Module.End R (Octonion R)) ⟨0, 0, v, 0⟩).v, 0⟩ := by
  have h₁ := derivationLieAlgebra.leibniz E ⟨1, 0, 0, 0⟩ ⟨0, 0, v, 0⟩
  have h₂ := derivationLieAlgebra.leibniz E ⟨0, 0, v, 0⟩ ⟨1, 0, 0, 0⟩
  have hl : (⟨1, 0, 0, 0⟩ : Octonion R) * ⟨0, 0, v, 0⟩ = ⟨0, 0, v, 0⟩ := by
    refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp
  have hr : (⟨0, 0, v, 0⟩ : Octonion R) * ⟨1, 0, 0, 0⟩ = 0 := by
    refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp
  rw [hl, hE, zero_mul, zero_add] at h₁
  rw [hr, map_zero, hE, mul_zero, add_zero] at h₂
  exact Octonion.ext (by simpa using (congrArg Octonion.a h₂).symm)
    (by simpa using congrArg Octonion.b h₁) rfl (by simpa using congrArg Octonion.w h₁)

/-- A derivation killing `e = ⟨1, 0, 0, 0⟩` maps a lower vector matrix `z = ⟨0, 0, 0, w⟩` to
another one, by the mirror of `apply_upperVec`: here `z * e = z` and `e * z = 0`. -/
private theorem apply_lowerVec (w : Fin 3 → R) :
    (E : Module.End R (Octonion R)) ⟨0, 0, 0, w⟩ =
      ⟨0, 0, 0, ((E : Module.End R (Octonion R)) ⟨0, 0, 0, w⟩).w⟩ := by
  have h₁ := derivationLieAlgebra.leibniz E ⟨0, 0, 0, w⟩ ⟨1, 0, 0, 0⟩
  have h₂ := derivationLieAlgebra.leibniz E ⟨1, 0, 0, 0⟩ ⟨0, 0, 0, w⟩
  have hr : (⟨0, 0, 0, w⟩ : Octonion R) * ⟨1, 0, 0, 0⟩ = ⟨0, 0, 0, w⟩ := by
    refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp
  have hl : (⟨1, 0, 0, 0⟩ : Octonion R) * ⟨0, 0, 0, w⟩ = 0 := by
    refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp
  rw [hr, hE, mul_zero, add_zero] at h₁
  rw [hl, map_zero, hE, zero_mul, zero_add] at h₂
  exact Octonion.ext (by simpa using (congrArg Octonion.a h₂).symm)
    (by simpa using congrArg Octonion.b h₁) (by simpa using congrArg Octonion.v h₁) rfl

/-- A derivation killing `⟨1, 0, 0, 0⟩` acts separately on the two vector entries and kills the
diagonal. -/
private theorem apply_eq_of_apply_diagIdempotent_eq_zero (x : Octonion R) :
    (E : Module.End R (Octonion R)) x =
      ⟨0, 0, ((E : Module.End R (Octonion R)) ⟨0, 0, x.v, 0⟩).v,
        ((E : Module.End R (Octonion R)) ⟨0, 0, 0, x.w⟩).w⟩ := by
  have hx : x = ⟨x.a, x.b, 0, 0⟩ + ⟨0, 0, x.v, 0⟩ + ⟨0, 0, 0, x.w⟩ := by
    refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp
  conv_lhs => rw [hx, map_add, map_add, apply_diag_eq_zero hE, apply_upperVec hE,
    apply_lowerVec hE]
  refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp

/-- The actions of a derivation killing `⟨1, 0, 0, 0⟩` on the upper and on the lower entry are
negative adjoints for the dot product, the top-left entry of the derivative of
`⟨0, 0, v, 0⟩ * ⟨0, 0, 0, w⟩ = ⟨v ⬝ᵥ w, 0, 0, 0⟩`. -/
private theorem dotProduct_upper_add_dotProduct_lower (v w : Fin 3 → R) :
    ((E : Module.End R (Octonion R)) ⟨0, 0, v, 0⟩).v ⬝ᵥ w +
      v ⬝ᵥ ((E : Module.End R (Octonion R)) ⟨0, 0, 0, w⟩).w = 0 := by
  have h := derivationLieAlgebra.leibniz E ⟨0, 0, v, 0⟩ ⟨0, 0, 0, w⟩
  have hp : (⟨0, 0, v, 0⟩ : Octonion R) * ⟨0, 0, 0, w⟩ = ⟨v ⬝ᵥ w, 0, 0, 0⟩ := by
    refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp
  rw [hp, apply_diag_eq_zero hE, apply_upperVec hE v, apply_lowerVec hE w] at h
  have ha := congrArg Octonion.a h
  simpa using ha.symm

/-- The action of a derivation killing `⟨1, 0, 0, 0⟩` on the lower entry differentiates the cross
product of two upper entries, the bottom-left entry of the derivative of
`⟨0, 0, v, 0⟩ * ⟨0, 0, v', 0⟩ = ⟨0, 0, 0, v ⨯₃ v'⟩`. -/
private theorem lower_cross (v v' : Fin 3 → R) :
    ((E : Module.End R (Octonion R)) ⟨0, 0, 0, v ⨯₃ v'⟩).w =
      ((E : Module.End R (Octonion R)) ⟨0, 0, v, 0⟩).v ⨯₃ v' +
        v ⨯₃ ((E : Module.End R (Octonion R)) ⟨0, 0, v', 0⟩).v := by
  have h := derivationLieAlgebra.leibniz E ⟨0, 0, v, 0⟩ ⟨0, 0, v', 0⟩
  have hp : (⟨0, 0, v, 0⟩ : Octonion R) * ⟨0, 0, v', 0⟩ = ⟨0, 0, 0, v ⨯₃ v'⟩ := by
    refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp
  rw [hp, apply_upperVec hE v, apply_upperVec hE v'] at h
  have hw := congrArg Octonion.w h
  simpa using hw

/-- **A derivation killing `⟨1, 0, 0, 0⟩` is special linear.** It acts on the upper entry by some
matrix `M` and, by the dot-product relation, on the lower one by `-Mᵀ`; comparing the cross-product
relation with `Matrix.mulVec_cross_add_cross_mulVec` at `e₀ ⨯₃ e₁ = e₂` then shows that `M` has
trace zero. -/
private theorem exists_slDerivation_eq :
    ∃ M : LieAlgebra.SpecialLinear.sl (Fin 3) R, slDerivation M = E := by
  set M : Matrix (Fin 3) (Fin 3) R :=
    LinearMap.toMatrix' (vEntry ∘ₗ (E : Module.End R (Octonion R)) ∘ₗ upperVec) with hMdef
  have hM : ∀ v, M *ᵥ v = ((E : Module.End R (Octonion R)) ⟨0, 0, v, 0⟩).v := fun v => by
    rw [hMdef, LinearMap.toMatrix'_mulVec]
    -- The composite is, by definition, `v ↦ (E ⟨0, 0, v, 0⟩).v`.
    rfl
  have hN : ∀ w, ((E : Module.End R (Octonion R)) ⟨0, 0, 0, w⟩).w = -(Mᵀ *ᵥ w) := fun w => by
    funext i
    have h := dotProduct_upper_add_dotProduct_lower hE (Pi.single i 1) w
    rw [← hM, dotProduct_comm, ← dotProduct_transpose_mulVec, single_one_dotProduct,
      single_one_dotProduct] at h
    simpa using eq_neg_of_add_eq_zero_right h
  have htr : M.trace = 0 := by
    have h := lower_cross hE (Pi.single 0 1) (Pi.single 1 1)
    rw [hN, ← hM, ← hM, Matrix.mulVec_cross_add_cross_mulVec] at h
    have h₀ : M.trace • ((Pi.single 0 1 : Fin 3 → R) ⨯₃ Pi.single 1 1) = 0 := by
      linear_combination (norm := module) -h
    simpa [cross_apply] using congrFun h₀ 2
  refine ⟨⟨M, LinearMap.mem_ker.mpr htr⟩, derivationLieAlgebra.ext fun x => ?_⟩
  rw [apply_eq_of_apply_diagIdempotent_eq_zero hE x, hN, ← hM]
  refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp

end Surjective

/-- **Every derivation of `𝕆` lies in the fourteen-parameter family**: a derivation `D` is
`slDerivation M + upperDerivation u + lowerDerivation t`, where `u` and `t` are the upper and lower
entries of `D ⟨1, 0, 0, 0⟩` and `M` is the matrix by which `D` then acts on the upper entries. No
hypothesis on the commutative ring `R` is needed. -/
theorem derivationOfTriple_surjective :
    Function.Surjective (derivationOfTriple (R := R)) := by
  intro D
  set u := ((D : Module.End R (Octonion R)) ⟨1, 0, 0, 0⟩).v
  set t := ((D : Module.End R (Octonion R)) ⟨1, 0, 0, 0⟩).w
  have hE : ((D - upperDerivation u - lowerDerivation t : derivationLieAlgebra R (Octonion R)) :
      Module.End R (Octonion R)) ⟨1, 0, 0, 0⟩ = 0 := by
    refine Octonion.ext ?_ ?_ ?_ ?_ <;>
      simp [u, t, derivation_apply_diagIdempotent_a, derivation_apply_diagIdempotent_b]
  obtain ⟨M, hM⟩ := exists_slDerivation_eq hE
  exact ⟨(M, u, t), by rw [derivationOfTriple_apply, hM]; abel⟩

/-- **The derivations of the split octonions are `𝔰𝔩₃ × R³ × R³`**, as an `R`-module: the
fourteen-parameter family `TauCeti.Octonion.derivationOfTriple` is a linear equivalence, over any
commutative ring. This is the `ℤ/3`-graded decomposition `G₂ = 𝔰𝔩₃ ⊕ V ⊕ V*` of `Der 𝕆`; its
inverse reads the vector parameters off the value at `⟨1, 0, 0, 0⟩`
(`TauCeti.Octonion.tripleEquivDerivationLieAlgebra_symm_apply_snd_fst` and
`TauCeti.Octonion.tripleEquivDerivationLieAlgebra_symm_apply_snd_snd`) and the matrix off the
values at the upper vector matrices
(`TauCeti.Octonion.tripleEquivDerivationLieAlgebra_symm_apply_fst_mulVec`). -/
noncomputable def tripleEquivDerivationLieAlgebra :
    (LieAlgebra.SpecialLinear.sl (Fin 3) R × (Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R]
      derivationLieAlgebra R (Octonion R) :=
  LinearEquiv.ofBijective derivationOfTriple
    ⟨derivationOfTriple_injective, derivationOfTriple_surjective⟩

@[simp]
theorem tripleEquivDerivationLieAlgebra_apply
    (p : LieAlgebra.SpecialLinear.sl (Fin 3) R × (Fin 3 → R) × (Fin 3 → R)) :
    tripleEquivDerivationLieAlgebra p = derivationOfTriple p :=
  (rfl)

/-- The upper vector parameter of a derivation is the upper entry of its value at
`⟨1, 0, 0, 0⟩`. -/
@[simp]
theorem tripleEquivDerivationLieAlgebra_symm_apply_snd_fst
    (D : derivationLieAlgebra R (Octonion R)) :
    (tripleEquivDerivationLieAlgebra.symm D).2.1 =
      ((D : Module.End R (Octonion R)) ⟨1, 0, 0, 0⟩).v := by
  obtain ⟨⟨M, u, t⟩, rfl⟩ := tripleEquivDerivationLieAlgebra.surjective D
  rw [LinearEquiv.symm_apply_apply]
  simp

/-- The lower vector parameter of a derivation is the lower entry of its value at
`⟨1, 0, 0, 0⟩`. -/
@[simp]
theorem tripleEquivDerivationLieAlgebra_symm_apply_snd_snd
    (D : derivationLieAlgebra R (Octonion R)) :
    (tripleEquivDerivationLieAlgebra.symm D).2.2 =
      ((D : Module.End R (Octonion R)) ⟨1, 0, 0, 0⟩).w := by
  obtain ⟨⟨M, u, t⟩, rfl⟩ := tripleEquivDerivationLieAlgebra.surjective D
  rw [LinearEquiv.symm_apply_apply]
  simp

/-- The `𝔰𝔩₃` parameter of a derivation is the matrix by which it acts on the upper vector
matrices: `M v` is the upper entry of `D ⟨0, 0, v, 0⟩`. -/
@[simp]
theorem tripleEquivDerivationLieAlgebra_symm_apply_fst_mulVec
    (D : derivationLieAlgebra R (Octonion R)) (v : Fin 3 → R) :
    ((tripleEquivDerivationLieAlgebra.symm D).1 : Matrix (Fin 3) (Fin 3) R) *ᵥ v =
      ((D : Module.End R (Octonion R)) ⟨0, 0, v, 0⟩).v := by
  obtain ⟨⟨M, u, t⟩, rfl⟩ := tripleEquivDerivationLieAlgebra.surjective D
  rw [LinearEquiv.symm_apply_apply]
  simp

/-- **`Der 𝕆` is a free module**, being isomorphic to `𝔰𝔩₃ × R³ × R³`. -/
instance : Module.Free R (derivationLieAlgebra R (Octonion R)) :=
  Module.Free.of_equiv tripleEquivDerivationLieAlgebra

/-- **`Der 𝕆` is a finite module**, being isomorphic to `𝔰𝔩₃ × R³ × R³`. -/
instance : Module.Finite R (derivationLieAlgebra R (Octonion R)) :=
  Module.Finite.equiv tripleEquivDerivationLieAlgebra

/-- **`Der 𝕆` has rank `14`**: eight for `𝔰𝔩₃` and three for each of the two vector families of
`TauCeti.Octonion.tripleEquivDerivationLieAlgebra`. This is the dimension of the exceptional Lie
algebra `G₂`. -/
@[simp]
theorem finrank_derivationLieAlgebra (R : Type*) [CommRing R] [StrongRankCondition R] :
    Module.finrank R (derivationLieAlgebra R (Octonion R)) = 14 := by
  rw [← tripleEquivDerivationLieAlgebra.finrank_eq, Module.finrank_prod, Module.finrank_prod,
    finrank_sl, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  norm_num

/-- **`𝕆` has nonzero derivations**, so the derivation algebra whose skewness the rest of this file
establishes is not the zero Lie algebra.  The witness is the upper vector derivation attached to
the first basis vector, which sends the idempotent `⟨1, 0, 0, 0⟩` to `⟨0, 0, e₀, 0⟩`. -/
instance instNontrivialDerivationLieAlgebra [Nontrivial R] :
    Nontrivial (derivationLieAlgebra R (Octonion R)) := by
  refine ⟨upperDerivation (Pi.single 0 1), 0, fun h => ?_⟩
  have h₁ := congrArg (fun D : derivationLieAlgebra R (Octonion R) =>
    ((D : Module.End R (Octonion R)) ⟨1, 0, 0, 0⟩).v 0) h
  simp at h₁

end SpecialLinear

end Octonion

end TauCeti

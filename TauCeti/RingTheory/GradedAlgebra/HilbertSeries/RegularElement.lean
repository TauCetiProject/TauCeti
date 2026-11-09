/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.Basic
public import TauCeti.RingTheory.GradedAlgebra.Quotient
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TauCeti.LinearAlgebra.Exact

/-!
# Hilbert series of a quotient by a homogeneous regular element

Let `A` be an `ℕ`-graded algebra over a field, with finite-dimensional graded pieces, and
let `f` be a homogeneous non-zero-divisor of degree `d`. The quotient has Hilbert series
`Hilb(A/(f), t) = Hilb(A, t) * (1 - t^d)`.

The finite-dimensionality hypothesis is on the pieces, not on the whole algebra. The
coefficient identity is proved over the natural numbers before passing to power series
over any coefficient ring. Thus it also computes dimensions in positive characteristic;
using integer coefficients retains these dimensions without reduction modulo the
characteristic. Degree zero is allowed: in this case the formula asserts that every
quotient piece vanishes.

These are the one-element exact-sequence formulas used to compute the Hilbert series
of a quotient by a homogeneous regular sequence, in particular a coinvariant algebra
presented by homogeneous basic invariants. The quotient pieces are the images of the
original graded pieces under the quotient map.

## Main results

* `finrank_quotientPiece_span_singleton_add`: the dimension identity in degrees at least `d`.
* `finrank_quotientPiece_span_singleton_of_lt`: quotienting changes no piece below `d`.
* `mk_finrank_quotientPiece_span_singleton`: the Hilbert-series identity.

## References

* R. P. Stanley, *Invariants of finite groups and their applications to combinatorics*,
  Bull. Amer. Math. Soc. (N.S.) **1** (1979), §3.

The proof uses the homogeneous cancellation theorem
  `TauCeti.GradedAlgebra.mem_of_mul_mem_add_of_isLeftRegular` and the short-exact-sequence
  dimension formula `Function.Exact.finrank_eq_add`.
-/

public section

namespace TauCeti.GradedAlgebra

variable {k A : Type*} [CommRing A]

section Exact

variable [CommSemiring k] [Algebra k A] (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
  {f : A} {d : ℕ}

/-- The degree-`d + n` quotient map has kernel the multiples of `f` from degree `n`,
when `f` is homogeneous and regular. -/
theorem exact_mulLeft_submoduleMap_span_singleton (hf : f ∈ 𝒜 d)
    (hreg : IsLeftRegular f) (n : ℕ) :
    Function.Exact
      (((LinearMap.mulLeft k f).domRestrict (𝒜 n)).codRestrict (𝒜 (d + n))
        (fun x ↦ SetLike.mul_mem_graded hf x.2))
      ((Ideal.Quotient.mkₐ k (Ideal.span {f})).toLinearMap.submoduleMap (𝒜 (d + n))) := by
  intro x
  constructor
  · intro hx
    have hxI : (x : A) ∈ Ideal.span {f} :=
      Ideal.Quotient.eq_zero_iff_mem.1 (congrArg Subtype.val hx)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.1 hxI
    have ha𝒜 : a ∈ 𝒜 n :=
      mem_of_mul_mem_add_of_isLeftRegular 𝒜 hf hreg (ha ▸ x.2)
    exact ⟨⟨a, ha𝒜⟩, Subtype.ext ha.symm⟩
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ⟨a, rfl⟩)

end Exact

section Field

variable [Field k] [Algebra k A] (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
  {f : A} {d : ℕ}

/-- Multiplication by a homogeneous non-zero-divisor identifies the kernel of the
quotient map in degree `d + n` with the original degree-`n` piece. Consequently the
dimensions of the quotient degree-`d + n` piece and the original degree-`n` piece sum
to the dimension of the original degree-`d + n` piece. -/
theorem finrank_quotientPiece_span_singleton_add (hf : f ∈ 𝒜 d)
    (hreg : IsLeftRegular f) (n : ℕ) [Module.Finite k (𝒜 (d + n))] :
    Module.finrank k (quotientPiece 𝒜 (Ideal.span {f}) (d + n)) +
      Module.finrank k (𝒜 n) = Module.finrank k (𝒜 (d + n)) := by
  rw [quotientPiece_def]
  let μ : 𝒜 n →ₗ[k] 𝒜 (d + n) :=
    ((LinearMap.mulLeft k f).domRestrict (𝒜 n)).codRestrict (𝒜 (d + n))
      (fun x ↦ SetLike.mul_mem_graded hf x.2)
  let q := (Ideal.Quotient.mkₐ k (Ideal.span {f})).toLinearMap.submoduleMap (𝒜 (d + n))
  have hμ : Function.Injective μ := fun x y h ↦
    Subtype.ext (hreg (congrArg Subtype.val h))
  have hq : Function.Surjective q := LinearMap.submoduleMap_surjective _ _
  have hex : Function.Exact μ q := exact_mulLeft_submoduleMap_span_singleton 𝒜 hf hreg n
  simpa only [add_comm] using (hex.finrank_eq_add hμ hq).symm

end Field

section CommSemiring

variable [CommSemiring k] [Algebra k A] (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
  {f : A} {d : ℕ}

/-- The quotient map is an isomorphism on pieces below the degree of a homogeneous
relation. Regularity of the relation is not required. -/
theorem bijective_submoduleMap_span_singleton_of_lt (hf : f ∈ 𝒜 d) {n : ℕ} (hn : n < d) :
    Function.Bijective
      ((Ideal.Quotient.mkₐ k (Ideal.span {f})).toLinearMap.submoduleMap (𝒜 n)) := by
  refine ⟨?_, LinearMap.submoduleMap_surjective _ _⟩
  intro x y hxy
  have hxyI : (x : A) - y ∈ Ideal.span {f} :=
    Ideal.Quotient.eq.1 (congrArg Subtype.val hxy)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.1 hxyI
  apply Subtype.ext
  apply sub_eq_zero.1
  have hproj := DirectSum.coe_decompose_mul_of_left_mem_of_not_le 𝒜 (b := a) hf
    (Nat.not_le_of_lt hn)
  rw [← GradedAlgebra.proj_apply, ← ha, map_sub] at hproj
  simpa only [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 x.2,
    DirectSum.decompose_of_mem_same 𝒜 y.2] using hproj

/-- Quotienting by a homogeneous element of degree `d` does not change the dimension
of any graded piece of degree less than `d`. Regularity is not needed here. -/
theorem finrank_quotientPiece_span_singleton_of_lt (hf : f ∈ 𝒜 d) {n : ℕ} (hn : n < d) :
    Module.finrank k (quotientPiece 𝒜 (Ideal.span {f}) n) = Module.finrank k (𝒜 n) := by
  rw [quotientPiece_def]
  exact (LinearEquiv.ofBijective _
    (bijective_submoduleMap_span_singleton_of_lt 𝒜 hf hn)).finrank_eq.symm

end CommSemiring

section Field

variable [Field k] [Algebra k A] (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
  {f : A} {d : ℕ}

/-- The Hilbert series of a quotient by a homogeneous non-zero-divisor of degree `d`
is the original Hilbert series multiplied by `1 - t^d`. The coefficients can be taken
in any ring, including `ℤ` to retain dimensions in positive characteristic. No positivity
hypothesis on `d` or connectedness hypothesis on the grading is needed. -/
theorem mk_finrank_quotientPiece_span_singleton {S : Type*} [Ring S]
    [∀ n, Module.Finite k (𝒜 n)] (hf : f ∈ 𝒜 d) (hreg : IsLeftRegular f) :
    PowerSeries.mk (fun n ↦
      (Module.finrank k (quotientPiece 𝒜 (Ideal.span {f}) n) : S)) =
      PowerSeries.mk (fun n ↦ (Module.finrank k (𝒜 n) : S)) * (1 - PowerSeries.X ^ d) := by
  ext n
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    PowerSeries.coeff_mul_X_pow']
  split_ifs with hdn
  · have hdim := finrank_quotientPiece_span_singleton_add 𝒜 hf hreg (n - d)
    rw [Nat.add_sub_of_le hdn] at hdim
    have hcast := congrArg (fun m : ℕ ↦ (m : S)) hdim
    apply eq_sub_iff_add_eq.2
    simpa only [Nat.cast_add, PowerSeries.coeff_mk] using hcast
  · rw [sub_zero]
    exact congrArg (fun m : ℕ ↦ (m : S))
      (finrank_quotientPiece_span_singleton_of_lt 𝒜 hf (Nat.lt_of_not_ge hdn))

end Field

end TauCeti.GradedAlgebra

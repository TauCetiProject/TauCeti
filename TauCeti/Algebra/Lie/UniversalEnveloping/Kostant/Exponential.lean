/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Form
public import TauCeti.RingTheory.Nilpotent.Exp.Basic

/-!
# Root subgroup elements of a Kostant integral form

Let `L` be a Lie algebra over `ℚ` with distinguished root vectors `e : ι → L` and Cartan vectors
`h : κ → L`, and let `U_ℤ = kostantForm e h` be the integral form they generate inside
`UniversalEnvelopingAlgebra ℚ L`. A root vector `eᵢ` need not be nilpotent in the enveloping
algebra itself — a nonzero Chevalley root vector never is, the enveloping algebra being a domain —
but whenever its image under an algebra map `f` is nilpotent — as it is for the
finite-dimensional representations the construction is applied to —

```text
x_i(t) = exp (t • f (ι ℚ (eᵢ))) = ∑ n, tⁿ • f (eᵢ⁽ⁿ⁾)
```

makes sense and has integer coefficients on the images of the root-vector generators of the
Kostant form. The statements below carry no nilpotency hypothesis: `IsNilpotent.exp` is the junk
value `0` at a non-nilpotent element, and `t • f (ι ℚ (eᵢ))` is non-nilpotent whenever `t ≠ 0` and
`f (ι ℚ (eᵢ))` is, since `A` is a `ℚ`-algebra. For such `f` and `t ≠ 0` the membership statements
hold only through this junk value and say nothing about root subgroups: there is no inverse
`x_i(-t)` and no group of automorphisms, and the interpretation as a root subgroup element needs
nilpotency of `f (ι ℚ (eᵢ))`. What is built here is this integral-point family of units, indexed by
`t : ℤ`; a later development is to exhibit it as the `ℤ`-points of a **root subgroup map**
`x_α : 𝔾ₐ → G` of the Chevalley--Demazure construction. No scheme, and no morphism of schemes,
appears below.

The results below record what integrality buys. First, `x_i(t)` lies in the image of the Kostant
form. Second, and this is the form the construction of a Chevalley group actually uses, `x_i(t)`
preserves any additive subgroup of a representation that the Kostant form preserves — an
*admissible lattice*. Both statements are for an arbitrary integer `t`, which is exactly the range
of scalars for which the rational coefficients `tⁿ/n!` of the ordinary exponential series
recombine into integers.

The divided-power expansion, the one-parameter group law `x_i(t) x_i(u) = x_i(t + u)` and the
general stability statements are in `TauCeti/RingTheory/Nilpotent/Exp/Basic.lean`;
nothing here re-proves them. Nothing here assumes the Chevalley relations either: the results hold
for any families of distinguished vectors, and a pinned root datum will supply the specific ones.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.exp_zsmul_mem_map_kostantForm`: the exponential
  `exp (t • f (eᵢ))` lies in the image of the Kostant form; for nilpotent `f (eᵢ)` it is a root
  subgroup element.
* `TauCeti.UniversalEnvelopingAlgebra.dividedPower_apply_mem_of_kostantForm_apply_mem`: divided
  powers of root vectors preserve any Kostant-stable additive subgroup.
* `TauCeti.UniversalEnvelopingAlgebra.exp_zsmul_apply_mem_of_kostantForm_apply_mem`: the
  exponential `exp (t • ρ (eᵢ))`, a root subgroup element when `ρ (eᵢ)` is nilpotent, preserves
  every additive subgroup of a representation that the Kostant form preserves.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {A : Type v} [Ring A] [Algebra ℚ A]

/-! ## Root subgroup elements inside the integral form -/

/-- The exponential `exp (t • f (eᵢ))` lies in the image of the Kostant integral form. When
`f (eᵢ)` is nilpotent this is a **root subgroup element**; otherwise, for `t ≠ 0`, it is the junk
value `0` of `IsNilpotent.exp` and the statement is trivially true.

The exponential is an a priori rational combination of powers of `f (eᵢ)`; the content, for
nilpotent `f (eᵢ)`, is that it is an integral combination of the images of the root-vector
generators `eᵢ⁽ⁿ⁾`. -/
theorem exp_zsmul_mem_map_kostantForm (e : ι → L) (h : κ → L)
    (f : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] A) {i : ι} (t : ℤ) :
    IsNilpotent.exp (t • f (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) ∈
      (kostantForm e h).map (f : _root_.UniversalEnvelopingAlgebra ℚ L →+* A) :=
  exp_zsmul_mem (dividedPower_mem_map_kostantForm e h f i) t

/-! ## Root subgroup elements act on admissible lattices -/

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Every designated root vector's divided powers preserve an additive subgroup stable under the
whole Kostant form. -/
theorem dividedPower_apply_mem_of_kostantForm_apply_mem (e : ι → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V) {M : AddSubgroup V}
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M) (i : ι) (n : ℕ)
    {v : V} (hv : v ∈ M) :
    Associative.dividedPower n
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) v ∈ M := by
  rw [← Associative.map_dividedPower ρ n]
  exact hM _ (dividedPower_mem_kostantForm e h i n) v hv

/-- **A root subgroup element preserves an admissible lattice.** If an additive subgroup `M` of a
representation `V` of `L` is stable under the Kostant integral form, then it is stable under the
exponential `exp (t • ρ (eᵢ))` with `t` an integer, which is a root subgroup element when `ρ (eᵢ)`
is nilpotent. Without nilpotency and for `t ≠ 0` the exponential is the junk value `0`, which
preserves `M` trivially.

Only stability under the divided powers of the single root vector `eᵢ` is used; that weaker
statement is `TauCeti.exp_zsmul_smul_mem`.

For nilpotent `ρ (eᵢ)`, stability of `M` under the whole group generated by these elements
follows, since the inverse of `exp (t • ρ (eᵢ))` is `exp (-t • ρ (eᵢ))`, of the same shape. This
is how a Chevalley group is cut out as a group of automorphisms of a lattice. -/
theorem exp_zsmul_apply_mem_of_kostantForm_apply_mem (e : ι → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V) {M : AddSubgroup V}
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M) {i : ι} (t : ℤ)
    {v : V} (hv : v ∈ M) :
    IsNilpotent.exp (t • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) v ∈ M :=
  exp_zsmul_smul_mem (x := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) (fun n _ hw =>
    dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hw) t hv

end TauCeti.UniversalEnvelopingAlgebra

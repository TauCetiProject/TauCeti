/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basis
public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.Basis
import TauCeti.Algebra.Polynomial.BigOperators

/-!
# The ordered PBW basis of the PBW Rees algebra

Let `b` be an ordered basis of a Lie algebra `L` over a commutative ring `R`. The ordered
products of the Rees generators `j(bᵢ) = ι(bᵢ)t`, with the indices in increasing order, form a
basis of the PBW Rees algebra over the parameter ring `R[t]`. The basis vector at the exponent
vector `n` is `ι(b)ⁿ t^|n|`, the ordered PBW basis vector of `U(L)` times the power of the
parameter given by its total degree.

Consequently, the PBW Rees algebra of a Lie algebra free over `R` is a free, hence flat,
`R[t]`-module: the Rees deformation is a flat family over the parameter line, over any
commutative ring and in every characteristic.

## Main definitions

* `Module.Basis.pbwReesBasis`: the ordered PBW basis of the PBW Rees algebra over `R[t]`.

## Main results

* `Module.Basis.pbwReesBasis_eq_prod_pow`: the basis vector at `n` is the product of the powers
  `j(bᵢ) ^ nᵢ`, with the support traversed in increasing order.
* `Module.Basis.coe_pbwReesBasis_apply`: the same vector is `ι(b)ⁿ t^|n|` in `U(L)[t]`.
* `Module.Basis.coeff_pbwReesBasis_repr_apply`: its coordinates are read off from the PBW
  coordinates of the coefficients.
* The instance `Module.Free R[X] (reesAlgebra R L)`: for `L` free over `R`, the PBW Rees algebra
  is free over `R[t]`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.4,
  for the ordered PBW basis.
-/

public section

open Polynomial TauCeti TauCeti.UniversalEnvelopingAlgebra

namespace Module.Basis

universe u v w

variable {R : Type u} {L : Type v} {ι : Type w}
  [CommRing R] [LieRing L] [LieAlgebra R L] [LinearOrder ι] (b : Basis ι R L)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- **The ordered PBW basis of the PBW Rees algebra.** For an ordered basis `b` of `L`, the
vectors `ι(b)ⁿ t^|n|`, the ordered PBW basis vectors of `U(L)` placed in the parameter degree
given by their total degree, form a basis of the PBW Rees algebra over the parameter ring. -/
noncomputable def pbwReesBasis : Basis (ι →₀ ℕ) R[X] (reesAlgebra R L) :=
  coeffSubalgebra.basis (pbwFiltration R L) (one_mem_pbwFiltration R L 1) b.pbwBasis
    Finsupp.degree b.span_image_pbwBasis_eq_pbwFiltration

/-- The Rees basis vector at `n` is the PBW basis vector at `n` in parameter degree `|n|`. -/
@[simp]
theorem coe_pbwReesBasis_apply (n : ι →₀ ℕ) :
    (b.pbwReesBasis n : U[X]) = monomial n.degree (b.pbwBasis n) :=
  coeffSubalgebra.coe_basis_apply _ _ _ _ _ n

/-- The coefficient of `tʲ` in the Rees coordinate of `f` at `n` is the PBW coordinate at `n` of
the coefficient of `t^(j + |n|)` in `f`. -/
@[simp]
theorem coeff_pbwReesBasis_repr_apply (f : reesAlgebra R L) (n : ι →₀ ℕ) (j : ℕ) :
    (b.pbwReesBasis.repr f n).coeff j = b.pbwBasis.repr ((f : U[X]).coeff (j + n.degree)) n :=
  coeffSubalgebra.coeff_basis_repr_apply _ _ _ _ _ f n j

/-- **The Rees basis vectors are ordered products of Rees generators.** The basis vector at `n`
is the product of `j(bᵢ) ^ nᵢ`, with the support of `n` traversed in increasing order. -/
theorem pbwReesBasis_eq_prod_pow (n : ι →₀ ℕ) :
    b.pbwReesBasis n =
      ((n.support.sort (· ≤ ·)).map fun i ↦ reesGenerator R L (b i) ^ n i).prod := by
  apply Subtype.ext
  rw [coe_pbwReesBasis_apply, pbwBasis_eq_prod_pow, SubmonoidClass.coe_list_prod, List.map_map]
  simp only [Function.comp_def, SubmonoidClass.coe_pow, coe_reesGenerator, monomial_pow,
    one_mul]
  -- The exponents along the sorted support add up to the total degree.
  have hdeg : ((n.support.sort (· ≤ ·)).map n).sum = n.degree := by
    rw [Finsupp.degree_apply, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq,
      Finset.sum_eq_multiset_sum]
  rw [list_prod_map_monomial, hdeg]

/-- The Rees basis vector at the zero exponent is the unit. -/
@[simp]
theorem pbwReesBasis_zero : b.pbwReesBasis 0 = 1 := by
  simp [pbwReesBasis_eq_prod_pow]

/-- The Rees basis vector at a single exponent is a power of one Rees generator. -/
@[simp]
theorem pbwReesBasis_single (i : ι) (k : ℕ) :
    b.pbwReesBasis (Finsupp.single i k) = reesGenerator R L (b i) ^ k := by
  apply Subtype.ext
  simp [monomial_pow]

end Module.Basis

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type*) (L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- **The PBW Rees algebra is free over the parameter ring** when the Lie algebra is free over
`R`. Mathlib's `Module.Flat.of_free` then makes it flat over `R[t]`. -/
instance [Module.Free R L] : Module.Free R[X] (reesAlgebra R L) :=
  let _ : LinearOrder (Module.Free.ChooseBasisIndex R L) := IsWellOrder.linearOrder WellOrderingRel
  .of_basis (Module.Free.chooseBasis R L).pbwReesBasis

end TauCeti.UniversalEnvelopingAlgebra

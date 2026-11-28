/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.KacMoody.Basic

import TauCeti.Algebra.Lie.KacMoody.Auxiliary

/-!
# The Cartan subalgebra embeds in the Kac–Moody algebra

Let `A` be a generalized Cartan matrix: `Aᵢᵢ = 2`, `Aᵢⱼ ≤ 0` for `i ≠ j`, and `Aᵢⱼ = 0` exactly when
`Aⱼᵢ = 0`. For every realization `R` of `A` over a field `K`, the map
`TauCeti.KacMoody.cartanElement R : H → 𝔤` into the Lie algebra presented by the Chevalley and
Serre relations is injective (`TauCeti.KacMoody.cartanElement_injective`). Neither
symmetrizability, nor characteristic zero, nor the independence of the simple roots and coroots
is used.

In this file, `cartanElement_injective` is deduced directly from
`TauCeti.KacMoody.eq_zero_of_quotientTriangular_sum_eq_zero`
(`TauCeti/Algebra/Lie/KacMoody/Auxiliary.lean`), and used to prove that the simple coroots `hᵢ`
and raising and lowering generators `eᵢ`, `fᵢ` are nonzero in
`TauCeti.KacMoody.PresentedLieAlgebra R`.

## Main results

* `TauCeti.KacMoody.cartanElement_injective`: Cartan injectivity of the Kac–Moody algebra of a
  realization of a generalized Cartan matrix.
* `TauCeti.KacMoody.cartanElement_coroot_ne_zero`, `TauCeti.KacMoody.positiveGenerator_ne_zero`
  and `TauCeti.KacMoody.negativeGenerator_ne_zero`: the simple coroots `hᵢ` and the generators
  `eᵢ`, `fᵢ` are nonzero in the Kac–Moody algebra.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Theorem 1.2 (the representation
  of the auxiliary algebra on the tensor algebra) and §3.3 (the Serre elements are killed by the
  opposite generators).
-/

public section

open LieAlgebra

namespace TauCeti

namespace KacMoody

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} {R : CartanRealization (A.map (Int.cast : ℤ → K)) H}

/-- **Cartan injectivity.** For a generalized Cartan matrix `A`, that is `Aᵢᵢ = 2`, `Aᵢⱼ ≤ 0`
for `i ≠ j` and `Aᵢⱼ = 0 → Aⱼᵢ = 0`, the map from a realization `H` of `A` into the Lie algebra
presented by the Chevalley and Serre relations is injective. -/
theorem cartanElement_injective (hA : A.IsGeneralizedCartan) :
    Function.Injective (cartanElement R) :=
  (injective_iff_map_eq_zero _).mpr fun _ hx =>
    (eq_zero_of_quotientTriangular_sum_eq_zero R hA (a := 0) (b := 0) (by simpa using hx)).2.1

section GeneratorsNeZero

variable (hA : A.IsGeneralizedCartan)
include hA

/-- For a generalized Cartan matrix, the simple coroot `hᵢ` is nonzero in the Kac–Moody
algebra. -/
theorem cartanElement_coroot_ne_zero (i : I) : cartanElement R (R.coroot i) ≠ 0 :=
  (map_ne_zero_iff _ (cartanElement_injective hA)).2
    (R.coroot_linearIndependent.ne_zero i)

/-- For a generalized Cartan matrix, the raising generator `eᵢ` is nonzero in the Kac–Moody
algebra. -/
theorem positiveGenerator_ne_zero (i : I) : positiveGenerator R i ≠ 0 :=
  positiveGenerator_ne_zero_of_injective (cartanElement_injective hA) i

/-- For a generalized Cartan matrix, the lowering generator `fᵢ` is nonzero in the Kac–Moody
algebra. -/
theorem negativeGenerator_ne_zero (i : I) : negativeGenerator R i ≠ 0 :=
  negativeGenerator_ne_zero_of_injective (cartanElement_injective hA) i

end GeneratorsNeZero

end KacMoody

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Flat.Localization

/-!
# The rank of a module tensored with a localization

Localizing a module at a submonoid of non-zero-divisors does not change its rank over the base
ring (`IsLocalizedModule.finrank_eq`), and tensoring with the localization `A` of `R` is such a
localization (`IsLocalization.tensorProduct_isLocalizedModule`). Mathlib states this for
`A ⊗[R] M`; this file records the same formula for `M ⊗[R] A`, the form in which a
rationalization `M ⊗[ℤ_p] ℚ_p` of a `ℤ_p`-module is written. Since `M ⊗[R] A` is an `A`-module
on which `R` acts through `A`, its `R`-rank is also its `A`-rank; for `A` a field this is the
dimension of the vector space `M ⊗[R] A`.

Conversely, over a domain the rank detects isomorphisms after passing to the field of fractions:
an injective linear map between finite modules of the same rank becomes an injective map between
vector spaces of the same finite dimension after tensoring with the field of fractions, hence an
isomorphism. This is how an integral lattice of full rank in a module computes its
rationalization. The map may be linear over any `R`-algebra `A`, and its rationalization is then
`A`-linear for the module structure of `TensorProduct.AlgebraTensorModule` on the left factor.

## Main results

* `TauCeti.IsLocalization.finrank_tensorProduct`: `finrank R (M ⊗[R] A) = finrank R M` for a
  localization `A` of `R` at a submonoid of non-zero-divisors.
* `TauCeti.IsFractionRing.rTensor_bijective_of_injective_of_finrank_eq`: an injective linear map
  `f : M → N` with `N` finite and `finrank R M = finrank R N` over a domain `R` becomes bijective
  after tensoring with the field of fractions of `R`.
-/

public section

namespace TauCeti.IsLocalization

open scoped TensorProduct

variable {R : Type*} [CommRing R] (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
  [IsLocalization S A] (hS : S ≤ nonZeroDivisors R) (M : Type*) [AddCommGroup M] [Module R M]

include hS in
/-- Tensoring with a localization at a submonoid of non-zero-divisors does not change the rank
over the base ring. -/
theorem finrank_tensorProduct : Module.finrank R (M ⊗[R] A) = Module.finrank R M :=
  (TensorProduct.comm R M A).finrank_eq.trans
    (IsLocalizedModule.finrank_eq S (TensorProduct.mk R A M 1) hS)

end TauCeti.IsLocalization

namespace TauCeti.IsFractionRing

open scoped TensorProduct

variable {R : Type*} [CommRing R] [IsDomain R] (Q : Type*) [CommRing Q] [Algebra R Q]
  [IsFractionRing R Q] {A : Type*} [Ring A] [Algebra R A]
  {M N : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] [Module.Finite R N]

/-- **Full-rank injections become isomorphisms over the field of fractions.** Let `R` be a domain
with field of fractions `Q`, and `f : M → N` an injective `A`-linear map, for an `R`-algebra `A`,
where `N` is finite over `R` and `M` has the same rank as `N`. Then `f ⊗ 𝟙 Q` is bijective: it is
injective because `Q` is flat over `R`, and it is an injective map between `Q`-vector spaces of
the same finite dimension. -/
theorem rTensor_bijective_of_injective_of_finrank_eq (f : M →ₗ[A] N)
    (hf : Function.Injective f) (h : Module.finrank R M = Module.finrank R N) :
    Function.Bijective (TensorProduct.AlgebraTensorModule.rTensor R Q f) := by
  have := _root_.IsLocalization.flat Q (nonZeroDivisors R)
  let := IsFractionRing.toField R (K := Q)
  -- The base change `g` of `f` to `Q` is an injective `Q`-linear map between `Q`-vector spaces
  -- of the same finite dimension, hence bijective.
  set g := (f.restrictScalars R).baseChange Q
  have hg : Function.Injective g := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hf
  have := FiniteDimensional.of_injective g hg
  have hg' := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    rw [(TensorProduct.isBaseChange R M Q).finrank_eq,
      (TensorProduct.isBaseChange R N Q).finrank_eq, h])).mp hg
  -- `f ⊗ 𝟙 Q` is `g` up to the commutativity of the tensor product.
  have : ⇑(TensorProduct.AlgebraTensorModule.rTensor R Q f) =
      TensorProduct.comm R Q N ∘ g ∘ TensorProduct.comm R M Q := by
    ext x
    simp [g, LinearMap.baseChange_eq_ltensor, LinearMap.lTensor_comm]
  rw [this]
  exact ((TensorProduct.comm R Q N).bijective.comp ⟨hg, hg'⟩).comp
    (TensorProduct.comm R M Q).bijective

end TauCeti.IsFractionRing

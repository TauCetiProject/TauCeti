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
import TauCeti.Algebra.Module.LocalizedModule.Lift

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

In the other direction, an `A`-linear map of rationalizations `M ⊗ Q → N ⊗ Q` becomes integral
after multiplying by a non-zero-divisor of `R`, provided `M` is finitely generated over `A` and
`N` is torsion-free. So a rational embedding of lattices restricts, after scaling, to an integral
embedding.

## Main results

* `TauCeti.IsLocalization.finrank_tensorProduct`: `finrank R (M ⊗[R] A) = finrank R M` for a
  localization `A` of `R` at a submonoid of non-zero-divisors.
* `TauCeti.IsFractionRing.rTensor_bijective_of_injective_of_finrank_eq`: an injective linear map
  `f : M → N` with `N` finite and `finrank R M = finrank R N` over a domain `R` becomes bijective
  after tensoring with the field of fractions of `R`.
* `TauCeti.IsFractionRing.tmul_one_injective`: a torsion-free module embeds in its
  rationalization.
* `TauCeti.IsFractionRing.exists_linearMap_tmul_one_eq_smul`: a multiple of an `A`-linear map of
  rationalizations by a non-zero-divisor is the rationalization of an `A`-linear map.
* `TauCeti.IsFractionRing.exists_injective_linearMap_of_injective`: an injective `A`-linear map of
  rationalizations of torsion-free modules gives an injective `A`-linear map of the modules.
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

namespace TauCeti.IsFractionRing

open scoped TensorProduct nonZeroDivisors

variable {R : Type*} [CommRing R] (Q : Type*) [CommRing Q] [Algebra R Q] [IsFractionRing R Q]
  {A : Type*} [Ring A] [Algebra R A]
  {M N : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- A torsion-free module embeds in its rationalization: `m ↦ m ⊗ 1` is injective, since it is the
localization of `M` at the non-zero-divisors of `R`. -/
theorem tmul_one_injective [Module.IsTorsionFree R M] :
    Function.Injective fun m : M ↦ m ⊗ₜ[R] (1 : Q) := by
  have h := (IsLocalizedModule.injective_iff_isRegular R⁰
    ((TensorProduct.comm R Q M).toLinearMap ∘ₗ TensorProduct.mk R Q M 1)).mpr
      fun c ↦ IsRegular.isSMulRegular (isRegular_iff_mem_nonZeroDivisors.mpr c.2)
  simpa [Function.comp_def] using h

/-- **Clearing denominators of a rational map.** Let `R` have field of fractions `Q`, let `A` be an
`R`-algebra, and let `φ : M ⊗ Q → N ⊗ Q` be `A`-linear, where `M` is finitely generated over `A`
and `N` is torsion-free over `R`. Then some multiple `s • φ` by a non-zero-divisor `s` of `R` is
the rationalization of an `A`-linear map `f : M → N`, in the sense that
`f m ⊗ 1 = s • φ (m ⊗ 1)`. -/
theorem exists_linearMap_tmul_one_eq_smul [Module.Finite A M] [Module.IsTorsionFree R N]
    (φ : M ⊗[R] Q →ₗ[A] N ⊗[R] Q) :
    ∃ s ∈ R⁰, ∃ f : M →ₗ[A] N, ∀ m, f m ⊗ₜ[R] (1 : Q) = s • φ (m ⊗ₜ 1) := by
  -- `n ↦ n ⊗ 1` is the localization of `N` at the non-zero-divisors, and it is injective because
  -- `N` is torsion-free, so the values of `φ` on `M` lift to `N` after clearing denominators.
  let ι : N →ₗ[A] N ⊗[R] Q := (TensorProduct.AlgebraTensorModule.mk R A N Q).flip 1
  have : IsLocalizedModule R⁰ (ι.restrictScalars R) := by
    have : ι.restrictScalars R =
        (TensorProduct.comm R Q N).toLinearMap ∘ₗ TensorProduct.mk R Q N 1 := by
      ext n
      simp [ι]
    rw [this]
    infer_instance
  obtain ⟨f, s, hf⟩ := Module.Finite.exists_lift_of_isLocalizedModule_of_injective R⁰
    (g := ι) (tmul_one_injective Q) (φ ∘ₗ (TensorProduct.AlgebraTensorModule.mk R A M Q).flip 1)
  exact ⟨s, s.2, f, fun m ↦ by simpa [ι, Submonoid.smul_def] using congr($hf m)⟩

/-- **Rational embeddings of lattices come from integral ones.** If `M` is finitely generated over
the `R`-algebra `A`, both `M` and `N` are torsion-free over `R`, and some `A`-linear map of
rationalizations `M ⊗ Q → N ⊗ Q` is injective, then so is some `A`-linear map `M → N`. -/
theorem exists_injective_linearMap_of_injective [Module.Finite A M] [Module.IsTorsionFree R M]
    [Module.IsTorsionFree R N] (φ : M ⊗[R] Q →ₗ[A] N ⊗[R] Q) (hφ : Function.Injective φ) :
    ∃ f : M →ₗ[A] N, Function.Injective f := by
  obtain ⟨s, hs, f, hf⟩ := exists_linearMap_tmul_one_eq_smul Q φ
  have key (m : M) : φ ((s • m) ⊗ₜ 1) = f m ⊗ₜ 1 := by
    rw [← TensorProduct.smul_tmul', LinearMap.map_smul_of_tower, hf]
  refine ⟨f, fun m m' hmm' ↦ IsRegular.isSMulRegular (isRegular_iff_mem_nonZeroDivisors.mpr hs)
    (tmul_one_injective Q (hφ ?_))⟩
  simp only [key, hmm']

end TauCeti.IsFractionRing

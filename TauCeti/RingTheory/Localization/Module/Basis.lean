/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Module

/-!
# Promoting a basis to the fraction field along a spanning injection

Let `K` be the fraction field of a commutative ring `R`, `b` an `R`-basis of a module `M`, and
`f : M → V` an injective `R`-linear map into a `K`-vector space whose image spans `V` over `K`.
Then the family `f ∘ b` is a `K`-basis of `V`, and the `K`-coordinates of `f m` in it are the
images in `K` of the `R`-coordinates of `m` in `b`. For instance, a `ℤ`-basis of an order `O` in a
finite-dimensional `ℚ`-algebra `E` with `ℚ`-span `E` is a `ℚ`-basis of `E`.

Mathlib's `Module.Basis.ofIsLocalizedModule` gives the same basis when `f` is known to be a
localization map; here only injectivity and spanning are assumed.

## Main definitions

* `Module.Basis.ofFractionRingOfSpan`: the `K`-basis `f ∘ b` of `V`.

## Main results

* `Module.Basis.ofFractionRingOfSpan_apply`: its vectors are `f (b i)`.
* `Module.Basis.ofFractionRingOfSpan_repr_apply`: the coordinates of `f m` are the images of
  those of `m`.
-/

public section

open Submodule

namespace Module.Basis

variable {R K M V ι : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup M] [Module R M] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/-- The `K`-basis of `V` formed by the image of an `R`-basis `b` of `M` under an injective
`R`-linear map `f : M → V` whose image spans `V` over the fraction field `K` of `R`. -/
noncomputable def ofFractionRingOfSpan (b : Basis ι R M) (f : M →ₗ[R] V)
    (hf : Function.Injective f) (hspan : span K (Set.range f) = ⊤) : Basis ι K V :=
  .mk ((LinearIndependent.iff_fractionRing R K).1 (b.linearIndependent.map'
    f (LinearMap.ker_eq_bot.2 hf))) <| by
      rw [← hspan, span_le, Set.range_comp]
      simpa [← Submodule.map_span, b.span_eq, LinearMap.coe_range] using
        SetLike.coe_subset_coe.2 (span_le_restrictScalars R K (f '' Set.range b))

/-- The vectors of `Module.Basis.ofFractionRingOfSpan` are the images `f (b i)`. -/
@[simp]
theorem ofFractionRingOfSpan_apply (b : Basis ι R M) (f : M →ₗ[R] V)
    (hf : Function.Injective f) (hspan : span K (Set.range f) = ⊤) (i : ι) :
    b.ofFractionRingOfSpan f hf hspan i = f (b i) := by
  simp [ofFractionRingOfSpan]

/-- The coordinates of `f m` in `Module.Basis.ofFractionRingOfSpan` are the images in `K` of the
coordinates of `m` in `b`. -/
@[simp]
theorem ofFractionRingOfSpan_repr_apply [Finite ι] (b : Basis ι R M) (f : M →ₗ[R] V)
    (hf : Function.Injective f) (hspan : span K (Set.range f) = ⊤) (m : M) (i : ι) :
    (b.ofFractionRingOfSpan f hf hspan).repr (f m) i = algebraMap R K (b.repr m i) := by
  have := Fintype.ofFinite ι
  have hm : f m = ∑ j, algebraMap R K (b.repr m j) • b.ofFractionRingOfSpan f hf hspan j := by
    calc f m = f (∑ j, b.repr m j • b j) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, ofFractionRingOfSpan_apply, algebraMap_smul]
  rw [hm, Basis.repr_sum_self]

end Module.Basis

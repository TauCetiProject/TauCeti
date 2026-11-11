/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Automorphisms acting on the ring of integers

A ring automorphism of a field restricts to its ring of integers, because it preserves
integrality. This file records how that restricted action relates to the ambient one: the
structure map `𝓞 K → K` is equivariant, carrying `σ • z` to `σ` applied to the image of `z`.
It also records that restriction to a normal subfield commutes with the map between the two
rings of integers.

For a tower `F / K` of fields it also records that any group acting on `F` by ring automorphisms
that fix `K` pointwise, such as `Gal(F/K)`, acts on `𝓞 F` commuting with the `𝓞 K`-scalar action:
such an automorphism fixes the image of `𝓞 K`. Mathlib supplies the corresponding
`SMulCommClass` only over the base `ℤ` (`integralClosure`'s own instance, with `ℤ` the ring `𝓞 F`
is integral over), which is what a Frobenius over `ℚ` needs; a *relative* Frobenius over a
general base `K` needs this one.

`𝓞 K` is the integral closure of `ℤ`, and any ring automorphism of `K` preserves `ℤ`-integrality,
so the base ring `R` over which `σ` is linear is irrelevant to both statement and proof; it is a
free parameter, specialized to `ℚ` by the callers. Nothing here needs `K` to be finite-dimensional
either, so `[NumberField K]` is not assumed.

This is the `AlgEquiv` specialization of Mathlib's `integralClosure.coe_smul`, which is stated
for an arbitrary `[Group G] [MulSemiringAction G K]` and therefore cannot phrase the right-hand
side as function application. Callers want exactly that applied form, so the specialization is
recorded once here rather than reconstructed at each use site.

## Main results

* `NumberField.algebraMap_smul_eq_apply`: `algebraMap (𝓞 K) K (σ • z) = σ (algebraMap (𝓞 K) K z)`.
* `NumberField.algebraMap_restrictNormal_smul`: mapping the action of a restricted automorphism
  into the top ring of integers gives the action of the original automorphism.
* `NumberField.RingOfIntegers.smulCommClass`: a group acting on `F` and commuting with the
  `K`-action, such as `Gal(F/K)`, acts on `𝓞 F` commuting with the `𝓞 K`-action.
* `NumberField.RingOfIntegers.unitsMulDistribMulAction`: `Gal(F/K)` acts on the units
  `(𝓞 F)ˣ`.
* `AlgEquiv.mapAlgEquiv_symm_autCongr_smul`: restriction to rings of integers intertwines
  conjugation of automorphisms along an algebra equivalence.
-/

public section

open scoped NumberField Pointwise

namespace NumberField

variable {R K : Type*} [CommSemiring R] [Field K] [Algebra R K]

/-- **`algebraMap` intertwines the automorphism actions on `𝓞 K` and on `K`.** The action on the
ring of integers is the restriction of the action on `K` (`integralClosure.coe_smul`), so the
structure map sends `σ • z` to `σ` applied to the image of `z`.

Not named `algebraMap_smul`: that is Mathlib's unrelated `algebraMap R A r • m = r • m`. -/
@[simp] theorem algebraMap_smul_eq_apply (σ : K ≃ₐ[R] K) (z : 𝓞 K) :
    algebraMap (𝓞 K) K (σ • z) = σ (algebraMap (𝓞 K) K z) :=
  -- `integralClosure.coe_smul` proves this up to two definitional identifications:
  -- `RingOfIntegers.val` is an `abbrev` for `algebraMap`, and `AlgEquiv.smul_def` is `rfl`.
  integralClosure.coe_smul σ z

variable {M L : Type*} [Field M] [Field L] [Algebra K M] [Algebra M L] [Algebra K L]
  [IsScalarTower K M L] [Normal K M]

/-- **Restriction of automorphisms commutes with the map between rings of integers.** If `M/K`
is normal inside `L`, then acting on `𝓞 M` by the restriction of `σ ∈ Gal(L/K)` and mapping to
`𝓞 L` agrees with first mapping and then acting by `σ`. -/
@[simp]
theorem algebraMap_restrictNormal_smul (σ : L ≃ₐ[K] L) (x : 𝓞 M) :
    algebraMap (𝓞 M) (𝓞 L) (σ.restrictNormal M • x) =
      σ • algebraMap (𝓞 M) (𝓞 L) x := by
  ext
  -- Route both sides through `M`, where `AlgEquiv.restrictNormal_commutes` applies.
  simp [← IsScalarTower.algebraMap_apply (𝓞 M) (𝓞 L) L,
    IsScalarTower.algebraMap_apply (𝓞 M) M L]

variable {F : Type*} [Field F] [Algebra K F]

/-- **A `K`-linear action on `F` restricts to `𝓞 F` commuting with the `𝓞 K`-action.** A group
acting on `F` by ring automorphisms that commute with the `K`-action, such as `Gal(F/K)`, fixes
`K` pointwise, so it fixes the image of `𝓞 K` in `F` and therefore commutes with multiplication
by it.

This is the relative form of Mathlib's `SMulCommClass G R (integralClosure R K)`, which for
`𝓞 F = integralClosure ℤ F` gives only the base ring `ℤ`. Neither field has to be a number
field. -/
instance RingOfIntegers.smulCommClass {G : Type*} [Group G] [MulSemiringAction G F]
    [SMulCommClass G K F] : SMulCommClass G (𝓞 K) (𝓞 F) where
  smul_comm g r x := by
    ext
    -- Expand both scalar actions into multiplication and push `g` through the product; the
    -- remaining factor is the image of `𝓞 K`, which is routed through `K`, fixed by `g`.
    simp only [Algebra.smul_def, map_mul, algebraMap.smul', smul_mul',
      ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 F) F, IsScalarTower.algebraMap_apply (𝓞 K) K F,
      smul_algebraMap]

variable (K F) in
/-- **The Galois action on the units of `𝓞 F`.** An automorphism of `F` over `K` acts on `𝓞 F`
by ring automorphisms, so it acts on the units `(𝓞 F)ˣ`, multiplicatively. Mathlib's
`Units.mulDistribMulActionRight` is not a global instance, since for a group acting on itself by
conjugation it would clash with `ConjAct`; here the acting group is the automorphism group, so
there is no such clash. -/
instance RingOfIntegers.unitsMulDistribMulAction : MulDistribMulAction (F ≃ₐ[K] F) (𝓞 F)ˣ :=
  Units.mulDistribMulActionRight

end NumberField

namespace AlgEquiv

variable {R K L : Type*} [Field R] [Field K] [Field L] [Algebra R K] [Algebra R L]

/-- Restriction to rings of integers intertwines conjugation of automorphisms along an algebra
equivalence. -/
theorem mapAlgEquiv_symm_autCongr_smul (e : K ≃ₐ[R] L) (σ : K ≃ₐ[R] K)
    (x : 𝓞 L) :
    (NumberField.RingOfIntegers.mapAlgEquiv e).symm (autCongr e σ • x) =
      σ • (NumberField.RingOfIntegers.mapAlgEquiv e).symm x := by
  apply NumberField.RingOfIntegers.ext
  -- `mapAlgEquiv` has no application lemma; after applying extensionality, unfold its restriction
  -- to the ambient fields, where `autCongr` is visibly conjugation by `e`.
  change e.symm ((autCongr e σ • x : 𝓞 L) : L) = σ (e.symm (x : L))
  simp

end AlgEquiv

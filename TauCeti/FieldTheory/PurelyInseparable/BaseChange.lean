/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import TauCeti.RingTheory.Ideal.PrincipalUnitGroup
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Base change of a purely inseparable extension and its units

Let `K / k` be a purely inseparable extension and `L` a field over `k`. Since `Spec K → Spec k`
is a universal homeomorphism, `L ⊗[k] K` has exactly one prime ideal: it is a local ring whose
maximal ideal `𝔪` is its nilradical. When `K / k` is finite, `L ⊗[k] K` is finite-dimensional
over `L`, so `𝔪` is nilpotent.

Given a `k`-embedding `ι : K → L`, which exists for instance when `L` is algebraically closed and
is then unique, multiplication `a ⊗ x ↦ a ι(x)` is a surjection `L ⊗[k] K → L` of `L`-algebras.
Its kernel is `𝔪`, so the residue field of `L ⊗[k] K` is `L` and `L ⊗[k] K = L ⊕ 𝔪`; hence, when
`K / k` is finite, `dim_L 𝔪 = [K : k] - 1`. On units, the multiplication map is surjective with
kernel the principal unit group `1 + 𝔪`:

```text
1 → 1 + 𝔪 → (L ⊗[k] K)ˣ → Lˣ → 1.
```

The subgroup `1 + 𝔪` is filtered by the principal unit groups `1 + 𝔪 ^ n`, whose successive
quotients are the additive groups `𝔪 ^ n ⧸ 𝔪 ^ (n + 1)`
(`Ideal.principalUnitGroupPowQuotientEquiv`). When `K / k` is finite, `𝔪` is nilpotent, so this
filtration reaches the trivial group. For finite `K / k` and `L` an algebraic closure of `k`,
`(L ⊗[k] K)ˣ` is the group of `L`-points of the Weil restriction `R_{K/k} 𝔾ₘ`, and the
exact sequence above is the rational-point form of its extension of `𝔾ₘ` by a unipotent group of
dimension `[K : k] - 1`, the reason `R_{K/k} 𝔾ₘ` is not reductive when `K ≠ k`. This file treats
only the ring and its units, not the group scheme.

## Main results

* `TauCeti.IsPurelyInseparable.subsingleton_primeSpectrum_tensorProduct` and
  `TauCeti.IsPurelyInseparable.isLocalRing_tensorProduct`: `L ⊗[k] K` has a unique prime ideal,
  and is a local ring.
* `TauCeti.IsPurelyInseparable.nilradical_tensorProduct`: its maximal ideal is its nilradical.
* `TauCeti.IsPurelyInseparable.isNilpotent_maximalIdeal_tensorProduct`: for finite `K / k` the
  maximal ideal is nilpotent.
* `TauCeti.IsPurelyInseparable.ker_productLeftAlgHom`: the kernel of multiplication
  `L ⊗[k] K → L` along a `k`-embedding `K → L` is the maximal ideal.
* `TauCeti.IsPurelyInseparable.finrank_maximalIdeal_tensorProduct_add_one`: for finite `K / k`
  admitting a `k`-embedding `K → L`, the maximal ideal has dimension `[K : k] - 1` over `L`.
* `TauCeti.IsPurelyInseparable.ker_unitsMap_productLeftAlgHom`: on units, multiplication along a
  `k`-embedding `K → L` has kernel `1 + 𝔪`.
* `TauCeti.IsPurelyInseparable.unitsTensorProductQuotientEquiv`: for a `k`-embedding `K → L`,
  `(L ⊗[k] K)ˣ ⧸ (1 + 𝔪) ≃* Lˣ`.
* `TauCeti.IsPurelyInseparable.exists_principalUnitGroup_pow_maximalIdeal_tensorProduct_eq_bot`:
  for finite `K / k`, the filtration of `1 + 𝔪` by the subgroups `1 + 𝔪 ^ n` reaches the trivial
  group.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), §1.1.
* J. S. Milne, *Algebraic Groups* (2017), §2.i, for Weil restriction.
-/

public section

open TensorProduct IsLocalRing

namespace TauCeti.IsPurelyInseparable

variable (k K L : Type*) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]

/-- The base change of a purely inseparable extension to a field has exactly one prime ideal. -/
instance subsingleton_primeSpectrum_tensorProduct [IsPurelyInseparable k K] :
    Subsingleton (PrimeSpectrum (L ⊗[k] K)) :=
  (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k K L).injective.subsingleton

/-- The base change of a purely inseparable extension to a field is a local ring. -/
instance isLocalRing_tensorProduct [IsPurelyInseparable k K] : IsLocalRing (L ⊗[k] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (L ⊗[k] K)
  refine .of_unique_max_ideal ⟨m, hm, fun I hI ↦ ?_⟩
  exact congrArg PrimeSpectrum.asIdeal
    (Subsingleton.elim (⟨I, hI.isPrime⟩ : PrimeSpectrum _) ⟨m, hm.isPrime⟩)

/-- The maximal ideal of the base change of a purely inseparable extension to a field is its
nilradical. -/
theorem nilradical_tensorProduct [IsPurelyInseparable k K] :
    nilradical (L ⊗[k] K) = maximalIdeal (L ⊗[k] K) :=
  Ring.KrullDimLE.nilradical_eq_maximalIdeal _

/-- The maximal ideal of the base change of a finite purely inseparable extension to a field is
nilpotent. -/
theorem isNilpotent_maximalIdeal_tensorProduct [IsPurelyInseparable k K] [FiniteDimensional k K] :
    IsNilpotent (maximalIdeal (L ⊗[k] K)) := by
  have : IsArtinianRing (L ⊗[k] K) := IsArtinianRing.of_finite L (L ⊗[k] K)
  rw [← nilradical_tensorProduct]
  exact IsArtinianRing.isNilpotent_nilradical

/-- The filtration of `1 + 𝔪` by the principal unit groups of the powers of the maximal ideal `𝔪`
of `L ⊗[k] K` reaches the trivial group, for a finite purely inseparable extension `K / k`. -/
theorem exists_principalUnitGroup_pow_maximalIdeal_tensorProduct_eq_bot [IsPurelyInseparable k K]
    [FiniteDimensional k K] :
    ∃ n : ℕ, (maximalIdeal (L ⊗[k] K) ^ n).principalUnitGroup = ⊥ := by
  obtain ⟨n, hn⟩ := isNilpotent_maximalIdeal_tensorProduct k K L
  exact ⟨n, by rw [hn, Ideal.zero_eq_bot, Ideal.principalUnitGroup_bot]⟩

variable {k K L}

/-- For a purely inseparable extension `K / k` and a `k`-embedding `ι : K → L`, the kernel of
multiplication `L ⊗[k] K → L`, `a ⊗ x ↦ a ι(x)`, is the maximal ideal. In particular the residue
field of `L ⊗[k] K` is `L`. -/
theorem ker_productLeftAlgHom [IsPurelyInseparable k K] (ι : K →ₐ[k] L) :
    RingHom.ker (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId L L) ι) =
      maximalIdeal (L ⊗[k] K) :=
  eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ fun a ↦ ⟨a ⊗ₜ 1, by simp⟩)

variable (k K L) in
/-- The maximal ideal of `L ⊗[k] K` has dimension `[K : k] - 1` over `L`, for a finite purely
inseparable extension `K / k` that embeds into `L`. -/
theorem finrank_maximalIdeal_tensorProduct_add_one [IsPurelyInseparable k K]
    [FiniteDimensional k K] [Nonempty (K →ₐ[k] L)] :
    Module.finrank L ((maximalIdeal (L ⊗[k] K)).restrictScalars L) + 1 = Module.finrank k K := by
  let ι : K →ₐ[k] L := Classical.arbitrary _
  let φ := (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId L L) ι).toLinearMap
  have hker : LinearMap.ker φ = (maximalIdeal (L ⊗[k] K)).restrictScalars L := by
    ext x
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, ← ker_productLeftAlgHom ι,
      RingHom.mem_ker]
    rfl
  have hrange : LinearMap.range φ = ⊤ :=
    LinearMap.range_eq_top.mpr fun a ↦ ⟨a ⊗ₜ 1, by simp [φ]⟩
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hker, hrange, finrank_top, Module.finrank_self, Module.finrank_baseChange] at h
  omega

/-- For a purely inseparable extension `K / k` and a `k`-embedding `ι : K → L`, the kernel of
multiplication `(L ⊗[k] K)ˣ → Lˣ` on units is the principal unit group `1 + 𝔪` of the maximal
ideal. -/
theorem ker_unitsMap_productLeftAlgHom [IsPurelyInseparable k K] (ι : K →ₐ[k] L) :
    (Units.map ((Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId L L) ι :
        L ⊗[k] K →+* L)).toMonoidHom).ker =
      (maximalIdeal (L ⊗[k] K)).principalUnitGroup := by
  rw [← ker_productLeftAlgHom ι]
  exact (Ideal.principalUnitGroup_ker _).symm

/-- For a purely inseparable extension `K / k` and a `k`-embedding `ι : K → L`, the units of
`L ⊗[k] K` modulo the principal unit group `1 + 𝔪` of the maximal ideal are `Lˣ`, through
multiplication `a ⊗ x ↦ a ι(x)`, which on units is split by the inclusion of `L`. -/
noncomputable def unitsTensorProductQuotientEquiv [IsPurelyInseparable k K] (ι : K →ₐ[k] L) :
    (L ⊗[k] K)ˣ ⧸ (maximalIdeal (L ⊗[k] K)).principalUnitGroup ≃* Lˣ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_unitsMap_productLeftAlgHom ι).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ fun v ↦
      ⟨Units.map (algebraMap L (L ⊗[k] K)).toMonoidHom v, Units.ext <| by simp⟩)

@[simp]
theorem unitsTensorProductQuotientEquiv_mk [IsPurelyInseparable k K] (ι : K →ₐ[k] L)
    (u : (L ⊗[k] K)ˣ) :
    unitsTensorProductQuotientEquiv ι u =
      Units.map ((Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId L L) ι :
        L ⊗[k] K →+* L)).toMonoidHom u := by
  rw [unitsTensorProductQuotientEquiv, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  exact TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk _ _ u

end TauCeti.IsPurelyInseparable

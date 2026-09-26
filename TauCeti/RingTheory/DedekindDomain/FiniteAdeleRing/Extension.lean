/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# The finite adele ring along an integral extension of Dedekind domains

Let `B / R` be an integral extension of Dedekind domains with fraction fields `L / K`. Every
height-one prime `w` of `B` lies over the height-one prime `w.under R` of `R`, and the completion
maps `K_{w.under R} → L_w` (`HeightOneSpectrum.adicCompletionExtension`) carry integers to
integers. Placewise, they assemble into a ring homomorphism of finite adele rings
`𝔸_K^∞ → 𝔸_L^∞`, sending `(a_v)_v` to `(a_{w.under R})_w`. The restricted-product condition is
preserved because only finitely many primes of `B` lie over each prime of `R`.

This is the map along which the finite adeles and finite ideles of `K` and `L` are compared, for
instance under base change and norm.

## Main results

* `IsDedekindDomain.finiteAdeleExtension`: the extension map `𝔸_K^∞ →+* 𝔸_L^∞`.
* `IsDedekindDomain.continuous_finiteAdeleExtension`: it is continuous.
* `IsDedekindDomain.finiteAdeleExtension_algebraMap`: it extends `K → L` along the diagonal
  embeddings.
* `IsDedekindDomain.eq_finiteAdeleExtension_of_continuous`: it is the only continuous ring
  homomorphism with that property, because `K` is dense in its finite adeles.
* `IsDedekindDomain.finiteAdeleExtension_comp`: the extension maps compose in towers.
-/

public section

open Filter

namespace IsDedekindDomain

variable (R K B L : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing B] [IsDedekindDomain B] [Algebra R B] [Algebra.IsIntegral R B]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Algebra B L] [IsFractionRing B L]
  [IsScalarTower R B L]

/-- The extension map of finite adele rings along an integral extension `B / R` of Dedekind
domains: the component at a height-one prime `w` of `B` is the image of the component at
`w.under R` under the completion map `K_{w.under R} → L_w`. -/
noncomputable def finiteAdeleExtension : FiniteAdeleRing R K →+* FiniteAdeleRing B L :=
  RestrictedProduct.mapAlongRingHom _ _ (HeightOneSpectrum.under R)
    (by
      have := FaithfulSMul.of_field_isFractionRing R B K L
      exact HeightOneSpectrum.tendsto_under_cofinite R B)
    (fun w ↦ HeightOneSpectrum.adicCompletionExtension K L (w.under R) w)
    (Eventually.of_forall fun w x hx ↦
      HeightOneSpectrum.adicCompletionExtension_mem_adicCompletionIntegers K L (w.under R) w
        ⟨x, hx⟩)

variable {R K B L} in
/-- The component of `finiteAdeleExtension R K B L a` at `w` is the image of the component of `a`
at `w.under R`. -/
@[simp]
theorem finiteAdeleExtension_apply (a : FiniteAdeleRing R K) (w : HeightOneSpectrum B) :
    finiteAdeleExtension R K B L a w =
      HeightOneSpectrum.adicCompletionExtension K L (w.under R) w (a (w.under R)) :=
  (rfl)

/-- The extension map of finite adele rings is continuous. -/
@[continuity, fun_prop]
theorem continuous_finiteAdeleExtension : Continuous (finiteAdeleExtension R K B L) := by
  apply RestrictedProduct.mapAlong_continuous
  case φ_cont => exact fun w ↦ HeightOneSpectrum.continuous_adicCompletionExtension K L _ w
  case hφ => exact Eventually.of_forall fun w x hx ↦
    HeightOneSpectrum.adicCompletionExtension_mem_adicCompletionIntegers K L _ w ⟨x, hx⟩
  case hf =>
    have := FaithfulSMul.of_field_isFractionRing R B K L
    exact HeightOneSpectrum.tendsto_under_cofinite R B

/-- The extension map of finite adele rings extends `K → L` along the diagonal embeddings. -/
@[simp]
theorem finiteAdeleExtension_algebraMap (x : K) :
    finiteAdeleExtension R K B L (algebraMap K (FiniteAdeleRing R K) x) =
      algebraMap L (FiniteAdeleRing B L) (algebraMap K L x) := by
  ext w
  rw [finiteAdeleExtension_apply, FiniteAdeleRing.algebraMap_apply,
    FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.adicCompletionExtension_coe]

/-- `finiteAdeleExtension` is the only continuous ring homomorphism of finite adele rings extending
`K → L` along the diagonal embeddings: by strong approximation `K` is dense in its finite adeles,
and the finite adeles of `L` are Hausdorff. -/
theorem eq_finiteAdeleExtension_of_continuous {f : FiniteAdeleRing R K →+* FiniteAdeleRing B L}
    (hf : Continuous f)
    (hfK : ∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) :
    f = finiteAdeleExtension R K B L :=
  DFunLike.coe_injective <| (FiniteAdeleRing.denseRange_algebraMap R K).equalizer hf
    (continuous_finiteAdeleExtension R K B L) (funext fun x ↦ by simp [hfK])

/-- The extension maps of finite adele rings compose in a tower `K ⊆ L ⊆ M`. -/
theorem finiteAdeleExtension_comp (C M : Type*) [CommRing C] [IsDedekindDomain C] [Algebra B C]
    [Algebra.IsIntegral B C] [Field M] [Algebra L M] [Algebra B M] [IsScalarTower B L M]
    [Algebra C M] [IsFractionRing C M] [IsScalarTower B C M] [Algebra R C]
    [Algebra.IsIntegral R C] [Algebra K M] [Algebra R M] [IsScalarTower R K M]
    [IsScalarTower R C M] [IsScalarTower K L M] :
    (finiteAdeleExtension B L C M).comp (finiteAdeleExtension R K B L) =
      finiteAdeleExtension R K C M :=
  eq_finiteAdeleExtension_of_continuous R K C M
    ((continuous_finiteAdeleExtension B L C M).comp (continuous_finiteAdeleExtension R K B L))
    fun x ↦ by simp [← IsScalarTower.algebraMap_apply]

end IsDedekindDomain

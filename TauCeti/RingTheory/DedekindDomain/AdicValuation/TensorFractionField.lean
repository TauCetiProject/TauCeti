/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# The completion of the fraction field as a tensor product

Let `A` be a Dedekind domain with fraction field `K`, and let `v` be a height-one prime of `A`.
Inverting the nonzero elements of `A` in the ring of integers `𝒪_v` of the completion `K_v`
gives back `K_v`: the canonical map

```text
𝒪_v ⊗[A] K → K_v,   c ⊗ x ↦ c x
```

is an isomorphism of `𝒪_v`-algebras. It is injective because `K` is a localization of `A`, so
every element of `𝒪_v ⊗[A] K` becomes a pure tensor `c ⊗ 1` after multiplication by a nonzero
element of `A`; it is surjective because every element of `K_v` is an element of `𝒪_v` times an
element of `K` of the same valuation. Under this isomorphism the image `𝒪_v ⊗ 1` of `𝒪_v` is
exactly `𝒪_v ⊆ K_v`.

This identifies the completions `𝒪_v ⊗[A] B` of a `K`-algebra `B` used for lattices and ideles
over `A` with the classical completions `K_v ⊗[K] B` in the case `B = K`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersTensorEquiv`: the isomorphism
  `𝒪_v ⊗[A] K ≃ₐ[𝒪_v] K_v`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersTensorEquiv_tmul`: it sends `c ⊗ x`
  to `c x`.
* `IsDedekindDomain.HeightOneSpectrum.valued_adicCompletionIntegersTensorEquiv_one_tmul`: the
  image of `1 ⊗ x` has the valuation of `x`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersTensorEquiv_mem_iff`: an element of
  `𝒪_v ⊗[A] K` maps into `𝒪_v` exactly when it lies in the image of `𝒪_v`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4.
-/

public section

open TensorProduct
open scoped nonZeroDivisors

namespace IsDedekindDomain.HeightOneSpectrum

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] (v : HeightOneSpectrum A)

/-- The canonical map `𝒪_v ⊗[A] K → K_v` is bijective. -/
private theorem bijective_lift_ofId_toAlgHom :
    Function.Bijective (Algebra.TensorProduct.lift
      (Algebra.ofId (v.adicCompletionIntegers K) (v.adicCompletion K))
      (IsScalarTower.toAlgHom A K (v.adicCompletion K)) fun _ _ ↦ .all _ _) := by
  set f := Algebra.TensorProduct.lift
    (Algebra.ofId (v.adicCompletionIntegers K) (v.adicCompletion K))
    (IsScalarTower.toAlgHom A K (v.adicCompletion K)) fun _ _ ↦ .all _ _
  have hf (c : v.adicCompletionIntegers K) (x : K) :
      f (c ⊗ₜ x) = c * algebraMap K (v.adicCompletion K) x := by
    simp [f]
  refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
  · -- `K` is a localization of `A`, so it suffices to test injectivity on `𝒪_v ⊗ 1`.
    have := IsLocalizedModule.injective_of_map_zero A⁰
      (TensorProduct.mk A K (v.adicCompletionIntegers K) 1)
      (g := f.toLinearMap.restrictScalars A ∘ₗ (TensorProduct.comm A _ _).toLinearMap)
      fun c hc ↦ by
        have hc : (c : v.adicCompletion K) = 0 := by simpa [hf] using hc
        rw [mk_apply, show c = 0 from Subtype.ext hc, tmul_zero]
    exact (TensorProduct.comm A _ _).symm.injective (this (by simpa using hxy))
  · -- `z = (z / b) * b` for some `b ∈ K` with the valuation of `z`.
    rcases eq_or_ne z 0 with rfl | hz
    · exact ⟨0, map_zero f⟩
    obtain ⟨b, hb⟩ := v.valuation_surjective K (Valued.v z)
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hz (by simpa using hb.symm)
    have hb' : Valued.v (algebraMap K (v.adicCompletion K) b) = Valued.v z := by
      rw [← hb]
      exact valuedAdicCompletion_eq_valuation' v b
    refine ⟨⟨z * (algebraMap K (v.adicCompletion K) b)⁻¹, ?_⟩ ⊗ₜ b, ?_⟩
    · rw [mem_adicCompletionIntegers, map_mul, map_inv₀, hb', mul_inv_cancel₀ (by simpa using hz)]
    · simp [hf, hb0]

/-- **The completion of the fraction field is a tensor product**: the canonical isomorphism
`𝒪_v ⊗[A] K ≃ₐ[𝒪_v] K_v`, `c ⊗ x ↦ c x`. -/
noncomputable def adicCompletionIntegersTensorEquiv :
    v.adicCompletionIntegers K ⊗[A] K ≃ₐ[v.adicCompletionIntegers K] v.adicCompletion K :=
  AlgEquiv.ofBijective _ (bijective_lift_ofId_toAlgHom K v)

variable {K v}

/-- The isomorphism `𝒪_v ⊗[A] K ≃ K_v` sends `c ⊗ x` to `c x`. -/
@[simp]
theorem adicCompletionIntegersTensorEquiv_tmul (c : v.adicCompletionIntegers K) (x : K) :
    adicCompletionIntegersTensorEquiv K v (c ⊗ₜ x) = c * algebraMap K (v.adicCompletion K) x := by
  simp [adicCompletionIntegersTensorEquiv]

/-- The image of `1 ⊗ x` in `K_v` has the valuation of `x`. -/
theorem valued_adicCompletionIntegersTensorEquiv_one_tmul (x : K) :
    Valued.v (adicCompletionIntegersTensorEquiv K v (1 ⊗ₜ x)) = v.valuation K x := by
  simp [algebraMap_adicCompletion]

/-- An element of `𝒪_v ⊗[A] K` is sent into `𝒪_v` exactly when it lies in the image of `𝒪_v`,
the bottom `𝒪_v`-subalgebra. -/
theorem adicCompletionIntegersTensorEquiv_mem_iff {y : v.adicCompletionIntegers K ⊗[A] K} :
    adicCompletionIntegersTensorEquiv K v y ∈ v.adicCompletionIntegers K ↔
      y ∈ (⊥ : Subalgebra (v.adicCompletionIntegers K) (v.adicCompletionIntegers K ⊗[A] K)) := by
  rw [Algebra.mem_bot]
  refine ⟨fun hy ↦ ⟨⟨_, hy⟩, ?_⟩, ?_⟩
  · apply (adicCompletionIntegersTensorEquiv K v).injective
    rw [AlgEquiv.commutes, ValuationSubring.algebraMap_apply]
  · rintro ⟨c, rfl⟩
    rw [AlgEquiv.commutes, ValuationSubring.algebraMap_apply]
    exact c.2

end IsDedekindDomain.HeightOneSpectrum

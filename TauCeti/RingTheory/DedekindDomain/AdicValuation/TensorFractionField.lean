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
  refine ⟨(injective_iff_map_eq_zero f).2 fun y hy ↦ ?_, fun z ↦ ?_⟩
  · -- Clearing a denominator `s ∈ A` writes `s • y` as a pure tensor `c ⊗ 1`.
    obtain ⟨⟨c, s⟩, h⟩ := IsLocalizedModule.surj A⁰ (TensorProduct.mk A K
      (v.adicCompletionIntegers K) 1) (TensorProduct.comm A _ _ y)
    replace h : (1 ⊗ₜ algebraMap A K s) * y = c ⊗ₜ 1 := by
      have := congrArg (TensorProduct.comm A _ _).symm h
      dsimp only at this
      rw [Submonoid.smul_def, map_smul, LinearEquiv.symm_apply_apply, mk_apply,
        comm_symm_tmul] at this
      rw [← this, ← Algebra.TensorProduct.algebraMap_apply']
      exact (Algebra.smul_def _ _).symm
    have hc : c = 0 := by
      have := congrArg f h
      rw [map_mul, hy, mul_zero, hf, map_one, mul_one] at this
      exact_mod_cast this.symm
    have hs : algebraMap A K s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    have := congrArg ((1 : v.adicCompletionIntegers K) ⊗ₜ[A] (algebraMap A K s)⁻¹ * ·) h
    simpa [← mul_assoc, hs, hc, ← Algebra.TensorProduct.one_def] using this
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

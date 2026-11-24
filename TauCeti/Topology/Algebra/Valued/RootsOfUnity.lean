/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuedField
public import TauCeti.RingTheory.RootsOfUnity.Henselian
public import TauCeti.RingTheory.RootsOfUnity.IntegrallyClosed

/-!
# Roots of unity of a valued field with henselian valuation ring

Let `K` be a valued field whose valuation ring `𝒪[K]` is henselian, with residue field `𝓀[K]`.
If `m` is a unit of `𝒪[K]`, reduction modulo the maximal ideal identifies the `m`-th roots of
unity of `K` with those of `𝓀[K]`:

`μ_m(K) ≃* μ_m(𝓀[K])`.

The roots of unity of `K` lie in `𝒪[K]`, which is integrally closed in `K`
(`TauCeti.rootsOfUnityMulEquiv`), and reduction is an isomorphism on the roots of unity of a
henselian local ring of invertible order (`TauCeti.rootsOfUnityEquivResidueField`).

## Main definitions

* `Valued.rootsOfUnityResidueEquiv`: reduction `μ_m(K) ≃* μ_m(𝓀[K])` for `m` a unit of `𝒪[K]`.
-/

public section

noncomputable section

open IsLocalRing TauCeti

namespace Valued

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
  [HenselianLocalRing 𝒪[K]] {m : ℕ}

/-- **Roots of unity of invertible order reduce isomorphically**: if the valuation ring of `K` is
henselian and `m` is a unit of it, reduction modulo its maximal ideal is an isomorphism from the
`m`-th roots of unity of `K` onto those of its residue field. -/
def rootsOfUnityResidueEquiv (hm : IsUnit (m : 𝒪[K])) :
    rootsOfUnity m K ≃* rootsOfUnity m 𝓀[K] :=
  haveI : NeZero m := ⟨by rintro rfl; simp at hm⟩
  (rootsOfUnityMulEquiv 𝒪[K] K m).symm.trans (rootsOfUnityEquivResidueField hm)

/-- `rootsOfUnityResidueEquiv` is reduction of the root of unity of `𝒪[K]` that a root of unity of
`K` comes from. -/
@[simp]
theorem coe_rootsOfUnityResidueEquiv_apply [NeZero m] (hm : IsUnit (m : 𝒪[K]))
    (ζ : rootsOfUnity m K) :
    ((rootsOfUnityResidueEquiv hm ζ : 𝓀[K]ˣ) : 𝓀[K]) =
      residue 𝒪[K] (((rootsOfUnityMulEquiv 𝒪[K] K m).symm ζ : 𝒪[K]ˣ) : 𝒪[K]) := by
  rw [rootsOfUnityResidueEquiv, MulEquiv.trans_apply, coe_rootsOfUnityEquivResidueField]

/-- `rootsOfUnityResidueEquiv` is reduction: the image of a root of unity `ζ` of `K`, which lies in
`𝒪[K]`, is its residue. -/
theorem coe_rootsOfUnityResidueEquiv_apply_of_coe_eq (hm : IsUnit (m : 𝒪[K]))
    (ζ : rootsOfUnity m K) {x : 𝒪[K]} (hx : (x : K) = ((ζ : Kˣ) : K)) :
    ((rootsOfUnityResidueEquiv hm ζ : 𝓀[K]ˣ) : 𝓀[K]) = residue 𝒪[K] x := by
  have : NeZero m := ⟨by rintro rfl; simp at hm⟩
  rw [coe_rootsOfUnityResidueEquiv_apply]
  congr 1
  refine FaithfulSMul.algebraMap_injective 𝒪[K] K ?_
  rw [algebraMap_rootsOfUnityMulEquiv_symm_apply, ← hx]
  exact Algebra.algebraMap_ofSubsemiring_apply _ x

end Valued

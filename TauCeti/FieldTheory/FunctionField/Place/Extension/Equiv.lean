/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Equiv

/-!
# Ramification under field isomorphisms

The ramification index depends on the extension, not on its presentation as a field carrier:
transporting a place of the upstairs field along an isomorphism over the downstairs field does not
change its ramification index. This allows an extension to be placed in a finite Galois overfield
without changing its ramification behaviour.

More generally, a commutative square of isomorphisms `σ : K ≃ₐ[k] K'` below and `e : F ≃ₐ[k] F'`
above carries the place of `F` over `P` to a place of `F'` over `σ(P)`, with the same ramification
index (`TauCeti.Place.restrict_map` and
`TauCeti.Place.ramificationIdx_map`). With `K = K'` and `F = F'` as fields, this is how
a change of the embedding of the base field by an automorphism moves places and their ramification.
-/

public section

namespace TauCeti.Place

variable {k F L L' : Type*} [Field k] [Field F] [Field L] [Field L']
variable [Algebra k F] [Algebra k L] [Algebra k L'] [Algebra F L] [Algebra F L']
variable [IsScalarTower k F L] [IsScalarTower k F L']

/-- **The ramification index is invariant under an isomorphism of the upstairs field** over the
base field: transporting a place of `L` along `e : L ≃ₐ[F] L'` does not change its ramification
index over `F`. -/
@[simp]
theorem ramificationIdx_equivOfRingEquiv (e : L ≃ₐ[F] L') (Q : Place k L) :
    ramificationIdx F (equivOfRingEquiv (RingEquiv.refl k) e.toRingEquiv
      (fun c ↦ by simp [IsScalarTower.algebraMap_apply k F L,
        IsScalarTower.algebraMap_apply k F L']) Q) = ramificationIdx F Q := by
  rw [ramificationIdx_def, ramificationIdx_def]
  congr 1
  ext c
  rw [Valuation.comap_apply, Valuation.comap_apply, valuation_equivOfRingEquiv]
  exact congrArg Q.valuation (e.symm.commutes c)

section Commute

variable {K K' : Type*} [Field K] [Field K'] [Algebra K L] [Algebra K' L'] (e : L ≃ₐ[k] L')

/-- **The ramification index is invariant under a commutative square of isomorphisms**: if
`e : L ≃ₐ[k] L'` carries the image of `K` onto the image of `K'` along `σ : K ≃+* K'`, then
transporting a place of `L` along `e` does not change its ramification index. -/
theorem ramificationIdx_map (σ : K ≃+* K')
    (he : ∀ x, e (algebraMap K L x) = algebraMap K' L' (σ x)) (Q : Place k L) :
    ramificationIdx K' (Q.map e) = ramificationIdx K Q := by
  have h : (Q.map e).valuation.comap (algebraMap K' L') =
      (Q.valuation.comap (algebraMap K L)).comap (σ.symm : K' →+* K) := by
    ext x
    simp [valuation_map, e.symm_apply_eq.mpr (by rw [he, σ.apply_symm_apply] :
      algebraMap K' L' x = e (algebraMap K L (σ.symm x)))]
  rw [ramificationIdx_def, ramificationIdx_def, h,
    Valuation.ordIndex_comap_of_surjective _ σ.symm.surjective]

/-- **Restriction commutes with a commutative square of isomorphisms**: if `e : L ≃ₐ[k] L'`
carries the image of `K` onto the image of `K'` along a `k`-algebra isomorphism `σ`, then the
transport of a place `Q` of `L` lies over the transport of the place below `Q`. -/
theorem restrict_map [Algebra k K] [Algebra k K'] [IsScalarTower k K L] [IsScalarTower k K' L']
    [Algebra.IsIntegral K L] [Algebra.IsIntegral K' L'] (σ : K ≃ₐ[k] K')
    (he : ∀ x, e (algebraMap K L x) = algebraMap K' L' (σ x)) (Q : Place k L) :
    (Q.map e).restrict k K' = (Q.restrict k K).map σ := by
  rw [restrict_eq_iff_integers_le]
  intro f hf
  rw [mem_integers_map_iff, mem_integers_restrict_iff] at hf
  rwa [mem_integers_map_iff, e.symm_apply_eq.mpr (by rw [he, σ.apply_symm_apply] :
    algebraMap K' L' f = e (algebraMap K L (σ.symm f)))]

end Commute

end TauCeti.Place

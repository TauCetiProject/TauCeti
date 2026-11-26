/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.PathConnected
public import TauCeti.Topology.Algebra.Monoid.ZerothHomotopy

/-!
# The group of path components of the Fredholm operators

Composition of bounded operators on a normed space `E` is jointly norm-continuous and preserves
Fredholmness (Mathlib's `ContinuousLinearMap.IsFredholm.comp`), so the Fredholm locus
`{T : E →L[𝕜] E // T.IsFredholm}` is a topological monoid, the submonoid
`ContinuousLinearMap.fredholmSubmonoid 𝕜 E` of `E →L[𝕜] E`. Its path components therefore form a
monoid (`ZerothHomotopy.instMonoid`). Since the index of a composition is the sum of the indices
(`ContinuousLinearMap.IsFredholm.index_comp`), the Fredholm index on path components is a monoid
homomorphism to `Multiplicative ℤ`. When `E` is an infinite-dimensional complex Hilbert space it
is a bijection (`ZerothHomotopy.fredholmIndexEquiv`), hence an isomorphism of monoids
`ZerothHomotopy.fredholmIndexMulEquiv`; in particular the path components form a group.

Infinite dimension is needed: on a finite-dimensional space every endomorphism is Fredholm of
index `0`, and the Fredholm locus is path connected, so the component monoid is trivial.

## Main definitions

* `ContinuousLinearMap.fredholmSubmonoid 𝕜 E`: the Fredholm operators as a submonoid of
  `E →L[𝕜] E`, with the induced monoid and topological-monoid structures on
  `{T : E →L[𝕜] E // T.IsFredholm}`.
* `ZerothHomotopy.fredholmIndexMulEquiv`: the Fredholm index as an isomorphism of monoids from
  the path components of the Fredholm operators on an infinite-dimensional complex Hilbert space
  onto `Multiplicative ℤ`.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable (𝕜 E) in
/-- The Fredholm operators on `E`, as a submonoid of the bounded operators under composition. -/
def fredholmSubmonoid : Submonoid (E →L[𝕜] E) where
  carrier := {T | T.IsFredholm}
  one_mem' := IsFredholm.id
  mul_mem' hS hT := hS.comp hT

@[simp]
theorem mem_fredholmSubmonoid {T : E →L[𝕜] E} : T ∈ fredholmSubmonoid 𝕜 E ↔ T.IsFredholm :=
  Iff.rfl

/-- The Fredholm operators on `E` form a monoid under composition. -/
instance instMonoidIsFredholm : Monoid {T : E →L[𝕜] E // T.IsFredholm} :=
  inferInstanceAs (Monoid (fredholmSubmonoid 𝕜 E))

/-- Composition of Fredholm operators is jointly continuous for the operator norm. -/
instance instContinuousMulIsFredholm : ContinuousMul {T : E →L[𝕜] E // T.IsFredholm} :=
  inferInstanceAs (ContinuousMul (fredholmSubmonoid 𝕜 E))

@[simp]
theorem IsFredholm.coe_mul (S T : {T : E →L[𝕜] E // T.IsFredholm}) :
    ((S * T : {T : E →L[𝕜] E // T.IsFredholm}) : E →L[𝕜] E) = S * T :=
  (rfl)

@[simp]
theorem IsFredholm.coe_one : ((1 : {T : E →L[𝕜] E // T.IsFredholm}) : E →L[𝕜] E) = 1 :=
  (rfl)

end ContinuousLinearMap

namespace ZerothHomotopy

open ContinuousLinearMap

section Index

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

variable (𝕜 E) in
/-- The Fredholm index on the monoid of path components of the Fredholm operators, as a monoid
homomorphism to `Multiplicative ℤ`: the index of a composition is the sum of the indices. It is
the lift along `ZerothHomotopy.liftMonoidHom` of the index on Fredholm operators. -/
noncomputable def fredholmIndexMonoidHom :
    ZerothHomotopy {T : E →L[𝕜] E // T.IsFredholm} →* Multiplicative ℤ :=
  liftMonoidHom
    { toFun := fun T => Multiplicative.ofAdd T.val.index
      map_one' := by
        rw [IsFredholm.coe_one, one_def, index_def, ofAdd_eq_one]
        exact LinearMap.index_id
      map_mul' := fun S T => by
        rw [IsFredholm.coe_mul, mul_def, index_def, index_def, index_def,
          S.property.index_comp T.property, ofAdd_add] }
    fun S T γ => by
      simpa using congrArg (Multiplicative.ofAdd ∘ fredholmIndex) (sound γ)

@[simp]
theorem fredholmIndexMonoidHom_apply (x : ZerothHomotopy {T : E →L[𝕜] E // T.IsFredholm}) :
    fredholmIndexMonoidHom 𝕜 E x = Multiplicative.ofAdd x.fredholmIndex := by
  induction x
  simp [fredholmIndexMonoidHom]

/-- The index of a product of path components of Fredholm operators is the sum of the indices. -/
theorem fredholmIndex_mul (x y : ZerothHomotopy {T : E →L[𝕜] E // T.IsFredholm}) :
    (x * y).fredholmIndex = x.fredholmIndex + y.fredholmIndex := by
  have h := map_mul (fredholmIndexMonoidHom 𝕜 E) x y
  rw [fredholmIndexMonoidHom_apply, fredholmIndexMonoidHom_apply, fredholmIndexMonoidHom_apply,
    ← ofAdd_add] at h
  exact Multiplicative.ofAdd.injective h

end Index

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The path components of the Fredholm operators form the group `ℤ`.** On an
infinite-dimensional complex Hilbert space `E`, the Fredholm index identifies the monoid of
norm-path components of the Fredholm operators on `E` with `Multiplicative ℤ`. -/
noncomputable def fredholmIndexMulEquiv (hE : ¬ FiniteDimensional ℂ E) :
    ZerothHomotopy {T : E →L[ℂ] E // T.IsFredholm} ≃* Multiplicative ℤ :=
  MulEquiv.ofBijective (fredholmIndexMonoidHom ℂ E) <| by
    rw [show ⇑(fredholmIndexMonoidHom ℂ E) = Multiplicative.ofAdd ∘ fredholmIndex from
      funext (fredholmIndexMonoidHom_apply (𝕜 := ℂ))]
    exact Multiplicative.ofAdd.bijective.comp (fredholmIndex_bijective hE)

@[simp]
theorem fredholmIndexMulEquiv_apply (hE : ¬ FiniteDimensional ℂ E)
    (x : ZerothHomotopy {T : E →L[ℂ] E // T.IsFredholm}) :
    fredholmIndexMulEquiv hE x = Multiplicative.ofAdd x.fredholmIndex :=
  fredholmIndexMonoidHom_apply x

end ZerothHomotopy

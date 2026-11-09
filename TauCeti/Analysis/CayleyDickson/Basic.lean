/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Algebra.CayleyDickson.Basic

/-!
# The `L²` norm on the Cayley–Dickson double

The Cayley–Dickson double `CayleyDickson A` of a normed additive group `A` is normed as the `L²`
product of its two coordinates, `‖⟨a, b⟩‖ = √(‖a‖ ^ 2 + ‖b‖ ^ 2)`. This file transports the normed
additive group of `WithLp 2 (A × A)` to the double along the coordinate isomorphism
`TauCeti.CayleyDickson.addEquivWithLp`, and with it the normed-space and inner-product-space
structures, for which `⟪⟨a, b⟩, ⟨c, d⟩⟫ = ⟪a, c⟫ + ⟪b, d⟫`. The double is a structure rather than
the type `A × A`, so it does not inherit the supremum norm of a product type.

For a normed ring `A` with involution, the involution `star ⟨a, b⟩ = ⟨star a, -b⟩` of the double is
an isometry as soon as that of `A` is. For a normed additive group `A` with a unit `1`, the unit
`⟨1, 0⟩` of the double has norm one as soon as that of `A` does. The double of the real
quaternions, the real octonions, is studied in `TauCeti.Analysis.CayleyDickson.Quaternion`; there
the norm is the square root of the octonion norm and is multiplicative.

## Main definitions

* `TauCeti.CayleyDickson.addEquivWithLp`: the coordinates of an element of the double, as an
  additive isomorphism with `WithLp 2 (A × A)`.
* `TauCeti.CayleyDickson.linearIsometryEquivWithLp`: the same isomorphism, as a linear isometry
  equivalence.

## Main results

* `TauCeti.CayleyDickson.norm_def` and `TauCeti.CayleyDickson.norm_sq_eq`: the norm of the double
  is the `L²` norm of its two coordinates.
* `TauCeti.CayleyDickson.inner_def`: the inner product of the double is the sum of the inner
  products of the coordinates.
* The instances `NormedStarGroup (CayleyDickson A)` and `NormOneClass (CayleyDickson A)`.

## References

* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. **39** (2002), 145–205, §2.2.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

namespace CayleyDickson

variable {𝕜 A : Type*}

/-! ### The normed additive group -/

section NormedAddCommGroup

variable (A) in
/-- The coordinates of an element of the Cayley–Dickson double, as an additive isomorphism with the
`L²` product `WithLp 2 (A × A)`. The norm of the double is transported along it. -/
@[expose] def addEquivWithLp [AddCommGroup A] : CayleyDickson A ≃+ WithLp 2 (A × A) where
  toFun x := WithLp.toLp 2 (x.fst, x.snd)
  invFun p := ⟨p.fst, p.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem addEquivWithLp_apply [AddCommGroup A] (x : CayleyDickson A) :
    addEquivWithLp A x = WithLp.toLp 2 (x.fst, x.snd) :=
  (rfl)

@[simp]
theorem addEquivWithLp_symm_apply [AddCommGroup A] (p : WithLp 2 (A × A)) :
    (addEquivWithLp A).symm p = ⟨p.fst, p.snd⟩ :=
  (rfl)

variable [NormedAddCommGroup A]

/-- The double of a normed additive group is normed as the `L²` product of its two coordinates. -/
noncomputable instance : NormedAddCommGroup (CayleyDickson A) :=
  NormedAddCommGroup.induced (CayleyDickson A) (WithLp 2 (A × A)) (addEquivWithLp A)
    (addEquivWithLp A).injective

/-- The norm of the double is the norm of its coordinates in `WithLp 2 (A × A)`. -/
theorem norm_def (x : CayleyDickson A) : ‖x‖ = ‖WithLp.toLp 2 (x.fst, x.snd)‖ :=
  (rfl)

/-- **The norm of the double is the `L²` norm of its coordinates**,
`‖⟨a, b⟩‖ = √(‖a‖ ^ 2 + ‖b‖ ^ 2)`. -/
theorem norm_eq_sqrt (x : CayleyDickson A) : ‖x‖ = √(‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) := by
  rw [norm_def, WithLp.prod_norm_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd]

/-- The square of the norm of the double is the sum of the squares of the norms of its
coordinates. -/
theorem norm_sq_eq (x : CayleyDickson A) : ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 := by
  rw [norm_def, WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd]

/-- The first coordinate of an element of the double has norm at most that of the element. -/
theorem norm_fst_le (x : CayleyDickson A) : ‖x.fst‖ ≤ ‖x‖ := by
  simpa only [norm_def, WithLp.toLp_fst] using
    WithLp.norm_fst_le (x := WithLp.toLp 2 (x.fst, x.snd))

/-- The second coordinate of an element of the double has norm at most that of the element. -/
theorem norm_snd_le (x : CayleyDickson A) : ‖x.snd‖ ≤ ‖x‖ := by
  simpa only [norm_def, WithLp.toLp_snd] using
    WithLp.norm_snd_le (x := WithLp.toLp 2 (x.fst, x.snd))

/-- The coordinate isomorphism with `WithLp 2 (A × A)` preserves the norm. Not a `simp` lemma,
because `TauCeti.CayleyDickson.addEquivWithLp_apply` already rewrites its left-hand side. -/
theorem norm_addEquivWithLp (x : CayleyDickson A) : ‖addEquivWithLp A x‖ = ‖x‖ :=
  (rfl)

variable (𝕜 A) in
/-- The coordinates of an element of the Cayley–Dickson double, as a linear isometry equivalence
with the `L²` product `WithLp 2 (A × A)`. The normed-space and inner-product-space structures of
the double are induced along it. -/
@[expose] noncomputable def linearIsometryEquivWithLp [NormedField 𝕜] [NormedSpace 𝕜 A] :
    CayleyDickson A ≃ₗᵢ[𝕜] WithLp 2 (A × A) where
  __ := addEquivWithLp A
  map_smul' _ _ := rfl
  norm_map' := norm_addEquivWithLp

/-- The double of a normed space is a normed space over the same field. -/
noncomputable instance [NormedField 𝕜] [NormedSpace 𝕜 A] : NormedSpace 𝕜 (CayleyDickson A) :=
  NormedSpace.induced 𝕜 (CayleyDickson A) (WithLp 2 (A × A)) (linearIsometryEquivWithLp 𝕜 A)

@[simp]
theorem linearIsometryEquivWithLp_apply [NormedField 𝕜] [NormedSpace 𝕜 A] (x : CayleyDickson A) :
    linearIsometryEquivWithLp 𝕜 A x = WithLp.toLp 2 (x.fst, x.snd) :=
  (rfl)

@[simp]
theorem linearIsometryEquivWithLp_symm_apply [NormedField 𝕜] [NormedSpace 𝕜 A]
    (p : WithLp 2 (A × A)) : (linearIsometryEquivWithLp 𝕜 A).symm p = ⟨p.fst, p.snd⟩ :=
  (rfl)

/-- The coordinate isomorphism with `WithLp 2 (A × A)` is an isometry. -/
theorem isometry_addEquivWithLp : Isometry (addEquivWithLp A) :=
  AddMonoidHomClass.isometry_of_norm _ norm_addEquivWithLp

/-- The first coordinate of the double is continuous. -/
@[fun_prop]
theorem continuous_fst : Continuous (fst : CayleyDickson A → A) :=
  (WithLp.continuous_fst 2 A A).comp isometry_addEquivWithLp.continuous

/-- The second coordinate of the double is continuous. -/
@[fun_prop]
theorem continuous_snd : Continuous (snd : CayleyDickson A → A) :=
  (WithLp.continuous_snd 2 A A).comp isometry_addEquivWithLp.continuous

/-- The double of a complete normed group is complete. -/
instance [CompleteSpace A] : CompleteSpace (CayleyDickson A) :=
  (completeSpace_congr (e := (addEquivWithLp A).toEquiv)
    isometry_addEquivWithLp.isUniformEmbedding).mpr inferInstance

end NormedAddCommGroup

/-! ### The inner product -/

section InnerProductSpace

variable [RCLike 𝕜] [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]

/-- The double of an inner product space is an inner product space, with
`⟪⟨a, b⟩, ⟨c, d⟩⟫ = ⟪a, c⟫ + ⟪b, d⟫`. -/
noncomputable instance : InnerProductSpace 𝕜 (CayleyDickson A) :=
  InnerProductSpace.induced (linearIsometryEquivWithLp 𝕜 A)

/-- **The inner product of the double** is the sum of the inner products of the coordinates. -/
theorem inner_def (x y : CayleyDickson A) :
    ⟪x, y⟫_𝕜 = ⟪x.fst, y.fst⟫_𝕜 + ⟪x.snd, y.snd⟫_𝕜 := by
  rw [← (linearIsometryEquivWithLp 𝕜 A).inner_map_map, linearIsometryEquivWithLp_apply,
    linearIsometryEquivWithLp_apply, WithLp.prod_inner_apply, WithLp.ofLp_toLp,
    WithLp.ofLp_toLp]

end InnerProductSpace

/-! ### The involution and the unit -/

/-- The involution `star ⟨a, b⟩ = ⟨star a, -b⟩` of the double is an isometry when the involution
of `A` is. -/
instance [NormedRing A] [StarRing A] [NormedStarGroup A] : NormedStarGroup (CayleyDickson A) where
  norm_star_le x := by
    rw [norm_eq_sqrt, norm_eq_sqrt, star_fst, star_snd, norm_star, norm_neg]

/-- The unit `⟨1, 0⟩` of the double has norm one when that of `A` does. -/
instance [NormedAddCommGroup A] [One A] [NormOneClass A] : NormOneClass (CayleyDickson A) where
  norm_one := by simp [norm_eq_sqrt]

end CayleyDickson

end TauCeti

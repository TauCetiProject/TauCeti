/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.LocallyConstant
public import TauCeti.Topology.Sets.Clopens

/-!
# Extension by zero from a clopen subset

A continuous function on a clopen subset extends continuously to the ambient space by taking the
value zero on the complementary clopen. This file packages that operation as a continuous linear
map and records its pointwise values, its exact norm, and its interaction with restriction.

The construction is the test-function operator used to restrict an abstract measure to a clopen
subset.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.3.
-/

public section

open Set TopologicalSpace

namespace ContinuousMap

variable {X R : Type*} [TopologicalSpace X] [CompactSpace X] [NormedCommRing R]

private noncomputable def zeroExtendClopenFn (s : Clopens X) (f : C(s, R)) : C(X, R) := by
  let S : Bool → Set X
    | false => s
    | true => (s : Set X)ᶜ
  let F : (b : Bool) → C(S b, R)
    | false => f
    | true => 0
  apply liftCover S F
  · intro i j x hxi hxj
    cases i <;> cases j
    · rfl
    · exfalso
      have hxs : x ∈ s := by simpa [S] using hxi
      have hxns : x ∉ s := by simpa [S] using hxj
      exact hxns hxs
    · exfalso
      have hxns : x ∉ s := by simpa [S] using hxi
      have hxs : x ∈ s := by simpa [S] using hxj
      exact hxns hxs
    · rfl
  · intro x
    by_cases hx : x ∈ s
    · exact ⟨false, by simpa [S] using s.isOpen.mem_nhds hx⟩
    · exact ⟨true, by simpa [S] using s.isClosed.isOpen_compl.mem_nhds hx⟩

omit [CompactSpace X] in
private theorem zeroExtendClopenFn_apply_mem (s : Clopens X) (f : C(s, R))
    {x : X} (hx : x ∈ s) : zeroExtendClopenFn s f x = f ⟨x, hx⟩ := by
  rw [zeroExtendClopenFn]
  exact liftCover_coe (i := false) ⟨x, hx⟩

omit [CompactSpace X] in
private theorem zeroExtendClopenFn_apply_not_mem (s : Clopens X) (f : C(s, R))
    {x : X} (hx : x ∉ s) : zeroExtendClopenFn s f x = 0 := by
  rw [zeroExtendClopenFn]
  exact liftCover_coe (i := true) ⟨x, hx⟩

private noncomputable def zeroExtendClopenLinearMap (s : Clopens X) :
    C(s, R) →ₗ[R] C(X, R) where
  toFun := zeroExtendClopenFn s
  map_add' f g := by
    ext x
    by_cases hx : x ∈ s
    · simp only [zeroExtendClopenFn_apply_mem s _ hx, add_apply]
    · simp only [zeroExtendClopenFn_apply_not_mem s _ hx, add_apply, add_zero]
  map_smul' c f := by
    ext x
    by_cases hx : x ∈ s
    · simp only [zeroExtendClopenFn_apply_mem s _ hx, smul_apply]
      rw [Algebra.smul_def]
      rfl
    · simp only [zeroExtendClopenFn_apply_not_mem s _ hx, smul_apply, smul_zero]

/-- Extend a continuous function on a clopen subset by zero on its complement. -/
noncomputable def zeroExtendClopen (s : Clopens X) : C(s, R) →L[R] C(X, R) :=
  (zeroExtendClopenLinearMap s).mkContinuous 1 fun f ↦ by
    rw [one_mul]
    refine (norm_le _ (norm_nonneg f)).2 fun x ↦ ?_
    by_cases hx : x ∈ s
    · have hval : ((zeroExtendClopenLinearMap s) f) x = f ⟨x, hx⟩ :=
        zeroExtendClopenFn_apply_mem s f hx
      rw [hval]
      exact norm_coe_le_norm f ⟨x, hx⟩
    · have hval : ((zeroExtendClopenLinearMap s) f) x = 0 :=
        zeroExtendClopenFn_apply_not_mem s f hx
      rw [hval, norm_zero]
      exact norm_nonneg f

/-- On the clopen subset, extension by zero agrees with the original function. -/
@[simp]
theorem zeroExtendClopen_apply_mem (s : Clopens X) (f : C(s, R))
    {x : X} (hx : x ∈ s) : zeroExtendClopen s f x = f ⟨x, hx⟩ :=
  zeroExtendClopenFn_apply_mem s f hx

/-- Off the clopen subset, extension by zero vanishes. -/
@[simp]
theorem zeroExtendClopen_apply_not_mem (s : Clopens X) (f : C(s, R))
    {x : X} (hx : x ∉ s) : zeroExtendClopen s f x = 0 :=
  zeroExtendClopenFn_apply_not_mem s f hx

/-- Extension by zero preserves the supremum norm, including for the empty clopen. -/
@[simp]
theorem norm_zeroExtendClopen (s : Clopens X) (f : C(s, R)) :
    ‖zeroExtendClopen s f‖ = ‖f‖ := by
  apply le_antisymm
  · exact (norm_le _ (norm_nonneg f)).2 fun x ↦ by
      by_cases hx : x ∈ s
      · rw [zeroExtendClopen_apply_mem s f hx]
        exact norm_coe_le_norm f ⟨x, hx⟩
      · rw [zeroExtendClopen_apply_not_mem s f hx, norm_zero]
        exact norm_nonneg f
  · exact (norm_le _ (norm_nonneg (zeroExtendClopen s f))).2 fun x ↦ by
      rw [← zeroExtendClopen_apply_mem s f x.2]
      exact norm_coe_le_norm (zeroExtendClopen s f) x

/-- Restricting an extension by zero recovers the original function. -/
@[simp]
theorem restrict_zeroExtendClopen (s : Clopens X) (f : C(s, R)) :
    (zeroExtendClopen s f).restrict s = f := by
  ext x
  exact zeroExtendClopen_apply_mem s f x.2

/-- Extending a restricted function by zero is multiplication by the clopen characteristic
function. -/
@[simp]
theorem zeroExtendClopen_restrict (s : Clopens X) (f : C(X, R)) :
    zeroExtendClopen s (f.restrict s) =
      (LocallyConstant.charFn R s.isClopen : C(X, R)) * f := by
  ext x
  by_cases hx : x ∈ s
  · have hchar : ((LocallyConstant.charFn R s.isClopen : C(X, R)) x) = 1 := by
      simpa [hx] using congrFun (LocallyConstant.coe_charFn R s.isClopen) x
    rw [zeroExtendClopen_apply_mem s _ hx, mul_apply, hchar]
    simpa only [one_mul] using restrict_apply_mk f (s : Set X) x hx
  · have hchar : ((LocallyConstant.charFn R s.isClopen : C(X, R)) x) = 0 := by
      simpa [hx] using congrFun (LocallyConstant.coe_charFn R s.isClopen) x
    rw [zeroExtendClopen_apply_not_mem s _ hx, mul_apply, hchar, zero_mul]

-- The extension of the constant `7` on `{0} ⊆ Fin 2` takes value `7` at `0`.
example :
    zeroExtendClopen (⟨{0}, isClopen_discrete {0}⟩ : Clopens (Fin 2))
      (ContinuousMap.const _ (7 : ℤ)) 0 = 7 := by
  simp

-- The same extension vanishes at the other point.
example :
    zeroExtendClopen (⟨{0}, isClopen_discrete {0}⟩ : Clopens (Fin 2))
      (ContinuousMap.const _ (7 : ℤ)) 1 = 0 := by
  simp

-- Extending the unique function on the empty clopen gives the zero function.
example : zeroExtendClopen (⊥ : Clopens (Fin 2)) (0 : C((⊥ : Clopens (Fin 2)), ℤ)) = 0 := by
  ext x
  simp

end ContinuousMap

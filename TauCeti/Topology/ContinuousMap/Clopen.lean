/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.LocallyConstant
public import TauCeti.Topology.Sets.Clopens

/-!
# Extension by zero from a clopen subset

A continuous function on a clopen subset extends continuously to the ambient space by taking the
value zero on the complementary clopen. For a compact space and a seminormed module over a
semiring whose fixed scalars act continuously, this file packages that operation as a continuous
linear map and records its pointwise values, its exact norm, and its interaction with restriction.

The construction is the test-function operator used to restrict an abstract measure to a clopen
subset.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.3.
-/

public section

open Set TopologicalSpace ContinuousMap

namespace ContinuousMap

variable {X E : Type*} [TopologicalSpace X]

section Zero

variable [TopologicalSpace E] [Zero E]

private noncomputable def zeroExtendClopenFn (s : Clopens X) (f : C(s, E)) : C(X, E) := by
  let S : Bool → Set X
    | false => s
    | true => (s : Set X)ᶜ
  let F : (b : Bool) → C(S b, E)
    | false => f
    | true => 0
  apply liftCover S F
  · intro i j x hxi hxj
    cases i <;> cases j
    · rfl
    · exact (hxj hxi).elim
    · exact (hxi hxj).elim
    · rfl
  · intro x
    by_cases hx : x ∈ s
    · exact ⟨false, by simpa [S] using s.isOpen.mem_nhds hx⟩
    · exact ⟨true, by simpa [S] using s.isClosed.isOpen_compl.mem_nhds hx⟩

private theorem zeroExtendClopenFn_apply_mem (s : Clopens X) (f : C(s, E))
    {x : X} (hx : x ∈ s) : zeroExtendClopenFn s f x = f ⟨x, hx⟩ := by
  rw [zeroExtendClopenFn]
  exact liftCover_coe (i := false) ⟨x, hx⟩

private theorem zeroExtendClopenFn_apply_not_mem (s : Clopens X) (f : C(s, E))
    {x : X} (hx : x ∉ s) : zeroExtendClopenFn s f x = 0 := by
  rw [zeroExtendClopenFn]
  exact liftCover_coe (i := true) ⟨x, hx⟩

end Zero

section LinearMap

variable (R : Type*) [Semiring R] [TopologicalSpace E] [AddCommMonoid E] [ContinuousAdd E]
  [Module R E] [ContinuousConstSMul R E]

private noncomputable def zeroExtendClopenLinearMap (s : Clopens X) :
    C(s, E) →ₗ[R] C(X, E) where
  toFun := zeroExtendClopenFn s
  map_add' f g := by
    ext x
    by_cases hx : x ∈ s
    · simp only [zeroExtendClopenFn_apply_mem s _ hx, ContinuousMap.add_apply]
    · simp only [zeroExtendClopenFn_apply_not_mem s _ hx, ContinuousMap.add_apply, add_zero]
  map_smul' c f := by
    ext x
    by_cases hx : x ∈ s
    · simp only [zeroExtendClopenFn_apply_mem s _ hx, ContinuousMap.smul_apply, RingHom.id_apply]
    · simp only [zeroExtendClopenFn_apply_not_mem s _ hx, ContinuousMap.smul_apply, smul_zero]

end LinearMap

section Norm

variable [CompactSpace X] [SeminormedAddCommGroup E]

private theorem norm_zeroExtendClopenFn (s : Clopens X) (f : C(s, E)) :
    ‖zeroExtendClopenFn s f‖ = ‖f‖ := by
  apply le_antisymm
  · refine (norm_le _ (norm_nonneg f)).2 fun x ↦ ?_
    by_cases hx : x ∈ s
    · rw [zeroExtendClopenFn_apply_mem s f hx]
      exact norm_coe_le_norm f ⟨x, hx⟩
    · rw [zeroExtendClopenFn_apply_not_mem s f hx, norm_zero]
      exact norm_nonneg f
  · refine (norm_le _ (norm_nonneg (zeroExtendClopenFn s f))).2 fun x ↦ ?_
    rw [← zeroExtendClopenFn_apply_mem s f x.2]
    exact norm_coe_le_norm (zeroExtendClopenFn s f) x

end Norm

section Module

variable [CompactSpace X] [SeminormedAddCommGroup E]
  (R : Type*) [Semiring R] [Module R E] [ContinuousConstSMul R E]

/-- Extend a continuous function on a clopen subset by zero on its complement. -/
noncomputable def zeroExtendClopen (s : Clopens X) : C(s, E) →L[R] C(X, E) :=
  { zeroExtendClopenLinearMap R s with
    cont := AddMonoidHomClass.continuous_of_bound (zeroExtendClopenLinearMap R s) 1 fun f ↦ by
      simp only [zeroExtendClopenLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
        norm_zeroExtendClopenFn, one_mul, le_refl] }

variable {R}

/-- On the clopen subset, extension by zero agrees with the original function. -/
@[simp]
theorem zeroExtendClopen_apply_mem (s : Clopens X) (f : C(s, E))
    {x : X} (hx : x ∈ s) : zeroExtendClopen R s f x = f ⟨x, hx⟩ :=
  zeroExtendClopenFn_apply_mem s f hx

/-- Off the clopen subset, extension by zero vanishes. -/
@[simp]
theorem zeroExtendClopen_apply_not_mem (s : Clopens X) (f : C(s, E))
    {x : X} (hx : x ∉ s) : zeroExtendClopen R s f x = 0 :=
  zeroExtendClopenFn_apply_not_mem s f hx

/-- Extension by zero preserves the supremum norm, including for the empty clopen. -/
@[simp]
theorem norm_zeroExtendClopen (s : Clopens X) (f : C(s, E)) :
    ‖zeroExtendClopen R s f‖ = ‖f‖ :=
  norm_zeroExtendClopenFn s f

/-- Restricting an extension by zero recovers the original function. -/
@[simp]
theorem restrict_zeroExtendClopen (s : Clopens X) (f : C(s, E)) :
    (zeroExtendClopen R s f).restrict s = f := by
  ext x
  exact zeroExtendClopen_apply_mem (R := R) s f x.2

/-- A continuous function is the sum of the extensions by zero of its restrictions to a clopen
subset and to the complementary clopen. -/
theorem zeroExtendClopen_restrict_add_compl (s : Clopens X) (f : C(X, E)) :
    zeroExtendClopen R s (f.restrict s) +
      zeroExtendClopen R sᶜ (f.restrict ((sᶜ : Clopens X) : Set X)) = f := by
  ext x
  by_cases hx : x ∈ s
  · have hxc : x ∉ sᶜ := by simpa [← SetLike.mem_coe] using hx
    rw [add_apply, zeroExtendClopen_apply_mem s _ hx, zeroExtendClopen_apply_not_mem _ _ hxc,
      add_zero]
    exact restrict_apply_mk f _ x hx
  · have hxc : x ∈ sᶜ := by simpa [← SetLike.mem_coe] using hx
    rw [add_apply, zeroExtendClopen_apply_not_mem s _ hx, zeroExtendClopen_apply_mem _ _ hxc,
      zero_add]
    exact restrict_apply_mk f _ x hxc

end Module

section Ring

variable [CompactSpace X] {R : Type*} [SeminormedRing R]

/-- Extending a restricted function by zero is multiplication by the clopen characteristic
function. -/
@[simp]
theorem zeroExtendClopen_restrict (s : Clopens X) (f : C(X, R)) :
    zeroExtendClopen R s (f.restrict s) =
      (LocallyConstant.charFn R s.isClopen : C(X, R)) * f := by
  ext x
  by_cases hx : x ∈ s
  · simpa [hx, LocallyConstant.coe_charFn] using restrict_apply_mk f (s : Set X) x hx
  · simp [hx, LocallyConstant.coe_charFn]

end Ring

-- The extension of the constant `7` on `{0} ⊆ Fin 2` takes value `7` at `0`.
example :
    zeroExtendClopen ℤ (⟨{0}, isClopen_discrete {0}⟩ : Clopens (Fin 2))
      (ContinuousMap.const _ (7 : ℤ)) 0 = 7 := by
  simp

-- The same extension vanishes at the other point.
example :
    zeroExtendClopen ℤ (⟨{0}, isClopen_discrete {0}⟩ : Clopens (Fin 2))
      (ContinuousMap.const _ (7 : ℤ)) 1 = 0 := by
  simp

-- Extending the unique function on the empty clopen gives the zero function.
example : zeroExtendClopen ℤ (⊥ : Clopens (Fin 2)) (0 : C((⊥ : Clopens (Fin 2)), ℤ)) = 0 := by
  ext x
  simp

end ContinuousMap

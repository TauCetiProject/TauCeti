/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Coordinatewise linear maps

Kernels and ranges of coordinatewise maps are coordinatewise submodules. The kernel
identification and preservation of quasi-inverses on finite products allow Fredholm
operators to be assembled from their blocks. The range formula also identifies the cokernel
with a product of cokernels through Mathlib’s `Submodule.quotientPi`.
-/

public section

namespace LinearMap

variable {R ι : Type*} {E F : ι → Type*} [Semiring R]
  [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]
  [∀ i, AddCommMonoid (F i)] [∀ i, Module R (F i)]

/-- The kernel of a coordinatewise linear map is the product of its kernels. -/
@[simp]
theorem ker_piMap (f : ∀ i, E i →ₗ[R] F i) :
    (piMap f).ker = Submodule.pi Set.univ (fun i ↦ (f i).ker) := by
  ext x
  simp [mem_ker, funext_iff]

/-- The range of a coordinatewise linear map is the product of its ranges. -/
@[simp]
theorem range_piMap (f : ∀ i, E i →ₗ[R] F i) :
    (piMap f).range = Submodule.pi Set.univ (fun i ↦ (f i).range) :=
  SetLike.coe_injective (Set.range_piMap (fun i ↦ f i))

/-- A coordinatewise map sends a family supported at one coordinate to the corresponding
family supported at that coordinate. -/
@[simp]
theorem piMap_single [DecidableEq ι] (f : ∀ i, E i →ₗ[R] F i) (i : ι) (x : E i) :
    piMap f (Pi.single i x) = Pi.single i (f i x) := by
  ext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [Pi.single_eq_of_ne hj]

/-- The kernel of a coordinatewise map, identified with the product of the kernels. -/
def kerPiMapEquiv (f : ∀ i, E i →ₗ[R] F i) :
    (piMap f).ker ≃ₗ[R] ∀ i, (f i).ker where
  toFun x i := ⟨x.val i, congrFun x.property i⟩
  invFun x := ⟨fun i ↦ (x i).val, funext fun i ↦ (x i).property⟩
  left_inv _ := (rfl)
  right_inv _ := (rfl)
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp]
theorem kerPiMapEquiv_apply (f : ∀ i, E i →ₗ[R] F i) (x : (piMap f).ker) (i : ι) :
    (kerPiMapEquiv f x i : E i) = x.val i := (rfl)

@[simp]
theorem kerPiMapEquiv_symm_apply (f : ∀ i, E i →ₗ[R] F i)
    (x : ∀ i, (f i).ker) (i : ι) :
    ((kerPiMapEquiv f).symm x).val i = x i := (rfl)

end LinearMap

namespace LinearMap

variable {R ι : Type*} [Ring R] [Finite ι] {E F : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
  [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]

/-- A finite product of maps with noetherian range has noetherian range. -/
theorem HasNoetherianRange.piMap {f : ∀ i, E i →ₗ[R] F i}
    (h : ∀ i, (f i).HasNoetherianRange) : (piMap f).HasNoetherianRange := by
  let (i : ι) : IsNoetherian R (f i).range := (h i).isNoetherian_range
  let g : (∀ i, (f i).range) →ₗ[R] ∀ i, F i := LinearMap.piMap fun i ↦ (f i).range.subtype
  have hg : g.range = (LinearMap.piMap f).range := by
    rw [range_piMap, range_piMap]
    simp
  rw [hasNoetherianRange_iff_range, ← hg]
  exact (HasNoetherianRange.of_isNoetherian_dom (f := g)).isNoetherian_range

end LinearMap

namespace LinearMap

open FiniteRangeSetoid

variable {R ι : Type*} [CommRing R] [Finite ι] {E F : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
  [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]

/-- Coordinatewise quasi-inverses assemble to a quasi-inverse on a finite product. -/
theorem IsQuasiInverse.piMap {f : ∀ i, E i →ₗ[R] F i} {g : ∀ i, F i →ₗ[R] E i}
    (h : ∀ i, (g i).IsQuasiInverse (f i)) : (piMap g).IsQuasiInverse (piMap f) := by
  constructor
  · rw [IsLeftQuasiInverse, equiv_iff_hasNoetherianRange]
    convert HasNoetherianRange.piMap (fun i ↦
      (equiv_iff_hasNoetherianRange.mp (h i).1)) using 1
    ext x i
    rfl
  · rw [IsRightQuasiInverse, equiv_iff_hasNoetherianRange]
    convert HasNoetherianRange.piMap (fun i ↦
      (equiv_iff_hasNoetherianRange.mp (h i).2)) using 1
    ext x i
    rfl

end LinearMap

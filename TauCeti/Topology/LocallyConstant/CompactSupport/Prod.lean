/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Support
public import TauCeti.Topology.LocallyConstant.CompactSupport
public import TauCeti.Topology.Sets.CompactOpens

/-!
# Slices and exchange of factors for locally constant functions with compact support

For topological spaces `X`, `Y` and an `R`-module `M`, a locally constant function
`f : X × Y → M` with compact support has slices `y ↦ f (x, y)` and `x ↦ f (x, y)` that are again
locally constant with compact support, and so is `(y, x) ↦ f (x, y)`. This file packages these
operations as `R`-linear maps between the modules `C_c^∞(·, M)`, and computes them on the
indicators `1_K • m` of compact open sets, whose slices are the indicators of the slices `K_x`.

## Main definitions

* `LocallyConstant.compactlySupported.sliceRight R M x`: `C_c^∞(X × Y, M) → C_c^∞(Y, M)`,
  `f ↦ (y ↦ f (x, y))`.
* `LocallyConstant.compactlySupported.sliceLeft R M y`: `C_c^∞(X × Y, M) → C_c^∞(X, M)`,
  `f ↦ (x ↦ f (x, y))`.
* `LocallyConstant.compactlySupported.swap R M`: `C_c^∞(X × Y, M) → C_c^∞(Y × X, M)`,
  `f ↦ ((y, x) ↦ f (x, y))`.

## Main results

* `LocallyConstant.compactlySupported.sliceRight_compactOpenIndicator`: the slice of `1_K • m` at
  `x` is `1_{K_x} • m`.
* `LocallyConstant.compactlySupported.sliceLeft_compactOpenIndicator`: the slice of `1_K • m` at
  `y` in the first variable is `1_{K^y} • m`, where `K^y = K.swap.slice y`.
* `LocallyConstant.compactlySupported.swap_compactOpenIndicator`: exchanging the variables of
  `1_K • m` gives `1_{K.swap} • m`.
* `LocallyConstant.compactlySupported.sliceRight_swap`,
  `LocallyConstant.compactlySupported.sliceLeft_swap`: slicing `f ∘ swap` in one variable is
  slicing `f` in the other.
-/

public section

open TopologicalSpace

namespace LocallyConstant.compactlySupported

variable {R X Y M : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Semiring R]
  [AddCommMonoid M] [Module R M]

variable (R M) in
/-- The **slice** `y ↦ f (x, y)` of a locally constant function `f` on `X × Y` with compact
support, an element of `C_c^∞(Y, M)`, as an `R`-linear map in `f`. -/
noncomputable def sliceRight (x : X) :
    compactlySupported R (X × Y) M →ₗ[R] compactlySupported R Y M where
  toFun f := ⟨(f : LocallyConstant (X × Y) M).comap ⟨Prod.mk x, .prodMk_right x⟩,
    mem_compactlySupported.2 ((mem_compactlySupported.1 f.property).comp_prodMk_right x)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem sliceRight_apply (x : X) (f : compactlySupported R (X × Y) M) (y : Y) :
    (sliceRight R M x f : LocallyConstant Y M) y = (f : LocallyConstant (X × Y) M) (x, y) :=
  (rfl)

variable (R M) in
/-- The **slice** `x ↦ f (x, y)` of a locally constant function `f` on `X × Y` with compact
support, an element of `C_c^∞(X, M)`, as an `R`-linear map in `f`. -/
noncomputable def sliceLeft (y : Y) :
    compactlySupported R (X × Y) M →ₗ[R] compactlySupported R X M where
  toFun f := ⟨(f : LocallyConstant (X × Y) M).comap ⟨(·, y), .prodMk_left y⟩,
    mem_compactlySupported.2 ((mem_compactlySupported.1 f.property).comp_prodMk_left y)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem sliceLeft_apply (y : Y) (f : compactlySupported R (X × Y) M) (x : X) :
    (sliceLeft R M y f : LocallyConstant X M) x = (f : LocallyConstant (X × Y) M) (x, y) :=
  (rfl)

variable (R M) in
/-- Exchanging the variables of a function in `C_c^∞(X × Y, M)`: `f ↦ ((y, x) ↦ f (x, y))`. -/
noncomputable def swap : compactlySupported R (X × Y) M →ₗ[R] compactlySupported R (Y × X) M where
  toFun f := ⟨(f : LocallyConstant (X × Y) M).comap ⟨Prod.swap, continuous_swap⟩,
    mem_compactlySupported.2 ((mem_compactlySupported.1 f.property).comp_homeomorph
      (Homeomorph.prodComm Y X))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem swap_apply (f : compactlySupported R (X × Y) M) (p : Y × X) :
    (swap R M f : LocallyConstant (Y × X) M) p = (f : LocallyConstant (X × Y) M) p.swap :=
  (rfl)

/-- Exchanging the variables twice gives back the original function. -/
@[simp]
theorem swap_swap (f : compactlySupported R (X × Y) M) : swap R M (swap R M f) = f :=
  compactlySupported.ext fun p ↦ by rw [swap_apply, swap_apply, Prod.swap_swap]

/-- Slicing `(y, x) ↦ f (x, y)` at `y` is slicing `f` at `y` in the other variable. -/
@[simp]
theorem sliceRight_swap (y : Y) (f : compactlySupported R (X × Y) M) :
    sliceRight R M y (swap R M f) = sliceLeft R M y f :=
  compactlySupported.ext fun x ↦ by rw [sliceRight_apply, swap_apply, sliceLeft_apply,
    Prod.swap_prod_mk]

/-- Slicing `(y, x) ↦ f (x, y)` at `x` in the first variable is slicing `f` at `x`. -/
@[simp]
theorem sliceLeft_swap (x : X) (f : compactlySupported R (X × Y) M) :
    sliceLeft R M x (swap R M f) = sliceRight R M x f :=
  compactlySupported.ext fun y ↦ by rw [sliceLeft_apply, swap_apply, sliceRight_apply,
    Prod.swap_prod_mk]

section Indicator

variable [T2Space X] [T2Space Y]

/-- The slice at `x` of the indicator `1_K • m` of a compact open `K ⊆ X × Y` is the indicator of
the slice `K_x`. -/
theorem sliceRight_compactOpenIndicator (K : CompactOpens (X × Y)) (m : M) (x : X) :
    sliceRight R M x ⟨compactOpenIndicator K m, compactOpenIndicator_mem_compactlySupported K m⟩ =
      ⟨compactOpenIndicator (K.slice x) m, compactOpenIndicator_mem_compactlySupported _ m⟩ :=
  compactlySupported.ext fun y ↦ by
    by_cases h : (x, y) ∈ K <;> simp [h]

/-- The slice at `y` of the indicator `1_K • m` of a compact open `K ⊆ X × Y`, in the first
variable, is the indicator of the slice `K^y = {x | (x, y) ∈ K}`, that is of `K.swap.slice y`. -/
theorem sliceLeft_compactOpenIndicator (K : CompactOpens (X × Y)) (m : M) (y : Y) :
    sliceLeft R M y ⟨compactOpenIndicator K m, compactOpenIndicator_mem_compactlySupported K m⟩ =
      ⟨compactOpenIndicator (K.swap.slice y) m, compactOpenIndicator_mem_compactlySupported _ m⟩ :=
  compactlySupported.ext fun x ↦ by
    by_cases h : (x, y) ∈ K <;> simp [h]

/-- Exchanging the variables of the indicator `1_K • m` of a compact open `K ⊆ X × Y` gives the
indicator of `K.swap`. -/
theorem swap_compactOpenIndicator (K : CompactOpens (X × Y)) (m : M) :
    swap R M ⟨compactOpenIndicator K m, compactOpenIndicator_mem_compactlySupported K m⟩ =
      ⟨compactOpenIndicator K.swap m, compactOpenIndicator_mem_compactlySupported _ m⟩ :=
  compactlySupported.ext fun p ↦ by
    by_cases h : p.swap ∈ K <;> simp [h]

end Indicator

end LocallyConstant.compactlySupported

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Smoothness of finite-dimensional linear families of bundle sections

Let `V` be a `𝕜`-vector bundle over `B`, let `D` be a finite-dimensional normed vector space over a
complete nontrivially normed field `𝕜`, and let `W d` be a family of sections of `V` along
`b : X → B` that depends `𝕜`-linearly on `d : D` at every point of `s : Set X`. If each individual
section `W d` has `C^n` total-space lift on `s`, then expanding in `Module.finBasis 𝕜 D` and
combining `ContMDiffOn.smul_totalSpace` with `ContMDiffOn.sum_sectionAlong` shows that
`y ↦ ⟨b (g y), W (f y) (g y)⟩` is jointly `C^n` along any `C^n` maps `f : Y → D` and `g : Y → X`
carrying `u` into `s`. Smoothness of `b` on `s` is not assumed separately, since it follows by
projecting `W 0` via `Bundle.contMDiff_proj`.

## Main results

* `TauCeti.contMDiffOn_totalSpaceMk_comp_of_linear`: joint `C^n` regularity along `C^n` maps into
  the finite-dimensional parameter space and the base domain.
* `TauCeti.contMDiffOn_totalSpaceMk_of_linear`: specialization to `univ ×ˢ s ⊆ D × EX` for
  sections along a map from a normed space `EX` (in particular, curves `𝕜 → B` or `ℝ → B`).
-/

public section

open Bundle Set
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
  {D : Type*} [NormedAddCommGroup D] [NormedSpace 𝕜 D] [FiniteDimensional 𝕜 D]
  {n : ℕ∞ω}

/-- If a family `W : D → ∀ x, V (b x)` of sections of `V` along `b : X → B` depends linearly on a
finite-dimensional parameter space `D` at every point of `s` and has `C^n` total-space lift on `s`
for each fixed `d : D`, then composing with `C^n` maps `f : Y → D` and `g : Y → X` taking `u` into
`s` gives a `C^n` map into the total space on `u`. Smoothness of `b` on `s` follows automatically
from `W 0`. -/
theorem contMDiffOn_totalSpaceMk_comp_of_linear
    {EX HX X EY HY Y : Type*}
    [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
    {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    [NormedAddCommGroup EY] [NormedSpace 𝕜 EY] [TopologicalSpace HY]
    {IY : ModelWithCorners 𝕜 EY HY} [TopologicalSpace Y] [ChartedSpace HY Y]
    {b : X → B} {s : Set X} {u : Set Y}
    (W : D → ∀ x, V (b x))
    (hlin : ∀ x ∈ s, ∃ L : D →ₗ[𝕜] V (b x), ∀ d, W d x = L d)
    (hW : ∀ d : D, ContMDiffOn IX (IB.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F (b x) (W d x)) s)
    {f : Y → D} {g : Y → X}
    (hf : ContMDiffOn IY 𝓘(𝕜, D) n f u)
    (hg : ContMDiffOn IY IX n g u)
    (hgs : MapsTo g u s) :
    ContMDiffOn IY (IB.prod 𝓘(𝕜, F)) n
      (fun y ↦ TotalSpace.mk' F (b (g y)) (W (f y) (g y))) u := by
  let basis := Module.finBasis 𝕜 D
  have hbase : ContMDiffOn IY IB n (fun y ↦ b (g y)) u :=
    ((contMDiff_proj V).comp_contMDiffOn (hW 0)).comp hg hgs
  have hterm (i : Fin (Module.finrank 𝕜 D)) :
      ContMDiffOn IY (IB.prod 𝓘(𝕜, F)) n
        (fun y ↦ TotalSpace.mk' F (b (g y)) (basis.repr (f y) i • W (basis i) (g y))) u := by
    have hcoeff : ContMDiffOn IY 𝓘(𝕜, 𝕜) n (fun y ↦ basis.repr (f y) i) u :=
      ((basis.coord i).toContinuousLinearMap.contMDiff).comp_contMDiffOn hf
    exact hcoeff.smul_totalSpace ((hW (basis i)).comp hg hgs)
  refine (ContMDiffOn.sum_sectionAlong (b := fun y ↦ b (g y)) Finset.univ
    (fun i y ↦ basis.repr (f y) i • W (basis i) (g y)) hbase fun i _ ↦ hterm i).congr ?_
  intro y hy
  obtain ⟨L, hL⟩ := hlin (g y) (hgs hy)
  refine congrArg (TotalSpace.mk' F (b (g y))) ?_
  calc W (f y) (g y)
      = L (∑ i, basis.repr (f y) i • basis i) := by rw [hL (f y), basis.sum_repr]
    _ = ∑ i, basis.repr (f y) i • W (basis i) (g y) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, hL (basis i)]

/-- If a family `W : D → ∀ x, V (b x)` of sections of `V` along `b : EX → B` depends linearly on a
finite-dimensional parameter space `D` at every point of `s` and has `C^n` total-space lift on `s`
for each fixed `d : D`, then `(d, x) ↦ ⟨b x, W d x⟩` is jointly `C^n` on `univ ×ˢ s`. In
particular, for `EX = 𝕜` (or `ℝ`), this applies to families of sections along any smooth curve. -/
theorem contMDiffOn_totalSpaceMk_of_linear
    {EX : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {b : EX → B} {s : Set EX}
    (W : D → ∀ x, V (b x))
    (hlin : ∀ x ∈ s, ∃ L : D →ₗ[𝕜] V (b x), ∀ d, W d x = L d)
    (hW : ∀ d : D, ContMDiffOn 𝓘(𝕜, EX) (IB.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F (b x) (W d x)) s) :
    ContMDiffOn 𝓘(𝕜, D × EX) (IB.prod 𝓘(𝕜, F)) n
      (fun q : D × EX ↦ TotalSpace.mk' F (b q.2) (W q.1 q.2)) (univ ×ˢ s) :=
  contMDiffOn_totalSpaceMk_comp_of_linear W hlin hW
    contDiff_fst.contMDiff.contMDiffOn contDiff_snd.contMDiff.contMDiffOn (fun _ hq ↦ hq.2)

end TauCeti

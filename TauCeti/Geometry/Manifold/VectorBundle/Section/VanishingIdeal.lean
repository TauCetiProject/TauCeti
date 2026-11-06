/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The fibre of a vector bundle as sections modulo the vanishing ideal

Let `V` be a smooth real vector bundle of finite rank over a finite-dimensional Hausdorff smooth
manifold `M`, and let `I_x` be the ideal of smooth real functions vanishing at `x`. The smooth
sections `Γ(V)` form a module over `C^∞(M)`, and its submodule `I_x Γ(V)` consists of the finite
sums `∑ fᵢ sᵢ` with `fᵢ(x) = 0`. A smooth section lies in `I_x Γ(V)` exactly when it vanishes at
`x`, so evaluation at `x` identifies the quotient `Γ(V) / I_x Γ(V)` with the fibre `V_x`.

Together with `TauCeti.smoothCotangentEquiv`, which identifies `I_x / I_x²` with the cotangent
space `T_x*M`, this turns the algebraic description of differential operators between modules of
sections into fibrewise statements: a `C^∞(M)`-linear construction on sections that descends
to the quotients by `I_x Γ(V)` becomes a map between fibres at `x`.

Finite rank enters through local frames: near `x` a section is a finite combination of frame
sections, which is what makes `I_x Γ(V)`, a submodule of *finite* sums, large enough.

## Main results

* `TauCeti.mem_smoothVanishingIdeal_smul_top_iff`: a smooth section lies in `I_x Γ(V)` if and
  only if it vanishes at `x`.
* `ContMDiffSection.ker_evalLinearMap`: the kernel of evaluation at `x` is `I_x Γ(V)`.
* `ContMDiffSection.evalLinearMap_surjective`: every vector of the fibre is the value of a global
  smooth section.
* `TauCeti.smoothSectionFiberEquiv`: the real-linear equivalence `Γ(V) / I_x Γ(V) ≃ V_x` sending
  the class of `s` to `s x`, and `TauCeti.smoothSectionFiberEquiv_smul`, its compatibility with
  multiplication by smooth functions through evaluation at `x`.

## Implementation notes

Near `x`, a section is the sum of its coefficients in the local frame of a trivialization times
the frame sections. Cutting both off by a smooth bump function equal to one near `x` gives global
smooth coefficients and sections. The coefficients vanish at `x` when the section does, and the
section differs from the cut-off sum by a section vanishing near `x`, which is `(1 - χ) s` for
another bump function `χ`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural operations in differential geometry*, Springer,
  1993, §§1.3–1.6 and §12.
-/

public section

noncomputable section

open Bundle Filter Function
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- A section in `I_x Γ(V)` vanishes at `x`. -/
theorem apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top {x : M} {s : Cₛ^∞⟮I; F, V⟯}
    (hs : s ∈ smoothVanishingIdeal I x • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)) :
    s x = 0 := by
  refine Submodule.smul_induction_on (p := fun s : Cₛ^∞⟮I; F, V⟯ ↦ s x = 0) hs ?_ ?_
  · intro f hf t _
    simp [mem_smoothVanishingIdeal_iff.mp hf]
  · intro s t hs ht
    simp [hs, ht]

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

/-- A smooth section vanishing on a neighbourhood of `x` lies in `I_x Γ(V)`. -/
theorem mem_smoothVanishingIdeal_smul_top_of_eventuallyEq_zero {x : M} {s : Cₛ^∞⟮I; F, V⟯}
    (hs : ∀ᶠ y in 𝓝 x, s y = 0) :
    s ∈ smoothVanishingIdeal I x • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯) := by
  obtain ⟨ρ, -, hρ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hs).mem_iff.mp hs
  let χ : C^∞⟮I, M; ℝ⟯ := ⟨ρ, ρ.contMDiff⟩
  have hχ : ⇑χ = ρ := ContMDiffMap.coeFn_mk _ _
  have hfac : s = (1 - χ) • s := by
    ext y
    by_cases hy : ρ y = 0
    · simp [hχ, hy]
    · simp [show s y = 0 from hρ hy]
  rw [hfac]
  exact Submodule.smul_mem_smul (by simp [hχ]) Submodule.mem_top

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]

/-- **A section vanishing at a point is a finite sum of products with functions vanishing
there.** A smooth section of a finite-rank bundle vanishing at `x` lies in `I_x Γ(V)`. -/
theorem mem_smoothVanishingIdeal_smul_top_of_apply_eq_zero {x : M} {s : Cₛ^∞⟮I; F, V⟯}
    (hs : s x = 0) :
    s ∈ smoothVanishingIdeal I x • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯) := by
  let e := trivializationAt F V x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let b := Module.finBasis ℝ F
  -- Globally smooth sections agreeing with the local frame of `e` near `x`.
  obtain ⟨t, ht, hte⟩ := e.exists_contMDiff_eventuallyEq_localFrame (I := I) b hx
  -- A bump function supported in `e.baseSet` and equal to one near `x`.
  obtain ⟨ρ, hρ, -⟩ := (SmoothBumpFunction.nhds_basis_support (I := I)
    (e.open_baseSet.mem_nhds hx)).mem_iff.mp (e.open_baseSet.mem_nhds hx)
  -- The cut-off frame coefficients of `s` are globally smooth.
  let c (i : Fin (Module.finrank ℝ F)) : C^∞⟮I, M; ℝ⟯ :=
    ⟨fun y ↦ ρ y * e.localFrameCoeff I b i y (s y), contMDiff_of_tsupport fun y hy ↦ by
      have hye : y ∈ e.baseSet := hρ (tsupport_mul_subset_left hy)
      exact ρ.contMDiff.contMDiffAt.mul
        (contMDiffAt_localFrameCoeff (I := I) b hye (s.contMDiff y) i)⟩
  have hc_apply (i) (y : M) : c i y = ρ y * e.localFrameCoeff I b i y (s y) := rfl
  let T (i : Fin (Module.finrank ℝ F)) : Cₛ^∞⟮I; F, V⟯ := ⟨t i, ht i⟩
  have hT_apply (i) (y : M) : T i y = t i y := rfl
  have hc (i) : c i ∈ smoothVanishingIdeal I x := by
    rw [mem_smoothVanishingIdeal_iff, hc_apply, hs, map_zero, mul_zero]
  -- Near `x`, the section is the sum of its frame coefficients times the frame.
  have hrem : ∀ᶠ y in 𝓝 x, (s - ∑ i, c i • T i) y = 0 := by
    filter_upwards [ρ.eventuallyEq_one, eventually_all.2 hte,
      e.eventually_eq_localFrame_sum_coeff_smul (I := I) b hx (s := s)] with y hρy hty hsy
    rw [← ContMDiffSection.evalLinearMap_apply, map_sub, map_sum]
    simp only [ContMDiffSection.evalLinearMap_apply, ContMDiffSection.smul_apply, hc_apply,
      hT_apply, hty, hρy, Pi.one_apply, one_mul]
    rw [sub_eq_zero, ← hsy]
  have hsum : ∑ i, c i • T i ∈
      smoothVanishingIdeal I x • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯) :=
    Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hc i) Submodule.mem_top
  simpa using add_mem (mem_smoothVanishingIdeal_smul_top_of_eventuallyEq_zero hrem) hsum

/-- A smooth section of a finite-rank bundle lies in `I_x Γ(V)`, the submodule of finite sums of
products with smooth functions vanishing at `x`, if and only if it vanishes at `x`. -/
theorem mem_smoothVanishingIdeal_smul_top_iff {x : M} {s : Cₛ^∞⟮I; F, V⟯} :
    s ∈ smoothVanishingIdeal I x • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯) ↔ s x = 0 :=
  ⟨apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top,
    mem_smoothVanishingIdeal_smul_top_of_apply_eq_zero⟩

end TauCeti

namespace ContMDiffSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Evaluation of smooth sections at a point is surjective: every fibre vector is the value of a
global smooth section. -/
theorem evalLinearMap_surjective [ContMDiffVectorBundle ∞ F V I] (x : M) :
    Surjective (evalLinearMap I F ∞ V x) := fun v ↦ by
  obtain ⟨s, hs, hsx⟩ := FiberBundle.exists_contMDiff_section_eq I F ∞ v
  exact ⟨⟨s, hs⟩, by simpa using hsx⟩

/-- The kernel of evaluation at `x` on smooth sections of a finite-rank bundle is `I_x Γ(V)`. -/
theorem ker_evalLinearMap [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] (x : M) :
    LinearMap.ker (evalLinearMap I F ∞ V x) =
      (TauCeti.smoothVanishingIdeal I x •
        (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)).restrictScalars ℝ := by
  ext s
  simp [TauCeti.mem_smoothVanishingIdeal_smul_top_iff]

end ContMDiffSection

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

variable (I F V) in
/-- **The fibre of a vector bundle is the module of sections modulo the vanishing ideal.** For a
smooth real vector bundle `V` of finite rank over a finite-dimensional Hausdorff manifold,
evaluation at `x` induces a real-linear equivalence `Γ(V) / I_x Γ(V) ≃ V_x`. -/
def smoothSectionFiberEquiv (x : M) :
    (Cₛ^∞⟮I; F, V⟯ ⧸ smoothVanishingIdeal I x • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)) ≃ₗ[ℝ]
      V x :=
  (Submodule.Quotient.restrictScalarsEquiv ℝ _).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (ContMDiffSection.ker_evalLinearMap x).symm ≪≫ₗ
    (ContMDiffSection.evalLinearMap I F ∞ V x).quotKerEquivOfSurjective
      (ContMDiffSection.evalLinearMap_surjective x)

/-- The equivalence `Γ(V) / I_x Γ(V) ≃ V_x` sends the class of a section to its value at `x`. -/
@[simp]
theorem smoothSectionFiberEquiv_mk (x : M) (s : Cₛ^∞⟮I; F, V⟯) :
    smoothSectionFiberEquiv I F V x (Submodule.Quotient.mk s) = s x := by
  simp [smoothSectionFiberEquiv]

/-- The inverse of `Γ(V) / I_x Γ(V) ≃ V_x` sends the value of a section at `x` to its class. -/
@[simp]
theorem smoothSectionFiberEquiv_symm_apply (x : M) (s : Cₛ^∞⟮I; F, V⟯) :
    (smoothSectionFiberEquiv I F V x).symm (s x) = Submodule.Quotient.mk s := by
  rw [LinearEquiv.symm_apply_eq, smoothSectionFiberEquiv_mk]

/-- The equivalence `Γ(V) / I_x Γ(V) ≃ V_x` turns multiplication by a smooth function into
multiplication by its value at `x`. -/
theorem smoothSectionFiberEquiv_smul (x : M) (f : C^∞⟮I, M; ℝ⟯)
    (q : Cₛ^∞⟮I; F, V⟯ ⧸ smoothVanishingIdeal I x • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)) :
    smoothSectionFiberEquiv I F V x (f • q) = f x • smoothSectionFiberEquiv I F V x q := by
  induction q using Submodule.Quotient.induction_on with
  | H s => rw [← Submodule.Quotient.mk_smul, smoothSectionFiberEquiv_mk,
      smoothSectionFiberEquiv_mk, ContMDiffSection.smul_apply]

end TauCeti

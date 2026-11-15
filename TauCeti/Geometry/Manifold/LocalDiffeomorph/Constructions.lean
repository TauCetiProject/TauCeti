/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.ContDiff.WithLp
-- Access the body of `IsLocalDiffeomorphAt` to lower the regularity of its witness.
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Constructions of partial diffeomorphisms

Basic ways of producing a `PartialDiffeomorph` include lowering the regularity of a given one and
reading a continuous linear equivalence as one at any regularity. Mathlib's
`ContinuousLinearEquiv.toDiffeomorph` gives the latter at regularity `∞` only, so it does not cover
the analytic regularity `ω`. A transition between charts taking specified points to the same
coordinate gives a local change of parameters intertwining those charts. The file also records
that the coordinate axes of a partial diffeomorphism into a real Euclidean space, centred at a
point, pull back to curves through that point.

It also records the source, target, forward map and inverse map of Mathlib's composition
`PartialDiffeomorph.trans`, so that callers need not unfold it through `OpenPartialHomeomorph`.

## Main definitions

* `PartialDiffeomorph.ofLE`: a `C^n` partial diffeomorphism as a `C^m` one, for `m ≤ n`.
* `ContinuousLinearEquiv.toPartialDiffeomorph`: a continuous linear equivalence as a `C^n` partial
  diffeomorphism defined everywhere, for any `n`.
* `PartialDiffeomorph.trans_source`, `PartialDiffeomorph.trans_target`,
  `PartialDiffeomorph.coe_trans`, `PartialDiffeomorph.coe_trans_symm`: the composition of partial
  diffeomorphisms, computed componentwise.

## Main results

* `PartialDiffeomorph.exists_transition`: charts with a common coordinate induce a local change
  of parameters carrying the specified points to one another.
* `PartialDiffeomorph.exists_curve_single_axis`: pulling a coordinate axis back through a
  partial diffeomorphism into `EuclideanSpace ℝ ι` gives a curve through the centre point, `C^n`
  near `0`.
-/

public section

noncomputable section

open Filter Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {m n : WithTop ℕ∞}

namespace PartialDiffeomorph

/-- A `C^n` partial diffeomorphism as a `C^m` one, for `m ≤ n`. -/
def ofLE (Φ : PartialDiffeomorph I J M N n) (hmn : m ≤ n) : PartialDiffeomorph I J M N m where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  contMDiffOn_toFun := Φ.contMDiffOn.of_le hmn
  contMDiffOn_invFun := Φ.symm.contMDiffOn.of_le hmn

/-- Lowering the regularity keeps the underlying partial equivalence. -/
@[simp]
theorem ofLE_toPartialEquiv (Φ : PartialDiffeomorph I J M N n) (hmn : m ≤ n) :
    (Φ.ofLE hmn).toPartialEquiv = Φ.toPartialEquiv :=
  (rfl)

section Trans

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 F' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  (Φ : PartialDiffeomorph I J M N n) (Ψ : PartialDiffeomorph J K N P n)

/-- The source of a composition of partial diffeomorphisms. -/
theorem trans_source : (Φ.trans Ψ).source = Φ.source ∩ Φ ⁻¹' Ψ.source :=
  (rfl)

/-- The target of a composition of partial diffeomorphisms. -/
theorem trans_target : (Φ.trans Ψ).target = Ψ.target ∩ Ψ.symm ⁻¹' Φ.target :=
  (rfl)

/-- The forward map of a composition of partial diffeomorphisms is the composition of the forward
maps. -/
theorem coe_trans : ⇑(Φ.trans Ψ) = Ψ ∘ Φ :=
  (rfl)

/-- The inverse map of a composition of partial diffeomorphisms is the composition of the inverse
maps, in the opposite order. -/
theorem coe_trans_symm : ⇑(Φ.trans Ψ).symm = Φ.symm ∘ Ψ.symm :=
  (rfl)

end Trans

open Set

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

/-- Two charts taking specified source points to the same coordinate induce a local change of
parameters. The transition sends `x` to `y`, stays in both chart domains, and intertwines
the coordinate maps. -/
theorem exists_transition (c : PartialDiffeomorph I K M P n)
    (d : PartialDiffeomorph J K N P n) {x : M} {y : N}
    (hx : x ∈ c.source) (hy : y ∈ d.source) (hxy : c x = d y) :
    ∃ e : PartialDiffeomorph I J M N n,
      x ∈ e.source ∧ e x = y ∧ e.source ⊆ c.source ∧
        MapsTo e e.source d.source ∧ ∀ z ∈ e.source, d (e z) = c z := by
  have hsource : (c.trans d.symm).source = c.source ∩ c ⁻¹' d.target := by
    simp [trans_toPartialEquiv, symm_toPartialEquiv]
  have hcoe (z : M) : (c.trans d.symm) z = d.symm (c z) := by
    simp [trans_toPartialEquiv, symm_toPartialEquiv]
  refine ⟨c.trans d.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsource]
    refine ⟨hx, ?_⟩
    rw [mem_preimage, hxy]
    exact d.map_source hy
  · rw [hcoe, hxy]
    exact d.left_inv hy
  · intro z hz
    exact (hsource ▸ hz).1
  · intro z hz
    rw [hcoe]
    exact d.map_target (hsource ▸ hz).2
  · intro z hz
    rw [hcoe]
    exact d.right_inv (hsource ▸ hz).2

section Axis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pulling a coordinate axis of a `C^n` partial diffeomorphism `ψ` into `EuclideanSpace ℝ ι`
with `ψ x = 0` back through the inverse chart gives a curve through `x`, `C^n` near the parameter
`0`, which at every parameter near `0` lies in the chart source and maps to the point of the axis
with that coordinate. -/
theorem exists_curve_single_axis {x : M}
    (ψ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ ι) M (EuclideanSpace ℝ ι) n)
    (hxψ : x ∈ ψ.source) (hψx : ψ x = 0) (i : ι) :
    ∃ γ : ℝ → M, (∀ᶠ t in 𝓝 0, ContMDiffAt 𝓘(ℝ) I n γ t) ∧ γ 0 = x ∧
      ∀ᶠ t in 𝓝 0, γ t ∈ ψ.source ∧ ψ (γ t) = EuclideanSpace.single i t := by
  have haxis : ContDiff ℝ n fun t : ℝ ↦ EuclideanSpace.single i t := by
    rw [contDiff_piLp]
    intro j
    simp only [PiLp.single_apply]
    split_ifs <;> fun_prop
  have haxis0 : EuclideanSpace.single i (0 : ℝ) = (0 : EuclideanSpace ℝ ι) := by simp
  have hzero : (0 : EuclideanSpace ℝ ι) ∈ ψ.target := by
    simpa only [hψx] using ψ.map_source hxψ
  -- Openness of the chart target makes the inverse-chart curve valid near zero.
  have hTarget : ∀ᶠ t in 𝓝 (0 : ℝ), EuclideanSpace.single i t ∈ ψ.target := by
    apply haxis.continuous.continuousAt
    simpa only [haxis0] using ψ.open_target.mem_nhds hzero
  refine ⟨fun t ↦ ψ.toOpenPartialHomeomorph.symm (EuclideanSpace.single i t),
    hTarget.mono fun t ht ↦ ?_, ?_, hTarget.mono fun t ht ↦ ⟨ψ.map_target ht, ψ.right_inv ht⟩⟩
  · -- The inverse chart is `C^n` on its open target.
    exact (ψ.contMDiffOn_invFun.contMDiffAt (ψ.open_target.mem_nhds ht)).comp t
      haxis.contMDiff.contMDiffAt
  · simp only [haxis0]
    rw [← hψx]
    exact ψ.left_inv hxψ

end Axis

end PartialDiffeomorph

/-- A `C^n` local diffeomorphism at a point is a `C^m` one, for `m ≤ n`. -/
theorem IsLocalDiffeomorphAt.of_le {f : M → N} {x : M} (hf : IsLocalDiffeomorphAt I J n f x)
    (hmn : m ≤ n) : IsLocalDiffeomorphAt I J m f x := by
  obtain ⟨Φ, hxΦ, hfΦ⟩ := hf
  exact ⟨Φ.ofLE hmn, by simpa using hxΦ, by simpa using hfΦ⟩

/-- A `C^n` local diffeomorphism is a `C^m` one, for `m ≤ n`. -/
theorem IsLocalDiffeomorph.of_le {f : M → N} (hf : IsLocalDiffeomorph I J n f) (hmn : m ≤ n) :
    IsLocalDiffeomorph I J m f :=
  fun x ↦ (hf x).of_le hmn

namespace ContinuousLinearEquiv

/-- A continuous linear equivalence as a `C^n` partial diffeomorphism defined everywhere, for any
regularity `n`, including the analytic regularity `ω` not reached by
`ContinuousLinearEquiv.toDiffeomorph`. -/
def toPartialDiffeomorph (A : E ≃L[𝕜] F) : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) E F n where
  toPartialEquiv := A.toEquiv.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := A.contDiff.contMDiff.contMDiffOn
  contMDiffOn_invFun := A.symm.contDiff.contMDiff.contMDiffOn

/-- The partial equivalence underlying `ContinuousLinearEquiv.toPartialDiffeomorph` is the
underlying equivalence, on the whole space. -/
@[simp]
theorem toPartialDiffeomorph_toPartialEquiv (A : E ≃L[𝕜] F) :
    (A.toPartialDiffeomorph (n := n)).toPartialEquiv = A.toEquiv.toPartialEquiv :=
  (rfl)

end ContinuousLinearEquiv

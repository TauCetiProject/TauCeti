/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorField.Pullback
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Vector fields through partial diffeomorphisms

Let `Φ` be a partial diffeomorphism from a manifold `M` to a manifold `M'`, such as a chart, and
let it carry a vector field `X` on `M` to a vector field `Y` on `M'` on its source:
`dΦ_x (X x) = Y (Φ x)` for `x ∈ Φ.source`. Then `Φ⁻¹` carries `Y` back to `X` on the target
(`PartialDiffeomorph.mfderiv_symm_apply_eq_of_mfderiv_apply_eq`).

Vector fields built in a normed space are carried to the manifold this way: a `C^m` field `W₀`
with compact support in the target of a `C^n` partial diffeomorphism `Φ` onto an open subset of a
normed space, with `m + 1 ≤ n`, is the image under `Φ` of a `C^m` field on the manifold which
vanishes outside `Φ⁻¹ (tsupport W₀)` (`PartialDiffeomorph.exists_contMDiff_mfderiv_apply_eq`). On
the source of `Φ` it is the pullback `VectorField.mpullback` of `W₀`, extended by zero. For the
extended chart at a point, possibly with boundary, this is `TauCeti.chartField`; here `Φ` is any
partial diffeomorphism onto an open subset of the normed space, such as a straightening chart.

## Main results

* `PartialDiffeomorph.exists_contMDiff_mfderiv_apply_eq`: a compactly supported vector field on
  the target of a partial diffeomorphism into a normed space is the image of a vector field on the
  manifold, of the same regularity, vanishing off the preimage of its support.
* `PartialDiffeomorph.mfderiv_symm_apply_eq_of_mfderiv_apply_eq`: the inverse of a partial
  diffeomorphism carrying `X` to `Y` carries `Y` to `X` on its target.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

section Transplant

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace E] [T2Space M] [IsManifold I 1 M]

/-- **Transplanting a vector field through a partial diffeomorphism.** Let `Φ` be a `C^n` partial
diffeomorphism from `M` onto an open subset of a normed space `V`, and let `W₀` be a
`C^m` vector field on `V` with compact support in the target of `Φ`, where `m + 1 ≤ n`. Then there
is a `C^m` vector field `W` on `M`, vanishing outside the compact set `Φ⁻¹ (tsupport W₀)`, which
`Φ` carries to `W₀`: `dΦ_x (W x) = W₀ (Φ x)` for `x ∈ Φ.source`. -/
theorem exists_contMDiff_mfderiv_apply_eq {m : ℕ∞ω} (Φ : PartialDiffeomorph I 𝓘(ℝ, V) M V n)
    (hmn : m + 1 ≤ n) {W₀ : V → V} (hW₀ : ContDiff ℝ m W₀) (hc : HasCompactSupport W₀)
    (hsupp : tsupport W₀ ⊆ Φ.target) :
    ∃ W : (x : M) → TangentSpace I x,
      CMDiff m (fun x ↦ (⟨x, W x⟩ : TangentBundle I M)) ∧
        (∀ x ∉ Φ.symm '' tsupport W₀, W x = 0) ∧
        ∀ x ∈ Φ.source, mfderiv I 𝓘(ℝ, V) Φ x (W x) = W₀ (Φ x) := by
  classical
  have hn : n ≠ 0 := ne_bot_of_le_ne_bot (by simp) hmn
  set K := Φ.symm '' tsupport W₀
  have hK : IsCompact K :=
    hc.isCompact.image_of_continuousOn (Φ.symm.contMDiffOn.continuousOn.mono hsupp)
  have hKs : K ⊆ Φ.source := image_subset_iff.2 fun y hy ↦ Φ.map_target (hsupp hy)
  -- Off `K`, the pullback of `W₀` vanishes at the points of the source.
  have hW₀K {x : M} (hx : x ∈ Φ.source) (hxK : x ∉ K) : W₀ (Φ x) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hxK ⟨Φ x, h, Φ.left_inv hx⟩
  -- The pullback of `W₀`, a field on `M` defined on the source of `Φ`, extended by zero.
  let W₀' : (y : V) → TangentSpace 𝓘(ℝ, V) y := W₀
  let W : (x : M) → TangentSpace I x :=
    fun x ↦ if x ∈ Φ.source then VectorField.mpullback I 𝓘(ℝ, V) Φ W₀' x else 0
  have hWK {x : M} (hxK : x ∉ K) : W x = 0 := by
    by_cases hx : x ∈ Φ.source
    · simp only [W, hx, ↓reduceIte]
      rw [VectorField.mpullback_apply, show W₀' (Φ x) = 0 from hW₀K hx hxK, map_zero]
    · simp only [W, hx, ↓reduceIte]
  refine ⟨W, fun x ↦ ?_, fun x hxK ↦ hWK hxK, fun x hx ↦ ?_⟩
  · by_cases hx : x ∈ Φ.source
    · -- On the source, the field is the pullback of `W₀` by the differentials of `Φ`.
      refine (ContMDiffAt.mpullback_vectorField_preimage
        ((contMDiff_vectorSpace_iff_contDiff.2 hW₀) (Φ x))
        (Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds hx))
        (Φ.isInvertible_mfderiv hn hx) hmn).congr_of_eventuallyEq ?_
      filter_upwards [Φ.open_source.mem_nhds hx] with z hz
      simp only [W, hz, ↓reduceIte]
      rfl
    · -- Off the source, the field vanishes near `x`, which is not in the compact set `K`.
      refine ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _))
        x).congr_of_eventuallyEq ?_
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds fun h ↦ hx (hKs h)] with z hz
      rw [hWK hz]
      rfl
  · simp only [W, hx, ↓reduceIte]
    rw [VectorField.mpullback_apply]
    exact (Φ.isInvertible_mfderiv hn hx).self_apply_inverse _

end Transplant

section Related

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  (Φ : PartialDiffeomorph I I' M M' n) (hn : n ≠ 0)
  {X : (x : M) → TangentSpace I x} {Y : (y : M') → TangentSpace I' y}

include hn

/-- If a partial diffeomorphism carries the vector field `X` to `Y` on its source, its inverse
carries `Y` to `X` on its target. -/
theorem mfderiv_symm_apply_eq_of_mfderiv_apply_eq
    (hXY : ∀ x ∈ Φ.source, mfderiv I I' Φ x (X x) = Y (Φ x)) {y : M'} (hy : y ∈ Φ.target) :
    mfderiv I' I Φ.symm y (Y y) = X (Φ.symm y) := by
  obtain ⟨x, hx, rfl⟩ : ∃ x ∈ Φ.source, Φ x = y := ⟨_, Φ.map_target hy, Φ.right_inv hy⟩
  rw [← hXY x hx, Φ.mfderiv_symm_apply_mfderiv_apply hn hx]
  -- The tangent spaces at `x` and at `Φ⁻¹ (Φ x) = x` are both the model space `E`.
  exact congrArg (fun z ↦ (X z : E)) (Φ.left_inv hx).symm

end Related

end PartialDiffeomorph

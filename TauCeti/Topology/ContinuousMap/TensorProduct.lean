/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.UniformSpace.ProdApproximation
public import TauCeti.Algebra.Star.TensorProductLift
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# The star homomorphism `C(X) ⊗ C(Y) → C(X × Y)`

For topological spaces `X` and `Y` and a topological commutative star ring `R`,
`TauCeti.continuousMapTensorHom R X Y : C(X, R) ⊗[R] C(Y, R) →⋆ₙₐ[R] C(X × Y, R)` sends
`f ⊗ g` to `(x, y) ↦ f x * g y`. It is the star homomorphism version of Mathlib's linear map
`ContinuousMap.tensorHom` (`TauCeti.coe_continuousMapTensorHom`).

For compact Hausdorff `X` and `Y` and `RCLike 𝕜`, the Stone–Weierstrass theorem shows that it
has dense range (`TauCeti.denseRange_continuousMapTensorHom`), and therefore so does Mathlib's
`ContinuousMap.tensorHom` (`ContinuousMap.denseRange_tensorHom_of_rclike`); Mathlib proves the
latter for a totally disconnected `X` (`ContinuousMap.denseRange_tensorHom`).
-/

public section

noncomputable section

open TensorProduct

namespace TauCeti

variable (R : Type*) [CommRing R] [StarRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [ContinuousStar R]
variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

/-- The star homomorphism `C(X, R) ⊗[R] C(Y, R) → C(X × Y, R)`,
`f ⊗ g ↦ ((x, y) ↦ f x * g y)`. -/
def continuousMapTensorHom : C(X, R) ⊗[R] C(Y, R) →⋆ₙₐ[R] C(X × Y, R) :=
  Algebra.TensorProduct.liftNonUnitalStarAlgHom
    (ContinuousMap.compStarAlgHom' R R (ContinuousMap.fst : C(X × Y, X))).toNonUnitalStarAlgHom
    (ContinuousMap.compStarAlgHom' R R (ContinuousMap.snd : C(X × Y, Y))).toNonUnitalStarAlgHom
    fun _ _ ↦ Commute.all _ _

variable {R X Y}

/-- `TauCeti.continuousMapTensorHom` is Mathlib's linear map `ContinuousMap.tensorHom`. -/
theorem coe_continuousMapTensorHom :
    ⇑(continuousMapTensorHom R X Y) =
      ⇑(ContinuousMap.tensorHom : C(X, R) ⊗[R] C(Y, R) →ₗ[R] C(X × Y, R)) := by
  funext z
  induction z using TensorProduct.inductionOn with
  | tmul f g => ext; simp [continuousMapTensorHom]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

@[simp]
theorem continuousMapTensorHom_tmul_apply (f : C(X, R)) (g : C(Y, R)) (p : X × Y) :
    continuousMapTensorHom R X Y (f ⊗ₜ g) p = f p.1 * g p.2 := by
  rw [coe_continuousMapTensorHom, ContinuousMap.tensorHom_tmul, ContinuousMap.prodMul_apply]

variable {𝕜 : Type*} [RCLike 𝕜]
variable [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]

/-- **Stone–Weierstrass**: the functions `(x, y) ↦ Σ fᵢ x * gᵢ y` are dense in `C(X × Y, 𝕜)`. -/
theorem denseRange_continuousMapTensorHom : DenseRange (continuousMapTensorHom 𝕜 X Y) := by
  let S : StarSubalgebra 𝕜 C(X × Y, 𝕜) :=
    (continuousMapTensorHom 𝕜 X Y).range.toStarSubalgebra
      ((NonUnitalStarAlgHom.mem_range _).2 ⟨1 ⊗ₜ 1, by ext; simp⟩)
  have hsep : S.SeparatesPoints := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hne
    by_cases hx : x = x'
    · subst hx
      obtain ⟨g, hg, hgy⟩ :=
        separatesPoints_continuous_of_t35Space (fun h ↦ hne (by rw [h]) : y ≠ y')
      exact ⟨_, ⟨_, NonUnitalStarAlgHom.mem_range_self _
        (1 ⊗ₜ ⟨fun t ↦ (g t : 𝕜), RCLike.continuous_ofReal.comp hg⟩), rfl⟩, by simpa using hgy⟩
    · obtain ⟨f, hf, hfx⟩ := separatesPoints_continuous_of_t35Space hx
      exact ⟨_, ⟨_, NonUnitalStarAlgHom.mem_range_self _
        (⟨fun t ↦ (f t : 𝕜), RCLike.continuous_ofReal.comp hf⟩ ⊗ₜ 1), rfl⟩, by simpa using hfx⟩
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hsep
  rw [DenseRange, dense_iff_closure_eq]
  have := congr_arg (fun T : StarSubalgebra 𝕜 C(X × Y, 𝕜) ↦ (T : Set C(X × Y, 𝕜))) h
  simp only [StarSubalgebra.topologicalClosure_coe, StarSubalgebra.coe_top] at this
  exact this

/-- Mathlib's linear map `ContinuousMap.tensorHom : C(X, 𝕜) ⊗[𝕜] C(Y, 𝕜) → C(X × Y, 𝕜)` has
dense range for compact Hausdorff `X` and `Y`. -/
theorem _root_.ContinuousMap.denseRange_tensorHom_of_rclike :
    DenseRange (ContinuousMap.tensorHom : C(X, 𝕜) ⊗[𝕜] C(Y, 𝕜) → C(X × Y, 𝕜)) :=
  coe_continuousMapTensorHom (R := 𝕜) (X := X) (Y := Y) ▸ denseRange_continuousMapTensorHom

end TauCeti

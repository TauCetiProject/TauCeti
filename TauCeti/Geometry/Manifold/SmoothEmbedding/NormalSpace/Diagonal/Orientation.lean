/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Diagonal
public import TauCeti.Geometry.Manifold.Orientation.Prod
public import TauCeti.Topology.VectorBundle.Orientation.Comap
import TauCeti.LinearAlgebra.Orientation.Exact.Basic

/-!
# Orienting the normal bundle of the diagonal

The canonical quotient comparison transports a tangent orientation to the intrinsic normal
bundle of the diagonal. With tangent directions first and normal directions second, the
splitting `(a, q) ↦ (a, a + φ q)` agrees with the ordered product orientation. The construction
includes dimension zero and retains both orientation signs.

This is a linear and bundle orientation comparison. It does not identify the singular cross
product of fundamental classes with the fundamental class of a selected smooth product
orientation.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §11 (the diagonal normal orientation).
-/

public noncomputable section

open Bundle Function Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

private theorem map_shear_orientation {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {m : ℕ} (o : Orientation ℝ V (Fin m)) (hm : finrank ℝ V = m) :
    Orientation.map (Fin (m + m))
      ((LinearEquiv.refl ℝ V).skewProd (LinearEquiv.refl ℝ V) LinearMap.id)
      (Orientation.prod o o hm hm) = Orientation.prod o o hm hm := by
  let hf := LinearMap.inr_injective (R := ℝ) (M := V) (M₂ := V)
  let hfg := Function.Exact.inr_fst (R := ℝ) (M := V) (N := V)
  let hg := LinearMap.fst_surjective (R := ℝ) (M := V) (M₂ := V)
  let q := Orientation.prod o o hm hm
  let k := Orientation.kerOfExact hf hfg hg q o hm hm
  have h := Orientation.map_ofExact hf hfg hg hf hfg hg
    (LinearEquiv.refl ℝ V)
    ((LinearEquiv.refl ℝ V).skewProd (LinearEquiv.refl ℝ V) LinearMap.id)
    (LinearEquiv.refl ℝ V) (by intro v; simp) (by intro v; simp) k o hm hm
  simpa only [k, q, Orientation.map_refl, Equiv.refl_apply,
    Orientation.ofExact_kerOfExact] using h

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The splitting of the ambient tangent space into tangent directions followed by intrinsic
normal directions, using the canonical difference comparison. -/
def diagonalTangentNormalEquiv (x : M) :
    (TangentSpace I x × (diagonal (I := I) (M := M)).NormalSpace x (by simp))
      ≃L[ℝ] TangentSpace (I.prod I) (x, x) := by
  exact ((ContinuousLinearEquiv.refl ℝ (TangentSpace I x)).prodCongr
    (diagonalNormalEquiv (I := I) x)).trans
      (((ContinuousLinearEquiv.refl ℝ (TangentSpace I x)).skewProd
        (ContinuousLinearEquiv.refl ℝ (TangentSpace I x))
        (ContinuousLinearMap.id ℝ (TangentSpace I x))).trans
          (TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := I) (x, x)).symm)

/-- In native product tangent coordinates, the splitting sends `(a, q)` to `(a, a + φ q)`.
-/
@[simp]
theorem diagonalTangentNormalEquiv_apply (x : M) (a : TangentSpace I x)
    (q : (diagonal (I := I) (M := M)).NormalSpace x (by simp)) :
    TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := I) (x, x)
      (diagonalTangentNormalEquiv (I := I) x (a, q)) =
        (a, a + diagonalNormalEquiv (I := I) x q) := by
  simp only [diagonalTangentNormalEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply,
    ContinuousLinearEquiv.skewProd_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.apply_symm_apply, add_comm]

variable [FiniteDimensional ℝ E]

/-- The normal orientation whose quotient-to-tangent comparison preserves the given tangent
orientation. It uses the original intrinsic normal atlas and includes zero-dimensional fibres.
-/
def diagonalNormalOrientation {m : ℕ} (o : Manifold.Orientation I M (Fin m)) :
    letI := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
    letI := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    letI := (diagonal (I := I) (M := M)).normalSpaceVectorBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    VectorBundleOrientation E ((diagonal (I := I) (M := M)).NormalSpace · (by simp)) (Fin m) := by
  letI := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
  letI := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
    (by simp [Module.finrank_prod])
  letI := (diagonal (I := I) (M := M)).normalSpaceVectorBundle (P := E) (by simp)
    (by simp [Module.finrank_prod])
  exact o.toVectorBundleOrientation.comap (g := ContinuousMap.id M)
    (φ := diagonalNormalEquiv (I := I)) o.card_eq contMDiff_diagonalNormalEquiv.continuous

/-- The actual quotient comparison carries the chosen normal orientation to the tangent
orientation. -/
@[simp]
theorem diagonalNormalOrientation_map {m : ℕ} (o : Manifold.Orientation I M (Fin m)) (x : M) :
    letI := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
    letI := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    letI := (diagonal (I := I) (M := M)).normalSpaceVectorBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    Orientation.map (Fin m) (diagonalNormalEquiv (I := I) x).toLinearEquiv
      (diagonalNormalOrientation o x) = o.orientationAt x := by
  let := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
  let := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
    (by simp [Module.finrank_prod])
  let := (diagonal (I := I) (M := M)).normalSpaceVectorBundle (P := E) (by simp)
    (by simp [Module.finrank_prod])
  dsimp only [diagonalNormalOrientation]
  exact (VectorBundleOrientation.map_comap_apply (g := ContinuousMap.id M)
    (φ := diagonalNormalEquiv (I := I)) o.card_eq o.toVectorBundleOrientation
    contMDiff_diagonalNormalEquiv.continuous x).trans (o.toVectorBundleOrientation_apply x)

/-- Reversing the tangent orientation reverses the transported normal orientation, also in
rank zero. -/
@[simp]
theorem diagonalNormalOrientation_neg {m : ℕ} (o : Manifold.Orientation I M (Fin m)) :
    letI := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
    letI := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    letI := (diagonal (I := I) (M := M)).normalSpaceVectorBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    diagonalNormalOrientation (-o) = -diagonalNormalOrientation o := by
  let := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
  let := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
    (by simp [Module.finrank_prod])
  let := (diagonal (I := I) (M := M)).normalSpaceVectorBundle (P := E) (by simp)
    (by simp [Module.finrank_prod])
  dsimp only [diagonalNormalOrientation]
  rw [Manifold.Orientation.toVectorBundleOrientation_neg]
  exact VectorBundleOrientation.comap_neg (g := ContinuousMap.id M)
    (φ := diagonalNormalEquiv (I := I)) o.card_eq o.toVectorBundleOrientation
    contMDiff_diagonalNormalEquiv.continuous

/-- Tangent directions first and normal directions second give the ordered ambient product
orientation. This fixes the sign of the difference comparison and includes dimension zero. -/
theorem diagonalTangentNormalEquiv_map_orientation {m : ℕ}
    (o : Manifold.Orientation I M (Fin m)) (x : M) :
    letI := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
    letI := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    letI := (diagonal (I := I) (M := M)).normalSpaceVectorBundle (P := E) (by simp)
      (by simp [Module.finrank_prod])
    Orientation.map (Fin (m + m)) (diagonalTangentNormalEquiv (I := I) x).toLinearEquiv
      (Orientation.prod (o.orientationAt x) (diagonalNormalOrientation o x)
        (by simpa using o.finrank_tangentSpace_eq x)
        ((diagonalNormalEquiv (I := I) x).toLinearEquiv.finrank_eq.trans
          (by simpa using o.finrank_tangentSpace_eq x))) =
      (o.prod o).orientationAt (x, x) := by
  let := (diagonal (I := I) (M := M)).instTopologicalSpaceNormalBundle (K := E) (by simp)
  let := (diagonal (I := I) (M := M)).normalSpaceFiberBundle (P := E) (by simp)
    (by simp [Module.finrank_prod])
  let := (diagonal (I := I) (M := M)).normalSpaceVectorBundle (P := E) (by simp)
    (by simp [Module.finrank_prod])
  have hsplit : (diagonalTangentNormalEquiv (I := I) x).toLinearEquiv =
      ((LinearEquiv.refl ℝ (TangentSpace I x)).prodCongr
        (diagonalNormalEquiv (I := I) x).toLinearEquiv).trans
      (((LinearEquiv.refl ℝ (TangentSpace I x)).skewProd
        (LinearEquiv.refl ℝ (TangentSpace I x)) LinearMap.id).trans
        (TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := I) (x, x)).symm.toLinearEquiv) := by
    rfl
  rw [hsplit, Orientation.map_trans, Orientation.map_prod, Orientation.map_refl,
    Equiv.refl_apply, diagonalNormalOrientation_map, Orientation.map_trans,
    map_shear_orientation]
  have he : (TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := I)
      (x, x)).symm.toLinearEquiv = LinearEquiv.refl ℝ (E × E) := by
    ext v
    exact TauCeti.Manifold.tangentSpaceProdEquiv_symm_apply (I := I) (J := I) (x, x) v
  rw [he]
  -- The native product tangent type and the product model have definitionally equal instances.
  erw [Orientation.map_refl, Equiv.refl_apply]
  exact (Manifold.Orientation.orientationAt_prod o o (x, x)).symm

end TauCeti.SmoothEmbedding

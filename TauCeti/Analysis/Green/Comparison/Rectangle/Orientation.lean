/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Orientation
public import TauCeti.Geometry.Manifold.Orientation.Rectangle

/-!
# Actual outward-first orientations of rectangle faces

The face derivatives transport positively oriented tangent bases of the signed interval
orientations to the four counterclockwise velocities. Their outward-first frames agree with
the actual rectangle orientation transported by the rectangle inclusion derivative, including
at face endpoints.
-/

public section

noncomputable section

open Set Fact.Manifold
open scoped Manifold

namespace TauCeti.Green

/-- The counterclockwise velocities on the four rectangle faces have normals which leave
the rectangle immediately. The faces here include their endpoints; no set-theoretic boundary
manifold is asserted at a corner. -/
theorem rectangle_face_normals_outward {a b c d : ℝ} (x : Icc a b) (y : Icc c d)
    {t : ℝ} (ht : 0 < t) :
    (⟨x, c⟩ : ℂ) + t • (-Complex.I * 1) ∉ verticalRegion a b (fun _ ↦ c) (fun _ ↦ d) ∧
    (⟨b, y⟩ : ℂ) + t • (-Complex.I * Complex.I) ∉
      verticalRegion a b (fun _ ↦ c) (fun _ ↦ d) ∧
    (⟨x, d⟩ : ℂ) + t • (-Complex.I * -1) ∉ verticalRegion a b (fun _ ↦ c) (fun _ ↦ d) ∧
    (⟨a, y⟩ : ℂ) + t • (-Complex.I * -Complex.I) ∉
      verticalRegion a b (fun _ ↦ c) (fun _ ↦ d) := by
  simp only [mem_verticalRegion]
  constructor
  · intro h
    have h' := h.2.1
    norm_num at h'
    linarith
  constructor
  · intro h
    have h' := h.1.2
    norm_num at h'
    linarith
  constructor
  · intro h
    have h' := h.2.2
    norm_num at h'
    linarith
  · intro h
    have h' := h.1.1
    norm_num at h'
    linarith


/-- The canonical rectangle orientation, transported through its actual inclusion derivative
and the standard real-plane identification, is the complex orientation at every corner and edge. -/
theorem map_orientationAt_rectangle_complex {a b c d : ℝ} [Fact (a < b)] [Fact (c < d)]
    (x : Icc a b × Icc c d) :
    Orientation.map (Fin 2)
      ((subtypeValRectangleTangentEquiv x).trans Complex.equivRealProdCLM.symm).toLinearEquiv
      (((Manifold.Orientation.interval a b).prod
        (Manifold.Orientation.interval c d)).orientationAt x) = Complex.orientation := by
  have h := Manifold.Orientation.map_orientationAt_interval_prod x
  -- Orientation transport composes underlying linear equivalences, rather than their CLM wrappers.
  change Orientation.map (Fin 2)
    ((subtypeValRectangleTangentEquiv x).toLinearEquiv.trans
      Complex.equivRealProdCLM.symm.toLinearEquiv) _ = _
  rw [Orientation.map_trans, h, ← Module.Basis.orientation_map]
  apply congrArg Module.Basis.orientation
  have h0 : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 0 = Sum.inl 0 :=
    finSumFinEquiv_symm_apply_castAdd (n := 1) (0 : Fin 1)
  have h1 : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 1 = Sum.inr 0 :=
    finSumFinEquiv_symm_apply_natAdd (m := 1) (0 : Fin 1)
  ext i
  fin_cases i <;> simp [h0, h1, Module.Basis.map_apply, Module.Basis.reindex_apply,
    Module.Basis.prod_apply, Complex.equivRealProdCLM_symm_apply, Complex.coe_basisOneI]

/-- The positive tangent of the signed horizontal face orientation has the counterclockwise
velocity. Its outward-first frame has exactly the transported rectangle orientation, and its
normal leaves the rectangle. `upper = false` is the bottom face; `upper = true` is the top.
The assertions include both endpoints of each face. -/
theorem exists_horizontal_face_outwardFirst {a b c d : ℝ} [Fact (a < b)] [Fact (c < d)]
    (upper : Bool) (x : Icc a b) :
    let y : Icc c d := if upper then ⊤ else ⊥
    let v : ℂ := if upper then -1 else 1
    let o := if upper then -Manifold.Orientation.interval a b
      else Manifold.Orientation.interval a b
    ∃ B : Module.Basis (Fin 1) ℝ (TangentSpace (𝓡∂ 1) x),
      B.orientation = o.orientationAt x ∧
      NormedSpace.fromTangentSpace (𝕜 := ℝ) (⟨x, y⟩ : ℂ)
        (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℂ) (fun t : Icc a b ↦ (⟨t, y⟩ : ℂ)) x (B 0)) = v ∧
      (∀ t : ℝ, 0 < t → (⟨x, y⟩ : ℂ) + t • (-Complex.I * v) ∉
        verticalRegion a b (fun _ ↦ c) (fun _ ↦ d)) ∧
      ∃ hv : v ≠ 0, (outwardFirstBasis v hv).orientation =
        Orientation.map (Fin 2)
          ((subtypeValRectangleTangentEquiv (x, y)).trans
            Complex.equivRealProdCLM.symm).toLinearEquiv
          (((Manifold.Orientation.interval a b).prod
            (Manifold.Orientation.interval c d)).orientationAt (x, y)) := by
  obtain ⟨B, C, hB, hC, hb, hc⟩ := exists_interval_tangent_bases x
  have hd (y : ℝ) (w : TangentSpace (𝓡∂ 1) x) :
      NormedSpace.fromTangentSpace (𝕜 := ℝ) (⟨x, y⟩ : ℂ)
        (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℂ) (fun t : Icc a b ↦ (⟨t, y⟩ : ℂ)) x w) =
          (subtypeValIccTangentEquiv x w : ℂ) := by
    have h := mfderiv_interval_affine_apply ((y : ℂ) * Complex.I) Complex.ofRealCLM x w
    have he : (fun t : Icc a b ↦ (y : ℂ) * Complex.I + Complex.ofRealCLM t) =
        (fun t : Icc a b ↦ (⟨t, y⟩ : ℂ)) := by
      funext t
      apply Complex.ext <;> simp
    -- Expose the affine map as a single function so its equality rewrites the dependent base point.
    change NormedSpace.fromTangentSpace (𝕜 := ℝ)
      ((fun t : Icc a b ↦ (y : ℂ) * Complex.I + Complex.ofRealCLM t) x)
      (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℂ) _ x w) = _ at h
    rw [he] at h
    exact h
  cases upper <;> dsimp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
  · refine ⟨B, hB, ?_, ?_, one_ne_zero, ?_⟩
    · rw [hd]
      -- Evaluate the chosen basis on the canonical model before casting the real velocity.
      change (subtypeValIccTangentEquiv x (B 0) : ℂ) = 1
      exact_mod_cast hb
    · intro t ht
      exact (rectangle_face_normals_outward x (⊥ : Icc c d) ht).1
    · rw [orientation_outwardFirstBasis, map_orientationAt_rectangle_complex]
  · refine ⟨C, hC, ?_, ?_, neg_ne_zero.mpr one_ne_zero, ?_⟩
    · rw [hd]
      -- Evaluate the chosen basis on the canonical model before casting the real velocity.
      change (subtypeValIccTangentEquiv x (C 0) : ℂ) = -1
      exact_mod_cast hc
    · intro t ht
      exact (rectangle_face_normals_outward x (⊤ : Icc c d) ht).2.2.1
    · rw [orientation_outwardFirstBasis, map_orientationAt_rectangle_complex]

/-- The positive tangent of the signed vertical face orientation has the counterclockwise
velocity. Its outward-first frame has exactly the transported rectangle orientation, and its
normal leaves the rectangle. `left = false` is the right face; `left = true` is the left.
The assertions include both endpoints of each face. -/
theorem exists_vertical_face_outwardFirst {a b c d : ℝ} [Fact (a < b)] [Fact (c < d)]
    (left : Bool) (y : Icc c d) :
    let x : Icc a b := if left then ⊥ else ⊤
    let v : ℂ := if left then -Complex.I else Complex.I
    let o := if left then -Manifold.Orientation.interval c d
      else Manifold.Orientation.interval c d
    ∃ B : Module.Basis (Fin 1) ℝ (TangentSpace (𝓡∂ 1) y),
      B.orientation = o.orientationAt y ∧
      NormedSpace.fromTangentSpace (𝕜 := ℝ) (⟨x, y⟩ : ℂ)
        (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℂ) (fun t : Icc c d ↦ (⟨x, t⟩ : ℂ)) y (B 0)) = v ∧
      (∀ t : ℝ, 0 < t → (⟨x, y⟩ : ℂ) + t • (-Complex.I * v) ∉
        verticalRegion a b (fun _ ↦ c) (fun _ ↦ d)) ∧
      ∃ hv : v ≠ 0, (outwardFirstBasis v hv).orientation =
        Orientation.map (Fin 2)
          ((subtypeValRectangleTangentEquiv (x, y)).trans
            Complex.equivRealProdCLM.symm).toLinearEquiv
          (((Manifold.Orientation.interval a b).prod
            (Manifold.Orientation.interval c d)).orientationAt (x, y)) := by
  obtain ⟨B, C, hB, hC, hb, hc⟩ := exists_interval_tangent_bases y
  have hd (x : ℝ) (w : TangentSpace (𝓡∂ 1) y) :
      NormedSpace.fromTangentSpace (𝕜 := ℝ) (⟨x, y⟩ : ℂ)
        (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℂ) (fun t : Icc c d ↦ (⟨x, t⟩ : ℂ)) y w) =
          (subtypeValIccTangentEquiv y w : ℂ) * Complex.I := by
    have h := mfderiv_interval_affine_apply (x : ℂ)
      (Complex.I • Complex.ofRealCLM) y w
    have he : (fun t : Icc c d ↦ (x : ℂ) + (Complex.I • Complex.ofRealCLM) t) =
        (fun t : Icc c d ↦ (⟨x, t⟩ : ℂ)) := by
      funext t
      apply Complex.ext <;> simp
    -- Expose the affine map as a single function so its equality rewrites the dependent base point.
    change NormedSpace.fromTangentSpace (𝕜 := ℝ)
      ((fun t : Icc c d ↦ (x : ℂ) + (Complex.I • Complex.ofRealCLM) t) y)
      (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℂ) _ y w) = _ at h
    rw [he] at h
    -- Evaluate the scalar multiple of ofRealCLM before commuting the complex factors.
    change _ = Complex.I * (subtypeValIccTangentEquiv y w : ℂ) at h
    exact h.trans (mul_comm _ _)
  cases left <;> dsimp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
  · refine ⟨B, hB, ?_, ?_, Complex.I_ne_zero, ?_⟩
    · rw [hd]
      -- Read the basis in the fixed model before using its signed velocity.
      change (subtypeValIccTangentEquiv y (B 0) : ℂ) * Complex.I = Complex.I
      have hv : (subtypeValIccTangentEquiv y (B 0) : ℂ) = 1 := by exact_mod_cast hb
      rw [hv, one_mul]
    · intro t ht
      exact (rectangle_face_normals_outward (⊤ : Icc a b) y ht).2.1
    · rw [orientation_outwardFirstBasis, map_orientationAt_rectangle_complex]
  · refine ⟨C, hC, ?_, ?_, neg_ne_zero.mpr Complex.I_ne_zero, ?_⟩
    · rw [hd]
      -- Read the basis in the fixed model before using its signed velocity.
      change (subtypeValIccTangentEquiv y (C 0) : ℂ) * Complex.I = -Complex.I
      have hv : (subtypeValIccTangentEquiv y (C 0) : ℂ) = -1 := by exact_mod_cast hc
      rw [hv, neg_one_mul]
    · intro t ht
      exact (rectangle_face_normals_outward (⊥ : Icc a b) y ht).2.2.2
    · rw [orientation_outwardFirstBasis, map_orientationAt_rectangle_complex]

end TauCeti.Green

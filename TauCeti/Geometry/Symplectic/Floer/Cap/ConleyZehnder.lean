/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.ImInner.Maslov
public import TauCeti.Geometry.Symplectic.Floer.Cap.Chern
public import TauCeti.Geometry.Symplectic.Manifold.ConleyZehnder

/-!
# The recapping law for the Conley–Zehnder index of a capped loop

Let `γ` be a loop in a symplectic manifold `(M, σ)` based at `x`, for instance a contractible
one-periodic orbit of a Hamiltonian, and `Φ(t) : T_(γ 0) M ≃ T_(γ t) M` a continuous family of
linear maps preserving `σ`, such as the linearized flow along the orbit. The Conley–Zehnder index
of `Φ` along the capped loop `(γ, u)` is read in a symplectic frame of the tangent bundle along `γ`
that extends over the cap `u` (`TauCeti.SmoothTwoForm.frameConleyZehnderIndex`); it does not depend
on the frame over the cap (`TauCeti.SmoothTwoForm.frameConleyZehnderIndex_comp_eq`). This file
proves how it changes when the cap is changed: for two smooth based caps `u`, `u'` of `γ`, whose raw
caps differ by the sphere `D' -ᵥ D ∈ π₂(M, x)`,

`CZ(Φ; γ, u') = CZ(Φ; γ, u) - 2 c₁(D' -ᵥ D)`

(`TauCeti.Floer.IsSmoothBasedCap.frameConleyZehnderIndex_eq_sub_two_mul_firstChernHom`), with
`c₁` the first Chern number `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom` of an almost
complex structure tamed by `σ`. Equivalently the grading `μ = -CZ` of capped orbits increases by
`2 c₁(D' -ᵥ D)` when the cap `D` is replaced by `D'`, while the capped action increases by the area
`σ(D' -ᵥ D)`: this is the recapping law of the grading of capped Hamiltonian Floer theory.

The frames are taken complex linear for `J` over the caps, constant on the three edges of the
square where the caps sit at the base point, and symplectic along `γ`, where they are therefore
unitary. Such frames exist over every smooth based cap when `J` is compatible with `σ`
(`TauCeti.Floer.IsSmoothBasedCap.exists_unitary_frame_eq_on_edges`), and their restriction to the
loop is a symplectic frame along it
(`TauCeti.Floer.IsSmoothBasedCap.isSymplecticFrame_apply_zero`).

The proof combines three facts. Along `γ` the two frames differ by a loop `k` of unitary maps of
the model `G`. The index read in the second frame is the index read in the first plus twice the
Maslov index of `k⁻¹` (`TauCeti.SmoothTwoForm.frameConleyZehnderIndex_eq_add_maslovIndex`). The
Maslov index of a loop of unitary maps is minus the winding number of its complex determinant
(`TauCeti.SymplecticForm.maslovIndex_imInnerSymplecticForm_mul_two_pi_eq`), and the winding
number of the determinant of `k` is minus the first Chern number of the sphere glued from the two
caps, by clutching
(`TauCeti.Floer.IsSmoothBasedCap.firstChernHom_homotopyClass_vsub_homotopyClass_mul_two_pi_eq`).

## Main results

* `TauCeti.Floer.IsSmoothBasedCap.isSymplecticFrame_apply_zero`: a frame over a cap that is
  symplectic along the loop restricts to a symplectic frame along the loop.
* `TauCeti.Floer.IsSmoothBasedCap.frameConleyZehnderIndex_eq_sub_two_mul_firstChernHom`: the
  recapping law for the Conley–Zehnder index of a capped loop.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (the Conley–Zehnder index of a capped periodic orbit and
  its change under recapping).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Section 12.1 (the grading of capped periodic orbits) and Appendix C.1 (the first Chern number by
  clutching).
-/

public section

noncomputable section

open Bundle Set Module
open scoped Topology.Homotopy Manifold ContDiff InnerProductSpace

namespace TauCeti.Floer

open SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  {x : M} {γ : Ω M x} {u u' : ℝ × ℝ → M}

omit [FiniteDimensional ℝ E] in
/-- **The restriction of a frame over a cap to the loop.** Let `χ` be a frame of the tangent
bundle along a smooth based cap `u` of a loop `γ`, continuous into the tangent bundle, which
carries the symplectic form `Im ⟪·, ·⟫_ℂ` of the model `G` to `σ` along the edge `s = 0`, where
`u` runs along `γ`. Then `t ↦ χ (0, t)` is a symplectic frame along `γ`. -/
theorem IsSmoothBasedCap.isSymplecticFrame_apply_zero (hu : IsSmoothBasedCap I γ u)
    {χ : ∀ z, G ≃L[ℝ] TangentSpace I (u z)}
    (hχ : Continuous fun q : (ℝ × ℝ) × G ↦ (⟨u q.1, χ q.1 q.2⟩ : TangentBundle I M))
    (hσ : ∀ (t : unitInterval) v w, σ.eval₂ (u (0, t)) (χ (0, t) v) (χ (0, t) w) = (⟪v, w⟫_ℂ).im) :
    IsSymplecticFrame σ (imInnerSymplecticForm G) γ fun t ↦ χ (0, t) := by
  refine ⟨(hχ.comp ((continuous_const.prodMk (continuous_subtypeVal.comp continuous_fst)).prodMk
    continuous_snd)).congr fun q ↦ TotalSpace.ext (hu.apply_zero q.1) HEq.rfl, fun t v w ↦ ?_⟩
  rw [imInnerSymplecticForm_apply, ← hσ t v w, hu.apply_zero t]

variable [FiniteDimensional ℂ G] [Fact (finrank ℝ E = 2 * finrank ℂ G)] [T2Space M]
  [SigmaCompactSpace M] {J : SmoothAlmostComplexStructure I M}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℂ G] [Fact (finrank ℝ E = 2 * finrank ℂ G)]
  [T2Space M] [SigmaCompactSpace M] in
/-- Along the loop, a frame over a smooth based cap that is complex linear for `J` is complex
linear for `J` at the points of the loop. -/
private theorem IsSmoothBasedCap.apply_zero_I_smul (hu : IsSmoothBasedCap I γ u)
    {χ : ∀ z, G ≃L[ℝ] TangentSpace I (u z)} (hχJ : ∀ z v, χ z (Complex.I • v) = J (u z) (χ z v))
    (t : unitInterval) (v : G) : χ (0, t) (Complex.I • v) = J (γ t) (χ (0, t) v) := by
  have hJ (w : E) : J (u (0, t)) w = J (γ t) w := by rw [hu.apply_zero t]
  rw [hχJ]
  exact hJ _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℂ G] [Fact (finrank ℝ E = 2 * finrank ℂ G)]
  [T2Space M] [SigmaCompactSpace M] in
/-- Two frames along the same map that are complex linear for `J` differ by complex-linear maps
of the model: `φ'(y)⁻¹ ∘ φ(y)` commutes with multiplication by `i`. -/
private theorem trans_symm_I_smul {Y : Type*} {f : Y → M}
    {φ φ' : ∀ y, G ≃L[ℝ] TangentSpace I (f y)}
    (hφJ : ∀ y v, φ y (Complex.I • v) = J (f y) (φ y v))
    (hφJ' : ∀ y v, φ' y (Complex.I • v) = J (f y) (φ' y v)) (y : Y) (v : G) :
    (φ y).trans (φ' y).symm (Complex.I • v) = Complex.I • (φ y).trans (φ' y).symm v := by
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply, hφJ]
  apply (φ' y).injective
  rw [hφJ', ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ E = 2 * finrank ℂ G)] [T2Space M] [SigmaCompactSpace M] in
/-- A frame along the loop which agrees along the edge `s = 0` with a frame over a cap that is
constant on the edges `t = 0` and `t = 1` takes the same values at the two ends of the loop. -/
private theorem apply_zero_eq_apply_one_of_eq_on_edges {χ : ∀ z, G ≃L[ℝ] TangentSpace I (u z)}
    (hχ₀ : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      χ (s, t) v = χ (1, 0) v)
    {φ : ∀ t, G ≃L[ℝ] TangentSpace I (γ t)} (hφχ : ∀ t v, φ t v = χ (0, t) v) (v : G) :
    φ 0 v = φ 1 v := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  rw [hφχ, hφχ, hχ₀ 0 _ h0 (0 : unitInterval).property (Or.inr (Or.inl rfl)),
    hχ₀ 0 _ h0 (1 : unitInterval).property (Or.inr (Or.inr rfl))]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ E = 2 * finrank ℂ G)] [T2Space M] [SigmaCompactSpace M] in
/-- The change of frame between two frames along a loop is a loop when both frames take the same
values at the two ends of the loop. -/
private theorem trans_symm_zero_eq_trans_symm_one {φ φ' : ∀ t, G ≃L[ℝ] TangentSpace I (γ t)}
    (h : ∀ v, φ 0 v = φ 1 v) (h' : ∀ v, φ' 0 v = φ' 1 v) :
    (φ' 0).trans (φ 0).symm = (φ' 1).trans (φ 1).symm := by
  ext v
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply, h']
  apply (φ 0).injective
  -- `φ 0` and `φ 1` take values in the tangent spaces at `γ 0` and `γ 1`, equal only
  -- definitionally, so the inverses are cancelled by explicit terms rather than `rw`.
  exact ((φ 0).apply_symm_apply _).trans ((h _).trans ((φ 1).apply_symm_apply _)).symm

/-- **The recapping law, for frames along the loop.** The statement of
`TauCeti.Floer.IsSmoothBasedCap.frameConleyZehnderIndex_eq_sub_two_mul_firstChernHom`, for
symplectic frames `φ`, `φ'` along `γ` which agree with the frames `χ`, `χ'` over the caps along the
edge `s = 0`. -/
private theorem IsSmoothBasedCap.frameConleyZehnderIndex_eq_sub_two_mul_firstChernHom_aux
    (h : σ.IsNondegenerate) (hJ : σ.Tames J) (hu : IsSmoothBasedCap I γ u)
    (hu' : IsSmoothBasedCap I γ u')
    {χ : ∀ z, G ≃L[ℝ] TangentSpace I (u z)} {χ' : ∀ z, G ≃L[ℝ] TangentSpace I (u' z)}
    (hχ : Continuous fun q : (ℝ × ℝ) × G ↦ (⟨u q.1, χ q.1 q.2⟩ : TangentBundle I M))
    (hχ' : Continuous fun q : (ℝ × ℝ) × G ↦ (⟨u' q.1, χ' q.1 q.2⟩ : TangentBundle I M))
    (hχJ : ∀ z v, χ z (Complex.I • v) = J (u z) (χ z v))
    (hχJ' : ∀ z v, χ' z (Complex.I • v) = J (u' z) (χ' z v))
    (hχ₀ : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      χ (s, t) v = χ (1, 0) v)
    (hχ₀' : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      χ' (s, t) v = χ' (1, 0) v)
    {φ φ' : ∀ t, G ≃L[ℝ] TangentSpace I (γ t)}
    (hφ : IsSymplecticFrame σ (imInnerSymplecticForm G) γ φ)
    (hφ' : IsSymplecticFrame σ (imInnerSymplecticForm G) γ φ')
    (hφχ : ∀ t v, φ t v = χ (0, t) v) (hφχ' : ∀ t v, φ' t v = χ' (0, t) v)
    {Φ : ∀ t, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    frameConleyZehnderIndex (imInnerSymplecticForm G) hφ' hΦ hΦσ =
      frameConleyZehnderIndex (imInnerSymplecticForm G) hφ hΦ hΦσ -
        2 * (h.firstChernHom x (hu'.homotopyClass -ᵥ hu.homotopyClass) : ℝ) := by
  -- Along the loop both frames are complex linear for `J`.
  have hφJ (t : unitInterval) (v : G) : φ t (Complex.I • v) = J (γ t) (φ t v) := by
    rw [hφχ, hφχ]
    exact hu.apply_zero_I_smul hχJ t v
  have hφJ' (t : unitInterval) (v : G) : φ' t (Complex.I • v) = J (γ t) (φ' t v) := by
    rw [hφχ', hφχ']
    exact hu'.apply_zero_I_smul hχJ' t v
  -- So they differ by the complex-linear maps `k t = φ'(t)⁻¹ ∘ φ(t)`.
  let k : unitInterval → G ≃L[ℂ] G := fun t ↦
    ((φ t).trans (φ' t).symm).complexOfMapISmul (trans_symm_I_smul hφJ hφJ' t)
  have hk_apply (t : unitInterval) (v : G) : k t v = (φ' t).symm (φ t v) :=
    ContinuousLinearEquiv.complexOfMapISmul_apply _ _ v
  have hχk (t : unitInterval) (v : G) : χ (0, t) v = χ' (0, t) (k t v) := by
    rw [← hφχ, ← hφχ', hk_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hk : Continuous fun t ↦ (k t : G →L[ℂ] G) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ G G ℝ ℝ).isometry.isUniformInducing
      |>.isInducing.continuous_iff.2 ((continuous_trans_symm_of_continuous_frame hφ.continuous
        hφ'.continuous).congr fun t ↦ ContinuousLinearMap.ext fun v ↦ (hk_apply t v).symm)
  -- A continuous lift `θ` of the normalized determinant of `k` computes the first Chern number.
  obtain ⟨θ, hθ⟩ := Circle.exists_lift
    (⟨⟨fun t ↦ (k t).normalizedDet, hk.normalizedDet⟩, rfl, rfl⟩ : Path _ _)
  -- Applying the path built from `t ↦ (k t).normalizedDet` unfolds definitionally to that
  -- function, so `hθ` says that `θ` lifts the normalized determinant itself.
  have hθk (t : unitInterval) : Circle.exp (θ t) = (k t).normalizedDet := hθ t
  have hc := hu.firstChernHom_homotopyClass_vsub_homotopyClass_mul_two_pi_eq h hJ hu' hχ hχ' hχJ
    hχJ' hχ₀ hχ₀' hχk θ.continuous hθk
  -- The change of frame along the loop is a loop, since both frames are constant on the edges
  -- `t = 0` and `t = 1` of the caps.
  have hper := trans_symm_zero_eq_trans_symm_one (apply_zero_eq_apply_one_of_eq_on_edges hχ₀ hφχ)
    (apply_zero_eq_apply_one_of_eq_on_edges hχ₀' hφχ')
  -- The change of frame is the loop `k⁻¹` of unitary maps, whose Maslov index is the winding of
  -- `det k`, lifted by `θ`.
  have hm := SymplecticForm.maslovIndex_imInnerSymplecticForm_mul_two_pi_eq
    (transitionLoop hφ.continuous hφ'.continuous hper) (apply_transitionLoop_apply hφ hφ' hper)
    (k := fun t ↦ (k t).symm)
    (fun t v ↦ by
      simp only [k, transitionLoop_apply, ContinuousLinearEquiv.complexOfMapISmul_symm_apply,
        ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.symm_symm])
    (θ := fun t ↦ -θ t) θ.continuous.neg
    fun t ↦ by rw [Circle.exp_neg, hθk, ContinuousLinearEquiv.normalizedDet_symm]
  have hmc : (SymplecticForm.maslovIndex (imInnerSymplecticForm G)
      (transitionLoop hφ.continuous hφ'.continuous hper)
      (apply_transitionLoop_apply hφ hφ' hper) : ℝ) =
      -(h.firstChernHom x (hu'.homotopyClass -ᵥ hu.homotopyClass) : ℝ) :=
    mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) (by linarith)
  rw [frameConleyZehnderIndex_eq_add_maslovIndex hφ hφ' hper hΦ hΦσ, hmc]
  ring

/-- **The recapping law for the Conley–Zehnder index.** Let `u` and `u'` be smooth based caps of a
loop `γ` at `x`, in a manifold with a fiberwise nondegenerate two-form `σ` taming an almost complex
structure `J`. Let `χ` and `χ'` be real frames of the tangent bundle along `u` and `u'` with model a
complex inner product space `G`, continuous into the tangent bundle, complex linear for `J`,
constant on the three edges `s = 1`, `t = 0`, `t = 1` of the unit square where the caps are at
`x`, and carrying `Im ⟪·, ·⟫_ℂ` to `σ` along the loop. Then for every continuous family `Φ` of
linear maps along `γ` preserving `σ`, the Conley–Zehnder index of `Φ` read in `χ'` is its index
read in `χ` minus twice the first Chern number of the sphere `D' -ᵥ D` by which the raw caps of
`u'` and `u` differ. -/
theorem IsSmoothBasedCap.frameConleyZehnderIndex_eq_sub_two_mul_firstChernHom
    (h : σ.IsNondegenerate) (hJ : σ.Tames J) (hu : IsSmoothBasedCap I γ u)
    (hu' : IsSmoothBasedCap I γ u')
    {χ : ∀ z, G ≃L[ℝ] TangentSpace I (u z)} {χ' : ∀ z, G ≃L[ℝ] TangentSpace I (u' z)}
    (hχ : Continuous fun q : (ℝ × ℝ) × G ↦ (⟨u q.1, χ q.1 q.2⟩ : TangentBundle I M))
    (hχ' : Continuous fun q : (ℝ × ℝ) × G ↦ (⟨u' q.1, χ' q.1 q.2⟩ : TangentBundle I M))
    (hχJ : ∀ z v, χ z (Complex.I • v) = J (u z) (χ z v))
    (hχJ' : ∀ z v, χ' z (Complex.I • v) = J (u' z) (χ' z v))
    (hχ₀ : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      χ (s, t) v = χ (1, 0) v)
    (hχ₀' : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      χ' (s, t) v = χ' (1, 0) v)
    (hσ : ∀ (t : unitInterval) v w, σ.eval₂ (u (0, t)) (χ (0, t) v) (χ (0, t) w) = (⟪v, w⟫_ℂ).im)
    (hσ' : ∀ (t : unitInterval) v w,
      σ.eval₂ (u' (0, t)) (χ' (0, t) v) (χ' (0, t) w) = (⟪v, w⟫_ℂ).im)
    {Φ : ∀ t, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    frameConleyZehnderIndex (imInnerSymplecticForm G) (hu'.isSymplecticFrame_apply_zero hχ' hσ')
        hΦ hΦσ =
      frameConleyZehnderIndex (imInnerSymplecticForm G) (hu.isSymplecticFrame_apply_zero hχ hσ)
        hΦ hΦσ - 2 * (h.firstChernHom x (hu'.homotopyClass -ᵥ hu.homotopyClass) : ℝ) :=
  hu.frameConleyZehnderIndex_eq_sub_two_mul_firstChernHom_aux h hJ hu' hχ hχ' hχJ hχJ' hχ₀ hχ₀'
    _ _ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hΦ hΦσ

end TauCeti.Floer

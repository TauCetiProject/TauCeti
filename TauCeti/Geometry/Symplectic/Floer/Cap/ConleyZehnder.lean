/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.ImInner.Maslov
public import TauCeti.Geometry.Symplectic.Floer.Cap.Chern
public import TauCeti.Geometry.Symplectic.Manifold.ConleyZehnder
import TauCeti.Geometry.Symplectic.WittExtension

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
complex structure tamed by `σ`. Replacing the cap `D` by `D'` also lowers the capped action by the
area `σ(D' -ᵥ D)` (`TauCeti.Floer.RawCap.action_vadd`), so the index moves with the action: this is
the recapping law of the grading of capped Hamiltonian Floer theory, which in the sign convention
of `TauCeti.SymplecticForm.conleyZehnderIndex` is the index itself
(`TauCeti.Floer.SphericalCapClass.grading`).

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

## The index of a smooth cap

The index along a capped loop does not depend on the frame over the cap. Let `χ` and `χ'` be
symplectic frames of the tangent bundle along a smooth based cap `u`, with any symplectic models,
both constant on the three edges `s = 1`, `t = 0`, `t = 1` of the unit square. Their change of
frame is then defined on the whole square and is a loop on each segment `s = const`, so it is a
homotopy through loops from the change of frame along `γ` to a constant loop, which has Maslov
index zero (`TauCeti.SymplecticForm.maslovIndex_eq_of_homotopy`). Hence the two frames give the
same index along `γ` (`TauCeti.Floer.IsSmoothBasedCap.frameConleyZehnderIndex_loop_eq`).
Consequently the **Conley–Zehnder index of a smooth cap**,
`TauCeti.Floer.IsSmoothBasedCap.conleyZehnderIndex`, is well defined for a fiberwise nondegenerate
two-form, as the index read in any such frame
(`TauCeti.Floer.IsSmoothBasedCap.conleyZehnderIndex_eq`), and the recapping law holds for it
without reference to frames or to an almost complex structure
(`TauCeti.Floer.IsSmoothBasedCap.conleyZehnderIndex_eq_sub_two_mul_firstChernHom`). When `Φ`
starts at the identity and ends at a map `P` without the eigenvalue `1`, as the linearized flow
along a nondegenerate periodic orbit, the index of a smooth cap is an integer
(`TauCeti.Floer.IsSmoothBasedCap.exists_int_conleyZehnderIndex_eq`), with parity given by
`sign det (1 - P)`
(`TauCeti.Floer.IsSmoothBasedCap.exists_int_conleyZehnderIndex_eq_and_negOnePow_eq`).
Its descent to raw caps and cap classes is in `TauCeti/Geometry/Symplectic/Floer/Cap/Grading.lean`.

## Main definitions

* `TauCeti.Floer.IsSmoothBasedCap.conleyZehnderIndex`: the Conley–Zehnder index of a capped loop
  with a smooth based cap.

## Main results

* `TauCeti.Floer.IsSmoothBasedCap.isSymplecticFrame_apply_zero`: a frame over a cap that is
  symplectic along the loop restricts to a symplectic frame along the loop.
* `TauCeti.Floer.IsSmoothBasedCap.frameConleyZehnderIndex_eq_sub_two_mul_firstChernHom`: the
  recapping law for the Conley–Zehnder index of a capped loop.
* `TauCeti.Floer.IsSmoothBasedCap.frameConleyZehnderIndex_loop_eq`: symplectic frames over a cap
  that are constant on its three other edges give the same index along the loop.
* `TauCeti.Floer.IsSmoothBasedCap.conleyZehnderIndex_eq`,
  `TauCeti.Floer.IsSmoothBasedCap.conleyZehnderIndex_eq_sub_two_mul_firstChernHom`: the index of a
  smooth cap in any such frame, and its recapping law.
* `TauCeti.Floer.IsSmoothBasedCap.conleyZehnderIndex_const`: along the constant cap of a loop that
  stays at its base point `x`, the index is the index of `Φ` on the single tangent space `T_x M`.
* `TauCeti.Floer.IsSmoothBasedCap.exists_int_conleyZehnderIndex_eq`: the index along a
  nondegenerate orbit is an integer.
* `TauCeti.Floer.IsSmoothBasedCap.exists_int_conleyZehnderIndex_eq_and_negOnePow_eq`: its parity
  is the sign of `det (1 - P)` for the end value `P` of `Φ`.

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
  {W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W']
  [NormedSpace ℝ W'] {ω₀ : SymplecticForm W} {ω' : SymplecticForm W'}
  {x : M} {γ : Ω M x} {u u' : ℝ × ℝ → M}

omit [FiniteDimensional ℝ E] in
/-- **The restriction of a frame over a cap to the loop.** Let `χ` be a frame of the tangent
bundle along a smooth based cap `u` of a loop `γ`, continuous into the tangent bundle, which
carries the symplectic form `ω₀` of the model `W` to `σ` along the edge `s = 0`, where `u` runs
along `γ`. Then `t ↦ χ (0, t)` is a symplectic frame along `γ`. -/
theorem IsSmoothBasedCap.isSymplecticFrame_apply_zero (hu : IsSmoothBasedCap I γ u)
    {χ : ∀ z, W ≃L[ℝ] TangentSpace I (u z)}
    (hχ : Continuous fun q : (ℝ × ℝ) × W ↦ (⟨u q.1, χ q.1 q.2⟩ : TangentBundle I M))
    (hσ : ∀ (t : unitInterval) v w, σ.eval₂ (u (0, t)) (χ (0, t) v) (χ (0, t) w) = ω₀ v w) :
    IsSymplecticFrame σ ω₀ γ fun t ↦ χ (0, t) := by
  refine ⟨(hχ.comp ((continuous_const.prodMk (continuous_subtypeVal.comp continuous_fst)).prodMk
    continuous_snd)).congr fun q ↦ TotalSpace.ext (hu.apply_zero q.1) HEq.rfl, fun t v w ↦ ?_⟩
  rw [← hσ t v w, hu.apply_zero t]

omit [FiniteDimensional ℝ E] in
/-- A symplectic frame of the tangent bundle along a smooth based cap `u` of `γ` restricts, along
the edge `s = 0` where `u` runs along `γ`, to a symplectic frame along `γ`. -/
theorem IsSmoothBasedCap.isSymplecticFrame_apply_zero_of_isSymplecticFrame
    (hu : IsSmoothBasedCap I γ u) {χ : ∀ z, W ≃L[ℝ] TangentSpace I (u z)}
    (hχ : IsSymplecticFrame σ ω₀ u χ) : IsSymplecticFrame σ ω₀ γ fun t ↦ χ (0, t) :=
  hu.isSymplecticFrame_apply_zero hχ.continuous fun t ↦ hχ.apply_apply (0, t)

omit [FiniteDimensional ℝ E] in
/-- A frame along `f`, continuous into the tangent bundle, which carries `Im ⟪·, ·⟫_ℂ` on `G` to
`σ` is a symplectic frame with model `(G, Im ⟪·, ·⟫_ℂ)`. -/
private theorem isSymplecticFrame_imInnerSymplecticForm {Y : Type*} [TopologicalSpace Y]
    {f : Y → M} {χ : ∀ y, G ≃L[ℝ] TangentSpace I (f y)}
    (hχ : Continuous fun q : Y × G ↦ (⟨f q.1, χ q.1 q.2⟩ : TangentBundle I M))
    (hσ : ∀ y v w, σ.eval₂ (f y) (χ y v) (χ y w) = (⟪v, w⟫_ℂ).im) :
    IsSymplecticFrame σ (imInnerSymplecticForm G) f χ :=
  ⟨hχ, fun y v w ↦ by rw [hσ, imInnerSymplecticForm_apply]⟩

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

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ E = 2 * finrank ℂ G)] [T2Space M] [SigmaCompactSpace M] in
/-- A frame along the loop which agrees along the edge `s = 0` with a frame over a cap that is
constant on the edges `t = 0` and `t = 1` takes the same values at the two ends of the loop. -/
private theorem apply_zero_eq_apply_one_of_eq_on_edges {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] {χ : ∀ z, K ≃L[ℝ] TangentSpace I (u z)}
    (hχ₀ : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      χ (s, t) v = χ (1, 0) v)
    {φ : ∀ t, K ≃L[ℝ] TangentSpace I (γ t)} (hφχ : ∀ t v, φ t v = χ (0, t) v) (v : K) :
    φ 0 v = φ 1 v := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  rw [hφχ, hφχ, hχ₀ 0 _ h0 (0 : unitInterval).property (Or.inr (Or.inl rfl)),
    hχ₀ 0 _ h0 (1 : unitInterval).property (Or.inr (Or.inr rfl))]

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
    ((φ t).trans (φ' t).symm).complexOfMapISmul
      (SmoothAlmostComplexStructure.trans_symm_I_smul (hφJ t) (hφJ' t))
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
    (hσ : ∀ (t : unitInterval) v w,
      σ.eval₂ (u (0, t)) (χ (0, t) v) (χ (0, t) w) = imInnerSymplecticForm G v w)
    (hσ' : ∀ (t : unitInterval) v w,
      σ.eval₂ (u' (0, t)) (χ' (0, t) v) (χ' (0, t) w) = imInnerSymplecticForm G v w)
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

/-! ### The Conley–Zehnder index of a smooth based cap -/

section SmoothCap

variable [FiniteDimensional ℝ W] [FiniteDimensional ℝ W']

omit [T2Space M] [SigmaCompactSpace M] in
/-- Two symplectic frames with the same model along a map `u` of the plane, both constant on the
three edges `s = 1`, `t = 0`, `t = 1` of the unit square, give the same Conley–Zehnder index along
`γ`, read in frames `φ`, `φ'` along `γ` that agree with them on the edge `s = 0`: their change of
frame along `γ` is contracted through loops over the square. -/
private theorem frameConleyZehnderIndex_eq_of_eq_on_edges_aux
    {χ χ' : ∀ z, W ≃L[ℝ] TangentSpace I (u z)}
    (hχ : IsSymplecticFrame σ ω₀ u χ) (hχ' : IsSymplecticFrame σ ω₀ u χ')
    (hχ₀ : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      χ (s, t) v = χ (1, 0) v)
    (hχ₀' : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      χ' (s, t) v = χ' (1, 0) v)
    {φ φ' : ∀ t, W ≃L[ℝ] TangentSpace I (γ t)} (hφ : IsSymplecticFrame σ ω₀ γ φ)
    (hφ' : IsSymplecticFrame σ ω₀ γ φ') (hφχ : ∀ t v, φ t v = χ (0, t) v)
    (hφχ' : ∀ t v, φ' t v = χ' (0, t) v)
    {Φ : ∀ t, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    frameConleyZehnderIndex ω₀ hφ' hΦ hΦσ = frameConleyZehnderIndex ω₀ hφ hΦ hΦσ := by
  -- On the edges both frames take their value at the corner `(1, 0)`.
  have hedge (s t : unitInterval) (hst : (s : ℝ) = 1 ∨ (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
      (χ' ((s : ℝ), (t : ℝ))).trans (χ ((s : ℝ), (t : ℝ))).symm =
        (χ' (1, 0)).trans (χ (1, 0)).symm := by
    ext v
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
      hχ₀' _ _ s.property t.property hst]
    apply (χ ((s : ℝ), (t : ℝ))).injective
    -- The tangent spaces at `u (s, t)` and `u (1, 0)` are both the model space, so the inverses
    -- are cancelled by explicit terms rather than `rw`.
    exact ((χ _).apply_symm_apply _).trans
      ((hχ₀ _ _ s.property t.property hst _).trans ((χ (1, 0)).apply_symm_apply _)).symm
  have hper := trans_symm_zero_eq_trans_symm_one (apply_zero_eq_apply_one_of_eq_on_edges hχ₀ hφχ)
    (apply_zero_eq_apply_one_of_eq_on_edges hχ₀' hφχ')
  rw [frameConleyZehnderIndex_eq_add_maslovIndex hφ hφ' hper]
  suffices hm : ω₀.maslovIndex (transitionLoop hφ.continuous hφ'.continuous hper)
      (apply_transitionLoop_apply hφ hφ' hper) = 0 by
    rw [hm, Int.cast_zero, mul_zero, add_zero]
  -- The change of frame over the square is a homotopy through loops from the change of frame
  -- along `γ` to the constant loop at the corner `(1, 0)`.
  let F : C(unitInterval × unitInterval, W →L[ℝ] W) :=
    ⟨fun p ↦ ((χ' ((p.1 : ℝ), (p.2 : ℝ))).trans (χ ((p.1 : ℝ), (p.2 : ℝ))).symm : W ≃L[ℝ] W),
      (continuous_trans_symm_of_continuous_frame hχ'.continuous hχ.continuous).comp
        ((continuous_subtypeVal.comp continuous_fst).prodMk
          (continuous_subtypeVal.comp continuous_snd))⟩
  have hF (p : unitInterval × unitInterval) (v w : W) : ω₀ (F p v) (F p w) = ω₀ v w :=
    hχ'.apply_trans_symm_apply hχ _ v w
  -- Along the edge `s = 0` it is the change of frame from `φ` to `φ'`.
  have hF₀ (t : unitInterval) : F (0, t) = transitionLoop hφ.continuous hφ'.continuous hper t := by
    ext v
    rw [transitionLoop_apply, hφχ']
    apply (φ t).injective
    exact ((hφχ t _).trans ((χ (0, t)).apply_symm_apply _)).trans ((φ t).apply_symm_apply _).symm
  exact (ω₀.maslovIndex_eq_of_homotopy _
    (Path.refl (((χ' (1, 0)).trans (χ (1, 0)).symm : W ≃L[ℝ] W) : W →L[ℝ] W)) F hF hF₀
    (fun t ↦ congrArg (fun e : W ≃L[ℝ] W ↦ (e : W →L[ℝ] W)) (hedge 1 t (Or.inl rfl)))
    (fun s ↦ congrArg (fun e : W ≃L[ℝ] W ↦ (e : W →L[ℝ] W))
      ((hedge s 0 (Or.inr (Or.inl rfl))).trans (hedge s 1 (Or.inr (Or.inr rfl))).symm))).trans
    (ω₀.maslovIndex_refl _ _)

omit [T2Space M] [SigmaCompactSpace M] in
/-- **The index over a cap does not depend on the frame.** Let `χ` and `χ'` be symplectic frames
of the tangent bundle along a smooth based cap `u` of `γ`, with any two symplectic models
`(W, ω₀)` and `(W', ω')`, each constant on the three edges `s = 1`, `t = 0`, `t = 1` of the unit
square, where `u` is at the base point. Then for every continuous family `Φ` of linear maps along
`γ` preserving `σ`, the Conley–Zehnder indices of `Φ` read in the restrictions of `χ` and `χ'` to
`γ` agree. -/
theorem IsSmoothBasedCap.frameConleyZehnderIndex_loop_eq (hu : IsSmoothBasedCap I γ u)
    {χ : ∀ z, W ≃L[ℝ] TangentSpace I (u z)} {χ' : ∀ z, W' ≃L[ℝ] TangentSpace I (u z)}
    (hχ : IsSymplecticFrame σ ω₀ u χ) (hχ' : IsSymplecticFrame σ ω' u χ')
    (hχ₀ : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      χ (s, t) v = χ (1, 0) v)
    (hχ₀' : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      χ' (s, t) v = χ' (1, 0) v)
    {Φ : ∀ t, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    frameConleyZehnderIndex ω' (hu.isSymplecticFrame_apply_zero_of_isSymplecticFrame hχ') hΦ
        hΦσ =
      frameConleyZehnderIndex ω₀ (hu.isSymplecticFrame_apply_zero_of_isSymplecticFrame hχ) hΦ
        hΦσ := by
  -- Move the model of `χ'` to `(W, ω₀)` by a linear symplectomorphism `e : W ≃ W'`.
  have hdim : finrank ℝ W = finrank ℝ W' :=
    ((χ (0, 0)).toLinearEquiv.finrank_eq).trans (χ' (0, 0)).toLinearEquiv.finrank_eq.symm
  obtain ⟨e, he⟩ := SymplecticForm.exists_isSymplectomorphism ω₀ ω' hdim
  have he' : ∀ v w, ω' (e.toContinuousLinearEquiv v) (e.toContinuousLinearEquiv w) = ω₀ v w :=
    he.apply
  rw [← frameConleyZehnderIndex_trans (hu.isSymplecticFrame_apply_zero_of_isSymplecticFrame hχ')
    e.toContinuousLinearEquiv he']
  have hχ'' := hχ'.trans e.toContinuousLinearEquiv he'
  exact frameConleyZehnderIndex_eq_of_eq_on_edges_aux hχ hχ'' hχ₀
    (fun s t hs ht hst v ↦ hχ₀' s t hs ht hst (e v))
    (hu.isSymplecticFrame_apply_zero_of_isSymplecticFrame hχ)
    (hu.isSymplecticFrame_apply_zero_of_isSymplecticFrame hχ'') (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hΦ
    hΦσ

/-- Along every smooth based cap `u` of a loop at `x`, for a fiberwise nondegenerate two-form `σ`,
there is a symplectic frame of the tangent bundle with model `(G, Im ⟪·, ·⟫_ℂ)`, for any complex
inner product space `G` of the right dimension, that is constant on the three edges `s = 1`,
`t = 0`, `t = 1` of the unit square: a unitary frame for an almost complex structure compatible
with `σ` (`TauCeti.Floer.IsSmoothBasedCap.exists_unitary_frame_eq_on_edges`). -/
private theorem IsSmoothBasedCap.exists_isSymplecticFrame_eq_on_edges (h : σ.IsNondegenerate)
    (hu : IsSmoothBasedCap I γ u) :
    ∃ χ : ∀ z, G ≃L[ℝ] TangentSpace I (u z), IsSymplecticFrame σ (imInnerSymplecticForm G) u χ ∧
      ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
        χ (s, t) v = χ (1, 0) v := by
  obtain ⟨χ, hχ, -, hσ, hedge⟩ := hu.exists_unitary_frame_eq_on_edges (K := G)
    h.exists_compatible.choose_spec
  exact ⟨χ, isSymplecticFrame_imInnerSymplecticForm hχ hσ, hedge⟩

/-- The **Conley–Zehnder index of a capped loop with a smooth cap.** For a smooth based cap `u` of
a loop `γ` in a manifold with a fiberwise nondegenerate two-form `σ`, and a continuous family `Φ` of
linear maps along `γ` preserving `σ`, such as the linearized flow along a periodic orbit, this is
the Conley–Zehnder index of `Φ` read in a symplectic frame along `γ` that extends over `u` and is
constant on the three edges `s = 1`, `t = 0`, `t = 1` of the unit square. It does not depend on
that frame (`TauCeti.Floer.IsSmoothBasedCap.conleyZehnderIndex_eq`). -/
def IsSmoothBasedCap.conleyZehnderIndex (h : σ.IsNondegenerate) (hu : IsSmoothBasedCap I γ u)
    {Φ : ∀ t, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) : ℝ :=
  -- The frame is read with model `ℂⁿ`, `2 n = dim M`.
  haveI : Fact _ := ⟨h.two_mul_finrank_euclideanSpace x⟩
  frameConleyZehnderIndex _
    (hu.isSymplecticFrame_apply_zero_of_isSymplecticFrame (hu.exists_isSymplecticFrame_eq_on_edges
      (G := EuclideanSpace ℂ (Fin (finrank ℝ E / 2))) h).choose_spec.1) hΦ hΦσ

/-- **The index of a smooth cap in any frame.** The Conley–Zehnder index of a capped loop with a
smooth based cap `u` is the Conley–Zehnder index of `Φ` read in any symplectic frame along `u`,
with any symplectic model `(W, ω₀)`, that is constant on the three edges `s = 1`, `t = 0`, `t = 1`
of the unit square, restricted to `γ`. -/
theorem IsSmoothBasedCap.conleyZehnderIndex_eq (h : σ.IsNondegenerate)
    (hu : IsSmoothBasedCap I γ u) {χ : ∀ z, W ≃L[ℝ] TangentSpace I (u z)}
    (hχ : IsSymplecticFrame σ ω₀ u χ)
    (hχ₀ : ∀ s t : ℝ, s ∈ Icc 0 1 → t ∈ Icc 0 1 → (s = 1 ∨ t = 0 ∨ t = 1) → ∀ v,
      χ (s, t) v = χ (1, 0) v)
    {Φ : ∀ t, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    hu.conleyZehnderIndex h hΦ hΦσ =
      frameConleyZehnderIndex ω₀ (hu.isSymplecticFrame_apply_zero_of_isSymplecticFrame hχ) hΦ
        hΦσ :=
  have : Fact _ := ⟨h.two_mul_finrank_euclideanSpace x⟩
  have hχ' := (hu.exists_isSymplecticFrame_eq_on_edges
    (G := EuclideanSpace ℂ (Fin (finrank ℝ E / 2))) h).choose_spec
  hu.frameConleyZehnderIndex_loop_eq hχ hχ'.1 hχ₀ hχ'.2 hΦ hΦσ

/-- **The index of a constant cap.** Let `u` be the constant cap of a loop `γ` that stays at its
base point `x`, such as the loop of a constant periodic orbit. Along it the tangent bundle is framed
by the identity of `T_x M`, so the Conley–Zehnder index of `Φ` along `(γ, u)` is the
Conley–Zehnder index of the path `t ↦ Φ(t)` of linear symplectic maps of the single symplectic
vector space `(T_x M, σ_x)`, read on the model space `E` of `T_x M` as any path `Ψ` with
`Ψ(t) = Φ(t)`. -/
theorem IsSmoothBasedCap.conleyZehnderIndex_const (h : σ.IsNondegenerate)
    (hu : IsSmoothBasedCap I γ fun _ ↦ x)
    {Φ : ∀ t, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) {A B : E →L[ℝ] E}
    (Ψ : Path A B)
    (hΨ : ∀ t v w, h.symplecticFormAt x (Ψ t v) (Ψ t w) = h.symplecticFormAt x v w)
    (hΨΦ : ∀ t v, Ψ t v = Φ t v) :
    hu.conleyZehnderIndex h hΦ hΦσ =
      SymplecticForm.conleyZehnderIndex (V := E) (h.symplecticFormAt x) Ψ hΨ := by
  -- The identity of `T_x M` is a symplectic frame along the constant cap, constant on its edges.
  have hχ : IsSymplecticFrame σ (W := E) (h.symplecticFormAt x) (fun _ : ℝ × ℝ ↦ x)
      fun _ ↦ ContinuousLinearEquiv.refl ℝ E :=
    ⟨(FiberBundle.continuous_totalSpaceMk E (TangentSpace I) x).comp continuous_snd,
      fun _ v w ↦ (h.symplecticFormAt_apply x v w).symm⟩
  -- Read in the identity frame, the path is `Φ` itself. The model `E` and `T_x M` are the same
  -- type only up to unfolding `TangentSpace`, so the steps are composed as terms.
  exact (hu.conleyZehnderIndex_eq h hχ (fun _ _ _ _ _ _ ↦ rfl) hΦ hΦσ).trans
    ((frameConleyZehnderIndex_def _ _ _).trans
      (SymplecticForm.conleyZehnderIndex_congr _ _ _ _ fun t ↦
        ContinuousLinearMap.ext fun v ↦ (framePath_apply _ _ t v).trans (hΨΦ t v).symm))

/-- **The recapping law for smooth caps.** For two smooth based caps `u` and `u'` of a loop `γ`,
the Conley–Zehnder index of `Φ` along `(γ, u')` is its index along `(γ, u)` minus twice the first
Chern number of the sphere `D' -ᵥ D` by which their raw caps differ. -/
theorem IsSmoothBasedCap.conleyZehnderIndex_eq_sub_two_mul_firstChernHom (h : σ.IsNondegenerate)
    (hu : IsSmoothBasedCap I γ u) (hu' : IsSmoothBasedCap I γ u')
    {Φ : ∀ t, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    hu'.conleyZehnderIndex h hΦ hΦσ =
      hu.conleyZehnderIndex h hΦ hΦσ -
        2 * (h.firstChernHom x (hu'.homotopyClass -ᵥ hu.homotopyClass) : ℝ) := by
  let G₀ := EuclideanSpace ℂ (Fin (finrank ℝ E / 2))
  have : Fact (finrank ℝ E = 2 * finrank ℂ G₀) := ⟨h.two_mul_finrank_euclideanSpace x⟩
  -- Read both indices in unitary frames over the caps for one compatible almost complex structure.
  have hJ := h.exists_compatible.choose_spec
  obtain ⟨χ, hχc, hχJ, hσ, hχ₀⟩ := hu.exists_unitary_frame_eq_on_edges (K := G₀) hJ
  obtain ⟨χ', hχc', hχJ', hσ', hχ₀'⟩ := hu'.exists_unitary_frame_eq_on_edges (K := G₀) hJ
  have hχ : IsSymplecticFrame σ (imInnerSymplecticForm G₀) u χ :=
    isSymplecticFrame_imInnerSymplecticForm hχc hσ
  have hχ' : IsSymplecticFrame σ (imInnerSymplecticForm G₀) u' χ' :=
    isSymplecticFrame_imInnerSymplecticForm hχc' hσ'
  rw [hu.conleyZehnderIndex_eq h hχ hχ₀, hu'.conleyZehnderIndex_eq h hχ' hχ₀']
  exact hu.frameConleyZehnderIndex_eq_sub_two_mul_firstChernHom h hJ.tames hu' hχc hχc' hχJ hχJ'
    hχ₀ hχ₀' (fun t ↦ hχ.apply_apply (0, t)) (fun t ↦ hχ'.apply_apply (0, t)) hΦ hΦσ

/-- **The index of a smooth cap of a nondegenerate orbit is an integer.** If the family `Φ` starts
at the identity and its endpoint `Φ(1)` fixes no nonzero vector, as the linearized flow along a
nondegenerate periodic orbit does, the Conley–Zehnder index of `Φ` along the capped loop `(γ, u)` is
an integer. -/
theorem IsSmoothBasedCap.exists_int_conleyZehnderIndex_eq (h : σ.IsNondegenerate)
    (hu : IsSmoothBasedCap I γ u) {Φ : ∀ t, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) (hΦ₀ : ∀ v, Φ 0 v = v)
    (hΦ₁ : ∀ v, Φ 1 v = v → v = 0) : ∃ k : ℤ, hu.conleyZehnderIndex h hΦ hΦσ = k := by
  have : Fact _ := ⟨h.two_mul_finrank_euclideanSpace x⟩
  obtain ⟨χ, hχ, hχ₀⟩ := hu.exists_isSymplecticFrame_eq_on_edges
    (G := EuclideanSpace ℂ (Fin (finrank ℝ E / 2))) h
  -- A frame over the cap that is constant on its three other edges is periodic along `γ`.
  rw [hu.conleyZehnderIndex_eq h hχ hχ₀]
  exact exists_int_frameConleyZehnderIndex_eq _
    (apply_zero_eq_apply_one_of_eq_on_edges hχ₀ fun _ _ ↦ rfl) hΦ hΦσ hΦ₀ hΦ₁

/-- **The parity of the index of a smooth cap.** Let `u` be a smooth based cap of a loop `γ` in a
manifold of dimension `2 n` with a fiberwise nondegenerate two-form `σ`, and let `Φ` be a
continuous family of linear maps along `γ` preserving `σ`, starting at the identity, whose end
value is an endomorphism `P` of `T_(γ 0) M` without the eigenvalue `1`, such as the linearized
flow along a nondegenerate periodic orbit. Then the Conley–Zehnder index of `Φ` along the capped
loop `(γ, u)` is an integer `k` with `(-1) ^ (n - k) = sign det (1 - P)`. -/
theorem IsSmoothBasedCap.exists_int_conleyZehnderIndex_eq_and_negOnePow_eq
    (h : σ.IsNondegenerate) (hu : IsSmoothBasedCap I γ u)
    {Φ : ∀ t, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) (hΦ₀ : ∀ v, Φ 0 v = v)
    {P : TangentSpace I (γ 0) →ₗ[ℝ] TangentSpace I (γ 0)} (hP : ∀ v, Φ 1 v = P v)
    (hPdet : LinearMap.det (1 - P) ≠ 0) :
    ∃ k : ℤ, hu.conleyZehnderIndex h hΦ hΦσ = k ∧
      ((((finrank ℝ E / 2 : ℕ) : ℤ) - k).negOnePow : ℤ) =
        SignType.sign (LinearMap.det (1 - P)) := by
  have : Fact _ := ⟨h.two_mul_finrank_euclideanSpace x⟩
  obtain ⟨χ, hχ, hχ₀⟩ := hu.exists_isSymplecticFrame_eq_on_edges
    (G := EuclideanSpace ℂ (Fin (finrank ℝ E / 2))) h
  -- A frame over the cap that is constant on its three other edges is periodic along `γ`.
  rw [hu.conleyZehnderIndex_eq h hχ hχ₀]
  exact exists_int_frameConleyZehnderIndex_eq_and_negOnePow_eq _
    (apply_zero_eq_apply_one_of_eq_on_edges hχ₀ fun _ _ ↦ rfl) hΦ hΦσ hΦ₀ hP hPdet

end SmoothCap

end TauCeti.Floer

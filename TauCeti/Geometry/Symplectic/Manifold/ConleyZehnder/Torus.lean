/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.ImInner.Maslov
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chern
public import TauCeti.Geometry.Symplectic.Manifold.ConleyZehnder.Cylinder
public import TauCeti.Topology.VectorBundle.Complex.TorusClutching
import TauCeti.Geometry.Symplectic.Floer.Cap.Chern
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.UnitaryFrame
import TauCeti.Geometry.Symplectic.WittExtension

/-!
# The Conley–Zehnder index through two cylinders and the torus they bound

Let `(M, σ)` be a symplectic manifold, `γ₀` a reference loop with a periodic symplectic frame `φ₀`
of the tangent bundle along it, and `γ` a loop, for instance a one-periodic orbit of a
Hamiltonian in the free homotopy class of `γ₀`. A smooth cylinder `u` from `γ` to `γ₀` grades a
continuous family `Φ` of linear symplectic maps along `γ`, such as the linearized flow along the
orbit, by the Conley–Zehnder index of `Φ` read in a frame of the cylinder extending `φ₀`
(`TauCeti.IsSmoothCylinder.conleyZehnderIndex`). Two cylinders `u` and `u'` from `γ` to `γ₀` glue,
`u` run backwards followed by `u'`, to a map of the torus

`w = rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'`,

which runs along `γ₀` on the edges `s = 0` and `s = 1` of the unit square and along `γ` on its
middle line `s = 1/2`. This file proves the **cylinder-change law**
(`TauCeti.IsSmoothCylinder.conleyZehnderIndex_eq_sub_two_mul_torusClutchingNumber`):

`CZ(Φ; u') = CZ(Φ; u) - 2 c₁(w)`,

where `c₁(w)` is the first Chern number of the tangent bundle on the torus `w`, its clutching number
(`TauCeti.torusClutchingNumber`) for any almost complex structure tamed by `σ`. So when the first
Chern number vanishes on tori, the Chern half of symplectic atoroidality, the index does not depend
on the cylinder (`TauCeti.IsSmoothCylinder.conleyZehnderIndex_eq_of_torusClutchingNumber_eq_zero`):
for a fixed reference frame, the grading of a one-periodic orbit through a cylinder to `γ₀` is
independent of the cylinder.

The proof follows the recapping law for capped loops
(`TauCeti.Floer.IsSmoothBasedCap.conleyZehnderIndex_eq_sub_two_mul_firstChernHom`), with the
sphere glued from two caps replaced by the torus glued from two cylinders.

* **Clutching** (`TauCeti.torusClutchingNumber_mul_two_pi_eq_of_rectangleTrans`). Let `φ` and `φ'`
  be continuous frames of a complex vector bundle along `u` and `u'`, periodic on the loops of the
  cylinders and equal along `γ₀`, which differ along `γ` by a loop `k` of automorphisms of the
  model, `φ (0, t) = φ' (0, t) ∘ k t`. They glue to a frame `Ψ` over the square of `w` with
  `Ψ (1, t) = Ψ (0, t) ∘ k t`, so the clutching number of `w` is `-wind(det k)`
  (`TauCeti.torusClutchingNumber_mul_two_pi_eq_of_frame`).
* **Unitary frames.** For a compatible almost complex structure `J`, the tangent bundle has a
  periodic unitary frame along `γ₀`
  (`TauCeti.SmoothTwoForm.Compatible.exists_continuous_unitary_frame_loop`), and every smooth
  cylinder has a unitary frame extending it
  (`TauCeti.IsSmoothCylinder.exists_unitary_isCylinderFrame`). Along `γ` two such frames differ
  by a loop `k` of unitary maps, and the index read in them changes by twice the winding of
  `det k` (`TauCeti.SmoothTwoForm.frameConleyZehnderIndex_mul_two_pi_eq_of_complex`).
* **Reference frames.** Changing the reference frame shifts the indices through `u` and `u'` by the
  same amount (`TauCeti.IsSmoothCylinder.conleyZehnderIndex_eq_add_maslovIndex`), so the law for a
  unitary reference frame gives it for every reference frame.

## Main results

* `TauCeti.torusClutchingNumber_mul_two_pi_eq_of_rectangleTrans`: the clutching number of the torus
  glued from two cylinders is minus the winding of the change of frame along their common loop.
* `TauCeti.IsSmoothCylinder.exists_unitary_isCylinderFrame`: unitary frames of a cylinder extending
  a periodic unitary reference frame.
* `TauCeti.IsSmoothCylinder.conleyZehnderIndex_eq_sub_two_mul_torusClutchingNumber`: the
  cylinder-change law.
* `TauCeti.IsSmoothCylinder.conleyZehnderIndex_eq_of_torusClutchingNumber_eq_zero`: under the
  Chern condition on tori the index does not depend on the cylinder.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (the Conley–Zehnder index in a trivialization along a
  periodic orbit and its change with the trivialization).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2 (the grading of noncontractible
  orbits through reference loops, which needs `f^*(2c₁) = 0` on tori).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the first Chern number of a bundle over a closed surface by clutching).
-/

public section

noncomputable section

open Bundle Set Module
open scoped Topology.Homotopy Manifold ContDiff

namespace TauCeti

/-! ### The clutching number of the torus glued from two cylinders -/

section Clutching

variable {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)]

/-- **The clutching number of the torus glued from two cylinders.** Let `u` and `u'` be maps of the
plane that agree on the line `s = 0`, and let `w` be the map of the unit square
`rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'`, `u` run backwards followed by `u'`. Let `φ`
and `φ'` be continuous frames of `E` along `u` and `u'` that are periodic on the loops of the
cylinders, `φ (s, 1) = φ (s, 0)` for `s ∈ [0, 1]`, and agree along the edge `s = 1`,
`φ (1, t) = φ' (1, t)` for `t ∈ [0, 1]`; then `w` is a map of the torus. Let `k` be a family of
automorphisms of `F` with `φ (0, t) = φ' (0, t) ∘ k t` along the edge `s = 0`. Then for every
continuous lift `θ` of the normalized determinant of `k` through `Circle.exp`, `2π` times the
torus clutching number of `w` is `θ 0 - θ 1`. -/
theorem torusClutchingNumber_mul_two_pi_eq_of_rectangleTrans {u u' : ℝ × ℝ → X}
    (hseam : ∀ t, u (0, t) = u' (0, t)) {w : C(Fin 2 → unitInterval, X)}
    (hw : ∀ y, w y = rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ)))
    {φ : ∀ z, F ≃L[ℂ] E (u z)} {φ' : ∀ z, F ≃L[ℂ] E (u' z)}
    (hφ : Continuous fun q : (ℝ × ℝ) × F ↦ TotalSpace.mk' F (u q.1) (φ q.1 q.2))
    (hφ' : Continuous fun q : (ℝ × ℝ) × F ↦ TotalSpace.mk' F (u' q.1) (φ' q.1 q.2))
    (hper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v,
      TotalSpace.mk' F (u (s, 1)) (φ (s, 1) v) = TotalSpace.mk' F (u (s, 0)) (φ (s, 0) v))
    (hper' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v,
      TotalSpace.mk' F (u' (s, 1)) (φ' (s, 1) v) = TotalSpace.mk' F (u' (s, 0)) (φ' (s, 0) v))
    (hend : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v,
      TotalSpace.mk' F (u (1, t)) (φ (1, t) v) = TotalSpace.mk' F (u' (1, t)) (φ' (1, t) v))
    {k : unitInterval → F ≃L[ℂ] F}
    (hφk : ∀ (t : unitInterval) v, TotalSpace.mk' F (u (0, t)) (φ (0, t) v) =
      TotalSpace.mk' F (u' (0, t)) (φ' (0, t) (k t v)))
    {θ : unitInterval → ℝ} (hθ : Continuous θ)
    (hθk : ∀ t, Circle.exp (θ t) = (k t).normalizedDet) :
    (torusClutchingNumber F E w : ℝ) * (2 * Real.pi) = θ 0 - θ 1 := by
  have hk := Floer.continuous_of_mk_eq_mk hseam hφ hφ' hφk
  -- The frame `Ψ` over the square of `w`: `φ` on the left half and `φ' ∘ k` on the right half.
  obtain ⟨Ψ, hΨc, hΨ⟩ := Floer.exists_frame_rectangleTrans (p := w) hseam hw hφ hφ' hk hφk
  -- Points of the total space read in `φ` or `φ'` only depend on the point of the plane.
  have hmk {z z' : ℝ × ℝ} (hz : z = z') (v : F) :
      TotalSpace.mk' F (u z) (φ z v) = TotalSpace.mk' F (u z') (φ z' v) := by
    subst hz
    rfl
  have hmk' {z z' : ℝ × ℝ} (hz : z = z') (v : F) :
      TotalSpace.mk' F (u' z) (φ' z v) = TotalSpace.mk' F (u' z') (φ' z' v) := by
    subst hz
    rfl
  -- Along the edges `s = 0` and `s = 1` of the square, `Ψ` reads `φ (1, ·)` and `φ (1, ·) ∘ k`.
  refine torusClutchingNumber_mul_two_pi_eq_of_frame hΨc (k := k) (fun t v ↦ ?_) (fun s v ↦ ?_) hθ
    hθk
  · rw [hΨ, hΨ, ite_eq_right (by norm_num), ite_eq_left (by simp)]
    refine ((hmk' (Prod.ext (by norm_num [Real.smoothTransition.one_of_one_le]) (by simp))
      _).trans (hend t t.property _).symm).trans (hmk (Prod.ext ?_ (by simp)) _)
    simp [Real.smoothTransition.zero_of_nonpos]
  -- `Ψ` takes the same values on the top and bottom edges: the frames are periodic, and so is `k`,
  -- since both frames are periodic along the common loop `u (0, ·)`.
  · have hk₀₁ : k 1 = k 0 := by
      have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
      ext v
      have e₁ := hφk 1 v
      have e₀ := hφk 0 v
      rw [Icc.coe_one] at e₁
      rw [Icc.coe_zero] at e₀
      exact (φ' (0, 0)).injective (TotalSpace.mk_inj.1
        ((((hper' 0 h0 (k 1 v)).symm.trans e₁.symm).trans (hper 0 h0 v)).trans e₀))
    rw [hΨ, hΨ]
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hs, ↓reduceIte, Icc.coe_one,
        Icc.coe_zero]
      exact hper (1 - Real.smoothTransition (3 * (s : ℝ)))
        ⟨by linarith [Real.smoothTransition.le_one (3 * (s : ℝ))],
          by linarith [Real.smoothTransition.nonneg (3 * (s : ℝ))]⟩ v
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hs, ↓reduceIte, Icc.coe_one,
        Icc.coe_zero, hk₀₁]
      exact hper' (Real.smoothTransition (3 * (s : ℝ) - 2))
        ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ _

end Clutching

/-! ### Unitary frames of a cylinder -/

section Symplectic

open SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {γ γ₀ : ℝ → M} {u u' : ℝ × ℝ → M}

/-- **Unitary frames of a cylinder.** Let `J` be an almost complex structure compatible with `σ`,
`G` a complex inner product space of half the real dimension of `M`, and `ψ₀` a unitary frame of
the tangent bundle along the reference loop `γ₀`, complex linear for `J`, carrying
`Im ⟪·, ·⟫` to `σ` and periodic, `ψ₀ 0 = ψ₀ 1`. Then every smooth cylinder `u` from `γ` to `γ₀`
carries a frame along `u` on the whole plane, complex linear for `J` and carrying `Im ⟪·, ·⟫` to
`σ`, whose restriction to the unit square is a frame of the cylinder extending `ψ₀`. -/
theorem IsSmoothCylinder.exists_unitary_isCylinderFrame {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [Fact (finrank ℝ E = 2 * finrank ℂ G)]
    (hJ : σ.Compatible J) (hu : IsSmoothCylinder I γ γ₀ u)
    {ψ₀ : ∀ t : unitInterval, G ≃L[ℝ] TangentSpace I (γ₀ t)}
    (hψ₀ : IsSymplecticFrame σ (imInnerSymplecticForm G) (fun t : unitInterval ↦ γ₀ t) ψ₀)
    (hψ₀₁ : ∀ v, ψ₀ 0 v = ψ₀ 1 v) (hψ₀J : ∀ t v, ψ₀ t (Complex.I • v) = J (γ₀ t) (ψ₀ t v)) :
    ∃ χ : ∀ z : ℝ × ℝ, G ≃L[ℝ] TangentSpace I (u z),
      IsSymplecticFrame σ (imInnerSymplecticForm G) u χ ∧
      IsCylinderFrame σ (imInnerSymplecticForm G) u ψ₀ (fun p ↦ χ ((p.1 : ℝ), (p.2 : ℝ))) ∧
      ∀ z v, χ z (Complex.I • v) = J (u z) (χ z v) := by
  obtain ⟨Ψ, hΨc, hΨJ, -, hΨσ⟩ := hJ.exists_continuous_unitary_frame (G := G)
    hu.contMDiff.continuous
  have hΨ : IsSymplecticFrame σ (imInnerSymplecticForm G) u Ψ :=
    ⟨hΨc, fun z v w ↦ by rw [hΨσ, imInnerSymplecticForm_apply]⟩
  exact hu.exists_isCylinderFrame_of_isSymplecticFrame hΨ hψ₀ hψ₀₁ (j := (Complex.I • ·))
    (K := fun x ↦ J x) hΨJ hψ₀J

/-! ### The cylinder-change law -/

/-- **The torus clutching number from complex frames of two cylinders.** For smooth cylinders `u`
and `u'` from `γ` to `γ₀`, complex frames `χ` and `χ'` of `(TM, J)` along them, periodic on the
loops of the cylinders and equal along `γ₀`, that differ along `γ` by a loop `k` of complex
automorphisms of the model, the torus `w` glued from the two cylinders has `2π` times its
clutching number equal to minus the winding of `det k`. -/
private theorem torusClutchingNumber_mul_two_pi_eq_of_complex_frames {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
    [Fact (finrank ℝ E = 2 * finrank ℂ G)] (hu : IsSmoothCylinder I γ γ₀ u)
    (hu' : IsSmoothCylinder I γ γ₀ u') {w : C(Fin 2 → unitInterval, M)}
    (hw : ∀ y, w y = rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ)))
    {χ : ∀ z, G ≃L[ℝ] TangentSpace I (u z)} {χ' : ∀ z, G ≃L[ℝ] TangentSpace I (u' z)}
    (hχ : Continuous fun q : (ℝ × ℝ) × G ↦ (⟨u q.1, χ q.1 q.2⟩ : TangentBundle I M))
    (hχ' : Continuous fun q : (ℝ × ℝ) × G ↦ (⟨u' q.1, χ' q.1 q.2⟩ : TangentBundle I M))
    (hχJ : ∀ z v, χ z (Complex.I • v) = J (u z) (χ z v))
    (hχJ' : ∀ z v, χ' z (Complex.I • v) = J (u' z) (χ' z v))
    (hper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v, χ (s, 1) v = χ (s, 0) v)
    (hper' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v, χ' (s, 1) v = χ' (s, 0) v)
    (hend : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v, χ (1, t) v = χ' (1, t) v)
    {k : unitInterval → G ≃L[ℂ] G} (hχk : ∀ (t : unitInterval) v, χ (0, t) v = χ' (0, t) (k t v))
    {θ : unitInterval → ℝ} (hθ : Continuous θ) (hθk : ∀ t, Circle.exp (θ t) = (k t).normalizedDet) :
    (torusClutchingNumber G (J.toContMDiff 0).toContinuousComplexStructure.Fiber w : ℝ) *
      (2 * Real.pi) = θ 0 - θ 1 := by
  set Jc := (J.toContMDiff 0).toContinuousComplexStructure
  have hJ₀ {b : M} (w : TangentSpace I b) : J b w = J.toContMDiff 0 b w :=
    (J.toContMDiff_apply 0 b w).symm
  have hχJc (z : ℝ × ℝ) (v : G) := (hχJ z v).trans (hJ₀ _)
  have hχJc' (z : ℝ × ℝ) (v : G) := (hχJ' z v).trans (hJ₀ _)
  -- The complex frames are `χ` and `χ'` followed by the identification of `TM` with the fibres of
  -- `Jc`, so points of the total space are compared in the tangent bundle.
  have hcont {v : ℝ × ℝ → M} {ξ : ∀ z, G ≃L[ℝ] TangentSpace I (v z)}
      (hξ : Continuous fun q : (ℝ × ℝ) × G ↦ (⟨v q.1, ξ q.1 q.2⟩ : TangentBundle I M))
      (hξJ : ∀ z w, ξ z (Complex.I • w) = J.toContMDiff 0 (v z) (ξ z w)) :
      Continuous fun q : (ℝ × ℝ) × G ↦
        TotalSpace.mk' G (v q.1) ((J.toContMDiff 0).complexFrame (ξ q.1) (hξJ q.1) q.2) :=
    ((Jc.totalSpaceHomeomorph G).symm.continuous.comp hξ).congr fun q ↦ by
      rw [Function.comp_apply, Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_symm_apply,
        ContMDiffAlmostComplexStructure.complexFrame_apply]
  have hmk {v v' : ℝ × ℝ → M} {ξ : ∀ z, G ≃L[ℝ] TangentSpace I (v z)}
      {ξ' : ∀ z, G ≃L[ℝ] TangentSpace I (v' z)} (hξJ : ∀ z w, ξ z (Complex.I • w) = _)
      (hξJ' : ∀ z w, ξ' z (Complex.I • w) = _) {z z' : ℝ × ℝ} {x x' : G}
      (h : (⟨v z, ξ z x⟩ : TangentBundle I M) = ⟨v' z', ξ' z' x'⟩) :
      TotalSpace.mk' G (v z) ((J.toContMDiff 0).complexFrame (ξ z) (hξJ z) x) =
        TotalSpace.mk' G (v' z') ((J.toContMDiff 0).complexFrame (ξ' z') (hξJ' z') x') := by
    refine (Jc.totalSpaceHomeomorph G).injective ?_
    rw [ContMDiffAlmostComplexStructure.totalSpaceHomeomorph_mk_complexFrame,
      ContMDiffAlmostComplexStructure.totalSpaceHomeomorph_mk_complexFrame, h]
  refine torusClutchingNumber_mul_two_pi_eq_of_rectangleTrans
    (φ := fun z ↦ (J.toContMDiff 0).complexFrame (χ z) (hχJc z))
    (φ' := fun z ↦ (J.toContMDiff 0).complexFrame (χ' z) (hχJc' z))
    (fun t ↦ (hu.apply_zero t).trans (hu'.apply_zero t).symm) hw (hcont hχ hχJc)
    (hcont hχ' hχJc') (fun s hs v ↦ hmk hχJc hχJc ?_) (fun s hs v ↦ hmk hχJc' hχJc' ?_)
    (fun t ht v ↦ hmk hχJc hχJc' ?_) (k := k) (fun t v ↦ hmk hχJc hχJc' ?_) hθ hθk
  · exact TotalSpace.ext (hu.periodic s hs) (heq_of_eq (hper s hs v))
  · exact TotalSpace.ext (hu'.periodic s hs) (heq_of_eq (hper' s hs v))
  · exact TotalSpace.ext ((hu.apply_one t ht).trans (hu'.apply_one t ht).symm)
      (heq_of_eq (hend t ht v))
  · exact TotalSpace.ext ((hu.apply_zero t).trans (hu'.apply_zero t).symm) (heq_of_eq (hχk t v))

/-- **The cylinder-change law for unitary frames.** Let `χ` and `χ'` be frames along smooth
cylinders `u` and `u'` from `γ` to `γ₀`, complex linear for an almost complex structure `J` tamed by
`σ` and carrying `Im ⟪·, ·⟫` to `σ`, whose restrictions to the unit square are frames of the
cylinders extending the same reference frame `ψ₀`. Then the Conley–Zehnder index of `Φ` read in
`χ'` along `γ` is its index read in `χ` minus twice the torus clutching number of the torus glued
from the two cylinders. -/
private theorem frameConleyZehnderIndex_eq_sub_two_mul_torusClutchingNumber {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
    [Fact (finrank ℝ E = 2 * finrank ℂ G)] (hu : IsSmoothCylinder I γ γ₀ u)
    (hu' : IsSmoothCylinder I γ γ₀ u') {w : C(Fin 2 → unitInterval, M)}
    (hw : ∀ y, w y = rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ)))
    {ψ₀ : ∀ t : unitInterval, G ≃L[ℝ] TangentSpace I (γ₀ t)}
    {χ : ∀ z, G ≃L[ℝ] TangentSpace I (u z)} {χ' : ∀ z, G ≃L[ℝ] TangentSpace I (u' z)}
    (hχs : IsSymplecticFrame σ (imInnerSymplecticForm G) u χ)
    (hχs' : IsSymplecticFrame σ (imInnerSymplecticForm G) u' χ')
    (hχ : IsCylinderFrame σ (imInnerSymplecticForm G) u ψ₀ (fun p ↦ χ ((p.1 : ℝ), (p.2 : ℝ))))
    (hχ' : IsCylinderFrame σ (imInnerSymplecticForm G) u' ψ₀ (fun p ↦ χ' ((p.1 : ℝ), (p.2 : ℝ))))
    (hχJ : ∀ z v, χ z (Complex.I • v) = J (u z) (χ z v))
    (hχJ' : ∀ z v, χ' z (Complex.I • v) = J (u' z) (χ' z v))
    {Φ : ∀ t : unitInterval, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ (t : unitInterval) u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    frameConleyZehnderIndex (imInnerSymplecticForm G) (hχ'.isSymplecticFrame_apply_zero hu') hΦ
        hΦσ =
      frameConleyZehnderIndex (imInnerSymplecticForm G) (hχ.isSymplecticFrame_apply_zero hu) hΦ
        hΦσ - 2 * (torusClutchingNumber G (J.toContMDiff 0).toContinuousComplexStructure.Fiber w :
          ℝ) := by
  -- The restrictions of the frames to `γ`.
  let φ : ∀ t : unitInterval, G ≃L[ℝ] TangentSpace I (γ t) := fun t ↦ χ (0, t)
  let φ' : ∀ t : unitInterval, G ≃L[ℝ] TangentSpace I (γ t) := fun t ↦ χ' (0, t)
  have hφ : IsSymplecticFrame σ (imInnerSymplecticForm G) (fun t : unitInterval ↦ γ t) φ :=
    hχ.isSymplecticFrame_apply_zero hu
  have hφ' : IsSymplecticFrame σ (imInnerSymplecticForm G) (fun t : unitInterval ↦ γ t) φ' :=
    hχ'.isSymplecticFrame_apply_zero hu'
  -- Along `γ` both frames are complex linear for `J`.
  have hJf (a b : M) (hab : a = b) (x : E) : J a x = J b x := by
    subst hab
    rfl
  have hφJ (t : unitInterval) (v : G) : φ t (Complex.I • v) = J (γ t) (φ t v) :=
    (hχJ (0, t) v).trans (hJf _ _ (hu.apply_zero t) _)
  have hφJ' (t : unitInterval) (v : G) : φ' t (Complex.I • v) = J (γ t) (φ' t v) :=
    (hχJ' (0, t) v).trans (hJf _ _ (hu'.apply_zero t) _)
  -- So they differ by complex-linear maps `k t`, with `φ(t) = φ'(t) ∘ k(t)`.
  obtain ⟨k, hk, hχk⟩ := exists_continuous_complex_frame_change hφ.continuous hφ'.continuous hφJ
    hφJ'
  -- A continuous lift `θ` of the normalized determinant of `k` computes the clutching number.
  obtain ⟨θ, hθ⟩ := Circle.exists_lift
    (⟨⟨fun t ↦ (k t).normalizedDet, hk.normalizedDet⟩, rfl, rfl⟩ : Path _ _)
  have hθk (t : unitInterval) : Circle.exp (θ t) = (k t).normalizedDet := hθ t
  have hc := torusClutchingNumber_mul_two_pi_eq_of_complex_frames hu hu' hw hχs.continuous
    hχs'.continuous hχJ hχJ' (fun s hs v ↦ hχ.periodic ⟨s, hs⟩ v)
    (fun s hs v ↦ hχ'.periodic ⟨s, hs⟩ v)
    (fun t ht v ↦ (hχ.apply_one ⟨t, ht⟩ v).trans (hχ'.apply_one ⟨t, ht⟩ v).symm) hχk
    θ.continuous hθk
  -- The change of frame along `γ` is a loop, and changes the index by twice the winding of
  -- `det k`.
  have hper := trans_symm_zero_eq_trans_symm_one (I := I) (γ := fun t : unitInterval ↦ γ t)
    (χ := φ) (χ' := φ') (fun v ↦ (hχ.periodic 0 v).symm) fun v ↦ (hχ'.periodic 0 v).symm
  have hm := frameConleyZehnderIndex_mul_two_pi_eq_of_complex hφ hφ' hper hχk θ.continuous hθk
    hΦ hΦσ
  refine mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) ?_
  linear_combination hm + 2 * hc

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The square glued from two smooth cylinders from `γ` to `γ₀`, `u` run backwards followed by
`u'`, is a map of the torus: it agrees on its left and right edges, where it runs along `γ₀`, and on
its top and bottom edges, since the loops of the cylinders close up. -/
private theorem IsSmoothCylinder.rectangleTrans_apply_eq (hu : IsSmoothCylinder I γ γ₀ u)
    (hu' : IsSmoothCylinder I γ γ₀ u') {w : C(Fin 2 → unitInterval, M)}
    (hw : ∀ y, w y = rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ))) :
    (∀ t, w ![1, t] = w ![0, t]) ∧ ∀ s, w ![s, 1] = w ![s, 0] := by
  have hcyl : IsSmoothCylinder I (fun t ↦ u (1, t)) γ₀
      (rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u') :=
    hu.comp_prodMap_one_sub.trans hu' fun t ↦ by simp [hu.apply_zero, hu'.apply_zero]
  refine ⟨fun t ↦ ?_, fun s ↦ ?_⟩ <;> rw [hw, hw] <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Icc.coe_one, Icc.coe_zero]
  · rw [hcyl.apply_one t t.property, hcyl.apply_zero, hu.apply_one t t.property]
  · exact hcyl.periodic s s.property

variable [T2Space M] [SigmaCompactSpace M] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] {ω₀ : SymplecticForm W}
  {φ₀ : ∀ t : unitInterval, W ≃L[ℝ] TangentSpace I (γ₀ t)}

/-- **The cylinder-change law for the Conley–Zehnder index.** Let `σ` be a fiberwise nondegenerate
two-form, `γ₀` a reference loop with a symplectic frame `φ₀` of the tangent bundle along it,
`φ₀ 0 = φ₀ 1`, and `u`, `u'` two smooth cylinders from a loop `γ` to `γ₀`. Let `w` be the torus
`rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u'` glued from them, `u` run backwards followed
by `u'`. Then for every continuous family `Φ` of linear maps along `γ` preserving `σ`, the
Conley–Zehnder index of `Φ` through `u'` is its index through `u` minus twice the first Chern
number of the tangent bundle on `w`: its torus clutching number for any almost complex structure
`J` tamed by `σ` and any complex model fibre `G`. -/
theorem IsSmoothCylinder.conleyZehnderIndex_eq_sub_two_mul_torusClutchingNumber
    (h : σ.IsNondegenerate) (hu : IsSmoothCylinder I γ γ₀ u) (hu' : IsSmoothCylinder I γ γ₀ u')
    (hφ₀ : IsSymplecticFrame σ ω₀ (fun t : unitInterval ↦ γ₀ t) φ₀) (hφ₀₁ : ∀ v, φ₀ 0 v = φ₀ 1 v)
    (hJ : σ.Tames J) (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
    [Fact (finrank ℝ E = 2 * finrank ℂ G)] {w : C(Fin 2 → unitInterval, M)}
    (hw : ∀ y, w y = rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ)))
    {Φ : ∀ t : unitInterval, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ (t : unitInterval) u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    hu'.conleyZehnderIndex h hφ₀ hφ₀₁ hΦ hΦσ = hu.conleyZehnderIndex h hφ₀ hφ₀₁ hΦ hΦσ -
      2 * (torusClutchingNumber G (J.toContMDiff 0).toContinuousComplexStructure.Fiber w : ℝ) := by
  let G₀ := EuclideanSpace ℂ (Fin (finrank ℝ E / 2))
  have : Fact (finrank ℝ E = 2 * finrank ℂ G₀) := ⟨h.two_mul_finrank_euclideanSpace (γ₀ 0)⟩
  obtain ⟨J₀, hJ₀⟩ := h.exists_compatible
  -- A periodic unitary frame `ψ₀` along the reference loop, for the compatible structure `J₀`.
  have hγ₀ : Continuous fun t : unitInterval ↦ γ₀ t :=
    (hu.contMDiff.continuous.comp (by fun_prop : Continuous fun t : unitInterval ↦
      ((1 : ℝ), (t : ℝ)))).congr fun t ↦ hu.apply_one t t.property
  have hγ₀₁ : γ₀ (0 : unitInterval) = γ₀ (1 : unitInterval) := by
    rw [Icc.coe_zero, Icc.coe_one, ← hu.apply_one 0 ⟨le_rfl, zero_le_one⟩,
      ← hu.apply_one 1 ⟨zero_le_one, le_rfl⟩, hu.periodic 1 ⟨zero_le_one, le_rfl⟩]
  obtain ⟨ψ₀, hψ₀c, hψ₀J, -, hψ₀σ, hψ₀₁⟩ :=
    hJ₀.exists_continuous_unitary_frame_loop (G := G₀) hγ₀ hγ₀₁
  have hψ₀ : IsSymplecticFrame σ (imInnerSymplecticForm G₀) (fun t : unitInterval ↦ γ₀ t) ψ₀ :=
    ⟨hψ₀c, fun t v w ↦ by rw [hψ₀σ, imInnerSymplecticForm_apply]⟩
  -- The law for unitary frames of the two cylinders extending `ψ₀`.
  obtain ⟨χ, hχs, hχ, hχJ⟩ := hu.exists_unitary_isCylinderFrame hJ₀ hψ₀ hψ₀₁ hψ₀J
  obtain ⟨χ', hχs', hχ', hχJ'⟩ := hu'.exists_unitary_isCylinderFrame hJ₀ hψ₀ hψ₀₁ hψ₀J
  have hlaw := frameConleyZehnderIndex_eq_sub_two_mul_torusClutchingNumber hu hu' hw hχs hχs' hχ
    hχ' hχJ hχJ' hΦ hΦσ
  -- The torus clutching number does not depend on the tame structure or the model.
  obtain ⟨hR, hT⟩ := hu.rectangleTrans_apply_eq hu' hw
  rw [Tames.torusClutchingNumber_eq G G₀ hJ hJ₀.tames 0 0 w hR hT] at hlaw
  -- Change the reference frame to `ψ₀`, moved to the model `W` by a linear symplectomorphism.
  obtain ⟨e, he⟩ := SymplecticForm.exists_isSymplectomorphism ω₀ (imInnerSymplecticForm G₀)
    (((φ₀ 0).toLinearEquiv.finrank_eq).trans (ψ₀ 0).toLinearEquiv.finrank_eq.symm)
  have he' : ∀ v w, imInnerSymplecticForm G₀ (e.toContinuousLinearEquiv v)
      (e.toContinuousLinearEquiv w) = ω₀ v w := he.apply
  rw [hu'.conleyZehnderIndex_eq_add_maslovIndex h (hψ₀.trans _ he') (fun v ↦ hψ₀₁ _) hφ₀ hφ₀₁ hΦ
      hΦσ, hu.conleyZehnderIndex_eq_add_maslovIndex h (hψ₀.trans _ he') (fun v ↦ hψ₀₁ _) hφ₀ hφ₀₁
      hΦ hΦσ, hu'.conleyZehnderIndex_trans h hψ₀ hψ₀₁ _ he',
    hu.conleyZehnderIndex_trans h hψ₀ hψ₀₁ _ he', hu'.conleyZehnderIndex_eq h hψ₀ hψ₀₁ hχ',
    hu.conleyZehnderIndex_eq h hψ₀ hψ₀₁ hχ, hlaw]
  ring

/-- **Independence of the cylinder under the Chern condition on tori.** If the first Chern number of
the tangent bundle vanishes on every map of the torus, that is, the torus clutching number of
`(TM, J)` vanishes for an almost complex structure `J` tamed by `σ`, then the Conley–Zehnder index
of a continuous family `Φ` of linear maps along `γ` preserving `σ` is the same through every smooth
cylinder from `γ` to the reference loop `γ₀`. -/
theorem IsSmoothCylinder.conleyZehnderIndex_eq_of_torusClutchingNumber_eq_zero
    (h : σ.IsNondegenerate) (hu : IsSmoothCylinder I γ γ₀ u) (hu' : IsSmoothCylinder I γ γ₀ u')
    (hφ₀ : IsSymplecticFrame σ ω₀ (fun t : unitInterval ↦ γ₀ t) φ₀) (hφ₀₁ : ∀ v, φ₀ 0 v = φ₀ 1 v)
    (hJ : σ.Tames J) (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
    [Fact (finrank ℝ E = 2 * finrank ℂ G)]
    (hc : ∀ w : C(Fin 2 → unitInterval, M),
      torusClutchingNumber G (J.toContMDiff 0).toContinuousComplexStructure.Fiber w = 0)
    {Φ : ∀ t : unitInterval, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ (t : unitInterval) u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    hu'.conleyZehnderIndex h hφ₀ hφ₀₁ hΦ hΦσ = hu.conleyZehnderIndex h hφ₀ hφ₀₁ hΦ hΦσ := by
  let w : C(Fin 2 → unitInterval, M) :=
    ⟨fun y ↦ rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) u' ((y 0 : ℝ), (y 1 : ℝ)),
      ((hu.comp_prodMap_one_sub.trans hu' fun t ↦ by
        simp [hu.apply_zero, hu'.apply_zero]).contMDiff.continuous.comp (by fun_prop))⟩
  rw [hu.conleyZehnderIndex_eq_sub_two_mul_torusClutchingNumber h hu' hφ₀ hφ₀₁ hJ G
    (w := w) (fun _ ↦ rfl) hΦ hΦσ, hc w, Int.cast_zero, mul_zero, sub_zero]

end Symplectic

end TauCeti

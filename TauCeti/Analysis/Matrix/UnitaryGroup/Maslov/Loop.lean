/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Lagrangian
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Path
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.RealImage
public import TauCeti.Topology.Algebra.Star.Unitary
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Orthogonal.Unitary

/-!
# The Maslov index of paths of unitary frames and of loops of Lagrangian subspaces

A unitary matrix `U` frames the Lagrangian subspace `U ℝⁿ` (`Matrix.realImage`) of `ℂⁿ`. Two
Maslov indices are attached to a path `γ` of unitary frames:

* Souriau's spectral formula for the Robbin–Salamon index of the path of Lagrangians `γ t ℝⁿ`
  relative to `ℝⁿ` (`Matrix.UnitaryGroup.maslovIndex`), a real number, defined for every path;
* the native Maslov index of loops of maximal totally real subspaces
  (`TauCeti.TotallyRealLoop.maslovIndex`), the degree of the loop of Maslov phases
  `t ↦ ρ(ℝⁿ, γ t ℝⁿ)`, defined when the path of subspaces closes up, and the relative Maslov
  index of two paths with common endpoints (`TauCeti.TotallyRealPath.relativeMaslovIndex`).

This file shows that they agree.

The Lagrangian `U ℝⁿ` and the Souriau map `U Uᵀ` determine each other
(`Matrix.UnitaryGroup.realImage_eq_realImage_iff_souriau_eq`): two unitary frames of the same
subspace differ by a real orthogonal matrix, which does not change `U Uᵀ`; conversely, if
`U Uᵀ = V Vᵀ` then `O = V⁻¹ U` is unitary with `O Oᵀ = 1`, so `Oᵀ = O⁻¹ = Oᴴ`, its entries are
real and `U ℝⁿ = V O ℝⁿ = V ℝⁿ`. So a path of unitary frames gives a closed loop of Lagrangians
(`Matrix.UnitaryGroup.realImageLoop`) exactly when its Souriau maps close up, which is the
hypothesis under which the spectral terms of Souriau's formula cancel.

The Maslov phase of `U ℝⁿ` relative to `ℝⁿ` is `det U / conj (det U) = (det U)²`, the determinant
of the Souriau map (`Matrix.UnitaryGroup.maslovPhase_realImage`). Both indices are therefore
read off the same loop `t ↦ det (γ t γ tᵀ)` of the circle:

* **The loop comparison.** If the Souriau maps of the endpoints agree, the native Maslov index of
  the loop `t ↦ γ t ℝⁿ` is Souriau's index of `γ`
  (`Matrix.UnitaryGroup.maslovIndex_realImageLoop`).
* **The path comparison.** For two paths of unitary frames with the same Lagrangians at the
  endpoints, the relative Maslov index of their paths of Lagrangians is the difference of their
  Souriau indices (`Matrix.UnitaryGroup.relativeMaslovIndex_realImagePath`): the angle terms
  differ by the degree of the loop of quotients, and the spectral terms cancel.
* **Every loop of maximal totally real subspaces.** The native Maslov index of every loop of
  maximal totally real subspaces of `ℂⁿ` equals Souriau's index of some path `γ : Path U V` of
  unitary frames with `U Uᵀ = V Vᵀ`, whose loop of Lagrangians `t ↦ γ t ℝⁿ` has the same native
  Maslov index (`TauCeti.TotallyRealLoop.exists_maslovIndex_eq_unitaryGroup_maslovIndex`). This
  combines the loop comparison with the deformation of a totally real loop to a Lagrangian one,
  `TauCeti.TotallyRealLoop.exists_unitary_maslovIndex_eq`.

In particular the Robbin–Salamon index of a closed path of Lagrangians, as given by Souriau's
formula, has the sign and normalization of the native loop invariant, which counts half-turns of
the determinant of a frame. Through the loop comparison, Souriau's index of paths whose Lagrangians
close up inherits the invariance of the native index under free homotopies, along which the
endpoints move (`Matrix.UnitaryGroup.maslovIndex_eq_of_homotopy_of_souriau_eq`). For a general
path it is not invariant under arbitrary free homotopies, but it is invariant under homotopies
along whose endpoints the eigenvalue `1` of the Souriau map keeps its multiplicity
(`Matrix.UnitaryGroup.maslovIndex_eq_of_homotopy_of_rootMultiplicity_eq`).

## Main declarations

* `Matrix.UnitaryGroup.realImage_eq_realImage_iff_souriau_eq`: unitary frames frame the same
  Lagrangian exactly when they have the same Souriau map.
* `Matrix.UnitaryGroup.maslovPhase_realImage`: the Maslov phase of `U ℝⁿ` relative to `ℝⁿ` is
  `det (U Uᵀ)`.
* `Matrix.UnitaryGroup.realImagePath`, `Matrix.UnitaryGroup.realImageLoop`: the path and
  the loop `t ↦ γ t ℝⁿ` of Lagrangians framed by a path `γ` of unitary frames.
* `Matrix.UnitaryGroup.maslovIndex_realImageLoop`: the loop comparison.
* `Matrix.UnitaryGroup.relativeMaslovIndex_realImagePath`: the path comparison.
* `Matrix.UnitaryGroup.maslovIndex_eq_of_homotopy_of_souriau_eq`: free homotopy invariance of
  Souriau's index of paths whose Lagrangians close up.
* `TauCeti.TotallyRealLoop.exists_maslovIndex_eq_unitaryGroup_maslovIndex`: the native Maslov
  index of every loop of maximal totally real subspaces of `ℂⁿ` equals Souriau's index of some
  path `γ : Path U V` of unitary frames with `U Uᵀ = V Vᵀ`.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Theorem 2.3 (the loop property: on loops the index is the Maslov index of the loop).
* J.-M. Souriau, *Construction explicite de l'indice de Maslov. Applications*, Group theoretical
  methods in physics, Lecture Notes in Physics **50**, Springer, 1976, 117--148.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.3 (the Lagrangian Grassmannian `U(n) / O(n)`, the map `U ↦ U Uᵀ` and
  the Maslov index of loops of Lagrangian subspaces as the degree of `det²`).
-/

public section

open ComplexConjugate Matrix
open scoped unitInterval

namespace Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Unitary frames of the same Lagrangian are the frames with the same Souriau map.** For
unitary `U` and `V`, the Lagrangians `U ℝⁿ` and `V ℝⁿ` agree exactly when `U Uᵀ = V Vᵀ`. -/
theorem realImage_eq_realImage_iff_souriau_eq {U V : unitaryGroup n ℂ} :
    (U : Matrix n n ℂ).realImage = (V : Matrix n n ℂ).realImage ↔ souriau U = souriau V := by
  constructor
  · -- Two unitary frames of the same subspace differ by a real orthogonal matrix.
    intro h
    have hgram (W : unitaryGroup n ℂ) :
        (((Unitary.toUnits W : GL n ℂ) : Matrix n n ℂ)ᴴ * (Unitary.toUnits W : GL n ℂ)).map
          Complex.re = 1 := by
      rw [Unitary.val_toUnits_apply, ← star_eq_conjTranspose,
          Unitary.star_mul_self_of_mem W.property,
        Matrix.map_one _ Complex.zero_re Complex.one_re]
    obtain ⟨N, hN, hVN⟩ := exists_mem_orthogonalGroup_eq_mul_map_ofReal
      (M := Unitary.toUnits U) (M' := Unitary.toUnits V)
      (by rwa [Unitary.val_toUnits_apply, Unitary.val_toUnits_apply]) (hgram U) (hgram V)
    rw [Unitary.val_toUnits_apply, Unitary.val_toUnits_apply] at hVN
    rw [show V = U * ⟨_, map_ofReal_mem_unitaryGroup hN⟩ from
        Subtype.ext (by rw [hVN, Submonoid.coe_mul]),
      souriau_mul_of_mul_transpose_eq_one U _ (map_ofReal_mul_transpose_map_ofReal_eq_one hN)]
  · -- If `U Uᵀ = V Vᵀ`, then `V⁻¹ U` is a real orthogonal matrix.
    intro h
    have hs : souriau (V⁻¹ * U) = 1 := by
      refine Subtype.ext ?_
      rw [coe_souriau_mul_left, h, ← coe_souriau_mul_left, inv_mul_cancel]
      simp
    have hO : ((V⁻¹ * U : unitaryGroup n ℂ) : Matrix n n ℂ) *
        ((V⁻¹ * U : unitaryGroup n ℂ) : Matrix n n ℂ)ᵀ = 1 := by
      simpa only [coe_souriau, OneMemClass.coe_one] using congrArg Subtype.val hs
    obtain ⟨N, hN, hON⟩ := exists_mem_orthogonalGroup_map_eq_of_mul_transpose_eq_one _ hO
    rw [Complex.coe_algebraMap] at hON
    have hU : (U : Matrix n n ℂ) = V * N.map ((↑) : ℝ → ℂ) := by
      rw [hON, ← Submonoid.coe_mul, mul_inv_cancel_left]
    rw [hU, realImage_mul_map_ofReal _ ((isUnit_iff_isUnit_det _).2
      (isUnit_det_of_right_inverse ((mem_orthogonalGroup_iff _ _).1 hN)))]

/-- **The Maslov phase of a unitary frame.** The Maslov phase of the Lagrangian `U ℝⁿ` relative to
`ℝⁿ` is `det U / conj (det U) = (det U)²`, the determinant of the Souriau map `U Uᵀ`. -/
theorem maslovPhase_realImage (U : unitaryGroup n ℂ) :
    TauCeti.isMaximalTotallyReal_realSubspace.maslovPhase
        (isMaximalTotallyReal_realImage (det_isUnit U).ne_zero) =
      (detCircle (souriau U) : ℂ) := by
  set A := (U : Matrix n n ℂ).toEuclideanCLE (det_isUnit U).ne_zero
  have hconj : conj (U : Matrix n n ℂ).det = ((U : Matrix n n ℂ).det)⁻¹ := by
    rw [← coe_detCircle, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
  -- The linear map underlying `A.toLinearEquiv` is the one underlying `A`, whose determinant is
  -- computed by `Matrix.det_toEuclideanCLE`.
  have hd : LinearMap.det (A.toLinearEquiv : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) =
      (U : Matrix n n ℂ).det :=
    det_toEuclideanCLE _ _
  rw [TauCeti.IsMaximalTotallyReal.maslovPhase_congr _ _
      (TauCeti.isMaximalTotallyReal_realSubspace.map_linearEquiv A.toLinearEquiv)
      (realImage_eq_map_toEuclideanCLE (det_isUnit U).ne_zero),
    TauCeti.isMaximalTotallyReal_realSubspace.maslovPhase_map, hd, hconj, div_inv_eq_mul,
    detCircle_souriau, Circle.coe_pow, coe_detCircle, sq]

/-! ### Paths and loops of Lagrangians framed by unitary frames -/

/-- The **path of Lagrangians** `t ↦ γ t ℝⁿ` framed by a path `γ` of unitary frames. -/
noncomputable def realImagePath {U V : unitaryGroup n ℂ} (γ : Path U V) :
    TauCeti.TotallyRealPath (EuclideanSpace ℂ n) where
  toFun t := (γ t : Matrix n n ℂ).realImage
  exists_frame := ⟨TauCeti.realSubspace n, TauCeti.isMaximalTotallyReal_realSubspace,
    fun t ↦ (γ t : Matrix n n ℂ).toEuclideanCLE (det_isUnit (γ t)).ne_zero,
    by simpa only [coe_toEuclideanCLE, Function.comp_def] using
      continuous_toEuclideanCLM.comp (continuous_subtypeVal.comp γ.continuous),
    fun t ↦ realImage_eq_map_toEuclideanCLE _⟩

@[simp]
theorem realImagePath_apply {U V : unitaryGroup n ℂ} (γ : Path U V) (t : I) :
    realImagePath γ t = (γ t : Matrix n n ℂ).realImage :=
  (rfl)

/-- The path of Lagrangians framed by `γ` starts at `U ℝⁿ`. -/
theorem realImagePath_zero {U V : unitaryGroup n ℂ} (γ : Path U V) :
    realImagePath γ 0 = (U : Matrix n n ℂ).realImage := by
  simp

/-- The path of Lagrangians framed by `γ` ends at `V ℝⁿ`. -/
theorem realImagePath_one {U V : unitaryGroup n ℂ} (γ : Path U V) :
    realImagePath γ 1 = (V : Matrix n n ℂ).realImage := by
  simp

/-- The **loop of Lagrangians** `t ↦ γ t ℝⁿ` framed by a path `γ` of unitary frames whose Souriau
maps close up, `U Uᵀ = V Vᵀ`, so that `U ℝⁿ = V ℝⁿ`. -/
noncomputable def realImageLoop {U V : unitaryGroup n ℂ} (γ : Path U V)
    (h : souriau U = souriau V) : TauCeti.TotallyRealLoop (EuclideanSpace ℂ n) :=
  (realImagePath γ).toTotallyRealLoop <| by
    rw [realImagePath_zero, realImagePath_one, realImage_eq_realImage_iff_souriau_eq]
    exact h

@[simp]
theorem realImageLoop_apply {U V : unitaryGroup n ℂ} (γ : Path U V) (h : souriau U = souriau V)
    (t : I) : realImageLoop γ h t = (γ t : Matrix n n ℂ).realImage := by
  rw [realImageLoop, TauCeti.TotallyRealPath.toTotallyRealLoop_apply, realImagePath_apply]

/-! ### Comparison of the Maslov indices -/

/-- **The native Maslov index of a Lagrangian loop is Souriau's index.** For a path `γ` of unitary
frames whose Souriau maps close up, the Maslov index of the loop of Lagrangians `t ↦ γ t ℝⁿ`, the
degree of its loop of Maslov phases, is Souriau's spectral formula for the Robbin–Salamon index of
`γ`. -/
theorem maslovIndex_realImageLoop {U V : unitaryGroup n ℂ} (γ : Path U V)
    (h : souriau U = souriau V) : ((realImageLoop γ h).maslovIndex : ℝ) = maslovIndex γ := by
  rw [maslovIndex_eq_degree γ h, (realImageLoop γ h).maslovIndex_eq_degree
    TauCeti.isMaximalTotallyReal_realSubspace _ fun t ↦ ?_]
  rw [TauCeti.IsMaximalTotallyReal.maslovPhase_congr _ _
      (isMaximalTotallyReal_realImage (det_isUnit (γ t)).ne_zero) (realImageLoop_apply γ h t),
    maslovPhase_realImage]
  simp

/-- **Relative Maslov index and Souriau's index.** For two paths `γ` and `δ` of unitary frames
whose paths of Lagrangians `t ↦ γ t ℝⁿ` and `t ↦ δ t ℝⁿ` have the same endpoints, their relative
Maslov index is the difference of the Souriau indices of `γ` and `δ`. -/
theorem relativeMaslovIndex_realImagePath {U V U' V' : unitaryGroup n ℂ} (γ : Path U V)
    (δ : Path U' V') (h₀ : realImagePath γ 0 = realImagePath δ 0)
    (h₁ : realImagePath γ 1 = realImagePath δ 1) :
    ((realImagePath γ).relativeMaslovIndex (realImagePath δ) h₀ h₁ : ℝ) =
      maslovIndex γ - maslovIndex δ := by
  have hs₀ : souriau U = souriau U' := by
    rw [← realImage_eq_realImage_iff_souriau_eq, ← realImagePath_zero γ, ← realImagePath_zero δ]
    exact h₀
  have hs₁ : souriau V = souriau V' := by
    rw [← realImage_eq_realImage_iff_souriau_eq, ← realImagePath_one γ, ← realImagePath_one δ]
    exact h₁
  -- The relative phases `ρ(δ t ℝⁿ, γ t ℝⁿ)` are the quotients `det (W (γ t)) / det (W (δ t))` of
  -- the determinants of the Souriau maps `W`, a loop based at `1`.
  let ρ : Path (1 : Circle) 1 :=
    ((detSouriauPath γ).mul (detSouriauPath δ).inv).cast
      (by rw [hs₀, mul_inv_cancel]) (by rw [hs₁, mul_inv_cancel])
  have hL₀ := TauCeti.isMaximalTotallyReal_realSubspace (n := n)
  have hρ (t : I) : (ρ t : ℂ) = ((realImagePath δ).isMaximalTotallyReal t).maslovPhase
      ((realImagePath γ).isMaximalTotallyReal t) := by
    rw [← hL₀.maslovPhase_div_maslovPhase,
      hL₀.maslovPhase_congr _ (isMaximalTotallyReal_realImage (det_isUnit (γ t)).ne_zero)
        (realImagePath_apply γ t),
      hL₀.maslovPhase_congr _ (isMaximalTotallyReal_realImage (det_isUnit (δ t)).ne_zero)
        (realImagePath_apply δ t),
      maslovPhase_realImage, maslovPhase_realImage]
    simp [ρ, div_eq_mul_inv]
  -- The angle swept by `ρ` is the difference of the angles of the two determinant paths, and the
  -- spectral terms of Souriau's formula cancel since the endpoints have the same Souriau maps.
  have hdeg : Circle.angleChange (detSouriauPath γ) - Circle.angleChange (detSouriauPath δ) =
      Circle.degree ρ * (2 * Real.pi) := by
    rw [← Circle.angleChange_eq_degree_mul,
      Circle.angleChange_congr ρ ((detSouriauPath γ).mul (detSouriauPath δ).inv)
        fun t ↦ congrFun (Path.cast_coe _ _ _) t,
      Circle.angleChange_mul, Circle.angleChange_inv, sub_eq_add_neg]
  -- `simp only` rewrites the spectral terms without touching the endpoints of the determinant
  -- paths, which depend on `souriau U` and `souriau V`.
  rw [TauCeti.TotallyRealPath.relativeMaslovIndex_eq_degree _ _ h₀ h₁ ρ hρ, maslovIndex_def,
    maslovIndex_def]
  simp only [hs₀, hs₁]
  rw [(eq_div_iff (by positivity : (2 * Real.pi) ≠ 0)).2 hdeg.symm]
  ring

/-- **Free homotopy invariance.** Let `F` be a continuous two-parameter family of unitary frames
such that for every `s` the path of Lagrangians `t ↦ F (s, t) ℝⁿ` closes up, that is, the endpoint
frames of `t ↦ F (s, t)` have the same Souriau map. If `t ↦ F (0, t)` and `t ↦ F (1, t)` frame the
same paths of Lagrangians as `γ₀` and `γ₁`, that is, have the same Souriau maps, then `γ₀` and
`γ₁` have the same Robbin–Salamon index, although the endpoints move along the homotopy. -/
theorem maslovIndex_eq_of_homotopy_of_souriau_eq {U₀ V₀ U₁ V₁ : unitaryGroup n ℂ}
    (γ₀ : Path U₀ V₀) (γ₁ : Path U₁ V₁) (F : I × I → unitaryGroup n ℂ) (hF : Continuous F)
    (h₀ : ∀ t, souriau (F (0, t)) = souriau (γ₀ t)) (h₁ : ∀ t, souriau (F (1, t)) = souriau (γ₁ t))
    (hF01 : ∀ s, souriau (F (s, 0)) = souriau (F (s, 1))) :
    maslovIndex γ₀ = maslovIndex γ₁ := by
  have hγ₀ : souriau U₀ = souriau V₀ := by
    simpa using (h₀ 0).symm.trans ((hF01 0).trans (h₀ 1))
  have hγ₁ : souriau U₁ = souriau V₁ := by
    simpa using (h₁ 0).symm.trans ((hF01 1).trans (h₁ 1))
  rw [← maslovIndex_realImageLoop γ₀ hγ₀,
    ← maslovIndex_realImageLoop γ₁ hγ₁]
  exact congrArg _ <| TauCeti.TotallyRealLoop.maslovIndex_eq_of_realImage_homotopy _ _
    (fun p ↦ Unitary.toUnits (F p)) (Unitary.continuous_toUnits.comp hF)
    (fun t ↦ by simpa using (realImage_eq_realImage_iff_souriau_eq.2 (h₀ t)).symm)
    (fun t ↦ by simpa using (realImage_eq_realImage_iff_souriau_eq.2 (h₁ t)).symm)
    fun s ↦ realImage_eq_realImage_iff_souriau_eq.2 (hF01 s)

end Matrix.UnitaryGroup

namespace TauCeti.TotallyRealLoop

open Matrix Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Every loop of maximal totally real subspaces of `ℂⁿ` has a Souriau index.** There is a
path `γ` of unitary frames whose Souriau maps close up such that the loop of Lagrangians
`t ↦ γ t ℝⁿ` has the native Maslov index of `Λ`, and that index is Souriau's index of `γ`.
See also `TauCeti.TotallyRealLoop.exists_unitary_maslovIndex_eq`. -/
theorem exists_maslovIndex_eq_unitaryGroup_maslovIndex
    (Λ : TotallyRealLoop (EuclideanSpace ℂ n)) :
    ∃ (U V : unitaryGroup n ℂ) (γ : Path U V) (h : souriau U = souriau V),
      (realImageLoop γ h).maslovIndex = Λ.maslovIndex ∧
        (Λ.maslovIndex : ℝ) = Matrix.UnitaryGroup.maslovIndex γ := by
  -- Deform `Λ` to a loop of Lagrangians `t ↦ W t ℝⁿ` with unitary frames `W`.
  obtain ⟨W, hW, Λ', hΛ', hμ⟩ := Λ.exists_unitary_maslovIndex_eq
  let γ : Path (W 0) (W 1) := ⟨⟨W, hW⟩, rfl, rfl⟩
  have h : souriau (W 0) = souriau (W 1) := by
    rw [← realImage_eq_realImage_iff_souriau_eq, ← hΛ', ← hΛ']
    exact Λ'.toFun_zero_eq_toFun_one
  have hΛγ : Λ' = realImageLoop γ h := ext fun t ↦ (hΛ' t).trans (realImageLoop_apply γ h t).symm
  refine ⟨W 0, W 1, γ, h, hΛγ ▸ hμ, ?_⟩
  rw [← hμ, ← maslovIndex_realImageLoop γ h, hΛγ]

end TauCeti.TotallyRealLoop

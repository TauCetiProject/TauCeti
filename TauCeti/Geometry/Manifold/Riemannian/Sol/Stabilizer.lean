/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sol.Height
public import TauCeti.Geometry.Manifold.Riemannian.Sol.Isotropy
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Ext

/-!
# The isotropy group of Sol

The full group of Riemannian isometries fixing the identity of Sol consists of its
eight dihedral symmetries. Height rigidity determines the pullback of the vertical
unit field. Naturality of the Levi-Civita connection then determines the horizontal
axes: the endomorphism `v ↦ ∇ᵥ ∂z` has eigenvalues `1`, `-1`, and `0`.
Isometries preserving height preserve its eigenspaces, while height reversal
interchanges the two horizontal eigenspaces.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4, pp. 470–471 (Sol and its isometry group).
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition,
  Propositions 5.13 and 5.22 (naturality and first-order determination of isometries).
-/

public section

noncomputable section

open Bundle Manifold VectorField CovariantDerivative
open scoped Manifold ContDiff

namespace TauCeti.Sol

local notation "P" => ℝ × ℝ × ℝ
local notation "J" => 𝓘(ℝ, P)
local notation "Z" => constantField (0, 0, 1)
local notation "∇" => leviCivitaConnection J Sol

private theorem mpullback_vertical (Φ : Isom J Sol) {ε : ℝ}
    (hd : ∀ (p : Sol) (u : TangentSpace J p),
      (tangentSpaceCastModel J (Φ p) (mfderiv J J Φ p u)).2.2 =
        ε * (tangentSpaceCastModel J p u).2.2) :
    mpullback J J Φ Z = ε • Z := by
  funext p
  apply ext_inner_right ℝ
  intro u
  rw [← Φ.inner_mfderiv p]
  rw [← RiemannianIsometry.coe_toDiffeomorph Φ,
    Φ.toDiffeomorph.mfderiv_apply_mpullback (by simp)]
  rw [RiemannianIsometry.coe_toDiffeomorph]
  simp only [inner_def, constantField_apply, ContinuousLinearEquiv.apply_symm_apply,
    Pi.smul_apply, map_smul, Prod.smul_mk, smul_eq_mul]
  simp only [mul_zero, zero_mul, zero_add, one_mul, mul_one]
  exact hd p u

private theorem derivative_commutes (Φ : Isom J Sol) {ε : ℝ}
    (hd : ∀ (p : Sol) (u : TangentSpace J p),
      (tangentSpaceCastModel J (Φ p) (mfderiv J J Φ p u)).2.2 =
        ε * (tangentSpaceCastModel J p u).2.2)
    (p : Sol) (u : P) :
    let A := fun v : P => tangentSpaceCastModel J (Φ p)
      (mfderiv J J Φ p ((tangentSpaceCastModel J p).symm v))
    ε • A (u.1, -u.2.1, 0) = ((A u).1, -(A u).2.1, 0) := by
  have h := Φ.mfderiv_leviCivitaConnection_mpullback
    (mdifferentiableAt_constantField (0, 0, 1) (Φ p))
    ((tangentSpaceCastModel J p).symm u)
  rw [mpullback_vertical Φ hd,
    ∇.isCovariantDerivativeOn.smul_const ε (mdifferentiableAt_constantField _ p)] at h
  have hread := congrArg (tangentSpaceCastModel J (Φ p)) h
  simp only [smul_apply, map_smul] at hread
  have hc (q : Sol) (v : TangentSpace J q) :
      ∇ Z q v = (tangentSpaceCastModel J q).symm
        ((tangentSpaceCastModel J q v).1, -(tangentSpaceCastModel J q v).2.1, 0) := by
    apply (tangentSpaceCastModel J q).injective
    obtain ⟨w, rfl⟩ := (tangentSpaceCastModel J q).symm.surjective v
    simp
  simpa only [hc, ContinuousLinearEquiv.apply_symm_apply] using hread

private theorem diagonal_derivative (Φ : Isom J Sol) (hfix : Φ 1 = 1)
    (hd : ∀ (p : Sol) (u : TangentSpace J p),
      (tangentSpaceCastModel J (Φ p) (mfderiv J J Φ p u)).2.2 =
        (tangentSpaceCastModel J p u).2.2) :
    ∃ a b : ℝ, (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧ ∀ u : P,
      tangentSpaceCastModel J (Φ 1)
        (mfderiv J J Φ 1 ((tangentSpaceCastModel J (1 : Sol)).symm u)) =
          (a * u.1, b * u.2.1, u.2.2) := by
  let A : P →L[ℝ] P := (tangentSpaceCastModel J (Φ 1)).toContinuousLinearMap.comp
    ((mfderiv J J Φ 1).comp (tangentSpaceCastModel J (1 : Sol)).symm.toContinuousLinearMap)
  have hz (u : P) : (A u).2.2 = u.2.2 := by
    simpa only [A, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using
      hd 1 ((tangentSpaceCastModel J (1 : Sol)).symm u)
  have hc (u : P) : A (u.1, -u.2.1, 0) = ((A u).1, -(A u).2.1, 0) := by
    simpa [A] using derivative_commutes Φ (ε := 1) (by simpa using hd) 1 u
  -- The distinct eigenvalues force each coordinate axis to be invariant.
  have h₁ : A (1, 0, 0) = ((A (1, 0, 0)).1, 0, 0) := by
    have h := congrArg (fun v : P => v.2.1) (hc (1, 0, 0))
    simp only [neg_zero] at h
    have hzero : (A (1, 0, 0)).2.1 = 0 := by linarith
    exact Prod.ext rfl (Prod.ext hzero (hz (1, 0, 0)))
  have h₂ : A (0, 1, 0) = (0, (A (0, 1, 0)).2.1, 0) := by
    have h := congrArg Prod.fst (hc (0, 1, 0))
    have hneg : A (0, -1, 0) = -A (0, 1, 0) := by
      simpa using A.map_neg (0, 1, 0)
    rw [hneg] at h
    simp only [Prod.fst_neg] at h
    exact Prod.ext (by linarith)
      (Prod.ext rfl (hz (0, 1, 0)))
  have h₃ : A (0, 0, 1) = (0, 0, 1) := by
    have h := hc (0, 0, 1)
    simp only [neg_zero] at h
    have hzero : A (0, 0, 0) = 0 := A.map_zero
    rw [hzero] at h
    exact Prod.ext (congrArg Prod.fst h).symm
      (Prod.ext (by have := congrArg (fun v : P => v.2.1) h; dsimp at this; linarith)
        (hz (0, 0, 1)))
  -- At the identity the metric is Euclidean, so the two horizontal factors are signs.
  have hnorm (u : P) : (A u).1 ^ 2 + (A u).2.1 ^ 2 + (A u).2.2 ^ 2 =
      u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2 := by
    have h := Φ.inner_mfderiv 1 ((tangentSpaceCastModel J (1 : Sol)).symm u)
      ((tangentSpaceCastModel J (1 : Sol)).symm u)
    have hzfix : (Φ 1).z = 0 := by simp [hfix]
    simp only [inner_def, hzfix, z_one, mul_zero, Real.exp_zero, one_mul,
      ContinuousLinearEquiv.apply_symm_apply] at h
    simpa only [A, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, pow_two] using h
  refine ⟨(A (1, 0, 0)).1, (A (0, 1, 0)).2.1, ?_, ?_, ?_⟩
  · have h := hnorm (1, 0, 0)
    rw [h₁] at h
    exact sq_eq_one_iff.mp (by simpa using h)
  · have h := hnorm (0, 1, 0)
    rw [h₂] at h
    exact sq_eq_one_iff.mp (by simpa using h)
  · intro u
    have hu : u = u.1 • (1, 0, 0) + u.2.1 • (0, 1, 0) + u.2.2 • (0, 0, 1) := by
      ext <;> simp
    have hA (v : P) : A v = tangentSpaceCastModel J (Φ 1)
        (mfderiv J J Φ 1 ((tangentSpaceCastModel J (1 : Sol)).symm v)) := by
      simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [← hA]
    rw [hu, map_add, map_add, map_smul, map_smul, map_smul, h₁, h₂, h₃]
    simp [mul_comm]

private theorem eq_of_diagonal_derivative (Φ Ψ : Isom J Sol) (a b : ℝ)
    (hfix : Φ 1 = 1)
    (hd : ∀ u : P, tangentSpaceCastModel J (Φ 1)
      (mfderiv J J Φ 1 ((tangentSpaceCastModel J (1 : Sol)).symm u)) =
        (a * u.1, b * u.2.1, u.2.2))
    (hΨ : ∀ p : Sol, Ψ p = mk (a * p.x) (b * p.y) p.z) : Φ = Ψ := by
  let L : P →L[ℝ] P :=
    (a • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      ((b • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).prod
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
  have hL (u : P) : L u = (a * u.1, b * u.2.1, u.2.2) := by simp [L]
  have hΨfix : Ψ 1 = 1 := by
    rw [hΨ]
    ext <;> simp
  apply Φ.ext_of_mfderiv_eq Ψ (hfix.trans hΨfix.symm)
  apply ContinuousLinearMap.ext
  intro v
  apply (tangentSpaceCastModel J (Φ 1)).injective
  have hv := hd (tangentSpaceCastModel J (1 : Sol) v)
  rw [ContinuousLinearEquiv.symm_apply_apply] at hv
  have hw := tangentSpaceCastModel_mfderiv_of_eq_linear Ψ L (fun p => by
    apply toProd.injective
    simp [hΨ, hL]) 1 v
  rw [hL] at hw
  -- Both target tangent spaces are the fibre at the identity, by the two fixed-point laws.
  convert hv.trans hw.symm using 1
  congr 1

private theorem mem_dihedral_of_preserves_height (Φ : Isom J Sol) (hfix : Φ 1 = 1)
    (hd : ∀ (p : Sol) (u : TangentSpace J p),
      (tangentSpaceCastModel J (Φ p) (mfderiv J J Φ p u)).2.2 =
        (tangentSpaceCastModel J p u).2.2) : Φ ∈ dihedralToIsom.range := by
  obtain ⟨a, b, ha, hb, hd⟩ := diagonal_derivative Φ hfix hd
  have hr : reflection ∈ dihedralToIsom.range := by
    rw [range_dihedralToIsom]
    exact Subgroup.subset_closure (by simp)
  have hs : axisSwap ∈ dihedralToIsom.range := by
    rw [range_dihedralToIsom]
    exact Subgroup.subset_closure (by simp)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · have heq : Φ = 1 := eq_of_diagonal_derivative Φ 1 1 1 hfix hd (by simp)
    rw [heq]
    exact dihedralToIsom.range.one_mem
  · have heq : Φ = reflection :=
      eq_of_diagonal_derivative Φ reflection 1 (-1) hfix hd (by simp)
    rw [heq]
    exact hr
  · have heq : Φ = axisSwap * reflection * axisSwap :=
      eq_of_diagonal_derivative Φ _ (-1) 1 hfix hd (by
        intro p; simp [RiemannianIsometry.mul_apply])
    rw [heq]
    exact dihedralToIsom.range.mul_mem (dihedralToIsom.range.mul_mem hs hr) hs
  · have heq : Φ = (reflection * axisSwap) ^ 2 :=
      eq_of_diagonal_derivative Φ _ (-1) (-1) hfix hd (by
        intro p; simp [pow_succ, RiemannianIsometry.mul_apply])
    rw [heq]
    exact dihedralToIsom.range.pow_mem (dihedralToIsom.range.mul_mem hr hs) 2

private theorem mem_dihedral_of_fixes_one (Φ : Isom J Sol) (hfix : Φ 1 = 1) :
    Φ ∈ dihedralToIsom.range := by
  obtain ⟨ε, hε, hd⟩ := exists_mfderiv_height_eq Φ
  rcases hε with rfl | rfl
  · exact mem_dihedral_of_preserves_height Φ hfix (by simpa using hd)
  · let L : P →L[ℝ] P :=
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).prod
        ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
          (-((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))))
    have hL (u : P) : L u = (u.2.1, u.1, -u.2.2) := by simp [L]
    have hswap (p : Sol) (u : TangentSpace J p) :
        tangentSpaceCastModel J (axisSwap p) (mfderiv J J axisSwap p u) =
          ((tangentSpaceCastModel J p u).2.1, (tangentSpaceCastModel J p u).1,
            -(tangentSpaceCastModel J p u).2.2) := by
      rw [← hL]
      exact tangentSpaceCastModel_mfderiv_of_eq_linear axisSwap L (fun q => by
        apply toProd.injective
        simp [hL]) p u
    have hfix' : (axisSwap * Φ) 1 = 1 := by
      ext <;> simp [RiemannianIsometry.mul_apply, hfix]
    have hd' (p : Sol) (u : TangentSpace J p) :
        (tangentSpaceCastModel J ((axisSwap * Φ) p)
          (mfderiv J J (axisSwap * Φ) p u)).2.2 =
            (tangentSpaceCastModel J p u).2.2 := by
      rw [RiemannianIsometry.coe_mul,
        mfderiv_comp_apply p (axisSwap.mdifferentiableAt _) (Φ.mdifferentiableAt p)]
      simp only [Function.comp_apply, hswap, hd, neg_mul, one_mul, neg_neg]
    have hm := mem_dihedral_of_preserves_height (axisSwap * Φ) hfix' hd'
    have hs : axisSwap ∈ dihedralToIsom.range := by
      rw [range_dihedralToIsom]
      exact Subgroup.subset_closure (by simp)
    have h := dihedralToIsom.range.mul_mem hs hm
    simpa only [← mul_assoc, axisSwap_mul_self, one_mul] using h

/-- The full isotropy group of Sol at the identity is its group of eight dihedral symmetries.
There are no additional Riemannian isometries fixing the identity. -/
theorem range_dihedralToIsom_eq_stabilizer :
    dihedralToIsom.range = MulAction.stabilizer (Isom J Sol) (1 : Sol) := by
  ext Φ
  rw [MulAction.mem_stabilizer_iff, RiemannianIsometry.smul_def]
  constructor
  · rintro ⟨g, rfl⟩
    exact dihedralToIsom_apply_one g
  · exact mem_dihedral_of_fixes_one Φ

end TauCeti.Sol

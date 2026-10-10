/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Nil.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Ext
-- Nil uses the model-space atlas; read vector-field regularity in that atlas.
import all TauCeti.Geometry.Manifold.Riemannian.Nil.Basic

/-!
# The full isometry group of Nil

The stabilizer of the identity consists exactly of the orthogonal automorphisms.
The Ricci tensor singles out the central line. Naturality of the Levi-Civita
connection then forces the sign on that line to equal the determinant of the
horizontal orthogonal map. First-order uniqueness identifies the isometry with
that automorphism. Consequently the full isometry group is `Nil ⋊ O(2)`.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4 (Nil).
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition,
  Propositions 5.13 and 5.22 (connection naturality and first-order uniqueness).
-/

public section

noncomputable section

open Bundle Filter Manifold Set Topology VectorField CovariantDerivative
open scoped Manifold ContDiff

namespace TauCeti.Nil

local notation "P" => ℝ × ℝ × ℝ
local notation "J" => 𝓘(ℝ, P)
local notation "∇" => leviCivitaConnection J Nil

local notation "Z" =>
  (fun p : Nil => ContinuousLinearEquiv.symm (tangentSpaceCastModel J p) (0, 0, 1))

private theorem smooth_central : ContMDiff J ((J).prod J) ∞ (T% Z) := by
  -- The atlas and tangent casts of this model-space synonym are identities.
  exact (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (n := ∞)
    (V := fun _ : P => (0, 0, 1))).2 contDiff_const

-- Only local constancy is needed to differentiate the pulled-back central field.
private theorem pullback_central_locally (Φ : Isom J Nil) (p : Nil) :
    ∃ c : ℝ, c ^ 2 = 1 ∧
      ∀ᶠ q in 𝓝 p, mpullback J J Φ Z q = c • Z q := by
  let W := mpullback J J Φ Z
  have hW : ContMDiff J ((J).prod J) 1 (T% W) :=
    (smooth_central.of_le (by simp)).mpullback_vectorField Φ.contMDiff
      (fun q => Φ.toDiffeomorph.isInvertible_mfderiv (by simp)) (by simp)
  let c : Nil → ℝ := fun q => (tangentSpaceCastModel J q (W q)).2.2
  have hc : Continuous c := by
    -- The vector-space criterion reads the inherited tangent atlas in global coordinates.
    exact ((contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (n := 1)).1 hW).continuous.snd.snd
  have hmap (q : Nil) : mfderiv J J Φ q (W q) = Z (Φ q) :=
    Φ.toDiffeomorph.mfderiv_apply_mpullback (by simp) Z q
  have hxy (q : Nil) : (tangentSpaceCastModel J q (W q)).1 = 0 ∧
      (tangentSpaceCastModel J q (W q)).2.1 = 0 := by
    apply (mfderiv_central_iff Φ q (W q)).mp
    simp [hmap]
  have heq (q : Nil) : W q = c q • Z q := by
    apply (tangentSpaceCastModel J q).injective
    ext <;> simp [c, (hxy q).1, (hxy q).2]
  have hsq (q : Nil) : c q ^ 2 = 1 := by
    have h := Φ.inner_mfderiv q (W q) (W q)
    rw [hmap, heq] at h
    simp only [inner_def, map_smul, ContinuousLinearEquiv.apply_symm_apply,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_zero, sub_zero,
      zero_add, mul_one] at h
    nlinarith
  refine ⟨c p, hsq p, ?_⟩
  have hconst : ∀ᶠ q in 𝓝 p, c q = c p := by
    have hglobal := isPreconnected_univ.eq_of_sq_eq hc.continuousOn
      (continuous_const.continuousOn (f := fun _ : Nil => c p))
      (fun q _ => (hsq q).trans (hsq p).symm)
      (fun _ => by intro h; have hp := hsq p; simp [h] at hp) (mem_univ p) rfl
    exact Eventually.of_forall fun q => hglobal (mem_univ q)
  filter_upwards [hconst] with q hq
  exact (heq q).trans (by rw [hq])

private def differential (Φ : Isom J Nil) : P →L[ℝ] P :=
  (tangentSpaceCastModel J (Φ 1)).toContinuousLinearMap ∘L
    mfderiv J J Φ 1 ∘L (tangentSpaceCastModel J (1 : Nil)).symm.toContinuousLinearMap

private theorem differential_symm_apply (Φ : Isom J Nil) (u : P) :
    (tangentSpaceCastModel J (Φ 1)).symm (differential Φ u) =
      mfderiv J J Φ 1 ((tangentSpaceCastModel J (1 : Nil)).symm u) := by
  simp only [differential, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

private def rotation (u : P) : P := (u.2.1 / 2, -u.1 / 2, 0)

private theorem differential_rotation (Φ : Isom J Nil) (hΦ : Φ 1 = 1) :
    ∃ c : ℝ, c ^ 2 = 1 ∧ differential Φ (0, 0, 1) = (0, 0, c) ∧ ∀ u : P,
      c • differential Φ (rotation u) = rotation (differential Φ u) := by
  obtain ⟨c, hc, heq⟩ := pullback_central_locally Φ 1
  have hZ := smooth_central.mdifferentiable (by simp)
  have hW : MDifferentiable J ((J).prod J) (T% (mpullback J J Φ Z)) :=
    hZ.mpullback_vectorField Φ.contMDiff
      (fun q => Φ.toDiffeomorph.isInvertible_mfderiv (by simp)) (by simp)
  have hcov := ∇.isCovariantDerivativeOnUniv
  have hconn := hcov.congr_of_eventuallyEq (hW 1) ((hZ 1).smul_const_section)
    (by simp) heq
  rw [hcov.smul_const c (hZ 1)] at hconn
  have hz : c • differential Φ (0, 0, 1) = (0, 0, 1) := by
    have h := Φ.toDiffeomorph.mfderiv_apply_mpullback (by simp) Z (1 : Nil)
    rw [RiemannianIsometry.coe_toDiffeomorph] at h
    rw [heq.self_of_nhds, map_smul] at h
    simpa [differential] using congrArg (tangentSpaceCastModel J (Φ 1)) h
  refine ⟨c, hc, ?_, fun u => ?_⟩
  · have h := congrArg (fun v : P => c • v) hz
    simpa [smul_smul, ← pow_two, hc] using h
  have h := Φ.mfderiv_leviCivitaConnection_mpullback (hZ (Φ 1))
    ((tangentSpaceCastModel J (1 : Nil)).symm u)
  rw [hconn, smul_apply, map_smul] at h
  have hs := congrArg (tangentSpaceCastModel J (Φ 1)) h
  have hleft := leviCivitaConnection_const_apply (1 : Nil) u (0, 0, 1)
  have hright := leviCivitaConnection_const_apply (Φ 1) (differential Φ u) (0, 0, 1)
  simp only [x_one, mul_one, mul_zero, sub_zero, zero_mul, add_zero, neg_zero,
    zero_div] at hleft
  have hx : (Φ 1).x = 0 := by simp [hΦ]
  simp only [hx, mul_one, mul_zero, sub_zero, zero_mul, add_zero, neg_zero,
    zero_div] at hright
  have hl : ∇ Z 1 ((tangentSpaceCastModel J (1 : Nil)).symm u) =
      (tangentSpaceCastModel J (1 : Nil)).symm (rotation u) := by
    apply (tangentSpaceCastModel J (1 : Nil)).injective
    simpa only [rotation, ContinuousLinearEquiv.apply_symm_apply] using hleft
  rw [hl] at hs
  rw [differential_symm_apply] at hright
  simpa only [differential, rotation, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearEquiv.coe_coe, map_smul] using hs.trans hright

private theorem differential_inner (Φ : Isom J Nil) (hΦ : Φ 1 = 1) (u v : P) :
    (differential Φ u).1 * (differential Φ v).1 +
      (differential Φ u).2.1 * (differential Φ v).2.1 +
      (differential Φ u).2.2 * (differential Φ v).2.2 =
        u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2 := by
  have h := Φ.inner_mfderiv (1 : Nil)
    ((tangentSpaceCastModel J (1 : Nil)).symm u)
    ((tangentSpaceCastModel J (1 : Nil)).symm v)
  have hx : (Φ 1).x = 0 := by simp [hΦ]
  simpa only [inner_def, hx, x_one, zero_mul, sub_zero,
    ContinuousLinearEquiv.apply_symm_apply, differential,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe] using h

private theorem exists_differential_orthogonal (Φ : Isom J Nil) (hΦ : Φ 1 = 1) :
    ∃ g : Matrix.orthogonalGroup (Fin 2) ℝ, ∀ u : P,
      differential Φ u =
        (g.1 0 0 * u.1 + g.1 0 1 * u.2.1,
          g.1 1 0 * u.1 + g.1 1 1 * u.2.1, g.1.det * u.2.2) := by
  -- Ricci preservation splits off the central line; metric preservation makes
  -- the remaining two columns orthonormal.
  obtain ⟨c, hc, hz, hr⟩ := differential_rotation Φ hΦ
  let L := differential Φ
  let e₁ : P := (1, 0, 0)
  let e₂ : P := (0, 1, 0)
  let e₃ : P := (0, 0, 1)
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  have hhor (u : P) (hu : u.2.2 = 0) : (L u).2.2 = 0 := by
    have h := differential_inner Φ hΦ u e₃
    simp only [e₃, hz, mul_zero, mul_one, zero_add, hu] at h
    exact (mul_eq_zero.mp h).resolve_right hc0
  have h₁z := hhor e₁ rfl
  have h₂z := hhor e₂ rfl
  have hmetric (u v : P) : (L u).1 * (L v).1 + (L u).2.1 * (L v).2.1 +
      (L u).2.2 * (L v).2.2 = u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2 :=
    differential_inner Φ hΦ u v
  have h₁ := hmetric e₁ e₁
  have h₂ := hmetric e₂ e₂
  have h₁₂ := hmetric e₁ e₂
  simp only [h₁z, h₂z, mul_zero, add_zero] at h₁ h₂ h₁₂
  norm_num only [e₁, e₂, mul_one, mul_zero, zero_add, add_zero] at h₁ h₂ h₁₂
  -- Connection naturality intertwines the horizontal quarter-turn with sign `c`.
  have hrot := hr e₁
  have hre : rotation e₁ = (-1 / 2 : ℝ) • e₂ := by ext <;> norm_num [rotation, e₁, e₂]
  rw [hre, map_smul] at hrot
  have hx := congrArg Prod.fst hrot
  have hy := congrArg (fun v : P => v.2.1) hrot
  simp only [rotation, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx hy
  have hcx : c * (L e₂).1 = -(L e₁).2.1 := by linarith
  have hcy : c * (L e₂).2.1 = (L e₁).1 := by linarith
  let A : Matrix (Fin 2) (Fin 2) ℝ :=
    !![(L e₁).1, (L e₂).1; (L e₁).2.1, (L e₂).2.1]
  have hA : A ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply] <;>
      nlinarith [h₁, h₂, h₁₂]
  -- This intertwining forces the horizontal determinant to equal the central sign.
  have hdet : A.det = c := by
    have h : c * A.det = 1 := by
      simp only [A, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      nlinarith [h₁]
    rcases sq_eq_one_iff.mp hc with hc | hc <;> rw [hc] at h ⊢ <;> linarith
  refine ⟨⟨A, hA⟩, fun u => ?_⟩
  have hu : u = u.1 • e₁ + u.2.1 • e₂ + u.2.2 • e₃ := by
    ext <;> simp [e₁, e₂, e₃]
  have hLu := congrArg L hu
  rw [map_add, map_add, map_smul, map_smul, map_smul] at hLu
  rw [hLu]
  ext <;> simp [A, h₁z, h₂z, hz, hdet, L, e₃] <;> ring

/-- The full stabilizer of the identity in the Riemannian isometry group of Nil
is exactly the image of its orthogonal automorphisms. -/
theorem range_orthogonalToIsom_eq_stabilizer :
    orthogonalToIsom.range = MulAction.stabilizer (Isom J Nil) (1 : Nil) := by
  apply le_antisymm range_orthogonalToIsom_le_stabilizer
  intro Φ hΦ
  have hfix : Φ 1 = 1 := by simpa using MulAction.mem_stabilizer_iff.mp hΦ
  obtain ⟨g, hg⟩ := exists_differential_orthogonal Φ hfix
  refine ⟨g, ?_⟩
  have hgfix : orthogonalToIsom g (1 : Nil) = 1 := by simp
  symm
  apply Φ.ext_of_mfderiv_eq (orthogonalToIsom g) (hfix.trans hgfix.symm)
  ext v
  apply (tangentSpaceCastModel J (Φ 1)).injective
  have h := tangentSpaceCastModel_mfderiv_orthogonalToIsom_one g v
  dsimp only at h
  have heq := hg (tangentSpaceCastModel J (1 : Nil) v)
  have hfull := heq.trans h.symm
  simp only [differential, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at hfull
  have hcast {p q : Nil} (hp : p = q) (w : TangentSpace J p) :
      tangentSpaceCastModel J p w = tangentSpaceCastModel J q w := by
    subst q
    rfl
  rw [hcast (hgfix.trans hfix.symm)] at hfull
  exact hfull

/-- Every Riemannian isometry of Nil is a left translation followed by an
orthogonal automorphism. Equivalently, the canonical semidirect-product action is surjective. -/
theorem semidirectProductToIsom_surjective : Function.Surjective semidirectProductToIsom := by
  intro Φ
  let Ψ := (toIsom (Φ 1))⁻¹ * Φ
  have hΨ : Ψ ∈ MulAction.stabilizer (Isom J Nil) (1 : Nil) := by
    simp [Ψ, MulAction.mem_stabilizer_iff, RiemannianIsometry.smul_def,
      ← map_inv, RiemannianIsometry.mul_apply]
  rw [← range_orthogonalToIsom_eq_stabilizer] at hΨ
  obtain ⟨g, hg⟩ := hΨ
  refine ⟨SemidirectProduct.inl (Φ 1) * SemidirectProduct.inr g, ?_⟩
  apply RiemannianIsometry.ext
  intro p
  have h := DFunLike.congr_fun hg p
  simpa [Ψ, semidirectProductToIsom_apply, RiemannianIsometry.mul_apply,
    ← map_inv] using congrArg (fun q : Nil => Φ 1 * q) h

/-- The full Riemannian isometry group of Nil is `Nil ⋊ O(2)`, with its canonical
translation and orthogonal actions. This is an isomorphism of groups. -/
def semidirectProductIsomMulEquiv :
    Nil ⋊[orthogonalMulAut] Matrix.orthogonalGroup (Fin 2) ℝ ≃* Isom J Nil :=
  MulEquiv.ofBijective semidirectProductToIsom
    ⟨semidirectProductToIsom_injective, semidirectProductToIsom_surjective⟩

/-- The full-group identification acts by the existing semidirect-product action. -/
@[simp]
theorem semidirectProductIsomMulEquiv_apply
    (a : Nil ⋊[orthogonalMulAut] Matrix.orthogonalGroup (Fin 2) ℝ) :
    semidirectProductIsomMulEquiv a = semidirectProductToIsom a := (rfl)

/-- The translation part recovered from an arbitrary isometry is its value at the identity. -/
@[simp]
theorem semidirectProductIsomMulEquiv_symm_apply_left (Φ : Isom J Nil) :
    (semidirectProductIsomMulEquiv.symm Φ).left = Φ 1 := by
  have h := congrArg (fun Ψ : Isom J Nil => Ψ 1)
    (semidirectProductIsomMulEquiv.apply_symm_apply Φ)
  simpa only [semidirectProductIsomMulEquiv_apply, semidirectProductToIsom_apply,
    map_one, mul_one] using h

/-- The orthogonal part recovered from an arbitrary isometry is obtained by removing
its translation by the image of the identity. -/
@[simp]
theorem orthogonalToIsom_semidirectProductIsomMulEquiv_symm_apply_right (Φ : Isom J Nil) :
    orthogonalToIsom (semidirectProductIsomMulEquiv.symm Φ).right = (toIsom (Φ 1))⁻¹ * Φ := by
  have h := semidirectProductIsomMulEquiv.apply_symm_apply Φ
  apply RiemannianIsometry.ext
  intro p
  have hp := DFunLike.congr_fun h p
  rw [semidirectProductIsomMulEquiv_apply, semidirectProductToIsom_apply,
    semidirectProductIsomMulEquiv_symm_apply_left] at hp
  simpa [RiemannianIsometry.mul_apply, ← map_inv] using
    congrArg (fun q : Nil => (Φ 1)⁻¹ * q) hp

end TauCeti.Nil

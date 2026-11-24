/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Diffeomorphism.Sphere.Frame
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Iwasawa
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Positive
import TauCeti.Geometry.Diffeomorphism.Inversion
import TauCeti.Topology.Homotopy.Contractible
import TauCeti.Topology.Instances.Matrix

/-!
# The orthogonal retraction of the diffeomorphism group of a sphere

Let `Sⁿ` be the unit sphere of `ℝⁿ⁺¹ = EuclideanSpace ℝ (Fin (n + 1))`, fix a point `p` of it, and
let `1 ≤ m`. This file builds a continuous retraction of the weak Whitney space `Diff(Sⁿ)` of
`C^m` diffeomorphisms onto the reference copy of the orthogonal group `O(n + 1)`, the image of
`TauCeti.orthogonalToDiffSphere n m`, and deduces that `Diff(Sⁿ)` is homeomorphic to `O(n + 1)`
times the fibre of the retraction over the identity.

The construction starts from the frame `TauCeti.sphereFrame p f` of a diffeomorphism `f` at `p`:
the point `f p` followed by the derivative of `f` at `p` applied to the standard basis of the
tangent model. It is a basis (`TauCeti.linearIndependent_sphereFrame_diffeomorph`), each of its
vectors depends continuously on `f` (`TauCeti.continuous_sphereFrame_diffeomorph`), and composing
`f` with an orthogonal transformation `A` applies `A` to it
(`TauCeti.sphereFrame_unitSphereEquiv_comp`). The orthogonal factor of the Iwasawa decomposition
`TauCeti.iwasawaHomeomorph` of the matrix of this frame
(`Matrix.GeneralLinearGroup.iwasawaUnitaryFactor`), that is, its Gram–Schmidt
orthonormalisation, therefore depends continuously and `O(n + 1)`-equivariantly on `f`.
Normalised to be `1` at the identity, it is the retraction
`r := TauCeti.diffSphereToOrthogonal p hm`, with

* `r (orthogonalToDiffSphere n m A * f) = A * r f`, so `r (orthogonalToDiffSphere n m A) = A`;
* `orthogonalToDiffSphere n m (r f) p = f p`: the orthogonal map it produces agrees with `f` at
  the base point.

Equivariance splits `Diff(Sⁿ)` as a product, `f ↦ (r f, (orthogonalToDiffSphere n m (r f))⁻¹ * f)`
(`TauCeti.diffSphereHomeomorphProd`), the second factor being the fibre `{f | r f = 1}`: the
diffeomorphisms fixing `p` whose frame there has the same Gram–Schmidt orthonormalisation as the
frame of the identity (`TauCeti.diffSphereToOrthogonal_eq_one_iff`). Consequently, if that
fibre is contractible, then the reference inclusion is a homotopy equivalence with homotopy inverse
`r` (`TauCeti.orthogonalToDiffSphereHomotopyEquiv`). For `n = 3` this reduces the Smale
conjecture to the contractibility of the fibre (`TauCeti.smaleConjecture_of_contractibleSpace`,
in `TauCeti.Geometry.Diffeomorphism.Smale.OrthogonalRetraction`); for `n = 2` the same reduction
applies to Smale's theorem `Diff(S²) ≃ O(3)`. This is the first step of the arguments of Smale and
Hatcher, which identify the fibre, up to homotopy, with the diffeomorphisms of the disc `Dⁿ`
fixing a neighbourhood of its boundary.

## Main definitions

* `TauCeti.diffSphereToOrthogonal p hm`: the orthogonal retraction `Diff(Sⁿ) → O(n + 1)`.
* `TauCeti.diffSphereHomeomorphProd p hm`: the homeomorphism of `Diff(Sⁿ)` with `O(n + 1)` times
  the fibre of the retraction over `1`.
* `TauCeti.orthogonalToDiffSphereHomotopyEquiv p hm`: for a contractible fibre, the reference
  inclusion as a homotopy equivalence.

## Main results

* `TauCeti.continuous_diffSphereToOrthogonal`: the retraction is continuous.
* `TauCeti.diffSphereToOrthogonal_orthogonalToDiffSphere_mul`,
  `TauCeti.diffSphereToOrthogonal_orthogonalToDiffSphere`: it is `O(n + 1)`-equivariant and a
  left inverse of the reference inclusion.
* `TauCeti.orthogonalToDiffSphere_diffSphereToOrthogonal_apply_self`: it agrees with `f` at `p`.
* `TauCeti.diffSphereToOrthogonal_eq_one_iff`: `f` lies in the fibre over `1` exactly when its
  frame is the frame of the identity times an upper triangular matrix with positive diagonal; in
  particular it fixes `p` (`TauCeti.apply_self_eq_of_diffSphereToOrthogonal_eq_one`).

## References

* S. Smale, *Diffeomorphisms of the 2-sphere*, Proc. Amer. Math. Soc. 10 (1959), 621–626.
* A. Hatcher, *A proof of the Smale conjecture, Diff(S³) ≃ O(4)*, Ann. of Math. 117 (1983),
  553–607.
-/

public section

open Metric Matrix Function
open scoped Manifold ContDiff EuclideanSpace TauCeti.ManifoldWeakWhitney
  TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {n : ℕ} {m : ℕ∞ω}

section Retraction

variable (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- The matrix whose columns are the frame of `f` at `p`. -/
private noncomputable def frameMatrix (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j ↦ (sphereFrame p f j).ofLp i

private theorem frameMatrix_apply (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (i j : Fin (n + 1)) :
    frameMatrix p f i j = (sphereFrame p f j).ofLp i :=
  rfl

private theorem col_frameMatrix (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (j : Fin (n + 1)) :
    (frameMatrix p f).col j = (sphereFrame p f j).ofLp :=
  rfl

private theorem isUnit_frameMatrix (hm : 1 ≤ m)
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    IsUnit (frameMatrix p f) :=
  linearIndependent_col_iff_isUnit.mp
    ((linearIndependent_sphereFrame_diffeomorph p hm f).map'
      (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).toLinearMap (WithLp.linearEquiv 2 ℝ _).ker)

/-- The frame matrix of a diffeomorphism, as an invertible matrix. -/
private noncomputable def frameGL (hm : 1 ≤ m)
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) : GL (Fin (n + 1)) ℝ :=
  (isUnit_frameMatrix p hm f).unit

private theorem coe_frameGL (hm : 1 ≤ m)
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    (frameGL p hm f : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = frameMatrix p f :=
  rfl

private theorem continuous_frameGL (hm : 1 ≤ m) : Continuous (frameGL (m := m) p hm) := by
  refine IsOpenUnits.isOpenEmbedding_unitsVal.isEmbedding.isInducing.continuous_iff.mpr
    (continuous_matrix fun i j ↦ ?_)
  exact (continuous_apply i).comp
    ((PiLp.continuous_ofLp 2 _).comp (continuous_sphereFrame_diffeomorph p hm j))

/-- Composing with an orthogonal transformation multiplies the frame matrix by it. -/
private theorem frameGL_orthogonalToDiffSphere_mul (hm : 1 ≤ m)
    (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    frameGL p hm (orthogonalToDiffSphere n m A * f) = Unitary.toUnits A * frameGL p hm f := by
  refine Units.ext ?_
  have hcoe : ⇑(orthogonalToDiffSphere n m A * f) =
      (UnitaryGroup.toLinearIsometryEquiv A).unitSphereEquiv ∘ f := by
    rw [Diffeomorph.coe_mul, coe_orthogonalToDiffSphere]
  rw [Units.val_mul, Unitary.val_toUnits_apply, coe_frameGL, coe_frameGL]
  ext i j
  rw [frameMatrix_apply, hcoe, sphereFrame_unitSphereEquiv_comp, Function.comp_apply,
    UnitaryGroup.toLinearIsometryEquiv_apply, WithLp.ofLp_toLp, ← col_frameMatrix]
  exact congrFun col_mul_eq_mulVec_col.symm i

/-- The first column of the orthogonal factor of the frame matrix is `f p`. -/
private theorem col_zero_iwasawaUnitaryFactor_frameGL (hm : 1 ≤ m)
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    ((frameGL p hm f).iwasawaUnitaryFactor : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).col 0 =
      (f p : EuclideanSpace ℝ (Fin (n + 1))).ofLp := by
  have hcol : (frameGL p hm f : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).col 0 =
      (f p : EuclideanSpace ℝ (Fin (n + 1))).ofLp := by
    rw [coe_frameGL, col_frameMatrix, sphereFrame_zero]
  refine ((frameGL p hm f).col_zero_iwasawaUnitaryFactor ?_).trans hcol
  have h := EuclideanSpace.inner_eq_star_dotProduct (f p : EuclideanSpace ℝ (Fin (n + 1)))
    (f p : EuclideanSpace ℝ (Fin (n + 1)))
  rw [star_trivial, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, one_pow] at h
  rw [hcol, star_trivial, ← h]

/-- **The orthogonal retraction of the diffeomorphism group of a sphere.** For `1 ≤ m` and a point
`p` of `Sⁿ`, it sends a `C^m` diffeomorphism `f` to the orthogonal factor of the frame of `f` at `p`
(the Gram–Schmidt orthonormalisation of `f p` and of the derivative of `f` at `p`), corrected by
that of the identity so that the identity goes to `1`. It is continuous
(`TauCeti.continuous_diffSphereToOrthogonal`), equivariant
(`TauCeti.diffSphereToOrthogonal_orthogonalToDiffSphere_mul`), a left inverse of the reference
inclusion (`TauCeti.diffSphereToOrthogonal_orthogonalToDiffSphere`), and its value agrees with `f`
at `p` (`TauCeti.orthogonalToDiffSphere_diffSphereToOrthogonal_apply_self`). -/
noncomputable def diffSphereToOrthogonal (hm : 1 ≤ m)
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    Matrix.orthogonalGroup (Fin (n + 1)) ℝ :=
  (frameGL p hm f).iwasawaUnitaryFactor * (frameGL p hm 1).iwasawaUnitaryFactor⁻¹

variable (hm : 1 ≤ m)

/-- The orthogonal retraction is continuous for the weak Whitney topology. -/
theorem continuous_diffSphereToOrthogonal :
    Continuous (diffSphereToOrthogonal (n := n) (m := m) p hm) :=
  (GeneralLinearGroup.continuous_iwasawaUnitaryFactor.comp (continuous_frameGL p hm)).mul
    continuous_const

/-- The orthogonal retraction is equivariant for left multiplication by orthogonal maps. -/
theorem diffSphereToOrthogonal_orthogonalToDiffSphere_mul
    (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    diffSphereToOrthogonal p hm (orthogonalToDiffSphere n m A * f) =
      A * diffSphereToOrthogonal p hm f := by
  simp only [diffSphereToOrthogonal, frameGL_orthogonalToDiffSphere_mul,
    GeneralLinearGroup.iwasawaUnitaryFactor_toUnits_mul, mul_assoc]

/-- The orthogonal retraction sends the identity to `1`. -/
@[simp]
theorem diffSphereToOrthogonal_one : diffSphereToOrthogonal (n := n) (m := m) p hm 1 = 1 :=
  mul_inv_cancel _

/-- The orthogonal retraction is a left inverse of the reference inclusion
`O(n + 1) → Diff(Sⁿ)`. Not a simp lemma: `TauCeti.orthogonalToDiffSphere_apply` unfolds the
inclusion first. -/
theorem diffSphereToOrthogonal_orthogonalToDiffSphere (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
    diffSphereToOrthogonal p hm (orthogonalToDiffSphere n m A) = A := by
  simpa using diffSphereToOrthogonal_orthogonalToDiffSphere_mul p hm A 1

/-- The orthogonal map produced by the retraction agrees with the diffeomorphism at the base
point. Not a simp lemma, for the same reason as
`TauCeti.diffSphereToOrthogonal_orthogonalToDiffSphere`. -/
theorem orthogonalToDiffSphere_diffSphereToOrthogonal_apply_self
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    orthogonalToDiffSphere n m (diffSphereToOrthogonal p hm f) p = f p := by
  set K₁ := (frameGL p hm 1).iwasawaUnitaryFactor
  -- `K₁` sends `e₀` to `p`, and `r f * K₁`, the orthogonal factor of the frame of `f`, to `f p`.
  have hp : (p : EuclideanSpace ℝ (Fin (n + 1))).ofLp =
      (K₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *ᵥ Pi.single 0 1 := by
    rw [mulVec_single_one, col_zero_iwasawaUnitaryFactor_frameGL, Diffeomorph.one_apply]
  have hK : diffSphereToOrthogonal p hm f * K₁ = (frameGL p hm f).iwasawaUnitaryFactor :=
    inv_mul_cancel_right _ _
  apply Subtype.ext
  apply WithLp.ofLp_injective
  rw [ofLp_orthogonalToDiffSphere_apply, hp, mulVec_mulVec, ← Submonoid.coe_mul, hK,
    mulVec_single_one, col_zero_iwasawaUnitaryFactor_frameGL]

/-- A diffeomorphism in the fibre of the orthogonal retraction over `1` fixes the base point. -/
theorem apply_self_eq_of_diffSphereToOrthogonal_eq_one
    {f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m}
    (hf : diffSphereToOrthogonal p hm f = 1) : f p = p := by
  rw [← orthogonalToDiffSphere_diffSphereToOrthogonal_apply_self p hm f, hf, map_one,
    Diffeomorph.one_apply]

/-- Two frames are related by a matrix `B` exactly when the frame matrices are. -/
private theorem frameMatrix_eq_mul_iff
    (f g : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    frameMatrix p f = frameMatrix p g * B ↔
      ∀ j, sphereFrame p f j = ∑ i, B i j • sphereFrame p g i := by
  refine ⟨fun h j ↦ WithLp.ofLp_injective (p := 2) (V := Fin (n + 1) → ℝ) ?_, fun h ↦ ?_⟩
  · funext k
    have hkj := congrFun (congrFun h k) j
    rw [frameMatrix_apply, Matrix.mul_apply] at hkj
    simp only [hkj, frameMatrix_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm]
  · ext k j
    rw [frameMatrix_apply, Matrix.mul_apply, h j]
    simp only [frameMatrix_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **The fibre of the orthogonal retraction.** A diffeomorphism `f` is sent to `1` exactly when
its frame at `p` is obtained from the frame of the identity by an upper triangular matrix with
positive diagonal, that is, when the two frames have the same Gram–Schmidt orthonormalisation.
In particular `f p = p` (`TauCeti.apply_self_eq_of_diffSphereToOrthogonal_eq_one`). -/
theorem diffSphereToOrthogonal_eq_one_iff
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    diffSphereToOrthogonal p hm f = 1 ↔
      ∃ b ∈ posUpperTriangularGroup (Fin (n + 1)) ℝ, ∀ j,
        sphereFrame p f j =
          ∑ i, (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j • sphereFrame p id i := by
  set K₁ := ((iwasawaHomeomorph ℝ (n + 1)).symm (frameGL p hm 1)).1
  have hK₁ : (K₁ : GL (Fin (n + 1)) ℝ) ∈ unitarySubgroup (GL (Fin (n + 1)) ℝ) := K₁.property
  -- `r f = 1` says that `f` and the identity have the same orthogonal factor `K₁`.
  have hr : diffSphereToOrthogonal p hm f = 1 ↔
      (((iwasawaHomeomorph ℝ (n + 1)).symm (frameGL p hm f)).1 : GL (Fin (n + 1)) ℝ) = K₁ := by
    rw [diffSphereToOrthogonal, mul_inv_eq_one, Subtype.ext_iff,
      GeneralLinearGroup.coe_iwasawaUnitaryFactor, GeneralLinearGroup.coe_iwasawaUnitaryFactor,
      Units.val_inj]
  -- The triangular factor of the identity's frame.
  have hb₁ : (K₁ : GL (Fin (n + 1)) ℝ)⁻¹ * frameGL p hm 1 ∈
      posUpperTriangularGroup (Fin (n + 1)) ℝ :=
    PosUpperTriangularGroup.mem_iff.mpr
      ((iwasawaHomeomorph_symm_unitary_eq_iff (frameGL p hm 1) K₁ hK₁).mp rfl)
  have hframe (b : GL (Fin (n + 1)) ℝ) : frameGL p hm f = frameGL p hm 1 * b ↔
      ∀ j, sphereFrame p f j = ∑ i, (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j •
        sphereFrame p id i := by
    rw [← frameMatrix_eq_mul_iff, ← Units.val_inj, Units.val_mul, coe_frameGL, coe_frameGL,
      Diffeomorph.coe_one]
  rw [hr, iwasawaHomeomorph_symm_unitary_eq_iff _ _ hK₁, ← PosUpperTriangularGroup.mem_iff]
  constructor
  · intro h
    refine ⟨(frameGL p hm 1)⁻¹ * frameGL p hm f, ?_, (hframe _).mp (mul_inv_cancel_left _ _).symm⟩
    have := mul_mem (inv_mem hb₁) h
    rwa [_root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at this
  · rintro ⟨b, hb, hfb⟩
    rw [(hframe b).mpr hfb, ← mul_assoc]
    exact mul_mem hb₁ hb

end Retraction

section Product

variable (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (hm : 1 ≤ m)

/-- **`Diff(Sⁿ)` is `O(n + 1)` times the fibre of the orthogonal retraction.** The homeomorphism
sends `f` to `(r f, A⁻¹ f)`, where `r f = diffSphereToOrthogonal p hm f` and `A` is the
diffeomorphism induced by `r f`; its inverse multiplies the two factors. -/
noncomputable def diffSphereHomeomorphProd :
    Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m ≃ₜ
      Matrix.orthogonalGroup (Fin (n + 1)) ℝ ×
        {f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m //
          diffSphereToOrthogonal p hm f = 1} where
  toFun f := (diffSphereToOrthogonal p hm f,
    ⟨(orthogonalToDiffSphere n m (diffSphereToOrthogonal p hm f))⁻¹ * f, by
      rw [← map_inv, diffSphereToOrthogonal_orthogonalToDiffSphere_mul, inv_mul_cancel]⟩)
  invFun x := orthogonalToDiffSphere n m x.1 * x.2
  left_inv f := mul_inv_cancel_left _ _
  right_inv := by
    rintro ⟨A, g, hg⟩
    have hA : diffSphereToOrthogonal p hm (orthogonalToDiffSphere n m A * g) = A := by
      rw [diffSphereToOrthogonal_orthogonalToDiffSphere_mul, hg, mul_one]
    ext : 1
    · exact hA
    · exact Subtype.ext (by simp only [hA, inv_mul_cancel_left])
  continuous_toFun := by
    have hr := continuous_diffSphereToOrthogonal (n := n) (m := m) p hm
    exact hr.prodMk ((((continuous_orthogonalToDiffSphere n m).comp hr).inv.mul
      continuous_id).subtype_mk _)
  continuous_invFun :=
    ((continuous_orthogonalToDiffSphere n m).comp continuous_fst).mul
      (continuous_subtypeVal.comp continuous_snd)

@[simp]
theorem diffSphereHomeomorphProd_apply_fst
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    (diffSphereHomeomorphProd p hm f).1 = diffSphereToOrthogonal p hm f :=
  (rfl)

@[simp]
theorem coe_diffSphereHomeomorphProd_apply_snd
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    ((diffSphereHomeomorphProd p hm f).2 : Diff (𝓡 n) _ m) =
      (orthogonalToDiffSphere n m (diffSphereToOrthogonal p hm f))⁻¹ * f :=
  (rfl)

@[simp]
theorem diffSphereHomeomorphProd_symm_apply
    (x : Matrix.orthogonalGroup (Fin (n + 1)) ℝ ×
      {f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m //
        diffSphereToOrthogonal p hm f = 1}) :
    (diffSphereHomeomorphProd p hm).symm x = orthogonalToDiffSphere n m x.1 * x.2 :=
  (rfl)

/-- **The reference inclusion is a homotopy equivalence if the fibre is contractible.** If the
fibre over `1` of the orthogonal retraction is contractible, then the reference inclusion
`O(n + 1) → Diff(Sⁿ)` is a homotopy equivalence, with homotopy inverse the retraction. -/
noncomputable def orthogonalToDiffSphereHomotopyEquiv
    [ContractibleSpace {f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m //
      diffSphereToOrthogonal p hm f = 1}] :
    ContinuousMap.HomotopyEquiv (Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
      (Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) where
  toFun := continuousOrthogonalToDiffSphere n m
  invFun := ⟨diffSphereToOrthogonal p hm, continuous_diffSphereToOrthogonal p hm⟩
  left_inv := by
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id (Matrix.orthogonalGroup (Fin (n + 1)) ℝ))
    ext1 A
    rw [ContinuousMap.comp_apply, continuousOrthogonalToDiffSphere_apply, ContinuousMap.coe_mk,
      ContinuousMap.id_apply]
    exact diffSphereToOrthogonal_orthogonalToDiffSphere p hm A
  right_inv := by
    let Φ := diffSphereHomeomorphProd p hm
    let o : {f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m //
        diffSphereToOrthogonal p hm f = 1} := ⟨1, diffSphereToOrthogonal_one p hm⟩
    -- The fibre is contractible, so its identity is homotopic to the constant map at `1`.
    have hF : (ContinuousMap.const _ o).Homotopic (ContinuousMap.id _) :=
      ContinuousMap.homotopic_of_contractibleSpace _ _
    -- Transport `id × const 1 ≃ id` along the product decomposition `Φ`.
    have h := (ContinuousMap.Homotopic.refl (⟨Φ.symm, Φ.symm.continuous⟩ : C(_, _))).comp
      ((((ContinuousMap.Homotopic.refl (ContinuousMap.id _)).prodMap hF)).comp
        (ContinuousMap.Homotopic.refl (⟨Φ, Φ.continuous⟩ : C(_, _))))
    convert h using 1 <;> ext1 f
    · simp [Φ, o]
    · simp [Φ]

/-- The homotopy equivalence `TauCeti.orthogonalToDiffSphereHomotopyEquiv` is the reference
inclusion. -/
@[simp]
theorem orthogonalToDiffSphereHomotopyEquiv_toFun
    [ContractibleSpace {f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m //
      diffSphereToOrthogonal p hm f = 1}] :
    (orthogonalToDiffSphereHomotopyEquiv p hm).toFun = continuousOrthogonalToDiffSphere n m :=
  (rfl)

/-- The homotopy inverse in `TauCeti.orthogonalToDiffSphereHomotopyEquiv` is the orthogonal
retraction. -/
@[simp]
theorem coe_orthogonalToDiffSphereHomotopyEquiv_symm
    [ContractibleSpace {f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m //
      diffSphereToOrthogonal p hm f = 1}] :
    ⇑(orthogonalToDiffSphereHomotopyEquiv p hm).symm = diffSphereToOrthogonal p hm :=
  (rfl)

end Product

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Diffeomorphism.Sphere.Frame
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Iwasawa
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Positive
import TauCeti.Geometry.Diffeomorphism.Inversion
import Mathlib.Topology.Algebra.Star.Unitary
import TauCeti.Topology.Algebra.Group.EquivariantSplitting
import TauCeti.Topology.Homotopy.HomotopyEquiv
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
vectors depends continuously on `f` (`TauCeti.continuous_sphereFrame_diffeomorph`), and
postcomposing `f` with an orthogonal transformation `A`, that is, passing to `A ∘ f`, applies `A` to
every frame vector (`TauCeti.sphereFrame_unitSphereEquiv_comp`). The orthogonal factor of the
Iwasawa decomposition `TauCeti.iwasawaHomeomorph` of the matrix of this frame
(`Matrix.GeneralLinearGroup.iwasawaUnitaryFactor`), that is, its Gram–Schmidt
orthonormalisation, therefore depends continuously and `O(n + 1)`-equivariantly on `f`.
Normalised to be `1` at the identity, it is the retraction
`r := TauCeti.diffSphereToOrthogonal p hm`, with

* `r (orthogonalToDiffSphere n m A * f) = A * r f`, so `r (orthogonalToDiffSphere n m A) = A`;
* `orthogonalToDiffSphere n m (r f) p = f p`: the orthogonal map it produces agrees with `f` at
  the base point.

Equivariance splits `Diff(Sⁿ)` as a product, `f ↦ (r f, (orthogonalToDiffSphere n m (r f))⁻¹ * f)`
(`TauCeti.diffSphereHomeomorphProd`, an instance of the general splitting
`TauCeti.homeomorphProdFiber` along an equivariant map to the acting group), the second factor
being the fibre `{f | r f = 1}`: the diffeomorphisms fixing `p` whose frame there has the same
Gram–Schmidt orthonormalisation as the frame of the identity
(`TauCeti.diffSphereToOrthogonal_eq_one_iff`). Consequently, if that fibre is contractible, then
the reference inclusion is a homotopy equivalence with homotopy inverse `r`
(`TauCeti.orthogonalToDiffSphereHomotopyEquiv`), since a product with a contractible factor
deforms onto a slice (`ContinuousMap.HomotopyEquiv.prodContractibleAt`). For `n = 3` this reduces
the Smale conjecture to the contractibility of the fibre
(`TauCeti.smaleConjecture_of_contractibleSpace`, in
`TauCeti.Geometry.Diffeomorphism.Smale.OrthogonalRetraction`); for `n = 2` the same reduction
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
  particular it fixes `p` (`TauCeti.apply_eq_self_of_diffSphereToOrthogonal_eq_one`), and every
  diffeomorphism equal to the identity near `p` lies in it
  (`TauCeti.diffSphereToOrthogonal_eq_one_of_eventuallyEq_id`).

## References

* S. Smale, *Diffeomorphisms of the 2-sphere*, Proc. Amer. Math. Soc. 10 (1959), 621–626.
* A. Hatcher, *A proof of the Smale conjecture, Diff(S³) ≃ O(4)*, Ann. of Math. 117 (1983),
  553–607.
-/

public section

open Metric Matrix Function Filter
open scoped Manifold ContDiff EuclideanSpace Topology TauCeti.ManifoldWeakWhitney
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
    IsUnit (frameMatrix p f) := by
  have hcol : (frameMatrix p f).col =
      (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).toLinearMap ∘ sphereFrame p f :=
    funext fun j ↦ (col_frameMatrix p f j).trans (WithLp.linearEquiv_apply 2 ℝ _ _).symm
  rw [← linearIndependent_col_iff_isUnit, hcol]
  exact (linearIndependent_sphereFrame_diffeomorph p hm f).map' _ (WithLp.linearEquiv 2 ℝ _).ker

/-- The frame matrix of a diffeomorphism, as an invertible matrix. -/
private noncomputable def frameGL (hm : 1 ≤ m)
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) : GL (Fin (n + 1)) ℝ :=
  (isUnit_frameMatrix p hm f).unit

private theorem coe_frameGL (hm : 1 ≤ m)
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    (frameGL p hm f : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = frameMatrix p f :=
  (isUnit_frameMatrix p hm f).unit_spec

private theorem continuous_frameGL (hm : 1 ≤ m) : Continuous (frameGL (m := m) p hm) := by
  refine IsOpenUnits.isOpenEmbedding_unitsVal.isEmbedding.isInducing.continuous_iff.mpr
    (continuous_matrix fun i j ↦ ?_)
  simp only [Function.comp_apply, coe_frameGL, frameMatrix_apply]
  exact (continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp
    ((continuous_apply j).comp (continuous_sphereFrame_diffeomorph p hm)))

/-- Composing with an orthogonal transformation multiplies the frame matrix by it. -/
private theorem frameGL_orthogonalToDiffSphere_mul (hm : 1 ≤ m)
    (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    frameGL p hm (orthogonalToDiffSphere n m A * f) = Unitary.toUnits A * frameGL p hm f := by
  refine Units.ext ?_
  have hcoe : ⇑(orthogonalToDiffSphere n m A * f) =
      (UnitaryGroup.toLinearIsometryEquiv A).unitSphereEquiv ∘ f := by
    rw [Diffeomorph.coe_mul, coe_orthogonalToDiffSphere]
  rw [Units.val_mul, Unitary.val_toUnits_apply, coe_frameGL, coe_frameGL, ← col_inj]
  -- Column by column: the `j`-th frame vector of `A ∘ f` is `A` applied to that of `f`.
  funext j
  rw [col_mul_eq_mulVec_col, col_frameMatrix, col_frameMatrix, hcoe,
    sphereFrame_unitSphereEquiv_comp, Function.comp_apply,
    UnitaryGroup.toLinearIsometryEquiv_apply, WithLp.ofLp_toLp]

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

/-- The matrix of frame coordinates `v` against the frame of `g` gives the corresponding linear
combination of the frame vectors. -/
private theorem frameMatrix_mulVec
    (g : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (v : Fin (n + 1) → ℝ) :
    frameMatrix p g *ᵥ v = (∑ i, v i • sphereFrame p g i).ofLp := by
  rw [mulVec_eq_sum, WithLp.ofLp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [op_smul_eq_smul, WithLp.ofLp_smul, ← col_frameMatrix, col_def]

variable (hm : 1 ≤ m)

/-- The orthogonal retraction is continuous for the weak Whitney topology. -/
theorem continuous_diffSphereToOrthogonal :
    Continuous (diffSphereToOrthogonal (n := n) (m := m) p hm) :=
  (GeneralLinearGroup.continuous_iwasawaUnitaryFactor.comp (continuous_frameGL p hm)).mul
    continuous_const

/-- The orthogonal retraction is equivariant for left multiplication by orthogonal maps. -/
@[simp]
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
`O(n + 1) → Diff(Sⁿ)`. -/
@[simp]
theorem diffSphereToOrthogonal_orthogonalToDiffSphere (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
    diffSphereToOrthogonal p hm (orthogonalToDiffSphere n m A) = A := by
  simpa using diffSphereToOrthogonal_orthogonalToDiffSphere_mul p hm A 1

/-- The orthogonal map produced by the retraction agrees with the diffeomorphism at the base
point. -/
@[simp]
theorem orthogonalToDiffSphere_diffSphereToOrthogonal_apply_self
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    orthogonalToDiffSphere n m (diffSphereToOrthogonal p hm f) p = f p := by
  set K₁ := (frameGL p hm 1).iwasawaUnitaryFactor
  -- `r f * K₁` is the orthogonal factor of the frame of `f`.
  have hK : diffSphereToOrthogonal p hm f * K₁ = (frameGL p hm f).iwasawaUnitaryFactor :=
    inv_mul_cancel_right _ _
  apply Subtype.ext
  apply WithLp.ofLp_injective
  -- `K₁` sends `e₀` to `p`, and `r f * K₁` sends it to `f p`.
  calc (orthogonalToDiffSphere n m (diffSphereToOrthogonal p hm f) p :
          EuclideanSpace ℝ (Fin (n + 1))).ofLp
      = (diffSphereToOrthogonal p hm f : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *ᵥ
          (p : EuclideanSpace ℝ (Fin (n + 1))).ofLp :=
        ofLp_orthogonalToDiffSphere_apply n m _ p
    _ = (diffSphereToOrthogonal p hm f : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *ᵥ
          ((K₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *ᵥ Pi.single 0 1) := by
        rw [mulVec_single_one, col_zero_iwasawaUnitaryFactor_frameGL, Diffeomorph.one_apply]
    _ = ((diffSphereToOrthogonal p hm f * K₁ : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *ᵥ Pi.single 0 1 := by
        rw [mulVec_mulVec, Submonoid.coe_mul]
    _ = (f p : EuclideanSpace ℝ (Fin (n + 1))).ofLp := by
        rw [hK, mulVec_single_one, col_zero_iwasawaUnitaryFactor_frameGL]

/-- A diffeomorphism in the fibre of the orthogonal retraction over `1` fixes the base point. -/
theorem apply_eq_self_of_diffSphereToOrthogonal_eq_one
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
  -- Column by column, through the coordinates `ofLp` of `ℝⁿ⁺¹`.
  rw [← col_inj, funext_iff]
  refine forall_congr' fun j ↦ ?_
  rw [col_mul_eq_mulVec_col, col_frameMatrix, frameMatrix_mulVec,
    (WithLp.ofLp_injective 2).eq_iff]
  simp only [col_apply]

/-- **The fibre of the orthogonal retraction.** A diffeomorphism `f` is sent to `1` exactly when
its frame at `p` is obtained from the frame of the identity by an upper triangular matrix with
positive diagonal, that is, when the two frames have the same Gram–Schmidt orthonormalisation.
In particular `f p = p` (`TauCeti.apply_eq_self_of_diffSphereToOrthogonal_eq_one`). -/
theorem diffSphereToOrthogonal_eq_one_iff
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    diffSphereToOrthogonal p hm f = 1 ↔
      ∃ b ∈ posUpperTriangularGroup (Fin (n + 1)) ℝ, ∀ j,
        sphereFrame p f j =
          ∑ i, (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j • sphereFrame p id i := by
  -- `r f = 1` says that the frame matrices of `f` and of the identity have the same orthogonal
  -- factor, that is, they differ by a positive upper triangular matrix.
  rw [diffSphereToOrthogonal, mul_inv_eq_one,
    GeneralLinearGroup.iwasawaUnitaryFactor_eq_iwasawaUnitaryFactor_iff]
  have hframe (b : GL (Fin (n + 1)) ℝ) : frameGL p hm f = frameGL p hm 1 * b ↔
      ∀ j, sphereFrame p f j = ∑ i, (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j •
        sphereFrame p id i := by
    rw [← frameMatrix_eq_mul_iff, ← Units.val_inj, Units.val_mul, coe_frameGL, coe_frameGL,
      Diffeomorph.coe_one]
  refine ⟨fun h ↦ ⟨_, h, (hframe _).mp (mul_inv_cancel_left _ _).symm⟩, ?_⟩
  rintro ⟨b, hb, hfb⟩
  rwa [(hframe b).mpr hfb, inv_mul_cancel_left]

/-- A diffeomorphism equal to the identity near `p` lies in the fibre of the orthogonal retraction
over `1`: its frame at `p` is the frame of the identity. -/
theorem diffSphereToOrthogonal_eq_one_of_eventuallyEq_id
    {f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m} (hf : ⇑f =ᶠ[𝓝 p] id) :
    diffSphereToOrthogonal p hm f = 1 :=
  (diffSphereToOrthogonal_eq_one_iff p hm f).mpr
    ⟨1, one_mem _, fun j ↦ by simp [hf.sphereFrame_eq, Matrix.one_apply]⟩

end Retraction

section Product

variable (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (hm : 1 ≤ m)

/-- The action of `O(n + 1)` on `Diff(Sⁿ)` by left multiplication through the reference
inclusion. -/
private noncomputable abbrev orthogonalMulAction :
    MulAction (Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
      (Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :=
  MulAction.compHom _ (orthogonalToDiffSphere n m)

attribute [local instance] orthogonalMulAction

private theorem continuousSMul_orthogonalMulAction :
    ContinuousSMul (Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
      (Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :=
  ⟨((continuous_orthogonalToDiffSphere n m).comp continuous_fst).mul continuous_snd⟩

attribute [local instance] continuousSMul_orthogonalMulAction

/-- **`Diff(Sⁿ)` is `O(n + 1)` times the fibre of the orthogonal retraction.** The homeomorphism
sends `f` to `(r f, A⁻¹ f)`, where `r f = diffSphereToOrthogonal p hm f` and `A` is the
diffeomorphism induced by `r f`; its inverse multiplies the two factors. It is the splitting
`TauCeti.homeomorphProdFiber` for the action of `O(n + 1)` on `Diff(Sⁿ)` by left multiplication
through the reference inclusion, along the equivariant retraction. -/
noncomputable def diffSphereHomeomorphProd :
    Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m ≃ₜ
      Matrix.orthogonalGroup (Fin (n + 1)) ℝ ×
        {f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m //
          diffSphereToOrthogonal p hm f = 1} :=
  homeomorphProdFiber (diffSphereToOrthogonal p hm) (continuous_diffSphereToOrthogonal p hm)
    (diffSphereToOrthogonal_orthogonalToDiffSphere_mul p hm)

@[simp]
theorem diffSphereHomeomorphProd_apply_fst
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    (diffSphereHomeomorphProd p hm f).1 = diffSphereToOrthogonal p hm f :=
  homeomorphProdFiber_apply_fst _ _ _ f

@[simp]
theorem coe_diffSphereHomeomorphProd_apply_snd
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    ((diffSphereHomeomorphProd p hm f).2 : Diff (𝓡 n) _ m) =
      (orthogonalToDiffSphere n m (diffSphereToOrthogonal p hm f))⁻¹ * f :=
  (coe_homeomorphProdFiber_apply_snd _ _ _ f).trans
    (congrArg (· * f) (map_inv (orthogonalToDiffSphere n m) _))

@[simp]
theorem diffSphereHomeomorphProd_symm_apply
    (x : Matrix.orthogonalGroup (Fin (n + 1)) ℝ ×
      {f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m //
        diffSphereToOrthogonal p hm f = 1}) :
    (diffSphereHomeomorphProd p hm).symm x = orthogonalToDiffSphere n m x.1 * x.2 :=
  homeomorphProdFiber_symm_apply _ _ _ x

/-- **The reference inclusion is a homotopy equivalence if the fibre is contractible.** If the
fibre over `1` of the orthogonal retraction is contractible, then the reference inclusion
`O(n + 1) → Diff(Sⁿ)` is a homotopy equivalence, with homotopy inverse the retraction: it is the
slice of `O(n + 1)` at the identity of the fibre
(`ContinuousMap.HomotopyEquiv.prodContractibleAt`), followed by the product decomposition
`TauCeti.diffSphereHomeomorphProd`. -/
noncomputable def orthogonalToDiffSphereHomotopyEquiv
    [ContractibleSpace {f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m //
      diffSphereToOrthogonal p hm f = 1}] :
    ContinuousMap.HomotopyEquiv (Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
      (Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :=
  (ContinuousMap.HomotopyEquiv.prodContractibleAt _ ⟨1, diffSphereToOrthogonal_one p hm⟩).trans
    (diffSphereHomeomorphProd p hm).symm.toHomotopyEquiv

/-- The homotopy equivalence `TauCeti.orthogonalToDiffSphereHomotopyEquiv` is the reference
inclusion. -/
@[simp]
theorem orthogonalToDiffSphereHomotopyEquiv_toFun
    [ContractibleSpace {f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m //
      diffSphereToOrthogonal p hm f = 1}] :
    (orthogonalToDiffSphereHomotopyEquiv p hm).toFun = continuousOrthogonalToDiffSphere n m :=
  ContinuousMap.ext fun A ↦ by
    change (diffSphereHomeomorphProd p hm).symm
      (ContinuousMap.HomotopyEquiv.prodContractibleAt _ ⟨1, diffSphereToOrthogonal_one p hm⟩ A) = _
    rw [ContinuousMap.HomotopyEquiv.prodContractibleAt_apply, diffSphereHomeomorphProd_symm_apply,
      continuousOrthogonalToDiffSphere_apply, mul_one]

/-- The homotopy inverse in `TauCeti.orthogonalToDiffSphereHomotopyEquiv` is the orthogonal
retraction. -/
@[simp]
theorem coe_orthogonalToDiffSphereHomotopyEquiv_symm
    [ContractibleSpace {f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m //
      diffSphereToOrthogonal p hm f = 1}] :
    ⇑(orthogonalToDiffSphereHomotopyEquiv p hm).symm = diffSphereToOrthogonal p hm :=
  funext fun f ↦ by simp [orthogonalToDiffSphereHomotopyEquiv]

end Product

end TauCeti

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.RepresentationTheory.InvariantForm
import TauCeti.LinearAlgebra.BilinearForm.Isometry.InvariantForm
import TauCeti.LinearAlgebra.BilinearForm.Isotropic

/-!
# The standard representation of the symplectic group

This file restricts the standard representation of the general linear group to the symplectic
group. It defines the standard alternating form from `Matrix.J`, proves that the standard action
preserves it, and packages the resulting equivariant self-duality. It also shows that the
symplectic group acts transitively on the isotropic subspaces of each dimension, and that over a
field the standard form spans its invariant bilinear forms.

## Main definitions

* `TauCeti.symplecticGroupToGL` is the canonical inclusion into the general linear group.
* `TauCeti.stdSymplecticRep` is the standard representation of `Matrix.symplecticGroup`.
* `TauCeti.stdSymplecticBilinForm` is the nondegenerate invariant alternating form; its value on
  a pair of standard basis vectors is `TauCeti.stdSymplecticBilinForm_single_single`, and its value
  against the all-ones vector is `TauCeti.stdSymplecticBilinForm_one_right`.
* `TauCeti.stdSymplecticRepEquivDual` is the induced equivariant self-duality.

## Main results

* `TauCeti.exists_map_stdSymplecticRep_eq`: `Sp₂ₙ(k)` acts transitively on the isotropic subspaces
  of each dimension. It follows from the transitivity of isometries on isotropic subspaces,
  `LinearMap.BilinForm.IsAlt.exists_isometryEquiv_map_eq`.
* `TauCeti.isInvariantForm_stdSymplecticBilinForm`: the standard form is invariant.
* `TauCeti.toMatrix'_mem_symplecticGroup_iff`: a linear endomorphism of `k^(2n)` has a symplectic
  matrix exactly when it preserves the standard alternating form.
* `TauCeti.exists_eq_smul_stdSymplecticBilinForm` and
  `TauCeti.invariantForms_stdSymplecticRep_eq_span_stdSymplecticBilinForm`:
  over a field, every `Sp₂ₙ(k)`-invariant bilinear form is a multiple of the standard one. Its
  invariance under the symplectic transvections already forces this
  (`LinearMap.BilinForm.exists_eq_smul_of_forall_isIsometry_transvection`).

## References

* The equivariance, self-duality, and character constructions follow the formal template in
  `TauCeti.RepresentationTheory.ClassicalGroups.Orthogonal`.
-/

public section

open Matrix

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- The canonical inclusion of the symplectic group into the general linear group. -/
def symplecticGroupToGL :
    Matrix.symplecticGroup (Fin n) k →* GL (Fin n ⊕ Fin n) k where
  toFun g := Matrix.SpecialLinearGroup.toGL
    ⟨g, SymplecticGroup.det_eq_one g.property⟩
  map_one' := by
    ext i j
    rfl
  map_mul' g h := by
    ext i j
    rfl

/-- The symplectic-to-general-linear inclusion has the original matrix as underlying matrix. -/
@[simp]
theorem symplecticGroupToGL_coe (g : Matrix.symplecticGroup (Fin n) k) :
    (symplecticGroupToGL k n g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) = g :=
  (rfl)

/-- The canonical inclusion of the symplectic group into the general linear group is injective. -/
theorem symplecticGroupToGL_injective : Function.Injective (symplecticGroupToGL k n) := by
  intro g h hgh
  apply Subtype.ext
  simpa only [symplecticGroupToGL_coe] using
    congrArg (fun x : GL (Fin n ⊕ Fin n) k =>
      (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)) hgh

/-- The standard representation of the symplectic group on column vectors. -/
def stdSymplecticRep :
    Representation k (Matrix.symplecticGroup (Fin n) k) ((Fin n ⊕ Fin n) → k) :=
  (Units.coeHom (((Fin n ⊕ Fin n) → k) →ₗ[k] ((Fin n ⊕ Fin n) → k))).comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (symplecticGroupToGL k n))

/-- The standard symplectic action is multiplication by the underlying matrix. -/
@[simp]
theorem stdSymplecticRep_apply (g : Matrix.symplecticGroup (Fin n) k) :
    stdSymplecticRep k n g =
      Matrix.mulVecLin (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
  -- Unfold the representation wrapper to expose the coercion from an invertible linear map.
  change (Matrix.GeneralLinearGroup.toLin (symplecticGroupToGL k n g) :
    ((Fin n ⊕ Fin n) → k) →ₗ[k] ((Fin n ⊕ Fin n) → k)) = _
  simpa only [symplecticGroupToGL_coe] using
    Matrix.GeneralLinearGroup.coe_toLin (symplecticGroupToGL k n g)

/-- Evaluation of the standard symplectic action is matrix-vector multiplication. -/
theorem stdSymplecticRep_apply_apply (g : Matrix.symplecticGroup (Fin n) k)
    (v : (Fin n ⊕ Fin n) → k) :
    stdSymplecticRep k n g v =
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) *ᵥ v :=
  LinearMap.congr_fun (stdSymplecticRep_apply k n g) v

/-- The standard representation of the symplectic group is faithful. -/
theorem stdSymplecticRep_injective : Function.Injective (stdSymplecticRep k n) := by
  intro g h hgh
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  exact LinearMap.congr_fun
    ((stdSymplecticRep_apply k n g).symm.trans (hgh.trans (stdSymplecticRep_apply k n h))) v

/-- The standard representation of the symplectic group, bundled as an object of `FDRep`. -/
noncomputable abbrev stdSymplecticFDRep :
    FDRep k (Matrix.symplecticGroup (Fin n) k) :=
  FDRep.of (stdSymplecticRep k n)

/-- The standard alternating bilinear form represented by `Matrix.J`. -/
def stdSymplecticBilinForm :
    LinearMap.BilinForm k ((Fin n ⊕ Fin n) → k) :=
  Matrix.toBilin' (Matrix.J (Fin n) k)

/-- The standard symplectic form is `vᵀ J w`. -/
@[simp]
theorem stdSymplecticBilinForm_apply (v w : (Fin n ⊕ Fin n) → k) :
    stdSymplecticBilinForm k n v w = v ⬝ᵥ Matrix.J (Fin n) k *ᵥ w :=
  Matrix.toBilin'_apply' _ _ _

/-- The standard symplectic form on a pair of standard basis vectors reads off the matrix entry
of `Matrix.J`. -/
-- No `simp` tag: `stdSymplecticBilinForm_apply` already rewrites the left-hand side, after which
-- the simp set finishes the dot product on its own, so simpNF rejects the tag.
theorem stdSymplecticBilinForm_single_single (x y : Fin n ⊕ Fin n) :
    stdSymplecticBilinForm k n (Pi.single x (1 : k)) (Pi.single y (1 : k)) =
      Matrix.J (Fin n) k x y := by
  simp [stdSymplecticBilinForm_apply]

/-- The standard alternating form against the all-ones vector, in coordinates. -/
theorem stdSymplecticBilinForm_one_right (w : (Fin n ⊕ Fin n) → k) :
    stdSymplecticBilinForm k n w 1 =
      ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, w a * Matrix.J (Fin n) k a b := by
  rw [stdSymplecticBilinForm_apply, ← Matrix.toBilin'_apply' (Matrix.J (Fin n) k),
    Matrix.toBilin'_apply]
  simp

/-- The standard symplectic form is alternating. -/
theorem isAlt_stdSymplecticBilinForm : (stdSymplecticBilinForm k n).IsAlt := by
  intro v
  simp [stdSymplecticBilinForm_apply, Matrix.J, Matrix.fromBlocks_mulVec, dotProduct, mul_comm,
    Matrix.neg_mulVec]

/-- The standard symplectic form is nondegenerate. -/
theorem stdSymplecticBilinForm_nondegenerate : (stdSymplecticBilinForm k n).Nondegenerate := by
  rw [stdSymplecticBilinForm, Matrix.nondegenerate_toBilin'_iff]
  exact Matrix.Nondegenerate.of_det_mem_nonZeroDivisors
    (Matrix.isUnit_det_J (Fin n) k).mem_nonZeroDivisors

/-- The standard symplectic action preserves the standard alternating form. -/
@[simp]
theorem stdSymplecticBilinForm_comp_stdSymplecticRep (g : Matrix.symplecticGroup (Fin n) k) :
    (stdSymplecticBilinForm k n).comp (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k).mulVecLin
        (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k).mulVecLin =
      stdSymplecticBilinForm k n := by
  rw [stdSymplecticBilinForm, ← Matrix.toLin'_apply', Matrix.toBilin'_comp]
  rw [(SymplecticGroup.mem_iff' (l := Fin n) (R := k)).mp g.property]

/-- The standard symplectic pairing is invariant under the standard action. -/
@[simp]
theorem stdSymplecticBilinForm_stdSymplecticRep
    (g : Matrix.symplecticGroup (Fin n) k) (v w : (Fin n ⊕ Fin n) → k) :
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k).mulVec v ⬝ᵥ (Matrix.J (Fin n) k *
          (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)).mulVec w =
      stdSymplecticBilinForm k n v w := by
  simpa only [LinearMap.BilinForm.comp_apply, stdSymplecticBilinForm_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using
    LinearMap.congr_fun
      (LinearMap.congr_fun (stdSymplecticBilinForm_comp_stdSymplecticRep k n g) v) w

/-- The standard symplectic form is an invariant form of the standard representation. -/
theorem isInvariantForm_stdSymplecticBilinForm :
    Representation.IsInvariantForm (stdSymplecticRep k n) (stdSymplecticBilinForm k n) :=
  Representation.isInvariantForm_iff_isIsometry.mpr fun g =>
    BilinForm.isIsometry_iff_comp.mpr <| by
      rw [stdSymplecticRep_apply]
      exact stdSymplecticBilinForm_comp_stdSymplecticRep k n g

/-- A linear endomorphism of `k^(2n)` has a symplectic matrix exactly when it preserves the
standard symplectic form. -/
theorem toMatrix'_mem_symplecticGroup_iff
    {f : ((Fin n ⊕ Fin n) → k) →ₗ[k] ((Fin n ⊕ Fin n) → k)} :
    LinearMap.toMatrix' f ∈ Matrix.symplecticGroup (Fin n) k ↔
      BilinForm.IsIsometry (stdSymplecticBilinForm k n) f := by
  rw [SymplecticGroup.mem_iff', ← Matrix.toBilin'.injective.eq_iff, ← Matrix.toBilin'_comp,
    Matrix.toLin'_toMatrix', ← stdSymplecticBilinForm, BilinForm.isIsometry_iff_comp]

/-- The standard symplectic form identifies the standard module with its dual. -/
noncomputable def stdSymplecticRepToDual :
    ((Fin n ⊕ Fin n) → k) ≃ₗ[k] Module.Dual k ((Fin n ⊕ Fin n) → k) :=
  ((Matrix.J (Fin n) k)ᵀ.toLinearEquiv (Pi.basisFun k (Fin n ⊕ Fin n))
    (by simpa only [Matrix.det_transpose] using Matrix.isUnit_det_J (Fin n) k)).trans
      (Pi.basisFun k (Fin n ⊕ Fin n)).toDualEquiv

/-- The standard symplectic self-duality evaluates as the standard alternating form. -/
@[simp]
theorem stdSymplecticRepToDual_apply (v w : (Fin n ⊕ Fin n) → k) :
    stdSymplecticRepToDual k n v w = stdSymplecticBilinForm k n v w :=
  by
    rw [stdSymplecticRepToDual, LinearEquiv.trans_apply, Matrix.toLinearEquiv_apply,
      Matrix.toLin_eq_toLin', Module.Basis.toDualEquiv_apply]
    calc
      (Pi.basisFun k (Fin n ⊕ Fin n)).toDual
          ((Matrix.J (Fin n) k)ᵀ *ᵥ v) w =
          ((Matrix.J (Fin n) k)ᵀ *ᵥ v) ⬝ᵥ w := by
        simp [Module.Basis.toDual, Pi.basisFun, dotProduct]
      _ = w ⬝ᵥ (Matrix.J (Fin n) k)ᵀ *ᵥ v := dotProduct_comm _ _
      _ = v ⬝ᵥ Matrix.J (Fin n) k *ᵥ w :=
        Matrix.dotProduct_transpose_mulVec (Matrix.J (Fin n) k) w v
      _ = stdSymplecticBilinForm k n v w := (stdSymplecticBilinForm_apply k n v w).symm

/-- The dual, or contragredient, of the standard representation of the symplectic group. -/
noncomputable def stdSymplecticDualRep :
    Representation k (Matrix.symplecticGroup (Fin n) k)
      (Module.Dual k ((Fin n ⊕ Fin n) → k)) :=
  (stdSymplecticRep k n).dual

/-- The dual standard symplectic action is the transpose of the inverse matrix action. -/
@[simp]
theorem stdSymplecticDualRep_apply (g : Matrix.symplecticGroup (Fin n) k) :
    stdSymplecticDualRep k n g =
      Module.Dual.transpose (R := k)
        (Matrix.mulVecLin ((g⁻¹ : Matrix.symplecticGroup (Fin n) k) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)) := by
  rw [stdSymplecticDualRep, Representation.dual_apply, stdSymplecticRep_apply]

/-- The standard-form identification intertwines the standard and dual actions. -/
theorem stdSymplecticRepToDual_equivariant (g : Matrix.symplecticGroup (Fin n) k) :
    stdSymplecticRepToDual k n ∘ₗ stdSymplecticRep k n g =
      stdSymplecticDualRep k n g ∘ₗ stdSymplecticRepToDual k n := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  -- Extensionality leaves the displayed compositions hidden behind coercions.
  change stdSymplecticRepToDual k n (stdSymplecticRep k n g v) w = _
  rw [stdSymplecticRepToDual_apply]
  rw [stdSymplecticDualRep_apply, LinearMap.comp_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply]
  -- Expose the evaluation of the form-induced map on the right.
  change _ = stdSymplecticRepToDual k n v
    (((g⁻¹ : Matrix.symplecticGroup (Fin n) k) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) *ᵥ w)
  rw [stdSymplecticRepToDual_apply, ← stdSymplecticRep_apply_apply k n g⁻¹]
  calc
    stdSymplecticBilinForm k n (stdSymplecticRep k n g v) w =
        stdSymplecticBilinForm k n (stdSymplecticRep k n g v)
          (stdSymplecticRep k n g (stdSymplecticRep k n g⁻¹ w)) := by
      rw [Representation.self_inv_apply]
    _ = stdSymplecticBilinForm k n v (stdSymplecticRep k n g⁻¹ w) := by
      simpa only [stdSymplecticRep_apply, stdSymplecticBilinForm_apply,
        Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc] using
        stdSymplecticBilinForm_stdSymplecticRep k n g v
          (stdSymplecticRep k n g⁻¹ w)

/-- The standard representation of the symplectic group is equivariantly self-dual. -/
noncomputable def stdSymplecticRepEquivDual :
    (stdSymplecticRep k n).Equiv (stdSymplecticDualRep k n) :=
  .mk (stdSymplecticRepToDual k n) (stdSymplecticRepToDual_equivariant k n)

/-- The symplectic self-duality equivalence evaluates as the standard alternating form. -/
@[simp]
theorem stdSymplecticRepEquivDual_apply (v w : (Fin n ⊕ Fin n) → k) :
    stdSymplecticRepEquivDual k n v w = stdSymplecticBilinForm k n v w :=
  stdSymplecticRepToDual_apply k n v w

/-- The dual standard symplectic representation, bundled as an object of `FDRep`. -/
noncomputable abbrev stdSymplecticDualFDRep :
    FDRep k (Matrix.symplecticGroup (Fin n) k) :=
  FDRep.of (stdSymplecticDualRep k n)

end CommRing

section Field

variable [Field k]

/-- The character of the standard symplectic representation is the matrix trace. -/
@[simp]
theorem char_stdSymplecticRep (g : Matrix.symplecticGroup (Fin n) k) :
    (stdSymplecticRep k n).character g =
      Matrix.trace (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
  rw [Representation.character, stdSymplecticRep_apply, ← Matrix.toLin'_apply']
  exact Matrix.trace_toLin'_eq (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)

/-- The bundled standard symplectic character is the matrix trace. -/
@[simp]
theorem char_stdSymplecticFDRep (g : Matrix.symplecticGroup (Fin n) k) :
    (stdSymplecticFDRep k n).character g =
      Matrix.trace (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_stdSymplecticRep k n g

/-- The dual standard symplectic character is the inverse matrix trace. -/
@[simp]
theorem char_stdSymplecticDualRep (g : Matrix.symplecticGroup (Fin n) k) :
    (stdSymplecticDualRep k n).character g =
      Matrix.trace ((g⁻¹ : Matrix.symplecticGroup (Fin n) k) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
  rw [stdSymplecticDualRep, Representation.char_dual, char_stdSymplecticRep]

/-- The bundled dual standard symplectic character is the inverse matrix trace. -/
@[simp]
theorem char_stdSymplecticDualFDRep (g : Matrix.symplecticGroup (Fin n) k) :
    (stdSymplecticDualFDRep k n).character g =
      Matrix.trace ((g⁻¹ : Matrix.symplecticGroup (Fin n) k) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_stdSymplecticDualRep k n g

/-- **`Sp₂ₙ(k)` acts transitively on the isotropic subspaces of each dimension.** Two subspaces of
`k^(2n)` that are isotropic for the standard alternating form and have the same dimension are
related by the standard action of a symplectic matrix. This holds in every characteristic. -/
theorem exists_map_stdSymplecticRep_eq {U₁ U₂ : Submodule k ((Fin n ⊕ Fin n) → k)}
    (h₁ : U₁ ≤ LinearMap.BilinForm.orthogonal (stdSymplecticBilinForm k n) U₁)
    (h₂ : U₂ ≤ LinearMap.BilinForm.orthogonal (stdSymplecticBilinForm k n) U₂)
    (h : Module.finrank k U₁ = Module.finrank k U₂) :
    ∃ g : Matrix.symplecticGroup (Fin n) k, U₁.map (stdSymplecticRep k n g) = U₂ := by
  obtain ⟨g, hg⟩ := (isAlt_stdSymplecticBilinForm k n).exists_isometryEquiv_map_eq
    (stdSymplecticBilinForm_nondegenerate k n) h₁ h₂ h
  have hA : LinearMap.toMatrix' (g : ((Fin n ⊕ Fin n) → k) →ₗ[k] (Fin n ⊕ Fin n) → k) ∈
      Matrix.symplecticGroup (Fin n) k :=
    (toMatrix'_mem_symplecticGroup_iff k n).mpr (BilinForm.isIsometry_iff.mpr fun x y => by simp)
  refine ⟨⟨_, hA⟩, ?_⟩
  rw [stdSymplecticRep_apply, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix', hg]

/-- **The invariant bilinear forms of the symplectic group.** Over a field, a bilinear form on
`k^(2n)` invariant under the standard action of `Sp₂ₙ(k)` is a scalar multiple of the standard
symplectic form. Invariance under the symplectic transvections `x ↦ x + ω(v, x) v` already
suffices (`LinearMap.BilinForm.exists_eq_smul_of_forall_isIsometry_transvection`). -/
theorem exists_eq_smul_stdSymplecticBilinForm {B : LinearMap.BilinForm k ((Fin n ⊕ Fin n) → k)}
    (hB : Representation.IsInvariantForm (stdSymplecticRep k n) B) :
    ∃ c : k, B = c • stdSymplecticBilinForm k n := by
  refine LinearMap.BilinForm.exists_eq_smul_of_forall_isIsometry_transvection
    (stdSymplecticBilinForm_nondegenerate k n).1 fun v => ?_
  let τ := LinearMap.transvection (stdSymplecticBilinForm k n v) v
  have hτ : LinearMap.toMatrix' τ ∈ Matrix.symplecticGroup (Fin n) k :=
    (toMatrix'_mem_symplecticGroup_iff k n).mpr
      ((isAlt_stdSymplecticBilinForm k n).isIsometry_transvection v)
  have h := hB.isIsometry ⟨_, hτ⟩
  rwa [stdSymplecticRep_apply, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix'] at h

/-- **The invariant bilinear forms of the symplectic group**: over a field, the bilinear forms on
`k^(2n)` invariant under `Sp₂ₙ(k)` are the multiples of the standard symplectic form, so they form
the span of that form, which is a line when `n > 0`. -/
theorem invariantForms_stdSymplecticRep_eq_span_stdSymplecticBilinForm :
    Representation.invariantForms (stdSymplecticRep k n) =
      Submodule.span k {stdSymplecticBilinForm k n} :=
  (isInvariantForm_stdSymplecticBilinForm k n).invariantForms_eq_span_of_forall_exists_eq_smul
    fun _ => exists_eq_smul_stdSymplecticBilinForm k n

end Field

end TauCeti

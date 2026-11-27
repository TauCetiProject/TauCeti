/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Isometry
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Mobius.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.UpperHalfSpace
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Borel
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup

/-!
# Möbius transformations are isometries of hyperbolic three-space

Every matrix of `SL(2, ℂ)` acts on hyperbolic three-space `ℍ³ = UpperHalfSpace ℂ` by a
Riemannian isometry of the hyperbolic metric `(|dw|² + dt²) / t²`. This file proves it by
decomposing the Möbius action into isometries already known on the upper half-space model:

* an upper triangular matrix `(a b; 0 a⁻¹)` acts as the similarity of scale `|a|²`, rotation
  `w ↦ (a / conj a) w` and translation `a b`
  (`TauCeti.UpperHalfSpace.smul_eq_similarity_of_apply_one_zero_eq_zero`);
* the matrix `S = (0 -1; 1 0)` acts as the inversion in the unit sphere about the origin followed
  by the reflection `w ↦ -conj w`
  (`TauCeti.UpperHalfSpace.smul_eq_similarity_inversion_of_coe_eq_S`);
* every matrix with `c ≠ 0` is `(1 a/c; 0 1) S (c d; 0 c⁻¹)`
  (`TauCeti.SL2Borel.mk_mul_modularGroup_S_mul_mk`).

The action of `SL(2, ℂ)` and of `PSL(2, ℂ)` is therefore by smooth maps preserving the metric, so
it gives homomorphisms into the isometry group `TauCeti.Isom` of `ℍ³`. The one from `PSL(2, ℂ)` is
injective, because the projective action is faithful. These homomorphisms let the Riemannian
theory of `ℍ³` (its distance, its volume, its geodesics) be applied to Kleinian groups.

## Main results

* `TauCeti.UpperHalfSpace.inner_mfderiv_smul`: the differential of `A • ·` preserves the
  hyperbolic metric.
* `TauCeti.UpperHalfSpace.slToIsom`, `TauCeti.UpperHalfSpace.pslToIsom`: the homomorphisms from
  `SL(2, ℂ)` and `PSL(2, ℂ)` to the isometry group of `ℍ³`, evaluating to the Möbius action.
* `TauCeti.UpperHalfSpace.pslToIsom_injective`: `PSL(2, ℂ)` embeds in the isometry group.
* `TauCeti.UpperHalfSpace.slToIsom_eq_similarity` and
  `TauCeti.UpperHalfSpace.slToIsom_eq_similarity_mul_inversion`: the isometries of the upper
  triangular matrices and of `S`.

## References

* A. F. Beardon, *The Geometry of Discrete Groups*, Springer GTM 91 (1983), §§3.3 and 4.1 (every
  Möbius transformation is a composite of similarities and inversions, and its Poincaré extension
  is an isometry of the upper half-space).
* J. Elstrodt, F. Grunewald, J. Mennicke, *Groups Acting on Hyperbolic Space*, Springer (1998),
  Chapter 1, §1 (the action of `PSL(2, ℂ)` on `ℍ³` by isometries).
-/

public section

noncomputable section

open Bundle Matrix ComplexConjugate Manifold
open scoped MatrixGroups ContDiff

namespace TauCeti.UpperHalfSpace

/-- The squared Euclidean norm of a point `(w, t)` of the upper half-space over `ℂ` is
`|w|² + t²`. -/
private theorem norm_coe_sq (p : UpperHalfSpace ℂ) :
    ‖(p : WithLp 2 (ℂ × ℝ))‖ ^ 2 = Complex.normSq (p : WithLp 2 (ℂ × ℝ)).fst + height p ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, Complex.normSq_eq_norm_sq, Real.norm_eq_abs, sq_abs,
    snd_coe]

/-! ### The Möbius action through similarities and inversions -/

/-- **Upper triangular matrices act by similarities**: `(a b; 0 a⁻¹)` acts on `ℍ³` as the
similarity `(w, t) ↦ (|a|² (a / conj a) w + a b, |a|² t)`, of scale `|a|²`, rotation
`w ↦ (a / conj a) w` and translation `a b`. -/
theorem smul_eq_similarity_of_apply_one_zero_eq_zero {A : SL(2, ℂ)} (hc : A 1 0 = 0)
    (p : UpperHalfSpace ℂ) :
    A • p = similarity (Complex.normSq (A 0 0))
      (Complex.normSq_pos.2
        (SpecialLinearGroup.apply_zero_zero_ne_zero_of_apply_one_zero_eq_zero hc))
      (rotation (Circle.ofConjDivSelf (conj (A 0 0)) ((map_ne_zero _).2
        (SpecialLinearGroup.apply_zero_zero_ne_zero_of_apply_one_zero_eq_zero hc))))
      (A 0 0 * A 0 1) p := by
  have ha : conj (A 0 0) ≠ 0 :=
    (map_ne_zero _).2 (SpecialLinearGroup.apply_zero_zero_ne_zero_of_apply_one_zero_eq_zero hc)
  refine ext_fst_height ?_ ?_
  · simp only [fst_smul_of_apply_one_zero_eq_zero hc, coe_similarity_apply, WithLp.toLp_fst,
      rotation_apply, Circle.ofConjDivSelf_coe, Complex.conj_conj, Complex.real_smul,
      Complex.normSq_eq_conj_mul_self]
    field_simp
  · rw [height_smul_of_apply_one_zero_eq_zero hc, height_similarity_apply]

/-- **The matrix `S = (0 -1; 1 0)` acts as an inversion followed by a reflection**: the inversion
in the unit sphere about the origin, then the reflection `w ↦ -conj w` of the horizontal
coordinate. -/
theorem smul_eq_similarity_inversion_of_coe_eq_S {A : SL(2, ℂ)}
    (hA : (A : Matrix (Fin 2) (Fin 2) ℂ) = !![0, -1; 1, 0]) (p : UpperHalfSpace ℂ) :
    A • p = similarity 1 one_pos (Complex.conjLIE.trans (.neg ℝ)) 0
      (inversion 0 1 one_ne_zero p) := by
  have hJ : Complex.normSq (p : WithLp 2 (ℂ × ℝ)).fst + height p ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (pow_pos (height_pos p) 2)).ne'
  have hd : dist (p : WithLp 2 (ℂ × ℝ)) (WithLp.toLp 2 (0, 0)) ^ 2 =
      Complex.normSq (p : WithLp 2 (ℂ × ℝ)).fst + height p ^ 2 := by
    rw [← Prod.zero_eq_mk, WithLp.toLp_zero, dist_zero_right, norm_coe_sq]
  refine ext_fst_height ?_ ?_
  · rw [fst_smul_of_coe_eq_S hA, coe_similarity_apply, coe_inversion_apply]
    simp [EuclideanGeometry.inversion, hd, div_eq_inv_mul]
  · rw [height_smul_of_coe_eq_S hA, height_similarity_apply, height_inversion_apply, div_pow,
      hd]
    field_simp

/-- If `A • ·` and `B • ·` are Riemannian isometries, then so is `(A * B) • ·`. -/
private theorem exists_isom_coe_eq_smul_mul {A B : SL(2, ℂ)}
    (hA : ∃ Φ : Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) (UpperHalfSpace ℂ), ⇑Φ = (A • ·))
    (hB : ∃ Φ : Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) (UpperHalfSpace ℂ), ⇑Φ = (B • ·)) :
    ∃ Φ : Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) (UpperHalfSpace ℂ), ⇑Φ = ((A * B) • ·) := by
  obtain ⟨Φ, hΦ⟩ := hA
  obtain ⟨Ψ, hΨ⟩ := hB
  refine ⟨Φ * Ψ, funext fun p ↦ ?_⟩
  rw [RiemannianIsometry.mul_apply, hΦ, hΨ, mul_smul]

/-- Every Möbius transformation is a Riemannian isometry of `ℍ³`: for `A ∈ SL(2, ℂ)` there is an
isometry of the hyperbolic metric whose underlying map is `p ↦ A • p`. It is a similarity when `A`
is upper triangular, and otherwise a similarity, an inversion in the unit sphere and a similarity
composed. `slToIsom` packages these isometries as a homomorphism. -/
private theorem exists_isom_coe_eq_smul (A : SL(2, ℂ)) :
    ∃ Φ : Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) (UpperHalfSpace ℂ), ⇑Φ = (A • ·) := by
  have upper {B : SL(2, ℂ)} (hB : B 1 0 = 0) :
      ∃ Φ : Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) (UpperHalfSpace ℂ), ⇑Φ = (B • ·) :=
    ⟨_, funext fun p ↦ (smul_eq_similarity_of_apply_one_zero_eq_zero hB p).symm⟩
  rcases eq_or_ne (A 1 0) 0 with hc | hc
  · exact upper hc
  rw [← SL2Borel.mk_mul_modularGroup_S_mul_mk A (Units.mk0 _ hc) rfl]
  refine exists_isom_coe_eq_smul_mul
    (exists_isom_coe_eq_smul_mul (upper (SL2Borel.apply_one_zero _)) ?_)
    (upper (SL2Borel.apply_one_zero _))
  refine ⟨similarity 1 one_pos (Complex.conjLIE.trans (.neg ℝ)) 0 * inversion 0 1 one_ne_zero,
    funext fun p ↦ ?_⟩
  rw [RiemannianIsometry.mul_apply,
    smul_eq_similarity_inversion_of_coe_eq_S TauCeti.Matrix.SpecialLinearGroup.coe_modularGroup_S]

/-- **Möbius transformations preserve the hyperbolic metric**: the differential of
`p ↦ A • p` preserves the hyperbolic inner product `⟪v, w⟫ / t²` of `ℍ³`. -/
theorem inner_mfderiv_smul (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ)
    (v w : TangentSpace 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) p) :
    inner ℝ (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) (A • ·) p v)
        (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) (A • ·) p w) =
      inner ℝ v w := by
  obtain ⟨Φ, hΦ⟩ := exists_isom_coe_eq_smul A
  -- the tangent space at the image carries the metric at that point, so transport along `hΦ` by
  -- generalizing the map rather than rewriting inside the dependent type
  have key : ∀ f : UpperHalfSpace ℂ → UpperHalfSpace ℂ, ⇑Φ = f →
      inner ℝ (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) f p v)
        (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) f p w) = inner ℝ v w := by
    rintro f rfl
    exact Φ.inner_mfderiv p v w
  exact key _ hΦ

/-- Each matrix of `SL(2, ℂ)` acts on `ℍ³` by a smooth map. -/
instance : ContMDiffConstSMul 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) ∞ SL(2, ℂ) (UpperHalfSpace ℂ) where
  contMDiff_const_smul A := by
    obtain ⟨Φ, hΦ⟩ := exists_isom_coe_eq_smul A
    rw [← hΦ, ← RiemannianIsometry.coe_toDiffeomorph]
    exact Φ.toDiffeomorph.contMDiff

/-- Each element of `PSL(2, ℂ)` acts on `ℍ³` by a smooth map. -/
instance : ContMDiffConstSMul 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) ∞ PSL(2, ℂ) (UpperHalfSpace ℂ) where
  contMDiff_const_smul g := by
    induction g using QuotientGroup.induction_on with | H A => ?_
    simpa only [pslMk_smul] using contMDiff_const_smul A

/-! ### The homomorphisms to the isometry group -/

/-- The homomorphism sending a matrix of `SL(2, ℂ)` to its Möbius transformation, as a Riemannian
isometry of hyperbolic three-space. -/
def slToIsom : SL(2, ℂ) →* Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) (UpperHalfSpace ℂ) :=
  RiemannianIsometry.constSMulHom inner_mfderiv_smul

/-- `slToIsom A` acts on `ℍ³` by `A • p`. -/
@[simp]
theorem slToIsom_apply (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) : slToIsom A p = A • p := by
  rw [slToIsom, RiemannianIsometry.constSMulHom_apply, RiemannianIsometry.constSMul_apply]

/-- The inverse of `slToIsom A` acts on `ℍ³` by `A⁻¹ • p`. -/
@[simp]
theorem slToIsom_symm_apply (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) :
    (slToIsom A).symm p = A⁻¹ • p := by
  rw [← RiemannianIsometry.inv_apply, ← map_inv, slToIsom_apply]

/-- The underlying diffeomorphism of `slToIsom A` is `Diffeomorph.constSmul _ ∞ A`. -/
@[simp]
theorem toDiffeomorph_slToIsom (A : SL(2, ℂ)) :
    (slToIsom A).toDiffeomorph = Diffeomorph.constSmul 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) ∞ A := by
  rw [slToIsom, RiemannianIsometry.constSMulHom_apply, RiemannianIsometry.toDiffeomorph_constSMul]

/-- The homomorphism sending an element of `PSL(2, ℂ)` to its Möbius transformation, as a
Riemannian isometry of hyperbolic three-space. -/
def pslToIsom : PSL(2, ℂ) →* Isom 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) (UpperHalfSpace ℂ) :=
  QuotientGroup.lift (Subgroup.center SL(2, ℂ)) slToIsom fun A hA ↦ by
    ext p
    rw [slToIsom_apply, smul_eq_of_mem_center hA, RiemannianIsometry.one_apply]

/-- `pslToIsom` sends the class of `A : SL(2, ℂ)` to `slToIsom A`. -/
@[simp]
theorem pslToIsom_mk (A : SL(2, ℂ)) : pslToIsom (A : PSL(2, ℂ)) = slToIsom A :=
  (rfl)

/-- `pslToIsom g` acts on `ℍ³` by `g • p`. -/
@[simp]
theorem pslToIsom_apply (g : PSL(2, ℂ)) (p : UpperHalfSpace ℂ) : pslToIsom g p = g • p := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  rw [pslToIsom_mk, slToIsom_apply, pslMk_smul]

/-- The inverse of `pslToIsom g` acts on `ℍ³` by `g⁻¹ • p`. -/
@[simp]
theorem pslToIsom_symm_apply (g : PSL(2, ℂ)) (p : UpperHalfSpace ℂ) :
    (pslToIsom g).symm p = g⁻¹ • p := by
  rw [← RiemannianIsometry.inv_apply, ← map_inv, pslToIsom_apply]

/-- The underlying diffeomorphism of `pslToIsom g` is `Diffeomorph.constSmul _ ∞ g`. -/
@[simp]
theorem toDiffeomorph_pslToIsom (g : PSL(2, ℂ)) :
    (pslToIsom g).toDiffeomorph = Diffeomorph.constSmul 𝓘(ℝ, WithLp 2 (ℂ × ℝ)) ∞ g := by
  ext p
  rw [RiemannianIsometry.coe_toDiffeomorph, pslToIsom_apply, Diffeomorph.coe_constSmul]

/-- **`PSL(2, ℂ)` is a group of isometries of `ℍ³`**: `pslToIsom` is injective, because only the
identity of `PSL(2, ℂ)` fixes every point. -/
theorem pslToIsom_injective : Function.Injective pslToIsom :=
  fun _ _ h ↦ eq_of_smul_eq_smul fun p : UpperHalfSpace ℂ ↦ by
    simpa only [pslToIsom_apply] using DFunLike.congr_fun h p

/-- The isometry of an upper triangular matrix `(a b; 0 a⁻¹)` is the similarity of scale `|a|²`,
rotation `w ↦ (a / conj a) w` and translation `a b`. -/
theorem slToIsom_eq_similarity {A : SL(2, ℂ)} (hc : A 1 0 = 0) :
    slToIsom A = similarity (Complex.normSq (A 0 0))
      (Complex.normSq_pos.2
        (SpecialLinearGroup.apply_zero_zero_ne_zero_of_apply_one_zero_eq_zero hc))
      (rotation (Circle.ofConjDivSelf (conj (A 0 0)) ((map_ne_zero _).2
        (SpecialLinearGroup.apply_zero_zero_ne_zero_of_apply_one_zero_eq_zero hc))))
      (A 0 0 * A 0 1) := by
  ext p
  rw [slToIsom_apply, smul_eq_similarity_of_apply_one_zero_eq_zero hc]

/-- The isometry of `S = (0 -1; 1 0)` is the inversion in the unit sphere about the origin
followed by the reflection `w ↦ -conj w` of the horizontal coordinate. -/
theorem slToIsom_eq_similarity_mul_inversion {A : SL(2, ℂ)}
    (hA : (A : Matrix (Fin 2) (Fin 2) ℂ) = !![0, -1; 1, 0]) :
    slToIsom A =
      similarity 1 one_pos (Complex.conjLIE.trans (.neg ℝ)) 0 * inversion 0 1 one_ne_zero := by
  ext p
  rw [slToIsom_apply, smul_eq_similarity_inversion_of_coe_eq_S hA, RiemannianIsometry.mul_apply]

end TauCeti.UpperHalfSpace

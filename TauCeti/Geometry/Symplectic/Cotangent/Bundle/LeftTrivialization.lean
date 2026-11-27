/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint
public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.InvariantVectorField.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Relation
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
public import TauCeti.Geometry.Manifold.VectorField.Prod
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.MomentMap
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.VectorField.ModelChart

/-!
# The left trivialization of the cotangent bundle of a Lie group

Let `G` be a real Lie group modelled on `E`, with Lie algebra `𝔤 = GroupLieAlgebra I G`, whose
underlying space is `E`. Moving covectors at the identity around with the cotangent lift of left
multiplication identifies `T*G` with the product `G × 𝔤*`:

`Φ : G × (E →L[ℝ] ℝ) ≃ T*G`, `(g, a) ↦ g • a`,

where `a` is read as a covector at `1` (`TauCeti.CotangentBundle.leftTrivialization`). The covector
`Φ (g, a)` at `g` is `a ∘ d(L_{g⁻¹})_g`, and `Φ` is a diffeomorphism. It intertwines left
multiplication on the first factor with the cotangent-lifted action of `G`
(`TauCeti.CotangentBundle.leftTrivialization_mul`). Right multiplication by `h` acts as
`(g, a) ↦ (g h, Ad*_{h⁻¹} a)`: it relates `Φ (g, a)` to `Φ (g h, Ad*_{h⁻¹} a)` in the sense of
`TauCeti.CotangentBundle.cotangentRel`
(`TauCeti.CotangentBundle.cotangentRel_mul_right_leftTrivialization`).

In these coordinates the canonical forms of `T*G` are expressed through the left Maurer–Cartan form
`θ_g = d(L_{g⁻¹})_g`. The Liouville form is `⟨a, θ⟩`: it sends a tangent vector `(v, α)` at
`(g, a)` to `a (θ_g v)`
(`TauCeti.CotangentBundle.mpullback_leftTrivialization_liouvilleForm_apply`).
The canonical symplectic form `ω = -dλ` pairs `(v, α)` and `(w, β)` at `(g, a)` to

`β (θ_g v) - α (θ_g w) + a ⁅θ_g v, θ_g w⁆`

(`TauCeti.CotangentBundle.eval₂_mpullback_leftTrivialization_symplecticForm`). The first two terms
pair the group directions with the dual directions; the last is the Kirillov form of `a`, which is
the restriction of `ω` to the slice `G × {a}`. The moment map of the cotangent lift of left
multiplication becomes the coadjoint orbit map `(g, a) ↦ Ad*_g a`
(`TauCeti.CotangentBundle.momentMap_leftTrivialization`).

The formula for the symplectic form comes from the invariant formula for the exterior derivative
on the product fields `(ξ^L, α)` and `(η^L, β)`, where `ξ^L` is the left-invariant vector field of
`ξ ∈ 𝔤` and `α`, `β` are constant: the Liouville form takes the value `a ξ` on `(ξ^L, α)` at
`(g, a)`, whose derivative along `(η^L, β)` is `β ξ`, and the bracket of the two fields is
`(⁅ξ, η⁆^L, 0)`.

Pulling the left-trivialized symplectic form back along `id × f` for a smooth map `f : N → 𝔤*`
gives the two-form `-d⟨f, θ⟩` on `G × N`, where the one-form `⟨f, θ⟩` sends `(v, u)` at `(g, n)`
to `f n (θ_g v)`. It pairs `(v, u)` and `(w, u')` at `(g, n)` to
`df_n u' (θ_g v) - df_n u (θ_g w) + f n ⁅θ_g v, θ_g w⁆`
(`TauCeti.CotangentBundle.eval₂_mpullback_prodMap_leftTrivialization_symplecticForm`). With
`f (η, v) = ν + η + μ_V v` on `N = 𝔪* × V` this is the form `-d⟨ν + η + μ_V(v), θ⟩` on
`G × (𝔪* × V)` of the Marle–Guillemin–Sternberg local model of a Hamiltonian action near an orbit.

## Main definitions

* `TauCeti.CotangentBundle.leftTrivialization I G`: the diffeomorphism `G × 𝔤* ≃ T*G`,
  `(g, a) ↦ g • a`.

## Main results

* `TauCeti.CotangentBundle.leftTrivialization_snd_apply`: `Φ (g, a)` is the covector
  `a ∘ d(L_{g⁻¹})_g` at `g`.
* `TauCeti.CotangentBundle.leftTrivialization_symm_apply_fst`,
  `TauCeti.CotangentBundle.leftTrivialization_symm_apply_snd_apply`: `Φ⁻¹` sends a covector `z` at
  `g` to `(g, ξ ↦ z (ξ^L g))`.
* `TauCeti.CotangentBundle.leftTrivialization_mul`: `Φ (h g, a) = h • Φ (g, a)`.
* `TauCeti.CotangentBundle.cotangentRel_mul_right_leftTrivialization`: right multiplication by `h`
  relates `Φ (g, a)` to `Φ (g h, Ad*_{h⁻¹} a)`.
* `TauCeti.CotangentBundle.momentMap_leftTrivialization`: the cotangent moment map of left
  multiplication is `(g, a) ↦ Ad*_g a`.
* `TauCeti.CotangentBundle.fundamentalVectorField_leftTrivialization`: the fundamental vector
  field of `ξ` at `(g, a)` is `(ξ^R(g), 0)`.
* `TauCeti.CotangentBundle.coadjointRepresentation_proj_inv_momentMap`: the left-trivialized value
  of a covector `z` over `g` is `Ad*_{g⁻¹} μ(z)`.
* `TauCeti.CotangentBundle.eq_of_proj_eq_of_momentMap_eq`: a covector of `T*G` is determined by
  its base point and its moment map.
* `TauCeti.CotangentBundle.exists_momentMap_eq_and_proj_eq`: every pair of a base point and a
  value of the moment map is realized by a covector of `T*G`.
* `TauCeti.CotangentBundle.mpullback_leftTrivialization_liouvilleForm_apply`: the Liouville form is
  `⟨a, θ⟩`.
* `TauCeti.CotangentBundle.eval₂_mpullback_leftTrivialization_symplecticForm`: the symplectic form
  pairs `(v, α)` and `(w, β)` to `β (θ v) - α (θ w) + a ⁅θ v, θ w⁆`.
* `TauCeti.CotangentBundle.isSymplectic_mpullback_leftTrivialization_symplecticForm`: this form is
  symplectic on `G × 𝔤*`.
* `TauCeti.CotangentBundle.eval₂_mpullback_prodMap_leftTrivialization_symplecticForm`: the
  two-form `-d⟨f, θ⟩` on `G × N`, the pullback along `id × f`.

## References

* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999 (the left trivialization of `T*G` and Lie–Poisson reduction).
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
* V. Guillemin, S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics*, Mathematical Physics Studies 6, Reidel, 1984, 161–175.
-/

public section

open Bundle Manifold VectorField TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.CotangentBundle

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

/-! ### The diffeomorphism `G × 𝔤* ≃ T*G` -/

/-- The covector `a` at the identity of `G`. -/
private abbrev covectorAtOne (a : E →L[ℝ] ℝ) : CotangentBundle I G :=
  TotalSpace.mk' (E →L[ℝ] ℝ) (1 : G) a

omit [LieGroup I ∞ G] in
/-- A covector over the identity is the covector at `1` given by its own values. -/
private theorem covectorAtOne_snd {z : CotangentBundle I G} (hz : z.proj = 1) :
    covectorAtOne (I := I) (G := G) z.snd = z :=
  CotangentBundle.ext hz.symm fun _ ↦ rfl

/-- A covector translated back to the identity lies over the identity. -/
private theorem proj_inv_smul_self (z : CotangentBundle I G) : (z.proj⁻¹ • z).proj = 1 := by
  rw [proj_smul, smul_eq_mul, inv_mul_cancel]

/-- The underlying map `(g, a) ↦ g • a` of the left trivialization. -/
private def leftTrivializationFun (p : G × (E →L[ℝ] ℝ)) : CotangentBundle I G :=
  p.1 • covectorAtOne p.2

/-- The inverse `z ↦ (π z, π z⁻¹ • z)` of the left trivialization, which moves a covector back to
the identity. -/
private def leftTrivializationInvFun (z : CotangentBundle I G) : G × (E →L[ℝ] ℝ) :=
  (z.proj, (z.proj⁻¹ • z).snd)

private theorem contMDiff_leftTrivializationFun :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (leftTrivializationFun (I := I) (G := G)) :=
  contMDiff_fst.smul ((contMDiff_mk (I := I) (1 : G)).comp contMDiff_snd)

private theorem contMDiff_leftTrivializationInvFun :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (leftTrivializationInvFun (I := I) (G := G)) := by
  have hπ : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I ∞ fun z : CotangentBundle I G ↦ z.proj :=
    contMDiff_proj _
  -- The covector moved back to the identity is smooth as a point of `T*G` lying over `1`.
  have hback : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      fun z : CotangentBundle I G ↦ z.proj⁻¹ • z :=
    ((contMDiff_inv I ∞).comp hπ).smul contMDiff_id
  -- Over the identity, the coordinates of a covector at the identity are the covector itself.
  have hcoord (x : G) (z : CotangentBundle I G) (hx : x = 1) (hz : z.proj = 1) :
      ContinuousLinearMap.inCoordinates E (TangentSpace I) ℝ (fun _ : G ↦ ℝ) x z.proj x z.proj
        z.snd = z.snd := by
    obtain rfl := hx
    obtain ⟨y, q⟩ := z
    obtain rfl : y = 1 := hz
    exact inCoordinates_self 1 q
  refine hπ.prodMk fun z₀ ↦ ?_
  exact ((contMDiffAt_hom_bundle _).mp (hback z₀)).2.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun z ↦
      (hcoord _ _ (proj_inv_smul_self z₀) (proj_inv_smul_self z)).symm)

variable (I G) in
/-- The **left trivialization** of the cotangent bundle of a Lie group: the diffeomorphism
`G × 𝔤* ≃ T*G` sending `(g, a)` to the image `g • a` of the covector `a` at the identity under the
cotangent lift of left multiplication by `g`, the covector `a ∘ d(L_{g⁻¹})_g` at `g`. The dual
`𝔤*` of the Lie algebra is modelled by `E →L[ℝ] ℝ`, the cotangent fibre of the model. -/
def leftTrivialization :
    (G × (E →L[ℝ] ℝ)) ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), I.prod 𝓘(ℝ, E →L[ℝ] ℝ)⟯ CotangentBundle I G where
  toFun := leftTrivializationFun
  invFun := leftTrivializationInvFun
  left_inv p := by
    obtain ⟨g, a⟩ := p
    refine Prod.ext ?_ ?_
    · simp [leftTrivializationFun, leftTrivializationInvFun, smul_eq_mul]
    · have h : (g • covectorAtOne (I := I) (G := G) a).proj⁻¹ • g •
          covectorAtOne (I := I) (G := G) a = covectorAtOne a := by
        rw [proj_smul, smul_eq_mul, mul_one, inv_smul_smul]
      simp only [leftTrivializationInvFun, leftTrivializationFun]
      rw [h]
  right_inv z := by
    simp only [leftTrivializationFun, leftTrivializationInvFun]
    rw [covectorAtOne_snd (proj_inv_smul_self z), smul_inv_smul]
  contMDiff_toFun := contMDiff_leftTrivializationFun
  contMDiff_invFun := contMDiff_leftTrivializationInvFun

/-- The left trivialization of `(g, a)` is the translate by `g` of the covector `a` at the
identity. -/
theorem leftTrivialization_apply (p : G × (E →L[ℝ] ℝ)) :
    leftTrivialization I G p = p.1 • (TotalSpace.mk' (E →L[ℝ] ℝ) 1 p.2 : CotangentBundle I G) :=
  (rfl)

/-- The left trivialization of `(g, a)` is a covector at `g`. -/
@[simp]
theorem proj_leftTrivialization (p : G × (E →L[ℝ] ℝ)) :
    (leftTrivialization I G p).proj = p.1 := by
  rw [leftTrivialization_apply, proj_smul, smul_eq_mul, mul_one]

/-- The left trivialization of `(g, a)` is the covector `a ∘ d(L_{g⁻¹})_g` at `g`. -/
theorem leftTrivialization_snd_apply (p : G × (E →L[ℝ] ℝ)) (v : TangentSpace I p.1) :
    (leftTrivialization I G p).snd v = p.2 (mfderiv I I (p.1⁻¹ * ·) p.1 v) := by
  obtain ⟨g, a⟩ := p
  -- The base point `g • 1` of the translated covector is `g`, but only propositionally.
  have key : ∀ (x : G) (_ : x = g) (v : TangentSpace I g),
      mfderiv I I (g⁻¹ * ·) x v = mfderiv I I (g⁻¹ * ·) g v := by
    rintro x rfl v
    rfl
  exact (smul_snd_apply (I := I) g (covectorAtOne (G := G) a) v).trans
    (congrArg a (key _ (mul_one g) v))

/-- The left trivialization of `(g, a)` takes the value `a ξ` on the left-invariant vector field of
`ξ`. -/
@[simp]
theorem leftTrivialization_snd_apply_mulInvariantVectorField (p : G × (E →L[ℝ] ℝ))
    (ξ : GroupLieAlgebra I G) :
    (leftTrivialization I G p).snd (mulInvariantVectorField ξ p.1) = p.2 ξ := by
  rw [leftTrivialization_snd_apply, mfderiv_inv_mul_mulInvariantVectorField]

/-- The inverse of the left trivialization sends a covector at `g` to its base point and its
translate to the identity. -/
theorem leftTrivialization_symm_apply (z : CotangentBundle I G) :
    (leftTrivialization I G).symm z = (z.proj, (z.proj⁻¹ • z).snd) :=
  (rfl)

/-- The inverse of the left trivialization sends a covector to its base point. -/
@[simp]
theorem leftTrivialization_symm_apply_fst (z : CotangentBundle I G) :
    ((leftTrivialization I G).symm z).1 = z.proj :=
  (rfl)

/-- The inverse of the left trivialization sends a covector `z` at `g` to the element of `𝔤*`
whose value on `ξ` is the value of `z` on the left-invariant vector field of `ξ` at `g`. -/
@[simp]
theorem leftTrivialization_symm_apply_snd_apply (z : CotangentBundle I G)
    (ξ : GroupLieAlgebra I G) :
    ((leftTrivialization I G).symm z).2 ξ = z.snd (mulInvariantVectorField ξ z.proj) := by
  have h := leftTrivialization_snd_apply_mulInvariantVectorField ((leftTrivialization I G).symm z) ξ
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm

/-- **Equivariance.** The left trivialization intertwines left multiplication on the first factor
with the cotangent-lifted action of `G` on `T*G`. -/
theorem leftTrivialization_mul (h g : G) (a : E →L[ℝ] ℝ) :
    leftTrivialization I G (h * g, a) = h • leftTrivialization I G (g, a) := by
  rw [leftTrivialization_apply, leftTrivialization_apply, mul_smul]

/-- **Right translation in the left trivialization.** Right multiplication by `h` relates the
covector `Φ (g, a)` to `Φ (g h, Ad*_{h⁻¹} a)`, where `(Ad*_{h⁻¹} a) ζ = a (Ad_h ζ)`: the covector
at `g h` pulls back along `d(R_h)_g` to `Φ (g, a)`. -/
theorem cotangentRel_mul_right_leftTrivialization (g h : G) (a : E →L[ℝ] ℝ) :
    cotangentRel I I (· * h) (leftTrivialization I G (g, a))
      (leftTrivialization I G (g * h, a ∘L Lie.adjointContinuousLinearMap (I := I) h)) := by
  set b : E →L[ℝ] ℝ := a ∘L Lie.adjointContinuousLinearMap (I := I) h
  refine (cotangentRel_iff _ _ _ _ _).2 ⟨by simp, ?_⟩
  -- Replace `Φ (g, a)` by a covector written over its base point `g`.
  have hq : ∀ v : TangentSpace I g,
      (leftTrivialization I G (g, a)).snd v = a (mfderiv I I (g⁻¹ * ·) g v) :=
    leftTrivialization_snd_apply (g, a)
  have hp := proj_leftTrivialization (I := I) (G := G) (g, a)
  generalize leftTrivialization I G (g, a) = z at hq hp ⊢
  obtain ⟨x, q⟩ := z
  obtain rfl : x = g := hp
  ext v
  obtain ⟨ξ, rfl⟩ := exists_mulInvariantVectorField_eq (I := I) (G := G) (g := x) v
  -- `d(R_h)` carries `ξ^L` at `g` to `(Ad_{h⁻¹} ξ)^L` at `g h`, and `Ad_h ∘ Ad_{h⁻¹} = id`.
  exact ((hq _).trans (congrArg a (mfderiv_inv_mul_mulInvariantVectorField ξ x))).trans <|
    (congrArg a (Lie.adjointContinuousLinearMap_adjointContinuousLinearMap_inv h ξ)).symm.trans <|
      (leftTrivialization_snd_apply_mulInvariantVectorField (x * h, b)
        (Lie.adjointContinuousLinearMap (I := I) h⁻¹ ξ)).symm.trans
        (congrArg (leftTrivialization I G (x * h, b)).snd
          (Lie.mfderiv_mul_right_mulInvariantVectorField h x ξ).symm)

/-- **The coadjoint orbit map is the cotangent moment map.** For the cotangent lift of left
multiplication, the moment map of the covector `Φ (g, a)` is `Ad*_g a`. -/
@[simp]
theorem momentMap_leftTrivialization (p : G × (E →L[ℝ] ℝ)) :
    momentMap I G (leftTrivialization I G p) =
      Lie.coadjointRepresentation ℝ I G p.1 (p.2 : E →ₗ[ℝ] ℝ) := by
  rw [leftTrivialization_apply, momentMap_smul]
  congr 1
  ext ξ
  have h : (fun g : G ↦ g • (1 : G)) = id := funext fun g ↦ mul_one g
  rw [momentMap_apply, fundamentalVectorField_apply, h, mfderiv_id]
  -- The covector `p.2` at `1` applied to `id ξ` is `p.2 ξ`, and the coercion of `p.2` to a linear
  -- map has the same values. Rewriting cannot see this because the covector at `1` is typed on
  -- `TangentSpace I 1`, which is only definitionally the model space `E`.
  rfl

/-- The fundamental vector field of `ξ` for the cotangent lift of left multiplication, read in the
left trivialization: at `(g, a)` it is `(ξ^R(g), 0)`, as `h • Φ (g, a) = Φ (h g, a)`. -/
theorem fundamentalVectorField_leftTrivialization (ξ : GroupLieAlgebra I G)
    (p : G × (E →L[ℝ] ℝ)) :
    fundamentalVectorField (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ξ (leftTrivialization I G p) =
      mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (leftTrivialization I G) p
        ((mulRightInvariantVectorField ξ p.1, 0) : E × (E →L[ℝ] ℝ)) := by
  obtain ⟨k, a⟩ := p
  -- `h • Φ (k, a) = Φ (h k, a)`, so the orbit map of `Φ (k, a)` at `1` is that of `Φ (1, a)` at
  -- `k`, which is `Φ` composed with the slice `x ↦ (x, a)`.
  have hfun : (fun h : G ↦ h • leftTrivialization I G (1, a)) =
      leftTrivialization I G ∘ fun x : G ↦ (x, a) := by
    funext h
    simp [← leftTrivialization_mul]
  have hs : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (fun x : G ↦ (x, a)) k :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hΦ : MDifferentiableAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (leftTrivialization I G) (k, a) :=
    ((leftTrivialization I G).contMDiff _).mdifferentiableAt (by simp)
  have h := mfderiv_smul_mulRightInvariantVectorField (I' := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ξ k
    (leftTrivialization I G (1, a))
  rw [← leftTrivialization_mul, mul_one, hfun, mfderiv_comp_apply k hΦ hs, mfderiv_prod_left] at h
  -- `ContinuousLinearMap.inl` is `v ↦ (v, 0)` by definition. Its codomain, the product of the
  -- coordinate tangent spaces, is the tangent space of the product only by definition, so
  -- `ContinuousLinearMap.inl_apply` cannot be rewritten here.
  exact h.symm

/-- **The left-trivialized value from the moment map.** The covector `z` over `g` translates to the
identity as `Ad*_{g⁻¹} μ(z)`, the second component of `Φ⁻¹ z`. -/
theorem coadjointRepresentation_proj_inv_momentMap (z : CotangentBundle I G) :
    Lie.coadjointRepresentation ℝ I G z.proj⁻¹ (momentMap I G z) =
      (((leftTrivialization I G).symm z).2 : E →ₗ[ℝ] ℝ) := by
  obtain ⟨p, rfl⟩ : ∃ p, leftTrivialization I G p = z :=
    ⟨_, (leftTrivialization I G).apply_symm_apply z⟩
  rw [momentMap_leftTrivialization, proj_leftTrivialization, Diffeomorph.symm_apply_apply]
  exact Representation.inv_self_apply _ _ _

/-- A covector of `T*G` is determined by its base point and its moment map for the cotangent lift
of left multiplication. -/
theorem eq_of_proj_eq_of_momentMap_eq {z z' : CotangentBundle I G} (hπ : z.proj = z'.proj)
    (hμ : momentMap I G z = momentMap I G z') : z = z' := by
  have h := coadjointRepresentation_proj_inv_momentMap z
  rw [hπ, hμ, coadjointRepresentation_proj_inv_momentMap] at h
  rw [← (leftTrivialization I G).apply_symm_apply z, ← (leftTrivialization I G).apply_symm_apply z']
  exact congrArg _ (Prod.ext hπ (ContinuousLinearMap.coe_injective h.symm))

/-- Every point `g` of `G` is the base point of a covector with any prescribed moment map `c` for
the cotangent lift of left multiplication, namely the left translate of `Ad*_{g⁻¹} c`. -/
theorem exists_momentMap_eq_and_proj_eq [FiniteDimensional ℝ E]
    (c : Module.Dual ℝ (GroupLieAlgebra I G)) (g : G) :
    ∃ z : CotangentBundle I G, momentMap I G z = c ∧ z.proj = g := by
  refine ⟨leftTrivialization I G
    (g, LinearMap.toContinuousLinearMap (Lie.coadjointRepresentation ℝ I G g⁻¹ c : E →ₗ[ℝ] ℝ)),
    ?_, proj_leftTrivialization _⟩
  rw [momentMap_leftTrivialization]
  exact Representation.self_inv_apply _ _ _

/-! ### The canonical forms in the left trivialization -/

/-- **The Liouville form in the left trivialization** is `⟨a, θ⟩`: it sends a tangent vector
`(v, α)` at `(g, a)` to `a (d(L_{g⁻¹})_g v)`. -/
theorem mpullback_leftTrivialization_liouvilleForm_apply (p : G × (E →L[ℝ] ℝ))
    (v : Fin 1 → TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) p) :
    (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
      (liouvilleForm I G)).val p v = p.2 (mfderiv I I (p.1⁻¹ * ·) p.1 (v 0).1) := by
  rw [SmoothForm.coe_mpullback, mpullback_liouvilleForm_apply_of_proj_comp_eq (g := Prod.fst)
    (fun q ↦ proj_leftTrivialization q)
    (((leftTrivialization I G).contMDiff p).mdifferentiableAt (by simp)), mfderiv_fst]
  exact leftTrivialization_snd_apply p (v 0).1

/-- The canonical symplectic form of `T*G`, read in the left trivialization, is a symplectic form
on `G × 𝔤*`. -/
theorem isSymplectic_mpullback_leftTrivialization_symplecticForm :
    SmoothTwoForm.IsSymplectic (SmoothForm.mpullback (leftTrivialization I G)
      (leftTrivialization I G).contMDiff (symplecticForm I G)) :=
  ((leftTrivialization I G).isLocalDiffeomorph.isSymplectic_mpullback_iff
    (leftTrivialization I G).surjective).2 isSymplectic_symplecticForm

/-- The Liouville form in the left trivialization takes the value `a ξ` on a product field
`(ξ^L, Y)` at `(g, a)`. -/
private theorem liouville_prodVectorField (ξ : GroupLieAlgebra I G)
    (Y : Π a : E →L[ℝ] ℝ, TangentSpace 𝓘(ℝ, E →L[ℝ] ℝ) a) (p : G × (E →L[ℝ] ℝ)) :
    (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
      (liouvilleForm I G)).val p ![prodVectorField (mulInvariantVectorField ξ) Y p] = p.2 ξ := by
  rw [mpullback_leftTrivialization_liouvilleForm_apply, Matrix.cons_val_zero, prodVectorField_fst,
    mfderiv_inv_mul_mulInvariantVectorField]

variable [CompleteSpace E]

/-- The bracket of the product fields `(ξ^L, α)` and `(η^L, β)` on `G × 𝔤*`, with `α` and `β`
constant, is `(⁅ξ, η⁆^L, 0)`. -/
private theorem mlieBracket_prodVectorField_mulInvariantVectorField (ξ η : GroupLieAlgebra I G)
    (α β : E →L[ℝ] ℝ) (p : G × (E →L[ℝ] ℝ)) :
    mlieBracket (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
        (prodVectorField (mulInvariantVectorField ξ) (constVectorField α))
        (prodVectorField (mulInvariantVectorField η) (constVectorField β)) p =
      prodVectorField (mulInvariantVectorField ⁅ξ, η⁆) 0 p := by
  rw [mlieBracket_prodVectorField (mdifferentiable_mulInvariantVectorField ξ _)
    (mdifferentiable_mulInvariantVectorField η _) (mdifferentiable_constVectorField α _)
    (mdifferentiable_constVectorField β _), mlieBracket_constVectorField,
    ← mulInvariantVector_mlieBracket, ← GroupLieAlgebra.bracket_def]

/-- **The canonical symplectic form in the left trivialization.** At `(g, a)` it pairs the tangent
vectors `(v, α)` and `(w, β)` to `β (θ v) - α (θ w) + a ⁅θ v, θ w⁆`, where `θ = d(L_{g⁻¹})_g`
translates tangent vectors at `g` to the Lie algebra and the last term is the Kirillov form of `a`
(`Module.Dual.kirillovForm`). -/
theorem eval₂_mpullback_leftTrivialization_symplecticForm (p : G × (E →L[ℝ] ℝ))
    (v w : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) p) :
    (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
      (symplecticForm I G)).eval₂ p v w =
      w.2 (mfderiv I I (p.1⁻¹ * ·) p.1 v.1) - v.2 (mfderiv I I (p.1⁻¹ * ·) p.1 w.1) +
        Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (p.2 : E →ₗ[ℝ] ℝ)
          (mfderiv I I (p.1⁻¹ * ·) p.1 v.1) (mfderiv I I (p.1⁻¹ * ·) p.1 w.1) := by
  -- Write `v` and `w` as the values at `p` of product fields `(ξ^L, α)` and `(η^L, β)`.
  obtain ⟨ξ, hξ⟩ := exists_mulInvariantVectorField_eq (I := I) (G := G) (g := p.1) v.1
  obtain ⟨η, hη⟩ := exists_mulInvariantVectorField_eq (I := I) (G := G) (g := p.1) w.1
  set X := prodVectorField (mulInvariantVectorField ξ) (constVectorField v.2)
  set Y := prodVectorField (mulInvariantVectorField η) (constVectorField w.2)
  have hreal (u : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) p) (ζ : GroupLieAlgebra I G)
      (hζ : mulInvariantVectorField ζ p.1 = u.1) :
      prodVectorField (mulInvariantVectorField ζ) (constVectorField u.2) p = u :=
    (tangentSpaceProdEquiv p).injective <| by
      rw [tangentSpaceProdEquiv_prodVectorField, tangentSpaceProdEquiv_apply]
      exact Prod.ext hζ
        ((constVectorField_apply _ _).trans (NormedSpace.fromTangentSpace_symm_apply _ _))
  have hv : X p = v := hreal v ξ hξ
  have hw : Y p = w := hreal w η hη
  set lam := SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
    (liouvilleForm I G)
  have hX : MDifferentiableAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).tangent
      (T% X) p :=
    mdifferentiableAt_prodVectorField (mdifferentiable_mulInvariantVectorField ξ _)
      (mdifferentiable_constVectorField _ _)
  have hY : MDifferentiableAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).tangent
      (T% Y) p :=
    mdifferentiableAt_prodVectorField (mdifferentiable_mulInvariantVectorField η _)
      (mdifferentiable_constVectorField _ _)
  -- On the field `(ζ^L, γ)` the Liouville form is `(g, a) ↦ a ζ`, a function of `a` alone. The
  -- vector `ζ` of `GroupLieAlgebra I G`, definitionally the model space `E`, is retyped by `@id E`
  -- so that the evaluation map is type-correct on `E →L[ℝ] ℝ` for `mvfderiv_apply_eval`.
  have hlam (ζ : GroupLieAlgebra I G) (γ : E →L[ℝ] ℝ) :
      (fun q ↦ lam.val q ![prodVectorField (mulInvariantVectorField ζ) (constVectorField γ) q]) =
        (fun a : E →L[ℝ] ℝ ↦ a (@id E ζ)) ∘ Prod.snd :=
    funext fun q ↦ liouville_prodVectorField ζ (constVectorField γ) q
  -- The invariant formula `dλ(X, Y) = X(λ Y) - Y(λ X) - λ [X, Y]`, with `ω = -dλ`.
  have hω : (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
      (symplecticForm I G)).eval₂ p (X p) (Y p) = -(mextDeriv lam.val p ![X p, Y p]) := by
    rw [symplecticForm_eq_neg_mextDerivₗ, map_neg, ← SmoothForm.mextDerivₗ_mpullback,
      SmoothBundleForm.eval₂_apply, NegMemClass.coe_neg, Pi.neg_apply, mextDerivₗ_apply,
      ContinuousAlternatingMap.neg_apply]
  rw [← hv, ← hw, hω, SmoothForm.mextDeriv_apply_one hX hY, hlam, hlam,
    mlieBracket_prodVectorField_mulInvariantVectorField, liouville_prodVectorField,
    mvfderiv_comp_snd_apply, mvfderiv_comp_snd_apply, mvfderiv_apply_eval, mvfderiv_apply_eval]
  simp only [X, Y, prodVectorField_fst, prodVectorField_snd, constVectorField_apply,
    NormedSpace.fromTangentSpace_symm_apply, id, mfderiv_inv_mul_mulInvariantVectorField]
  have hk : Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (p.2 : E →ₗ[ℝ] ℝ) ξ η =
      p.2 (⁅ξ, η⁆ : GroupLieAlgebra I G) :=
    (Module.Dual.kirillovForm_apply _ ξ η).trans (congrFun (ContinuousLinearMap.coe_coe p.2) _)
  linear_combination -hk

/-- **The form `-d⟨f, θ⟩` on `G × N`.** Pulling the left-trivialized canonical symplectic form back
along `id × f` for a smooth map `f : N → 𝔤*` gives the two-form that pairs `(v, u)` and `(w, u')`
at `(g, n)` to `df_n u' (θ v) - df_n u (θ w) + f n ⁅θ v, θ w⁆`, where `θ = d(L_{g⁻¹})_g`. -/
theorem eval₂_mpullback_prodMap_leftTrivialization_symplecticForm {EN HN : Type*}
    [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {IN : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    [IsManifold IN 1 N] {f : N → E →L[ℝ] ℝ} (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) (p : G × N)
    (v w : TangentSpace (I.prod IN) p) :
    (SmoothForm.mpullback (Prod.map id f) (contMDiff_id.prodMap hf)
      (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
        (symplecticForm I G))).eval₂ p v w =
      mvfderiv IN f p.2 w.2 (mfderiv I I (p.1⁻¹ * ·) p.1 v.1) -
        mvfderiv IN f p.2 v.2 (mfderiv I I (p.1⁻¹ * ·) p.1 w.1) +
        Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (f p.2 : E →ₗ[ℝ] ℝ)
          (mfderiv I I (p.1⁻¹ * ·) p.1 v.1) (mfderiv I I (p.1⁻¹ * ·) p.1 w.1) := by
  rw [SmoothForm.eval₂_mpullback, eval₂_mpullback_leftTrivialization_symplecticForm,
    mfderiv_prodMap mdifferentiableAt_id ((hf p.2).mdifferentiableAt (by simp)), mfderiv_id]
  -- `ContinuousLinearMap.prodMap` acts componentwise and `Prod.map id f p = (p.1, f p.2)`, both
  -- definitionally.
  rfl

end TauCeti.CotangentBundle

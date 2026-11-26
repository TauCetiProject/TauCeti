/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.Orbit
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LeftTrivialization
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Naturality

/-!
# Cotangent reduction of a Lie group: coadjoint orbits as reduced spaces

Let `G` be a real Lie group with finite-dimensional boundaryless model and Lie algebra `𝔤`, acting
on its cotangent bundle `T*G` by the cotangent lift of left multiplication, with canonical form
`ω = -dλ` and moment map `μ`; in the left trivialization `T*G ≃ G × 𝔤*`, `(g, a) ↦ g • a`, the
moment map is `μ(g, a) = Ad*_g a` (`TauCeti.CotangentBundle.momentMap_leftTrivialization`). The
action is free and proper and every value of `μ` is regular, so for every `c ∈ 𝔤*`, coadjoint-fixed
or not, the Marsden–Weinstein–Meyer theorem makes `T*G //_c G = μ⁻¹(c) / G_c` a symplectic
manifold. This file identifies it with the coadjoint orbit of `c`:

`T*G //_c G ≅ (G ⧸ G_c, -ω_c)`,

where `G ⧸ G_c` is the homogeneous coadjoint orbit and `ω_c` its Kirillov–Kostant–Souriau form
(`TauCeti.CotangentBundle.reducedSpaceCoadjointOrbitDiffeomorph`). The diffeomorphism sends the
orbit of a covector `z ∈ μ⁻¹(c)` over `g` to the coset of `g⁻¹`; under the orbit map
`[k] ↦ Ad*_k c` this is the point `Ad*_{g⁻¹} c = a` of the orbit, the left-trivialized value of `z`
(`TauCeti.CotangentBundle.orbitMap_reducedSpaceCoadjointOrbitDiffeomorph_mk`).
The sign is forced: in the conventions `ι_(ξ_M) ω = d⟨μ, ξ⟩` and `(Ad*_g ν)(ξ) = ν(Ad_{g⁻¹} ξ)`,
the reduced form is the opposite of the KKS form
(`TauCeti.CotangentBundle.mpullback_reducedSpaceCoadjointOrbitDiffeomorph_neg_coadjointOrbitForm`).
This is the case `Q = G` of cotangent reduction at values that are not coadjoint-invariant, where
the orbit space `Q ⧸ G` is a point and the coadjoint orbit bundle over it is the orbit itself.

The proof computes in the left trivialization.

* **The level.** A fundamental vector field of the lifted action is `(ξ^R(g), 0)` at `(g, a)`
  (`TauCeti.CotangentBundle.fundamentalVectorField_leftTrivialization`). So a tangent vector
  `(v, α)` lies in `ker dμ`, the vectors `ω`-orthogonal to all fundamental vectors, exactly when
  `α ζ = a ⁅θ v, ζ⁆` for every `ζ`, where `θ = d(L_{g⁻¹})_g`. On two such vectors the formula
  `ω((v, α), (w, β)) = β (θ v) - α (θ w) + a ⁅θ v, θ w⁆`
  (`TauCeti.CotangentBundle.eval₂_mpullback_leftTrivialization_symplecticForm`) becomes
  `-a ⁅θ v, θ w⁆`.
* **Inversion.** The derivative of inversion satisfies `θ_{g⁻¹}(d(inv)_g v) = -Ad_g (θ_g v)`
  (`TauCeti.Lie.mfderiv_inv_mul_mfderiv_inv`), so the left-invariant Kirillov form `σ_c` of `c`,
  pulled back along `z ↦ π(z)⁻¹`, pairs the same vectors to
  `c ⁅Ad_g θ v, Ad_g θ w⁆ = (Ad*_{g⁻¹} c) ⁅θ v, θ w⁆ = a ⁅θ v, θ w⁆`, since `Ad*_g a = c`. Hence `ω`
  is minus this pullback on `ker dμ`
  (`TauCeti.CotangentBundle.eval₂_symplecticForm_eq_neg_of_differential_eq_zero`).
* **Recognition.** Since `σ_c` is the pullback of `ω_c` along `G → G ⧸ G_c`, the map
  `z ↦ [π(z)⁻¹]` from the level to `G ⧸ G_c` pulls `-ω_c` back to the restriction of `ω`. It is
  onto, its fibres are the `G_c`-orbits, because a covector of `T*G` is determined by its base point
  and its moment map (`TauCeti.CotangentBundle.eq_of_proj_eq_of_momentMap_eq`), and both sides have
  dimension `dim 𝔤 - dim 𝔤_c`. The recognition of reduced spaces
  (`TauCeti.SmoothTwoForm.exists_diffeomorph_comp_eq_and_mpullback_eq`) then gives the
  diffeomorphism.

## Main definitions

* `TauCeti.CotangentBundle.reducedSpaceCoadjointOrbitDiffeomorph`: the diffeomorphism
  `μ⁻¹(c) / G_c ≅ G ⧸ G_c`.

## Main results

* `TauCeti.CotangentBundle.eval₂_symplecticForm_eq_neg_of_differential_eq_zero`: on `ker dμ` at a
  point of `μ⁻¹(c)`, the canonical form is minus the pullback of `σ_c` along `z ↦ π(z)⁻¹`.
* `TauCeti.CotangentBundle.reducedSpaceCoadjointOrbitDiffeomorph_mk`: the diffeomorphism sends the
  orbit of `z` to the coset of `π(z)⁻¹`.
* `TauCeti.CotangentBundle.orbitMap_reducedSpaceCoadjointOrbitDiffeomorph_mk`: followed by the
  orbit map into `𝔤*`, it sends the orbit of `z` to the left-trivialized value of `z`.
* `TauCeti.CotangentBundle.mpullback_reducedSpaceCoadjointOrbitDiffeomorph_neg_coadjointOrbitForm`:
  it pulls `-ω_c` back to the reduced symplectic form.

## References

* J. E. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130 (coadjoint orbits as reduced spaces of `T*G`).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Chapters 13 and 14 (the left trivialization of `T*G`, and the
  coadjoint orbit with the minus orbit symplectic form as the reduced space for the left action).
-/

public section

noncomputable section

open Function Module Manifold TauCeti.Lie
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {c : Module.Dual ℝ (GroupLieAlgebra I G)}

section Level

/-- In the left trivialization, a tangent vector `(v, α)` at `(g, a)` that is `ω`-orthogonal to all
fundamental vectors `(ξ^R(g), 0)` satisfies `α ζ = a ⁅θ v, ζ⁆` for every `ζ`, where
`θ = d(L_{g⁻¹})_g`. -/
private theorem apply_eq_of_forall_eval₂_eq_zero (p : G × (E →L[ℝ] ℝ))
    (v : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) p)
    (hv : ∀ ξ : GroupLieAlgebra I G,
      (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
        (symplecticForm I G)).eval₂ p
          ((mulRightInvariantVectorField ξ p.1, 0) : E × (E →L[ℝ] ℝ)) v = 0)
    (ζ : GroupLieAlgebra I G) :
    v.2 ζ = Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (p.2 : E →ₗ[ℝ] ℝ)
      (mfderiv I I (p.1⁻¹ * ·) p.1 v.1) ζ := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have h := (eval₂_mpullback_leftTrivialization_symplecticForm p
    ((mulRightInvariantVectorField (adjointContinuousLinearMap (I := I) p.1 ζ) p.1, 0) :
      E × (E →L[ℝ] ℝ)) v).symm.trans (hv _)
  dsimp only at h
  rw [← mulInvariantVectorField_eq_mulRightInvariantVectorField_adjoint,
    mfderiv_inv_mul_mulInvariantVectorField] at h
  -- The dual component of `(ξ^R, 0)` is the zero functional, typed on the cotangent fibre of the
  -- model; `zero_apply` does not match it there, so its value `0` is restated by `change`.
  change v.2 ζ - 0 + Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (p.2 : E →ₗ[ℝ] ℝ) ζ
    (mfderiv I I (p.1⁻¹ * ·) p.1 v.1) = 0 at h
  have hs := LinearMap.IsAlt.neg
    (Module.Dual.isAlt_kirillovForm (L := GroupLieAlgebra I G) (p.2 : E →ₗ[ℝ] ℝ)) ζ
    (mfderiv I I (p.1⁻¹ * ·) p.1 v.1)
  linear_combination h + hs

/-- In the left trivialization, on two tangent vectors `(v, α)` and `(w, β)` at `(g, a)` that are
`ω`-orthogonal to all fundamental vectors, the canonical form is `-a ⁅θ v, θ w⁆`. -/
private theorem eval₂_eq_neg_kirillovForm_of_forall_eval₂_eq_zero (p : G × (E →L[ℝ] ℝ))
    (v w : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) p)
    (hv : ∀ ξ : GroupLieAlgebra I G,
      (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
        (symplecticForm I G)).eval₂ p
          ((mulRightInvariantVectorField ξ p.1, 0) : E × (E →L[ℝ] ℝ)) v = 0)
    (hw : ∀ ξ : GroupLieAlgebra I G,
      (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
        (symplecticForm I G)).eval₂ p
          ((mulRightInvariantVectorField ξ p.1, 0) : E × (E →L[ℝ] ℝ)) w = 0) :
    (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
      (symplecticForm I G)).eval₂ p v w =
      -Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (p.2 : E →ₗ[ℝ] ℝ)
        (mfderiv I I (p.1⁻¹ * ·) p.1 v.1) (mfderiv I I (p.1⁻¹ * ·) p.1 w.1) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  rw [eval₂_mpullback_leftTrivialization_symplecticForm]
  have hv' := apply_eq_of_forall_eval₂_eq_zero p v hv (mfderiv I I (p.1⁻¹ * ·) p.1 w.1)
  have hw' := apply_eq_of_forall_eval₂_eq_zero p w hw (mfderiv I I (p.1⁻¹ * ·) p.1 v.1)
  have hs := LinearMap.IsAlt.neg
    (Module.Dual.isAlt_kirillovForm (L := GroupLieAlgebra I G) (p.2 : E →ₗ[ℝ] ℝ))
    (mfderiv I I (p.1⁻¹ * ·) p.1 v.1) (mfderiv I I (p.1⁻¹ * ·) p.1 w.1)
  linear_combination hw' - hv' - hs

omit [FiniteDimensional ℝ E] in
/-- Inversion of the base point, `z ↦ π(z)⁻¹`, is a smooth map `T*G → G`. -/
private theorem contMDiff_inv_proj :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I ∞ fun z : CotangentBundle I G ↦ z.proj⁻¹ :=
  (contMDiff_inv I ∞).comp (Bundle.contMDiff_proj _)

/-- **The canonical form on a level of `T*G`.** For the cotangent lift of left multiplication, at
a covector `z` with `μ(z) = c` the canonical symplectic form `ω` agrees on `ker dμ_z` with minus
the pullback of the left-invariant Kirillov form `σ_c` of `c` along `z ↦ π(z)⁻¹`. -/
theorem eval₂_symplecticForm_eq_neg_of_differential_eq_zero
    (h : (symplecticForm I G).IsEquivariantMomentMap (momentMap I G)) {z : CotangentBundle I G}
    (hz : momentMap I G z = c) {V W : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z}
    (hV : h.differential z V = 0) (hW : h.differential z W = 0) :
    (symplecticForm I G).eval₂ z V W =
      -(SmoothForm.mpullback (fun z : CotangentBundle I G ↦ z.proj⁻¹)
        ((contMDiff_inv I ∞).comp (Bundle.contMDiff_proj _))
        c.leftInvariantKirillovForm).eval₂ z V W := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  obtain ⟨p, rfl⟩ : ∃ p, leftTrivialization I G p = z :=
    ⟨_, (leftTrivialization I G).apply_symm_apply z⟩
  obtain ⟨v, rfl⟩ : ∃ v, mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (leftTrivialization I G) p v = V :=
    ⟨_, (leftTrivialization I G).mfderiv_apply_mfderiv_symm_apply (by simp) p V⟩
  obtain ⟨w, rfl⟩ : ∃ w, mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (leftTrivialization I G) p w = W :=
    ⟨_, (leftTrivialization I G).mfderiv_apply_mfderiv_symm_apply (by simp) p W⟩
  -- Vectors in `ker dμ` are `ω`-orthogonal to the fundamental vectors `(ξ^R, 0)`.
  have horth {u : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) p}
      (hu : h.differential _ (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
        (leftTrivialization I G) p u) = 0) (ξ : GroupLieAlgebra I G) :
      (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
        (symplecticForm I G)).eval₂ p
          ((mulRightInvariantVectorField ξ p.1, 0) : E × (E →L[ℝ] ℝ)) u = 0 := by
    refine (SmoothForm.eval₂_mpullback _ _ _ p _ u).trans ?_
    rw [← fundamentalVectorField_leftTrivialization, ← InfinitesimalAction.fundamental_apply,
      ← h.differential_apply_eq_eval₂, hu]
    rfl
  -- Both sides are computed in the left trivialization at `p = (g, a)`.
  have hfun : (fun z : CotangentBundle I G ↦ z.proj⁻¹) ∘ leftTrivialization I G =
      (fun g : G ↦ g⁻¹) ∘ Prod.fst :=
    funext fun q ↦ by simp
  have hd (u : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) p) :
      mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I ((fun g : G ↦ g⁻¹) ∘ Prod.fst) p u =
        mfderiv I I (fun g : G ↦ g⁻¹) p.1 u.1 := by
    rw [mfderiv_comp_apply p ((contMDiff_inv I ∞).mdifferentiableAt (by simp))
      mdifferentiableAt_fst, mfderiv_fst]
    rfl
  rw [← SmoothForm.eval₂_mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
      (symplecticForm I G),
    ← SmoothForm.eval₂_mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff,
    eval₂_eq_neg_kirillovForm_of_forall_eval₂_eq_zero p v w (horth hV) (horth hW),
    SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_congr _ ((contMDiff_inv I ∞).comp contMDiff_fst) hfun,
    SmoothForm.eval₂_mpullback, ← SmoothForm.bilinFormAt_apply, hd, hd, Function.comp_apply,
    Module.Dual.bilinFormAt_leftInvariantKirillovForm_apply]
  -- The translates `θ_{g⁻¹}(d(inv) v)` are typed in tangent spaces of `G` at `g⁻¹`, and the
  -- brackets in the Lie algebra; both are the model space `E`, and `rw` cannot match the lemmas
  -- across these definitionally equal types, so `erw` is used.
  erw [mfderiv_inv_mul_mfderiv_inv, mfderiv_inv_mul_mfderiv_inv]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  rw [Module.Dual.kirillovForm_apply]
  erw [← adjointContinuousLinearMap_lie]
  -- `c (Ad_g ⁅θ v, θ w⁆) = (Ad*_g a) (Ad_g ⁅θ v, θ w⁆) = a ⁅θ v, θ w⁆`, as `μ(z) = Ad*_g a = c`.
  rw [← hz, momentMap_leftTrivialization]
  refine congrArg Neg.neg ((Module.Dual.kirillovForm_apply (L := GroupLieAlgebra I G) _ _ _).trans
    (Eq.trans ?_ (Lie.coadjointRepresentation_apply _ _ _).symm))
  rw [← ContinuousLinearMap.comp_apply, ← adjointContinuousLinearMap_mul, inv_mul_cancel,
    adjointContinuousLinearMap_one, ContinuousLinearMap.id_apply]

variable (c) in
/-- Every point `g` of `G` is the base point of a covector in each level `μ⁻¹(c)`, namely the
left translate of `Ad*_{g⁻¹} c`. -/
private theorem exists_momentMap_eq_and_proj_eq (g : G) :
    ∃ z : CotangentBundle I G, momentMap I G z = c ∧ z.proj = g := by
  refine ⟨leftTrivialization I G
    (g, LinearMap.toContinuousLinearMap (Lie.coadjointRepresentation ℝ I G g⁻¹ c : E →ₗ[ℝ] ℝ)),
    ?_, proj_leftTrivialization _⟩
  rw [momentMap_leftTrivialization]
  exact Representation.self_inv_apply _ _ _

end Level

section ReducedSpace

variable [I.Boundaryless] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {n : ℕ}
  {h : (symplecticForm I G).IsEquivariantMomentMap (momentMap I G)}
  (hreg : ∀ z, momentMap I G z = c → Surjective (h.differential z))
  (hn : finrank ℝ (E × (E →L[ℝ] ℝ)) - finrank ℝ (GroupLieAlgebra I G) = n)
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)

/-- The map `z ↦ [π(z)⁻¹]` from the level `μ⁻¹(c)` to the coadjoint orbit `G ⧸ G_c` is smooth. -/
private theorem contMDiff_quotientMk_inv_proj :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    haveI := h.isManifold_levelSubMulAction hreg hn
    ContMDiff 𝓘(ℝ, Fin n → ℝ)
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) ∞
      fun z : h.levelSubMulAction c ↦
        (((z : CotangentBundle I G).proj⁻¹ : G) :
          G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  exact ((c.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff.comp
    contMDiff_inv_proj).comp (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff :)

/-- The map `z ↦ [π(z)⁻¹]` pulls minus the KKS form of `G ⧸ G_c` back to the restriction of the
canonical symplectic form to the level `μ⁻¹(c)`. -/
private theorem mpullback_quotientMk_inv_proj_neg_coadjointOrbitForm :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    haveI := h.isManifold_levelSubMulAction hreg hn
    SmoothForm.mpullback _ (contMDiff_quotientMk_inv_proj hreg hn) (-c.coadjointOrbitForm) =
      SmoothForm.mpullback Subtype.val
        (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff (symplecticForm I G) := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  have hi := (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
  have hq := c.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff
  rw [SmoothForm.mpullback_congr (contMDiff_quotientMk_inv_proj hreg hn)
      ((hq.comp contMDiff_inv_proj).comp hi) rfl,
    ← SmoothForm.mpullback_mpullback _ _ hi (hq.comp contMDiff_inv_proj),
    ← SmoothForm.mpullback_mpullback _ _ contMDiff_inv_proj hq, map_neg,
    c.mpullback_quotientMk_coadjointOrbitForm]
  refine SmoothBundleForm.ext_eval₂ fun z v w ↦ ?_
  -- The level is tangent to `ker dμ`.
  have hker (u : TangentSpace 𝓘(ℝ, Fin n → ℝ) z) :
      h.differential z (mfderiv 𝓘(ℝ, Fin n → ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) Subtype.val z u) = 0 :=
    LinearMap.mem_ker.1 (h.range_mfderiv_coe_levelSubMulAction hreg hn z ▸
      LinearMap.mem_range_self _ u)
  rw [SmoothForm.eval₂_mpullback Subtype.val, SmoothForm.eval₂_mpullback Subtype.val, map_neg,
    SmoothBundleForm.eval₂_neg, eval₂_symplecticForm_eq_neg_of_differential_eq_zero h
      (h.mem_levelSubMulAction.1 z.property) (hker v) (hker w)]

/-- The map `z ↦ [π(z)⁻¹]` on the level descends to a diffeomorphism from the reduced space onto
the coadjoint orbit `G ⧸ G_c`, by the recognition of reduced spaces
`TauCeti.SmoothTwoForm.exists_diffeomorph_comp_eq_and_mpullback_eq`: it is onto, its fibres are the
`G_c`-orbits, it pulls minus the KKS form back to the restriction of the canonical form, and both
sides have dimension `dim 𝔤 - dim 𝔤_c`. -/
private theorem exists_diffeomorph_quotientMk_eq_inv_proj :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := properSMul (IG := I) (G := G) (I := I) (M := G)
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    ∃ Φ : MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)),
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c))⟯
        G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c,
      ∀ z : h.levelSubMulAction c, Φ (Quotient.mk _ z) =
        (((z : CotangentBundle I G).proj⁻¹ : G) :
          G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := properSMul (IG := I) (G := G) (I := I) (M := G)
  let := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  obtain ⟨η, ⟨hηs, hη⟩, -⟩ := h.existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback hreg
    hn d isSymplectic_symplecticForm mpullback_smul_symplecticForm
  refine (SmoothTwoForm.exists_diffeomorph_comp_eq_and_mpullback_eq
    (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d) Quotient.mk_surjective
    hηs.isNondegenerate (contMDiff_quotientMk_inv_proj hreg hn) (fun w ↦ ?_) (fun z z' ↦ ?_) ?_
    ((mpullback_quotientMk_inv_proj_neg_coadjointOrbitForm hreg hn).trans hη.symm)).imp
    fun Φ hΦ z ↦ congrFun hΦ.1 z
  · induction w using QuotientGroup.induction_on with | H g => ?_
    obtain ⟨z, hz, hzg⟩ := exists_momentMap_eq_and_proj_eq c g⁻¹
    exact ⟨⟨z, h.mem_levelSubMulAction.2 hz⟩, by simp [hzg]⟩
  · have hz := h.mem_levelSubMulAction.1 z.property
    have hz' := h.mem_levelSubMulAction.1 z'.property
    rw [QuotientGroup.eq, inv_inv, Quotient.eq,
      h.orbitRel_levelSubMulAction_iff, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · intro hk
      refine ⟨(z : CotangentBundle I G).proj * (z' : CotangentBundle I G).proj⁻¹,
        eq_of_proj_eq_of_momentMap_eq ?_ ?_⟩
      · rw [proj_smul, smul_eq_mul, inv_mul_cancel_right]
      · rw [momentMap_smul, hz', hz]
        exact Representation.mem_stabilizer.1 hk
    · rintro ⟨g, hg⟩
      rw [← hg, proj_smul, smul_eq_mul, mul_inv_cancel_right]
      refine Representation.mem_stabilizer.2 ?_
      rw [← hz', ← momentMap_smul, hg, hz, hz']
  · -- Both sides have dimension `dim 𝔤 - dim 𝔤_c`.
    obtain ⟨z₀, hz₀, -⟩ := exists_momentMap_eq_and_proj_eq c (1 : G)
    have h₁ := h.finrank_quotientModelSpace_add_finrank_add_finrank_lieAnnihilator hreg hn d
      isSymplectic_symplecticForm.isNondegenerate ⟨z₀, h.mem_levelSubMulAction.2 hz₀⟩
    have h₂ := c.finrank_quotientModelSpace_add_finrank_lieAnnihilator
    -- The Lie algebra `GroupLieAlgebra I G` is by definition the tangent space `E` at `1`.
    have hG : finrank ℝ (GroupLieAlgebra I G) = finrank ℝ E := rfl
    rw [finrank_prod, ContinuousLinearMap.dual_finrank_eq, hG] at h₁
    omega

variable (h) in
/-- **Cotangent reduction of a Lie group at an arbitrary value.** For the cotangent lift of left
multiplication of a Lie group `G` on `T*G`, the Marsden–Weinstein–Meyer reduced space
`T*G //_c G = μ⁻¹(c) / G_c` at any `c ∈ 𝔤*`, with the atlas of the Marsden–Weinstein–Meyer
theorem, is diffeomorphic to the coadjoint orbit `G ⧸ G_c` of `c`. The diffeomorphism sends the
orbit of a covector `z` in `μ⁻¹(c)` to the coset of `π(z)⁻¹`
(`TauCeti.CotangentBundle.reducedSpaceCoadjointOrbitDiffeomorph_mk`), and it carries minus the
Kirillov–Kostant–Souriau form of the orbit to the reduced symplectic form
(`TauCeti.CotangentBundle.mpullback_reducedSpaceCoadjointOrbitDiffeomorph_neg_coadjointOrbitForm`).

The hypotheses `h` and `hreg` are those of the atlas: they hold by
`TauCeti.CotangentBundle.isEquivariantMomentMap_momentMap` and
`TauCeti.CotangentBundle.differential_momentMap_surjective`. -/
def reducedSpaceCoadjointOrbitDiffeomorph :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := properSMul (IG := I) (G := G) (I := I) (M := G)
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)),
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c))⟯
      G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c :=
  (exists_diffeomorph_quotientMk_eq_inv_proj hreg hn d).choose

/-- The diffeomorphism `T*G //_c G ≃ G ⧸ G_c` sends the orbit of a covector `z` in `μ⁻¹(c)` to the
coset of the inverse `π(z)⁻¹` of its base point. -/
@[simp]
theorem reducedSpaceCoadjointOrbitDiffeomorph_mk (z : h.levelSubMulAction c) :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := properSMul (IG := I) (G := G) (I := I) (M := G)
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    reducedSpaceCoadjointOrbitDiffeomorph h hreg hn d (Quotient.mk _ z) =
      (((z : CotangentBundle I G).proj⁻¹ : G) :
        G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) :=
  (exists_diffeomorph_quotientMk_eq_inv_proj hreg hn d).choose_spec z

/-- **Cotangent reduction of a Lie group: the symplectic forms.** The diffeomorphism
`μ⁻¹(c) / G_c ≅ G ⧸ G_c` pulls minus the Kirillov–Kostant–Souriau form `ω_c` of the coadjoint orbit
back to the reduced symplectic form `η` of the Marsden–Weinstein–Meyer theorem, the form on the
reduced space with `π^* η = i^* ω` for the orbit projection `π` and the inclusion `i` of the level
into `T*G` (`existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback` in
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`). So the reduced space of `T*G` by the cotangent lift
of left multiplication is the coadjoint orbit with the opposite of its KKS form. -/
theorem mpullback_reducedSpaceCoadjointOrbitDiffeomorph_neg_coadjointOrbitForm :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := properSMul (IG := I) (G := G) (I := I) (M := G)
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∀ η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)),
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff (symplecticForm I G) →
        SmoothForm.mpullback (reducedSpaceCoadjointOrbitDiffeomorph h hreg hn d)
            (reducedSpaceCoadjointOrbitDiffeomorph h hreg hn d).contMDiff (-c.coadjointOrbitForm) =
          η := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := properSMul (IG := I) (G := G) (I := I) (M := G)
  let := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  have hp := h.isSubmersion_quotientMk_levelSubMulAction hreg hn d
  intro η hη
  -- Pulling back along the orbit projection `π` is injective, and the diffeomorphism composed with
  -- `π` is `z ↦ [π(z)⁻¹]`.
  refine SmoothForm.mpullback_injective_of_surjective hp.contMDiff Quotient.mk_surjective
    (hp.surjective_mfderiv (by simp)) (((SmoothForm.mpullback_mpullback _ _ _
      (reducedSpaceCoadjointOrbitDiffeomorph h hreg hn d).contMDiff _).trans ?_).trans hη.symm)
  refine (SmoothForm.mpullback_congr _ (contMDiff_quotientMk_inv_proj hreg hn) ?_ _).trans
    (mpullback_quotientMk_inv_proj_neg_coadjointOrbitForm hreg hn)
  exact funext (reducedSpaceCoadjointOrbitDiffeomorph_mk hreg hn d)

/-- **The point of the coadjoint orbit.** Under the orbit map `[k] ↦ Ad*_k c`, the diffeomorphism
`T*G //_c G ≃ G ⧸ G_c` sends the orbit of a covector `z ∈ μ⁻¹(c)` to its left-trivialized value,
the translate `a = z ∘ d(L_g)_1` to the identity of `z` over `g`, which is `Ad*_{g⁻¹} c`. -/
theorem orbitMap_reducedSpaceCoadjointOrbitDiffeomorph_mk (z : h.levelSubMulAction c) :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := properSMul (IG := I) (G := G) (I := I) (M := G)
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    (Lie.coadjointRepresentation ℝ I G).orbitMap c
        (reducedSpaceCoadjointOrbitDiffeomorph h hreg hn d (Quotient.mk _ z)) =
      (((leftTrivialization I G).symm z).2 : E →ₗ[ℝ] ℝ) := by
  rw [reducedSpaceCoadjointOrbitDiffeomorph_mk, Representation.orbitMap_mk]
  exact (congrArg _ (h.mem_levelSubMulAction.1 z.property).symm).trans
    (coadjointRepresentation_proj_inv_momentMap _)

end ReducedSpace

end TauCeti.CotangentBundle

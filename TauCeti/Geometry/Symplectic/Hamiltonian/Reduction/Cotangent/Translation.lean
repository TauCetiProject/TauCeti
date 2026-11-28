/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent.ReducedSpace
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift
public import TauCeti.Geometry.Lie.FundamentalVectorField.Translation
public import TauCeti.Topology.Algebra.ProperAction.Submodule

import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.LinearAlgebra.Pi.Coordinates

/-!
# Cotangent reduction of a vector space by translations along a subspace

Let `V` be a finite-dimensional real normed space and `W ≤ V` a linear subspace. The Lie group
`Multiplicative W` acts on `V` by translations, `g • x = toAdd g + x`, smoothly, freely and
properly (`Submodule.properVAdd`), and the fundamental vector field of `ξ ∈ W` is the constant
vector field `ξ` (`TauCeti.fundamentalVectorField_multiplicative_submodule`). So the moment map
of the cotangent-lifted action on `T*V` is the restriction of the covector to `W`,
`⟨μ(q, p), ξ⟩ = p(ξ)`, and its zero level consists of the covectors vanishing on `W`
(`TauCeti.CotangentBundle.momentMap_multiplicative_submodule_eq_zero_iff`).

Let `ρ : V →L[ℝ] B` be a surjective continuous linear map with kernel `W`, for instance the
projection onto a complement of `W` or the quotient map `V → V ⧸ W`. Its fibres are the
`W`-orbits (`LinearMap.apply_eq_apply_iff_exists_smul_eq`), and it is a submersion, so it identifies
the orbit space `V ⧸ W` of the quotient manifold theorem with `B`
(`ProperSMul.diffeomorphOfOrbitSubmersion`). Composed with cotangent reduction at zero
(`TauCeti.CotangentBundle.zeroReducedSpaceDiffeomorph`) and with the cotangent lift of this
identification, this gives the symplectomorphism of the Marsden–Weinstein–Meyer reduced space

`T*V //₀ W = μ⁻¹(0) / W ≅ T*B`

(`TauCeti.CotangentBundle.translationReducedSpaceDiffeomorph`), which sends the orbit of a covector
`p` at `q`, vanishing on `W`, to the covector `p'` at `ρ q` with `p' ∘ ρ = p`
(`TauCeti.CotangentBundle.translationReducedSpaceDiffeomorph_mk_snd_apply`). It carries the reduced
symplectic form to the canonical symplectic form of `T*B`
(`TauCeti.CotangentBundle.mpullback_translationReducedSpaceDiffeomorph_symplecticForm`) and the
restriction of the Liouville form of `T*V` to the Liouville form of `T*B`.

For `V = ℝⁿ⁺¹ = Fin (n + 1) → ℝ`, `W = ℝ e₀` and `ρ` forgetting the first coordinate, this is the
reduction `T*ℝⁿ⁺¹ //₀ ℝ ≅ T*ℝⁿ` by translations along the first coordinate axis
(`exists_diffeomorph_proj_eq_tail_and_snd_apply_tail_and_mpullback_symplecticForm_eq`, in the
namespace `TauCeti.CotangentBundle`).

## Main definitions

* `TauCeti.CotangentBundle.translationReducedSpaceDiffeomorph`: the diffeomorphism
  `T*V //₀ W ≅ T*B`.

## Main results

* `TauCeti.CotangentBundle.momentMap_multiplicative_submodule_eq_zero_iff`: the zero level of the
  translation action consists of the covectors vanishing on `W`.
* `TauCeti.CotangentBundle.mpullback_translationReducedSpaceDiffeomorph_symplecticForm`:
  `T*V //₀ W ≅ T*B` is a symplectomorphism.
* `exists_diffeomorph_proj_eq_tail_and_snd_apply_tail_and_mpullback_symplecticForm_eq`, in the
  namespace `TauCeti.CotangentBundle`: `T*ℝⁿ⁺¹ //₀ ℝ ≅ T*ℝⁿ`.

## References

* Jerrold Marsden, Gerard Misiołek, Juan-Pablo Ortega, Matthew Perlmutter and Tudor Ratiu,
  *Hamiltonian Reduction by Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, Chapter 2
  (cotangent bundle reduction at zero).
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23.
-/

public section

noncomputable section

open Function Manifold Module
open scoped ContDiff Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace TauCeti

variable (W : Submodule ℝ V)

namespace CotangentBundle

/-- **The zero level of translations along a subspace** consists of the covectors vanishing on
`W`. -/
theorem momentMap_multiplicative_submodule_eq_zero_iff {z : CotangentBundle 𝓘(ℝ, V) V} :
    momentMap 𝓘(ℝ, W) (Multiplicative W) z = 0 ↔ ∀ w ∈ W, z.snd w = 0 := by
  refine ⟨fun h w hw ↦ ?_, fun h ↦ LinearMap.ext fun ξ ↦ ?_⟩
  · have hξ := LinearMap.congr_fun h
      ((tangentSpaceCastModel 𝓘(ℝ, W) (1 : Multiplicative W)).symm ⟨w, hw⟩)
    rwa [momentMap_apply, fundamentalVectorField_multiplicative_submodule,
      ContinuousLinearEquiv.apply_symm_apply,
      LinearMap.zero_apply] at hξ
  · rw [momentMap_apply, fundamentalVectorField_multiplicative_submodule, LinearMap.zero_apply]
    exact h _ (Subtype.prop _)

/-! ### The reduced space at zero -/

section ReducedSpace

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {W} {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {ρ : V →L[ℝ] B}

variable [FiniteDimensional ℝ V]
  {h : (symplecticForm 𝓘(ℝ, V) V).IsEquivariantMomentMap
    (momentMap 𝓘(ℝ, W) (Multiplicative W))}
  (hreg : ∀ z, momentMap 𝓘(ℝ, W) (Multiplicative W) z = 0 → Surjective (h.differential z))
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ}
  (hn : finrank ℝ (V × (V →L[ℝ] ℝ)) -
    finrank ℝ (GroupLieAlgebra 𝓘(ℝ, W) (Multiplicative W)) = n)
  (d : Lie.EmbeddedLieSubgroupData 𝓘(ℝ, W)
    ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, W) (Multiplicative W)).stabilizer 0) F)

/-- The orbit space `V ⧸ W` of translations along `W`, with the charts of the quotient manifold
theorem, is diffeomorphic to `B` by the map sending the orbit of `x` to `ρ x`, since `ρ` is a
surjective submersion whose fibres are the `W`-orbits. -/
private def orbitRelQuotientDiffeomorph (hρ : Surjective ρ) (hker : ρ.ker = W) :
    letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, W) (Multiplicative W) 𝓘(ℝ, V) V
    MulAction.orbitRel.Quotient (Multiplicative W) V ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace W V),
      𝓘(ℝ, B)⟯ B :=
  ProperSMul.diffeomorphOfOrbitSubmersion 𝓘(ℝ, W) le_rfl ρ
    (ρ.isSubmersion_of_surjective hρ (by simp)) hρ
    ((ρ : V →ₗ[ℝ] B).apply_eq_apply_iff_exists_smul_eq hker)

/-- `orbitRelQuotientDiffeomorph` composed with the orbit projection is `ρ`. -/
private theorem orbitRelQuotientDiffeomorph_comp_mk (hρ : Surjective ρ) (hker : ρ.ker = W) :
    letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, W) (Multiplicative W) 𝓘(ℝ, V) V
    ⇑(orbitRelQuotientDiffeomorph hρ hker) ∘ Quotient.mk (MulAction.orbitRel (Multiplicative W) V) =
      ρ :=
  ProperSMul.diffeomorphOfOrbitSubmersion_comp_mk _ _ _ _ _ _

variable (h) in
/-- **Cotangent reduction by translations.** Let `W ≤ V` act on `V` by translations and let
`ρ : V →L[ℝ] B` be surjective with kernel `W`. The Marsden–Weinstein–Meyer reduced space
`T*V //₀ W = μ⁻¹(0) / W`, with the atlas of the Marsden–Weinstein–Meyer theorem, is diffeomorphic
to `T*B`: the orbit of a covector `p` at `q`, vanishing on `W`, goes to the covector `p'` at `ρ q`
with `p' ∘ ρ = p` (`TauCeti.CotangentBundle.translationReducedSpaceDiffeomorph_mk_snd_apply`).

The hypotheses `h` and `hreg` are those of the atlas: they hold by
`TauCeti.CotangentBundle.isEquivariantMomentMap_momentMap` and
`TauCeti.CotangentBundle.differential_momentMap_surjective`. -/
def translationReducedSpaceDiffeomorph (hρ : Surjective ρ) (hker : ρ.ker = W) :
    haveI := properSMul (IG := 𝓘(ℝ, W)) (G := Multiplicative W) (I := 𝓘(ℝ, V)) (M := V)
    letI := h.orbitRelQuotientChartedSpace 0 hreg hn d
    MulAction.orbitRel.Quotient
        ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, W) (Multiplicative W)).stabilizer 0)
        (h.levelSubMulAction 0) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)),
        𝓘(ℝ, B).prod 𝓘(ℝ, B →L[ℝ] ℝ)⟯ CotangentBundle 𝓘(ℝ, B) B :=
  haveI := properSMul (IG := 𝓘(ℝ, W)) (G := Multiplicative W) (I := 𝓘(ℝ, V)) (M := V)
  letI := h.orbitRelQuotientChartedSpace 0 hreg hn d
  letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, W) (Multiplicative W) 𝓘(ℝ, V) V
  (zeroReducedSpaceDiffeomorph h hreg hn d).trans (orbitRelQuotientDiffeomorph hρ hker).cotangent

/-- `translationReducedSpaceDiffeomorph` sends the orbit of a covector at `q` to a covector at
`ρ q`. -/
@[simp]
theorem proj_translationReducedSpaceDiffeomorph_mk (hρ : Surjective ρ) (hker : ρ.ker = W)
    (z : h.levelSubMulAction 0) :
    haveI := properSMul (IG := 𝓘(ℝ, W)) (G := Multiplicative W) (I := 𝓘(ℝ, V)) (M := V)
    letI := h.orbitRelQuotientChartedSpace 0 hreg hn d
    (translationReducedSpaceDiffeomorph h hreg hn d hρ hker (Quotient.mk _ z)).proj =
      ρ (z : CotangentBundle 𝓘(ℝ, V) V).proj := by
  have := properSMul (IG := 𝓘(ℝ, W)) (G := Multiplicative W) (I := 𝓘(ℝ, V)) (M := V)
  let := h.orbitRelQuotientChartedSpace 0 hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, W) (Multiplicative W) 𝓘(ℝ, V) V
  rw [translationReducedSpaceDiffeomorph, Diffeomorph.coe_trans, comp_apply,
    Diffeomorph.proj_cotangent,
    zeroReducedSpaceDiffeomorph_mk, proj_reductionMap, orbitRelQuotientDiffeomorph,
    ProperSMul.diffeomorphOfOrbitSubmersion_mk]

/-- **The reduced covector.** `translationReducedSpaceDiffeomorph` sends the orbit of a covector
`p` at `q`, vanishing on `W`, to the covector `p'` at `ρ q` with `p'(ρ v) = p(v)`. Since `ρ` is
onto, this determines `p'`. -/
theorem translationReducedSpaceDiffeomorph_mk_snd_apply (hρ : Surjective ρ) (hker : ρ.ker = W)
    (z : h.levelSubMulAction 0) (v : V) :
    haveI := properSMul (IG := 𝓘(ℝ, W)) (G := Multiplicative W) (I := 𝓘(ℝ, V)) (M := V)
    letI := h.orbitRelQuotientChartedSpace 0 hreg hn d
    (translationReducedSpaceDiffeomorph h hreg hn d hρ hker (Quotient.mk _ z)).snd (ρ v) =
      (z : CotangentBundle 𝓘(ℝ, V) V).snd v := by
  have := properSMul (IG := 𝓘(ℝ, W)) (G := Multiplicative W) (I := 𝓘(ℝ, V)) (M := V)
  let := h.orbitRelQuotientChartedSpace 0 hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, W) (Multiplicative W) 𝓘(ℝ, V) V
  set e := orbitRelQuotientDiffeomorph hρ hker
  set q := (z : CotangentBundle 𝓘(ℝ, V) V).proj
  have hπ := ProperSMul.isSubmersion_quotientMk (I := 𝓘(ℝ, W)) (G := Multiplicative W)
    (I' := 𝓘(ℝ, V)) (M := V)
  have hπd : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, ProperSMul.QuotientModelSpace W V)
      (Quotient.mk (MulAction.orbitRel (Multiplicative W) V)) q :=
    (hπ.contMDiff q).mdifferentiableAt (by simp)
  -- `e ∘ π = ρ`, so `ρ v = de (dπ v)`.
  have hρv : ρ v = mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace W V) 𝓘(ℝ, B) e (Quotient.mk _ q)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, ProperSMul.QuotientModelSpace W V) (Quotient.mk _) q v) := by
    have hcomp := mfderiv_comp_apply q (e.mdifferentiable (by simp) (Quotient.mk _ q)) hπd v
    rw [orbitRelQuotientDiffeomorph_comp_mk, ContinuousLinearMap.mfderiv_eq] at hcomp
    exact hcomp
  have hz := (momentMap_eq_zero_iff_of_ker_eq (ProperSMul.ker_mfderiv_quotientMk q)).1
    (h.mem_levelSubMulAction.1 z.property)
  rw [hρv, translationReducedSpaceDiffeomorph, Diffeomorph.coe_trans, comp_apply,
    zeroReducedSpaceDiffeomorph_mk]
  have hcot := e.cotangent_snd_apply_mfderiv
    (reductionMap 𝓘(ℝ, V) 𝓘(ℝ, ProperSMul.QuotientModelSpace W V)
      (Quotient.mk (MulAction.orbitRel (Multiplicative W) V))
      (z : CotangentBundle 𝓘(ℝ, V) V))
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, ProperSMul.QuotientModelSpace W V)
      (Quotient.mk (MulAction.orbitRel (Multiplicative W) V)) q v)
  rw [proj_reductionMap] at hcot
  exact hcot.trans (reductionMap_snd_apply_mfderiv (hπ.hasRightInverse_mfderiv (by simp) q) hz v)

/-- **Cotangent reduction by translations: the symplectic forms.** The diffeomorphism
`T*V //₀ W ≅ T*B` pulls the canonical symplectic form of `T*B` back to the reduced symplectic form
`η` of the Marsden–Weinstein–Meyer theorem, the form on the reduced space with `π^* η = i^* ω` for
the orbit projection `π` and the inclusion `i` of the zero level into `T*V`. -/
theorem mpullback_translationReducedSpaceDiffeomorph_symplecticForm (hρ : Surjective ρ)
    (hker : ρ.ker = W) :
    haveI := properSMul (IG := 𝓘(ℝ, W)) (G := Multiplicative W) (I := 𝓘(ℝ, V)) (M := V)
    letI := h.levelSubMulActionChartedSpace 0 hreg hn
    letI := h.orbitRelQuotientChartedSpace 0 hreg hn d
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∀ η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient
          ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, W) (Multiplicative W)).stabilizer 0)
          (h.levelSubMulAction 0)),
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
            (symplecticForm 𝓘(ℝ, V) V) →
        SmoothForm.mpullback (translationReducedSpaceDiffeomorph h hreg hn d hρ hker)
            (translationReducedSpaceDiffeomorph h hreg hn d hρ hker).contMDiff
            (symplecticForm 𝓘(ℝ, B) B) = η := by
  have := properSMul (IG := 𝓘(ℝ, W)) (G := Multiplicative W) (I := 𝓘(ℝ, V)) (M := V)
  let := h.levelSubMulActionChartedSpace 0 hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace 0 hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, W) (Multiplicative W) 𝓘(ℝ, V) V
  intro η hη
  -- The diffeomorphism is the cotangent lift of `V ⧸ W ≅ B` after cotangent reduction at zero.
  refine (SmoothForm.mpullback_mpullback (zeroReducedSpaceDiffeomorph h hreg hn d) _
    (Diffeomorph.contMDiff _) (Diffeomorph.contMDiff _) _).symm.trans ?_
  rw [Diffeomorph.mpullback_cotangent_symplecticForm]
  exact mpullback_zeroReducedSpaceDiffeomorph_symplecticForm hreg hn d η hη

/-- **Cotangent reduction by translations: the tautological forms.** Along the orbit projection
`π : μ⁻¹(0) → T*V //₀ W`, the diffeomorphism `T*V //₀ W ≅ T*B` pulls the Liouville form of `T*B`
back to the restriction of the Liouville form of `T*V` to the zero level. -/
theorem mpullback_quotientMk_mpullback_translationReducedSpaceDiffeomorph_liouvilleForm
    (hρ : Surjective ρ) (hker : ρ.ker = W) :
    haveI := properSMul (IG := 𝓘(ℝ, W)) (G := Multiplicative W) (I := 𝓘(ℝ, V)) (M := V)
    letI := h.levelSubMulActionChartedSpace 0 hreg hn
    letI := h.orbitRelQuotientChartedSpace 0 hreg hn d
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff
        (SmoothForm.mpullback (translationReducedSpaceDiffeomorph h hreg hn d hρ hker)
          (translationReducedSpaceDiffeomorph h hreg hn d hρ hker).contMDiff
          (liouvilleForm 𝓘(ℝ, B) B)) =
      SmoothForm.mpullback Subtype.val (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
        (liouvilleForm 𝓘(ℝ, V) V) := by
  have := properSMul (IG := 𝓘(ℝ, W)) (G := Multiplicative W) (I := 𝓘(ℝ, V)) (M := V)
  let := h.levelSubMulActionChartedSpace 0 hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace 0 hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, W) (Multiplicative W) 𝓘(ℝ, V) V
  refine (congrArg _ (SmoothForm.mpullback_mpullback (zeroReducedSpaceDiffeomorph h hreg hn d) _
    (Diffeomorph.contMDiff _) (Diffeomorph.contMDiff _) _).symm).trans ?_
  rw [Diffeomorph.mpullback_cotangent_liouvilleForm]
  exact mpullback_quotientMk_mpullback_zeroReducedSpaceDiffeomorph_liouvilleForm hreg hn d

end ReducedSpace

/-! ### Translations along the first coordinate axis of `ℝⁿ⁺¹` -/

section Coordinate

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {n m : ℕ}
  {h : (symplecticForm 𝓘(ℝ, Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ)).IsEquivariantMomentMap
    (momentMap 𝓘(ℝ, ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ))
      (Multiplicative (ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ))))}
  (hreg : ∀ z, momentMap 𝓘(ℝ, ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ))
    (Multiplicative (ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ))) z = 0 → Surjective (h.differential z))
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (hm : finrank ℝ ((Fin (n + 1) → ℝ) × ((Fin (n + 1) → ℝ) →L[ℝ] ℝ)) -
    finrank ℝ (GroupLieAlgebra 𝓘(ℝ, ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ))
      (Multiplicative (ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ)))) = m)
  (d : Lie.EmbeddedLieSubgroupData 𝓘(ℝ, ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ))
    ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ))
      (Multiplicative (ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ)))).stabilizer 0) F)

/-- **`T*ℝⁿ⁺¹ //₀ ℝ ≅ T*ℝⁿ`.** For the line `ℝ e₀` acting on `ℝⁿ⁺¹ = Fin (n + 1) → ℝ` by
translations along the first coordinate axis, the Marsden–Weinstein–Meyer reduced space at zero
is symplectomorphic to `T*ℝⁿ`, by a diffeomorphism lying over the projection `Fin.tail` that
forgets the first coordinate, and sending the orbit of a covector `p` to the covector `p'` with
`p'(Fin.tail v) = p(v)`. -/
theorem exists_diffeomorph_proj_eq_tail_and_snd_apply_tail_and_mpullback_symplecticForm_eq :
    haveI := properSMul (IG := 𝓘(ℝ, ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ)))
      (G := Multiplicative (ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ)))
      (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) (M := Fin (n + 1) → ℝ)
    letI := h.levelSubMulActionChartedSpace 0 hreg hm
    letI := h.orbitRelQuotientChartedSpace 0 hreg hm d
    haveI := h.isManifold_levelSubMulAction hreg hm
    haveI := h.isManifold_orbitRelQuotient hreg hm d
    ∃ Φ : MulAction.orbitRel.Quotient
          ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ))
            (Multiplicative (ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ)))).stabilizer 0)
          (h.levelSubMulAction 0) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin m → ℝ)),
          𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] ℝ)⟯
        CotangentBundle 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ),
      (∀ z : h.levelSubMulAction 0, (Φ (Quotient.mk _ z)).proj =
        Fin.tail (z : CotangentBundle 𝓘(ℝ, Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ)).proj) ∧
      (∀ (z : h.levelSubMulAction 0) (v : Fin (n + 1) → ℝ), (Φ (Quotient.mk _ z)).snd (Fin.tail v) =
        (z : CotangentBundle 𝓘(ℝ, Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ)).snd v) ∧
      ∀ η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin m → ℝ))
          (MulAction.orbitRel.Quotient
            ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ))
              (Multiplicative (ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ)))).stabilizer 0)
            (h.levelSubMulAction 0)),
        SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hm d).contMDiff
            η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hm).contMDiff
            (symplecticForm 𝓘(ℝ, Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ)) →
        SmoothForm.mpullback Φ Φ.contMDiff (symplecticForm 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ)) = η := by
  set ρ := LinearMap.toContinuousLinearMap (LinearMap.funLeft ℝ ℝ (Fin.succ : Fin n → Fin (n + 1)))
  have hρ : Surjective ρ := by
    rw [LinearMap.coe_toContinuousLinearMap']
    exact LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n)
  have hker : ρ.ker = ℝ ∙ (Pi.single 0 1 : Fin (n + 1) → ℝ) := by
    rw [LinearMap.coe_toContinuousLinearMap, LinearMap.ker_funLeft_succ]
  exact ⟨translationReducedSpaceDiffeomorph h hreg hm d hρ hker,
    proj_translationReducedSpaceDiffeomorph_mk hreg hm d hρ hker,
    translationReducedSpaceDiffeomorph_mk_snd_apply hreg hm d hρ hker,
    mpullback_translationReducedSpaceDiffeomorph_symplecticForm hreg hm d hρ hker⟩

end Coordinate

end CotangentBundle

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
public import TauCeti.Topology.Algebra.PointTopology.Group

/-!
# Adelic points of an affine algebraic group

Let `F` be a number field and `H` a commutative Hopf algebra over `F`, the coordinate ring of an
affine group `G = Spec H`. This file defines the adelic points `G(𝔸_F)` as the convolution group
`WithConv (H →ₐ[F] 𝔸_F)` of `F`-algebra maps `H → 𝔸_F`, with Tau Ceti's point topology (the
coarsest topology making every evaluation `x ↦ x(h)` continuous), under which it is a topological
group (`TauCeti.PointTopology.isTopologicalGroup`). Likewise for the finite adelic points
`G(𝔸_{F,f})`, the archimedean points `G(F_∞)` and the local points `G(F_v)` at a finite place `v`.
The constructions here use only the bialgebra structure of `H`, which already makes the points a
monoid, so they are stated for bialgebras.

All maps between these groups are coefficient maps `AlgHom.mapValue`, except `finiteEmbed`: the
adele ring is the product `F_∞ × 𝔸_{F,f}`, and `finiteEmbed x = (1, x)` puts the identity point at
the archimedean component. It is an embedding of point groups, not induced by a ring map: the
inclusion `𝔸_{F,f} → 𝔸_F` with archimedean coordinate zero is not unital.

## Main definitions

* `TauCeti.AdelicPoints F H`: the group `G(𝔸_F)`.
* `TauCeti.AdelicPoints.FiniteAdelicPoints`, `TauCeti.AdelicPoints.InfinitePoints`,
  `TauCeti.AdelicPoints.LocalPoints`: the groups `G(𝔸_{F,f})`, `G(F_∞)` and `G(F_v)`.
* `TauCeti.AdelicPoints.diagonal`, `TauCeti.AdelicPoints.finiteDiagonal`,
  `TauCeti.AdelicPoints.infiniteDiagonal`: the rational diagonals out of `G(F)`.
* `TauCeti.AdelicPoints.finiteProjection`, `TauCeti.AdelicPoints.infiniteProjection`,
  `TauCeti.AdelicPoints.localProjection`: the projections of `G(𝔸_F)` to `G(𝔸_{F,f})`, `G(F_∞)` and
  `G(F_v)`.
* `TauCeti.AdelicPoints.finiteEmbed`: the homomorphism `G(𝔸_{F,f}) → G(𝔸_F)`, `x ↦ (1, x)`.

## Main results

* `TauCeti.AdelicPoints.localProjection_diagonal`: the local component of the diagonal image of a
  rational point is its image in `G(F_v)`.
* `TauCeti.AdelicPoints.finiteProjection_finiteEmbed`,
  `TauCeti.AdelicPoints.infiniteProjection_finiteEmbed`: `finiteEmbed x` has finite component `x`
  and archimedean component `1`.
* `TauCeti.AdelicPoints.isEmbedding_finiteEmbed`: `finiteEmbed` is a topological embedding.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Proposition 2.1.
* J. Arthur, *An introduction to the trace formula*, §2.
-/

@[expose] public section

open IsDedekindDomain NumberField Topology WithConv TauCeti.PointTopology

namespace TauCeti

variable (F : Type*) [Field F] [NumberField F] (H : Type*) [Semiring H] [Bialgebra F H]

/-- The adelic points `G(𝔸_F)` of the affine group `G = Spec H` over a number field `F`: the
convolution monoid of `F`-algebra maps `H → 𝔸_F` (a group when `H` is a Hopf algebra), with the
point topology. -/
abbrev AdelicPoints := WithConv (H →ₐ[F] AdeleRing (𝓞 F) F)

namespace AdelicPoints

/-- The finite adelic points `G(𝔸_{F,f})`. -/
abbrev FiniteAdelicPoints := WithConv (H →ₐ[F] FiniteAdeleRing (𝓞 F) F)

/-- The archimedean points `G(F_∞)`, with values in `F_∞ = F ⊗_ℚ ℝ`, the infinite adele ring. -/
abbrev InfinitePoints := WithConv (H →ₐ[F] InfiniteAdeleRing F)

/-- The local points `G(F_v)` at a finite place `v`. -/
abbrev LocalPoints (v : HeightOneSpectrum (𝓞 F)) := WithConv (H →ₐ[F] v.adicCompletion F)

/-- The rational diagonal `G(F) → G(𝔸_F)`, the coefficient map along `F → 𝔸_F`. -/
noncomputable def diagonal : WithConv (H →ₐ[F] F) →* AdelicPoints F H :=
  AlgHom.mapValue (Algebra.ofId F _)

/-- The finite rational diagonal `G(F) → G(𝔸_{F,f})`. -/
noncomputable def finiteDiagonal : WithConv (H →ₐ[F] F) →* FiniteAdelicPoints F H :=
  AlgHom.mapValue (Algebra.ofId F _)

/-- The archimedean rational diagonal `G(F) → G(F_∞)`. -/
noncomputable def infiniteDiagonal : WithConv (H →ₐ[F] F) →* InfinitePoints F H :=
  AlgHom.mapValue (Algebra.ofId F _)

/-- The projection `G(𝔸_F) → G(𝔸_{F,f})` to the finite component. -/
noncomputable def finiteProjection : AdelicPoints F H →* FiniteAdelicPoints F H :=
  AlgHom.mapValue (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

/-- The projection `G(𝔸_F) → G(F_∞)` to the archimedean component. -/
noncomputable def infiniteProjection : AdelicPoints F H →* InfinitePoints F H :=
  AlgHom.mapValue (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

/-- The projection `p_v : G(𝔸_F) → G(F_v)` at a finite place `v`, the coefficient map along the
projection `𝔸_F → F_v`. -/
noncomputable def localProjection (v : HeightOneSpectrum (𝓞 F)) :
    AdelicPoints F H →* LocalPoints F H v :=
  AlgHom.mapValue (((FiniteAdeleRing.proj F v : FiniteAdeleRing (𝓞 F) F →ₐ[F] _)).comp
    (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))

variable {F H}

theorem diagonal_apply (g : WithConv (H →ₐ[F] F)) (h : H) :
    (diagonal F H g).ofConv h = algebraMap F (AdeleRing (𝓞 F) F) (g.ofConv h) := by
  simp [diagonal]

theorem finiteProjection_apply (x : AdelicPoints F H) (h : H) :
    (finiteProjection F H x).ofConv h = (x.ofConv h).2 := by
  rw [finiteProjection, AlgHom.mapValue_apply, ofConv_toConv]
  rfl

theorem infiniteProjection_apply (x : AdelicPoints F H) (h : H) :
    (infiniteProjection F H x).ofConv h = (x.ofConv h).1 := by
  rw [infiniteProjection, AlgHom.mapValue_apply, ofConv_toConv]
  rfl

theorem localProjection_apply (v : HeightOneSpectrum (𝓞 F)) (x : AdelicPoints F H) (h : H) :
    (localProjection F H v x).ofConv h = (x.ofConv h).2 v := by
  rw [localProjection, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, AlgHom.comp_apply,
    ContinuousAlgHom.coe_coe, FiniteAdeleRing.proj_apply]
  rfl

/-- The projection at `v` factors through the finite component. -/
theorem localProjection_eq_comp (v : HeightOneSpectrum (𝓞 F)) :
    localProjection F H v =
      (AlgHom.mapValue (FiniteAdeleRing.proj F v : FiniteAdeleRing (𝓞 F) F →ₐ[F] _)).comp
        (finiteProjection F H) :=
  AlgHom.mapValue_comp _ _

/-- The local component of the diagonal image of a rational point `g` is the image of `g` in
`G(F_v)`. -/
@[simp]
theorem localProjection_diagonal (v : HeightOneSpectrum (𝓞 F)) (g : WithConv (H →ₐ[F] F)) :
    localProjection F H v (diagonal F H g) = AlgHom.mapValue (Algebra.ofId F _) g := by
  refine ofConv_injective (AlgHom.ext fun h ↦ ?_)
  rw [localProjection_apply, diagonal_apply, AlgHom.mapValue_apply, ofConv_toConv]
  rfl

/-- The finite component of the diagonal image of a rational point is its finite diagonal
image. -/
@[simp]
theorem finiteProjection_diagonal (g : WithConv (H →ₐ[F] F)) :
    finiteProjection F H (diagonal F H g) = finiteDiagonal F H g := by
  refine ofConv_injective (AlgHom.ext fun h ↦ ?_)
  rw [finiteProjection_apply, diagonal_apply, finiteDiagonal, AlgHom.mapValue_apply,
    ofConv_toConv]
  rfl

/-- The archimedean component of the diagonal image of a rational point is its archimedean
diagonal image. -/
@[simp]
theorem infiniteProjection_diagonal (g : WithConv (H →ₐ[F] F)) :
    infiniteProjection F H (diagonal F H g) = infiniteDiagonal F H g := by
  refine ofConv_injective (AlgHom.ext fun h ↦ ?_)
  rw [infiniteProjection_apply, diagonal_apply, infiniteDiagonal, AlgHom.mapValue_apply,
    ofConv_toConv]
  rfl

/-- An adelic point is determined by its archimedean and finite components. -/
theorem ext_iff_projection {x y : AdelicPoints F H} :
    x = y ↔ infiniteProjection F H x = infiniteProjection F H y ∧
      finiteProjection F H x = finiteProjection F H y := by
  refine ⟨fun hxy ↦ hxy ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  refine ofConv_injective (AlgHom.ext fun h ↦ Prod.ext ?_ ?_)
  · simpa only [infiniteProjection_apply] using DFunLike.congr_fun (congrArg ofConv h₁) h
  · simpa only [finiteProjection_apply] using DFunLike.congr_fun (congrArg ofConv h₂) h

/-- An adelic point is determined by its archimedean and finite components. -/
theorem ext_projection {x y : AdelicPoints F H}
    (h₁ : infiniteProjection F H x = infiniteProjection F H y)
    (h₂ : finiteProjection F H x = finiteProjection F H y) : x = y :=
  ext_iff_projection.2 ⟨h₁, h₂⟩

private theorem infiniteProjection_toConv_prod (a : H →ₐ[F] InfiniteAdeleRing F)
    (b : H →ₐ[F] FiniteAdeleRing (𝓞 F) F) :
    infiniteProjection F H (toConv (a.prod b)) = toConv a :=
  ofConv_injective (AlgHom.ext fun h ↦ by rw [infiniteProjection_apply]; rfl)

private theorem finiteProjection_toConv_prod (a : H →ₐ[F] InfiniteAdeleRing F)
    (b : H →ₐ[F] FiniteAdeleRing (𝓞 F) F) :
    finiteProjection F H (toConv (a.prod b)) = toConv b :=
  ofConv_injective (AlgHom.ext fun h ↦ by rw [finiteProjection_apply]; rfl)

variable (F H) in
/-- The homomorphism `G(𝔸_{F,f}) → G(𝔸_F)`, `x ↦ (1, x)`, with the identity point at the
archimedean component. -/
noncomputable def finiteEmbed : FiniteAdelicPoints F H →* AdelicPoints F H where
  toFun x := toConv (AlgHom.prod (1 : InfinitePoints F H).ofConv x.ofConv)
  map_one' := ext_projection (by rw [infiniteProjection_toConv_prod, toConv_ofConv, map_one])
    (by rw [finiteProjection_toConv_prod, toConv_ofConv, map_one])
  map_mul' x y := by
    refine ext_projection ?_ ?_
    · rw [map_mul, infiniteProjection_toConv_prod, infiniteProjection_toConv_prod,
        infiniteProjection_toConv_prod, toConv_ofConv, mul_one]
    · rw [map_mul, finiteProjection_toConv_prod, finiteProjection_toConv_prod,
        finiteProjection_toConv_prod, toConv_ofConv, toConv_ofConv, toConv_ofConv]

private theorem finiteEmbed_eq (x : FiniteAdelicPoints F H) :
    finiteEmbed F H x = toConv (AlgHom.prod (1 : InfinitePoints F H).ofConv x.ofConv) :=
  rfl

theorem finiteEmbed_apply (x : FiniteAdelicPoints F H) (h : H) :
    (finiteEmbed F H x).ofConv h = ((1 : InfinitePoints F H).ofConv h, x.ofConv h) := by
  rw [finiteEmbed_eq, ofConv_toConv, AlgHom.prod_apply]

/-- The finite component of `finiteEmbed x` is `x`. -/
@[simp]
theorem finiteProjection_finiteEmbed (x : FiniteAdelicPoints F H) :
    finiteProjection F H (finiteEmbed F H x) = x := by
  rw [finiteEmbed_eq, finiteProjection_toConv_prod, toConv_ofConv]

/-- The archimedean component of `finiteEmbed x` is the identity. -/
@[simp]
theorem infiniteProjection_finiteEmbed (x : FiniteAdelicPoints F H) :
    infiniteProjection F H (finiteEmbed F H x) = 1 := by
  rw [finiteEmbed_eq, infiniteProjection_toConv_prod, toConv_ofConv]

theorem finiteEmbed_injective : Function.Injective (finiteEmbed F H) :=
  Function.LeftInverse.injective finiteProjection_finiteEmbed

/-! ### Continuity -/

@[fun_prop]
theorem continuous_finiteProjection : Continuous (finiteProjection F H) :=
  AlgHom.continuous_mapValue continuous_snd

@[fun_prop]
theorem continuous_infiniteProjection : Continuous (infiniteProjection F H) :=
  AlgHom.continuous_mapValue continuous_fst

@[fun_prop]
theorem continuous_localProjection (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (localProjection F H v) :=
  AlgHom.continuous_mapValue ((FiniteAdeleRing.proj F v).continuous.comp continuous_snd)

@[fun_prop]
theorem continuous_finiteEmbed : Continuous (finiteEmbed F H) :=
  continuous_withConv_iff.2 fun h ↦ by
    simp only [finiteEmbed_apply]
    exact continuous_const.prodMk (continuous_eval_ofConv h)

/-- `finiteEmbed` is a topological embedding: it has the continuous left inverse
`finiteProjection`. -/
theorem isEmbedding_finiteEmbed : IsEmbedding (finiteEmbed F H) :=
  Function.LeftInverse.isEmbedding finiteProjection_finiteEmbed continuous_finiteProjection
    continuous_finiteEmbed

end AdelicPoints

end TauCeti

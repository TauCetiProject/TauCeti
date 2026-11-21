/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Discrete
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
public import TauCeti.Topology.Algebra.PointTopology.Prod
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic

/-!
# Adelic, finite-adelic, archimedean, and local point groups of affine group schemes

For an affine group scheme over a number field `F` represented by a Hopf algebra `H` over `F`, its
groups of rational, local, archimedean, finite-adelic, and full adelic points are the convolution
groups `WithConv (H →ₐ[F] R)` equipped with the affine evaluation topology (`PointTopology`) as `R`
ranges over `F`, its completions `v.adicCompletion F` and `w.Completion`, the archimedean product
`NumberField.InfiniteAdeleRing F`, the finite adele ring
`IsDedekindDomain.FiniteAdeleRing (𝓞 F) F`, and the full adele ring `NumberField.AdeleRing (𝓞 F) F`.

Topologizing `G(𝔸_F)` directly through coordinate evaluation on `𝔸_F` makes the group operations and
functoriality in `H` immediate without choosing an integral model or matrix embedding upfront, and
provides the ambient topological group in which arithmetic quotients `G(F) \ G(𝔸_F)` and
Borel–Harish-Chandra finiteness theorems are formulated. In
`TauCeti.Algebra.AlgebraicGroup.AdelicPoints.RestrictedProduct` this intrinsic topology on
`G(𝔸_{F,f})` is shown to agree with the restricted product of `G(F_v)` with respect to the local
integral subgroups of any integral model.

This file defines these topological groups together with:

* Diagonal embeddings of `F`-rational points and place projections between full adelic,
  finite-adelic, archimedean, and single-place point groups, with their compatibility identities and
  injectivity of the diagonal maps.
* Topological group splittings `AdelicPoints.prodEquiv` into archimedean times finite-adelic points
  (with closed factor embeddings `infiniteEmbed` and `finiteEmbed`) and
  `AdelicPoints.infinitePiEquiv` into the finite product over `InfinitePlace F`.
* Closedness of the diagonal subgroup `AdelicPoints.principalPointsSubgroup F H` of `F`-rational
  points in `AdelicPoints F H` for every Hopf algebra `H`, and its discreteness when `H` is a
  finitely generated `F`-algebra.

## Main declarations

* `TauCeti.AdelicPoints`, `TauCeti.AdelicPoints.FiniteAdelicPoints`,
  `TauCeti.AdelicPoints.InfinitePoints`, `TauCeti.AdelicPoints.LocalPoints`,
  `TauCeti.AdelicPoints.InfiniteLocalPoints`: the adelic and local topological groups of points.
* `TauCeti.AdelicPoints.diagonal`, `TauCeti.AdelicPoints.finiteProjection`,
  `TauCeti.AdelicPoints.infiniteProjection`, `TauCeti.AdelicPoints.localProjection`: diagonal and
  projection homomorphisms.
* `TauCeti.AdelicPoints.prodEquiv`, `TauCeti.AdelicPoints.infinitePiEquiv`: archimedean/finite and
  archimedean-place topological group splittings.
* `TauCeti.AdelicPoints.principalPointsSubgroup`,
  `TauCeti.AdelicPoints.isClosed_principalPointsSubgroup`,
  `TauCeti.AdelicPoints.discreteTopology_principalPointsSubgroup`: the diagonal subgroup of rational
  points is closed and (for `H` of finite type over `F`) discrete in `AdelicPoints F H`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  §§2–3.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.
-/

public section

open IsDedekindDomain NumberField Topology WithConv TauCeti.AlgHom TauCeti.PointTopology
open scoped NumberField.AdeleRing

namespace TauCeti

/-- Full adelic points `G(𝔸_F)` of the affine group scheme over `F` with coordinate Hopf algebra
`H`, carrying the convolution group structure and the affine point topology. -/
abbrev AdelicPoints (F H : Type*) [Field F] [NumberField F] [Semiring H] [HopfAlgebra F H] :
    Type _ :=
  WithConv (H →ₐ[F] AdeleRing (𝓞 F) F)

namespace AdelicPoints

section Archimedean

variable (F H : Type*) [Field F] [Semiring H] [HopfAlgebra F H]

/-- Archimedean points `G(F_∞)`. -/
abbrev InfinitePoints : Type _ :=
  WithConv (H →ₐ[F] InfiniteAdeleRing F)

/-- Local points `G(F_w)` at an infinite place `w : InfinitePlace F`. -/
abbrev InfiniteLocalPoints (w : InfinitePlace F) : Type _ :=
  WithConv (H →ₐ[F] w.Completion)

variable {F H}

/-- Diagonal homomorphism `G(F) →* G(F_∞)` into archimedean points. -/
noncomputable def infiniteDiagonal : WithConv (H →ₐ[F] F) →* InfinitePoints F H :=
  AlgHom.mapValue (Algebra.ofId F (InfiniteAdeleRing F))

/-- Diagonal homomorphism `G(F) →* G(F_w)` at an infinite place `w`. -/
noncomputable def infiniteLocalDiagonal (w : InfinitePlace F) :
    WithConv (H →ₐ[F] F) →* InfiniteLocalPoints F H w :=
  AlgHom.mapValue (Algebra.ofId F w.Completion)

/-- Projection `G(F_∞) →* G(F_w)` from archimedean points to an infinite place `w`. -/
noncomputable def infiniteLocalProjection (w : InfinitePlace F) :
    InfinitePoints F H →* InfiniteLocalPoints F H w :=
  AlgHom.mapValue (Pi.evalAlgHom F (fun w : InfinitePlace F ↦ w.Completion) w)

@[simp]
theorem infiniteDiagonal_ofConv_apply (g : WithConv (H →ₐ[F] F)) (h : H) :
    (infiniteDiagonal g).ofConv h = algebraMap F (InfiniteAdeleRing F) (g.ofConv h) := by
  simp [infiniteDiagonal]

@[simp]
theorem infiniteLocalDiagonal_ofConv_apply (w : InfinitePlace F)
    (g : WithConv (H →ₐ[F] F)) (h : H) :
    (infiniteLocalDiagonal w g).ofConv h = algebraMap F w.Completion (g.ofConv h) := by
  simp [infiniteLocalDiagonal]

@[simp]
theorem infiniteLocalProjection_ofConv_apply (w : InfinitePlace F)
    (x : InfinitePoints F H) (h : H) :
    (infiniteLocalProjection w x).ofConv h = x.ofConv h w := by
  rw [infiniteLocalProjection, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    Pi.evalAlgHom_apply]

@[continuity, fun_prop]
theorem continuous_infiniteLocalProjection (w : InfinitePlace F) :
    Continuous (infiniteLocalProjection (F := F) (H := H) w) :=
  AlgHom.continuous_mapValue
    ((continuous_apply w).congr fun a ↦
      (Pi.evalAlgHom_apply F (fun w : InfinitePlace F ↦ w.Completion) w a).symm)

@[simp]
theorem infiniteLocalProjection_infiniteDiagonal (w : InfinitePlace F)
    (g : WithConv (H →ₐ[F] F)) :
    infiniteLocalProjection w (infiniteDiagonal g) = infiniteLocalDiagonal w g := by
  rw [infiniteLocalProjection, infiniteDiagonal, infiniteLocalDiagonal, ← MonoidHom.comp_apply,
    ← AlgHom.mapValue_comp, Algebra.comp_ofId]

variable (F H) in
/-- Topological group isomorphism `G(F_∞) ≃ₜ* ∀ w : InfinitePlace F, G(F_w)`. -/
noncomputable def infinitePiEquiv :
    InfinitePoints F H ≃ₜ* ∀ w : InfinitePlace F, InfiniteLocalPoints F H w :=
  piPointsContinuousMulEquiv F H (fun w : InfinitePlace F ↦ w.Completion)

@[simp]
theorem infinitePiEquiv_apply (x : InfinitePoints F H) (w : InfinitePlace F) :
    infinitePiEquiv F H x w = infiniteLocalProjection w x := by
  rw [infinitePiEquiv, piPointsContinuousMulEquiv_apply, infiniteLocalProjection]

@[simp]
theorem infinitePiEquiv_symm_ofConv_apply
    (f : ∀ w : InfinitePlace F, InfiniteLocalPoints F H w) (h : H) (w : InfinitePlace F) :
    ((infinitePiEquiv F H).symm f).ofConv h w = (f w).ofConv h :=
  piPointsContinuousMulEquiv_symm_ofConv_apply F H
    (fun w : InfinitePlace F ↦ w.Completion) f h w

/-- The local diagonal embedding `G(F) →* G(F_w)` at an infinite place `w` is injective. -/
theorem infiniteLocalDiagonal_injective (w : InfinitePlace F) :
    Function.Injective (infiniteLocalDiagonal (F := F) (H := H) w) :=
  AlgHom.mapValue_injective (RingHom.injective _)

end Archimedean

section NumberField

variable (F H : Type*) [Field F] [NumberField F] [Semiring H] [HopfAlgebra F H]

/-- Finite-adelic points `G(𝔸_{F,f})`. -/
abbrev FiniteAdelicPoints : Type _ :=
  WithConv (H →ₐ[F] FiniteAdeleRing (𝓞 F) F)

/-- Local points `G(F_v)` at a finite place `v : HeightOneSpectrum (𝓞 F)`. -/
abbrev LocalPoints (v : HeightOneSpectrum (𝓞 F)) : Type _ :=
  WithConv (H →ₐ[F] v.adicCompletion F)

variable {F H}

/-! ### Diagonal embeddings and place projections -/

/-- Diagonal homomorphism `G(F) →* G(𝔸_F)`. -/
noncomputable def diagonal : WithConv (H →ₐ[F] F) →* AdelicPoints F H :=
  AlgHom.mapValue (Algebra.ofId F (AdeleRing (𝓞 F) F))

/-- Diagonal homomorphism `G(F) →* G(𝔸_{F,f})` into finite-adelic points. -/
noncomputable def finiteDiagonal : WithConv (H →ₐ[F] F) →* FiniteAdelicPoints F H :=
  AlgHom.mapValue (Algebra.ofId F (FiniteAdeleRing (𝓞 F) F))

/-- Diagonal homomorphism `G(F) →* G(F_v)` at a finite place `v`. -/
noncomputable def localDiagonal (v : HeightOneSpectrum (𝓞 F)) :
    WithConv (H →ₐ[F] F) →* LocalPoints F H v :=
  AlgHom.mapValue (Algebra.ofId F (v.adicCompletion F))

/-- Projection `G(𝔸_F) →* G(F_∞)` onto the archimedean factor. -/
noncomputable def infiniteProjection : AdelicPoints F H →* InfinitePoints F H :=
  AlgHom.mapValue (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

/-- Projection `G(𝔸_F) →* G(𝔸_{F,f})` onto the finite-adelic factor. -/
noncomputable def finiteProjection : AdelicPoints F H →* FiniteAdelicPoints F H :=
  AlgHom.mapValue (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

/-- Projection `G(𝔸_{F,f}) →* G(F_v)` from finite-adelic points to a finite place `v`. -/
noncomputable def finiteLocalProjection (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdelicPoints F H →* LocalPoints F H v :=
  AlgHom.mapValue (FiniteAdeleRing.proj F v).toAlgHom

/-- Projection `G(𝔸_F) →* G(F_v)` from full adelic points to a finite place `v`. -/
noncomputable def localProjection (v : HeightOneSpectrum (𝓞 F)) :
    AdelicPoints F H →* LocalPoints F H v :=
  (finiteLocalProjection v).comp finiteProjection

@[simp]
theorem diagonal_ofConv_apply (g : WithConv (H →ₐ[F] F)) (h : H) :
    (diagonal g).ofConv h = algebraMap F (AdeleRing (𝓞 F) F) (g.ofConv h) := by
  simp [diagonal]

@[simp]
theorem finiteDiagonal_ofConv_apply (g : WithConv (H →ₐ[F] F)) (h : H) :
    (finiteDiagonal g).ofConv h = algebraMap F (FiniteAdeleRing (𝓞 F) F) (g.ofConv h) := by
  simp [finiteDiagonal]

@[simp]
theorem localDiagonal_ofConv_apply (v : HeightOneSpectrum (𝓞 F))
    (g : WithConv (H →ₐ[F] F)) (h : H) :
    (localDiagonal v g).ofConv h = algebraMap F (v.adicCompletion F) (g.ofConv h) := by
  simp [localDiagonal]

@[simp]
theorem infiniteProjection_ofConv_apply (x : AdelicPoints F H) (h : H) :
    (infiniteProjection x).ofConv h = (x.ofConv h).1 := by
  rw [infiniteProjection, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, AlgHom.fst_apply]

@[simp]
theorem finiteProjection_ofConv_apply (x : AdelicPoints F H) (h : H) :
    (finiteProjection x).ofConv h = (x.ofConv h).2 := by
  rw [finiteProjection, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, AlgHom.snd_apply]

@[simp]
theorem finiteLocalProjection_ofConv_apply (v : HeightOneSpectrum (𝓞 F))
    (x : FiniteAdelicPoints F H) (h : H) :
    (finiteLocalProjection v x).ofConv h = x.ofConv h v := by
  simp [finiteLocalProjection]

@[simp]
theorem localProjection_ofConv_apply (v : HeightOneSpectrum (𝓞 F))
    (x : AdelicPoints F H) (h : H) :
    (localProjection v x).ofConv h = (x.ofConv h).2 v := by
  simp [localProjection]

@[simp]
theorem finiteLocalProjection_finiteProjection (v : HeightOneSpectrum (𝓞 F))
    (x : AdelicPoints F H) :
    finiteLocalProjection v (finiteProjection x) = localProjection v x := by
  rw [localProjection, MonoidHom.comp_apply]

@[continuity, fun_prop]
theorem continuous_infiniteProjection :
    Continuous (infiniteProjection (F := F) (H := H)) :=
  AlgHom.continuous_mapValue
    (continuous_fst.congr fun a ↦ (AlgHom.fst_apply F a).symm)

@[continuity, fun_prop]
theorem continuous_finiteProjection :
    Continuous (finiteProjection (F := F) (H := H)) :=
  AlgHom.continuous_mapValue
    (continuous_snd.congr fun a ↦ (AlgHom.snd_apply F a).symm)

@[continuity, fun_prop]
theorem continuous_finiteLocalProjection (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (finiteLocalProjection (F := F) (H := H) v) :=
  AlgHom.continuous_mapValue (FiniteAdeleRing.proj F v).cont

@[continuity, fun_prop]
theorem continuous_localProjection (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (localProjection (F := F) (H := H) v) :=
  (continuous_finiteLocalProjection v).comp continuous_finiteProjection

@[simp]
theorem infiniteProjection_diagonal (g : WithConv (H →ₐ[F] F)) :
    infiniteProjection (diagonal g) = infiniteDiagonal g := by
  apply ofConv_injective
  ext h
  simp

@[simp]
theorem finiteProjection_diagonal (g : WithConv (H →ₐ[F] F)) :
    finiteProjection (diagonal g) = finiteDiagonal g := by
  apply ofConv_injective
  ext h
  simp

@[simp]
theorem finiteLocalProjection_finiteDiagonal (v : HeightOneSpectrum (𝓞 F))
    (g : WithConv (H →ₐ[F] F)) :
    finiteLocalProjection v (finiteDiagonal g) = localDiagonal v g := by
  rw [finiteLocalProjection, finiteDiagonal, localDiagonal, ← MonoidHom.comp_apply,
    ← AlgHom.mapValue_comp, Algebra.comp_ofId]

@[simp]
theorem localProjection_diagonal (v : HeightOneSpectrum (𝓞 F))
    (g : WithConv (H →ₐ[F] F)) :
    localProjection v (diagonal g) = localDiagonal v g := by
  simp [localProjection]

/-! ### Archimedean/finite product splitting -/

variable (F H) in
/-- Topological group isomorphism `G(𝔸_F) ≃ₜ* G(F_∞) × G(𝔸_{F,f})`. -/
noncomputable def prodEquiv :
    AdelicPoints F H ≃ₜ* InfinitePoints F H × FiniteAdelicPoints F H :=
  prodPointsContinuousMulEquiv F H (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

@[simp]
theorem prodEquiv_fst (x : AdelicPoints F H) :
    (prodEquiv F H x).1 = infiniteProjection x := by
  rw [prodEquiv, prodPointsContinuousMulEquiv_fst, infiniteProjection]

@[simp]
theorem prodEquiv_snd (x : AdelicPoints F H) :
    (prodEquiv F H x).2 = finiteProjection x := by
  rw [prodEquiv, prodPointsContinuousMulEquiv_snd, finiteProjection]

@[simp]
theorem prodEquiv_symm_ofConv_apply
    (p : InfinitePoints F H × FiniteAdelicPoints F H) (h : H) :
    ((prodEquiv F H).symm p).ofConv h = (p.1.ofConv h, p.2.ofConv h) :=
  prodPointsContinuousMulEquiv_symm_ofConv_apply F H
    (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) p h

variable (F H) in
/-- Closed topological group embedding `x ↦ (x, 1)` of `G(F_∞)` into `G(𝔸_F)`. -/
noncomputable def infiniteEmbed : InfinitePoints F H →* AdelicPoints F H :=
  inlPoints F H (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

variable (F H) in
/-- Closed topological group embedding `y ↦ (1, y)` of `G(𝔸_{F,f})` into `G(𝔸_F)`. -/
noncomputable def finiteEmbed : FiniteAdelicPoints F H →* AdelicPoints F H :=
  inrPoints F H (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

@[simp]
theorem infiniteProjection_infiniteEmbed (x : InfinitePoints F H) :
    infiniteProjection (infiniteEmbed F H x) = x := by
  rw [infiniteEmbed, infiniteProjection, mapValue_fst_inlPoints]

@[simp]
theorem finiteProjection_infiniteEmbed (x : InfinitePoints F H) :
    finiteProjection (infiniteEmbed F H x) = 1 := by
  rw [infiniteEmbed, finiteProjection, mapValue_snd_inlPoints]

@[simp]
theorem infiniteProjection_finiteEmbed (y : FiniteAdelicPoints F H) :
    infiniteProjection (finiteEmbed F H y) = 1 := by
  rw [finiteEmbed, infiniteProjection, mapValue_fst_inrPoints]

@[simp]
theorem finiteProjection_finiteEmbed (y : FiniteAdelicPoints F H) :
    finiteProjection (finiteEmbed F H y) = y := by
  rw [finiteEmbed, finiteProjection, mapValue_snd_inrPoints]

@[simp]
theorem localProjection_infiniteEmbed (v : HeightOneSpectrum (𝓞 F))
    (x : InfinitePoints F H) :
    localProjection v (infiniteEmbed F H x) = 1 := by
  rw [← finiteLocalProjection_finiteProjection, finiteProjection_infiniteEmbed, map_one]

@[simp]
theorem localProjection_finiteEmbed (v : HeightOneSpectrum (𝓞 F))
    (y : FiniteAdelicPoints F H) :
    localProjection v (finiteEmbed F H y) = finiteLocalProjection v y := by
  rw [← finiteLocalProjection_finiteProjection, finiteProjection_finiteEmbed]

/-- Multiplying an archimedean factor point `infiniteEmbed F H x` by a finite-adelic factor point
`finiteEmbed F H y` reconstructs `(prodEquiv F H).symm (x, y)`. -/
theorem infiniteEmbed_mul_finiteEmbed (x : InfinitePoints F H) (y : FiniteAdelicPoints F H) :
    infiniteEmbed F H x * finiteEmbed F H y = (prodEquiv F H).symm (x, y) := by
  apply (prodEquiv F H).injective
  ext1 <;> simp

/-- `infiniteEmbed` sends `x` to `(prodEquiv F H).symm (x, 1)`. -/
theorem infiniteEmbed_apply (x : InfinitePoints F H) :
    infiniteEmbed F H x = (prodEquiv F H).symm (x, 1) := by
  simpa only [map_one, mul_one] using infiniteEmbed_mul_finiteEmbed x 1

/-- `finiteEmbed` sends `y` to `(prodEquiv F H).symm (1, y)`. -/
theorem finiteEmbed_apply (y : FiniteAdelicPoints F H) :
    finiteEmbed F H y = (prodEquiv F H).symm (1, y) := by
  simpa only [map_one, one_mul] using infiniteEmbed_mul_finiteEmbed 1 y

@[simp]
theorem infiniteEmbed_ofConv_apply (x : InfinitePoints F H) (h : H) :
    (infiniteEmbed F H x).ofConv h =
      (x.ofConv h, algebraMap F (FiniteAdeleRing (𝓞 F) F) (Coalgebra.counit h)) := by
  simp [infiniteEmbed_apply, AlgHom.convOne_def]

@[simp]
theorem finiteEmbed_ofConv_apply (y : FiniteAdelicPoints F H) (h : H) :
    (finiteEmbed F H y).ofConv h =
      (algebraMap F (InfiniteAdeleRing F) (Coalgebra.counit h), y.ofConv h) := by
  simp [finiteEmbed_apply, AlgHom.convOne_def]

@[continuity, fun_prop]
theorem continuous_infiniteEmbed : Continuous (infiniteEmbed F H) :=
  continuous_inlPoints F H (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

@[continuity, fun_prop]
theorem continuous_finiteEmbed : Continuous (finiteEmbed F H) :=
  continuous_inrPoints F H (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

/-- The archimedean factor inclusion `G(F_∞) →* G(𝔸_F)` is a closed topological embedding. -/
theorem isClosedEmbedding_infiniteEmbed : IsClosedEmbedding (infiniteEmbed F H) :=
  isClosedEmbedding_inlPoints F H (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

/-- The finite-adelic factor inclusion `G(𝔸_{F,f}) →* G(𝔸_F)` is a closed topological embedding. -/
theorem isClosedEmbedding_finiteEmbed : IsClosedEmbedding (finiteEmbed F H) :=
  isClosedEmbedding_inrPoints F H (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

/-! ### Injectivity, closedness, and discreteness of rational points -/

/-- The diagonal embedding `G(F) →* G(𝔸_F)` of rational points into full adelic points is
injective. -/
theorem diagonal_injective :
    Function.Injective (diagonal (F := F) (H := H)) :=
  AlgHom.mapValue_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

/-- The local diagonal embedding `G(F) →* G(F_v)` at a finite place `v` is injective. -/
theorem localDiagonal_injective (v : HeightOneSpectrum (𝓞 F)) :
    Function.Injective (localDiagonal (F := F) (H := H) v) :=
  AlgHom.mapValue_injective (RingHom.injective _)

/-- The finite-adelic diagonal embedding `G(F) →* G(𝔸_{F,f})` is injective. -/
theorem finiteDiagonal_injective :
    Function.Injective (finiteDiagonal (F := F) (H := H)) := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (HeightOneSpectrum (𝓞 F)))
  refine .of_comp (f := finiteLocalProjection v) ?_
  simpa only [Function.comp_def, finiteLocalProjection_finiteDiagonal] using
    localDiagonal_injective (F := F) (H := H) v

/-- Over a number field `F` (which carries at least one archimedean place), the archimedean
diagonal embedding `G(F) →* G(F_∞)` is injective. -/
theorem infiniteDiagonal_injective :
    Function.Injective (infiniteDiagonal (F := F) (H := H)) :=
  AlgHom.mapValue_injective (RingHom.injective _)

private theorem range_diagonal_eq_range_mapValue_principalSubalgebra :
    Set.range (diagonal (F := F) (H := H)) =
      Set.range (AlgHom.mapValue (H := H)
        (TauCeti.GlobalNumberFields.principalSubalgebra F).val) := by
  let e := TauCeti.GlobalNumberFields.principalSubalgebraEquiv F
  have hcomp : Algebra.ofId F (AdeleRing (𝓞 F) F) =
      (TauCeti.GlobalNumberFields.principalSubalgebra F).val.comp e.toAlgHom := by
    ext
  have hsurj : Function.Surjective (AlgHom.mapValue (H := H) e.toAlgHom) := fun y ↦
    ⟨AlgHom.mapValue e.symm.toAlgHom y, ofConv_injective <| AlgHom.ext fun h ↦ by simp⟩
  rw [diagonal, hcomp, AlgHom.mapValue_comp, MonoidHom.coe_comp, hsurj.range_comp]

/-- The diagonal copy of `G(F)` is closed in `G(𝔸_F)` for every Hopf algebra `H` over `F`. -/
theorem isClosed_range_diagonal :
    IsClosed (Set.range (diagonal (F := F) (H := H))) := by
  rw [range_diagonal_eq_range_mapValue_principalSubalgebra]
  exact (AlgHom.isClosedEmbedding_mapValue
    (TauCeti.GlobalNumberFields.isClosedEmbedding_principalSubalgebra_val F)).isClosed_range

/-- When `H` is a finitely generated Hopf `F`-algebra, the diagonal copy of `G(F)` is discrete in
`G(𝔸_F)`. -/
theorem discreteTopology_range_diagonal {H : Type*} [Semiring H] [HopfAlgebra F H]
    [Algebra.FiniteType F H] :
    DiscreteTopology (Set.range (diagonal (F := F) (H := H))) := by
  have hemb := AlgHom.isEmbedding_mapValue (H₁ := H)
    (TauCeti.GlobalNumberFields.isClosedEmbedding_principalSubalgebra_val F).isEmbedding
  let e : WithConv (H →ₐ[F] TauCeti.GlobalNumberFields.principalSubalgebra F) ≃ₜ
      Set.range (diagonal (F := F) (H := H)) :=
    hemb.toHomeomorph.trans
      (Homeomorph.setCongr range_diagonal_eq_range_mapValue_principalSubalgebra.symm)
  exact e.symm.isEmbedding.discreteTopology

variable (F H) in
/-- The subgroup of `F`-rational points inside `G(𝔸_F)`. -/
noncomputable def principalPointsSubgroup : Subgroup (AdelicPoints F H) :=
  (diagonal (F := F) (H := H)).range

variable (F H) in
theorem principalPointsSubgroup_def :
    principalPointsSubgroup F H = (diagonal (F := F) (H := H)).range := by
  rfl

variable (F H) in
@[simp]
theorem coe_principalPointsSubgroup :
    (principalPointsSubgroup F H : Set (AdelicPoints F H)) =
      Set.range (diagonal (F := F) (H := H)) := by
  rw [principalPointsSubgroup_def, MonoidHom.coe_range]

@[simp]
theorem mem_principalPointsSubgroup_iff {x : AdelicPoints F H} :
    x ∈ principalPointsSubgroup F H ↔ ∃ g : WithConv (H →ₐ[F] F), diagonal g = x := by
  rw [principalPointsSubgroup_def, MonoidHom.mem_range]

theorem diagonal_mem_principalPointsSubgroup (g : WithConv (H →ₐ[F] F)) :
    diagonal g ∈ principalPointsSubgroup F H := by
  rw [mem_principalPointsSubgroup_iff]
  exact ⟨g, rfl⟩

variable (F H) in
/-- The subgroup of `F`-rational points is closed in `G(𝔸_F)` for every Hopf `F`-algebra `H`. -/
theorem isClosed_principalPointsSubgroup :
    IsClosed (principalPointsSubgroup F H : Set (AdelicPoints F H)) := by
  rw [coe_principalPointsSubgroup]
  exact isClosed_range_diagonal

/-- When `H` is a finitely generated Hopf `F`-algebra, the subgroup of `F`-rational points is
discrete in `G(𝔸_F)`. -/
instance discreteTopology_principalPointsSubgroup {H : Type*} [Semiring H] [HopfAlgebra F H]
    [Algebra.FiniteType F H] :
    DiscreteTopology (principalPointsSubgroup F H) := by
  rw [← SetLike.isDiscrete_iff_discreteTopology, coe_principalPointsSubgroup,
    isDiscrete_iff_discreteTopology]
  exact discreteTopology_range_diagonal

end NumberField

end AdelicPoints

end TauCeti

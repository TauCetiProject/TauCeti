/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Discrete
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
public import TauCeti.Topology.Algebra.PointTopology.Prod
public import TauCeti.Topology.Algebra.PointTopology.Separation

/-!
# Adelic, finite-adelic, archimedean, and local point groups of affine group schemes

For an affine group scheme over a number field `F` represented by a Hopf algebra `H` over `F`, its
groups of rational, local, archimedean, finite-adelic, and full adelic points are the convolution
groups `WithConv (H →ₐ[F] R)` equipped with the affine evaluation topology (`PointTopology`) as `R`
ranges over `F`, its completions `v.adicCompletion F` and `w.Completion`, the archimedean product
`NumberField.InfiniteAdeleRing F`, the finite adele ring
`IsDedekindDomain.FiniteAdeleRing (𝓞 F) F`, and the full adele ring `NumberField.AdeleRing (𝓞 F) F`.

This file defines these topological groups together with:

* `TauCeti.characterValue`: evaluation of a group-like element `χ : GroupLike k H` of a Hopf algebra
  as a continuous group homomorphism `WithConv (H →ₐ[k] R) →* Rˣ` for any commutative `k`-algebra
  `R`, functorial in `R` and multiplicative in `χ`.
* Diagonal embeddings of `F`-rational points and place projections between full adelic,
  finite-adelic, archimedean, and single-place point groups, with their compatibility identities.
* Topological group splittings `AdelicPoints.prodEquiv` into archimedean times finite-adelic points
  (with closed factor embeddings `infiniteEmbed` and `finiteEmbed`) and
  `AdelicPoints.infinitePiEquiv` into the finite product over `InfinitePlace F`.
* Closedness of the diagonal subgroup of `F`-rational points in `AdelicPoints F H` for every Hopf
  algebra `H`, and its discreteness when `H` is a finitely generated commutative `F`-algebra.

## Main declarations

* `TauCeti.characterValue`: continuous homomorphism `WithConv (H →ₐ[k] R) →* Rˣ` attached to a
  character `χ : GroupLike k H`.
* `TauCeti.AdelicPoints`, `TauCeti.AdelicPoints.FiniteAdelicPoints`,
  `TauCeti.AdelicPoints.InfinitePoints`, `TauCeti.AdelicPoints.LocalPoints`,
  `TauCeti.AdelicPoints.InfiniteLocalPoints`: the adelic and local topological groups of points.
* `TauCeti.AdelicPoints.diagonal`, `TauCeti.AdelicPoints.finiteProjection`,
  `TauCeti.AdelicPoints.infiniteProjection`, `TauCeti.AdelicPoints.localProjection`: diagonal and
  projection homomorphisms.
* `TauCeti.AdelicPoints.prodEquiv`, `TauCeti.AdelicPoints.infinitePiEquiv`: archimedean/finite and
  archimedean-place topological group splittings.
* `TauCeti.AdelicPoints.isClosed_range_diagonal`,
  `TauCeti.AdelicPoints.discreteTopology_range_diagonal`: the diagonal subgroup of rational points
  is closed and discrete in `AdelicPoints F H`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  §§2–3.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.
-/

public section

open IsDedekindDomain NumberField Topology WithConv TauCeti.PointTopology
open scoped NumberField.AdeleRing

namespace TauCeti

section CharacterValue

variable {k H : Type*} [CommSemiring k] [Semiring H] [HopfAlgebra k H]

/-- Evaluating convolution points of a Hopf algebra `H` at a group-like element `χ : GroupLike k H`
defines a group homomorphism into `Rˣ`, with inverse given by evaluating at the antipode of `χ`. -/
noncomputable def characterValue (R : Type*) [CommSemiring R] [Algebra k R]
    (χ : GroupLike k H) : WithConv (H →ₐ[k] R) →* Rˣ where
  toFun x := Units.map x.ofConv.toMonoidHom (GroupLike.toUnits k χ)
  map_one' := Units.ext <| by
    simp [AlgHom.convOne_def]
  map_mul' x y := Units.ext <| by
    simp [AlgHom.convMul_apply, χ.2.comul_eq_tmul_self]

@[simp]
theorem coe_characterValue_apply (R : Type*) [CommSemiring R] [Algebra k R]
    (χ : GroupLike k H) (x : WithConv (H →ₐ[k] R)) :
    (characterValue R χ x : R) = x.ofConv χ := by
  rw [characterValue]
  rfl

@[simp]
theorem coe_inv_characterValue_apply (R : Type*) [CommSemiring R] [Algebra k R]
    (χ : GroupLike k H) (x : WithConv (H →ₐ[k] R)) :
    (↑(characterValue R χ x)⁻¹ : R) = x.ofConv (HopfAlgebra.antipode k (χ : H)) := by
  rw [characterValue]
  rfl

@[simp]
theorem characterValue_one (R : Type*) [CommSemiring R] [Algebra k R] :
    characterValue R (1 : GroupLike k H) = 1 := by
  ext x
  simp

@[simp]
theorem characterValue_mul (R : Type*) [CommSemiring R] [Algebra k R]
    (χ₁ χ₂ : GroupLike k H) (x : WithConv (H →ₐ[k] R)) :
    characterValue R (χ₁ * χ₂) x = characterValue R χ₁ x * characterValue R χ₂ x := by
  ext
  simp

/-- Character evaluation commutes with change of coefficient algebra. -/
theorem characterValue_mapValue {R S : Type*} [CommSemiring R] [Algebra k R]
    [CommSemiring S] [Algebra k S] (φ : R →ₐ[k] S) (χ : GroupLike k H)
    (x : WithConv (H →ₐ[k] R)) :
    characterValue S χ (AlgHom.mapValue φ x) =
      Units.map φ.toMonoidHom (characterValue R χ x) := by
  ext
  simp

/-- Character evaluation is continuous for the point topology and the units topology, for every
topology on the coefficient algebra `R`. -/
@[continuity, fun_prop]
theorem continuous_characterValue (R : Type*) [CommSemiring R] [Algebra k R] [TopologicalSpace R]
    (χ : GroupLike k H) :
    Continuous (characterValue R χ) := by
  rw [Units.continuous_iff]
  exact ⟨(continuous_eval_ofConv (χ : H)).congr fun x ↦ (coe_characterValue_apply R χ x).symm,
    (continuous_eval_ofConv (HopfAlgebra.antipode k (χ : H))).congr fun x ↦
      (coe_inv_characterValue_apply R χ x).symm⟩

end CharacterValue

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

/-- Coordinate evaluation `F_∞ →ₐ[F] F_w` at an infinite place `w`. -/
noncomputable def infiniteEvalAlgHom (F : Type*) [Field F] (w : InfinitePlace F) :
    InfiniteAdeleRing F →ₐ[F] w.Completion :=
  Pi.evalAlgHom F (fun w : InfinitePlace F ↦ w.Completion) w

@[simp]
theorem infiniteEvalAlgHom_apply (a : InfiniteAdeleRing F) (w : InfinitePlace F) :
    infiniteEvalAlgHom F w a = a w := by
  rw [infiniteEvalAlgHom]
  rfl

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
  AlgHom.mapValue (infiniteEvalAlgHom F w)

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
  simp [infiniteLocalProjection]

@[continuity, fun_prop]
theorem continuous_infiniteLocalProjection (w : InfinitePlace F) :
    Continuous (infiniteLocalProjection (F := F) (H := H) w) :=
  AlgHom.continuous_mapValue
    ((continuous_apply w).congr fun a ↦ (infiniteEvalAlgHom_apply a w).symm)

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
  rw [infinitePiEquiv, piPointsContinuousMulEquiv_apply, infiniteLocalProjection,
    infiniteEvalAlgHom]

@[simp]
theorem infinitePiEquiv_symm_ofConv_apply
    (f : ∀ w : InfinitePlace F, InfiniteLocalPoints F H w) (h : H) (w : InfinitePlace F) :
    ((infinitePiEquiv F H).symm f).ofConv h w = (f w).ofConv h :=
  piPointsContinuousMulEquiv_symm_ofConv_apply F H
    (fun w : InfinitePlace F ↦ w.Completion) f h w

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

/-- The first-coordinate projection `𝔸_F →ₐ[F] F_∞` as an `F`-algebra homomorphism. -/
noncomputable def adeleFstAlgHom (F : Type*) [Field F] [NumberField F] :
    AdeleRing (𝓞 F) F →ₐ[F] InfiniteAdeleRing F :=
  AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

/-- The second-coordinate projection `𝔸_F →ₐ[F] 𝔸_{F,f}` as an `F`-algebra homomorphism. -/
noncomputable def adeleSndAlgHom (F : Type*) [Field F] [NumberField F] :
    AdeleRing (𝓞 F) F →ₐ[F] FiniteAdeleRing (𝓞 F) F :=
  AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

@[simp]
theorem adeleFstAlgHom_apply (a : AdeleRing (𝓞 F) F) :
    adeleFstAlgHom F a = a.1 := by
  rw [adeleFstAlgHom]
  rfl

@[simp]
theorem adeleSndAlgHom_apply (a : AdeleRing (𝓞 F) F) :
    adeleSndAlgHom F a = a.2 := by
  rw [adeleSndAlgHom]
  rfl

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
  AlgHom.mapValue (adeleFstAlgHom F)

/-- Projection `G(𝔸_F) →* G(𝔸_{F,f})` onto the finite-adelic factor. -/
noncomputable def finiteProjection : AdelicPoints F H →* FiniteAdelicPoints F H :=
  AlgHom.mapValue (adeleSndAlgHom F)

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
  simp [infiniteProjection]

@[simp]
theorem finiteProjection_ofConv_apply (x : AdelicPoints F H) (h : H) :
    (finiteProjection x).ofConv h = (x.ofConv h).2 := by
  simp [finiteProjection]

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

@[continuity, fun_prop]
theorem continuous_infiniteProjection :
    Continuous (infiniteProjection (F := F) (H := H)) :=
  AlgHom.continuous_mapValue (continuous_fst.congr fun a ↦ (adeleFstAlgHom_apply a).symm)

@[continuity, fun_prop]
theorem continuous_finiteProjection :
    Continuous (finiteProjection (F := F) (H := H)) :=
  AlgHom.continuous_mapValue (continuous_snd.congr fun a ↦ (adeleSndAlgHom_apply a).symm)

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
  rw [prodEquiv, prodPointsContinuousMulEquiv_fst, infiniteProjection, adeleFstAlgHom]

@[simp]
theorem prodEquiv_snd (x : AdelicPoints F H) :
    (prodEquiv F H x).2 = finiteProjection x := by
  rw [prodEquiv, prodPointsContinuousMulEquiv_snd, finiteProjection, adeleSndAlgHom]

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
  rw [infiniteEmbed, infiniteProjection, adeleFstAlgHom, fst_inlPoints]

@[simp]
theorem finiteProjection_infiniteEmbed (x : InfinitePoints F H) :
    finiteProjection (infiniteEmbed F H x) = 1 := by
  rw [infiniteEmbed, finiteProjection, adeleSndAlgHom, snd_inlPoints]

@[simp]
theorem infiniteProjection_finiteEmbed (y : FiniteAdelicPoints F H) :
    infiniteProjection (finiteEmbed F H y) = 1 := by
  rw [finiteEmbed, infiniteProjection, adeleFstAlgHom, fst_inrPoints]

@[simp]
theorem finiteProjection_finiteEmbed (y : FiniteAdelicPoints F H) :
    finiteProjection (finiteEmbed F H y) = y := by
  rw [finiteEmbed, finiteProjection, adeleSndAlgHom, snd_inrPoints]

theorem infiniteEmbed_mul_finiteEmbed (x : InfinitePoints F H) (y : FiniteAdelicPoints F H) :
    infiniteEmbed F H x * finiteEmbed F H y = (prodEquiv F H).symm (x, y) := by
  apply (prodEquiv F H).injective
  ext1 <;> simp

@[continuity, fun_prop]
theorem continuous_infiniteEmbed : Continuous (infiniteEmbed F H) :=
  continuous_inlPoints F H (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

@[continuity, fun_prop]
theorem continuous_finiteEmbed : Continuous (finiteEmbed F H) :=
  continuous_inrPoints F H (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

theorem isClosedEmbedding_infiniteEmbed : IsClosedEmbedding (infiniteEmbed F H) :=
  isClosedEmbedding_inlPoints F H (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

theorem isClosedEmbedding_finiteEmbed : IsClosedEmbedding (finiteEmbed F H) :=
  isClosedEmbedding_inrPoints F H (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

/-! ### Injectivity, closedness, and discreteness of rational points -/

theorem diagonal_injective :
    Function.Injective (diagonal (F := F) (H := H)) :=
  AlgHom.mapValue_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem localDiagonal_injective (v : HeightOneSpectrum (𝓞 F)) :
    Function.Injective (localDiagonal (F := F) (H := H) v) :=
  AlgHom.mapValue_injective (RingHom.injective _)

theorem finiteDiagonal_injective :
    Function.Injective (finiteDiagonal (F := F) (H := H)) := by
  obtain ⟨J, hJ⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨J, hJ.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hJ
      (NumberField.RingOfIntegers.not_isField F)⟩
  refine .of_comp (f := finiteLocalProjection v) ?_
  simpa only [Function.comp_def, finiteLocalProjection_finiteDiagonal] using
    localDiagonal_injective (F := F) (H := H) v

theorem infiniteDiagonal_injective :
    Function.Injective (infiniteDiagonal (F := F) (H := H)) :=
  AlgHom.mapValue_injective (RingHom.injective _)

/-- The principal subalgebra of `𝔸_F` is the range of `Algebra.ofId F 𝔸_F`, whose underlying set is
`NumberField.AdeleRing.principalSubgroup (𝓞 F) F`. -/
private noncomputable def principalSubalgebra (F : Type*) [Field F] [NumberField F] :
    Subalgebra F (AdeleRing (𝓞 F) F) :=
  (Algebra.ofId F (AdeleRing (𝓞 F) F)).range

private instance discreteTopology_principalSubalgebra (F : Type*) [Field F] [NumberField F] :
    DiscreteTopology (principalSubalgebra F) :=
  inferInstanceAs <| DiscreteTopology (AdeleRing.principalSubgroup (𝓞 F) F)

private theorem isClosedEmbedding_principalSubalgebra_val (F : Type*) [Field F] [NumberField F] :
    IsClosedEmbedding (principalSubalgebra F).val :=
  IsClosedEmbedding.subtypeVal (TauCeti.GlobalNumberFields.isClosed_principalSubgroup F)

private theorem range_diagonal_eq_range_mapValue_principalSubalgebra :
    Set.range (diagonal (F := F) (H := H)) =
      Set.range (AlgHom.mapValue (H := H) (principalSubalgebra F).val) := by
  let e : F ≃ₐ[F] principalSubalgebra F :=
    AlgEquiv.ofInjective (Algebra.ofId F (AdeleRing (𝓞 F) F))
      (AdeleRing.algebraMap_injective (𝓞 F) F)
  have hcomp : Algebra.ofId F (AdeleRing (𝓞 F) F) =
      (principalSubalgebra F).val.comp e.toAlgHom := by
    ext
  have hsurj : Function.Surjective (AlgHom.mapValue (H := H) e.toAlgHom) := fun y ↦
    ⟨AlgHom.mapValue e.symm.toAlgHom y, ofConv_injective <| AlgHom.ext fun h ↦ by simp⟩
  rw [diagonal, hcomp, AlgHom.mapValue_comp, MonoidHom.coe_comp, hsurj.range_comp]

/-- The diagonal copy of `G(F)` is closed in `G(𝔸_F)` for every Hopf algebra `H` over `F`. -/
theorem isClosed_range_diagonal :
    IsClosed (Set.range (diagonal (F := F) (H := H))) := by
  rw [range_diagonal_eq_range_mapValue_principalSubalgebra]
  exact (AlgHom.isClosedEmbedding_mapValue
    (isClosedEmbedding_principalSubalgebra_val F)).isClosed_range

/-- When `H` is a finitely generated commutative Hopf `F`-algebra, the diagonal copy of `G(F)` is
discrete in `G(𝔸_F)`. -/
theorem discreteTopology_range_diagonal {H : Type*} [CommSemiring H] [HopfAlgebra F H]
    [Algebra.FiniteType F H] :
    DiscreteTopology (Set.range (diagonal (F := F) (H := H))) := by
  have : DiscreteTopology (H →ₐ[F] principalSubalgebra F) := discreteTopology_of_finiteType
  have : DiscreteTopology (WithConv (H →ₐ[F] principalSubalgebra F)) :=
    isHomeomorph_ofConv.isEmbedding.discreteTopology
  have hemb := AlgHom.isEmbedding_mapValue (H₁ := H)
    (isClosedEmbedding_principalSubalgebra_val F).isEmbedding
  let e : WithConv (H →ₐ[F] principalSubalgebra F) ≃ₜ
      Set.range (diagonal (F := F) (H := H)) :=
    hemb.toHomeomorph.trans
      (Homeomorph.setCongr range_diagonal_eq_range_mapValue_principalSubalgebra.symm)
  exact e.symm.isEmbedding.discreteTopology

/-- The subgroup of `F`-rational points inside `G(𝔸_F)`. -/
noncomputable def principalPointsSubgroup : Subgroup (AdelicPoints F H) :=
  (diagonal (F := F) (H := H)).range

theorem isClosed_principalPointsSubgroup :
    IsClosed (principalPointsSubgroup (F := F) (H := H) : Set (AdelicPoints F H)) :=
  isClosed_range_diagonal

instance discreteTopology_principalPointsSubgroup {H : Type*} [CommSemiring H] [HopfAlgebra F H]
    [Algebra.FiniteType F H] :
    DiscreteTopology (principalPointsSubgroup (F := F) (H := H)) :=
  discreteTopology_range_diagonal

end NumberField

/-- The trivial group scheme `Spec F` has a single adelic point. -/
instance instSubsingletonSelf (F : Type*) [Field F] [NumberField F] :
    Subsingleton (AdelicPoints F F) :=
  ⟨fun x y ↦ ofConv_injective <| AlgHom.ext fun c ↦
    (x.ofConv.commutes c).trans (y.ofConv.commutes c).symm⟩

end AdelicPoints

end TauCeti

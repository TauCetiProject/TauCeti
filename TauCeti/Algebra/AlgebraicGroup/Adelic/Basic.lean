/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Topology
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Topology
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
public import TauCeti.Topology.Algebra.PointTopology.Prod
public import TauCeti.Topology.Algebra.PointTopology.Separation

/-!
# Additional adelic and local point-group API

Extending `TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic`, this file provides:
* local rational diagonals `localDiagonal` and `infiniteLocalDiagonal`, together with injectivity
  of all diagonal maps (`diagonal_injective`, `finiteDiagonal_injective`,
  `infiniteDiagonal_injective`);
* archimedean product splitting `piInfiniteContinuousMulEquiv : InfinitePoints K H ≃ₜ*
  ∏_{w ∣ ∞} InfiniteLocalPoints K H w`;
* the infinite embedding `infiniteEmbed`, closed-embedding results `isClosedEmbedding_infiniteEmbed`
  and `isClosedEmbedding_finiteEmbed`, and the factorization `infiniteEmbed_mul_finiteEmbed`;
* explicit identifications of adelic and finite-adelic points of `𝔾ₐ` and `𝔾ₘ`
  (`gaContinuousMulEquiv`, `gmContinuousMulEquiv`, `finiteGaContinuousMulEquiv`,
  `finiteGmContinuousMulEquiv`).

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1 and §3, pp. 2–5.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.1–1.2, pp. 6–7.
-/

public section

open IsDedekindDomain Topology WithConv TauCeti.PointTopology
open scoped LaurentPolynomial

namespace TauCeti.AdelicPoints

/-- Points of `Spec H` at an archimedean place `w` of `K`, with the point topology. -/
abbrev InfiniteLocalPoints (K H : Type*) [Field K] [Semiring H] [Algebra K H]
    (w : NumberField.InfinitePlace K) := WithConv (H →ₐ[K] w.Completion)

section InfiniteLocal

variable (K H : Type*) [Field K] [Semiring H] [Bialgebra K H]

/-- Diagonal homomorphism from `K`-rational points of `H` to `w`-adic points at `w`. -/
noncomputable def infiniteLocalDiagonal (w : NumberField.InfinitePlace K) :
    WithConv (H →ₐ[K] K) →* InfiniteLocalPoints K H w :=
  AlgHom.mapValue (Algebra.ofId K w.Completion)

variable {K H}

/-- Evaluating a diagonal archimedean local point applies `algebraMap K w.Completion`. -/
@[simp]
theorem infiniteLocalDiagonal_apply_apply (w : NumberField.InfinitePlace K)
    (g : WithConv (H →ₐ[K] K)) (h : H) :
    infiniteLocalDiagonal K H w g h = algebraMap K w.Completion (g h) := by
  simp [infiniteLocalDiagonal]

/-- The diagonal map into `InfiniteLocalPoints K H w` is injective. -/
theorem infiniteLocalDiagonal_injective (w : NumberField.InfinitePlace K) :
    Function.Injective (infiniteLocalDiagonal K H w) :=
  AlgHom.mapValue_injective (algebraMap K w.Completion).injective

end InfiniteLocal

section InfinitePi

variable (K H : Type*) [Field K] [Semiring H] [Bialgebra K H]

/-- Product decomposition `G(K_∞) ≃ₜ* ∏_{w ∣ ∞} G(K_w)` of archimedean adelic points. -/
noncomputable def piInfiniteContinuousMulEquiv :
    InfinitePoints K H ≃ₜ* ∀ w : NumberField.InfinitePlace K, InfiniteLocalPoints K H w :=
  piPointsContinuousMulEquiv K H (fun w : NumberField.InfinitePlace K ↦ w.Completion)

variable {K H}

/-- Whenever `InfiniteAdeleRing K` is nontrivial, `infiniteDiagonal` is injective. -/
theorem infiniteDiagonal_injective [Nontrivial (NumberField.InfiniteAdeleRing K)] :
    Function.Injective (infiniteDiagonal K H) := fun _ _ h₁₂ ↦
  WithConv.ofConv_injective <| AlgHom.ext fun h ↦
    (algebraMap K (NumberField.InfiniteAdeleRing K)).injective <| by
      simpa only [infiniteDiagonal_apply_apply] using
        congrArg (fun p : InfinitePoints K H ↦ p h) h₁₂

/-- Projecting a diagonal infinite-adelic point to `w` gives `infiniteLocalDiagonal K H w g`. -/
theorem infiniteLocalProjection_infiniteDiagonal_eq (w : NumberField.InfinitePlace K)
    (g : WithConv (H →ₐ[K] K)) :
    infiniteLocalProjection K H w (infiniteDiagonal K H g) = infiniteLocalDiagonal K H w g :=
  infiniteLocalProjection_infiniteDiagonal w g

/-- At each infinite place `w`, `piInfiniteContinuousMulEquiv` agrees with
`infiniteLocalProjection K H w`. -/
@[simp]
theorem piInfiniteContinuousMulEquiv_apply (x : InfinitePoints K H)
    (w : NumberField.InfinitePlace K) :
    piInfiniteContinuousMulEquiv K H x w = infiniteLocalProjection K H w x := by
  refine WithConv.ofConv_injective <| AlgHom.ext fun h ↦ ?_
  change ((piPointsContinuousMulEquiv K H _ x) w).ofConv h = _
  rw [piPointsContinuousMulEquiv_apply]
  simp

/-- Evaluating `(piInfiniteContinuousMulEquiv K H).symm f` on `h : H` at `w` gives
`(f w).ofConv h`. -/
@[simp]
theorem piInfiniteContinuousMulEquiv_symm_apply_ofConv
    (f : ∀ w : NumberField.InfinitePlace K, InfiniteLocalPoints K H w)
    (h : H) (w : NumberField.InfinitePlace K) :
    ((piInfiniteContinuousMulEquiv K H).symm f).ofConv h w = (f w).ofConv h :=
  piPointsContinuousMulEquiv_symm_apply_ofConv f h w

end InfinitePi

section LocalDiagonal

variable (R K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Semiring H] [Bialgebra K H]

/-- Diagonal homomorphism from `K`-rational points of `H` to `v`-adic points at `v`. -/
noncomputable def localDiagonal (v : HeightOneSpectrum R) :
    WithConv (H →ₐ[K] K) →* LocalPoints R K H v :=
  AlgHom.mapValue (Algebra.ofId K (v.adicCompletion K))

variable {R K H}

/-- Evaluating a diagonal `v`-adic point applies `algebraMap K (v.adicCompletion K)`. -/
@[simp]
theorem localDiagonal_apply_apply (v : HeightOneSpectrum R) (g : WithConv (H →ₐ[K] K)) (h : H) :
    localDiagonal R K H v g h = algebraMap K (v.adicCompletion K) (g h) := by
  simp [localDiagonal]

/-- Evaluating `(localDiagonal R K H v g).ofConv` applies `algebraMap K (v.adicCompletion K)`. -/
theorem localDiagonal_apply_ofConv (v : HeightOneSpectrum R) (g : WithConv (H →ₐ[K] K)) (h : H) :
    (localDiagonal R K H v g).ofConv h = algebraMap K (v.adicCompletion K) (g.ofConv h) := by
  simp [localDiagonal]

/-- The diagonal map into `LocalPoints R K H v` is injective. -/
theorem localDiagonal_injective (v : HeightOneSpectrum R) :
    Function.Injective (localDiagonal R K H v) :=
  AlgHom.mapValue_injective (algebraMap K (v.adicCompletion K)).injective

end LocalDiagonal

section FiniteAndAdelic

variable (R K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Semiring H] [Bialgebra K H]

/-- Inclusion of `InfinitePoints K H` into `AdelicPoints R K H` as `x ↦ (x, 1)`. -/
noncomputable def infiniteEmbed : InfinitePoints K H →* AdelicPoints R K H :=
  (prodContinuousMulEquiv R K H).symm.toMonoidHom.comp (MonoidHom.inl _ _)

variable {R K H}

/-- When `R` is a field, `HeightOneSpectrum R` is empty and `FiniteAdelicPoints R K H` is a
subsingleton. -/
theorem finiteAdelicPoints_subsingleton_of_isField (hR : IsField R) :
    Subsingleton (FiniteAdelicPoints R K H) :=
  have := FiniteAdeleRing.subsingleton_of_isField K hR
  ⟨fun _ _ ↦ WithConv.ext <| AlgHom.ext fun _ ↦ Subsingleton.elim _ _⟩

/-- When `FiniteAdeleRing R K` is nontrivial, `finiteDiagonal` is injective. -/
theorem finiteDiagonal_injective [Nontrivial (FiniteAdeleRing R K)] :
    Function.Injective (finiteDiagonal R K H) := fun _ _ h₁₂ ↦
  WithConv.ofConv_injective <| AlgHom.ext fun h ↦
    (algebraMap K (FiniteAdeleRing R K)).injective <| by
      simpa only [finiteDiagonal_apply_apply] using
        congrArg (fun p : FiniteAdelicPoints R K H ↦ p h) h₁₂

/-- When `R` is not a field, `finiteDiagonal` is injective. -/
theorem finiteDiagonal_injective_of_not_isField (hR : ¬ IsField R) :
    Function.Injective (finiteDiagonal R K H) :=
  have := HeightOneSpectrum.nonempty_of_not_isField hR; finiteDiagonal_injective

/-- When `AdeleRing R K` is nontrivial, `diagonal` is injective. -/
theorem diagonal_injective [Nontrivial (NumberField.AdeleRing R K)] :
    Function.Injective (diagonal R K H) := fun _ _ h₁₂ ↦
  WithConv.ofConv_injective <| AlgHom.ext fun h ↦
    (algebraMap K (NumberField.AdeleRing R K)).injective <| by
      simpa only [diagonal_apply_apply] using congrArg (fun p : AdelicPoints R K H ↦ p h) h₁₂

/-- Whenever `R` is not a field, `diagonal` is injective. -/
theorem diagonal_injective_of_not_isField (hR : ¬ IsField R) :
    Function.Injective (diagonal R K H) :=
  have := HeightOneSpectrum.nonempty_of_not_isField hR; diagonal_injective

/-- Under `prodContinuousMulEquiv`, a diagonal adelic point splits into diagonal components. -/
theorem prodContinuousMulEquiv_diagonal (g : WithConv (H →ₐ[K] K)) :
    prodContinuousMulEquiv R K H (diagonal R K H g) =
      (infiniteDiagonal K H g, finiteDiagonal R K H g) :=
  Prod.ext (by simp) (by simp)

/-- `infiniteEmbed` maps `x` to `(x, 1)` under `prodContinuousMulEquiv`. -/
theorem prodContinuousMulEquiv_infiniteEmbed (x : InfinitePoints K H) :
    prodContinuousMulEquiv R K H (infiniteEmbed R K H x) = (x, 1) :=
  (prodContinuousMulEquiv R K H).apply_symm_apply (x, 1)

/-- `infiniteProjection` is a left inverse of `infiniteEmbed`. -/
@[simp]
theorem infiniteProjection_infiniteEmbed (x : InfinitePoints K H) :
    infiniteProjection R K H (infiniteEmbed R K H x) = x :=
  congr_arg Prod.fst ((prodContinuousMulEquiv_apply _).symm.trans
    (prodContinuousMulEquiv_infiniteEmbed x))

/-- `finiteProjection` sends `infiniteEmbed x` to `1`. -/
@[simp]
theorem finiteProjection_infiniteEmbed (x : InfinitePoints K H) :
    finiteProjection R K H (infiniteEmbed R K H x) = 1 :=
  congr_arg Prod.snd ((prodContinuousMulEquiv_apply _).symm.trans
    (prodContinuousMulEquiv_infiniteEmbed x))

/-- Factorization `infiniteEmbed (infiniteProjection x) * finiteEmbed (finiteProjection x) = x`. -/
theorem infiniteEmbed_mul_finiteEmbed (x : AdelicPoints R K H) :
    infiniteEmbed R K H (infiniteProjection R K H x) *
        finiteEmbed R K H (finiteProjection R K H x) = x := by
  apply (prodContinuousMulEquiv R K H).injective; simp [map_mul]

/-- `infiniteEmbed` is continuous. -/
@[continuity, fun_prop]
theorem continuous_infiniteEmbed : Continuous (infiniteEmbed R K H) :=
  (prodContinuousMulEquiv R K H).symm.continuous.comp (continuous_id.prodMk continuous_const)

/-- `infiniteEmbed` is a closed embedding into `AdelicPoints R K H`. -/
theorem isClosedEmbedding_infiniteEmbed : IsClosedEmbedding (infiniteEmbed R K H) :=
  Function.LeftInverse.isClosedEmbedding infiniteProjection_infiniteEmbed
    continuous_infiniteProjection continuous_infiniteEmbed

/-- `finiteEmbed` is a closed embedding into `AdelicPoints R K H`. -/
theorem isClosedEmbedding_finiteEmbed : IsClosedEmbedding (finiteEmbed R K H) :=
  Function.LeftInverse.isClosedEmbedding finiteProjection_finiteEmbed
    continuous_finiteProjection continuous_finiteEmbed

/-- Finite-adelic points of `𝔾ₐ` are topologically isomorphic to
`Multiplicative (FiniteAdeleRing R K)`. -/
noncomputable def finiteGaContinuousMulEquiv (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    FiniteAdelicPoints R K (SymmetricAlgebra K K) ≃ₜ* Multiplicative (FiniteAdeleRing R K) :=
  AdditiveGroup.gaPointsContinuousMulEquiv K (FiniteAdeleRing R K)

/-- Forward map of `finiteGaContinuousMulEquiv`. -/
@[simp]
theorem finiteGaContinuousMulEquiv_apply (x : FiniteAdelicPoints R K (SymmetricAlgebra K K)) :
    finiteGaContinuousMulEquiv R K x = AdditiveGroup.gaPointsMulEquiv x :=
  AdditiveGroup.gaPointsContinuousMulEquiv_apply x

/-- Inverse map of `finiteGaContinuousMulEquiv`. -/
@[simp]
theorem finiteGaContinuousMulEquiv_symm_apply (a : Multiplicative (FiniteAdeleRing R K)) :
    (finiteGaContinuousMulEquiv R K).symm a = (AdditiveGroup.gaPointsMulEquiv (R := K)).symm a :=
  AdditiveGroup.gaPointsContinuousMulEquiv_symm_apply a

/-- Topological group isomorphism `Gₘ(𝔸ᶠ[R, K]) ≃ₜ* (FiniteAdeleRing R K)ˣ`. -/
noncomputable def finiteGmContinuousMulEquiv (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    FiniteAdelicPoints R K K[T;T⁻¹] ≃ₜ* (FiniteAdeleRing R K)ˣ :=
  MultiplicativeGroup.pointsContinuousMulEquiv K (FiniteAdeleRing R K)

/-- Forward map of `finiteGmContinuousMulEquiv`. -/
@[simp]
theorem finiteGmContinuousMulEquiv_apply (x : FiniteAdelicPoints R K K[T;T⁻¹]) :
    finiteGmContinuousMulEquiv R K x = MultiplicativeGroup.pointsMulEquiv x :=
  MultiplicativeGroup.pointsContinuousMulEquiv_apply x

/-- Inverse map of `finiteGmContinuousMulEquiv`. -/
@[simp]
theorem finiteGmContinuousMulEquiv_symm_apply (u : (FiniteAdeleRing R K)ˣ) :
    (finiteGmContinuousMulEquiv R K).symm u =
      (MultiplicativeGroup.pointsMulEquiv (R := K)).symm u :=
  MultiplicativeGroup.pointsContinuousMulEquiv_symm_apply u

/-- Topological group isomorphism `Gₐ(𝔸[R, K]) ≃ₜ* Multiplicative (NumberField.AdeleRing R K)`. -/
noncomputable def gaContinuousMulEquiv (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    AdelicPoints R K (SymmetricAlgebra K K) ≃ₜ* Multiplicative (NumberField.AdeleRing R K) :=
  AdditiveGroup.gaPointsContinuousMulEquiv K (NumberField.AdeleRing R K)

/-- Forward map of `AdelicPoints.gaContinuousMulEquiv`. -/
@[simp]
theorem gaContinuousMulEquiv_apply (x : AdelicPoints R K (SymmetricAlgebra K K)) :
    gaContinuousMulEquiv R K x = AdditiveGroup.gaPointsMulEquiv x :=
  AdditiveGroup.gaPointsContinuousMulEquiv_apply x

/-- Inverse map of `AdelicPoints.gaContinuousMulEquiv`. -/
@[simp]
theorem gaContinuousMulEquiv_symm_apply (a : Multiplicative (NumberField.AdeleRing R K)) :
    (gaContinuousMulEquiv R K).symm a = (AdditiveGroup.gaPointsMulEquiv (R := K)).symm a :=
  AdditiveGroup.gaPointsContinuousMulEquiv_symm_apply a

/-- Topological group isomorphism `Gₘ(𝔸[R, K]) ≃ₜ* IdeleGroup R K` (Conrad 2012, Example 3.1). -/
noncomputable def gmContinuousMulEquiv (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    AdelicPoints R K K[T;T⁻¹] ≃ₜ* NumberField.IdeleGroup R K :=
  MultiplicativeGroup.pointsContinuousMulEquiv K (NumberField.AdeleRing R K)

/-- Forward map of `AdelicPoints.gmContinuousMulEquiv`. -/
@[simp]
theorem gmContinuousMulEquiv_apply (x : AdelicPoints R K K[T;T⁻¹]) :
    gmContinuousMulEquiv R K x = MultiplicativeGroup.pointsMulEquiv x :=
  MultiplicativeGroup.pointsContinuousMulEquiv_apply x

/-- Inverse map of `AdelicPoints.gmContinuousMulEquiv`. -/
@[simp]
theorem gmContinuousMulEquiv_symm_apply (u : NumberField.IdeleGroup R K) :
    (gmContinuousMulEquiv R K).symm u = (MultiplicativeGroup.pointsMulEquiv (R := K)).symm u :=
  MultiplicativeGroup.pointsContinuousMulEquiv_symm_apply u

end FiniteAndAdelic

end TauCeti.AdelicPoints

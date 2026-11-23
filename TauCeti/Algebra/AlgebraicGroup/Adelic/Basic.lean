/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic
public import TauCeti.Topology.Algebra.PointTopology.Separation

/-!
# Additional adelic and local point-group API

Extending `TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic`, this file provides:
* local rational diagonals `localDiagonal` and `infiniteLocalDiagonal`, together with injectivity
  of all diagonal maps (`diagonal_injective`, `finiteDiagonal_injective`,
  `infiniteDiagonal_injective`);
* archimedean product splitting `piInfiniteContinuousMulEquiv : InfinitePoints K H ≃ₜ*
  ∀ w, InfiniteLocalPoints K H w`;
* the infinite embedding `infiniteEmbed`, closed-embedding results `isClosedEmbedding_infiniteEmbed`
  and `isClosedEmbedding_finiteEmbed`, and the factorization `infiniteEmbed_mul_finiteEmbed`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1 and §3.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.1–1.2, pp. 6–7.
-/

public section

open IsDedekindDomain Topology WithConv TauCeti.PointTopology

namespace TauCeti.AdelicPoints

/-- Wrapped `K`-algebra homomorphisms `H →ₐ[K] w.Completion` into the completion at an
archimedean place `w` of `K`, with the point topology; when `H` is commutative (resp. a
commutative Hopf algebra), these are the `w`-adic points (resp. group of points) of `Spec H`. -/
abbrev InfiniteLocalPoints (K H : Type*) [Field K] [Semiring H] [Algebra K H]
    (w : NumberField.InfinitePlace K) := WithConv (H →ₐ[K] w.Completion)

section InfiniteLocal

variable (K H : Type*) [Field K] [Semiring H] [Bialgebra K H]

/-- Diagonal homomorphism from `WithConv (H →ₐ[K] K)` to `InfiniteLocalPoints K H w`. -/
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

private theorem injective_of_diagonal_apply {K H R' : Type*} [Field K] [Semiring H]
    [Algebra K H] [CommSemiring R'] [Algebra K R'] [Nontrivial R']
    (f : WithConv (H →ₐ[K] K) → WithConv (H →ₐ[K] R'))
    (hf : ∀ g h, f g h = algebraMap K R' (g h)) : Function.Injective f := fun _ _ h₁₂ ↦
  WithConv.ofConv_injective <| AlgHom.ext fun h ↦
    (algebraMap K R').injective <| by simpa only [hf] using congrArg (fun p ↦ p h) h₁₂

section InfinitePi

variable (K H : Type*) [Field K] [Semiring H] [Bialgebra K H]

/-- Multiplicative homeomorphism identifying `InfinitePoints K H` with the product
`∀ w : NumberField.InfinitePlace K, InfiniteLocalPoints K H w` (an isomorphism of topological
monoids, or topological groups when `H` is a Hopf algebra). -/
noncomputable def piInfiniteContinuousMulEquiv :
    InfinitePoints K H ≃ₜ* ∀ w : NumberField.InfinitePlace K, InfiniteLocalPoints K H w :=
  piPointsContinuousMulEquiv K H (fun w : NumberField.InfinitePlace K ↦ w.Completion)

variable {K H}

/-- Whenever `InfiniteAdeleRing K` is nontrivial, `infiniteDiagonal` is injective. -/
theorem infiniteDiagonal_injective [Nontrivial (NumberField.InfiniteAdeleRing K)] :
    Function.Injective (infiniteDiagonal K H) :=
  -- `infiniteDiagonal` is not `@[expose]`d in `AdelicPoints.Basic`, so `mapValue_injective`
  -- cannot unify.
  injective_of_diagonal_apply _ infiniteDiagonal_apply_apply

/-- At each infinite place `w`, `piInfiniteContinuousMulEquiv` agrees with
`infiniteLocalProjection K H w`. -/
@[simp]
theorem piInfiniteContinuousMulEquiv_apply (x : InfinitePoints K H)
    (w : NumberField.InfinitePlace K) :
    piInfiniteContinuousMulEquiv K H x w = infiniteLocalProjection K H w x := by
  refine WithConv.ofConv_injective <| AlgHom.ext fun h ↦ ?_
  have hpi : (piInfiniteContinuousMulEquiv K H x w).ofConv h =
      (AlgHom.mapValue (Pi.evalAlgHom K _ w) x).ofConv h :=
    congrArg (fun p ↦ p.ofConv h) (piPointsContinuousMulEquiv_apply x w)
  have heval : (AlgHom.mapValue (Pi.evalAlgHom K _ w) x).ofConv h =
      (infiniteLocalProjection K H w x).ofConv h := by
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      infiniteLocalProjection_apply_apply]
    exact Pi.evalAlgHom_apply ..
  exact hpi.trans heval

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

/-- Diagonal homomorphism from `WithConv (H →ₐ[K] K)` to `LocalPoints R K H v`. -/
noncomputable def localDiagonal (v : HeightOneSpectrum R) :
    WithConv (H →ₐ[K] K) →* LocalPoints R K H v :=
  AlgHom.mapValue (Algebra.ofId K (v.adicCompletion K))

variable {R K H}

/-- Evaluating a diagonal `v`-adic point applies `algebraMap K (v.adicCompletion K)`. -/
@[simp]
theorem localDiagonal_apply_apply (v : HeightOneSpectrum R) (g : WithConv (H →ₐ[K] K)) (h : H) :
    localDiagonal R K H v g h = algebraMap K (v.adicCompletion K) (g h) := by
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
    Function.Injective (finiteDiagonal R K H) :=
  -- `finiteDiagonal` is not `@[expose]`d in `AdelicPoints.Basic`, so `mapValue_injective`
  -- cannot unify.
  injective_of_diagonal_apply _ finiteDiagonal_apply_apply

/-- When `R` is not a field, `finiteDiagonal` is injective. -/
theorem finiteDiagonal_injective_of_not_isField (hR : ¬ IsField R) :
    Function.Injective (finiteDiagonal R K H) :=
  have := HeightOneSpectrum.nonempty_of_not_isField hR; finiteDiagonal_injective

/-- When `AdeleRing R K` is nontrivial, `diagonal` is injective. -/
theorem diagonal_injective [Nontrivial (NumberField.AdeleRing R K)] :
    Function.Injective (diagonal R K H) :=
  -- `diagonal` is not `@[expose]`d in `AdelicPoints.Basic`, so `mapValue_injective` cannot unify.
  injective_of_diagonal_apply _ diagonal_apply_apply

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

end FiniteAndAdelic

end TauCeti.AdelicPoints

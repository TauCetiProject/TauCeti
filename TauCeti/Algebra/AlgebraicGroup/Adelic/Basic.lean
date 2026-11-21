/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Topology
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Topology
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
public import TauCeti.Topology.Algebra.PointTopology.Prod
public import TauCeti.Topology.Algebra.PointTopology.Separation

/-!
# Adelic, finite-adelic, and local point groups of an affine group

Let `R` be a Dedekind domain with fraction field `K`, and let `H` be the coordinate bialgebra (or
Hopf algebra) of `G = Spec H` over `K`. Evaluating `A ↦ WithConv (H →ₐ[K] A)` on
`NumberField.AdeleRing R K`, `IsDedekindDomain.FiniteAdeleRing R K`,
`NumberField.InfiniteAdeleRing K`, `v.adicCompletion K`, and `w.Completion` defines the
`𝔸[R, K]`-valued, finite-adelic, infinite-adelic, and local point spaces of `G` with the evaluation
point topology (Conrad 2012, Proposition 2.1 and §3), requiring no embedding `G ↪ GL_n` and no
integral model. Here `AdelicPoints R K H` is `G(𝔸[R, K]) = G(K_∞ × 𝔸ᶠ[R, K])`: when `K` is a number
field and `R = 𝓞 K`, this is the global adelic group `G(𝔸_K)`, whereas for function fields
`InfinitePlace K` is empty so it collapses to `G(𝔸ᶠ[R, K])`, and for proper localizations of `𝓞 K`
the inverted finite places are omitted.

## Main declarations

* `TauCeti.AdelicPoints`, `TauCeti.FiniteAdelicPoints`, `TauCeti.InfinitePoints`,
  `TauCeti.LocalPoints`, `TauCeti.InfiniteLocalPoints`: adelic and local point spaces.
* `TauCeti.InfinitePoints.piContinuousMulEquiv`, `TauCeti.AdelicPoints.splittingContinuousMulEquiv`:
  `G(K_∞) ≃ₜ* ∏_{w ∣ ∞} G(K_w)` and `G(𝔸[R, K]) ≃ₜ* G(K_∞) × G(𝔸ᶠ[R, K])`, with closed factor
  inclusions `infiniteEmbed` and `finiteEmbed`.
* Diagonal homomorphisms `diagonal` and place projections, with sharp injectivity criteria and
  concrete identifications `gaContinuousMulEquiv` and `gmContinuousMulEquiv` for `𝔾ₐ` and `𝔾ₘ`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1 and §3, pp. 2–5.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.1–1.2, pp. 6–7.
-/

public section

open IsDedekindDomain Topology WithConv TauCeti.PointTopology
open scoped LaurentPolynomial

namespace TauCeti

/-- Points of `Spec H` at an archimedean place `w` of `K`, with the point topology. -/
abbrev InfiniteLocalPoints (K H : Type*) [Field K] [Semiring H] [Algebra K H]
    (w : NumberField.InfinitePlace K) := WithConv (H →ₐ[K] w.Completion)

/-- Points of `Spec H` over `InfiniteAdeleRing K = ∏_{w ∣ ∞} K_w`, with the point topology. -/
abbrev InfinitePoints (K H : Type*) [Field K] [Semiring H] [Algebra K H] :=
  WithConv (H →ₐ[K] NumberField.InfiniteAdeleRing K)

/-- Points of `Spec H` at a finite place `v` of `(R, K)`, valued in `v.adicCompletion K`. -/
abbrev LocalPoints {R : Type*} (K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Semiring H] [Algebra K H] (v : HeightOneSpectrum R) :=
  WithConv (H →ₐ[K] v.adicCompletion K)

/-- Finite-adelic points `G(𝔸ᶠ[R, K])` of `Spec H`, valued in `FiniteAdeleRing R K`. -/
abbrev FiniteAdelicPoints (R K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Semiring H] [Algebra K H] :=
  WithConv (H →ₐ[K] FiniteAdeleRing R K)

/-- Points `G(𝔸[R, K])` of `Spec H` valued in `NumberField.AdeleRing R K = K_∞ × 𝔸ᶠ[R, K]` (the
global adelic points `G(𝔸_K)` when `K` is a number field and `R = 𝓞 K`). -/
abbrev AdelicPoints (R K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Semiring H] [Algebra K H] :=
  WithConv (H →ₐ[K] NumberField.AdeleRing R K)

namespace InfiniteLocalPoints

variable (K H : Type*) [Field K] [Semiring H] [Bialgebra K H]

/-- Diagonal homomorphism from `K`-rational points of `H` to `w`-adic points at `w`. -/
noncomputable def diagonal (w : NumberField.InfinitePlace K) :
    WithConv (H →ₐ[K] K) →* InfiniteLocalPoints K H w :=
  AlgHom.mapValue (Algebra.ofId K w.Completion)

variable {K H}

/-- Evaluating a diagonal archimedean local point applies `algebraMap K w.Completion`. -/
@[simp]
theorem diagonal_apply_ofConv (w : NumberField.InfinitePlace K) (g : WithConv (H →ₐ[K] K)) (h : H) :
    (diagonal K H w g).ofConv h = algebraMap K w.Completion (g.ofConv h) := by simp [diagonal]

/-- The diagonal map into `InfiniteLocalPoints K H w` is injective. -/
theorem diagonal_injective (w : NumberField.InfinitePlace K) :
    Function.Injective (diagonal K H w) :=
  AlgHom.mapValue_injective (algebraMap K w.Completion).injective

end InfiniteLocalPoints

namespace InfinitePoints

variable (K H : Type*) [Field K] [Semiring H] [Bialgebra K H]

/-- Diagonal homomorphism from `K`-rational points of `H` to infinite-adelic points. -/
noncomputable def diagonal : WithConv (H →ₐ[K] K) →* InfinitePoints K H :=
  AlgHom.mapValue (Algebra.ofId K (NumberField.InfiniteAdeleRing K))

/-- Projection from infinite-adelic points to the completion at an archimedean place `w`. -/
noncomputable def localProjection (w : NumberField.InfinitePlace K) :
    InfinitePoints K H →* InfiniteLocalPoints K H w :=
  AlgHom.mapValue (Pi.evalAlgHom K (fun w : NumberField.InfinitePlace K ↦ w.Completion) w)

/-- Product decomposition `G(K_∞) ≃ₜ* ∏_{w ∣ ∞} G(K_w)` of archimedean adelic points. -/
noncomputable def piContinuousMulEquiv :
    InfinitePoints K H ≃ₜ* ∀ w : NumberField.InfinitePlace K, InfiniteLocalPoints K H w :=
  piPointsContinuousMulEquiv K H (fun w : NumberField.InfinitePlace K ↦ w.Completion)

variable {K H}

/-- Evaluating a diagonal infinite-adelic point applies `algebraMap K (InfiniteAdeleRing K)`. -/
@[simp]
theorem diagonal_apply_ofConv (g : WithConv (H →ₐ[K] K)) (h : H) :
    (diagonal K H g).ofConv h = algebraMap K (NumberField.InfiniteAdeleRing K) (g.ofConv h) := by
  simp [diagonal]

/-- Whenever `InfiniteAdeleRing K` is nontrivial (in particular over any number field), the
diagonal map into `InfinitePoints K H` is injective. -/
theorem diagonal_injective [Nontrivial (NumberField.InfiniteAdeleRing K)] :
    Function.Injective (diagonal K H) :=
  AlgHom.mapValue_injective (algebraMap K (NumberField.InfiniteAdeleRing K)).injective

/-- Evaluating `localProjection` at `w` reads the `w`-coordinate of an infinite-adelic point. -/
@[simp]
theorem localProjection_apply_ofConv (w : NumberField.InfinitePlace K)
    (x : InfinitePoints K H) (h : H) :
    (localProjection K H w x).ofConv h = x.ofConv h w := by
  rw [localProjection, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
  exact Pi.evalAlgHom_apply _ _ w (x.ofConv h)

/-- Projection from infinite-adelic points to an archimedean place is continuous. -/
@[continuity, fun_prop]
theorem continuous_localProjection (w : NumberField.InfinitePlace K) :
    Continuous (localProjection K H w) :=
  AlgHom.continuous_mapValue (continuous_apply w)

/-- Projecting a diagonal infinite-adelic point to `w` gives the diagonal local point at `w`. -/
@[simp]
theorem localProjection_diagonal (w : NumberField.InfinitePlace K) (g : WithConv (H →ₐ[K] K)) :
    localProjection K H w (diagonal K H g) = InfiniteLocalPoints.diagonal K H w g := by
  simp only [localProjection, diagonal, InfiniteLocalPoints.diagonal, ← MonoidHom.comp_apply,
    ← AlgHom.mapValue_comp, Algebra.comp_ofId]

/-- At each infinite place `w`, `piContinuousMulEquiv` agrees with `localProjection K H w`. -/
@[simp]
theorem piContinuousMulEquiv_apply (x : InfinitePoints K H) (w : NumberField.InfinitePlace K) :
    piContinuousMulEquiv K H x w = localProjection K H w x := by
  rw [piContinuousMulEquiv, localProjection]
  exact piPointsContinuousMulEquiv_apply x w

/-- Evaluating `(piContinuousMulEquiv K H).symm f` on `h : H` at `w` gives `(f w).ofConv h`. -/
@[simp]
theorem piContinuousMulEquiv_symm_apply_ofConv
    (f : ∀ w : NumberField.InfinitePlace K, InfiniteLocalPoints K H w) (h : H)
    (w : NumberField.InfinitePlace K) :
    ((piContinuousMulEquiv K H).symm f).ofConv h w = (f w).ofConv h := by
  rw [piContinuousMulEquiv]
  exact piPointsContinuousMulEquiv_symm_apply_ofConv f h w

end InfinitePoints

namespace LocalPoints

variable {R : Type*} (K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Semiring H] [Bialgebra K H]

/-- Diagonal homomorphism from `K`-rational points of `H` to `v`-adic points at `v`. -/
noncomputable def diagonal (v : HeightOneSpectrum R) :
    WithConv (H →ₐ[K] K) →* LocalPoints K H v :=
  AlgHom.mapValue (Algebra.ofId K (v.adicCompletion K))

variable {K H}

/-- Evaluating a diagonal `v`-adic point applies `algebraMap K (v.adicCompletion K)`. -/
@[simp]
theorem diagonal_apply_ofConv (v : HeightOneSpectrum R) (g : WithConv (H →ₐ[K] K)) (h : H) :
    (diagonal K H v g).ofConv h = algebraMap K (v.adicCompletion K) (g.ofConv h) := by
  simp [diagonal]

/-- The diagonal map into `LocalPoints K H v` is injective. -/
theorem diagonal_injective (v : HeightOneSpectrum R) : Function.Injective (diagonal K H v) :=
  AlgHom.mapValue_injective (algebraMap K (v.adicCompletion K)).injective

end LocalPoints

namespace FiniteAdelicPoints

section Semiring

variable (R K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Semiring H] [Algebra K H]

/-- When `R` is a field, `HeightOneSpectrum R` is empty and `FiniteAdelicPoints R K H` is a
subsingleton, showing `¬ IsField R` in `FiniteAdelicPoints.diagonal_injective_of_not_isField` is
sharp. -/
theorem subsingleton_of_isField (hR : IsField R) : Subsingleton (FiniteAdelicPoints R K H) :=
  have := FiniteAdeleRing.subsingleton_of_isField K hR
  ⟨fun _ _ ↦ WithConv.ext <| AlgHom.ext fun _ ↦ Subsingleton.elim _ _⟩

end Semiring

variable (R K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Semiring H] [Bialgebra K H]

/-- Diagonal homomorphism from `K`-rational points of `H` to finite-adelic points. -/
noncomputable def diagonal : WithConv (H →ₐ[K] K) →* FiniteAdelicPoints R K H :=
  AlgHom.mapValue (Algebra.ofId K (FiniteAdeleRing R K))

/-- Projection from finite-adelic points to `v`-adic points at a finite place `v`. -/
noncomputable def localProjection (v : HeightOneSpectrum R) :
    FiniteAdelicPoints R K H →* LocalPoints K H v :=
  AlgHom.mapValue (FiniteAdeleRing.proj K v).toAlgHom

variable {R K H}

/-- Evaluating a diagonal finite-adelic point applies `algebraMap K (FiniteAdeleRing R K)`. -/
@[simp]
theorem diagonal_apply_ofConv (g : WithConv (H →ₐ[K] K)) (h : H) :
    (diagonal R K H g).ofConv h = algebraMap K (FiniteAdeleRing R K) (g.ofConv h) := by
  simp [diagonal]

/-- Evaluating `localProjection` at `v` reads the `v`-component of `x.ofConv h`. -/
@[simp]
theorem localProjection_apply_ofConv (v : HeightOneSpectrum R)
    (x : FiniteAdelicPoints R K H) (h : H) :
    (localProjection R K H v x).ofConv h = x.ofConv h v := by simp [localProjection]

/-- Projection from finite-adelic points to `LocalPoints K H v` is continuous. -/
@[continuity, fun_prop]
theorem continuous_localProjection (v : HeightOneSpectrum R) :
    Continuous (localProjection R K H v) :=
  AlgHom.continuous_mapValue (FiniteAdeleRing.proj K v).continuous

/-- Projecting a diagonal finite-adelic point to `v` gives the diagonal local point at `v`. -/
@[simp]
theorem localProjection_diagonal (v : HeightOneSpectrum R) (g : WithConv (H →ₐ[K] K)) :
    localProjection R K H v (diagonal R K H g) = LocalPoints.diagonal K H v g := by
  simp only [localProjection, diagonal, LocalPoints.diagonal, ← MonoidHom.comp_apply,
    ← AlgHom.mapValue_comp, Algebra.comp_ofId]

/-- Whenever `FiniteAdeleRing R K` is nontrivial (in particular when `HeightOneSpectrum R` is
nonempty), `FiniteAdelicPoints.diagonal` is injective. -/
theorem diagonal_injective [Nontrivial (FiniteAdeleRing R K)] :
    Function.Injective (diagonal R K H) :=
  AlgHom.mapValue_injective (algebraMap K (FiniteAdeleRing R K)).injective

/-- When `R` is not a field, the diagonal map into `FiniteAdelicPoints R K H` is injective. -/
theorem diagonal_injective_of_not_isField (hR : ¬ IsField R) :
    Function.Injective (diagonal R K H) :=
  have := HeightOneSpectrum.nonempty_of_not_isField hR
  diagonal_injective

/-- Finite-adelic points of `𝔾ₐ` are isomorphic as a topological group to
`Multiplicative (FiniteAdeleRing R K)`. -/
noncomputable def gaContinuousMulEquiv (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    FiniteAdelicPoints R K (SymmetricAlgebra K K) ≃ₜ* Multiplicative (FiniteAdeleRing R K) :=
  AdditiveGroup.gaPointsContinuousMulEquiv K (FiniteAdeleRing R K)

/-- The forward map of `FiniteAdelicPoints.gaContinuousMulEquiv` is `gaPointsMulEquiv`. -/
@[simp]
theorem gaContinuousMulEquiv_apply (x : FiniteAdelicPoints R K (SymmetricAlgebra K K)) :
    gaContinuousMulEquiv R K x = AdditiveGroup.gaPointsMulEquiv x :=
  AdditiveGroup.gaPointsContinuousMulEquiv_apply x

/-- The inverse map of `FiniteAdelicPoints.gaContinuousMulEquiv` is `gaPointsMulEquiv.symm`. -/
@[simp]
theorem gaContinuousMulEquiv_symm_apply (a : Multiplicative (FiniteAdeleRing R K)) :
    (gaContinuousMulEquiv R K).symm a = (AdditiveGroup.gaPointsMulEquiv (R := K)).symm a :=
  AdditiveGroup.gaPointsContinuousMulEquiv_symm_apply a

/-- Finite-adelic points of `𝔾ₘ` are isomorphic as a topological group to
`(FiniteAdeleRing R K)ˣ`. -/
noncomputable def gmContinuousMulEquiv (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    FiniteAdelicPoints R K K[T;T⁻¹] ≃ₜ* (FiniteAdeleRing R K)ˣ :=
  MultiplicativeGroup.pointsContinuousMulEquiv K (FiniteAdeleRing R K)

/-- The forward map of `FiniteAdelicPoints.gmContinuousMulEquiv` is
`MultiplicativeGroup.pointsMulEquiv`. -/
@[simp]
theorem gmContinuousMulEquiv_apply (x : FiniteAdelicPoints R K K[T;T⁻¹]) :
    gmContinuousMulEquiv R K x = MultiplicativeGroup.pointsMulEquiv x :=
  MultiplicativeGroup.pointsContinuousMulEquiv_apply x

/-- The inverse map of `FiniteAdelicPoints.gmContinuousMulEquiv` is
`MultiplicativeGroup.pointsMulEquiv.symm`. -/
@[simp]
theorem gmContinuousMulEquiv_symm_apply (u : (FiniteAdeleRing R K)ˣ) :
    (gmContinuousMulEquiv R K).symm u = (MultiplicativeGroup.pointsMulEquiv (R := K)).symm u :=
  MultiplicativeGroup.pointsContinuousMulEquiv_symm_apply u

end FiniteAdelicPoints

namespace AdelicPoints

variable (R K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Semiring H] [Bialgebra K H]

/-- Diagonal homomorphism from `K`-rational points of `H` into `AdelicPoints R K H`. -/
noncomputable def diagonal : WithConv (H →ₐ[K] K) →* AdelicPoints R K H :=
  AlgHom.mapValue (Algebra.ofId K (NumberField.AdeleRing R K))

/-- Projection from `AdelicPoints R K H` onto `InfinitePoints K H`. -/
noncomputable def infiniteProjection : AdelicPoints R K H →* InfinitePoints K H :=
  AlgHom.mapValue (AlgHom.fst K (NumberField.InfiniteAdeleRing K) (FiniteAdeleRing R K))

/-- Projection from `AdelicPoints R K H` onto `FiniteAdelicPoints R K H`. -/
noncomputable def finiteProjection : AdelicPoints R K H →* FiniteAdelicPoints R K H :=
  AlgHom.mapValue (AlgHom.snd K (NumberField.InfiniteAdeleRing K) (FiniteAdeleRing R K))

/-- Projection from `AdelicPoints R K H` to `v`-adic points at a finite place `v`. -/
noncomputable def localProjection (v : HeightOneSpectrum R) :
    AdelicPoints R K H →* LocalPoints K H v :=
  (FiniteAdelicPoints.localProjection R K H v).comp (finiteProjection R K H)

/-- Projection from `AdelicPoints R K H` to `w`-adic points at an infinite place `w`. -/
noncomputable def infiniteLocalProjection (w : NumberField.InfinitePlace K) :
    AdelicPoints R K H →* InfiniteLocalPoints K H w :=
  (InfinitePoints.localProjection K H w).comp (infiniteProjection R K H)

/-- Infinite-finite splitting `G(𝔸[R, K]) ≃ₜ* G(K_∞) × G(𝔸ᶠ[R, K])` of `AdelicPoints R K H`. -/
noncomputable def splittingContinuousMulEquiv :
    AdelicPoints R K H ≃ₜ* InfinitePoints K H × FiniteAdelicPoints R K H :=
  prodPointsContinuousMulEquiv K H (NumberField.InfiniteAdeleRing K) (FiniteAdeleRing R K)

/-- Inclusion of `InfinitePoints K H` into `AdelicPoints R K H` as `x ↦ (x, 1)`. -/
noncomputable def infiniteEmbed : InfinitePoints K H →* AdelicPoints R K H :=
  (splittingContinuousMulEquiv R K H).symm.toMonoidHom.comp (MonoidHom.inl _ _)

/-- Inclusion of `FiniteAdelicPoints R K H` into `AdelicPoints R K H` as `x ↦ (1, x)`. -/
noncomputable def finiteEmbed : FiniteAdelicPoints R K H →* AdelicPoints R K H :=
  (splittingContinuousMulEquiv R K H).symm.toMonoidHom.comp (MonoidHom.inr _ _)

variable {R K H}

/-- Evaluating a diagonal adelic point applies `algebraMap K (AdeleRing R K)`. -/
@[simp]
theorem diagonal_apply_ofConv (g : WithConv (H →ₐ[K] K)) (h : H) :
    (diagonal R K H g).ofConv h = algebraMap K (NumberField.AdeleRing R K) (g.ofConv h) := by
  simp [diagonal]

/-- Whenever `AdeleRing R K` is nontrivial (in particular over any number field, or whenever `R` is
not a field), the diagonal map into `AdelicPoints R K H` is injective. -/
theorem diagonal_injective [Nontrivial (NumberField.AdeleRing R K)] :
    Function.Injective (diagonal R K H) :=
  AlgHom.mapValue_injective (algebraMap K (NumberField.AdeleRing R K)).injective

/-- Whenever `R` is not a field, the diagonal map into `AdelicPoints R K H` is injective. -/
theorem diagonal_injective_of_not_isField (hR : ¬ IsField R) :
    Function.Injective (diagonal R K H) :=
  have := HeightOneSpectrum.nonempty_of_not_isField hR
  diagonal_injective

/-- `infiniteProjection` is continuous. -/
@[continuity, fun_prop]
theorem continuous_infiniteProjection : Continuous (infiniteProjection R K H) :=
  AlgHom.continuous_mapValue continuous_fst

/-- `finiteProjection` is continuous. -/
@[continuity, fun_prop]
theorem continuous_finiteProjection : Continuous (finiteProjection R K H) :=
  AlgHom.continuous_mapValue continuous_snd

/-- `localProjection` to a finite place is continuous. -/
@[continuity, fun_prop]
theorem continuous_localProjection (v : HeightOneSpectrum R) :
    Continuous (localProjection R K H v) :=
  (FiniteAdelicPoints.continuous_localProjection v).comp continuous_finiteProjection

/-- `infiniteLocalProjection` to an infinite place is continuous. -/
@[continuity, fun_prop]
theorem continuous_infiniteLocalProjection (w : NumberField.InfinitePlace K) :
    Continuous (infiniteLocalProjection R K H w) :=
  (InfinitePoints.continuous_localProjection w).comp continuous_infiniteProjection

/-- The first component of `splittingContinuousMulEquiv` is `infiniteProjection`. -/
@[simp]
theorem splittingContinuousMulEquiv_fst (x : AdelicPoints R K H) :
    (splittingContinuousMulEquiv R K H x).1 = infiniteProjection R K H x := by
  rw [splittingContinuousMulEquiv, infiniteProjection]
  exact (congrArg Prod.fst (prodPointsContinuousMulEquiv_apply x)).trans
    (AlgHom.prodPointsMulEquiv_apply_fst x)

/-- The second component of `splittingContinuousMulEquiv` is `finiteProjection`. -/
@[simp]
theorem splittingContinuousMulEquiv_snd (x : AdelicPoints R K H) :
    (splittingContinuousMulEquiv R K H x).2 = finiteProjection R K H x := by
  rw [splittingContinuousMulEquiv, finiteProjection]
  exact (congrArg Prod.snd (prodPointsContinuousMulEquiv_apply x)).trans
    (AlgHom.prodPointsMulEquiv_apply_snd x)

/-- Evaluating `(splittingContinuousMulEquiv R K H).symm p` at `h : H` pairs its infinite and
finite factor evaluations. -/
@[simp]
theorem splittingContinuousMulEquiv_symm_apply_ofConv
    (p : InfinitePoints K H × FiniteAdelicPoints R K H) (h : H) :
    ((splittingContinuousMulEquiv R K H).symm p).ofConv h = (p.1.ofConv h, p.2.ofConv h) := by
  rw [splittingContinuousMulEquiv]
  exact (congrArg (fun q ↦ q.ofConv h) (prodPointsContinuousMulEquiv_symm_apply p)).trans
    (AlgHom.prodPointsMulEquiv_symm_apply_ofConv p h)

/-- Projecting a diagonal adelic point onto the infinite factor gives `InfinitePoints.diagonal`. -/
@[simp]
theorem infiniteProjection_diagonal (g : WithConv (H →ₐ[K] K)) :
    infiniteProjection R K H (diagonal R K H g) = InfinitePoints.diagonal K H g := by
  ext h; simp [infiniteProjection]

/-- Projecting a diagonal adelic point onto the finite factor gives
`FiniteAdelicPoints.diagonal`. -/
@[simp]
theorem finiteProjection_diagonal (g : WithConv (H →ₐ[K] K)) :
    finiteProjection R K H (diagonal R K H g) = FiniteAdelicPoints.diagonal R K H g := by
  ext h; simp [finiteProjection]

/-- Projecting a diagonal adelic point to a finite place `v` gives `LocalPoints.diagonal`. -/
@[simp]
theorem localProjection_diagonal (v : HeightOneSpectrum R) (g : WithConv (H →ₐ[K] K)) :
    localProjection R K H v (diagonal R K H g) = LocalPoints.diagonal K H v g := by
  simp [localProjection]

/-- Projecting a diagonal adelic point to an infinite place `w` gives
`InfiniteLocalPoints.diagonal`. -/
@[simp]
theorem infiniteLocalProjection_diagonal (w : NumberField.InfinitePlace K)
    (g : WithConv (H →ₐ[K] K)) :
    infiniteLocalProjection R K H w (diagonal R K H g) = InfiniteLocalPoints.diagonal K H w g := by
  simp [infiniteLocalProjection]

/-- Under `splittingContinuousMulEquiv`, a diagonal adelic point splits into diagonal components. -/
@[simp]
theorem splittingContinuousMulEquiv_diagonal (g : WithConv (H →ₐ[K] K)) :
    splittingContinuousMulEquiv R K H (diagonal R K H g) =
      (InfinitePoints.diagonal K H g, FiniteAdelicPoints.diagonal R K H g) :=
  Prod.ext (by simp) (by simp)

/-- `infiniteEmbed` maps `x` to `(x, 1)` under `splittingContinuousMulEquiv`. -/
@[simp]
theorem splittingContinuousMulEquiv_infiniteEmbed (x : InfinitePoints K H) :
    splittingContinuousMulEquiv R K H (infiniteEmbed R K H x) = (x, 1) :=
  (splittingContinuousMulEquiv R K H).apply_symm_apply (x, 1)

/-- `finiteEmbed` maps `x` to `(1, x)` under `splittingContinuousMulEquiv`. -/
@[simp]
theorem splittingContinuousMulEquiv_finiteEmbed (x : FiniteAdelicPoints R K H) :
    splittingContinuousMulEquiv R K H (finiteEmbed R K H x) = (1, x) :=
  (splittingContinuousMulEquiv R K H).apply_symm_apply (1, x)

/-- `infiniteProjection` is a left inverse of `infiniteEmbed`. -/
@[simp]
theorem infiniteProjection_infiniteEmbed (x : InfinitePoints K H) :
    infiniteProjection R K H (infiniteEmbed R K H x) = x := by
  simpa only [← splittingContinuousMulEquiv_fst] using
    congrArg Prod.fst (splittingContinuousMulEquiv_infiniteEmbed x)

/-- `finiteProjection` sends `infiniteEmbed x` to `1`. -/
@[simp]
theorem finiteProjection_infiniteEmbed (x : InfinitePoints K H) :
    finiteProjection R K H (infiniteEmbed R K H x) = 1 := by
  simpa only [← splittingContinuousMulEquiv_snd] using
    congrArg Prod.snd (splittingContinuousMulEquiv_infiniteEmbed x)

/-- `infiniteProjection` sends `finiteEmbed x` to `1`. -/
@[simp]
theorem infiniteProjection_finiteEmbed (x : FiniteAdelicPoints R K H) :
    infiniteProjection R K H (finiteEmbed R K H x) = 1 := by
  simpa only [← splittingContinuousMulEquiv_fst] using
    congrArg Prod.fst (splittingContinuousMulEquiv_finiteEmbed x)

/-- `finiteProjection` is a left inverse of `finiteEmbed`. -/
@[simp]
theorem finiteProjection_finiteEmbed (x : FiniteAdelicPoints R K H) :
    finiteProjection R K H (finiteEmbed R K H x) = x := by
  simpa only [← splittingContinuousMulEquiv_snd] using
    congrArg Prod.snd (splittingContinuousMulEquiv_finiteEmbed x)

/-- Every point of `AdelicPoints R K H` factors as
`infiniteEmbed (infiniteProjection x) * finiteEmbed (finiteProjection x)`. -/
theorem infiniteEmbed_mul_finiteEmbed (x : AdelicPoints R K H) :
    infiniteEmbed R K H (infiniteProjection R K H x) *
        finiteEmbed R K H (finiteProjection R K H x) = x := by
  apply (splittingContinuousMulEquiv R K H).injective; simp [map_mul, Prod.ext_iff]

/-- `infiniteEmbed` is continuous. -/
@[continuity, fun_prop]
theorem continuous_infiniteEmbed : Continuous (infiniteEmbed R K H) :=
  (splittingContinuousMulEquiv R K H).symm.continuous.comp (continuous_id.prodMk continuous_const)

/-- `finiteEmbed` is continuous. -/
@[continuity, fun_prop]
theorem continuous_finiteEmbed : Continuous (finiteEmbed R K H) :=
  (splittingContinuousMulEquiv R K H).symm.continuous.comp (continuous_const.prodMk continuous_id)

/-- `infiniteEmbed` is a closed embedding into `AdelicPoints R K H`. -/
theorem isClosedEmbedding_infiniteEmbed : IsClosedEmbedding (infiniteEmbed R K H) :=
  Function.LeftInverse.isClosedEmbedding infiniteProjection_infiniteEmbed
    continuous_infiniteProjection continuous_infiniteEmbed

/-- `finiteEmbed` is a closed embedding into `AdelicPoints R K H`. -/
theorem isClosedEmbedding_finiteEmbed : IsClosedEmbedding (finiteEmbed R K H) :=
  Function.LeftInverse.isClosedEmbedding finiteProjection_finiteEmbed
    continuous_finiteProjection continuous_finiteEmbed

/-- `𝔸[R, K]`-valued points of `𝔾ₐ` are isomorphic as a topological group to
`Multiplicative (AdeleRing R K)`. -/
noncomputable def gaContinuousMulEquiv (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    AdelicPoints R K (SymmetricAlgebra K K) ≃ₜ* Multiplicative (NumberField.AdeleRing R K) :=
  AdditiveGroup.gaPointsContinuousMulEquiv K (NumberField.AdeleRing R K)

/-- The forward map of `AdelicPoints.gaContinuousMulEquiv` is `gaPointsMulEquiv`. -/
@[simp]
theorem gaContinuousMulEquiv_apply (x : AdelicPoints R K (SymmetricAlgebra K K)) :
    gaContinuousMulEquiv R K x = AdditiveGroup.gaPointsMulEquiv x :=
  AdditiveGroup.gaPointsContinuousMulEquiv_apply x

/-- The inverse map of `AdelicPoints.gaContinuousMulEquiv` is `gaPointsMulEquiv.symm`. -/
@[simp]
theorem gaContinuousMulEquiv_symm_apply (a : Multiplicative (NumberField.AdeleRing R K)) :
    (gaContinuousMulEquiv R K).symm a = (AdditiveGroup.gaPointsMulEquiv (R := K)).symm a :=
  AdditiveGroup.gaPointsContinuousMulEquiv_symm_apply a

/-- `𝔸[R, K]`-valued points of `𝔾ₘ` are isomorphic as a topological group to `IdeleGroup R K`
(Conrad 2012, Example 3.1). -/
noncomputable def gmContinuousMulEquiv (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    AdelicPoints R K K[T;T⁻¹] ≃ₜ* NumberField.IdeleGroup R K :=
  MultiplicativeGroup.pointsContinuousMulEquiv K (NumberField.AdeleRing R K)

/-- The forward map of `AdelicPoints.gmContinuousMulEquiv` is
`MultiplicativeGroup.pointsMulEquiv`. -/
@[simp]
theorem gmContinuousMulEquiv_apply (x : AdelicPoints R K K[T;T⁻¹]) :
    gmContinuousMulEquiv R K x = MultiplicativeGroup.pointsMulEquiv x :=
  MultiplicativeGroup.pointsContinuousMulEquiv_apply x

/-- The inverse map of `AdelicPoints.gmContinuousMulEquiv` is
`MultiplicativeGroup.pointsMulEquiv.symm`. -/
@[simp]
theorem gmContinuousMulEquiv_symm_apply (u : NumberField.IdeleGroup R K) :
    (gmContinuousMulEquiv R K).symm u = (MultiplicativeGroup.pointsMulEquiv (R := K)).symm u :=
  MultiplicativeGroup.pointsContinuousMulEquiv_symm_apply u

end AdelicPoints

end TauCeti

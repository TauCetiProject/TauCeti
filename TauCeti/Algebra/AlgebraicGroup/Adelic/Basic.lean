/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Topology
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Topology
public import TauCeti.Algebra.AlgebraicGroup.Trivial
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocallyCompact
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
public import TauCeti.Topology.Algebra.PointTopology.Prod
public import TauCeti.Topology.Algebra.PointTopology.Separation

/-!
# Adelic, finite-adelic, and local point groups of an affine group

Let `R` be a Dedekind domain with fraction field `K`, and let `H` be the coordinate bialgebra (or
Hopf algebra) of an affine monoid (or group) scheme `G = Spec H` over `K`. Evaluating the functor
of points `A ↦ WithConv (H →ₐ[K] A)` on `NumberField.AdeleRing R K`,
`IsDedekindDomain.FiniteAdeleRing R K`, `NumberField.InfiniteAdeleRing K`, and the completions
`v.adicCompletion K` and `w.Completion` defines the global adelic, finite-adelic, infinite, and
local point spaces of `G`, each carrying the evaluation point topology of
`TauCeti.Topology.Algebra.PointTopology.Basic`.

Following Conrad (*Weil and Grothendieck approaches to adelic points*, Proposition 2.1 and §3),
this intrinsic functor-of-points definition requires no choice of affine embedding `G ↪ GL_n` and
no integral model over `R`:

* when `H` is a Hopf algebra over `K`, all five point spaces are Hausdorff topological groups, and
  when `H` is of finite type over `K` the finite-adelic points (assuming finite residue fields of
  `R`) and infinite points (assuming `[NumberField K]`) are locally compact;
* the product decomposition `AdeleRing R K = InfiniteAdeleRing K × FiniteAdeleRing R K` induces a
  topological multiplicative equivalence
  `AdelicPoints.splittingContinuousMulEquiv : AdelicPoints R K H ≃ₜ* InfinitePoints K H ×
  FiniteAdelicPoints R K H`, together with closed factor embeddings `infiniteEmbed` and
  `finiteEmbed`;
* `K`-rational points map diagonally into each point space via `Algebra.ofId`, compatibly with all
  place and factor projections, and injectively into `FiniteAdelicPoints R K H` whenever `R` is not
  a field (whereas when `R` is a field, `HeightOneSpectrum R` is empty and
  `FiniteAdelicPoints R K H` is trivial);
* for `𝔾ₐ = Spec (SymmetricAlgebra K K)` and `𝔾ₘ = Spec K[T;T⁻¹]`, the adelic points recover
  `Multiplicative (AdeleRing R K)` and `IdeleGroup R K`.

## Main declarations

* `TauCeti.AdelicPoints`, `TauCeti.FiniteAdelicPoints`, `TauCeti.InfinitePoints`,
  `TauCeti.LocalPoints`, `TauCeti.InfiniteLocalPoints`: the global and local point spaces.
* `TauCeti.InfinitePoints.piContinuousMulEquiv` and
  `TauCeti.AdelicPoints.splittingContinuousMulEquiv`: the archimedean product decomposition
  `G(K∞) ≃ₜ* ∏_{w ∣ ∞} G(K_w)` and the splitting `G(𝔸) ≃ₜ* G(K∞) × G(𝔸ᶠ)`, with factor inclusions
  `infiniteEmbed` and `finiteEmbed`.
* `TauCeti.AdelicPoints.diagonal`, `TauCeti.FiniteAdelicPoints.diagonal`,
  `TauCeti.InfinitePoints.diagonal`, `TauCeti.LocalPoints.diagonal`,
  `TauCeti.InfiniteLocalPoints.diagonal`: diagonal embeddings of `K`-rational points, with
  injectivity criteria and projection compatibilities.
* `TauCeti.AdelicPoints.gaContinuousMulEquiv` and `TauCeti.AdelicPoints.gmContinuousMulEquiv`:
  adelic points of `𝔾ₐ` and `𝔾ₘ` as `Multiplicative (AdeleRing R K)` and `IdeleGroup R K`.

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

/-! ### Point space abbreviations -/

/-- The points of `Spec H` at an archimedean place `w` of `K`, equipped with the convolution
operations and the evaluation point topology. -/
abbrev InfiniteLocalPoints (K H : Type*) [Field K] [Semiring H] [Algebra K H]
    (w : NumberField.InfinitePlace K) :=
  WithConv (H →ₐ[K] w.Completion)

/-- The points of `Spec H` over the infinite adele ring `K∞ = ∏_{w ∣ ∞} K_w`, equipped with the
convolution operations and the evaluation point topology. -/
abbrev InfinitePoints (K H : Type*) [Field K] [Semiring H] [Algebra K H] :=
  WithConv (H →ₐ[K] NumberField.InfiniteAdeleRing K)

/-- The points of `Spec H` at a finite place `v` of a Dedekind domain `R` with fraction field `K`,
valued in the adic completion `v.adicCompletion K`. -/
abbrev LocalPoints {R : Type*} (K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Semiring H] [Algebra K H]
    (v : HeightOneSpectrum R) :=
  WithConv (H →ₐ[K] v.adicCompletion K)

/-- The finite-adelic points `G(𝔸ᶠ)` of `Spec H`, valued in `FiniteAdeleRing R K` with the
evaluation point topology. -/
abbrev FiniteAdelicPoints (R K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Semiring H] [Algebra K H] :=
  WithConv (H →ₐ[K] FiniteAdeleRing R K)

/-- The adelic points `G(𝔸)` of `Spec H`, valued in `NumberField.AdeleRing R K` with the
evaluation point topology. -/
abbrev AdelicPoints (R K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Semiring H] [Algebra K H] :=
  WithConv (H →ₐ[K] NumberField.AdeleRing R K)

/-! ### Archimedean local and infinite-adelic points -/

namespace InfiniteLocalPoints

variable (K H : Type*) [Field K] [Semiring H] [Bialgebra K H]

/-- The diagonal homomorphism from `K`-rational points of `H` to `w`-adic points at an infinite
place `w`. -/
noncomputable def diagonal (w : NumberField.InfinitePlace K) :
    WithConv (H →ₐ[K] K) →* InfiniteLocalPoints K H w :=
  AlgHom.mapValue (Algebra.ofId K w.Completion)

variable {K H}

/-- Evaluating a diagonal archimedean local point applies `algebraMap K w.Completion`. -/
@[simp]
theorem diagonal_apply_ofConv (w : NumberField.InfinitePlace K)
    (g : WithConv (H →ₐ[K] K)) (h : H) :
    (diagonal K H w g).ofConv h = algebraMap K w.Completion (g.ofConv h) := by
  simp [diagonal]

/-- The diagonal map into `InfiniteLocalPoints K H w` is injective. -/
theorem diagonal_injective (w : NumberField.InfinitePlace K) :
    Function.Injective (diagonal K H w) :=
  AlgHom.mapValue_injective (algebraMap K w.Completion).injective

end InfiniteLocalPoints

namespace InfinitePoints

variable (K H : Type*) [Field K] [Semiring H] [Bialgebra K H]

/-- The diagonal homomorphism from `K`-rational points of `H` to infinite-adelic points. -/
noncomputable def diagonal : WithConv (H →ₐ[K] K) →* InfinitePoints K H :=
  AlgHom.mapValue (Algebra.ofId K (NumberField.InfiniteAdeleRing K))

/-- Projection from infinite-adelic points to the completion at an archimedean place `w`. -/
noncomputable def localProjection (w : NumberField.InfinitePlace K) :
    InfinitePoints K H →* InfiniteLocalPoints K H w :=
  AlgHom.mapValue (Pi.evalAlgHom K (fun w : NumberField.InfinitePlace K ↦ w.Completion) w)

/-- **Product decomposition of archimedean adelic points.** Since `InfiniteAdeleRing K =
∏_{w ∣ ∞} w.Completion`, `InfinitePoints K H` is isomorphic as a topological monoid (and hence as
a topological group when `H` is a Hopf algebra) to `∏_{w ∣ ∞} InfiniteLocalPoints K H w`. -/
noncomputable def piContinuousMulEquiv :
    InfinitePoints K H ≃ₜ* ∀ w : NumberField.InfinitePlace K, InfiniteLocalPoints K H w :=
  piPointsContinuousMulEquiv K H (fun w : NumberField.InfinitePlace K ↦ w.Completion)

variable {K H}

/-- Evaluating a diagonal infinite-adelic point applies `algebraMap K (InfiniteAdeleRing K)`. -/
@[simp]
theorem diagonal_apply_ofConv (g : WithConv (H →ₐ[K] K)) (h : H) :
    (diagonal K H g).ofConv h = algebraMap K (NumberField.InfiniteAdeleRing K) (g.ofConv h) := by
  simp [diagonal]

/-- Over a number field, the diagonal map into `InfinitePoints K H` is injective because `K` has
at least one infinite place. -/
theorem diagonal_injective [NumberField K] : Function.Injective (diagonal K H) :=
  AlgHom.mapValue_injective (algebraMap K (NumberField.InfiniteAdeleRing K)).injective

/-- Evaluating `localProjection` at `w` reads the `w`-coordinate of an infinite-adelic point. -/
@[simp]
theorem localProjection_apply_ofConv (w : NumberField.InfinitePlace K)
    (x : InfinitePoints K H) (h : H) :
    (localProjection K H w x).ofConv h = x.ofConv h w := by
  simp only [localProjection, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
  rfl

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
  delta piContinuousMulEquiv localProjection
  exact piPointsContinuousMulEquiv_apply x w

end InfinitePoints

/-! ### Nonarchimedean local and finite-adelic points -/

namespace LocalPoints

variable {R : Type*} (K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Semiring H] [Bialgebra K H]

/-- The diagonal homomorphism from `K`-rational points of `H` to `v`-adic points at a finite
place `v`. -/
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
theorem diagonal_injective (v : HeightOneSpectrum R) :
    Function.Injective (diagonal K H v) :=
  AlgHom.mapValue_injective (algebraMap K (v.adicCompletion K)).injective

end LocalPoints

namespace FiniteAdelicPoints

section Semiring

variable (R K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Semiring H] [Algebra K H]

/-- When the Dedekind domain `R` is itself a field, `HeightOneSpectrum R` is empty, so
`FiniteAdeleRing R K` is the zero ring and `FiniteAdelicPoints R K H` is a subsingleton. This
shows that the hypothesis `¬ IsField R` in `FiniteAdelicPoints.diagonal_injective` cannot be
dropped. -/
theorem subsingleton_of_isField (hR : IsField R) : Subsingleton (FiniteAdelicPoints R K H) := by
  have hempty : IsEmpty (HeightOneSpectrum R) := ⟨fun v ↦ by
    obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    obtain ⟨y, hy⟩ := hR.mul_inv_cancel hx0
    exact v.isPrime.ne_top (v.asIdeal.eq_top_iff_one.mpr (hy ▸ v.asIdeal.mul_mem_right y hxv))⟩
  have hsub : Subsingleton (FiniteAdeleRing R K) :=
    ⟨fun a b ↦ FiniteAdeleRing.ext K fun v ↦ hempty.elim v⟩
  exact ⟨fun x y ↦ WithConv.ext <| AlgHom.ext fun _ ↦ Subsingleton.elim _ _⟩

end Semiring

variable (R K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Semiring H] [Bialgebra K H]

/-- The diagonal homomorphism from `K`-rational points of `H` to finite-adelic points. -/
noncomputable def diagonal : WithConv (H →ₐ[K] K) →* FiniteAdelicPoints R K H :=
  AlgHom.mapValue (Algebra.ofId K (FiniteAdeleRing R K))

/-- Projection from finite-adelic points to the `v`-adic points at a finite place `v`. -/
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
    (localProjection R K H v x).ofConv h = x.ofConv h v := by
  simp [localProjection]

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

/-- When `R` has at least one height-one prime, the diagonal map into `FiniteAdelicPoints R K H`
is injective. -/
theorem diagonal_injective_of_nonempty [Nonempty (HeightOneSpectrum R)] :
    Function.Injective (diagonal R K H) := by
  obtain ⟨v⟩ := ‹Nonempty (HeightOneSpectrum R)›
  exact Function.Injective.of_comp (f := localProjection R K H v) fun x y hxy ↦
    LocalPoints.diagonal_injective v (by simpa using hxy)

/-- When the Dedekind domain `R` is not a field (for instance `R = 𝓞 K` for a number field or
function field, or `R = ℤ`), the diagonal map into `FiniteAdelicPoints R K H` is injective. -/
theorem diagonal_injective (hR : ¬ IsField R) :
    Function.Injective (diagonal R K H) := by
  have : Nontrivial R := ⟨⟨(0 : R), 1, fun h ↦ zero_ne_one
    ((map_zero (algebraMap R K)).symm.trans ((congrArg (algebraMap R K) h).trans (map_one _)))⟩⟩
  obtain ⟨m⟩ := (inferInstance : Nonempty (MaximalSpectrum R))
  have : Nonempty (HeightOneSpectrum R) :=
    ⟨(HeightOneSpectrum.equivMaximalSpectrum hR).symm m⟩
  exact diagonal_injective_of_nonempty

/-- The finite-adelic points of `𝔾ₐ = Spec (SymmetricAlgebra K K)` are isomorphic as a topological
group to `Multiplicative (FiniteAdeleRing R K)`. -/
noncomputable def gaContinuousMulEquiv (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    FiniteAdelicPoints R K (SymmetricAlgebra K K) ≃ₜ* Multiplicative (FiniteAdeleRing R K) :=
  AdditiveGroup.gaPointsContinuousMulEquiv K (FiniteAdeleRing R K)

/-- The finite-adelic points of `𝔾ₘ = Spec K[T;T⁻¹]` are isomorphic as a topological group to the
unit group `(FiniteAdeleRing R K)ˣ` of finite ideles. -/
noncomputable def gmContinuousMulEquiv (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    FiniteAdelicPoints R K K[T;T⁻¹] ≃ₜ* (FiniteAdeleRing R K)ˣ :=
  MultiplicativeGroup.pointsContinuousMulEquiv K (FiniteAdeleRing R K)

end FiniteAdelicPoints

/-! ### Global adelic points and the infinite-finite splitting -/

namespace AdelicPoints

variable (R K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Semiring H] [Bialgebra K H]

/-- The diagonal homomorphism from `K`-rational points of `H` to global adelic points. -/
noncomputable def diagonal : WithConv (H →ₐ[K] K) →* AdelicPoints R K H :=
  AlgHom.mapValue (Algebra.ofId K (NumberField.AdeleRing R K))

/-- Projection from global adelic points to infinite-adelic points. -/
noncomputable def infiniteProjection : AdelicPoints R K H →* InfinitePoints K H :=
  AlgHom.mapValue (AlgHom.fst K (NumberField.InfiniteAdeleRing K) (FiniteAdeleRing R K))

/-- Projection from global adelic points to finite-adelic points. -/
noncomputable def finiteProjection : AdelicPoints R K H →* FiniteAdelicPoints R K H :=
  AlgHom.mapValue (AlgHom.snd K (NumberField.InfiniteAdeleRing K) (FiniteAdeleRing R K))

/-- Projection from global adelic points to `v`-adic points at a finite place `v`. -/
noncomputable def localProjection (v : HeightOneSpectrum R) :
    AdelicPoints R K H →* LocalPoints K H v :=
  (FiniteAdelicPoints.localProjection R K H v).comp (finiteProjection R K H)

/-- Projection from global adelic points to `w`-adic points at an infinite place `w`. -/
noncomputable def infiniteLocalProjection (w : NumberField.InfinitePlace K) :
    AdelicPoints R K H →* InfiniteLocalPoints K H w :=
  (InfinitePoints.localProjection K H w).comp (infiniteProjection R K H)

/-- **Infinite-finite splitting of adelic points.** Since `AdeleRing R K = InfiniteAdeleRing K ×
FiniteAdeleRing R K` as a topological `K`-algebra, the adelic points split as the topological
product of the infinite-adelic points and the finite-adelic points. -/
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

/-- Over a number field, the diagonal map into `AdelicPoints R K H` is injective. -/
theorem diagonal_injective [NumberField K] : Function.Injective (diagonal R K H) :=
  AlgHom.mapValue_injective (NumberField.AdeleRing.algebraMap_injective R K)

/-- Whenever `R` is not a field, the diagonal map into `AdelicPoints R K H` is injective (even
without `[NumberField K]`, via the finite-adelic projection). -/
theorem diagonal_injective_of_not_isField (hR : ¬ IsField R) :
    Function.Injective (diagonal R K H) := fun _ _ h ↦
  FiniteAdelicPoints.diagonal_injective (H := H) hR <|
    WithConv.ext <| AlgHom.ext fun x ↦ by
      simpa using congrArg (fun p ↦ (p.ofConv x).2) h

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
  delta splittingContinuousMulEquiv infiniteProjection
  exact (congrArg Prod.fst (prodPointsContinuousMulEquiv_apply x)).trans
    (AlgHom.prodPointsMulEquiv_apply_fst x)

/-- The second component of `splittingContinuousMulEquiv` is `finiteProjection`. -/
@[simp]
theorem splittingContinuousMulEquiv_snd (x : AdelicPoints R K H) :
    (splittingContinuousMulEquiv R K H x).2 = finiteProjection R K H x := by
  delta splittingContinuousMulEquiv finiteProjection
  exact (congrArg Prod.snd (prodPointsContinuousMulEquiv_apply x)).trans
    (AlgHom.prodPointsMulEquiv_apply_snd x)

/-- Projecting a diagonal adelic point onto the infinite factor gives the infinite diagonal
point. -/
@[simp]
theorem infiniteProjection_diagonal (g : WithConv (H →ₐ[K] K)) :
    infiniteProjection R K H (diagonal R K H g) = InfinitePoints.diagonal K H g := by
  ext h
  simp [infiniteProjection]

/-- Projecting a diagonal adelic point onto the finite factor gives the finite-adelic diagonal
point. -/
@[simp]
theorem finiteProjection_diagonal (g : WithConv (H →ₐ[K] K)) :
    finiteProjection R K H (diagonal R K H g) = FiniteAdelicPoints.diagonal R K H g := by
  ext h
  simp [finiteProjection]

/-- Projecting a diagonal adelic point to a finite place `v` gives the local diagonal point. -/
@[simp]
theorem localProjection_diagonal (v : HeightOneSpectrum R) (g : WithConv (H →ₐ[K] K)) :
    localProjection R K H v (diagonal R K H g) = LocalPoints.diagonal K H v g := by
  simp [localProjection]

/-- Projecting a diagonal adelic point to an infinite place `w` gives the local diagonal point. -/
@[simp]
theorem infiniteLocalProjection_diagonal (w : NumberField.InfinitePlace K)
    (g : WithConv (H →ₐ[K] K)) :
    infiniteLocalProjection R K H w (diagonal R K H g) = InfiniteLocalPoints.diagonal K H w g := by
  simp [infiniteLocalProjection]

/-- Under `splittingContinuousMulEquiv`, a diagonal adelic point splits into the pair of infinite
and finite-adelic diagonal points. -/
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

/-- Every adelic point factors uniquely as the product of its infinite component and its finite
component embedded via `infiniteEmbed` and `finiteEmbed`. -/
theorem infiniteEmbed_mul_finiteEmbed (x : AdelicPoints R K H) :
    infiniteEmbed R K H (infiniteProjection R K H x) *
        finiteEmbed R K H (finiteProjection R K H x) = x := by
  apply (splittingContinuousMulEquiv R K H).injective
  simp [map_mul, Prod.ext_iff]

/-- `infiniteEmbed` is continuous. -/
@[continuity, fun_prop]
theorem continuous_infiniteEmbed : Continuous (infiniteEmbed R K H) :=
  (splittingContinuousMulEquiv R K H).symm.continuous.comp (continuous_id.prodMk continuous_const)

/-- `finiteEmbed` is continuous. -/
@[continuity, fun_prop]
theorem continuous_finiteEmbed : Continuous (finiteEmbed R K H) :=
  (splittingContinuousMulEquiv R K H).symm.continuous.comp (continuous_const.prodMk continuous_id)

/-- `infiniteEmbed` is a closed embedding of `InfinitePoints K H` into `AdelicPoints R K H`. -/
theorem isClosedEmbedding_infiniteEmbed : IsClosedEmbedding (infiniteEmbed R K H) :=
  Function.LeftInverse.isClosedEmbedding infiniteProjection_infiniteEmbed
    continuous_infiniteProjection continuous_infiniteEmbed

/-- `finiteEmbed` is a closed embedding of `FiniteAdelicPoints R K H` into `AdelicPoints R K H`. -/
theorem isClosedEmbedding_finiteEmbed : IsClosedEmbedding (finiteEmbed R K H) :=
  Function.LeftInverse.isClosedEmbedding finiteProjection_finiteEmbed
    continuous_finiteProjection continuous_finiteEmbed

/-- The adelic points of `𝔾ₐ = Spec (SymmetricAlgebra K K)` are isomorphic as a topological group
to `Multiplicative (AdeleRing R K)`. -/
noncomputable def gaContinuousMulEquiv (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    AdelicPoints R K (SymmetricAlgebra K K) ≃ₜ* Multiplicative (NumberField.AdeleRing R K) :=
  AdditiveGroup.gaPointsContinuousMulEquiv K (NumberField.AdeleRing R K)

/-- The adelic points of `𝔾ₘ = Spec K[T;T⁻¹]` are isomorphic as a topological group to the idele
group `NumberField.IdeleGroup R K = (AdeleRing R K)ˣ` (Conrad 2012, Example 3.1). -/
noncomputable def gmContinuousMulEquiv (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    AdelicPoints R K K[T;T⁻¹] ≃ₜ* NumberField.IdeleGroup R K :=
  MultiplicativeGroup.pointsContinuousMulEquiv K (NumberField.AdeleRing R K)

end AdelicPoints

end TauCeti

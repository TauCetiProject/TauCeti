/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
public import TauCeti.Topology.Algebra.PointTopology.Prod

/-!
# Adelic points of an affine group scheme

Let `R` be a Dedekind domain with fraction field `K`, and let `H` be a bialgebra over `K`; when `H`
is a commutative Hopf algebra it is the coordinate ring of the affine group scheme `G = Spec H`.
This file defines the groups of points of `G` over Mathlib's `AdeleRing R K = K_∞ × 𝔸_{K,f}`,
written `𝔸_K`, over its two factors and over the completions at the finite places of `R`,

* `TauCeti.AdelicPoints R K H`, the points `G(𝔸_K) = WithConv (H →ₐ[K] 𝔸_K)`;
* `TauCeti.AdelicPoints.FiniteAdelicPoints R K H`, the points `G(𝔸_{K,f})` over the finite
  adeles;
* `TauCeti.AdelicPoints.InfinitePoints K H`, the points `G(K_∞)` over the infinite adeles;
* `TauCeti.AdelicPoints.LocalPoints R K H v`, the points `G(K_v)` over the completion at a finite
  place `v`,

each with the convolution product and Tau Ceti's point topology, the coarsest topology making
every evaluation `x ↦ x h` continuous. For a Hopf algebra `H` these are topological groups
(`TauCeti.PointTopology.isTopologicalGroup`). The point topology on `G(𝔸_K)` is in general not
the subspace topology of `𝔸_K` under a chosen coordinate: for the multiplicative group it is the
topology of the ideles, not that of `𝔸_K`.

When `K` is a number field and `R = 𝓞 K`, `AdeleRing R K` is the adele ring of `K` and these are
the adelic points of `G` in the usual sense. For other `R` it is not the adele ring of `K`: for a
function field `K` the factor `K_∞` is trivial, and for `R = ℤ[1/2]` the places over `2` are
missing.

The rational diagonals and the projections are changes of coefficients `AlgHom.mapValue` along
algebra maps of the coefficient rings:

* the rational diagonals `G(K) → G(𝔸_K)`, `G(K) → G(𝔸_{K,f})` and `G(K) → G(K_∞)` along the
  diagonal embeddings of `K`;
* the projections `G(𝔸_K) → G(𝔸_{K,f})` and `G(𝔸_K) → G(K_∞)` to the finite and infinite
  components;
* the projections `p_v : G(𝔸_K) → G(K_v)` to the points over the completion at a finite place
  `v`, and `p_w : G(𝔸_K) → G(K_w)` at an infinite place `w`.

The projections are continuous, and each of them carries the rational diagonal to the
corresponding rational diagonal; in particular `p_v` sends a rational point to its image in
`G(K_v)`. Finally, the splitting `𝔸_K = K_∞ × 𝔸_{K,f}` gives an isomorphism of topological groups
`G(𝔸_K) ≃ G(K_∞) × G(𝔸_{K,f})`, and through it the embedding `finiteEmbed : G(𝔸_{K,f}) → G(𝔸_K)`,
`x ↦ (1, x)`, of a finite adelic point as the adelic point with trivial infinite component.
This is an embedding of groups of points: it is not induced by a ring map `𝔸_{K,f} → 𝔸_K`, and
its infinite coordinate is the identity point, not zero.

## Main declarations

* `TauCeti.AdelicPoints`, `TauCeti.AdelicPoints.FiniteAdelicPoints`,
  `TauCeti.AdelicPoints.InfinitePoints`, `TauCeti.AdelicPoints.LocalPoints`.
* `TauCeti.AdelicPoints.diagonal`, `TauCeti.AdelicPoints.finiteDiagonal`,
  `TauCeti.AdelicPoints.infiniteDiagonal`: the rational diagonals.
* `TauCeti.AdelicPoints.diagonal_injective`: for a number field the rational diagonal into the
  adelic points is injective.
* `TauCeti.AdelicPoints.finiteProjection`, `TauCeti.AdelicPoints.infiniteProjection`: the finite
  and infinite components.
* `TauCeti.AdelicPoints.localProjection`, `TauCeti.AdelicPoints.infinitePlaceProjection`: the
  components at a finite and at an infinite place, factoring through
  `TauCeti.AdelicPoints.finiteLocalProjection` and `TauCeti.AdelicPoints.infiniteLocalProjection`.
* `TauCeti.AdelicPoints.localProjection_diagonal`,
  `TauCeti.AdelicPoints.infinitePlaceProjection_diagonal`: the local components of a rational point
  are its images in the local points.
* `TauCeti.AdelicPoints.prodContinuousMulEquiv`: `G(𝔸_K) ≃ₜ* G(K_∞) × G(𝔸_{K,f})`, with
  `TauCeti.AdelicPoints.prodContinuousMulEquiv_finiteEmbed`.
* `TauCeti.AdelicPoints.finiteEmbed`, with `TauCeti.AdelicPoints.finiteProjection_finiteEmbed`
  and `TauCeti.AdelicPoints.infiniteProjection_finiteEmbed`.
* `TauCeti.AdelicPoints.ext_iff_projection`: an adelic point is determined by its infinite and
  finite components.
* `TauCeti.AdelicPoints.exists_finiteEmbed_eq_iff`, `TauCeti.AdelicPoints.mrange_finiteEmbed`,
  `TauCeti.AdelicPoints.isEmbedding_finiteEmbed`: `finiteEmbed` is a topological embedding onto
  the adelic points with trivial infinite component.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, p. 2, and §3.
* J. Arthur, *An introduction to the trace formula*, Clay Math. Proc. 4 (2005), §2, p. 11.
-/

public section

open IsDedekindDomain NumberField WithConv

namespace TauCeti

variable (R K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Semiring H] [Bialgebra K H]

/-- The points `G(𝔸_K) = WithConv (H →ₐ[K] 𝔸_K)` of `G = Spec H` over Mathlib's
`𝔸_K = AdeleRing R K`. They are the adelic points of `G` when `K` is a number field and `R = 𝓞 K`;
for other `R`, `AdeleRing R K` is not the adele ring of `K`. They carry the convolution product and
the point topology; for a Hopf algebra `H` they form a topological group. -/
abbrev AdelicPoints := WithConv (H →ₐ[K] AdeleRing R K)

namespace AdelicPoints

/-- The points `G(𝔸_{K,f}) = WithConv (H →ₐ[K] 𝔸_{K,f})` of `G = Spec H` over the finite adele
ring `𝔸_{K,f} = FiniteAdeleRing R K`, the restricted product over the height-one primes of `R`,
with the convolution product and the point topology. They are the finite adelic points of `G` when
`K` is a number field and `R = 𝓞 K`. -/
abbrev FiniteAdelicPoints := WithConv (H →ₐ[K] FiniteAdeleRing R K)

/-- The infinite points `G(K_∞) = WithConv (H →ₐ[K] K_∞)` of `G = Spec H`, over the infinite
adele ring `K_∞ = ∏_{w | ∞} K_w`, with the convolution product and the point topology. -/
abbrev InfinitePoints := WithConv (H →ₐ[K] InfiniteAdeleRing K)

/-- The local points `G(K_v) = WithConv (H →ₐ[K] K_v)` of `G = Spec H` at the finite place `v`,
over the completion `K_v` of `K` at `v`, with the convolution product and the point topology. -/
abbrev LocalPoints (v : HeightOneSpectrum R) := WithConv (H →ₐ[K] v.adicCompletion K)

open TauCeti.PointTopology

/-! ### Rational diagonals -/

/-- The rational diagonal `G(K) → G(𝔸_K)`: a rational point composed with the diagonal embedding
`K → 𝔸_K`. -/
noncomputable def diagonal : WithConv (H →ₐ[K] K) →* AdelicPoints R K H :=
  AlgHom.mapValue (Algebra.ofId K _)

/-- The rational diagonal `G(K) → G(𝔸_{K,f})` into the finite adelic points. -/
noncomputable def finiteDiagonal : WithConv (H →ₐ[K] K) →* FiniteAdelicPoints R K H :=
  AlgHom.mapValue (Algebra.ofId K _)

/-- The rational diagonal `G(K) → G(K_∞)` into the infinite points. -/
noncomputable def infiniteDiagonal : WithConv (H →ₐ[K] K) →* InfinitePoints K H :=
  AlgHom.mapValue (Algebra.ofId K _)

/-- The rational diagonal is change of coefficients along the diagonal embedding `K → 𝔸_K`. -/
theorem diagonal_def : diagonal R K H = AlgHom.mapValue (Algebra.ofId K (AdeleRing R K)) := (rfl)

variable {R K H}

/-- The rational diagonal is post-composition with the structure map `K → 𝔸_K`. -/
theorem diagonal_eq_mapValue :
    diagonal R K H = AlgHom.mapValue (Algebra.ofId K (AdeleRing R K)) :=
  (rfl)

@[simp]
theorem diagonal_apply_apply (g : WithConv (H →ₐ[K] K)) (h : H) :
    diagonal R K H g h = algebraMap K (AdeleRing R K) (g h) := by
  simp [diagonal]

@[simp]
theorem finiteDiagonal_apply_apply (g : WithConv (H →ₐ[K] K)) (h : H) :
    finiteDiagonal R K H g h = algebraMap K (FiniteAdeleRing R K) (g h) := by
  simp [finiteDiagonal]

@[simp]
theorem infiniteDiagonal_apply_apply (g : WithConv (H →ₐ[K] K)) (h : H) :
    infiniteDiagonal K H g h = algebraMap K (InfiniteAdeleRing K) (g h) := by
  simp [infiniteDiagonal]

/-- For a number field `K`, the rational diagonal `G(K) → G(𝔸_K)` is injective, since `K` embeds
in `𝔸_K`. -/
theorem diagonal_injective [NumberField K] : Function.Injective (diagonal R K H) :=
  AlgHom.mapValue_injective (AdeleRing.algebraMap_injective R K)

/-! ### Finite and infinite components -/

variable (R K H)

/-- The finite component `G(𝔸_K) → G(𝔸_{K,f})`, along the projection `𝔸_K → 𝔸_{K,f}`. -/
noncomputable def finiteProjection : AdelicPoints R K H →* FiniteAdelicPoints R K H :=
  AlgHom.mapValue (AlgHom.snd K _ _)

/-- The infinite component `G(𝔸_K) → G(K_∞)`, along the projection `𝔸_K → K_∞`. -/
noncomputable def infiniteProjection : AdelicPoints R K H →* InfinitePoints K H :=
  AlgHom.mapValue (AlgHom.fst K _ _)

variable {R K H}

@[simp]
theorem finiteProjection_apply_apply (x : AdelicPoints R K H) (h : H) :
    finiteProjection R K H x h = (x h).2 := by
  -- `AdeleRing R K` is a type synonym of the product, so `simp` does not see `AlgHom.snd_apply`
  simp only [finiteProjection, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
  exact AlgHom.snd_apply (R := K) (A := InfiniteAdeleRing K) (B := FiniteAdeleRing R K) _

@[simp]
theorem infiniteProjection_apply_apply (x : AdelicPoints R K H) (h : H) :
    infiniteProjection R K H x h = (x h).1 := by
  -- `AdeleRing R K` is a type synonym of the product, so `simp` does not see `AlgHom.fst_apply`
  simp only [infiniteProjection, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
  exact AlgHom.fst_apply (R := K) (A := InfiniteAdeleRing K) (B := FiniteAdeleRing R K) _

@[fun_prop]
theorem continuous_finiteProjection : Continuous (finiteProjection R K H) :=
  AlgHom.continuous_mapValue continuous_snd

@[fun_prop]
theorem continuous_infiniteProjection : Continuous (infiniteProjection R K H) :=
  AlgHom.continuous_mapValue continuous_fst

/-- The finite component of the diagonal image of a rational point is its finite diagonal image. -/
@[simp]
theorem finiteProjection_diagonal (g : WithConv (H →ₐ[K] K)) :
    finiteProjection R K H (diagonal R K H g) = finiteDiagonal R K H g :=
  AlgHom.mapValue_mapValue_ofId _ g

/-- The infinite component of the diagonal image of a rational point is its infinite diagonal
image. -/
@[simp]
theorem infiniteProjection_diagonal (g : WithConv (H →ₐ[K] K)) :
    infiniteProjection R K H (diagonal R K H g) = infiniteDiagonal K H g :=
  AlgHom.mapValue_mapValue_ofId _ g

/-! ### Components at a single place -/

variable (R K H)

/-- The component `G(𝔸_{K,f}) → G(K_v)` of a finite adelic point at the finite place `v`, along the
projection `𝔸_{K,f} → K_v` onto the completion at `v`. -/
noncomputable def finiteLocalProjection (v : HeightOneSpectrum R) :
    FiniteAdelicPoints R K H →* LocalPoints R K H v :=
  AlgHom.mapValue (FiniteAdeleRing.proj K v).toAlgHom

/-- The component `p_v : G(𝔸_K) → G(K_v)` of an adelic point at the finite place `v`: the finite
component followed by `TauCeti.AdelicPoints.finiteLocalProjection`. -/
noncomputable def localProjection (v : HeightOneSpectrum R) :
    AdelicPoints R K H →* LocalPoints R K H v :=
  (finiteLocalProjection R K H v).comp (finiteProjection R K H)

/-- The component `G(K_∞) → G(K_w)` of an infinite point at the infinite place `w`, along the
projection `K_∞ → K_w` onto the completion at `w`. -/
noncomputable def infiniteLocalProjection (w : InfinitePlace K) :
    InfinitePoints K H →* WithConv (H →ₐ[K] w.Completion) :=
  AlgHom.mapValue (Pi.evalAlgHom K _ w)

/-- The component `p_w : G(𝔸_K) → G(K_w)` of an adelic point at the infinite place `w`: the
infinite component followed by `TauCeti.AdelicPoints.infiniteLocalProjection`. -/
noncomputable def infinitePlaceProjection (w : InfinitePlace K) :
    AdelicPoints R K H →* WithConv (H →ₐ[K] w.Completion) :=
  (infiniteLocalProjection K H w).comp (infiniteProjection R K H)

variable {R K H}

@[simp]
theorem finiteLocalProjection_apply_apply (v : HeightOneSpectrum R) (x : FiniteAdelicPoints R K H)
    (h : H) : finiteLocalProjection R K H v x h = x h v := by
  simp [finiteLocalProjection, FiniteAdeleRing.proj_apply]

theorem localProjection_apply (v : HeightOneSpectrum R) (x : AdelicPoints R K H) :
    localProjection R K H v x = finiteLocalProjection R K H v (finiteProjection R K H x) :=
  (rfl)

@[simp]
theorem localProjection_apply_apply (v : HeightOneSpectrum R) (x : AdelicPoints R K H) (h : H) :
    localProjection R K H v x h = (x h).2 v := by
  simp [localProjection_apply]

@[simp]
theorem infiniteLocalProjection_apply_apply (w : InfinitePlace K) (x : InfinitePoints K H)
    (h : H) : infiniteLocalProjection K H w x h = x h w := by
  -- `InfiniteAdeleRing K` is a type synonym of the product of the completions, so `simp` does not
  -- see `Pi.evalAlgHom_apply`
  simp only [infiniteLocalProjection, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
  exact Pi.evalAlgHom_apply ..

theorem infinitePlaceProjection_apply (w : InfinitePlace K) (x : AdelicPoints R K H) :
    infinitePlaceProjection R K H w x =
      infiniteLocalProjection K H w (infiniteProjection R K H x) :=
  (rfl)

@[simp]
theorem infinitePlaceProjection_apply_apply (w : InfinitePlace K) (x : AdelicPoints R K H)
    (h : H) : infinitePlaceProjection R K H w x h = (x h).1 w := by
  simp [infinitePlaceProjection_apply]

@[fun_prop]
theorem continuous_finiteLocalProjection (v : HeightOneSpectrum R) :
    Continuous (finiteLocalProjection R K H v) :=
  AlgHom.continuous_mapValue (FiniteAdeleRing.proj K v).cont

/-- The component `p_v` at a finite place is continuous. -/
@[fun_prop]
theorem continuous_localProjection (v : HeightOneSpectrum R) :
    Continuous (localProjection R K H v) :=
  (continuous_finiteLocalProjection v).comp continuous_finiteProjection

@[fun_prop]
theorem continuous_infiniteLocalProjection (w : InfinitePlace K) :
    Continuous (infiniteLocalProjection K H w) :=
  AlgHom.continuous_mapValue (continuous_apply w)

/-- The component `p_w` at an infinite place is continuous. -/
@[fun_prop]
theorem continuous_infinitePlaceProjection (w : InfinitePlace K) :
    Continuous (infinitePlaceProjection R K H w) :=
  (continuous_infiniteLocalProjection w).comp continuous_infiniteProjection

/-- The component at a finite place `v` of the finite diagonal image of a rational point is its
image in `G(K_v)`. -/
@[simp]
theorem finiteLocalProjection_finiteDiagonal (v : HeightOneSpectrum R)
    (g : WithConv (H →ₐ[K] K)) :
    finiteLocalProjection R K H v (finiteDiagonal R K H g) =
      (AlgHom.mapValue (Algebra.ofId K (v.adicCompletion K)) g : LocalPoints R K H v) :=
  AlgHom.mapValue_mapValue_ofId _ g

/-- The component `p_v` at a finite place `v` of the diagonal image of a rational point is its
image in `G(K_v)`. -/
@[simp]
theorem localProjection_diagonal (v : HeightOneSpectrum R) (g : WithConv (H →ₐ[K] K)) :
    localProjection R K H v (diagonal R K H g) =
      (AlgHom.mapValue (Algebra.ofId K (v.adicCompletion K)) g : LocalPoints R K H v) := by
  rw [localProjection_apply, finiteProjection_diagonal, finiteLocalProjection_finiteDiagonal]

/-- The component at an infinite place `w` of the infinite diagonal image of a rational point
is its image in `G(K_w)`. -/
@[simp]
theorem infiniteLocalProjection_infiniteDiagonal (w : InfinitePlace K)
    (g : WithConv (H →ₐ[K] K)) :
    infiniteLocalProjection K H w (infiniteDiagonal K H g) =
      AlgHom.mapValue (Algebra.ofId K w.Completion) g :=
  AlgHom.mapValue_mapValue_ofId _ g

/-- The component `p_w` at an infinite place `w` of the diagonal image of a rational point is its
image in `G(K_w)`. -/
@[simp]
theorem infinitePlaceProjection_diagonal (w : InfinitePlace K) (g : WithConv (H →ₐ[K] K)) :
    infinitePlaceProjection R K H w (diagonal R K H g) =
      AlgHom.mapValue (Algebra.ofId K w.Completion) g := by
  rw [infinitePlaceProjection_apply, infiniteProjection_diagonal,
    infiniteLocalProjection_infiniteDiagonal]

/-! ### The infinite and finite splitting -/

variable (R K H)

/-- The splitting `𝔸_K = K_∞ × 𝔸_{K,f}` as an isomorphism of topological groups of points
`G(𝔸_K) ≃ G(K_∞) × G(𝔸_{K,f})`, sending an adelic point to its infinite and finite
components. -/
noncomputable def prodContinuousMulEquiv :
    AdelicPoints R K H ≃ₜ* InfinitePoints K H × FiniteAdelicPoints R K H :=
  PointTopology.prodContinuousMulEquiv K H (InfiniteAdeleRing K) (FiniteAdeleRing R K)

variable {R K H}

@[simp]
theorem prodContinuousMulEquiv_apply (x : AdelicPoints R K H) :
    prodContinuousMulEquiv R K H x = (infiniteProjection R K H x, finiteProjection R K H x) := by
  rw [prodContinuousMulEquiv, PointTopology.prodContinuousMulEquiv_apply, infiniteProjection,
    finiteProjection]

/-- The adelic point with infinite component `y` and finite component `x` takes the value
`(y h, x h)` at `h`. -/
@[simp]
theorem prodContinuousMulEquiv_symm_apply_apply
    (p : InfinitePoints K H × FiniteAdelicPoints R K H) (h : H) :
    (prodContinuousMulEquiv R K H).symm p h = (p.1 h, p.2 h) := by
  rw [prodContinuousMulEquiv, PointTopology.prodContinuousMulEquiv_symm_apply_apply]

variable (R K H)

/-- The embedding `G(𝔸_{K,f}) → G(𝔸_K)`, `x ↦ (1, x)`, of a finite adelic point as the adelic point
with finite component `x` and trivial infinite component, through the splitting
`TauCeti.AdelicPoints.prodContinuousMulEquiv`. -/
noncomputable def finiteEmbed : FiniteAdelicPoints R K H →* AdelicPoints R K H :=
  (prodContinuousMulEquiv R K H).symm.toMonoidHom.comp (MonoidHom.inr _ _)

variable {R K H}

theorem finiteEmbed_apply (x : FiniteAdelicPoints R K H) :
    finiteEmbed R K H x = (prodContinuousMulEquiv R K H).symm (1, x) :=
  (rfl)

@[simp]
theorem finiteEmbed_apply_apply (x : FiniteAdelicPoints R K H) (h : H) :
    finiteEmbed R K H x h = (algebraMap K (InfiniteAdeleRing K) (Coalgebra.counit h), x h) := by
  rw [finiteEmbed_apply, prodContinuousMulEquiv_symm_apply_apply, AlgHom.convOne_apply]

/-- The splitting sends `finiteEmbed x` to `(1, x)`. -/
theorem prodContinuousMulEquiv_finiteEmbed (x : FiniteAdelicPoints R K H) :
    prodContinuousMulEquiv R K H (finiteEmbed R K H x) = (1, x) :=
  (prodContinuousMulEquiv R K H).apply_symm_apply (1, x)

/-- The finite component of `finiteEmbed x` is `x`. -/
@[simp]
theorem finiteProjection_finiteEmbed (x : FiniteAdelicPoints R K H) :
    finiteProjection R K H (finiteEmbed R K H x) = x :=
  congr_arg Prod.snd ((prodContinuousMulEquiv_apply _).symm.trans
    (prodContinuousMulEquiv_finiteEmbed x))

/-- The infinite component of `finiteEmbed x` is the identity point. -/
@[simp]
theorem infiniteProjection_finiteEmbed (x : FiniteAdelicPoints R K H) :
    infiniteProjection R K H (finiteEmbed R K H x) = 1 :=
  congr_arg Prod.fst ((prodContinuousMulEquiv_apply _).symm.trans
    (prodContinuousMulEquiv_finiteEmbed x))

/-- The embedding of finite adelic points into adelic points is continuous. -/
@[fun_prop]
theorem continuous_finiteEmbed : Continuous (finiteEmbed R K H) :=
  (prodContinuousMulEquiv R K H).symm.continuous.comp (continuous_const.prodMk continuous_id)

/-- An adelic point is determined by its infinite and finite components. -/
theorem ext_iff_projection {x y : AdelicPoints R K H} :
    x = y ↔ infiniteProjection R K H x = infiniteProjection R K H y ∧
      finiteProjection R K H x = finiteProjection R K H y := by
  rw [← (prodContinuousMulEquiv R K H).injective.eq_iff, prodContinuousMulEquiv_apply,
    prodContinuousMulEquiv_apply, Prod.ext_iff]

/-- An adelic point is determined by its infinite and finite components. -/
theorem ext_projection {x y : AdelicPoints R K H}
    (h₁ : infiniteProjection R K H x = infiniteProjection R K H y)
    (h₂ : finiteProjection R K H x = finiteProjection R K H y) : x = y :=
  ext_iff_projection.mpr ⟨h₁, h₂⟩

/-- The component of `finiteEmbed x` at a finite place `v` is the component of `x` at `v`. -/
@[simp]
theorem localProjection_finiteEmbed (v : HeightOneSpectrum R) (x : FiniteAdelicPoints R K H) :
    localProjection R K H v (finiteEmbed R K H x) = finiteLocalProjection R K H v x := by
  rw [localProjection_apply, finiteProjection_finiteEmbed]

/-- The component of `finiteEmbed x` at an infinite place `w` is the identity point. -/
@[simp]
theorem infinitePlaceProjection_finiteEmbed (w : InfinitePlace K) (x : FiniteAdelicPoints R K H) :
    infinitePlaceProjection R K H w (finiteEmbed R K H x) = 1 := by
  rw [infinitePlaceProjection_apply, infiniteProjection_finiteEmbed, map_one]

/-- `finiteEmbed` is injective: `finiteProjection` is a left inverse. -/
theorem finiteEmbed_injective : Function.Injective (finiteEmbed R K H) :=
  Function.LeftInverse.injective finiteProjection_finiteEmbed

/-- The image of `finiteEmbed` consists of the adelic points with trivial infinite component. -/
theorem mrange_finiteEmbed :
    MonoidHom.mrange (finiteEmbed R K H) = MonoidHom.mker (infiniteProjection R K H) := by
  ext y
  rw [MonoidHom.mem_mker]
  constructor
  · rintro ⟨x, rfl⟩
    exact infiniteProjection_finiteEmbed x
  · intro h
    exact ⟨finiteProjection R K H y, ext_projection (by rw [h, infiniteProjection_finiteEmbed])
      (finiteProjection_finiteEmbed _)⟩

/-- An adelic point is in the image of `finiteEmbed` exactly when its infinite component is the
identity point. As a simp lemma, it rewrites the existence of a finite adelic preimage to the
condition that the infinite component is the identity point. -/
@[simp]
theorem exists_finiteEmbed_eq_iff {y : AdelicPoints R K H} :
    (∃ x, finiteEmbed R K H x = y) ↔ infiniteProjection R K H y = 1 := by
  rw [← MonoidHom.mem_mrange, mrange_finiteEmbed, MonoidHom.mem_mker]

/-- `finiteEmbed` is a topological embedding: it has the continuous left inverse
`finiteProjection`. -/
theorem isEmbedding_finiteEmbed : Topology.IsEmbedding (finiteEmbed R K H) :=
  Function.LeftInverse.isEmbedding finiteProjection_finiteEmbed continuous_finiteProjection
    continuous_finiteEmbed

end AdelicPoints

end TauCeti

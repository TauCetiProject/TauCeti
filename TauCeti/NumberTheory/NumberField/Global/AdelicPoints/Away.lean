/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Decomposition
public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic

/-!
# Splitting off finitely many places from adelic points

Let `R` be a Dedekind domain with fraction field `K`, let `H` be a bialgebra over `K`, the
coordinate ring of `G = Spec H` when `H` is a commutative Hopf algebra, and let `S` be a set of
height one primes of `R`. This file defines the points of `G` away from `S`,

* `TauCeti.AdelicPoints.FiniteAwayPoints R K H S`, the points `G(𝔸_{K,f}^S)` over the finite
  adele ring away from `S`;
* `TauCeti.AdelicPoints.AwayPoints R K H S`, the points `G(𝔸_K^S)` over the adele ring away from
  `S`, `𝔸_K^S = K_∞ × 𝔸_{K,f}^S`,

with their rational diagonals and the projections forgetting the components at `S`. For a finite
set `S`, the splittings of the coefficient rings
`IsDedekindDomain.FiniteAdeleRing.awayEquiv` and `NumberField.AdeleRing.awayEquiv` give the
isomorphisms of topological groups

* `G(𝔸_{K,f}) ≃ (∏_{v ∈ S} G(K_v)) × G(𝔸_{K,f}^S)`, and
* `G(𝔸_K) ≃ G(K_S) × G(𝔸_K^S)` with `G(K_S) = ∏_{v ∈ S} G(K_v)`,

sending a point to its components at the places of `S` and its projection away from `S`. The
rational diagonal of `G(K)` goes to the pair of diagonals. Splitting off no places retains the
original group: for `S = ∅` the projections away from `S` are bijective.

The places in `S` are finite places; the splitting `G(𝔸_K) ≃ G(K_∞) × G(𝔸_{K,f})` at the infinite
places is `TauCeti.AdelicPoints.prodContinuousMulEquiv`.

## Main declarations

* `TauCeti.AdelicPoints.FiniteAwayPoints`, `TauCeti.AdelicPoints.AwayPoints`.
* `TauCeti.AdelicPoints.finiteAwayProjection`, `TauCeti.AdelicPoints.awayProjection`: forgetting
  the components at `S`.
* `TauCeti.AdelicPoints.finiteAwayDiagonal`, `TauCeti.AdelicPoints.awayDiagonal`: the rational
  diagonals away from `S`.
* `TauCeti.AdelicPoints.finiteAwayContinuousMulEquiv`:
  `G(𝔸_{K,f}) ≃ₜ* (∏_{v ∈ S} G(K_v)) × G(𝔸_{K,f}^S)`.
* `TauCeti.AdelicPoints.awayContinuousMulEquiv`: `G(𝔸_K) ≃ₜ* (∏_{v ∈ S} G(K_v)) × G(𝔸_K^S)`.
* `TauCeti.AdelicPoints.finiteAwayContinuousMulEquiv_finiteDiagonal`,
  `TauCeti.AdelicPoints.awayContinuousMulEquiv_diagonal`: the rational diagonal goes to the pair
  of diagonals.
* `TauCeti.AdelicPoints.finiteAwayProjection_empty_bijective`,
  `TauCeti.AdelicPoints.awayProjection_empty_bijective`: splitting off no places.

## References

* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.2, p. 7.
-/

public section
noncomputable section

open IsDedekindDomain HeightOneSpectrum NumberField WithConv

namespace TauCeti.AdelicPoints

variable (R K H : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Semiring H] [Bialgebra K H] (S : Set (HeightOneSpectrum R))

/-- The points `G(𝔸_{K,f}^S)` of `G = Spec H` over the finite adele ring away from `S`, with the
convolution product and the point topology. -/
abbrev FiniteAwayPoints := WithConv (H →ₐ[K] FiniteAdeleRing.Away R K S)

/-- The points `G(𝔸_K^S)` of `G = Spec H` over the adele ring away from `S`,
`𝔸_K^S = K_∞ × 𝔸_{K,f}^S`, with the convolution product and the point topology. -/
abbrev AwayPoints := WithConv (H →ₐ[K] InfiniteAdeleRing K × FiniteAdeleRing.Away R K S)

/-- The rational diagonal `G(K) → G(𝔸_{K,f}^S)`. -/
def finiteAwayDiagonal : WithConv (H →ₐ[K] K) →* FiniteAwayPoints R K H S :=
  AlgHom.mapValue (Algebra.ofId K _)

/-- The rational diagonal `G(K) → G(𝔸_K^S)`. -/
def awayDiagonal : WithConv (H →ₐ[K] K) →* AwayPoints R K H S :=
  AlgHom.mapValue (Algebra.ofId K _)

/-- The projection `G(𝔸_{K,f}) → G(𝔸_{K,f}^S)` forgetting the components at `S`. -/
def finiteAwayProjection : FiniteAdelicPoints R K H →* FiniteAwayPoints R K H S :=
  AlgHom.mapValue (FiniteAdeleRing.restrictAway K S).toAlgHom

/-- The projection `G(𝔸_K) → G(𝔸_K^S)` forgetting the components at `S`: the infinite component
is kept and the finite component is projected away from `S`. -/
def awayProjection : AdelicPoints R K H →* AwayPoints R K H S :=
  AlgHom.mapValue <| (AlgHom.fst K (InfiniteAdeleRing K) (FiniteAdeleRing R K)).prod <|
    (FiniteAdeleRing.restrictAway K S).toAlgHom.comp
      (AlgHom.snd K (InfiniteAdeleRing K) (FiniteAdeleRing R K))

variable {R K H S}

@[simp]
theorem finiteAwayDiagonal_apply_apply (g : WithConv (H →ₐ[K] K)) (h : H) :
    finiteAwayDiagonal R K H S g h = algebraMap K (FiniteAdeleRing.Away R K S) (g h) := by
  simp [finiteAwayDiagonal]

@[simp]
theorem awayDiagonal_apply_apply (g : WithConv (H →ₐ[K] K)) (h : H) :
    awayDiagonal R K H S g h =
      algebraMap K (InfiniteAdeleRing K × FiniteAdeleRing.Away R K S) (g h) := by
  simp [awayDiagonal]

@[simp]
theorem finiteAwayProjection_apply_apply (x : FiniteAdelicPoints R K H) (h : H) :
    (finiteAwayProjection R K H S x).ofConv h = FiniteAdeleRing.restrictAway K S (x.ofConv h) := by
  simp [finiteAwayProjection]

@[simp]
theorem awayProjection_apply_apply (x : AdelicPoints R K H) (h : H) :
    (awayProjection R K H S x).ofConv h =
      ((x.ofConv h).1, FiniteAdeleRing.restrictAway K S (x.ofConv h).2) := by
  simp only [awayProjection, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    AlgHom.prod_apply, ContinuousAlgHom.coe_coe]
  rw [AlgHom.fst_apply, AlgHom.snd_apply]

@[fun_prop]
theorem continuous_finiteAwayProjection : Continuous (finiteAwayProjection R K H S) :=
  AlgHom.continuous_mapValue (FiniteAdeleRing.restrictAway K S).cont

@[fun_prop]
theorem continuous_awayProjection : Continuous (awayProjection R K H S) :=
  AlgHom.continuous_mapValue <| continuous_fst.prodMk <|
    (FiniteAdeleRing.restrictAway K S).cont.comp continuous_snd

/-- The projection away from `S` of the finite diagonal image of a rational point is its diagonal
image away from `S`. -/
@[simp]
theorem finiteAwayProjection_finiteDiagonal (g : WithConv (H →ₐ[K] K)) :
    finiteAwayProjection R K H S (finiteDiagonal R K H g) = finiteAwayDiagonal R K H S g := by
  ext h
  simp

/-- The projection away from `S` of the diagonal image of a rational point is its diagonal image
away from `S`. -/
@[simp]
theorem awayProjection_diagonal (g : WithConv (H →ₐ[K] K)) :
    awayProjection R K H S (diagonal R K H g) = awayDiagonal R K H S g := by
  refine WithConv.ofConv_injective (AlgHom.ext fun h ↦ ?_)
  simp [AdeleRing.algebraMap_fst_def, AdeleRing.algebraMap_snd_def, AlgHomClass.commutes]

/-! ### The splittings -/

variable (R K H) in
/-- For a finite set `S` of finite places, the splitting
`G(𝔸_{K,f}) ≃ₜ* (∏_{v ∈ S} G(K_v)) × G(𝔸_{K,f}^S)` of the finite adelic points, sending a point to
its components at the places of `S` and its projection away from `S`. -/
def finiteAwayContinuousMulEquiv (hS : S.Finite) :
    FiniteAdelicPoints R K H ≃ₜ* (∀ v : S, LocalPoints R K H v.val) × FiniteAwayPoints R K H S :=
  (FiniteAdeleRing.awayEquiv R K hS).mapValueContinuousMulEquiv.trans
    (PointTopology.piProdContinuousMulEquiv K H _ _)

variable (R K H) in
/-- For a finite set `S` of finite places, the splitting `G(𝔸_K) ≃ₜ* G(K_S) × G(𝔸_K^S)` of the
adelic points, with `G(K_S) = ∏_{v ∈ S} G(K_v)`, sending a point to its components at the places
of `S` and its projection away from `S`. -/
def awayContinuousMulEquiv (hS : S.Finite) :
    AdelicPoints R K H ≃ₜ* (∀ v : S, LocalPoints R K H v.val) × AwayPoints R K H S :=
  (AdeleRing.awayEquiv R K hS).mapValueContinuousMulEquiv.trans
    (PointTopology.piProdContinuousMulEquiv K H _ _)

variable (hS : S.Finite)

/-- The component at `v ∈ S` of the splitting of a finite adelic point is its local component. -/
@[simp]
theorem finiteAwayContinuousMulEquiv_apply_fst (x : FiniteAdelicPoints R K H) (v : S) :
    (finiteAwayContinuousMulEquiv R K H hS x).1 v = finiteLocalProjection R K H v.val x := by
  refine WithConv.ofConv_injective (AlgHom.ext fun h ↦ ?_)
  simp [finiteAwayContinuousMulEquiv]

/-- The component away from `S` of the splitting of a finite adelic point is its projection away
from `S`. -/
@[simp]
theorem finiteAwayContinuousMulEquiv_apply_snd (x : FiniteAdelicPoints R K H) :
    (finiteAwayContinuousMulEquiv R K H hS x).2 = finiteAwayProjection R K H S x := by
  refine WithConv.ofConv_injective (AlgHom.ext fun h ↦ ?_)
  simp [finiteAwayContinuousMulEquiv]

/-- The component at `v ∈ S` of the splitting of an adelic point is its local component `p_v`. -/
@[simp]
theorem awayContinuousMulEquiv_apply_fst (x : AdelicPoints R K H) (v : S) :
    (awayContinuousMulEquiv R K H hS x).1 v = localProjection R K H v.val x := by
  refine WithConv.ofConv_injective (AlgHom.ext fun h ↦ ?_)
  simp [awayContinuousMulEquiv]

/-- The component away from `S` of the splitting of an adelic point is its projection away from
`S`. -/
@[simp]
theorem awayContinuousMulEquiv_apply_snd (x : AdelicPoints R K H) :
    (awayContinuousMulEquiv R K H hS x).2 = awayProjection R K H S x := by
  refine WithConv.ofConv_injective (AlgHom.ext fun h ↦ ?_)
  simp [awayContinuousMulEquiv]

/-- At a place `v ∈ S`, the finite adelic point assembled from local points `p.1` and a point
`p.2` away from `S` has the local component of `p.1` at `v`. -/
@[simp]
theorem finiteAwayContinuousMulEquiv_symm_apply_apply_of_mem
    (p : (∀ v : S, LocalPoints R K H v.val) × FiniteAwayPoints R K H S) (h : H)
    (v : HeightOneSpectrum R) (hv : v ∈ S) :
    ((finiteAwayContinuousMulEquiv R K H hS).symm p).ofConv h v = (p.1 ⟨v, hv⟩).ofConv h := by
  simp [finiteAwayContinuousMulEquiv, hv]

/-- At a place `v ∉ S`, the finite adelic point assembled from local points `p.1` and a point
`p.2` away from `S` has the component of `p.2` at `v`. -/
@[simp]
theorem finiteAwayContinuousMulEquiv_symm_apply_apply_of_notMem
    (p : (∀ v : S, LocalPoints R K H v.val) × FiniteAwayPoints R K H S) (h : H)
    (v : HeightOneSpectrum R) (hv : v ∉ S) :
    ((finiteAwayContinuousMulEquiv R K H hS).symm p).ofConv h v = p.2.ofConv h ⟨v, hv⟩ := by
  simp [finiteAwayContinuousMulEquiv, hv]

/-- The adelic point assembled from local points `p.1` at the places of `S` and a point `p.2`
away from `S` has the infinite component of `p.2`, and as finite component the finite adele
assembled from the values of `p.1` and the finite component of `p.2`. -/
@[simp]
theorem awayContinuousMulEquiv_symm_apply_apply
    (p : (∀ v : S, LocalPoints R K H v.val) × AwayPoints R K H S) (h : H) :
    ((awayContinuousMulEquiv R K H hS).symm p).ofConv h =
      ((p.2.ofConv h).1,
        (FiniteAdeleRing.awayEquiv R K hS).symm (fun v ↦ (p.1 v).ofConv h, (p.2.ofConv h).2)) := by
  simp [awayContinuousMulEquiv]

/-- The splitting of the finite adelic points sends the finite diagonal image of a rational point
to the pair of its local images at the places of `S` and its diagonal image away from `S`. -/
theorem finiteAwayContinuousMulEquiv_finiteDiagonal (g : WithConv (H →ₐ[K] K)) :
    finiteAwayContinuousMulEquiv R K H hS (finiteDiagonal R K H g) =
      (fun v : S ↦ AlgHom.mapValue (Algebra.ofId K (v.val.adicCompletion K)) g,
        finiteAwayDiagonal R K H S g) := by
  ext v : 2 <;> simp

/-- The splitting of the adelic points sends the diagonal image of a rational point to the pair
of its local images at the places of `S` and its diagonal image away from `S`. -/
theorem awayContinuousMulEquiv_diagonal (g : WithConv (H →ₐ[K] K)) :
    awayContinuousMulEquiv R K H hS (diagonal R K H g) =
      (fun v : S ↦ AlgHom.mapValue (Algebra.ofId K (v.val.adicCompletion K)) g,
        awayDiagonal R K H S g) := by
  ext v : 2 <;> simp

/-! ### Splitting off no places -/

/-- Splitting off no places retains the finite adelic points: the projection
`G(𝔸_{K,f}) → G(𝔸_{K,f}^∅)` is bijective. -/
theorem finiteAwayProjection_empty_bijective :
    Function.Bijective (finiteAwayProjection R K H ∅) := by
  let e := finiteAwayContinuousMulEquiv R K H Set.finite_empty
  refine ⟨fun x y hxy ↦ e.injective (Prod.ext (Subsingleton.elim _ _) ?_), fun z ↦
    ⟨e.symm (isEmptyElim, z), ?_⟩⟩
  · simpa [e] using hxy
  · rw [← finiteAwayContinuousMulEquiv_apply_snd Set.finite_empty,
      ContinuousMulEquiv.apply_symm_apply]

/-- Splitting off no places retains the adelic points: the projection `G(𝔸_K) → G(𝔸_K^∅)` is
bijective. -/
theorem awayProjection_empty_bijective : Function.Bijective (awayProjection R K H ∅) := by
  let e := awayContinuousMulEquiv R K H Set.finite_empty
  refine ⟨fun x y hxy ↦ e.injective (Prod.ext (Subsingleton.elim _ _) ?_), fun z ↦
    ⟨e.symm (isEmptyElim, z), ?_⟩⟩
  · simpa [e] using hxy
  · rw [← awayContinuousMulEquiv_apply_snd Set.finite_empty, ContinuousMulEquiv.apply_symm_apply]

end TauCeti.AdelicPoints

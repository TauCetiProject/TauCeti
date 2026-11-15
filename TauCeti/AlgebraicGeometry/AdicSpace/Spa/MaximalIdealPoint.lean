/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.NormedField
public import TauCeti.RingTheory.Valuation.Spectral

public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
import TauCeti.RingTheory.Huber.Continuous.PowerBounded
import TauCeti.RingTheory.Huber.Restricted.Noetherian
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Complete
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.ResidueField

/-!
# The classical points of an adic spectrum over a complete field

Let `K` be a complete nontrivially normed field with an ultrametric norm and `A` a topological
`K`-algebra. Wedhorn's Example 7.58 attaches a point of `X = Spa (A, A°)` to each maximal ideal
`𝔪` of an affinoid `K`-algebra `A`. The residue field `A ⧸ 𝔪` is a finite extension of `K`, so
the norm of `K` extends uniquely to it, and pulling that norm back along `A → A ⧸ 𝔪` gives a point
of `X` with support `𝔪`. These are the *classical points* of `X`, the points of rigid geometry.

This file makes the construction for every closed maximal ideal `𝔪` whose residue field is finite
over `K`, with no other hypothesis on `A`. The extended norm is Mathlib's spectral norm, packaged
as the valuation `TauCeti.spectralValuation`. The two conditions defining `Spa (A, A°)` hold for
the following reasons.

* *Continuity.* Closedness of `𝔪` makes `A ⧸ 𝔪` a Hausdorff topological `K`-vector space for the
  quotient topology. On a finite extension the spectral valuation is continuous for every such
  topology (`TauCeti.isContinuous_spectralValuation`), and continuity pulls back along the
  continuous map `A → A ⧸ 𝔪`.
* *The plus ring.* A scalar `c ∈ K` with `0 < ‖c‖ < 1` is topologically nilpotent in `A` and has
  nonzero value, so a continuous valuation with archimedean value group is at most `1` on every
  power-bounded element (Wedhorn, Proposition 7.41).

Both steps work for any continuous `K`-algebra map `φ : A → L` to a finite field extension `L` of
`K` whose topology makes it a Hausdorff topological `K`-vector space
(`AlgHom.ofValuation_comap_spectralValuation_mem_spa`). The classical point
`TauCeti.ValuationSpectrum.maximalIdealPoint` is the case of the residue map `A → A ⧸ 𝔪`.

For a complete Huber ring every maximal ideal is closed (`TauCeti.Huber.isClosed_of_isMaximal`).
For an affinoid `K`-algebra, finiteness of the residue fields is Wedhorn's Proposition 5.61.

Conversely, the classical point at `𝔪` is the only point of `Spa (A, A°)` with support `𝔪`. Such a
point is a valuation on `A ⧸ 𝔪` pulled back to `A`, and it compares scalars by their norms because
it pulls back to a point of `Spa (K, K°)`. Up to equivalence the norm of `K` has only one extension
to the finite extension `A ⧸ 𝔪` (`Valuation.isEquiv_spectralValuation_iff`), so the point is the
classical one.

For a `K`-algebra `A` topologically of finite type, every maximal ideal is closed and has residue
field finite over `K`. The classical points then give an injective map
`Max(A) → Spa (A, A°)`, `TauCeti.ValuationSpectrum.maximalSpectrumToSpa`, whose image consists of
the points with maximal support.

## Main definitions

* `TauCeti.ValuationSpectrum.maximalIdealPoint`: the classical point of `Spa (A, A°)` attached to
  a closed maximal ideal with residue field finite over `K`.
* `TauCeti.ValuationSpectrum.maximalSpectrumToSpa`: for `A` topologically of finite type over `K`,
  the map `Max(A) → Spa (A, A°)` sending a maximal ideal to its classical point.

## Main results

* `AlgHom.ofValuation_comap_spectralValuation_mem_spa`: the spectral valuation
  pulled back along a continuous `K`-algebra map to a finite extension is a point of
  `Spa (A, A°)`.
* `TauCeti.ValuationSpectrum.maximalIdealPoint_vle_iff`: the classical point compares elements
  by the spectral norms of their residues.
* `TauCeti.ValuationSpectrum.maximalIdealPoint_vle_algebraMap_iff`: it compares scalars by their
  norms, so it extends the norm of `K`.
* `TauCeti.ValuationSpectrum.maximalIdealPoint_vle_iff_of_ker_eq`: at the kernel of a `K`-algebra
  map `ψ : A → K` it compares elements by the norms of their values under `ψ`.
* `TauCeti.ValuationSpectrum.supp_maximalIdealPoint`: its support is `𝔪`.
* `TauCeti.ValuationSpectrum.maximalIdealPoint_inj`: distinct maximal ideals give distinct
  points when they are closed and their residue fields are finite over `K`.
* `TauCeti.ValuationSpectrum.eq_maximalIdealPoint_iff`: a point of `Spa (A, A°)` is the classical
  point at `𝔪` exactly when its support is `𝔪`.
* `TauCeti.ValuationSpectrum.maximalSpectrumToSpa_injective` and
  `TauCeti.ValuationSpectrum.range_maximalSpectrumToSpa`: for `A` topologically of finite type over
  `K`, `Max(A)` embeds into `Spa (A, A°)`, with image the points whose support is maximal.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.61,
  Proposition 7.41, Example 7.57 and Example 7.58.
-/

public section

noncomputable section

open scoped NNReal

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] [Algebra K A]
  [ContinuousSMul K A]

/-- **The spectral valuation pulled back to `A` is a point of `Spa (A, A°)`**, along every
continuous `K`-algebra map `φ : A → L` to a finite field extension `L` of `K` carrying a Hausdorff
topological `K`-vector space structure. -/
theorem _root_.AlgHom.ofValuation_comap_spectralValuation_mem_spa {L : Type*} [Field L]
    [Algebra K L] [FiniteDimensional K L] [TopologicalSpace L] [IsTopologicalAddGroup L]
    [ContinuousSMul K L] [T2Space L] (φ : A →ₐ[K] L) (hφ : Continuous φ) :
    ofValuation ((spectralValuation K L).comap (φ : A →+* L)) ∈ spa (powerBoundedSubring A) := by
  set v := (spectralValuation K L).comap (φ : A →+* L)
  have hv : v.IsContinuous := (isContinuous_spectralValuation K L).comap hφ
  refine (mem_spa_iff _ _).mpr ⟨(isContinuous_ofValuation_iff v).mpr hv, fun a ha ↦ ?_⟩
  rw [vle_ofValuation, map_one]
  -- the value group of `v` sits inside `ℝ≥0ˣ`, so it is archimedean
  have : MulArchimedean v.ValueGroup₀ :=
    MulArchimedean.comap MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom
      MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  -- a scalar of norm strictly between `0` and `1` is topologically nilpotent with nonzero value
  obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt K one_pos
  have hcnil : IsTopologicallyNilpotent c := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc₁
  have hnil : IsTopologicallyNilpotent (algebraMap K A c) := hcnil.map (continuous_algebraMap K A)
  have hc : v (algebraMap K A c) ≠ 0 := by
    simpa [v] using norm_pos_iff.mp hc₀
  exact hv.le_one_of_isPowerBounded hnil hc (mem_powerBoundedSubring.mp ha)

section MaximalIdeal

attribute [local instance] Ideal.Quotient.field

variable (K) (𝔪 : Ideal A) [𝔪.IsMaximal] [FiniteDimensional K (A ⧸ 𝔪)]

/-- **The classical point of `Spa (A, A°)` attached to a maximal ideal** `𝔪` (Wedhorn, Example
7.58), for `𝔪` closed with residue field finite over `K`: the unique extension of the norm of `K`
to `A ⧸ 𝔪`, the spectral norm, pulled back along `A → A ⧸ 𝔪`. -/
def maximalIdealPoint (h𝔪 : IsClosed (𝔪 : Set A)) : spa (powerBoundedSubring A) :=
  ⟨ofValuation ((spectralValuation K (A ⧸ 𝔪)).comap (Ideal.Quotient.mk 𝔪)), by
    -- closedness of `𝔪` makes `A ⧸ 𝔪` Hausdorff, and `K` acts on it through `A`
    have : IsClosed (𝔪 : Set A) := h𝔪
    have : ContinuousSMul K (A ⧸ 𝔪) := continuousSMul_of_algebraMap K (A ⧸ 𝔪) <| by
      rw [IsScalarTower.algebraMap_eq K A (A ⧸ 𝔪), RingHom.coe_comp,
        Ideal.Quotient.algebraMap_eq]
      exact continuous_quot_mk.comp (continuous_algebraMap K A)
    exact (Ideal.Quotient.mkₐ K 𝔪).ofValuation_comap_spectralValuation_mem_spa continuous_quot_mk⟩

variable {K 𝔪}

/-- The underlying point of `Spv A` is the spectral valuation of `A ⧸ 𝔪` pulled back to `A`. -/
theorem maximalIdealPoint_val (h𝔪 : IsClosed (𝔪 : Set A)) :
    (maximalIdealPoint K 𝔪 h𝔪).1 =
      ofValuation ((spectralValuation K (A ⧸ 𝔪)).comap (Ideal.Quotient.mk 𝔪)) :=
  (rfl)

/-- **The classical point at `𝔪` compares elements by the spectral norms of their residues.** -/
@[simp]
theorem maximalIdealPoint_vle_iff (h𝔪 : IsClosed (𝔪 : Set A)) (a b : A) :
    (maximalIdealPoint K 𝔪 h𝔪).1.toValuativeRel.vle a b ↔
      spectralNorm K (A ⧸ 𝔪) (Ideal.Quotient.mk 𝔪 a) ≤
        spectralNorm K (A ⧸ 𝔪) (Ideal.Quotient.mk 𝔪 b) := by
  rw [maximalIdealPoint_val, vle_ofValuation, ← NNReal.coe_le_coe]
  simp

/-- **The classical point at `𝔪` compares scalars by their norms**: it extends the norm of `K`. -/
theorem maximalIdealPoint_vle_algebraMap_iff (h𝔪 : IsClosed (𝔪 : Set A)) (c d : K) :
    (maximalIdealPoint K 𝔪 h𝔪).1.toValuativeRel.vle (algebraMap K A c) (algebraMap K A d) ↔
      ‖c‖ ≤ ‖d‖ := by
  simp [Ideal.Quotient.mk_algebraMap, spectralNorm_extends]

/-- **At a `K`-rational maximal ideal the classical point compares values.** If `𝔪` is the kernel
of a `K`-algebra map `ψ : A → K`, the classical point at `𝔪` compares `a` and `b` as the norm
compares `ψ a` and `ψ b`. -/
theorem maximalIdealPoint_vle_iff_of_ker_eq (h𝔪 : IsClosed (𝔪 : Set A)) (ψ : A →ₐ[K] K)
    (hψ : RingHom.ker ψ = 𝔪) (a b : A) :
    (maximalIdealPoint K 𝔪 h𝔪).1.toValuativeRel.vle a b ↔ ‖ψ a‖ ≤ ‖ψ b‖ := by
  -- every `a` has the residue of the scalar `ψ a`, since `a - ψ a` lies in `ker ψ = 𝔪`
  have hmk (a : A) : Ideal.Quotient.mk 𝔪 a = algebraMap K (A ⧸ 𝔪) (ψ a) := by
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, ← hψ]
    simp
  rw [maximalIdealPoint_vle_iff, hmk, hmk, spectralNorm_extends, spectralNorm_extends]

/-- **The support of the classical point at `𝔪` is `𝔪`.** -/
@[simp]
theorem supp_maximalIdealPoint (h𝔪 : IsClosed (𝔪 : Set A)) :
    (maximalIdealPoint K 𝔪 h𝔪).1.supp = 𝔪 := by
  ext a
  simp [maximalIdealPoint_val, Valuation.mem_supp_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- **Distinct eligible maximal ideals give distinct classical points**, since each point recovers
its ideal as its support. Thus the closed maximal ideals whose residue fields are finite over `K`
give distinct points of `Spa (A, A°)`. -/
theorem maximalIdealPoint_inj {𝔫 : Ideal A} [𝔫.IsMaximal] [FiniteDimensional K (A ⧸ 𝔫)]
    (h𝔪 : IsClosed (𝔪 : Set A)) (h𝔫 : IsClosed (𝔫 : Set A)) :
    maximalIdealPoint K 𝔪 h𝔪 = maximalIdealPoint K 𝔫 h𝔫 ↔ 𝔪 = 𝔫 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  rw [← supp_maximalIdealPoint (K := K) h𝔪, ← supp_maximalIdealPoint (K := K) h𝔫, h]

/-- **The classical point at `𝔪` is the only point of `Spa (A, A°)` with support `𝔪`.** A point
with support `𝔪` is a valuation on the residue field `A ⧸ 𝔪` pulled back to `A`. It compares
scalars by their norms, because it pulls back to a point of `Spa (K, K°)`. By the uniqueness of
the extension of the norm of `K` to the finite extension `A ⧸ 𝔪`
(`Valuation.isEquiv_spectralValuation_iff`), that valuation is equivalent to the spectral
valuation. -/
theorem eq_maximalIdealPoint_iff (h𝔪 : IsClosed (𝔪 : Set A)) (x : spa (powerBoundedSubring A)) :
    x = maximalIdealPoint K 𝔪 h𝔪 ↔ x.1.supp = 𝔪 := by
  refine ⟨fun h ↦ h ▸ supp_maximalIdealPoint h𝔪, fun hx ↦ ?_⟩
  -- `x` pulls back to a point of `Spa (K, K°)`, so it compares scalars by their norms
  have hK := comap_mem_spa (continuous_algebraMap K A) (fun c hc ↦ mem_powerBoundedSubring.mpr
    (isPowerBounded_algebraMap_of_norm_le_one
      (isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp hc)))) x.2
  -- the valuation of `x` factors through the residue field `A ⧸ 𝔪`
  have hle : 𝔪 ≤ x.1.valuation.supp := hx ▸ (supp_eq_valuation_supp x.1).le
  set w := x.1.valuation.onQuot hle
  have hw (a : A) : w (Ideal.Quotient.mk 𝔪 a) = x.1.valuation a := by
    rw [← Valuation.comap_apply, Valuation.onQuot_comap_eq]
  have hequiv : w.IsEquiv (spectralValuation K (A ⧸ 𝔪)) :=
    (w.isEquiv_spectralValuation_iff).mpr fun c d ↦ by
      simpa [← Ideal.Quotient.mk_algebraMap, hw] using vle_iff_norm_le_of_mem_spa hK c d
  refine Subtype.ext (ext' fun a b ↦ ?_)
  rw [maximalIdealPoint_val, vle_ofValuation, ← valuation_le_iff, ← hw, ← hw]
  exact hequiv a b

end MaximalIdeal

section TopologicallyFiniteType

attribute [local instance] Ideal.Quotient.field MaximalSpectrum.isMaximal

variable (K) (hA : IsTopologicallyFiniteType (algebraMap K A))

/-- **The classical points of an affinoid `K`-algebra** (Wedhorn, Example 7.58). For `A`
topologically of finite type over `K`, every maximal ideal `𝔪` is closed and has residue field
finite over `K` (Wedhorn, Proposition 5.61), so it has a classical point
`TauCeti.ValuationSpectrum.maximalIdealPoint` in `Spa (A, A°)`. -/
def maximalSpectrumToSpa (𝔪 : MaximalSpectrum A) : spa (powerBoundedSubring A) :=
  haveI := hA.finite_quotient_of_isMaximal 𝔪.asIdeal
  maximalIdealPoint K 𝔪.asIdeal (hA.isClosed_ideal 𝔪.asIdeal)

variable {K hA}

/-- **The classical point at `𝔪` compares elements by the spectral norms of their residues.** -/
@[simp]
theorem maximalSpectrumToSpa_vle_iff (𝔪 : MaximalSpectrum A) (a b : A) :
    (maximalSpectrumToSpa K hA 𝔪).1.toValuativeRel.vle a b ↔
      spectralNorm K (A ⧸ 𝔪.asIdeal) (Ideal.Quotient.mk 𝔪.asIdeal a) ≤
        spectralNorm K (A ⧸ 𝔪.asIdeal) (Ideal.Quotient.mk 𝔪.asIdeal b) :=
  haveI := hA.finite_quotient_of_isMaximal 𝔪.asIdeal
  maximalIdealPoint_vle_iff _ a b

/-- **The support of the classical point at `𝔪` is `𝔪`.** -/
@[simp]
theorem supp_maximalSpectrumToSpa (𝔪 : MaximalSpectrum A) :
    (maximalSpectrumToSpa K hA 𝔪).1.supp = 𝔪.asIdeal :=
  haveI := hA.finite_quotient_of_isMaximal 𝔪.asIdeal
  supp_maximalIdealPoint _

/-- **A point of `Spa (A, A°)` is the classical point at `𝔪` exactly when its support is `𝔪`**,
for `A` topologically of finite type over `K`. -/
theorem eq_maximalSpectrumToSpa_iff (x : spa (powerBoundedSubring A)) (𝔪 : MaximalSpectrum A) :
    x = maximalSpectrumToSpa K hA 𝔪 ↔ x.1.supp = 𝔪.asIdeal :=
  haveI := hA.finite_quotient_of_isMaximal 𝔪.asIdeal
  eq_maximalIdealPoint_iff _ x

/-- **Distinct maximal ideals give distinct classical points**: `Max(A)` embeds into
`Spa (A, A°)`. -/
theorem maximalSpectrumToSpa_injective : Function.Injective (maximalSpectrumToSpa K hA) :=
  fun 𝔪 𝔫 h ↦ MaximalSpectrum.ext <| by
    rw [← supp_maximalSpectrumToSpa (hA := hA) 𝔪, h, supp_maximalSpectrumToSpa]

/-- **The classical points of `Spa (A, A°)` are the points with maximal support**, for `A`
topologically of finite type over `K`. -/
theorem range_maximalSpectrumToSpa :
    Set.range (maximalSpectrumToSpa K hA) = {x | x.1.supp.IsMaximal} := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨⟨x.1.supp, hx⟩, ((eq_maximalSpectrumToSpa_iff x _).mpr rfl).symm⟩⟩
  rintro ⟨𝔪, rfl⟩
  rw [Set.mem_ofPred_eq, supp_maximalSpectrumToSpa]
  exact 𝔪.isMaximal

end TopologicallyFiniteType

end TauCeti.ValuationSpectrum

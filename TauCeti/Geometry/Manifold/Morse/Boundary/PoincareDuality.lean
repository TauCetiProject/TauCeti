/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.DualOrientation
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedCochainComplex
import TauCeti.Algebra.Homology.CochainComplex.Antidiagonal

/-!
# Poincaré duality for the integral Morse complex

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, oriented by
`oM`, `X` a Morse–Smale pseudo-gradient adapted to `f` and `𝔬` orientations of its unstable
manifolds. The opposite function `-f`, with the pseudo-gradient `-X` and the dual orientation data
`𝔬.dual hX hf oM` (`TauCeti.MorseOrientation.dual`), has the same critical points, with indices
`n - ind_f`, and its integral Morse boundary is the transpose of that of `f` up to the sign
`(-1) ^ ind_f p` at each critical point `p`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseBoundaryCoeff_dual`). This file turns that
identity of boundary maps into an identification of complexes and of their (co)homology.

The integral Morse cochain complex of `f`, and with it every complex and duality statement below,
is built under the hypothesis `hsq` that the integral Morse boundary of `f` squares to zero. That
hypothesis, which needs the orientations of the compactified spaces of index-two trajectories, is
not proved in the library yet, so the results here are conditional on it.

* **`∂² = 0` for `-f`.** The Morse boundary of `-f` squares to zero exactly when that of `f` does
  (`IsMorseSmale.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_iff`, in
  `TauCeti.Geometry.Manifold.Morse.Boundary.DualOrientation`). In particular the integral Morse
  complex of `-f` is defined whenever that of `f` is
  (`IsMorseSmale.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_of_int`).
* **Cochains of `f` are chains of `-f`.** Reading an additive map `a` from the integral chains of
  `f` of index `i` to a ring `R` as the chain of `-f` of index `k` whose coefficient at `q` is
  `a q * (-1) ^ ((i + 1).choose 2)` (`TauCeti.IsMorse.signedCochainToNegChain`) is an isomorphism
  when `i + k = n` (`TauCeti.IsMorse.bijective_signedCochainToNegChain`). The sign
  `(-1) ^ ((i + 1).choose 2)` changes by `(-1) ^ (i + 1)` from `i` to `i + 1`, which absorbs the
  sign `(-1) ^ ind_f p` of the transposition, so that the identification carries the Morse
  coboundary `a ↦ a ∘ ∂` of `f` to the Morse boundary of `-f`
  (`IsMorseSmale.signedCochainToNegChain_comp_signedMorseBoundaryAt`).
* **Poincaré duality.** Hence the Morse cohomology of `f` with coefficients in `R`, the cohomology
  of `Hom_ℤ(CM_*(f; ℤ), R)`, is isomorphic in degree `i` to the Morse homology of `-f` with
  coefficients in `R` in degree `k`, for `i + k = n`
  (`IsMorseSmale.signedMorseCohomologyEquivNegHomology`), by the homological algebra of
  `CochainComplex.homologyIsoOfAntidiagonal`. This is the Morse-theoretic form of
  Poincaré duality on an oriented manifold; identifying it with Poincaré duality in singular
  (co)homology needs the comparison of Morse and singular (co)homology, which is not made here.
  Its mod-two form, which needs no orientations, is
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseCohomologyEquivNegHomology`.

## Main declarations

* `TauCeti.IsMorse.signedCochainToNegChain`: an integral cochain of `f` read, with a sign, as a
  chain of `-f`.
* `TauCeti.IsMorse.bijective_signedCochainToNegChain`: in complementary degrees it is an
  isomorphism.

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmale.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_of_int`: the Morse
  boundary of `-f` squares to zero whenever the integral Morse boundary of `f` does.
* `IsMorseSmale.signedCochainToNegChain_comp_signedMorseBoundaryAt`: the identification carries
  the coboundary of `f` to the boundary of `-f`.
* `IsMorseSmale.signedMorseCohomologyEquivNegHomology`: the Morse cohomology of `f` in degree `i`
  is the Morse homology of `-f` in degree `k`, for `i + k = n`;
  `IsMorseSmale.signedMorseCohomologyEquivNegHomology_homologyπ` computes it on the class of a
  cocycle.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 5 (the Morse complex of `-f` is the dual complex,
  and Poincaré duality).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients and Poincaré duality).
-/

public section

universe u v

open CategoryTheory Limits Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-! ### `∂² = 0` for the opposite function -/

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} (𝔬 : MorseOrientation f X) (hf : IsMorse 𝓘(ℝ, E) f)
  (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (Module.finrank ℝ E)))

/-- **`∂² = 0` over `ℤ` for `f` gives `∂² = 0` for `-f` over every ring.** For the dual orientation
data, if the integral Morse boundary of `f` squares to zero, so does the Morse boundary of `-f` with
coefficients in any ring `R`. -/
theorem IsMorseSmale.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_of_int
    (hMS : hX.IsMorseSmale)
    (hsq : hX.signedMorseBoundary 𝔬 hf ℤ ∘ₗ hX.signedMorseBoundary 𝔬 hf ℤ = 0)
    (R : Type*) [Ring R] :
    (hX.neg hf).signedMorseBoundary (𝔬.dual hX hf oM) hf.neg R ∘ₗ
        (hX.neg hf).signedMorseBoundary (𝔬.dual hX hf oM) hf.neg R = 0 :=
  (hMS.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_iff 𝔬 hf oM).2
    (signedMorseBoundary_comp_signedMorseBoundary_eq_zero_of_int hsq R)

end IsAdaptedPseudoGradient

/-! ### Cochains of `f` as chains of `-f` -/

namespace IsMorse

variable (hf : IsMorse 𝓘(ℝ, E) f) (R : Type v) [Ring R]

/-- **An integral cochain of `f` read as a chain of `-f`.** The coefficient at a critical point `q`
of index `k` for `-f` of the chain associated with an additive map `a` from the integral chains of
`f` of index `i` to `R` is `a q * (-1) ^ ((i + 1).choose 2)` when `q` has index `i` for `f`, and `0`
otherwise. When `i + k = n` every critical point of index `k` for `-f` has index `i` for `f`, and
this is an isomorphism (`TauCeti.IsMorse.bijective_signedCochainToNegChain`); otherwise it is
zero (`TauCeti.IsMorse.signedCochainToNegChain_eq_zero`). The sign makes it carry the Morse
coboundary of `f` to the Morse boundary of `-f` (in the namespace
`TauCeti.IsAdaptedPseudoGradient`,
`IsMorseSmale.signedCochainToNegChain_comp_signedMorseBoundaryAt`). -/
noncomputable def signedCochainToNegChain (i k : ℕ) :
    (({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = i} →₀ ℤ) →ₗ[ℤ] R) →ₗ[R]
      ({q : criticalPoints 𝓘(ℝ, E) (-f) // manifoldMorseIndex 𝓘(ℝ, E) (-f) q = k} →₀ R) :=
  haveI := hf.neg.finite_criticalPoints.to_subtype
  { toFun a := Finsupp.equivFunOnFinite.symm fun q ↦
      if hq : manifoldMorseIndex 𝓘(ℝ, E) f q.val = i then
        a (Finsupp.single ⟨⟨q.val.val, by simpa using q.val.property⟩, hq⟩ 1) *
          (((-1 : ℤ) ^ (i + 1).choose 2 : ℤ) : R)
      else 0
    map_add' a b := by
      ext q
      by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f q.val = i <;> simp [hq, add_mul]
    map_smul' r a := by
      ext q
      by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f q.val = i <;> simp [hq, mul_assoc] }

variable {R}

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The coefficient at `q` of the chain of `-f` associated with a cochain `a` of `f` of index `i`
is `a q * (-1) ^ ((i + 1).choose 2)` if `q` has index `i` for `f`, and `0` otherwise. -/
@[simp]
theorem signedCochainToNegChain_apply {i k : ℕ}
    (a : ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = i} →₀ ℤ) →ₗ[ℤ] R)
    (q : {q : criticalPoints 𝓘(ℝ, E) (-f) // manifoldMorseIndex 𝓘(ℝ, E) (-f) q = k}) :
    hf.signedCochainToNegChain R i k a q =
      if hq : manifoldMorseIndex 𝓘(ℝ, E) f q.val = i then
        a (Finsupp.single ⟨⟨q.val.val, by simpa using q.val.property⟩, hq⟩ 1) *
          (((-1 : ℤ) ^ (i + 1).choose 2 : ℤ) : R)
      else 0 :=
  (rfl)

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- When `i + k = n`, the coefficient at `q` of the chain of `-f` associated with a cochain `a` of
`f` of index `i` is `a q * (-1) ^ ((i + 1).choose 2)`, with `q` read as a critical point of `f` of
index `i` through `TauCeti.IsMorse.criticalPointsIndexNegEquiv`. -/
theorem signedCochainToNegChain_apply_of_add_eq {i k : ℕ} (hik : i + k = finrank ℝ E)
    (a : ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = i} →₀ ℤ) →ₗ[ℤ] R)
    (q : {q : criticalPoints 𝓘(ℝ, E) (-f) // manifoldMorseIndex 𝓘(ℝ, E) (-f) q = k}) :
    hf.signedCochainToNegChain R i k a q =
      a (Finsupp.single (hf.criticalPointsIndexNegEquiv ((add_comm k i).trans hik) q) 1) *
        (((-1 : ℤ) ^ (i + 1).choose 2 : ℤ) : R) := by
  rw [signedCochainToNegChain_apply]
  split_ifs with hq
  · -- Both are `q`, read as a critical point of index `i` for `f`.
    congr 3
    ext
    simp
  · exact absurd
      (by simpa using (hf.criticalPointsIndexNegEquiv ((add_comm k i).trans hik) q).property) hq

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Outside complementary degrees, a cochain of `f` gives the zero chain of `-f`: no critical
point has index `k` for `-f` and index `i` for `f` unless `i + k = n`. -/
theorem signedCochainToNegChain_eq_zero {i k : ℕ} (hik : i + k ≠ finrank ℝ E) :
    hf.signedCochainToNegChain R i k = 0 := by
  ext a q
  rw [signedCochainToNegChain_apply]
  split_ifs with hq
  · have := (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
        (by simpa using q.val.property)).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
    exact absurd (by rw [← this, q.property, hq, add_comm]) hik
  · rfl

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **Cochains of `f` are chains of `-f`.** In complementary degrees `i + k = n`, reading an
integral cochain of `f` of index `i` with values in `R` as a chain of `-f` of index `k` is an
isomorphism. -/
theorem bijective_signedCochainToNegChain {i k : ℕ} (hik : i + k = finrank ℝ E) :
    Function.Bijective (hf.signedCochainToNegChain R i k) := by
  have := hf.neg.finite_criticalPoints.to_subtype
  set e := hf.criticalPointsIndexNegEquiv ((add_comm k i).trans hik)
  have hε : (((-1 : ℤ) ^ (i + 1).choose 2 : ℤ) : R) * (((-1 : ℤ) ^ (i + 1).choose 2 : ℤ) : R) =
      1 := by
    rw [← Int.cast_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, Int.cast_one]
  refine ⟨fun a b hab ↦ Finsupp.lhom_ext' fun p ↦ LinearMap.ext_ring ?_, fun c ↦ ?_⟩
  · -- The values of `a` and `b` at `p` are recovered from the coefficients at `p` read as a
    -- critical point of `-f`, since the sign squares to `1`.
    have h := DFunLike.congr_fun hab (e.symm p)
    rw [signedCochainToNegChain_apply_of_add_eq hf hik,
      signedCochainToNegChain_apply_of_add_eq hf hik, e.apply_symm_apply] at h
    simpa only [LinearMap.comp_apply, Finsupp.lsingle_apply, mul_assoc, hε, mul_one] using
      congrArg (· * (((-1 : ℤ) ^ (i + 1).choose 2 : ℤ) : R)) h
  · -- The cochain with values `c q * (-1) ^ ((i + 1).choose 2)` is sent to `c`.
    refine ⟨Finsupp.linearCombination ℤ
      fun p ↦ c (e.symm p) * (((-1 : ℤ) ^ (i + 1).choose 2 : ℤ) : R), Finsupp.ext fun q ↦ ?_⟩
    rw [signedCochainToNegChain_apply_of_add_eq hf hik, Finsupp.linearCombination_single, one_smul,
      e.symm_apply_apply, mul_assoc, hε, mul_one]

end IsMorse

/-! ### The coboundary of `f` is the boundary of `-f` -/

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} (𝔬 : MorseOrientation f X) (hf : IsMorse 𝓘(ℝ, E) f)
  (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (Module.finrank ℝ E))) {R : Type v} [Ring R]

/-- **The coboundary of `f` is the boundary of `-f`.** For the dual orientation data, reading
integral cochains of `f` as chains of `-f` (`TauCeti.IsMorse.signedCochainToNegChain`) carries the
Morse coboundary `a ↦ a ∘ ∂` of `f` from index `i` to index `i + 1` to the Morse boundary of `-f`
from index `k + 1` to index `k`. Both count the trajectories of `X` between critical points of
index `i + 1` and `i` for `f` with their signs: the sign `(-1) ^ ind_f p` of the transposition is
absorbed by the change of the sign `(-1) ^ ((i + 1).choose 2)` from `i` to `i + 1`. -/
theorem IsMorseSmale.signedCochainToNegChain_comp_signedMorseBoundaryAt (hMS : hX.IsMorseSmale)
    (i k : ℕ)
    (a : ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = i} →₀ ℤ) →ₗ[ℤ] R) :
    hf.signedCochainToNegChain R (i + 1) k (a ∘ₗ hX.signedMorseBoundaryAt 𝔬 hf ℤ i) =
      (hX.neg hf).signedMorseBoundaryAt (𝔬.dual hX hf oM) hf.neg R k
        (hf.signedCochainToNegChain R i (k + 1) a) := by
  by_cases hik : i + (k + 1) = finrank ℝ E
  · have := hf.finite_criticalPoints.to_subtype
    have := hf.neg.finite_criticalPoints.to_subtype
    have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
    have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) (-f))
    ext p
    set P := hf.criticalPointsIndexNegEquiv (j := k) (k := i + 1) (by omega) p
    set e := hf.criticalPointsIndexNegEquiv (j := k + 1) (k := i) (by omega)
    have hP : manifoldMorseIndex 𝓘(ℝ, E) f (p : M) = i + 1 := by
      rw [← hf.coe_criticalPointsIndexNegEquiv_apply (j := k) (k := i + 1) (by omega) p]
      exact P.property
    -- The value of `a` on the boundary of `P` is the sum of its values at the critical points `q`
    -- of index `i` weighted by the boundary coefficients from `P` to `q`.
    have ha : a (hX.signedMorseBoundaryAt 𝔬 hf ℤ i (Finsupp.single P 1)) =
        ∑ q, a (Finsupp.single q 1) * (hX.signedMorseBoundaryCoeff 𝔬 P q : R) := by
      conv_lhs => rw [← Finsupp.univ_sum_single (hX.signedMorseBoundaryAt 𝔬 hf ℤ i _)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [signedMorseBoundaryAt_single_apply, one_mul, Int.cast_id, ← Finsupp.smul_single_one,
        map_zsmul, zsmul_eq_mul']
    rw [hf.signedCochainToNegChain_apply_of_add_eq (by omega), LinearMap.comp_apply, ha,
      signedMorseBoundaryAt_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _, Finset.sum_mul]
    refine Fintype.sum_equiv e.symm _ _ fun q ↦ ?_
    rw [hf.signedCochainToNegChain_apply_of_add_eq (by omega), e.apply_symm_apply,
      hMS.signedMorseBoundaryCoeff_dual 𝔬 hf oM, mul_assoc, mul_assoc, ← Int.cast_mul,
      ← Int.cast_mul]
    refine congrArg (_ * ·) (congrArg Int.cast ?_)
    -- What remains is an identity of integers.
    have hP' : Set.equivOfEq criticalPoints_neg p.val = P.val := by
      ext
      simp [P]
    have hq' : Set.equivOfEq criticalPoints_neg (e.symm q).val = q.val := by
      ext
      simp [e]
    rw [hP', hq', hP, Nat.choose_succ_succ' (i + 1), Nat.choose_one_right, pow_add]
    ring
  · rw [hf.signedCochainToNegChain_eq_zero (by omega), hf.signedCochainToNegChain_eq_zero hik,
      LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

variable {𝔬 hf} (hMS : hX.IsMorseSmale)
  (hsq : hX.signedMorseBoundary 𝔬 hf ℤ ∘ₗ hX.signedMorseBoundary 𝔬 hf ℤ = 0)

/-- **Reading cochains of `f` as chains of `-f` commutes with the differentials.** For the dual
orientation data, it intertwines the coboundary of the integral Morse cochain complex of `f` with
coefficients in `R` from index `i` to index `i + 1` with the differential of the Morse chain complex
of `-f` with coefficients in `R` from index `k + 1` to index `k`. The maps are bijective only in
complementary degrees (`TauCeti.IsMorse.bijective_signedCochainToNegChain`). -/
theorem IsMorseSmale.signedMorseCochainComplex_d_comp_ofHom_signedCochainToNegChain (i k : ℕ) :
    (hX.signedMorseCochainComplex 𝔬 hf R hsq).d i (i + 1) ≫
        ModuleCat.ofHom (hf.signedCochainToNegChain R (i + 1) k) =
      ModuleCat.ofHom (hf.signedCochainToNegChain R i (k + 1)) ≫
        ((hX.neg hf).signedMorseComplex (𝔬.dual hX hf oM) hf.neg R
          (hMS.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_of_int 𝔬 hf oM hsq
            R)).d (k + 1) k := by
  rw [signedMorseComplex_d, signedMorseCochainComplex_d]
  ext a : 2
  exact hMS.signedCochainToNegChain_comp_signedMorseBoundaryAt 𝔬 hf oM i k a

/-- **Poincaré duality for Morse (co)homology.** On a manifold of dimension `n` oriented by `oM`,
for `i + k = n`, reading integral cochains of `f` as chains of `-f` identifies the Morse cohomology
of `f` with coefficients in `R` in degree `i` with the Morse homology of `-f`, for the
pseudo-gradient `-X` and the dual orientation data, with coefficients in `R` in degree `k`.
This is conditional on the hypothesis `hsq` that the integral Morse boundary of `f` squares to
zero, which builds both complexes and is not proved in the library yet. -/
noncomputable def IsMorseSmale.signedMorseCohomologyEquivNegHomology {i k : ℕ}
    (hik : i + k = finrank ℝ E) :
    (hX.signedMorseCochainComplex 𝔬 hf R hsq).homology i ≃ₗ[R]
      ((hX.neg hf).signedMorseComplex (𝔬.dual hX hf oM) hf.neg R
        (hMS.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_of_int 𝔬 hf oM hsq
          R)).homology k :=
  ((hX.signedMorseCochainComplex 𝔬 hf R hsq).homologyIsoOfAntidiagonal
    ((hX.neg hf).signedMorseComplex (𝔬.dual hX hf oM) hf.neg R
      (hMS.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_of_int 𝔬 hf oM hsq R))
    (fun i k ↦ ModuleCat.ofHom (hf.signedCochainToNegChain R i k))
    (hMS.signedMorseCochainComplex_d_comp_ofHom_signedCochainToNegChain oM hsq)
    (fun _ _ hik ↦ (ConcreteCategory.isIso_iff_bijective _).2
      (hf.bijective_signedCochainToNegChain (R := R) hik))
    -- The cochains of `f` and the chains of `-f` of index `n + 1` vanish.
    (isZero_signedMorseCochainComplex_X_of_finrank_lt (R := R) hsq (by omega))
    (isZero_signedMorseComplex_X_of_finrank_lt
      (hMS.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_of_int 𝔬 hf oM hsq R)
      (by omega)) hik).toLinearEquiv

/-- A cocycle of `f` of index `i`, read as a chain of `-f` of index `k`, is a cycle of `-f`. -/
theorem IsMorseSmale.iCycles_comp_ofHom_signedCochainToNegChain_comp_d (i k : ℕ) :
    ((hX.signedMorseCochainComplex 𝔬 hf R hsq).iCycles i ≫
        ModuleCat.ofHom (hf.signedCochainToNegChain R i k)) ≫
      ((hX.neg hf).signedMorseComplex (𝔬.dual hX hf oM) hf.neg R
        (hMS.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_of_int 𝔬 hf oM hsq
          R)).d k (k - 1) = 0 :=
  (hX.signedMorseCochainComplex 𝔬 hf R hsq).iCycles_comp_comp_d_of_comm
    ((hX.neg hf).signedMorseComplex (𝔬.dual hX hf oM) hf.neg R
      (hMS.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_of_int 𝔬 hf oM hsq R))
    (fun i k ↦ ModuleCat.ofHom (hf.signedCochainToNegChain R i k))
    (hMS.signedMorseCochainComplex_d_comp_ofHom_signedCochainToNegChain oM hsq) i k

/-- **Poincaré duality for Morse (co)homology on classes.** For `i + k = n`, the identification of
the Morse cohomology of `f` with the Morse homology of `-f` sends the class of a cocycle of `f` to
the class of the same cocycle read as a cycle of `-f`. -/
theorem IsMorseSmale.signedMorseCohomologyEquivNegHomology_homologyπ {i k : ℕ}
    (hik : i + k = finrank ℝ E) (x : (hX.signedMorseCochainComplex 𝔬 hf R hsq).cycles i) :
    hMS.signedMorseCohomologyEquivNegHomology oM hsq hik
        ((hX.signedMorseCochainComplex 𝔬 hf R hsq).homologyπ i x) =
      ((hX.neg hf).signedMorseComplex (𝔬.dual hX hf oM) hf.neg R
        (hMS.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_of_int 𝔬 hf oM hsq
          R)).homologyπ k
        (((hX.neg hf).signedMorseComplex (𝔬.dual hX hf oM) hf.neg R
          (hMS.signedMorseBoundary_dual_comp_signedMorseBoundary_dual_eq_zero_of_int 𝔬 hf oM hsq
            R)).liftCycles
          ((hX.signedMorseCochainComplex 𝔬 hf R hsq).iCycles i ≫
            ModuleCat.ofHom (hf.signedCochainToNegChain R i k))
          (k - 1) (by rcases k with _ | k <;> simp)
          (hMS.iCycles_comp_ofHom_signedCochainToNegChain_comp_d oM hsq i k) x) := by
  rw [signedMorseCohomologyEquivNegHomology, Iso.toLinearEquiv_apply,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom (CochainComplex.homologyπ_comp_homologyIsoOfAntidiagonal_hom
    _ _ _ _ _ _ _ hik) x

end IsAdaptedPseudoGradient

end TauCeti

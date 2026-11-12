/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Localization.Submodule

import Mathlib.RingTheory.Localization.Integer
import TauCeti.RingTheory.DedekindDomain.PseudoBasis

/-!
# Integral points and Steinitz pseudo-bases of number-field subspaces

For a `K`-subspace `W` of `ι → K`, the tuples in `ι → 𝓞 K` whose image in `ι → K` belongs to `W`
form a saturated `𝓞 K`-submodule `W.integerPoints` (`W ∩ (𝓞 K)^ι`). When `K` is a number field and
`ι` is finite, `W.integerPoints` need not be free over `𝓞 K`, but Steinitz's structure theorem
(`Submodule.exists_pseudoBasis`) decomposes it as a direct sum `⊕ k, J k • b k` for a `K`-basis `b`
of `W` and nonzero ideals `J k` of `𝓞 K` (`Submodule.exists_pseudoBasis_integerPoints`).

## Main definitions

* `Submodule.integerPoints W`: the `𝓞 K`-submodule `W ∩ (𝓞 K)^ι` of `ι → 𝓞 K`.
* `Submodule.IsIntegerPseudoBasis W b J`: the predicate that a `K`-basis `b` of `W` and ideals `J`
  of `𝓞 K` form a Steinitz pseudo-basis of `W.integerPoints`.

## Main results

* `Submodule.mem_integerPoints_of_smul_mem`: `W.integerPoints` is saturated in `ι → 𝓞 K`.
* `Submodule.IsIntegerPseudoBasis.coe_smul_basis_mem_range`: scaling `b k` by an element of `J k`
  gives a vector in `W` with ambient coordinates in `𝓞 K`.
* `Submodule.exists_pseudoBasis_integerPoints`: `W` admits a `K`-basis `b` and nonzero ideals `J k`
  of `𝓞 K` satisfying `W.IsIntegerPseudoBasis b J`.
* `Matrix.integerPoints_ker_mulVecLin`: the integral points of the `K`-kernel of an `𝓞 K`-matrix
  are its `𝓞 K`-kernel.

## References

* E. Steinitz, *Rechteckige Systeme und Moduln in algebraischen Zahlkörpern*, Math. Ann. **71**
  (1911), 328–354.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §2.8 and Appendix C.2.
-/

public section

open Module NumberField Set
open scoped nonZeroDivisors

namespace Submodule

variable {K : Type*} [Field K] {ι : Type*}

/-- The integral points of a `K`-subspace `W` of `ι → K`: the tuples `z : ι → 𝓞 K` whose image in
`ι → K` lies in `W`. -/
def integerPoints (W : Submodule K (ι → K)) : Submodule (𝓞 K) (ι → 𝓞 K) :=
  (W.restrictScalars (𝓞 K)).comap ((Algebra.linearMap (𝓞 K) K).compLeft ι)

/-- A tuple in `ι → 𝓞 K` is an integral point of `W` when its image in `ι → K` lies in `W`. -/
@[simp]
theorem mem_integerPoints {W : Submodule K (ι → K)} {z : ι → 𝓞 K} :
    z ∈ W.integerPoints ↔ (fun i ↦ (z i : K)) ∈ W :=
  Iff.rfl

/-- The zero subspace has only the zero integral point. -/
@[simp]
theorem integerPoints_bot : (⊥ : Submodule K (ι → K)).integerPoints = ⊥ := by
  ext z
  simp [funext_iff]

/-- The whole space `ι → K` has all of `ι → 𝓞 K` as integral points. -/
@[simp]
theorem integerPoints_top : (⊤ : Submodule K (ι → K)).integerPoints = ⊤ := by
  ext z
  simp

/-- `Submodule.integerPoints` is monotone in the subspace. -/
@[gcongr]
theorem integerPoints_mono {W₁ W₂ : Submodule K (ι → K)} (h : W₁ ≤ W₂) :
    W₁.integerPoints ≤ W₂.integerPoints :=
  fun _ hz ↦ h hz

/-- The integral points of `W` form a saturated `𝓞 K`-submodule of `ι → 𝓞 K`: if a nonzero
`𝓞 K`-multiple of `z` lies in `W.integerPoints`, then so does `z`. -/
theorem mem_integerPoints_of_smul_mem {W : Submodule K (ι → K)} {c : 𝓞 K} {z : ι → 𝓞 K}
    (hc : c ≠ 0) (h : c • z ∈ W.integerPoints) : z ∈ W.integerPoints := by
  rw [mem_integerPoints] at h ⊢
  have hcK : (c : K) ≠ 0 := by simpa using hc
  convert W.smul_mem (c : K)⁻¹ h using 1
  ext i
  simp [inv_mul_cancel_left₀ hcK]

/-- `(b, J)` is a Steinitz pseudo-basis for the integral points of `W`: a vector `w ∈ W` has all
coordinates in `𝓞 K` if and only if its `k`-th `b`-coordinate lies in `J k` for every `k`. -/
def IsIntegerPseudoBasis (W : Submodule K (ι → K)) {κ : Type*} (b : Basis κ K W)
    (J : κ → Ideal (𝓞 K)) : Prop :=
  ∀ w : W, (∀ i, (w : ι → K) i ∈ range (algebraMap (𝓞 K) K)) ↔
    ∀ k, b.repr w k ∈ IsLocalization.coeSubmodule K (J k)

/-- Under `W.IsIntegerPseudoBasis b J`, integrality of the ambient coordinates of `w ∈ W` is
equivalent to membership of `b.repr w k` in `J k` for every `k`. -/
theorem IsIntegerPseudoBasis.mem_coeSubmodule_iff {W : Submodule K (ι → K)} {κ : Type*}
    {b : Basis κ K W} {J : κ → Ideal (𝓞 K)} (hW : W.IsIntegerPseudoBasis b J) (w : W) :
    (∀ i, (w : ι → K) i ∈ range (algebraMap (𝓞 K) K)) ↔
      ∀ k, b.repr w k ∈ IsLocalization.coeSubmodule K (J k) :=
  hW w

/-- Scaling a pseudo-basis vector `b k` by a scalar `c` in `J k` produces a vector in `W` whose
ambient coordinates all lie in `𝓞 K`. -/
theorem IsIntegerPseudoBasis.coe_smul_basis_mem_range {W : Submodule K (ι → K)} {κ : Type*}
    {b : Basis κ K W} {J : κ → Ideal (𝓞 K)} (hW : W.IsIntegerPseudoBasis b J) {k : κ} {c : K}
    (hc : c ∈ IsLocalization.coeSubmodule K (J k)) (i : ι) :
    c * (b k : ι → K) i ∈ range (algebraMap (𝓞 K) K) := by
  simpa [Algebra.smul_def] using
    (hW.mem_coeSubmodule_iff (c • b k)).2 (b.repr_smul_self_mem_coeSubmodule J hc) i

/-- **Existence of a pseudo-basis for the integral points of a subspace.** Any `K`-subspace `W` of
`ι → K` over a number field admits a `K`-basis `b` indexed by `Fin (finrank K W)` and nonzero ideals
`J k` of `𝓞 K` satisfying `W.IsIntegerPseudoBasis b J`. -/
theorem exists_pseudoBasis_integerPoints [NumberField K] [Finite ι] (W : Submodule K (ι → K)) :
    ∃ (b : Basis (Fin (finrank K W)) K W) (J : Fin (finrank K W) → Ideal (𝓞 K)),
      (∀ k, J k ≠ ⊥) ∧ W.IsIntegerPseudoBasis b J := by
  classical
  cases nonempty_fintype ι
  -- View `W ∩ (𝓞 K)^ι` as an `𝓞 K`-submodule `M` of `W`.
  let φ : W.integerPoints →ₗ[𝓞 K] W :=
    { toFun z := ⟨fun i ↦ ((z : ι → 𝓞 K) i : K), z.2⟩
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext i; simp [Algebra.smul_def] }
  set M : Submodule (𝓞 K) W := LinearMap.range φ with hM
  have hmemM (w : W) : w ∈ M ↔ ∀ i, (w : ι → K) i ∈ range (algebraMap (𝓞 K) K) := by
    refine ⟨fun ⟨z, hz⟩ i ↦ hz ▸ ⟨(z : ι → 𝓞 K) i, rfl⟩, fun hw ↦ ?_⟩
    choose z hz using hw
    exact ⟨⟨z, by rw [mem_integerPoints]; convert w.2 with i; exact hz i⟩,
      Subtype.ext (funext hz)⟩
  have hFG : M.FG := by
    rw [hM, LinearMap.range_eq_map]
    exact (IsNoetherian.noetherian ⊤).map φ
  have hspan : span K (M : Set W) = ⊤ := eq_top_iff.2 fun w _ ↦ by
    obtain ⟨⟨d, hd⟩, hdw⟩ := IsLocalization.exist_integer_multiples (𝓞 K)⁰ Finset.univ (w : ι → K)
    have hd0 : algebraMap (𝓞 K) K d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.ne_zero hd)
    have hdwM : d • w ∈ M := (hmemM (d • w)).2 fun i ↦ by
      simpa [Algebra.smul_def, IsLocalization.IsInteger] using hdw i (Finset.mem_univ i)
    have hw : w = (algebraMap (𝓞 K) K d)⁻¹ • (d • w) := by
      rw [← algebraMap_smul K d w, inv_smul_smul₀ hd0]
    exact hw ▸ smul_mem _ _ (subset_span hdwM)
  obtain ⟨b, J, hJ, hb⟩ := M.exists_pseudoBasis (K := K) (ι := Fin (finrank K W)) hFG hspan
    (Nat.card_fin _)
  exact ⟨b, J, hJ, fun w ↦ (hmemM w).symm.trans (hb w)⟩

end Submodule

namespace Matrix

open scoped Matrix NumberField

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- The integral points of the `K`-kernel of an `𝓞 K`-matrix are precisely its `𝓞 K`-kernel. -/
@[simp]
theorem integerPoints_ker_mulVecLin {m : Type*} (A : Matrix m ι (𝓞 K)) :
    (LinearMap.ker (A.map (algebraMap (𝓞 K) K)).mulVecLin).integerPoints =
      LinearMap.ker A.mulVecLin := by
  ext z
  simp only [Submodule.mem_integerPoints, LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff,
    Pi.zero_apply]
  refine forall_congr' fun i ↦ ?_
  have hcast : (((A *ᵥ z) i : 𝓞 K) : K) =
      (A.map (algebraMap (𝓞 K) K) *ᵥ fun j ↦ (z j : K)) i :=
    RingHom.map_mulVec (algebraMap (𝓞 K) K) A z i
  rw [← hcast, NumberField.RingOfIntegers.coe_eq_zero_iff]

end Matrix

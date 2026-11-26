/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import TauCeti.Analysis.Normed.Module.Seminorm.Word
public import TauCeti.Data.List.MonomialWord

/-!
# Sobolev seminorms along a family of operators

Let `f : M →ₗ[𝕜] F` be a linear map from a module `M` to a normed space `F`, and let
`D₁, …, D_m` be operators on `M`. For an exponent vector `α : Fin m → ℕ` write
`D^α = D₁^{α₁} ∘ ⋯ ∘ D_m^{α_m}` for the ordered monomial. The *Sobolev seminorm* of order `k` is

`Q^D_k(x) = (∑_{|α| ≤ k} ‖f(D^α x)‖²)^{1/2}`,

summed over the ordered monomials of degree at most `k`. Every ordered monomial is a word, and the
`ℓ²` norm of a finite family is at most its `ℓ¹` norm, so `Q^D_k` is bounded by the word seminorm
`P^D_k(x) = ∑_{|w| ≤ k} ‖f(D_w x)‖` of `Seminorm.endWordSeminorm`. Conversely, if the operator
`D_w` of every word of length at most `k` is a `𝕜`-combination of the ordered monomials `D^α` of
degree at most `k`, then `P^D_k ≤ C_k Q^D_k` by the triangle inequality.

For the smooth vectors of a Lie group representation and `D i = dπ(X_i)` these are the Sobolev
seminorms `ContRepresentation.sobolevSeminorm` of Bernstein–Krötz, and the spanning hypothesis is
the spanning half of the Poincaré–Birkhoff–Witt theorem.

## Main definitions

* `TauCeti.SobolevIndex m k`: the exponent vectors `α : Fin m → ℕ` with `|α| ≤ k`.
* `Seminorm.endSobolevSeminorm f D k`: the Sobolev seminorm `Q^D_k`.

## Main results

* `TauCeti.exists_sobolevIndex_monomialWord_eq`: a sorted word of length at most `k` is the
  ordered monomial word `TauCeti.monomialWord α` of an index `α` in `SobolevIndex m k`.
* `Seminorm.endSobolevSeminorm_apply`: the Sobolev seminorm as a square root of a sum of squares.
* `Seminorm.norm_apply_le_endSobolevSeminorm`: `‖f(D^α x)‖ ≤ Q^D_k(x)` for `|α| ≤ k`.
* `Seminorm.endSobolevSeminorm_le_endWordSeminorm`: `Q^D_k ≤ P^D_k`.
* `Seminorm.exists_endWordSeminorm_le_mul_endSobolevSeminorm`: `P^D_k ≤ C_k Q^D_k` when the
  operators of words of length at most `k` lie in the span of the ordered monomials.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §§2.1–2.4.
-/

public section

noncomputable section

namespace TauCeti

/-! ### Ordered monomials -/

variable {m : ℕ}

/-- The exponent vectors `α : Fin m → ℕ` of total degree `|α| = ∑ i, α i ≤ k`, with entries
recorded in `Fin (k + 1)` so that they form a finite type. -/
abbrev SobolevIndex (m k : ℕ) : Type :=
  {α : Fin m → Fin (k + 1) // ∑ i, (α i : ℕ) ≤ k}

/-- The exponent vector in `ℕ` of an index in `SobolevIndex m k`. -/
def SobolevIndex.exponent {k : ℕ} (α : SobolevIndex m k) (i : Fin m) : ℕ :=
  α.val i

/-- The `i`-th entry of the exponent vector of `α`. -/
@[simp]
theorem SobolevIndex.exponent_apply {k : ℕ} (α : SobolevIndex m k) (i : Fin m) :
    α.exponent i = α.val i :=
  (rfl)

/-- An index in `SobolevIndex m k` is determined by its exponent vector. -/
theorem SobolevIndex.exponent_injective {k : ℕ} :
    Function.Injective (SobolevIndex.exponent (m := m) (k := k)) := fun _ _ h ↦
  Subtype.ext (funext fun i ↦ Fin.ext (congrFun h i))

/-- The ordered monomial word of an index in `SobolevIndex m k`, as a word of length at most
`k`. -/
def SobolevIndex.toBoundedWord {k : ℕ} (α : SobolevIndex m k) : BoundedWord (Fin m) k :=
  ⟨⟨(monomialWord α.exponent).length, by
      rw [length_monomialWord]; exact Nat.lt_succ_of_le α.property⟩,
    (monomialWord α.exponent).get⟩

/-- The word `SobolevIndex.toBoundedWord α` spells the ordered monomial word of `α`. -/
@[simp]
theorem SobolevIndex.ofFn_toBoundedWord {k : ℕ} (α : SobolevIndex m k) :
    List.ofFn α.toBoundedWord.2 = monomialWord α.exponent :=
  List.ofFn_get _

/-- Distinct ordered monomials give distinct words. -/
theorem SobolevIndex.toBoundedWord_injective {k : ℕ} :
    Function.Injective (SobolevIndex.toBoundedWord (m := m) (k := k)) := fun α β h ↦ by
  have := congrArg (fun w : BoundedWord (Fin m) k ↦ List.ofFn w.2) h
  simp only [SobolevIndex.ofFn_toBoundedWord] at this
  exact SobolevIndex.exponent_injective (monomialWord_injective this)

/-- A sorted word of length at most `k` is the ordered monomial word of an index in
`SobolevIndex m k`. -/
theorem exists_sobolevIndex_monomialWord_eq {k : ℕ} {w : List (Fin m)}
    (hw : w.Pairwise (· ≤ ·)) (hk : w.length ≤ k) :
    ∃ α : SobolevIndex m k, monomialWord α.exponent = w := by
  have hsum : ∑ i, w.count i = w.length := by
    rw [← length_monomialWord, monomialWord_count hw]
  refine ⟨⟨fun i ↦ ⟨w.count i, Nat.lt_succ_of_le (List.count_le_length.trans hk)⟩, ?_⟩, ?_⟩
  · simpa [hsum] using hk
  · refine (congrArg monomialWord (funext fun i ↦ ?_)).trans (monomialWord_count hw)
    simp only [SobolevIndex.exponent_apply]

end TauCeti

namespace Seminorm

open TauCeti

/-! ### The Sobolev seminorms along a family of operators -/

variable {𝕜 M F : Type*} [NormedField 𝕜] [AddCommGroup M] [Module 𝕜 M]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {m : ℕ}

/-- The Sobolev seminorm `Q^D_k(x) = (∑_{|α| ≤ k} ‖f(D^α x)‖²)^{1/2}` along a family `D` of
operators, summed over the ordered monomials `D^α = D₁^{α₁} ∘ ⋯ ∘ D_m^{α_m}` of degree at most
`k`: the norm of the vector `(f(D^α x))_{|α| ≤ k}` in the `ℓ²` product. For the smooth vectors and
`D i = dπ(X_i)` this is `ContRepresentation.sobolevSeminorm`. -/
def endSobolevSeminorm (f : M →ₗ[𝕜] F) (D : Fin m → Module.End 𝕜 M) (k : ℕ) : Seminorm 𝕜 M :=
  (normSeminorm 𝕜 (PiLp 2 fun _ : SobolevIndex m k ↦ F)).comp
    ((WithLp.linearEquiv 2 𝕜 _).symm.toLinearMap ∘ₗ
      LinearMap.pi fun α ↦ f ∘ₗ ((monomialWord α.exponent).map D).prod)

/-- The Sobolev seminorm along a family of operators as an explicit square root of a sum of
squares. -/
theorem endSobolevSeminorm_apply (f : M →ₗ[𝕜] F) (D : Fin m → Module.End 𝕜 M) (k : ℕ) (x : M) :
    endSobolevSeminorm f D k x =
      √(∑ α : SobolevIndex m k, ‖f (((monomialWord α.exponent).map D).prod x)‖ ^ 2) := by
  simp [endSobolevSeminorm, PiLp.norm_eq_of_L2]

/-- The term of an ordered monomial is bounded by the Sobolev seminorm:
`‖f(D^α x)‖ ≤ Q^D_k(x)` for `|α| ≤ k`. -/
theorem norm_apply_le_endSobolevSeminorm (f : M →ₗ[𝕜] F) (D : Fin m → Module.End 𝕜 M) {k : ℕ}
    (α : SobolevIndex m k) (x : M) :
    ‖f (((monomialWord α.exponent).map D).prod x)‖ ≤ endSobolevSeminorm f D k x := by
  rw [endSobolevSeminorm_apply]
  exact Real.le_sqrt_of_sq_le (Finset.single_le_sum
    (f := fun α : SobolevIndex m k ↦ ‖f (((monomialWord α.exponent).map D).prod x)‖ ^ 2)
    (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ α))

/-- **The Sobolev seminorm is bounded by the word seminorm**, `Q^D_k ≤ P^D_k`: every ordered
monomial is a word, and the `ℓ²` norm of a finite family is at most its `ℓ¹` norm. -/
theorem endSobolevSeminorm_le_endWordSeminorm (f : M →ₗ[𝕜] F) (D : Fin m → Module.End 𝕜 M)
    (k : ℕ) (x : M) :
    endSobolevSeminorm f D k x ≤ ((normSeminorm 𝕜 F).comp f).endWordSeminorm D k x := by
  classical
  set b : BoundedWord (Fin m) k → ℝ := fun w ↦ ‖f (((List.ofFn w.2).map D).prod x)‖
  have hb : ∀ α : SobolevIndex m k,
      ‖f (((monomialWord α.exponent).map D).prod x)‖ = b α.toBoundedWord := fun α ↦ by
    simp only [b, SobolevIndex.ofFn_toBoundedWord]
  have hsum : ∑ α : SobolevIndex m k, b α.toBoundedWord ≤ ∑ w, b w :=
    Finset.sum_le_sum_of_injOn SobolevIndex.toBoundedWord
      SobolevIndex.toBoundedWord_injective.injOn (Finset.subset_univ _) (fun _ _ ↦ le_rfl)
      fun _ _ _ ↦ norm_nonneg _
  rw [endSobolevSeminorm_apply, endWordSeminorm_apply, Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _, ?_⟩
  simp_rw [hb]
  calc ∑ α : SobolevIndex m k, b α.toBoundedWord ^ 2
    _ ≤ (∑ α : SobolevIndex m k, b α.toBoundedWord) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ ↦ norm_nonneg _
    _ ≤ (∑ w, b w) ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hsum 2

/-- **The word seminorm is bounded by a multiple of the Sobolev seminorm.** If the operator
`D_w` of every word `w` of length at most `k` is a `𝕜`-combination of the ordered monomials `D^α`
of degree at most `k`, then there is `C_k` with `P^D_k ≤ C_k Q^D_k`. -/
theorem exists_endWordSeminorm_le_mul_endSobolevSeminorm (f : M →ₗ[𝕜] F)
    (D : Fin m → Module.End 𝕜 M) {k : ℕ}
    (hD : ∀ w : List (Fin m), w.length ≤ k → (w.map D).prod ∈ Submodule.span 𝕜
      (Set.range fun α : SobolevIndex m k ↦ ((monomialWord α.exponent).map D).prod)) :
    ∃ C : ℝ, ∀ x : M,
      ((normSeminorm 𝕜 F).comp f).endWordSeminorm D k x ≤ C * endSobolevSeminorm f D k x := by
  classical
  choose c hc using fun w : BoundedWord (Fin m) k ↦
    (Submodule.mem_span_range_iff_exists_fun 𝕜).1
      (hD (List.ofFn w.2) ((List.length_ofFn).trans_le (Nat.lt_succ_iff.1 w.1.isLt)))
  refine ⟨∑ w, ∑ α, ‖c w α‖, fun x ↦ ?_⟩
  rw [endWordSeminorm_apply, Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ ↦ ?_
  rw [← hc w, Finset.sum_mul, comp_apply, coe_normSeminorm, LinearMap.sum_apply, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ ↦ ?_)
  rw [LinearMap.smul_apply, map_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_apply_le_endSobolevSeminorm f D α x) (norm_nonneg _)

end Seminorm

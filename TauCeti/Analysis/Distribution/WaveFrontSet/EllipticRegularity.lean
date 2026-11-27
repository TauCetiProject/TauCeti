/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.LineDeriv
public import TauCeti.Analysis.Distribution.WaveFrontSet.SingularSupport
import TauCeti.Analysis.Distribution.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.ProdInner
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
import TauCeti.Analysis.Calculus.ContDiff.Matrix
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Normed.Module.Cone

/-!
# Microlocal elliptic regularity for differential operators

Let `P = ∑ i ∈ s, c i a i ∂^(m i)` be a linear differential operator with smooth real coefficient
functions `a i`, complex constants `c i` and iterated directional derivatives `∂^(m i)` of orders
`k i ≤ M`; writing a smooth complex coefficient as `u + i v`, this covers every operator with
smooth complex coefficients. Its principal symbol of order `M` at `x`, in the geometric convention
without factors of `i`, is the homogeneous polynomial

`σ_M(P)(x, ξ) = ∑ i ∈ s with k i = M, c i a i(x) ∏ₗ ⟪m i l, ξ⟫`,

that is, `TauCeti.principalSymbol`: `TauCeti.constCoeffPrincipalSymbol` of the coefficients
`c i a i(x)` frozen at `x`. Its *characteristic set* `Char(P)` (`TauCeti.characteristicSet`)
consists of the points `(x, ξ)` with `ξ ≠ 0` and `σ_M(P)(x, ξ) = 0`; for constant coefficients
this is `TauCeti.constCoeffCharacteristicSet`. This file proves
**microlocal elliptic regularity**: at a noncharacteristic covector, `T` is as regular as `P T`,

`WF(T) ⊆ WF(P T) ∪ Char(P)`

(`Distribution.waveFrontSet_subset_waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_union`).
Together with the reverse microlocality `WF(P T) ⊆ WF(T)` of differential operators
(`Distribution.waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`), an operator
elliptic at every point of `Ω` satisfies `WF(P T) = WF(T)`, and hence has the same singular
support: `P T` is smooth on an open set exactly when `T` is. In particular such an operator is
hypoelliptic, and every distributional solution of `P T = 0` is a function smooth on `Ω`. The
constant-coefficient statements are the special case `a i = 1`, and the Laplacian is the basic
example (`Distribution.waveFrontSet_laplacianCLM`), for which this is Weyl's lemma.

The same holds for square systems `(P T) j = ∑ i, ∑ a ∈ s, c i j a g i j a ∂^(m a) (T i)` acting
on finitely many distributions `T i`: if the matrix of the principal symbols of the entries is
invertible at `(x, ξ)` and every `(P T) j` is microlocally smooth there, so is every `T i`
(`Distribution.IsMicrolocallySmoothAt.of_sum_sum_smul_smulLeftCLM_iteratedLineDerivOp`). This is
the form needed for operators between vector bundles, which are systems in local frames.
Ellipticity of a system is invertibility of its principal symbol matrix, not nonvanishing of its
entries, so the scalar statement cannot be applied entry by entry; the scalar statement is the
system with one component.

## The argument

Write `L(T, ψ)(η) = T (ψ e_η)` for the localized Fourier transform, and
`p(y, η) = ∑ a ∈ s, c a g a(y) ∏ₗ 2πi ⟪m a l, η⟫` for the full symbol of a scalar operator in the
frequency variable of Mathlib's Fourier transform. Moving the derivatives onto the cutoff,
`L(∂_v T, ψ) = 2πi ⟪v, η⟫ L(T, ψ) - L(T, ∂_v ψ)` and `L(g T, ψ) = L(T, g ψ)`, gives

`L(T, p(·, η) Ψ)(η) = L(P T, Ψ)(η) - ∑ a ∈ s, c a D_a(η)`,

where each error `D_a` only involves `L(T, ∂^β (g a Ψ))` for derivatives of `g a Ψ`, with one
power of `η` less than `p`. For a system, let `A(y, η)` be the matrix of the terms of order `M`
of the full symbols of the entries, `(2πi) ^ M` times the principal symbol matrix. Near a
noncharacteristic `(x, ξ)`, `|det A(y, η)| ≥ c (1 + ‖η‖) ^ (M r)`, with `r` the number of
components, for `y` near `x` and `η` in an open cone `Γ` around `ξ` outside a ball: the
determinant of the principal symbol matrix is homogeneous of degree `M r`
(`TauCeti.exists_nhds_cone_le_norm_of_continuous_of_homogeneous`). To estimate `L(T q, φ)(η)`
for a cutoff `φ`, apply the identity to the frequency-dependent cutoffs `Ψ j = (A⁻¹) j q φ`
(Hörmander I, proof of Theorem 8.3.1), obtained by multiplying `φ` by an entry of the adjugate of
`A` and dividing by its determinant, so that `∑ j, A i j Ψ j = δ_iq φ`
(`TestFunction.exists_sum_mul_eq_ite_of_forall_det_ne_zero`). Their derivatives are
`O((1 + ‖η‖) ^ (-M))`, and the terms of order less than `M` of the full symbols become errors one
power of `η` smaller. Since the cutoffs depend on `η`, every estimate is made uniform over the
cutoffs supported in a fixed compact set with bounded derivatives of some order: the polynomial
growth of the localized Fourier transform (`Distribution.exists_forall_norm_localFourier_le`) and
the rapid decay of `L((P T) j, Ψ)` on `Γ`
(`IsMicrolocallySmoothAt.exists_nhds_cone_forall_one_add_norm_pow_mul_norm_localFourier_le`, on one
cone for all `j` by `exists_nhds_cone_forall_forall_one_add_norm_pow_mul_norm_localFourier_le`).
If every `L(T i, φ)` is `O(B (1 + ‖η‖) ^ (k - d))` on `Γ` for the cutoffs `φ` whose derivatives
are bounded by `B`, the identity shows that it is `O(B (1 + ‖η‖) ^ (k - d - 1))`, and induction on
`d` gives rapid decay on `Γ`.

## Main definitions

* `TauCeti.constCoeffPrincipalSymbol s c m M`: the principal symbol `σ_M(P)` of order `M` of a
  constant-coefficient operator.
* `TauCeti.constCoeffCharacteristicSet s c m M`: its characteristic set `Char(P)`.
* `TauCeti.principalSymbol s b m M x`: the principal symbol of `P = ∑ i ∈ s, b i ∂^(m i)` with the
  coefficient functions `b i` frozen at `x`.
* `TauCeti.characteristicSet s b m M`: its characteristic set `Char(P)`.

## Main results

* `TauCeti.eventually_forall_constCoeffPrincipalSymbol_ne_zero`: for coefficients depending
  continuously on a point, ellipticity at a point holds at all nearby points.
* `TauCeti.constCoeffPrincipalSymbol_laplacian`: the principal symbol of the Laplacian is
  `‖ξ‖ ^ 2`.
* `TauCeti.exists_nhds_cone_le_norm_principalSymbol`: a principal symbol with
  continuous coefficients that does not vanish at `(x, ξ)` is bounded below by `c₀ ‖η‖ ^ M` for
  `y` near `x` and `η` in an open cone around `ξ`.
* `TauCeti.exists_mul_one_add_norm_pow_le_norm_sum_mul_prod`: on such a cone the full symbol
  `∑ i ∈ s, b i y ∏ₗ 2πi ⟪m i l, η⟫`, lower-order terms included, is bounded below by a multiple
  of `(1 + ‖η‖) ^ M` outside a ball.
* `Distribution.IsMicrolocallySmoothAt.of_sum_sum_smul_smulLeftCLM_iteratedLineDerivOp` and
  its wave front set form
  `waveFrontSet_subset_iUnion_waveFrontSet_sum_sum_smul_smulLeftCLM_iteratedLineDerivOp_union`:
  microlocal elliptic regularity for square systems with invertible principal symbol matrix.
* `Distribution.IsMicrolocallySmoothAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`: if `P T` is
  microlocally smooth at `(x, ξ)` and `σ_M(P)(x, ξ) ≠ 0`, then `T` is microlocally smooth there.
* `Distribution.waveFrontSet_subset_waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_union`:
  `WF(T) ⊆ WF(P T) ∪ Char(P)`.
* `Distribution.waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero`,
  `Distribution.singularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero`: an
  elliptic operator preserves the wave front set and the singular support.
* `Distribution.IsMicrolocallySmoothAt.of_sum_smul_iteratedLineDerivOp`,
  `Distribution.waveFrontSet_subset_waveFrontSet_sum_smul_iteratedLineDerivOp_union`,
  `Distribution.waveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero`,
  `Distribution.singularSupport_sum_smul_iteratedLineDerivOp_of_forall_ne_zero`: the same for
  constant coefficients.
* `Distribution.waveFrontSet_laplacianCLM`, `Distribution.singularSupport_laplacianCLM`:
  `WF(Δ T) = WF(T)` and `singsupp(Δ T) = singsupp(T)` for the Laplacian
  `Δ = LineDeriv.laplacianCLM ℝ E 𝓓'(Ω, ℂ)`.
* `Distribution.exists_contDiffOn_eq_ofFun_of_sum_smul_smulLeftCLM_iteratedLineDerivOp_eq_ofFun`:
  elliptic operators are hypoelliptic: if `P T` is a function smooth on `Ω`, so is `T`.
* `Distribution.exists_contDiffOn_eq_ofFun_of_sum_smul_smulLeftCLM_iteratedLineDerivOp_eq_zero`,
  `Distribution.exists_contDiffOn_eq_ofFun_of_sum_smul_iteratedLineDerivOp_eq_zero`: every
  distributional solution of `P T = 0` is a smooth function.
* `Distribution.exists_contDiffOn_eq_ofFun_of_laplacianCLM_eq_zero`: Weyl's lemma for
  distributions, `Δ T = 0` makes `T` a smooth function.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.3.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter LineDeriv Real Set TopologicalSpace TestFunction
open scoped Distributions Topology RealInnerProductSpace ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The principal symbol and the characteristic set -/

/-- The **principal symbol** of order `M` of the constant-coefficient operator
`P = ∑ i ∈ s, c i ∂^(m i)`, in the geometric convention without factors of `i`:
`σ_M(P)(ξ) = ∑ i ∈ s with k i = M, c i ∏ₗ ⟪m i l, ξ⟫`. Only the terms of order exactly `M`
contribute. -/
def constCoeffPrincipalSymbol {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) (ξ : E) : ℂ :=
  ∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, ξ⟫ : ℂ)

/-- The **characteristic set** of the constant-coefficient operator `P = ∑ i ∈ s, c i ∂^(m i)`
of order `M`: the points `(x, ξ)` with `ξ ≠ 0` at which the principal symbol
`constCoeffPrincipalSymbol s c m M` vanishes. -/
def constCoeffCharacteristicSet {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) : Set (E × E) :=
  {p | p.2 ≠ 0 ∧ constCoeffPrincipalSymbol s c m M p.2 = 0}

theorem constCoeffPrincipalSymbol_def {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) (ξ : E) :
    constCoeffPrincipalSymbol s c m M ξ = ∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, ξ⟫ : ℂ) :=
  (rfl)

@[fun_prop]
theorem continuous_constCoeffPrincipalSymbol {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) (M : ℕ) :
    Continuous (constCoeffPrincipalSymbol s c m M) := by
  unfold constCoeffPrincipalSymbol
  fun_prop

@[simp]
theorem mem_constCoeffCharacteristicSet_iff {ι : Type*} {s : Finset ι} {c : ι → ℂ} {k : ι → ℕ}
    {m : ∀ i, Fin (k i) → E} {M : ℕ} {p : E × E} :
    p ∈ constCoeffCharacteristicSet s c m M ↔
      p.2 ≠ 0 ∧ constCoeffPrincipalSymbol s c m M p.2 = 0 :=
  Iff.rfl

/-- The characteristic set is empty exactly when the operator is elliptic: its principal symbol
vanishes at no `ξ ≠ 0`. -/
theorem constCoeffCharacteristicSet_eq_empty_iff {ι : Type*} {s : Finset ι}
    {c : ι → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} :
    constCoeffCharacteristicSet s c m M = ∅ ↔
      ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol s c m M ξ ≠ 0 := by
  simp only [eq_empty_iff_forall_notMem, mem_constCoeffCharacteristicSet_iff, Prod.forall,
    not_and, ne_eq]
  exact ⟨fun h ξ ↦ h 0 ξ, fun h _ ξ ↦ h ξ⟩

/-- The principal symbol is homogeneous of degree `M`. -/
theorem constCoeffPrincipalSymbol_smul {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) (t : ℝ) (η : E) :
    constCoeffPrincipalSymbol s c m M (t • η) =
      (t : ℂ) ^ M * constCoeffPrincipalSymbol s c m M η := by
  rw [constCoeffPrincipalSymbol, constCoeffPrincipalSymbol, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hki : k i = M := (Finset.mem_filter.1 hi).2
  have hprod : ∏ l, (⟪m i l, t • η⟫ : ℂ) = (t : ℂ) ^ k i * ∏ l, (⟪m i l, η⟫ : ℂ) := by
    simp only [inner_smul_right, ofReal_mul]
    rw [← Finset.pow_card_mul_prod, Finset.card_univ, Fintype.card_fin]
  have hpow : (t : ℂ) ^ k i = (t : ℂ) ^ M := by rw [hki]
  rw [hprod, hpow]
  ring

/-- The characteristic set is conic in the frequency variable. -/
theorem smul_mem_constCoeffCharacteristicSet_iff {ι : Type*} {s : Finset ι} {c : ι → ℂ}
    {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} {x ξ : E} {t : ℝ} (ht : t ≠ 0) :
    (x, t • ξ) ∈ constCoeffCharacteristicSet s c m M ↔
      (x, ξ) ∈ constCoeffCharacteristicSet s c m M := by
  simp [constCoeffPrincipalSymbol_smul, ht]

/-- The **principal symbol** of order `M` at `x` of the operator `P = ∑ i ∈ s, b i ∂^(m i)` with
coefficient functions `b i`: the principal symbol of the constant-coefficient operator with the
coefficients frozen at `x`, `σ_M(P)(x, ξ) = ∑ i ∈ s with k i = M, b i x ∏ₗ ⟪m i l, ξ⟫`. -/
def principalSymbol {ι : Type*} (s : Finset ι) (b : ι → E → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) (x ξ : E) : ℂ :=
  constCoeffPrincipalSymbol s (fun i ↦ b i x) m M ξ

/-- The **characteristic set** `Char(P)` of the operator `P = ∑ i ∈ s, b i ∂^(m i)` of order `M`:
the points `(x, ξ)` with `ξ ≠ 0` at which the principal symbol `principalSymbol s b m M x` vanishes.
-/
def characteristicSet {ι : Type*} (s : Finset ι) (b : ι → E → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) : Set (E × E) :=
  {p | p.2 ≠ 0 ∧ principalSymbol s b m M p.1 p.2 = 0}

theorem principalSymbol_def {ι : Type*} (s : Finset ι) (b : ι → E → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) (x ξ : E) :
    principalSymbol s b m M x ξ = constCoeffPrincipalSymbol s (fun i ↦ b i x) m M ξ :=
  (rfl)

/-- With continuous coefficients, the principal symbol is jointly continuous in the position and
the frequency. -/
@[fun_prop]
theorem continuous_principalSymbol {ι : Type*} (s : Finset ι) {b : ι → E → ℂ}
    (hb : ∀ i, Continuous (b i)) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) (M : ℕ) :
    Continuous fun p : E × E ↦ principalSymbol s b m M p.1 p.2 := by
  simp only [principalSymbol, constCoeffPrincipalSymbol]
  fun_prop

/-- The principal symbol is homogeneous of degree `M` in the frequency variable. -/
theorem principalSymbol_smul {ι : Type*} (s : Finset ι) (b : ι → E → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) (x : E) (t : ℝ) (η : E) :
    principalSymbol s b m M x (t • η) = (t : ℂ) ^ M * principalSymbol s b m M x η :=
  constCoeffPrincipalSymbol_smul s _ m M t η

/-- With constant coefficients, the principal symbol is `constCoeffPrincipalSymbol`. -/
@[simp]
theorem principalSymbol_const {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) (x ξ : E) :
    principalSymbol s (fun i _ ↦ c i) m M x ξ = constCoeffPrincipalSymbol s c m M ξ :=
  (rfl)

@[simp]
theorem mem_characteristicSet_iff {ι : Type*} {s : Finset ι} {b : ι → E → ℂ} {k : ι → ℕ}
    {m : ∀ i, Fin (k i) → E} {M : ℕ} {p : E × E} :
    p ∈ characteristicSet s b m M ↔ p.2 ≠ 0 ∧ principalSymbol s b m M p.1 p.2 = 0 :=
  Iff.rfl

/-- The characteristic set is empty exactly when the operator is elliptic: its principal symbol
with the coefficients frozen at any point vanishes at no `ξ ≠ 0`. -/
theorem characteristicSet_eq_empty_iff {ι : Type*} {s : Finset ι} {b : ι → E → ℂ}
    {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} :
    characteristicSet s b m M = ∅ ↔ ∀ x ξ : E, ξ ≠ 0 → principalSymbol s b m M x ξ ≠ 0 := by
  simp only [eq_empty_iff_forall_notMem, mem_characteristicSet_iff, Prod.forall, not_and, ne_eq]

/-- With constant coefficients, the characteristic set is `constCoeffCharacteristicSet`. -/
@[simp]
theorem characteristicSet_const {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) :
    characteristicSet s (fun i _ ↦ c i) m M = constCoeffCharacteristicSet s c m M :=
  (rfl)

/-- The characteristic set is conic in the frequency variable. -/
theorem smul_mem_characteristicSet_iff {ι : Type*} {s : Finset ι} {b : ι → E → ℂ}
    {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} {x ξ : E} {t : ℝ} (ht : t ≠ 0) :
    (x, t • ξ) ∈ characteristicSet s b m M ↔ (x, ξ) ∈ characteristicSet s b m M := by
  simp [principalSymbol_smul, ht]

/-- **An elliptic cone, uniformly near a point.** Let the coefficients `b i` of a differential
operator depend continuously on the position. If the principal symbol with the coefficients frozen
at `x` does not vanish at `ξ`, then there are a neighbourhood `U` of `x`, an open cone `Γ` around
`ξ` and `c₀ > 0` such that, for every `y ∈ U`, the principal symbol with the coefficients frozen at
`y` is bounded below by `c₀ ‖η‖ ^ M` on `Γ`. -/
theorem exists_nhds_cone_le_norm_principalSymbol {ι : Type*} {s : Finset ι}
    {b : ι → E → ℂ} (hb : ∀ i, Continuous (b i)) {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ}
    {x ξ : E} (hξ : principalSymbol s b m M x ξ ≠ 0) :
    ∃ U ∈ 𝓝 x, ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ y ∈ U, ∀ η ∈ Γ, c₀ * ‖η‖ ^ M ≤ ‖principalSymbol s b m M y η‖ :=
  exists_nhds_cone_le_norm_of_continuous_of_homogeneous
    (f := fun p ↦ principalSymbol s b m M p.1 p.2) (continuous_principalSymbol s hb m M)
    (fun y η t _ ↦ principalSymbol_smul s b m M y t η) hξ

/-- **An elliptic cone.** If the principal symbol does not vanish at `ξ`, then it is bounded
below by `c₀ ‖η‖ ^ M` on an open cone around `ξ`, for some `c₀ > 0`. -/
theorem exists_cone_le_norm_constCoeffPrincipalSymbol {ι : Type*} {s : Finset ι} {c : ι → ℂ}
    {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} {ξ : E}
    (hξ : constCoeffPrincipalSymbol s c m M ξ ≠ 0) :
    ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ η ∈ Γ, c₀ * ‖η‖ ^ M ≤ ‖constCoeffPrincipalSymbol s c m M η‖ := by
  obtain ⟨U, hU, Γ, hΓ, hξΓ, hcone, c₀, hc₀, h⟩ :=
    exists_nhds_cone_le_norm_principalSymbol (b := fun i _ ↦ c i)
      (fun _ ↦ continuous_const) (x := 0) hξ
  exact ⟨Γ, hΓ, hξΓ, hcone, c₀, hc₀, fun η hη ↦ h 0 (mem_of_mem_nhds hU) η hη⟩

/-- **Ellipticity is an open condition.** For coefficients `c x` depending continuously on a
parameter `x` at `x₀`, if the principal symbol with coefficients `c x₀` vanishes at no `ξ ≠ 0`,
then the same holds for all `x` near `x₀`. -/
theorem eventually_forall_constCoeffPrincipalSymbol_ne_zero [FiniteDimensional ℝ E]
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : Finset ι} {c : X → ι → ℂ} {x₀ : X}
    (hc : ∀ i ∈ s, ContinuousAt (fun x ↦ c x i) x₀) {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ}
    (h : ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol s (c x₀) m M ξ ≠ 0) :
    ∀ᶠ x in 𝓝 x₀, ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol s (c x) m M ξ ≠ 0 := by
  have hcont (ξ : E) :
      ContinuousAt (fun p : X × E ↦ constCoeffPrincipalSymbol s (c p.1) m M p.2) (x₀, ξ) := by
    simp only [constCoeffPrincipalSymbol_def]
    refine tendsto_finsetSum _ fun i hi ↦ ?_
    have hci : ContinuousAt (fun p : X × E ↦ c p.1 i) (x₀, ξ) :=
      ContinuousAt.comp (f := Prod.fst) (x := (x₀, ξ)) (hc i (Finset.mem_filter.1 hi).1)
        continuousAt_fst
    exact hci.mul (Continuous.continuousAt (by fun_prop))
  -- On the compact unit sphere the principal symbol stays nonzero near `x₀`.
  have hS := (isCompact_sphere (0 : E) 1).eventually_forall_of_forall_eventually
    (P := fun x ξ ↦ constCoeffPrincipalSymbol s (c x) m M ξ ≠ 0) fun ξ hξ ↦
      (hcont ξ).eventually_ne (h ξ (ne_zero_of_mem_unit_sphere ⟨ξ, hξ⟩))
  filter_upwards [hS] with x hx ξ hξ
  -- Homogeneity reduces a nonzero `ξ` to the unit sphere.
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
  have hu : ‖ξ‖⁻¹ • ξ ∈ Metric.sphere (0 : E) 1 := by
    simp [norm_smul, hn]
  have hξ' : ξ = ‖ξ‖ • (‖ξ‖⁻¹ • ξ) := by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  rw [hξ', constCoeffPrincipalSymbol_smul]
  exact mul_ne_zero (pow_ne_zero _ (ofReal_ne_zero.2 hn)) (hx _ hu)

/-- **The principal symbol of the Laplacian.** For an orthonormal basis `b`, the principal symbol
of `∑ i, ∂_{b i} ∂_{b i}` is `∑ i, ⟪b i, ξ⟫ ^ 2 = ‖ξ‖ ^ 2`. -/
theorem constCoeffPrincipalSymbol_laplacian {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (ξ : E) :
    constCoeffPrincipalSymbol Finset.univ (fun _ ↦ 1) (fun i ↦ ![b i, b i]) 2 ξ =
      ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
  have hsum : ∑ i, ⟪b i, ξ⟫ * ⟪b i, ξ⟫ = ‖ξ‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner ξ ξ]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm]
  rw [← hsum]
  simp [constCoeffPrincipalSymbol, Fin.prod_univ_two]

end TauCeti

namespace Distribution

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

/-! ### Polynomial bounds for the symbol -/

/-- The symbol of `∂^m` in the frequency variable of the localized Fourier transform is
`(2πi) ^ r` times the product of the inner products. -/
private theorem prod_two_pi_I_inner {r : ℕ} (m : Fin r → E) (η : E) :
    ∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ) = (2 * π * I) ^ r * ∏ l, (⟪m l, η⟫ : ℂ) := by
  rw [← Finset.pow_card_mul_prod, Finset.card_univ, Fintype.card_fin]

/-- The symbol `∏ₗ 2πi ⟪m l, η⟫` of `∂^m` is bounded by `(2π) ^ r ∏ₗ ‖m l‖ ‖η‖ ^ r`. -/
private theorem norm_prod_two_pi_I_inner_le {r : ℕ} (m : Fin r → E) (η : E) :
    ‖∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)‖ ≤ (2 * π) ^ r * (∏ l, ‖m l‖) * ‖η‖ ^ r := by
  have h2π : ‖(2 * π * I : ℂ)‖ = 2 * π := by simp [abs_of_pos pi_pos]
  rw [prod_two_pi_I_inner, norm_mul, norm_pow, h2π, mul_assoc]
  gcongr
  rw [← ofReal_prod, norm_real]
  simpa using TauCeti.norm_prod_inner_le (𝕜 := ℝ) Finset.univ m η

/-- **The terms of lower order.** If all orders are at most `M` and the coefficients are bounded
by `A`, the terms of the full symbol of order less than `M` are `O(‖η‖ ^ (M - 1))` for
`‖η‖ ≥ 1`. -/
private theorem norm_sum_filter_ne_mul_le {ι : Type*} {s : Finset ι} {b : ι → ℂ} {A : ℝ}
    (hA : ∀ i ∈ s, ‖b i‖ ≤ A) {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ}
    (hk : ∀ i ∈ s, k i ≤ M) {η : E} (h1 : 1 ≤ ‖η‖) :
    ‖∑ i ∈ s with k i ≠ M, b i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖ * ‖η‖ ≤
      (∑ i ∈ s with k i ≠ M, A * ((2 * π) ^ k i * ∏ l, ‖m i l‖)) * ‖η‖ ^ M := by
  refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hi' := Finset.mem_filter.1 hi
  have hki : k i + 1 ≤ M := by
    have := hk i hi'.1
    have := hi'.2
    omega
  rw [norm_mul]
  calc ‖b i‖ * ‖∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖ * ‖η‖
      ≤ A * ((2 * π) ^ k i * (∏ l, ‖m i l‖) * ‖η‖ ^ k i) * ‖η‖ := by
        gcongr
        · exact (norm_nonneg _).trans (hA i hi'.1)
        · exact hA i hi'.1
        · exact norm_prod_two_pi_I_inner_le _ _
    _ = A * ((2 * π) ^ k i * ∏ l, ‖m i l‖) * ‖η‖ ^ (k i + 1) := by ring
    _ ≤ A * ((2 * π) ^ k i * ∏ l, ‖m i l‖) * ‖η‖ ^ M :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hki)
          (mul_nonneg ((norm_nonneg _).trans (hA i hi'.1)) (by positivity))

/-- **The full symbol is elliptic at large frequencies.** Let all orders be at most `M`, let the
coefficients `b i y` be bounded by `A` for `y ∈ U`, and let the principal symbol with the
coefficients frozen at every `y ∈ U` be bounded below by `c₀ ‖η‖ ^ M` on `Γ`. Then the full symbol
`p (y, η) = ∑ i ∈ s, b i y ∏ₗ 2πi ⟪m i l, η⟫` is bounded below by a multiple of `(1 + ‖η‖) ^ M`
for `y ∈ U` and `η ∈ Γ` outside a ball: the terms of lower order are smaller by a factor `‖η‖`. -/
theorem _root_.TauCeti.exists_mul_one_add_norm_pow_le_norm_sum_mul_prod {ι : Type*}
    {s : Finset ι} {b : ι → E → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ}
    (hk : ∀ i ∈ s, k i ≤ M) {U Γ : Set E} {A c₀ : ℝ} (hc₀ : 0 < c₀)
    (hA : ∀ y ∈ U, ∀ i ∈ s, ‖b i y‖ ≤ A)
    (hΓ : ∀ y ∈ U, ∀ η ∈ Γ,
      c₀ * ‖η‖ ^ M ≤ ‖constCoeffPrincipalSymbol s (fun i ↦ b i y) m M η‖) :
    ∃ R c' : ℝ, 0 < c' ∧ ∀ y ∈ U, ∀ η ∈ Γ, R ≤ ‖η‖ →
      c' * (1 + ‖η‖) ^ M ≤ ‖∑ i ∈ s, b i y * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖ := by
  set A' : ℝ := ∑ i ∈ s with k i ≠ M, A * ((2 * π) ^ k i * ∏ l, ‖m i l‖)
  set B : ℝ := (2 * π) ^ M * c₀
  have hB : 0 < B := by positivity
  have h2π : ‖(2 * π * I : ℂ)‖ = 2 * π := by simp [abs_of_pos pi_pos]
  refine ⟨max 1 (2 * A' / B), B / 2 ^ (M + 1), by positivity, fun y hy η hη hR ↦ ?_⟩
  have h1 : 1 ≤ ‖η‖ := (le_max_left _ _).trans hR
  have hAη : 2 * A' ≤ B * ‖η‖ := by
    rw [mul_comm B]
    exact (div_le_iff₀ hB).1 ((le_max_right _ _).trans hR)
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i ↦ k i = M)]
  -- The terms of order `M` give `(2πi) ^ M` times the principal symbol.
  have htop : ∑ i ∈ s with k i = M, b i y * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ) =
      (2 * π * I) ^ M * ∑ i ∈ s with k i = M, b i y * ∏ l, (⟪m i l, η⟫ : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hpow : (2 * π * I : ℂ) ^ k i = (2 * π * I) ^ M := by rw [(Finset.mem_filter.1 hi).2]
    rw [prod_two_pi_I_inner, hpow]
    ring
  -- The terms of order less than `M` are bounded by `A' ‖η‖ ^ M / ‖η‖`.
  have hlow : ‖∑ i ∈ s with ¬k i = M, b i y * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖ * ‖η‖ ≤
      A' * ‖η‖ ^ M :=
    norm_sum_filter_ne_mul_le (hA y hy) hk h1
  set L := ‖∑ i ∈ s with ¬k i = M, b i y * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖
  have hL : L ≤ B / 2 * ‖η‖ ^ M := by
    refine le_of_mul_le_mul_right ?_ (zero_lt_one.trans_le h1)
    nlinarith [pow_nonneg (norm_nonneg η) M]
  have hpow : (1 + ‖η‖) ^ M ≤ 2 ^ M * ‖η‖ ^ M := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) M
  have htop' : B * ‖η‖ ^ M ≤
      ‖∑ i ∈ s with k i = M, b i y * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖ := by
    rw [htop, norm_mul, norm_pow, h2π, ← constCoeffPrincipalSymbol]
    calc B * ‖η‖ ^ M = (2 * π) ^ M * (c₀ * ‖η‖ ^ M) := by simp only [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hΓ y hy η hη) (by positivity)
  calc B / 2 ^ (M + 1) * (1 + ‖η‖) ^ M ≤ B / 2 ^ (M + 1) * (2 ^ M * ‖η‖ ^ M) := by gcongr
    _ = B * ‖η‖ ^ M - B / 2 * ‖η‖ ^ M := by
        rw [pow_succ]
        field_simp
        ring
    _ ≤ _ - L := by gcongr
    _ ≤ _ := by
        rw [sub_le_iff_le_add]
        exact htop'.trans (norm_le_add_norm_add _ _)

/-- **The derivatives of the full symbol in the position.** For smooth coefficients and orders at
most `M`, the derivatives of order at most `n` of `y ↦ p (y, η)` are `O((1 + ‖η‖) ^ M)` on a
compact set, uniformly in `η`. -/
private theorem exists_norm_iteratedFDeriv_symbol_le {ι : Type*} {s : Finset ι} {b : ι → E → ℂ}
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ}
    (hk : ∀ i ∈ s, k i ≤ M) {K : Set E} (hK : IsCompact K) (n : ℕ) :
    ∃ A, 0 ≤ A ∧ ∀ y ∈ K, ∀ η, ∀ j ≤ n, ‖iteratedFDeriv ℝ j
      (fun z ↦ ∑ i ∈ s, b i z * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) y‖ ≤ A * (1 + ‖η‖) ^ M := by
  obtain ⟨G, hG0, hG⟩ := exists_forall_norm_iteratedFDeriv_le_of_isCompact s (n := n)
    (fun i _ ↦ (hb i).of_le (by exact_mod_cast le_top)) hK
  refine ⟨∑ i ∈ s, G * ((2 * π) ^ k i * ∏ l, ‖m i l‖), by positivity, fun y hy η j hj ↦ ?_⟩
  have hw : 1 ≤ 1 + ‖η‖ := le_add_of_nonneg_right (norm_nonneg η)
  have hterm (i : ι) : (fun z ↦ b i z * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) =
      fun z ↦ (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) • b i z := by
    ext z
    rw [smul_eq_mul, mul_comm]
  rw [iteratedFDeriv_sum fun i _ ↦ ((hb i).mul contDiff_const).of_le (by simp), Finset.sum_apply,
    Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  rw [hterm, iteratedFDeriv_const_smul_apply' ((hb i).contDiffAt.of_le (by simp)), norm_smul]
  calc ‖∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖ * ‖iteratedFDeriv ℝ j (b i) y‖
      ≤ ((2 * π) ^ k i * (∏ l, ‖m i l‖) * (1 + ‖η‖) ^ k i) * G := by
        gcongr
        · exact (norm_prod_two_pi_I_inner_le _ _).trans (by gcongr; linarith)
        · exact hG i hi j hj y hy
    _ ≤ ((2 * π) ^ k i * (∏ l, ‖m i l‖) * (1 + ‖η‖) ^ M) * G := by
        gcongr
        exact hk i hi
    _ = G * ((2 * π) ^ k i * ∏ l, ‖m i l‖) * (1 + ‖η‖) ^ M := by ring

/-! ### Transfer of decay through derivatives -/

/-- **Each derivative costs one order of decay.** Suppose that, for the cutoffs `φ` supported in
`U` whose derivatives of order at most `ρ` are bounded by `B`, the localized Fourier transforms of
`T` are `O(B (1 + ‖η‖) ^ k / (1 + ‖η‖) ^ j)` on `Γ`, uniformly in `φ`. Then those of `∂^m T`, for
`r` directions `m`, are `O(B (1 + ‖η‖) ^ (k + r) / (1 + ‖η‖) ^ j)` for the cutoffs whose derivatives
of order at most `ρ + r` are bounded by `B`. -/
private theorem exists_localFourier_iteratedLineDerivOp_le {T : 𝓓'(Ω, ℂ)} {U Γ : Set E}
    {j k ρ : ℕ} {C : ℝ} (hC : 0 ≤ C) (hT : ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ U → ∀ B : ℝ,
      (∀ i ≤ ρ, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ B) →
        ∀ η ∈ Γ, (1 + ‖η‖) ^ j * ‖T.localFourier φ η‖ ≤ C * B * (1 + ‖η‖) ^ k)
    {r : ℕ} (m : Fin r → E) :
    ∃ C', 0 ≤ C' ∧ ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ U → ∀ B : ℝ,
      (∀ i ≤ ρ + r, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ B) →
        ∀ η ∈ Γ, (1 + ‖η‖) ^ j * ‖(∂^{m} T).localFourier φ η‖ ≤ C' * B * (1 + ‖η‖) ^ (k + r) := by
  induction r with
  | zero => exact ⟨C, hC, fun φ hφ B hB η hη ↦ by simpa using hT φ hφ B hB η hη⟩
  | succ r ih =>
    obtain ⟨C₁, hC₁, h₁⟩ := ih (Fin.tail m)
    refine ⟨(2 * π + 1) * ‖m 0‖ * C₁, by positivity, fun φ hφ B hB η hη ↦ ?_⟩
    have hw : 1 ≤ 1 + ‖η‖ := le_add_of_nonneg_right (norm_nonneg η)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
    have hφ₁ := h₁ φ hφ B (fun i hi ↦ hB i (by omega)) η hη
    have hφ₂ := h₁ (∂_{m 0} φ) ((tsupport_lineDerivOp_subset φ _).trans hφ) (‖m 0‖ * B)
      (norm_iteratedFDeriv_lineDerivOp_le φ (m 0) (r := ρ + r) hB) η hη
    rw [iteratedLineDerivOp_succ_left]
    calc (1 + ‖η‖) ^ j * ‖(∂_{m 0} (∂^{Fin.tail m} T)).localFourier φ η‖
        ≤ 2 * π * ‖m 0‖ * (1 + ‖η‖) * ((1 + ‖η‖) ^ j * ‖(∂^{Fin.tail m} T).localFourier φ η‖) +
            (1 + ‖η‖) ^ j * ‖(∂^{Fin.tail m} T).localFourier (∂_{m 0} φ) η‖ :=
          (one_add_norm_pow_mul_norm_localFourier_lineDerivOp_le _ _ _ _ _).trans_eq (by ring)
      _ ≤ 2 * π * ‖m 0‖ * (1 + ‖η‖) * (C₁ * B * (1 + ‖η‖) ^ (k + r)) +
            C₁ * (‖m 0‖ * B) * (1 + ‖η‖) ^ (k + r + 1) :=
          add_le_add (mul_le_mul_of_nonneg_left hφ₁ (by positivity)) <| hφ₂.trans <|
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hw (Nat.le_succ _)) (by positivity)
      _ = (2 * π + 1) * ‖m 0‖ * C₁ * B * (1 + ‖η‖) ^ (k + (r + 1)) := by ring

/-- **The symbol of an iterated derivative.** Under the hypothesis of
`exists_localFourier_iteratedLineDerivOp_le`, the localized Fourier transform of `∂^m T` is its
symbol `∏ₗ 2πi ⟪m l, η⟫` times that of `T`, up to an error decaying one order faster than the
bound on `∂^m T`, uniformly over the cutoffs whose derivatives of order at most `ρ + r` are
bounded by `B`. -/
private theorem exists_localFourier_iteratedLineDerivOp_sub_le {T : 𝓓'(Ω, ℂ)} {U Γ : Set E}
    {j k ρ : ℕ} {C : ℝ} (hC : 0 ≤ C) (hT : ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ U → ∀ B : ℝ,
      (∀ i ≤ ρ, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ B) →
        ∀ η ∈ Γ, (1 + ‖η‖) ^ j * ‖T.localFourier φ η‖ ≤ C * B * (1 + ‖η‖) ^ k)
    {r : ℕ} (m : Fin r → E) :
    ∃ C', 0 ≤ C' ∧ ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ U → ∀ B : ℝ,
      (∀ i ≤ ρ + r, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ B) → ∀ η ∈ Γ,
        (1 + ‖η‖) ^ (j + 1) * ‖(∂^{m} T).localFourier φ η -
          (∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)) * T.localFourier φ η‖ ≤
            C' * B * (1 + ‖η‖) ^ (k + r) := by
  induction r with
  | zero => exact ⟨0, le_rfl, fun φ _ B _ η _ ↦ by simp⟩
  | succ r ih =>
    obtain ⟨C₁, hC₁, h₁⟩ := ih (Fin.tail m)
    obtain ⟨C₂, hC₂, h₂⟩ := exists_localFourier_iteratedLineDerivOp_le hC hT (Fin.tail m)
    refine ⟨2 * π * ‖m 0‖ * C₁ + C₂ * ‖m 0‖, by positivity, fun φ hφ B hB η hη ↦ ?_⟩
    have hφ₁ := h₁ φ hφ B (fun i hi ↦ hB i (by omega)) η hη
    have hφ₂ := h₂ (∂_{m 0} φ) ((tsupport_lineDerivOp_subset φ _).trans hφ) (‖m 0‖ * B)
      (norm_iteratedFDeriv_lineDerivOp_le φ (m 0) (r := ρ + r) hB) η hη
    set a : ℂ := 2 * π * I * ⟪m 0, η⟫
    set D := (∂^{Fin.tail m} T).localFourier φ η -
      (∏ l, (2 * π * I * ⟪Fin.tail m l, η⟫ : ℂ)) * T.localFourier φ η
    set L := (∂^{Fin.tail m} T).localFourier (∂_{m 0} φ) η
    have hid : (∂^{m} T).localFourier φ η -
        (∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)) * T.localFourier φ η = a * D - L := by
      rw [iteratedLineDerivOp_succ_left, localFourier_lineDerivOp, Fin.prod_univ_succ]
      simp only [a, D, L, Fin.tail]
      ring
    rw [hid]
    calc (1 + ‖η‖) ^ (j + 1) * ‖a * D - L‖ ≤ (1 + ‖η‖) ^ (j + 1) * (‖a‖ * ‖D‖ + ‖L‖) := by
          gcongr
          exact (norm_sub_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ (1 + ‖η‖) ^ (j + 1) * (2 * π * ‖m 0‖ * (1 + ‖η‖) * ‖D‖ + ‖L‖) := by
          gcongr
          exact TauCeti.norm_two_pi_I_mul_inner_le _ _
      _ = 2 * π * ‖m 0‖ * (1 + ‖η‖) * ((1 + ‖η‖) ^ (j + 1) * ‖D‖) +
            (1 + ‖η‖) * ((1 + ‖η‖) ^ j * ‖L‖) := by ring
      _ ≤ 2 * π * ‖m 0‖ * (1 + ‖η‖) * (C₁ * B * (1 + ‖η‖) ^ (k + r)) +
            (1 + ‖η‖) * (C₂ * (‖m 0‖ * B) * (1 + ‖η‖) ^ (k + r)) := by
          gcongr
      _ = (2 * π * ‖m 0‖ * C₁ + C₂ * ‖m 0‖) * B * (1 + ‖η‖) ^ (k + (r + 1)) := by ring

/-! ### The regularity induction -/

/-- The terms of order `M` of the full symbol matrix of the system
`(P T) j = ∑ i, ∑ a ∈ s, c i j a g i j a ∂^(m a) (T i)` at `y`, in the frequency `η` of the
localized Fourier transform: `(2πi) ^ M` times its principal symbol matrix. -/
private def topSymbolMatrix {ι τ : Type*} (s : Finset τ) (c : ι → ι → τ → ℂ)
    (g : ι → ι → τ → E → ℝ) {k : τ → ℕ} (m : ∀ a, Fin (k a) → E) (M : ℕ) (y η : E) :
    Matrix ι ι ℂ :=
  Matrix.of fun i j ↦ ∑ a ∈ s with k a = M, (c i j a * g i j a y) *
    ∏ l, (2 * π * I * ⟪m a l, η⟫ : ℂ)

/-- **The symbol identity for systems.** Let `Ψ j` be cutoffs with
`∑ j, A y i j Ψ j y = δ_iq φ y` for the matrix `A` of the terms of order `M` of the full symbol of
the system `(P T) j = ∑ i, ∑ a ∈ s, c i j a g i j a ∂^(m a) (T i)` at the frequency `η`. Moving the
derivatives onto the cutoffs writes `L(T q, φ)(η)` as `∑ j, L((P T) j, Ψ j)(η)` minus the errors of
`exists_localFourier_iteratedLineDerivOp_sub_le` and the terms of order less than `M`. -/
private theorem localFourier_eq_sum_sub_sum_sub_sum {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset τ) (c : ι → ι → τ → ℂ) {g : ι → ι → τ → E → ℝ}
    (hg : ∀ i j a, ContDiff ℝ ∞ (g i j a)) {k : τ → ℕ} (m : ∀ a, Fin (k a) → E) (M : ℕ)
    (T : ι → 𝓓'(Ω, ℂ)) {φ : 𝓓(Ω, ℂ)} {Ψ : ι → 𝓓(Ω, ℂ)} {η : E} {q : ι}
    (hΨ : ∀ i y, ∑ j, topSymbolMatrix s c g m M y η i j * Ψ j y = if i = q then φ y else 0) :
    (T q).localFourier φ η =
      ∑ j, (∑ i, ∑ a ∈ s, c i j a • smulLeftCLM (hg i j a) (∂^{m a} (T i))).localFourier (Ψ j) η -
      ∑ j, ∑ i, ∑ a ∈ s, c i j a *
        ((∂^{m a} (T i)).localFourier (TestFunction.smulLeftCLM (hg i j a) (Ψ j)) η -
          (∏ l, (2 * π * I * ⟪m a l, η⟫ : ℂ)) *
            (T i).localFourier (TestFunction.smulLeftCLM (hg i j a) (Ψ j)) η) -
      ∑ j, ∑ i, ∑ a ∈ s with k a ≠ M, c i j a * (∏ l, (2 * π * I * ⟪m a l, η⟫ : ℂ)) *
        (T i).localFourier (TestFunction.smulLeftCLM (hg i j a) (Ψ j)) η := by
  set pr : τ → ℂ := fun a ↦ ∏ l, (2 * π * I * ⟪m a l, η⟫ : ℂ)
  set Lt : ι → ι → τ → ℂ := fun i j a ↦
    (T i).localFourier (TestFunction.smulLeftCLM (hg i j a) (Ψ j)) η
  -- The cutoffs `∑ j, A i j Ψ j` are `δ_iq φ`.
  have hcut (i : ι) : ∑ j, ∑ a ∈ s with k a = M,
      (c i j a * pr a) • TestFunction.smulLeftCLM (hg i j a) (Ψ j) = if i = q then φ else 0 := by
    ext y
    have h := hΨ i y
    simp only [topSymbolMatrix, Matrix.of_apply, Finset.sum_mul] at h
    rw [apply_ite (fun ψ : 𝓓(Ω, ℂ) ↦ ψ y), FunLike.coe_zero, Pi.zero_apply, ← h]
    simp only [FunLike.coe_sum, Finset.sum_apply, IsSMulApply.smul_apply,
      TestFunction.smulLeftCLM_apply, smul_eq_mul, Complex.real_smul, pr]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
    ring
  have hq : (T q).localFourier φ η = ∑ i, ∑ j, ∑ a ∈ s with k a = M, c i j a * pr a * Lt i j a := by
    rw [Finset.sum_eq_single q (fun i _ hi ↦ ?_) (fun h ↦ absurd (Finset.mem_univ q) h)]
    · have h0 := congrArg (fun ψ ↦ (T q).localFourier ψ η) (hcut q)
      simp only [↓reduceIte, localFourier_sum_cutoff, localFourier_smul_cutoff] at h0
      exact h0.symm
    · have h0 := congrArg (fun ψ ↦ (T i).localFourier ψ η) (hcut i)
      simp only [hi, ↓reduceIte, localFourier_zero_cutoff, localFourier_sum_cutoff,
        localFourier_smul_cutoff] at h0
      exact h0
  have hP (j : ι) : (∑ i, ∑ a ∈ s, c i j a • smulLeftCLM (hg i j a) (∂^{m a} (T i))).localFourier
      (Ψ j) η = ∑ i, ∑ a ∈ s, c i j a *
        (∂^{m a} (T i)).localFourier (TestFunction.smulLeftCLM (hg i j a) (Ψ j)) η := by
    simp_rw [localFourier_sum, localFourier_smul, localFourier_smulLeftCLM]
  simp_rw [hP, hq]
  rw [Finset.sum_comm (γ := ι) (f := fun i j ↦ ∑ a ∈ s with k a = M, c i j a * pr a * Lt i j a)]
  simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_filter_add_sum_filter_not s (fun a ↦ k a = M)]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [pr, Lt, mul_sub, Finset.sum_sub_distrib, ne_eq, mul_assoc]
  ring

/-- **Dividing cutoffs by the principal symbol matrix of an elliptic system.** Let the
determinant of the matrix `A y η` of the terms of order `M` of the full symbol of a system be
bounded below by `c' (1 + ‖η‖) ^ (M card ι)` for `y` in an open set `W` containing a compact set
`K` and for `η ∈ Γ` with `R ≤ ‖η‖`. Then every cutoff `φ` supported in `K` is
`∑ j, A i j Ψ j = δ_iq φ` for cutoffs `Ψ j` supported in `K` whose derivatives of order at most `n`
are bounded by `Z B / (1 + ‖η‖) ^ M` when those of `φ` are bounded by `B`, with `Z` independent of
`φ`, `B` and `η`. -/
private theorem exists_forall_exists_sum_topSymbolMatrix_mul_eq_ite {ι τ : Type*} [Fintype ι]
    [DecidableEq ι] {s : Finset τ} {c : ι → ι → τ → ℂ} {g : ι → ι → τ → E → ℝ}
    (hg : ∀ i j a, ContDiff ℝ ∞ (g i j a)) {k : τ → ℕ} {m : ∀ a, Fin (k a) → E} {M : ℕ}
    (hk : ∀ a ∈ s, k a ≤ M) {K W Γ : Set E} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    {R c' : ℝ} (hc' : 0 < c') (hp : ∀ y ∈ W, ∀ η ∈ Γ, R ≤ ‖η‖ →
      c' * (1 + ‖η‖) ^ (M * Fintype.card ι) ≤ ‖(topSymbolMatrix s c g m M y η).det‖) (n : ℕ) :
    ∃ Z, 0 ≤ Z ∧ ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ K → ∀ B : ℝ,
      (∀ l ≤ n, ∀ y, ‖iteratedFDeriv ℝ l φ y‖ ≤ B) → ∀ η ∈ Γ, R ≤ ‖η‖ → ∀ q : ι,
        ∃ Ψ : ι → 𝓓(Ω, ℂ), (∀ j, tsupport (Ψ j) ⊆ K) ∧
          (∀ i y, ∑ j, topSymbolMatrix s c g m M y η i j * Ψ j y = if i = q then φ y else 0) ∧
          ∀ j, ∀ l ≤ n, ∀ y, ‖iteratedFDeriv ℝ l (Ψ j) y‖ ≤ Z * B / (1 + ‖η‖) ^ M := by
  set r := Fintype.card ι
  have hb (i j : ι) (a : τ) : ContDiff ℝ ∞ fun y ↦ c i j a * (g i j a y : ℂ) :=
    contDiff_const.mul (ofRealCLM.contDiff.comp (hg i j a))
  have hA (η : E) (i j : ι) : ContDiff ℝ ∞ fun y ↦ topSymbolMatrix s c g m M y η i j :=
    ContDiff.sum fun a _ ↦ (hb i j a).mul contDiff_const
  -- The derivatives of the entries are `O((1 + ‖η‖) ^ M)` on `K`.
  choose Ae hAe0 hAe using fun ij : ι × ι ↦ exists_norm_iteratedFDeriv_symbol_le
    (s := s.filter (k · = M)) (m := m) (b := fun a y ↦ c ij.1 ij.2 a * g ij.1 ij.2 a y)
    (fun a ↦ hb ij.1 ij.2 a) (fun a ha ↦ hk a (Finset.mem_filter.1 ha).1) hK n
  set A₀ := ∑ ij : ι × ι, Ae ij
  have hA₀ : 0 ≤ A₀ := Finset.sum_nonneg fun ij _ ↦ hAe0 ij
  have hent : ∀ y ∈ K, ∀ η : E, ∀ i j, ∀ l ≤ n, ‖iteratedFDeriv ℝ l
      (fun z ↦ topSymbolMatrix s c g m M z η i j) y‖ ≤ A₀ * (1 + ‖η‖) ^ M := fun y hy η i j l hl ↦
    (hAe (i, j) y hy η l hl).trans (by
      gcongr
      exact Finset.single_le_sum (fun ij _ ↦ hAe0 ij) (Finset.mem_univ (i, j)))
  -- Bounds for the reciprocal of the determinant and for the adjugate.
  set Ad := ((r.factorial : ℝ) * 2 ^ (n * r) * A₀ ^ r)
  set Aa := ((r.factorial : ℝ) * 2 ^ (n * r) * A₀ ^ (r - 1))
  obtain ⟨Q, hQ0, hQ⟩ := TauCeti.exists_norm_iteratedFDeriv_inv_le_div (E := E) (𝕜 := ℂ) n Ad hc'
  refine ⟨4 ^ n * Q * Aa, by positivity, fun φ hφK B hB η hη hηR q ↦ ?_⟩
  have hr : 1 ≤ r := Fintype.card_pos_iff.2 ⟨q⟩
  have hpow (e : ℕ) : (A₀ * (1 + ‖η‖) ^ M) ^ e = A₀ ^ e * (1 + ‖η‖) ^ (M * e) := by
    rw [mul_pow, pow_mul]
  have hdet (y : E) (hy : y ∈ K) : ∀ l ≤ n, ‖iteratedFDeriv ℝ l
      (fun z ↦ (topSymbolMatrix s c g m M z η).det) y‖ ≤ Ad * (1 + ‖η‖) ^ (M * r) :=
    fun l hl ↦ (TauCeti.norm_iteratedFDeriv_det_le (hA η) (by exact_mod_cast le_top)
      (hent y hy η) l hl).trans_eq (by
        simp only [Finset.prod_const, Finset.card_univ, Finset.sum_const, Fintype.card_perm,
          nsmul_eq_mul, hpow, Ad]
        ring)
  have hadj (y : E) (hy : y ∈ K) (j k : ι) : ∀ l ≤ n, ‖iteratedFDeriv ℝ l
      (fun z ↦ (topSymbolMatrix s c g m M z η).adjugate j k) y‖ ≤
        Aa * (1 + ‖η‖) ^ (M * (r - 1)) :=
    fun l hl ↦ (TauCeti.norm_iteratedFDeriv_adjugate_apply_le (hA η) (by exact_mod_cast le_top)
      (hent y hy η) j k l hl).trans_eq (by rw [hpow]; ring)
  obtain ⟨Ψ, hΨK, hΨ, hΨB⟩ := φ.exists_sum_mul_eq_ite_of_forall_det_ne_zero hW hKW hφK (hA η)
    (fun y hy ↦ norm_pos_iff.1 ((mul_pos hc' (by positivity)).trans_le (hp y hy η hη hηR)))
    (Q := Q / (1 + ‖η‖) ^ (M * r)) (G := Aa * (1 + ‖η‖) ^ (M * (r - 1))) (by positivity)
    (by positivity)
    (fun l hl y hy ↦ hQ _ _ y (by positivity) ((ContDiff.matrix_det (hA η)).of_le (by simp))
      (hdet y hy) (hp y (hKW hy) η hη hηR) l hl)
    (fun j k l hl y hy ↦ hadj y hy j k l hl) hB q
  refine ⟨Ψ, hΨK, hΨ, fun j l hl y ↦ (hΨB j l hl y).trans_eq ?_⟩
  -- `(1 + ‖η‖) ^ (M (r - 1)) (1 + ‖η‖) ^ M = (1 + ‖η‖) ^ (M r)`.
  have hsplit : (1 + ‖η‖) ^ (M * r) = (1 + ‖η‖) ^ (M * (r - 1)) * (1 + ‖η‖) ^ M := by
    rw [← pow_add]
    congr 1
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hr]
  rw [hsplit, show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
  field_simp

omit [InnerProductSpace ℝ E] in
/-- In the regularity induction, frequencies of norm less than `R` cost only the factor `1 + R`. -/
private theorem one_add_norm_pow_succ_mul_le {η : E} {R : ℝ} (hηR : ‖η‖ < R) {j k₀ : ℕ}
    {z : ℂ} {Y : ℝ} (hz : (1 + ‖η‖) ^ j * ‖z‖ ≤ Y * (1 + ‖η‖) ^ k₀) :
    (1 + ‖η‖) ^ (j + 1) * ‖z‖ ≤ (1 + R) * Y * (1 + ‖η‖) ^ k₀ := by
  calc (1 + ‖η‖) ^ (j + 1) * ‖z‖ = (1 + ‖η‖) * ((1 + ‖η‖) ^ j * ‖z‖) := by ring
    _ ≤ (1 + R) * (Y * (1 + ‖η‖) ^ k₀) :=
        mul_le_mul (by linarith) hz (by positivity) (by linarith [norm_nonneg η])
    _ = (1 + R) * Y * (1 + ‖η‖) ^ k₀ := by ring

omit [InnerProductSpace ℝ E] in
/-- A bound `w ‖∑ x ∈ u, f x‖ ≤ ∑ x ∈ u, b x` from termwise bounds `w ‖f x‖ ≤ b x`, for `w ≥ 0`. -/
private theorem mul_norm_sum_le_of_le {α : Type*} {u : Finset α} {f : α → ℂ} {b : α → ℝ} {w : ℝ}
    (hw : 0 ≤ w) (h : ∀ x ∈ u, w * ‖f x‖ ≤ b x) : w * ‖∑ x ∈ u, f x‖ ≤ ∑ x ∈ u, b x :=
  (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw).trans
    ((Finset.mul_sum _ _ _).trans_le (Finset.sum_le_sum h))

/-- **A term of lower order gains one power.** If `(1 + ‖η‖) ^ d ‖L‖ ≤ C' (1 + ‖η‖) ^ k₀`, then
the term `c ∏ₗ 2πi ⟪m l, η⟫ L` of order `k < M` satisfies
`(1 + ‖η‖) ^ (d + 1) ‖c ∏ₗ 2πi ⟪m l, η⟫ L‖ ≤ ‖c‖ (2π) ^ k ∏ₗ ‖m l‖ C' (1 + ‖η‖) ^ (k₀ + M)`. -/
private theorem one_add_norm_pow_succ_mul_norm_mul_prod_mul_le {k M d k₀ : ℕ} (hkM : k + 1 ≤ M)
    (c : ℂ) (m : Fin k → E) {η : E} {L : ℂ} {C' : ℝ} (hC' : 0 ≤ C')
    (hL : (1 + ‖η‖) ^ d * ‖L‖ ≤ C' * (1 + ‖η‖) ^ k₀) :
    (1 + ‖η‖) ^ (d + 1) * ‖c * (∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)) * L‖ ≤
      ‖c‖ * ((2 * π) ^ k * ∏ l, ‖m l‖) * C' * (1 + ‖η‖) ^ (k₀ + M) := by
  have hw : 1 ≤ 1 + ‖η‖ := le_add_of_nonneg_right (norm_nonneg η)
  have hpr : ‖∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)‖ ≤ (2 * π) ^ k * (∏ l, ‖m l‖) * (1 + ‖η‖) ^ k :=
    (norm_prod_two_pi_I_inner_le _ _).trans (by gcongr; linarith)
  calc (1 + ‖η‖) ^ (d + 1) * ‖c * (∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)) * L‖
      = ‖c‖ * ‖∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)‖ * (1 + ‖η‖) * ((1 + ‖η‖) ^ d * ‖L‖) := by
        rw [norm_mul, norm_mul]
        ring
    _ ≤ ‖c‖ * ((2 * π) ^ k * (∏ l, ‖m l‖) * (1 + ‖η‖) ^ k) * (1 + ‖η‖) *
          (C' * (1 + ‖η‖) ^ k₀) := by gcongr
    _ = ‖c‖ * ((2 * π) ^ k * ∏ l, ‖m l‖) * C' * (1 + ‖η‖) ^ (k₀ + (k + 1)) := by ring
    _ ≤ _ := by gcongr

omit [InnerProductSpace ℝ E] in
/-- The arithmetic of the symbol identity for systems at large frequencies: bounds on the three
groups of terms of `X - Y - Y'` in terms of `D` with `D w ^ M = Z B` give the bound
`Z (r CP + G' (S₁ + S₂)) B w ^ k₀` on `w ^ (d + 1) ‖X - Y - Y'‖`. -/
private theorem mul_norm_sub_sub_le {X Y Y' : ℂ} {w : ℝ} (hw : 1 ≤ w) {d k₀ M : ℕ}
    {r CP S₁ S₂ G' D Z B : ℝ} (hr : 0 ≤ r) (hCP : 0 ≤ CP) (hD0 : 0 ≤ D) (hD : D * w ^ M = Z * B)
    (hX : w ^ (d + 1) * ‖X‖ ≤ r * (CP * D))
    (hY : w ^ (d + 1) * ‖Y‖ ≤ S₁ * (G' * D) * w ^ (k₀ + M))
    (hY' : w ^ (d + 1) * ‖Y'‖ ≤ S₂ * (G' * D) * w ^ (k₀ + M)) :
    w ^ (d + 1) * ‖X - Y - Y'‖ ≤ Z * (r * CP + G' * (S₁ + S₂)) * B * w ^ k₀ := by
  have hDle : D ≤ D * w ^ M * w ^ k₀ :=
    le_mul_of_one_le_right hD0 (one_le_pow₀ hw) |>.trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hw))
  calc w ^ (d + 1) * ‖X - Y - Y'‖
      ≤ w ^ (d + 1) * ‖X‖ + w ^ (d + 1) * ‖Y‖ + w ^ (d + 1) * ‖Y'‖ := by
        rw [← mul_add, ← mul_add]
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ r * (CP * (D * w ^ M * w ^ k₀)) + S₁ * (G' * D) * w ^ (k₀ + M) +
          S₂ * (G' * D) * w ^ (k₀ + M) :=
        add_le_add (add_le_add (hX.trans (by gcongr)) hY) hY'
    _ = Z * (r * CP + G' * (S₁ + S₂)) * B * w ^ k₀ := by
        rw [pow_add]
        linear_combination (r * CP + G' * (S₁ + S₂)) * w ^ k₀ * hD

/-- **The regularity step at large frequencies.** Let the cutoffs `Ψ j`, supported in `K`, satisfy
`∑ j, A i j Ψ j = δ_iq φ` for the matrix `A` of the terms of order `M` of the full symbol of the
system at the frequency `η ∈ Γ`, with derivatives of order at most `n` bounded by
`Z B / (1 + ‖η‖) ^ M`. Suppose that the localized Fourier transforms of every `(P T) j` are
`O(B' / (1 + ‖η‖) ^ (d + 1))` and those of every `T i` are `O(B' (1 + ‖η‖) ^ k₀ / (1 + ‖η‖) ^ d)` on
`Γ` for the cutoffs supported in `K` with derivatives bounded by `B'`, and that the errors of
`exists_localFourier_iteratedLineDerivOp_sub_le` are bounded accordingly. Then
`L(T q, φ)` is `O(B (1 + ‖η‖) ^ k₀ / (1 + ‖η‖) ^ (d + 1))`, by the symbol identity
`localFourier_eq_sum_sub_sum_sub_sum`. -/
private theorem one_add_norm_pow_succ_mul_norm_localFourier_le {ι τ : Type*} [Fintype ι]
    [DecidableEq ι] {s : Finset τ} {c : ι → ι → τ → ℂ} {g : ι → ι → τ → E → ℝ}
    (hg : ∀ i j a, ContDiff ℝ ∞ (g i j a)) {k : τ → ℕ} {m : ∀ a, Fin (k a) → E} {M : ℕ}
    (hk : ∀ a ∈ s, k a ≤ M) {T : ι → 𝓓'(Ω, ℂ)} {K Γ : Set E} {n rP ρ d k₀ : ℕ}
    (hn : ρ + M ≤ n) (hrP : rP ≤ n) {CP C G : ℝ} (hCP0 : 0 ≤ CP) (hC : 0 ≤ C) (hG0 : 0 ≤ G)
    (hCP : ∀ j, ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ K → ∀ B : ℝ,
      (∀ l ≤ rP, ∀ y, ‖iteratedFDeriv ℝ l φ y‖ ≤ B) → ∀ η ∈ Γ, (1 + ‖η‖) ^ (d + 1) *
        ‖(∑ i, ∑ a ∈ s, c i j a • smulLeftCLM (hg i j a) (∂^{m a} (T i))).localFourier φ η‖ ≤
          CP * B)
    (hG : ∀ i j, ∀ a ∈ s, ∀ l ≤ n, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ l (fun y ↦ (g i j a y : ℂ)) y‖ ≤ G)
    (hT : ∀ i, ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ K → ∀ B : ℝ,
      (∀ l ≤ ρ, ∀ y, ‖iteratedFDeriv ℝ l φ y‖ ≤ B) →
        ∀ η ∈ Γ, (1 + ‖η‖) ^ d * ‖(T i).localFourier φ η‖ ≤ C * B * (1 + ‖η‖) ^ k₀)
    {Cd : ι → τ → ℝ} (hCd0 : ∀ i a, 0 ≤ Cd i a) (hCd : ∀ i a, ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ K →
      ∀ B : ℝ, (∀ l ≤ ρ + k a, ∀ y, ‖iteratedFDeriv ℝ l φ y‖ ≤ B) → ∀ η ∈ Γ,
        (1 + ‖η‖) ^ (d + 1) * ‖(∂^{m a} (T i)).localFourier φ η -
          (∏ l, (2 * π * I * ⟪m a l, η⟫ : ℂ)) * (T i).localFourier φ η‖ ≤
            Cd i a * B * (1 + ‖η‖) ^ (k₀ + k a))
    {φ : 𝓓(Ω, ℂ)} {q : ι} {η : E} (hη : η ∈ Γ) {Ψ : ι → 𝓓(Ω, ℂ)}
    (hΨK : ∀ j, tsupport (Ψ j) ⊆ K)
    (hΨ : ∀ i y, ∑ j, topSymbolMatrix s c g m M y η i j * Ψ j y = if i = q then φ y else 0)
    {Z B : ℝ} (hZB : 0 ≤ Z * B)
    (hΨB : ∀ j, ∀ l ≤ n, ∀ y, ‖iteratedFDeriv ℝ l (Ψ j) y‖ ≤ Z * B / (1 + ‖η‖) ^ M) :
    (1 + ‖η‖) ^ (d + 1) * ‖(T q).localFourier φ η‖ ≤
      Z * (Fintype.card ι * CP + 2 ^ n * G * ((∑ j, ∑ i, ∑ a ∈ s, ‖c i j a‖ * Cd i a) +
        ∑ j, ∑ i, ∑ a ∈ s with k a ≠ M, ‖c i j a‖ * ((2 * π) ^ k a * ∏ l, ‖m a l‖) * C)) * B *
        (1 + ‖η‖) ^ k₀ := by
  set D := Z * B / (1 + ‖η‖) ^ M
  have hD0 : 0 ≤ D := by positivity
  have hgΨ (i j : ι) (a : τ) (ha : a ∈ s) : ∀ l ≤ n, ∀ y,
      ‖iteratedFDeriv ℝ l (TestFunction.smulLeftCLM (hg i j a) (Ψ j)) y‖ ≤ 2 ^ n * G * D :=
    norm_iteratedFDeriv_smulLeftCLM_le (hg i j a) (Ψ j) (hΨK j) hG0
      (fun l hl y hy ↦ hG i j a ha l hl y hy) (hΨB j)
  have hgΨK (i j : ι) (a : τ) : tsupport (TestFunction.smulLeftCLM (hg i j a) (Ψ j)) ⊆ K :=
    (tsupport_smulLeftCLM_subset (hg i j a) (Ψ j)).trans (inter_subset_right.trans (hΨK j))
  have hw0 : 0 ≤ (1 + ‖η‖) ^ (d + 1) := by positivity
  rw [localFourier_eq_sum_sub_sum_sub_sum s c hg m M T hΨ]
  refine mul_norm_sub_sub_le (d := d) (k₀ := k₀) (M := M) (r := Fintype.card ι)
    (G' := 2 ^ n * G) (le_add_of_nonneg_right (norm_nonneg η)) (by positivity) hCP0 hD0
    (div_mul_cancel₀ _ (by positivity))
    -- The terms with `(P T) j`.
    ((mul_norm_sum_le_of_le hw0 fun j _ ↦ hCP j (Ψ j) (hΨK j) D
      (fun l hl y ↦ hΨB j l (hl.trans hrP) y) η hη).trans_eq (by simp))
    -- The errors of `exists_localFourier_iteratedLineDerivOp_sub_le`.
    ((mul_norm_sum_le_of_le hw0 fun j _ ↦ mul_norm_sum_le_of_le hw0 fun i _ ↦
      mul_norm_sum_le_of_le (b := fun a ↦ ‖c i j a‖ * (Cd i a * (2 ^ n * G * D) *
        (1 + ‖η‖) ^ (k₀ + M))) hw0 fun a ha ↦ by
        rw [norm_mul, mul_left_comm]
        refine mul_le_mul_of_nonneg_left ((hCd i a _ (hgΨK i j a) _
          (fun l hl ↦ hgΨ i j a ha l (hl.trans (by have := hk a ha; omega))) η hη).trans ?_)
          (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀
          (le_add_of_nonneg_right (norm_nonneg η)) (by have := hk a ha; omega))
          (by have := hCd0 i a; positivity)).trans_eq (by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
        Finset.sum_congr rfl fun _ _ ↦ by ring))
    -- The terms of order less than `M`.
    ((mul_norm_sum_le_of_le hw0 fun j _ ↦ mul_norm_sum_le_of_le hw0 fun i _ ↦
      mul_norm_sum_le_of_le hw0 fun a ha ↦
        one_add_norm_pow_succ_mul_norm_mul_prod_mul_le (M := M) (d := d) (k₀ := k₀)
          (by have := hk a (Finset.mem_filter.1 ha).1; have := (Finset.mem_filter.1 ha).2; omega)
          (c i j a) (m a) (by positivity) (hT i _ (hgΨK i j a) _ (fun l hl ↦
            hgΨ i j a (Finset.mem_filter.1 ha).1 l
              (hl.trans ((Nat.le_add_right ρ M).trans hn))) η hη)).trans_eq (by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
        Finset.sum_congr rfl fun _ _ ↦ by ring))

/-- **One step of the regularity induction for systems.** Let the system
`(P T) j = ∑ i, ∑ a ∈ s, c i j a g i j a ∂^(m a) (T i)` have orders at most `M`, and suppose that
on an open set `W ⊇ K` the determinant of the matrix of the terms of order `M` of its full symbol
is bounded below by `c' (1 + ‖η‖) ^ (M card ι)` for `η ∈ Γ` outside a ball, and that the localized
Fourier transforms of every `(P T) j` decay rapidly on `Γ`, uniformly over the cutoffs supported in
the compact set `K` with bounded derivatives. If those of every `T i` are
`O(B (1 + ‖η‖) ^ k₀ / (1 + ‖η‖) ^ d)` on `Γ`, uniformly over the cutoffs supported in `K` whose
derivatives of order at most `ρ` are bounded by `B`, then they are
`O(B (1 + ‖η‖) ^ k₀ / (1 + ‖η‖) ^ (d + 1))` for the cutoffs whose derivatives of some larger
order `ρ'` are bounded by `B`. At large frequencies, divide the cutoff by the principal symbol
matrix (`exists_forall_exists_sum_topSymbolMatrix_mul_eq_ite`) and apply
`one_add_norm_pow_succ_mul_norm_localFourier_le`. -/
private theorem exists_localFourier_le_succ {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    {s : Finset τ} {c : ι → ι → τ → ℂ} {g : ι → ι → τ → E → ℝ}
    (hg : ∀ i j a, ContDiff ℝ ∞ (g i j a)) {k : τ → ℕ} {m : ∀ a, Fin (k a) → E} {M : ℕ}
    (hk : ∀ a ∈ s, k a ≤ M) {T : ι → 𝓓'(Ω, ℂ)} {K W Γ : Set E} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W)
    (hP : ∀ N : ℕ, ∃ (r : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ j, ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ K → ∀ B : ℝ,
      (∀ l ≤ r, ∀ y, ‖iteratedFDeriv ℝ l φ y‖ ≤ B) → ∀ η ∈ Γ, (1 + ‖η‖) ^ N *
        ‖(∑ i, ∑ a ∈ s, c i j a • smulLeftCLM (hg i j a) (∂^{m a} (T i))).localFourier φ η‖ ≤
          C * B)
    {R c' : ℝ} (hc' : 0 < c') (hp : ∀ y ∈ W, ∀ η ∈ Γ, R ≤ ‖η‖ →
      c' * (1 + ‖η‖) ^ (M * Fintype.card ι) ≤ ‖(topSymbolMatrix s c g m M y η).det‖)
    {d k₀ ρ : ℕ} {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ K → ∀ B : ℝ,
      (∀ l ≤ ρ, ∀ y, ‖iteratedFDeriv ℝ l φ y‖ ≤ B) →
        ∀ η ∈ Γ, (1 + ‖η‖) ^ d * ‖(T i).localFourier φ η‖ ≤ C * B * (1 + ‖η‖) ^ k₀) :
    ∃ (ρ' : ℕ) (C' : ℝ), 0 ≤ C' ∧ ∀ i, ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ K → ∀ B : ℝ,
      (∀ l ≤ ρ', ∀ y, ‖iteratedFDeriv ℝ l φ y‖ ≤ B) →
        ∀ η ∈ Γ, (1 + ‖η‖) ^ (d + 1) * ‖(T i).localFourier φ η‖ ≤ C' * B * (1 + ‖η‖) ^ k₀ := by
  obtain ⟨rP, CP, hCP0, hCP⟩ := hP (d + 1)
  set n := max (ρ + M) rP
  obtain ⟨Z, hZ0, hZ⟩ :=
    exists_forall_exists_sum_topSymbolMatrix_mul_eq_ite (Ω := Ω) hg hk hK hW hKW hc' hp n
  obtain ⟨G, hG0, hG⟩ := exists_forall_norm_iteratedFDeriv_le_of_isCompact
    (Finset.univ ×ˢ Finset.univ ×ˢ s) (f := fun x : ι × ι × τ ↦ fun y ↦ (g x.1 x.2.1 x.2.2 y : ℂ))
    (n := n) (fun x _ ↦ (ofRealCLM.contDiff.comp (hg _ _ _)).of_le (by exact_mod_cast le_top)) hK
  choose Cd hCd0 hCd using fun (i : ι) (a : τ) ↦
    exists_localFourier_iteratedLineDerivOp_sub_le hC (hT i) (m a)
  set S := (∑ j, ∑ i, ∑ a ∈ s, ‖c i j a‖ * Cd i a) +
    ∑ j, ∑ i, ∑ a ∈ s with k a ≠ M, ‖c i j a‖ * ((2 * π) ^ k a * ∏ l, ‖m a l‖) * C
  have hS : 0 ≤ S := add_nonneg (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (hCd0 _ _)) (by positivity)
  refine ⟨n, max ((1 + R) * C) (Z * (Fintype.card ι * CP + 2 ^ n * G * S)),
    le_max_of_le_right (by positivity), fun q φ hφ B hB η hη ↦ ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  rcases lt_or_ge ‖η‖ R with hηR | hηR
  · refine (one_add_norm_pow_succ_mul_le hηR
      (hT q φ hφ B (fun l hl ↦ hB l (by omega)) η hη)).trans ?_
    rw [← mul_assoc]
    gcongr
    exact le_max_left _ _
  -- At large frequencies, divide the cutoff by the principal symbol matrix.
  obtain ⟨Ψ, hΨK, hΨ, hΨB⟩ := hZ φ hφ B (fun l hl ↦ hB l hl) η hη hηR q
  refine (one_add_norm_pow_succ_mul_norm_localFourier_le hg hk (le_max_left _ _)
    (le_max_right _ _) hCP0 hC hG0 hCP (fun i j a ha ↦ hG (i, j, a) (by simp [ha])) hT hCd0 hCd
    hη hΨK hΨ (by positivity) hΨB).trans ?_
  gcongr
  exact le_max_right _ _

/-! ### Microlocal elliptic regularity -/

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- **An elliptic cone for a system.** If the matrix of the principal symbols of the entries of a
system, with the coefficients frozen at `x`, is invertible at `ξ`, then for `y` near `x` and `η` in
an open cone around `ξ` with `1 ≤ ‖η‖`, the determinant of the matrix of the terms of order `M` of
the full symbol is bounded below by a multiple of `(1 + ‖η‖) ^ (M card ι)`. -/
private theorem exists_nhds_cone_le_norm_det_topSymbolMatrix {ι τ : Type*} [Fintype ι]
    [DecidableEq ι] {s : Finset τ} {c : ι → ι → τ → ℂ} {g : ι → ι → τ → E → ℝ}
    (hg : ∀ i j a, Continuous (g i j a)) {k : τ → ℕ} {m : ∀ a, Fin (k a) → E} {M : ℕ} {x ξ : E}
    (hξ : (Matrix.of fun i j ↦ principalSymbol s (fun a y ↦ c i j a * g i j a y) m M x ξ).det ≠ 0) :
    ∃ U ∈ 𝓝 x, ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∃ c' : ℝ, 0 < c' ∧ ∀ y ∈ U, ∀ η ∈ Γ, 1 ≤ ‖η‖ →
        c' * (1 + ‖η‖) ^ (M * Fintype.card ι) ≤ ‖(topSymbolMatrix s c g m M y η).det‖ := by
  set N := M * Fintype.card ι
  set σ : E × E → Matrix ι ι ℂ := fun p ↦
    Matrix.of fun i j ↦ principalSymbol s (fun a y ↦ c i j a * g i j a y) m M p.1 p.2
  have hb (i j : ι) (a : τ) : Continuous fun y ↦ c i j a * (g i j a y : ℂ) :=
    continuous_const.mul (continuous_ofReal.comp (hg i j a))
  -- The determinant of the principal symbol matrix is homogeneous of degree `N`.
  have hσc : Continuous fun p ↦ (σ p).det := Continuous.matrix_det <|
    continuous_pi fun i ↦ continuous_pi fun j ↦ continuous_principalSymbol s (hb i j) m M
  have hσh (y η : E) (t : ℝ) (_ : 0 < t) : (σ (y, t • η)).det = (t : ℂ) ^ N * (σ (y, η)).det := by
    have h : σ (y, t • η) = ((t : ℂ) ^ M) • σ (y, η) := by
      ext i j
      simp [σ, principalSymbol_smul]
    rw [h, Matrix.det_smul, ← pow_mul]
  obtain ⟨U, hU, Γ, hΓ, hξΓ, hcone, c₀, hc₀, hell⟩ :=
    exists_nhds_cone_le_norm_of_continuous_of_homogeneous hσc hσh hξ
  refine ⟨U, hU, Γ, hΓ, hξΓ, hcone, (2 * π) ^ N * c₀ / 2 ^ N, by positivity,
    fun y hy η hη h1 ↦ ?_⟩
  -- The terms of order `M` are `(2πi) ^ M` times the principal symbols.
  have htop : topSymbolMatrix s c g m M y η = ((2 * π * I) ^ M) • σ (y, η) := by
    ext i j
    simp only [topSymbolMatrix, σ, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      principalSymbol_def, constCoeffPrincipalSymbol_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    have hpow : (2 * π * I : ℂ) ^ k a = (2 * π * I) ^ M := by rw [(Finset.mem_filter.1 ha).2]
    rw [prod_two_pi_I_inner, hpow]
    ring
  have h2π : ‖(2 * π * I : ℂ)‖ = 2 * π := by simp [abs_of_pos pi_pos]
  have hpow : (1 + ‖η‖) ^ N ≤ 2 ^ N * ‖η‖ ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) N
  rw [htop, Matrix.det_smul, norm_mul, norm_pow, norm_pow, h2π, ← pow_mul]
  calc (2 * π) ^ N * c₀ / 2 ^ N * (1 + ‖η‖) ^ N ≤ (2 * π) ^ N * c₀ / 2 ^ N * (2 ^ N * ‖η‖ ^ N) := by
        gcongr
    _ = (2 * π) ^ N * (c₀ * ‖η‖ ^ N) := by field_simp
    _ ≤ (2 * π) ^ N * ‖(σ (y, η)).det‖ := by gcongr; exact hell y hy η hη

/-- **Microlocal elliptic regularity for systems of differential operators** (Hörmander I,
Theorem 8.3.1; Taylor, Lecture I, §7). Let `P` be the square system
`(P T) j = ∑ i, ∑ a ∈ s, c i j a g i j a ∂^(m a) (T i)` with smooth real coefficients `g i j a`,
complex constants `c i j a` and orders `k a ≤ M`, and let `ξ` be noncharacteristic for `P` at `x`:
the matrix of the principal symbols of its entries with the coefficients frozen at `x`,
`principalSymbol s (fun a y ↦ c i j a * g i j a y) m M x ξ`, is invertible. If every component
`(P T) j` is microlocally smooth at `(x, ξ)`, then so is every component `T i`. -/
theorem IsMicrolocallySmoothAt.of_sum_sum_smul_smulLeftCLM_iteratedLineDerivOp {ι τ : Type*}
    [Fintype ι] [DecidableEq ι] {s : Finset τ} {c : ι → ι → τ → ℂ} {g : ι → ι → τ → E → ℝ}
    (hg : ∀ i j a, ContDiff ℝ ∞ (g i j a)) {k : τ → ℕ} {m : ∀ a, Fin (k a) → E} {M : ℕ}
    (hk : ∀ a ∈ s, k a ≤ M) {T : ι → 𝓓'(Ω, ℂ)} {x ξ : E}
    (hP : ∀ j, (∑ i, ∑ a ∈ s, c i j a • Distribution.smulLeftCLM (hg i j a)
      (∂^{m a} (T i))).IsMicrolocallySmoothAt x ξ)
    (hξ : (Matrix.of fun i j ↦ principalSymbol s (fun a y ↦ c i j a * g i j a y) m M x ξ).det ≠ 0)
    (i : ι) : (T i).IsMicrolocallySmoothAt x ξ := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySmoothAt_iff.1 (hP i)
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U₁, hU₁, Γ₁, hΓ₁, hξ₁, hcone₁, c', hc', hp⟩ :=
    exists_nhds_cone_le_norm_det_topSymbolMatrix (fun i j a ↦ (hg i j a).continuous) hξ
  obtain ⟨U₂, hU₂, Γ₂, hΓ₂, hξ₂, hcone₂, hdecay⟩ :=
    exists_nhds_cone_forall_forall_one_add_norm_pow_mul_norm_localFourier_le hP
  -- Compact neighbourhoods `K ⊆ W = interior K'` of `x`, with `K' ⊆ U₁ ∩ U₂ ∩ Ω`.
  obtain ⟨K', hK'x, hK'sub, -⟩ :=
    local_compact_nhds (inter_mem (inter_mem hU₁ hU₂) (Ω.isOpen.mem_nhds hx))
  obtain ⟨K, hKx, hKW, hKc⟩ := local_compact_nhds (interior_mem_nhds.2 hK'x)
  have hKΩ : K ⊆ Ω := hKW.trans (interior_subset.trans (hK'sub.trans inter_subset_right))
  have hKU₂ : K ⊆ U₂ := hKW.trans (interior_subset.trans (hK'sub.trans
    (inter_subset_left.trans inter_subset_right)))
  -- By induction on `d`, the localized Fourier transforms of every `T i` with cutoffs supported
  -- in `K` are `O((1 + ‖η‖) ^ k₀ / (1 + ‖η‖) ^ d)` on `Γ₁ ∩ Γ₂`, uniformly over bounded cutoffs.
  choose k₀' C₀ hC₀ h₀ using fun i ↦ exists_forall_norm_localFourier_le (T i) (K := ⟨K, hKc⟩) hKΩ
  set k₀ := ∑ i, k₀' i
  have hind (d : ℕ) : ∃ (ρ : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ i, ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ K → ∀ B : ℝ,
      (∀ l ≤ ρ, ∀ y, ‖iteratedFDeriv ℝ l φ y‖ ≤ B) → ∀ η ∈ Γ₁ ∩ Γ₂,
        (1 + ‖η‖) ^ d * ‖(T i).localFourier φ η‖ ≤ C * B * (1 + ‖η‖) ^ k₀ := by
    induction d with
    | zero =>
      refine ⟨k₀, ∑ i, C₀ i, Finset.sum_nonneg fun i _ ↦ hC₀ i, fun i φ hφ B hB η _ ↦ ?_⟩
      have hki : k₀' i ≤ k₀ := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
      rw [pow_zero, one_mul]
      refine (h₀ i φ hφ B (fun l hl ↦ hB l (hl.trans hki)) η).trans <|
        mul_le_mul (mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun i _ ↦ hC₀ i) (Finset.mem_univ i)) hB0)
          (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg η)) hki) (by positivity)
          (mul_nonneg (Finset.sum_nonneg fun i _ ↦ hC₀ i) hB0)
    | succ d ih =>
      obtain ⟨ρ, C, hC, hT⟩ := ih
      refine exists_localFourier_le_succ (Γ := Γ₁ ∩ Γ₂) (R := 1) hg hk hKc isOpen_interior hKW
        (fun N ↦ ?_) hc' (fun y hy η hη h1 ↦ hp y (hK'sub (interior_subset hy)).1.1 η hη.1 h1)
        hC hT
      obtain ⟨r, C', hC', h⟩ := hdecay N
      exact ⟨r, C', hC', fun j φ hφ B hB η hη ↦ h j φ (hφ.trans hKU₂) B hB η hη.2⟩
  obtain ⟨φ, hφK, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤) hKx hKΩ (1 : ℂ)
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], Γ₁ ∩ Γ₂, hΓ₁.inter hΓ₂, ⟨hξ₁, hξ₂⟩,
    fun t ht η hη ↦ ⟨hcone₁ t ht η hη.1, hcone₂ t ht η hη.2⟩, fun N ↦ ?_⟩
  obtain ⟨ρ, C, -, h⟩ := hind (k₀ + N)
  obtain ⟨B, -, hB⟩ := φ.hasCompactSupport.exists_bound_iteratedFDeriv_of_contDiff
    (φ.contDiff.of_le (m := ρ) (by exact_mod_cast le_top))
  refine ⟨C * B, fun η hη ↦ ?_⟩
  have hpos : 0 < (1 + ‖η‖) ^ k₀ := by positivity
  refine le_of_mul_le_mul_left ?_ hpos
  calc (1 + ‖η‖) ^ k₀ * ((1 + ‖η‖) ^ N * ‖(T i).localFourier φ η‖)
      = (1 + ‖η‖) ^ (k₀ + N) * ‖(T i).localFourier φ η‖ := by ring
    _ ≤ C * B * (1 + ‖η‖) ^ k₀ := h i φ hφK B hB η hη
    _ = (1 + ‖η‖) ^ k₀ * (C * B) := mul_comm _ _

/-- **Microlocal elliptic regularity for systems of differential operators**: for the square
system `(P T) j = ∑ i, ∑ a ∈ s, c i j a g i j a ∂^(m a) (T i)` with smooth real coefficients and
orders `k a ≤ M`, every component satisfies `WF(T i) ⊆ (⋃ j, WF((P T) j)) ∪ Char(P)`, where
`Char(P)` is the set of `(x, ξ)` with `ξ ≠ 0` at which the matrix of the principal symbols of the
entries, with the coefficients frozen at `x`, is not invertible. -/
theorem waveFrontSet_subset_iUnion_waveFrontSet_sum_sum_smul_smulLeftCLM_iteratedLineDerivOp_union
    {ι τ : Type*} [Fintype ι] [DecidableEq ι] (s : Finset τ) (c : ι → ι → τ → ℂ)
    {g : ι → ι → τ → E → ℝ} (hg : ∀ i j a, ContDiff ℝ ∞ (g i j a)) {k : τ → ℕ}
    (m : ∀ a, Fin (k a) → E) {M : ℕ} (hk : ∀ a ∈ s, k a ≤ M) (T : ι → 𝓓'(Ω, ℂ)) (i : ι) :
    (T i).waveFrontSet ⊆
      (⋃ j, (∑ i, ∑ a ∈ s, c i j a • smulLeftCLM (hg i j a) (∂^{m a} (T i))).waveFrontSet) ∪
        {p | p.2 ≠ 0 ∧ (Matrix.of fun i j ↦
          principalSymbol s (fun a y ↦ c i j a * g i j a y) m M p.1 p.2).det = 0} := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hT⟩ := mem_waveFrontSet_iff.1 hp
  by_contra h
  simp only [mem_union, mem_iUnion, mem_waveFrontSet_iff, mem_ofPred_eq, not_or, not_exists,
    not_and, not_not] at h
  exact hT (IsMicrolocallySmoothAt.of_sum_sum_smul_smulLeftCLM_iteratedLineDerivOp hg hk
    (fun j ↦ h.1 j hx hξ) (h.2 hξ) i)

/-- **Microlocal elliptic regularity for differential operators** (Hörmander I, Theorem 8.3.1).
Let `P = ∑ i ∈ s, c i a i ∂^(m i)` have smooth real coefficients `a i`, complex constants `c i` and
orders `k i ≤ M`, and let `ξ` be noncharacteristic for `P` at `x`: the principal symbol with the
coefficients frozen at `x`, `principalSymbol s (fun i y ↦ c i * a i y) m M x`, does not vanish at
`ξ`. If `P T` is microlocally smooth at `(x, ξ)`, then so is `T`. This is the system
`IsMicrolocallySmoothAt.of_sum_sum_smul_smulLeftCLM_iteratedLineDerivOp` with one component. -/
theorem IsMicrolocallySmoothAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp {ι : Type*}
    {s : Finset ι} {c : ι → ℂ} {a : ι → E → ℝ} (ha : ∀ i, ContDiff ℝ ∞ (a i)) {k : ι → ℕ}
    {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M) {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hP : (∑ i ∈ s, c i • Distribution.smulLeftCLM (ha i) (∂^{m i} T)).IsMicrolocallySmoothAt x ξ)
    (hξ : principalSymbol s (fun i y ↦ c i * a i y) m M x ξ ≠ 0) :
    T.IsMicrolocallySmoothAt x ξ :=
  IsMicrolocallySmoothAt.of_sum_sum_smul_smulLeftCLM_iteratedLineDerivOp (ι := Unit)
    (c := fun _ _ ↦ c) (fun _ _ ↦ ha) hk (T := fun _ ↦ T) (fun _ ↦ by simpa using hP)
    (by simpa using hξ) ()

/-- **Microlocal elliptic regularity for differential operators**: `WF(T) ⊆ WF(P T) ∪ Char(P)` for
`P = ∑ i ∈ s, c i a i ∂^(m i)` with smooth real coefficients `a i` and orders `k i ≤ M`, where
`Char(P) = characteristicSet s (fun i y ↦ c i * a i y) m M` is the set of `(x, ξ)` with `ξ ≠ 0` at
which the principal symbol with the coefficients frozen at `x` vanishes. -/
theorem waveFrontSet_subset_waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_union
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) {a : ι → E → ℝ} (ha : ∀ i, ContDiff ℝ ∞ (a i))
    {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M) (T : 𝓓'(Ω, ℂ)) :
    T.waveFrontSet ⊆ (∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T)).waveFrontSet ∪
      characteristicSet s (fun i y ↦ c i * a i y) m M := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hT⟩ := mem_waveFrontSet_iff.1 hp
  by_contra h
  rw [mem_union, not_or, mem_waveFrontSet_iff, mem_characteristicSet_iff] at h
  exact hT (IsMicrolocallySmoothAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp ha hk
    (by simpa [hx, hξ] using h.1) fun h0 ↦ h.2 ⟨hξ, h0⟩)

/-- **An elliptic differential operator preserves the wave front set.** If the principal symbol
of `P = ∑ i ∈ s, c i a i ∂^(m i)` of order `M`, with the coefficients frozen at any point of `Ω`,
vanishes at no `ξ ≠ 0`, then `WF(P T) = WF(T)`. -/
theorem waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) {a : ι → E → ℝ} (ha : ∀ i, ContDiff ℝ ∞ (a i)) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M)
    (hσ : ∀ x ∈ Ω, ∀ ξ : E, ξ ≠ 0 → principalSymbol s (fun i y ↦ c i * a i y) m M x ξ ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T)).waveFrontSet = T.waveFrontSet := by
  refine subset_antisymm (waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset s c ha m T)
    fun p hp ↦ ?_
  refine (waveFrontSet_subset_waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_union s c ha
    m hk T hp).resolve_right ?_
  exact fun h ↦ hσ p.1 (waveFrontSet_subset T hp).1 p.2 h.1 h.2

/-- **Elliptic regularity for differential operators.** If the principal symbol of
`P = ∑ i ∈ s, c i a i ∂^(m i)` of order `M`, with the coefficients frozen at any point of `Ω`,
vanishes at no `ξ ≠ 0`, then `P T` and `T` have the same singular support: `T` is a smooth function
near every point near which `P T` is. -/
theorem singularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} (s : Finset ι) (c : ι → ℂ) {a : ι → E → ℝ}
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ}
    (hk : ∀ i ∈ s, k i ≤ M)
    (hσ : ∀ x ∈ Ω, ∀ ξ : E, ξ ≠ 0 → principalSymbol s (fun i y ↦ c i * a i y) m M x ξ ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T)).singularSupport = T.singularSupport := by
  rw [← fst_image_waveFrontSet, ← fst_image_waveFrontSet,
    waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero s c ha m hk hσ]

/-- **Microlocal elliptic regularity for constant-coefficient operators** (Hörmander I,
Theorem 8.3.1). Let `P = ∑ i ∈ s, c i ∂^(m i)` have orders `k i ≤ M`, and let `ξ` be
noncharacteristic for `P`: the principal symbol `constCoeffPrincipalSymbol s c m M` does not
vanish at `ξ`. If `P T` is microlocally smooth at `(x, ξ)`, then so is `T`. -/
theorem IsMicrolocallySmoothAt.of_sum_smul_iteratedLineDerivOp {ι : Type*} {s : Finset ι}
    {c : ι → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M)
    {T : 𝓓'(Ω, ℂ)} {x ξ : E} (hP : (∑ i ∈ s, c i • ∂^{m i} T).IsMicrolocallySmoothAt x ξ)
    (hξ : constCoeffPrincipalSymbol s c m M ξ ≠ 0) :
    T.IsMicrolocallySmoothAt x ξ :=
  IsMicrolocallySmoothAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp (a := fun _ _ ↦ 1)
    (fun _ ↦ contDiff_const) hk (by simpa using hP) (by simpa using hξ)

/-- **Microlocal elliptic regularity for constant-coefficient operators**:
`WF(T) ⊆ WF(P T) ∪ Char(P)` for `P = ∑ i ∈ s, c i ∂^(m i)` with orders `k i ≤ M`, where
`Char(P) = constCoeffCharacteristicSet s c m M` is the set of `(x, ξ)` with `ξ ≠ 0` at which the
principal symbol vanishes. -/
theorem waveFrontSet_subset_waveFrontSet_sum_smul_iteratedLineDerivOp_union {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M)
    (T : 𝓓'(Ω, ℂ)) :
    T.waveFrontSet ⊆ (∑ i ∈ s, c i • ∂^{m i} T).waveFrontSet ∪
      constCoeffCharacteristicSet s c m M := by
  simpa using waveFrontSet_subset_waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_union s c
    (a := fun _ _ ↦ 1) (fun _ ↦ contDiff_const) m hk T

/-- **An elliptic constant-coefficient operator preserves the wave front set.** If the principal
symbol of `P = ∑ i ∈ s, c i ∂^(m i)` of order `M` vanishes at no `ξ ≠ 0`, then
`WF(P T) = WF(T)`. -/
theorem waveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M)
    (hσ : ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol s c m M ξ ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • ∂^{m i} T).waveFrontSet = T.waveFrontSet := by
  simpa using waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero s c
    (a := fun _ _ ↦ 1) (fun _ ↦ contDiff_const) m hk (fun _ _ ξ hξ ↦ by simpa using hσ ξ hξ) T

/-- **Elliptic regularity for constant-coefficient operators.** If the principal symbol of
`P = ∑ i ∈ s, c i ∂^(m i)` of order `M` vanishes at no `ξ ≠ 0`, then `P T` and `T` have the same
singular support: `T` is a smooth function near every point near which `P T` is. -/
theorem singularSupport_sum_smul_iteratedLineDerivOp_of_forall_ne_zero [MeasurableSpace E]
    [BorelSpace E] {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E)
    {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M)
    (hσ : ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol s c m M ξ ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • ∂^{m i} T).singularSupport = T.singularSupport := by
  simpa using singularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero s c
    (a := fun _ _ ↦ 1) (fun _ ↦ contDiff_const) m hk (fun _ _ ξ hξ ↦ by simpa using hσ ξ hξ) T

/-- **The Laplacian preserves the wave front set.** The Laplacian
`Δ = LineDeriv.laplacianCLM ℝ E 𝓓'(Ω, ℂ)`, which is `∑ i, ∂_{b i} ∂_{b i}` for any orthonormal
basis `b`, satisfies `WF(Δ T) = WF(T)`: its principal symbol `∑ i, ⟪b i, ξ⟫ ^ 2 = ‖ξ‖ ^ 2`
vanishes only at `ξ = 0`. -/
@[simp]
theorem waveFrontSet_laplacianCLM (T : 𝓓'(Ω, ℂ)) :
    (laplacianCLM ℝ E 𝓓'(Ω, ℂ) T).waveFrontSet = T.waveFrontSet := by
  set b := stdOrthonormalBasis ℝ E
  have h := waveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero Finset.univ (fun _ ↦ 1)
    (k := fun _ ↦ 2) (fun i ↦ ![b i, b i]) (M := 2) (fun _ _ ↦ le_rfl) (fun ξ hξ ↦ ?_) T
  · simpa [laplacianCLM_eq_sum_iteratedLineDerivOp b] using h
  rw [constCoeffPrincipalSymbol_laplacian]
  exact_mod_cast (pow_pos (norm_pos_iff.2 hξ) 2).ne'

/-- **Elliptic regularity for the Laplacian.** `Δ T` and `T` have the same singular support. -/
@[simp]
theorem singularSupport_laplacianCLM [MeasurableSpace E] [BorelSpace E] (T : 𝓓'(Ω, ℂ)) :
    (laplacianCLM ℝ E 𝓓'(Ω, ℂ) T).singularSupport = T.singularSupport := by
  rw [← fst_image_waveFrontSet, ← fst_image_waveFrontSet, waveFrontSet_laplacianCLM]

/-! ### Smoothness of solutions -/

/-- **Elliptic differential operators are hypoelliptic.** If the principal symbol of
`P = ∑ i ∈ s, c i a i ∂^(m i)` of order `M`, with the coefficients frozen at any point of `Ω`,
vanishes at no `ξ ≠ 0`, and `P T` is a function smooth on `Ω`, then so is `T`. -/
theorem exists_contDiffOn_eq_ofFun_of_sum_smul_smulLeftCLM_iteratedLineDerivOp_eq_ofFun
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} (s : Finset ι) (c : ι → ℂ) {a : ι → E → ℝ}
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ}
    (hk : ∀ i ∈ s, k i ≤ M)
    (hσ : ∀ x ∈ Ω, ∀ ξ : E, ξ ≠ 0 → principalSymbol s (fun i y ↦ c i * a i y) m M x ξ ≠ 0)
    {T : 𝓓'(Ω, ℂ)} {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g Ω)
    (hT : ∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T) = ofFun Ω g MeasureTheory.volume ⊤) :
    ∃ f : E → ℂ, ContDiffOn ℝ ∞ f Ω ∧ T = ofFun Ω f MeasureTheory.volume ⊤ := by
  rw [← singularSupport_eq_empty_iff,
    ← singularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero s c ha m hk hσ,
    hT]
  exact singularSupport_ofFun_eq_empty hg

/-- **Solutions of elliptic equations are smooth.** If the principal symbol of
`P = ∑ i ∈ s, c i a i ∂^(m i)` of order `M`, with the coefficients frozen at any point of `Ω`,
vanishes at no `ξ ≠ 0`, then every distributional solution of `P T = 0` is a function smooth
on `Ω`. -/
theorem exists_contDiffOn_eq_ofFun_of_sum_smul_smulLeftCLM_iteratedLineDerivOp_eq_zero
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} (s : Finset ι) (c : ι → ℂ) {a : ι → E → ℝ}
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ}
    (hk : ∀ i ∈ s, k i ≤ M)
    (hσ : ∀ x ∈ Ω, ∀ ξ : E, ξ ≠ 0 → principalSymbol s (fun i y ↦ c i * a i y) m M x ξ ≠ 0)
    {T : 𝓓'(Ω, ℂ)} (hT : ∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T) = 0) :
    ∃ f : E → ℂ, ContDiffOn ℝ ∞ f Ω ∧ T = ofFun Ω f MeasureTheory.volume ⊤ :=
  exists_contDiffOn_eq_ofFun_of_sum_smul_smulLeftCLM_iteratedLineDerivOp_eq_ofFun s c ha m hk hσ
    contDiffOn_const (hT.trans ofFun_zero.symm)

/-- **Solutions of elliptic constant-coefficient equations are smooth.** If the principal symbol
of `P = ∑ i ∈ s, c i ∂^(m i)` of order `M` vanishes at no `ξ ≠ 0`, then every distributional
solution of `P T = 0` is a function smooth on `Ω`. -/
theorem exists_contDiffOn_eq_ofFun_of_sum_smul_iteratedLineDerivOp_eq_zero [MeasurableSpace E]
    [BorelSpace E] {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E)
    {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M)
    (hσ : ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol s c m M ξ ≠ 0)
    {T : 𝓓'(Ω, ℂ)} (hT : ∑ i ∈ s, c i • ∂^{m i} T = 0) :
    ∃ f : E → ℂ, ContDiffOn ℝ ∞ f Ω ∧ T = ofFun Ω f MeasureTheory.volume ⊤ := by
  rw [← singularSupport_eq_empty_iff,
    ← singularSupport_sum_smul_iteratedLineDerivOp_of_forall_ne_zero s c m hk hσ, hT,
    singularSupport_zero]

/-- **Weyl's lemma for distributions.** Every distribution `T` with `Δ T = 0` on `Ω` is a function
smooth on `Ω`. -/
theorem exists_contDiffOn_eq_ofFun_of_laplacianCLM_eq_zero [MeasurableSpace E] [BorelSpace E]
    {T : 𝓓'(Ω, ℂ)} (hT : laplacianCLM ℝ E 𝓓'(Ω, ℂ) T = 0) :
    ∃ f : E → ℂ, ContDiffOn ℝ ∞ f Ω ∧ T = ofFun Ω f MeasureTheory.volume ⊤ := by
  rw [← singularSupport_eq_empty_iff, ← singularSupport_laplacianCLM, hT, singularSupport_zero]

end Distribution

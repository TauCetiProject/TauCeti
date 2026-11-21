/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
import TauCeti.Algebra.Ring.Commutator
import TauCeti.Geometry.Manifold.DifferentialForm.Squared
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# The de Rham operator `d + d*`

On an oriented Riemannian manifold `M` of dimension `m`, the **de Rham operator** `d + d*` acts on
smooth forms of all degrees `0, …, m`, written here as families `α = (α_k)_k` with `α_k` a smooth
`k`-form. Its degree-`k` component is

`((d + d*)α)_k = dα_(k-1) + d*α_(k+1)`,

where `d*` is the codifferential `TauCeti.SmoothForm.codifferential`, the first term is absent in
degree `0` and the second in the top degree. It is the basic example of a first-order elliptic
operator of Dirac type.

* **Its square is the Hodge Laplacian.** Since `dd = 0` and `d*d* = 0`, the cross terms cancel and
  `(d + d*)² = d*d + dd* = Δ` in every degree.
* **It is formally self-adjoint**, for the `L²` pairing summed over all degrees, because `d*` is
  the formal adjoint of `d`.
* **Its kernel is the harmonic forms**: a compactly supported family satisfies `(d + d*)α = 0`
  exactly when every `α_k` is harmonic, hence closed and coclosed.
* **Its principal symbol.** The commutator `c(f) = [d + d*, f]` with multiplication by a smooth
  function is built from `[d, f] = df ∧ ·` and `[d*, f] = -ι_(grad f)`, so it is the zeroth-order
  operator `df ∧ · - ι_(grad f)`; every double commutator `[[d + d*, f], g]` vanishes. In the
  convention `σ_geom(P)(df) = [P, f]` of first-order principal symbols, the symbol of `d + d*` at
  `ξ` is `σ(ξ) = ξ ∧ · - ι_ξ`. It satisfies the Clifford relation
  `c(f) c(g) + c(g) c(f) = -2 ⟪df, dg⟫`, so `σ(ξ)² = -|ξ|²`: the operator is of Dirac type and
  elliptic, and the Fourier symbol of `(d + d*)² = Δ` is `|ξ|² Id`, consistently with
  `TauCeti.SmoothForm.coe_lie_lie_hodgeLaplacian_funSMulₗ`.

The first three statements use only that `d` and `d*` square to zero, that `d*` is a formal
adjoint of `d` and that both preserve compact support. They are proved once for the operator
`D + δ` (`TauCeti.SmoothForm.diffAddCodiff`) of any families of differentials `D` and
codifferentials `δ` with these properties, in parallel with the Laplacian
`TauCeti.SmoothForm.laplacian`; the de Rham operator is the case `(d, d*)`.

## Main definitions

* `TauCeti.SmoothForm.diffAddCodiff`: the operator `D + δ` on forms of all degrees.
* `TauCeti.SmoothForm.deRhamOperator`: the de Rham operator `d + d*`.

## Main results

* `TauCeti.SmoothForm.diffAddCodiff_comp_diffAddCodiff`,
  `TauCeti.SmoothForm.deRhamOperator_comp_deRhamOperator`: `(D + δ)² = δD + Dδ` when `D` and `δ`
  square to zero, and `(d + d*)² = Δ`.
* `TauCeti.SmoothForm.sum_integralTopForm_inner_diffAddCodiff_eq_inner_diffAddCodiff`,
  `TauCeti.SmoothForm.sum_integralTopForm_inner_deRhamOperator_eq_inner_deRhamOperator`:
  `D + δ` and `d + d*` are formally self-adjoint.
* `TauCeti.SmoothForm.diffAddCodiff_eq_zero_iff`, `TauCeti.SmoothForm.deRhamOperator_eq_zero_iff`:
  the kernel of `d + d*` on compactly supported forms consists of the harmonic forms.
* `TauCeti.SmoothForm.lie_diffAddCodiff_piMap`,
  `TauCeti.SmoothForm.lie_deRhamOperator_piMap_funSMulₗ`:
  the commutator of `D + δ` with a degreewise operator, and the symbol of `d + d*`.
* `TauCeti.SmoothForm.coe_lie_deRhamOperator_piMap_funSMulₗ_apply_add_one_add_one` and its
  boundary-degree cases: the symbol `[d + d*, f] = df ∧ · - ι_(grad f)` degree by degree.
* `TauCeti.SmoothForm.lie_lie_deRhamOperator_piMap_funSMulₗ_eq_zero`: `d + d*` has order one.
* `TauCeti.SmoothForm.coe_lie_deRhamOperator_piMap_funSMulₗ_mul_add_mul_apply`,
  `TauCeti.SmoothForm.coe_lie_deRhamOperator_piMap_funSMulₗ_mul_self_apply`: the Clifford
  relation of the symbol, so `d + d*` is of Dirac type.
* `TauCeti.SmoothForm.apply_eq_zero_of_lie_deRhamOperator_piMap_funSMulₗ_apply_eq_zero`:
  `d + d*` is elliptic.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1–6.2.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989),
  Chapter II, §5.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {m k l : ℕ}

namespace SmoothForm

/-! ### The operator `D + δ` on forms of all degrees -/

section DiffAddCodiff

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable (D : ∀ k, SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ (k + 1))
  (δ : ∀ {k l : ℕ}, k + 1 + l = m → SmoothForm I M ℝ (k + 1) →ₗ[ℝ] SmoothForm I M ℝ k)

/-- The degree-`k` component `Dα_(k-1) + δα_(k+1)` of `D + δ`, on a manifold of dimension
`m = k + l`. -/
private def diffAddCodiffComponent : ∀ {k l : ℕ}, k + l = m →
    ((j : Fin (m + 1)) → SmoothForm I M ℝ j) →ₗ[ℝ] SmoothForm I M ℝ k
  | 0, 0, _ => 0
  | 0, l + 1, hkl => δ (show 0 + 1 + l = m by omega) ∘ₗ
      LinearMap.proj (φ := fun j : Fin (m + 1) ↦ SmoothForm I M ℝ j) ⟨0 + 1, by omega⟩
  | k + 1, 0, hkl => D k ∘ₗ
      LinearMap.proj (φ := fun j : Fin (m + 1) ↦ SmoothForm I M ℝ j) ⟨k, by omega⟩
  | k + 1, l + 1, hkl => D k ∘ₗ
      LinearMap.proj (φ := fun j : Fin (m + 1) ↦ SmoothForm I M ℝ j) ⟨k, by omega⟩ +
    δ (show k + 1 + 1 + l = m by omega) ∘ₗ
      LinearMap.proj (φ := fun j : Fin (m + 1) ↦ SmoothForm I M ℝ j) ⟨k + 1 + 1, by omega⟩

/-- The operator `D + δ` on smooth forms of all degrees `0, …, m` on a manifold of dimension `m`,
built from a family of differentials `D : Ω^k → Ω^(k+1)` and a family of codifferentials
`δ : Ω^(k+1) → Ω^k`. Its degree-`k` component is `Dα_(k-1) + δα_(k+1)`, where the first term is
absent in degree `0` and the second in the top degree `m`. The de Rham operator
(`TauCeti.SmoothForm.deRhamOperator`) is the case `D = d`, `δ = d*`. When `D` and `δ` square to
zero its square is the Laplacian `δD + Dδ` in every degree
(`TauCeti.SmoothForm.diffAddCodiff_comp_diffAddCodiff`). -/
def diffAddCodiff :
    ((k : Fin (m + 1)) → SmoothForm I M ℝ k) →ₗ[ℝ] ((k : Fin (m + 1)) → SmoothForm I M ℝ k) :=
  LinearMap.pi fun k ↦ diffAddCodiffComponent D δ (k := k) (l := m - k) (by omega)

private theorem diffAddCodiff_apply_eq_component (hkl : k + l = m)
    (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) :
    diffAddCodiff D δ α ⟨k, by omega⟩ = diffAddCodiffComponent D δ hkl α := by
  obtain rfl : l = m - k := by omega
  rfl

/-- On a zero-dimensional manifold `D + δ` is zero. -/
@[simp]
theorem diffAddCodiff_apply_zero_zero (hkl : 0 + 0 = m)
    (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) :
    diffAddCodiff D δ α 0 = 0 :=
  diffAddCodiff_apply_eq_component D δ hkl α

/-- In positive dimension the degree-`0` component of `D + δ` is `δα₁`. -/
theorem diffAddCodiff_apply_zero_add_one (hkl : 0 + 1 + l = m)
    (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) :
    diffAddCodiff D δ α ⟨0, by omega⟩ = δ hkl (α ⟨0 + 1, by omega⟩) :=
  diffAddCodiff_apply_eq_component D δ (show 0 + (l + 1) = m by omega) α

/-- The top-degree component of `D + δ` is `Dα_(m-1)`. -/
theorem diffAddCodiff_apply_add_one_zero (hkl : k + 1 + 0 = m)
    (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) :
    diffAddCodiff D δ α ⟨k + 1, by omega⟩ = D k (α ⟨k, by omega⟩) :=
  diffAddCodiff_apply_eq_component D δ hkl α

/-- Strictly between degree `0` and the top degree the degree-`(k + 1)` component of `D + δ` is
`Dα_k + δα_(k+2)`. -/
theorem diffAddCodiff_apply_add_one_add_one (hkl : k + 1 + 1 + l = m)
    (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) :
    diffAddCodiff D δ α ⟨k + 1, by omega⟩ =
      D k (α ⟨k, by omega⟩) + δ hkl (α ⟨k + 1 + 1, by omega⟩) :=
  diffAddCodiff_apply_eq_component D δ (show k + 1 + (l + 1) = m by omega) α

/-- `D + δ` vanishes when both families vanish. -/
@[simp]
theorem diffAddCodiff_zero :
    diffAddCodiff (I := I) (M := M) (m := m) (fun _ ↦ 0) (fun _ ↦ 0) = 0 := by
  refine LinearMap.ext fun α ↦ funext fun ⟨k, hk⟩ ↦ ?_
  obtain ⟨l, hkl⟩ : ∃ l, k + l = m := ⟨m - k, by omega⟩
  rcases k with _ | k <;> rcases l with _ | l
  · exact diffAddCodiff_apply_zero_zero _ _ hkl α
  · exact diffAddCodiff_apply_zero_add_one _ _ (show 0 + 1 + l = m by omega) α
  · exact diffAddCodiff_apply_add_one_zero _ _ hkl α
  · exact (diffAddCodiff_apply_add_one_add_one _ _ (show k + 1 + 1 + l = m by omega) α).trans
      (add_zero _)

variable {D δ}

/-- **The square of `D + δ` is the Laplacian**: if `D` and `δ` square to zero, then the
degree-`k` component of `(D + δ)²α` is `(δD + Dδ)α_k`. -/
theorem diffAddCodiff_diffAddCodiff_apply (hDD : ∀ k, D (k + 1) ∘ₗ D k = 0)
    (hδδ : ∀ {k l l' : ℕ} (hkl : k + 1 + l = m) (hkl' : k + 1 + 1 + l' = m),
      δ hkl ∘ₗ δ hkl' = 0)
    (hkl : k + l = m) (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) :
    diffAddCodiff D δ (diffAddCodiff D δ α) ⟨k, by omega⟩ =
      laplacian D δ hkl (α ⟨k, by omega⟩) := by
  have hD (k : ℕ) (β : SmoothForm I M ℝ k) : D (k + 1) (D k β) = 0 :=
    LinearMap.congr_fun (hDD k) β
  have hδ {k l l' : ℕ} (hkl : k + 1 + l = m) (hkl' : k + 1 + 1 + l' = m)
      (β : SmoothForm I M ℝ (k + 1 + 1)) : δ hkl (δ hkl' β) = 0 :=
    LinearMap.congr_fun (hδδ hkl hkl') β
  rcases k with _ | k <;> rcases l with _ | l
  · exact (diffAddCodiff_apply_zero_zero D δ hkl _).trans (laplacian_zero_zero D δ hkl _).symm
  · rw [diffAddCodiff_apply_zero_add_one D δ (show 0 + 1 + l = m by omega),
      laplacian_zero_add_one D δ hkl (by omega)]
    rcases l with _ | l
    · rw [diffAddCodiff_apply_add_one_zero D δ (k := 0) (by omega)]
    · rw [diffAddCodiff_apply_add_one_add_one D δ (k := 0) (l := l) (by omega), map_add, hδ,
        add_zero]
  · rw [diffAddCodiff_apply_add_one_zero D δ hkl, laplacian_add_one_zero]
    rcases k with _ | k
    · rw [diffAddCodiff_apply_zero_add_one D δ (l := 0) (by omega)]
    · rw [diffAddCodiff_apply_add_one_add_one D δ (k := k) (l := 0) (by omega), map_add, hD,
        zero_add]
  · rw [diffAddCodiff_apply_add_one_add_one D δ (show k + 1 + 1 + l = m by omega),
      laplacian_add_one_add_one D δ hkl (by omega)]
    have hup : δ (show k + 1 + 1 + l = m by omega)
        (diffAddCodiff D δ α ⟨k + 1 + 1, by omega⟩) =
          δ (show k + 1 + 1 + l = m by omega) (D (k + 1) (α ⟨k + 1, by omega⟩)) := by
      rcases l with _ | l
      · rw [diffAddCodiff_apply_add_one_zero D δ (k := k + 1) (by omega)]
      · rw [diffAddCodiff_apply_add_one_add_one D δ (k := k + 1) (l := l) (by omega), map_add,
          hδ, add_zero]
    have hdown : D k (diffAddCodiff D δ α ⟨k, by omega⟩) =
        D k (δ (show k + 1 + (l + 1) = m by omega) (α ⟨k + 1, by omega⟩)) := by
      rcases k with _ | k
      · rw [diffAddCodiff_apply_zero_add_one D δ (l := l + 1) (by omega)]
      · rw [diffAddCodiff_apply_add_one_add_one D δ (k := k) (l := l + 1) (by omega), map_add, hD,
          zero_add]
    rw [hup, hdown]
    exact add_comm _ _

/-- **The square of `D + δ` is the Laplacian**: if `D` and `δ` square to zero, then
`(D + δ)² = δD + Dδ`, acting degreewise. -/
theorem diffAddCodiff_comp_diffAddCodiff (hDD : ∀ k, D (k + 1) ∘ₗ D k = 0)
    (hδδ : ∀ {k l l' : ℕ} (hkl : k + 1 + l = m) (hkl' : k + 1 + 1 + l' = m),
      δ hkl ∘ₗ δ hkl' = 0) :
    diffAddCodiff D δ ∘ₗ diffAddCodiff D δ =
      LinearMap.piMap fun j : Fin (m + 1) ↦ laplacian D δ (k := j) (l := m - j) (by omega) := by
  refine LinearMap.ext fun α ↦ funext fun ⟨k, hk⟩ ↦ ?_
  exact diffAddCodiff_diffAddCodiff_apply hDD hδδ (l := m - k) (by omega) α

/-- **Commutators with a degreewise operator**: for operators `F_k` acting in each degree, the
commutator of `D + δ` with `F` is `D' + δ'` for the commutators `D'_k = D_k F_k - F_(k+1) D_k` and
`δ' = δ F - F δ`. With `F` multiplication by a smooth function, this says that the symbol of
`D + δ` is the sum of the symbols of `D` and `δ`. -/
theorem lie_diffAddCodiff_piMap (F : ∀ k, SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ k) :
    ⁅diffAddCodiff D δ, LinearMap.piMap fun j : Fin (m + 1) ↦ F j⁆ =
      diffAddCodiff (fun k ↦ D k ∘ₗ F k - F (k + 1) ∘ₗ D k)
        (fun {k _} hkl ↦ δ hkl ∘ₗ F (k + 1) - F k ∘ₗ δ hkl) := by
  refine LinearMap.ext fun α ↦ funext fun ⟨k, hk⟩ ↦ ?_
  obtain ⟨l, hkl⟩ : ∃ l, k + l = m := ⟨m - k, by omega⟩
  simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, Pi.sub_apply]
  rcases k with _ | k <;> rcases l with _ | l
  · simp only [Fin.zero_eta, diffAddCodiff_apply_zero_zero _ _ hkl, LinearMap.coe_piMap,
      Pi.map_apply, map_zero]
    -- The zeros are typed in degree `↑(0 : Fin (m + 1))` but subtracted in degree `0`, so
    -- `sub_self` applies only up to definitional unfolding.
    exact sub_self _
  · simp only [diffAddCodiff_apply_zero_add_one _ _ (show 0 + 1 + l = m by omega),
      LinearMap.coe_piMap, Pi.map_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  · simp only [diffAddCodiff_apply_add_one_zero _ _ hkl, LinearMap.coe_piMap, Pi.map_apply,
      LinearMap.sub_apply, LinearMap.comp_apply]
  · simp only [diffAddCodiff_apply_add_one_add_one _ _ (show k + 1 + 1 + l = m by omega),
      LinearMap.coe_piMap, Pi.map_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
    abel

end DiffAddCodiff

/-! ### The `L²` pairing -/

section Pairing

/-- The `L²` pairing `∫_M ⟨α, β⟩ vol` of smooth `k`-forms. -/
private def pairing (o : Manifold.Orientation I M (Fin m)) (k : ℕ) (α β : SmoothForm I M ℝ k) :
    ℝ :=
  integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (α.val x) (β.val x) •
    riemannianVolumeForm o x)

variable (o : Manifold.Orientation I M (Fin m))
  {D : ∀ k, SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ (k + 1)}
  {δ : ∀ {k l : ℕ}, k + 1 + l = m → SmoothForm I M ℝ (k + 1) →ₗ[ℝ] SmoothForm I M ℝ k}
  (hD : ∀ {k : ℕ} {α : SmoothForm I M ℝ k},
    α ∈ compactlySupportedForms I M k → D k α ∈ compactlySupportedForms I M (k + 1))
  (hδ : ∀ {k l : ℕ} (hkl : k + 1 + l = m) {β : SmoothForm I M ℝ (k + 1)},
    β ∈ compactlySupportedForms I M (k + 1) → δ hkl β ∈ compactlySupportedForms I M k)

include hD hδ in
/-- The pairing of `(D + δ)α` with `β`, summed over all degrees, is the sum over `i < m` of the
pairings of `Dα_i` with `β_(i+1)` and of `δα_(i+1)` with `β_i`. -/
private theorem sum_pairing_diffAddCodiff (α β : (j : Fin (m + 1)) → SmoothForm I M ℝ j)
    (h : (∀ j : Fin (m + 1), α j ∈ compactlySupportedForms I M j) ∨
      ∀ j : Fin (m + 1), β j ∈ compactlySupportedForms I M j) :
    ∑ j : Fin (m + 1), pairing o j (diffAddCodiff D δ α j) (β j) =
      ∑ i : Fin m, (pairing o (i + 1) (D i (α ⟨i, by omega⟩)) (β ⟨i + 1, by omega⟩) +
        pairing o i (δ (k := i) (l := m - (i + 1)) (by omega) (α ⟨i + 1, by omega⟩))
          (β ⟨i, by omega⟩)) := by
  set a : Fin m → ℝ := fun i ↦
    pairing o (i + 1) (D i (α ⟨i, by omega⟩)) (β ⟨i + 1, by omega⟩) with ha
  set b : Fin m → ℝ := fun i ↦
    pairing o i (δ (k := i) (l := m - (i + 1)) (by omega) (α ⟨i + 1, by omega⟩))
      (β ⟨i, by omega⟩) with hb
  -- The degree-`j` term is `a_(j-1) + b_j`, where `a_(-1)` and `b_m` are absent.
  let A : Fin (m + 1) → ℝ := Fin.cases (motive := fun _ ↦ ℝ) 0 a
  let B : Fin (m + 1) → ℝ := fun j ↦ if hj : (j : ℕ) < m then b ⟨j, hj⟩ else 0
  have hsplit (j : Fin (m + 1)) : pairing o j (diffAddCodiff D δ α j) (β j) = A j + B j := by
    obtain ⟨k, hk⟩ := j
    obtain ⟨l, hkl⟩ : ∃ l, k + l = m := ⟨m - k, by omega⟩
    rcases k with _ | k <;> rcases l with _ | l
    · rw [show diffAddCodiff D δ α ⟨0, hk⟩ = 0 from diffAddCodiff_apply_zero_zero D δ hkl α]
      simp only [A, B, show ¬(0 : ℕ) < m by omega, ↓reduceDIte, add_zero]
      rw [pairing]
      exact integralTopForm_inner_zero_left o _
    · rw [diffAddCodiff_apply_zero_add_one D δ (l := m - (0 + 1)) (by omega)]
      simp only [A, B, show (0 : ℕ) < m by omega, ↓reduceDIte]
      -- `⟨0, hk⟩` is the numeral `0` of `Fin (m + 1)` (`Fin.mk_zero`).
      rw [show Fin.cases (motive := fun _ ↦ ℝ) 0 a ⟨0, hk⟩ = 0 from Fin.cases_zero]
      rw [zero_add (b _), hb]
    · rw [diffAddCodiff_apply_add_one_zero D δ hkl]
      simp only [A, B, show ¬k + 1 < m by omega, ↓reduceDIte]
      rw [Fin.cases_succ', add_zero]
    · rw [diffAddCodiff_apply_add_one_add_one D δ (l := m - (k + 1 + 1)) (by omega)]
      simp only [A, B, show k + 1 < m by omega, ↓reduceDIte]
      rw [Fin.cases_succ', ha, hb]
      unfold pairing
      refine integralTopForm_inner_add_left o hkl _ _ _ ?_
      rcases h with h | h
      · exact .inl ⟨hD (h ⟨k, by omega⟩), hδ _ (h ⟨k + 1 + 1, by omega⟩)⟩
      · exact .inr (h ⟨k + 1, hk⟩)
  rw [Finset.sum_congr rfl fun j _ ↦ hsplit j, Finset.sum_add_distrib, Fin.sum_univ_succ,
    Fin.sum_univ_castSucc, Finset.sum_add_distrib]
  simp only [ha, Fin.cases_zero, Fin.cases_succ, zero_add, hb, Fin.eta, Fin.val_castSucc, Fin.is_lt,
    ↓reduceDIte, Fin.val_last, lt_self_iff_false, add_zero, add_right_inj, A, B]
  -- The remaining sums differ only in `Fin.castSucc i`, which is `⟨i, _⟩` by definition.
  rfl

variable (hadj : ∀ {k l : ℕ} (hkl : k + 1 + l = m) (α : SmoothForm I M ℝ k)
    (β : SmoothForm I M ℝ (k + 1)),
    α ∈ compactlySupportedForms I M k ∨ β ∈ compactlySupportedForms I M (k + 1) →
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
          ((D k α).val x) (β.val x) • riemannianVolumeForm o x) =
        integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
          (α.val x) ((δ hkl β).val x) • riemannianVolumeForm o x))

include hD hδ hadj in
/-- **`D + δ` is formally self-adjoint**: if `δ` is a formal adjoint of `D` and both preserve
compact support, then `∑_k ∫_M ⟨((D + δ)α)_k, β_k⟩ vol = ∑_k ∫_M ⟨α_k, ((D + δ)β)_k⟩ vol` for
families `α` and `β` of smooth forms of all degrees, one of them compactly supported in every
degree. -/
theorem sum_integralTopForm_inner_diffAddCodiff_eq_inner_diffAddCodiff
    (α β : (j : Fin (m + 1)) → SmoothForm I M ℝ j)
    (h : (∀ j : Fin (m + 1), α j ∈ compactlySupportedForms I M j) ∨
      ∀ j : Fin (m + 1), β j ∈ compactlySupportedForms I M j) :
    ∑ j : Fin (m + 1), integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) j
        ((diffAddCodiff D δ α j).val x) ((β j).val x) • riemannianVolumeForm o x) =
      ∑ j : Fin (m + 1), integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) j
        ((α j).val x) ((diffAddCodiff D δ β j).val x) • riemannianVolumeForm o x) := by
  have hcomm (k : ℕ) (a b : SmoothForm I M ℝ k) : pairing o k a b = pairing o k b a :=
    RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm o a.val b.val
  -- Both sides are sums of `pairing`s, which is the integral by definition.
  change ∑ j : Fin (m + 1), pairing o j _ _ = ∑ j : Fin (m + 1), pairing o j _ _
  rw [Finset.sum_congr rfl fun (j : Fin (m + 1)) _ ↦ hcomm j (α j) _,
    sum_pairing_diffAddCodiff o hD hδ α β h,
    sum_pairing_diffAddCodiff o hD hδ β α h.symm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- `⟨Dα_i, β_(i+1)⟩ = ⟨α_i, δβ_(i+1)⟩` and `⟨δα_(i+1), β_i⟩ = ⟨Dβ_i, α_(i+1)⟩`.
  have hcs : α ⟨i, by omega⟩ ∈ compactlySupportedForms I M i ∨
      β ⟨i + 1, by omega⟩ ∈ compactlySupportedForms I M (i + 1) :=
    h.imp (fun h ↦ h ⟨i, by omega⟩) fun h ↦ h ⟨i + 1, by omega⟩
  have hcs' : β ⟨i, by omega⟩ ∈ compactlySupportedForms I M i ∨
      α ⟨i + 1, by omega⟩ ∈ compactlySupportedForms I M (i + 1) :=
    (h.imp (fun h ↦ h ⟨i + 1, by omega⟩) fun h ↦ h ⟨i, by omega⟩).symm
  rw [add_comm]
  congr 1
  · rw [hcomm, pairing, ← hadj _ _ _ hcs', pairing]
  · rw [pairing, hadj _ _ _ hcs]
    exact hcomm _ _ _

include hD hδ hadj in
/-- **The kernel of `D + δ`**: if `D` and `δ` square to zero, `δ` is a formal adjoint of `D` and
both preserve compact support, then a family `α` of compactly supported smooth forms satisfies
`(D + δ)α = 0` exactly when every component `α_k` is harmonic, `(δD + Dδ)α_k = 0`. -/
theorem diffAddCodiff_eq_zero_iff (hDD : ∀ k, D (k + 1) ∘ₗ D k = 0)
    (hδδ : ∀ {k l l' : ℕ} (hkl : k + 1 + l = m) (hkl' : k + 1 + 1 + l' = m),
      δ hkl ∘ₗ δ hkl' = 0)
    {α : (j : Fin (m + 1)) → SmoothForm I M ℝ j}
    (hα : ∀ j : Fin (m + 1), α j ∈ compactlySupportedForms I M j) :
    diffAddCodiff D δ α = 0 ↔
      ∀ j : Fin (m + 1), laplacian D δ (k := j) (l := m - j) (by omega) (α j) = 0 := by
  refine ⟨fun h j ↦ ?_, fun h ↦ ?_⟩
  · have := diffAddCodiff_diffAddCodiff_apply hDD hδδ (k := j) (l := m - j) (by omega) α
    rw [h, map_zero] at this
    exact this.symm
  have hlap {k l : ℕ} (hkl : k + l = m) : laplacian D δ hkl (α ⟨k, by omega⟩) = 0 := by
    obtain rfl : l = m - k := by omega
    exact h ⟨k, by omega⟩
  -- Every component is closed and, in positive degree, coclosed.
  have hdiff (k : ℕ) (hk : k + 1 ≤ m) : D k (α ⟨k, by omega⟩) = 0 := by
    rcases k with _ | k
    · exact (laplacian_eq_zero_iff_apply_eq_zero o hD hadj (l := m) (by omega)
        (hα ⟨0, by omega⟩)).1
        (hlap _)
    · exact ((laplacian_eq_zero_iff o hD hδ hadj (l := m - (k + 1)) (by omega)
        (hα ⟨k + 1, by omega⟩)).1 (hlap _)).1
  have hcodiff {k l : ℕ} (hkl : k + 1 + l = m) : δ hkl (α ⟨k + 1, by omega⟩) = 0 :=
    ((laplacian_eq_zero_iff o hD hδ hadj hkl (hα ⟨k + 1, by omega⟩)).1 (hlap _)).2
  funext ⟨k, hk⟩
  obtain ⟨l, hkl⟩ : ∃ l, k + l = m := ⟨m - k, by omega⟩
  rcases k with _ | k <;> rcases l with _ | l
  · exact diffAddCodiff_apply_zero_zero D δ hkl α
  · rw [diffAddCodiff_apply_zero_add_one D δ (show 0 + 1 + l = m by omega), hcodiff,
      Pi.zero_apply]
  · rw [diffAddCodiff_apply_add_one_zero D δ hkl, hdiff k (by omega), Pi.zero_apply]
  · rw [diffAddCodiff_apply_add_one_add_one D δ (show k + 1 + 1 + l = m by omega),
      hdiff k (by omega), hcodiff, add_zero, Pi.zero_apply]

end Pairing

/-! ### The de Rham operator -/

section DeRham

variable (o : Manifold.Orientation I M (Fin m))

/-- The **de Rham operator** `d + d*` on smooth forms of all degrees `0, …, m` on an oriented
Riemannian manifold of dimension `m`. Its degree-`k` component is `dα_(k-1) + d*α_(k+1)`, where
the first term is absent in degree `0` and the second in the top degree `m`. It is the operator
`TauCeti.SmoothForm.diffAddCodiff` of `D = d` and `δ = d*`. -/
def deRhamOperator :
    ((k : Fin (m + 1)) → SmoothForm I M ℝ k) →ₗ[ℝ] ((k : Fin (m + 1)) → SmoothForm I M ℝ k) :=
  diffAddCodiff (mextDerivₗ I) fun hkl ↦ codifferential o hkl

/-- The de Rham operator is the operator `D + δ` of the pair `(d, d*)`. -/
theorem deRhamOperator_def :
    deRhamOperator o = diffAddCodiff (mextDerivₗ I) (fun hkl ↦ codifferential o hkl) :=
  (rfl)

/-- On a zero-dimensional manifold the de Rham operator is zero. -/
@[simp]
theorem deRhamOperator_apply_zero_zero (hkl : 0 + 0 = m)
    (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) :
    deRhamOperator o α 0 = 0 :=
  diffAddCodiff_apply_zero_zero _ _ hkl α

/-- In positive dimension the degree-`0` component of `(d + d*)α` is `d*α₁`. -/
theorem deRhamOperator_apply_zero_add_one (hkl : 0 + 1 + l = m)
    (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) :
    deRhamOperator o α ⟨0, by omega⟩ = codifferential o hkl (α ⟨0 + 1, by omega⟩) :=
  diffAddCodiff_apply_zero_add_one _ _ hkl α

/-- The top-degree component of `(d + d*)α` is `dα_(m-1)`. -/
theorem deRhamOperator_apply_add_one_zero (hkl : k + 1 + 0 = m)
    (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) :
    deRhamOperator o α ⟨k + 1, by omega⟩ = mextDerivₗ I k (α ⟨k, by omega⟩) :=
  diffAddCodiff_apply_add_one_zero _ _ hkl α

/-- Strictly between degree `0` and the top degree the degree-`(k + 1)` component of `(d + d*)α`
is `dα_k + d*α_(k+2)`. -/
theorem deRhamOperator_apply_add_one_add_one (hkl : k + 1 + 1 + l = m)
    (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) :
    deRhamOperator o α ⟨k + 1, by omega⟩ =
      mextDerivₗ I k (α ⟨k, by omega⟩) + codifferential o hkl (α ⟨k + 1 + 1, by omega⟩) :=
  diffAddCodiff_apply_add_one_add_one _ _ hkl α

/-- The de Rham operator does not depend on the orientation. -/
@[simp]
theorem deRhamOperator_neg_orientation : deRhamOperator (-o) = deRhamOperator o := by
  simp only [deRhamOperator_def, codifferential_neg_orientation]

/-- **The square of the de Rham operator is the Hodge Laplacian**: the degree-`k` component of
`(d + d*)²α` is `Δα_k`. -/
theorem deRhamOperator_deRhamOperator_apply (hkl : k + l = m)
    (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) :
    deRhamOperator o (deRhamOperator o α) ⟨k, by omega⟩ = hodgeLaplacian o hkl (α ⟨k, by omega⟩) :=
  hodgeLaplacian_def o hkl ▸
    diffAddCodiff_diffAddCodiff_apply (fun k ↦ mextDerivₗ_comp_mextDerivₗ I k)
    (fun hkl hkl' ↦ codifferential_comp_codifferential o hkl hkl') hkl α

/-- **The square of the de Rham operator is the Hodge Laplacian**: `(d + d*)² = Δ`, acting
degreewise. -/
theorem deRhamOperator_comp_deRhamOperator :
    deRhamOperator o ∘ₗ deRhamOperator o =
      LinearMap.piMap fun j : Fin (m + 1) ↦ hodgeLaplacian o (k := j) (l := m - j) (by omega) := by
  refine LinearMap.ext fun α ↦ funext fun ⟨k, hk⟩ ↦ ?_
  exact deRhamOperator_deRhamOperator_apply o (l := m - k) (by omega) α

section Boundaryless

variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The de Rham operator is formally self-adjoint**: on an oriented boundaryless Riemannian
manifold, `∑_k ∫_M ⟨((d + d*)α)_k, β_k⟩ vol = ∑_k ∫_M ⟨α_k, ((d + d*)β)_k⟩ vol` for families `α`
and `β` of smooth forms of all degrees, one of them compactly supported in every degree. -/
theorem sum_integralTopForm_inner_deRhamOperator_eq_inner_deRhamOperator
    (α β : (j : Fin (m + 1)) → SmoothForm I M ℝ j)
    (h : (∀ j : Fin (m + 1), α j ∈ compactlySupportedForms I M j) ∨
      ∀ j : Fin (m + 1), β j ∈ compactlySupportedForms I M j) :
    ∑ j : Fin (m + 1), integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) j
        ((deRhamOperator o α j).val x) ((β j).val x) • riemannianVolumeForm o x) =
      ∑ j : Fin (m + 1), integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) j
        ((α j).val x) ((deRhamOperator o β j).val x) • riemannianVolumeForm o x) :=
  sum_integralTopForm_inner_diffAddCodiff_eq_inner_diffAddCodiff o
    (mextDerivₗ_mem_compactlySupportedForms I) (codifferential_mem_compactlySupportedForms o)
    (integralTopForm_inner_mextDeriv_eq_inner_codifferential o) α β h

/-- **The kernel of the de Rham operator consists of the harmonic forms**: on an oriented
boundaryless Riemannian manifold, a family `α` of compactly supported smooth forms satisfies
`(d + d*)α = 0` exactly when every component `α_k` is harmonic, `Δα_k = 0`. -/
theorem deRhamOperator_eq_zero_iff {α : (j : Fin (m + 1)) → SmoothForm I M ℝ j}
    (hα : ∀ j : Fin (m + 1), α j ∈ compactlySupportedForms I M j) :
    deRhamOperator o α = 0 ↔
      ∀ j : Fin (m + 1), hodgeLaplacian o (k := j) (l := m - j) (by omega) (α j) = 0 := by
  simp only [hodgeLaplacian_def]
  exact diffAddCodiff_eq_zero_iff o (mextDerivₗ_mem_compactlySupportedForms I)
      (codifferential_mem_compactlySupportedForms o)
      (integralTopForm_inner_mextDeriv_eq_inner_codifferential o)
      (fun k ↦ mextDerivₗ_comp_mextDerivₗ I k)
      (fun hkl hkl' ↦ codifferential_comp_codifferential o hkl hkl') hα

end Boundaryless

/-! ### The principal symbol of the de Rham operator -/

section Symbol

/-- **The symbol of the de Rham operator**: the commutator of `d + d*` with multiplication by a
smooth function `f` is the operator `D + δ` of the commutators `[d, f] = df ∧ ·` and
`[d*, f] = -ι_(grad f)` (`TauCeti.SmoothForm.mextDerivₗ_funSMulₗ_apply`,
`TauCeti.SmoothForm.coe_codifferential_funSMulₗ`). Thus `[d + d*, f] = df ∧ · - ι_(grad f)`, the
geometric principal symbol of `d + d*` at `df`. -/
theorem lie_deRhamOperator_piMap_funSMulₗ (f : C^∞⟮I, M; ℝ⟯) :
    ⁅deRhamOperator o, LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) f⁆ =
      diffAddCodiff (fun k ↦ mextDerivₗ I k ∘ₗ funSMulₗ f - funSMulₗ f ∘ₗ mextDerivₗ I k)
        (fun hkl ↦ codifferential o hkl ∘ₗ funSMulₗ f - funSMulₗ f ∘ₗ codifferential o hkl) :=
  lie_diffAddCodiff_piMap (fun _ ↦ funSMulₗ f)

/-- On a zero-dimensional manifold the symbol `[d + d*, f]` of the de Rham operator is zero. -/
@[simp]
theorem lie_deRhamOperator_piMap_funSMulₗ_apply_zero_zero (hkl : 0 + 0 = m)
    (f : C^∞⟮I, M; ℝ⟯) (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) :
    ⁅deRhamOperator o, LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) f⁆ α 0 =
      0 := by
  rw [lie_deRhamOperator_piMap_funSMulₗ, diffAddCodiff_apply_zero_zero _ _ hkl]

/-- **The symbol of the de Rham operator in degree `0`**: in positive dimension the degree-`0`
component of `[d + d*, f]α` is `-ι_(grad f) α₁`. -/
theorem coe_lie_deRhamOperator_piMap_funSMulₗ_apply_zero_add_one (hkl : 0 + 1 + l = m)
    (f : C^∞⟮I, M; ℝ⟯) (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) :
    (⁅deRhamOperator o, LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) f⁆ α
      ⟨0, by omega⟩ : RoughForm I M ℝ 0) =
      -RoughForm.interior (Manifold.mgradient I f) (α ⟨0 + 1, by omega⟩).val := by
  rw [lie_deRhamOperator_piMap_funSMulₗ, diffAddCodiff_apply_zero_add_one _ _ hkl]
  funext x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, Submodule.coe_sub, Pi.sub_apply,
    coe_codifferential_funSMulₗ, coe_funSMulₗ, Pi.neg_apply]
  abel

/-- **The symbol of the de Rham operator in the top degree**: the top-degree component of
`[d + d*, f]α` is `df ∧ α_(m-1)`. -/
theorem coe_lie_deRhamOperator_piMap_funSMulₗ_apply_add_one_zero (hkl : k + 1 + 0 = m)
    (f : C^∞⟮I, M; ℝ⟯) (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) (x : M)
    (v : Fin (k + 1) → TangentSpace I x) :
    (⁅deRhamOperator o, LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) f⁆ α
      ⟨k + 1, by omega⟩ : RoughForm I M ℝ (k + 1)) x v =
      (mextDeriv (RoughForm.ofFunction I f)).wedge (α ⟨k, by omega⟩).val x
        (v ∘ Fin.cast (show 0 + 1 + k = k + 1 by omega)) := by
  rw [lie_deRhamOperator_piMap_funSMulₗ, diffAddCodiff_apply_add_one_zero _ _ hkl]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, Submodule.coe_sub, Pi.sub_apply,
    ContinuousAlternatingMap.sub_apply, mextDerivₗ_funSMulₗ_apply, coe_funSMulₗ,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, add_sub_cancel_right]

/-- **The symbol of the de Rham operator**: strictly between degree `0` and the top degree, the
degree-`(k + 1)` component of `[d + d*, f]α` is `df ∧ α_k - ι_(grad f) α_(k+2)`. -/
theorem coe_lie_deRhamOperator_piMap_funSMulₗ_apply_add_one_add_one (hkl : k + 1 + 1 + l = m)
    (f : C^∞⟮I, M; ℝ⟯) (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) (x : M)
    (v : Fin (k + 1) → TangentSpace I x) :
    (⁅deRhamOperator o, LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) f⁆ α
      ⟨k + 1, by omega⟩ : RoughForm I M ℝ (k + 1)) x v =
      (mextDeriv (RoughForm.ofFunction I f)).wedge (α ⟨k, by omega⟩).val x
          (v ∘ Fin.cast (show 0 + 1 + k = k + 1 by omega)) -
        RoughForm.interior (Manifold.mgradient I f) (α ⟨k + 1 + 1, by omega⟩).val x v := by
  rw [lie_deRhamOperator_piMap_funSMulₗ, diffAddCodiff_apply_add_one_add_one _ _ hkl]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, Submodule.coe_add, Submodule.coe_sub,
    Pi.add_apply, Pi.sub_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sub_apply, mextDerivₗ_funSMulₗ_apply, coe_codifferential_funSMulₗ,
    coe_funSMulₗ, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

/-- **The de Rham operator has order one**: its double commutator with multiplication by smooth
functions `f` and `g` vanishes, `[[d + d*, f], g] = 0`. -/
theorem lie_lie_deRhamOperator_piMap_funSMulₗ_eq_zero (f g : C^∞⟮I, M; ℝ⟯) :
    ⁅⁅deRhamOperator o, LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) f⁆,
      LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) g⁆ = 0 := by
  rw [lie_deRhamOperator_piMap_funSMulₗ]
  refine (lie_diffAddCodiff_piMap (fun _ ↦ funSMulₗ g)).trans ?_
  simp only [mextDerivₗ_lie_lie_funSMulₗ_eq_zero, codifferential_lie_lie_funSMulₗ_eq_zero]
  exact diffAddCodiff_zero

/-- **The de Rham operator is of Dirac type**: its symbol `c(f) = [d + d*, f]` satisfies the
Clifford relation `c(f) c(g) + c(g) c(f) = -2 ⟪df, dg⟫` for smooth functions `f` and `g`. In the
convention `σ_geom(P)(df) = [P, f]` of first-order principal symbols, the symbol
`σ(ξ) = ξ ∧ · - ι_ξ` of `d + d*` therefore satisfies `σ(α) σ(β) + σ(β) σ(α) = -2 ⟪α, β⟫`. -/
theorem coe_lie_deRhamOperator_piMap_funSMulₗ_mul_add_mul_apply (f g : C^∞⟮I, M; ℝ⟯)
    (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) (j : Fin (m + 1)) :
    (((⁅deRhamOperator o, LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) f⁆ *
        ⁅deRhamOperator o, LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) g⁆ +
      ⁅deRhamOperator o, LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) g⁆ *
        ⁅deRhamOperator o, LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) f⁆)
          α j : SmoothForm I M ℝ j) : RoughForm I M ℝ j) =
      fun x ↦ (-2 * ⟪Manifold.mgradient I f x, Manifold.mgradient I g x⟫) • (α j).val x := by
  set a := deRhamOperator o
  set b := LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) f
  set c := LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) g
  -- Since `[[a, b], c] = 0`, `[[a², b], c] = [a, c] [a, b] + [a, b] [a, c]`.
  have key := lie_lie_mul_self a b c
  rw [lie_lie_deRhamOperator_piMap_funSMulₗ_eq_zero, mul_zero, zero_mul, add_zero, zero_add] at key
  rw [add_comm (⁅a, b⁆ * ⁅a, c⁆), ← key, Module.End.mul_eq_comp, deRhamOperator_comp_deRhamOperator]
  have h := coe_lie_lie_hodgeLaplacian_funSMulₗ o (k := j) (l := m - j) (by omega) f g (α j)
  simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp] at h
  simpa only [b, c, Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.coe_piMap,
    Pi.map_apply, Pi.sub_apply] using h

/-- **The symbol of the de Rham operator squares to `-|df|²`**: for a smooth function `f`, the
commutator `c(f) = [d + d*, f]` satisfies `c(f)² = -|grad f|²`. -/
theorem coe_lie_deRhamOperator_piMap_funSMulₗ_mul_self_apply (f : C^∞⟮I, M; ℝ⟯)
    (α : (j : Fin (m + 1)) → SmoothForm I M ℝ j) (j : Fin (m + 1)) :
    (((⁅deRhamOperator o, LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) f⁆ *
        ⁅deRhamOperator o, LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) f⁆)
          α j : SmoothForm I M ℝ j) : RoughForm I M ℝ j) =
      fun x ↦ (-⟪Manifold.mgradient I f x, Manifold.mgradient I f x⟫) • (α j).val x := by
  have h := coe_lie_deRhamOperator_piMap_funSMulₗ_mul_add_mul_apply o f f α j
  simp only [LinearMap.add_apply, Pi.add_apply, Submodule.coe_add] at h
  funext x
  have hx := congrFun h x
  simp only [Pi.add_apply] at hx
  linear_combination (norm := module) (1 / 2 : ℝ) • hx

/-- **The de Rham operator is elliptic**: if the symbol `[d + d*, f]` annihilates a family `α` of
smooth forms, then `α` vanishes wherever `df ≠ 0`. -/
theorem apply_eq_zero_of_lie_deRhamOperator_piMap_funSMulₗ_apply_eq_zero (f : C^∞⟮I, M; ℝ⟯)
    {α : (j : Fin (m + 1)) → SmoothForm I M ℝ j}
    (h : ⁅deRhamOperator o, LinearMap.piMap fun j : Fin (m + 1) ↦ funSMulₗ (F := ℝ) (k := j) f⁆ α =
      0)
    (j : Fin (m + 1)) {x : M} (hx : Manifold.mgradient I f x ≠ 0) : (α j).val x = 0 := by
  have hsq := congrFun (coe_lie_deRhamOperator_piMap_funSMulₗ_mul_self_apply o f α j) x
  rw [mul_apply_eq_comp, h, map_zero, Pi.zero_apply, Submodule.coe_zero, Pi.zero_apply,
    eq_comm, smul_eq_zero, neg_eq_zero, inner_self_eq_zero] at hsq
  exact hsq.resolve_left hx

end Symbol

end DeRham

end SmoothForm

end TauCeti

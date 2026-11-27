/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Esymm
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.TopPower
import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary

/-!
# Mixed wedge products of (1,1)-forms with powers of the Kähler form

Let `E` be a complex inner product space of dimension `n`, with `ω` the Kähler form of
multiplication by `i` and the real inner product `Re ⟪·, ·⟫_ℂ`. For real two-forms `α` of type
(1,1), let `λ[α]` be the eigenvalues of the Hermitian form `H_α` relative to the inner product.
The function `α ↦ σ_k(λ[α])` is the diagonal of a unique symmetric multilinear form `M_k` on
(1,1)-forms, its polarization

`M_k(α₁, …, α_k) = (1 / k!) ∑_{S ⊆ {1, …, k}} (-1)^{#S} σ_k(λ[∑_{i ∉ S} αᵢ])`

(`TauCeti.AlmostComplexStructure.mixedEsymm`), and for `k + l = n` the mixed form identity

`α₁ ∧ ⋯ ∧ α_k ∧ ω ^ l = (k! l! / n!) M_k(α₁, …, α_k) ω ^ n`

holds (`TauCeti.AlmostComplexStructure.wedge_wedgeProd_wedgePow_ofComplexModule`). It reduces to
the form identity `α ^ k ∧ ω ^ l = (k! l! / n!) σ_k(λ[α]) ω ^ n` of
`TauCeti.AlmostComplexStructure.wedge_wedgePow_wedgePow_ofComplexModule` by polarization of the
wedge product of two-forms (`ContinuousAlternatingMap.factorial_smul_wedgeProd`): two-forms
commute, so `k! α₁ ∧ ⋯ ∧ α_k` is the alternating sum of the powers `(∑_{i ∉ S} αᵢ) ^ k`.

Since the left side of the mixed identity is multilinear and symmetric in the `αᵢ` and `ω ^ n`
does not vanish, `M_k` is multilinear (`TauCeti.AlmostComplexStructure.mixedEsymmMultilinear`) and
symmetric (`TauCeti.AlmostComplexStructure.mixedEsymm_comp_perm`), with diagonal
`M_k(α, …, α) = σ_k(λ[α])` (`TauCeti.AlmostComplexStructure.mixedEsymm_const`). For `k > n` it
vanishes. Expanding `σ_k(λ[β + t α]) = M_k(β + t α, …, β + t α)` by multilinearity gives the
derivative `(d/dt) σ_k(λ[β + t α]) |_{t = 0} = k M_k(α, β, …, β)`
(`TauCeti.AlmostComplexStructure.hasDerivAt_esymm_relEigenvalues_add_smul_cons`), the form of
`M_k` that Gårding's mixed inequality uses.

## Main definitions

The real (1,1)-forms are the subspace `TauCeti.AlmostComplexStructure.realOneOneForms E`.

* `TauCeti.AlmostComplexStructure.mixedEsymm`: the polarization `M_k` of `σ_k ∘ λ`.
* `TauCeti.AlmostComplexStructure.mixedEsymmMultilinear`: `M_k` as a multilinear form.

## Main results

* `TauCeti.AlmostComplexStructure.wedge_wedgeProd_wedgePow_ofComplexModule`: the mixed form
  identity.
* `TauCeti.AlmostComplexStructure.mixedEsymm_const`: `M_k(α, …, α) = σ_k(λ[α])`.
* `TauCeti.AlmostComplexStructure.mixedEsymm_comp_perm`: `M_k` is symmetric.
* `TauCeti.AlmostComplexStructure.hasDerivAt_esymm_relEigenvalues_add_smul_cons`: `M_k` as a
  directional derivative of `σ_k ∘ λ`.

## References

* S. Dinew and S. Kołodziej, *A priori estimates for complex Hessian equations*, Anal. PDE 7
  (2014), read as arXiv:1112.3063v1 (the form identity and its mixed version, lines 33–35).
-/

public section

noncomputable section

open Module ContinuousAlternatingMap Complex Finset

open scoped Finset

namespace TauCeti.AlmostComplexStructure

attribute [local instance] InnerProductSpace.complexToReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The polarization `M_k(α₁, …, α_k)` of `α ↦ σ_k(λ[α])` on real (1,1)-forms, where `λ[α]` are
the eigenvalues of the Hermitian form `H_α` relative to the inner product and `σ_k` is the `k`-th
elementary symmetric polynomial:
`M_k(α₁, …, α_k) = (1 / k!) ∑_{S ⊆ {1, …, k}} (-1)^{#S} σ_k(λ[∑_{i ∉ S} αᵢ])`. -/
def mixedEsymm {n k : ℕ} (hn : finrank ℂ E = n) (α : Fin k → realOneOneForms E) : ℝ :=
  (k.factorial : ℝ)⁻¹ * ∑ S : Finset (Fin k), (-1 : ℝ) ^ #S *
    MvPolynomial.eval
      ((isSymm_hermitianSesqForm (realOneOneForms_apply_I_smul (∑ i ∈ Sᶜ, α i))).relEigenvalues hn)
      (MvPolynomial.esymm (Fin n) ℝ k)

/-- Unfolding lemma for `mixedEsymm`: the polarization formula
`M_k(α₁, …, α_k) = (1 / k!) ∑_{S ⊆ {1, …, k}} (-1)^{#S} σ_k(λ[∑_{i ∉ S} αᵢ])`. -/
theorem mixedEsymm_def {n k : ℕ} (hn : finrank ℂ E = n) (α : Fin k → realOneOneForms E) :
    mixedEsymm hn α = (k.factorial : ℝ)⁻¹ * ∑ S : Finset (Fin k), (-1 : ℝ) ^ #S *
      MvPolynomial.eval
        ((isSymm_hermitianSesqForm (realOneOneForms_apply_I_smul (∑ i ∈ Sᶜ, α i))).relEigenvalues
          hn)
        (MvPolynomial.esymm (Fin n) ℝ k) :=
  (rfl)

/-- `M_k` vanishes for `k > n`, since then `σ_k` vanishes on `ℝⁿ`. -/
theorem mixedEsymm_eq_zero_of_lt {n k : ℕ} (hn : finrank ℂ E = n) (hnk : n < k)
    (α : Fin k → realOneOneForms E) : mixedEsymm hn α = 0 := by
  simp [mixedEsymm_def, MvPolynomial.esymm_eq_zero_of_card_lt (σ := Fin n) (by simpa using hnk)]

/-- **The mixed form identity** `α₁ ∧ ⋯ ∧ α_k ∧ ω ^ l = (k! l! / n!) M_k(α₁, …, α_k) ω ^ n`: on
a complex inner product space of dimension `n = k + l`, with `ω` the Kähler form of
multiplication by `i`, real two-forms `α₁, …, α_k` of type (1,1) satisfy it on every tuple of
`2 n` vectors, where `M_k` is the polarization of `α ↦ σ_k(λ[α])`. -/
theorem wedge_wedgeProd_wedgePow_ofComplexModule {n k l : ℕ} (hn : finrank ℂ E = n)
    (hkl : k + l = n) (α : Fin k → realOneOneForms E) (v : Fin (2 * n) → E) :
    wedge (wedgeProd fun i ↦ (α i : E [⋀^Fin 2]→L[ℝ] ℝ))
        ((alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow l)
        (v ∘ Fin.cast (by omega)) =
      (k.factorial * l.factorial / n.factorial * mixedEsymm hn α) *
        (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v := by
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hw : (wedgeProd fun i ↦ (α i : E [⋀^Fin 2]→L[ℝ] ℝ)) = (k.factorial : ℝ)⁻¹ •
      ∑ S : Finset (Fin k), (-1 : ℝ) ^ #S •
        wedgePow ((∑ i ∈ Sᶜ, α i : realOneOneForms E) : E [⋀^Fin 2]→L[ℝ] ℝ) k := by
    simp only [Submodule.coe_sum]
    rw [← factorial_smul_wedgeProd even_two, smul_smul, inv_mul_cancel₀ hk, one_smul]
  rw [hw, wedge_smul_left, wedge_sum_left, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.sum_apply]
  simp only [wedge_smul_left, ContinuousAlternatingMap.smul_apply,
    wedge_wedgePow_wedgePow_ofComplexModule
      (realOneOneForms_apply_I_smul (∑ i ∈ _ᶜ, α i)) hn hkl v, mixedEsymm_def,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  ring

/-- For `k ≤ n`, a scalar `a` is `M_k(α₁, …, α_k)` once `α₁ ∧ ⋯ ∧ α_k ∧ ω ^ (n - k)` is
`(k! (n - k)! / n!) a ω ^ n`; with the mixed form identity, this transfers identities between
wedge products to `M_k`. -/
private theorem mixedEsymm_eq_of_forall_wedge {n k : ℕ} (hn : finrank ℂ E = n) (hkn : k ≤ n)
    {α : Fin k → realOneOneForms E} {a : ℝ}
    (h : ∀ v : Fin (2 * n) → E,
      wedge (wedgeProd fun i ↦ (α i : E [⋀^Fin 2]→L[ℝ] ℝ))
          ((alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow (n - k))
          (v ∘ Fin.cast (by omega)) =
        (k.factorial * (n - k).factorial / n.factorial * a) *
          (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v) :
    mixedEsymm hn α = a := by
  have hc : (k.factorial * (n - k).factorial / n.factorial : ℝ) ≠ 0 := by positivity
  refine mul_left_cancel₀ hc (eq_of_forall_mul_wedgePow_kahlerForm hn fun v ↦ ?_)
  rw [← h v, wedge_wedgeProd_wedgePow_ofComplexModule hn (by omega)]

omit [FiniteDimensional ℂ E] in
/-- Coercing an updated family of (1,1)-forms updates the family of coerced forms. -/
private theorem coe_update {k : ℕ} (α : Fin k → realOneOneForms E) (i : Fin k)
    (z : realOneOneForms E) :
    (fun j ↦ (Function.update α i z j : E [⋀^Fin 2]→L[ℝ] ℝ)) =
      Function.update (fun j ↦ (α j : E [⋀^Fin 2]→L[ℝ] ℝ)) i z :=
  Function.comp_update Subtype.val α i z

/-- `M_k(α₁, …, α_k)`, scaled by `k! l! / n!` for `k + l = n`, is the value of
`α₁ ∧ ⋯ ∧ α_k ∧ ω ^ l` measured against `ω ^ n`; so `M_k` is determined by the wedge product of the
`αᵢ`. -/
theorem mixedEsymm_eq_of_wedgeProd_eq {n k : ℕ} (hn : finrank ℂ E = n)
    {α β : Fin k → realOneOneForms E}
    (h : (wedgeProd fun i ↦ (α i : E [⋀^Fin 2]→L[ℝ] ℝ)) =
      wedgeProd fun i ↦ (β i : E [⋀^Fin 2]→L[ℝ] ℝ)) :
    mixedEsymm hn α = mixedEsymm hn β := by
  rcases lt_or_ge n k with hnk | hkn
  · rw [mixedEsymm_eq_zero_of_lt hn hnk, mixedEsymm_eq_zero_of_lt hn hnk]
  exact mixedEsymm_eq_of_forall_wedge hn hkn fun v ↦ by
    rw [h, wedge_wedgeProd_wedgePow_ofComplexModule hn (by omega)]

/-- **The diagonal of `M_k`**: `M_k(α, …, α) = σ_k(λ[α])`. -/
@[simp]
theorem mixedEsymm_const {n k : ℕ} (hn : finrank ℂ E = n) (α : realOneOneForms E) :
    mixedEsymm hn (fun _ : Fin k ↦ α) =
      MvPolynomial.eval
        ((isSymm_hermitianSesqForm (realOneOneForms_apply_I_smul α)).relEigenvalues hn)
        (MvPolynomial.esymm (Fin n) ℝ k) := by
  rcases lt_or_ge n k with hnk | hkn
  · rw [mixedEsymm_eq_zero_of_lt hn hnk,
      MvPolynomial.esymm_eq_zero_of_card_lt (σ := Fin n) (by simpa using hnk), _root_.map_zero]
  exact mixedEsymm_eq_of_forall_wedge hn hkn fun v ↦ by
    rw [wedgeProd_const,
      wedge_wedgePow_wedgePow_ofComplexModule (realOneOneForms_apply_I_smul α) hn (by omega)]

/-- **Symmetry of `M_k`**: permuting its arguments does not change its value. -/
theorem mixedEsymm_comp_perm {n k : ℕ} (hn : finrank ℂ E = n) (α : Fin k → realOneOneForms E)
    (σ : Equiv.Perm (Fin k)) : mixedEsymm hn (α ∘ σ) = mixedEsymm hn α :=
  mixedEsymm_eq_of_wedgeProd_eq hn
    (wedgeProd_comp_perm even_two (fun i ↦ (α i : E [⋀^Fin 2]→L[ℝ] ℝ)) σ)

/-- `M_k` is additive in each argument. -/
theorem mixedEsymm_update_add {n k : ℕ} (hn : finrank ℂ E = n) (α : Fin k → realOneOneForms E)
    (i : Fin k) (x y : realOneOneForms E) :
    mixedEsymm hn (Function.update α i (x + y)) =
      mixedEsymm hn (Function.update α i x) + mixedEsymm hn (Function.update α i y) := by
  rcases lt_or_ge n k with hnk | hkn
  · simp only [mixedEsymm_eq_zero_of_lt hn hnk, add_zero]
  have hkl : k + (n - k) = n := by omega
  exact mixedEsymm_eq_of_forall_wedge hn hkn fun v ↦ by
    rw [coe_update, Submodule.coe_add, wedgeProd_update_add, wedge_add_left,
      ContinuousAlternatingMap.add_apply, ← coe_update, ← coe_update,
      wedge_wedgeProd_wedgePow_ofComplexModule hn hkl,
      wedge_wedgeProd_wedgePow_ofComplexModule hn hkl, mul_add, add_mul]

/-- `M_k` is homogeneous in each argument. -/
theorem mixedEsymm_update_smul {n k : ℕ} (hn : finrank ℂ E = n) (α : Fin k → realOneOneForms E)
    (i : Fin k) (c : ℝ) (x : realOneOneForms E) :
    mixedEsymm hn (Function.update α i (c • x)) = c * mixedEsymm hn (Function.update α i x) := by
  rcases lt_or_ge n k with hnk | hkn
  · simp only [mixedEsymm_eq_zero_of_lt hn hnk, mul_zero]
  exact mixedEsymm_eq_of_forall_wedge hn hkn fun v ↦ by
    rw [coe_update, Submodule.coe_smul, wedgeProd_update_smul, wedge_smul_left,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul, ← coe_update,
      wedge_wedgeProd_wedgePow_ofComplexModule hn (by omega), mul_left_comm (_ / _) c,
      mul_assoc c]

/-- The polarization `M_k` of `α ↦ σ_k(λ[α])`, as a multilinear form on real (1,1)-forms. -/
def mixedEsymmMultilinear {n : ℕ} (hn : finrank ℂ E = n) (k : ℕ) :
    MultilinearMap (RingHom.id ℝ) (fun _ : Fin k ↦ realOneOneForms E) ℝ where
  toFun := mixedEsymm hn
  map_update_add' α i x y := by
    convert mixedEsymm_update_add hn α i x y
  map_update_smul' α i c x := by
    rw [RingHom.id_apply, smul_eq_mul]
    convert mixedEsymm_update_smul hn α i c x

@[simp]
theorem mixedEsymmMultilinear_apply {n : ℕ} (hn : finrank ℂ E = n) {k : ℕ}
    (α : Fin k → realOneOneForms E) : mixedEsymmMultilinear hn k α = mixedEsymm hn α := (rfl)

/-- The directional derivative of `σ_k ∘ λ` at `β` in the direction `α` is
`∑ᵢ M_k(β, …, β, α, β, …, β)`, with `α` in the `i`-th slot: `σ_k(λ[β + t α])` is the polynomial
`∑_{S ⊆ {1, …, k}} t^{#S} M_k(α on S, β off S)` in `t`. -/
theorem hasDerivAt_esymm_relEigenvalues_add_smul {n k : ℕ} (hn : finrank ℂ E = n)
    (α β : realOneOneForms E) :
    HasDerivAt (fun t : ℝ ↦ MvPolynomial.eval
        ((isSymm_hermitianSesqForm (realOneOneForms_apply_I_smul (β + t • α))).relEigenvalues hn)
        (MvPolynomial.esymm (Fin n) ℝ k))
      (∑ i : Fin k, mixedEsymm hn (Function.update (fun _ ↦ β) i α)) 0 := by
  -- Pull `M_k` back along `(a, b) ↦ a β + b α` to a multilinear form on the
  -- finite-dimensional space `ℝ × ℝ`, where it is automatically continuous.
  let L : ℝ × ℝ →ₗ[ℝ] realOneOneForms E :=
    (LinearMap.fst ℝ ℝ ℝ).smulRight β + (LinearMap.snd ℝ ℝ ℝ).smulRight α
  let g := (mixedEsymmMultilinear hn k).compLinearMap fun _ ↦ L
  let G : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ ℝ × ℝ) ℝ :=
    ⟨g, g.continuous_of_finiteDimensional⟩
  have hG (x : Fin k → ℝ × ℝ) : G x = mixedEsymm hn (L ∘ x) := rfl
  have hline : HasDerivAt (fun t : ℝ ↦ fun _ : Fin k ↦ ((1 : ℝ), t))
      (fun _ ↦ ((0 : ℝ), (1 : ℝ))) 0 :=
    hasDerivAt_pi.2 fun _ ↦ (hasDerivAt_const _ _).prodMk (hasDerivAt_id 0)
  convert (G.hasFDerivAt _).comp_hasDerivAt (0 : ℝ) hline using 1
  · funext t
    simp [hG, Function.comp_def, L]
  · rw [ContinuousMultilinearMap.linearDeriv_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hG, Function.comp_update]
    simp [Function.comp_def, L]

/-- **`M_k` as a derivative**: `(m + 1) M_{m+1}(α, β, …, β)` is the derivative of
`t ↦ σ_{m+1}(λ[β + t α])` at `0`, by symmetry of `M_{m+1}`. -/
theorem hasDerivAt_esymm_relEigenvalues_add_smul_cons {n m : ℕ} (hn : finrank ℂ E = n)
    (α β : realOneOneForms E) :
    HasDerivAt (fun t : ℝ ↦ MvPolynomial.eval
        ((isSymm_hermitianSesqForm (realOneOneForms_apply_I_smul (β + t • α))).relEigenvalues hn)
        (MvPolynomial.esymm (Fin n) ℝ (m + 1)))
      ((m + 1) * mixedEsymm hn (Fin.cons α fun _ : Fin m ↦ β)) 0 := by
  convert hasDerivAt_esymm_relEigenvalues_add_smul (k := m + 1) hn α β using 1
  have hi (i : Fin (m + 1)) : mixedEsymm hn (Function.update (fun _ ↦ β) i α) =
      mixedEsymm hn (Fin.cons α fun _ : Fin m ↦ β) := by
    rw [← mixedEsymm_comp_perm hn _ (Equiv.swap 0 i)]
    congr 1
    funext j
    rcases eq_or_ne j 0 with rfl | hj0
    · simp
    rcases eq_or_ne j i with rfl | hji
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj0
      simp [Equiv.swap_apply_right, Function.update_of_ne hj0.symm]
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj0
      simp [Equiv.swap_apply_of_ne_of_ne hj0 hji, Function.update_of_ne hji]
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end TauCeti.AlmostComplexStructure

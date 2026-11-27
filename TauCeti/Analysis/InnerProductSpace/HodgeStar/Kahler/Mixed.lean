/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Esymm
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Complex

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

* `TauCeti.AlmostComplexStructure.realOneOneForms E`: the real two-forms of type (1,1), those
  with `α(i u, i v) = α(u, v)`, as a real subspace.
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

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The real two-forms of type (1,1) on a complex vector space, those invariant under
multiplication by `i` in both arguments: `α(i u, i v) = α(u, v)`. -/
def realOneOneForms : Submodule ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) where
  carrier := {α | ∀ u v : E, α ![I • u, I • v] = α ![u, v]}
  add_mem' {α β} hα hβ u v := by
    rw [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.add_apply, hα u v, hβ u v]
  zero_mem' _ _ := rfl
  smul_mem' c α hα u v := by
    rw [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply, hα u v]

variable {E}

theorem mem_realOneOneForms {α : E [⋀^Fin 2]→L[ℝ] ℝ} :
    α ∈ realOneOneForms E ↔ ∀ u v : E, α ![I • u, I • v] = α ![u, v] := Iff.rfl

/-- A real (1,1)-form satisfies `α(i u, i v) = α(u, v)`. -/
theorem realOneOneForms_apply_I_smul (α : realOneOneForms E) (u v : E) :
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) ![I • u, I • v] = (α : E [⋀^Fin 2]→L[ℝ] ℝ) ![u, v] :=
  mem_realOneOneForms.1 α.property u v

variable [FiniteDimensional ℂ E]

/-- The polarization `M_k(α₁, …, α_k)` of `α ↦ σ_k(λ[α])` on real (1,1)-forms, where `λ[α]` are
the eigenvalues of the Hermitian form `H_α` relative to the inner product and `σ_k` is the `k`-th
elementary symmetric polynomial:
`M_k(α₁, …, α_k) = (1 / k!) ∑_{S ⊆ {1, …, k}} (-1)^{#S} σ_k(λ[∑_{i ∉ S} αᵢ])`. -/
def mixedEsymm {n k : ℕ} (hn : finrank ℂ E = n) (α : Fin k → realOneOneForms E) : ℝ :=
  (k.factorial : ℝ)⁻¹ * ∑ S : Finset (Fin k), (-1 : ℝ) ^ #S *
    MvPolynomial.eval
      ((isSymm_hermitianSesqForm (realOneOneForms_apply_I_smul (∑ i ∈ Sᶜ, α i))).relEigenvalues hn)
      (MvPolynomial.esymm (Fin n) ℝ k)

/-- `M_k` vanishes for `k > n`, since then `σ_k` vanishes on `ℝⁿ`. -/
theorem mixedEsymm_eq_zero_of_lt {n k : ℕ} (hn : finrank ℂ E = n) (hnk : n < k)
    (α : Fin k → realOneOneForms E) : mixedEsymm hn α = 0 := by
  have hzero : MvPolynomial.esymm (Fin n) ℝ k = 0 := by
    rw [MvPolynomial.esymm_eq_sum_subtype]
    exact Finset.sum_eq_zero fun t _ ↦
      absurd (t.property ▸ Finset.card_le_univ (t : Finset (Fin n))) (by simpa using hnk.not_ge)
  simp [mixedEsymm, hzero]

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
  rw [hw, wedge_def, pairedWedge_smul_left, pairedWedge_sum_left,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sum_apply]
  simp only [pairedWedge_smul_left, ContinuousAlternatingMap.smul_apply, ← wedge_def,
    wedge_wedgePow_wedgePow_ofComplexModule
      (realOneOneForms_apply_I_smul (∑ i ∈ _ᶜ, α i)) hn hkl v, mixedEsymm,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  ring

/-- The top power `ω ^ n` of the Kähler form does not vanish: it takes the value `n!` on the real
frame of an orthonormal basis. -/
theorem exists_wedgePow_kahlerForm_apply_ne_zero {n : ℕ} (hn : finrank ℂ E = n) :
    ∃ v : Fin (2 * n) → E,
      (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v ≠ 0 := by
  let u : OrthonormalBasis (Fin n) ℂ E := (stdOrthonormalBasis ℂ E).reindex (finCongr hn)
  refine ⟨(ofComplexModule E).complexRealFrame u, ?_⟩
  rw [wedgePow_kahlerForm_apply_complexRealFrame real_inner_ofComplexModule_ofComplexModule
    u.orthonormal.real u.orthonormal.real_inner_ofComplexModule_eq_zero]
  positivity

/-- Two scalars agree if they agree after multiplying the top power of the Kähler form. -/
theorem eq_of_forall_mul_wedgePow_kahlerForm {n : ℕ} (hn : finrank ℂ E = n) {a b : ℝ}
    (h : ∀ v : Fin (2 * n) → E,
      a * (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v =
        b * (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v) :
    a = b := by
  obtain ⟨v, hv⟩ := exists_wedgePow_kahlerForm_apply_ne_zero hn
  exact mul_right_cancel₀ hv (h v)

/-- `M_k(α₁, …, α_k)`, scaled by `k! l! / n!` for `k + l = n`, is the value of
`α₁ ∧ ⋯ ∧ α_k ∧ ω ^ l` measured against `ω ^ n`; so `M_k` is determined by the wedge product of the
`αᵢ`. -/
theorem mixedEsymm_eq_of_wedgeProd_eq {n k : ℕ} (hn : finrank ℂ E = n) (hkn : k ≤ n)
    {α β : Fin k → realOneOneForms E}
    (h : (wedgeProd fun i ↦ (α i : E [⋀^Fin 2]→L[ℝ] ℝ)) =
      wedgeProd fun i ↦ (β i : E [⋀^Fin 2]→L[ℝ] ℝ)) :
    mixedEsymm hn α = mixedEsymm hn β := by
  have hkl : k + (n - k) = n := by omega
  have hc : (k.factorial * (n - k).factorial / n.factorial : ℝ) ≠ 0 := by positivity
  refine mul_left_cancel₀ hc (eq_of_forall_mul_wedgePow_kahlerForm hn fun v ↦ ?_)
  rw [← wedge_wedgeProd_wedgePow_ofComplexModule hn hkl,
    ← wedge_wedgeProd_wedgePow_ofComplexModule hn hkl, h]

/-- **The diagonal of `M_k`**: `M_k(α, …, α) = σ_k(λ[α])`. -/
theorem mixedEsymm_const {n k : ℕ} (hn : finrank ℂ E = n) (α : realOneOneForms E) :
    mixedEsymm hn (fun _ : Fin k ↦ α) =
      MvPolynomial.eval
        ((isSymm_hermitianSesqForm (realOneOneForms_apply_I_smul α)).relEigenvalues hn)
        (MvPolynomial.esymm (Fin n) ℝ k) := by
  rcases lt_or_ge n k with hnk | hkn
  · have hzero : MvPolynomial.esymm (Fin n) ℝ k = 0 := by
      rw [MvPolynomial.esymm_eq_sum_subtype]
      exact Finset.sum_eq_zero fun t _ ↦
        absurd (t.property ▸ Finset.card_le_univ (t : Finset (Fin n))) (by simpa using hnk.not_ge)
    rw [mixedEsymm_eq_zero_of_lt hn hnk, hzero, _root_.map_zero]
  have hkl : k + (n - k) = n := by omega
  have hc : (k.factorial * (n - k).factorial / n.factorial : ℝ) ≠ 0 := by positivity
  refine mul_left_cancel₀ hc (eq_of_forall_mul_wedgePow_kahlerForm hn fun v ↦ ?_)
  rw [← wedge_wedgeProd_wedgePow_ofComplexModule hn hkl,
    ← wedge_wedgePow_wedgePow_ofComplexModule (realOneOneForms_apply_I_smul α) hn hkl,
    wedgeProd_const]

/-- **Symmetry of `M_k`**: permuting its arguments does not change its value. -/
theorem mixedEsymm_comp_perm {n k : ℕ} (hn : finrank ℂ E = n) (α : Fin k → realOneOneForms E)
    (σ : Equiv.Perm (Fin k)) : mixedEsymm hn (α ∘ σ) = mixedEsymm hn α := by
  rcases lt_or_ge n k with hnk | hkn
  · rw [mixedEsymm_eq_zero_of_lt hn hnk, mixedEsymm_eq_zero_of_lt hn hnk]
  exact mixedEsymm_eq_of_wedgeProd_eq hn hkn
    (wedgeProd_comp_perm even_two (fun i ↦ (α i : E [⋀^Fin 2]→L[ℝ] ℝ)) σ)

/-- `M_k` is additive in each argument. -/
theorem mixedEsymm_update_add {n k : ℕ} (hn : finrank ℂ E = n) (α : Fin k → realOneOneForms E)
    (i : Fin k) (x y : realOneOneForms E) :
    mixedEsymm hn (Function.update α i (x + y)) =
      mixedEsymm hn (Function.update α i x) + mixedEsymm hn (Function.update α i y) := by
  rcases lt_or_ge n k with hnk | hkn
  · simp only [mixedEsymm_eq_zero_of_lt hn hnk, add_zero]
  have hkl : k + (n - k) = n := by omega
  have hc : (k.factorial * (n - k).factorial / n.factorial : ℝ) ≠ 0 := by positivity
  have hcoe (z : realOneOneForms E) : (fun j ↦ (Function.update α i z j : E [⋀^Fin 2]→L[ℝ] ℝ)) =
      Function.update (fun j ↦ (α j : E [⋀^Fin 2]→L[ℝ] ℝ)) i z :=
    Function.comp_update Subtype.val α i z
  refine mul_left_cancel₀ hc (eq_of_forall_mul_wedgePow_kahlerForm hn fun v ↦ ?_)
  rw [mul_add, add_mul, ← wedge_wedgeProd_wedgePow_ofComplexModule hn hkl,
    ← wedge_wedgeProd_wedgePow_ofComplexModule hn hkl,
    ← wedge_wedgeProd_wedgePow_ofComplexModule hn hkl, hcoe, hcoe, hcoe, Submodule.coe_add,
    wedgeProd_update_add, wedge_add_left, ContinuousAlternatingMap.add_apply]

/-- `M_k` is homogeneous in each argument. -/
theorem mixedEsymm_update_smul {n k : ℕ} (hn : finrank ℂ E = n) (α : Fin k → realOneOneForms E)
    (i : Fin k) (c : ℝ) (x : realOneOneForms E) :
    mixedEsymm hn (Function.update α i (c • x)) = c * mixedEsymm hn (Function.update α i x) := by
  rcases lt_or_ge n k with hnk | hkn
  · simp only [mixedEsymm_eq_zero_of_lt hn hnk, mul_zero]
  have hkl : k + (n - k) = n := by omega
  have hc : (k.factorial * (n - k).factorial / n.factorial : ℝ) ≠ 0 := by positivity
  have hcoe (z : realOneOneForms E) : (fun j ↦ (Function.update α i z j : E [⋀^Fin 2]→L[ℝ] ℝ)) =
      Function.update (fun j ↦ (α j : E [⋀^Fin 2]→L[ℝ] ℝ)) i z :=
    Function.comp_update Subtype.val α i z
  refine mul_left_cancel₀ hc (eq_of_forall_mul_wedgePow_kahlerForm hn fun v ↦ ?_)
  rw [mul_left_comm (_ / _) c, mul_assoc c, ← wedge_wedgeProd_wedgePow_ofComplexModule hn hkl,
    ← wedge_wedgeProd_wedgePow_ofComplexModule hn hkl, hcoe, hcoe, Submodule.coe_smul,
    wedgeProd_update_smul, wedge_smul_left, ContinuousAlternatingMap.smul_apply, smul_eq_mul]

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
  classical
  set f := mixedEsymmMultilinear (E := E) hn k
  set c : Finset (Fin k) → ℝ := fun S ↦ f (S.piecewise (fun _ ↦ α) fun _ ↦ β)
  have hexp (t : ℝ) : MvPolynomial.eval
      ((isSymm_hermitianSesqForm (realOneOneForms_apply_I_smul (β + t • α))).relEigenvalues hn)
      (MvPolynomial.esymm (Fin n) ℝ k) = ∑ S : Finset (Fin k), t ^ #S * c S := by
    rw [← mixedEsymm_const hn, ← mixedEsymmMultilinear_apply,
      show (fun _ : Fin k ↦ β + t • α) = (fun _ ↦ t • α) + fun _ ↦ β from
        funext fun _ ↦ add_comm _ _, f.map_add_univ]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    have hS : S.piecewise (fun _ ↦ t • α) (fun _ ↦ β) =
        S.piecewise (fun i ↦ t • S.piecewise (fun _ ↦ α) (fun _ ↦ β) i)
          (S.piecewise (fun _ ↦ α) fun _ ↦ β) := by
      funext i
      by_cases hi : i ∈ S <;> simp [Finset.piecewise, hi]
    rw [hS, f.map_piecewise_smul, Finset.prod_const, RingHom.id_apply, smul_eq_mul]
  simp only [hexp]
  have hd : HasDerivAt (fun t : ℝ ↦ ∑ S : Finset (Fin k), t ^ #S * c S)
      (∑ S : Finset (Fin k), (#S * (0 : ℝ) ^ (#S - 1)) * c S) 0 :=
    HasDerivAt.fun_sum fun S _ ↦ HasDerivAt.mul_const (hasDerivAt_pow #S (0 : ℝ)) (c S)
  convert hd using 1
  have hzero (S : Finset (Fin k)) (hS : S ∉ Finset.univ.image fun i : Fin k ↦ {i}) :
      (#S * (0 : ℝ) ^ (#S - 1)) * c S = 0 := by
    have h1 : #S ≠ 1 := fun h1 ↦ by
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h1
      exact hS (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rcases Nat.eq_zero_or_pos #S with h0 | hpos
    · simp [h0]
    · rw [zero_pow (by omega), mul_zero, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ _) fun S _ hS ↦ hzero S hS,
    Finset.sum_image fun i _ j _ h ↦ Finset.singleton_injective h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hpw : ({i} : Finset (Fin k)).piecewise (fun _ ↦ α) (fun _ ↦ β) =
      Function.update (fun _ ↦ β) i α := by
    funext j
    by_cases hj : j = i <;> simp [Finset.piecewise, hj]
  simp only [Finset.card_singleton, Nat.cast_one, Nat.sub_self, pow_zero, mul_one, one_mul, c,
    hpw]
  rfl

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
    · simp [Equiv.swap_apply_of_ne_of_ne hj0 hji, Function.update_of_ne hji]
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj0
      simp
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end TauCeti.AlmostComplexStructure

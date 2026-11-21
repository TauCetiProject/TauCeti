/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import TauCeti.Analysis.InnerProductSpace.SkewSymmetric.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Cons

/-!
# The real normal form of commuting skew-symmetric maps

Let `E` be a finite-dimensional real inner product space and let `(A i)` be a family of pairwise
commuting skew-symmetric linear maps of `E`, `⟪A i x, y⟫ = -⟪x, A i y⟫`. Over `ℂ` such a family is
simultaneously diagonalizable with imaginary eigenvalues. Over `ℝ` this file proves the
corresponding *real normal form*: `E` is the orthogonal direct sum of the common kernel of the
`A i` and finitely many planes `span(q_k, p_k)`, with `(q_k, p_k)` orthonormal, on each of which
every `A i` acts as a multiple of the quarter turn `J_k : q_k ↦ p_k, p_k ↦ -q_k`:

`A i q_k = a_k(i) p_k`, `A i p_k = -a_k(i) q_k`,

where for each plane some coefficient `a_k(i)` is nonzero
(`TauCeti.exists_orthonormal_apply_eq_smul_of_skew`). The planes are found one at a time. If some
`A i₀` is nonzero, the maps `A i ∘ A i₀` are symmetric and commute, so they have a joint
eigenvector `q` (`LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`) on which `A i₀ ∘ A i₀` is
a negative multiple of the identity; the plane spanned by `q` and `A i₀ q` is invariant under
every `A i`, and so is its orthogonal complement, where one continues by induction on the
dimension.

When the family is the image of a linear map `ρ : V → End(E)`, the coefficients are linear in the
parameter: there are nonzero linear functionals `α_k` on `V` with `ρ X = α_k(X) J_k` on the `k`-th
plane (`TauCeti.exists_orthonormal_apply_eq_smul_of_skew_of_linearMap`). This is the real form of
the weight decomposition. For an abelian Lie subalgebra `𝔱` of a Lie algebra `𝔤` with an invariant
inner product, applied to `ρ = ad|𝔱`, it splits `𝔤` into the centralizer of `𝔱` and the *real root
planes*, on which `ad H` acts as `α(H) J` for a nonzero root `α`; for the Lie algebra of a maximal
torus of a compact Lie group, the centralizer is that Lie algebra itself.

## Main results

* `TauCeti.exists_orthonormal_apply_eq_smul_of_skew`: the real normal form of a commuting family
  of skew-symmetric maps.
* `TauCeti.exists_orthonormal_apply_eq_smul_of_skew_of_linearMap`: the same for a linear family,
  with linear weights.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapters IV and V (maximal tori and the roots of a compact Lie group).
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  Section 2.5 (real normal matrices and their block-diagonal normal form).
-/

public section

open Module
open scoped InnerProductSpace Function

namespace TauCeti

universe u

variable {ι : Type*}

section Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : ι → E →ₗ[ℝ] E}

/-- For a commuting family of skew-symmetric maps containing a nonzero map `A i₀`, the symmetric
maps `A i ∘ A i₀` have a joint unit eigenvector whose eigenvalue for `A i₀ ∘ A i₀` is nonzero. -/
private theorem exists_norm_eq_one_apply_apply_eq_smul_of_skew [FiniteDimensional ℝ E]
    (hA : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ) (hc : ∀ i j, Commute (A i) (A j)) {i₀ : ι}
    (hi₀ : A i₀ ≠ 0) :
    ∃ (q : E) (χ : ι → ℝ), ‖q‖ = 1 ∧ χ i₀ ≠ 0 ∧ ∀ i, A i (A i₀ q) = χ i • q := by
  set T : ι → E →ₗ[ℝ] E := fun i ↦ A i * A i₀
  have hTsymm (i : ι) : (T i).IsSymmetric := fun x y ↦ by
    have hcomm := LinearMap.congr_fun (hc i₀ i).eq y
    simp only [T, mul_apply_eq_comp] at hcomm ⊢
    rw [hA, hA, neg_neg, hcomm]
  have hTcomm : Pairwise (Commute on T) := fun i j _ ↦
    ((hc i j).mul_left (hc i₀ j)).mul_right ((hc i i₀).mul_left (hc i₀ i₀))
  obtain ⟨χ, hχ, hne⟩ :
      ∃ χ : ι → ℝ, χ i₀ ≠ 0 ∧ (⨅ i, Module.End.eigenspace (T i) (χ i)) ≠ ⊥ := by
    -- Otherwise every joint eigenspace lies in `ker (A i₀ ∘ A i₀)`, which is then everything.
    by_contra! h
    apply hi₀
    have hle : (⊤ : Submodule ℝ E) ≤ LinearMap.ker (T i₀) := by
      rw [← LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTsymm hTcomm, iSup_le_iff]
      intro χ
      by_cases h0 : χ i₀ = 0
      · exact (iInf_le _ i₀).trans (by rw [h0, Module.End.eigenspace_zero])
      · rw [h χ h0]
        exact bot_le
    ext x
    have hx : A i₀ (A i₀ x) = 0 := hle Submodule.mem_top
    have hsq : ‖A i₀ x‖ ^ 2 = 0 := by
      rw [norm_sq_apply_of_skew (hA i₀), hx, inner_zero_right, neg_zero]
    simpa using hsq
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨‖v‖⁻¹ • v, χ, norm_smul_inv_norm hv0, hχ, fun i ↦ ?_⟩
  have h := (Submodule.mem_iInf _).1 (Submodule.smul_mem _ ‖v‖⁻¹ hv) i
  rwa [Module.End.mem_eigenspace_iff] at h

/-- A commuting family of skew-symmetric maps containing a nonzero map `A i₀` has a common invariant
plane spanned by orthonormal vectors `q, p`, on which each `A i` is `a i` times the quarter turn
`q ↦ p, p ↦ -q`, with `a i₀ ≠ 0`. -/
private theorem exists_orthonormal_pair_apply_eq_smul_of_skew [FiniteDimensional ℝ E]
    (hA : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ) (hc : ∀ i j, Commute (A i) (A j)) {i₀ : ι}
    (hi₀ : A i₀ ≠ 0) :
    ∃ (q p : E) (a : ι → ℝ), ‖q‖ = 1 ∧ ‖p‖ = 1 ∧ ⟪q, p⟫_ℝ = 0 ∧ a i₀ ≠ 0 ∧
      ∀ i, A i q = a i • p ∧ A i p = -a i • q := by
  obtain ⟨q, χ, hq, hχ, hTq⟩ := exists_norm_eq_one_apply_apply_eq_smul_of_skew hA hc hi₀
  -- `A i₀` moves `q` by the length `s`, with `s ^ 2 = -χ i₀`; the plane is `span(q, A i₀ q)`.
  set s : ℝ := ‖A i₀ q‖
  have hs2 : s ^ 2 = -χ i₀ := by
    rw [norm_sq_apply_of_skew (hA i₀), hTq, real_inner_smul_right, real_inner_self_eq_norm_sq,
      hq]
    ring
  have hs : s ≠ 0 := fun h ↦ hχ (by rw [h] at hs2; linarith)
  -- Each `A i` maps `q` into the line of `A i₀ q`: `χ i₀ • A i q = χ i • A i₀ q`.
  have key (i : ι) : χ i₀ • A i q = χ i • A i₀ q := by
    have hcomm := LinearMap.congr_fun (hc i₀ i).eq (A i₀ q)
    simp only [mul_apply_eq_comp] at hcomm
    rw [← map_smul, ← hTq, ← hcomm, hTq, map_smul]
  refine ⟨q, s⁻¹ • A i₀ q, fun i ↦ χ i / χ i₀ * s, hq,
    norm_smul_inv_norm (norm_ne_zero_iff.1 hs), ?_, by simp [hχ, hs], fun i ↦ ⟨?_, ?_⟩⟩
  · rw [real_inner_smul_right, inner_self_apply_eq_zero_of_skew (hA i₀), mul_zero]
  · rw [mul_smul, smul_inv_smul₀ hs, div_eq_inv_mul, mul_smul, ← key, inv_smul_smul₀ hχ]
  · rw [map_smul, hTq, smul_smul]
    congr 1
    field_simp
    linear_combination χ i * hs2

end Plane

/-- The real normal form, with the orthogonality conclusion stated pointwise; proved by induction
on the dimension. -/
private theorem exists_orthonormal_apply_eq_smul_of_skew_aux (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
      finrank ℝ E = n → ∀ A : ι → E →ₗ[ℝ] E, (∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ) →
      (∀ i j, Commute (A i) (A j)) →
      ∃ (r : ℕ) (q p : Fin r → E) (a : Fin r → ι → ℝ), Orthonormal ℝ (Sum.elim q p) ∧
        (∀ k i, A i (q k) = a k i • p k ∧ A i (p k) = -a k i • q k) ∧ (∀ k, ∃ i, a k i ≠ 0) ∧
        ∀ x, (∀ k, ⟪q k, x⟫_ℝ = 0 ∧ ⟪p k, x⟫_ℝ = 0) → ∀ i, A i x = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E _ _ _ hn A hA hc
  by_cases h0 : ∀ i, A i = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ⟨fun j ↦ ?_, fun j ↦ ?_⟩, fun k ↦ k.elim0,
      fun k ↦ k.elim0, fun x _ i ↦ by simp [h0 i]⟩ <;> rcases j with j | j <;> exact j.elim0
  simp only [not_forall] at h0
  obtain ⟨i₀, hi₀⟩ := h0
  obtain ⟨q₀, p₀, a₀, hq₀, hp₀, hqp₀, ha₀, hA₀⟩ :=
    exists_orthonormal_pair_apply_eq_smul_of_skew hA hc hi₀
  -- The orthogonal complement `F` of the plane of `q₀, p₀` is invariant under every `A i`.
  set F : Submodule ℝ E := (ℝ ∙ q₀)ᗮ ⊓ (ℝ ∙ p₀)ᗮ
  have hF (x : E) : x ∈ F ↔ ⟪q₀, x⟫_ℝ = 0 ∧ ⟪p₀, x⟫_ℝ = 0 := by
    simp only [F, Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hmaps (i : ι) : ∀ x ∈ F, A i x ∈ F := fun x hx ↦ by
    rw [hF] at hx ⊢
    have h₁ := hA i q₀ x
    have h₂ := hA i p₀ x
    rw [(hA₀ i).1, real_inner_smul_left, hx.2, mul_zero] at h₁
    rw [(hA₀ i).2, real_inner_smul_left, hx.1, mul_zero] at h₂
    constructor <;> linarith
  have hlt : finrank ℝ F < n := by
    rw [← hn]
    refine Submodule.finrank_lt fun htop ↦ ?_
    have h := ((hF q₀).1 (htop ▸ Submodule.mem_top)).1
    rw [real_inner_self_eq_norm_sq, hq₀] at h
    norm_num at h
  set B : ι → F →ₗ[ℝ] F := fun i ↦ (A i).restrict (hmaps i)
  have hB (i : ι) (x : F) : (B i x : E) = A i x := LinearMap.coe_restrict_apply (hmaps i) x
  obtain ⟨r, q, p, a, hon, hact, hne, hker⟩ := ih _ hlt F rfl B
    (fun i x y ↦ by simp only [Submodule.coe_inner, hB, hA])
    (fun i j ↦ LinearMap.ext fun x ↦ Subtype.ext <| by
      simpa only [mul_apply_eq_comp, hB] using LinearMap.congr_fun (hc i j).eq (x : E))
  have hon' : Orthonormal ℝ (Sum.elim (fun k ↦ (q k : E)) fun k ↦ (p k : E)) := by
    convert hon.comp_linearIsometry F.subtypeₗᵢ using 1
    ext (k | k) <;> rfl
  refine ⟨r + 1, Fin.cons q₀ fun k ↦ (q k : E), Fin.cons p₀ fun k ↦ (p k : E), Fin.cons a₀ a,
    orthonormal_sum_elim_cons_iff.2 ⟨⟨hq₀, hp₀, hqp₀⟩, fun k ↦ ⟨((hF _).1 (q k).property).1,
      ((hF _).1 (q k).property).2, (hF _).1 (p k).property⟩, hon'⟩, fun k i ↦ ?_, fun k ↦ ?_,
    fun x hx i ↦ ?_⟩
  · cases k using Fin.cases with
    | zero => simpa using hA₀ i
    | succ k =>
      simp only [Fin.cons_succ]
      exact ⟨congrArg Subtype.val (hact k i).1, congrArg Subtype.val (hact k i).2⟩
  · cases k using Fin.cases with
    | zero => exact ⟨i₀, ha₀⟩
    | succ k => exact hne k
  · have hxF : x ∈ F := (hF x).2 (by simpa using hx 0)
    have h := hker ⟨x, hxF⟩ (fun k ↦ by simpa [Submodule.coe_inner] using hx k.succ) i
    simpa [hB] using congrArg (Subtype.val : F → E) h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Real normal form of commuting skew-symmetric maps.** For a family of pairwise commuting
skew-symmetric maps `A i` of a finite-dimensional real inner product space `E`, there are
finitely many planes with orthonormal bases `(q k, p k)`, pairwise orthogonal, and coefficients
`a k i` such that `A i q_k = a_k(i) p_k` and `A i p_k = -a_k(i) q_k`, so that `A i` acts on the
`k`-th plane as `a_k(i)` times the quarter turn `q_k ↦ p_k ↦ -q_k`. On each plane some coefficient
is nonzero, and the orthogonal complement of all the planes is the common kernel of the `A i`. -/
theorem exists_orthonormal_apply_eq_smul_of_skew (A : ι → E →ₗ[ℝ] E)
    (hA : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ) (hc : Pairwise fun i j ↦ Commute (A i) (A j)) :
    ∃ (r : ℕ) (q p : Fin r → E) (a : Fin r → ι → ℝ), Orthonormal ℝ (Sum.elim q p) ∧
      (∀ k i, A i (q k) = a k i • p k ∧ A i (p k) = -a k i • q k) ∧ (∀ k, ∃ i, a k i ≠ 0) ∧
      (Submodule.span ℝ (Set.range (Sum.elim q p)))ᗮ = ⨅ i, LinearMap.ker (A i) := by
  have hc' (i j : ι) : Commute (A i) (A j) := by
    rcases eq_or_ne i j with rfl | hij
    exacts [Commute.refl _, hc hij]
  obtain ⟨r, q, p, a, hon, hact, hne, hker⟩ :=
    exists_orthonormal_apply_eq_smul_of_skew_aux (finrank ℝ E) E rfl A hA hc'
  refine ⟨r, q, p, a, hon, hact, hne, Submodule.ext fun x ↦ ?_⟩
  rw [← Submodule.span_singleton_le_iff_mem, ← Submodule.isOrtho_iff_le, Submodule.isOrtho_comm,
    Submodule.isOrtho_span, Submodule.mem_iInf]
  simp only [Set.forall_mem_range, Set.mem_singleton_iff, forall_eq]
  refine ⟨fun hx i ↦ hker x (fun k ↦ ⟨hx (.inl k), hx (.inr k)⟩) i, fun hx ↦ ?_⟩
  -- Conversely, `q k` and `p k` lie in the range of an `A i` with `a k i ≠ 0`, which is orthogonal
  -- to the common kernel.
  have horth (i : ι) (y : E) : ⟪A i y, x⟫_ℝ = 0 := by
    rw [hA, LinearMap.mem_ker.1 (hx i), inner_zero_right, neg_zero]
  rintro (k | k) <;> obtain ⟨i, hi⟩ := hne k
  · have h := horth i (p k)
    rwa [(hact k i).2, real_inner_smul_left, mul_eq_zero, neg_eq_zero, or_iff_right hi] at h
  · have h := horth i (q k)
    rwa [(hact k i).1, real_inner_smul_left, mul_eq_zero, or_iff_right hi] at h

/-- **Real weight decomposition of a commuting linear family of skew-symmetric maps.** If
`ρ : V → End(E)` is linear with pairwise commuting skew-symmetric values, there are finitely many
pairwise orthogonal planes with orthonormal bases `(q k, p k)` and nonzero linear functionals
`α k` on `V` such that `ρ X q_k = α_k(X) p_k` and `ρ X p_k = -α_k(X) q_k`, and the orthogonal
complement of all the planes is the common kernel of the `ρ X`. For `ρ = ad` restricted to an
abelian subalgebra and an invariant inner product, these are the real root planes and the real
roots. -/
theorem exists_orthonormal_apply_eq_smul_of_skew_of_linearMap {V : Type*} [AddCommGroup V]
    [Module ℝ V] (ρ : V →ₗ[ℝ] E →ₗ[ℝ] E) (hρ : ∀ X x y, ⟪ρ X x, y⟫_ℝ = -⟪x, ρ X y⟫_ℝ)
    (hc : ∀ X Y, Commute (ρ X) (ρ Y)) :
    ∃ (r : ℕ) (q p : Fin r → E) (α : Fin r → Dual ℝ V), Orthonormal ℝ (Sum.elim q p) ∧
      (∀ k X, ρ X (q k) = α k X • p k ∧ ρ X (p k) = -α k X • q k) ∧ (∀ k, α k ≠ 0) ∧
      (Submodule.span ℝ (Set.range (Sum.elim q p)))ᗮ = ⨅ X, LinearMap.ker (ρ X) := by
  obtain ⟨r, q, p, a, hon, hact, hne, hker⟩ :=
    exists_orthonormal_apply_eq_smul_of_skew (ρ : V → E →ₗ[ℝ] E) hρ fun X Y _ ↦ hc X Y
  -- The coefficient of `ρ X q_k` along the unit vector `p_k` is linear in `X`.
  have hp (k : Fin r) : p k ≠ 0 := hon.ne_zero (.inr k)
  let α (k : Fin r) : Dual ℝ V :=
    { toFun := a k
      map_add' := fun X Y ↦ smul_left_injective ℝ (hp k) <| by
        simp only [add_smul, ← (hact k _).1, map_add, LinearMap.add_apply]
      map_smul' := fun c X ↦ smul_left_injective ℝ (hp k) <| by
        simp only [RingHom.id_apply, smul_eq_mul, mul_smul, ← (hact k _).1, map_smul,
          LinearMap.smul_apply] }
  refine ⟨r, q, p, α, hon, hact, fun k h ↦ ?_, hker⟩
  obtain ⟨X, hX⟩ := hne k
  exact hX (LinearMap.congr_fun h X)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson
import TauCeti.Geometry.Symplectic.Lagrangian.Basic

/-!
# Semidefinite members of a torus of compact elements of `sp(V, ω)`

Let `(V, ω)` be a finite-dimensional real symplectic vector space with a compatible complex
structure `J`, and let `A : 𝔥 → sp(V, ω)` be a linear map from a nonzero finite-dimensional real
space `𝔥` whose values pairwise commute and are `J`-complex linear: the infinitesimal action of a
torus on `V` by linear symplectomorphisms. In a common Darboux basis
(`exists_isDarbouxBasis_forall_hamiltonianEndEquiv_symm_eq_sum_apply_smul_elliptic` in the
namespace `TauCeti.SymplecticForm`) every `A ξ` rotates the plane `span(qₖ, pₖ)` with angular
frequency `αₖ(ξ)`, for linear weights `αₖ ∈ 𝔥*`, and its quadratic Hamiltonian is
`v ↦ ½ ω(A ξ v, v) = ∑ₖ αₖ(ξ) Iₖ`, which is positive semidefinite when every `αₖ(ξ)` is nonnegative
(`TauCeti.SymplecticForm.apply_apply_nonneg_of_hamiltonianEndEquiv_symm_eq_sum_smul_elliptic`).

This file proves that if the action fixes an isotropic subspace `W` pointwise and
`dim V ≤ 2 (dim W + dim 𝔥)`, then some nonzero `ξ ∈ 𝔥` has a positive semidefinite quadratic
Hamiltonian, `0 ≤ ω(A ξ v, v)` for every `v`
(`TauCeti.SymplecticForm.exists_ne_zero_forall_apply_apply_nonneg`).

* **Few nonzero weights.** A vector `w` killed by every `A ξ` has no component in a plane with
  nonzero weight `αₖ`: if `αₖ(ξ) ≠ 0`, then `qₖ` and `pₖ` are multiples of `A ξ pₖ` and `A ξ qₖ`, so
  `ω(w, qₖ) = ω(w, pₖ) = 0` by skew-adjointness. Hence `W` together with the vectors `qₖ` of the
  planes of nonzero weight spans an isotropic subspace in which `W` is a direct summand, and the
  number of nonzero weights is at most `n - dim W ≤ dim 𝔥`, where `dim V = 2n`.
* **The nonzero weights form a basis of `𝔥*`.** If `A` is not injective, a nonzero `ξ` with
  `A ξ = 0` will do. Otherwise, if `αₖ(ξ) = 0` for every `k`, then `A ξ = 0`, so `ξ = 0`.
  Thus `ξ ↦ (αₖ(ξ))ₖ`, over the nonzero weights, is injective; as there are at most
  `dim 𝔥` of them it is bijective, and some `ξ` has `αₖ(ξ) = 1` for every nonzero weight. Its
  quadratic Hamiltonian is the sum of the elliptic blocks `Iₖ` of nonzero weight.

This is the linear algebra behind the fact that on a symplectic toric manifold a point with a
nontrivial isotropy algebra is a local extremum of some component of the moment map: the isotropy
algebra acts on the tangent space fixing the isotropic orbit tangent space, whose dimension is
`dim G - dim 𝔤_x = ½ dim M - dim 𝔤_x`.

## References

* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, Section 2.
* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*, Bull. Soc.
  Math. France 116 (1988), 315–339.
-/

public section

open Module

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V}

section Weights

variable {𝔥 : Type*} [AddCommGroup 𝔥] [Module ℝ 𝔥] {A : 𝔥 →ₗ[ℝ] Module.End ℝ V}
  {n : ℕ} {b : Basis (Fin n × Fin 2) ℝ V} {α : Fin n → Module.Dual ℝ 𝔥}

omit [FiniteDimensional ℝ V] in
/-- A vector killed by every `A ξ` has no component in a plane of nonzero weight: if
`αₖ(ξ) ≠ 0`, then `qₖ` and `pₖ` are multiples of `A ξ pₖ` and `A ξ qₖ`, and `ω(A ξ u, w) = 0`. -/
private theorem repr_eq_zero_of_forall_apply_eq_zero (hb : ω.IsDarbouxBasis b)
    (hα : ∀ ξ k, A ξ (b (k, 0)) = -α k ξ • b (k, 1) ∧ A ξ (b (k, 1)) = α k ξ • b (k, 0))
    (hskew : ∀ ξ, A ξ ∈ skewAdjointLieSubalgebra ω.toBilinForm) {k : Fin n} (hk : α k ≠ 0)
    {w : V} (hw : ∀ ξ, A ξ w = 0) (a : Fin 2) : b.repr w (k, a) = 0 := by
  obtain ⟨ξ, hξ⟩ := DFunLike.ne_iff.1 hk
  rw [LinearMap.zero_apply] at hξ
  have hsk (u : V) : ω (A ξ u) w = 0 := by
    have h := skewAdjointLieSubalgebra.apply_left
      (⟨A ξ, hskew ξ⟩ : skewAdjointLieSubalgebra ω.toBilinForm) u w
    simpa [hw ξ] using h
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · simpa [(hα ξ k).1, hb.apply_snd, hξ] using hsk (b (k, 0))
  · simpa [(hα ξ k).2, hb.apply_fst, hξ] using hsk (b (k, 1))

/-- **Few nonzero weights.** If `A` vanishes on an isotropic subspace `W`, then the number of
planes of nonzero weight is at most `n - dim W`: `W` and the vectors `qₖ` of those planes span an
isotropic subspace in which `W` is a direct summand. -/
private theorem nat_card_add_finrank_le (hb : ω.IsDarbouxBasis b)
    (hα : ∀ ξ k, A ξ (b (k, 0)) = -α k ξ • b (k, 1) ∧ A ξ (b (k, 1)) = α k ξ • b (k, 0))
    (hskew : ∀ ξ, A ξ ∈ skewAdjointLieSubalgebra ω.toBilinForm)
    {W : Submodule ℝ V} (hW : ω.IsIsotropic W) (hAW : ∀ ξ, ∀ w ∈ W, A ξ w = 0) :
    Nat.card {k // α k ≠ 0} + finrank ℝ W ≤ n := by
  classical
  have hrepr {k : Fin n} (hk : α k ≠ 0) {w : V} (hw : w ∈ W) (a : Fin 2) : b.repr w (k, a) = 0 :=
    repr_eq_zero_of_forall_apply_eq_zero hb hα hskew hk (fun ξ ↦ hAW ξ w hw) a
  -- The span `P` of the vectors `qₖ` of the planes of nonzero weight.
  let T : Set (Fin n × Fin 2) := {p | α p.1 ≠ 0 ∧ p.2 = 0}
  set P : Submodule ℝ V := Submodule.span ℝ (b '' T) with hP
  have hPrange : b '' T = Set.range fun k : {k // α k ≠ 0} ↦ b (k.val, 0) := by
    ext v
    constructor
    · rintro ⟨⟨k, a⟩, ⟨hk, ha⟩, rfl⟩
      exact ⟨⟨k, hk⟩, by simp only at ha; rw [ha]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨(k.val, 0), ⟨k.property, rfl⟩, rfl⟩
  have hfinP : finrank ℝ P = Nat.card {k // α k ≠ 0} := by
    rw [hP, hPrange, Nat.card_eq_fintype_card]
    exact finrank_span_eq_card (b.linearIndependent.comp _ fun k l h ↦
      Subtype.ext (congrArg Prod.fst h))
  have hWP : W ⊓ P = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v ⟨hvW, hvP⟩ ↦ b.ext_elem fun p ↦ ?_
    rw [map_zero, Finsupp.zero_apply]
    by_cases hp : p ∈ T
    · exact hrepr hp.1 hvW p.2
    · exact Finsupp.notMem_support_iff.1 fun h ↦ hp (b.mem_span_image.1 hvP h)
  -- `W ⊔ P` is isotropic.
  have hPW : P ≤ ω.orthogonal W := Submodule.span_le.2 fun _ ⟨⟨k, a⟩, ⟨hk, ha⟩, hv⟩ ↦ by
    simp only at ha
    subst ha hv
    refine mem_orthogonal_iff.2 fun w hw ↦ ?_
    rw [← ω.neg_eq, hb.apply_fst, hrepr hk hw, neg_zero]
  have hPiso : ω.IsIsotropic P := isIsotropic_span_iff.2 fun _ ⟨⟨k, _⟩, ⟨_, hk⟩, hv⟩ _
      ⟨⟨l, _⟩, ⟨_, hl⟩, hv'⟩ ↦ by
    simp only at hk hl
    subst hk hl hv hv'
    exact hb.apply_fst_fst k l
  have hWPiso : ω.IsIsotropic (W ⊔ P) := by
    refine isIsotropic_iff.2 fun v hv v' hv' ↦ ?_
    obtain ⟨w, hw, p, hp, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨w', hw', p', hp', rfl⟩ := Submodule.mem_sup.1 hv'
    have h₁ := isIsotropic_iff.1 hW w hw w' hw'
    have h₂ := isIsotropic_iff.1 hPiso p hp p' hp'
    have h₃ := mem_orthogonal_iff.1 (hPW hp') w hw
    have h₄ := mem_orthogonal_iff.1 (hPW hp) w' hw'
    rw [← ω.neg_eq] at h₄
    simp only [map_add, LinearMap.add_apply, h₁, h₂, h₃, neg_eq_zero.1 h₄, add_zero]
  have h₁ := hWPiso.two_mul_finrank_le
  have h₂ := Submodule.finrank_sup_add_finrank_inf_eq W P
  rw [hWP, finrank_bot, hfinP] at h₂
  have h₃ : finrank ℝ V = n * 2 := by
    rw [finrank_eq_card_basis b, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  omega

end Weights

/-- **A torus of compact elements of `sp(V, ω)` fixing a large isotropic subspace has a
semidefinite member.** Let `A : 𝔥 → sp(V, ω)` be a linear map from a nonzero finite-dimensional
space, with pairwise commuting values that are complex linear for a complex
structure `J` compatible with `ω`. If every `A ξ` vanishes on an isotropic subspace `W` with
`dim V ≤ 2 (dim W + dim 𝔥)`, then there is `ξ ≠ 0` with `0 ≤ ω(A ξ v, v)` for every `v`. -/
theorem exists_ne_zero_forall_apply_apply_nonneg (hJ : ω.Compatible J)
    {𝔥 : Type*} [AddCommGroup 𝔥] [Module ℝ 𝔥] [FiniteDimensional ℝ 𝔥] [Nontrivial 𝔥]
    (A : 𝔥 →ₗ[ℝ] Module.End ℝ V) (hcomm : ∀ ξ η, Commute (A ξ) (A η))
    (hskew : ∀ ξ, A ξ ∈ skewAdjointLieSubalgebra ω.toBilinForm)
    (hAJ : ∀ ξ, IsComplexLinearMap J J (A ξ))
    {W : Submodule ℝ V} (hW : ω.IsIsotropic W) (hAW : ∀ ξ, ∀ w ∈ W, A ξ w = 0)
    (hdim : finrank ℝ V ≤ 2 * (finrank ℝ W + finrank ℝ 𝔥)) :
    ∃ ξ, ξ ≠ 0 ∧ ∀ v, 0 ≤ ω (A ξ v) v := by
  classical
  -- A nonzero element of the kernel of `A` will do.
  by_cases hA : Function.Injective A
  swap
  · rw [injective_iff_map_eq_zero] at hA
    push Not at hA
    obtain ⟨ξ, hAξ, hξ0⟩ := hA
    exact ⟨ξ, hξ0, fun v ↦ by simp [hAξ]⟩
  obtain ⟨n, b, α, hb, -, hα, hQ⟩ :=
    exists_isDarbouxBasis_forall_hamiltonianEndEquiv_symm_eq_sum_apply_smul_elliptic hJ A hcomm
      hskew hAJ
  have hcard := nat_card_add_finrank_le hb hα hskew hW hAW
  have h₃ : finrank ℝ V = n * 2 := by
    rw [finrank_eq_card_basis b, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rw [Nat.card_eq_fintype_card] at hcard
  -- The nonzero weights separate the points of `𝔥`, and there are at most `dim 𝔥` of them, so
  -- `ξ ↦ (αₖ(ξ))ₖ` is bijective onto the functions on the nonzero weights.
  let Φ : 𝔥 →ₗ[ℝ] {k // α k ≠ 0} → ℝ := LinearMap.pi fun k ↦ α k.val
  have hΦ : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun ξ hξ ↦ hA ?_
    have hαξ (k : Fin n) : α k ξ = 0 := by
      by_cases hk : α k = 0
      · rw [hk, LinearMap.zero_apply]
      · exact congrFun hξ ⟨k, hk⟩
    have h0 : ω.hamiltonianEndEquiv.symm ⟨A ξ, hskew ξ⟩ = 0 := by simp [hQ, hαξ]
    simpa using congrArg Subtype.val (ω.hamiltonianEndEquiv.symm.map_eq_zero_iff.1 h0)
  have hle := LinearMap.finrank_le_finrank_of_injective hΦ
  rw [Module.finrank_fintype_fun_eq_card] at hle
  obtain ⟨ξ, hξ⟩ := ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    rw [Module.finrank_fintype_fun_eq_card]; omega)).1 hΦ) 1
  have hξα (k : Fin n) : 0 ≤ α k ξ := by
    by_cases hk : α k = 0
    · rw [hk, LinearMap.zero_apply]
    · have h := congrFun hξ ⟨k, hk⟩
      simp only [Φ, LinearMap.pi_apply, Pi.one_apply] at h
      rw [h]
      exact zero_le_one
  refine ⟨ξ, fun h ↦ ?_, fun v ↦ ?_⟩
  -- `ξ ≠ 0`: there is a nonzero weight, since `dim 𝔥 > 0`, and `αₖ(ξ) = 1` for it.
  · obtain ⟨k⟩ := Fintype.card_pos_iff.1 (lt_of_lt_of_le Module.finrank_pos hle)
    have := congrFun hξ k
    rw [h, map_zero] at this
    exact zero_ne_one this
  · exact apply_apply_nonneg_of_hamiltonianEndEquiv_symm_eq_sum_smul_elliptic (hQ ξ) hξα v

end TauCeti.SymplecticForm

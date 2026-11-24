/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Stability
public import TauCeti.Analysis.CStarAlgebra.Lift
public import TauCeti.Analysis.CStarAlgebra.SequenceAlgebra.Basic

/-!
# Lifting elements from C⋆-sequence algebras and ultrapowers

Using `TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Stability` and
`TauCeti.Analysis.CStarAlgebra.Lift`, we lift structured elements from `lp A ∞ ⧸ lp.nullIdeal A l`
(and hence `CStarFilterQuotient A l`, `CStarSequenceAlgebra A`, and `CStarUltrapower A ω`) to
bounded coordinate families satisfying the same relation at every index: norm-preserving
self-adjoint lifts (`lp.exists_isSelfAdjoint_mk_nullIdeal_eq_and_norm_eq`), star projections
(`lp.exists_isStarProjection_mk_nullIdeal_eq`), isometries
(`lp.exists_star_mul_self_eq_one_and_mk_nullIdeal_eq`), and unitaries
(`lp.unitary_map_mkUnitalStarAlgHom_surjective`,
`TauCeti.CStarFilterQuotient.exists_unitary_family_mk_eq`), together with the non-unitary lift
`1 - invSuccSmul 1` of `1` (`TauCeti.CStarSequenceAlgebra.notMem_unitary_one_sub_invSuccSmul_one`).

## References

* M. Rørdam, *Classification of Nuclear, Simple C⋆-Algebras*, Chapter 6.
* B. Blackadar, *Operator Algebras*, II.8.1 and II.8.3.
-/

public section

open Filter Topology
open scoped ENNReal CStarAlgebra

noncomputable section

namespace lp

section NonUnital

variable {ι : Type*} {A : ι → Type*} [∀ i, NonUnitalCStarAlgebra (A i)]

/-- **Self-adjoint norm-attaining lifting.** Every self-adjoint element of
`lp A ∞ ⧸ lp.nullIdeal A l` lifts to a self-adjoint bounded family `a : lp A ∞` of the same norm. -/
theorem exists_isSelfAdjoint_mk_nullIdeal_eq_and_norm_eq (l : Filter ι)
    {x : lp A ∞ ⧸ lp.nullIdeal A l} (hx : IsSelfAdjoint x) :
    ∃ a : lp A ∞, IsSelfAdjoint a ∧ TwoSidedIdeal.Quotient.mk (lp.nullIdeal A l) a = x ∧
      ‖a‖ = ‖x‖ := by
  simpa only [TwoSidedIdeal.Quotient.mkStarAlgHom_apply] using
    NonUnitalStarAlgHom.exists_isSelfAdjoint_apply_eq_norm_eq
      (TwoSidedIdeal.Quotient.mkStarAlgHom (lp.nullIdeal A l))
      (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective (lp.nullIdeal A l) x) hx

/-- **Projection lifting.** Every star projection in `lp A ∞ ⧸ lp.nullIdeal A l` lifts to a star
projection in `lp A ∞`. -/
theorem exists_isStarProjection_mk_nullIdeal_eq (l : Filter ι)
    {p : lp A ∞ ⧸ lp.nullIdeal A l} (hp : IsStarProjection p) :
    ∃ q : lp A ∞, IsStarProjection q ∧ TwoSidedIdeal.Quotient.mk (lp.nullIdeal A l) q = p := by
  obtain ⟨b, hb_sa, hb_mk, -⟩ :=
    exists_isSelfAdjoint_mk_nullIdeal_eq_and_norm_eq l hp.isSelfAdjoint
  have hb_i : ∀ i, IsSelfAdjoint (b i) := lp.isSelfAdjoint_iff.mp hb_sa
  have hcoord (i : ι) : ∃ qᵢ : A i, IsStarProjection qᵢ ∧
      (‖b i * b i - b i‖ < 1 / 9 → ‖qᵢ - b i‖ ≤ 2 * ‖b i * b i - b i‖) := by
    by_cases hi : ‖b i * b i - b i‖ < 1 / 9
    · obtain ⟨qᵢ, h₁, h₂⟩ := (hb_i i).exists_isStarProjection_and_norm_sub_le hi
      exact ⟨qᵢ, h₁, fun _ ↦ h₂⟩
    · exact ⟨0, .zero _, fun h ↦ (hi h).elim⟩
  choose q₀ hq₀_proj hq₀_norm using hcoord
  let q : lp A ∞ := ⟨q₀, memℓp_infty ⟨1, by
    rintro _ ⟨i, rfl⟩; exact IsStarProjection.norm_le _ (hq₀_proj i)⟩⟩
  have hbb : TwoSidedIdeal.Quotient.mk (nullIdeal A l) (b * b) =
      TwoSidedIdeal.Quotient.mk (nullIdeal A l) b := by
    rw [map_mul, hb_mk, hp.isIdempotentElem.eq]
  have htend : Tendsto (fun i ↦ ‖b i * b i - b i‖) l (𝓝 0) := by
    simpa only [lp.infty_coeFn_mul, Pi.mul_apply] using mk_nullIdeal_eq_mk_iff.mp hbb
  refine ⟨q, lp.isStarProjection_iff.mpr hq₀_proj, ?_⟩
  rw [← hb_mk, mk_nullIdeal_eq_mk_iff]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by simpa using htend.const_mul 2)
  filter_upwards [htend.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / 9))] with i hi
  exact hq₀_norm i hi

end NonUnital

section Unital

variable {ι : Type*} {A : ι → Type*} [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]

/-- **Isometry lifting.** Every element `x : lp A ∞ ⧸ lp.nullIdeal A l` satisfying `star x * x = 1`
lifts to an element `v : lp A ∞` satisfying `star v * v = 1`. -/
theorem exists_star_mul_self_eq_one_and_mk_nullIdeal_eq (l : Filter ι)
    {x : lp A ∞ ⧸ lp.nullIdeal A l} (hx : star x * x = 1) :
    ∃ v : lp A ∞, star v * v = 1 ∧ TwoSidedIdeal.Quotient.mk (lp.nullIdeal A l) v = x := by
  obtain ⟨b, hb_mk⟩ := TwoSidedIdeal.Quotient.mk_surjective (lp.nullIdeal A l) x
  have hcoord (i : ι) : ∃ vᵢ : A i, star vᵢ * vᵢ = 1 ∧
      (‖star (b i) * b i - 1‖ < 1 / 2 → ‖vᵢ - b i‖ ≤ ‖b i‖ * ‖star (b i) * b i - 1‖) := by
    by_cases hi : ‖star (b i) * b i - 1‖ < 1 / 2
    · obtain ⟨vᵢ, h₁, h₂⟩ := TauCeti.exists_star_mul_self_eq_one_and_norm_sub_le hi
      exact ⟨vᵢ, h₁, fun _ ↦ h₂⟩
    · exact ⟨1, by simp, fun h ↦ (hi h).elim⟩
  choose v₀ hv₀_iso hv₀_norm using hcoord
  let v : lp A ∞ := ⟨v₀, memℓp_infty ⟨1, by
    rintro _ ⟨i, rfl⟩
    have hsq : ‖v₀ i‖ ^ 2 = 1 := by
      rw [sq, ← CStarRing.norm_star_mul_self, hv₀_iso i, norm_one]
    nlinarith [norm_nonneg (v₀ i)]⟩⟩
  have hv_iso : star v * v = 1 := by
    ext i
    simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.star_apply, lp.infty_coeFn_one,
      Pi.one_apply] using hv₀_iso i
  have hb1 : TwoSidedIdeal.Quotient.mk (nullIdeal A l) (star b * b) =
      TwoSidedIdeal.Quotient.mk (nullIdeal A l) 1 := by
    rw [map_mul, TwoSidedIdeal.Quotient.mk_star, TwoSidedIdeal.Quotient.mk_one, hb_mk, hx]
  have htend : Tendsto (fun i ↦ ‖star (b i) * b i - 1‖) l (𝓝 0) := by
    simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.star_apply, lp.infty_coeFn_one,
      Pi.one_apply] using mk_nullIdeal_eq_mk_iff.mp hb1
  refine ⟨v, hv_iso, ?_⟩
  rw [← hb_mk, mk_nullIdeal_eq_mk_iff]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by simpa using htend.const_mul ‖b‖)
  filter_upwards [htend.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / 2))] with i hi
  exact (hv₀_norm i hi).trans
    (mul_le_mul_of_nonneg_right (norm_apply_le_norm ENNReal.top_ne_zero b i) (norm_nonneg _))

/-- **Unitary lifting.** For any filter `l : Filter ι`, the quotient map from `lp A ∞` to
`lp A ∞ ⧸ lp.nullIdeal A l` is surjective on unitary groups. -/
theorem unitary_map_mkUnitalStarAlgHom_surjective (l : Filter ι) :
    Function.Surjective
      (Unitary.map (StarMonoidHom.ofClass
        (TwoSidedIdeal.Quotient.mkUnitalStarAlgHom (lp.nullIdeal A l)))) := by
  intro U
  obtain ⟨b, hb_mk⟩ := TwoSidedIdeal.Quotient.mk_surjective (lp.nullIdeal A l) (U : _)
  have hcoord (i : ι) : ∃ uᵢ : unitary (A i),
      ‖star (b i) * b i - 1‖ < 1 / 2 → ‖b i * star (b i) - 1‖ < 1 →
        ‖(uᵢ : A i) - b i‖ ≤ ‖b i‖ * ‖star (b i) * b i - 1‖ := by
    by_cases hi : ‖star (b i) * b i - 1‖ < 1 / 2 ∧ ‖b i * star (b i) - 1‖ < 1
    · obtain ⟨uᵢ, h⟩ := TauCeti.exists_unitary_and_norm_sub_le hi.left hi.right
      exact ⟨uᵢ, fun _ _ ↦ h⟩
    · exact ⟨1, fun h₁ h₂ ↦ (hi ⟨h₁, h₂⟩).elim⟩
  choose u₀ hu₀_norm using hcoord
  let V : unitary (lp A ∞) := unitaryEquiv.symm u₀
  have hb1 : TwoSidedIdeal.Quotient.mk (nullIdeal A l) (star b * b) =
      TwoSidedIdeal.Quotient.mk (nullIdeal A l) 1 := by
    rw [map_mul, TwoSidedIdeal.Quotient.mk_star, TwoSidedIdeal.Quotient.mk_one, hb_mk,
      (Unitary.mem_iff.mp U.property).left]
  have htend₁ : Tendsto (fun i ↦ ‖star (b i) * b i - 1‖) l (𝓝 0) := by
    simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.star_apply, lp.infty_coeFn_one,
      Pi.one_apply] using mk_nullIdeal_eq_mk_iff.mp hb1
  have hb2 : TwoSidedIdeal.Quotient.mk (nullIdeal A l) (b * star b) =
      TwoSidedIdeal.Quotient.mk (nullIdeal A l) 1 := by
    rw [map_mul, TwoSidedIdeal.Quotient.mk_star, TwoSidedIdeal.Quotient.mk_one, hb_mk,
      (Unitary.mem_iff.mp U.property).right]
  have htend₂ : Tendsto (fun i ↦ ‖b i * star (b i) - 1‖) l (𝓝 0) := by
    simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.star_apply, lp.infty_coeFn_one,
      Pi.one_apply] using mk_nullIdeal_eq_mk_iff.mp hb2
  refine ⟨V, Subtype.ext ?_⟩
  rw [Unitary.coe_map, StarMonoidHom.ofClass_coe, TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_apply,
    ← hb_mk, mk_nullIdeal_eq_mk_iff]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by simpa using htend₁.const_mul ‖b‖)
  filter_upwards [htend₁.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / 2)),
    htend₂.eventually (gt_mem_nhds zero_lt_one)] with i hi₁ hi₂
  rw [coe_unitaryEquiv_symm_apply]
  exact (hu₀_norm i hi₁ hi₂).trans
    (mul_le_mul_of_nonneg_right (norm_apply_le_norm ENNReal.top_ne_zero b i) (norm_nonneg _))

end Unital

end lp

namespace TauCeti

namespace CStarFilterQuotient

section NonUnital

variable {ι : Type*} {A : Type*} [NonUnitalCStarAlgebra A]

/-- Every self-adjoint element of `CStarFilterQuotient A l` lifts to a self-adjoint bounded family
of the same norm. -/
theorem exists_isSelfAdjoint_mk_eq_and_norm_eq (l : Filter ι)
    {x : CStarFilterQuotient A l} (hx : IsSelfAdjoint x) :
    ∃ a : lp (fun _ : ι ↦ A) ∞, IsSelfAdjoint a ∧ mk A l a = x ∧ ‖a‖ = ‖x‖ := by
  simpa only [mk_apply] using lp.exists_isSelfAdjoint_mk_nullIdeal_eq_and_norm_eq l hx

/-- Every star projection in `CStarFilterQuotient A l` lifts to a star projection in
`lp (fun _ : ι ↦ A) ∞`. -/
theorem exists_isStarProjection_mk_eq (l : Filter ι)
    {p : CStarFilterQuotient A l} (hp : IsStarProjection p) :
    ∃ q : lp (fun _ : ι ↦ A) ∞, IsStarProjection q ∧ mk A l q = p := by
  simpa only [mk_apply] using lp.exists_isStarProjection_mk_nullIdeal_eq l hp

end NonUnital

section Unital

variable {ι : Type*} {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- Every isometry `star x * x = 1` in `CStarFilterQuotient A l` lifts to an isometry in
`lp (fun _ : ι ↦ A) ∞`. -/
theorem exists_star_mul_self_eq_one_and_mk_eq (l : Filter ι)
    {x : CStarFilterQuotient A l} (hx : star x * x = 1) :
    ∃ v : lp (fun _ : ι ↦ A) ∞, star v * v = 1 ∧ mk A l v = x := by
  simpa only [mk_apply] using lp.exists_star_mul_self_eq_one_and_mk_nullIdeal_eq l hx

/-- The quotient map `unitalMk A l` is surjective on unitary groups. -/
theorem unitary_map_unitalMk_surjective (l : Filter ι) :
    Function.Surjective (Unitary.map (StarMonoidHom.ofClass (unitalMk A l))) := fun U ↦ by
  obtain ⟨V, hV⟩ := lp.unitary_map_mkUnitalStarAlgHom_surjective (A := fun _ : ι ↦ A) l U
  exact ⟨V, Subtype.ext <| by simpa [unitalMk_apply, mk_apply] using congrArg Subtype.val hV⟩

/-- Every unitary `U : unitary (CStarFilterQuotient A l)` lifts to a family `u : ι → unitary A` of
unitaries in `A`. -/
theorem exists_unitary_family_mk_eq (l : Filter ι) (U : unitary (CStarFilterQuotient A l)) :
    ∃ u : ι → unitary A, mk A l (lp.unitaryEquiv.symm u : lp (fun _ : ι ↦ A) ∞) = U := by
  obtain ⟨V, hV⟩ := unitary_map_unitalMk_surjective l U
  exact ⟨lp.unitaryEquiv V, by
    rw [MulEquiv.symm_apply_apply]; simpa [unitalMk_apply] using congrArg Subtype.val hV⟩

end Unital

end CStarFilterQuotient

namespace CStarSequenceAlgebra

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- In `CStarSequenceAlgebra A`, the sequence `n ↦ 1 - (n + 1)⁻¹ • 1` represents `1` (hence a
unitary), even though it vanishes at `n = 0`. -/
theorem mk_one_sub_invSuccSmul_one :
    CStarFilterQuotient.mk A atTop (1 - invSuccSmul (1 : A)) = 1 := by
  rw [map_sub, CStarFilterQuotient.mk_one, mk_invSuccSmul_eq_zero le_rfl, sub_zero]

/-- The bounded representative `1 - invSuccSmul (1 : A)` of `(1 : CStarSequenceAlgebra A)` is not
itself unitary in `lp (fun _ : ℕ ↦ A) ∞`, because its `0`-th coordinate is `0`. -/
theorem notMem_unitary_one_sub_invSuccSmul_one :
    1 - invSuccSmul (1 : A) ∉ unitary (lp (fun _ : ℕ ↦ A) ∞) := by
  intro h
  have h0 : ((star (1 - invSuccSmul (1 : A)) * (1 - invSuccSmul (1 : A))) :
      lp (fun _ : ℕ ↦ A) ∞) 0 = 1 := by
    rw [(Unitary.mem_iff.mp h).left, lp.infty_coeFn_one, Pi.one_apply]
  have hz : (1 - invSuccSmul (1 : A)) 0 = (0 : A) := by
    rw [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_one, Pi.one_apply, invSuccSmul_apply]; simp
  rw [lp.infty_coeFn_mul, Pi.mul_apply, hz, mul_zero] at h0
  exact zero_ne_one h0

end CStarSequenceAlgebra

end TauCeti

end

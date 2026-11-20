/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Stability
public import TauCeti.Analysis.CStarAlgebra.SequenceAlgebra.Basic

/-!
# Lifting elements from C⋆-sequence algebras and ultrapowers

Using the quantitative continuous-functional-calculus perturbation bounds from
`TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Stability`, we lift structured elements
from filter quotients `lp A ∞ ⧸ lp.nullIdeal A l` (and in particular from `CStarFilterQuotient A l`,
`CStarSequenceAlgebra A`, and `CStarUltrapower A ω`) to bounded coordinate families satisfying the
same relation at every index:

* `lp.exists_isSelfAdjoint_mk_nullIdeal_eq_and_norm_eq`: self-adjoint elements lift to self-adjoint
  bounded families of the same norm;
* `lp.exists_isStarProjection_mk_nullIdeal_eq`: star projections lift to star projections;
* `lp.exists_star_mul_self_eq_one_and_mk_nullIdeal_eq`: isometries (`star x * x = 1`) lift to
  isometries;
* `lp.unitary_map_mkUnitalStarAlgHom_surjective` and
  `TauCeti.CStarFilterQuotient.exists_unitary_family_mk_eq`: unitaries lift to unitaries (hence to
  coordinate families `u : ι → unitary A`).

Finally, `TauCeti.CStarSequenceAlgebra.notMem_unitary_one_sub_invSuccSmul_one` exhibits the sequence
`n ↦ (1 - (n + 1)⁻¹) • 1`, whose class in `CStarSequenceAlgebra A` is `1` (hence unitary) even
though the sequence vanishes at `n = 0` and is therefore not unitary in `ℓ^∞(ℕ, A)`.

## References

* M. Rørdam, *Classification of Nuclear, Simple C⋆-Algebras*, Chapter 6.
* B. Blackadar, *Operator Algebras*, II.8.1 and II.8.3.
-/

public section

open Filter Topology
open scoped ENNReal CStarAlgebra

noncomputable section

section Helpers

private def liftProjCoord {B : Type*} [NonUnitalCStarAlgebra B] (x : B) (hx : IsSelfAdjoint x) :
    B := by
  classical
  exact if h : ‖x * x - x‖ < 1 / 9 then
    Classical.choose (hx.exists_isStarProjection_and_norm_sub_le h)
  else 0

private theorem isStarProjection_liftProjCoord {B : Type*} [NonUnitalCStarAlgebra B] (x : B)
    (hx : IsSelfAdjoint x) : IsStarProjection (liftProjCoord x hx) := by
  classical
  unfold liftProjCoord
  split_ifs with h
  · exact (Classical.choose_spec (hx.exists_isStarProjection_and_norm_sub_le h)).1
  · exact .zero B

private theorem norm_liftProjCoord_sub_le {B : Type*} [NonUnitalCStarAlgebra B] {x : B}
    (hx : IsSelfAdjoint x) (h : ‖x * x - x‖ < 1 / 9) :
    ‖liftProjCoord x hx - x‖ ≤ 2 * ‖x * x - x‖ := by
  classical
  simp only [liftProjCoord, h, ↓reduceDIte]
  exact (Classical.choose_spec (hx.exists_isStarProjection_and_norm_sub_le h)).2

private def liftIsometryCoord {B : Type*} [CStarAlgebra B] (x : B) : B := by
  classical
  exact if h : ‖star x * x - 1‖ < 1 / 2 then
    Classical.choose (TauCeti.exists_star_mul_self_eq_one_and_norm_sub_le h)
  else 1

private theorem star_liftIsometryCoord_mul_self {B : Type*} [CStarAlgebra B] (x : B) :
    star (liftIsometryCoord x) * liftIsometryCoord x = 1 := by
  classical
  unfold liftIsometryCoord
  split_ifs with h
  · exact (Classical.choose_spec (TauCeti.exists_star_mul_self_eq_one_and_norm_sub_le h)).1
  · simp

private theorem norm_liftIsometryCoord_le {B : Type*} [CStarAlgebra B] [Nontrivial B] (x : B) :
    ‖liftIsometryCoord x‖ ≤ 1 := by
  have hsq : ‖liftIsometryCoord x‖ ^ 2 = 1 := by
    rw [sq, ← CStarRing.norm_star_mul_self, star_liftIsometryCoord_mul_self, norm_one]
  nlinarith [norm_nonneg (liftIsometryCoord x)]

private theorem norm_liftIsometryCoord_sub_le {B : Type*} [CStarAlgebra B] {x : B}
    (h : ‖star x * x - 1‖ < 1 / 2) :
    ‖liftIsometryCoord x - x‖ ≤ ‖x‖ * ‖star x * x - 1‖ := by
  classical
  simp only [liftIsometryCoord, h, ↓reduceDIte]
  exact (Classical.choose_spec (TauCeti.exists_star_mul_self_eq_one_and_norm_sub_le h)).2

private def liftUnitaryCoord {B : Type*} [CStarAlgebra B] (x : B) : unitary B := by
  classical
  exact if h : ‖star x * x - 1‖ < 1 / 2 ∧ ‖x * star x - 1‖ < 1 then
    Classical.choose (TauCeti.exists_unitary_and_norm_sub_le h.1 h.2)
  else 1

private theorem norm_liftUnitaryCoord_sub_le {B : Type*} [CStarAlgebra B] {x : B}
    (h₁ : ‖star x * x - 1‖ < 1 / 2) (h₂ : ‖x * star x - 1‖ < 1) :
    ‖(liftUnitaryCoord x : B) - x‖ ≤ ‖x‖ * ‖star x * x - 1‖ := by
  classical
  simp only [liftUnitaryCoord, h₁, h₂, and_self, ↓reduceDIte]
  exact Classical.choose_spec (TauCeti.exists_unitary_and_norm_sub_le h₁ h₂)

end Helpers

namespace lp

section NonUnital

variable {ι : Type*} {A : ι → Type*} [∀ i, NonUnitalCStarAlgebra (A i)]

/-- **Self-adjoint norm-attaining lifting.** Every self-adjoint element of
`lp A ∞ ⧸ lp.nullIdeal A l` lifts to a self-adjoint bounded family `a : lp A ∞` of the same norm. -/
theorem exists_isSelfAdjoint_mk_nullIdeal_eq_and_norm_eq (l : Filter ι)
    {x : lp A ∞ ⧸ lp.nullIdeal A l} (hx : IsSelfAdjoint x) :
    ∃ a : lp A ∞, IsSelfAdjoint a ∧ TwoSidedIdeal.Quotient.mk (lp.nullIdeal A l) a = x ∧
      ‖a‖ = ‖x‖ := by
  obtain ⟨b, rfl, hb⟩ := exists_mk_nullIdeal_eq_and_norm_eq l x
  have ha_mk : TwoSidedIdeal.Quotient.mk (lp.nullIdeal A l) (realPart b : lp A ∞) =
      TwoSidedIdeal.Quotient.mk (lp.nullIdeal A l) b := by
    rw [← TwoSidedIdeal.Quotient.mkStarAlgHom_apply, map_realPart,
      TwoSidedIdeal.Quotient.mkStarAlgHom_apply, hx.coe_realPart]
  refine ⟨(realPart b : lp A ∞), (realPart b).2, ha_mk, le_antisymm ?_ ?_⟩
  · rw [AddSubgroup.norm_coe]
    exact (realPart.norm_le b).trans_eq hb
  · rw [← ha_mk]
    exact TwoSidedIdeal.Quotient.norm_mk_le _ _

/-- **Projection lifting.** Every star projection in `lp A ∞ ⧸ lp.nullIdeal A l` lifts to a star
projection in `lp A ∞`. -/
theorem exists_isStarProjection_mk_nullIdeal_eq (l : Filter ι)
    {p : lp A ∞ ⧸ lp.nullIdeal A l} (hp : IsStarProjection p) :
    ∃ q : lp A ∞, IsStarProjection q ∧ TwoSidedIdeal.Quotient.mk (lp.nullIdeal A l) q = p := by
  obtain ⟨b, hb_sa, hb_mk, -⟩ :=
    exists_isSelfAdjoint_mk_nullIdeal_eq_and_norm_eq l hp.isSelfAdjoint
  have hb_i : ∀ i, IsSelfAdjoint (b i) := isSelfAdjoint_iff.1 hb_sa
  let q : lp A ∞ :=
    ⟨fun i ↦ liftProjCoord (b i) (hb_i i), memℓp_infty ⟨1, by
      rintro _ ⟨i, rfl⟩
      exact IsStarProjection.norm_le _ (isStarProjection_liftProjCoord (b i) (hb_i i))⟩⟩
  have hq_proj : IsStarProjection q :=
    isStarProjection_iff.2 fun i ↦ isStarProjection_liftProjCoord (b i) (hb_i i)
  have htend : Tendsto (fun i ↦ ‖b i * b i - b i‖) l (𝓝 0) := by
    have hbb : TwoSidedIdeal.Quotient.mk (nullIdeal A l) (b * b) =
        TwoSidedIdeal.Quotient.mk (nullIdeal A l) b := by
      rw [map_mul, hb_mk, hp.isIdempotentElem.eq]
    simpa only [lp.infty_coeFn_mul, Pi.mul_apply] using mk_nullIdeal_eq_mk_iff.1 hbb
  refine ⟨q, hq_proj, ?_⟩
  rw [← hb_mk, mk_nullIdeal_eq_mk_iff]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by simpa using htend.const_mul 2)
  filter_upwards [htend.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / 9))] with i hi
  exact norm_liftProjCoord_sub_le (hb_i i) hi

end NonUnital

section Unital

variable {ι : Type*} {A : ι → Type*} [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]

/-- **Isometry lifting.** Every element `x : lp A ∞ ⧸ lp.nullIdeal A l` satisfying `star x * x = 1`
lifts to an element `v : lp A ∞` satisfying `star v * v = 1`. -/
theorem exists_star_mul_self_eq_one_and_mk_nullIdeal_eq (l : Filter ι)
    {x : lp A ∞ ⧸ lp.nullIdeal A l} (hx : star x * x = 1) :
    ∃ v : lp A ∞, star v * v = 1 ∧ TwoSidedIdeal.Quotient.mk (lp.nullIdeal A l) v = x := by
  obtain ⟨b, hb_mk⟩ := TwoSidedIdeal.Quotient.mk_surjective (lp.nullIdeal A l) x
  let v : lp A ∞ :=
    ⟨fun i ↦ liftIsometryCoord (b i), memℓp_infty ⟨1, by
      rintro _ ⟨i, rfl⟩
      exact norm_liftIsometryCoord_le (b i)⟩⟩
  have hv_iso : star v * v = 1 := by
    ext i
    simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.star_apply, lp.infty_coeFn_one,
      Pi.one_apply] using star_liftIsometryCoord_mul_self (b i)
  have htend : Tendsto (fun i ↦ ‖star (b i) * b i - 1‖) l (𝓝 0) := by
    have hb1 : TwoSidedIdeal.Quotient.mk (nullIdeal A l) (star b * b) =
        TwoSidedIdeal.Quotient.mk (nullIdeal A l) 1 := by
      rw [map_mul, TwoSidedIdeal.Quotient.mk_star, TwoSidedIdeal.Quotient.mk_one, hb_mk, hx]
    simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.star_apply, lp.infty_coeFn_one,
      Pi.one_apply] using mk_nullIdeal_eq_mk_iff.1 hb1
  refine ⟨v, hv_iso, ?_⟩
  rw [← hb_mk, mk_nullIdeal_eq_mk_iff]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by simpa using htend.const_mul ‖b‖)
  filter_upwards [htend.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / 2))] with i hi
  exact (norm_liftIsometryCoord_sub_le hi).trans
    (mul_le_mul_of_nonneg_right (norm_apply_le_norm ENNReal.top_ne_zero b i) (norm_nonneg _))

/-- **Unitary lifting.** For any filter `l : Filter ι`, the quotient map from `lp A ∞` to
`lp A ∞ ⧸ lp.nullIdeal A l` is surjective on unitary groups. -/
theorem unitary_map_mkUnitalStarAlgHom_surjective (l : Filter ι) :
    Function.Surjective
      (Unitary.map (StarMonoidHom.ofClass
        (TwoSidedIdeal.Quotient.mkUnitalStarAlgHom (lp.nullIdeal A l)))) := by
  intro U
  obtain ⟨b, hb_mk⟩ := TwoSidedIdeal.Quotient.mk_surjective (lp.nullIdeal A l) (U : _)
  let V : unitary (lp A ∞) := unitaryEquiv.symm fun i ↦ liftUnitaryCoord (b i)
  have htend₁ : Tendsto (fun i ↦ ‖star (b i) * b i - 1‖) l (𝓝 0) := by
    have hb1 : TwoSidedIdeal.Quotient.mk (nullIdeal A l) (star b * b) =
        TwoSidedIdeal.Quotient.mk (nullIdeal A l) 1 := by
      rw [map_mul, TwoSidedIdeal.Quotient.mk_star, TwoSidedIdeal.Quotient.mk_one, hb_mk,
        (Unitary.mem_iff.1 U.2).1]
    simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.star_apply, lp.infty_coeFn_one,
      Pi.one_apply] using mk_nullIdeal_eq_mk_iff.1 hb1
  have htend₂ : Tendsto (fun i ↦ ‖b i * star (b i) - 1‖) l (𝓝 0) := by
    have hb2 : TwoSidedIdeal.Quotient.mk (nullIdeal A l) (b * star b) =
        TwoSidedIdeal.Quotient.mk (nullIdeal A l) 1 := by
      rw [map_mul, TwoSidedIdeal.Quotient.mk_star, TwoSidedIdeal.Quotient.mk_one, hb_mk,
        (Unitary.mem_iff.1 U.2).2]
    simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.star_apply, lp.infty_coeFn_one,
      Pi.one_apply] using mk_nullIdeal_eq_mk_iff.1 hb2
  refine ⟨V, Subtype.ext ?_⟩
  rw [Unitary.coe_map, StarMonoidHom.ofClass_coe, TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_apply,
    ← hb_mk, mk_nullIdeal_eq_mk_iff]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by simpa using htend₁.const_mul ‖b‖)
  filter_upwards [htend₁.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / 2)),
    htend₂.eventually (gt_mem_nhds zero_lt_one)] with i hi₁ hi₂
  rw [coe_unitaryEquiv_symm_apply]
  exact (norm_liftUnitaryCoord_sub_le hi₁ hi₂).trans
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
    Function.Surjective (Unitary.map (StarMonoidHom.ofClass (unitalMk A l))) := by
  intro U
  obtain ⟨V, hV⟩ := lp.unitary_map_mkUnitalStarAlgHom_surjective (A := fun _ : ι ↦ A) l U
  refine ⟨V, Subtype.ext ?_⟩
  simpa [unitalMk_apply, mk_apply] using congrArg Subtype.val hV

/-- Every unitary `U : unitary (CStarFilterQuotient A l)` lifts to a family `u : ι → unitary A` of
unitaries in `A`. -/
theorem exists_unitary_family_mk_eq (l : Filter ι) (U : unitary (CStarFilterQuotient A l)) :
    ∃ u : ι → unitary A, mk A l (lp.unitaryEquiv.symm u : lp (fun _ : ι ↦ A) ∞) = U := by
  obtain ⟨V, hV⟩ := unitary_map_unitalMk_surjective l U
  refine ⟨lp.unitaryEquiv V, ?_⟩
  rw [MulEquiv.symm_apply_apply]
  simpa [unitalMk_apply] using congrArg Subtype.val hV

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
    rw [(Unitary.mem_iff.1 h).1, lp.infty_coeFn_one, Pi.one_apply]
  have hz : (1 - invSuccSmul (1 : A)) 0 = (0 : A) := by
    rw [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_one, Pi.one_apply, invSuccSmul_apply]
    simp
  rw [lp.infty_coeFn_mul, Pi.mul_apply, hz, mul_zero] at h0
  exact zero_ne_one h0

end CStarSequenceAlgebra

end TauCeti

end

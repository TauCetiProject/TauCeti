/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Specht.Complex
-- Non-public: the retract is built from the ideal presentation of the Specht module and from
-- base-change and transport identities; the statement only mentions the complex Specht module,
-- the regular representation and the Young symmetrizer.
import TauCeti.RepresentationTheory.BaseChange
import TauCeti.RepresentationTheory.OfMulAction
import TauCeti.RepresentationTheory.Symmetric.Specht.Comparison
import TauCeti.RepresentationTheory.Symmetric.Specht.Ideal.Idempotent

/-!
# The complex Specht module as a retract of the regular representation

The complex Specht module `S^μ` of a partition `μ` of `n` is a direct summand of the regular
representation `ℂ[Sₙ]`: there are intertwining maps `i : S^μ → ℂ[Sₙ]` and `p : ℂ[Sₙ] → S^μ` with
`p ∘ i = id`. They can be chosen so that the antipode `σ ↦ σ⁻¹` of the idempotent `i (p 1)` of
`ℂ[Sₙ]` is a nonzero multiple of the Young symmetrizer `c_μ` itself
(`TauCeti.exists_retract_spechtModuleℂ`).

The retract is first built over `ℚ` for a tableau `t`, from the ideal presentation
`φ : ℚ[Sₙ] c_t ≅ S^μ` (`TauCeti.YoungTableau.spechtIdealEquivSpechtSubrepresentation`). The
embedding is `w ↦ φ⁻¹(w) a_t` and the projection is `x ↦ φ(κ⁻² x b_t c_t)`, where `c_t² = κ c_t`
(`TauCeti.YoungTableau.youngSymmetrizer_sq`). The idempotent is `κ⁻² b_t c_t a_t`, and since the
antipode fixes `a_t` and `b_t` and reverses products, its antipode is `κ⁻² (a_t b_t)² = κ⁻¹ c_t`.
The embedding is twisted by `a_t` so as to produce `c_t`, not the reversed symmetrizer `b_t a_t`.
The labels are then identified with `Fin n` and the coefficients extended from `ℚ` to `ℂ`.

## Main results

* `TauCeti.exists_retract_spechtModuleℂ`: the complex Specht module is a retract of the regular
  representation, with an idempotent whose antipode is a nonzero multiple of `c_μ`.
-/

public section

open Representation
open scoped TensorProduct

namespace TauCeti

namespace YoungTableau

variable {μ : YoungDiagram} (t : YoungTableau μ)

/-- The scalar `κ = n! / dim ℚ[Sₙ] c_t` of essential idempotence, `c_t * c_t = κ • c_t`. -/
private noncomputable def κ : ℚ :=
  (μ.card.factorial : ℚ) / (Module.finrank ℚ (spechtIdeal t) : ℚ)

private theorem κ_ne_zero : κ t ≠ 0 := by
  have := finrank_spechtIdeal_pos t
  have : (0 : ℚ) < Module.finrank ℚ (spechtIdeal t) := by exact_mod_cast this
  exact div_ne_zero (by exact_mod_cast μ.card.factorial_ne_zero) this.ne'

/-- The embedding `S^μ → ℚ[Sₙ]`, `w ↦ φ⁻¹(w) a_t`, of the Specht module into the regular
representation, through its ideal presentation `φ : ℚ[Sₙ] c_t ≅ S^μ`. -/
private noncomputable def spechtToRegular :
    (spechtSubrepresentation (R := ℚ) μ).toRepresentation.IntertwiningMap
      (leftRegular ℚ (Equiv.Perm (Fin μ.card))) where
  toLinearMap := LinearMap.mulRight ℚ (rowSymmetrizer (R := ℚ) t) ∘ₗ
    ((spechtIdeal t).subtype.restrictScalars ℚ ∘ₗ
    (spechtIdealEquivSpechtSubrepresentation t).symm.toLinearMap)
  isIntertwining' g := by
    refine LinearMap.ext fun w => ?_
    have := LinearMap.congr_fun
      ((spechtIdealEquivSpechtSubrepresentation t).symm.toIntertwiningMap.isIntertwining' g) w
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
      Submodule.coe_subtype, LinearMap.coe_restrictScalars, leftRegular_apply_eq_single_mul]
    rw [this, TauCeti.Representation.ofModule'_apply, Submodule.coe_smul, smul_eq_mul, mul_assoc]

private theorem mul_mem_spechtIdeal (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) :
    (κ t)⁻¹ ^ 2 • (x * (columnAntisymmetrizer t * youngSymmetrizer t)) ∈ spechtIdeal t :=
  (mem_spechtIdeal_iff t _).mpr
    ⟨(κ t)⁻¹ ^ 2 • (x * columnAntisymmetrizer t), by rw [smul_mul_assoc, mul_assoc]⟩

/-- The projection `ℚ[Sₙ] → S^μ`, `x ↦ φ(κ⁻² x b_t c_t)`, a left inverse of
`spechtToRegular`. -/
private noncomputable def regularToSpecht :
    (leftRegular ℚ (Equiv.Perm (Fin μ.card))).IntertwiningMap
      (spechtSubrepresentation (R := ℚ) μ).toRepresentation where
  toLinearMap := (spechtIdealEquivSpechtSubrepresentation t).toLinearMap ∘ₗ
    { toFun x := ⟨_, mul_mem_spechtIdeal t x⟩
      map_add' x y := Subtype.ext (by simp [add_mul])
      map_smul' r x := Subtype.ext (by simp [smul_comm r]) }
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    have := LinearMap.congr_fun
      ((spechtIdealEquivSpechtSubrepresentation t).toIntertwiningMap.isIntertwining' g)
      ⟨_, mul_mem_spechtIdeal t x⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk] at this ⊢
    rw [← this]
    congr 1
    apply Subtype.ext
    simp [leftRegular_apply_eq_single_mul, mul_assoc]

private theorem regularToSpecht_comp_spechtToRegular :
    (regularToSpecht t).comp (spechtToRegular t) = .id _ := by
  refine IntertwiningMap.ext (LinearMap.ext fun w => ?_)
  set y : spechtIdeal t := (spechtIdealEquivSpechtSubrepresentation t).symm w
  have key : (κ t)⁻¹ ^ 2 • ((y : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) * rowSymmetrizer t *
      (columnAntisymmetrizer t * youngSymmetrizer t)) =
        (y : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) := by
    rw [mul_assoc, ← mul_assoc (rowSymmetrizer t), ← youngSymmetrizer_def, ← mul_assoc]
    -- `c_t` acts on `y ∈ ℚ[Sₙ] c_t` as the scalar `κ`, twice
    simp only [mul_youngSymmetrizer_of_mem_spechtIdeal y.2, smul_mul_assoc, smul_smul, ← κ.eq_1]
    have := κ_ne_zero t
    rw [show (κ t)⁻¹ ^ 2 * (κ t * κ t) = 1 by field_simp, one_smul]
  rw [IntertwiningMap.toLinearMap_apply, IntertwiningMap.toLinearMap_apply,
    IntertwiningMap.comp_apply, IntertwiningMap.id_apply]
  simp only [regularToSpecht, spechtToRegular, IntertwiningMap.coe_mk, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mulRight_apply]
  exact (congrArg (fun z => (spechtIdealEquivSpechtSubrepresentation t).toIntertwiningMap z)
    (Subtype.ext key : _ = y)).trans
      ((spechtIdealEquivSpechtSubrepresentation t).apply_symm_apply w)

/-- The idempotent `e = i (p 1)` of the retract is `κ⁻² b_t c_t a_t`, whose antipode is
`κ⁻² a_t b_t a_t b_t = κ⁻¹ c_t`. -/
private theorem antipode_spechtToRegular_regularToSpecht :
    HopfAlgebra.antipode ℚ (spechtToRegular t (regularToSpecht t (MonoidAlgebra.single 1 1))) =
      (κ t)⁻¹ • youngSymmetrizer t := by
  have he : spechtToRegular t (regularToSpecht t (MonoidAlgebra.single 1 1)) =
      (κ t)⁻¹ ^ 2 • (columnAntisymmetrizer t * youngSymmetrizer t * rowSymmetrizer t) := by
    simp [regularToSpecht, spechtToRegular, ← MonoidAlgebra.one_def]
  -- the antipode fixes `a_t` and `b_t`, so it sends `b_t (a_t b_t) a_t` to `(a_t b_t)²`
  have hsq : rowSymmetrizer (R := ℚ) t * (columnAntisymmetrizer t * rowSymmetrizer t *
      columnAntisymmetrizer t) = youngSymmetrizer t * youngSymmetrizer t := by
    simp only [youngSymmetrizer_def, mul_assoc]
  rw [he, map_smul, HopfAlgebra.antipode_mul_antidistrib, HopfAlgebra.antipode_mul_antidistrib,
    antipode_rowSymmetrizer, antipode_youngSymmetrizer, antipode_columnAntisymmetrizer, hsq,
    youngSymmetrizer_sq, ← κ.eq_1, smul_smul]
  have := κ_ne_zero t
  congr 1
  field_simp

end YoungTableau

section Retract

open YoungTableau

variable {n : ℕ} (μ : n.Partition)

/-- The row-superstandard tableau of the diagram of `μ`, from which the Young symmetrizer
`μ.youngSymmetrizer` is defined. -/
private noncomputable abbrev tab : YoungTableau (YoungDiagram.ofPartition μ) :=
  (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition μ)).toTableau

/-- The identification of `Sₙ` with the symmetric group on the labels of the diagram of `μ`. -/
private noncomputable abbrev relabel :
    Equiv.Perm (Fin n) ≃* Equiv.Perm (Fin (YoungDiagram.ofPartition μ).card) :=
  (finCongr (YoungDiagram.card_ofPartition μ).symm).permCongrHom

/-- The embedding of `S^μ` into `ℚ[Sₙ]`, with the labels identified with `Fin n`. -/
private noncomputable def iQ : Representation.IntertwiningMap (spechtModule (R := ℚ) μ).ρ
    (leftRegular ℚ (Equiv.Perm (Fin n))) where
  toLinearMap := (MonoidAlgebra.domCongr ℚ ℚ (relabel μ).symm).toLinearMap ∘ₗ
    (spechtToRegular (tab μ)).toLinearMap
  isIntertwining' g := by
    refine LinearMap.ext fun w => ?_
    have := (spechtToRegular (tab μ)).isIntertwining _ _ (relabel μ g) w
    simp only [LinearMap.coe_comp, Function.comp_apply, IntertwiningMap.toLinearMap_apply,
      FDRep.of_ρ', MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom] at this ⊢
    rw [this, leftRegular_apply_eq_single_mul, leftRegular_apply_eq_single_mul]
    simp only [AlgEquiv.toLinearMap_apply, map_mul, MonoidAlgebra.domCongr_single,
      MulEquiv.symm_apply_apply]

/-- The projection of `ℚ[Sₙ]` onto `S^μ`, with the labels identified with `Fin n`. -/
private noncomputable def pQ : Representation.IntertwiningMap
    (leftRegular ℚ (Equiv.Perm (Fin n))) (spechtModule (R := ℚ) μ).ρ where
  toLinearMap := (regularToSpecht (tab μ)).toLinearMap ∘ₗ
    (MonoidAlgebra.domCongr ℚ ℚ (relabel μ)).toLinearMap
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    have := (regularToSpecht (tab μ)).isIntertwining _ _ (relabel μ g)
      (MonoidAlgebra.domCongr ℚ ℚ (relabel μ) x)
    simp only [LinearMap.coe_comp, Function.comp_apply, IntertwiningMap.toLinearMap_apply,
      AlgEquiv.toLinearMap_apply, FDRep.of_ρ', MonoidHom.coe_comp,
      MulEquiv.coe_toMonoidHom] at this ⊢
    rw [← this, leftRegular_apply_eq_single_mul, leftRegular_apply_eq_single_mul, map_mul,
      MonoidAlgebra.domCongr_single]

private theorem pQ_comp_iQ : (pQ μ).comp (iQ μ) = .id _ := by
  refine IntertwiningMap.ext (LinearMap.ext fun w => ?_)
  rw [IntertwiningMap.toLinearMap_apply, IntertwiningMap.toLinearMap_apply,
    IntertwiningMap.comp_apply, IntertwiningMap.id_apply]
  simp only [pQ, iQ, IntertwiningMap.coe_mk, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, IntertwiningMap.toLinearMap_apply]
  rw [← MonoidAlgebra.domCongr_symm, AlgEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (regularToSpecht_comp_spechtToRegular (tab μ)) w

/-- The embedding of `ℂ ⊗_ℚ S^μ` into `ℂ[Sₙ]`. -/
private noncomputable def iC : Representation.IntertwiningMap
    (Representation.baseChange ℂ (spechtModule (R := ℚ) μ).ρ)
    (leftRegular ℂ (Equiv.Perm (Fin n))) :=
  (baseChangeOfMulActionEquiv ℚ ℂ (Equiv.Perm (Fin n))
    (Equiv.Perm (Fin n))).toIntertwiningMap.comp ((iQ μ).baseChange ℂ)

/-- The projection of `ℂ[Sₙ]` onto `ℂ ⊗_ℚ S^μ`, a left inverse of `iC`. -/
private noncomputable def pC : Representation.IntertwiningMap
    (leftRegular ℂ (Equiv.Perm (Fin n)))
    (Representation.baseChange ℂ (spechtModule (R := ℚ) μ).ρ) :=
  ((pQ μ).baseChange ℂ).comp (baseChangeOfMulActionEquiv ℚ ℂ (Equiv.Perm (Fin n))
    (Equiv.Perm (Fin n))).symm.toIntertwiningMap

private theorem pC_comp_iC : (pC μ).comp (iC μ) = .id _ := by
  have hpi (w : _) : pQ μ (iQ μ w) = w := DFunLike.congr_fun (pQ_comp_iQ μ) w
  refine IntertwiningMap.ext (LinearMap.ext fun w => ?_)
  rw [IntertwiningMap.toLinearMap_apply, IntertwiningMap.toLinearMap_apply,
    IntertwiningMap.comp_apply, IntertwiningMap.id_apply]
  induction w using TensorProduct.inductionOn with
  | tmul z w =>
    simp only [pC, iC, IntertwiningMap.comp_apply, Representation.Equiv.coe_toIntertwiningMap,
      Representation.Equiv.symm_apply_apply, IntertwiningMap.baseChange_tmul, hpi]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The antipode of the idempotent `iC (pC 1)` is `κ⁻¹ c_μ`. -/
private theorem antipode_iC_pC :
    HopfAlgebra.antipode ℂ (iC μ (pC μ (MonoidAlgebra.single 1 1))) =
      algebraMap ℚ ℂ (κ (tab μ))⁻¹ • μ.youngSymmetrizer ℂ := by
  have h1 : iC μ (pC μ (MonoidAlgebra.single 1 1)) =
      baseChangeOfMulActionEquiv ℚ ℂ (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n))
        (1 ⊗ₜ iQ μ (pQ μ (MonoidAlgebra.single 1 1))) := by
    simp only [iC, pC, IntertwiningMap.comp_apply, Representation.Equiv.coe_toIntertwiningMap,
      baseChangeOfMulActionEquiv_symm_single, IntertwiningMap.baseChange_tmul]
  have h2 : iQ μ (pQ μ (MonoidAlgebra.single 1 1)) = MonoidAlgebra.domCongr ℚ ℚ (relabel μ).symm
      (spechtToRegular (tab μ) (regularToSpecht (tab μ) (MonoidAlgebra.single 1 1))) := by
    simp only [iQ, pQ, IntertwiningMap.coe_mk, LinearMap.coe_comp, Function.comp_apply,
      AlgEquiv.toLinearMap_apply, IntertwiningMap.toLinearMap_apply, MonoidAlgebra.domCongr_single,
      map_one]
  rw [h1, h2, baseChangeOfMulActionEquiv_one_tmul, MonoidAlgebra.antipode_mapAlgHom,
    MonoidAlgebra.antipode_domCongr, antipode_spechtToRegular_regularToSpecht]
  simp only [Equiv.permCongrHom_symm, finCongr_symm, map_smul, map_inv₀, eq_ratCast]
  rw [Nat.Partition.youngSymmetrizer_def, youngSymmetrizerOver_def]
  ext g
  simp [Rat.smul_def]

/-- **The complex Specht module is a retract of the regular representation**, through
intertwining maps `i` and `p` with `p ∘ i = id` whose idempotent `i (p 1)` has antipode a
nonzero multiple of the Young symmetrizer `c_μ`. -/
theorem exists_retract_spechtModuleℂ :
    ∃ (i : Representation.IntertwiningMap (spechtModuleℂ μ).ρ
        (leftRegular ℂ (Equiv.Perm (Fin n))))
      (p : Representation.IntertwiningMap (leftRegular ℂ (Equiv.Perm (Fin n)))
        (spechtModuleℂ μ).ρ),
      p.comp i = .id _ ∧ ∃ c : ℂ, c ≠ 0 ∧
        HopfAlgebra.antipode ℂ (i (p (MonoidAlgebra.single 1 1))) = c • μ.youngSymmetrizer ℂ := by
  rw [spechtModuleℂ_def]
  exact ⟨iC μ, pC μ, pC_comp_iC μ, _, by simpa using inv_ne_zero (κ_ne_zero (tab μ)),
    antipode_iC_pC μ⟩

end Retract

end TauCeti

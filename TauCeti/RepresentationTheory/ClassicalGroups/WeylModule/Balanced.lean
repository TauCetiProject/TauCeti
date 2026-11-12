/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Decomposition
public import TauCeti.RepresentationTheory.Symmetric.Specht.Complex
-- Non-public: the Specht module is exhibited as a retract of the regular representation only
-- inside the proof of `TauCeti.balancedSchurPresentation`; no statement mentions the ideal
-- presentation, the comparison with it, or the coinvariant contraction.
import TauCeti.RepresentationTheory.Symmetric.Specht.Comparison
import TauCeti.RepresentationTheory.Symmetric.Specht.Ideal.Idempotent
import TauCeti.RepresentationTheory.Tensor.Coinvariants

/-!
# The balanced tensor presentation of the Schur functor

The tensor power `(ℂᵈ)^{⊗n}` is a right module over `ℂ[Sₙ]` through `v · σ = σ⁻¹ v`, and the
complex Specht module `S^μ` of a partition `μ` of `n` is a left module, so they have a balanced
tensor product `(ℂᵈ)^{⊗n} ⊗_{ℂ[Sₙ]} S^μ`: the quotient of `(ℂᵈ)^{⊗n} ⊗ S^μ` by the balancing
relations `(v · σ) ⊗ s - v ⊗ (σ · s)`, `TauCeti.balancedSchurRelations d n μ`. The general linear
group `GL d ℂ`, acting diagonally on the tensor power, commutes with `Sₙ` and so acts on it.
This file proves that it is the Schur functor `𝕊^μ(ℂᵈ)` (`TauCeti.balancedSchurPresentation`):
there is a surjective, `GL d ℂ`-equivariant linear map `(ℂᵈ)^{⊗n} ⊗ S^μ → 𝕊^μ(ℂᵈ)` whose kernel
is exactly the span of the balancing relations. This is the classical definition
`𝕊^μ V = V^{⊗n} ⊗_{ℂ[Sₙ]} S^μ` of the Schur functor, compared with its construction as the image
`c_μ V^{⊗n}` of a Young symmetrizer. Both vanish when `μ` has more than `d` rows.

The balanced tensor product is the coinvariants `((ℂᵈ)^{⊗n} ⊗ S^μ)_{Sₙ}`
(`TauCeti.coinvariantsKer_tprod_eq_balancedSchurRelations`), and for a retract `W` of the regular
representation, with idempotent `e`, the coinvariants `(V ⊗ W)_G` are the image of the antipode
of `e` acting on `V` (`Representation.IntertwiningMap.ker_tprodContraction` and
`Representation.IntertwiningMap.range_tprodContraction`). The proof exhibits `S^μ` as such a
retract, with an idempotent whose antipode is a multiple of the Young symmetrizer `c_μ = a_t b_t`
itself. Starting from the ideal presentation `φ : ℚ[Sₙ] c_t ≅ S^μ`
(`TauCeti.YoungTableau.spechtIdealEquivSpechtSubrepresentation`), the embedding is
`w ↦ φ⁻¹(w) a_t` and the projection is `x ↦ φ(κ⁻² x b_t c_t)`, where `c_t² = κ c_t`. The
idempotent is `κ⁻² b_t c_t a_t`, and since the antipode fixes `a_t` and `b_t` and reverses
products, its antipode is `κ⁻² (a_t b_t)² = κ⁻¹ c_t`. The image of `c_μ` is the Weyl module
of `μ` (`TauCeti.weylRepOfShapeEquivRange`), which is the Schur functor. The embedding is
twisted by `a_t` so as to produce `c_t`, not the reversed symmetrizer `b_t a_t`.

## Main definitions

* `TauCeti.balancedSchurRelations`: the balancing relations in `(ℂᵈ)^{⊗n} ⊗ S^μ`.

## Main results

* `TauCeti.coinvariantsKer_tprod_eq_balancedSchurRelations`: they are the coinvariant kernel.
* `TauCeti.balancedSchurRelations_le_comap_rTensor`: they are invariant under `GL d ℂ`.
* `TauCeti.balancedSchurRelations_le_ker_lift_iff`: a bilinear map factors through the quotient
  exactly when it is balanced.
* `TauCeti.balancedSchurPresentation`: **the balanced tensor presentation**: the quotient by them
  is `𝕊^μ(ℂᵈ)`, as a representation of `GL d ℂ`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §6.1, where
  `𝕊_λ V = V^{⊗d} ⊗_{ℂ[S_d]} V_λ` is identified with the image `V^{⊗d} c_λ`.
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

-- The essential idempotence of `c_t`, restated with the named scalar `κ`.
private theorem mul_youngSymmetrizer_eq {x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))}
    (hx : x ∈ spechtIdeal t) : x * youngSymmetrizer t = κ t • x :=
  mul_youngSymmetrizer_of_mem_spechtIdeal hx

private theorem youngSymmetrizer_mul_self :
    youngSymmetrizer t * youngSymmetrizer t = κ t • youngSymmetrizer (R := ℚ) t :=
  youngSymmetrizer_sq t

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
    rw [mul_assoc, ← mul_assoc (rowSymmetrizer t), ← youngSymmetrizer_def, ← mul_assoc,
      mul_youngSymmetrizer_eq t y.2, smul_mul_assoc, mul_youngSymmetrizer_eq t y.2, smul_smul,
      smul_smul]
    have hκ : (κ t)⁻¹ ^ 2 * κ t * κ t = 1 := by
      have := κ_ne_zero t
      field_simp
    rw [hκ, one_smul]
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
    youngSymmetrizer_mul_self, smul_smul]
  have := κ_ne_zero t
  congr 1
  field_simp

end YoungTableau

section Retract

open YoungTableau

variable {n : ℕ} (μ : n.Partition)

private theorem permCongrHom_symm :
    (finCongr (YoungDiagram.card_ofPartition μ).symm).permCongrHom.symm =
      (finCongr (YoungDiagram.card_ofPartition μ)).permCongrHom := by
  ext σ i
  simp

/-- The row-superstandard tableau of the diagram of `μ`, along which `S^μ` is defined. -/
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
  exact IntertwiningMap.apply_apply_eq_of_comp_eq_id
    (regularToSpecht_comp_spechtToRegular (tab μ)) w

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
  refine IntertwiningMap.ext (LinearMap.ext fun w => ?_)
  rw [IntertwiningMap.toLinearMap_apply, IntertwiningMap.toLinearMap_apply,
    IntertwiningMap.comp_apply, IntertwiningMap.id_apply]
  induction w using TensorProduct.inductionOn with
  | tmul z w =>
    simp only [pC, iC, IntertwiningMap.comp_apply, Representation.Equiv.coe_toIntertwiningMap,
      Representation.Equiv.symm_apply_apply, IntertwiningMap.baseChange_tmul,
      IntertwiningMap.apply_apply_eq_of_comp_eq_id (pQ_comp_iQ μ)]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

-- On `1 ⊗ x` the identification `ℂ ⊗_ℚ ℚ[G] ≅ ℂ[G]` extends the coefficients of `x`.
private theorem baseChangeOfMulActionEquiv_one_tmul {G : Type*} [Group G]
    (x : MonoidAlgebra ℚ G) :
    baseChangeOfMulActionEquiv ℚ ℂ G G (1 ⊗ₜ x) =
      MonoidAlgebra.mapAlgHom G (Algebra.ofId ℚ ℂ) x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add]
  | single g r => simp

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
    MonoidAlgebra.antipode_domCongr,
    antipode_spechtToRegular_regularToSpecht, map_smul, map_smul, ← algebraMap_smul ℂ,
    MonoidAlgebra.mapAlgHom_domCongr, permCongrHom_symm, Nat.Partition.youngSymmetrizer_def,
    youngSymmetrizerOver_def]

/-- **The complex Specht module is a retract of the regular representation**, through
intertwining maps `i` and `p` with `p ∘ i = id` whose idempotent `i (p 1)` has antipode a
nonzero multiple of the Young symmetrizer `c_μ`. -/
private theorem exists_retract_spechtModuleℂ :
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

variable (d n : ℕ) (μ : n.Partition)

/-- **The balancing relations** of `(ℂᵈ)^{⊗n} ⊗ S^μ`: the complex span of
`(v · σ) ⊗ s - v ⊗ (σ · s)` for `σ ∈ Sₙ`, where `v · σ = σ⁻¹ v` makes the tensor power a right
module over `ℂ[Sₙ]`. The quotient by them is the balanced tensor product
`(ℂᵈ)^{⊗n} ⊗_{ℂ[Sₙ]} S^μ`; by linearity the relations for every `a ∈ ℂ[Sₙ]` lie in the span. -/
noncomputable def balancedSchurRelations :
    Submodule ℂ ((⨂[ℂ] (_ : Fin n), (Fin d → ℂ)) ⊗[ℂ] spechtModuleℂ μ) :=
  Submodule.span ℂ {x | ∃ (v : ⨂[ℂ] (_ : Fin n), (Fin d → ℂ)) (s : spechtModuleℂ μ)
    (g : Equiv.Perm (Fin n)),
    x = permTensorAction ℂ d n g⁻¹ v ⊗ₜ[ℂ] s - v ⊗ₜ[ℂ] (spechtModuleℂ μ).ρ g s}

/-- The balancing relations are the span of the relations `(v · σ) ⊗ s - v ⊗ (σ · s)`. -/
theorem balancedSchurRelations_def :
    balancedSchurRelations d n μ = Submodule.span ℂ {x | ∃ (v : ⨂[ℂ] (_ : Fin n), (Fin d → ℂ))
      (s : spechtModuleℂ μ) (g : Equiv.Perm (Fin n)),
      x = permTensorAction ℂ d n g⁻¹ v ⊗ₜ[ℂ] s - v ⊗ₜ[ℂ] (spechtModuleℂ μ).ρ g s} :=
  (rfl)

/-- **The balancing relations are the coinvariant kernel** of the tensor product of the
permutation action with the Specht action: the balanced tensor product is the coinvariants
`((ℂᵈ)^{⊗n} ⊗ S^μ)_{Sₙ}`. -/
theorem coinvariantsKer_tprod_eq_balancedSchurRelations :
    Coinvariants.ker (V := (⨂[ℂ] (_ : Fin n), (Fin d → ℂ)) ⊗[ℂ] spechtModuleℂ μ)
      ((permTensorAction ℂ d n).tprod (spechtModuleℂ μ).ρ) = balancedSchurRelations d n μ :=
  Coinvariants.ker_tprod_eq_span (permTensorAction ℂ d n) (spechtModuleℂ μ).ρ

/-- Each balancing relation `(v · σ) ⊗ s - v ⊗ (σ · s)` lies in the span of the balancing
relations. -/
theorem sub_mem_balancedSchurRelations (v : ⨂[ℂ] (_ : Fin n), (Fin d → ℂ))
    (s : spechtModuleℂ μ) (g : Equiv.Perm (Fin n)) :
    permTensorAction ℂ d n g⁻¹ v ⊗ₜ[ℂ] s - v ⊗ₜ[ℂ] (spechtModuleℂ μ).ρ g s ∈
      balancedSchurRelations d n μ := by
  rw [balancedSchurRelations_def]
  exact Submodule.subset_span ⟨v, s, g, rfl⟩

/-- **The universal property of the balanced tensor product**: a bilinear map out of
`(ℂᵈ)^{⊗n} × S^μ` vanishes on the balancing relations, and so factors through the quotient by
them (`Submodule.liftQ`, uniquely since the quotient map is onto), exactly when it is balanced,
sending `(v · σ, s)` and `(v, σ · s)` to the same value. -/
theorem balancedSchurRelations_le_ker_lift_iff {M : Type*} [AddCommGroup M] [Module ℂ M]
    (B : (⨂[ℂ] (_ : Fin n), (Fin d → ℂ)) →ₗ[ℂ] spechtModuleℂ μ →ₗ[ℂ] M) :
    balancedSchurRelations d n μ ≤ LinearMap.ker (TensorProduct.lift B) ↔
      ∀ v s g, B (permTensorAction ℂ d n g⁻¹ v) s = B v ((spechtModuleℂ μ).ρ g s) := by
  rw [balancedSchurRelations_def, Submodule.span_le]
  refine ⟨fun h v s g => ?_, ?_⟩
  · have := h ⟨v, s, g, rfl⟩
    rwa [SetLike.mem_coe, LinearMap.mem_ker, map_sub, TensorProduct.lift.tmul,
      TensorProduct.lift.tmul, sub_eq_zero] at this
  · rintro h _ ⟨v, s, g, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, TensorProduct.lift.tmul,
      TensorProduct.lift.tmul, h, sub_self]

/-- **The balancing relations are invariant under `GL d ℂ`** acting on the tensor-power factor,
because that action commutes with the permutation of the tensor factors. So `GL d ℂ` acts on the
balanced tensor product. -/
theorem balancedSchurRelations_le_comap_rTensor (g : GL (Fin d) ℂ) :
    balancedSchurRelations d n μ ≤ (balancedSchurRelations d n μ).comap
      ((tensorPowerRep ℂ d n g).rTensor (spechtModuleℂ μ)) := by
  rw [balancedSchurRelations_def, Submodule.span_le]
  rintro _ ⟨v, s, σ, rfl⟩
  have h := commute_permTensorActionAlgHom_tensorPowerRep ℂ d n
    (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ⁻¹) g
  rw [permTensorActionAlgHom_of] at h
  have hv : tensorPowerRep ℂ d n g (permTensorAction ℂ d n σ⁻¹ v) =
      permTensorAction ℂ d n σ⁻¹ (tensorPowerRep ℂ d n g v) := by
    simpa only [mul_apply_eq_comp] using congr($(h.eq) v).symm
  simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, LinearMap.rTensor_tmul, hv]
  exact sub_mem_balancedSchurRelations d n μ _ s σ

/-- **The balanced tensor presentation of the Schur functor.** There is a surjective linear map
`(ℂᵈ)^{⊗n} ⊗ S^μ → 𝕊^μ(ℂᵈ)` whose kernel is exactly the span of the balancing relations
`(v · σ) ⊗ s - v ⊗ (σ · s)`, and which intertwines the diagonal action of `GL d ℂ` on the
tensor-power factor with the action on the Schur functor. So it induces a `GL d ℂ`-equivariant
equivalence `(ℂᵈ)^{⊗n} ⊗_{ℂ[Sₙ]} S^μ ≅ 𝕊^μ(ℂᵈ)`, also when `μ` has more than `d` rows, where
both sides vanish. -/
theorem balancedSchurPresentation :
    ∃ f : ((⨂[ℂ] (_ : Fin n), (Fin d → ℂ)) ⊗[ℂ] spechtModuleℂ μ) →ₗ[ℂ]
        schurFunctor d (YoungDiagram.ofPartition μ),
      Function.Surjective f ∧ LinearMap.ker f = balancedSchurRelations d n μ ∧
      ∀ (g : GL (Fin d) ℂ) (v : ⨂[ℂ] (_ : Fin n), (Fin d → ℂ)) (s : spechtModuleℂ μ),
        f ((tensorPowerRep ℂ d n g v) ⊗ₜ[ℂ] s) =
          (schurFunctor d (YoungDiagram.ofPartition μ)).ρ g (f (v ⊗ₜ[ℂ] s)) := by
  obtain ⟨i, p, hpi, c, hc, he⟩ := exists_retract_spechtModuleℂ μ
  -- the contraction `v ⊗ s ↦ S(i s) · v` has image `c_μ (ℂᵈ)^{⊗n}`, identified with `𝕊^μ(ℂᵈ)`
  let F := i.tprodContraction (permTensorAction ℂ d n)
  have hrange : LinearMap.range F =
      LinearMap.range ((permTensorAction ℂ d n).asAlgebraHom (μ.youngSymmetrizer ℂ)) := by
    rw [IntertwiningMap.range_tprodContraction hpi, he, map_smul, LinearMap.range_smul _ _ hc]
  let W := weylRepOfShapeEquivRange ℂ d n μ
  let e := (LinearEquiv.ofEq _ _ hrange).trans W.symm.toLinearEquiv
  refine ⟨e.toLinearMap ∘ₗ F.rangeRestrict, e.surjective.comp F.surjective_rangeRestrict, ?_, ?_⟩
  · rw [LinearEquiv.ker_comp, LinearMap.ker_rangeRestrict, IntertwiningMap.ker_tprodContraction hpi,
      coinvariantsKer_tprod_eq_balancedSchurRelations]
  · intro g v s
    have hF : F (tensorPowerRep ℂ d n g v ⊗ₜ s) = tensorPowerRep ℂ d n g (F (v ⊗ₜ s)) := by
      have h := commute_permTensorActionAlgHom_tensorPowerRep ℂ d n
        (HopfAlgebra.antipode ℂ (i s)) g
      rw [permTensorActionAlgHom_def] at h
      simpa only [F, IntertwiningMap.tprodContraction_tmul, mul_apply_eq_comp] using
        congr($(h.eq) v)
    have hr : LinearEquiv.ofEq _ _ hrange (F.rangeRestrict (tensorPowerRep ℂ d n g v ⊗ₜ s)) =
        (tensorPowerRep ℂ d n).subrepresentation _
          (range_asAlgebraHom_permTensorAction_le_comap ℂ d n _) g
          (LinearEquiv.ofEq _ _ hrange (F.rangeRestrict (v ⊗ₜ s))) :=
      Subtype.ext hF
    have hW := LinearMap.congr_fun (W.symm.toIntertwiningMap.isIntertwining' g)
      (LinearEquiv.ofEq _ _ hrange (F.rangeRestrict (v ⊗ₜ s)))
    simp only [LinearMap.coe_comp, Function.comp_apply] at hW
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, e,
      LinearEquiv.trans_apply, hr, Representation.Equiv.toLinearEquiv_apply, FDRep.of_ρ']
    exact hW

end TauCeti

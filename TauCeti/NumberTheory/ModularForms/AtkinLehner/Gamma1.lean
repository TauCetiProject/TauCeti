/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Operator
public import TauCeti.NumberTheory.ModularForms.Fricke.Operator
import Mathlib.LinearAlgebra.Matrix.Integer
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The Atkin–Lehner operators on `Γ₁(N)` and the nebentypus

An Atkin–Lehner matrix `W` for an exact divisor `Q` of `N` normalizes `Γ₀(N)`, and the operators
of `TauCeti/NumberTheory/ModularForms/AtkinLehner/Operator.lean` act on `M_k(Γ₀(N))`. It
normalizes `Γ₁(N)` as well, so the weight-`k` slash by `W` is also an operator `W_Q` on
`M_k(Γ₁(N))` and on `S_k(Γ₁(N))`; that is the operator built here, the carrier on which forms of
nontrivial nebentypus live.

`W_Q` does not commute with the diamond operators. Moving a representative `γ ∈ Γ₀(N)` of a label
`d ∈ (ZMod N)ˣ` across `W` inverts the residue of the label modulo `Q` and keeps its residue modulo
`N / Q` (`TauCeti.IsAtkinLehnerMatrix.toHomUnits_gamma0Map_of_mul_eq_mul`); writing `ι_Q` for this
automorphism `TauCeti.Nat.IsExactDivisor.unitsInvPart` of `(ZMod N)ˣ`,

`W_Q ∘ ⟨d⟩ = ⟨ι_Q d⟩ ∘ W_Q`.

Read on a nebentypus space this is Atkin and Li's transport of characters: `W_Q` carries
`M_k(N, χ)` into `M_k(N, χ ∘ ι_Q)`, and for `χ = χ_Q · χ_{N/Q}` split along `N = Q · (N / Q)`,
`χ ∘ ι_Q = χ_Q⁻¹ · χ_{N/Q}` (`TauCeti.Nat.IsExactDivisor.comp_unitsInvPart`). So `W_Q` preserves the
nebentypus space only when the `Q`-part of `χ` is quadratic, which is why the Atkin–Lehner theory
of a newform of general nebentypus is a theory of pseudo-eigenvalues rather than eigenvalues.

On `Γ₁(N)` the operator depends on the chosen Atkin–Lehner matrix, unlike on `Γ₀(N)`: two choices
differ by `γ ∈ Γ₀(N)` on the left, and replacing `W` by `γ W` precomposes `W_Q` with the diamond
operator of `γ`. On `M_k(N, χ)` that is the scalar `χ(d_γ)`, so the operator is determined by `Q`
up to a scalar there. At `Q = N` the Fricke matrix gives the Fricke operator of
`TauCeti/NumberTheory/ModularForms/Fricke/Operator.lean`, and `ι_N` is inversion.

## Main definitions

* `TauCeti.atkinLehnerOperatorGamma1`, `TauCeti.atkinLehnerOperatorGamma1Cusp`: the slash by an
  Atkin–Lehner matrix on `M_k(Γ₁(N))` and on `S_k(Γ₁(N))`.
* `TauCeti.atkinLehnerGamma1CharRestrict`, `TauCeti.atkinLehnerGamma1CharCuspRestrict`: those
  operators restricted to linear maps `M_k(N, χ) → M_k(N, χ ∘ ι_Q)` and
  `S_k(N, χ) → S_k(N, χ ∘ ι_Q)`.

## Main results

* `TauCeti.Gamma1_map_inv_conjAct_atkinLehnerGL_eq`: `W` normalizes the image of `Γ₁(N)` in
  `GL (Fin 2) ℝ`.
* `TauCeti.atkinLehnerOperatorGamma1_diamondOp`,
  `TauCeti.atkinLehnerOperatorGamma1Cusp_diamondOpCusp`: the diamond shift
  `W_Q ∘ ⟨d⟩ = ⟨ι_Q d⟩ ∘ W_Q`.
* `TauCeti.atkinLehnerOperatorGamma1_mem_modFormCharSpace`,
  `TauCeti.atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace`: `W_Q` carries the nebentypus
  `χ` to `χ ∘ ι_Q`.
* `TauCeti.atkinLehnerOperatorGamma1_mul_left`,
  `TauCeti.atkinLehnerOperatorGamma1_mul_left_of_mem_modFormCharSpace`: the dependence on the
  matrix, `W_{γ W} = W_W ∘ ⟨d_γ⟩`, a scalar `χ(d_γ)` on `M_k(N, χ)`; with cusp-form counterparts
  `TauCeti.atkinLehnerOperatorGamma1Cusp_mul_left` and
  `TauCeti.atkinLehnerOperatorGamma1Cusp_mul_left_of_mem_cuspFormCharSpace`.
* `TauCeti.atkinLehnerOperatorGamma1_fricke`, `TauCeti.atkinLehnerOperatorGamma1Cusp_fricke`: at
  the Fricke matrix the operator is `frickeOperator`.

## References

* A. O. L. Atkin and W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of
  `W`-operators*, Invent. Math. **48** (1978), 221–243, §1.
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise TauCeti.ExactDivisor

namespace TauCeti

variable {N Q : ℕ} {M : Matrix (Fin 2) (Fin 2) ℤ} {k : ℤ}

/-- **Moving `Γ₀(N)` past `W` in `GL (Fin 2) ℝ`, with the label shift**: `g W = W g'` for some
`g' ∈ Γ₀(N)` whose diamond label is the label of `g` with its residue modulo `Q` inverted. -/
theorem exists_mapGL_mul_atkinLehnerGL_eq (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (g : ↥(Gamma0 N)) :
    ∃ g' : ↥(Gamma0 N), mapGL ℝ (g : SL(2, ℤ)) * atkinLehnerGL hQ h =
        atkinLehnerGL hQ h * mapGL ℝ (g' : SL(2, ℤ)) ∧
      (Gamma0Map N).toHomUnits g' =
        (h.isExactDivisor hQ.ne' hQN).unitsInvPart ((Gamma0Map N).toHomUnits g) := by
  obtain ⟨δ, hδ, hmul⟩ := h.exists_mem_Gamma0_mul_eq_mul_right hQ.ne' hQN g.2
  refine ⟨⟨δ, hδ⟩, Units.ext ?_, h.toHomUnits_gamma0Map_of_mul_eq_mul hQ.ne' hQN g.2 hδ hmul⟩
  simp only [Matrix.GeneralLinearGroup.coe_mul, coe_atkinLehnerGL, mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, algebraMap_int_eq,
    Int.coe_castRingHom, ← Matrix.map_mul_intCast, hmul]

/-- **Moving `W` past `Γ₀(N)` in `GL (Fin 2) ℝ`, with the label shift**: `W g = g' W` for some
`g' ∈ Γ₀(N)` whose diamond label is the label of `g` with its residue modulo `Q` inverted. -/
theorem exists_atkinLehnerGL_mul_mapGL_eq (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (g : ↥(Gamma0 N)) :
    ∃ g' : ↥(Gamma0 N), atkinLehnerGL hQ h * mapGL ℝ (g : SL(2, ℤ)) =
        mapGL ℝ (g' : SL(2, ℤ)) * atkinLehnerGL hQ h ∧
      (Gamma0Map N).toHomUnits g' =
        (h.isExactDivisor hQ.ne' hQN).unitsInvPart ((Gamma0Map N).toHomUnits g) := by
  -- `W g = g' W` is the relation `g' W = W g` of `toHomUnits_gamma0Map_of_mul_eq_mul` read
  -- backwards, which gives the label of `g` from that of `g'`; the shift is an involution.
  obtain ⟨δ, hδ, hmul⟩ := h.exists_mem_Gamma0_mul_eq_mul_left hQ.ne' hQN g.2
  refine ⟨⟨δ, hδ⟩, Units.ext ?_, ?_⟩
  · simp only [Matrix.GeneralLinearGroup.coe_mul, coe_atkinLehnerGL, mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, algebraMap_int_eq,
      Int.coe_castRingHom, ← Matrix.map_mul_intCast, hmul]
  · rw [h.toHomUnits_gamma0Map_of_mul_eq_mul hQ.ne' hQN hδ g.2 hmul.symm,
      Nat.IsExactDivisor.unitsInvPart_unitsInvPart]

/-- **`W` normalizes `Γ₁(N)` in `GL (Fin 2) ℝ`.** Moving an element of `Γ₁(N)`, of diamond label
`1`, across `W` gives an element of label `ι_Q 1 = 1`. This is what makes the slash by `W` an
operator on modular forms of level `Γ₁(N)`. -/
theorem Gamma1_map_inv_conjAct_atkinLehnerGL_eq (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) :
    ConjAct.toConjAct (atkinLehnerGL hQ h)⁻¹ • (Gamma1 N).map (mapGL ℝ) =
      (Gamma1 N).map (mapGL ℝ) := by
  ext y
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, map_inv, inv_inv, Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, hτy⟩
    obtain ⟨δ, hmul, hδ⟩ :=
      exists_mapGL_mul_atkinLehnerGL_eq hQ hQN h ⟨τ, Gamma1_in_Gamma0 N hτ⟩
    rw [(mem_Gamma1_iff_toHomUnits_eq_one ⟨τ, Gamma1_in_Gamma0 N hτ⟩).mp hτ, map_one] at hδ
    refine ⟨δ, (mem_Gamma1_iff_toHomUnits_eq_one δ).mpr hδ, ?_⟩
    rw [hτy] at hmul
    refine (mul_left_cancel (a := atkinLehnerGL hQ h) ?_).symm
    rw [← hmul]
    group
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨δ, hmul, hδ⟩ :=
      exists_atkinLehnerGL_mul_mapGL_eq hQ hQN h ⟨σ, Gamma1_in_Gamma0 N hσ⟩
    rw [(mem_Gamma1_iff_toHomUnits_eq_one ⟨σ, Gamma1_in_Gamma0 N hσ⟩).mp hσ, map_one] at hδ
    exact ⟨δ, (mem_Gamma1_iff_toHomUnits_eq_one δ).mpr hδ, by rw [hmul]; group⟩

/-- **The Atkin–Lehner slash operator on `M_k(Γ₁(N))`**: `f ↦ f ∣[k] W`, as a `ℂ`-linear
endomorphism, for an Atkin–Lehner matrix `W` of an exact divisor `Q` of `N`. Like the operator on
`M_k(Γ₀(N))` it carries no normalizing scalar. It depends on `W`, through a diamond operator
(`atkinLehnerOperatorGamma1_mul_left`). -/
noncomputable def atkinLehnerOperatorGamma1 (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (k : ℤ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    ModularForm.mcast rfl (ModularForm.translate f (atkinLehnerGL hQ h))
      (Gamma1_map_inv_conjAct_atkinLehnerGL_eq hQ hQN h).symm
  map_add' f g := by
    ext z
    exact congr_fun (SlashAction.add_slash k (atkinLehnerGL hQ h) ⇑f ⇑g) z
  map_smul' c f := by
    ext z
    exact congr_fun
      (ModularForm.smul_slash_of_det_pos k (val_det_atkinLehnerGL_pos hQ h) ⇑f c) z

/-- On underlying functions the Atkin–Lehner operator on `M_k(Γ₁(N))` is `⇑f ∣[k] W`. -/
@[simp]
theorem coe_atkinLehnerOperatorGamma1 (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(atkinLehnerOperatorGamma1 hQ hQN h k f) : ℍ → ℂ) = ⇑f ∣[k] atkinLehnerGL hQ h := (rfl)

/-- **The Atkin–Lehner slash operator on `S_k(Γ₁(N))`**, the cusp-form counterpart of
`atkinLehnerOperatorGamma1`. -/
noncomputable def atkinLehnerOperatorGamma1Cusp (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (k : ℤ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    CuspForm.mcast rfl (CuspForm.translate f (atkinLehnerGL hQ h))
      (Gamma1_map_inv_conjAct_atkinLehnerGL_eq hQ hQN h).symm
  map_add' f g := by
    ext z
    exact congr_fun (SlashAction.add_slash k (atkinLehnerGL hQ h) ⇑f ⇑g) z
  map_smul' c f := by
    ext z
    exact congr_fun
      (ModularForm.smul_slash_of_det_pos k (val_det_atkinLehnerGL_pos hQ h) ⇑f c) z

/-- On underlying functions the Atkin–Lehner operator on `S_k(Γ₁(N))` is `⇑f ∣[k] W`. -/
@[simp]
theorem coe_atkinLehnerOperatorGamma1Cusp (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(atkinLehnerOperatorGamma1Cusp hQ hQN h k f) : ℍ → ℂ) = ⇑f ∣[k] atkinLehnerGL hQ h :=
  (rfl)

/-- **The two Atkin–Lehner operators on `Γ₁(N)` agree under the coercion**
`S_k(Γ₁(N)) → M_k(Γ₁(N))`: both slash by `W`. -/
@[simp]
theorem atkinLehnerOperatorGamma1_coe_cuspForm (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (k : ℤ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    atkinLehnerOperatorGamma1 hQ hQN h k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (atkinLehnerOperatorGamma1Cusp hQ hQN h k f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  DFunLike.coe_injective <| by
    rw [coe_atkinLehnerOperatorGamma1, ModularFormClass.coe_modularForm,
      ModularFormClass.coe_modularForm, coe_atkinLehnerOperatorGamma1Cusp]

/-- **The diamond shift** `W_Q ∘ ⟨d⟩ = ⟨ι_Q d⟩ ∘ W_Q` on `M_k(Γ₁(N))`, where `ι_Q` inverts the
residue of `d` modulo `Q` and keeps its residue modulo `N / Q`. -/
theorem atkinLehnerOperatorGamma1_diamondOp (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (k : ℤ) (d : (ZMod N)ˣ) :
    (atkinLehnerOperatorGamma1 hQ hQN h k).comp (diamondOp k d) =
      (diamondOp k ((h.isExactDivisor hQ.ne' hQN).unitsInvPart d)).comp
        (atkinLehnerOperatorGamma1 hQ hQN h k) := by
  obtain ⟨g, hg⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
  obtain ⟨g', hmul, hg'⟩ := exists_mapGL_mul_atkinLehnerGL_eq hQ hQN h g
  refine LinearMap.ext fun f ↦ DFunLike.coe_injective ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, coe_atkinLehnerOperatorGamma1,
    coe_diamondOp k d g hg, coe_diamondOp k _ g' (by rw [hg', hg]),
    coe_atkinLehnerOperatorGamma1, ← SlashAction.slash_mul, ← SlashAction.slash_mul, hmul]

/-- **The diamond shift on cusp forms**: the `S_k(Γ₁(N))` counterpart of
`atkinLehnerOperatorGamma1_diamondOp`. -/
theorem atkinLehnerOperatorGamma1Cusp_diamondOpCusp (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (k : ℤ) (d : (ZMod N)ˣ) :
    (atkinLehnerOperatorGamma1Cusp hQ hQN h k).comp (diamondOpCusp k d) =
      (diamondOpCusp k ((h.isExactDivisor hQ.ne' hQN).unitsInvPart d)).comp
        (atkinLehnerOperatorGamma1Cusp hQ hQN h k) := by
  obtain ⟨g, hg⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
  obtain ⟨g', hmul, hg'⟩ := exists_mapGL_mul_atkinLehnerGL_eq hQ hQN h g
  refine LinearMap.ext fun f ↦ DFunLike.coe_injective ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, coe_atkinLehnerOperatorGamma1Cusp,
    coe_diamondOpCusp k d g hg, coe_diamondOpCusp k _ g' (by rw [hg', hg]),
    coe_atkinLehnerOperatorGamma1Cusp, ← SlashAction.slash_mul, ← SlashAction.slash_mul, hmul]

/-- **`W_Q` shifts the nebentypus `χ` to `χ ∘ ι_Q`**: it carries `M_k(N, χ)` into
`M_k(N, χ ∘ ι_Q)`. For `χ = χ_Q · χ_{N/Q}` the new nebentypus is `χ_Q⁻¹ · χ_{N/Q}`
(`Nat.IsExactDivisor.comp_unitsInvPart`). -/
theorem atkinLehnerOperatorGamma1_mem_modFormCharSpace (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) {χ : (ZMod N)ˣ →* ℂˣ}
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    atkinLehnerOperatorGamma1 hQ hQN h k f ∈
      modFormCharSpace k
        (χ.comp ((h.isExactDivisor hQ.ne' hQN).unitsInvPart : (ZMod N)ˣ →* (ZMod N)ˣ)) := by
  rw [mem_modFormCharSpace_iff]
  intro d
  have hd := LinearMap.congr_fun (atkinLehnerOperatorGamma1_diamondOp hQ hQN h k
    ((h.isExactDivisor hQ.ne' hQN).unitsInvPart d)) f
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Nat.IsExactDivisor.unitsInvPart_unitsInvPart,
    diamondOp_apply_of_mem_modFormCharSpace k χ _ hf, map_smul] at hd
  rw [diamondOpHom_apply, ← hd, MonoidHom.comp_apply, MonoidHom.coe_ofClass]

/-- **`W_Q` shifts the nebentypus `χ` to `χ ∘ ι_Q` on cusp forms**: it carries `S_k(N, χ)` into
`S_k(N, χ ∘ ι_Q)`. -/
theorem atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    atkinLehnerOperatorGamma1Cusp hQ hQN h k f ∈
      cuspFormCharSpace k
        (χ.comp ((h.isExactDivisor hQ.ne' hQN).unitsInvPart : (ZMod N)ˣ →* (ZMod N)ˣ)) := by
  rw [mem_cuspFormCharSpace_iff]
  intro d
  have hd := LinearMap.congr_fun (atkinLehnerOperatorGamma1Cusp_diamondOpCusp hQ hQN h k
    ((h.isExactDivisor hQ.ne' hQN).unitsInvPart d)) f
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Nat.IsExactDivisor.unitsInvPart_unitsInvPart,
    diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ _ hf, map_smul] at hd
  rw [diamondOpCuspHom_apply, ← hd, MonoidHom.comp_apply, MonoidHom.coe_ofClass]

/-- **The Atkin–Lehner operator on `Γ₁(N)` restricted to a nebentypus space**, as a `ℂ`-linear
map `M_k(N, χ) →ₗ[ℂ] M_k(N, χ ∘ ι_Q)`. This is `atkinLehnerOperatorGamma1` cut down by
`LinearMap.restrict`. -/
noncomputable def atkinLehnerGamma1CharRestrict (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    modFormCharSpace k χ →ₗ[ℂ]
      modFormCharSpace k
        (χ.comp ((h.isExactDivisor hQ.ne' hQN).unitsInvPart : (ZMod N)ˣ →* (ZMod N)ˣ)) :=
  (atkinLehnerOperatorGamma1 hQ hQN h k).restrict fun _ hf ↦
    atkinLehnerOperatorGamma1_mem_modFormCharSpace hQ hQN h hf

/-- On underlying modular forms, `atkinLehnerGamma1CharRestrict` is `atkinLehnerOperatorGamma1`. -/
@[simp]
theorem coe_atkinLehnerGamma1CharRestrict_apply (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (f : modFormCharSpace k χ) :
    (atkinLehnerGamma1CharRestrict hQ hQN h k χ f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      atkinLehnerOperatorGamma1 hQ hQN h k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  -- Naming the restriction as a `def` destroys the `LinearMap.restrict` head symbol, so
  -- `LinearMap.coe_restrict_apply` does not fire as a `simp` lemma; it still applies by name.
  LinearMap.coe_restrict_apply _ _

/-- **The Atkin–Lehner operator on `Γ₁(N)` restricted to a nebentypus space of cusp forms**, as a
`ℂ`-linear map `S_k(N, χ) →ₗ[ℂ] S_k(N, χ ∘ ι_Q)`. The cusp-form counterpart of
`atkinLehnerGamma1CharRestrict`. -/
noncomputable def atkinLehnerGamma1CharCuspRestrict (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspFormCharSpace k χ →ₗ[ℂ]
      cuspFormCharSpace k
        (χ.comp ((h.isExactDivisor hQ.ne' hQN).unitsInvPart : (ZMod N)ˣ →* (ZMod N)ˣ)) :=
  (atkinLehnerOperatorGamma1Cusp hQ hQN h k).restrict fun _ hf ↦
    atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace hQ hQN h hf

/-- On underlying cusp forms, `atkinLehnerGamma1CharCuspRestrict` is
`atkinLehnerOperatorGamma1Cusp`. The cusp-form counterpart of
`coe_atkinLehnerGamma1CharRestrict_apply`, stated for the same reason. -/
@[simp]
theorem coe_atkinLehnerGamma1CharCuspRestrict_apply (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (f : cuspFormCharSpace k χ) :
    (atkinLehnerGamma1CharCuspRestrict hQ hQN h k χ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      atkinLehnerOperatorGamma1Cusp hQ hQN h k (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  LinearMap.coe_restrict_apply _ _

/-- Replacing `W` by `γ W`, for `γ ∈ Γ₀(N)`, multiplies the matrix read in `GL (Fin 2) ℝ` by `γ`
on the left. -/
private theorem atkinLehnerGL_mul_left (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    atkinLehnerGL hQ (h.mul_left hQN hγ) = mapGL ℝ γ * atkinLehnerGL hQ h := by
  refine Units.ext ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, coe_atkinLehnerGL, mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, algebraMap_int_eq,
    Int.coe_castRingHom, ← Matrix.map_mul_intCast]

/-- **The dependence on the Atkin–Lehner matrix**: replacing `W` by `γ W`, for `γ ∈ Γ₀(N)`,
precomposes the operator on `M_k(Γ₁(N))` with the diamond operator of `γ`. Every Atkin–Lehner
matrix for `Q` is of the form `γ W` (`IsAtkinLehnerMatrix.exists_mem_Gamma0_eq_mul_left`). -/
theorem atkinLehnerOperatorGamma1_mul_left (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (k : ℤ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    atkinLehnerOperatorGamma1 hQ hQN (h.mul_left hQN hγ) k =
      (atkinLehnerOperatorGamma1 hQ hQN h k).comp
        (diamondOp k ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩)) := by
  refine LinearMap.ext fun f ↦ DFunLike.coe_injective ?_
  rw [LinearMap.comp_apply, coe_atkinLehnerOperatorGamma1, coe_atkinLehnerOperatorGamma1,
    coe_diamondOp k _ ⟨γ, hγ⟩ rfl, atkinLehnerGL_mul_left hQ hQN h hγ, SlashAction.slash_mul]

/-- **On `M_k(N, χ)` the operator is determined by `Q` up to a scalar**: replacing `W` by `γ W`
multiplies `W_Q f` by `χ(d_γ)`, for `d_γ` the diamond label of `γ ∈ Γ₀(N)`. -/
theorem atkinLehnerOperatorGamma1_mul_left_of_mem_modFormCharSpace (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N)
    {χ : (ZMod N)ˣ →* ℂˣ} {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    atkinLehnerOperatorGamma1 hQ hQN (h.mul_left hQN hγ) k f =
      (χ ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) : ℂ) • atkinLehnerOperatorGamma1 hQ hQN h k f := by
  rw [atkinLehnerOperatorGamma1_mul_left, LinearMap.comp_apply,
    diamondOp_apply_of_mem_modFormCharSpace k χ _ hf, map_smul]

/-- **The dependence on the Atkin–Lehner matrix, on cusp forms**: the `S_k(Γ₁(N))` counterpart of
`atkinLehnerOperatorGamma1_mul_left`. -/
theorem atkinLehnerOperatorGamma1Cusp_mul_left (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (k : ℤ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    atkinLehnerOperatorGamma1Cusp hQ hQN (h.mul_left hQN hγ) k =
      (atkinLehnerOperatorGamma1Cusp hQ hQN h k).comp
        (diamondOpCusp k ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩)) := by
  refine LinearMap.ext fun f ↦ DFunLike.coe_injective ?_
  rw [LinearMap.comp_apply, coe_atkinLehnerOperatorGamma1Cusp, coe_atkinLehnerOperatorGamma1Cusp,
    coe_diamondOpCusp k _ ⟨γ, hγ⟩ rfl, atkinLehnerGL_mul_left hQ hQN h hγ, SlashAction.slash_mul]

/-- **On `S_k(N, χ)` the operator is determined by `Q` up to a scalar**: the cusp-form counterpart
of `atkinLehnerOperatorGamma1_mul_left_of_mem_modFormCharSpace`. -/
theorem atkinLehnerOperatorGamma1Cusp_mul_left_of_mem_cuspFormCharSpace (hQ : 0 < Q)
    (hQN : Q ∣ N) (h : IsAtkinLehnerMatrix N Q M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N)
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) :
    atkinLehnerOperatorGamma1Cusp hQ hQN (h.mul_left hQN hγ) k f =
      (χ ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) : ℂ) • atkinLehnerOperatorGamma1Cusp hQ hQN h k f := by
  rw [atkinLehnerOperatorGamma1Cusp_mul_left, LinearMap.comp_apply,
    diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ _ hf, map_smul]

/-- **At the Fricke matrix the operator is the Fricke operator** `frickeOperator` on
`M_k(Γ₁(N))`. -/
theorem atkinLehnerOperatorGamma1_fricke [NeZero N] (k : ℤ) :
    atkinLehnerOperatorGamma1 (NeZero.pos N) dvd_rfl isAtkinLehnerMatrix_fricke k =
      frickeOperator k :=
  LinearMap.ext fun f ↦ DFunLike.coe_injective <| by
    rw [coe_atkinLehnerOperatorGamma1, coe_frickeOperator, atkinLehnerGL_fricke]

/-- **At the Fricke matrix the cusp-form operator is the Fricke operator** `frickeOperatorCusp`
on `S_k(Γ₁(N))`. -/
theorem atkinLehnerOperatorGamma1Cusp_fricke [NeZero N] (k : ℤ) :
    atkinLehnerOperatorGamma1Cusp (NeZero.pos N) dvd_rfl isAtkinLehnerMatrix_fricke k =
      frickeOperatorCusp k :=
  LinearMap.ext fun f ↦ DFunLike.coe_injective <| by
    rw [coe_atkinLehnerOperatorGamma1Cusp, coe_frickeOperatorCusp, atkinLehnerGL_fricke]

end TauCeti

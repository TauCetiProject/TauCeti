/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.SixJ

/-!
# The Biedenharn–Elliott pentagon identity for `U_q(sl₂)`

On a fourfold tensor product `((L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ) ⊗ L_d^θ` of signed ladder modules at a
generic parameter `q`, Mac Lane's pentagon coherence identity (`BialgebraModule.assoc_pentagon`)
equates the two-step and three-step composites of coproduct tensor associators landing in
`L_a^ε ⊗ (L_b^δ ⊗ (L_c^ζ ⊗ L_d^θ))`.

Composing with the normalized fourfold channel inclusions (`clebschGordanQuadLeftInclusion`) and
projections (`clebschGordanQuadRightProjection`) defines `quadRecouplingHom`. Evaluating it on
every ladder vector `v_l` (`l = 0` as well as `0 ≤ l ≤ e`) along both sides of `assoc_pentagon`
(`quadRecouplingHom_vec_eq_two_step` and `quadRecouplingHom_vec_eq_three_step`) yields the
channel-index pentagon identity (`recouplingCoeff_pentagon`) and the unconditional six-weight
**Biedenharn–Elliott pentagon identity** (`sixJ_pentagon`).

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapters VII and XII.
* A. N. Kirillov and N. Yu. Reshetikhin, *Representations of the algebra `U_q(sl(2))`,
  `q`-orthogonal polynomials and invariants of links*, World Scientific, 1989, pp. 285--339.
-/

public noncomputable section

namespace TauCeti.UqSl2

open BialgebraModule LadderModule

section QuadMaps

variable {q : ℂ} [Fact (q ≠ 0)] {a b c d : ℕ} {ε δ ζ θ : ℤˣ}

/-- Normalized inclusion of the `(i₁, i₂, i₃)` fully left-associated channel into
`((L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ) ⊗ L_d^θ`. -/
def clebschGordanQuadLeftInclusion (hq : IsGenericQuantumParameter q)
    (i₁ : Fin (min a b + 1)) (i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1))
    (i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1)) :
    LadderModule q (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) + d - 2 * (i₃ : ℕ))
        (((ε * δ) * ζ) * θ) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q)
        (Tensor ℂ (UqSl2 q)
          (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)) (LadderModule q c ζ))
        (LadderModule q d θ) :=
  (tensorMap ℂ (UqSl2 q) (clebschGordanLeftInclusion hq i₁ i₂) LinearMap.id).comp
    (clebschGordanInclusion hq i₃)

/-- Definitional composite formula for `clebschGordanQuadLeftInclusion`. -/
theorem clebschGordanQuadLeftInclusion_def (hq : IsGenericQuantumParameter q)
    (i₁ : Fin (min a b + 1)) (i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1))
    (i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1)) :
    clebschGordanQuadLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) (θ := θ) hq i₁ i₂ i₃ =
      (tensorMap ℂ (UqSl2 q) (clebschGordanLeftInclusion hq i₁ i₂) LinearMap.id).comp
        (clebschGordanInclusion hq i₃) := (rfl)

/-- Normalized projection of `L_a^ε ⊗ (L_b^δ ⊗ (L_c^ζ ⊗ L_d^θ))` onto its `(r₁, r₂, r₃)` fully
right-associated channel. -/
def clebschGordanQuadRightProjection (hq : IsGenericQuantumParameter q)
    (r₁ : Fin (min c d + 1)) (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) :
    Tensor ℂ (UqSl2 q) (LadderModule q a ε)
        (Tensor ℂ (UqSl2 q) (LadderModule q b δ)
          (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ))) →ₗ[UqSl2 q]
      LadderModule q (a + (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) - 2 * (r₃ : ℕ))
        (ε * (δ * (ζ * θ))) :=
  (clebschGordanRightProjection hq r₂ r₃).comp
    (tensorMap ℂ (UqSl2 q) LinearMap.id
      (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanProjection hq r₁)))

/-- Definitional composite formula for `clebschGordanQuadRightProjection`. -/
theorem clebschGordanQuadRightProjection_def (hq : IsGenericQuantumParameter q)
    (r₁ : Fin (min c d + 1)) (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) :
    clebschGordanQuadRightProjection (ε := ε) (δ := δ) (ζ := ζ) (θ := θ) hq r₁ r₂ r₃ =
      (clebschGordanRightProjection hq r₂ r₃).comp
        (tensorMap ℂ (UqSl2 q) LinearMap.id
          (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanProjection hq r₁))) := (rfl)

/-- The fourfold recoupling intertwiner from fully left-associated channel `(i₁, i₂, i₃)` to fully
right-associated channel `(r₁, r₂, r₃)` across `(assoc (A ⊗ B) C D).trans (assoc A B (C ⊗ D))`. -/
def quadRecouplingHom (hq : IsGenericQuantumParameter q)
    (i₁ : Fin (min a b + 1)) (i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1))
    (i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1))
    (r₁ : Fin (min c d + 1)) (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) :
    LadderModule q (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) + d - 2 * (i₃ : ℕ))
        (((ε * δ) * ζ) * θ) →ₗ[UqSl2 q]
      LadderModule q (a + (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) - 2 * (r₃ : ℕ))
        (ε * (δ * (ζ * θ))) :=
  (clebschGordanQuadRightProjection hq r₁ r₂ r₃).comp
    (((assoc ℂ (UqSl2 q)
        (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
        (LadderModule q c ζ) (LadderModule q d θ)).trans
      (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ)))).toLinearMap.comp
      (clebschGordanQuadLeftInclusion hq i₁ i₂ i₃))

/-- Definitional composite formula for `quadRecouplingHom`. -/
theorem quadRecouplingHom_def (hq : IsGenericQuantumParameter q)
    (i₁ : Fin (min a b + 1)) (i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1))
    (i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1))
    (r₁ : Fin (min c d + 1)) (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) :
    quadRecouplingHom (ε := ε) (δ := δ) (ζ := ζ) (θ := θ) hq i₁ i₂ i₃ r₁ r₂ r₃ =
      (clebschGordanQuadRightProjection hq r₁ r₂ r₃).comp
        (((assoc ℂ (UqSl2 q)
            (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
            (LadderModule q c ζ) (LadderModule q d θ)).trans
          (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
            (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ)))).toLinearMap.comp
          (clebschGordanQuadLeftInclusion hq i₁ i₂ i₃)) := (rfl)

/-- `clebschGordanQuadLeftInclusion` factors through `clebschGordanLeftInclusion` on the outer
triple `(L_{a+b-2i₁}^{ε*δ} ⊗ L_c^ζ) ⊗ L_d^θ`. -/
theorem clebschGordanQuadLeftInclusion_apply (hq : IsGenericQuantumParameter q)
    (i₁ : Fin (min a b + 1)) (i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1))
    (i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1))
    (v : LadderModule q (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) + d - 2 * (i₃ : ℕ))
      (((ε * δ) * ζ) * θ)) :
    clebschGordanQuadLeftInclusion hq i₁ i₂ i₃ v =
      tensorMap ℂ (UqSl2 q) (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i₁) LinearMap.id)
        LinearMap.id (clebschGordanLeftInclusion hq i₂ i₃ v) := by
  have hmap : tensorMap ℂ (UqSl2 q)
        (clebschGordanLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) hq i₁ i₂)
        (LinearMap.id : LadderModule q d θ →ₗ[UqSl2 q] _) =
      (tensorMap ℂ (UqSl2 q)
        (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i₁) LinearMap.id) LinearMap.id).comp
        (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i₂) LinearMap.id) := by
    rw [clebschGordanLeftInclusion_def, ← tensorMap_comp, LinearMap.id_comp]
  rw [clebschGordanQuadLeftInclusion_def, LinearMap.comp_apply, hmap, LinearMap.comp_apply,
    clebschGordanLeftInclusion_def, LinearMap.comp_apply]

/-- `clebschGordanQuadRightProjection` factors through `clebschGordanRightProjection` on the right
triple `L_b^δ ⊗ (L_c^ζ ⊗ L_d^θ)`. -/
theorem clebschGordanQuadRightProjection_apply (hq : IsGenericQuantumParameter q)
    (r₁ : Fin (min c d + 1)) (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1))
    (z : Tensor ℂ (UqSl2 q) (LadderModule q a ε)
      (Tensor ℂ (UqSl2 q) (LadderModule q b δ)
        (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ)))) :
    clebschGordanQuadRightProjection hq r₁ r₂ r₃ z =
      clebschGordanProjection hq r₃
        (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanRightProjection hq r₁ r₂) z) := by
  have hmap : (tensorMap ℂ (UqSl2 q) (LinearMap.id : LadderModule q a ε →ₗ[UqSl2 q] _)
        (clebschGordanProjection hq r₂)).comp
      (tensorMap ℂ (UqSl2 q) LinearMap.id
        (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanProjection hq r₁))) =
      tensorMap ℂ (UqSl2 q) LinearMap.id
        (clebschGordanRightProjection (ε := δ) (δ := ζ) (ζ := θ) hq r₁ r₂) := by
    rw [clebschGordanRightProjection_def, ← tensorMap_comp, LinearMap.id_comp]
  rw [clebschGordanQuadRightProjection_def, LinearMap.comp_apply,
    clebschGordanRightProjection_def, LinearMap.comp_apply, ← hmap, LinearMap.comp_apply]

/-- Evaluation of `quadRecouplingHom` on every ladder vector `v_l` along the two-step associator
path `((A ⊗ B) ⊗ C) ⊗ D → (A ⊗ B) ⊗ (C ⊗ D) → A ⊗ (B ⊗ (C ⊗ D))`. -/
theorem quadRecouplingHom_vec_eq_two_step (hq : IsGenericQuantumParameter q)
    (i₁ : Fin (min a b + 1)) (i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1))
    (i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1))
    (r₁ : Fin (min c d + 1)) (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) (l : ℤ) :
    quadRecouplingHom (ε := ε) (δ := δ) (ζ := ζ) (θ := θ) hq i₁ i₂ i₃ r₁ r₂ r₃ (vec q _ _ l) =
      (∑ p₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) (c + d - 2 * (r₁ : ℕ)) + 1),
        recouplingCoeff hq ε δ (ζ * θ) i₁ p₂ r₂ r₃ *
          recouplingCoeff hq (ε * δ) ζ θ i₂ i₃ r₁ p₂) • vec q _ _ l := by
  set e₂ := assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
    (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ))
  rw [quadRecouplingHom_def, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, ← e₂.coe_toLinearMap,
    clebschGordanQuadLeftInclusion_apply,
    ← tensorMap_tensorMap_assoc ℂ (UqSl2 q) (clebschGordanInclusion hq i₁) LinearMap.id
      LinearMap.id, tensorMap_id, assoc_clebschGordanLeftInclusion_vec hq i₂ i₃ l]
  simp only [map_sum, LinearMap.map_smul_of_tower, e₂.coe_toLinearMap]
  have hterm (p₁ : Fin (min c d + 1))
      (p₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) (c + d - 2 * (p₁ : ℕ)) + 1)) :
      clebschGordanQuadRightProjection hq r₁ r₂ r₃
          (e₂ (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i₁) LinearMap.id
            (clebschGordanRightInclusion hq p₁ p₂ (vec q _ _ l)))) =
        if hp₁ : p₁ = r₁ then recouplingCoeff hq ε δ (ζ * θ) i₁ (hp₁ ▸ p₂) r₂ r₃ • vec q _ _ l
        else 0 := by
    have hcomm : tensorMap ℂ (UqSl2 q) (clebschGordanInclusion (m := a) (n := b)
          (ε := ε) (δ := δ) hq i₁) LinearMap.id
          (clebschGordanRightInclusion (n := c) (p := d) (δ := ζ) (ζ := θ) hq p₁ p₂ (vec q _ _ l)) =
        tensorMap ℂ (UqSl2 q) (tensorMap ℂ (UqSl2 q) LinearMap.id LinearMap.id)
          (clebschGordanInclusion hq p₁) (clebschGordanLeftInclusion hq i₁ p₂ (vec q _ _ l)) := by
      have hmap : (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion (m := a) (n := b)
            (ε := ε) (δ := δ) hq i₁) LinearMap.id).comp
          (tensorMap ℂ (UqSl2 q) LinearMap.id
            (clebschGordanInclusion (m := c) (n := d) (ε := ζ) (δ := θ) hq p₁)) =
          (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq p₁)).comp
            (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i₁) LinearMap.id) := by
        rw [← tensorMap_comp, ← tensorMap_comp, LinearMap.comp_id, LinearMap.id_comp,
          LinearMap.id_comp, LinearMap.comp_id]
      rw [clebschGordanRightInclusion_def, LinearMap.comp_apply, ← LinearMap.comp_apply, hmap,
        LinearMap.comp_apply, tensorMap_id, clebschGordanLeftInclusion_def, LinearMap.comp_apply]
    have hpi (y : Tensor ℂ (UqSl2 q) (LadderModule q a ε)
        (Tensor ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q (c + d - 2 * (p₁ : ℕ)) (ζ * θ)))) :
        tensorMap ℂ (UqSl2 q) LinearMap.id
            (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanProjection hq r₁))
            (tensorMap ℂ (UqSl2 q) LinearMap.id (tensorMap ℂ (UqSl2 q) LinearMap.id
              (clebschGordanInclusion (m := c) (n := d) (ε := ζ) (δ := θ) hq p₁)) y) =
          tensorMap ℂ (UqSl2 q) LinearMap.id (tensorMap ℂ (UqSl2 q) LinearMap.id
            ((clebschGordanProjection (m := c) (n := d) (ε := ζ) (δ := θ) hq r₁).comp
              (clebschGordanInclusion hq p₁))) y := by
      rw [← LinearMap.comp_apply, ← tensorMap_comp, LinearMap.id_comp,
        ← tensorMap_comp, LinearMap.id_comp]
    rw [hcomm, ← tensorMap_tensorMap_assoc ℂ (UqSl2 q) LinearMap.id LinearMap.id
      (clebschGordanInclusion hq p₁), clebschGordanQuadRightProjection_def, LinearMap.comp_apply,
      hpi]
    split_ifs with hp₁
    · subst hp₁
      have hid : (clebschGordanProjection (m := c) (n := d) (ε := ζ) (δ := θ) hq p₁).comp
          (clebschGordanInclusion hq p₁) = LinearMap.id :=
        LinearMap.ext (clebschGordanProjection_inclusion_self hq p₁)
      rw [hid, tensorMap_id, tensorMap_id, LinearMap.id_apply, ← LinearEquiv.coe_toLinearMap,
        ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.comp_assoc,
        ← recouplingHom_def, recouplingHom_vec]
    · have hzero : (clebschGordanProjection (m := c) (n := d) (ε := ζ) (δ := θ) hq r₁).comp
          (clebschGordanInclusion hq p₁) = 0 :=
        LinearMap.ext fun x => clebschGordanProjection_inclusion_of_ne hq (Ne.symm hp₁) x
      rw [hzero, tensorMap_zero_right, tensorMap_zero_right, LinearMap.zero_apply, map_zero]
  simp_rw [hterm]
  rw [Finset.sum_eq_single r₁ (fun p₁ _ hp₁ => by simp [hp₁]) (by simp)]
  simp only [↓reduceDIte, smul_smul, ← Finset.sum_smul]
  exact congrArg (· • vec q _ _ l) (Finset.sum_congr rfl fun _ _ => mul_comm _ _)

private theorem tensorMap_hom_id_clebschGordanInclusion_vec (hq : IsGenericQuantumParameter q)
    {w w' d : ℕ} {σ σ' θ : ℤˣ} (hw : w = w') (hσ : σ = σ')
    (f : LadderModule q w σ →ₗ[UqSl2 q] LadderModule q w' σ') (j : Fin (min w d + 1)) (l : ℤ) :
    tensorMap ℂ (UqSl2 q) f (LinearMap.id : LadderModule q d θ →ₗ[UqSl2 q] _)
        (clebschGordanInclusion hq j (vec q _ _ l)) =
      schurScalar f • clebschGordanInclusion hq ⟨j, by rw [← hw]; exact j.isLt⟩ (vec q _ _ l) := by
  subst hw hσ; rw [tensorMap_clebschGordanInclusion hq f LinearMap.id j, schurScalar_id, mul_one]

/-- Evaluation of `quadRecouplingHom` on every ladder vector `v_l` along the three-step associator
path `((A ⊗ B) ⊗ C) ⊗ D → (A ⊗ (B ⊗ C)) ⊗ D → A ⊗ ((B ⊗ C) ⊗ D) → A ⊗ (B ⊗ (C ⊗ D))` via
`BialgebraModule.assoc_pentagon_apply`. -/
theorem quadRecouplingHom_vec_eq_three_step (hq : IsGenericQuantumParameter q)
    (i₁ : Fin (min a b + 1)) (i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1))
    (i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1))
    (r₁ : Fin (min c d + 1)) (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) (l : ℤ) :
    quadRecouplingHom (ε := ε) (δ := δ) (ζ := ζ) (θ := θ) hq i₁ i₂ i₃ r₁ r₂ r₃ (vec q _ _ l) =
      (∑ q₁ : Fin (min b c + 1), ∑ q₂ : Fin (min a (b + c - 2 * (q₁ : ℕ)) + 1),
        if hw : a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) =
            a + (b + c - 2 * (q₁ : ℕ)) - 2 * (q₂ : ℕ) then
          ∑ p₁ : Fin (min (b + c - 2 * (q₁ : ℕ)) d + 1),
            ∑ p₂ : Fin (min a (b + c - 2 * (q₁ : ℕ) + d - 2 * (p₁ : ℕ)) + 1),
              if (p₂ : ℕ) = (r₃ : ℕ) then
                recouplingCoeff hq δ ζ θ q₁ p₁ r₁ r₂ *
                  recouplingCoeff hq ε (δ * ζ) θ q₂ ⟨i₃, by rw [← hw]; exact i₃.isLt⟩ p₁ p₂ *
                  recouplingCoeff hq ε δ ζ i₁ i₂ q₁ q₂
              else 0
        else 0) • vec q _ _ l := by
  rw [quadRecouplingHom_def, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, assoc_pentagon_apply]
  have hinner : tensorMap ℂ (UqSl2 q)
        (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
          (LadderModule q c ζ)).toLinearMap LinearMap.id
        (clebschGordanQuadLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) (θ := θ) hq i₁ i₂ i₃
          (vec q _ _ l)) =
      ∑ q₁ : Fin (min b c + 1), ∑ q₂ : Fin (min a (b + c - 2 * (q₁ : ℕ)) + 1),
        tensorMap ℂ (UqSl2 q)
          ((clebschGordanRightInclusion hq q₁ q₂).comp (recouplingHom hq i₁ i₂ q₁ q₂))
          LinearMap.id (clebschGordanInclusion hq i₃ (vec q _ _ l)) := by
    rw [clebschGordanQuadLeftInclusion_def, LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← tensorMap_comp, LinearMap.id_comp, assoc_comp_clebschGordanLeftInclusion hq i₁ i₂,
      tensorMap_sum_left]
    simp only [tensorMap_sum_left, LinearMap.sum_apply]
  rw [hinner, Finset.sum_smul]; simp_rw [Finset.sum_smul]; simp only [map_sum]
  refine Finset.sum_congr rfl fun q₁ _ => Finset.sum_congr rfl fun q₂ _ => ?_
  split_ifs with hw
  · have hsplit : tensorMap ℂ (UqSl2 q)
          ((clebschGordanRightInclusion (m := a) (n := b) (p := c)
              (ε := ε) (δ := δ) (ζ := ζ) hq q₁ q₂).comp (recouplingHom hq i₁ i₂ q₁ q₂))
          (LinearMap.id : LadderModule q d θ →ₗ[UqSl2 q] _)
          (clebschGordanInclusion hq i₃ (vec q _ _ l)) =
        recouplingCoeff hq ε δ ζ i₁ i₂ q₁ q₂ •
          tensorMap ℂ (UqSl2 q)
            (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq q₁)) LinearMap.id
            (clebschGordanLeftInclusion hq q₂ ⟨i₃, by rw [← hw]; exact i₃.isLt⟩
              (vec q _ _ l)) := by
      have hcomp1 : tensorMap ℂ (UqSl2 q)
            ((clebschGordanRightInclusion (m := a) (n := b) (p := c)
                (ε := ε) (δ := δ) (ζ := ζ) hq q₁ q₂).comp (recouplingHom hq i₁ i₂ q₁ q₂))
            (LinearMap.id : LadderModule q d θ →ₗ[UqSl2 q] _) =
          (tensorMap ℂ (UqSl2 q) (clebschGordanRightInclusion hq q₁ q₂) LinearMap.id).comp
            (tensorMap ℂ (UqSl2 q) (recouplingHom hq i₁ i₂ q₁ q₂) LinearMap.id) := by
        rw [← tensorMap_comp, LinearMap.id_comp]
      have hcomp2 : tensorMap ℂ (UqSl2 q)
            (clebschGordanRightInclusion (m := a) (n := b) (p := c)
              (ε := ε) (δ := δ) (ζ := ζ) hq q₁ q₂)
            (LinearMap.id : LadderModule q d θ →ₗ[UqSl2 q] _) =
          (tensorMap ℂ (UqSl2 q)
            (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq q₁))
            LinearMap.id).comp
            (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq q₂) LinearMap.id) := by
        rw [clebschGordanRightInclusion_def, ← tensorMap_comp, LinearMap.id_comp]
      rw [hcomp1, LinearMap.comp_apply,
        tensorMap_hom_id_clebschGordanInclusion_vec hq hw (mul_assoc ε δ ζ)
          (recouplingHom hq i₁ i₂ q₁ q₂) i₃ l,
        LinearMap.map_smul_of_tower, hcomp2, LinearMap.comp_apply,
        clebschGordanLeftInclusion_def, LinearMap.comp_apply, ← recouplingCoeff_def]
    rw [hsplit, ← LinearEquiv.coe_toLinearMap, LinearMap.map_smul_of_tower,
      LinearEquiv.coe_toLinearMap,
      ← tensorMap_tensorMap_assoc ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq q₁)
        LinearMap.id,
      assoc_clebschGordanLeftInclusion_vec hq q₂ ⟨i₃, by rw [← hw]; exact i₃.isLt⟩ l]
    simp only [map_sum, LinearMap.map_smul_of_tower]
    have hpterm (p₁ : Fin (min (b + c - 2 * (q₁ : ℕ)) d + 1))
        (p₂ : Fin (min a (b + c - 2 * (q₁ : ℕ) + d - 2 * (p₁ : ℕ)) + 1)) :
        clebschGordanQuadRightProjection hq r₁ r₂ r₃
            (tensorMap ℂ (UqSl2 q) LinearMap.id
              (assoc ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)
                (LadderModule q d θ)).toLinearMap
              (tensorMap ℂ (UqSl2 q) LinearMap.id
                (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq q₁) LinearMap.id)
                (clebschGordanRightInclusion (ε := ε) hq p₁ p₂ (vec q _ _ l)))) =
          (if (p₂ : ℕ) = (r₃ : ℕ) then recouplingCoeff hq δ ζ θ q₁ p₁ r₁ r₂ else 0) •
            vec q _ _ l := by
      have hchain : tensorMap ℂ (UqSl2 q) (LinearMap.id : LadderModule q a ε →ₗ[UqSl2 q] _)
            (clebschGordanRightProjection (ε := δ) (δ := ζ) (ζ := θ) hq r₁ r₂)
            (tensorMap ℂ (UqSl2 q) LinearMap.id
              (assoc ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)
                (LadderModule q d θ)).toLinearMap
              (tensorMap ℂ (UqSl2 q) LinearMap.id
                (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq q₁) LinearMap.id)
                (clebschGordanRightInclusion (ε := ε) hq p₁ p₂ (vec q _ _ l)))) =
          tensorMap ℂ (UqSl2 q) LinearMap.id
            (recouplingHom (ε := δ) (δ := ζ) (ζ := θ) hq q₁ p₁ r₁ r₂)
            (clebschGordanInclusion hq p₂ (vec q _ _ l)) := by
        rw [clebschGordanRightInclusion_def, LinearMap.comp_apply,
          ← LinearMap.comp_apply, ← tensorMap_comp, LinearMap.id_comp,
          ← LinearMap.comp_apply, ← tensorMap_comp, LinearMap.id_comp,
          ← LinearMap.comp_apply, ← tensorMap_comp, LinearMap.id_comp]
        congr 2
        simp only [recouplingHom_def, clebschGordanLeftInclusion_def, LinearMap.comp_assoc]
      rw [clebschGordanQuadRightProjection_apply, hchain,
        clebschGordanProjection_tensorMap_inclusion_vec hq LinearMap.id
          (recouplingHom hq q₁ p₁ r₁ r₂) p₂ r₃ l,
        schurScalar_id, one_mul, ← recouplingCoeff_def]
    simp_rw [hpterm, smul_smul, ← Finset.sum_smul, smul_smul]
    congr 1; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => ?_; split_ifs <;> ring
  · rw [hom_eq_zero_of_ne hq (.inl hw) (recouplingHom hq i₁ i₂ q₁ q₂), LinearMap.comp_zero,
      tensorMap_zero_left, LinearMap.zero_apply, map_zero, map_zero, map_zero, zero_smul]

end QuadMaps

/-! ### Channel-index and six-weight Biedenharn–Elliott pentagon identities -/

section PentagonIdentities

variable {q : ℂ}

/-- **Index-form pentagon identity** for `recouplingCoeff` across all fourfold left-associated
channels `(i₁, i₂, i₃)` and right-associated channels `(r₁, r₂, r₃)`. -/
theorem recouplingCoeff_pentagon (hq : IsGenericQuantumParameter q) (ε δ ζ θ : ℤˣ) {a b c d : ℕ}
    (i₁ : Fin (min a b + 1)) (i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1))
    (i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1))
    (r₁ : Fin (min c d + 1)) (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) :
    (∑ p₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) (c + d - 2 * (r₁ : ℕ)) + 1),
        recouplingCoeff hq ε δ (ζ * θ) i₁ p₂ r₂ r₃ *
          recouplingCoeff hq (ε * δ) ζ θ i₂ i₃ r₁ p₂) =
      ∑ q₁ : Fin (min b c + 1), ∑ q₂ : Fin (min a (b + c - 2 * (q₁ : ℕ)) + 1),
        if hw : a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) =
            a + (b + c - 2 * (q₁ : ℕ)) - 2 * (q₂ : ℕ) then
          ∑ p₁ : Fin (min (b + c - 2 * (q₁ : ℕ)) d + 1),
            ∑ p₂ : Fin (min a (b + c - 2 * (q₁ : ℕ) + d - 2 * (p₁ : ℕ)) + 1),
              if (p₂ : ℕ) = (r₃ : ℕ) then
                recouplingCoeff hq δ ζ θ q₁ p₁ r₁ r₂ *
                  recouplingCoeff hq ε (δ * ζ) θ q₂ ⟨i₃, by rw [← hw]; exact i₃.isLt⟩ p₁ p₂ *
                  recouplingCoeff hq ε δ ζ i₁ i₂ q₁ q₂
              else 0
        else 0 := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have hvec := (quadRecouplingHom_vec_eq_two_step (ε := ε) (δ := δ) (ζ := ζ) (θ := θ)
    hq i₁ i₂ i₃ r₁ r₂ r₃ 0).symm.trans
    (quadRecouplingHom_vec_eq_three_step (ε := ε) (δ := δ) (ζ := ζ) (θ := θ) hq i₁ i₂ i₃ r₁ r₂ r₃ 0)
  have hrepr := congrArg
    (fun v => (basis q (a + (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) - 2 * (r₃ : ℕ))
      (ε * (δ * (ζ * θ)))).repr v 0) hvec
  simpa only [map_smul, Finsupp.smul_apply, basis_repr_vec, Fin.val_zero, Nat.cast_zero,
    ↓reduceIte, smul_eq_mul, mul_one] using hrepr

/-- **The Biedenharn–Elliott pentagon identity** for the quantum 6j symbols `sixJ` of `U_q(sl₂)`
across all signed ladder modules `L_a^ε ⊗ L_b^δ ⊗ L_c^ζ ⊗ L_d^θ` at generic `q`. -/
theorem sixJ_pentagon (hq : IsGenericQuantumParameter q) (ε δ ζ θ : ℤˣ)
    (a b c d e u w x y : ℕ) :
    sixJ hq ε δ (ζ * θ) a b y e u x * sixJ hq (ε * δ) ζ θ u c d e w y =
      ∑ z ∈ Finset.range (b + c + 1),
        sixJ hq δ ζ θ b c d x z y *
          sixJ hq ε (δ * ζ) θ a z d e w x *
          sixJ hq ε δ ζ a b c w u z := by
  by_cases hadm : IsClebschGordanChannel a b u ∧ IsClebschGordanChannel u c w ∧
      IsClebschGordanChannel w d e ∧ IsClebschGordanChannel c d y ∧
      IsClebschGordanChannel b y x ∧ IsClebschGordanChannel a x e
  · rcases hadm with ⟨hab, huc, hwd, hcd, hby, hax⟩
    set i₁ := hab.index
    set i₂ := huc.leftIndex hab
    have hw_eq : a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) = w := by
      rw [huc.val_leftIndex, hab.sub_two_mul_index, huc.sub_two_mul_index]
    set i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1) :=
      ⟨hwd.index, by rw [hw_eq]; exact hwd.index.isLt⟩
    set r₁ := hcd.index
    set r₂ := hby.rightIndex hcd
    have hx_eq : b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ) = x := by
      rw [hby.val_rightIndex, hcd.sub_two_mul_index, hby.sub_two_mul_index]
    set r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1) :=
      ⟨hax.index, by rw [hx_eq]; exact hax.index.isLt⟩
    have he_left : a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) + d - 2 * (i₃ : ℕ) = e := by
      change a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) + d - 2 * (hwd.index : ℕ) = e
      rw [hw_eq, hwd.sub_two_mul_index]
    have hpent := recouplingCoeff_pentagon hq ε δ ζ θ i₁ i₂ i₃ r₁ r₂ r₃
    have hlhs :
        (∑ p₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) (c + d - 2 * (r₁ : ℕ)) + 1),
          recouplingCoeff hq ε δ (ζ * θ) i₁ p₂ r₂ r₃ *
            recouplingCoeff hq (ε * δ) ζ θ i₂ i₃ r₁ p₂) =
        sixJ hq ε δ (ζ * θ) a b y e u x * sixJ hq (ε * δ) ζ θ u c d e w y := by
      by_cases huy : IsClebschGordanChannel u y e
      · set p₂₀ : Fin (min (a + b - 2 * (i₁ : ℕ)) (c + d - 2 * (r₁ : ℕ)) + 1) :=
          ⟨huy.index, by rw [hab.sub_two_mul_index, hcd.sub_two_mul_index]; exact huy.index.isLt⟩
        rw [Finset.sum_eq_single p₂₀]
        · have he_uy : a + b - 2 * (i₁ : ℕ) + (c + d - 2 * (r₁ : ℕ)) - 2 * (p₂₀ : ℕ) = e := by
            change a + b - 2 * (i₁ : ℕ) + (c + d - 2 * (r₁ : ℕ)) - 2 * (huy.index : ℕ) = e
            rw [hab.sub_two_mul_index, hcd.sub_two_mul_index, huy.sub_two_mul_index]
          have he_right : a + (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) - 2 * (r₃ : ℕ) = e := by
            change a + (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) - 2 * (hax.index : ℕ) = e
            rw [hx_eq, hax.sub_two_mul_index]
          have hf₁ : recouplingCoeff hq ε δ (ζ * θ) i₁ p₂₀ r₂ r₃ =
              sixJ hq ε δ (ζ * θ) a b y e u x := by
            rw [recouplingCoeff_eq_ite, ite_eq_left (he_uy.trans he_right.symm), he_uy, hx_eq,
              hab.sub_two_mul_index, hcd.sub_two_mul_index]
          have hf₂ : recouplingCoeff hq (ε * δ) ζ θ i₂ i₃ r₁ p₂₀ =
              sixJ hq (ε * δ) ζ θ u c d e w y := by
            rw [recouplingCoeff_eq_ite, ite_eq_left (he_left.trans he_uy.symm), he_left, hw_eq,
              hab.sub_two_mul_index, hcd.sub_two_mul_index]
          rw [hf₁, hf₂]
        · intro p₂ _ hp₂
          have hne : a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) + d - 2 * (i₃ : ℕ) ≠
              a + b - 2 * (i₁ : ℕ) + (c + d - 2 * (r₁ : ℕ)) - 2 * (p₂ : ℕ) := by
            have := hab.sub_two_mul_index; have := hcd.sub_two_mul_index
            have := huy.sub_two_mul_index; have := huy.index.isLt; have := p₂.isLt
            have hp₂' : (p₂ : ℕ) ≠ (huy.index : ℕ) := fun h => hp₂ (Fin.ext h)
            omega
          rw [recouplingCoeff_eq_zero_of_ne hq (ε * δ) ζ θ hne, mul_zero]
        · simp
      · rw [sixJ_eq_zero_of_not hq ε δ (ζ * θ) (fun h => huy h.1.2), zero_mul]
        refine Finset.sum_eq_zero fun p₂ _ => ?_
        have hne : a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) + d - 2 * (i₃ : ℕ) ≠
            a + b - 2 * (i₁ : ℕ) + (c + d - 2 * (r₁ : ℕ)) - 2 * (p₂ : ℕ) := fun heq => by
          have := hab.sub_two_mul_index; have := hcd.sub_two_mul_index; have := p₂.isLt
          exact huy (isClebschGordanChannel_def.mpr ⟨⟨p₂, by omega⟩, by dsimp only; omega⟩)
        rw [recouplingCoeff_eq_zero_of_ne hq (ε * δ) ζ θ hne, mul_zero]
    rw [← hlhs, hpent, ← sum_fin_channel_eq_sum_range b c _ fun z hbc => by
      rw [sixJ_eq_zero_of_not hq δ ζ θ (fun h => hbc h.1.1), zero_mul, zero_mul]]
    refine Finset.sum_congr rfl fun q₁ _ => ?_
    set z := b + c - 2 * (q₁ : ℕ)
    have hbc : IsClebschGordanChannel b c z := isClebschGordanChannel_sub_two_mul q₁
    have hbc_idx : (hbc.index : ℕ) = (q₁ : ℕ) := congrArg Fin.val (hbc.index_eq_of_eq rfl)
    by_cases haz : IsClebschGordanChannel a z w
    · rw [Finset.sum_eq_single haz.index]
      · have hw_az : a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) = a + z - 2 * (haz.index : ℕ) := by
          rw [hw_eq, haz.sub_two_mul_index]
        rw [dite_eq_left hw_az]
        by_cases hzd : IsClebschGordanChannel z d x
        · rw [Finset.sum_eq_single hzd.index]
          · set p₂₀ : Fin (min a (z + d - 2 * (hzd.index : ℕ)) + 1) :=
              ⟨hax.index, by rw [hzd.sub_two_mul_index]; exact hax.index.isLt⟩
            rw [Finset.sum_eq_single p₂₀]
            · have hp₂_eq : (p₂₀ : ℕ) = (r₃ : ℕ) := rfl
              have hi₃ : (⟨i₃, by rw [← hw_az]; exact i₃.isLt⟩ :
                  Fin (min (a + z - 2 * (haz.index : ℕ)) d + 1)).val = (hwd.index : ℕ) := rfl
              rw [ite_eq_left hp₂_eq,
                sixJ_eq_recouplingCoeff hq δ ζ θ ⟨hbc, hzd⟩ ⟨hcd, hby⟩,
                sixJ_eq_recouplingCoeff hq ε (δ * ζ) θ ⟨haz, hwd⟩ ⟨hzd, hax⟩,
                sixJ_eq_recouplingCoeff hq ε δ ζ ⟨hab, huc⟩ ⟨hbc, haz⟩]
              exact congrArg₂ (· * ·)
                (congrArg₂ (· * ·)
                  (recouplingCoeff_congr hq δ ζ θ hbc_idx.symm (hzd.val_leftIndex hbc).symm
                    rfl rfl)
                  (recouplingCoeff_congr hq ε (δ * ζ) θ rfl
                    (hi₃.trans (hwd.val_leftIndex haz).symm) rfl
                    (hax.val_rightIndex hzd).symm))
                (recouplingCoeff_congr hq ε δ ζ rfl rfl hbc_idx.symm
                  (haz.val_rightIndex hbc).symm)
            · exact fun p₂ _ hp₂ => ite_eq_right fun heq => hp₂ (Fin.ext heq)
            · simp
          · intro p₁ _ hp₁
            refine Finset.sum_eq_zero fun _ _ => ?_
            have hne : z + d - 2 * (p₁ : ℕ) ≠ b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ) := by
              rw [hx_eq]; exact fun heq => hp₁ (hzd.index_eq_of_eq heq).symm
            rw [recouplingCoeff_eq_zero_of_ne hq δ ζ θ hne, zero_mul, zero_mul, ite_self]
          · simp
        · rw [sixJ_eq_zero_of_not hq δ ζ θ (fun h => hzd h.1.2), zero_mul, zero_mul]
          refine Finset.sum_eq_zero fun p₁ _ => Finset.sum_eq_zero fun _ _ => ?_
          have hne : z + d - 2 * (p₁ : ℕ) ≠ b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ) := by
            rw [hx_eq]; exact fun heq => hzd (isClebschGordanChannel_def.mpr ⟨p₁, heq⟩)
          rw [recouplingCoeff_eq_zero_of_ne hq δ ζ θ hne, zero_mul, zero_mul, ite_self]
      · intro q₂ _ hq₂
        exact dite_eq_right
          (by rw [hw_eq]; exact fun heq => hq₂ (haz.index_eq_of_eq heq.symm).symm)
      · simp
    · rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => haz h.2.2), mul_zero]
      exact Finset.sum_eq_zero fun q₂ _ => dite_eq_right
        (by rw [hw_eq]; exact fun heq => haz (isClebschGordanChannel_def.mpr ⟨q₂, heq.symm⟩))
  · have hlhs0 : sixJ hq ε δ (ζ * θ) a b y e u x * sixJ hq (ε * δ) ζ θ u c d e w y = 0 := by
      by_cases h1 : (IsClebschGordanChannel a b u ∧ IsClebschGordanChannel u y e) ∧
          (IsClebschGordanChannel b y x ∧ IsClebschGordanChannel a x e)
      · rw [sixJ_eq_zero_of_not hq (ε * δ) ζ θ (fun h2 => hadm ⟨h1.1.1, h2.1.1, h2.1.2,
          h2.2.1, h1.2.1, h1.2.2⟩), mul_zero]
      · rw [sixJ_eq_zero_of_not hq ε δ (ζ * θ) h1, zero_mul]
    rw [hlhs0]; symm; refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h1 : (IsClebschGordanChannel b c z ∧ IsClebschGordanChannel z d x) ∧
        (IsClebschGordanChannel c d y ∧ IsClebschGordanChannel b y x)
    · by_cases h2 : (IsClebschGordanChannel a z w ∧ IsClebschGordanChannel w d e) ∧
          (IsClebschGordanChannel z d x ∧ IsClebschGordanChannel a x e)
      · rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h3 => hadm ⟨h3.1.1, h3.1.2, h2.1.2,
          h1.2.1, h1.2.2, h2.2.2⟩), mul_zero]
      · rw [sixJ_eq_zero_of_not hq ε (δ * ζ) θ h2, mul_zero, zero_mul]
    · rw [sixJ_eq_zero_of_not hq δ ζ θ h1, zero_mul, zero_mul]

end PentagonIdentities

end TauCeti.UqSl2

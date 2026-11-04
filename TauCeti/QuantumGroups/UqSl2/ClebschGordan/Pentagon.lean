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

Composing with the normalized fourfold inclusions (`clebschGordanQuadLeftInclusion`) and projections
(`clebschGordanQuadRightProjection`) defines `quadRecouplingHom`. Evaluating it on `v_l` along both
sides of `assoc_pentagon` yields the index-form identity (`recouplingCoeff_pentagon`) and the
unconditional six-weight **Biedenharn–Elliott pentagon identity** (`sixJ_pentagon`) for the `α₀ = 1`
change-of-decomposition (`F`-matrix) entries `sixJ` of `clebschGordanInclusion` (rather than the
rescaled, tetrahedrally symmetric Racah/Kirillov–Reshetikhin 6j symbol).

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapters VII and XII.
* A. N. Kirillov and N. Yu. Reshetikhin, *Representations of the algebra `U_q(sl(2))`,
  `q`-orthogonal polynomials and invariants of links*, World Scientific, 1989, pp. 285--339
  (for the quantum recoupling pentagon relation, up to basis rescaling).
-/

public noncomputable section

namespace TauCeti.UqSl2

open BialgebraModule LadderModule

section QuadMaps

variable {q : ℂ} [Fact (q ≠ 0)] {a b c d : ℕ} {ε δ ζ θ : ℤˣ}

/-- Normalized inclusion of the `(i₁, i₂, i₃)` fully left-associated channel into
`((L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ) ⊗ L_d^θ`. -/
def clebschGordanQuadLeftInclusion (hq : IsGenericQuantumParameter q) (i₁ : Fin (min a b + 1))
    (i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1))
    (i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1)) :
    LadderModule q (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) + d - 2 * (i₃ : ℕ))
        (((ε * δ) * ζ) * θ) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q) (Tensor ℂ (UqSl2 q)
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
def clebschGordanQuadRightProjection (hq : IsGenericQuantumParameter q) (r₁ : Fin (min c d + 1))
    (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) :
    Tensor ℂ (UqSl2 q) (LadderModule q a ε) (Tensor ℂ (UqSl2 q) (LadderModule q b δ)
        (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ))) →ₗ[UqSl2 q]
      LadderModule q (a + (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) - 2 * (r₃ : ℕ))
        (ε * (δ * (ζ * θ))) :=
  (clebschGordanRightProjection hq r₂ r₃).comp (tensorMap ℂ (UqSl2 q) LinearMap.id
    (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanProjection hq r₁)))

/-- Definitional composite formula for `clebschGordanQuadRightProjection`. -/
theorem clebschGordanQuadRightProjection_def (hq : IsGenericQuantumParameter q)
    (r₁ : Fin (min c d + 1)) (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) :
    clebschGordanQuadRightProjection (ε := ε) (δ := δ) (ζ := ζ) (θ := θ) hq r₁ r₂ r₃ =
      (clebschGordanRightProjection hq r₂ r₃).comp (tensorMap ℂ (UqSl2 q) LinearMap.id
        (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanProjection hq r₁))) := (rfl)

/-- Fourfold recoupling intertwiner from left channel `(i₁, i₂, i₃)` to right channel
`(r₁, r₂, r₃)` across `(assoc (A ⊗ B) C D).trans (assoc A B (C ⊗ D))`. -/
def quadRecouplingHom (hq : IsGenericQuantumParameter q) (i₁ : Fin (min a b + 1))
    (i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1))
    (i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1)) (r₁ : Fin (min c d + 1))
    (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) :
    LadderModule q (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) + d - 2 * (i₃ : ℕ))
        (((ε * δ) * ζ) * θ) →ₗ[UqSl2 q]
      LadderModule q (a + (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) - 2 * (r₃ : ℕ))
        (ε * (δ * (ζ * θ))) :=
  (clebschGordanQuadRightProjection hq r₁ r₂ r₃).comp
    (((assoc ℂ (UqSl2 q) (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
        (LadderModule q c ζ) (LadderModule q d θ)).trans
      (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ)))).toLinearMap.comp
      (clebschGordanQuadLeftInclusion hq i₁ i₂ i₃))

/-- Definitional composite formula for `quadRecouplingHom`. -/
theorem quadRecouplingHom_def (hq : IsGenericQuantumParameter q) (i₁ : Fin (min a b + 1))
    (i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1))
    (i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1)) (r₁ : Fin (min c d + 1))
    (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) :
    quadRecouplingHom (ε := ε) (δ := δ) (ζ := ζ) (θ := θ) hq i₁ i₂ i₃ r₁ r₂ r₃ =
      (clebschGordanQuadRightProjection hq r₁ r₂ r₃).comp
        (((assoc ℂ (UqSl2 q) (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
            (LadderModule q c ζ) (LadderModule q d θ)).trans
          (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
            (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ)))).toLinearMap.comp
          (clebschGordanQuadLeftInclusion hq i₁ i₂ i₃)) := (rfl)

/-- `clebschGordanQuadLeftInclusion` factors through `clebschGordanLeftInclusion` on `(i₂, i₃)`. -/
theorem clebschGordanQuadLeftInclusion_apply (hq : IsGenericQuantumParameter q)
    (i₁ : Fin (min a b + 1)) (i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1))
    (i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1))
    (v : LadderModule q (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) + d - 2 * (i₃ : ℕ))
      (((ε * δ) * ζ) * θ)) :
    clebschGordanQuadLeftInclusion hq i₁ i₂ i₃ v =
      tensorMap ℂ (UqSl2 q) (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i₁) LinearMap.id)
        LinearMap.id (clebschGordanLeftInclusion hq i₂ i₃ v) := by
  symm; rw [clebschGordanLeftInclusion_def, LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← tensorMap_comp, LinearMap.id_comp, ← clebschGordanLeftInclusion_def,
    ← LinearMap.comp_apply, ← clebschGordanQuadLeftInclusion_def]

/-- `clebschGordanQuadRightProjection` factors through `clebschGordanRightProjection`. -/
theorem clebschGordanQuadRightProjection_apply (hq : IsGenericQuantumParameter q)
    (r₁ : Fin (min c d + 1)) (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1))
    (z : Tensor ℂ (UqSl2 q) (LadderModule q a ε) (Tensor ℂ (UqSl2 q) (LadderModule q b δ)
      (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ)))) :
    clebschGordanQuadRightProjection hq r₁ r₂ r₃ z =
      clebschGordanProjection hq r₃
        (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanRightProjection hq r₁ r₂) z) := by
  rw [clebschGordanQuadRightProjection_def, clebschGordanRightProjection_def, LinearMap.comp_assoc,
    ← tensorMap_comp ℂ (UqSl2 q) LinearMap.id LinearMap.id, LinearMap.id_comp,
    ← clebschGordanRightProjection_def, LinearMap.comp_apply]

/-- Projecting the reassociated `(L_a^ε ⊗ L_b^δ) ⊗ (L_c^ζ ⊗ L_d^θ)` channel `(i₁, p₁, p₂)` onto
right channel `(r₁, r₂, r₃)` extracts `recouplingCoeff` when `p₁ = r₁` and `0` otherwise. -/
theorem clebschGordanQuadRightProjection_assoc_vec (hq : IsGenericQuantumParameter q)
    (i₁ : Fin (min a b + 1)) (p₁ : Fin (min c d + 1))
    (p₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) (c + d - 2 * (p₁ : ℕ)) + 1))
    (r₁ : Fin (min c d + 1)) (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) (l : ℤ) :
    clebschGordanQuadRightProjection (ε := ε) (δ := δ) (ζ := ζ) (θ := θ) hq r₁ r₂ r₃
        (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
          (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ))
          (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i₁) LinearMap.id
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
  rw [hcomm, ← tensorMap_tensorMap_assoc ℂ (UqSl2 q) LinearMap.id LinearMap.id
    (clebschGordanInclusion hq p₁), clebschGordanQuadRightProjection_def, ← LinearMap.comp_apply,
    LinearMap.comp_assoc, ← tensorMap_comp, ← tensorMap_comp, LinearMap.id_comp,
    LinearMap.id_comp, LinearMap.comp_apply]
  split_ifs with hp₁
  · subst hp₁; rw [clebschGordanProjection_comp_inclusion_self, tensorMap_id, tensorMap_id,
      LinearMap.id_apply, ← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply,
      ← LinearMap.comp_apply, LinearMap.comp_assoc, ← recouplingHom_def, recouplingHom_vec]
  · rw [clebschGordanProjection_comp_inclusion_of_ne hq (Ne.symm hp₁),
      tensorMap_zero_right, tensorMap_zero_right, LinearMap.zero_apply, map_zero]

/-- Evaluation of `quadRecouplingHom` on every ladder vector `v_l` along the two-step associator
path `((A ⊗ B) ⊗ C) ⊗ D → (A ⊗ B) ⊗ (C ⊗ D) → A ⊗ (B ⊗ (C ⊗ D))`. -/
theorem quadRecouplingHom_vec_eq_sum_recouplingCoeff_mul_smul (hq : IsGenericQuantumParameter q)
    (i₁ : Fin (min a b + 1)) (i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1))
    (i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1)) (r₁ : Fin (min c d + 1))
    (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) (l : ℤ) :
    quadRecouplingHom (ε := ε) (δ := δ) (ζ := ζ) (θ := θ) hq i₁ i₂ i₃ r₁ r₂ r₃ (vec q _ _ l) =
      (∑ p₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) (c + d - 2 * (r₁ : ℕ)) + 1),
        recouplingCoeff hq ε δ (ζ * θ) i₁ p₂ r₂ r₃ *
          recouplingCoeff hq (ε * δ) ζ θ i₂ i₃ r₁ p₂) • vec q _ _ l := by
  -- First associator step `((A ⊗ B) ⊗ C) ⊗ D → (A ⊗ B) ⊗ (C ⊗ D)` expands `(i₂, i₃)`.
  rw [quadRecouplingHom_def, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, clebschGordanQuadLeftInclusion_apply,
    ← tensorMap_tensorMap_assoc ℂ (UqSl2 q) (clebschGordanInclusion hq i₁) LinearMap.id
      LinearMap.id, tensorMap_id, assoc_clebschGordanLeftInclusion_vec hq i₂ i₃ l]
  -- Second associator step `(A ⊗ B) ⊗ (C ⊗ D) → A ⊗ (B ⊗ (C ⊗ D))` projects onto `p₁ = r₁`.
  simp only [← LinearEquiv.coe_toLinearMap, map_sum, LinearMap.map_smul_of_tower]
  simp only [LinearEquiv.coe_toLinearMap, clebschGordanQuadRightProjection_assoc_vec]
  rw [Finset.sum_eq_single r₁ (fun p₁ _ hp₁ => by simp [hp₁]) (by simp)]
  simp only [↓reduceDIte, smul_smul, ← Finset.sum_smul]
  exact congrArg (· • vec q _ _ l) (Finset.sum_congr rfl fun _ _ => mul_comm _ _)

/-- Projecting the third-step associator image `id ⊗ assoc` on channel `(q₁, p₁, p₂)` onto right
channel `(r₁, r₂, r₃)` extracts `recouplingCoeff` when `(p₂ : ℕ) = (r₃ : ℕ)` and `0` otherwise. -/
theorem clebschGordanQuadRightProjection_tensorMap_id_assoc_vec (hq : IsGenericQuantumParameter q)
    (q₁ : Fin (min b c + 1)) (p₁ : Fin (min (b + c - 2 * (q₁ : ℕ)) d + 1))
    (p₂ : Fin (min a (b + c - 2 * (q₁ : ℕ) + d - 2 * (p₁ : ℕ)) + 1)) (r₁ : Fin (min c d + 1))
    (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) (l : ℤ) :
    clebschGordanQuadRightProjection (ε := ε) (δ := δ) (ζ := ζ) (θ := θ) hq r₁ r₂ r₃
        (tensorMap ℂ (UqSl2 q) LinearMap.id (assoc ℂ (UqSl2 q) (LadderModule q b δ)
          (LadderModule q c ζ) (LadderModule q d θ)).toLinearMap
          (tensorMap ℂ (UqSl2 q) LinearMap.id
            (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq q₁) LinearMap.id)
            (clebschGordanRightInclusion (ε := ε) hq p₁ p₂ (vec q _ _ l)))) =
      (if (p₂ : ℕ) = (r₃ : ℕ) then recouplingCoeff hq δ ζ θ q₁ p₁ r₁ r₂ else 0) • vec q _ _ l := by
  have hstep (x : _) : tensorMap ℂ (UqSl2 q) LinearMap.id
        (clebschGordanRightProjection (ε := δ) (δ := ζ) (ζ := θ) hq r₁ r₂)
        (tensorMap ℂ (UqSl2 q) LinearMap.id (assoc ℂ (UqSl2 q) (LadderModule q b δ)
            (LadderModule q c ζ) (LadderModule q d θ)).toLinearMap
          (tensorMap ℂ (UqSl2 q) LinearMap.id
            (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq q₁) LinearMap.id)
            (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq p₁) x))) =
      tensorMap ℂ (UqSl2 q) (LinearMap.id : LadderModule q a ε →ₗ[UqSl2 q] _)
        (recouplingHom hq q₁ p₁ r₁ r₂) x := by
    simp only [← LinearMap.comp_apply, ← tensorMap_comp, LinearMap.id_comp, recouplingHom_def,
      clebschGordanLeftInclusion_def]
  rw [clebschGordanQuadRightProjection_apply, clebschGordanRightInclusion_def, LinearMap.comp_apply,
    hstep, clebschGordanProjection_tensorMap_inclusion_vec hq LinearMap.id
      (recouplingHom hq q₁ p₁ r₁ r₂) p₂ r₃ l, schurScalar_id, one_mul, ← recouplingCoeff_def]

/-- Evaluation of `quadRecouplingHom` on every ladder vector `v_l` along the three-step associator
path `((A ⊗ B) ⊗ C) ⊗ D → (A ⊗ (B ⊗ C)) ⊗ D → A ⊗ ((B ⊗ C) ⊗ D) → A ⊗ (B ⊗ (C ⊗ D))` via
`BialgebraModule.assoc_pentagon_apply`. -/
theorem quadRecouplingHom_vec_eq_sum_sum_recouplingCoeff_mul_smul (hq : IsGenericQuantumParameter q)
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
                  recouplingCoeff hq ε (δ * ζ) θ q₂ (i₃.cast (congrArg (min · d + 1) hw)) p₁ p₂ *
                  recouplingCoeff hq ε δ ζ i₁ i₂ q₁ q₂
              else 0
        else 0) • vec q _ _ l := by
  -- Rewrite the two-step associator into the three-step composite via Mac Lane's pentagon.
  rw [quadRecouplingHom_def, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, assoc_pentagon_apply]
  -- Step 1 (`assoc ⊗ id`): expand the inner triple `(A ⊗ B) ⊗ C → A ⊗ (B ⊗ C)` over `(q₁, q₂)`.
  have hinner : tensorMap ℂ (UqSl2 q) (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (LadderModule q c ζ)).toLinearMap LinearMap.id
        (clebschGordanQuadLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) (θ := θ) hq i₁ i₂ i₃
          (vec q _ _ l)) =
      ∑ q₁ : Fin (min b c + 1), ∑ q₂ : Fin (min a (b + c - 2 * (q₁ : ℕ)) + 1),
        tensorMap ℂ (UqSl2 q) ((clebschGordanRightInclusion hq q₁ q₂).comp
          (recouplingHom hq i₁ i₂ q₁ q₂)) LinearMap.id (clebschGordanInclusion hq i₃
            (vec q _ _ l)) := by
    rw [clebschGordanQuadLeftInclusion_def, LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← tensorMap_comp, LinearMap.id_comp, assoc_comp_clebschGordanLeftInclusion hq i₁ i₂,
      tensorMap_sum_left]
    simp only [tensorMap_sum_left, LinearMap.sum_apply]
  rw [hinner, Finset.sum_smul]; simp_rw [Finset.sum_smul]; simp only [map_sum]
  refine Finset.sum_congr rfl fun q₁ _ => Finset.sum_congr rfl fun q₂ _ => ?_
  split_ifs with hw
  · -- Step 2 (`assoc A (B ⊗ C) D`): pull out the scalar and expand `(q₂, i₃')` over `(p₁, p₂)`.
    let i₃' := i₃.cast (congrArg (min · d + 1) hw)
    have hsplit : tensorMap ℂ (UqSl2 q) ((clebschGordanRightInclusion (m := a) (n := b) (p := c)
            (ε := ε) (δ := δ) (ζ := ζ) hq q₁ q₂).comp (recouplingHom hq i₁ i₂ q₁ q₂))
          (LinearMap.id : LadderModule q d θ →ₗ[UqSl2 q] _)
          (clebschGordanInclusion hq i₃ (vec q _ _ l)) =
        recouplingCoeff hq ε δ ζ i₁ i₂ q₁ q₂ • tensorMap ℂ (UqSl2 q)
          (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq q₁)) LinearMap.id
          (clebschGordanLeftInclusion hq q₂ i₃' (vec q _ _ l)) := by
      have hcomp : tensorMap ℂ (UqSl2 q) ((clebschGordanRightInclusion (m := a) (n := b) (p := c)
              (ε := ε) (δ := δ) (ζ := ζ) hq q₁ q₂).comp (recouplingHom hq i₁ i₂ q₁ q₂))
            (LinearMap.id : LadderModule q d θ →ₗ[UqSl2 q] _) =
          (tensorMap ℂ (UqSl2 q) (clebschGordanRightInclusion hq q₁ q₂) LinearMap.id).comp
            (tensorMap ℂ (UqSl2 q) (recouplingHom hq i₁ i₂ q₁ q₂) LinearMap.id) := by
        rw [← tensorMap_comp, LinearMap.id_comp]
      rw [hcomp, LinearMap.comp_apply,
        tensorMap_clebschGordanInclusion_vec hq (recouplingHom hq i₁ i₂ q₁ q₂) LinearMap.id
          (j' := i₃') (Fin.val_cast _ _).symm l,
        schurScalar_id, mul_one, LinearMap.map_smul_of_tower, ← recouplingCoeff_def]
      congr 1; symm
      rw [clebschGordanLeftInclusion_def, LinearMap.comp_apply, ← LinearMap.comp_apply,
        ← tensorMap_comp, LinearMap.id_comp, ← clebschGordanRightInclusion_def]
    rw [hsplit, ← LinearEquiv.coe_toLinearMap, LinearMap.map_smul_of_tower,
      LinearEquiv.coe_toLinearMap,
      ← tensorMap_tensorMap_assoc ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq q₁)
        LinearMap.id,
      assoc_clebschGordanLeftInclusion_vec hq q₂ i₃' l]
    -- Step 3 (`id ⊗ assoc B C D`): project each `(q₁, p₁, p₂)` term onto `(r₁, r₂, r₃)`.
    simp only [map_sum, LinearMap.map_smul_of_tower,
      clebschGordanQuadRightProjection_tensorMap_id_assoc_vec, smul_smul, ← Finset.sum_smul]
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
    (i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1)) (r₁ : Fin (min c d + 1))
    (r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1))
    (r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)) :
    (∑ p₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) (c + d - 2 * (r₁ : ℕ)) + 1),
        recouplingCoeff hq ε δ (ζ * θ) i₁ p₂ r₂ r₃ * recouplingCoeff hq (ε * δ) ζ θ i₂ i₃ r₁ p₂) =
      ∑ q₁ : Fin (min b c + 1), ∑ q₂ : Fin (min a (b + c - 2 * (q₁ : ℕ)) + 1),
        if hw : a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) =
            a + (b + c - 2 * (q₁ : ℕ)) - 2 * (q₂ : ℕ) then
          ∑ p₁ : Fin (min (b + c - 2 * (q₁ : ℕ)) d + 1),
            ∑ p₂ : Fin (min a (b + c - 2 * (q₁ : ℕ) + d - 2 * (p₁ : ℕ)) + 1),
              if (p₂ : ℕ) = (r₃ : ℕ) then
                recouplingCoeff hq δ ζ θ q₁ p₁ r₁ r₂ *
                  recouplingCoeff hq ε (δ * ζ) θ q₂ (i₃.cast (congrArg (min · d + 1) hw)) p₁ p₂ *
                  recouplingCoeff hq ε δ ζ i₁ i₂ q₁ q₂
              else 0
        else 0 := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  exact smul_left_injective ℂ (by simp : vec q _ _ 0 ≠ 0)
    ((quadRecouplingHom_vec_eq_sum_recouplingCoeff_mul_smul (ε := ε) (δ := δ) (ζ := ζ) (θ := θ)
      hq i₁ i₂ i₃ r₁ r₂ r₃ 0).symm.trans (quadRecouplingHom_vec_eq_sum_sum_recouplingCoeff_mul_smul
        hq i₁ i₂ i₃ r₁ r₂ r₃ 0))

/-- When the left and right fourfold channels share total highest weight `e`, the two-step sum in
`recouplingCoeff_pentagon` collapses to the product of the two `α₀ = 1` change-of-decomposition
entries `sixJ` along `((A ⊗ B) ⊗ C) ⊗ D → (A ⊗ B) ⊗ (C ⊗ D) → A ⊗ (B ⊗ (C ⊗ D))`. -/
theorem sum_recouplingCoeff_mul_eq_sixJ_mul (hq : IsGenericQuantumParameter q) (ε δ ζ θ : ℤˣ)
    {a b c d u w e y x : ℕ} {i₁ : Fin (min a b + 1)} {i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1)}
    {i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1)} {r₁ : Fin (min c d + 1)}
    {r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1)}
    {r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)}
    (hu : a + b - 2 * (i₁ : ℕ) = u) (hw : a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) = w)
    (he : a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) + d - 2 * (i₃ : ℕ) = e)
    (hy : c + d - 2 * (r₁ : ℕ) = y) (hx : b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ) = x)
    (he' : a + (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) - 2 * (r₃ : ℕ) = e) :
    (∑ p₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) (c + d - 2 * (r₁ : ℕ)) + 1),
        recouplingCoeff hq ε δ (ζ * θ) i₁ p₂ r₂ r₃ * recouplingCoeff hq (ε * δ) ζ θ i₂ i₃ r₁ p₂) =
      sixJ hq ε δ (ζ * θ) a b y e u x * sixJ hq (ε * δ) ζ θ u c d e w y := by
  subst hu hw he hy hx
  by_cases huy : IsClebschGordanChannel (a + b - 2 * (i₁ : ℕ)) (c + d - 2 * (r₁ : ℕ))
      (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) + d - 2 * (i₃ : ℕ))
  · rw [Finset.sum_eq_single huy.index]
    · have he_uy := huy.sub_two_mul_index
      rw [recouplingCoeff_eq_ite hq ε δ (ζ * θ), ite_eq_left (he_uy.trans he'.symm),
        recouplingCoeff_eq_ite hq (ε * δ) ζ θ, ite_eq_left he_uy.symm, he_uy]
    · exact fun p₂ _ hp₂ => by
        rw [recouplingCoeff_eq_zero_of_ne_index_right hq (ε * δ) ζ θ rfl huy hp₂, mul_zero]
    · simp
  · rw [sixJ_eq_zero_of_not hq ε δ (ζ * θ) (fun h => huy h.1.2), zero_mul]
    exact Finset.sum_eq_zero fun p₂ _ => by
      rw [recouplingCoeff_eq_zero_of_not_channel_right hq (ε * δ) ζ θ rfl huy, mul_zero]

/-- For each inner channel `q₁` of `L_b^δ ⊗ L_c^ζ` and matching total highest weights `e`, the
inner three-step sums in `recouplingCoeff_pentagon` collapse to the product of the three `α₀ = 1`
change-of-decomposition entries `sixJ` along the three-step associator path. -/
theorem sum_sum_recouplingCoeff_eq_sixJ_mul (hq : IsGenericQuantumParameter q) (ε δ ζ θ : ℤˣ)
    {a b c d u w e y x : ℕ} {i₁ : Fin (min a b + 1)} {i₂ : Fin (min (a + b - 2 * (i₁ : ℕ)) c + 1)}
    {i₃ : Fin (min (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ)) d + 1)} {r₁ : Fin (min c d + 1)}
    {r₂ : Fin (min b (c + d - 2 * (r₁ : ℕ)) + 1)}
    {r₃ : Fin (min a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) + 1)}
    (hu : a + b - 2 * (i₁ : ℕ) = u) (hw : a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) = w)
    (he : a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) + d - 2 * (i₃ : ℕ) = e)
    (hy : c + d - 2 * (r₁ : ℕ) = y) (hx : b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ) = x)
    (he' : a + (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ)) - 2 * (r₃ : ℕ) = e)
    (q₁ : Fin (min b c + 1)) :
    (∑ q₂ : Fin (min a (b + c - 2 * (q₁ : ℕ)) + 1),
        if hw' : a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) =
            a + (b + c - 2 * (q₁ : ℕ)) - 2 * (q₂ : ℕ) then
          ∑ p₁ : Fin (min (b + c - 2 * (q₁ : ℕ)) d + 1),
            ∑ p₂ : Fin (min a (b + c - 2 * (q₁ : ℕ) + d - 2 * (p₁ : ℕ)) + 1),
              if (p₂ : ℕ) = (r₃ : ℕ) then
                recouplingCoeff hq δ ζ θ q₁ p₁ r₁ r₂ *
                  recouplingCoeff hq ε (δ * ζ) θ q₂ (i₃.cast (congrArg (min · d + 1) hw')) p₁ p₂ *
                  recouplingCoeff hq ε δ ζ i₁ i₂ q₁ q₂
              else 0
        else 0) =
      sixJ hq δ ζ θ b c d x (b + c - 2 * (q₁ : ℕ)) y *
        sixJ hq ε (δ * ζ) θ a (b + c - 2 * (q₁ : ℕ)) d e w x *
        sixJ hq ε δ ζ a b c w u (b + c - 2 * (q₁ : ℕ)) := by
  subst hu hw he hy hx
  have hbc := isClebschGordanChannel_sub_two_mul q₁
  have hax : IsClebschGordanChannel a (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ))
      (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ) + d - 2 * (i₃ : ℕ)) :=
    isClebschGordanChannel_def.mpr ⟨r₃, he'⟩
  -- Step 1 (sum over `q₂`): only `q₂ = haz.index` matches weight `w`; otherwise both sides vanish.
  by_cases haz : IsClebschGordanChannel a (b + c - 2 * (q₁ : ℕ))
      (a + b - 2 * (i₁ : ℕ) + c - 2 * (i₂ : ℕ))
  · rw [Finset.sum_eq_single haz.index]
    · rw [dite_eq_left haz.sub_two_mul_index.symm]
      -- Step 2 (sum over `p₁`): only `p₁ = hzd.index` couples `b + c - 2q₁` with `d` to weight `x`.
      by_cases hzd : IsClebschGordanChannel (b + c - 2 * (q₁ : ℕ)) d
          (b + (c + d - 2 * (r₁ : ℕ)) - 2 * (r₂ : ℕ))
      · rw [Finset.sum_eq_single hzd.index]
        · -- Step 3 (sum over `p₂`): `(p₂ : ℕ) = (r₃ : ℕ)` selects `p₂ = hax.rightIndex hzd`.
          have hp₂_eq : ((hax.rightIndex hzd) : ℕ) = (r₃ : ℕ) := by
            rw [Fin.val_cast, hax.index_eq_of_eq he']
          rw [Finset.sum_eq_single (hax.rightIndex hzd)]
          · rw [ite_eq_left hp₂_eq,
              sixJ_eq_recouplingCoeff hq δ ζ θ ⟨hbc, hzd⟩
                ⟨isClebschGordanChannel_sub_two_mul r₁, isClebschGordanChannel_sub_two_mul r₂⟩,
              sixJ_eq_recouplingCoeff hq ε (δ * ζ) θ ⟨haz, isClebschGordanChannel_sub_two_mul i₃⟩
                ⟨hzd, hax⟩,
              sixJ_eq_recouplingCoeff hq ε δ ζ
                ⟨isClebschGordanChannel_sub_two_mul i₁, isClebschGordanChannel_sub_two_mul i₂⟩
                ⟨hbc, haz⟩]
            exact congrArg₂ (· * ·) (congrArg₂ (· * ·)
                (recouplingCoeff_congr hq δ ζ θ (by simp) (by simp) (by simp) (by simp))
                (recouplingCoeff_congr hq ε (δ * ζ) θ rfl (by simp) rfl rfl))
              (recouplingCoeff_congr hq ε δ ζ (by simp) (by simp) (by simp) (by simp))
          · exact fun p₂ _ hp₂ => ite_eq_right fun heq => hp₂ (Fin.ext (heq.trans hp₂_eq.symm))
          · simp
        · exact fun p₁ _ hp₁ => Finset.sum_eq_zero fun _ _ => by
            simp [recouplingCoeff_eq_zero_of_ne_index_left hq δ ζ θ rfl hzd hp₁]
        · simp
      · rw [sixJ_eq_zero_of_not hq δ ζ θ (fun h => hzd h.1.2), zero_mul, zero_mul]
        exact Finset.sum_eq_zero fun p₁ _ => Finset.sum_eq_zero fun _ _ => by
          simp [recouplingCoeff_eq_zero_of_not_channel_left hq δ ζ θ rfl hzd]
    · exact fun q₂ _ hq₂ => dite_eq_right fun heq => hq₂ (haz.index_eq_of_eq heq.symm).symm
    · simp
  · rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => haz h.2.2), mul_zero]
    exact Finset.sum_eq_zero fun q₂ _ => dite_eq_right fun heq =>
      haz (isClebschGordanChannel_def.mpr ⟨q₂, heq.symm⟩)

/-- **The Biedenharn–Elliott pentagon identity** for the `α₀ = 1` change-of-decomposition
(`F`-matrix) entries `sixJ` of `clebschGordanInclusion` across all signed ladder modules
`L_a^ε ⊗ L_b^δ ⊗ L_c^ζ ⊗ L_d^θ` at generic `q`. -/
theorem sixJ_pentagon (hq : IsGenericQuantumParameter q) (ε δ ζ θ : ℤˣ) (a b c d e u w x y : ℕ) :
    sixJ hq ε δ (ζ * θ) a b y e u x * sixJ hq (ε * δ) ζ θ u c d e w y =
      ∑ z ∈ Finset.range (b + c + 1), sixJ hq δ ζ θ b c d x z y *
        sixJ hq ε (δ * ζ) θ a z d e w x * sixJ hq ε δ ζ a b c w u z := by
  -- Split on whether all six external binary couplings are admissible; otherwise both sides vanish.
  by_cases hadm : IsClebschGordanChannel a b u ∧ IsClebschGordanChannel u c w ∧
      IsClebschGordanChannel w d e ∧ IsClebschGordanChannel c d y ∧
      IsClebschGordanChannel b y x ∧ IsClebschGordanChannel a x e
  · rcases hadm with ⟨hab, huc, hwd, hcd, hby, hax⟩
    have hw : a + b - 2 * (hab.index : ℕ) + c - 2 * ((huc.leftIndex hab) : ℕ) = w := by
      rw [Fin.val_cast, hab.sub_two_mul_index, huc.sub_two_mul_index]
    have hx : b + (c + d - 2 * (hcd.index : ℕ)) - 2 * ((hby.rightIndex hcd) : ℕ) = x := by
      rw [Fin.val_cast, hcd.sub_two_mul_index, hby.sub_two_mul_index]
    let i₃ := hwd.index.cast (congrArg (min · d + 1) hw.symm)
    let r₃ := hax.index.cast (congrArg (min a · + 1) hx.symm)
    have he : a + b - 2 * (hab.index : ℕ) + c - 2 * ((huc.leftIndex hab) : ℕ) + d -
        2 * (i₃ : ℕ) = e := by rw [(Fin.val_cast _ _ : (i₃ : ℕ) = _), hw, hwd.sub_two_mul_index]
    have he' : a + (b + (c + d - 2 * (hcd.index : ℕ)) - 2 * ((hby.rightIndex hcd) : ℕ)) -
        2 * (r₃ : ℕ) = e := by rw [(Fin.val_cast _ _ : (r₃ : ℕ) = _), hx, hax.sub_two_mul_index]
    rw [← sum_recouplingCoeff_mul_eq_sixJ_mul hq ε δ ζ θ hab.sub_two_mul_index hw he
        hcd.sub_two_mul_index hx he',
      recouplingCoeff_pentagon hq ε δ ζ θ hab.index (huc.leftIndex hab) i₃
        hcd.index (hby.rightIndex hcd) r₃,
      ← sum_fin_channel_eq_sum_range b c _ fun z hbc => by
        rw [sixJ_eq_zero_of_not hq δ ζ θ (fun h => hbc h.1.1), zero_mul, zero_mul]]
    exact Finset.sum_congr rfl fun q₁ _ => sum_sum_recouplingCoeff_eq_sixJ_mul hq ε δ ζ θ
      hab.sub_two_mul_index hw he hcd.sub_two_mul_index hx he' q₁
  · -- Inadmissible case: at least one of the six boundary couplings fails, killing both sides.
    trans 0
    · by_cases h1 : (IsClebschGordanChannel a b u ∧ IsClebschGordanChannel u y e) ∧
          (IsClebschGordanChannel b y x ∧ IsClebschGordanChannel a x e)
      · rw [sixJ_eq_zero_of_not hq (ε * δ) ζ θ (fun h2 => hadm ⟨h1.1.1, h2.1.1, h2.1.2,
          h2.2.1, h1.2.1, h1.2.2⟩), mul_zero]
      · rw [sixJ_eq_zero_of_not hq ε δ (ζ * θ) h1, zero_mul]
    · symm; refine Finset.sum_eq_zero fun z _ => ?_
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

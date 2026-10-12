/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.GlobalExistence
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The reduced minimal equation of an elliptic curve over `ℚ`

Every elliptic curve `E` over `ℚ` has a Weierstrass equation that is minimal at every prime
(`WeierstrassCurve.exists_isGlobalMinimal_smul`, `ℤ` being a principal ideal domain). Such an
equation is not unique: the changes of variables between globally minimal equations are exactly
those defined over `ℤ` (`WeierstrassCurve.IsGlobalMinimal.exists_baseChange_eq_of_smul_eq`), with
`u = ±1` and `r, s, t ∈ ℤ`. Using that freedom to reduce `a₁` modulo `2`, then `a₂` modulo `3`,
then `a₃` modulo `2` gives the **reduced minimal equation**, with

`a₁ ∈ {0, 1}`, `a₂ ∈ {-1, 0, 1}`, `a₃ ∈ {0, 1}`.

It is unique: a change of variables over `ℤ` between two reduced equations is the identity or the
negation automorphism `[-1]`, both of which fix the equation. This is the equation by which tables
of elliptic curves over `ℚ` (Cremona's tables, the LMFDB) present a curve, so it lets a label name
an equation rather than an isomorphism class.

The reduced minimal equation is a long Weierstrass equation. It is a different object from the
minimal-pair short equation `WeierstrassCurve.minimalPairModel`, which need not be minimal at `2`
and `3`.

## Main definitions

* `WeierstrassCurve.IsReducedMinimal W`: `W` is globally minimal over `ℤ` with `a₁, a₃ ∈ {0, 1}`
  and `a₂ ∈ {-1, 0, 1}`.
* `WeierstrassCurve.reducedMinimalModel E`: the reduced minimal equation of `E`.

## Main results

* `WeierstrassCurve.exists_isReducedMinimal_smul`: every elliptic curve over `ℚ` has a reduced
  minimal equation.
* `WeierstrassCurve.IsReducedMinimal.eq_of_smul_eq`: two reduced minimal equations related by a
  change of variables are equal.
* `WeierstrassCurve.existsUnique_reducedMinimal`: the reduced minimal equation in the
  variable-change orbit of `E` exists and is unique. The change of variables reaching it is not
  unique: it may be composed with `[-1]`.
* `WeierstrassCurve.eq_reducedMinimalModel` and
  `WeierstrassCurve.VariableChange.reducedMinimalModel_smul`: the reduced minimal model is
  characterised by being reduced minimal and isomorphic to `E`, so it is invariant under a change
  of variables.
* `WeierstrassCurve.IsReducedMinimal.reducedMinimalModel_eq` and
  `WeierstrassCurve.reducedMinimalModel_reducedMinimalModel`: reduced equations are fixed by the
  construction, so it is idempotent.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.1 and VIII.8.
* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., Cambridge University Press,
  1997: the normalisation `a₁, a₃ ∈ {0, 1}`, `a₂ ∈ {-1, 0, 1}` of a minimal equation.
-/

public section

namespace WeierstrassCurve

/-- **A reduced minimal Weierstrass equation over `ℚ`**: globally minimal over `ℤ`, with the
residual freedom of the changes of variables over `ℤ` pinned by `a₁, a₃ ∈ {0, 1}` and
`a₂ ∈ {-1, 0, 1}`. Every elliptic curve over `ℚ` has exactly one such equation in its
variable-change orbit (`existsUnique_reducedMinimal`). -/
def IsReducedMinimal (W : WeierstrassCurve ℚ) [W.IsElliptic] : Prop :=
  IsGlobalMinimal ℤ W ∧ (W.a₁ = 0 ∨ W.a₁ = 1) ∧ (W.a₂ = -1 ∨ W.a₂ = 0 ∨ W.a₂ = 1) ∧
    (W.a₃ = 0 ∨ W.a₃ = 1)

/-- Reduced minimality, unfolded. This is the interface to `WeierstrassCurve.IsReducedMinimal`
outside its defining module. -/
@[simp]
theorem isReducedMinimal_iff {W : WeierstrassCurve ℚ} [W.IsElliptic] :
    IsReducedMinimal W ↔ IsGlobalMinimal ℤ W ∧ (W.a₁ = 0 ∨ W.a₁ = 1) ∧
      (W.a₂ = -1 ∨ W.a₂ = 0 ∨ W.a₂ = 1) ∧ (W.a₃ = 0 ∨ W.a₃ = 1) :=
  Iff.rfl

/-- A reduced minimal equation is globally minimal over `ℤ`. -/
theorem IsReducedMinimal.isGlobalMinimal {W : WeierstrassCurve ℚ} [W.IsElliptic]
    (h : IsReducedMinimal W) : IsGlobalMinimal ℤ W :=
  h.1

/-! ### The normalisation over `ℤ` -/

/-- Every equation over `ℤ` is carried to one with `a₁, a₃ ∈ {0, 1}` and
`a₂ ∈ {-1, 0, 1}` by a change of variables over `ℤ`. -/
theorem exists_variableChange_reduced (W : WeierstrassCurve ℤ) :
    ∃ C : VariableChange ℤ, ((C • W).a₁ = 0 ∨ (C • W).a₁ = 1) ∧
      ((C • W).a₂ = -1 ∨ (C • W).a₂ = 0 ∨ (C • W).a₂ = 1) ∧
      ((C • W).a₃ = 0 ∨ (C • W).a₃ = 1) := by
  -- Reduce `a₁` modulo `2` by `s`, then `a₂` modulo `3` by `r`, then `a₃` modulo `2` by `t`: with
  -- `u = 1` the new `a₁` depends on `s` alone, the new `a₂` on `s` and `r`, and the new `a₃` on
  -- `r` and `t`.
  obtain ⟨s, hs⟩ : ∃ s : ℤ, W.a₁ + 2 * s = 0 ∨ W.a₁ + 2 * s = 1 := ⟨-(W.a₁ / 2), by omega⟩
  obtain ⟨r, hr⟩ : ∃ r : ℤ, (W.a₂ - s * W.a₁ - s ^ 2) + 3 * r = -1 ∨
      (W.a₂ - s * W.a₁ - s ^ 2) + 3 * r = 0 ∨ (W.a₂ - s * W.a₁ - s ^ 2) + 3 * r = 1 :=
    ⟨-((W.a₂ - s * W.a₁ - s ^ 2 + 1) / 3), by omega⟩
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (W.a₃ + r * W.a₁) + 2 * t = 0 ∨ (W.a₃ + r * W.a₁) + 2 * t = 1 :=
    ⟨-((W.a₃ + r * W.a₁) / 2), by omega⟩
  refine ⟨⟨1, r, s, t⟩, ?_, ?_, ?_⟩
  · simpa [variableChange_a₁] using hs
  · simpa [variableChange_a₂, sub_add_eq_add_sub] using hr
  · simpa [variableChange_a₃] using ht

namespace VariableChange

/-- A change of variables over `ℤ` between two equations in reduced form fixes the equation:
it is the identity when `u = 1`, and the negation automorphism when `u = -1`. -/
theorem smul_eq_self_of_reduced {W : WeierstrassCurve ℤ} (C : VariableChange ℤ)
    (h₁ : W.a₁ = 0 ∨ W.a₁ = 1) (h₂ : W.a₂ = -1 ∨ W.a₂ = 0 ∨ W.a₂ = 1) (h₃ : W.a₃ = 0 ∨ W.a₃ = 1)
    (h₁' : (C • W).a₁ = 0 ∨ (C • W).a₁ = 1)
    (h₂' : (C • W).a₂ = -1 ∨ (C • W).a₂ = 0 ∨ (C • W).a₂ = 1)
    (h₃' : (C • W).a₃ = 0 ∨ (C • W).a₃ = 1) : C • W = W := by
  rcases Int.units_eq_one_or C.u with hu | hu
  · have hs : C.s = 0 := by
      have : (C • W).a₁ = W.a₁ + 2 * C.s := by simp [variableChange_a₁, hu]
      omega
    have hr : C.r = 0 := by
      have : (C • W).a₂ = W.a₂ + 3 * C.r := by simp [variableChange_a₂, hu, hs]
      omega
    have ht : C.t = 0 := by
      have : (C • W).a₃ = W.a₃ + 2 * C.t := by simp [variableChange_a₃, hu, hr]
      omega
    have hC : C = 1 := VariableChange.ext hu hr hs ht
    rw [hC, one_smul]
  · have hs : C.s = -W.a₁ := by
      have : (C • W).a₁ = -(W.a₁ + 2 * C.s) := by simp [variableChange_a₁, hu]
      omega
    have hr : C.r = 0 := by
      have : (C • W).a₂ = W.a₂ + 3 * C.r := by simp [variableChange_a₂, hu, hs]; ring
      omega
    have ht : C.t = -W.a₃ := by
      have : (C • W).a₃ = -(W.a₃ + 2 * C.t) := by simp [variableChange_a₃, hu, hr]
      omega
    have hC : C = W.negVariableChange := VariableChange.ext
      (by rw [hu, negVariableChange_u])
      (by rw [hr, negVariableChange_r]) (by rw [hs, negVariableChange_s])
      (by rw [ht, negVariableChange_t])
    rw [hC, negVariableChange_smul_self]

end VariableChange

/-! ### Existence and uniqueness -/

/-- **Every elliptic curve over `ℚ` has a reduced minimal equation** in its variable-change
orbit. -/
theorem exists_isReducedMinimal_smul (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : VariableChange ℚ, IsReducedMinimal (C • E) := by
  -- Start with a globally minimal equation and normalize its coefficients over `ℤ`.
  obtain ⟨C₀, hC₀⟩ := exists_isGlobalMinimal_smul ℤ E
  have := hC₀.isIntegral
  have hW : (integralModel ℤ (C₀ • E)).baseChange ℚ = C₀ • E := baseChange_integralModel_eq ℤ _
  obtain ⟨D, h₁, h₂, h₃⟩ := exists_variableChange_reduced (integralModel ℤ (C₀ • E))
  refine ⟨D.baseChange ℚ * C₀, ?_, ?_⟩
  · exact IsGlobalMinimal.of_forall_isMinimal fun v => by
      rw [mul_smul]
      exact (hC₀.baseChange_smul D).isMinimal v
  · rw [mul_smul, ← hW, baseChange_smul_baseChange]
    simp only [baseChange, map_a₁, map_a₂, map_a₃, algebraMap_int_eq, eq_intCast]
    exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂, by exact_mod_cast h₃⟩

/-- **Two reduced minimal equations related by a change of variables are equal.** This gives
uniqueness of the reduced equation in each variable-change orbit. -/
theorem IsReducedMinimal.eq_of_smul_eq {W₁ W₂ : WeierstrassCurve ℚ} [W₁.IsElliptic]
    [W₂.IsElliptic] (h₁ : IsReducedMinimal W₁) (h₂ : IsReducedMinimal W₂) (C : VariableChange ℚ)
    (hC : C • W₁ = W₂) : W₁ = W₂ := by
  -- The change descends to `ℤ`; reduced form makes its action fix the equation.
  obtain ⟨C₀, rfl⟩ := h₁.isGlobalMinimal.exists_baseChange_eq_of_smul_eq h₂.isGlobalMinimal C hC
  have := h₁.isGlobalMinimal.isIntegral
  have := h₂.isGlobalMinimal.isIntegral
  have e₁ := baseChange_integralModel_eq ℤ W₁
  have e₂ := baseChange_integralModel_eq ℤ W₂
  -- Descend the relation to the integral models, and the reduced form to their coefficients.
  have key : C₀ • integralModel ℤ W₁ = integralModel ℤ W₂ :=
    smul_eq_of_baseChange_smul_eq ℚ (algebraMap ℤ ℚ).injective_int C₀ (by rw [e₁, e₂, hC])
  obtain ⟨-, a₁, a₂, a₃⟩ := h₁
  obtain ⟨-, b₁, b₂, b₃⟩ := h₂
  rw [← e₁] at a₁ a₂ a₃
  rw [← e₂, ← key] at b₁ b₂ b₃
  simp only [baseChange, map_a₁, map_a₂, map_a₃, algebraMap_int_eq, eq_intCast] at a₁ a₂ a₃ b₁ b₂ b₃
  have := VariableChange.smul_eq_self_of_reduced C₀ (by exact_mod_cast a₁) (by exact_mod_cast a₂)
    (by exact_mod_cast a₃) (by exact_mod_cast b₁) (by exact_mod_cast b₂) (by exact_mod_cast b₃)
  rw [← e₁, ← e₂, ← key, this]

/-- **Existence and uniqueness of the reduced minimal equation**: the variable-change orbit of an
elliptic curve over `ℚ` contains exactly one reduced minimal equation. The equation is unique; the
change of variables reaching it is not, since it may be composed with `[-1]`. -/
theorem existsUnique_reducedMinimal (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃! W : { W : WeierstrassCurve ℚ // W.IsElliptic },
      @IsReducedMinimal W.1 W.2 ∧ ∃ C : VariableChange ℚ, C • E = W.1 := by
  obtain ⟨C, hC⟩ := exists_isReducedMinimal_smul E
  refine ⟨⟨C • E, inferInstance⟩, ⟨hC, C, rfl⟩, ?_⟩
  rintro ⟨W, hW⟩ ⟨hWr, D, rfl⟩
  exact Subtype.ext (hWr.eq_of_smul_eq hC (C * D⁻¹) (by rw [mul_smul, inv_smul_smul]))

/-! ### The reduced minimal model of a curve -/

/-- **The reduced minimal model** of an elliptic curve over `ℚ`: the unique reduced minimal
equation in its variable-change orbit. It is characterised by
`isReducedMinimal_reducedMinimalModel`, `exists_smul_eq_reducedMinimalModel` and
`eq_reducedMinimalModel`, fixes reduced equations, and depends only on the
`ℚ`-isomorphism class of `E` (`VariableChange.reducedMinimalModel_smul`). -/
noncomputable def reducedMinimalModel (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    WeierstrassCurve ℚ :=
  (exists_isReducedMinimal_smul E).choose • E

/-- The reduced minimal model is obtained from `E` by a change of variables. -/
theorem exists_smul_eq_reducedMinimalModel (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : VariableChange ℚ, C • E = reducedMinimalModel E :=
  ⟨_, (rfl)⟩

/-- The reduced minimal model of an elliptic curve is an elliptic curve. -/
instance isElliptic_reducedMinimalModel (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (reducedMinimalModel E).IsElliptic := by
  obtain ⟨C, hC⟩ := exists_smul_eq_reducedMinimalModel E
  rw [← hC]
  infer_instance

/-- The reduced minimal model is reduced minimal. -/
theorem isReducedMinimal_reducedMinimalModel (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    IsReducedMinimal (reducedMinimalModel E) :=
  (exists_isReducedMinimal_smul E).choose_spec

/-- **A reduced minimal equation isomorphic to `E` is the reduced minimal model of `E`.** -/
theorem eq_reducedMinimalModel {E W : WeierstrassCurve ℚ} [E.IsElliptic] [W.IsElliptic]
    (hW : IsReducedMinimal W) (C : VariableChange ℚ) (hC : C • E = W) :
    W = reducedMinimalModel E := by
  obtain ⟨D, hD⟩ := exists_smul_eq_reducedMinimalModel E
  exact hW.eq_of_smul_eq (isReducedMinimal_reducedMinimalModel E) (D * C⁻¹)
    (by rw [mul_smul, ← hC, inv_smul_smul, hD])

/-- A reduced minimal equation is its own reduced minimal model. -/
theorem IsReducedMinimal.reducedMinimalModel_eq {W : WeierstrassCurve ℚ} [W.IsElliptic]
    (hW : IsReducedMinimal W) : reducedMinimalModel W = W :=
  (eq_reducedMinimalModel hW 1 (one_smul _ _)).symm

/-- Taking the reduced minimal model twice has the same result as taking it once. -/
@[simp]
theorem reducedMinimalModel_reducedMinimalModel (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    reducedMinimalModel (reducedMinimalModel E) = reducedMinimalModel E :=
  (isReducedMinimal_reducedMinimalModel E).reducedMinimalModel_eq

namespace VariableChange

/-- **The reduced minimal model is an isomorphism invariant**: it is unchanged by a change of
variables. -/
@[simp]
theorem reducedMinimalModel_smul (C : VariableChange ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    reducedMinimalModel (C • E) = reducedMinimalModel E := by
  obtain ⟨D, hD⟩ := exists_smul_eq_reducedMinimalModel (C • E)
  exact eq_reducedMinimalModel (isReducedMinimal_reducedMinimalModel (C • E)) (D * C)
    (by rw [mul_smul, hD])

end VariableChange

end WeierstrassCurve

end

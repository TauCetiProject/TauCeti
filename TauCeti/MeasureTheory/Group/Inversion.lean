/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.Conjugation

/-!
# Precomposition with inversion on `Lp` of a group

A measure on a type with involutive inversion that is invariant under inversion — normalized Haar
measure on a compact group, for instance — makes `g ↦ g⁻¹` measure preserving, so precomposition
with it is a linear isometric equivalence of `Lp E p μ`. Inversion is an involution, so this
equivalence is its own inverse: an element of `Lp` vanishes exactly when its inverse-translate does.

The construction is `MeasureTheory.Lp.compMeasurePreservingₗᵢEquiv`
(`TauCeti/MeasureTheory/Function/Lp/CompMeasurePreserving/Equiv.lean`) at the inverse pair
`Inv.inv`, `Inv.inv`; what this file adds is the interaction with the class functions of
`TauCeti/MeasureTheory/Group/Conjugation.lean` and the compatibility with the continuous functions
that supply the elements of `Lp` in practice.

The intended use is the change of variables `∫ f g⁻¹ dg = ∫ f g dg` in inner-product form: for `p`
equal to `2` this map preserves the inner product, which is what turns a statement about a function
into the corresponding statement about its inverse-translate.

## Main definitions

* `TauCeti.invLpₗᵢ` (`TauCeti.negLpₗᵢ`): precomposition with inversion (negation), as a linear
  isometric equivalence of `Lp E p μ`.

## Main statements

* `TauCeti.invLpₗᵢ_apply` (`TauCeti.negLpₗᵢ_apply`): precomposition with `Inv.inv` (`Neg.neg`).
* `TauCeti.coeFn_invLpₗᵢ` (`TauCeti.coeFn_negLpₗᵢ`): represented by `g ↦ f g⁻¹` (`g ↦ f (-g)`).
* `TauCeti.invLpₗᵢ_invLpₗᵢ`, `TauCeti.invLpₗᵢ_symm`, `TauCeti.invLpₗᵢ_trans_self` (and
  `negLpₗᵢ_*`): it is an involutive linear isometry equivalence.
* `TauCeti.compLp_invLpₗᵢ` (`TauCeti.compLp_negLpₗᵢ`): commutes with `ContinuousLinearMap.compLp`.
* `TauCeti.invLpₗᵢ_mem_classFunctionLp` and `TauCeti.invLpₗᵢ_mem_classFunctionLp_iff`: it preserves
  the class functions, because inversion commutes with conjugation, and being an involution it
  reflects them too.
* `TauCeti.invLpₗᵢ_toLp` (`TauCeti.negLpₗᵢ_toLp`): on a continuous function it is precomposition
  with inversion (negation).
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {G E : Type*} [MeasurableSpace G] [NormedAddCommGroup E] {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {μ : Measure G}
variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

section Involution

variable [InvolutiveInv G] [MeasurableInv G] [μ.IsInvInvariant]

/-- **Precomposition with inversion on `Lp`**, for a measure invariant under inversion. It is a
linear isometric equivalence because `g ↦ g⁻¹` preserves `μ` and is its own inverse. -/
@[to_additive (dont_translate := 𝕜 E)
/-- **Precomposition with negation on `Lp`**, for a negation-invariant measure. -/]
noncomputable def invLpₗᵢ : Lp E p μ ≃ₗᵢ[𝕜] Lp E p μ :=
  Lp.compMeasurePreservingₗᵢEquiv 𝕜 (Measure.measurePreserving_inv μ)
    (Measure.measurePreserving_inv μ) (.of_eq (funext inv_inv))

variable {𝕜}

/-- The inversion equivalence is precomposition with `Inv.inv`.

Not a `simp` lemma: unfolding to `Lp.compMeasurePreserving` dissolves the abstraction, and it
would take `TauCeti.invLpₗᵢ_invLpₗᵢ` out of simp normal form (the `simpNF` linter rejects the
pair). Use it to rewrite by hand where the underlying precomposition is wanted. -/
@[to_additive (dont_translate := 𝕜 E)
/-- The negation equivalence is precomposition with `Neg.neg` (not `@[simp]`). -/]
theorem invLpₗᵢ_apply (f : Lp E p μ) :
    invLpₗᵢ 𝕜 f = Lp.compMeasurePreserving Inv.inv (Measure.measurePreserving_inv μ) f :=
  Lp.compMeasurePreservingₗᵢEquiv_apply 𝕜 _ _ _ f

/-- The inverse-translate of a class of functions is represented by `g ↦ f g⁻¹`. -/
@[to_additive (dont_translate := 𝕜 E)
/-- The reflected class of functions is represented by `g ↦ f (-g)`. -/]
theorem coeFn_invLpₗᵢ (f : Lp E p μ) : invLpₗᵢ 𝕜 f =ᵐ[μ] fun g ↦ f g⁻¹ :=
  Lp.coeFn_compMeasurePreservingₗᵢEquiv 𝕜 (Measure.measurePreserving_inv μ)
    (Measure.measurePreserving_inv μ) _ f

/-- **Inverting twice is the identity.**  The two precompositions compose to precomposition with
`g ↦ (g⁻¹)⁻¹`, which is the identity on the nose. -/
@[to_additive (dont_translate := 𝕜 E) /-- **Negating twice is the identity.** -/, simp]
theorem invLpₗᵢ_invLpₗᵢ (f : Lp E p μ) : invLpₗᵢ 𝕜 (invLpₗᵢ 𝕜 f) = f := by
  simpa only [invLpₗᵢ_apply] using
    Lp.leftInverse_compMeasurePreserving (E := E) (p := p)
    (Measure.measurePreserving_inv μ) (Measure.measurePreserving_inv μ)
    (.of_eq (funext inv_inv)) f

/-- The inversion equivalence is its own inverse: it is an equivalence and an involution. -/
@[to_additive (dont_translate := 𝕜 E) /-- The negation equivalence is its own inverse. -/, simp]
theorem invLpₗᵢ_symm : (invLpₗᵢ 𝕜 (E := E) (p := p) (μ := μ)).symm = invLpₗᵢ 𝕜 :=
  LinearIsometryEquiv.ext fun f ↦ (LinearIsometryEquiv.symm_apply_eq _).2 (invLpₗᵢ_invLpₗᵢ f).symm

/-- Composing the inversion equivalence with itself gives the identity equivalence. -/
@[to_additive (dont_translate := 𝕜 E)
/-- Composing the negation equivalence with itself gives the identity equivalence. -/, simp]
theorem invLpₗᵢ_trans_self :
    (invLpₗᵢ 𝕜 (E := E) (p := p) (μ := μ)).trans (invLpₗᵢ 𝕜) =
      LinearIsometryEquiv.refl 𝕜 (Lp E p μ) :=
  LinearIsometryEquiv.ext fun f ↦ invLpₗᵢ_invLpₗᵢ f

/-- Postcomposition with a continuous semilinear map commutes with inversion on `Lp`. -/
@[to_additive (dont_translate := 𝕜₀ 𝕜' E F σ)
/-- Postcomposition with a continuous semilinear map commutes with negation on `Lp`. -/]
theorem compLp_invLpₗᵢ {𝕜₀ 𝕜' F : Type*} [NontriviallyNormedField 𝕜₀] [NontriviallyNormedField 𝕜']
    {σ : 𝕜₀ →+* 𝕜'} [RingHomIsometric σ] [NormedSpace 𝕜₀ E] [NormedAddCommGroup F]
    [NormedSpace 𝕜' F] (L : E →SL[σ] F) (f : Lp E p μ) :
    L.compLp (invLpₗᵢ 𝕜₀ f) = invLpₗᵢ 𝕜' (L.compLp f) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (invLpₗᵢ 𝕜₀ f), coeFn_invLpₗᵢ (𝕜 := 𝕜₀) f,
    coeFn_invLpₗᵢ (𝕜 := 𝕜') (L.compLp f),
    (Measure.measurePreserving_inv μ).quasiMeasurePreserving.ae_eq_comp
      (L.coeFn_compLp f)] with g h1 h2 h3 h4
  rw [h1, h2, h3]; exact h4.symm

end Involution

section ClassFunction

variable [Group G] [MeasurableInv G] [μ.IsInvInvariant] [MeasurableMul G]
  [SMulInvariantMeasure (ConjAct G) G μ]

/-- **Inversion preserves the class functions.**  Conjugation commutes with inversion,
`(h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹`, so the conjugates of the inverse-translate of `f` are the
inverse-translates of the conjugates of `f`. -/
theorem invLpₗᵢ_mem_classFunctionLp {f : Lp E p μ} (hf : f ∈ classFunctionLp 𝕜 E p μ) :
    invLpₗᵢ 𝕜 f ∈ classFunctionLp 𝕜 E p μ := by
  rw [mem_classFunctionLp_iff] at hf ⊢
  intro c
  obtain ⟨a, rfl⟩ := DomMulAct.mk.surjective c
  obtain ⟨h, rfl⟩ := ConjAct.toConjAct.surjective a
  rw [← compMeasurePreserving_conj_eq_smul (E := E) (p := p) (μ := μ), ← conjLpₗᵢ_apply (𝕜 := 𝕜)]
  calc
    conjLpₗᵢ 𝕜 h (invLpₗᵢ 𝕜 f) = invLpₗᵢ 𝕜 (conjLpₗᵢ 𝕜 h f) := by
      simp only [conjLpₗᵢ_apply, invLpₗᵢ_apply]
      rw [← Lp.compMeasurePreserving_comp_apply f (Measure.measurePreserving_inv μ)
        (measurePreserving_conj μ h)]
      rw [← Lp.compMeasurePreserving_comp_apply f (measurePreserving_conj μ h)
        (Measure.measurePreserving_inv μ)]
      have hcomp : Inv.inv ∘ (fun g ↦ h * g * h⁻¹) =
          (fun g ↦ h * g * h⁻¹) ∘ Inv.inv := by
        funext g
        simp [mul_assoc]
      simp only [hcomp]
    _ = invLpₗᵢ 𝕜 f := congrArg (invLpₗᵢ 𝕜)
      ((conjLpₗᵢ_apply h f).trans ((compMeasurePreserving_conj_eq_smul h f).trans (hf _)))

/-- **Inversion reflects the class functions.**  Preservation both ways, since inversion is an
involution: the inverse-translate of `f` is a class function exactly when `f` is one.

Not a `simp` lemma: `TauCeti.mem_classFunctionLp_iff` already rewrites the left-hand side to the
invariance condition, so `simp` never reaches this one (the `simpNF` linter rejects it). -/
theorem invLpₗᵢ_mem_classFunctionLp_iff {f : Lp E p μ} :
    invLpₗᵢ 𝕜 f ∈ classFunctionLp 𝕜 E p μ ↔ f ∈ classFunctionLp 𝕜 E p μ :=
  ⟨fun hf ↦ by simpa only [invLpₗᵢ_invLpₗᵢ] using invLpₗᵢ_mem_classFunctionLp (𝕜 := 𝕜) hf,
    fun hf ↦ invLpₗᵢ_mem_classFunctionLp (𝕜 := 𝕜) hf⟩

end ClassFunction

section Continuous

variable [InvolutiveInv G] [MeasurableInv G] [μ.IsInvInvariant] [TopologicalSpace G]
  [ContinuousInv G] [CompactSpace G] [BorelSpace G] [SecondCountableTopologyEither G E]
  [IsFiniteMeasure μ]

/-- **On a continuous function, inversion on `Lp` is precomposition with inversion.** -/
@[to_additive (dont_translate := 𝕜 E)
/-- **On a continuous function, negation on `Lp` is precomposition with negation.** -/]
theorem invLpₗᵢ_toLp (F : C(G, E)) :
    invLpₗᵢ 𝕜 (ContinuousMap.toLp p μ 𝕜 F) =
      ContinuousMap.toLp p μ 𝕜 (F.comp ⟨Inv.inv, continuous_inv⟩) := by
  rw [invLpₗᵢ_apply]
  exact Lp.compMeasurePreserving_toLp 𝕜 F ⟨Inv.inv, continuous_inv⟩
    (Measure.measurePreserving_inv μ)

end Continuous

end TauCeti

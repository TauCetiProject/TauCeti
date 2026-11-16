/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations

/-!
# Four-forms built from the Kähler form on a Hermitian four-space

Let `V` be a four-dimensional real inner product space with an orthogonal complex structure `J`,
oriented as a complex space, and let `ω` be its Kähler form. This file evaluates two wedge
products of forms on a positively oriented unitary frame `e`, `J e₀ = e₁`, `J e₂ = e₃`, through
the Hodge star of `ω` and of the complex line `x ∧ J x`.

## Main results

In the namespace `TauCeti.AlmostComplexStructure`:

* `wedge_alternatingFormEquiv_kahlerForm_apply`: `ω ∧ β = ⟪ω, β⟫ vol`.
* `wedge_wedge_ofSubsingleton_innerSL_apply`:
  `(J x)^♭ ∧ x^♭ ∧ β = (β(x, J x) - ‖x‖² ⟪ω, β⟫) vol`.
-/

public section

open Module exteriorPower ContinuousAlternatingMap
open scoped RealInnerProductSpace

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Fact (finrank ℝ V = 4)]
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hkl : 2 + 2 = finrank ℝ V)

include h₀ h₂ in
/-- **`ω ∧ β = ⟪ω, β⟫ vol`**: the wedge of the Kähler form with a two-form `β`, evaluated on a
positively oriented unitary frame, is the inner product of `ω` with `β`. -/
theorem wedge_alternatingFormEquiv_kahlerForm_apply (β : V [⋀^Fin 2]→L[ℝ] ℝ) :
    wedge (alternatingFormEquiv V 2 J.kahlerForm) β (e ∘ finCongr (hkl.trans Fact.out)) =
      ⟪J.kahlerForm, (alternatingFormEquiv V 2).symm β⟫ := by
  obtain ⟨o, he⟩ : ∃ o, e.toBasis.orientation = o := ⟨_, rfl⟩
  rw [o.wedge_apply_orthonormalBasis even_two hkl e he,
    ← o.alternatingFormInner_formHodgeStar_left even_two, o.formHodgeStar_alternatingFormEquiv,
    hodgeStar_kahlerForm h₀ h₂ hkl he, alternatingFormInner_apply, LinearEquiv.symm_apply_apply]

include h₀ h₂ in
/-- **`(J x)^♭ ∧ x^♭ ∧ β = (β(x, J x) - ‖x‖² ⟪ω, β⟫) vol`**: the wedge of the covectors of `J x`
and `x` with a two-form `β`, evaluated on a positively oriented unitary frame. Here
`β(x, J x) - ‖x‖² ⟪ω, β⟫ = -⟪⋆(x ∧ J x), β⟫`. -/
theorem wedge_wedge_ofSubsingleton_innerSL_apply (x : V) (β : V [⋀^Fin 2]→L[ℝ] ℝ) :
    wedge (wedge (ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ (J x)))
      (ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ x))) β (e ∘ finCongr (hkl.trans Fact.out)) =
      β ![x, J x] - ‖x‖ ^ 2 * ⟪J.kahlerForm, (alternatingFormEquiv V 2).symm β⟫ := by
  obtain ⟨o, he⟩ : ∃ o, e.toBasis.orientation = o := ⟨_, rfl⟩
  have hw : wedge (ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ (J x)))
      (ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ x)) =
        alternatingFormEquiv V 2 (-ιMulti ℝ 2 ![x, J x]) := by
    ext v
    have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
    rw [hv, wedge_apply_one_one, alternatingFormEquiv_apply, inner_neg_left, inner_ιMulti_two]
    simp only [Fin.isValue, ofSubsingleton_apply_apply, Matrix.cons_val_fin_one,
      coe_innerSL_apply, neg_sub]
    ring
  set β₂ := (alternatingFormEquiv V 2).symm β with hβ₂
  have hβ : β = alternatingFormEquiv V 2 β₂ := by rw [hβ₂, LinearEquiv.apply_symm_apply]
  have hsym (y z : ⋀[ℝ]^2 V) : ⟪y, o.hodgeStar hkl z⟫ = ⟪o.hodgeStar hkl y, z⟫ :=
    (o.isSymmetric_hodgeStar_of_even even_two hkl y z).symm
  rw [hw, o.wedge_apply_orthonormalBasis even_two hkl e he, hβ,
    o.formHodgeStar_alternatingFormEquiv, alternatingFormInner_alternatingFormEquiv, hsym, map_neg,
    hodgeStar_ιMulti_apply h₀ h₂ hkl he, alternatingFormEquiv_apply, inner_neg_left,
    inner_sub_left, real_inner_smul_left, real_inner_comm β₂, real_inner_comm β₂]
  ring

end TauCeti.AlmostComplexStructure

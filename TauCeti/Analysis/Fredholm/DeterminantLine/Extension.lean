/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Basic

/-!
# The determinant line of an operator extended by finitely many directions

Let `D₁ : E →L[𝕜] F` have finite-dimensional kernel and cokernel, and let `D₂ : Λ →L[𝕜] F` be a
map from a finite-dimensional space `Λ`. The **extended operator** `D₁.coprod D₂ : E × Λ →L[𝕜] F`,
`(x, l) ↦ D₁ x + D₂ l`, adjoins the directions `D₂` to the domain of `D₁`. Unlike a
stabilization (`ContinuousLinearMap.detLineCoprodEquiv`), it is not assumed to be onto. Its index
is `ind D₁ + dim Λ` (`ContinuousLinearMap.index_coprod`), and the five-term exact sequence

`0 → ker D₁ → ker (D₁.coprod D₂) → Λ → F ⧸ range D₁ → F ⧸ range (D₁.coprod D₂) → 0`

of `TauCeti.Analysis.Fredholm.Parametric` refines this to a canonical isomorphism of determinant
lines

`det (D₁.coprod D₂) ≃ det D₁ ⊗ det Λ`

(`ContinuousLinearMap.detLineCoprodTensorEquiv`), with no choice of bases or complements. It is
the six-term isomorphism `TauCeti.detLineSixTermEquiv` of that sequence followed by the zero space,
whose determinant line is canonically `𝕜`.

Extended operators arise at the ends of Fredholm problems with degenerate asymptotics. When the
asymptotic operator `A_e` at an end has a kernel, one works in a weighted Sobolev space on which
the operator `D` is Fredholm, and adjoins the cutoff extensions `E_e (v) = χ_e v` of the vectors
`v ∈ ker A_e` as free endpoint variables: the extended operator
`(ξ, v) ↦ D ξ + D (E_e v)` is `D.coprod (D ∘ E_e)`. Its determinant line, which orients the moduli
spaces with free asymptotic ends, is then `det D ⊗ det (ker A_e)`.

The identification does not depend on the auxiliary choices made in setting up the extension
(`ContinuousLinearMap.detLineCoprodTensorEquiv_detLineCongr`). An isomorphism
`e : E × Λ' ≃ E × Λ` that fixes `E × 0` pointwise, induces `eΛ : Λ' ≃ Λ` on the second factor and
intertwines `D₁.coprod D₂'` with `D₁.coprod D₂` carries the identification for `D₂'` to that for
`D₂`, through the isomorphism of determinant lines induced by `eΛ`. This covers

* changes of cutoff, where `D₂' = D₂ + D₁ ∘ L` for a linear `L : Λ → E` and
  `e (x, l) = (x + L l, l)`: the cutoff extensions of two cutoff functions differ by a vector of
  the weighted domain;
* relabelings of the free variables, where `D₂' = D₂ ∘ eΛ` and `e = id × eΛ`.

## Main definitions

* `ContinuousLinearMap.detLineCoprodTensorEquiv`: the isomorphism
  `det (D₁.coprod D₂) ≃ det D₁ ⊗ det Λ`.

## Main results

* `ContinuousLinearMap.detLineCoprodTensorEquiv_tmul`: its value on exterior products.
* `ContinuousLinearMap.detLineCoprodTensorEquiv_detLineCongr`: it is natural for changes of the
  extension data fixing `D₁`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant lines of exact sequences).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

open Module TensorProduct

namespace ContinuousLinearMap

variable {𝕜 E Λ F : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [ContinuousAdd F] {D₁ : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F}
  [FiniteDimensional 𝕜 D₁.ker] [FiniteDimensional 𝕜 (F ⧸ D₁.range)] [FiniteDimensional 𝕜 Λ]

attribute [local instance] finiteDimensional_quotient_range_coprod

/-- The zero space closing the five-term sequence of an extension has rank zero. -/
private theorem finrank_punit : finrank 𝕜 PUnit.{1} = 0 :=
  finrank_zero_of_subsingleton

variable (𝕜 Λ) in
/-- The isomorphism `det Λ ⊗ (det 0)^* ≃ det Λ`, through the canonical generator of the
determinant line of the zero space. -/
private noncomputable def detLineTensorDualPUnitEquiv :
    TauCeti.detLine 𝕜 Λ ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 PUnit.{1}) ≃ₗ[𝕜] TauCeti.detLine 𝕜 Λ :=
  TensorProduct.congr (LinearEquiv.refl 𝕜 _)
      ((TauCeti.detLineEquivOfFinrankEqZero finrank_punit).symm.dualMap ≪≫ₗ
        LinearMap.ringLmapEquivSelf 𝕜 𝕜 𝕜) ≪≫ₗ
    TensorProduct.rid 𝕜 _

omit [TopologicalSpace Λ] [FiniteDimensional 𝕜 Λ] in
private theorem detLineTensorDualPUnitEquiv_tmul (γ : TauCeti.detLine 𝕜 Λ) :
    detLineTensorDualPUnitEquiv 𝕜 Λ
        (γ ⊗ₜ (TauCeti.detLineEquivOfFinrankEqZero finrank_punit).toLinearMap) = γ := by
  simp [detLineTensorDualPUnitEquiv]

variable (D₁ D₂) in
/-- The six-term isomorphism `TauCeti.detLineSixTermEquiv` of the exact sequence
`0 → ker D₁ → ker (D₁.coprod D₂) → Λ → F ⧸ range D₁ → F ⧸ range (D₁.coprod D₂) → 0 → 0`
of the extension. -/
private noncomputable def detLineCoprodSixTermEquiv :
    ((D₁.coprod D₂ : E × Λ →L[𝕜] F) : E × Λ →ₗ[𝕜] F).detLine ≃ₗ[𝕜]
      (TauCeti.detLine 𝕜 D₁.ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 (F ⧸ D₁.range))) ⊗[𝕜]
        (TauCeti.detLine 𝕜 Λ ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 PUnit.{1})) :=
  TauCeti.detLineSixTermEquiv (kerCoprodHom_injective D₁ D₂)
    (exact_kerCoprodHom_parameterProj D₁ D₂) (exact_parameterProj_parameterToCoker D₁ D₂)
    (exact_parameterToCoker_cokerCoprodHom D₁ D₂)
    ((LinearMap.exact_zero_iff_surjective PUnit.{1} _).2 (cokerCoprodHom_surjective D₁ D₂))
    (Function.surjective_to_subsingleton _)

variable (D₁ D₂) in
/-- **The determinant line of an extended operator.** For `D₁ : E →L[𝕜] F` with
finite-dimensional kernel and cokernel and finitely many directions `D₂ : Λ →L[𝕜] F`, the
canonical isomorphism `det (D₁.coprod D₂) ≃ det D₁ ⊗ det Λ`. It is `TauCeti.detLineSixTermEquiv`
for the exact sequence
`0 → ker D₁ → ker (D₁.coprod D₂) → Λ → F ⧸ range D₁ → F ⧸ range (D₁.coprod D₂) → 0 → 0`,
followed by the identification of the determinant line of the zero space with `𝕜`; its value on
exterior products is `ContinuousLinearMap.detLineCoprodTensorEquiv_tmul`. The extended operator
need not be onto. -/
noncomputable def detLineCoprodTensorEquiv :
    ((D₁.coprod D₂ : E × Λ →L[𝕜] F) : E × Λ →ₗ[𝕜] F).detLine ≃ₗ[𝕜]
      (D₁ : E →ₗ[𝕜] F).detLine ⊗[𝕜] TauCeti.detLine 𝕜 Λ :=
  detLineCoprodSixTermEquiv D₁ D₂ ≪≫ₗ (detLineTensorDualPUnitEquiv 𝕜 Λ).lTensor _

/-- `ContinuousLinearMap.detLineCoprodTensorEquiv` is the six-term isomorphism of the exact
sequence of the extension, followed by the identification of `det 0` with `𝕜`. -/
private theorem detLineCoprodTensorEquiv_apply
    (t : ((D₁.coprod D₂ : E × Λ →L[𝕜] F) : E × Λ →ₗ[𝕜] F).detLine) :
    detLineCoprodTensorEquiv D₁ D₂ t =
      (detLineTensorDualPUnitEquiv 𝕜 Λ).lTensor _ (detLineCoprodSixTermEquiv D₁ D₂ t) :=
  (rfl)

/-- **The value of `ContinuousLinearMap.detLineCoprodTensorEquiv` on exterior products.** Choose
`u`, a family of `dim (ker D₁)` vectors of `ker D₁`, and families `v`, `w` and `x` in
`ker (D₁.coprod D₂)`, `Λ` and `F ⧸ range D₁` whose images complete them along the exact sequence
`0 → ker D₁ → ker (D₁.coprod D₂) → Λ → F ⧸ range D₁ → F ⧸ range (D₁.coprod D₂) → 0`. Let `β`, `γ`,
`δ` and `ε` be the exterior products in `ker (D₁.coprod D₂)`, `Λ`, `F ⧸ range D₁` and
`F ⧸ range (D₁.coprod D₂)` of the images of `u`, `v`, `w` and `x` followed by `v`, `w`, `x` and
nothing. If `ψ` takes the value `1` at `δ`, then `β ⊗ φ` goes to `φ ε • ((α ⊗ ψ) ⊗ γ)`, with `α`
the exterior product of `u`. -/
theorem detLineCoprodTensorEquiv_tmul (u : Fin (finrank 𝕜 D₁.ker) → D₁.ker)
    (v : Fin (finrank 𝕜 (parameterProj D₁ D₂).range) → (D₁.coprod D₂).ker)
    (w : Fin (finrank 𝕜 (LinearMap.range (parameterToCoker D₁ D₂))) → Λ)
    (x : Fin (finrank 𝕜 (LinearMap.range (cokerCoprodHom D₁ D₂))) → F ⧸ D₁.range)
    {β : TauCeti.detLine 𝕜 (D₁.coprod D₂).ker} (hβ : (β : ExteriorAlgebra 𝕜 (D₁.coprod D₂).ker) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (kerCoprodHom D₁ D₂ ∘ u) v))
    {γ : TauCeti.detLine 𝕜 Λ} (hγ : (γ : ExteriorAlgebra 𝕜 Λ) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (parameterProj D₁ D₂ ∘ v) w))
    {δ : TauCeti.detLine 𝕜 (F ⧸ D₁.range)} (hδ : (δ : ExteriorAlgebra 𝕜 (F ⧸ D₁.range)) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (parameterToCoker D₁ D₂ ∘ w) x))
    {ε : TauCeti.detLine 𝕜 (F ⧸ (D₁.coprod D₂).range)}
    (hε : (ε : ExteriorAlgebra 𝕜 (F ⧸ (D₁.coprod D₂).range)) =
      ExteriorAlgebra.ιMulti 𝕜 _ (cokerCoprodHom D₁ D₂ ∘ x))
    (φ : Dual 𝕜 (TauCeti.detLine 𝕜 (F ⧸ (D₁.coprod D₂).range)))
    {ψ : Dual 𝕜 (TauCeti.detLine 𝕜 (F ⧸ D₁.range))} (hψ : ψ δ = 1) :
    detLineCoprodTensorEquiv D₁ D₂ (β ⊗ₜ φ) =
      φ ε • ((exteriorPower.ιMulti 𝕜 _ u ⊗ₜ ψ) ⊗ₜ γ) := by
  -- The empty family closing the sequence at the zero space.
  set y : Fin (finrank 𝕜 PUnit.{1}) → F ⧸ (D₁.coprod D₂).range := Fin.elim0 ∘ Fin.cast finrank_punit
  have hε' : (ε : ExteriorAlgebra 𝕜 (F ⧸ (D₁.coprod D₂).range)) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (cokerCoprodHom D₁ D₂ ∘ x) y) := by
    rw [hε, ← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  rw [detLineCoprodTensorEquiv_apply, detLineCoprodSixTermEquiv,
    TauCeti.detLineSixTermEquiv_tmul _ _ _ _ _ _ u v w x y hβ hγ hδ hε' φ hψ
      (TauCeti.detLineEquivOfFinrankEqZero_ιMulti finrank_punit _),
    LinearEquiv.map_smul, LinearEquiv.lTensor_tmul, detLineTensorDualPUnitEquiv_tmul]

section Naturality

/-! ### Changing the extension data -/

variable {Λ' : Type*} [AddCommGroup Λ'] [Module 𝕜 Λ'] [TopologicalSpace Λ'] [FiniteDimensional 𝕜 Λ']
  {D₂' : Λ' →L[𝕜] F}

omit [TopologicalSpace Λ] [FiniteDimensional 𝕜 Λ] [TopologicalSpace Λ'] [FiniteDimensional 𝕜 Λ'] in
/-- The identification `det Λ ⊗ (det 0)^* ≃ det Λ`, applied to the second factor, commutes with
the isomorphisms induced by `eΛ : Λ' ≃ Λ` and by identities. -/
private theorem lTensor_detLineTensorDualPUnitEquiv_congr {A B : Type*} [AddCommGroup A]
    [Module 𝕜 A] [AddCommGroup B] [Module 𝕜 B] (eΛ : Λ' ≃ₗ[𝕜] Λ)
    (s : (TauCeti.detLine 𝕜 A ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 B)) ⊗[𝕜]
      (TauCeti.detLine 𝕜 Λ' ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 PUnit.{1}))) :
    (detLineTensorDualPUnitEquiv 𝕜 Λ).lTensor _
        (TensorProduct.congr
          (TensorProduct.congr (LinearEquiv.refl 𝕜 A).detLineCongr
            (LinearEquiv.refl 𝕜 B).detLineCongr.symm.dualMap)
          (TensorProduct.congr eΛ.detLineCongr
            (LinearEquiv.refl 𝕜 PUnit.{1}).detLineCongr.symm.dualMap) s) =
      TensorProduct.congr (LinearEquiv.refl 𝕜 _) eΛ.detLineCongr
        ((detLineTensorDualPUnitEquiv 𝕜 Λ').lTensor _ s) := by
  induction s using TensorProduct.inductionOn with
  | add s₁ s₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul a s =>
    induction s using TensorProduct.inductionOn with
    | add s₁ s₂ h₁ h₂ => simp only [map_add, TensorProduct.tmul_add, h₁, h₂]
    | tmul γ χ => simp [detLineTensorDualPUnitEquiv]

/-- `ContinuousLinearMap.detLineCoprodTensorEquiv_detLineCongr` for given isomorphisms `e₂` of the
kernels and `e₅` of the cokernels of the two extended operators, compatible with the five-term
exact sequences. -/
private theorem detLineCoprodTensorEquiv_congr (eΛ : Λ' ≃ₗ[𝕜] Λ)
    (e₂ : (D₁.coprod D₂').ker ≃ₗ[𝕜] (D₁.coprod D₂).ker)
    (e₅ : (F ⧸ (D₁.coprod D₂').range) ≃ₗ[𝕜] F ⧸ (D₁.coprod D₂).range)
    (h₁ : ∀ x, e₂ (kerCoprodHom D₁ D₂' x) = kerCoprodHom D₁ D₂ x)
    (h₂ : ∀ p, parameterProj D₁ D₂ (e₂ p) = eΛ (parameterProj D₁ D₂' p))
    (h₃ : ∀ l, parameterToCoker D₁ D₂ (eΛ l) = parameterToCoker D₁ D₂' l)
    (h₄ : ∀ z, e₅ (cokerCoprodHom D₁ D₂' z) = cokerCoprodHom D₁ D₂ z)
    (t : ((D₁.coprod D₂' : E × Λ' →L[𝕜] F) : E × Λ' →ₗ[𝕜] F).detLine) :
    detLineCoprodTensorEquiv D₁ D₂
        (TensorProduct.congr e₂.detLineCongr e₅.detLineCongr.symm.dualMap t) =
      TensorProduct.congr (LinearEquiv.refl 𝕜 _) eΛ.detLineCongr
        (detLineCoprodTensorEquiv D₁ D₂' t) := by
  rw [detLineCoprodTensorEquiv_apply, detLineCoprodTensorEquiv_apply,
    ← lTensor_detLineTensorDualPUnitEquiv_congr eΛ]
  refine congrArg ((detLineTensorDualPUnitEquiv 𝕜 Λ).lTensor _) ?_
  -- The exactness data of both sequences is read off `detLineCoprodSixTermEquiv`.
  refine TauCeti.detLineSixTermEquiv_congr _ _ _ _ _ _ _ _ _ _ _ _ (LinearEquiv.refl 𝕜 D₁.ker) e₂
    eΛ (LinearEquiv.refl 𝕜 (F ⧸ D₁.range)) e₅ (LinearEquiv.refl 𝕜 PUnit.{1}) ?_ ?_ ?_ ?_ ?_ t
  exacts [LinearMap.ext fun x ↦ (h₁ x).symm, LinearMap.ext h₂, LinearMap.ext h₃,
    LinearMap.ext fun z ↦ (h₄ z).symm, LinearMap.ext fun _ ↦ rfl]

/-- **Independence of the extension data.** Let `e : E × Λ' ≃ E × Λ` fix `E × 0` pointwise, induce
`eΛ : Λ' ≃ Λ` on the second factor, and intertwine `D₁.coprod D₂'` with `D₁.coprod D₂`. Then
transporting determinant lines along `e` (`LinearMap.detLineCongr`) carries the identification
`det (D₁.coprod D₂') ≃ det D₁ ⊗ det Λ'` to the identification
`det (D₁.coprod D₂) ≃ det D₁ ⊗ det Λ`, through the isomorphism `det Λ' ≃ det Λ` induced by `eΛ`.

For instance `e (x, l) = (x + L l, l)` with `D₂' = D₂ + D₁ ∘ L` changes the cutoff of the
extension, and `e = id × eΛ` with `D₂' = D₂ ∘ eΛ` relabels the free variables. -/
theorem detLineCoprodTensorEquiv_detLineCongr (e : (E × Λ') ≃ₗ[𝕜] E × Λ) (eΛ : Λ' ≃ₗ[𝕜] Λ)
    (heE : ∀ x, e (x, 0) = (x, 0)) (heΛ : ∀ p, (e p).2 = eΛ p.2)
    (hD : ((D₁.coprod D₂ : E × Λ →L[𝕜] F) : E × Λ →ₗ[𝕜] F) ∘ₗ e.toLinearMap =
      (LinearEquiv.refl 𝕜 F).toLinearMap ∘ₗ ((D₁.coprod D₂' : E × Λ' →L[𝕜] F) : E × Λ' →ₗ[𝕜] F))
    (t : ((D₁.coprod D₂' : E × Λ' →L[𝕜] F) : E × Λ' →ₗ[𝕜] F).detLine) :
    detLineCoprodTensorEquiv D₁ D₂ (LinearMap.detLineCongr _ e (LinearEquiv.refl 𝕜 F) hD t) =
      TensorProduct.congr (LinearEquiv.refl 𝕜 _) eΛ.detLineCongr
        (detLineCoprodTensorEquiv D₁ D₂' t) := by
  have hD' (p : E × Λ') : D₁.coprod D₂ (e p) = D₁.coprod D₂' p := LinearMap.congr_fun hD p
  rw [LinearMap.detLineCongr_eq_congr]
  refine detLineCoprodTensorEquiv_congr eΛ _ _ (fun x ↦ Subtype.ext ?_) (fun p ↦ ?_)
    (fun l ↦ ?_) (fun z ↦ ?_) t
  · simp [kerCoprodHom_apply, heE]
  · simp [parameterProj_apply, heΛ]
  · have := hD' (0, l)
    simp only [coprod_apply, map_zero, zero_add, heΛ] at this
    rw [parameterToCoker_apply, parameterToCoker_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq, ← this]
    exact LinearMap.mem_range.2 ⟨-(e (0, l)).1, by simp⟩
  · induction z using Submodule.Quotient.induction_on with
    | H y => simp

end Naturality

end ContinuousLinearMap

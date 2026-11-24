/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.OrientationCover
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Character
import Mathlib.Topology.Homotopy.Lifting

/-!
# Covering monodromy and orientation sign character for Fredholm determinant lines

Specializing `TauCeti.VectorBundleOrientationCover.orientationTransport` and
`TauCeti.VectorBundleOrientationCover.quotientTransport` to the real determinant line bundle
`TauCeti.FredholmDetLine ℝ E F`, and reading fibre orientations as determinant-line rays via
`TauCeti.FredholmDetLine.orientationEquivRay`, defines covering-monodromy transport of determinant
orientations along path homotopy classes (`TauCeti.FredholmDetLine.quotientOrientationTransport`)
and continuous paths (`TauCeti.FredholmDetLine.pathOrientationTransport`) in
`{T : E →L[ℝ] F // T.IsFredholm}`.

Because coherent families on `[[0, 1]]` lift continuously to the orientation double cover
(`TauCeti.isDetLineCoherentOn_iff_continuous_orientationCoverMk`), covering monodromy follows every
coherent family (`TauCeti.IsDetLineCoherentOn.monodromy_orientationCoverMk`). Consequently
`TauCeti.FredholmDetLine.pathOrientationTransport` agrees with the chart-based transport
`TauCeti.detLineOrientationTransport`
(`TauCeti.FredholmDetLine.pathOrientationTransport_mk_eq_detLineOrientationTransport`,
`TauCeti.FredholmDetLine.pathOrientationTransport_apply_eq_map_detLineOrientationTransport`).

Around based loops at `T₀`, transport acts by the orientation character
`TauCeti.FredholmDetLine.orientationMonodromySign : FundamentalGroup _ T₀ →* ℤˣ`
(`TauCeti.FredholmDetLine.quotientOrientationTransport_toPath_eq_smul`).

## Main definitions

* `TauCeti.FredholmDetLine.pathOfContinuousOn`: the `Path` in `{T : E →L[ℝ] F // T.IsFredholm}`
  associated to a continuous Fredholm family on `[[0, 1]]`.
* `TauCeti.FredholmDetLine.quotientOrientationTransport`: determinant-line orientation transport
  along a homotopy class of paths of Fredholm operators.
* `TauCeti.FredholmDetLine.pathOrientationTransport`: determinant-line orientation transport along
  a continuous path of Fredholm operators.
* `TauCeti.FredholmDetLine.orientationMonodromySign`: the loop orientation sign character
  `FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀ →* ℤˣ`.

## Main results

* `TauCeti.IsDetLineCoherentOn.monodromy_orientationCoverMk`: covering monodromy carries the
  initial ray of a coherent family on `[[0, 1]]` to its final ray.
* `TauCeti.FredholmDetLine.pathOrientationTransport_mk_eq_detLineOrientationTransport`,
  `TauCeti.FredholmDetLine.pathOrientationTransport_apply_eq_map_detLineOrientationTransport`:
  covering-monodromy transport agrees with `TauCeti.detLineOrientationTransport`.
* `TauCeti.FredholmDetLine.quotientOrientationTransport_toPath_eq_smul`: loop transport acts by
  `orientationMonodromySign`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

noncomputable section

open ContinuousLinearMap Filter Module Set Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

namespace FredholmDetLine

omit [CompleteSpace E] [CompleteSpace F] in
/-- The bundled path in `{T : E →L[ℝ] F // T.IsFredholm}` determined by a continuous Fredholm
family `T : ℝ → E →L[ℝ] F` on `[[0, 1]]`. -/
def pathOfContinuousOn {T : ℝ → E →L[ℝ] F} (hT : ContinuousOn T (uIcc 0 1))
    (hF : ∀ t ∈ uIcc (0 : ℝ) 1, (T t).IsFredholm) :
    Path (⟨T 0, hF 0 left_mem_uIcc⟩ : {T : E →L[ℝ] F // T.IsFredholm})
      ⟨T 1, hF 1 right_mem_uIcc⟩ where
  toFun t := ⟨T t.val, hF t.val (Icc_subset_uIcc t.property)⟩
  continuous_toFun :=
    (hT.comp_continuous continuous_subtypeVal fun t ↦ Icc_subset_uIcc t.property).subtype_mk _
  source' := rfl
  target' := rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp]
theorem pathOfContinuousOn_apply {T : ℝ → E →L[ℝ] F} (hT : ContinuousOn T (uIcc 0 1))
    (hF : ∀ t ∈ uIcc (0 : ℝ) 1, (T t).IsFredholm) (t : unitInterval) :
    pathOfContinuousOn hT hF t = ⟨T t.val, hF t.val (Icc_subset_uIcc t.property)⟩ := (rfl)

end FredholmDetLine

/-- Along a continuous Fredholm family `T : ℝ → E →L[ℝ] F` on `[[0, 1]]`, covering monodromy of the
orientation double cover carries the initial ray of a coherent family `v` to its final ray. -/
theorem IsDetLineCoherentOn.monodromy_orientationCoverMk
    {T : ℝ → E →L[ℝ] F} {v : ∀ t, (T t : E →ₗ[ℝ] F).detLine}
    (hv : IsDetLineCoherentOn T v (uIcc 0 1))
    (hT : ContinuousOn T (uIcc 0 1)) (hF : ∀ t ∈ uIcc (0 : ℝ) 1, (T t).IsFredholm) :
    (FredholmDetLine.isCoveringMap_orientationCover_proj (E := E) (F := F) (ι := Fin 1)).monodromy
      (.mk (FredholmDetLine.pathOfContinuousOn hT hF))
      ((FredholmDetLine.orientationCoverFiberEquiv (Fin 1) ⟨T 0, hF 0 left_mem_uIcc⟩).symm
        (rayOfNeZero ℝ (v 0) (hv.ne_zero left_mem_uIcc))) =
    ⟨FredholmDetLine.orientationCoverMk (Fin 1) ⟨T 1, hF 1 right_mem_uIcc⟩
      (rayOfNeZero ℝ (v 1) (hv.ne_zero right_mem_uIcc)),
      FredholmDetLine.proj_orientationCoverMk _ _⟩ := by
  obtain ⟨hv_ne, hg⟩ :=
    (isDetLineCoherentOn_iff_continuous_orientationCoverMk (ι := Fin 1) hT hF).1 hv
  let g_sub : uIcc (0 : ℝ) 1 → VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1) :=
    fun x ↦ FredholmDetLine.orientationCoverMk (Fin 1) ⟨T x.val, hF x.val x.property⟩
      (rayOfNeZero ℝ (v x.val) (hv_ne x.val x.property))
  let Γ : C(unitInterval, VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1)) :=
    ⟨fun t ↦ g_sub ⟨t.val, Icc_subset_uIcc t.property⟩,
      hg.comp (continuous_subtypeVal.subtype_mk _)⟩
  have hpΓ : (VectorBundleOrientationCover.proj :
      VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1) → _) ∘ ⇑Γ =
      ⇑(FredholmDetLine.pathOfContinuousOn hT hF) :=
    funext fun _ ↦ FredholmDetLine.proj_orientationCoverMk _ _
  have hΓ0 : Γ 0 = ((FredholmDetLine.orientationCoverFiberEquiv (Fin 1)
      ⟨T 0, hF 0 left_mem_uIcc⟩).symm (rayOfNeZero ℝ (v 0) (hv.ne_zero left_mem_uIcc))).val := by
    rw [FredholmDetLine.orientationCoverFiberEquiv_symm_apply]
    exact congrArg g_sub (Subtype.ext rfl)
  refine Subtype.ext ?_
  rw [(FredholmDetLine.isCoveringMap_orientationCover_proj (E := E) (F := F)
    (ι := Fin 1)).monodromy_eq_apply_one hpΓ hΓ0]
  exact congrArg g_sub (Subtype.ext rfl)

namespace FredholmDetLine

variable {T₀ T₁ T₂ : {T : E →L[ℝ] F // T.IsFredholm}}

/-- **Orientation transport along a path homotopy class.** Obtained by conjugating
`VectorBundleOrientationCover.quotientTransport` of `FredholmDetLine ℝ E F` by
`FredholmDetLine.orientationEquivRay`. -/
def quotientOrientationTransport (γ : Path.Homotopic.Quotient T₀ T₁) :
    Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine ≃ Module.Ray ℝ (T₁.val : E →ₗ[ℝ] F).detLine :=
  (orientationEquivRay (ι := Fin 1) T₀).symm.trans
    ((VectorBundleOrientationCover.quotientTransport (FredholmDetLine ℝ E F)
        (ι := Fin 1) (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) γ).trans
      (orientationEquivRay (ι := Fin 1) T₁))

theorem quotientOrientationTransport_def (γ : Path.Homotopic.Quotient T₀ T₁) :
    quotientOrientationTransport γ =
      (orientationEquivRay (ι := Fin 1) T₀).symm.trans
        ((VectorBundleOrientationCover.quotientTransport (FredholmDetLine ℝ E F)
            (ι := Fin 1) (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) γ).trans
          (orientationEquivRay (ι := Fin 1) T₁)) := (rfl)

-- Kept non-`simp` so `quotientOrientationTransport_neg` / `_units_smul` satisfy `simpNF`.
theorem quotientOrientationTransport_apply (γ : Path.Homotopic.Quotient T₀ T₁)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    quotientOrientationTransport γ r =
      orientationCoverFiberEquiv (Fin 1) T₁
        ((isCoveringMap_orientationCover_proj (E := E) (F := F) (ι := Fin 1)).monodromy γ
          ((orientationCoverFiberEquiv (Fin 1) T₀).symm r)) := by
  simp [quotientOrientationTransport_def, VectorBundleOrientationCover.quotientTransport_apply,
    orientationCoverFiberEquiv_def]

@[simp]
theorem quotientOrientationTransport_refl (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    quotientOrientationTransport (.refl T₀) = Equiv.refl _ := by
  ext r
  simp [quotientOrientationTransport_def]

@[simp]
theorem quotientOrientationTransport_symm (γ : Path.Homotopic.Quotient T₀ T₁) :
    quotientOrientationTransport γ.symm = (quotientOrientationTransport γ).symm := by
  ext r
  simp [quotientOrientationTransport_def]

/-- Concatenation law for orientation transport along path homotopy classes. -/
theorem quotientOrientationTransport_trans
    (γ₁ : Path.Homotopic.Quotient T₀ T₁) (γ₂ : Path.Homotopic.Quotient T₁ T₂) :
    quotientOrientationTransport (γ₁.trans γ₂) =
      (quotientOrientationTransport γ₁).trans (quotientOrientationTransport γ₂) := by
  ext r
  simp [quotientOrientationTransport_def, VectorBundleOrientationCover.quotientTransport_trans]

@[simp]
theorem quotientOrientationTransport_neg (γ : Path.Homotopic.Quotient T₀ T₁)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    quotientOrientationTransport γ (-r) = -quotientOrientationTransport γ r := by
  simp [quotientOrientationTransport_def]

@[simp]
theorem quotientOrientationTransport_units_smul (γ : Path.Homotopic.Quotient T₀ T₁) (u : ℝˣ)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    quotientOrientationTransport γ (u • r) = u • quotientOrientationTransport γ r := by
  simp [quotientOrientationTransport_def]

/-- **Orientation transport along a continuous path of Fredholm operators**, conjugating
`VectorBundleOrientationCover.orientationTransport` of `FredholmDetLine ℝ E F` by
`FredholmDetLine.orientationEquivRay`. -/
def pathOrientationTransport (γ : Path T₀ T₁) :
    Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine ≃ Module.Ray ℝ (T₁.val : E →ₗ[ℝ] F).detLine :=
  quotientOrientationTransport (.mk γ)

theorem pathOrientationTransport_def (γ : Path T₀ T₁) :
    pathOrientationTransport γ = quotientOrientationTransport (.mk γ) := (rfl)

/-- `pathOrientationTransport` is `VectorBundleOrientationCover.orientationTransport` of
`FredholmDetLine ℝ E F`, read on determinant-line rays via `orientationEquivRay`. -/
theorem pathOrientationTransport_eq_orientationTransport (γ : Path T₀ T₁) :
    pathOrientationTransport γ =
      (orientationEquivRay (ι := Fin 1) T₀).symm.trans
        ((VectorBundleOrientationCover.orientationTransport (FredholmDetLine ℝ E F)
            (ι := Fin 1) (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) γ).trans
          (orientationEquivRay (ι := Fin 1) T₁)) := by
  rw [pathOrientationTransport_def, quotientOrientationTransport_def,
    VectorBundleOrientationCover.quotientTransport_mk]

@[simp]
theorem pathOrientationTransport_refl (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    pathOrientationTransport (Path.refl T₀) = Equiv.refl _ := by
  rw [pathOrientationTransport_def, Path.Homotopic.Quotient.mk_refl,
    quotientOrientationTransport_refl]

@[simp]
theorem pathOrientationTransport_symm (γ : Path T₀ T₁) :
    pathOrientationTransport γ.symm = (pathOrientationTransport γ).symm := by
  rw [pathOrientationTransport_def, Path.Homotopic.Quotient.mk_symm,
    quotientOrientationTransport_symm, pathOrientationTransport_def]

/-- Concatenation law for orientation transport along continuous paths of Fredholm operators. -/
theorem pathOrientationTransport_trans (γ₁ : Path T₀ T₁) (γ₂ : Path T₁ T₂) :
    pathOrientationTransport (γ₁.trans γ₂) =
      (pathOrientationTransport γ₁).trans (pathOrientationTransport γ₂) := by
  rw [pathOrientationTransport_def, Path.Homotopic.Quotient.mk_trans,
    quotientOrientationTransport_trans, pathOrientationTransport_def, pathOrientationTransport_def]

/-- **Endpoint-relative homotopy invariance** for `Path`s in `{T : E →L[ℝ] F // T.IsFredholm}`. -/
theorem pathOrientationTransport_eq_of_homotopic {γ₀ γ₁ : Path T₀ T₁} (h : γ₀.Homotopic γ₁) :
    pathOrientationTransport γ₀ = pathOrientationTransport γ₁ := by
  rw [pathOrientationTransport_def, pathOrientationTransport_def, Path.Homotopic.Quotient.eq.2 h]

/-- Compatibility of `pathOrientationTransport` with `Path.cast` along endpoint equalities. -/
theorem pathOrientationTransport_cast {S₀ S₁ T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path S₀ S₁) (h₀ : T₀ = S₀) (h₁ : T₁ = S₁)
    (o : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport (γ.cast h₀ h₁) o =
      Module.Ray.map (LinearMap.detLineCongrOfEq
          (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.val : E →ₗ[ℝ] F)) h₁.symm))
        (pathOrientationTransport γ
          (Module.Ray.map (LinearMap.detLineCongrOfEq
            (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.val : E →ₗ[ℝ] F)) h₀)) o)) := by
  subst h₀
  subst h₁
  simp

@[simp]
theorem pathOrientationTransport_neg (γ : Path T₀ T₁)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport γ (-r) = -pathOrientationTransport γ r :=
  quotientOrientationTransport_neg (.mk γ) r

@[simp]
theorem pathOrientationTransport_units_smul (γ : Path T₀ T₁) (u : ℝˣ)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport γ (u • r) = u • pathOrientationTransport γ r :=
  quotientOrientationTransport_units_smul (.mk γ) u r

/-- **Agreement of covering monodromy and coherent-family transport** on `[[0, 1]]`. -/
theorem pathOrientationTransport_mk_eq_detLineOrientationTransport
    {T : ℝ → E →L[ℝ] F} (hT : ContinuousOn T (uIcc 0 1))
    (hF : ∀ t ∈ uIcc (0 : ℝ) 1, (T t).IsFredholm)
    (o : Module.Ray ℝ (T 0 : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport (pathOfContinuousOn hT hF) o =
      detLineOrientationTransport 0 1 hT hF o := by
  induction o using Module.Ray.ind with | h v₀ hv₀ =>
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_Icc hT hF left_mem_uIcc hv₀
  rw [pathOrientationTransport_def, quotientOrientationTransport_apply,
    hv.monodromy_orientationCoverMk hT hF,
    orientationCoverFiberEquiv_mk' ⟨T 1, hF 1 right_mem_uIcc⟩,
    detLineOrientationTransport_rayOfNeZero hT hF hv]

/-- **Bridge between `pathOrientationTransport` and `detLineOrientationTransport`** along
`γ.extend`. -/
theorem pathOrientationTransport_apply_eq_map_detLineOrientationTransport
    (γ : Path T₀ T₁) (o : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport γ o =
      Module.Ray.map (LinearMap.detLineCongrOfEq
          (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.val : E →ₗ[ℝ] F)) γ.extend_one))
        (detLineOrientationTransport (T := fun t ↦ (γ.extend t).val) 0 1
          (continuous_subtypeVal.comp γ.continuous_extend).continuousOn
          (fun t _ ↦ (γ.extend t).property)
          (Module.Ray.map (LinearMap.detLineCongrOfEq
            (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.val : E →ₗ[ℝ] F))
              γ.extend_zero.symm)) o)) := by
  have hT : ContinuousOn (fun t ↦ (γ.extend t).val) (uIcc 0 1) :=
    (continuous_subtypeVal.comp γ.continuous_extend).continuousOn
  have hF : ∀ t ∈ uIcc (0 : ℝ) 1, ((γ.extend t).val).IsFredholm := fun t _ ↦ (γ.extend t).property
  have hγ : pathOrientationTransport γ = pathOrientationTransport
      ((pathOfContinuousOn hT hF).cast γ.extend_zero.symm γ.extend_one.symm) :=
    congrArg pathOrientationTransport
      (Path.ext (funext fun t ↦ Subtype.ext (congrArg Subtype.val (γ.extend_extends' t).symm)))
  simp only [hγ, pathOrientationTransport_cast]
  congr 1
  exact pathOrientationTransport_mk_eq_detLineOrientationTransport hT hF _

/-- Around any loop homotopy class based at `T₀`, orientation transport either fixes every ray or
reverses every ray. -/
theorem quotientOrientationTransport_eq_self_or_eq_neg (γ : Path.Homotopic.Quotient T₀ T₀) :
    (∀ r, quotientOrientationTransport γ r = r) ∨
      (∀ r, quotientOrientationTransport γ r = -r) := by
  rcases VectorBundleOrientationCover.quotientTransport_eq_self_or_eq_neg
    (F := ℝ) (E := FredholmDetLine ℝ E F) (ι := Fin 1)
    (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) γ with h | h
  · exact .inl fun r ↦ by simp [quotientOrientationTransport_def, h]
  · exact .inr fun r ↦ by simp [quotientOrientationTransport_def, h]

/-- **Orientation monodromy sign character** `FundamentalGroup _ T₀ →* ℤˣ`, defined as
`VectorBundleOrientationCover.orientationCharacter` of `FredholmDetLine ℝ E F`. -/
def orientationMonodromySign (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀ →* ℤˣ :=
  VectorBundleOrientationCover.orientationCharacter ℝ (FredholmDetLine ℝ E F)
    (ι := Fin 1) (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) T₀

theorem orientationMonodromySign_def (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    orientationMonodromySign T₀ =
      VectorBundleOrientationCover.orientationCharacter ℝ (FredholmDetLine ℝ E F)
        (ι := Fin 1) (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) T₀ := (rfl)

/-- Orientation transport along `γ : FundamentalGroup _ T₀` acts on every ray by
`orientationMonodromySign T₀ γ`. -/
theorem quotientOrientationTransport_toPath_eq_smul
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    quotientOrientationTransport γ.toPath r =
      (Units.map (Int.castRingHom ℝ).toMonoidHom (orientationMonodromySign T₀ γ)) • r := by
  simp [quotientOrientationTransport_def,
    VectorBundleOrientationCover.quotientTransport_toPath_eq_smul, orientationMonodromySign_def]

/-- `orientationMonodromySign T₀ γ = 1` iff orientation transport along `γ` fixes `r`. -/
theorem orientationMonodromySign_eq_one_iff_apply
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    orientationMonodromySign T₀ γ = 1 ↔ quotientOrientationTransport γ.toPath r = r := by
  simp [orientationMonodromySign_def,
    VectorBundleOrientationCover.orientationCharacter_eq_one_iff_quotientTransport_eq _ γ
      ((orientationEquivRay (ι := Fin 1) T₀).symm r),
    quotientOrientationTransport_def, Equiv.eq_symm_apply]

/-- `orientationMonodromySign T₀ γ = -1` iff orientation transport along `γ` reverses `r`. -/
theorem orientationMonodromySign_eq_neg_one_iff_apply
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    orientationMonodromySign T₀ γ = -1 ↔ quotientOrientationTransport γ.toPath r = -r := by
  simp only [orientationMonodromySign_def,
    VectorBundleOrientationCover.orientationCharacter_eq_neg_one_iff_quotientTransport_eq _ γ
      ((orientationEquivRay (ι := Fin 1) T₀).symm r),
    quotientOrientationTransport_def, Equiv.trans_apply,
    ← orientationEquivRay_symm_neg, Equiv.eq_symm_apply, iff_self]

/-- `orientationMonodromySign T₀ γ = 1` iff orientation transport along `γ` is the identity. -/
theorem orientationMonodromySign_eq_one_iff
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀) :
    orientationMonodromySign T₀ γ = 1 ↔ quotientOrientationTransport γ.toPath = Equiv.refl _ := by
  obtain ⟨r₀⟩ := (inferInstance : Nonempty (Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine))
  refine ⟨fun h ↦ Equiv.ext fun r ↦ (orientationMonodromySign_eq_one_iff_apply γ r).1 h,
    fun h ↦ (orientationMonodromySign_eq_one_iff_apply γ r₀).2 ?_⟩
  simp [h]

/-- `orientationMonodromySign T₀ γ = -1` iff orientation transport along `γ` reverses every ray. -/
theorem orientationMonodromySign_eq_neg_one_iff
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀) :
    orientationMonodromySign T₀ γ = -1 ↔
      ∀ r, quotientOrientationTransport γ.toPath r = -r := by
  obtain ⟨r₀⟩ := (inferInstance : Nonempty (Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine))
  exact ⟨fun h r ↦ (orientationMonodromySign_eq_neg_one_iff_apply γ r).1 h,
    fun h ↦ (orientationMonodromySign_eq_neg_one_iff_apply γ r₀).2 (h r₀)⟩

end FredholmDetLine

end TauCeti

end

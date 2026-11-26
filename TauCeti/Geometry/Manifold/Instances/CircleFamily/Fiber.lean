/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.CircleFamily
public import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse

/-!
# The fibres of the circle family as smooth circles

The total family `TauCeti.CircleFamily` of the circles `AddCircle p`, `p > 0`, carries the smooth
structure transported from `ℝ_(>0) × AddCircle 1` through its normalization
`N(p, x) = (p, D_(p,1) x)`, where `D_(p,q) : AddCircle p → AddCircle q` is the rescaling
`AddCircle.diffeomorphAddCircle`. This file makes each fibre `{z // z.period = p}` of the period
projection a smooth circle in the same way, and compares it with the circle `AddCircle p` whose
points it contains.

* **The fibre atlas.** The normalized angle `z ↦ (N z).2 = D_(p,1) z.point` is a homeomorphism from
  the fibre over `p` onto the unit-period circle (`TauCeti.CircleFamily.fiberNormalization`). The
  fibre carries the atlas transported from `AddCircle 1` through it, which makes it an analytic
  one-manifold modelled on `ℝ` and makes the normalized angle an analytic diffeomorphism
  (`TauCeti.CircleFamily.fiberNormalizationDiffeomorph`).
* **The fixed-period inclusion.** The inclusion `x ↦ (p, x)` of `AddCircle p` onto the fibre, the
  identity on points, is then an analytic diffeomorphism
  (`TauCeti.CircleFamily.fiberDiffeomorph`); followed by the normalized angle, it is the rescaling
  `D_(p,1)` (`TauCeti.CircleFamily.fiberDiffeomorph_trans_fiberNormalizationDiffeomorph`). So the
  atlas of `AddCircle p`, carried to the fibre by the inclusion, and the transported atlas have the
  same maximal atlases (`TauCeti.CircleFamily.transOpenPartialHomeomorph_mem_maximalAtlas_iff`):
  the two ways of making the fibre a smooth circle agree.
* **The fibre as a submanifold.** The fixed-period inclusion into the total family and the
  inclusion of the fibre are analytic embeddings
  (`TauCeti.CircleFamily.isSmoothEmbedding_mk`,
  `TauCeti.CircleFamily.isSmoothEmbedding_coe_fiber`), and a map into the fibre is `C^n`
  exactly when it is `C^n` as a map into the total family
  (`TauCeti.CircleFamily.contMDiff_fiber_iff`).

No behaviour at period zero is asserted.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.CircleFamily

variable (p : PositivePeriod)

/-! ### The fibre atlas -/

/-- The normalized angle `z ↦ D_(p,1) z.point`, the second component of the normalization, as a
homeomorphism from the fibre of the period projection over `p` onto the unit-period circle. -/
def fiberNormalization : {z : CircleFamily // z.period = p} ≃ₜ AddCircle (1 : ℝ) :=
  (fiberHomeomorph p).symm.trans (AddCircle.diffeomorphAddCircle (p : ℝ) 1 ⊤).toHomeomorph

/-- The normalized angle of a point of a fibre is the rescaling of its circle point to period
one. -/
@[simp]
theorem fiberNormalization_apply (z : {z : CircleFamily // z.period = p}) :
    fiberNormalization p z =
      AddCircle.diffeomorphAddCircle (z.val.period : ℝ) 1 ⊤ z.val.point := by
  obtain ⟨⟨q, x⟩, rfl⟩ := z
  simp only [fiberNormalization, Homeomorph.trans_apply, Diffeomorph.coe_toHomeomorph,
    fiberHomeomorph_symm_apply, retraction_mk]

/-- The normalized angle is the second component of the normalization of the family. -/
theorem fiberNormalization_eq_normalization_snd (n : ℕ∞ω)
    (z : {z : CircleFamily // z.period = p}) :
    fiberNormalization p z = (normalization n z.val).2 := by
  rw [fiberNormalization_apply, normalization_snd]

/-- The inverse of the normalized angle rescales the unit-period circle to period `p`. -/
@[simp]
theorem coe_fiberNormalization_symm_apply (x : AddCircle (1 : ℝ)) :
    ((fiberNormalization p).symm x).val = mk p (AddCircle.diffeomorphAddCircle 1 (p : ℝ) ⊤ x) := by
  simp only [fiberNormalization, Homeomorph.symm_trans_apply, Diffeomorph.coe_toHomeomorph_symm,
    AddCircle.diffeomorphAddCircle_symm, Homeomorph.symm_symm, coe_fiberHomeomorph]

/-- The fibre of the period projection over `p` carries the atlas transported from the
unit-period circle through the normalized angle. -/
instance : ChartedSpace ℝ {z : CircleFamily // z.period = p} :=
  (fiberNormalization p).pullbackChartedSpace

/-- The transported atlas makes the fibre over `p` an analytic one-manifold. -/
instance {n : ℕ∞ω} : IsManifold 𝓘(ℝ) n {z : CircleFamily // z.period = p} :=
  (fiberNormalization p).pullback_isManifold _ n

/-- The normalized angle as a `C^n` diffeomorphism from the fibre over `p` onto the unit-period
circle. -/
def fiberNormalizationDiffeomorph (n : ℕ∞ω) :
    {z : CircleFamily // z.period = p} ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle (1 : ℝ) :=
  (fiberNormalization p).pullbackDiffeomorph 𝓘(ℝ) n

/-- The underlying map of the normalized-angle diffeomorphism is the normalized angle. -/
@[simp]
theorem coe_fiberNormalizationDiffeomorph (n : ℕ∞ω) :
    ⇑(fiberNormalizationDiffeomorph p n) = fiberNormalization p :=
  Homeomorph.coe_pullbackDiffeomorph _ _ _

/-- The underlying homeomorphism of the normalized-angle diffeomorphism is the normalized angle. -/
@[simp]
theorem toHomeomorph_fiberNormalizationDiffeomorph (n : ℕ∞ω) :
    (fiberNormalizationDiffeomorph p n).toHomeomorph = fiberNormalization p :=
  Homeomorph.pullbackDiffeomorph_toHomeomorph _ _ _

/-- The underlying map of the inverse of the normalized-angle diffeomorphism is the inverse of the
normalized angle. -/
@[simp]
theorem coe_fiberNormalizationDiffeomorph_symm (n : ℕ∞ω) :
    ⇑(fiberNormalizationDiffeomorph p n).symm = (fiberNormalization p).symm :=
  Homeomorph.coe_pullbackDiffeomorph_symm _ _ _

/-! ### The fixed-period inclusion -/

/-- **The fixed-period inclusion is a diffeomorphism onto its fibre.** The map `x ↦ (p, x)` from
`AddCircle p` onto the fibre of the period projection over `p`, with the atlas transported from the
unit-period circle, is a `C^n` diffeomorphism. Its underlying homeomorphism is
`TauCeti.CircleFamily.fiberHomeomorph p`, the identity on points. -/
def fiberDiffeomorph (n : ℕ∞ω) :
    AddCircle (p : ℝ) ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ {z : CircleFamily // z.period = p} :=
  (AddCircle.diffeomorphAddCircle (p : ℝ) 1 n).trans (fiberNormalizationDiffeomorph p n).symm

/-- The underlying homeomorphism of the fixed-period inclusion is
`TauCeti.CircleFamily.fiberHomeomorph p`. -/
@[simp]
theorem toHomeomorph_fiberDiffeomorph (n : ℕ∞ω) :
    (fiberDiffeomorph p n).toHomeomorph = fiberHomeomorph p := by
  refine Homeomorph.ext fun x ↦ Subtype.ext ?_
  simp [fiberDiffeomorph]

/-- The underlying map of the fixed-period inclusion is `TauCeti.CircleFamily.fiberHomeomorph p`. -/
theorem coe_fiberDiffeomorph (n : ℕ∞ω) : ⇑(fiberDiffeomorph p n) = fiberHomeomorph p := by
  rw [← Diffeomorph.coe_toHomeomorph, toHomeomorph_fiberDiffeomorph]

/-- The fixed-period inclusion sends `x` to the point `(p, x)` of the family. -/
@[simp]
theorem coe_fiberDiffeomorph_apply (n : ℕ∞ω) (x : AddCircle (p : ℝ)) :
    (fiberDiffeomorph p n x).val = mk p x := by
  rw [coe_fiberDiffeomorph, coe_fiberHomeomorph]

/-- The inverse of the fixed-period inclusion is the retraction of the family onto `AddCircle p`,
restricted to the fibre. -/
@[simp]
theorem fiberDiffeomorph_symm_apply (n : ℕ∞ω) (z : {z : CircleFamily // z.period = p}) :
    (fiberDiffeomorph p n).symm z = retraction p z.val := by
  rw [← Diffeomorph.coe_toHomeomorph_symm, toHomeomorph_fiberDiffeomorph,
    fiberHomeomorph_symm_apply]

/-- **The fixed-period inclusion followed by the normalized angle is the rescaling `D_(p,1)`.** -/
@[simp]
theorem fiberDiffeomorph_trans_fiberNormalizationDiffeomorph (n : ℕ∞ω) :
    (fiberDiffeomorph p n).trans (fiberNormalizationDiffeomorph p n) =
      AddCircle.diffeomorphAddCircle (p : ℝ) 1 n := by
  ext x
  simp only [fiberDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    Diffeomorph.apply_symm_apply]

/-- **The two atlases of a fibre agree.** A chart `e` of `AddCircle p`, carried to the fibre over
`p` by the fixed-period inclusion, lies in the maximal `C^n` atlas of the transported structure of
the fibre exactly when `e` lies in the maximal `C^n` atlas of `AddCircle p`. So the two maximal
atlases correspond under the inclusion, which is the identity on points. -/
theorem transOpenPartialHomeomorph_mem_maximalAtlas_iff (n : ℕ∞ω)
    {e : OpenPartialHomeomorph (AddCircle (p : ℝ)) ℝ} :
    (fiberHomeomorph p).symm.transOpenPartialHomeomorph e ∈
        IsManifold.maximalAtlas 𝓘(ℝ) n {z : CircleFamily // z.period = p} ↔
      e ∈ IsManifold.maximalAtlas 𝓘(ℝ) n (AddCircle (p : ℝ)) := by
  refine ⟨fun he ↦ ?_, fun he ↦ ?_⟩
  · -- Carry the chart back along the inclusion, a diffeomorphism.
    have h := (fiberDiffeomorph p ω).transOpenPartialHomeomorph_mem_maximalAtlas le_top he
    rwa [toHomeomorph_fiberDiffeomorph, ← Homeomorph.trans_transOpenPartialHomeomorph,
      Homeomorph.self_trans_symm, Homeomorph.refl_transOpenPartialHomeomorph] at h
  · have h := (fiberDiffeomorph p ω).symm.transOpenPartialHomeomorph_mem_maximalAtlas le_top he
    rwa [Diffeomorph.symm_toHomeomorph, toHomeomorph_fiberDiffeomorph] at h

/-! ### The fibre as a submanifold of the family -/

/-- The inclusion of the fibre over `p` into the family is analytic. -/
theorem contMDiff_coe_fiber (n : ℕ∞ω) :
    ContMDiff 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) n (Subtype.val : {z : CircleFamily // z.period = p} → _) := by
  have h := (contMDiff_mk p n).comp (fiberDiffeomorph p n).symm.contMDiff
  convert h using 1
  funext z
  simp [mk_retraction z.property]

/-- **The fixed-period circle is an embedded submanifold of the family.** For `1 ≤ n`, the
inclusion `x ↦ (p, x)` of `AddCircle p` into the family is a `C^n` embedding. -/
theorem isSmoothEmbedding_mk {n : ℕ∞ω} (hn : 1 ≤ n) :
    Manifold.IsSmoothEmbedding 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) n (mk p) :=
  (contMDiff_mk p n).isSmoothEmbedding_of_leftInverse hn (contMDiff_retraction p 1)
    (retraction_mk p)

/-- **The fibre is an embedded submanifold of the family.** For `1 ≤ n`, the inclusion of the fibre
over `p`, with its transported atlas, into the family is a `C^n` embedding. -/
theorem isSmoothEmbedding_coe_fiber {n : ℕ∞ω} (hn : 1 ≤ n) :
    Manifold.IsSmoothEmbedding 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) n
      (Subtype.val : {z : CircleFamily // z.period = p} → _) :=
  (contMDiff_coe_fiber p n).isSmoothEmbedding_of_leftInverse hn
    ((fiberDiffeomorph p 1).contMDiff.comp (contMDiff_retraction p 1))
    fun z ↦ by
      rw [Function.comp_apply, ← fiberDiffeomorph_symm_apply p 1, Diffeomorph.apply_symm_apply]

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N] {n : ℕ∞ω}
  {f : N → {z : CircleFamily // z.period = p}}

/-- A map into the fibre over `p` is `C^n` at a point exactly when it is `C^n` there as a map into
the family. -/
theorem contMDiffAt_fiber_iff {x : N} :
    ContMDiffAt J 𝓘(ℝ) n f x ↔ ContMDiffAt J (𝓘(ℝ).prod 𝓘(ℝ)) n (fun y ↦ (f y).val) x := by
  refine ⟨fun hf ↦ (contMDiff_coe_fiber p n (f x)).comp x hf, fun hf ↦ ?_⟩
  -- Recover `f` from the family-valued map through the retraction onto `AddCircle p`.
  have h := ((fiberDiffeomorph p n).contMDiff.comp (contMDiff_retraction p n)).contMDiffAt.comp x hf
  convert h using 1
  funext y
  rw [Function.comp_apply, Function.comp_apply, ← fiberDiffeomorph_symm_apply p n,
    Diffeomorph.apply_symm_apply]

/-- A map into the fibre over `p` is `C^n` exactly when it is `C^n` as a map into the family. -/
theorem contMDiff_fiber_iff :
    ContMDiff J 𝓘(ℝ) n f ↔ ContMDiff J (𝓘(ℝ).prod 𝓘(ℝ)) n (fun y ↦ (f y).val) :=
  forall_congr' fun _ ↦ contMDiffAt_fiber_iff p

end TauCeti.CircleFamily

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Pullback
public import TauCeti.Geometry.Contact.Standard
public import TauCeti.Geometry.Contact.Transition

/-!
# Contactomorphisms

There are three natural notions of symmetry of a contact manifold, of decreasing flexibility.
Let `e : M → N` be a diffeomorphism.

* `e` is a **contactomorphism** from a hyperplane field `ξ` on `M` to a hyperplane field `ξ'` on
  `N` when its differential carries `ξ` onto `ξ'` (`Diffeomorph.IsContactomorphism`). This only
  involves the contact structures, not any contact form, so it also makes sense for contact
  structures that are not cooriented.
* For one-forms `α` on `M` and `α'` on `N`, `e` is a **cooriented contactomorphism** when
  `e^* α' = f α` for a positive function `f` (`Diffeomorph.IsCoorientedContactomorphism`).
* It is a **strict contactomorphism** when `e^* α' = α`
  (`Diffeomorph.IsStrictContactomorphism`).

A strict contactomorphism is cooriented
(`Diffeomorph.IsStrictContactomorphism.isCoorientedContactomorphism`), and a cooriented
contactomorphism is a contactomorphism between the kernels `ξ = ker α` and `ξ' = ker α'`
(`Diffeomorph.IsCoorientedContactomorphism.isContactomorphism`). Conversely, for nowhere vanishing
forms, the contactomorphisms between their kernels are exactly the diffeomorphisms with
`e^* α' = f α` for a unique nowhere vanishing smooth function `f`
(`Diffeomorph.isContactomorphism_kerDistribution_iff`). The sign of `f` records whether `e`
preserves the coorientations. Each notion is closed under identities, composition and inverses.
A strict contactomorphism preserves and reflects contactness
(`Diffeomorph.IsStrictContactomorphism.isContactForm_iff`), as does any cooriented one, and
moreover intertwines the Reeb vector fields
(`Diffeomorph.IsStrictContactomorphism.mfderiv_reebVectorField`), which a mere cooriented
contactomorphism need not do.

The three notions are distinct already for the standard contact form `α = dz - ⟪p, dq⟫` on
`V × V × ℝ`. The dilation `(q, p, z) ↦ (q, 2 p, 2 z)` pulls `α` back to `2 α`, so it is a
cooriented contactomorphism which is not strict
(`TauCeti.exists_isCoorientedContactomorphism_not_isStrictContactomorphism`), and the reflection
`(q, p, z) ↦ (q, -p, -z)` pulls `α` back to `-α`, so it is a contactomorphism which reverses the
coorientation (`TauCeti.exists_isContactomorphism_not_isCoorientedContactomorphism`).

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Sections 1.1, 2.1 and 2.3.
-/

public section

noncomputable section

open TauCeti
open scoped ContDiff Manifold

namespace Diffeomorph

variable {E H M E' H' N E'' H'' P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E'' H''} [TopologicalSpace P] [ChartedSpace H'' P]

/-! ### Contactomorphisms of hyperplane fields -/

section Distribution

variable {ξ : Π x : M, Submodule ℝ (TangentSpace I x)}
  {ξ' : Π y : N, Submodule ℝ (TangentSpace J y)} {ξ'' : Π z : P, Submodule ℝ (TangentSpace K z)}

/-- A diffeomorphism `e : M → N` is a **contactomorphism** from the hyperplane field `ξ` on `M`
to the hyperplane field `ξ'` on `N` when its differential carries `ξ` onto `ξ'`: at every point
`x`, the subspace `ξ x` is the inverse image of `ξ' (e x)` under `d e_x`. No contact form or
coorientation is involved. -/
def IsContactomorphism (e : M ≃ₘ⟮I, J⟯ N) (ξ : Π x : M, Submodule ℝ (TangentSpace I x))
    (ξ' : Π y : N, Submodule ℝ (TangentSpace J y)) : Prop :=
  ∀ x, ξ x = (ξ' (e x)).comap (mfderiv I J e x).toLinearMap

/-- A diffeomorphism is a contactomorphism when a tangent vector lies in `ξ` exactly when its
image under the differential lies in `ξ'`. -/
theorem isContactomorphism_iff {e : M ≃ₘ⟮I, J⟯ N} :
    e.IsContactomorphism ξ ξ' ↔ ∀ x v, v ∈ ξ x ↔ mfderiv I J e x v ∈ ξ' (e x) := by
  simp only [IsContactomorphism, SetLike.ext_iff, Submodule.mem_comap,
    ContinuousLinearMap.coe_coe]

/-- A diffeomorphism is a contactomorphism exactly when its differential maps `ξ` onto `ξ'` at
every point. -/
theorem isContactomorphism_iff_map {e : M ≃ₘ⟮I, J⟯ N} :
    e.IsContactomorphism ξ ξ' ↔ ∀ x, (ξ x).map (mfderiv I J e x).toLinearMap = ξ' (e x) := by
  refine forall_congr' fun x ↦ ?_
  have hbij : Function.Bijective (mfderiv I J e x) := (e.isInvertible_mfderiv (by simp)).bijective
  constructor
  · intro h
    rw [h, Submodule.map_comap_eq_of_surjective hbij.2]
  · intro h
    rw [← h, Submodule.comap_map_eq_of_injective hbij.1]

/-- The identity is a contactomorphism of every hyperplane field. -/
@[simp]
theorem isContactomorphism_refl (ξ : Π x : M, Submodule ℝ (TangentSpace I x)) :
    (Diffeomorph.refl I M ∞).IsContactomorphism ξ ξ := by
  rw [isContactomorphism_iff]
  intro x v
  rw [coe_refl, mfderiv_id, ContinuousLinearMap.id_apply, id_eq]

/-- The composite of contactomorphisms is a contactomorphism. -/
theorem IsContactomorphism.trans {e₁ : M ≃ₘ⟮I, J⟯ N} {e₂ : N ≃ₘ⟮J, K⟯ P}
    (h₁ : e₁.IsContactomorphism ξ ξ') (h₂ : e₂.IsContactomorphism ξ' ξ'') :
    (e₁.trans e₂).IsContactomorphism ξ ξ'' := by
  rw [isContactomorphism_iff] at h₁ h₂ ⊢
  intro x v
  rw [coe_trans, mfderiv_comp_apply x (e₂.mdifferentiable (by simp) _)
    (e₁.mdifferentiable (by simp) x), h₁, h₂]
  -- The base point `(e₂ ∘ e₁) x` is `e₂ (e₁ x)` by definition of composition.
  rfl

/-- The inverse of a contactomorphism is a contactomorphism. -/
theorem IsContactomorphism.symm {e : M ≃ₘ⟮I, J⟯ N} (h : e.IsContactomorphism ξ ξ') :
    e.symm.IsContactomorphism ξ' ξ := by
  rw [isContactomorphism_iff] at h ⊢
  intro y w
  obtain ⟨x, rfl⟩ : ∃ x, e x = y := ⟨e.symm y, e.apply_symm_apply y⟩
  have key := h x (mfderiv J I e.symm (e x) w)
  rw [e.mfderiv_apply_mfderiv_symm_apply (by simp)] at key
  -- The base points `e.symm (e x)` and `x` agree, and all tangent spaces are the model space.
  have hx : ∀ v : E, v ∈ ξ (e.symm (e x)) ↔ v ∈ ξ x := by
    rw [e.symm_apply_apply]
    exact fun _ ↦ Iff.rfl
  exact key.symm.trans (hx _).symm

end Distribution

/-! ### Cooriented and strict contactomorphisms of one-forms -/

section Form

variable [IsManifold I ∞ M] [IsManifold J ∞ N] [IsManifold K ∞ P]
  {e : M ≃ₘ⟮I, J⟯ N} {α : SmoothForm I M ℝ 1} {α' : SmoothForm J N ℝ 1}
  {α'' : SmoothForm K P ℝ 1}

/-- A diffeomorphism `e : M → N` is a **cooriented contactomorphism** from the one-form `α` on `M`
to the one-form `α'` on `N` when `e^* α' = f α` for a positive function `f`. For contact forms,
it preserves the contact structures together with the coorientations given by the forms. -/
def IsCoorientedContactomorphism (e : M ≃ₘ⟮I, J⟯ N) (α : SmoothForm I M ℝ 1)
    (α' : SmoothForm J N ℝ 1) : Prop :=
  ∃ f : M → ℝ, (∀ x, 0 < f x) ∧ ∀ x, mpullback I J e α'.1 x = f x • α.1 x

/-- A diffeomorphism `e : M → N` is a **strict contactomorphism** from the one-form `α` on `M` to
the one-form `α'` on `N` when `e^* α' = α`. -/
def IsStrictContactomorphism (e : M ≃ₘ⟮I, J⟯ N) (α : SmoothForm I M ℝ 1)
    (α' : SmoothForm J N ℝ 1) : Prop :=
  mpullback I J e α'.1 = α.1

/-- The defining property of a cooriented contactomorphism. -/
theorem isCoorientedContactomorphism_iff :
    e.IsCoorientedContactomorphism α α' ↔
      ∃ f : M → ℝ, (∀ x, 0 < f x) ∧ ∀ x, mpullback I J e α'.1 x = f x • α.1 x :=
  Iff.rfl

/-- The defining equation of a strict contactomorphism. -/
theorem isStrictContactomorphism_iff :
    e.IsStrictContactomorphism α α' ↔ mpullback I J e α'.1 = α.1 :=
  Iff.rfl

/-- A diffeomorphism is a strict contactomorphism exactly when it pulls `α'` back to `α` as
smooth forms. -/
theorem isStrictContactomorphism_iff_smoothForm_mpullback_eq :
    e.IsStrictContactomorphism α α' ↔ SmoothForm.mpullback e e.contMDiff α' = α := by
  rw [isStrictContactomorphism_iff, ← SmoothForm.coe_mpullback, Subtype.ext_iff]

/-- A diffeomorphism pulling `α'` back to a nowhere vanishing multiple of `α` is a
contactomorphism from `ker α` to `ker α'`, whatever the signs of the multiplier. -/
theorem isContactomorphism_kerDistribution_of_mpullback_eq_smul {f : M → ℝ}
    (hf : ∀ x, f x ≠ 0) (h : ∀ x, mpullback I J e α'.1 x = f x • α.1 x) :
    e.IsContactomorphism α.kerDistribution α'.kerDistribution := by
  intro x
  rw [← SmoothForm.kerDistribution_mpullback e e.contMDiff α' x]
  exact congrFun (SmoothForm.kerDistribution_of_eq_smul hf fun x ↦ by
    rw [SmoothForm.coe_mpullback]
    exact h x).symm x

/-- **Contactomorphisms are conformal on defining forms.** For nowhere vanishing one-forms `α` and
`α'`, a diffeomorphism is a contactomorphism from `ker α` to `ker α'` exactly when it pulls `α'`
back to `f α` for a unique smooth nowhere vanishing function `f`. -/
theorem isContactomorphism_kerDistribution_iff (hα : ∀ x, α.1 x ≠ 0) (hα' : ∀ y, α'.1 y ≠ 0) :
    e.IsContactomorphism α.kerDistribution α'.kerDistribution ↔
      ∃! f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ (∀ x, f x ≠ 0) ∧
        ∀ x, mpullback I J e α'.1 x = f x • α.1 x := by
  have hβ (x : M) : (SmoothForm.mpullback e e.contMDiff α').1 x ≠ 0 := by
    rw [SmoothForm.coe_mpullback]
    intro h0
    -- A vanishing pullback forces `α'` to vanish at `e x`, since `d e_x` is surjective.
    exact hα' (e x) ((mpullback_apply_eq_mpullback_apply_iff («ω» := α'.1) (η := 0)
      (e.isInvertible_mfderiv (by simp)).surjective).1 (by rw [h0, mpullback_zero]; rfl))
  have key := SmoothForm.kerDistribution_eq_iff_existsUnique_fun_smul hα hβ
  simp only [SmoothForm.coe_mpullback] at key
  rw [← key]
  constructor
  · intro h
    funext x
    rw [SmoothForm.kerDistribution_mpullback, ← h x]
  · intro h x
    rw [← SmoothForm.kerDistribution_mpullback e e.contMDiff α' x, h]

/-- A cooriented contactomorphism is a contactomorphism of the kernels. -/
theorem IsCoorientedContactomorphism.isContactomorphism
    (h : e.IsCoorientedContactomorphism α α') :
    e.IsContactomorphism α.kerDistribution α'.kerDistribution := by
  obtain ⟨f, hf, hfe⟩ := h
  exact isContactomorphism_kerDistribution_of_mpullback_eq_smul (fun x ↦ (hf x).ne') hfe

/-- A strict contactomorphism is cooriented, with multiplier `1`. -/
theorem IsStrictContactomorphism.isCoorientedContactomorphism
    (h : e.IsStrictContactomorphism α α') : e.IsCoorientedContactomorphism α α' :=
  ⟨1, fun _ ↦ one_pos, fun x ↦ by rw [h, Pi.one_apply, one_smul]⟩

/-- A strict contactomorphism is a contactomorphism of the kernels. -/
theorem IsStrictContactomorphism.isContactomorphism (h : e.IsStrictContactomorphism α α') :
    e.IsContactomorphism α.kerDistribution α'.kerDistribution :=
  h.isCoorientedContactomorphism.isContactomorphism

/-- The identity is a strict contactomorphism of every one-form. -/
@[simp]
theorem isStrictContactomorphism_refl (α : SmoothForm I M ℝ 1) :
    (Diffeomorph.refl I M ∞).IsStrictContactomorphism α α := by
  rw [isStrictContactomorphism_iff, coe_refl, mpullback_id]

/-- The identity is a cooriented contactomorphism of every one-form. -/
@[simp]
theorem isCoorientedContactomorphism_refl (α : SmoothForm I M ℝ 1) :
    (Diffeomorph.refl I M ∞).IsCoorientedContactomorphism α α :=
  (isStrictContactomorphism_refl α).isCoorientedContactomorphism

/-- The composite of strict contactomorphisms is a strict contactomorphism. -/
theorem IsStrictContactomorphism.trans {e₁ : M ≃ₘ⟮I, J⟯ N} {e₂ : N ≃ₘ⟮J, K⟯ P}
    (h₁ : e₁.IsStrictContactomorphism α α') (h₂ : e₂.IsStrictContactomorphism α' α'') :
    (e₁.trans e₂).IsStrictContactomorphism α α'' := by
  rw [isStrictContactomorphism_iff, coe_trans,
    mpullback_comp (e₁.mdifferentiable (by simp)) (e₂.mdifferentiable (by simp)), h₂, h₁]

/-- The composite of cooriented contactomorphisms is a cooriented contactomorphism; the
multipliers multiply. -/
theorem IsCoorientedContactomorphism.trans {e₁ : M ≃ₘ⟮I, J⟯ N} {e₂ : N ≃ₘ⟮J, K⟯ P}
    (h₁ : e₁.IsCoorientedContactomorphism α α') (h₂ : e₂.IsCoorientedContactomorphism α' α'') :
    (e₁.trans e₂).IsCoorientedContactomorphism α α'' := by
  obtain ⟨f, hf, hfe⟩ := h₁
  obtain ⟨g, hg, hge⟩ := h₂
  refine ⟨fun x ↦ g (e₁ x) * f x, fun x ↦ mul_pos (hg _) (hf x), fun x ↦ ?_⟩
  rw [coe_trans, mpullback_comp (e₁.mdifferentiable (by simp)) (e₂.mdifferentiable (by simp)),
    show mpullback J K e₂ α''.1 = fun y ↦ g y • α'.1 y from funext hge, mpullback_fun_smul]
  simp only [hfe, smul_smul]

/-- The inverse of a strict contactomorphism is a strict contactomorphism. -/
theorem IsStrictContactomorphism.symm (h : e.IsStrictContactomorphism α α') :
    e.symm.IsStrictContactomorphism α' α := by
  rw [isStrictContactomorphism_iff, ← h, mpullback_symm_mpullback (by simp)]

/-- The inverse of a cooriented contactomorphism is a cooriented contactomorphism; its multiplier
is the reciprocal of the original multiplier, read through the inverse. -/
theorem IsCoorientedContactomorphism.symm (h : e.IsCoorientedContactomorphism α α') :
    e.symm.IsCoorientedContactomorphism α' α := by
  obtain ⟨f, hf, hfe⟩ := h
  refine ⟨fun y ↦ (f (e.symm y))⁻¹, fun y ↦ inv_pos.2 (hf _), fun y ↦ ?_⟩
  have hα : α.1 = fun x ↦ (f x)⁻¹ • mpullback I J e α'.1 x := funext fun x ↦ by
    rw [hfe, smul_smul, inv_mul_cancel₀ (hf x).ne', one_smul]
  rw [hα, mpullback_fun_smul, mpullback_symm_mpullback (by simp)]

/-- Strict contactomorphisms preserve and reflect contactness. -/
theorem IsStrictContactomorphism.isContactForm_iff (h : e.IsStrictContactomorphism α α') :
    α.IsContactForm ↔ α'.IsContactForm := by
  rw [← e.isContactForm_mpullback_iff α',
    isStrictContactomorphism_iff_smoothForm_mpullback_eq.1 h]

/-- **Strict contactomorphisms intertwine the Reeb vector fields.** -/
theorem IsStrictContactomorphism.mfderiv_reebVectorField [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] (h : e.IsStrictContactomorphism α α') (hα' : α'.IsContactForm)
    (x : M) : mfderiv I J e x (α.reebVectorField x) = α'.reebVectorField (e x) := by
  rw [← isStrictContactomorphism_iff_smoothForm_mpullback_eq.1 h]
  exact hα'.mfderiv_reebVectorField_mpullback e e.contMDiff
    (fun _ ↦ (e.isInvertible_mfderiv (by simp)).bijective) x

end Form

end Diffeomorph

/-! ### The three notions are distinct -/

namespace TauCeti

section Examples

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The linear diffeomorphism `(q, p, z) ↦ (q, c p, c z)` of `V × V × ℝ`, for a unit `c`. -/
private def fiberScaling (c : ℝˣ) : (V × V × ℝ) ≃ₘ⟮𝓘(ℝ, V × V × ℝ), 𝓘(ℝ, V × V × ℝ)⟯ (V × V × ℝ) :=
  ((ContinuousLinearEquiv.refl ℝ V).prodCongr
    (ContinuousLinearEquiv.smulLeft c : (V × ℝ) ≃L[ℝ] V × ℝ)).toDiffeomorph

/-- The scaling `(q, p, z) ↦ (q, c p, c z)` pulls the standard contact form back to `c` times
itself. -/
private theorem mpullback_fiberScaling (c : ℝˣ) :
    mpullback 𝓘(ℝ, V × V × ℝ) 𝓘(ℝ, V × V × ℝ) (fiberScaling V c) (innerProductContactForm V).1 =
      ((c : ℝ) • innerProductContactForm V).1 := by
  have hcoe : ⇑(fiberScaling V c) =
      fun x : V × V × ℝ ↦ (x.1, (c : ℝ) • x.2.1, (c : ℝ) • x.2.2) := by
    funext x
    simp [fiberScaling, Units.smul_def, Prod.ext_iff]
  rw [hcoe, mpullback_innerProductContactForm_smul]

/-- The unit vector `(0, 0, 1)` of the `z`-axis, tangent to `V × V × ℝ` at the origin. -/
private def zAxis : TangentSpace 𝓘(ℝ, V × V × ℝ) (0 : V × V × ℝ) :=
  ((0 : V), (0 : V), (1 : ℝ))

/-- The standard contact form at the origin does not vanish on the unit vector of the `z`-axis. -/
private theorem innerProductContactForm_zero_apply :
    (innerProductContactForm V).1 0 ![zAxis V] = 1 := by
  simpa [zAxis] using innerProductContactForm_apply V 0 (zAxis V)

/-- **Cooriented contactomorphisms need not be strict.** The dilation
`(q, p, z) ↦ (q, 2 p, 2 z)` of `V × V × ℝ` pulls the standard contact form `α` back to `2 α`. -/
theorem exists_isCoorientedContactomorphism_not_isStrictContactomorphism :
    ∃ e : (V × V × ℝ) ≃ₘ⟮𝓘(ℝ, V × V × ℝ), 𝓘(ℝ, V × V × ℝ)⟯ (V × V × ℝ),
      e.IsCoorientedContactomorphism (innerProductContactForm V) (innerProductContactForm V) ∧
        ¬ e.IsStrictContactomorphism (innerProductContactForm V) (innerProductContactForm V) := by
  have hc : (2 : ℝ) ≠ 0 := two_ne_zero
  refine ⟨fiberScaling V (Units.mk0 2 hc), ⟨fun _ ↦ 2, fun _ ↦ two_pos, fun x ↦ ?_⟩, fun h ↦ ?_⟩
  · rw [mpullback_fiberScaling, Units.val_mk0, SmoothForm.smul_toRoughForm, Pi.smul_apply]
  · rw [Diffeomorph.isStrictContactomorphism_iff, mpullback_fiberScaling] at h
    have h₀ := congrArg (fun β ↦ β 0 ![zAxis V]) h
    simp only [Units.val_mk0, SmoothForm.smul_toRoughForm, Pi.smul_apply,
      ContinuousAlternatingMap.smul_apply, innerProductContactForm_zero_apply, smul_eq_mul,
      mul_one] at h₀
    norm_num at h₀

/-- **Contactomorphisms need not be cooriented.** The reflection `(q, p, z) ↦ (q, -p, -z)` of
`V × V × ℝ` pulls the standard contact form `α` back to `-α`, so it preserves the standard contact
structure `ker α` but reverses its coorientation. -/
theorem exists_isContactomorphism_not_isCoorientedContactomorphism :
    ∃ e : (V × V × ℝ) ≃ₘ⟮𝓘(ℝ, V × V × ℝ), 𝓘(ℝ, V × V × ℝ)⟯ (V × V × ℝ),
      e.IsContactomorphism (innerProductContactForm V).kerDistribution
          (innerProductContactForm V).kerDistribution ∧
        ¬ e.IsCoorientedContactomorphism (innerProductContactForm V)
          (innerProductContactForm V) := by
  have hc : (-1 : ℝ) ≠ 0 := by norm_num
  have hpull (x : V × V × ℝ) :
      mpullback 𝓘(ℝ, V × V × ℝ) 𝓘(ℝ, V × V × ℝ) (fiberScaling V (Units.mk0 (-1) hc))
        (innerProductContactForm V).1 x = (-1 : ℝ) • (innerProductContactForm V).1 x := by
    rw [mpullback_fiberScaling, Units.val_mk0, SmoothForm.smul_toRoughForm, Pi.smul_apply]
  refine ⟨fiberScaling V (Units.mk0 (-1) hc),
    Diffeomorph.isContactomorphism_kerDistribution_of_mpullback_eq_smul (fun _ ↦ hc) hpull, ?_⟩
  rintro ⟨f, hf, hfe⟩
  have h₀ := congrArg (fun β ↦ β ![zAxis V]) ((hpull 0).symm.trans (hfe 0))
  simp only [ContinuousAlternatingMap.smul_apply, innerProductContactForm_zero_apply,
    smul_eq_mul, mul_one] at h₀
  linarith [hf 0]

end Examples

end TauCeti

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

Let `α` be a one-form on `M`, `β` a one-form on `N`, and `e : M ≃ N` a diffeomorphism. There are
three successively stronger ways in which `e` can respect the contact data, distinguished in
Geiges' book:

* `e` is a **contactomorphism** (`Diffeomorph.IsContactomorphism`) when it carries the hyperplane
  field `ker α` onto `ker β`, that is, when `e^* β` and `α` have the same kernels. Only the
  hyperplane fields enter, not the forms.
* `e` **preserves the coorientation** (`Diffeomorph.PreservesCoorientation`) when `e^* β` is a
  positive multiple of `α` at every point. The coorientation of `ker α` given by `α` is then
  carried to the coorientation of `ker β` given by `β`.
* `e` is a **strict contactomorphism** (`Diffeomorph.IsStrictContactomorphism`) when
  `e^* β = α`.

Each notion is closed under identities, composition and inverses, and each implies the previous
one. When `α` vanishes nowhere the first two are expressed by a smooth multiplier: `e` is a
contactomorphism exactly when `e^* β = f α` for a unique nowhere vanishing smooth function `f`
(`Diffeomorph.isContactomorphism_iff_existsUnique_fun_smul`), and it preserves the coorientation
exactly when moreover `f > 0` (`Diffeomorph.preservesCoorientation_iff_exists_fun_smul`). On a
connected manifold the multiplier has constant sign, so a contactomorphism preserves either the
coorientation given by `β` or the opposite one given by `-β`
(`Diffeomorph.IsContactomorphism.preservesCoorientation_or_neg`). A contactomorphism preserves
and reflects contactness (`Diffeomorph.IsContactomorphism.isContactForm_iff`), and a strict
contactomorphism carries the Reeb vector field of `α` to that of `β`
(`Diffeomorph.IsStrictContactomorphism.mfderiv_reebVectorField`).

The three notions are distinct. On the standard contact space `V × V × ℝ` with the form
`α = dz - ⟪p, dq⟫`, the linear map `(q, p, z) ↦ (q, c p, c z)` for a nonzero real `c` pulls `α`
back to `c α`. It is a contactomorphism for every `c ≠ 0`, it preserves the coorientation exactly
when `c > 0`, and it is strict exactly when `c = 1`
(`TauCeti.isContactomorphism_innerProductContactForm_of_coe_eq`,
`TauCeti.preservesCoorientation_innerProductContactForm_iff_of_coe_eq`,
`TauCeti.isStrictContactomorphism_innerProductContactForm_iff_of_coe_eq`).

## Main definitions

* `Diffeomorph.IsContactomorphism e α β`: `e` carries `ker α` onto `ker β`.
* `Diffeomorph.PreservesCoorientation e α β`: `e^* β` is a positive multiple of `α` at every
  point.
* `Diffeomorph.IsStrictContactomorphism e α β`: `e^* β = α`.

## Main results

* `Diffeomorph.isContactomorphism_iff`,
  `Diffeomorph.isContactomorphism_iff_map_kerDistribution`: pointwise descriptions of
  contactomorphisms by the differential.
* `Diffeomorph.isContactomorphism_iff_existsUnique_fun_smul`,
  `Diffeomorph.preservesCoorientation_iff_exists_fun_smul`: descriptions by smooth multipliers.
* `Diffeomorph.IsContactomorphism.preservesCoorientation_or_neg`: on a connected manifold, a
  contactomorphism preserves or reverses the coorientation.
* `TauCeti.exists_isContactomorphism_not_preservesCoorientation`,
  `TauCeti.exists_preservesCoorientation_not_isStrictContactomorphism`: the three notions differ.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Sections 1.1 and 2.1.
-/

public section

noncomputable section

open scoped ContDiff Manifold InnerProductSpace

open TauCeti

variable {E H M F H' N G H'' P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ G H''} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]

namespace Diffeomorph

variable (e : M ≃ₘ⟮I, J⟯ N) (α : SmoothForm I M ℝ 1) (β : SmoothForm J N ℝ 1)

/-- A diffeomorphism `e : M ≃ N` is a **contactomorphism** from `ker α` to `ker β` when the
pulled-back form `e^* β` has the same kernel hyperplanes as `α`. Equivalently, the differential of
`e` carries each hyperplane `ker α_x` onto `ker β_(e x)`
(`Diffeomorph.isContactomorphism_iff_map_kerDistribution`). Only the hyperplane fields enter, not
the forms or their coorientations. -/
def IsContactomorphism : Prop :=
  (SmoothForm.mpullback e e.contMDiff β).kerDistribution = α.kerDistribution

/-- A diffeomorphism `e : M ≃ N` **preserves the coorientation** from `α` to `β` when at every
point the pulled-back covector `(e^* β)_x` is a positive multiple of `α_x`. For nowhere vanishing
forms this says that `e` is a contactomorphism carrying the coorientation of `ker α` given by `α`
to the coorientation of `ker β` given by `β`. -/
def PreservesCoorientation : Prop :=
  ∀ x, ∃ c : ℝ, 0 < c ∧ (SmoothForm.mpullback e e.contMDiff β).1 x = c • α.1 x

/-- A diffeomorphism `e : M ≃ N` is a **strict contactomorphism** from `α` to `β` when it pulls
`β` back to `α`. -/
def IsStrictContactomorphism : Prop :=
  SmoothForm.mpullback e e.contMDiff β = α

variable {e α β}

/-- A contactomorphism is a diffeomorphism under which `e^* β` and `α` have the same kernels. -/
theorem isContactomorphism_def :
    e.IsContactomorphism α β ↔
      (SmoothForm.mpullback e e.contMDiff β).kerDistribution = α.kerDistribution :=
  Iff.rfl

/-- A diffeomorphism preserves the coorientation when `e^* β` is a positive multiple of `α` at
every point. -/
theorem preservesCoorientation_def :
    e.PreservesCoorientation α β ↔
      ∀ x, ∃ c : ℝ, 0 < c ∧ (SmoothForm.mpullback e e.contMDiff β).1 x = c • α.1 x :=
  Iff.rfl

/-- A strict contactomorphism is a diffeomorphism pulling `β` back to `α`. -/
theorem isStrictContactomorphism_def :
    e.IsStrictContactomorphism α β ↔ SmoothForm.mpullback e e.contMDiff β = α :=
  Iff.rfl

/-! ### Contactomorphisms -/

/-- A diffeomorphism is a contactomorphism exactly when its differential at each point carries a
tangent vector into the hyperplane of `β` precisely when the vector lies in the hyperplane of
`α`. -/
theorem isContactomorphism_iff :
    e.IsContactomorphism α β ↔ ∀ x (v : TangentSpace I x),
      mfderiv I J e x v ∈ β.kerDistribution (e x) ↔ v ∈ α.kerDistribution x := by
  simp only [IsContactomorphism, funext_iff, SmoothForm.kerDistribution_mpullback,
    Submodule.ext_iff, Submodule.mem_comap, ContinuousLinearMap.coe_coe]

/-- A diffeomorphism is a contactomorphism exactly when its differential at each point maps the
hyperplane of `α` onto the hyperplane of `β`. -/
theorem isContactomorphism_iff_map_kerDistribution :
    e.IsContactomorphism α β ↔ ∀ x,
      (α.kerDistribution x).map (mfderiv I J e x : TangentSpace I x →ₗ[ℝ] TangentSpace J (e x)) =
        β.kerDistribution (e x) := by
  have hbij (x : M) := (e.isInvertible_mfderiv (by simp) (x := x)).bijective
  simp only [IsContactomorphism, funext_iff, SmoothForm.kerDistribution_mpullback]
  refine forall_congr' fun x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]
    exact Submodule.map_comap_eq_of_surjective (hbij x).2 _
  · rw [← h]
    exact Submodule.comap_map_eq_of_injective (hbij x).1 _

/-- The differential of a contactomorphism maps the hyperplane of `α` onto the hyperplane of
`β`. -/
theorem IsContactomorphism.map_kerDistribution (h : e.IsContactomorphism α β) (x : M) :
    (α.kerDistribution x).map (mfderiv I J e x : TangentSpace I x →ₗ[ℝ] TangentSpace J (e x)) =
      β.kerDistribution (e x) :=
  isContactomorphism_iff_map_kerDistribution.mp h x

variable (α) in
/-- The identity is a contactomorphism. -/
@[simp]
theorem isContactomorphism_refl : (Diffeomorph.refl I M ∞).IsContactomorphism α α := by
  simp [IsContactomorphism]

/-- The composite of two contactomorphisms is a contactomorphism. -/
theorem IsContactomorphism.trans {γ : SmoothForm K P ℝ 1} {e' : N ≃ₘ⟮J, K⟯ P}
    (h : e.IsContactomorphism α β) (h' : e'.IsContactomorphism β γ) :
    (e.trans e').IsContactomorphism α γ := by
  rw [IsContactomorphism, SmoothForm.mpullback_trans, ← h]
  funext x
  rw [SmoothForm.kerDistribution_mpullback, h', ← SmoothForm.kerDistribution_mpullback]

/-- The inverse of a contactomorphism is a contactomorphism. -/
theorem IsContactomorphism.symm (h : e.IsContactomorphism α β) :
    e.symm.IsContactomorphism β α := by
  rw [IsContactomorphism]
  conv_rhs => rw [← SmoothForm.mpullback_symm_mpullback e β]
  funext y
  rw [SmoothForm.kerDistribution_mpullback, SmoothForm.kerDistribution_mpullback, h]

/-- Being a contactomorphism depends only on the hyperplane field of the target form, not on its
coorientation. -/
@[simp]
theorem isContactomorphism_neg_right :
    e.IsContactomorphism α (-β) ↔ e.IsContactomorphism α β := by
  simp only [IsContactomorphism, map_neg, SmoothForm.kerDistribution_neg]

/-- Being a contactomorphism is unchanged by rescaling the target form by a nonzero constant. -/
@[simp]
theorem isContactomorphism_smul_right {c : ℝ} (hc : c ≠ 0) :
    e.IsContactomorphism α (c • β) ↔ e.IsContactomorphism α β := by
  simp only [IsContactomorphism, map_smul, SmoothForm.kerDistribution_smul hc]

/-- For a nowhere vanishing form `α`: a diffeomorphism is a contactomorphism exactly when it pulls
`β` back to `f α` for a unique nowhere vanishing smooth function `f`. -/
theorem isContactomorphism_iff_existsUnique_fun_smul (hα : ∀ x, α.1 x ≠ 0) :
    e.IsContactomorphism α β ↔
      ∃! f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ (∀ x, f x ≠ 0) ∧
        ∀ x, (SmoothForm.mpullback e e.contMDiff β).1 x = f x • α.1 x :=
  SmoothForm.kerDistribution_eq_iff_existsUnique_fun_smul hα

/-- A contactomorphism preserves and reflects contactness. -/
theorem IsContactomorphism.isContactForm_iff (h : e.IsContactomorphism α β) :
    α.IsContactForm ↔ β.IsContactForm := by
  rw [← e.isContactForm_mpullback_iff β]
  exact ⟨fun hα ↦ hα.isContactForm_of_kerDistribution_eq h,
    fun hβ ↦ hβ.isContactForm_of_kerDistribution_eq (Eq.symm h)⟩

/-! ### Coorientation-preserving contactomorphisms -/

/-- A diffeomorphism preserving the coorientation is a contactomorphism. -/
theorem PreservesCoorientation.isContactomorphism (h : e.PreservesCoorientation α β) :
    e.IsContactomorphism α β := by
  funext x
  obtain ⟨c, hc, hx⟩ := h x
  ext v
  simp only [SmoothForm.mem_kerDistribution, hx, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    mul_eq_zero, hc.ne', false_or]

/-- The composite of two coorientation-preserving diffeomorphisms preserves the coorientation. -/
theorem PreservesCoorientation.trans {γ : SmoothForm K P ℝ 1} {e' : N ≃ₘ⟮J, K⟯ P}
    (h : e.PreservesCoorientation α β) (h' : e'.PreservesCoorientation β γ) :
    (e.trans e').PreservesCoorientation α γ := by
  intro x
  obtain ⟨c, hc, hx⟩ := h x
  obtain ⟨c', hc', hx'⟩ := h' (e x)
  refine ⟨c' * c, mul_pos hc' hc, ?_⟩
  rw [SmoothForm.mpullback_trans, (SmoothForm.mpullback_apply_eq_smul_iff e _ _ c' x).mpr hx', hx,
    smul_smul]

/-- The inverse of a coorientation-preserving diffeomorphism preserves the coorientation. -/
theorem PreservesCoorientation.symm (h : e.PreservesCoorientation α β) :
    e.symm.PreservesCoorientation β α := by
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  obtain ⟨c, hc, hx⟩ := h x
  -- Both sides pull back along `e` to `α`, and pullback at `x` is injective.
  refine ⟨c⁻¹, inv_pos.mpr hc, (SmoothForm.mpullback_apply_eq_smul_iff e _ _ _ x).mp ?_⟩
  rw [SmoothForm.mpullback_mpullback_symm, hx, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-- For a nowhere vanishing form `α`: a diffeomorphism preserves the coorientation exactly when
it pulls `β` back to `f α` for a positive smooth function `f`. -/
theorem preservesCoorientation_iff_exists_fun_smul (hα : ∀ x, α.1 x ≠ 0) :
    e.PreservesCoorientation α β ↔
      ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ (∀ x, 0 < f x) ∧
        ∀ x, (SmoothForm.mpullback e e.contMDiff β).1 x = f x • α.1 x := by
  refine ⟨fun h ↦ ?_, fun ⟨f, _, hf, hmul⟩ x ↦ ⟨f x, hf x, hmul x⟩⟩
  obtain ⟨f, ⟨hf, -, hmul⟩, -⟩ :=
    (isContactomorphism_iff_existsUnique_fun_smul hα).mp h.isContactomorphism
  refine ⟨f, hf, fun x ↦ ?_, hmul⟩
  obtain ⟨c, hc, hx⟩ := h x
  have hcf : c = f x := smul_left_injective ℝ (hα x) (hx.symm.trans (hmul x))
  exact hcf ▸ hc

/-- On a connected manifold, a contactomorphism from a nowhere vanishing form either preserves
the coorientation given by `β` or the opposite coorientation given by `-β`: its multiplier is a
continuous nowhere vanishing function, so it has constant sign. -/
theorem IsContactomorphism.preservesCoorientation_or_neg [PreconnectedSpace M]
    (h : e.IsContactomorphism α β) (hα : ∀ x, α.1 x ≠ 0) :
    e.PreservesCoorientation α β ∨ e.PreservesCoorientation α (-β) := by
  obtain ⟨f, ⟨hf, hf₀, hmul⟩, -⟩ := (isContactomorphism_iff_existsUnique_fun_smul hα).mp h
  by_cases hpos : ∀ x, 0 < f x
  · exact .inl fun x ↦ ⟨f x, hpos x, hmul x⟩
  · right
    obtain ⟨y, hy⟩ := not_forall.mp hpos
    have hneg (x : M) : f x < 0 := by
      by_contra hx
      obtain ⟨z, hz⟩ := intermediate_value_univ y x hf.continuous ⟨not_lt.mp hy, not_lt.mp hx⟩
      exact hf₀ z hz
    intro x
    refine ⟨-f x, neg_pos.mpr (hneg x), ?_⟩
    rw [map_neg, SmoothForm.neg_toRoughForm, Pi.neg_apply, hmul, neg_smul]

/-! ### Strict contactomorphisms -/

/-- A strict contactomorphism preserves the coorientation. -/
theorem IsStrictContactomorphism.preservesCoorientation (h : e.IsStrictContactomorphism α β) :
    e.PreservesCoorientation α β :=
  fun x ↦ ⟨1, one_pos, by rw [h, one_smul]⟩

/-- A strict contactomorphism is a contactomorphism. -/
theorem IsStrictContactomorphism.isContactomorphism (h : e.IsStrictContactomorphism α β) :
    e.IsContactomorphism α β :=
  h.preservesCoorientation.isContactomorphism

variable (α) in
/-- The identity is a strict contactomorphism. -/
@[simp]
theorem isStrictContactomorphism_refl :
    (Diffeomorph.refl I M ∞).IsStrictContactomorphism α α := by
  simp [IsStrictContactomorphism]

variable (α) in
/-- The identity preserves the coorientation. -/
@[simp]
theorem preservesCoorientation_refl : (Diffeomorph.refl I M ∞).PreservesCoorientation α α :=
  (isStrictContactomorphism_refl α).preservesCoorientation

/-- The composite of two strict contactomorphisms is a strict contactomorphism. -/
theorem IsStrictContactomorphism.trans {γ : SmoothForm K P ℝ 1} {e' : N ≃ₘ⟮J, K⟯ P}
    (h : e.IsStrictContactomorphism α β) (h' : e'.IsStrictContactomorphism β γ) :
    (e.trans e').IsStrictContactomorphism α γ := by
  rw [IsStrictContactomorphism, SmoothForm.mpullback_trans, h', h]

/-- The inverse of a strict contactomorphism is a strict contactomorphism. -/
theorem IsStrictContactomorphism.symm (h : e.IsStrictContactomorphism α β) :
    e.symm.IsStrictContactomorphism β α :=
  SmoothForm.mpullback_symm_eq_of_mpullback_eq h

/-- The differential of a strict contactomorphism carries the Reeb vector field of `α` to the Reeb
vector field of `β`. -/
theorem IsStrictContactomorphism.mfderiv_reebVectorField [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (h : e.IsStrictContactomorphism α β) (hβ : β.IsContactForm)
    (x : M) :
    mfderiv I J e x (α.reebVectorField x) = β.reebVectorField (e x) := by
  subst h
  exact hβ.mfderiv_reebVectorField_mpullback e e.contMDiff
    (fun _ ↦ (e.isInvertible_mfderiv (by simp)).bijective) x

end Diffeomorph

/-! ### The standard contact form -/

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem mpullback_innerProductContactForm_of_coe_eq {c : ℝ}
    {e : (V × V × ℝ) ≃ₘ[ℝ] (V × V × ℝ)} (he : ⇑e = fun x ↦ (x.1, c • x.2)) :
    SmoothForm.mpullback e e.contMDiff (innerProductContactForm V) =
      c • innerProductContactForm V := by
  apply Subtype.ext
  rw [SmoothForm.coe_mpullback, he, mpullback_innerProductContactForm_smul]

/-- For `c ≠ 0`, a diffeomorphism `(q, p, z) ↦ (q, c p, c z)` of the standard contact space is a
contactomorphism. -/
theorem isContactomorphism_innerProductContactForm_of_coe_eq {c : ℝ} (hc : c ≠ 0)
    {e : (V × V × ℝ) ≃ₘ[ℝ] (V × V × ℝ)} (he : ⇑e = fun x ↦ (x.1, c • x.2)) :
    e.IsContactomorphism (innerProductContactForm V) (innerProductContactForm V) := by
  rw [Diffeomorph.IsContactomorphism, mpullback_innerProductContactForm_of_coe_eq he]
  exact SmoothForm.kerDistribution_smul hc

/-- A diffeomorphism `(q, p, z) ↦ (q, c p, c z)` of the standard contact space preserves the
coorientation exactly when `c > 0`. -/
theorem preservesCoorientation_innerProductContactForm_iff_of_coe_eq {c : ℝ}
    {e : (V × V × ℝ) ≃ₘ[ℝ] (V × V × ℝ)} (he : ⇑e = fun x ↦ (x.1, c • x.2)) :
    e.PreservesCoorientation (innerProductContactForm V) (innerProductContactForm V) ↔ 0 < c := by
  rw [Diffeomorph.PreservesCoorientation, mpullback_innerProductContactForm_of_coe_eq he]
  refine ⟨fun h ↦ ?_, fun hc x ↦ ⟨c, hc, by rw [SmoothForm.smul_toRoughForm, Pi.smul_apply]⟩⟩
  obtain ⟨d, hd, h₀⟩ := h 0
  have hcd : c = d :=
    smul_left_injective ℝ ((isContactForm_innerProductContactForm V).apply_ne_zero 0) h₀
  exact hcd ▸ hd

/-- A diffeomorphism `(q, p, z) ↦ (q, c p, c z)` of the standard contact space is a strict
contactomorphism exactly when `c = 1`. -/
theorem isStrictContactomorphism_innerProductContactForm_iff_of_coe_eq {c : ℝ}
    {e : (V × V × ℝ) ≃ₘ[ℝ] (V × V × ℝ)} (he : ⇑e = fun x ↦ (x.1, c • x.2)) :
    e.IsStrictContactomorphism (innerProductContactForm V) (innerProductContactForm V) ↔
      c = 1 := by
  rw [Diffeomorph.IsStrictContactomorphism, mpullback_innerProductContactForm_of_coe_eq he]
  refine ⟨fun h ↦ ?_, fun hc ↦ by rw [hc, one_smul]⟩
  have h₀ := congrArg (fun β : SmoothForm 𝓘(ℝ, V × V × ℝ) (V × V × ℝ) ℝ 1 ↦ β.1 0) h
  rw [SmoothForm.smul_toRoughForm, Pi.smul_apply] at h₀
  exact smul_left_injective ℝ ((isContactForm_innerProductContactForm V).apply_ne_zero 0)
    (h₀.trans (one_smul ℝ _).symm)

/-- For every `c ≠ 0` the map `(q, p, z) ↦ (q, c p, c z)` is a diffeomorphism. -/
private theorem exists_diffeomorph_coe_eq {c : ℝ} (hc : c ≠ 0) :
    ∃ e : (V × V × ℝ) ≃ₘ[ℝ] (V × V × ℝ), ⇑e = fun x ↦ (x.1, c • x.2) :=
  ⟨((ContinuousLinearEquiv.refl ℝ V).prodCongr
    (ContinuousLinearEquiv.smulLeft (Units.mk0 c hc))).toDiffeomorph, by
      funext x
      simp [Units.smul_def]⟩

/-- Not every contactomorphism preserves the coorientation: `(q, p, z) ↦ (q, -p, -z)` reverses
the coorientation of the standard contact structure. -/
theorem exists_isContactomorphism_not_preservesCoorientation :
    ∃ e : (V × V × ℝ) ≃ₘ[ℝ] (V × V × ℝ),
      e.IsContactomorphism (innerProductContactForm V) (innerProductContactForm V) ∧
        ¬ e.PreservesCoorientation (innerProductContactForm V) (innerProductContactForm V) := by
  obtain ⟨e, he⟩ := exists_diffeomorph_coe_eq (V := V) (c := -1) (by norm_num)
  refine ⟨e, isContactomorphism_innerProductContactForm_of_coe_eq (by norm_num) he, ?_⟩
  rw [preservesCoorientation_innerProductContactForm_iff_of_coe_eq he]
  norm_num

/-- Not every coorientation-preserving contactomorphism is strict: `(q, p, z) ↦ (q, 2 p, 2 z)`
pulls the standard contact form `α` back to `2 α`. -/
theorem exists_preservesCoorientation_not_isStrictContactomorphism :
    ∃ e : (V × V × ℝ) ≃ₘ[ℝ] (V × V × ℝ),
      e.PreservesCoorientation (innerProductContactForm V) (innerProductContactForm V) ∧
        ¬ e.IsStrictContactomorphism (innerProductContactForm V) (innerProductContactForm V) := by
  obtain ⟨e, he⟩ := exists_diffeomorph_coe_eq (V := V) (c := 2) (by norm_num)
  refine ⟨e, (preservesCoorientation_innerProductContactForm_iff_of_coe_eq he).mpr (by norm_num),
    ?_⟩
  rw [isStrictContactomorphism_innerProductContactForm_iff_of_coe_eq he]
  norm_num

end TauCeti

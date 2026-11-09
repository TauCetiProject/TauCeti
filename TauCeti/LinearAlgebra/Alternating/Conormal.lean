/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code, Codex
-/
module

public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.LinearAlgebra.Multilinear.Quotient

/-!
# Conormal alternating forms

For a submodule `W` of `M`, the conormal forms are the alternating forms on `M` that vanish as
soon as one argument lies in `W`. When `M ⧸ W` is a finite-dimensional real vector space and
the form degree equals its dimension, a ray of such forms orients the quotient from the
conormal side, without passing to the quotient module. Conormality of a ray does not depend on
the representing form, and reversing a ray preserves it.

Pullback from the quotient identifies alternating forms on `M ⧸ W` with conormal
forms on `M` via `Submodule.conormalFormsEquiv`. In the top degree of the quotient, any two
conormal orientations agree up to reversal (`Module.Ray.IsConormal.eq_or_eq_neg`), by descending
along the injective pullback `Submodule.conormalPullback` and applying Mathlib's
`Orientation.eq_or_eq_neg`.

## Attribution

Adapted from `Mei/LinearAlgebra/Alternating/Conormal.lean` in
[Mei](https://github.com/yuma-mizuno-lean/Mei) at commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0). Original copyright and author credit are
retained. The evaluation signs of a ray, which the source develops in the same file, are omitted.
-/

public section

variable {R M ι : Type*}

namespace Submodule

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- The alternating forms on `M` that vanish as soon as one argument lies in `W`. -/
def conormalForms (W : Submodule R M) (ι : Type*) : Submodule R (M [⋀^ι]→ₗ[R] R) where
  carrier := {α | ∀ (v : ι → M) (j : ι), v j ∈ W → α v = 0}
  add_mem' {α β} hα hβ v j hv := by simp [hα v j hv, hβ v j hv]
  zero_mem' _ _ _ := rfl
  smul_mem' c α hα v j hv := by simp [hα v j hv]

/-- Membership in `conormalForms` is vanishing on every tuple with an argument in `W`. -/
@[simp]
theorem mem_conormalForms {W : Submodule R M} {α : M [⋀^ι]→ₗ[R] R} :
    α ∈ W.conormalForms ι ↔ ∀ (v : ι → M) (j : ι), v j ∈ W → α v = 0 := Iff.rfl

/-- Every alternating form is conormal to the zero submodule. -/
@[simp]
theorem conormalForms_bot : (⊥ : Submodule R M).conormalForms ι = ⊤ := by
  ext α
  simp only [mem_conormalForms, mem_bot, Submodule.mem_top, iff_true]
  exact fun v j hv => α.map_coord_zero j hv

/-- A conormal form depends only on the classes of its arguments modulo the submodule. -/
theorem conormalForms_apply_eq_of_sub_mem [Finite ι] {W : Submodule R M}
    {α : M [⋀^ι]→ₗ[R] R} (hα : α ∈ W.conormalForms ι) {x y : ι → M}
    (hxy : ∀ j, x j - y j ∈ W) : α x = α y :=
  α.toMultilinearMap.apply_eq_of_mkQ_eq (fun _ => W)
    (fun _ j _ hx => hα _ j (by simp [hx])) fun j => (Submodule.Quotient.eq W).mpr (hxy j)

/-- A conormal form descends to an alternating form on the quotient. -/
theorem exists_compLinearMap_mkQ_eq [Finite ι] {W : Submodule R M} {α : M [⋀^ι]→ₗ[R] R}
    (hα : α ∈ W.conormalForms ι) : ∃ β : (M ⧸ W) [⋀^ι]→ₗ[R] R, β.compLinearMap W.mkQ = α := by
  classical
  have hf : ∀ [DecidableEq ι] (m : ι → M) (j : ι) (x : M), x ∈ W →
      α.toMultilinearMap (Function.update m j x) = 0 := fun _ j _ hx => hα _ j (by simp [hx])
  refine ⟨{ α.toMultilinearMap.liftQ (fun _ => W) hf with
    map_eq_zero_of_eq' := fun v i j hij hne => ?_ }, AlternatingMap.ext fun v => ?_⟩
  · have := α.toMultilinearMap.liftQ_apply (fun _ => W) hf fun k => (v k).out
    simp only [Submodule.Quotient.mk_out] at this
    exact this.trans (α.map_eq_zero_of_eq _ (congrArg Quotient.out hij) hne)
  · exact α.toMultilinearMap.liftQ_apply (fun _ => W) hf v

/-- Pullback of alternating forms along the quotient map `M → M ⧸ W`. -/
def conormalPullback (W : Submodule R M) :
    ((M ⧸ W) [⋀^ι]→ₗ[R] R) →ₗ[R] (M [⋀^ι]→ₗ[R] R) where
  toFun α := α.compLinearMap W.mkQ
  map_add' α β := AlternatingMap.add_compLinearMap α β W.mkQ
  map_smul' c α := AlternatingMap.ext fun v => by simp

@[simp]
theorem conormalPullback_apply (W : Submodule R M) (α : (M ⧸ W) [⋀^ι]→ₗ[R] R) :
    W.conormalPullback α = α.compLinearMap W.mkQ := (rfl)

theorem conormalPullback_injective (W : Submodule R M) :
    Function.Injective (W.conormalPullback (ι := ι)) := fun _ _ he =>
  AlternatingMap.compLinearMap_injective W.mkQ W.mkQ_surjective he

/-- The pullback of a form on the quotient is conormal. -/
theorem conormalPullback_mem (W : Submodule R M) (α : (M ⧸ W) [⋀^ι]→ₗ[R] R) :
    W.conormalPullback α ∈ W.conormalForms ι := by
  intro v j hv
  apply α.map_coord_zero j
  exact (Submodule.Quotient.mk_eq_zero W).mpr hv

variable [Finite ι]

/-- Pullback to conormal forms is bijective. -/
theorem conormalPullback_codRestrict_bijective (W : Submodule R M) :
    Function.Bijective
      (W.conormalPullback.codRestrict (W.conormalForms ι) W.conormalPullback_mem) :=
  ⟨fun _ _ he => W.conormalPullback_injective (congrArg Subtype.val he), fun α =>
    let ⟨β, hβ⟩ := exists_compLinearMap_mkQ_eq α.property
    ⟨β, Subtype.ext hβ⟩⟩

/-- Pullback from the quotient identifies alternating forms with conormal forms.
This is the linear version of orienting a normal quotient by conormal forms. -/
noncomputable def conormalFormsEquiv (W : Submodule R M) :
    ((M ⧸ W) [⋀^ι]→ₗ[R] R) ≃ₗ[R] W.conormalForms ι :=
  LinearEquiv.ofBijective _ W.conormalPullback_codRestrict_bijective

@[simp]
theorem conormalFormsEquiv_apply (W : Submodule R M) (α : (M ⧸ W) [⋀^ι]→ₗ[R] R) :
    (W.conormalFormsEquiv α).val = α.compLinearMap W.mkQ := by
  rw [conormalFormsEquiv, LinearEquiv.ofBijective_apply, LinearMap.codRestrict_apply,
    conormalPullback_apply]

end CommRing

end Submodule

namespace Module.Ray

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M] [Module R M]

/-- A ray of alternating forms is conormal to `W` when it is represented by a form vanishing as
soon as one argument lies in `W`. By `isConormal_rayOfNeZero_iff`, every representative then
vanishes in this way. -/
def IsConormal (o : Module.Ray R (M [⋀^ι]→ₗ[R] R)) (W : Submodule R M) : Prop :=
  o.someVector ∈ W.conormalForms ι

/-- A ray is conormal exactly when any representing form is a conormal form. -/
@[simp]
theorem isConormal_rayOfNeZero_iff {α : M [⋀^ι]→ₗ[R] R} (hα : α ≠ 0) {W : Submodule R M} :
    (rayOfNeZero R α hα).IsConormal W ↔ α ∈ W.conormalForms ι := by
  have hβ := Module.Ray.someVector_ne_zero (rayOfNeZero R α hα)
  have hβα : SameRay R (rayOfNeZero R α hα).someVector α :=
    (ray_eq_iff hβ hα).mp (Module.Ray.someVector_ray _)
  obtain ⟨r, -, hr⟩ := hβα.exists_pos_left hβ hα
  obtain ⟨s, -, hs⟩ := hβα.symm.exists_pos_left hα hβ
  rw [IsConormal]
  exact ⟨fun hmem => hr ▸ Submodule.smul_mem _ r hmem,
    fun hmem => hs ▸ Submodule.smul_mem _ s hmem⟩

/-- Reversing a ray does not change conormality. -/
@[simp]
theorem isConormal_neg_iff {o : Module.Ray R (M [⋀^ι]→ₗ[R] R)} {W : Submodule R M} :
    (-o).IsConormal W ↔ o.IsConormal W := by
  induction o using Module.Ray.ind with
  | h α hα =>
    rw [neg_rayOfNeZero, isConormal_rayOfNeZero_iff, isConormal_rayOfNeZero_iff,
      Submodule.neg_mem_iff]

/-- Every ray of alternating forms is conormal to the zero submodule. -/
@[simp]
theorem isConormal_bot (o : Module.Ray R (M [⋀^ι]→ₗ[R] R)) : o.IsConormal ⊥ := by
  rw [IsConormal, Submodule.conormalForms_bot]
  exact Submodule.mem_top

/-- A conormal ray is the pullback of a ray of alternating forms on the quotient. -/
theorem IsConormal.exists_eq_rayOfNeZero_conormalPullback [Finite ι]
    {o : Module.Ray R (M [⋀^ι]→ₗ[R] R)} {W : Submodule R M} (ho : o.IsConormal W) :
    ∃ (α : (M ⧸ W) [⋀^ι]→ₗ[R] R) (hα : α ≠ 0),
      o = rayOfNeZero R (W.conormalPullback α)
        ((map_ne_zero_iff _ (W.conormalPullback_injective)).mpr hα) := by
  obtain ⟨α, hα⟩ := Submodule.exists_compLinearMap_mkQ_eq ho
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact o.someVector_ne_zero (by rw [← hα]; simp)
  refine ⟨α, hα0, ?_⟩
  rw [← o.someVector_ray]
  congr
  exact hα.symm

/-- Two conormal orientations in the top degree of a finite-dimensional normal
quotient agree up to reversal. -/
theorem IsConormal.eq_or_eq_neg [Fintype ι] {o p : Module.Ray R (M [⋀^ι]→ₗ[R] R)}
    {W : Submodule R M} [FiniteDimensional R (M ⧸ W)]
    (ho : o.IsConormal W) (hp : p.IsConormal W)
    (hk : finrank R (M ⧸ W) = Fintype.card ι) : o = p ∨ o = -p := by
  obtain ⟨α, hα, rfl⟩ := ho.exists_eq_rayOfNeZero_conormalPullback
  obtain ⟨β, hβ, rfl⟩ := hp.exists_eq_rayOfNeZero_conormalPullback
  -- Descend to genuine orientations of the quotient, then pull their rays back.
  rcases Orientation.eq_or_eq_neg (rayOfNeZero R α hα) (rayOfNeZero R β hβ) hk.symm
    with he | he
  · exact Or.inl ((ray_eq_iff _ _).mpr (((ray_eq_iff hα hβ).mp he).map W.conormalPullback))
  · right
    rw [neg_rayOfNeZero] at he
    rw [neg_rayOfNeZero, ray_eq_iff]
    simpa only [map_neg] using
      ((ray_eq_iff hα (neg_ne_zero.mpr hβ)).mp he).map W.conormalPullback

end Module.Ray

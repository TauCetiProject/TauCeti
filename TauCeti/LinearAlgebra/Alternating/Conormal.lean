/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code, Codex
-/
module

public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Basic

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
through this equivalence and applying Mathlib's `Orientation.eq_or_eq_neg`.

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
    (hxy : ∀ j, x j - y j ∈ W) : α x = α y := by
  classical
  let := Fintype.ofFinite ι
  have he : x = (x - y) + y := (sub_add_cancel x y).symm
  rw [he, ← α.coe_multilinearMap, MultilinearMap.map_add_univ]
  rw [Finset.sum_eq_single ∅ ?_ (by simp)]
  · simp
  · intro s _ hs
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    exact hα _ j (by simpa [Finset.piecewise, hj] using hxy j)

variable [Finite ι]

/-- Pullback from the quotient identifies alternating forms with conormal forms.
This is the linear version of orienting a normal quotient by conormal forms. -/
noncomputable def conormalFormsEquiv (W : Submodule R M) :
    ((M ⧸ W) [⋀^ι]→ₗ[R] R) ≃ₗ[R] W.conormalForms ι := by
  classical
  exact LinearEquiv.ofBijective
    ({ toFun α := ⟨α.compLinearMap W.mkQ, by
        intro v j hv
        apply α.map_coord_zero j
        exact (Submodule.Quotient.mk_eq_zero W).mpr hv⟩
       map_add' := fun _ _ => Subtype.ext (AlternatingMap.add_compLinearMap _ _ _)
       map_smul' := fun _ _ => Subtype.ext (by ext v; rfl) } :
      ((M ⧸ W) [⋀^ι]→ₗ[R] R) →ₗ[R] W.conormalForms ι)
    ⟨fun α β he => AlternatingMap.compLinearMap_injective W.mkQ W.mkQ_surjective
      (congrArg Subtype.val he), by
      intro α
      let f : (ι → M ⧸ W) → R := fun v => α.val (fun j => (v j).out)
      have hf (v : ι → M) : f (W.mkQ ∘ v) = α.val v := by
        apply conormalForms_apply_eq_of_sub_mem α.property
        intro j
        exact (Submodule.Quotient.eq W).mp (Submodule.Quotient.mk_out _)
      have hsurj : Function.Surjective (fun v : ι → M => W.mkQ ∘ v) := by
        intro v
        exact ⟨fun j => (v j).out, funext fun j => Submodule.Quotient.mk_out (v j)⟩
      let β : (M ⧸ W) [⋀^ι]→ₗ[R] R :=
        { toFun := f
          map_update_add' := by
            intro _ v j x y
            obtain ⟨v, rfl⟩ := hsurj v
            obtain ⟨x, rfl⟩ := W.mkQ_surjective x
            obtain ⟨y, rfl⟩ := W.mkQ_surjective y
            simp only [← map_add, ← Function.comp_update, hf, α.val.map_update_add]
          map_update_smul' := by
            intro _ v j c x
            obtain ⟨v, rfl⟩ := hsurj v
            obtain ⟨x, rfl⟩ := W.mkQ_surjective x
            simp only [← map_smul, ← Function.comp_update, hf, α.val.map_update_smul]
          map_eq_zero_of_eq' := fun v j l hjl hne =>
            α.val.map_eq_zero_of_eq _ (congrArg Quotient.out hjl) hne }
      exact ⟨β, Subtype.ext (AlternatingMap.ext hf)⟩⟩

@[simp]
theorem conormalFormsEquiv_apply (W : Submodule R M) (α : (M ⧸ W) [⋀^ι]→ₗ[R] R) :
    (W.conormalFormsEquiv α).val = α.compLinearMap W.mkQ := (rfl)

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
theorem isConormal_bot (o : Module.Ray R (M [⋀^ι]→ₗ[R] R)) : o.IsConormal ⊥ := by
  rw [IsConormal, Submodule.conormalForms_bot]
  exact Submodule.mem_top

/-- Two conormal orientations in the top degree of a finite-dimensional normal
quotient agree up to reversal. -/
theorem IsConormal.eq_or_eq_neg [Fintype ι] {o p : Module.Ray R (M [⋀^ι]→ₗ[R] R)}
    {W : Submodule R M} [FiniteDimensional R (M ⧸ W)]
    (ho : o.IsConormal W) (hp : p.IsConormal W)
    (hk : finrank R (M ⧸ W) = Fintype.card ι) : o = p ∨ o = -p := by
  let α := W.conormalFormsEquiv.symm ⟨o.someVector, ho⟩
  let β := W.conormalFormsEquiv.symm ⟨p.someVector, hp⟩
  let f := (W.conormalForms ι).subtype ∘ₗ W.conormalFormsEquiv.toLinearMap
  have hα : f α = o.someVector :=
    congrArg Subtype.val (W.conormalFormsEquiv.apply_symm_apply _)
  have hβ : f β = p.someVector :=
    congrArg Subtype.val (W.conormalFormsEquiv.apply_symm_apply _)
  have hα0 : α ≠ 0 := by
    intro hz
    exact o.someVector_ne_zero (by rw [← hα, hz, map_zero])
  have hβ0 : β ≠ 0 := by
    intro hz
    exact p.someVector_ne_zero (by rw [← hβ, hz, map_zero])
  -- Descend to genuine orientations of the quotient, then pull their rays back.
  rcases Orientation.eq_or_eq_neg (rayOfNeZero R α hα0) (rayOfNeZero R β hβ0) hk.symm
    with he | he
  · left
    have hs := ((ray_eq_iff hα0 hβ0).mp he).map f
    rw [hα, hβ] at hs
    simpa only [Module.Ray.someVector_ray] using
      (ray_eq_iff o.someVector_ne_zero p.someVector_ne_zero).mpr hs
  · right
    rw [neg_rayOfNeZero] at he
    have hs := ((ray_eq_iff hα0 (neg_ne_zero.mpr hβ0)).mp he).map f
    rw [hα, map_neg, hβ] at hs
    exact o.someVector_ray.symm.trans
      (((ray_eq_iff o.someVector_ne_zero (neg_ne_zero.mpr p.someVector_ne_zero)).mpr hs).trans
        ((neg_rayOfNeZero R p.someVector p.someVector_ne_zero).symm.trans
          (congrArg Neg.neg p.someVector_ray)))

end Module.Ray

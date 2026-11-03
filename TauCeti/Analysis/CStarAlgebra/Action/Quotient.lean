/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Equivariant

/-!
# Descent of C⋆-actions to quotients

A point-norm continuous action descends through a surjective nonunital ⋆-homomorphism precisely
when its kernel is invariant. The descended action is uniquely characterized by equivariance of
the quotient map. In particular, its continuity follows from continuity of the original orbits;
no openness hypothesis on the quotient map or local compactness of the group is needed.

The construction is stated for a surjective map between C⋆-algebras, so it applies to any model
of a C⋆-quotient without choosing an ideal or quotient carrier. It includes nonunital and zero
algebras. Equivariance out of the quotient can be checked after composing with the quotient map,
and successive descents agree with descent through the composite.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open scoped CStarAlgebra

namespace TauCeti.CStarAction

variable {G A B C : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

variable (α : CStarAction G A) (f : A →⋆ₙₐ[ℂ] B)
  (hf : Function.Surjective f)
  (hker : IsInvariant (fun g a => α g a) (f ⁻¹' {0}))

include hker in
private theorem map_action_eq_of_map_eq (g : G) {a b : A} (h : f a = f b) :
    f (α g a) = f (α g b) := by
  have hz : f (a - b) = 0 := by simp [h]
  have := hker g hz
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, map_sub, sub_eq_zero] using this

private def descendEquiv (g : G) : B ≃⋆ₐ[ℂ] B := by
  let act (g : G) (b : B) := f (α g (Function.surjInv hf b))
  have hact (g : G) (a : A) : act g (f a) = f (α g a) :=
    map_action_eq_of_map_eq α f hker g (Function.surjInv_eq hf (f a))
  exact
    { toFun := act g
      invFun := act g⁻¹
      left_inv := by
        intro b
        obtain ⟨a, rfl⟩ := hf b
        simp [hact]
      right_inv := by
        intro b
        obtain ⟨a, rfl⟩ := hf b
        simp [hact]
      map_add' := by
        intro b c
        obtain ⟨a, rfl⟩ := hf b
        obtain ⟨d, rfl⟩ := hf c
        rw [← map_add f, hact, hact, hact]
        simp
      map_mul' := by
        intro b c
        obtain ⟨a, rfl⟩ := hf b
        obtain ⟨d, rfl⟩ := hf c
        rw [← map_mul f, hact, hact, hact]
        simp
      map_smul' := by
        intro z b
        obtain ⟨a, rfl⟩ := hf b
        rw [← map_smul f, hact, hact]
        simp
      map_star' := by
        intro b
        obtain ⟨a, rfl⟩ := hf b
        rw [← map_star f, hact, hact]
        simp [map_star] }

private theorem descendEquiv_map (g : G) (a : A) :
    descendEquiv α f hf hker g (f a) = f (α g a) :=
  map_action_eq_of_map_eq α f hker g (Function.surjInv_eq hf (f a))

/-- Descend an action through a surjective ⋆-homomorphism with invariant kernel. Its value on
`f a` is `f (α g a)`, independently of the representative `a`. -/
def descend : CStarAction G B where
  toMonoidHom :=
    { toFun := descendEquiv α f hf hker
      map_one' := by
        ext b
        obtain ⟨a, rfl⟩ := hf b
        simp [descendEquiv_map]
      map_mul' := by
        intro g h
        ext b
        obtain ⟨a, rfl⟩ := hf b
        simp [descendEquiv_map, mul_apply] }
  continuous_orbit b := by
    obtain ⟨a, rfl⟩ := hf b
    apply ((map_continuous f : Continuous f).comp (α.continuous_orbit a)).congr
    intro g
    exact (descendEquiv_map α f hf hker g a).symm

/-- The defining representative formula for the quotient action. -/
@[simp]
theorem descend_apply (g : G) (a : A) :
    α.descend f hf hker g (f a) = f (α g a) :=
  descendEquiv_map α f hf hker g a

/-- The quotient map is equivariant for the descended action. -/
theorem isEquivariant_descend : α.IsEquivariant (α.descend f hf hker) f :=
  isEquivariant_iff.mpr fun g a => (α.descend_apply f hf hker g a).symm

/-- An action on the quotient makes its quotient map equivariant exactly when it is the
canonical descended action. -/
theorem isEquivariant_iff_descend_eq (β : CStarAction G B) :
    α.IsEquivariant β f ↔ α.descend f hf hker = β := by
  constructor
  · intro h
    exact (α.isEquivariant_descend f hf hker).eq_of_surjective h hf
  · rintro rfl
    exact α.isEquivariant_descend f hf hker

include hf in
/-- Descent exists, and is unique, precisely when the kernel is invariant. -/
theorem existsUnique_isEquivariant_iff :
    (∃! β : CStarAction G B, α.IsEquivariant β f) ↔
      IsInvariant (fun g a => α g a) (f ⁻¹' {0}) := by
  constructor
  · rintro ⟨β, hβ, _⟩
    exact hβ.isInvariant_kernel
  · intro hk
    exact ⟨α.descend f hf hk, α.isEquivariant_descend f hf hk,
      fun β hβ => hβ.eq_of_surjective (α.isEquivariant_descend f hf hk) hf⟩

/-- A map out of a quotient is equivariant if and only if its composite with the quotient map
is equivariant. -/
theorem isEquivariant_descend_iff (γ : CStarAction G C) (k : B →⋆ₙₐ[ℂ] C) :
    (α.descend f hf hker).IsEquivariant γ k ↔ α.IsEquivariant γ (k.comp f) := by
  constructor
  · intro hk
    exact hk.comp (α.isEquivariant_descend f hf hker)
  · intro hk
    apply isEquivariant_iff.mpr
    intro g b
    obtain ⟨a, rfl⟩ := hf b
    simpa only [descend_apply, NonUnitalStarAlgHom.comp_apply] using hk.apply g a

/-- Descending successively through two quotient maps agrees with descending through their
composite. -/
theorem descend_descend (k : B →⋆ₙₐ[ℂ] C) (hk : Function.Surjective k)
    (hkker : IsInvariant (fun g b => α.descend f hf hker g b) (k ⁻¹' {0})) :
    (α.descend f hf hker).descend k hk hkker =
      α.descend (k.comp f) (hk.comp hf)
        (((α.descend f hf hker).isEquivariant_descend k hk hkker).comp
          (α.isEquivariant_descend f hf hker)).isInvariant_kernel := by
  apply IsEquivariant.eq_of_surjective
    (((α.descend f hf hker).isEquivariant_descend k hk hkker).comp
      (α.isEquivariant_descend f hf hker))
    (α.isEquivariant_descend _ _ _) (hk.comp hf)

end TauCeti.CStarAction

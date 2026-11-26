/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.WeightSpace

/-!
# Actions on character weight spaces through reduction

Let `red : G →* Q` be a reduction homomorphism, `H ≤ Q` a subgroup, and `χ` a scalar
character of `H`. The weight space for the restriction to `red⁻¹(H)` and the pullback of `χ`
consists of the vectors on which each element above `H` acts by the character of its reduction.

If inverse conjugation by an element of `Q` preserves `H` and `χ`, every lift induces the same
endomorphism of this weight space. A monoid mapping into these elements acts on the weight space
provided each element of its image lifts through `red`.

## References

The lift action and its two supporting lemmas generalize `New.levelRep`,
`New.apply_liftResidue_eq`, and `New.map_liftResidue_mem_levelSpace` in the `rh-new`
development (`src/Lib/Adelic/Unitary/CongruenceLevels.lean`).
-/

public section

namespace Representation

variable {k V G Q S : Type*} [CommSemiring k] [AddCommMonoid V] [Module k V]
  [Group G] [Group Q] [Monoid S]

variable (ρ : Representation k G V) (red : G →* Q) {H : Subgroup Q} (χ : H →* k)

/-- Two elements with the same reduction have the same action on the pulled-back weight space. -/
theorem apply_eq_apply_of_mem_weightSpace_of_map_eq {v : V}
    (hv : v ∈ weightSpace (ρ.comp (H.comap red).subtype) (χ.comp (red.subgroupComap H)))
    {g g' : G} (heq : red g = red g') : ρ g v = ρ g' v := by
  have hred : red (g'⁻¹ * g) = 1 := by simp [heq]
  let b : H.comap red := ⟨g'⁻¹ * g, show red (g'⁻¹ * g) ∈ H from hred ▸ H.one_mem⟩
  have hb : red.subgroupComap H b = 1 := Subtype.ext hred
  have hfix : ρ (g'⁻¹ * g) v = v := by
    simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, hb, map_one, one_smul] using
      (mem_weightSpace.mp hv) b
  calc
    ρ g v = ρ (g' * (g'⁻¹ * g)) v := by simp
    _ = ρ g' (ρ (g'⁻¹ * g) v) := by rw [map_mul, mul_apply_eq_comp]
    _ = ρ g' v := by rw [hfix]

/-- A lift preserves the pulled-back weight space if inverse conjugation by its reduction
preserves the subgroup and its character. -/
theorem map_mem_weightSpace_comp_subgroupComap {g : G}
    (hg : ∀ h : H, ∃ h' : H, (red g)⁻¹ * h * red g = h' ∧ χ h' = χ h)
    {v : V}
    (hv : v ∈ weightSpace (ρ.comp (H.comap red).subtype) (χ.comp (red.subgroupComap H))) :
    ρ g v ∈ weightSpace (ρ.comp (H.comap red).subtype) (χ.comp (red.subgroupComap H)) := by
  rw [mem_weightSpace] at hv ⊢
  intro b
  obtain ⟨h', hconj, hchar⟩ := hg (red.subgroupComap H b)
  have hred : red (g⁻¹ * b * g) = h' := by
    rw [map_mul, map_mul, map_inv]
    exact hconj
  let b' : H.comap red := ⟨g⁻¹ * b * g, show red (g⁻¹ * b * g) ∈ H from hred ▸ h'.property⟩
  have hb' : red.subgroupComap H b' = h' := Subtype.ext hred
  have hfix : ρ (g⁻¹ * b * g) v = χ (red.subgroupComap H b) • v := by
    simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, hb', hchar] using hv b'
  calc
    ρ b (ρ g v) = ρ (b * g) v := by rw [map_mul, mul_apply_eq_comp]
    _ = ρ (g * (g⁻¹ * b * g)) v := by simp [← mul_assoc]
    _ = ρ g (ρ (g⁻¹ * b * g) v) := by rw [map_mul, mul_apply_eq_comp]
    _ = χ (red.subgroupComap H b) • ρ g v := by rw [hfix, map_smul]

variable (φ : S →* Q)
  (hlift : ∀ s, ∃ g, red g = φ s)
  (hχ : ∀ (s : S) (h : H), ∃ h' : H, (φ s)⁻¹ * h * φ s = h' ∧ χ h' = χ h)

private noncomputable def chooseLift (s : S) : G :=
  (hlift s).choose

@[simp]
private theorem map_chooseLift (s : S) : red (chooseLift red φ hlift s) = φ s :=
  (hlift s).choose_spec

/-- A monoid homomorphism acts on the pulled-back weight space by lifts through reduction
when each image element lifts and its inverse conjugation preserves the subgroup and character. -/
noncomputable def levelEigenspaceRep :
    Representation k S (weightSpace (ρ.comp (H.comap red).subtype)
      (χ.comp (red.subgroupComap H))) where
  toFun s := (ρ (chooseLift red φ hlift s)).restrict fun _ hv ↦
    ρ.map_mem_weightSpace_comp_subgroupComap red χ (by simpa only [map_chooseLift] using hχ s) hv
  map_one' := by
    ext v
    simp only [LinearMap.coe_restrict_apply, one_apply_eq_self]
    calc
      _ = ρ 1 v := ρ.apply_eq_apply_of_mem_weightSpace_of_map_eq red χ v.property (by simp)
      _ = _ := by simp
  map_mul' s t := by
    ext v
    simp only [LinearMap.coe_restrict_apply, mul_apply_eq_comp]
    rw [← mul_apply_eq_comp, ← map_mul]
    exact ρ.apply_eq_apply_of_mem_weightSpace_of_map_eq red χ v.property (by simp)

/-- The level action can be evaluated with any lift of the given element. -/
theorem levelEigenspaceRep_apply (s : S)
    (v : weightSpace (ρ.comp (H.comap red).subtype) (χ.comp (red.subgroupComap H))) {g : G}
    (hg : red g = φ s) : (ρ.levelEigenspaceRep red χ φ hlift hχ s v : V) = ρ g v :=
  ρ.apply_eq_apply_of_mem_weightSpace_of_map_eq red χ v.property
    ((map_chooseLift red φ hlift s).trans hg.symm)

end Representation

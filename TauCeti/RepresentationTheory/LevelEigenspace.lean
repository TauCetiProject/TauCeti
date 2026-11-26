/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.RepresentationTheory.Basic

/-!
# Actions on character eigenspaces through reduction

Let `red : G →* Q` be a reduction homomorphism, `H ≤ Q` a subgroup, and `χ` a
scalar character of `H`. The level eigenspace of a representation of `G`
consists of the vectors on which `red⁻¹(H)` acts through `χ ∘ red`.

If inverse conjugation by an element of `Q` preserves `H` and `χ`, every lift
induces the same endomorphism of this eigenspace. In particular, a
homomorphism into these elements of `Q` lifts to an action on the level
eigenspace as soon as each element of its image is in the range of `red`.
In the adelic application, `G` is the standard level and `Q` is a product
of general linear groups over residue fields.
-/

@[expose] public section

namespace Representation

variable {k V G Q S : Type*} [CommSemiring k] [AddCommMonoid V] [Module k V]
  [Group G] [Group Q] [Monoid S]

variable (ρ : Representation k G V) (red : G →* Q) {H : Subgroup Q} (χ : H →* k)

/-- The simultaneous eigenspace for the pullback of a character under reduction. -/
def levelEigenspace : Submodule k V :=
  ⨅ g : H.comap red,
    (ρ g).eqLocus (χ ⟨red g, g.property⟩ • LinearMap.id)

/-- Membership in a level eigenspace means that each element above the level subgroup
acts by the character of its reduction. -/
theorem mem_levelEigenspace_iff {v : V} :
    v ∈ ρ.levelEigenspace red χ ↔
      ∀ (g : G) (hg : red g ∈ H), ρ g v = χ ⟨red g, hg⟩ • v := by
  simp only [levelEigenspace, Submodule.mem_iInf, LinearMap.mem_eqLocus,
    LinearMap.smul_apply, LinearMap.id_apply]
  exact ⟨fun h g hg ↦ h ⟨g, hg⟩, fun h g ↦ h g g.property⟩

/-- Two elements with the same reduction have the same action on the level eigenspace. -/
theorem apply_eq_apply_of_red_eq {v : V} (hv : v ∈ ρ.levelEigenspace red χ)
    {g g' : G} (heq : red g = red g') : ρ g v = ρ g' v := by
  have hred : red (g'⁻¹ * g) = 1 := by simp [heq]
  have hfix := (ρ.mem_levelEigenspace_iff red χ).mp hv (g'⁻¹ * g)
    (hred ▸ H.one_mem)
  have hχ : χ ⟨red (g'⁻¹ * g), hred ▸ H.one_mem⟩ = 1 := by
    rw [show (⟨red (g'⁻¹ * g), hred ▸ H.one_mem⟩ : H) = 1 from Subtype.ext hred, map_one]
  rw [hχ, one_smul] at hfix
  calc
    ρ g v = ρ (g' * (g'⁻¹ * g)) v := by simp
    _ = ρ g' (ρ (g'⁻¹ * g) v) := by rw [map_mul, mul_apply_eq_comp]
    _ = ρ g' v := by rw [hfix]

/-- A lift preserves the level eigenspace if conjugation by the inverse of its reduction
preserves the subgroup and its character. -/
theorem map_mem_levelEigenspace {g : G}
    (hg : ∀ h : H, ∃ h' : H, (red g)⁻¹ * h * red g = h' ∧ χ h' = χ h)
    {v : V} (hv : v ∈ ρ.levelEigenspace red χ) :
    ρ g v ∈ ρ.levelEigenspace red χ := by
  rw [mem_levelEigenspace_iff] at hv ⊢
  intro b hb
  obtain ⟨h', hconj, hchar⟩ := hg ⟨red b, hb⟩
  have hred : red (g⁻¹ * b * g) = h' := by simpa only [map_mul, map_inv] using hconj
  have hmem : red (g⁻¹ * b * g) ∈ H := hred ▸ h'.property
  have hfix := hv (g⁻¹ * b * g) hmem
  rw [show (⟨red (g⁻¹ * b * g), hmem⟩ : H) = h' from Subtype.ext hred, hchar] at hfix
  calc
    ρ b (ρ g v) = ρ (b * g) v := by rw [map_mul, mul_apply_eq_comp]
    _ = ρ (g * (g⁻¹ * b * g)) v := by simp [← mul_assoc]
    _ = ρ g (ρ (g⁻¹ * b * g) v) := by rw [map_mul, mul_apply_eq_comp]
    _ = χ ⟨red b, hb⟩ • ρ g v := by rw [hfix, map_smul]

variable (φ : S →* Q)
  (hlift : ∀ s, ∃ g, red g = φ s)
  (hχ : ∀ (s : S) (h : H), ∃ h' : H, (φ s)⁻¹ * h * φ s = h' ∧ χ h' = χ h)

/-- A monoid homomorphism acts on the level eigenspace by lifts through reduction
when each image element lifts and its inverse conjugation preserves the subgroup
and its character. -/
noncomputable def levelEigenspaceRep : Representation k S (ρ.levelEigenspace red χ) where
  toFun s := (ρ (hlift s).choose).restrict fun _ hv ↦
    ρ.map_mem_levelEigenspace red χ (by simpa only [(hlift s).choose_spec] using hχ s) hv
  map_one' := by
    ext v
    change ρ (hlift 1).choose v = v.val
    calc
      _ = ρ 1 v := ρ.apply_eq_apply_of_red_eq red χ v.property
        ((hlift 1).choose_spec.trans (by simp))
      _ = _ := by simp
  map_mul' s t := by
    ext v
    change ρ (hlift (s * t)).choose v =
      ρ (hlift s).choose (ρ (hlift t).choose v)
    rw [← mul_apply_eq_comp, ← map_mul]
    apply ρ.apply_eq_apply_of_red_eq red χ v.property
    calc
      _ = φ (s * t) := (hlift (s * t)).choose_spec
      _ = φ s * φ t := map_mul φ s t
      _ = red (hlift s).choose * red (hlift t).choose :=
        congrArg₂ (· * ·) (hlift s).choose_spec.symm (hlift t).choose_spec.symm
      _ = red ((hlift s).choose * (hlift t).choose) := (map_mul red _ _).symm

/-- The level action can be evaluated with any lift of the given element. -/
theorem levelEigenspaceRep_apply (s : S) (v : ρ.levelEigenspace red χ) {g : G}
    (hg : red g = φ s) : (ρ.levelEigenspaceRep red χ φ hlift hχ s v : V) = ρ g v :=
  ρ.apply_eq_apply_of_red_eq red χ v.property ((hlift s).choose_spec.trans hg.symm)

end Representation

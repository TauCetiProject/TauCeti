/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.RepresentationTheory.FunLeft
public import TauCeti.RepresentationTheory.LinearCharacter.Eigenspace
import TauCeti.RepresentationTheory.Irreducible

/-!
# Eigensubmodules of an invariant character of a normal subgroup

Let `H` be a normal subgroup of a group `G`, let `ρ` be a representation of `G` on `V`, and let
`θ : H →* kˣ` be a linear character of `H` invariant under conjugation by `G`. The
`θ`-eigensubmodule of the restriction of `ρ` to `H` is stable under `G`: if `h ∈ H` acts on `v`
by `θ h`, then `h` acts on `ρ g v` by `θ(g⁻¹ h g) = θ h`. It is therefore a subrepresentation of
`ρ`, the vectors on which `H` acts through the scalars `θ`.

For finite `G`, this subrepresentation of the representation by left translation on functions
`G → k` is nonzero, since it contains `∑_h θ(h)⁻¹ δ_h`. Any minimal subrepresentation inside it
is then an irreducible representation of `G` on which `H` acts by `θ`. No hypothesis on the field
is needed.

## Main statements

* `Representation.apply_mem_charEigenspace_comp_subtype`: the `θ`-eigensubmodule of `H` is stable
  under `G`.
* `Representation.charEigenspaceSubrepresentation`: the `θ`-eigensubmodule of `H` as a
  subrepresentation of `ρ`, with membership `Representation.mem_charEigenspaceSubrepresentation`.
* `Representation.toSubmodule_charEigenspaceSubrepresentation`: its underlying submodule is the
  `θ`-eigensubmodule of the restriction of `ρ` to `H`.
* `Representation.exists_subrepresentation_isIrreducible_forall_apply_eq_smul`: for finite `G`, an
  irreducible representation of `G` on which `H` acts by `θ` exists.
-/

public section

namespace Representation

variable {k G V : Type*} [Group G] [AddCommGroup V] {H : Subgroup G} [hH : H.Normal]

section CommRing

variable [CommRing k] [Module k V]

/-- **The `θ`-eigensubmodule of a normal subgroup is stable.** Let `H` be a normal subgroup of
`G` and `θ` a character of `H` invariant under conjugation by `G`. If `H` acts on `v` through
`θ`, it acts on `ρ g v` through `θ` too. -/
theorem apply_mem_charEigenspace_comp_subtype (ρ : Representation k G V) {θ : H →* kˣ}
    (hθ : ∀ (g : G) (h : H), θ ⟨g * h * g⁻¹, hH.conj_mem h h.property g⟩ = θ h) (g : G)
    {v : V} (hv : v ∈ charEigenspace (ρ.comp H.subtype) θ) :
    ρ g v ∈ charEigenspace (ρ.comp H.subtype) θ := by
  rw [mem_charEigenspace_iff] at hv ⊢
  intro h
  obtain ⟨h', hh'⟩ : ∃ h' : H, (h' : G) = g⁻¹ * h * g :=
    ⟨⟨_, by simpa using hH.conj_mem h h.property g⁻¹⟩, rfl⟩
  have hconj : (h : G) * g = g * h' := by rw [hh']; group
  have hθh : θ h' = θ h := by
    rw [← hθ g h']
    congr 1
    ext
    simp [hh', mul_assoc]
  -- `h` acts on `ρ g v` as `h'` acts on `v`, transported by `ρ g`.
  have hρ : ρ h (ρ g v) = ρ g (ρ h' v) := by simpa using congr(ρ $hconj v)
  simpa [hρ, hθh] using congr(ρ g $(hv h'))

/-- **The `θ`-eigensubmodule of a normal subgroup as a subrepresentation.** For a normal subgroup
`H` of `G` and a character `θ` of `H` invariant under conjugation by `G`, the vectors on which `H`
acts through the scalars `θ` form a subrepresentation of `ρ`. -/
def charEigenspaceSubrepresentation (ρ : Representation k G V) (θ : H →* kˣ)
    (hθ : ∀ (g : G) (h : H), θ ⟨g * h * g⁻¹, hH.conj_mem h h.property g⟩ = θ h) :
    Subrepresentation ρ where
  toSubmodule := charEigenspace (ρ.comp H.subtype) θ
  apply_mem_toSubmodule g _ hv := apply_mem_charEigenspace_comp_subtype ρ hθ g hv

/-- A vector lies in the `θ`-eigensubrepresentation of `H` exactly when every `h ∈ H` acts on it
as multiplication by `θ h`. -/
@[simp]
theorem mem_charEigenspaceSubrepresentation (ρ : Representation k G V) {θ : H →* kˣ}
    (hθ : ∀ (g : G) (h : H), θ ⟨g * h * g⁻¹, hH.conj_mem h h.property g⟩ = θ h) {v : V} :
    v ∈ charEigenspaceSubrepresentation ρ θ hθ ↔ ∀ h : H, ρ h v = (θ h : k) • v :=
  mem_charEigenspace_iff (ρ.comp H.subtype) θ

/-- The underlying submodule of the `θ`-eigensubrepresentation of `H` is the `θ`-eigensubmodule
of the restriction of `ρ` to `H`. -/
@[simp]
theorem toSubmodule_charEigenspaceSubrepresentation (ρ : Representation k G V) {θ : H →* kˣ}
    (hθ : ∀ (g : G) (h : H), θ ⟨g * h * g⁻¹, hH.conj_mem h h.property g⟩ = θ h) :
    (charEigenspaceSubrepresentation ρ θ hθ).toSubmodule = charEigenspace (ρ.comp H.subtype) θ :=
  (rfl)

end CommRing

/-- **Existence of a representation on which `H` acts by an invariant character.** Let `H` be a
normal subgroup of a finite group `G` and `θ` a character of `H` invariant under conjugation by
`G`. Then the representation of `G` on functions `G → k` by left translation has an irreducible
subrepresentation on which `H` acts by `θ`. No hypothesis on the field is needed. -/
theorem exists_subrepresentation_isIrreducible_forall_apply_eq_smul [Field k] [Finite G]
    (θ : H →* kˣ)
    (hθ : ∀ (g : G) (h : H), θ ⟨g * h * g⁻¹, hH.conj_mem h h.property g⟩ = θ h) :
    ∃ σ : Subrepresentation ((trivial k G k).funLeft G), σ.toRepresentation.IsIrreducible ∧
      ∀ (h : H) (ξ : σ.toSubmodule), σ.toRepresentation h ξ = (θ h : k) • ξ := by
  classical
  have := Fintype.ofFinite G
  set ρ := (trivial k G k).funLeft G
  set S := charEigenspaceSubrepresentation ρ θ hθ
  -- `S` contains the vector `∑_h θ(h)⁻¹ δ_h`, which is nonzero: its value at `1` is `1`, since
  -- only `h = 1` contributes.
  have hone : charSum (ρ.comp H.subtype) θ (Pi.single 1 1) 1 = 1 := by
    rw [charSum_apply, Finset.sum_apply, Finset.sum_eq_single (1 : H)]
    · simp [ρ]
    · intro h _ hh
      simp [ρ, inv_eq_one, hh]
    · simp
  have hS : S ≠ ⊥ := by
    intro hS
    have hmem : charSum (ρ.comp H.subtype) θ (Pi.single 1 1) ∈ S :=
      charSum_apply_mem (ρ.comp H.subtype) θ _
    rw [hS] at hmem
    have h0 := congrFun ((Submodule.mem_bot k).1 hmem) 1
    exact one_ne_zero (hone.symm.trans h0)
  obtain ⟨τ, hτS, hτ⟩ := exists_isAtom_le hS
  refine ⟨τ, isIrreducible_toRepresentation_of_isAtom hτ, fun h ξ => ?_⟩
  exact Subtype.ext ((mem_charEigenspaceSubrepresentation ρ hθ).1 (hτS ξ.property) h)

end Representation

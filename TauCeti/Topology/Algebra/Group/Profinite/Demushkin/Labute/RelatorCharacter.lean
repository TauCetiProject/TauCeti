/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Character.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Presentation.Basic
import TauCeti.Algebra.Group.Subgroup.Ker

/-!
# The character of a Demushkin relator

Let `F` be the free pro-`p` group on a set `X` and `r ∈ F` a relator presenting a Demushkin group
`G = F ⧸ (r)`. The canonical character of `G` read on `F` is a continuous character
`χ : F → ℤ_pˣ` (`TauCeti.demushkinRelatorCharacter`), the character Labute attaches to `r`
(Labute, §4 Definition, p. 121). Its kernel contains `r`
(`TauCeti.demushkinRelatorCharacter_mem_ker`), so `r` has a class in Labute's module
`ker χ ⧸ (ker χ, ker χ)`.

## Main results

* `TauCeti.demushkinRelatorCharacter`: the character of a Demushkin relator, the canonical
  character of the presented group read on the free pro-`p` group.
* `TauCeti.demushkinRelatorCharacter_mem_ker`: the relator lies in the kernel of its character.
* `TauCeti.demushkinRelatorCharacter_apply_equiv_symm`: the character of a relator read along an
  isomorphism of free pro-`p` groups carrying it to another relator.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §4,
  Definition p. 121.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {X : Type*} {r : freeProP p X}

/-- **The character of a Demushkin relator** (Labute, §4): for a relator `r` of the free pro-`p`
group `F` on `X` presenting a Demushkin group `G = F ⧸ (r)`, the canonical character of `G`
composed with the quotient map `F → G`. Labute's module is the topological abelianization of its
kernel. -/
noncomputable def demushkinRelatorCharacter (hr : IsDemushkin p (presentedProP p X {r})) :
    freeProP p X →ₜ* ℤ_[p]ˣ :=
  (demushkinCharacter hr).comp (presentedProP.mk p {r})

/-- The character of a Demushkin relator is the canonical character on classes. -/
@[simp]
theorem demushkinRelatorCharacter_apply (hr : IsDemushkin p (presentedProP p X {r}))
    (x : freeProP p X) :
    demushkinRelatorCharacter hr x = demushkinCharacter hr (presentedProP.mk p {r} x) :=
  (rfl)

/-- The character of a Demushkin relator has the same image as the canonical character. -/
theorem range_demushkinRelatorCharacter (hr : IsDemushkin p (presentedProP p X {r})) :
    (demushkinRelatorCharacter hr).toMonoidHom.range =
      (demushkinCharacter hr).toMonoidHom.range :=
  MonoidHom.range_comp_of_surjective _ _ (presentedProP.mk_surjective p {r})

/-- **The relator lies in the kernel of its character**, so it has a class in Labute's module. -/
theorem demushkinRelatorCharacter_mem_ker (hr : IsDemushkin p (presentedProP p X {r})) :
    r ∈ (demushkinRelatorCharacter hr : freeProP p X →* ℤ_[p]ˣ).ker := by
  simp [presentedProP.mk_relator r (Set.mem_singleton r)]

/-- **The character of a Demushkin relator along an isomorphism.** If a continuous isomorphism
`e : F_X ≃ F_Y` of free pro-`p` groups carries `r` to `r'`, the character of `r` takes on `e⁻¹(y)`
the value of the canonical character on the class of `y` in `⟨Y ∣ r'⟩`, read back along the induced
isomorphism `⟨X ∣ r⟩ ≃ ⟨Y ∣ r'⟩`. -/
theorem demushkinRelatorCharacter_apply_equiv_symm {Y : Type*}
    (hr : IsDemushkin p (presentedProP p X {r})) (e : freeProP p X ≃ₜ* freeProP p Y)
    {r' : freeProP p Y} (he : e r = r') (y : freeProP p Y) :
    demushkinRelatorCharacter hr (e.symm y) =
      demushkinCharacter hr
        ((presentedProP.congrSingleton e he).symm (presentedProP.mk p {r'} y)) := by
  rw [presentedProP.congrSingleton_symm_mk, demushkinRelatorCharacter_apply]

end TauCeti

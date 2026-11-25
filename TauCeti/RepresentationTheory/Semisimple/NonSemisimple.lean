/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Two obstructions to semisimplicity

* **Extensions of trivial representations.** If a group acts trivially on a subrepresentation `W`
  and on the quotient by `W`, and the representation is semisimple, then the group acts trivially
  on the whole representation (`Representation.apply_eq_self_of_isSemisimpleRepresentation`): an
  invariant complement of `W` maps isomorphically onto the quotient, so the action on it is
  trivial too. A nontrivial unipotent action, such as `(1 a; 0 1)` with `a ≠ 0` on `k²`, is
  therefore never semisimple (`Representation.not_isSemisimpleRepresentation_of_apply_ne`).
* **Regular representations in modular characteristic.** If the order of a finite group `G` is
  zero in the field `k`, the left regular representation of `G` over `k` is not semisimple
  (`Representation.not_isSemisimpleRepresentation_leftRegular`): an invariant complement of the
  augmentation kernel would contain an invariant vector of augmentation `1`, but every invariant
  vector is a multiple of `∑_g g`, whose augmentation is the order of `G`. This is the converse
  direction of Maschke's theorem for the regular representation.

These are the non-examples showing that the invertible-index hypotheses in the relative Maschke
theorem (`Representation.isSemisimpleRepresentation_of_comp_subtype`) and in the restriction
theorems of `TauCeti.RepresentationTheory.Semisimple.Restriction` cannot be dropped.
-/

public section

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- **A semisimple extension of trivial representations is trivial.** If `G` acts trivially on a
subrepresentation `W` of a semisimple representation `ρ` and on the quotient `V ⧸ W` (that is,
`ρ g v - v ∈ W` for all `g` and `v`), then `G` acts trivially on `V`. -/
theorem apply_eq_self_of_isSemisimpleRepresentation {ρ : Representation k G V}
    [ρ.IsSemisimpleRepresentation] (W : Subrepresentation ρ)
    (hW : ∀ g, ∀ w ∈ W.toSubmodule, ρ g w = w) (hV : ∀ g v, ρ g v - v ∈ W.toSubmodule)
    (g : G) (v : V) : ρ g v = v := by
  obtain ⟨C, hC⟩ := exists_isCompl W
  have hC' := Subrepresentation.isCompl_toSubmodule.2 hC
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.1 (hC'.sup_eq_top ▸ Submodule.mem_top (x := v))
  have hc' : ρ g c - c = 0 := (Submodule.disjoint_def.1 hC'.disjoint) _
    (by simpa using hV g c) (C.toSubmodule.sub_mem (C.apply_mem_toSubmodule g hc) hc)
  rw [map_add, hW g w hw, sub_eq_zero.1 hc']

/-- **A nontrivial unipotent action is not semisimple.** If `G` acts trivially on a
subrepresentation `W` and on `V ⧸ W`, but some `ρ g` moves some vector, then `ρ` is not
semisimple. -/
theorem not_isSemisimpleRepresentation_of_apply_ne {ρ : Representation k G V}
    (W : Subrepresentation ρ) (hW : ∀ g, ∀ w ∈ W.toSubmodule, ρ g w = w)
    (hV : ∀ g v, ρ g v - v ∈ W.toSubmodule) {g : G} {v : V} (hgv : ρ g v ≠ v) :
    ¬ ρ.IsSemisimpleRepresentation := fun _ ↦
  hgv (apply_eq_self_of_isSemisimpleRepresentation W hW hV g v)

/-- **The regular representation in modular characteristic is not semisimple.** If the order of
a finite group `G` is zero in `k`, the left regular representation of `G` over `k` is not
semisimple. -/
theorem not_isSemisimpleRepresentation_leftRegular [Fintype G]
    (hG : (Fintype.card G : k) = 0) : ¬ (leftRegular k G).IsSemisimpleRepresentation := by
  intro
  -- The augmentation `ε (∑ a_g g) = ∑ a_g` is invariant, so its kernel `I` is a subrepresentation.
  let ε : MonoidAlgebra k G →ₗ[k] k :=
    (Finsupp.lsum k fun _ ↦ LinearMap.id) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
  have hε (x : MonoidAlgebra k G) : ε x = ∑ g, x.coeff g := by
    simp [ε, Finsupp.sum_fintype]
  have hερ (g : G) (x : MonoidAlgebra k G) : ε (leftRegular k G g x) = ε x := by
    simp only [hε, coeff_ofMulAction, smul_eq_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun _ ↦ rfl
  let I : Subrepresentation (leftRegular k G) :=
    ⟨LinearMap.ker ε, fun g x hx ↦ by rw [LinearMap.mem_ker, hερ, LinearMap.mem_ker.1 hx]⟩
  obtain ⟨C, hC⟩ := exists_isCompl I
  have hC' := Subrepresentation.isCompl_toSubmodule.2 hC
  -- Write `1 = i + c` with `ε i = 0`, so `ε c = 1`.
  obtain ⟨i, hi, c, hc, hic⟩ := Submodule.mem_sup.1
    (hC'.sup_eq_top ▸ Submodule.mem_top (x := MonoidAlgebra.single (1 : G) (1 : k)))
  have hεc : ε c = 1 := by
    have := congrArg ε hic
    rw [map_add, LinearMap.mem_ker.1 hi, zero_add, hε (MonoidAlgebra.single _ _),
      MonoidAlgebra.coeff_single] at this
    simpa using this
  -- `c` is invariant: `g c - c` lies in both `I` and `C`.
  have hinv (g : G) : leftRegular k G g c = c := by
    have h0 : leftRegular k G g c - c = 0 := (Submodule.disjoint_def.1 hC'.disjoint) _
      (LinearMap.mem_ker.2 (by rw [map_sub, hερ, sub_self]))
      (C.toSubmodule.sub_mem (C.apply_mem_toSubmodule g hc) hc)
    exact sub_eq_zero.1 h0
  -- So `c` is constant, and its augmentation is a multiple of `|G| = 0`.
  have hconst (x : G) : c.coeff x = c.coeff 1 := by
    have := congrArg (fun y : MonoidAlgebra k G ↦ y.coeff 1) (hinv x⁻¹)
    simpa [coeff_ofMulAction] using this
  rw [hε, Finset.sum_congr rfl fun x _ ↦ hconst x, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hG, zero_mul] at hεc
  exact zero_ne_one hεc

end Representation

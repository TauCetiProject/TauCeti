/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Choose

/-!
# Group actions that transport the factors of a product

Let a group `G` act on a type `X` that decomposes as a product `∏_{i : ι} M i`, with the indices
lying over a `G`-set `P` along `p : ι → P`, and suppose `g` carries the factor at `i` to the
factor at `j` along a bijection `T g : M i ≃ M j` whenever `p j = g • p i`. The action on `X`
need not be a `MulAction`: it is only required to be compatible with `T`. If every index is
carried to a fixed index `w`, an element of `X` is determined by the components at `w` of its
translates (`TauCeti.eq_of_forall_transport_component_eq`). If moreover every element of `G`
carries some index to `w`, every function `G → M w` that is equivariant for the stabilizer of
`p w` arises in this way (`TauCeti.exists_forall_transport_component_eq`).

The motivating example is the Galois group of `L/K` acting on the semi-local algebra
`K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w`, permuting the places above `v`. These two results are the
injectivity and surjectivity of the map into the representation coinduced from a decomposition
group, `TauCeti.resCoindToHom_bijective_of_transport`.

## Main results

* `TauCeti.eq_of_forall_transport_component_eq`,
  `TauCeti.exists_forall_transport_component_eq`: injectivity and surjectivity of the map
  `x ↦ (g ↦ (g • x)_w)` into the stabilizer-equivariant functions.
-/

public section

namespace TauCeti

variable {G P ι X : Type*} [Group G] [MulAction G P] {p : ι → P} {act : G → X → X}
  {M : ι → Type*} (e : X ≃ ∀ i, M i) (T : ∀ (g : G) {i j : ι}, p j = g • p i → M i ≃ M j)
  (he : ∀ (g : G) (x : X) {i j : ι} (h : p j = g • p i), e (act g x) j = T g h (e x i))
  {w : ι}

include he in
/-- If `G` carries every factor to the factor at `w`, an element of `X` is determined by the
components at `w` of its translates. -/
theorem eq_of_forall_transport_component_eq (htrans : ∀ i, ∃ g : G, p w = g • p i) {x x' : X}
    (h : ∀ g, e (act g x) w = e (act g x') w) : x = x' :=
  e.injective <| funext fun i ↦ by
    obtain ⟨g, hg⟩ := htrans i
    simpa only [he g _ hg, (T g hg).apply_eq_iff_eq] using h g

include he in
/-- If `G` carries every factor to the factor at `w`, every element of `G` carries some factor
to it, and the transport maps compose, then every function `G → M w` that is equivariant for the
stabilizer of `p w` is `g ↦ (g • x)_w` for some `x : X`. -/
theorem exists_forall_transport_component_eq
    (hT : ∀ (g g' : G) {i j k : ι} (h : p j = g • p i) (h' : p k = g' • p j) (a : M i),
      T g' h' (T g h a) = T (g' * g) (by rw [h', h, mul_smul]) a)
    (htrans : ∀ i, ∃ g : G, p w = g • p i) (hsurj : ∀ g : G, ∃ i, p w = g • p i)
    (f : G → M w) (hf : ∀ (d : G) (hd : p w = d • p w) (g : G), f (d * g) = T d hd (f g)) :
    ∃ x : X, ∀ g, e (act g x) w = f g := by
  choose g hg using htrans
  -- the component at `i` is the value of `f` at an element `g i` carrying `i` to `w`,
  -- transported back to `M i`; equivariance of `f` for the stabilizer of `p w` makes the
  -- result independent of the choice of `g i`
  refine ⟨e.symm fun i ↦ (T (g i) (hg i)).symm (f (g i)), fun σ ↦ ?_⟩
  obtain ⟨i, hi⟩ := hsurj σ
  have hd : p w = (σ * (g i)⁻¹) • p w := by rw [mul_smul, inv_smul_eq_iff.mpr (hg i), ← hi]
  have hcongr {g₁ g₂ : G} (h₁ : p w = g₁ • p i) (h₂ : p w = g₂ • p i) (hg : g₁ = g₂) (b : M i) :
      T g₁ h₁ b = T g₂ h₂ b := by
    subst hg
    rfl
  rw [he σ _ hi, e.apply_symm_apply,
    hcongr hi (by rw [mul_smul, ← hg i, ← hd]) (inv_mul_cancel_right σ (g i)).symm,
    ← hT _ _ (hg i) hd, Equiv.apply_symm_apply, ← hf, inv_mul_cancel_right]

end TauCeti

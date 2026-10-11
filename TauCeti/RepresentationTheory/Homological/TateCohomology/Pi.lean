/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HerbrandQuotient
public import TauCeti.RepresentationTheory.Pi
import TauCeti.SetTheory.Cardinal.Finite

/-!
# Low-degree Tate cohomology of a product of representations

Let `G` be a finite group and `M i` a family of representations of `G`, indexed by an arbitrary
type `ι`. This file shows that Tate cohomology in degrees `0` and `-1` commutes with the product
`Rep.pi M`:

`H-hat^0(G, ∏ i, M i) ≃ ∏ i, H-hat^0(G, M i)` and
`H-hat^(-1)(G, ∏ i, M i) ≃ ∏ i, H-hat^(-1)(G, M i)`,

the `i`-th component being induced by the projection onto `M i`. Both rest on the low-degree
descriptions `H-hat^0 = Mᴳ / N_G M` and `H-hat^(-1) = ker N_G / I_G M`, where invariants, norms and
the augmentation submodule `I_G M` of a product are all computed componentwise. For the norm image
and the augmentation submodule this needs a choice in every factor at once, and for the latter
also the finiteness of `G` (`Representation.mem_coinvariantsKer_pi_iff`).

Consequently the **Herbrand quotient of a product** is the product of the Herbrand quotients of
the factors, as soon as all but finitely many factors have trivial Tate cohomology in degrees `0`
and `-1`. This is the shape of the `S`-ideles of a cyclic extension `L/K` of number fields: they
are the product over the places `v` of `K` of the Galois modules `∏_{w ∣ v} L_wˣ` for `v ∈ S` and
`∏_{w ∣ v} 𝒪_wˣ` for `v ∉ S`, and the factors of the second kind are cohomologically trivial
when `L/K` is unramified at `v`.

## Main definitions

* `TauCeti.TateCohomology.H0LinearEquivPi`: `H-hat^0(G, ∏ i, M i) ≃ ∏ i, H-hat^0(G, M i)`.
* `TauCeti.TateCohomology.HNegOneLinearEquivPi`:
  `H-hat^(-1)(G, ∏ i, M i) ≃ ∏ i, H-hat^(-1)(G, M i)`.

## Main results

* `TauCeti.TateCohomology.H0LinearEquivPi_H0π` and
  `TauCeti.TateCohomology.HNegOneLinearEquivPi_HNegOneπ`: the equivalences send the class of an
  element to the family of the classes of its components.
* `TauCeti.TateCohomology.herbrandQuotient_pi`: `h(∏ i, M i) = ∏ i ∈ s, h(M i)` when the factors
  outside the finite set `s` have trivial Tate cohomology in degrees `0` and `-1`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §2.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §§6–7.
-/

public noncomputable section

universe u

open CategoryTheory LinearMap

namespace TauCeti.TateCohomology

variable {R G ι : Type u} [CommRing R] [Group G] [Fintype G] (M : ι → Rep R G)

omit [Fintype G] in
/-- The projection of a product onto a factor, as a compatible pair along the identity of `G`. -/
private theorem isIntertwiningMap_proj (i : ι) :
    (Rep.pi M).ρ.IsIntertwiningMap ((M i).ρ.comp ((MulEquiv.refl G : G ≃* G) : G →* G))
      (LinearMap.proj i) :=
  ⟨fun _ _ ↦ by simp⟩

/-! ### Degree zero -/

/-- The family of the maps `H-hat^0(G, ∏ j, M j) → H-hat^0(G, M i)` induced by the projections. -/
private def H0ToPi : tateCohomology (Rep.pi M) 0 →ₗ[R] ∀ i, tateCohomology (M i) 0 :=
  LinearMap.pi fun i ↦ (map (isIntertwiningMap_proj M i) 0).hom

private theorem H0ToPi_H0π (y : (Rep.pi M).ρ.invariants) (i : ι) :
    H0ToPi M (H0π (Rep.pi M) y) i =
      H0π (M i) ⟨y.1 i, ((Representation.mem_invariants_pi_iff _).1 y.2) i⟩ := by
  simp only [H0ToPi, LinearMap.pi_apply]
  exact (H0π_comp_map_apply (isIntertwiningMap_proj M i) y).trans
    (congrArg _ (Subtype.ext (mapInvariants_apply_coe _ y)))

private theorem H0ToPi_bijective : Function.Bijective (H0ToPi M) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using H0_induction_on with | h y => ?_
    -- Every component of `y` is a norm; a choice of preimages in all factors at once is a
    -- preimage of `y`.
    have h (i : ι) : ∃ z : M i, (M i).ρ.norm z = y.1 i := by
      obtain ⟨z, hz⟩ := (H0π_eq_zero_iff _).1 ((H0ToPi_H0π M y i).symm.trans (congrFun hx i))
      exact ⟨z, hz⟩
    choose z hz using h
    exact (H0π_eq_zero_iff y).2 ⟨z, funext fun i ↦ by simpa using hz i⟩
  · intro x
    have h (i : ι) : ∃ y : (M i).ρ.invariants, H0π (M i) y = x i :=
      H0_induction_on (C := fun x ↦ ∃ y, H0π (M i) y = x) (x i) fun y ↦ ⟨y, rfl⟩
    choose y hy using h
    refine ⟨H0π (Rep.pi M) ⟨fun i ↦ (y i).1, (Representation.mem_invariants_pi_iff _).2
      fun i ↦ (y i).2⟩, funext fun i ↦ ?_⟩
    rw [H0ToPi_H0π, ← hy i]

/-- **Degree-zero Tate cohomology commutes with products**:
`H-hat^0(G, ∏ i, M i) ≃ ∏ i, H-hat^0(G, M i)`, with components induced by the projections. -/
def H0LinearEquivPi : tateCohomology (Rep.pi M) 0 ≃ₗ[R] ∀ i, tateCohomology (M i) 0 :=
  LinearEquiv.ofBijective (H0ToPi M) (H0ToPi_bijective M)

/-- The degree-zero equivalence sends the class of an invariant element of the product to the
family of the classes of its components. -/
@[simp]
theorem H0LinearEquivPi_H0π (y : (Rep.pi M).ρ.invariants) (i : ι) :
    H0LinearEquivPi M (H0π (Rep.pi M) y) i =
      H0π (M i) ⟨y.1 i, ((Representation.mem_invariants_pi_iff _).1 y.2) i⟩ :=
  H0ToPi_H0π M y i

/-! ### Degree minus one -/

/-- The family of the maps `H-hat^(-1)(G, ∏ j, M j) → H-hat^(-1)(G, M i)` induced by the
projections. -/
private def HNegOneToPi : tateCohomology (Rep.pi M) (-1) →ₗ[R] ∀ i, tateCohomology (M i) (-1) :=
  LinearMap.pi fun i ↦ (map (isIntertwiningMap_proj M i) (-1)).hom

private theorem HNegOneToPi_HNegOneπ (y : ker (Rep.pi M).ρ.norm) (i : ι) :
    HNegOneToPi M (HNegOneπ (Rep.pi M) y) i =
      HNegOneπ (M i) ⟨y.1 i, (Representation.mem_ker_norm_pi_iff _).1 y.2 i⟩ := by
  simp only [HNegOneToPi, LinearMap.pi_apply]
  exact (HNegOneπ_comp_map_apply (isIntertwiningMap_proj M i) y).trans
    (congrArg _ (Subtype.ext (mapKerNorm_apply_coe _ y)))

private theorem HNegOneToPi_bijective : Function.Bijective (HNegOneToPi M) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using HNegOne_induction_on with | h y => ?_
    rw [HNegOneπ_eq_zero_iff, Submodule.submoduleOf, Submodule.mem_comap,
      Submodule.subtype_apply, Representation.mem_coinvariantsKer_pi_iff]
    intro i
    have := (HNegOneπ_eq_zero_iff _).1 ((HNegOneToPi_HNegOneπ M y i).symm.trans (congrFun hx i))
    rwa [Submodule.submoduleOf, Submodule.mem_comap] at this
  · intro x
    have h (i : ι) : ∃ y : ker (M i).ρ.norm, HNegOneπ (M i) y = x i :=
      HNegOne_induction_on (C := fun x ↦ ∃ y, HNegOneπ (M i) y = x) (x i) fun y ↦ ⟨y, rfl⟩
    choose y hy using h
    refine ⟨HNegOneπ (Rep.pi M) ⟨fun i ↦ (y i).1,
      (Representation.mem_ker_norm_pi_iff _).2 fun i ↦ (y i).2⟩, funext fun i ↦ ?_⟩
    rw [HNegOneToPi_HNegOneπ, ← hy i]

/-- **Degree `-1` Tate cohomology commutes with products**:
`H-hat^(-1)(G, ∏ i, M i) ≃ ∏ i, H-hat^(-1)(G, M i)`, with components induced by the projections. -/
def HNegOneLinearEquivPi : tateCohomology (Rep.pi M) (-1) ≃ₗ[R] ∀ i, tateCohomology (M i) (-1) :=
  LinearEquiv.ofBijective (HNegOneToPi M) (HNegOneToPi_bijective M)

/-- The degree `-1` equivalence sends the class of a norm-zero element of the product to the
family of the classes of its components. -/
@[simp]
theorem HNegOneLinearEquivPi_HNegOneπ (y : ker (Rep.pi M).ρ.norm) (i : ι) :
    HNegOneLinearEquivPi M (HNegOneπ (Rep.pi M) y) i =
      HNegOneπ (M i) ⟨y.1 i, (Representation.mem_ker_norm_pi_iff _).1 y.2 i⟩ :=
  HNegOneToPi_HNegOneπ M y i

/-! ### The Herbrand quotient of a product -/

/-- **The Herbrand quotient of a product** of representations of a finite group is the product of
the Herbrand quotients of the factors, when the factors outside a finite set `s` have trivial Tate
cohomology in degrees `0` and `-1`. In particular, for a finite index type it is the product of
all the Herbrand quotients. -/
theorem herbrandQuotient_pi (s : Finset ι)
    (h0 : ∀ i ∉ s, Subsingleton (tateCohomology (M i) 0))
    (h1 : ∀ i ∉ s, Subsingleton (tateCohomology (M i) (-1))) :
    herbrandQuotient (Rep.pi M) = ∏ i ∈ s, herbrandQuotient (M i) := by
  simp only [herbrandQuotient_def]
  rw [Nat.card_congr (H0LinearEquivPi M).toEquiv, Nat.card_congr (HNegOneLinearEquivPi M).toEquiv,
    Nat.card_pi_eq_prod_of_card_eq_one s fun i hi ↦ have := h0 i hi; Nat.card_of_subsingleton 0,
    Nat.card_pi_eq_prod_of_card_eq_one s fun i hi ↦ have := h1 i hi; Nat.card_of_subsingleton 0,
    Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]

end TauCeti.TateCohomology

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Projection
public import TauCeti.Order.SupIndep

/-!
# Projections onto the summands of an internal direct sum

Mathlib's `Submodule.projectionOnto` projects a module onto one of two complementary submodules.
A family `Q` of submodules that is `iSupIndep` and spans the whole module presents each `Q i` as
complementary to the supremum of the other summands (`iSupIndep.isCompl_biSup_ne`), so each
summand inherits such a projection.

This file records these projections, `TauCeti.internalProjection`. Their pointwise behaviour and
kernel are Mathlib's lemmas about `Submodule.projectionOnto`, restated for the specialization.
The one fact that goes beyond a single projection is that over a finite index type the projections
sum to the identity, `TauCeti.sum_coe_internalProjection`.

For a single complementary pair `F₀`, `F₁`, the projection onto `F₁` also computes any linear map
vanishing on `F₀` from its values on a basis of `F₁`
(`Submodule.apply_eq_sum_repr_projectionOnto`).

## Main definitions

* `TauCeti.internalProjection`: the projection of `M` onto the summand `Q i` of an internal direct
  sum decomposition, as a linear map `M →ₗ[A] Q i`.

## Main results

* `TauCeti.internalProjection_surjective`: the projection onto `Q i` is surjective.
* `TauCeti.ker_internalProjection`: the kernel of the projection onto `Q i` is the supremum of the
  other summands.
* `TauCeti.sum_coe_internalProjection`: over a finite index type the projections onto the summands
  sum to the identity.
* `DirectSum.IsInternal.coe_ofBijective_coeLinearMap_symm_apply_eq_internalProjection`: the
  component supplied by the inverse direct-sum equivalence is the internal projection.
* `Submodule.apply_eq_sum_repr_projectionOnto`: a linear map vanishing on `F₀` is determined by
  its values on a basis of a complement of `F₀`.

## Implementation notes

The decomposition is spelled as `iSupIndep Q` together with `⨆ i, Q i = ⊤` rather than as
`DirectSum.IsInternal`, which carries a `DecidableEq` hypothesis on the index type that nothing
here needs; `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top` converts between the two.
-/

public section

namespace TauCeti

universe u v w

variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]
variable {ι : Type w} {Q : ι → Submodule A M}

/-- The projection of `M` onto the summand `Q i` of an internal direct sum decomposition, along the
supremum of the other summands. -/
noncomputable def internalProjection (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) (i : ι) :
    M →ₗ[A] Q i :=
  (Q i).projectionOnto _ (hQi.isCompl_biSup_ne hQt i)

/-- The projection onto `Q i` fixes the elements of `Q i`. -/
theorem internalProjection_apply_of_mem (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) {i : ι} {x : M}
    (hx : x ∈ Q i) : internalProjection hQi hQt i x = ⟨x, hx⟩ :=
  Submodule.projectionOnto_apply_of_mem_left _ hx

/-- The projection onto `Q i` restricts to the identity on `Q i`. -/
@[simp]
theorem internalProjection_apply (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) {i : ι} (x : Q i) :
    internalProjection hQi hQt i (x : M) = x :=
  Submodule.projectionOnto_apply_left _ x

/-- The projection onto `Q j` kills the elements of any other summand `Q i`. -/
theorem internalProjection_apply_eq_zero_of_mem_of_ne (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤)
    {i j : ι} (hij : i ≠ j) {x : M} (hx : x ∈ Q i) : internalProjection hQi hQt j x = 0 :=
  Submodule.projectionOnto_apply_of_mem_right _
    (le_iSup₂ (f := fun k (_ : k ≠ j) ↦ Q k) i hij hx)

/-- The projection onto `Q j` restricts to `0` on any other summand `Q i`.

This is the form `simp` can use: the summand index `i` is read off the type of `x`, whereas in
`TauCeti.internalProjection_apply_eq_zero_of_mem_of_ne` it appears only in the hypotheses. -/
@[simp]
theorem internalProjection_apply_of_ne (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) {i j : ι}
    (hij : i ≠ j) (x : Q i) : internalProjection hQi hQt j (x : M) = 0 :=
  internalProjection_apply_eq_zero_of_mem_of_ne hQi hQt hij x.2

/-- The projection onto `Q i` is surjective, being the identity on `Q i`. -/
theorem internalProjection_surjective (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) (i : ι) :
    Function.Surjective (internalProjection hQi hQt i) :=
  Submodule.projectionOnto_surjective (hQi.isCompl_biSup_ne hQt i)

/-- The kernel of the projection onto `Q i` is the supremum of the other summands. -/
@[simp]
theorem ker_internalProjection (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) (i : ι) :
    LinearMap.ker (internalProjection hQi hQt i) = ⨆ j, ⨆ (_ : j ≠ i), Q j :=
  Submodule.ker_projectionOnto _

/-- Over a finite index type the projections onto the summands sum to the identity.

The sum of the projections is a linear map agreeing with the identity on each summand, and the
summands span `M`. -/
theorem sum_coe_internalProjection [Fintype ι] (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) (x : M) :
    ∑ i, ((internalProjection hQi hQt i x : M)) = x := by
  have hker : ∀ k : ι, Q k ≤ LinearMap.ker
      ((∑ i, (Q i).subtype ∘ₗ internalProjection hQi hQt i) - LinearMap.id) := by
    intro k y hy
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
      Finset.sum_eq_single_of_mem k (Finset.mem_univ k), sub_eq_zero]
    · simp [internalProjection_apply_of_mem hQi hQt hy]
    · intro j _ hjk
      simp [internalProjection_apply_eq_zero_of_mem_of_ne hQi hQt (Ne.symm hjk) hy]
  have htop : (⊤ : Submodule A M) ≤ LinearMap.ker
      ((∑ i, (Q i).subtype ∘ₗ internalProjection hQi hQt i) - LinearMap.id) := by
    rw [← hQt]
    exact iSup_le hker
  have hx := htop (Submodule.mem_top (x := x))
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
    sub_eq_zero] at hx
  simpa using hx

end TauCeti

namespace DirectSum.IsInternal

variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]
variable {ι : Type w} [DecidableEq ι] {Q : ι → Submodule A M}

/-- The component supplied by the inverse of the canonical internal-direct-sum equivalence is the
projection onto that summand. -/
theorem coe_ofBijective_coeLinearMap_symm_apply_eq_internalProjection
    (h : DirectSum.IsInternal Q) (i : ι) (x : M) :
    ((LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) h).symm x i : M) =
      (TauCeti.internalProjection h.submodule_iSupIndep h.submodule_iSup_eq_top i x : M) := by
  have hx : x ∈ ⨆ j, Q j := by
    rw [h.submodule_iSup_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.iSup_induction' with
  | mem j y hy =>
      rcases eq_or_ne j i with rfl | hji
      · rw [h.ofBijective_coeLinearMap_of_mem hy,
          TauCeti.internalProjection_apply_of_mem h.submodule_iSupIndep
            h.submodule_iSup_eq_top hy]
      · rw [h.ofBijective_coeLinearMap_of_mem_ne hji hy,
          TauCeti.internalProjection_apply_eq_zero_of_mem_of_ne h.submodule_iSupIndep
            h.submodule_iSup_eq_top hji hy]
  | zero => simp
  | add x y _ _ hx hy =>
      simpa only [map_add, DirectSum.add_apply, Submodule.coe_add] using
        congrArg₂ (fun a b ↦ a + b) hx hy

end DirectSum.IsInternal

namespace Submodule

variable {R : Type u} {V : Type v} {M : Type w} [Ring R] [AddCommGroup V] [Module R V]
  [AddCommGroup M] [Module R M]

/-- A linear map vanishing on `F₀` is computed from its values on a basis `b` of a complement
`F₁` of `F₀`, through the coordinates of the projection onto `F₁`. -/
theorem apply_eq_sum_repr_projectionOnto {ι : Type*} [Fintype ι] {F₀ F₁ : Submodule R V}
    (hF : IsCompl F₀ F₁) (b : Module.Basis ι R F₁) (D : V →ₗ[R] M) (hD : ∀ φ : F₀, D φ = 0)
    (v : V) :
    D v = ∑ j, b.repr (F₁.projectionOnto F₀ hF.symm v) j • D (b j) := by
  have hpq : ((F₀.projectionOnto F₁ hF v : F₀) : V) + (F₁.projectionOnto F₀ hF.symm v : V) = v := by
    simpa using LinearMap.congr_fun (subtype_comp_projectionOnto_add_eq_id hF) v
  conv_lhs => rw [← hpq, map_add, hD, zero_add, ← b.sum_repr (F₁.projectionOnto F₀ hF.symm v)]
  simp only [coe_sum, coe_smul, map_sum, map_smul]

end Submodule

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.IntegralBasis
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Conorm

/-!
# Riemann–Roch spaces under a constant field extension

Let `F' = F · k'` be a finite separable constant field extension of an algebraic function field
`F / k` with exact constant field `k`, and let `D` be a divisor of `F / k`.  The Riemann–Roch space
`L(Con D)` of the conorm of `D` is spanned over `k'` by the image of `L(D)`, any `k`-basis of
`L(D)` is a `k'`-basis of `L(Con D)`, and in particular `ℓ(Con D) = ℓ(D)`.

The inclusion of `L(D)` into `L(Con D)` and the linear independence over `k'` of a `k`-basis of
`L(D)` are the elementary half, coming from the local comparison of orders and from linear
disjointness.  Spanning is the local integral-basis statement: an element of `L(Con D)` multiplied
by a function of `F` of order `D P` at a place `P` is integral over `𝒪_P`, so its coordinates in a
basis of constants lie in `𝒪_P`; running over all places, the coordinates lie in `L(D)`.

Together with the preservation of divisor degrees, the dimension identity is what transports the
genus, the Riemann–Roch theorem and its consequences between `F / k` and `F' / k'`.

## Main results

* `TauCeti.repr_constantBasis_mem_riemannRochSpace`: the coordinates of an element of `L(Con D)`
  in a basis of constants lie in `L(D)`.
* `TauCeti.riemannRochSpace_conorm_eq_span`: `L(Con D)` is the `k'`-span of the image of `L(D)`.
* `TauCeti.riemannRochSpaceConormBasis`: a `k`-basis of `L(D)` as a `k'`-basis of `L(Con D)`.
* `TauCeti.Divisor.dim_conorm`: `ℓ(Con D) = ℓ(D)`.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
Theorem 3.6.3(d).
-/

public section

open Module

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [Algebra.IsSeparable k k']

attribute [local instance 10] Place.algebraIntegersExtension Place.isScalarTowerIntegersExtension

/-- **The coordinates of an element of `L(Con D)` in a basis of constants lie in `L(D)`**: at each
place `P` of `F / k`, clearing the pole order allowed by `D` makes the element integral over
`𝒪_P`, and a basis of constants is an integral basis at `P`. -/
theorem repr_constantBasis_mem_riemannRochSpace (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hF' : IsFunctionField k' F') {ι : Type*}
    (b : Basis ι k k') {D : Divisor k F} {z : F'}
    (hz : z ∈ riemannRochSpace (Divisor.conorm k' F' D)) (i : ι) :
    (constantBasis hex h b).repr z i ∈ riemannRochSpace D := by
  have := finiteDimensional_base_of_constantCompositum_eq_top hex h
  have := Module.Finite.finite_basis b
  set x := (constantBasis hex h b).repr z i with hx
  rcases eq_or_ne x 0 with hx0 | hx0
  · rw [hx0]
    exact zero_mem _
  rw [mem_riemannRochSpace_iff_neg_le_ord hx0]
  intro P
  obtain ⟨s, hs0, hs⟩ := P.exists_ne_zero_ord_eq (D.coeff P)
  -- multiplying by `s`, of order `D P` at `P`, makes `z` regular at every place over `P`
  have hint : IsIntegral P.integers (s • z) := by
    rw [Place.isIntegral_iff_forall_restrict_eq_mem_integers hF']
    intro P' hP'
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    have hs0' : algebraMap F F' s ≠ 0 := (map_ne_zero _).2 hs0
    rw [Algebra.smul_def, Place.mem_integers_iff_ord_nonneg, P'.ord_mul hs0' hz0,
      Place.ord_algebraMap_restrict k F P' s, hP', hs]
    have hord := (mem_riemannRochSpace_iff_neg_le_ord hz0).1 hz P'
    rw [Divisor.coeff_conorm, hP'] at hord
    linarith
  have hrepr := (Place.isIntegralBasis_constantBasis hex h b P).isIntegral_iff_repr_mem.1 hint i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← hx, Place.mem_integers_iff_ord_nonneg,
    P.ord_mul hs0 hx0, hs] at hrepr
  linarith

/-- **`L(Con D)` is spanned over `k'` by `L(D)`** (Stichtenoth, Theorem 3.6.3(d)): the
Riemann–Roch space of the conorm of `D` in a finite separable constant field extension is the
`k'`-span of the image of the Riemann–Roch space of `D`. -/
theorem riemannRochSpace_conorm_eq_span (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hF' : IsFunctionField k' F') (D : Divisor k F) :
    riemannRochSpace (Divisor.conorm k' F' D) =
      Submodule.span k' (algebraMap F F' '' riemannRochSpace D) := by
  have := finiteDimensional_base_of_constantCompositum_eq_top hex h
  refine le_antisymm (fun z hz ↦ ?_) (Submodule.span_le.2 ?_)
  · let b := Module.finBasis k k'
    rw [← (constantBasis hex h b).linearCombination_repr z, Finsupp.linearCombination_apply]
    apply Submodule.finsuppSum_mem
    intro i _
    rw [Algebra.smul_def, constantBasis_apply, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨_, repr_constantBasis_mem_riemannRochSpace hex h hF' b hz i, rfl⟩)
  · rintro _ ⟨f, hf, rfl⟩
    exact (mem_riemannRochSpace_conorm_iff hF' D f).2 hf

omit [FiniteDimensional F F'] in
/-- The image of a `k`-basis of `L(D)` is linearly independent over `k'`: `F` and `k'` are
linearly disjoint over `k` (Stichtenoth, Proposition 3.6.1(b)). -/
theorem linearIndependent_algebraMap_riemannRochSpace (hex : IsIntegrallyClosedIn k F)
    {D : Divisor k F} {ι : Type*} (b : Basis ι k (riemannRochSpace D)) :
    LinearIndependent k' fun i ↦ algebraMap F F' (b i) :=
  linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn_of_isSeparable hex
    (b.linearIndependent.map' (riemannRochSpace D).subtype (Submodule.ker_subtype _))

/-- The `k'`-span of the image of a `k`-basis of `L(D)` is `L(Con D)`. -/
theorem span_range_algebraMap_eq_riemannRochSpace_conorm (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hF' : IsFunctionField k' F') (D : Divisor k F)
    {ι : Type*} (b : Basis ι k (riemannRochSpace D)) :
    Submodule.span k' (Set.range fun i ↦ algebraMap F F' (b i)) =
      riemannRochSpace (Divisor.conorm k' F' D) := by
  rw [riemannRochSpace_conorm_eq_span hex h hF']
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact ⟨b i, (b i).2, rfl⟩
  rintro _ ⟨f, hf, rfl⟩
  -- `L(D)` is the `k`-span of `b`, so the image of `f` lies in the `k`-span of the image of `b`
  have hf' : f ∈ Submodule.span k (Set.range fun i ↦ (b i : F)) := by
    rwa [← Submodule.map_subtype_top (riemannRochSpace D), ← b.span_eq, Submodule.map_span,
      ← Set.range_comp] at hf
  have hmem : algebraMap F F' f ∈
      Submodule.span k (Set.range fun i ↦ algebraMap F F' (b i)) := by
    have := Submodule.mem_map_of_mem (f := (IsScalarTower.toAlgHom k F F').toLinearMap) hf'
    rwa [Submodule.map_span, ← Set.range_comp] at this
  exact Submodule.span_le_restrictScalars k k' _ hmem

/-- **A basis of `L(D)` is a basis of `L(Con D)`** (Stichtenoth, Theorem 3.6.3(d)): in a finite
separable constant field extension, the image of a `k`-basis of the Riemann–Roch space of `D` is a
`k'`-basis of the Riemann–Roch space of the conorm of `D`. -/
noncomputable def riemannRochSpaceConormBasis (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hF' : IsFunctionField k' F') (D : Divisor k F)
    {ι : Type*} (b : Basis ι k (riemannRochSpace D)) :
    Basis ι k' (riemannRochSpace (Divisor.conorm k' F' D)) :=
  (Basis.span (linearIndependent_algebraMap_riemannRochSpace hex b)).map
    (LinearEquiv.ofEq _ _ (span_range_algebraMap_eq_riemannRochSpace_conorm hex h hF' D b))

@[simp]
theorem riemannRochSpaceConormBasis_apply (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hF' : IsFunctionField k' F') (D : Divisor k F)
    {ι : Type*} (b : Basis ι k (riemannRochSpace D)) (i : ι) :
    (riemannRochSpaceConormBasis hex h hF' D b i : F') = algebraMap F F' (b i) := by
  simp [riemannRochSpaceConormBasis]

/-- **`ℓ(Con D) = ℓ(D)`** (Stichtenoth, Theorem 3.6.3(d)): the dimension of a Riemann–Roch space
is unchanged by a finite separable constant field extension. -/
theorem Divisor.dim_conorm (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    (hF' : IsFunctionField k' F') (D : Divisor k F) : (Divisor.conorm k' F' D).dim = D.dim := by
  rw [Divisor.dim_def, Divisor.dim_def,
    Module.finrank_eq_nat_card_basis
      (riemannRochSpaceConormBasis hex h hF' D (Basis.ofVectorSpace k (riemannRochSpace D))),
    Module.finrank_eq_nat_card_basis (Basis.ofVectorSpace k (riemannRochSpace D))]

end TauCeti

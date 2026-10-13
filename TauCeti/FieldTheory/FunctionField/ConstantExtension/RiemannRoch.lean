/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.FiniteDescent
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

For a separable algebraic extension `k' / k` that need not be finite, the multiples `n (z)_∞` of
a pole divisor are defined in `F'` directly, without a conorm, and the same comparison holds for
them: `L(n (z)_∞)` of `F' / k'` is the `k'`-span of the image of `L(n (z)_∞)` of `F / k`, and the
two dimensions agree.  An element of the larger space is defined over a finite subextension `L` of
`k' / k` (`ConstantExtension.FiniteDescent`), where the finite theorem applies to `F · L / L`.

## Main results

* `TauCeti.repr_constantBasis_mem_riemannRochSpace`: the coordinates of an element of `L(Con D)`
  in a basis of constants lie in `L(D)`.
* `TauCeti.riemannRochSpace_conorm_eq_span`: `L(Con D)` is the `k'`-span of the image of `L(D)`.
* `TauCeti.riemannRochSpaceConormBasis`: a `k`-basis of `L(D)` as a `k'`-basis of `L(Con D)`.
* `TauCeti.Divisor.dim_conorm`: `ℓ(Con D) = ℓ(D)`.
* `TauCeti.Divisor.finrank_mul_dim_le_finrank_mul_dim_conorm`: for an arbitrary finite constant
  field extension, separable or not and over any constant field, the inequality
  `[F' : F] · ℓ(D) ≤ [k' : k] · ℓ(Con D)`.
* `TauCeti.riemannRochSpace_nsmul_poles_eq_span_of_constantCompositum_eq_top` and
  `TauCeti.Divisor.dim_nsmul_poles_of_constantCompositum_eq_top`: along any separable algebraic
  constant field extension, `L(n (z)_∞)` of `F' / k'` is the `k'`-span of the image of
  `L(n (z)_∞)` of `F / k`, and the two dimensions are equal.

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

omit [FiniteDimensional F F'] [Algebra.IsSeparable k k'] in
/-- The `k'`-span of the image of `L(D)` in `F'` is the `k'`-span of the image of a `k`-basis of
`L(D)`. -/
theorem span_image_riemannRochSpace_eq_span_range {D : Divisor k F} {ι : Type*}
    (b : Basis ι k (riemannRochSpace D)) :
    Submodule.span k' (algebraMap F F' '' riemannRochSpace D) =
      Submodule.span k' (Set.range fun i ↦ algebraMap F F' (b i)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · -- every element of `L(D)` is a `k`-combination of `b`, and `F → F'` is `k`-linear
    rintro _ ⟨f, hf, rfl⟩
    lift f to riemannRochSpace D using hf
    induction b.mem_span f using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx =>
      rw [Submodule.coe_smul, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        ← Algebra.smul_def]
      exact Submodule.smul_of_tower_mem _ a hx
  · rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨b i, (b i).2, rfl⟩

/-- The `k'`-span of the image of a `k`-basis of `L(D)` is `L(Con D)`. -/
theorem span_range_algebraMap_eq_riemannRochSpace_conorm (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hF' : IsFunctionField k' F') (D : Divisor k F)
    {ι : Type*} (b : Basis ι k (riemannRochSpace D)) :
    Submodule.span k' (Set.range fun i ↦ algebraMap F F' (b i)) =
      riemannRochSpace (Divisor.conorm k' F' D) := by
  rw [riemannRochSpace_conorm_eq_span hex h hF', span_image_riemannRochSpace_eq_span_range b]

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

/-! ### Arbitrary finite constant field extensions -/

omit [Algebra.IsSeparable k k'] in
/-- **`ℓ(D)` against `ℓ(Con D)` for an arbitrary finite constant field extension**: if
`F' = F · k'` for a finite extension `k' / k`, then `[F' : F] · ℓ(D) ≤ [k' : k] · ℓ(Con D)` for
every divisor `D` of `F / k`.  Neither exactness of `k` in `F` nor separability of `k' / k` is
assumed.

For a separable `k' / k` over an exact constant field, `[F' : F] = [k' : k]` and the sharper
`TauCeti.Divisor.dim_conorm` gives `ℓ(Con D) = ℓ(D)`. -/
theorem Divisor.finrank_mul_dim_le_finrank_mul_dim_conorm [FiniteDimensional k k']
    (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤) (D : Divisor k F) :
    Module.finrank F F' * D.dim ≤ Module.finrank k k' * (Divisor.conorm k' F' D).dim := by
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  -- constants `c j` forming an `F`-basis of `F'`, extracted from the image of a basis of `k'`
  let b := Module.finBasis k k'
  obtain ⟨κ, a, ha, hspan, hc⟩ := exists_linearIndependent' F (algebraMap k' F' ∘ b)
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ = Module.finrank F F' := by
    rw [← finrank_span_eq_card hc, hspan,
      span_range_algebraMap_comp_of_constantCompositum_eq_top h b, finrank_top]
  -- constants have no poles
  have hc0 (j : κ) : (algebraMap k' F' ∘ b ∘ a) j ∈ riemannRochSpace (0 : Divisor k' F') := by
    rw [Function.comp_apply, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (mem_riemannRochSpace_iff.2 fun P ↦ by simp)
  have hdim := Divisor.card_mul_dim_le_finrank_mul_dim_conorm_add hF' hc hc0 D
  rwa [add_zero, hκ] at hdim

/-! ### Separable algebraic constant field extensions -/

omit [FiniteDimensional F F'] in
/-- **`L(n (z)_∞)` along a separable algebraic constant field extension** (Stichtenoth,
Theorem 3.6.3(d), for pole divisors): if `k` is the exact constant field of `F` and
`F' = F · k'` for a separable algebraic, possibly infinite, extension `k' / k`, then the
Riemann–Roch space of `n (z)_∞` in `F' / k'` is the `k'`-span of the image of the Riemann–Roch
space of `n (z)_∞` in `F / k`. -/
theorem riemannRochSpace_nsmul_poles_eq_span_of_constantCompositum_eq_top
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (n : ℕ) (z : Fˣ) :
    riemannRochSpace (n • Divisor.poles (hF.of_constantCompositum_eq_top h)
        (Units.map (algebraMap F F' : F →* F') z)) =
      Submodule.span k' (algebraMap F F' '' riemannRochSpace (n • Divisor.poles hF z)) := by
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have := isAlgebraic_of_constantCompositum_eq_top (k := k) h
  refine le_antisymm (fun g hg ↦ ?_) (Submodule.span_le.2 ?_)
  · -- `g` lies in `E = F · L` for a finite subextension `L` of `k' / k`
    obtain ⟨L, hL, hgL⟩ := exists_finiteDimensional_constantSubfield_of_mem_constantCompositum
      (k := k) (F := F) (h ▸ IntermediateField.mem_top : g ∈ constantCompositum F k' F')
    let E := constantCompositum F L F'
    let : Algebra L E := constantCompositumAlgebra F L F'
    have : IsScalarTower L E F' := isScalarTower_constantCompositum F L F'
    have : IsScalarTower k L E := isScalarTower_base_constantCompositum k F L F'
    have hE : constantCompositum F L E = ⊤ := (constantCompositum_eq_top_iff F L F' E).2 rfl
    have : FiniteDimensional F E := finiteDimensional_of_constantCompositum_eq_top (k := k) hE
    have hFE : IsFunctionField L E := hF.of_constantCompositum_eq_top hE
    have : Algebra.IsIntegral E F' := Algebra.IsIntegral.tower_top F
    have : Algebra.IsIntegral L k' := Algebra.IsIntegral.tower_top k
    have hzE : Units.map (algebraMap E F' : E →* F') (Units.map (algebraMap F E : F →* E) z) =
        Units.map (algebraMap F F' : F →* F') z := by
      ext
      exact (IsScalarTower.algebraMap_apply F E F' _).symm
    -- in `E`, the element lies in `L(Con (n (z)_∞))`, which the finite theorem describes
    have hgE : (⟨g, hgL⟩ : E) ∈ riemannRochSpace
        (Divisor.conorm L E (n • Divisor.poles hF z)) := by
      rw [map_nsmul, Divisor.conorm_poles L E hF hFE,
        ← mem_riemannRochSpace_nsmul_poles_map_iff (k' := k') hFE hF', hzE]
      exact hg
    rw [riemannRochSpace_conorm_eq_span hex hE hFE] at hgE
    have hmap := Submodule.mem_map_of_mem (f := (IsScalarTower.toAlgHom L E F').toLinearMap) hgE
    rw [Submodule.map_span, ← Set.image_comp] at hmap
    have himg : ⇑(IsScalarTower.toAlgHom L E F').toLinearMap ∘ ⇑(algebraMap F E) =
        ⇑(algebraMap F F') := funext fun f ↦ (IsScalarTower.algebraMap_apply F E F' f).symm
    rw [himg] at hmap
    exact Submodule.span_le_restrictScalars L k' _ hmap
  · rintro _ ⟨f, hf, rfl⟩
    exact (mem_riemannRochSpace_nsmul_poles_map_iff hF hF' n z f).2 hf

omit [FiniteDimensional F F'] in
/-- **`ℓ(n (z)_∞)` is unchanged by a separable algebraic constant field extension** (Stichtenoth,
Theorem 3.6.3(d), for pole divisors): if `k` is the exact constant field of `F` and
`F' = F · k'` for a separable algebraic, possibly infinite, extension `k' / k`, then
`n (z)_∞` has the same dimension in `F' / k'` as in `F / k`. -/
theorem Divisor.dim_nsmul_poles_of_constantCompositum_eq_top
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (n : ℕ) (z : Fˣ) :
    (n • Divisor.poles (hF.of_constantCompositum_eq_top h)
        (Units.map (algebraMap F F' : F →* F') z)).dim = (n • Divisor.poles hF z).dim := by
  set D := n • Divisor.poles hF z
  have := finiteDimensional_riemannRochSpace hF D
  let b := Module.finBasis k (riemannRochSpace D)
  rw [Divisor.dim_def, Divisor.dim_def,
    riemannRochSpace_nsmul_poles_eq_span_of_constantCompositum_eq_top hF hex h,
    span_image_riemannRochSpace_eq_span_range b,
    finrank_span_eq_card (linearIndependent_algebraMap_riemannRochSpace hex b),
    Fintype.card_fin]

end TauCeti

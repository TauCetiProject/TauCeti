/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Sheaf

/-!
# Germs of sections of the sheaf of a Weil divisor

The sections of `𝒪_X(D)` over an open subset `U` are the rational functions whose order at every
codimension-one point of `U` is at least `-D`. Shrinking `U` around a point `x` weakens that
condition, and this file identifies what survives in the limit: a rational function is a section
of `𝒪_X(D)` on *some* neighbourhood of `x` exactly when it satisfies the order bound at the
codimension-one points which generize `x`.

Only finitely many codimension-one points can obstruct the bound, because a nonzero rational
function has nonzero order at finitely many of them and `D` has finite support; deleting the
closures of the obstructing points leaves an open neighbourhood of `x` on which the bound holds
at every codimension-one point.

## Main declarations

* `SchemeWeilDivisor.finite_setOf_ord_lt`: the codimension-one points at which a nonzero rational
  function violates the bound imposed by `D` are finite in number;
* `SchemeWeilDivisor.exists_map_mem_sections_of_forall_specializes` and
  `SchemeWeilDivisor.exists_map_mem_sections_iff`: the germ criterion, that a section of `𝒦_X`
  becomes a section of `𝒪_X(D)` near `x` exactly when it satisfies the order bound at every
  codimension-one generization of `x`;
* `SchemeWeilDivisor.exists_map_mem_sections_iff_codimensionOne`: at a codimension-one point `x₀`
  the only codimension-one generization is `x₀` itself, so near `x₀` the sheaf `𝒪_X(D)` is cut out
  by the single valuation of the local ring there, and
  `SchemeWeilDivisor.exists_map_mem_sections_ord_eq`: every order allowed by that valuation is
  attained.

Together with the comparison-map results in
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Sheaf.lean`, the germ results show that the
comparison `𝒪_X(D) ⟶ 𝒪_X(D + x₀)` is an isomorphism on sections away from `closure {x₀}` and
compute the sections of both sheaves near `x₀`. They are the local input for the later construction
of the exact sequence `0 ⟶ 𝒪_X(D) ⟶ 𝒪_X(D + x₀) ⟶ 𝒮 ⟶ 0` with `𝒮` a skyscraper sheaf at `x₀`,
along which the Euler characteristic of a divisor sheaf is computed by induction on the divisor.

The finiteness input is
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Principal.lean`, the sections are
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Sheaf.lean`, the surjectivity of the order at a
codimension-one point with a discrete valuation ring as local ring is
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Order.lean`, and the topological input is Mathlib's
specialization order (`Specializes.mem_open`, `specializes_iff_mem_closure`).

## References

* R. Hartshorne, *Algebraic Geometry*, II.6.
* The Stacks Project, *Divisors*, Tag 0BE0.
-/

public section

open CategoryTheory Order TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

noncomputable section

section Noetherian

variable [IsNoetherian X]

omit [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))] in
/-- The codimension-one points at which a nonzero rational function violates the order bound
imposed by `D` form a finite set: away from the support of `D` and from the finitely many points
where the function has nonzero order, that bound reads `0 ≤ 0`. -/
lemma finite_setOf_ord_lt (D : SchemeWeilDivisor X) {f : X.functionField} (hf : f ≠ 0) :
    {y : CodimensionOnePoint X | X.ord f y < -WeilDivisor.coeff D y}.Finite := by
  have hfin : (Function.support fun y : CodimensionOnePoint X ↦ X.ord f y).Finite := by
    simpa using finite_support_orderAt (X := X) (Additive.ofMul (Units.mk0 f hf))
  refine ((D.support.finite_toSet).union hfin).subset fun y hy ↦ ?_
  by_contra hcon
  simp only [Set.mem_union, not_or, Finset.mem_coe, WeilDivisor.mem_support_iff,
    Function.mem_support, ne_eq, not_not] at hcon
  rw [Set.mem_ofPred_eq, hcon.1, hcon.2] at hy
  simp at hy

/-- **A section of `𝒦_X` bounded at the codimension-one generizations of `x` is a section of
`𝒪_X(D)` near `x`.** The finitely many codimension-one points where the bound fails are deleted
together with their closures, which leaves a neighbourhood of `x` because none of them generizes
`x`. -/
theorem exists_map_mem_sections_of_forall_specializes (D : SchemeWeilDivisor X)
    {V : X.Opens} [Nonempty V] {x : X} (hxV : x ∈ V) (s : Γ(Scheme.rationalFunctions X, V))
    (h : ∀ y : CodimensionOnePoint X, (y : X) ⤳ x →
      Scheme.rationalFunctionsEquiv V s = 0 ∨
        -WeilDivisor.coeff D y ≤ X.ord (Scheme.rationalFunctionsEquiv V s) y) :
    ∃ (U : X.Opens) (i : U ⟶ V), x ∈ U ∧
      (Scheme.rationalFunctions X).presheaf.map i.op s ∈ sections D U := by
  set f := Scheme.rationalFunctionsEquiv V s with hf
  rcases eq_or_ne f 0 with hf0 | hf0
  · refine ⟨V, 𝟙 V, hxV, mem_sections.mpr fun y hy ↦ ?_⟩
    have : Nonempty V := ⟨⟨y, hy⟩⟩
    simp only [op_id, CategoryTheory.Functor.map_id]
    exact Or.inl (hf ▸ hf0)
  -- The codimension-one points at which the bound fails, and the closed set they sweep out.
  let B : Set (CodimensionOnePoint X) := {y | X.ord f y < -WeilDivisor.coeff D y}
  have hmemB : ∀ y : CodimensionOnePoint X, y ∈ B ↔ X.ord f y < -WeilDivisor.coeff D y :=
    fun _ ↦ Iff.rfl
  have hBfin : B.Finite := finite_setOf_ord_lt D hf0
  have hZ : IsClosed (⋃ y ∈ B, closure {(y : X)}) :=
    hBfin.isClosed_biUnion fun _ _ ↦ isClosed_closure
  have hxZ : x ∉ ⋃ y ∈ B, closure {(y : X)} := by
    simp only [Set.mem_iUnion, not_exists]
    intro y hy hx'
    rcases h y (specializes_iff_mem_closure.mpr hx') with h0 | hle
    · exact hf0 (hf ▸ h0)
    · exact absurd hle (not_le.mpr ((hmemB y).mp hy))
  refine ⟨V ⊓ ⟨(⋃ y ∈ B, closure {(y : X)})ᶜ, hZ.isOpen_compl⟩, homOfLE inf_le_left,
    Opens.mem_inf.mpr ⟨hxV, hxZ⟩, mem_sections.mpr fun y hy ↦ ?_⟩
  obtain ⟨hyV, hyZ⟩ := Opens.mem_inf.mp hy
  have : Nonempty (V ⊓ ⟨(⋃ y ∈ B, closure {(y : X)})ᶜ, hZ.isOpen_compl⟩ : X.Opens) := ⟨⟨y, hy⟩⟩
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  rw [Scheme.rationalFunctionsEquiv_map]
  exact Or.inr (not_lt.mp fun hlt ↦
    hyZ (Set.mem_biUnion ((hmemB y).mpr hlt) (subset_closure rfl)))

/-- **The germ criterion for the sheaf of a Weil divisor.** A section of `𝒦_X` defined near `x`
restricts to a section of `𝒪_X(D)` on some neighbourhood of `x` exactly when it satisfies the
order bound imposed by `D` at every codimension-one point generizing `x`. -/
theorem exists_map_mem_sections_iff (D : SchemeWeilDivisor X) {V : X.Opens} [Nonempty V] {x : X}
    (hxV : x ∈ V) (s : Γ(Scheme.rationalFunctions X, V)) :
    (∃ (U : X.Opens) (i : U ⟶ V), x ∈ U ∧
        (Scheme.rationalFunctions X).presheaf.map i.op s ∈ sections D U) ↔
      ∀ y : CodimensionOnePoint X, (y : X) ⤳ x →
        Scheme.rationalFunctionsEquiv V s = 0 ∨
          -WeilDivisor.coeff D y ≤ X.ord (Scheme.rationalFunctionsEquiv V s) y := by
  refine ⟨fun ⟨U, i, hxU, hU⟩ y hy ↦ ?_,
    exists_map_mem_sections_of_forall_specializes D hxV s⟩
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  rw [← Scheme.rationalFunctionsEquiv_map i s]
  exact mem_sections.mp hU y (hy.mem_open U.isOpen hxU)

/-- **The local model of `𝒪_X(D)` at a codimension-one point.** A codimension-one point `x₀` has
no codimension-one generization but itself, so a section of `𝒦_X` is a section of `𝒪_X(D)` near
`x₀` exactly when its order at `x₀` is at least `-D x₀`. -/
theorem exists_map_mem_sections_iff_codimensionOne (D : SchemeWeilDivisor X) {V : X.Opens}
    [Nonempty V] (x₀ : CodimensionOnePoint X) (hx₀ : (x₀ : X) ∈ V)
    (s : Γ(Scheme.rationalFunctions X, V)) :
    (∃ (U : X.Opens) (i : U ⟶ V), (x₀ : X) ∈ U ∧
        (Scheme.rationalFunctions X).presheaf.map i.op s ∈ sections D U) ↔
      Scheme.rationalFunctionsEquiv V s = 0 ∨
        -WeilDivisor.coeff D x₀ ≤ X.ord (Scheme.rationalFunctionsEquiv V s) x₀ := by
  rw [exists_map_mem_sections_iff D hx₀ s]
  refine ⟨fun h ↦ h x₀ (specializes_refl _), fun h y hy ↦ ?_⟩
  rw [CodimensionOnePoint.eq_of_specializes hy]
  exact h

/-- Every order the local ring at a codimension-one point `x₀` allows is attained by a section of
`𝒪_X(D)` near `x₀`: the bound of `exists_map_mem_sections_iff_codimensionOne` is sharp. -/
theorem exists_map_mem_sections_ord_eq (D : SchemeWeilDivisor X) {V : X.Opens} [Nonempty V]
    (x₀ : CodimensionOnePoint X) (hx₀ : (x₀ : X) ∈ V) {n : ℤ}
    (hn : -WeilDivisor.coeff D x₀ ≤ n) :
    ∃ (s : Γ(Scheme.rationalFunctions X, V)) (U : X.Opens) (i : U ⟶ V), (x₀ : X) ∈ U ∧
      (Scheme.rationalFunctions X).presheaf.map i.op s ∈ sections D U ∧
        X.ord (Scheme.rationalFunctionsEquiv V s) x₀ = n := by
  obtain ⟨g, hg⟩ := exists_orderAt_eq x₀ n
  refine ⟨(Scheme.rationalFunctionsEquiv V).symm
    ((Additive.toMul g : X.functionFieldˣ) : X.functionField), ?_⟩
  have hord : X.ord (Scheme.rationalFunctionsEquiv V ((Scheme.rationalFunctionsEquiv V).symm
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField))) x₀ = n := by
    rw [LinearEquiv.apply_symm_apply, ← orderAt_apply x₀ g, hg]
  obtain ⟨U, i, hxU, hU⟩ :=
    (exists_map_mem_sections_iff_codimensionOne D x₀ hx₀ _).mpr (Or.inr (hord ▸ hn))
  exact ⟨U, i, hxU, hU, hord⟩

end Noetherian

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti

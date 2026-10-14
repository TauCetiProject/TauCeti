/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.AlgebraicGeometry.Curves.Degree
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Finite
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Space

/-!
# The Euler-characteristic degree of an effective Cartier divisor

Let `X` be a scheme over a field `k` and `I ⊆ 𝒪_X` an ideal sheaf whose closed subscheme
`D = V(I)` is finite over `k`, of rank `dim_k Γ(D, 𝒪_D)`. The exact sequence
`0 ⟶ I ⟶ 𝒪_X ⟶ ι_* 𝒪_D ⟶ 0` and the vanishing of higher cohomology on the affine Noetherian
scheme `D` give

  `χ(I) = χ(𝒪_X) - dim_k Γ(D, 𝒪_D)`

(`Scheme.IdealSheafData.eulerCharBelow_sheaf`), where `χ` is the degree-`2` truncation
`dim H⁰ - dim H¹` and `H⁰(X, 𝒪_X)`, `H¹(X, 𝒪_X)` are assumed finite-dimensional. When `I` is the
ideal sheaf `𝒪_X(-D)` of an effective Cartier divisor `D`, this says that the line bundle `𝒪_X(-D)`
has Euler-characteristic degree `-dim_k Γ(D, 𝒪_D)`
(`Scheme.IdealSheafData.IsEffectiveCartier.eulerDegree_toInvertibleSheaf`). On a connected
smooth proper curve over `k` the degree is additive, so `𝒪_X(D)` has degree
`dim_k Γ(D, 𝒪_D)` (`Scheme.IdealSheafData.IsEffectiveCartier.eulerDegree_inv_mk_toInvertibleSheaf`).
This is the classical `deg 𝒪_X(D) = deg D` for effective divisors, with the degree of `D` read off
as the rank of its closed subscheme, the notion of degree used for relative effective Cartier
divisors in families.

The rank is Mathlib's `Scheme.Hom.finrank` of the finite morphism `D ⟶ Spec k`, evaluated at the
unique point of `Spec k`; it is `dim_k Γ(D, 𝒪_D)` by
`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_of_field`.

## References

* R. Hartshorne, *Algebraic Geometry*: Proposition II.6.18 (`𝒪_X(-D)` is the ideal sheaf of
  `D`), Lemma III.2.10 and Theorem III.3.5 (the cohomology of `𝒪_D`), and the proof of
  Theorem IV.1.3 (Riemann–Roch), where degrees are computed from the same kind of exact
  sequence.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order
open TauCeti.AlgebraicGeometry Scheme.Modules
open Module (finrank)

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] (I : X.IdealSheafData)

/-- For the structure of scheme over `k` on `V(I)` given by `V(I) ⟶ X ⟶ Spec k`, the `k`-algebra
structure on its global functions is the map of global sections of that morphism. -/
private lemma algebraMap_eq :
    letI : I.subscheme.Over (Spec (.of k)) := ⟨I.subschemeι ≫ X ↘ Spec (.of k)⟩
    letI : Algebra k Γ(I.subscheme, ⊤) := (baseRingToGlobalSections k I.subscheme).toAlgebra
    algebraMap k Γ(I.subscheme, ⊤) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ X ↘ Spec (.of k)).appTop).hom := by
  let _ : I.subscheme.Over (Spec (.of k)) := ⟨I.subschemeι ≫ X ↘ Spec (.of k)⟩
  exact RingHom.ext fun r ↦ baseRingToGlobalSections_apply k I.subscheme r

section Finite

variable [IsFinite (I.subschemeι ≫ X ↘ Spec (.of k))]

include k in
/-- A closed subscheme finite over `k` is affine and Noetherian, so its structure sheaf has no
first cohomology. -/
private lemma subsingleton_cohomology_one_subscheme :
    Subsingleton (Cohomology
      (SheafOfModules.unit I.subscheme.ringCatSheaf : I.subscheme.Modules) 1) := by
  have : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ X ↘ Spec (.of k))
  have : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ X ↘ Spec (.of k))
  have : IsNoetherianRing Γ(I.subscheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have := subsingleton_cohomologyOn_succ_of_isAffineOpen
    (SheafOfModules.unit I.subscheme.ringCatSheaf) (isAffineOpen_top _) 0
  exact (cohomologyOnTopIso _ 1).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

/-- The Euler characteristic of the direct image of the structure sheaf of a closed subscheme
finite over `k` is its rank over `k`: its first cohomology vanishes, and its global sections have
dimension the rank. -/
private lemma eulerCharBelow_pushforward_subscheme (s : Spec (.of k)) :
    eulerCharBelow k X ((Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)) 2 =
      (I.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  let _ : I.subscheme.Over (Spec (.of k)) := ⟨I.subschemeι ≫ X ↘ Spec (.of k)⟩
  have : I.subschemeι.IsOver (Spec (.of k)) := ⟨rfl⟩
  let M : I.subscheme.Modules := SheafOfModules.unit I.subscheme.ringCatSheaf
  have := subsingleton_cohomology_one_subscheme k I
  refine (Scheme.Hom.eulerCharBelow_pushforward I.subschemeι k M 2).trans ?_
  rw [eulerCharBelow_two, Module.finrank_zero_of_subsingleton (M := Cohomology M 1),
    finrank_cohomology_zero_eq_finrank_globalSections]
  let _ : Algebra k Γ(I.subscheme, ⊤) := (baseRingToGlobalSections k I.subscheme).toAlgebra
  rw [Scheme.Hom.finrank_eq_finrank_of_field _ (algebraMap_eq k I) s]
  -- Both module structures on `Γ(V(I), ⊤)` are restriction of scalars along
  -- `baseRingToGlobalSections`, and the sections of `𝒪_{V(I)}` are the regular functions.
  rfl

section FiniteCohomology

variable [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- **The Euler characteristic of an ideal sheaf.** If `I ⊆ 𝒪_X` cuts out a closed subscheme
`D` finite over the field `k`, and `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)` are finite-dimensional, then
`χ(I) = χ(𝒪_X) - dim_k Γ(D, 𝒪_D)`, with `χ = dim H⁰ - dim H¹` and the dimension of `Γ(D, 𝒪_D)`
written as the rank of `D ⟶ Spec k` at the point `s`. No dimension or properness hypothesis on
`X` is needed. -/
theorem eulerCharBelow_sheaf (s : Spec (.of k)) :
    eulerCharBelow k X I.sheaf 2 =
      eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2 -
        (I.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  have hS := I.shortComplex_shortExact
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit ≅ SheafOfModules.unit X.ringCatSheaf :=
    TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf
  -- `H⁰` and `H¹` of `𝒪_X` are finite-dimensional.
  have h₂ (i : ℕ) (hi : i < 2) : FiniteDimensional k (Cohomology I.shortComplex.X₂ i) := by
    rw [shortComplex_X₂]
    refine (finiteDimensional_cohomology_congr k e i).mp ?_
    rw [← InvertibleSheaf.trivial_obj]
    interval_cases i <;> infer_instance
  -- `H⁰` of `ι_* 𝒪_{V(I)}` is finite-dimensional and its `H¹` vanishes.
  let _ : I.subscheme.Over (Spec (.of k)) := ⟨I.subschemeι ≫ X ↘ Spec (.of k)⟩
  have : I.subschemeι.IsOver (Spec (.of k)) := ⟨rfl⟩
  let M : I.subscheme.Modules := SheafOfModules.unit I.subscheme.ringCatSheaf
  have : FiniteDimensional k (Cohomology I.shortComplex.X₃ 0) := by
    let _ : Algebra k Γ(I.subscheme, ⊤) := (baseRingToGlobalSections k I.subscheme).toAlgebra
    have : Module.Finite k Γ(M, ⊤) :=
      -- The base-ring module structure on the global sections of `𝒪_{V(I)}` is the one given by
      -- the algebra structure, both being restriction of scalars along
      -- `baseRingToGlobalSections`.
      (I.subschemeι ≫ X ↘ Spec (.of k)).moduleFinite_appTop (algebraMap_eq k I)
    rw [shortComplex_X₃]
    refine (Scheme.Hom.moduleFinite_cohomology_pushforward_iff I.subschemeι k M 0).mpr ?_
    exact Module.Finite.equiv (cohomologyZeroBaseLinearEquiv k I.subscheme M).symm
  have hvan : Subsingleton (Cohomology I.shortComplex.X₃ 1) := by
    have := subsingleton_cohomology_one_subscheme k I
    rw [shortComplex_X₃]
    exact (cohomologyPushforwardIso I.subschemeι M 1).addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  -- `H¹(X, I)` sits between `H⁰(ι_* 𝒪_{V(I)})` and `H¹(X, 𝒪_X)`, so it is finite-dimensional.
  have h₁ (i : ℕ) (hi : i < 2) (hi' : 0 < i) :
      FiniteDimensional k (Cohomology I.shortComplex.X₁ i) := by
    obtain rfl : i = 1 := by omega
    have := h₂ 1 (by omega)
    exact finiteDimensional_cohomology_X₁ k X hS 0 1 rfl
  have hδ : cohomologyδBaseLinear k X hS 1 2 rfl = 0 :=
    LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  have h := eulerCharBelow_eq_add_of_cohomologyδ_eq_zero k hS 1 h₁ h₂ hδ
  rw [shortComplex_X₁, shortComplex_X₂, shortComplex_X₃,
    eulerCharBelow_pushforward_subscheme k I s, ← eulerCharBelow_congr k e,
    ← InvertibleSheaf.trivial_obj] at h
  rw [h]
  ring

/-- **The degree of `𝒪_X(-D)`.** On a scheme over a field `k` with finite-dimensional
`H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)`, the ideal sheaf `𝒪_X(-D)` of an effective Cartier divisor `D`
finite over `k` has Euler-characteristic degree `-dim_k Γ(D, 𝒪_D)`, the negative of the rank of
`D ⟶ Spec k`. -/
theorem IsEffectiveCartier.eulerDegree_toInvertibleSheaf (hI : I.IsEffectiveCartier)
    (s : Spec (.of k)) :
    hI.toInvertibleSheaf.eulerDegree k = -((I.subschemeι ≫ X ↘ Spec (.of k)).finrank s : ℤ) := by
  rw [InvertibleSheaf.eulerDegree_def, IsEffectiveCartier.toInvertibleSheaf_obj,
    eulerCharBelow_sheaf k I s]
  ring

end FiniteCohomology

end Finite

section Smooth

variable [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [ConnectedSpace X]

/-- **The degree of `𝒪_X(D)` on a smooth curve.** On a connected smooth proper curve over a
field `k`, the line bundle `𝒪_X(D)` of an effective Cartier divisor `D` has Euler-characteristic
degree `dim_k Γ(D, 𝒪_D)`, the rank of the finite morphism `D ⟶ Spec k`. The geometric
hypotheses supply the finiteness of `D` over `k`, the finiteness of `H⁰(X, 𝒪_X)` and
`H¹(X, 𝒪_X)`, and the additivity of the degree; no rational point or perfect-field assumption is
needed. -/
theorem IsEffectiveCartier.eulerDegree_inv_mk_toInvertibleSheaf (hI : I.IsEffectiveCartier)
    (s : Spec (.of k)) :
    LineBundleClass.eulerDegree k (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ =
      (I.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  -- Over a field every effective Cartier divisor is relative, hence finite over `k`.
  have : IsFinite (I.subschemeι ≫ X ↘ Spec (.of k)) :=
    ((isRelativeEffectiveCartier_iff_isEffectiveCartier I _).mpr hI).isFinite
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k))
  have : IsIntegral X := isIntegral_of_connected_of_isRegularLocalRing_stalk X
  have : ∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X)) :=
    fun x ↦ inferInstance
  have hdim : topologicalKrullDim X = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k))
  have := finiteDimensional_cohomology_one_trivial_of_isProper k hdim
  have := InvertibleSheaf.finiteDimensional_cohomology_zero k
    (fun x ↦ by exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim x).trans hdim.le)
    (InvertibleSheaf.trivial X)
  have h := LineBundleClass.eulerDegree_mul_of_smooth k (LineBundleClass.mk hI.toInvertibleSheaf)
    (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
  rw [mul_inv_cancel, LineBundleClass.eulerDegree_one, LineBundleClass.eulerDegree_mk,
    hI.eulerDegree_toInvertibleSheaf k I s] at h
  linarith

end Smooth

end

end AlgebraicGeometry.Scheme.IdealSheafData

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
public import TauCeti.AlgebraicGeometry.LineBundle.Basic

/-!
# The Euler characteristic of an ideal sheaf

Let `X` be a scheme over a field `k` and `I ⊆ 𝒪_X` an ideal sheaf whose closed subscheme
`D = V(I)` is finite over `k`, of rank `dim_k Γ(D, 𝒪_D)`. The exact sequence
`0 ⟶ I ⟶ 𝒪_X ⟶ ι_* 𝒪_D ⟶ 0` and the vanishing of higher cohomology on the affine Noetherian
scheme `D` give

  `χ(I) = χ(𝒪_X) - dim_k Γ(D, 𝒪_D)`

(`Scheme.IdealSheafData.eulerCharBelow_sheaf`), where `χ` is the degree-`2` truncation
`dim H⁰ - dim H¹` and `H⁰(X, 𝒪_X)`, `H¹(X, 𝒪_X)` are assumed finite-dimensional.

The rank is Mathlib's `Scheme.Hom.finrank` of the finite morphism `D ⟶ Spec k`, evaluated at a
point of `Spec k`; it is `dim_k Γ(D, 𝒪_D)` by
`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_of_field`.

## References

* R. Hartshorne, *Algebraic Geometry*: Lemma III.2.10 and Theorem III.3.5 (the cohomology of
  `𝒪_D`), and the proof of Theorem IV.1.3 (Riemann–Roch), where degrees are computed from the
  same kind of exact sequence.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open TauCeti.AlgebraicGeometry Scheme.Modules

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
  let S := ShortComplex.mk _ _ I.sheafι_toPushforwardSubscheme
  have hS : S.ShortExact := I.shortExact_toPushforwardSubscheme
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit ≅ SheafOfModules.unit X.ringCatSheaf :=
    TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf
  -- `H⁰` and `H¹` of `𝒪_X` are finite-dimensional.
  have h₂ (i : ℕ) (hi : i < 2) : FiniteDimensional k (Cohomology S.X₂ i) := by
    dsimp only [S]
    refine (finiteDimensional_cohomology_congr k e i).mp ?_
    rw [← InvertibleSheaf.trivial_obj]
    interval_cases i <;> infer_instance
  -- `H⁰` of `ι_* 𝒪_{V(I)}` is finite-dimensional and its `H¹` vanishes.
  let _ : I.subscheme.Over (Spec (.of k)) := ⟨I.subschemeι ≫ X ↘ Spec (.of k)⟩
  have : I.subschemeι.IsOver (Spec (.of k)) := ⟨rfl⟩
  let _ : IsFinite (I.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsFinite (I.subschemeι ≫ X ↘ Spec (.of k)))
  let M : I.subscheme.Modules := SheafOfModules.unit I.subscheme.ringCatSheaf
  have : FiniteDimensional k (Cohomology S.X₃ 0) := by
    let _ : Algebra k Γ(I.subscheme, ⊤) := (baseRingToGlobalSections k I.subscheme).toAlgebra
    have : Module.Finite k Γ(M, ⊤) :=
      -- The base-ring module structure on the global sections of `𝒪_{V(I)}` is the one given by
      -- the algebra structure, both being restriction of scalars along
      -- `baseRingToGlobalSections`.
      (I.subschemeι ≫ X ↘ Spec (.of k)).moduleFinite_appTop (algebraMap_eq k I)
    dsimp only [S]
    refine (Scheme.Hom.moduleFinite_cohomology_pushforward_iff I.subschemeι k M 0).mpr ?_
    exact Module.Finite.equiv (cohomologyZeroBaseLinearEquiv k I.subscheme M).symm
  have hvan : Subsingleton (Cohomology S.X₃ 1) := by
    have := subsingleton_cohomology_succ_of_isFinite (I.subscheme ↘ Spec (.of k)) M 0
    dsimp only [S]
    exact (cohomologyPushforwardIso I.subschemeι M 1).addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  -- `H¹(X, I)` sits between `H⁰(ι_* 𝒪_{V(I)})` and `H¹(X, 𝒪_X)`, so it is finite-dimensional.
  have h₁ (i : ℕ) (hi : i < 2) (hi' : 0 < i) :
      FiniteDimensional k (Cohomology S.X₁ i) := by
    obtain rfl : i = 1 := by omega
    have := h₂ 1 (by omega)
    exact finiteDimensional_cohomology_X₁ k X hS 0 1 rfl
  have hδ : cohomologyδBaseLinear k X hS 1 2 rfl = 0 :=
    LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  have h := eulerCharBelow_eq_add_of_cohomologyδ_eq_zero k hS 1 h₁ h₂ hδ
  -- The terms of the sequence are `I`, `𝒪_X` and `ι_* 𝒪_{V(I)}`.
  dsimp only [S] at h
  have h₀ : eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2 =
      eulerCharBelow k X (SheafOfModules.unit X.ringCatSheaf) 2 := by
    rw [InvertibleSheaf.trivial_obj]
    exact eulerCharBelow_congr k e 2
  have h₃ := Scheme.Hom.eulerCharBelow_pushforward_structureSheaf I.subschemeι k s 1
  -- `V(I)` lies over `k` through `X`, so its rank is that of `V(I) ⟶ X ⟶ Spec k`.
  rw [comp_over I.subschemeι (Spec (.of k))]
  linarith

end FiniteCohomology

end Finite

end

end AlgebraicGeometry.Scheme.IdealSheafData

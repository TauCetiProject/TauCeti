/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.LineBundle.Basic

/-!
# Cohomology over the field of constants

Let `X` be a scheme over a field `k` whose ring of global functions `κ = Γ(X, 𝒪_X)` is a field,
for instance a reduced connected scheme universally closed over `k`
(`AlgebraicGeometry.Scheme.isField_globalSections_of_isReduced_of_connectedSpace`), such as an
irreducible component of the special fibre of a proper model of a curve with its reduced
structure. Every cohomology group `Hⁱ(X, M)` is a vector space over `κ`
(`AlgebraicGeometry.Scheme.Modules.cohomologyModule`), and its `k`-structure is the restriction of
scalars along `k → κ`. Since `H⁰(X, 𝒪_X) = κ` is one-dimensional over `κ`, the tower law reads

`dim_k Hⁱ(X, M) = dim_k H⁰(X, 𝒪_X) · dim_κ Hⁱ(X, M)`.

In particular `dim_k H⁰(X, 𝒪_X) = [κ : k]` divides the `k`-dimension of every cohomology group
and every truncated Euler characteristic over `k`. For the components `Cᵢ` of the special fibre of
a regular model this is the weight `wᵢ = [κᵢ : k]` of the numerical type, and the genus of `Cᵢ`
over its constant field is `gᵢ = dim_{κᵢ} H¹(Cᵢ, 𝒪_{Cᵢ})`, with `dim_k H¹(Cᵢ, 𝒪_{Cᵢ}) = wᵢ gᵢ`.

Unlike `AlgebraicGeometry.Scheme.Modules.finrank_cohomology_eq_finrank_mul`, which starts from a
factorization of the structure morphism through `Spec κ` for a separately given field `κ`, the
statements here use the canonical action of the global functions on cohomology, so that no
structure morphism to `Spec Γ(X, 𝒪_X)` has to be chosen. No finiteness hypothesis is needed, since
both sides use Mathlib's `finrank`, which is zero on an infinite-dimensional space.

## Main results

* `AlgebraicGeometry.Scheme.Modules.finrank_globalSections_cohomology_zero_trivial_eq_one`:
  `H⁰(X, 𝒪_X)` has rank one over the global functions.
* `AlgebraicGeometry.Scheme.Modules.finrank_cohomology_eq_finrank_cohomology_zero_trivial_mul`:
  `dim_k Hⁱ(X, M) = dim_k H⁰(X, 𝒪_X) · dim_κ Hⁱ(X, M)` when `κ = Γ(X, 𝒪_X)` is a field.
* `AlgebraicGeometry.Scheme.Modules.finrank_cohomology_zero_trivial_dvd_finrank_cohomology` and
  `AlgebraicGeometry.Scheme.Modules.finrank_cohomology_zero_trivial_dvd_eulerCharBelow`: the
  resulting divisibilities.

## References

* [The Stacks Project, Section 55.8](https://stacks.math.columbia.edu/tag/0C6Y), for the weights
  `wᵢ = [κᵢ : k]` and genera `gᵢ = dim_{κᵢ} H¹(Cᵢ, 𝒪_{Cᵢ})` of the components of a numerical type.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open Module (finrank)

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- On a nonempty scheme, `H⁰(X, 𝒪_X)` is free of rank one over the ring `Γ(X, 𝒪_X)` of global
functions: it is identified with `Γ(X, 𝒪_X)` itself. -/
theorem finrank_globalSections_cohomology_zero_trivial_eq_one
    [Nonempty X] :
    finrank Γ(X, ⊤) (Cohomology (InvertibleSheaf.trivial X).obj 0) = 1 := by
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let e : (InvertibleSheaf.trivial X).obj ≅ M :=
    eqToIso (InvertibleSheaf.trivial_obj X) ≪≫ TauCeti.SheafOfModules.freePUnitIsoUnit _
  let f : Cohomology (InvertibleSheaf.trivial X).obj 0 ≃ₗ[Γ(X, ⊤)] Cohomology M 0 :=
    .ofLinearMap (cohomologyMapLinear e.hom 0) (cohomologyMapLinear e.inv 0)
      (by rw [← cohomologyMapLinear_comp, e.inv_hom_id, cohomologyMapLinear_id])
      (by rw [← cohomologyMapLinear_comp, e.hom_inv_id, cohomologyMapLinear_id])
  rw [f.finrank_eq, (cohomologyZeroLinearEquiv M).finrank_eq]
  -- The global sections of the structure sheaf, as a module over the global functions, are the
  -- global functions acting on themselves.
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  have : Nontrivial Γ(X, ⊤) := X.component_nontrivial ⊤
  exact Module.finrank_self Γ(X, ⊤)

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- **The tower law over the constant field.** If the ring `κ = Γ(X, 𝒪_X)` of global functions of
a scheme over a field `k` is a field, then `dim_k Hⁱ(X, M) = dim_k H⁰(X, 𝒪_X) · dim_κ Hⁱ(X, M)` for
every sheaf of modules `M` and every degree `i`. -/
theorem finrank_cohomology_eq_finrank_cohomology_zero_trivial_mul
    (hX : IsField Γ(X, ⊤)) (M : X.Modules) (i : ℕ) :
    finrank k (Cohomology M i) =
      finrank k (Cohomology (InvertibleSheaf.trivial X).obj 0) *
        finrank Γ(X, ⊤) (Cohomology M i) := by
  let _ : Algebra k Γ(X, ⊤) := (baseRingToGlobalSections k X).toAlgebra
  let _ := hX.toField
  have : Nonempty X := not_isEmpty_iff.mp fun _ ↦ not_subsingleton Γ(X, ⊤) inferInstance
  -- The base field acts on cohomology through the global functions.
  have (N : X.Modules) (j : ℕ) : IsScalarTower k Γ(X, ⊤) (Cohomology N j) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  rw [← Module.finrank_mul_finrank k Γ(X, ⊤) (Cohomology M i),
    ← Module.finrank_mul_finrank k Γ(X, ⊤) (Cohomology (InvertibleSheaf.trivial X).obj 0),
    finrank_globalSections_cohomology_zero_trivial_eq_one, mul_one]

/-- If the global functions of a scheme over a field `k` form a field, then `dim_k H⁰(X, 𝒪_X)`
divides the dimension over `k` of every cohomology group of every sheaf of modules. -/
theorem finrank_cohomology_zero_trivial_dvd_finrank_cohomology
    (hX : IsField Γ(X, ⊤)) (M : X.Modules) (i : ℕ) :
    finrank k (Cohomology (InvertibleSheaf.trivial X).obj 0) ∣ finrank k (Cohomology M i) :=
  ⟨_, finrank_cohomology_eq_finrank_cohomology_zero_trivial_mul k hX M i⟩

/-- If the global functions of a scheme over a field `k` form a field, then `dim_k H⁰(X, 𝒪_X)`
divides every truncated Euler characteristic over `k`. -/
theorem finrank_cohomology_zero_trivial_dvd_eulerCharBelow
    (hX : IsField Γ(X, ⊤)) (M : X.Modules) (n : ℕ) :
    (finrank k (Cohomology (InvertibleSheaf.trivial X).obj 0) : ℤ) ∣ eulerCharBelow k X M n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [eulerCharBelow_succ]
    exact ih.add ((Int.natCast_dvd_natCast.mpr
      (finrank_cohomology_zero_trivial_dvd_finrank_cohomology k hX M n)).mul_left _)

end AlgebraicGeometry.Scheme.Modules

end

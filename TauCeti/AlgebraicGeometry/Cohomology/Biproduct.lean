/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cohomology of finite direct sums of sheaves of modules

Sheaf cohomology is an additive functor of the coefficient sheaf, so it commutes with finite
direct sums. For a scheme `X` over a commutative ring `R` this file records that commutation as
an `R`-linear equivalence

`Hⁱ(X, ⨁ⱼ Mⱼ) ≃ₗ[R] ∀ j, Hⁱ(X, Mⱼ)`,

whose components are the maps induced by the projections of the biproduct. Mathlib's
`CategoryTheory.Functor.mapBiproduct` gives the additive version of this commutation; the point
here is linearity over the base ring, which the dimension counts below need. For a direct sum
of `|I|` copies of one sheaf `M` over a field it gives `dim Hⁱ(X, ⨁_{I} M) = |I| · dim Hⁱ(X, M)`,
and hence `χ(X, ⨁_{I} M) = |I| · χ(X, M)` for the truncated Euler characteristic
`Scheme.Modules.eulerCharBelow`. For `M = 𝒪_X` this computes, through
`TauCeti.SheafOfModules.biproductIsoFree`, the Euler characteristic of the free sheaf `𝒪_X^I`, a
trivial vector bundle. These counts hold with no finiteness hypothesis on
`Hⁱ(X, M)`, since `Module.finrank` takes the value `0` on both sides when `Hⁱ(X, M)` is
infinite-dimensional and `I` is nonempty.

## Main declarations

* `Scheme.Modules.cohomologyBiproductLinearEquiv`: `Hⁱ(X, ⨁ⱼ Mⱼ) ≃ₗ[R] ∀ j, Hⁱ(X, Mⱼ)`;
* `Scheme.Modules.finrank_cohomology_biproduct_const`:
  `dim Hⁱ(X, ⨁_{I} M) = |I| · dim Hⁱ(X, M)`;
* `Scheme.Modules.eulerCharBelow_biproduct_const` and `Scheme.Modules.eulerCharBelow_free`: the
  corresponding statements `χ(X, ⨁_{I} M) = |I| · χ(X, M)` and `χ(X, 𝒪_X^I) = |I| · χ(X, 𝒪_X)`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Scheme.Modules
open Module (finrank)

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]

variable {J : Type*} [Fintype J] (F : J → X.Modules) [HasBiproduct F]

/-- **Cohomology commutes with finite direct sums.** For a finite family of sheaves of modules
`Mⱼ` on a scheme over a commutative ring `R`, the maps induced by the projections of the
biproduct give an `R`-linear equivalence `Hⁱ(X, ⨁ⱼ Mⱼ) ≃ₗ[R] ∀ j, Hⁱ(X, Mⱼ)`. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyBiproductLinearEquiv (i : ℕ) :
    Cohomology (⨁ F) i ≃ₗ[R] ∀ j, Cohomology (F j) i := by
  classical
  exact LinearEquiv.ofLinearMap
    (LinearMap.pi fun j ↦ cohomologyMapBaseLinear R X (biproduct.π F j) i)
    (∑ j, (cohomologyMapBaseLinear R X (biproduct.ι F j) i).comp (LinearMap.proj j))
    (LinearMap.ext fun v ↦ funext fun j ↦ by
      simp [-cohomologyMapBaseLinear_apply, map_sum, ← LinearMap.comp_apply,
        ← cohomologyMapBaseLinear_comp, biproduct.ι_π, apply_dite (cohomologyMapBaseLinear R X · i),
        DFunLike.dite_apply])
    (LinearMap.ext fun x ↦ by
      simp [-cohomologyMapBaseLinear_apply, ← LinearMap.comp_apply,
        ← cohomologyMapBaseLinear_comp, ← LinearMap.sum_apply, ← cohomologyMapBaseLinear_sum])

/-- The `j`-th component of `cohomologyBiproductLinearEquiv` is the map on cohomology induced by
the `j`-th projection of the biproduct. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyBiproductLinearEquiv_apply (i : ℕ)
    (x : Cohomology (⨁ F) i) (j : J) :
    cohomologyBiproductLinearEquiv R F i x j = cohomologyMapBaseLinear R X (biproduct.π F j) i x :=
  (rfl)

/-- The inverse of `cohomologyBiproductLinearEquiv` sums the maps on cohomology induced by the
inclusions of the summands. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyBiproductLinearEquiv_symm_apply
    (i : ℕ) (v : ∀ j, Cohomology (F j) i) :
    (cohomologyBiproductLinearEquiv R F i).symm v =
      ∑ j, cohomologyMapBaseLinear R X (biproduct.ι F j) i (v j) := by
  classical
  simp [cohomologyBiproductLinearEquiv, LinearEquiv.ofLinearMap]

/-- **Dimension of the cohomology of a finite direct sum of copies of a sheaf.** Over a field
`k`, `dim Hⁱ(X, ⨁_{I} M) = |I| · dim Hⁱ(X, M)` for every finite type `I`. No finiteness of
`Hⁱ(X, M)` is needed: when it is infinite-dimensional and `I` is nonempty both sides are `0`.
Applied to `M = 𝒪_X`, this computes the cohomology of the free sheaf `𝒪_X^I`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.finrank_cohomology_biproduct_const (k : Type u)
    [Field k] [X.Over (Spec (.of k))] (M : X.Modules) (I : Type u) [Fintype I]
    [HasBiproduct fun _ : I ↦ M] (i : ℕ) :
    finrank k (Cohomology (⨁ fun _ : I ↦ M) i) = Fintype.card I * finrank k (Cohomology M i) := by
  rw [(cohomologyBiproductLinearEquiv k (fun _ : I ↦ M) i).finrank_eq, Module.finrank, rank_fun,
    Cardinal.toNat_mul, Cardinal.toNat_natCast, Module.finrank]

/-- The truncated Euler characteristic of a finite direct sum of copies of a sheaf:
`χ(X, ⨁_{I} M) = |I| · χ(X, M)`, with no finiteness hypothesis. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_biproduct_const (k : Type u)
    [Field k] [X.Over (Spec (.of k))] (M : X.Modules) (I : Type u) [Fintype I]
    [HasBiproduct fun _ : I ↦ M] (n : ℕ) :
    eulerCharBelow k X (⨁ fun _ : I ↦ M) n = Fintype.card I * eulerCharBelow k X M n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [eulerCharBelow_succ, eulerCharBelow_succ, ih, finrank_cohomology_biproduct_const]
    push_cast
    ring

variable (X) in
/-- The truncated Euler characteristic of the free sheaf on a finite type:
`χ(X, 𝒪_X^I) = |I| · χ(X, 𝒪_X)`, with no finiteness hypothesis. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_free (k : Type u) [Field k]
    [X.Over (Spec (.of k))] (I : Type u) [Fintype I] (n : ℕ) :
    eulerCharBelow k X (SheafOfModules.free (R := X.ringCatSheaf) I) n =
      Fintype.card I * eulerCharBelow k X (SheafOfModules.unit X.ringCatSheaf) n := by
  have : HasBiproduct (C := X.Modules) fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf :=
    HasBiproduct.of_hasCoproduct _
  rw [← eulerCharBelow_congr k (SheafOfModules.biproductIsoFree (R := X.sheaf) I) n]
  exact eulerCharBelow_biproduct_const k (SheafOfModules.unit X.ringCatSheaf) I n

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti

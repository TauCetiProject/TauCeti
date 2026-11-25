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
public import Mathlib.RingTheory.Finiteness.Prod
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
* `Scheme.Modules.cohomologyBiprodLinearEquiv`: `Hⁱ(X, M ⊞ N) ≃ₗ[R] Hⁱ(X, M) × Hⁱ(X, N)`, with
  `Scheme.Modules.finrank_cohomology_biprod` and `Scheme.Modules.eulerCharBelow_biprod` computing
  dimensions and truncated Euler characteristics when the cohomology is finite-dimensional;
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
  -- Mathlib's AddCommGrpCat biproduct-to-Pi isomorphism requires an index in Type.
  -- Our index may inhabit any universe, so verify the component maps directly.
  exact LinearEquiv.ofLinearMap
    (LinearMap.pi fun j ↦ cohomologyMapBaseLinear R X (biproduct.π F j) i)
    (∑ j, (cohomologyMapBaseLinear R X (biproduct.ι F j) i).comp (LinearMap.proj j))
    (LinearMap.ext fun v ↦ funext fun j ↦ by
      -- A projection of the inclusion sum keeps exactly its matching summand.
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply,
        LinearMap.proj_apply, LinearMap.id_apply]
      rw [map_sum, Finset.sum_eq_single j]
      · rw [← LinearMap.comp_apply, ← cohomologyMapBaseLinear_comp,
          biproduct.ι_π_self, cohomologyMapBaseLinear_id, LinearMap.id_apply]
      · intro k _ hkj
        rw [← LinearMap.comp_apply, ← cohomologyMapBaseLinear_comp,
          biproduct.ι_π_ne F hkj, cohomologyMapBaseLinear_zero, LinearMap.zero_apply]
      · simp)
    (LinearMap.ext fun x ↦ by
      -- The sum of inclusion/projection composites is the identity of the biproduct.
      have htotal : (∑ j, (cohomologyMapBaseLinear R X (biproduct.ι F j) i).comp
          (cohomologyMapBaseLinear R X (biproduct.π F j) i)) = LinearMap.id := by
        simp only [← cohomologyMapBaseLinear_comp, ← cohomologyMapBaseLinear_sum,
          biproduct.total, cohomologyMapBaseLinear_id]
      simpa only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply,
        LinearMap.proj_apply, LinearMap.id_apply] using LinearMap.congr_fun htotal x)

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
  simp only [cohomologyBiproductLinearEquiv, LinearEquiv.symm_ofLinearMap,
    LinearEquiv.coe_ofLinearMap, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

/-- **Dimension of the cohomology of a finite direct sum of copies of a sheaf.** Over a field
`k`, `dim Hⁱ(X, ⨁_{I} M) = |I| · dim Hⁱ(X, M)` for every finite type `I`. No finiteness of
`Hⁱ(X, M)` is needed: when it is infinite-dimensional and `I` is nonempty both sides are `0`.
Applied to `M = 𝒪_X`, this computes the cohomology of the free sheaf `𝒪_X^I`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.finrank_cohomology_biproduct_const (k : Type u)
    [Field k] [X.Over (Spec (.of k))] (M : X.Modules) (I : Type*) [Fintype I]
    [HasBiproduct fun _ : I ↦ M] (i : ℕ) :
    finrank k (Cohomology (⨁ fun _ : I ↦ M) i) = Fintype.card I * finrank k (Cohomology M i) := by
  rw [(cohomologyBiproductLinearEquiv k (fun _ : I ↦ M) i).finrank_eq, Module.finrank,
    rank_fun_eq_lift_mul,
    Cardinal.toNat_mul, Cardinal.toNat_natCast, Cardinal.toNat_lift, Module.finrank]

/-- The truncated Euler characteristic of a finite direct sum of copies of a sheaf:
`χ(X, ⨁_{I} M) = |I| · χ(X, M)`, with no finiteness hypothesis. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_biproduct_const (k : Type u)
    [Field k] [X.Over (Spec (.of k))] (M : X.Modules) (I : Type*) [Fintype I]
    [HasBiproduct fun _ : I ↦ M] (n : ℕ) :
    eulerCharBelow k X (⨁ fun _ : I ↦ M) n = Fintype.card I * eulerCharBelow k X M n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [eulerCharBelow_succ, eulerCharBelow_succ, ih, finrank_cohomology_biproduct_const]
    push_cast
    ring

section Binary

variable (k : Type u) [Field k] [X.Over (Spec (.of k))] (M N : X.Modules)

/-- **Cohomology commutes with binary direct sums.** The maps induced by the projections of
`M ⊞ N` give an `R`-linear equivalence `Hⁱ(X, M ⊞ N) ≃ₗ[R] Hⁱ(X, M) × Hⁱ(X, N)`. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyBiprodLinearEquiv (i : ℕ) :
    Cohomology (M ⊞ N) i ≃ₗ[R] Cohomology M i × Cohomology N i :=
  LinearEquiv.ofLinearMap
    ((cohomologyMapBaseLinear R X biprod.fst i).prod (cohomologyMapBaseLinear R X biprod.snd i))
    ((cohomologyMapBaseLinear R X biprod.inl i).coprod (cohomologyMapBaseLinear R X biprod.inr i))
    (by
      simp only [LinearMap.prod_comp, LinearMap.comp_coprod, ← cohomologyMapBaseLinear_comp,
        biprod.inl_fst, biprod.inr_fst, biprod.inl_snd, biprod.inr_snd, cohomologyMapBaseLinear_id,
        cohomologyMapBaseLinear_zero, LinearMap.coprod_zero_left, LinearMap.coprod_zero_right,
        LinearMap.id_comp, LinearMap.pair_fst_snd])
    (by
      simp only [LinearMap.coprod_comp_prod, ← cohomologyMapBaseLinear_comp,
        ← cohomologyMapBaseLinear_add, biprod.total, cohomologyMapBaseLinear_id])

/-- The components of `cohomologyBiprodLinearEquiv` are the maps on cohomology induced by the
projections of `M ⊞ N`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyBiprodLinearEquiv_apply (i : ℕ)
    (x : Cohomology (M ⊞ N) i) :
    cohomologyBiprodLinearEquiv R M N i x =
      (cohomologyMapBaseLinear R X biprod.fst i x, cohomologyMapBaseLinear R X biprod.snd i x) :=
  (rfl)

/-- The inverse of `cohomologyBiprodLinearEquiv` adds the maps on cohomology induced by the
inclusions of the summands. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyBiprodLinearEquiv_symm_apply (i : ℕ)
    (v : Cohomology M i × Cohomology N i) :
    (cohomologyBiprodLinearEquiv R M N i).symm v =
      cohomologyMapBaseLinear R X biprod.inl i v.1 + cohomologyMapBaseLinear R X biprod.inr i v.2 :=
  (rfl)

/-- `Hⁱ(X, M ⊞ N)` is a finitely generated `R`-module when `Hⁱ(X, M)` and `Hⁱ(X, N)` are. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.finite_cohomology_biprod (i : ℕ)
    [Module.Finite R (Cohomology M i)] [Module.Finite R (Cohomology N i)] :
    Module.Finite R (Cohomology (M ⊞ N) i) :=
  Module.Finite.equiv (cohomologyBiprodLinearEquiv R M N i).symm

/-- **Dimension of the cohomology of a binary direct sum.** Over a field `k`, if `Hⁱ(X, M)` and
`Hⁱ(X, N)` are finite-dimensional then `dim Hⁱ(X, M ⊞ N) = dim Hⁱ(X, M) + dim Hⁱ(X, N)`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.finrank_cohomology_biprod (i : ℕ)
    [FiniteDimensional k (Cohomology M i)] [FiniteDimensional k (Cohomology N i)] :
    finrank k (Cohomology (M ⊞ N) i) = finrank k (Cohomology M i) + finrank k (Cohomology N i) :=
  ((cohomologyBiprodLinearEquiv k M N i).finrank_eq).trans Module.finrank_prod

/-- **Euler characteristic of a binary direct sum.** If `Hⁱ(X, M)` and `Hⁱ(X, N)` are
finite-dimensional for `i < n`, then `χ_{<n}(X, M ⊞ N) = χ_{<n}(X, M) + χ_{<n}(X, N)`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_biprod (n : ℕ)
    (hM : ∀ i < n, FiniteDimensional k (Cohomology M i))
    (hN : ∀ i < n, FiniteDimensional k (Cohomology N i)) :
    eulerCharBelow k X (M ⊞ N) n = eulerCharBelow k X M n + eulerCharBelow k X N n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := hM n n.lt_succ_self
    have := hN n n.lt_succ_self
    rw [eulerCharBelow_succ, eulerCharBelow_succ, eulerCharBelow_succ,
      ih (fun i hi ↦ hM i (hi.trans n.lt_succ_self)) (fun i hi ↦ hN i (hi.trans n.lt_succ_self)),
      finrank_cohomology_biprod]
    push_cast
    ring

end Binary

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

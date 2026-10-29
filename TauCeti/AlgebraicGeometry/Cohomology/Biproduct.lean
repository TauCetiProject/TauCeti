/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
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
of `|I|` copies of one sheaf `M` over a field it gives `dim Hⁱ(X, ∐_{I} M) = |I| · dim Hⁱ(X, M)`,
and hence `χ(X, ∐_{I} M) = |I| · χ(X, M)` for the truncated Euler characteristic
`Scheme.Modules.eulerCharBelow`. For `M = 𝒪_X` this computes the Euler characteristic of the free
sheaf `𝒪_X^I`, a trivial vector bundle. These counts hold with no finiteness hypothesis on
`Hⁱ(X, M)`, since `Module.finrank` takes the value `0` on both sides when `Hⁱ(X, M)` is
infinite-dimensional and `I` is nonempty.

## Main declarations

* `Scheme.Modules.cohomologyBiproductLinearEquiv`: `Hⁱ(X, ⨁ⱼ Mⱼ) ≃ₗ[R] ∀ j, Hⁱ(X, Mⱼ)`;
* `Scheme.Modules.finrank_cohomology_sigma_const`: `dim Hⁱ(X, ∐_{I} M) = |I| · dim Hⁱ(X, M)`;
* `Scheme.Modules.eulerCharBelow_sigma_const` and `Scheme.Modules.eulerCharBelow_free`: the
  corresponding statements `χ(X, ∐_{I} M) = |I| · χ(X, M)` and `χ(X, 𝒪_X^I) = |I| · χ(X, 𝒪_X)`.
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

/-- The induced map on cohomology of a finite sum of morphisms of coefficient sheaves is the sum
of the induced maps. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapBaseLinear_sum {M N : X.Modules}
    {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) (i : ℕ) :
    cohomologyMapBaseLinear R X (∑ j ∈ s, f j) i = ∑ j ∈ s, cohomologyMapBaseLinear R X (f j) i :=
  map_sum (AddMonoidHom.mk' (cohomologyMapBaseLinear R X · i)
    fun g h ↦ cohomologyMapBaseLinear_add R X g h i) f s

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
      rw [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
        Finset.sum_eq_single j (fun l _ hl ↦ by
          rw [LinearMap.comp_apply, ← LinearMap.comp_apply (cohomologyMapBaseLinear R X _ i),
            ← cohomologyMapBaseLinear_comp, biproduct.ι_π_ne F hl, cohomologyMapBaseLinear_zero,
            LinearMap.zero_apply]) (by simp),
        LinearMap.comp_apply, ← LinearMap.comp_apply (cohomologyMapBaseLinear R X _ i),
        ← cohomologyMapBaseLinear_comp, biproduct.ι_π_self, cohomologyMapBaseLinear_id]
      rfl)
    (LinearMap.ext fun x ↦ by
      rw [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.id_apply]
      calc ∑ j, ((cohomologyMapBaseLinear R X (biproduct.ι F j) i).comp (LinearMap.proj j))
              ((LinearMap.pi fun j ↦ cohomologyMapBaseLinear R X (biproduct.π F j) i) x)
          = ∑ j, cohomologyMapBaseLinear R X (biproduct.π F j ≫ biproduct.ι F j) i x :=
            Finset.sum_congr rfl fun j _ ↦ by rw [cohomologyMapBaseLinear_comp]; rfl
        _ = x := by
          rw [← LinearMap.sum_apply, ← cohomologyMapBaseLinear_sum, biproduct.total,
            cohomologyMapBaseLinear_id, LinearMap.id_apply])

/-- The `j`-th component of `cohomologyBiproductLinearEquiv` is the map on cohomology induced by
the `j`-th projection of the biproduct. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyBiproductLinearEquiv_apply (i : ℕ)
    (x : Cohomology (⨁ F) i) (j : J) :
    cohomologyBiproductLinearEquiv R F i x j = cohomologyMapBaseLinear R X (biproduct.π F j) i x :=
  (rfl)

/-- The inverse of `cohomologyBiproductLinearEquiv` sums the maps on cohomology induced by the
inclusions of the summands. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyBiproductLinearEquiv_symm_apply
    (i : ℕ) (v : ∀ j, Cohomology (F j) i) :
    (cohomologyBiproductLinearEquiv R F i).symm v =
      ∑ j, cohomologyMapBaseLinear R X (biproduct.ι F j) i (v j) := by
  classical
  simp [cohomologyBiproductLinearEquiv, LinearEquiv.ofLinearMap]

/-- **Dimension of the cohomology of a finite direct sum of copies of a sheaf.** Over a field
`k`, `dim Hⁱ(X, ∐_{I} M) = |I| · dim Hⁱ(X, M)` for every finite type `I`. No finiteness of
`Hⁱ(X, M)` is needed: when it is infinite-dimensional and `I` is nonempty both sides are `0`.
Applied to `M = 𝒪_X`, this computes the cohomology of the free sheaf `𝒪_X^I`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.finrank_cohomology_sigma_const (k : Type u)
    [Field k] [X.Over (Spec (.of k))] (M : X.Modules) (I : Type u) [Fintype I] (i : ℕ) :
    finrank k (Cohomology (∐ fun _ : I ↦ M) i) = Fintype.card I * finrank k (Cohomology M i) := by
  have : HasBiproduct fun _ : I ↦ M := HasBiproduct.of_hasCoproduct _
  rw [← (cohomologyBaseLinearEquivOfIso k (biproduct.isoCoproduct fun _ : I ↦ M) i).finrank_eq,
    (cohomologyBiproductLinearEquiv k (fun _ : I ↦ M) i).finrank_eq, Module.finrank, rank_fun,
    Cardinal.toNat_mul, Cardinal.toNat_natCast, Module.finrank]

/-- The truncated Euler characteristic of a finite direct sum of copies of a sheaf:
`χ(X, ∐_{I} M) = |I| · χ(X, M)`, with no finiteness hypothesis. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_sigma_const (k : Type u) [Field k]
    [X.Over (Spec (.of k))] (M : X.Modules) (I : Type u) [Fintype I] (n : ℕ) :
    eulerCharBelow k X (∐ fun _ : I ↦ M) n = Fintype.card I * eulerCharBelow k X M n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [eulerCharBelow_succ, eulerCharBelow_succ, ih, finrank_cohomology_sigma_const]
    push_cast
    ring

variable (X) in
/-- The truncated Euler characteristic of the free sheaf on a finite type:
`χ(X, 𝒪_X^I) = |I| · χ(X, 𝒪_X)`, with no finiteness hypothesis. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_free (k : Type u) [Field k]
    [X.Over (Spec (.of k))] (I : Type u) [Fintype I] (n : ℕ) :
    eulerCharBelow k X (SheafOfModules.free (R := X.ringCatSheaf) I) n =
      Fintype.card I * eulerCharBelow k X (SheafOfModules.unit X.ringCatSheaf) n := by
  let e : (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) ≅
      ∐ fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf :=
    (SheafOfModules.isColimitFreeCofan I).coconePointUniqueUpToIso (colimit.isColimit _)
  rw [eulerCharBelow_congr k e n]
  exact eulerCharBelow_sigma_const k (SheafOfModules.unit X.ringCatSheaf) I n

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti

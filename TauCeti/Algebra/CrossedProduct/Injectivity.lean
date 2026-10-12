/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.TensorProduct
public import TauCeti.Algebra.BrauerGroup.Splitting
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Equal crossed-product classes come from cohomologous cocycles

For a finite Galois extension `L/K`, the Brauer class of the crossed product `(L, Gal(L/K), c)`
determines the cocycle `c` up to coboundaries: if two cocycles `z` and `w` have the same Brauer
class, then they are cohomologous. Together with
`TauCeti.BrauerGroup.crossedProductClass_eq_of_cohomologous` this says that the crossed-product
construction is injective on cocycles modulo coboundaries, which is the injectivity half of the
comparison between `H²(Gal(L/K), Lˣ)` and the relative Brauer group of `L/K`.

Since `crossedProductClass` is multiplicative (`TauCeti.BrauerGroup.crossedProductClass_mul`), it
suffices to show that a cocycle `c` whose crossed product is split is a coboundary. The argument is
a dimension count. A split crossed product `A = (L, Gal(L/K), c)` of dimension `[L : K]²` is a
matrix algebra `M_n(K)` with `n = [L : K]`, so it acts on a `K`-vector space `V` of dimension
`[L : K]`. Restricted to `L ⊆ A`, this makes `V` a one-dimensional `L`-vector space, so
`V = L · v` for any `v ≠ 0`. Each `u_σ` acts `σ`-semilinearly, hence `u_σ · v = b(σ) · v` for a
unique `b(σ) ∈ Lˣ`, and expanding `u_σ · u_τ · v = c(σ, τ) · u_{στ} · v` gives
`c(σ, τ) = σ(b(τ)) · b(στ)⁻¹ · b(σ)`.

## Main results

* `TauCeti.TwoCocycle.one_cohomologous_of_algHom_end`: a cocycle whose crossed product acts on a
  `K`-vector space of dimension `[L : K]` is a coboundary.
* `TauCeti.BrauerGroup.crossedProductClass_one`: the trivial cocycle presents the identity class.
* `TauCeti.BrauerGroup.crossedProductClass_eq_one_iff`: a crossed product is split exactly when
  its cocycle is a coboundary.
* `TauCeti.BrauerGroup.crossedProductClass_eq_iff`,
  `TauCeti.BrauerGroup.cohomologous_of_crossedProductClass_eq`: two cocycles have the same Brauer
  class exactly when they are cohomologous.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X, §5.
-/

public section

universe u v

namespace TauCeti

namespace TwoCocycle

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L]
  {V : Type*} [AddCommGroup V] [Module K V]

open CrossedProduct in
/-- **A crossed product with a module of dimension `[L : K]` has a trivial cocycle.** If the
crossed product of `c` acts `K`-linearly on a `K`-vector space `V` with `dim_K V = [L : K]`, then
`c` is a coboundary: `c(σ, τ) = σ(b(τ)) · b(στ)⁻¹ · b(σ)` for some `b : Aut_K(L) → Lˣ`. No
Galois hypothesis is needed. -/
theorem one_cohomologous_of_algHom_end (c : TwoCocycle K L)
    (ρ : CrossedProduct c →ₐ[K] Module.End K V)
    (hV : Module.finrank K V = Module.finrank K L) : (1 : TwoCocycle K L).Cohomologous c := by
  classical
  have hpos : 0 < Module.finrank K V := hV ▸ Module.finrank_pos
  have : FiniteDimensional K V := Module.finite_of_finrank_pos hpos
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  -- `ψ` is the action of `L ⊆ CrossedProduct c` on `V`, and `φ x = ι(x) · v` the orbit map of `v`
  let ψ : L →ₐ[K] Module.End K V := ρ.comp (inc c)
  let φ : L →ₗ[K] V := LinearMap.applyₗ v ∘ₗ ψ.toLinearMap
  have hφ (x : L) : φ x = ρ (inc c x) v := by simp [φ, ψ]
  -- the action of a product, and of `ι(x)` in the coordinate `φ`
  have hρ (a b : CrossedProduct c) (w : V) : ρ (a * b) w = ρ a (ρ b w) := by simp
  have hψφ (x y : L) : ρ (inc c x) (φ y) = φ (x * y) := by simp [hφ]
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun x hx ↦ by_contra fun hx0 ↦ hv ?_
    simpa [hx, hx0, hφ] using (hψφ x⁻¹ x).symm
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hV.symm).1 hinj
  -- `u_σ · v = ι(b₀(σ)) · v`, and `u_σ` acts `σ`-semilinearly
  choose b₀ hb₀ using fun σ : L ≃ₐ[K] L ↦ hsurj (ρ (basis c σ) v)
  have hu (σ : L ≃ₐ[K] L) (x : L) : ρ (basis c σ) (φ x) = φ (σ x * b₀ σ) := by
    rw [hφ x, ← hρ, basis_mul_inc, hρ, ← hb₀, hψφ]
  have hb₀ne (σ : L ≃ₐ[K] L) : b₀ σ ≠ 0 := by
    intro h0
    -- `u_{σ⁻¹} · u_σ · v = 0`, but `u_{σ⁻¹} · u_σ` is a unit of `L`
    have h : ρ (basis c σ⁻¹ * basis c σ) v = 0 := by
      rw [hρ, ← hb₀, h0, map_zero, map_zero]
    rw [basis_mul_basis, inv_mul_cancel, basis_one, ← map_mul, ← hφ, ← map_zero φ] at h
    exact mul_ne_zero (c.toFun σ⁻¹ σ).ne_zero (c.toFun 1 1).ne_zero (hinj h)
  let b : (L ≃ₐ[K] L) → Lˣ := fun σ ↦ Units.mk0 (b₀ σ) (hb₀ne σ)
  refine cohomologous_iff.2 ⟨b, fun σ τ ↦ ?_⟩
  -- expand `u_σ · u_τ · v = c(σ, τ) · u_{στ} · v` in the coordinate `φ`
  have key : c.toFun σ τ * b₀ (σ * τ) = σ (b₀ τ) * b₀ σ := by
    refine hinj ?_
    rw [← hψφ, hb₀, ← hρ, ← basis_mul_basis, hρ, ← hb₀, hu]
  simp only [toFun_one, Units.val_one, one_mul, Units.val_inv_eq_inv_val, Units.val_mk0, b]
  rw [mul_right_comm, ← key, mul_inv_cancel_right₀ (hb₀ne _)]

end TwoCocycle

namespace BrauerGroup

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]

/-- **The trivial cocycle presents the identity Brauer class**: the crossed product of the
trivial cocycle of a finite Galois extension is split. -/
@[simp]
theorem crossedProductClass_one : crossedProductClass (1 : TwoCocycle K L) = 1 := by
  rw [← mul_eq_left (a := crossedProductClass (1 : TwoCocycle K L)), ← crossedProductClass_mul,
    mul_one]

/-- **A crossed product is split exactly when its cocycle is a coboundary.** -/
theorem crossedProductClass_eq_one_iff {c : TwoCocycle K L} :
    crossedProductClass c = 1 ↔ (1 : TwoCocycle K L).Cohomologous c := by
  refine ⟨fun h ↦ ?_, fun h ↦ (crossedProductClass_eq_of_cohomologous h).symm.trans
    crossedProductClass_one⟩
  rw [crossedProductClass_def] at h
  obtain ⟨n, ⟨e⟩⟩ := (Algebra.isSplittingField_self_iff K (CrossedProduct c)).1
    ((BrauerGroup.mk_eq_one_iff_isSplittingField K (CrossedProduct c)).1 h)
  refine TwoCocycle.one_cohomologous_of_algHom_end c
    ((Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toAlgHom.comp e.toAlgHom) ?_
  -- `n ^ 2 = [L : K] ^ 2` by comparing dimensions across `e`
  have hdim := e.toLinearEquiv.finrank_eq
  rw [CrossedProduct.finrank_eq_finrank_sq, Module.finrank_matrix, Fintype.card_fin,
    Module.finrank_self, mul_one, ← sq] at hdim
  rw [Module.finrank_fin_fun]
  exact (Nat.pow_left_injective two_ne_zero hdim).symm

/-- **Equal crossed-product classes come from cohomologous cocycles, and conversely.** -/
theorem crossedProductClass_eq_iff {z w : TwoCocycle K L} :
    crossedProductClass z = crossedProductClass w ↔ z.Cohomologous w := by
  have hw : crossedProductClass w = crossedProductClass (w / z) * crossedProductClass z := by
    rw [← crossedProductClass_mul, div_mul_cancel]
  rw [hw, eq_comm, mul_eq_right, crossedProductClass_eq_one_iff,
    ← TwoCocycle.cohomologous_iff_one_cohomologous_div]

/-- **Injectivity of the crossed-product construction.** Two cocycles of a finite Galois
extension whose crossed products have the same Brauer class are cohomologous. The converse is
`TauCeti.BrauerGroup.crossedProductClass_eq_of_cohomologous`. -/
theorem cohomologous_of_crossedProductClass_eq {z w : TwoCocycle K L}
    (h : crossedProductClass z = crossedProductClass w) : z.Cohomologous w :=
  crossedProductClass_eq_iff.1 h

end BrauerGroup

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Uniformization
public import Mathlib.FieldTheory.Galois.Basic
import TauCeti.Algebra.Algebra.Equiv
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Galois equivariance of the Tate uniformisation

Let `K` be a complete non-archimedean normed field and `q ∈ Kˣ` with `‖q‖ < 1`, so that the Tate
curve `E_q` is an elliptic curve over `K`. For a complete normed extension `L` of `K`, the Tate
uniformisation over `L`

```text
tateUniformizationBaseChange L q hq : Lˣ / q^ℤ → E_q(L)
```

commutes with every continuous `K`-algebra map, which acts on parameters through
`tateParameterMap`. Every `K`-automorphism of an algebraic extension preserves the spectral norm,
which is the norm of `L`, so it is continuous and the uniformisation is **Galois-equivariant**
(`map_algEquiv_tateUniformizationBaseChange`).

On the parameter side, for a finite Galois extension `L/K` and `q` of infinite order, a class in
`Lˣ / q^ℤ` is fixed by `Gal(L/K)` exactly when it comes from `Kˣ / q^ℤ`
(`mem_range_tateParameterBaseChange_iff`). Indeed if `σ u = u qⁿ`, then `σᵏ u = u q^{kn}`, and
`σ` has finite order. This is the parameter half of Galois descent for the uniformisation: by
equivariance, a point `tateUniformizationBaseChange L q hq x` fixed by `Gal(L/K)` has a fixed
parameter `x`, and hence one defined over `K`, as soon as the uniformisation is injective.

## Main results

* `TauCeti.map_algEquiv_tateUniformizationBaseChange`: Galois equivariance.
* `TauCeti.mem_range_tateParameterBaseChange_iff`: the Galois-fixed parameters are those
  defined over `K`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

namespace TauCeti

open WeierstrassCurve WeierstrassCurve.Affine

/-! ### Galois-fixed parameters -/

section Fixed

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The Galois-fixed Tate parameters are those defined over the ground field.** For a finite
Galois extension `L/K` and `q ∈ Kˣ` of infinite order, a class in `Lˣ / q^ℤ` is fixed by every
`K`-automorphism of `L` exactly when it is the image of a class in `Kˣ / q^ℤ`. -/
theorem mem_range_tateParameterBaseChange_iff [FiniteDimensional K L] [IsGalois K L] {q : Kˣ}
    (hq : ¬ IsOfFinOrder q)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    x ∈ (tateParameterBaseChange (algebraMap K L) q).range ↔
      ∀ σ : L ≃ₐ[K] L, tateParameterMap q (σ : L →ₐ[K] L) x = x := by
  refine ⟨fun ⟨y, hy⟩ σ ↦ hy ▸ tateParameterMap_tateParameterBaseChange q _ y, fun hx ↦ ?_⟩
  induction x using QuotientGroup.induction_on with
  | H u =>
  -- every `σ` moves `u` by a power of `q`, and that power vanishes since `σ` has finite order
  have hfix (σ : L ≃ₐ[K] L) : σ (u : L) = u := by
    have h := hx σ
    rw [tateParameterMap_mk, eq_comm, QuotientGroup.eq] at h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
    have hσ : σ (u : L) = u * algebraMap K L ↑(q ^ n) := by
      simpa using congrArg Units.val (eq_mul_of_inv_mul_eq hn.symm)
    -- `σ` has finite order, so the factor `qⁿ` is a root of unity, and hence `n = 0`
    have hk : (q ^ n) ^ orderOf σ = 1 := by
      refine Units.val_injective <| (algebraMap K L).injective ?_
      simpa [u.ne_zero] using σ.pow_apply_eq_mul_pow (σ.commutes _) hσ (orderOf σ)
    have hn : n = 0 := by
      by_contra hn
      refine hq (isOfFinOrder_iff_zpow_eq_one.mpr ⟨n * orderOf σ, ?_, ?_⟩)
      · exact mul_ne_zero hn (by exact_mod_cast (orderOf_pos σ).ne')
      · rwa [zpow_mul, zpow_natCast]
    simpa [hn] using hσ
  obtain ⟨b, hb⟩ := IntermediateField.mem_bot.mp
    ((InfiniteGalois.mem_bot_iff_fixed (u : L)).mpr hfix)
  have hb₀ : b ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by simpa using hb.symm)
  refine ⟨(Units.mk0 b hb₀ : Kˣ), ?_⟩
  rw [tateParameterBaseChange_mk]
  congr 1
  ext
  simpa using hb

end Fixed

/-! ### Galois equivariance of the uniformisation -/

variable {K L : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [CompleteSpace L] [IsUltrametricDist L] [DecidableEq L]

/-- **The Tate uniformisation is Galois-equivariant.** For an algebraic extension `L/K`, every
`K`-automorphism `σ` of `L` is an isometry, and applying `σ` to the image of a parameter `x`
gives the image of `σ x`. -/
theorem map_algEquiv_tateUniformizationBaseChange [Algebra.IsAlgebraic K L] (q : Kˣ)
    (hq : ‖(q : K)‖ < 1) (σ : L ≃ₐ[K] L)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    Point.map (σ : L →ₐ[K] L) (tateUniformizationBaseChange L q hq x) =
      tateUniformizationBaseChange L q hq (tateParameterMap q (σ : L →ₐ[K] L) x) := by
  -- `q` has norm strictly between `0` and `1`, so the norm of `K` is nontrivial
  let := NontriviallyNormedField.ofNormNeOne ⟨(q : K), q.ne_zero, hq.ne⟩
  refine map_tateUniformizationBaseChange q hq _ ?_ x
  refine (AddMonoidHomClass.isometry_of_norm (σ : L →ₐ[K] L) fun y ↦ ?_).continuous
  rw [NormedAlgebra.norm_eq_spectralNorm K, NormedAlgebra.norm_eq_spectralNorm K]
  exact (spectralNorm_eq_of_equiv σ y).symm

end TauCeti

end

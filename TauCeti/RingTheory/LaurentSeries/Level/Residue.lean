/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Puiseux.FiniteExtension
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Residue

/-!
# Residues on ramified levels and on finite extensions of `K⸨X⸩`

Let `K` be a field and `d` a positive integer. On the ramified level `K⸨u⸩` over `K⸨t⸩`, with
`t = u ^ d`, a form `x dt` is written in the level parameter as `x · d(u ^ d)/du · du`, and its
residue `TauCeti.LaurentSeries.Level.residue K d x` is the coefficient of `u⁻¹` in
`x · d(u ^ d)/du`. Since `d(u ^ d)/du = d u ^ (d - 1)`, it is `d` times the coefficient of
`u ^ (-d)` in `x`. On a base form `f dt`, `f ∈ K⸨t⸩`, it is `d` times the residue of `f dt`, and on
the actual level `d` of the Puiseux field it is `d` times the rational-exponent residue
`TauCeti.puiseuxField.residue`.

This residue is invariant under every automorphism of the level over `K⸨t⸩`, in every
characteristic. Such an automorphism sends `u` to `η u` for a `d`-th root of unity `η ∈ K`
(`TauCeti.LaurentSeries.Level.kummer_surjective`), so it is the coordinate change `u ↦ η u`; it
multiplies the coefficient of `u ^ (-d)` by `η ^ (-d) = 1`. Consequently, for an extension `L` of
`K⸨t⸩`, the residue `Res_u (φ x dt)` computed through an isomorphism `φ : L ≃ₐ[K⸨t⸩] K⸨u⸩` does
not depend on `φ`, since two choices differ by an automorphism of the level.

When `K` is algebraically closed of characteristic zero, every extension of `K⸨t⸩` of degree `e`
is isomorphic to the level `K⸨u⸩`, `u ^ e = t` (`TauCeti.LaurentSeries.Level.algEquivOfFinrankEq`),
so every finite extension `L` carries a residue of forms
`TauCeti.LaurentSeries.Level.residueOfFinrankEq`, computed through any such isomorphism and
preserved by isomorphisms of extensions.

## Main definitions

* `TauCeti.LaurentSeries.Level.residue K d`: the residue of `x dt` on the level `K⸨u⸩`,
  `u ^ d = t`.
* `TauCeti.LaurentSeries.Level.residueOfFinrankEq`: the residue of `x dt` on a finite extension
  of `K⸨t⸩`, for `K` algebraically closed of characteristic zero.

## Main results

* `TauCeti.LaurentSeries.Level.residue_eq_nsmul_coeff`: the residue of `x dt` is `d` times the
  coefficient of `u ^ (-d)` in `x`.
* `TauCeti.LaurentSeries.Level.residue_algebraMap`: on base forms, the residue is multiplied by
  the degree `d`.
* `TauCeti.LaurentSeries.Level.residue_eq_nsmul_residue_toPuiseux`: on the Puiseux field, the
  level residue is `d` times the rational-exponent residue.
* `TauCeti.LaurentSeries.Level.residue_algEquiv_apply`: the residue is invariant under the
  automorphisms of the level over `K⸨t⸩`.
* `TauCeti.LaurentSeries.Level.residue_apply_eq_of_algEquiv`: the residue computed through an
  isomorphism with the level does not depend on the isomorphism.
* `TauCeti.LaurentSeries.Level.residueOfFinrankEq_apply`: the residue of a finite extension is
  computed through any isomorphism with the level.
-/

public section

open HahnSeries LaurentSeries Module
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Level

section Residue

variable (K : Type*) [Field K] (d : ℕ+)

/-- The **residue** of the form `x dt` on the ramified level `K⸨u⸩`, `u ^ d = t`: the coefficient
of `u⁻¹` in `x · d(u ^ d)/du`, since `dt = d(u ^ d)`. -/
noncomputable def residue : Level K d →+ K where
  toFun x := (ringEquivLaurentSeries K d x * derivative K (single (d : ℤ) 1)).coeff (-1)
  map_zero' := by simp
  map_add' x y := by simp [add_mul]

variable {K d}

/-- The residue of `x dt` on level `d` is the coefficient of `u⁻¹` in `x · d(u ^ d)/du`. -/
theorem residue_apply (x : Level K d) :
    residue K d x =
      (ringEquivLaurentSeries K d x * derivative K (single (d : ℤ) 1)).coeff (-1) :=
  (rfl)

/-- The residue of `x dt` on level `d` is `d` times the coefficient of `u ^ (-d)` in `x`. -/
theorem residue_eq_nsmul_coeff (x : Level K d) :
    residue K d x = (d : ℕ) • (ringEquivLaurentSeries K d x).coeff (-d) := by
  rw [residue_apply, puiseuxField.coeff_neg_one_mul_derivative_single_eq_nsmul_residue,
    puiseuxField.residue_levelEmbedding]

/-- On level `d`, the residue of a base form `f dt`, `f ∈ K⸨t⸩`, is `d` times its residue
`Res_t (f dt)`. -/
@[simp]
theorem residue_algebraMap (f : K⸨X⸩) :
    residue K d (Algebra.algebraMap K⸨X⸩ (Level K d) f) = (d : ℕ) • f.coeff (-1) := by
  rw [residue_eq_nsmul_coeff, algebraMap_apply, ← mul_neg_one, coeff_expand_mul]

/-- The residue on level `d` is `K`-linear: the residue of `(a x) dt`, for a constant `a ∈ K`, is
`a` times the residue of `x dt`. -/
@[simp]
theorem residue_algebraMap_algebraMap_mul (a : K) (x : Level K d) :
    residue K d (Algebra.algebraMap K⸨X⸩ (Level K d) (Algebra.algebraMap K K⸨X⸩ a) * x) =
      a * residue K d x := by
  rw [residue_eq_nsmul_coeff, residue_eq_nsmul_coeff, map_mul, algebraMap_apply, AlgHom.commutes,
    _root_.LaurentSeries.algebraMap_apply, C_mul_eq_smul, coeff_smul, smul_eq_mul, mul_smul_comm]

/-- Embedded in the Puiseux field, the residue of `x dt` on level `d` is `d` times the
rational-exponent residue, the coefficient of `t⁻¹`. -/
theorem residue_eq_nsmul_residue_toPuiseux (x : Level K d) :
    residue K d x = (d : ℕ) • puiseuxField.residue K (toPuiseux K d x) := by
  rw [residue_apply, puiseuxField.coeff_neg_one_mul_derivative_single_eq_nsmul_residue,
    toPuiseux_apply]

/-- The residue on level `d` is invariant under every automorphism of the level over `K⸨t⸩`, over
every field `K`: such an automorphism is a Kummer automorphism `u ↦ η u`, which multiplies the
coefficient of `u ^ (-d)` by `η ^ (-d) = 1`. -/
@[simp]
theorem residue_algEquiv_apply (σ : Level K d ≃ₐ[K⸨X⸩] Level K d) (x : Level K d) :
    residue K d (σ x) = residue K d x := by
  obtain ⟨η, rfl⟩ := kummer_surjective σ
  have hη : (η : Kˣ) ^ (-(d : ℤ)) = 1 := by
    rw [zpow_neg, zpow_natCast, (mem_rootsOfUnity _ _).mp η.prop, inv_one]
  rw [residue_eq_nsmul_coeff, residue_eq_nsmul_coeff, ringEquivLaurentSeries_kummer,
    TauCeti.LaurentSeries.coeff_rescale, hη, Units.val_one, one_mul]

/-- **Independence of the chosen isomorphism.** For an extension `L` of `K⸨t⸩`, the residue of
`x dt` computed through an isomorphism `L ≃ₐ[K⸨t⸩] K⸨u⸩` with the level, `u ^ d = t`, does not
depend on the isomorphism. -/
theorem residue_apply_eq_of_algEquiv {L : Type*} [Semiring L] [Algebra K⸨X⸩ L]
    (φ ψ : L ≃ₐ[K⸨X⸩] Level K d) (x : L) :
    residue K d (φ x) = residue K d (ψ x) := by
  rw [← residue_algEquiv_apply (φ.symm.trans ψ), AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

end Residue

section FiniteExtension

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  {L : Type*} [Field L] [Algebra K⸨X⸩ L] {e : ℕ+}

/-- The **residue** of the form `x dt` on an extension `L` of `K⸨t⸩` of degree `e`, for `K`
algebraically closed of characteristic zero: the level residue of the image of `x` under an
isomorphism `L ≃ₐ[K⸨t⸩] K⸨u⸩`, `u ^ e = t`. It does not depend on the isomorphism
(`TauCeti.LaurentSeries.Level.residueOfFinrankEq_apply`). -/
noncomputable def residueOfFinrankEq (h : finrank K⸨X⸩ L = e) : L →+ K :=
  (residue K e).comp (algEquivOfFinrankEq h).toAddMonoidHom

/-- The residue of a finite extension is computed through any isomorphism with the level. -/
theorem residueOfFinrankEq_apply (h : finrank K⸨X⸩ L = e) (φ : L ≃ₐ[K⸨X⸩] Level K e) (x : L) :
    residueOfFinrankEq h x = residue K e (φ x) :=
  residue_apply_eq_of_algEquiv _ φ x

/-- The residue of a finite extension is `K`-linear: the residue of `(a x) dt`, for a constant
`a ∈ K`, is `a` times the residue of `x dt`. -/
@[simp]
theorem residueOfFinrankEq_algebraMap_algebraMap_mul (h : finrank K⸨X⸩ L = e) (a : K) (x : L) :
    residueOfFinrankEq h (Algebra.algebraMap K⸨X⸩ L (Algebra.algebraMap K K⸨X⸩ a) * x) =
      a * residueOfFinrankEq h x := by
  rw [residueOfFinrankEq_apply h (algEquivOfFinrankEq h), map_mul, AlgEquiv.commutes,
    residue_algebraMap_algebraMap_mul, residueOfFinrankEq_apply h (algEquivOfFinrankEq h)]

/-- The residue of finite extensions is preserved by isomorphisms of extensions of `K⸨t⸩`. -/
@[simp]
theorem residueOfFinrankEq_algEquiv_apply {L' : Type*} [Field L'] [Algebra K⸨X⸩ L']
    (h : finrank K⸨X⸩ L = e) (h' : finrank K⸨X⸩ L' = e) (ψ : L ≃ₐ[K⸨X⸩] L') (x : L) :
    residueOfFinrankEq h' (ψ x) = residueOfFinrankEq h x := by
  rw [residueOfFinrankEq_apply h' (ψ.symm.trans (algEquivOfFinrankEq h)),
    residueOfFinrankEq_apply h (algEquivOfFinrankEq h), AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]

end FiniteExtension

end TauCeti.LaurentSeries.Level

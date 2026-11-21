/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Basic
public import TauCeti.RingTheory.LaurentSeries.Level.Trace

/-!
# Continuous one-forms of a ramified level and their trace

Let `L = K⸨u⸩` be the ramified level of degree `d` over `F = K⸨t⸩`, where `t = u ^ d`
(`TauCeti.LaurentSeries.Level K d`). Its continuous one-forms `Ω¹_cont(L/K)` are the continuous
one-forms `TauCeti.ContinuousKaehlerDifferential K` of `K⸨X⸩` read in the level variable `u`, with
the scalar action of `L`; every one is `g du` for a unique `g ∈ L`. Pulling back along
`t = u ^ d` gives the `F`-linear map

`Ω¹_cont(F/K) → Ω¹_cont(L/K)`, `f dt ↦ f (u ^ d) d(u ^ d) = f (u ^ d) d u ^ (d - 1) du`,

which sends `d f` to `d (f (u ^ d))`. Since `dt = d u ^ (d - 1) du`, every one-form on `L` is a
multiple of `dt` exactly when `d` is nonzero in `K`, that is, when `L/F` is separable. Then the
pullback extends to an isomorphism of `L`-modules

`L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`, `g ⊗ ω ↦ g ω`,

and the trace of `L/F` acts on the first factor. This gives the trace of one-forms
`Tr_{L/F} : Ω¹_cont(L/K) → Ω¹_cont(F/K)`, `g dt ↦ Tr_{L/F} (g) dt`. It preserves residues:
`Res_F (Tr_{L/F} ω) = Res_L ω`, where `Res_F (f dt)` is the coefficient of `t⁻¹` in `f` and
`Res_L (g du)` is the coefficient of `u⁻¹` in `g`.

When the characteristic of `K` divides `d`, the form `dt` vanishes on `L`, so the pullback is
zero (`Level.ContinuousKaehlerDifferential.map_eq_zero_iff`).

## Main definitions

* `TauCeti.LaurentSeries.Level.derivation K d`: the `K`-derivation `d/du` of level `d` in its
  level variable `u`.
* `TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential K d`: the continuous one-forms
  `Ω¹_cont(L/K)` of level `d`.
* `Level.ContinuousKaehlerDifferential.equivLevel K d`: the `L`-linear
  equivalence `Ω¹_cont(L/K) ≃ L`, `g du ↦ g`.
* `Level.ContinuousKaehlerDifferential.D K d`: the continuous differential `d_u : L → Ω¹_cont(L/K)`
  in the level parameter `u`.
* `Level.ContinuousKaehlerDifferential.map K d`: the pullback
  `Ω¹_cont(F/K) → Ω¹_cont(L/K)` along `t = u ^ d`.
* `Level.ContinuousKaehlerDifferential.tensorEquiv K d`: for `d` nonzero in
  `K`, the `L`-linear equivalence `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`.
* `Level.ContinuousKaehlerDifferential.trace K d`: for `d` nonzero in `K`,
  the trace `Ω¹_cont(L/K) → Ω¹_cont(F/K)`.

## Main results

* `TauCeti.LaurentSeries.Level.derivation_parameter`: `d/du (u) = 1`.
* `Level.ContinuousKaehlerDifferential.map_D`: the pullback of `d f` is `d_u (f (u ^ d))`.
* `Level.ContinuousKaehlerDifferential.equivLevel_map`: the pullback of `f dt` is
  `f (u ^ d) d u ^ (d - 1) du`.
* `Level.ContinuousKaehlerDifferential.map_eq_zero_iff`: the pullback vanishes exactly when `d`
  vanishes in `K`.
* `Level.ContinuousKaehlerDifferential.tensorEquiv_tmul`: the equivalence
  sends `g ⊗ ω` to `g` times the pullback of `ω`.
* `Level.ContinuousKaehlerDifferential.trace_smul_map`:
  `Tr_{L/F} (g ω) = Tr_{L/F} (g) ω` for `ω` a one-form on `F`.
* `Level.ContinuousKaehlerDifferential.trace_map`: the trace of a pulled
  back one-form is `d` times the form.
* `Level.ContinuousKaehlerDifferential.trace_D`: `Tr_{L/F} (d_u x) = d (Tr_{L/F} x)`.
* `Level.ContinuousKaehlerDifferential.coeff_neg_one_equivLaurentSeries_trace`:
  `Res_F (Tr_{L/F} ω) = Res_L ω`.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968), for the trace of
  differentials in a finite separable extension and its compatibility with residues.
-/

public section

open HahnSeries LaurentSeries TensorProduct
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Level

variable (K : Type*) [Field K] (d : ℕ+)

/-- The `K`-derivation `d/du` of the ramified level `Level K d` (`L = K⸨u⸩`, `u ^ d = t`) in its
level variable `u`: the formal derivative of `K⸨X⸩` transported across `ringEquivLaurentSeries`. -/
noncomputable def derivation : Derivation K (Level K d) (Level K d) :=
  let e := algEquivLaurentSeries K d
  letI : Module K K⸨X⸩ := Algebra.toModule
  (laurentSeriesAlgebraDerivation K).liftOfRightInverse
    (f := e.symm) (f_inv := e) e.symm_apply_apply (by simp)

/-- In the level variable `u`, `Level.derivation K d` is the formal derivative of `K⸨X⸩`. -/
@[simp]
theorem ringEquivLaurentSeries_derivation {K : Type*} [Field K] {d : ℕ+} (x : Level K d) :
    ringEquivLaurentSeries K d (Level.derivation K d x) =
      derivative K (ringEquivLaurentSeries K d x) := by
  obtain ⟨y, rfl⟩ := (algEquivLaurentSeries K d).symm.surjective x
  rw [Level.derivation, Derivation.liftOfRightInverse_apply]
  simp

/-- The level derivation sends the level parameter `u` to `1`. -/
@[simp]
theorem derivation_parameter :
    Level.derivation K d (parameter K d) = 1 := by
  apply (ringEquivLaurentSeries K d).injective
  simp

/-- The **continuous one-forms** `Ω¹_cont(L/K)` of the ramified level `L = K⸨u⸩`, `u ^ d = t`:
a wrapped copy of the continuous one-forms of `K⸨X⸩`, read in the level variable `u` and carrying
the scalar action of `L`. The wrapper keeps this action apart from the `K⸨t⸩`-module structure of
`Ω¹_cont(K⸨X⸩/K)` itself. -/
@[ext]
structure ContinuousKaehlerDifferential (K : Type*) [Field K] (d : ℕ+) where
  ofForm ::
  /-- The continuous one-form of `K⸨X⸩`, in the level variable, underlying a one-form of a
  ramified level. -/
  toForm : TauCeti.ContinuousKaehlerDifferential K

namespace ContinuousKaehlerDifferential

/-- The underlying continuous one-form of `K⸨X⸩` of a one-form of level `d`. -/
def equivForm :
    Level.ContinuousKaehlerDifferential K d ≃ TauCeti.ContinuousKaehlerDifferential K where
  toFun := toForm
  invFun := ofForm
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : AddCommGroup (Level.ContinuousKaehlerDifferential K d) :=
  (equivForm K d).addCommGroup

/-- The identification of the one-forms of level `d` with the continuous one-forms of `K⸨X⸩` in
the level variable `u`. -/
noncomputable def addEquivContinuousKaehlerDifferential :
    Level.ContinuousKaehlerDifferential K d ≃+ TauCeti.ContinuousKaehlerDifferential K :=
  (equivForm K d).addEquiv

/-- Reading a form constructed in the level variable recovers the original Laurent form. -/
@[simp]
theorem addEquivContinuousKaehlerDifferential_ofForm
    (ω : TauCeti.ContinuousKaehlerDifferential K) :
    addEquivContinuousKaehlerDifferential K d (ofForm ω) = ω :=
  (rfl)

/-- The level acts on its one-forms through its underlying Laurent series in `u`. -/
noncomputable instance : Module (Level K d) (Level.ContinuousKaehlerDifferential K d) :=
  letI := Module.compHom (TauCeti.ContinuousKaehlerDifferential K)
    (ringEquivLaurentSeries K d).toRingHom
  (addEquivContinuousKaehlerDifferential K d).module (Level K d)

/-- The base field `K⸨t⸩` acts on the one-forms of level `d` through the level. -/
noncomputable instance : Module K⸨X⸩ (Level.ContinuousKaehlerDifferential K d) :=
  Module.compHom _ (Algebra.algebraMap K⸨X⸩ (Level K d))

instance : IsScalarTower K⸨X⸩ (Level K d) (Level.ContinuousKaehlerDifferential K d) :=
  -- `f • ω` is `algebraMap f • ω` by definition of the restricted action.
  ⟨fun f g ω ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩

/-- Constants act on the one-forms of level `d` through the level. -/
noncomputable instance : Module K (Level.ContinuousKaehlerDifferential K d) :=
  Module.compHom _ (Algebra.algebraMap K (Level K d))

instance : IsScalarTower K (Level K d) (Level.ContinuousKaehlerDifferential K d) :=
  -- `c • ω` is `algebraMap c • ω` by definition of `Module.compHom`.
  ⟨fun c g ω ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩

instance : IsScalarTower K K⸨X⸩ (Level.ContinuousKaehlerDifferential K d) where
  smul_assoc c f ω := by
    rw [← IsScalarTower.algebraMap_smul (Level K d) (c • f),
      ← IsScalarTower.algebraMap_smul (Level K d) f, ← C_mul_eq_smul,
      ← _root_.LaurentSeries.algebraMap_apply, map_mul,
      ← IsScalarTower.algebraMap_apply K K⸨X⸩ (Level K d), ← Algebra.smul_def, smul_assoc]

variable {K d}

/-- The scalar action of the level on its one-forms is that of the underlying Laurent series. -/
@[simp]
theorem addEquivContinuousKaehlerDifferential_smul (g : Level K d)
    (ω : Level.ContinuousKaehlerDifferential K d) :
    addEquivContinuousKaehlerDifferential K d (g • ω) =
      ringEquivLaurentSeries K d g • addEquivContinuousKaehlerDifferential K d ω :=
  (rfl)

/-- The base field `K⸨t⸩` acts on the one-forms of level `d` through the expansion
`t ↦ u ^ d`. -/
@[simp]
theorem addEquivContinuousKaehlerDifferential_laurentSeries_smul (f : K⸨X⸩)
    (ω : Level.ContinuousKaehlerDifferential K d) :
    addEquivContinuousKaehlerDifferential K d (f • ω) =
      expand K d f • addEquivContinuousKaehlerDifferential K d ω := by
  rw [← IsScalarTower.algebraMap_smul (Level K d) f, addEquivContinuousKaehlerDifferential_smul,
    algebraMap_apply]

/-- Constants act on the one-forms of level `d` as on the underlying Laurent one-forms. -/
@[simp]
theorem addEquivContinuousKaehlerDifferential_const_smul (c : K)
    (ω : Level.ContinuousKaehlerDifferential K d) :
    addEquivContinuousKaehlerDifferential K d (c • ω) =
      c • addEquivContinuousKaehlerDifferential K d ω := by
  rw [← IsScalarTower.algebraMap_smul (Level K d) c, addEquivContinuousKaehlerDifferential_smul,
    ringEquivLaurentSeries_algebraMap_const, ← IsScalarTower.algebraMap_smul K⸨X⸩ c]

variable (K d)

/-- **One-forms of a level are multiples of `du`.** The `L`-linear equivalence
`Ω¹_cont(L/K) ≃ L` sending `g du` to `g`. -/
noncomputable def equivLevel :
    Level.ContinuousKaehlerDifferential K d ≃ₗ[Level K d] Level K d where
  toFun ω := (ringEquivLaurentSeries K d).symm
    (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K
      (addEquivContinuousKaehlerDifferential K d ω))
  invFun g := (addEquivContinuousKaehlerDifferential K d).symm
    ((TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).symm
      (ringEquivLaurentSeries K d g))
  map_add' ω η := by simp
  map_smul' g ω := by simp
  left_inv ω := by simp
  right_inv g := by simp

variable {K d}

/-- The coordinate of a one-form of level `d` in `du` is its coordinate in `dX` read in the level
variable. -/
@[simp]
theorem ringEquivLaurentSeries_equivLevel (ω : Level.ContinuousKaehlerDifferential K d) :
    ringEquivLaurentSeries K d (equivLevel K d ω) =
      TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K
        (addEquivContinuousKaehlerDifferential K d ω) :=
  (ringEquivLaurentSeries K d).apply_symm_apply _

variable (K d) in
/-- The continuous differential `d_u : L → Ω¹_cont(L/K)` of level `d`, read in the level variable
`u`. -/
noncomputable def D : Derivation K (Level K d) (Level.ContinuousKaehlerDifferential K d) :=
  (equivLevel K d).symm.toLinearMap.compDer (Level.derivation K d)

/-- In coordinates, `d_u x` has coefficient `dx / du` in `du`. -/
@[simp]
theorem equivLevel_D (x : Level K d) :
    equivLevel K d (D K d x) =
      (ringEquivLaurentSeries K d).symm (derivative K (ringEquivLaurentSeries K d x)) := by
  apply (ringEquivLaurentSeries K d).injective
  simp [D]

/-- In the level variable `u`, `D K d` is the continuous differential of `K⸨X⸩`. -/
@[simp]
theorem addEquivContinuousKaehlerDifferential_D (x : Level K d) :
    addEquivContinuousKaehlerDifferential K d (D K d x) =
      TauCeti.ContinuousKaehlerDifferential.D K (ringEquivLaurentSeries K d x) := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [← ringEquivLaurentSeries_equivLevel, equivLevel_D,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D, RingEquiv.apply_symm_apply]

/-! ### Pulling back one-forms along `t = u ^ d` -/

variable (K d)

/-- **Pulling back one-forms along `t = u ^ d`.** The `F`-linear map
`Ω¹_cont(F/K) → Ω¹_cont(L/K)`, `f dt ↦ f (u ^ d) d(u ^ d)`: the substitution `X ↦ X ^ d` into
continuous one-forms, read on level `d`. -/
noncomputable def map :
    TauCeti.ContinuousKaehlerDifferential K →ₗ[K⸨X⸩] Level.ContinuousKaehlerDifferential K d where
  toFun ω := (addEquivContinuousKaehlerDifferential K d).symm
    (TauCeti.ContinuousKaehlerDifferential.subst (K := K) (φ := PowerSeries.X ^ (d : ℕ))
      (by simp) (pow_ne_zero _ PowerSeries.X_ne_zero) ω)
  map_add' ω η := by simp
  map_smul' f ω := by
    apply (addEquivContinuousKaehlerDifferential K d).injective
    simp [TauCeti.LaurentSeries.substAlgHom_X_pow_eq_expand]

variable {K d}

/-- The pullback along `t = u ^ d` is the substitution `X ↦ X ^ d` into one-forms. -/
theorem addEquivContinuousKaehlerDifferential_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    addEquivContinuousKaehlerDifferential K d (map K d ω) =
      TauCeti.ContinuousKaehlerDifferential.subst (K := K) (φ := PowerSeries.X ^ (d : ℕ))
        (by simp) (pow_ne_zero _ PowerSeries.X_ne_zero) ω :=
  (addEquivContinuousKaehlerDifferential K d).apply_symm_apply _

/-- Pulling back `d f` along `t = u ^ d` yields the level differential of the image of `f`. -/
@[simp]
theorem map_D (f : K⸨X⸩) :
    map K d (TauCeti.ContinuousKaehlerDifferential.D K f) =
      D K d (Algebra.algebraMap K⸨X⸩ (Level K d) f) := by
  apply (addEquivContinuousKaehlerDifferential K d).injective
  rw [addEquivContinuousKaehlerDifferential_map, TauCeti.ContinuousKaehlerDifferential.subst_D,
    TauCeti.LaurentSeries.substAlgHom_X_pow_eq_expand, addEquivContinuousKaehlerDifferential_D,
    algebraMap_apply]

/-- In coordinates, the pullback sends `f dt` to `f (u ^ d) d u ^ (d - 1) du`. -/
@[simp]
theorem equivLevel_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    equivLevel K d (map K d ω) =
      Algebra.algebraMap K⸨X⸩ (Level K d)
          (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω) *
        (ringEquivLaurentSeries K d).symm (derivative K (single (d : ℤ) 1)) := by
  apply (ringEquivLaurentSeries K d).injective
  simp [addEquivContinuousKaehlerDifferential_map,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_subst,
    TauCeti.LaurentSeries.substAlgHom_X_pow_eq_expand, single_pow]

/-- **The pullback vanishes in characteristic dividing `d`.** Pulling back along `t = u ^ d` is
zero exactly when `d` vanishes in `K`, since `dt = d u ^ (d - 1) du`. -/
theorem map_eq_zero_iff : map K d = 0 ↔ ((d : ℕ) : K) = 0 := by
  rw [← Int.cast_natCast, ← derivative_single_one_eq_zero_iff (R := K)]
  constructor
  · intro h
    have h1 := congrArg (equivLevel K d) (LinearMap.congr_fun h
      ((TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).symm 1))
    simpa using h1
  · intro h
    refine LinearMap.ext fun ω ↦ (equivLevel K d).injective ?_
    simp [h]

/-! ### Scalar extension and the trace -/

section Separable

variable [NeZero ((d : ℕ) : K)]

private theorem symm_derivative_single_ne_zero :
    (ringEquivLaurentSeries K d).symm (derivative K (single (d : ℤ) 1)) ≠ 0 :=
  (RingEquiv.map_ne_zero_iff _).mpr derivative_single_natCast_one_ne_zero

variable (K d)

/-- **Scalar extension of one-forms.** When `d` is nonzero in `K`, the one-forms of the level
`L = K⸨u⸩` are the scalar extension of those of `F = K⸨t⸩`: the `L`-linear equivalence
`L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)` sending `g ⊗ ω` to `g` times the pullback of `ω`
(`TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.tensorEquiv_tmul`). -/
noncomputable def tensorEquiv :
    Level K d ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K ≃ₗ[Level K d]
      Level.ContinuousKaehlerDifferential K d :=
  (AlgebraTensorModule.congr (LinearEquiv.refl (Level K d) (Level K d))
      (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).toLinearEquiv).trans <|
    (AlgebraTensorModule.rid K⸨X⸩ (Level K d) (Level K d)).trans <|
      (LinearEquiv.smulOfNeZero (Level K d) (Level K d) _
        (symm_derivative_single_ne_zero (K := K) (d := d))).trans (equivLevel K d).symm

variable {K d}

/-- The equivalence `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)` sends `g ⊗ ω` to `g` times the pullback
of `ω`. -/
@[simp]
theorem tensorEquiv_tmul (g : Level K d) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    tensorEquiv K d (g ⊗ₜ ω) = g • map K d ω := by
  apply (equivLevel K d).injective
  simp [tensorEquiv, Algebra.smul_def, mul_comm, mul_left_comm]

/-- The equivalence `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)` is the scalar extension of the pullback
along `t = u ^ d`. -/
theorem toLinearMap_tensorEquiv :
    (tensorEquiv K d).toLinearMap = (map K d).liftBaseChange (Level K d) :=
  TensorProduct.AlgebraTensorModule.curry_injective <| LinearMap.ext₂ fun g ω ↦ by simp

variable (K d)

/-- **The trace of one-forms.** When `d` is nonzero in `K`, the trace
`Tr_{L/F} : Ω¹_cont(L/K) → Ω¹_cont(F/K)` of the level `L = K⸨u⸩` over `F = K⸨t⸩`: the trace of
`L/F` on the first factor of `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`. It sends `g dt` to
`Tr_{L/F} (g) dt`. -/
noncomputable def trace :
    Level.ContinuousKaehlerDifferential K d →ₗ[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K :=
  (TensorProduct.lid K⸨X⸩ _).toLinearMap ∘ₗ
    (Algebra.trace K⸨X⸩ (Level K d)).rTensor _ ∘ₗ
      ((tensorEquiv K d).symm.restrictScalars K⸨X⸩).toLinearMap

variable {K d}

/-- **The trace of `g ω`.** For a one-form `ω` on `F`, the trace of `g` times its pullback is
`Tr_{L/F} (g) ω`. -/
@[simp]
theorem trace_smul_map (g : Level K d) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K d (g • map K d ω) = Algebra.trace K⸨X⸩ (Level K d) g • ω := by
  rw [← tensorEquiv_tmul]
  simp [trace, -tensorEquiv_tmul]

/-- The trace of a pulled back one-form is `d` times the form. -/
@[simp]
theorem trace_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K d (map K d ω) = (d : ℕ) • ω := by
  have h : Algebra.trace K⸨X⸩ (Level K d) 1 = (d : ℕ) • 1 := by
    simpa using trace_parameter_zpow (K := K) d 0
  rw [← one_smul (Level K d) (map K d ω), trace_smul_map, h, smul_assoc, one_smul]

/-- In coordinates, the trace of `g du` is the trace of `g / (d u ^ (d - 1))` times `dt`. -/
theorem equivLaurentSeries_trace (ω : Level.ContinuousKaehlerDifferential K d) :
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K d ω) =
      Algebra.trace K⸨X⸩ (Level K d)
        (equivLevel K d ω /
          (ringEquivLaurentSeries K d).symm (derivative K (single (d : ℤ) 1))) := by
  set c := (ringEquivLaurentSeries K d).symm (derivative K (single (d : ℤ) (1 : K)))
  have hω : ω = (equivLevel K d ω / c) •
      map K d (TauCeti.ContinuousKaehlerDifferential.D K (single 1 1)) := by
    apply (equivLevel K d).injective
    simpa [c] using (div_mul_cancel₀ (equivLevel K d ω) symm_derivative_single_ne_zero).symm
  conv_lhs => rw [hω]
  rw [trace_smul_map, map_smul, TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D,
    smul_eq_mul]
  simp

/-- The trace of `d_u x` is the base differential `d(Tr_{L/F} x)`. -/
@[simp]
theorem trace_D (x : Level K d) :
    trace K d (D K d x) =
      TauCeti.ContinuousKaehlerDifferential.D K (Algebra.trace K⸨X⸩ (Level K d) x) := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, equivLevel_D,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D]
  ext j
  have hd : ((d : ℕ) : K) ≠ 0 := NeZero.ne _
  have h1 : (d : ℤ) * j - -((d : ℤ) - 1) = (d : ℤ) * (j + 1) - 1 := by ring
  have hd1 : derivative K (single (d : ℤ) (1 : K)) = single ((d : ℤ) - 1) ((d : ℕ) : K) := by
    simp [derivative_apply]
  rw [← map_div₀, coeff_trace, RingEquiv.apply_symm_apply, hd1, div_eq_mul_inv,
    HahnSeries.inv_single, coeff_mul_single, h1, coeff_derivative_sub_one, coeff_derivative,
    coeff_trace]
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]
  field_simp [hd]

/-- **The trace preserves residues.** When `d` is nonzero in `K`, for every one-form `ω = g du`
on the level `L = K⸨u⸩`, the residue of `Tr_{L/F} ω` at `t` is the residue of `ω` at `u`:
`Res_F (Tr_{L/F} ω) = Res_L ω`. -/
theorem coeff_neg_one_equivLaurentSeries_trace (ω : Level.ContinuousKaehlerDifferential K d) :
    (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K d ω)).coeff (-1) =
      (ringEquivLaurentSeries K d (equivLevel K d ω)).coeff (-1) := by
  rw [equivLaurentSeries_trace, coeff_neg_one_trace, map_div₀, RingEquiv.apply_symm_apply,
    div_mul_cancel₀ _ derivative_single_natCast_one_ne_zero]

end Separable

end ContinuousKaehlerDifferential

end TauCeti.LaurentSeries.Level

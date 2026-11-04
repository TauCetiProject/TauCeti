/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.LeftIdeal
public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.RingTheory.LaurentSeries.Derivative
public import Mathlib.Algebra.Lie.Derivation.BaseChange
-- Private: the dual numbers appear only in the construction below, never in a statement.
import Mathlib.Algebra.DualNumber

/-!
# Vector fields and the degree derivation on currents and level enveloping algebras

A Laurent series `h` defines the vector field `h d/dt`, which acts on the formal currents
`L((t)) = R⸨X⸩ ⊗[R] L` of a Lie algebra `L` by differentiating the scalar factor,
`f ⊗ x ↦ h f' ⊗ x`. This is a derivation of the current Lie algebra
(`TauCeti.CurrentAlgebra.vectorFieldDerivation`). It is skew for the residue pairing of every
bilinear form, `Res(δu dv) + Res(u d(δv)) = 0`, because `Res(h f' dg) + Res(f d(h g'))` is the
residue of the exact differential `d(f h g')`. Hence it lifts to a derivation of the residue
central extension `ĝ = L((t)) ⊕ R K` acting by `h d/dt` on currents and killing `K`
(`TauCeti.CurrentAlgebra.vectorFieldExtensionDerivation`), and to a derivation of the level
enveloping algebra `U(ĝ) / (ι K - a)` acting by `h d/dt` on the current generators
(`TauCeti.CurrentAlgebra.vectorFieldEnvelopingDerivation`), at every central value `a`, including
`a = 0`. This lift is unique, since a derivation of `U(ĝ) / (ι K - a)` is determined by its values
on the current generators (`LieAlgebra.ofTwoCocycle.derivation_ext_envelopingι`).

If `h` has order at least `P`, the vector field `h d/dt` sends currents of order at least `N` to
currents of order at least `P + N - 1`. So when `h` has positive order it preserves each order
submodule `a_N` and each left ideal `I_N = U · ι(a_N)`
(`TauCeti.CurrentAlgebra.vectorFieldEnvelopingDerivation_mem_orderLeftIdeal`). The lifts commute
with the level comparison `TauCeti.CurrentAlgebra.levelEnvelopingEquiv` between
`U(ĝ_Ψ) / (ι K - 1)` and `U(ĝ_Φ) / (ι K - k)` for `Ψ = k • Φ`, for every `k`, including `k = 0`
(`TauCeti.CurrentAlgebra.levelEnvelopingEquiv_vectorFieldEnvelopingDerivation`).

The main example is the **degree derivation** `d = t d/dt`, the vector field of `h = t`. It
multiplies the coefficient of `tⁿ` by `n`, so on modes `x_n = tⁿ ⊗ x` it acts by `[d, x_n] = n x_n`
(`TauCeti.CurrentAlgebra.vectorFieldDerivation_single_one_single_tmul`). Since `t` has order one,
`d` preserves every `I_N`. The vector field `h = 1` is the translation `d/dt`, which lowers orders
by one.

The current derivation is Mathlib's `Lie.Derivation.ofDerivation` of the derivation `h d/dt` of
`R⸨X⸩`, written as `h t⁻¹` times the Euler operator `HahnSeries.weightDerivation` of the integer
cast. This is a derivation for the coefficientwise algebra structure `HahnSeries.instAlgebra` used
by the currents, which is not definitionally the algebra structure for which
`TauCeti.laurentSeriesDerivation` is a derivation. The lift to the enveloping algebra applies the
universal property `TauCeti.CurrentAlgebra.liftOfCurrents` to `u ↦ ι u + ε ι(h u')` with values in
the dual numbers, as in `TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation`.

## Main definitions

* `TauCeti.CurrentAlgebra.vectorFieldDerivation`: the derivation `h d/dt` of formal currents.
* `TauCeti.CurrentAlgebra.vectorFieldExtensionDerivation`: its lift to the residue central
  extension, killing `K`.
* `TauCeti.CurrentAlgebra.vectorFieldEnvelopingDerivation`: its lift to `U(ĝ) / (ι K - a)`.

## Main results

* `TauCeti.CurrentAlgebra.residuePairing_vectorFieldDerivation_add`: vector fields are skew for
  the residue pairing.
* `TauCeti.CurrentAlgebra.vectorFieldEnvelopingDerivation_envelopingι`: the lift acts by `h d/dt`
  on the current generators.
* `TauCeti.CurrentAlgebra.vectorFieldEnvelopingDerivation_mem_orderLeftIdeal`: vector fields of
  positive order preserve each `I_N`.
* `TauCeti.CurrentAlgebra.levelEnvelopingEquiv_vectorFieldEnvelopingDerivation`: the lifts commute
  with the level comparison.
* `TauCeti.CurrentAlgebra.coeff_vectorFieldDerivation_single_one`: the degree derivation multiplies
  the coefficient of `tⁿ` by `n`.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Chapter 7, for the derivation `t d/dt`
  of the affine algebra and the extended affine algebra it defines.
* E. Frenkel, *Langlands Correspondence for Loop Groups*, for the action of the Lie algebra of
  vector fields `Der K` on the affine Kac--Moody algebra and its enveloping algebras.
-/

public section

noncomputable section

open scoped TensorProduct LaurentSeries
open HahnSeries LieAlgebra LieModule.Cohomology TauCeti.UniversalEnvelopingAlgebra
open LieAlgebra.ofTwoCocycle (centralElement envelopingι ι_ofProd envelopingι_mul_sub_mul
  algHom_ext_envelopingι derivation_ext_envelopingι)

-- The coefficientwise algebra structure matches the module used by the tensor product.
attribute [local instance 1100] HahnSeries.instAlgebra

-- Mathlib does not register the Lie ring of an associative ring as a global instance; the
-- commutators in the dual numbers over an enveloping algebra are written with it.
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "C" => currentAlgebra R L

/-! ### Vector fields on formal currents -/

section Currents

variable (R L) in
/-- **The vector field `h d/dt` on formal currents**: the derivation `f ⊗ x ↦ h f' ⊗ x`, which
differentiates the scalar factor and multiplies by the Laurent series `h`. For `h = t` it is the
degree derivation, and for `h = 1` the translation `d/dt`. -/
def vectorFieldDerivation (h : R⸨X⸩) : LieDerivation R C C :=
  -- `h d/dt` is `h t⁻¹` times the Euler operator `t d/dt`, a derivation for the coefficientwise
  -- algebra structure used by the currents.
  Lie.Derivation.ofDerivation L ((h * single (-1) 1) • weightDerivation (Int.castAddHom R))

/-- The vector field `h d/dt` differentiates the scalar factor of a pure tensor. -/
@[simp]
theorem vectorFieldDerivation_tmul (h f : R⸨X⸩) (x : L) :
    vectorFieldDerivation R L h (f ⊗ₜ x) = (h * LaurentSeries.derivative R f) ⊗ₜ x := by
  simp [vectorFieldDerivation, mul_smul, LaurentSeries.weightDerivation_intCastAddHom, ← mul_assoc,
    single_mul_single]

/-- **Vector fields lower orders by one less than their own order.** If `h` has order at least
`P` and `u` has order at least `N`, then `h u'` has order at least `P + N - 1`. -/
theorem vectorFieldDerivation_mem_orderSubmodule {P N : ℤ} {h : R⸨X⸩}
    (hh : (P : WithTop ℤ) ≤ h.orderTop) {u : C} (hu : u ∈ orderSubmodule R L N) :
    vectorFieldDerivation R L h u ∈ orderSubmodule R L (P + N - 1) := by
  rw [orderSubmodule_def] at hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨f, x, hf, rfl⟩ := hu
    rw [vectorFieldDerivation_tmul]
    refine tmul_mem_orderSubmodule R L _ ?_ x
    have hf' : ((N - 1 : ℤ) : WithTop ℤ) ≤ (LaurentSeries.derivative R f).orderTop := by
      have h₁ := hf.trans (LaurentSeries.orderTop_le_orderTop_derivative_add_one (R := R) f)
      cases hd : (LaurentSeries.derivative R f).orderTop with
      | top => exact le_top
      | coe k =>
        rw [hd, ← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe] at h₁
        exact WithTop.coe_le_coe.2 (by omega)
    have hPN : ((P + N - 1 : ℤ) : WithTop ℤ) ≤
        h.orderTop + (LaurentSeries.derivative R f).orderTop := by
      rw [add_sub_assoc, WithTop.coe_add]
      exact add_le_add hh hf'
    exact hPN.trans HahnSeries.orderTop_add_le_mul
  | zero => simp
  | add u v _ _ hu hv => simpa only [map_add] using add_mem hu hv
  | smul r u _ hu => simpa only [map_smul] using Submodule.smul_mem _ r hu

/-- **Vector fields are skew for the residue pairing**:
`Res(δu dv) + Res(u d(δv)) = 0` for `δ = h d/dt` and every bilinear form `Φ`. -/
theorem residuePairing_vectorFieldDerivation_add (Φ : LinearMap.BilinForm R L) (h : R⸨X⸩)
    (u v : C) :
    residuePairing R L Φ (vectorFieldDerivation R L h u) v +
      residuePairing R L Φ u (vectorFieldDerivation R L h v) = 0 := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ hu₁ hu₂ =>
    simp only [map_add, LinearMap.add_apply]
    linear_combination hu₁ + hu₂
  | tmul f x =>
    induction v using TensorProduct.inductionOn with
    | add v₁ v₂ hv₁ hv₂ =>
      simp only [map_add]
      linear_combination hv₁ + hv₂
    | tmul g y =>
      rw [vectorFieldDerivation_tmul, vectorFieldDerivation_tmul, residuePairing_tmul,
        residuePairing_tmul, ← add_mul, LaurentSeries.residuePairing_mul_derivative_add,
        zero_mul]

/-- **The degree derivation on modes**: `t d/dt` sends `x_n = r tⁿ ⊗ x` to `n x_n`. -/
theorem vectorFieldDerivation_single_one_single_tmul (n : ℤ) (r : R) (x : L) :
    vectorFieldDerivation R L (single 1 1) (single n r ⊗ₜ x) = n • (single n r ⊗ₜ x) := by
  rw [vectorFieldDerivation_tmul, TensorProduct.smul_tmul']
  congr 1
  ext m
  rw [LaurentSeries.coeff_single_one_mul_derivative, HahnSeries.coeff_smul]
  obtain rfl | hm := eq_or_ne m n
  · rfl
  · rw [HahnSeries.coeff_single_of_ne hm, smul_zero, smul_zero]

/-- **The degree derivation multiplies the coefficient of `tⁿ` by `n`.** -/
theorem coeff_vectorFieldDerivation_single_one (n : ℤ) (u : C) :
    coeff R L n (vectorFieldDerivation R L (single 1 1) u) = n • coeff R L n u := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv, smul_add]
  | tmul f x =>
    rw [vectorFieldDerivation_tmul, coeff_tmul, coeff_tmul,
      LaurentSeries.coeff_single_one_mul_derivative, smul_assoc]

end Currents

/-! ### The lift to the residue central extension -/

section Extension

variable (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)

local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "E" => ofTwoCocycle c

/-- **The vector field `h d/dt` on the residue central extension**: the derivation
`(u, z) ↦ (h u', 0)`, which acts by `h d/dt` on currents and kills the central line `R K`. -/
def vectorFieldExtensionDerivation (h : R⸨X⸩) : LieDerivation R E E :=
  ofTwoCocycle.derivation c (vectorFieldDerivation R L h) fun u v ↦ by
    simp only [twoCocycleOfBilinear_coe, twoCochainOfBilinear_apply_apply, ← map_add,
      residuePairing_vectorFieldDerivation_add, map_zero]

/-- In product coordinates the lift acts by `h d/dt` on the current and kills the scalar. -/
@[simp]
theorem vectorFieldExtensionDerivation_ofProd (h : R⸨X⸩) (u : C)
    (z : TrivialLieModule R C R) :
    vectorFieldExtensionDerivation Φ hΦ hΦs h (ofProd c (u, z)) =
      ofProd c (vectorFieldDerivation R L h u, 0) :=
  ofTwoCocycle.derivation_ofProd _ _ _ u z

/-- The product coordinates of the image under the lift. -/
@[simp]
theorem ofProd_symm_vectorFieldExtensionDerivation (h : R⸨X⸩) (v : E) :
    (ofProd c).symm (vectorFieldExtensionDerivation Φ hΦ hΦs h v) =
      (vectorFieldDerivation R L h ((ofProd c).symm v).1, 0) :=
  ofTwoCocycle.ofProd_symm_derivation _ _ _ v

/-- The lift lies over the vector field on currents. -/
theorem proj_vectorFieldExtensionDerivation (h : R⸨X⸩) (v : E) :
    ofTwoCocycle.proj c (vectorFieldExtensionDerivation Φ hΦ hΦs h v) =
      vectorFieldDerivation R L h (ofTwoCocycle.proj c v) :=
  ofTwoCocycle.proj_derivation _ _ _ v

/-- The lift kills the central element `K`. -/
@[simp]
theorem vectorFieldExtensionDerivation_centralElement (h : R⸨X⸩) :
    vectorFieldExtensionDerivation Φ hΦ hΦs h (centralElement c) = 0 :=
  (ofProd c).symm.injective (by simp)

end Extension

/-! ### The lift to the level enveloping algebra -/

section Enveloping

variable (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "UK" => CentralQuotient R (centralElement c) a

/-- The linear map `u ↦ ι u + ε ι(h u')` from the currents to the dual numbers over
`U(ĝ) / (ι K - a)`. -/
private def dualMap (h : R⸨X⸩) : C →ₗ[R] DualNumber UK where
  toFun u := TrivSqZeroExt.inl (envelopingι c a u) +
    TrivSqZeroExt.inr (envelopingι c a (vectorFieldDerivation R L h u))
  map_add' u v := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_smul' r u := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp

@[simp]
private theorem fst_dualMap (h : R⸨X⸩) (u : C) :
    (dualMap Φ hΦ hΦs a h u).fst = envelopingι c a u := by
  simp [dualMap]

@[simp]
private theorem snd_dualMap (h : R⸨X⸩) (u : C) :
    (dualMap Φ hΦ hΦs a h u).snd = envelopingι c a (vectorFieldDerivation R L h u) := by
  simp [dualMap]

/-- The map `u ↦ ι u + ε ι(h u')` satisfies the commutator relations of the currents: on
`ε`-components the residue terms cancel because `h d/dt` is skew for the residue pairing. -/
private theorem dualMap_mul_sub_mul (h : R⸨X⸩) (u v : C) :
    dualMap Φ hΦ hΦs a h u * dualMap Φ hΦ hΦs a h v -
        dualMap Φ hΦ hΦs a h v * dualMap Φ hΦ hΦs a h u =
      dualMap Φ hΦ hΦs a h ⁅u, v⁆ +
        algebraMap R (DualNumber UK) (a * residuePairing R L Φ u v) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · simp only [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul, fst_dualMap, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_inl, envelopingι_mul_sub_mul,
      twoCocycleOfBilinear_coe, twoCochainOfBilinear_apply_apply, LinearEquiv.apply_symm_apply]
  · -- The residue terms of the two commutators cancel since `h d/dt` is skew for the pairing.
    have hres : algebraMap R UK (a * residuePairing R L Φ u (vectorFieldDerivation R L h v)) +
        algebraMap R UK (a * residuePairing R L Φ (vectorFieldDerivation R L h u) v) = 0 := by
      rw [← map_add, ← mul_add, add_comm, residuePairing_vectorFieldDerivation_add, mul_zero,
        map_zero]
    simp only [TrivSqZeroExt.snd_sub, DualNumber.snd_mul, fst_dualMap, snd_dualMap,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl, add_zero,
      LieDerivation.apply_lie_eq_add, map_add]
    have h₁ := envelopingι_mul_sub_mul c a u (vectorFieldDerivation R L h v)
    have h₂ := envelopingι_mul_sub_mul c a (vectorFieldDerivation R L h u) v
    simp only [twoCocycleOfBilinear_coe, twoCochainOfBilinear_apply_apply,
      LinearEquiv.apply_symm_apply] at h₁ h₂
    linear_combination (norm := abel) h₁ + h₂ + hres

/-- The algebra morphism `U(ĝ) / (ι K - a) → (U(ĝ) / (ι K - a))[ε]` lifting
`u ↦ ι u + ε ι(h u')`. -/
private def dualAlgHom (h : R⸨X⸩) : UK →ₐ[R] DualNumber UK :=
  liftOfCurrents Φ hΦ hΦs a (dualMap Φ hΦ hΦs a h) (dualMap_mul_sub_mul Φ hΦ hΦs a h)

/-- The first component of `dualAlgHom` is the identity. -/
@[simp]
private theorem fst_dualAlgHom (h : R⸨X⸩) (x : UK) : (dualAlgHom Φ hΦ hΦs a h x).fst = x := by
  have hid : (TrivSqZeroExt.fstHom R UK UK).comp (dualAlgHom Φ hΦ hΦs a h) = AlgHom.id R UK :=
    algHom_ext_envelopingι c a fun u ↦ by simp [dualAlgHom]
  exact AlgHom.congr_fun hid x

/-- **The vector field `h d/dt` on the level enveloping algebra**: the derivation of
`U(ĝ) / (ι K - a)` acting by `ι u ↦ ι(h u')` on the current generators, for every central value
`a`, including `a = 0`. It is the unique such derivation by
`LieAlgebra.ofTwoCocycle.derivation_ext_envelopingι`. -/
def vectorFieldEnvelopingDerivation (h : R⸨X⸩) : derivationLieAlgebra R UK :=
  ⟨{ toFun x := (dualAlgHom Φ hΦ hΦs a h x).snd
     map_add' x y := by rw [map_add, TrivSqZeroExt.snd_add]
     map_smul' r x := by rw [RingHom.id_apply, map_smul, TrivSqZeroExt.snd_smul] },
    mem_derivationLieAlgebra.2 fun x y ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, DualNumber.snd_mul, fst_dualAlgHom]
      rw [add_comm]⟩

-- The underlying map of the lift, spelled out so that the lemmas below rewrite with it rather than
-- relying on the subtype coercion of `vectorFieldEnvelopingDerivation` to unfold.
private theorem vectorFieldEnvelopingDerivation_apply (h : R⸨X⸩) (x : UK) :
    (vectorFieldEnvelopingDerivation Φ hΦ hΦs a h : Module.End R UK) x =
      (dualAlgHom Φ hΦ hΦs a h x).snd :=
  (rfl)

/-- **The lift acts by `h d/dt` on the current generators**: `ι u ↦ ι(h u')`. -/
@[simp]
theorem vectorFieldEnvelopingDerivation_envelopingι (h : R⸨X⸩) (u : C) :
    (vectorFieldEnvelopingDerivation Φ hΦ hΦs a h : Module.End R UK) (envelopingι c a u) =
      envelopingι c a (vectorFieldDerivation R L h u) := by
  rw [vectorFieldEnvelopingDerivation_apply]
  simp [dualAlgHom]

/-- The lift to the enveloping algebra extends the lift to the residue central extension. -/
theorem vectorFieldEnvelopingDerivation_ι (h : R⸨X⸩) (x : ofTwoCocycle c) :
    (vectorFieldEnvelopingDerivation Φ hΦ hΦs a h : Module.End R UK)
        (CentralQuotient.ι (centralElement c) a x) =
      CentralQuotient.ι (centralElement c) a
        (vectorFieldExtensionDerivation Φ hΦ hΦs h x) := by
  obtain ⟨⟨u, z⟩, rfl⟩ := (ofProd c).surjective x
  rw [ι_ofProd, map_add, vectorFieldEnvelopingDerivation_envelopingι,
    vectorFieldExtensionDerivation_ofProd, ι_ofProd, Algebra.algebraMap_eq_smul_one, map_smul,
    derivationLieAlgebra.apply_one_eq_zero, smul_zero, map_zero, mul_zero, map_zero]

/-- **Vector fields of positive order preserve the left ideals.** If `h` has order at least one,
for instance for the degree derivation `t d/dt`, the lift carries each `I_N = U · ι(a_N)` into
itself. -/
theorem vectorFieldEnvelopingDerivation_mem_orderLeftIdeal {h : R⸨X⸩}
    (hh : (1 : WithTop ℤ) ≤ h.orderTop) {N : ℤ} {x : UK} (hx : x ∈ orderLeftIdeal Φ hΦ hΦs a N) :
    (vectorFieldEnvelopingDerivation Φ hΦ hΦs a h : Module.End R UK) x ∈
      orderLeftIdeal Φ hΦ hΦs a N := by
  rw [orderLeftIdeal_def] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    rw [vectorFieldEnvelopingDerivation_envelopingι]
    apply envelopingι_mem_orderLeftIdeal
    simpa using vectorFieldDerivation_mem_orderSubmodule (P := 1) (by exact_mod_cast hh) hu
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul y x hx' hx =>
    rw [smul_eq_mul, derivationLieAlgebra.leibniz]
    exact add_mem (Submodule.smul_mem _ _ (by rwa [orderLeftIdeal_def])) (Submodule.smul_mem _ y hx)

/-- **The degree derivation on the mode generators**: `[d, x_n] = n x_n`. -/
theorem vectorFieldEnvelopingDerivation_single_one_envelopingι_single_tmul (n : ℤ) (r : R)
    (x : L) :
    (vectorFieldEnvelopingDerivation Φ hΦ hΦs a (single 1 1) : Module.End R UK)
        (envelopingι c a (single n r ⊗ₜ x)) =
      n • envelopingι c a (single n r ⊗ₜ x) := by
  rw [vectorFieldEnvelopingDerivation_envelopingι, vectorFieldDerivation_single_one_single_tmul,
    map_zsmul]

end Enveloping

/-! ### Compatibility with the level comparison -/

section Level

variable {Φ Ψ : LinearMap.BilinForm R L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)
  (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm) {k : R}

local notation "cΦ" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "cΨ" => twoCocycleOfBilinear R L Ψ hΨ hΨs

/-- **Vector fields commute with the level comparison.** If `Ψ = k • Φ`, the isomorphism
`levelEnvelopingEquiv` from `U(ĝ_Ψ) / (ι K - 1)` to `U(ĝ_Φ) / (ι K - k)` intertwines the lifts of
every vector field `h d/dt`, in particular of the degree derivation, for every `k`, including
`k = 0`. -/
theorem levelEnvelopingEquiv_vectorFieldEnvelopingDerivation (h : Ψ = k • Φ) (f : R⸨X⸩)
    (x : CentralQuotient R (centralElement cΨ) 1) :
    levelEnvelopingEquiv hΦ hΦs hΨ hΨs h
        ((vectorFieldEnvelopingDerivation Ψ hΨ hΨs 1 f :
          Module.End R (CentralQuotient R (centralElement cΨ) 1)) x) =
      (vectorFieldEnvelopingDerivation Φ hΦ hΦs k f :
          Module.End R (CentralQuotient R (centralElement cΦ) k))
        (levelEnvelopingEquiv hΦ hΦs hΨ hΨs h x) := by
  let e := levelEnvelopingEquiv hΦ hΦs hΨ hΨs h
  -- Conjugating the lift for `Φ` by the comparison gives a derivation for `Ψ` with the same values
  -- on the current generators.
  have hconj : derivationLieAlgebraCongr e.symm.toLinearEquiv (fun x y ↦ map_mul e.symm x y)
      (vectorFieldEnvelopingDerivation Φ hΦ hΦs k f) =
        vectorFieldEnvelopingDerivation Ψ hΨ hΨs 1 f :=
    derivation_ext_envelopingι cΨ 1 fun u ↦ by
      simp [e, derivationLieAlgebraCongr_apply]
  rw [← hconj]
  simp [e]

end Level

end TauCeti.CurrentAlgebra

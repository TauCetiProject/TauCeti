/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.FieldTheory.FunctionField.Belyi.Model
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.GaloisDescent
public import TauCeti.FieldTheory.RatFunc.Transcendental
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.FieldTheory.FunctionField.Belyi.BaseChange

/-!
# Weil descent of algebraic Belyi pairs

Let `L / K` be a Galois extension of fields of characteristic zero, finite or infinite, and let
`X = (F, t)` be an algebraic Belyi pair over `L`. A **descent datum** for `X` relative to `K` is a
family of isomorphisms of pairs `f_σ : X^σ ≃ X`, one for each `σ ∈ Gal(L/K)`, from the conjugate
of `X` along `σ` to `X`, satisfying the cocycle condition `f_{στ} = f_σ ∘ σ(f_τ)`. The datum is
**continuous** (or **discrete**, `TauCeti.AlgebraicBelyiPair.DescentDatum.IsContinuous`) when every
element of `F` has an open stabilizer in `Gal(L/K)` for the Krull topology, equivalently when each
orbit map `σ ↦ f_σ(x)` is locally constant on `Gal(L/K)`. Over a finite extension `L / K` the Krull
topology is discrete, so every descent datum is continuous automatically. Over an infinite Galois
extension such as `L = AlgebraicClosure ℚ` over `ℚ`, continuity cannot be omitted: any
discontinuous quadratic character `χ : Gal(L/ℚ) → {±1}` defines a cocycle `z ↦ χ(σ) z` on
`(L(z), z²)` whose fixed field is `ℚ(z²)` rather than a degree-two extension of `ℚ(z²)`.

All conjugates of `X` have the same underlying field `F`, so each `f_σ` is a ring automorphism of
`F`. It acts on the constants `L` by `σ` and fixes `t`, and the cocycle condition says that
`σ ↦ f_σ` is a group homomorphism (`TauCeti.AlgebraicBelyiPair.DescentDatum.semilinearAction`).
Continuous Galois descent along this semilinear action (`TauCeti.GaloisDescent`) shows that its
fixed field `F₀` has exact constant field `K`, that `L ⊗[K] F₀ ≃ F`, and that `F` is the
compositum `F₀ · L`. Since `t` is fixed, it lies in `F₀`, and the base-change comparison of Belyi
pairs (`TauCeti.isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top`) shows that `F₀` over `K(t)`
is an algebraic Belyi pair of the same degree
(`TauCeti.GaloisDescent.isAlgebraicBelyiPair_fixedField_iff_of_isOpen`). Embedded in `F` as the
fixed field, the descended pair is a model of `X` over `K` in the sense of
`TauCeti.AlgebraicBelyiPair.Model` (`TauCeti.AlgebraicBelyiPair.DescentDatum.model`). Conversely,
every model `M` of `X` over `K` induces a continuous descent datum
(`TauCeti.AlgebraicBelyiPair.Model.descentDatum`), yielding **Weil's criterion**: `X` has a model
over `K` if and only if it admits a continuous descent datum relative to `K`
(`TauCeti.AlgebraicBelyiPair.nonempty_model_iff_exists_isContinuous`).

When `X` already has a model `M₀` over a finite intermediate extension `E₀ / K` inside `L`,
continuity of a descent datum is equivalent to the existence of an open subgroup of `Gal(L/E₀)` —
or, when `L / K` is normal, the fixing subgroup of a finite normal intermediate extension `E / K`
containing `E₀` — that fixes the embedded model `M₀` pointwise
(`TauCeti.AlgebraicBelyiPair.DescentDatum.isContinuous_iff_exists_openSubgroup_fixes_embedding`,
`TauCeti.AlgebraicBelyiPair.DescentDatum.isContinuous_iff_exists_normal_fixes_embedding`).

## Main definitions

* `TauCeti.AlgebraicBelyiPair.DescentDatum`: a descent datum for an algebraic Belyi pair over `L`
  relative to `K`.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.IsContinuous`: continuity (openness of point
  stabilizers in the Krull topology) of a descent datum, automatic when `L / K` is finite.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.semilinearAction`: the semilinear action of `Gal(L/K)`
  on the function field given by a descent datum.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.descend`: the descended algebraic Belyi pair over `K` of
  a continuous descent datum.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.baseChangeEquiv`: the base-change isomorphism
  `L ⊗[K] F₀ ≃ F`.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.model`: the descended pair as a model of `X` over `K`.
* `TauCeti.AlgebraicBelyiPair.Model.descentDatum`: the continuous descent datum induced by a model
  of `X` over `K`.

## Main results

* `TauCeti.GaloisDescent.isAlgebraicBelyiPair_fixedField_iff_of_isOpen` and
  `TauCeti.GaloisDescent.isAlgebraicBelyiPair_fixedField_iff`: the fixed field of a continuous
  semilinear action fixing `t` is an algebraic Belyi pair over `K` if and only if `F` is one over
  `L`.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.isContinuous_iff_isLocallyConstant`: continuity is
  equivalent to local constancy of each orbit map `σ ↦ f_σ(x)` on `Gal(L/K)`.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.isContinuous_iff_exists_openSubgroup_fixes_embedding`
  and `TauCeti.AlgebraicBelyiPair.DescentDatum.isContinuous_iff_exists_normal_fixes_embedding`:
  finite-level criteria for continuity relative to a model over a finite extension of `K`.
* `TauCeti.AlgebraicBelyiPair.DescentDatum.isDefinedOver_mk`: **effectiveness**, a pair with a
  continuous descent datum relative to `K` is defined over `K`.
* `TauCeti.AlgebraicBelyiPair.nonempty_model_iff_exists_isContinuous` and
  `TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_mk_iff_exists_isContinuous`: **Weil's
  criterion**, a pair is defined over `K` if and only if it admits a continuous descent datum
  relative to `K`.

## References

* A. Weil, *The field of definition of a variety*, American Journal of Mathematics 78 (1956),
  509–524.
* J.-M. Couveignes, *Calcul et rationalité de fonctions de Belyi en genre 0*, Annales de
  l'Institut Fourier 44 (1994), Théorème 3 (critère de Weil).
* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  (1.9) Theorem and (1.10) Lemma.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter X, §2, Proposition 3, for discrete
  semilinear Galois descent.
-/

public section

open IntermediateField

open scoped TensorProduct

universe u

namespace TauCeti

/-! ### Descent along a semilinear action -/

namespace GaloisDescent

variable {K L F : Type*} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F] [Algebra L F]
  [IsScalarTower K L F] [Algebra (RatFunc L) F] [IsScalarTower L (RatFunc L) F]
  [IsGalois K L] {ρ : (L ≃ₐ[K] L) →* (F ≃ₐ[K] F)}
  [Algebra (RatFunc K) (fixedField ρ.range)] [IsScalarTower K (RatFunc K) (fixedField ρ.range)]

/-- **Belyi pairs descend along continuous semilinear actions.** Let `ρ` be a continuous
semilinear action of `Gal(L/K)` on a field `F` finite over `L(t)`, for a Galois extension `L / K`
of fields of characteristic zero, and let the variable of `K(t)` act on the fixed field `F₀` of
`ρ` as the variable of `L(t)` acts on `F`. Then `F₀` over `K(t)` is an algebraic Belyi pair
exactly when `F` over `L(t)` is one. -/
theorem isAlgebraicBelyiPair_fixedField_iff_of_isOpen [CharZero K] [CharZero L]
    [FiniteDimensional (RatFunc L) F] [FiniteDimensional (RatFunc K) (fixedField ρ.range)]
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hopen : ∀ x : F, IsOpen {σ : L ≃ₐ[K] L | ρ σ x = x})
    (hX : algebraMap (fixedField ρ.range) F (algebraMap (RatFunc K) _ RatFunc.X) =
      algebraMap (RatFunc L) F RatFunc.X) :
    IsAlgebraicBelyiPair K (fixedField ρ.range) ↔ IsAlgebraicBelyiPair L F := by
  have hcomp := constantCompositum_fixedField_eq_top_of_isOpen hρ hopen
  exact ⟨fun h ↦ (isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top
      h.isIntegrallyClosedIn hcomp hX).mpr h,
    fun h ↦ (isAlgebraicBelyiPair_iff_of_constantCompositum_eq_top
      (isIntegrallyClosedIn_fixedField hρ h.isIntegrallyClosedIn) hcomp hX).mp h⟩

/-- **Belyi pairs descend along semilinear actions of finite Galois groups.** Let `ρ` be a
semilinear action of `Gal(L/K)` on a field `F` finite over `L(t)`, for a finite Galois extension
`L / K` of fields of characteristic zero, and let the variable of `K(t)` act on the fixed field
`F₀` of `ρ` as the variable of `L(t)` acts on `F`. Then `F₀` over `K(t)` is an algebraic Belyi
pair exactly when `F` over `L(t)` is one. -/
theorem isAlgebraicBelyiPair_fixedField_iff [FiniteDimensional K L] [CharZero K] [CharZero L]
    [FiniteDimensional (RatFunc L) F] [FiniteDimensional (RatFunc K) (fixedField ρ.range)]
    (hρ : ∀ σ a, ρ σ (algebraMap L F a) = algebraMap L F (σ a))
    (hX : algebraMap (fixedField ρ.range) F (algebraMap (RatFunc K) _ RatFunc.X) =
      algebraMap (RatFunc L) F RatFunc.X) :
    IsAlgebraicBelyiPair K (fixedField ρ.range) ↔ IsAlgebraicBelyiPair L F :=
  isAlgebraicBelyiPair_fixedField_iff_of_isOpen hρ (fun _ ↦ isOpen_discrete _) hX

end GaloisDescent

/-! ### Descent data and continuity -/

namespace AlgebraicBelyiPair

variable {K L : Type u} [Field K] [Field L] [CharZero L] [Algebra K L]

variable (K) in
/-- A **descent datum** for an algebraic Belyi pair `X` over `L` relative to a subfield `K`: for
each `σ ∈ Gal(L/K)` an isomorphism of pairs `f_σ : X^σ ≃ X` from the conjugate of `X` along `σ`,
satisfying the cocycle condition `f_{στ} = f_σ ∘ σ(f_τ)`.

All conjugates of `X` have the underlying field of `X`, and the conjugate `σ(f_τ)` of `f_τ` is
`f_τ` on that field (`TauCeti.AlgebraicBelyiPair.conjAlgEquiv_conjRingEquiv`), so the cocycle
condition is stated there, as `f_{στ}(x) = f_σ(f_τ(x))`. -/
@[ext]
structure DescentDatum (X : AlgebraicBelyiPair L) where
  /-- The isomorphism `f_σ` from the conjugate of the pair along `σ` to the pair. -/
  iso (σ : L ≃ₐ[K] L) : X.conj (σ : L ≃+* L) ≃ₐ[RatFunc L] X
  /-- The cocycle condition `f_{στ} = f_σ ∘ σ(f_τ)`, on the common underlying field. -/
  iso_mul (σ τ : L ≃ₐ[K] L) (x : X) :
    iso (σ * τ) (conjRingEquiv _ X x) = iso σ (conjRingEquiv _ X (iso τ (conjRingEquiv _ X x)))

namespace DescentDatum

section Continuity

variable {X : AlgebraicBelyiPair L} (D : DescentDatum K X)

/-- The ring automorphism of the function field of `X` induced by `f_σ`. -/
private noncomputable def ringEquiv (σ : L ≃ₐ[K] L) : X ≃+* X :=
  (conjRingEquiv (σ : L ≃+* L) X).trans (D.iso σ).toRingEquiv

private theorem ringEquiv_apply (σ : L ≃ₐ[K] L) (x : X) :
    D.ringEquiv σ x = D.iso σ (conjRingEquiv (σ : L ≃+* L) X x) :=
  (rfl)

/-- The cocycle condition forces `f_1` to act as the identity on `X`. -/
@[simp]
theorem iso_one_conjRingEquiv (x : X) :
    D.iso 1 (conjRingEquiv ((1 : L ≃ₐ[K] L) : L ≃+* L) X x) = x := by
  let φ : (L ≃ₐ[K] L) →* Equiv.Perm X :=
    MonoidHom.mk' (fun σ ↦ (D.ringEquiv σ).toEquiv) fun σ τ ↦ Equiv.ext (D.iso_mul σ τ)
  exact Equiv.congr_fun φ.map_one x

private theorem ringEquiv_algebraMap_ratFunc (σ : L ≃ₐ[K] L) (r : RatFunc L) :
    D.ringEquiv σ (algebraMap (RatFunc L) X r) =
      algebraMap (RatFunc L) X (RatFunc.mapRingEquiv (σ : L ≃+* L) r) := by
  rw [ringEquiv_apply, conjRingEquiv_algebraMap_ratFunc, AlgEquiv.commutes]

private theorem ringEquiv_algebraMap (σ : L ≃ₐ[K] L) (a : L) :
    D.ringEquiv σ (algebraMap L X a) = algebraMap L X (σ a) := by
  rw [IsScalarTower.algebraMap_apply L (RatFunc L) X, D.ringEquiv_algebraMap_ratFunc,
    RatFunc.mapRingEquiv_algebraMap_const, AlgEquiv.coe_toRingEquiv,
    ← IsScalarTower.algebraMap_apply]

/-- The subgroup of `Gal(L/K)` fixing an element `x : X` under the descent datum. -/
private def stabSubgroup (x : X) : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | D.iso σ (conjRingEquiv (σ : L ≃+* L) X x) = x}
  one_mem' := D.iso_one_conjRingEquiv x
  mul_mem' {σ τ} hσ hτ := by
    change D.iso (σ * τ) (conjRingEquiv _ X x) = x
    rw [D.iso_mul, hτ, hσ]
  inv_mem' {σ} hσ := by
    change D.iso σ⁻¹ (conjRingEquiv _ X x) = x
    have h := D.iso_mul σ⁻¹ σ x
    rw [inv_mul_cancel, D.iso_one_conjRingEquiv, hσ] at h
    exact h.symm

private theorem isLocallyConstant_iff_isOpen_stabSubgroup (x : X) :
    (IsLocallyConstant fun σ : L ≃ₐ[K] L ↦ D.iso σ (conjRingEquiv (σ : L ≃+* L) X x)) ↔
      IsOpen (D.stabSubgroup x : Set (L ≃ₐ[K] L)) := by
  rw [IsLocallyConstant.iff_isOpen_fiber_apply]
  refine ⟨fun h ↦ ?_, fun h τ ↦ ?_⟩
  · have h1 := h 1
    rw [D.iso_one_conjRingEquiv] at h1
    exact h1
  · have hpre : ((fun σ : L ≃ₐ[K] L ↦ D.iso σ (conjRingEquiv (σ : L ≃+* L) X x)) ⁻¹'
        {D.iso τ (conjRingEquiv (τ : L ≃+* L) X x)}) =
        (fun σ : L ≃ₐ[K] L ↦ τ⁻¹ * σ) ⁻¹' (D.stabSubgroup x : Set (L ≃ₐ[K] L)) := by
      refine Set.ext fun σ ↦ ⟨fun hσ ↦ ?_, fun hσ ↦ ?_⟩
      · change D.iso (τ⁻¹ * σ) (conjRingEquiv _ X x) = x
        change D.iso σ (conjRingEquiv _ X x) = D.iso τ (conjRingEquiv _ X x) at hσ
        rw [D.iso_mul, hσ, ← D.iso_mul, inv_mul_cancel, D.iso_one_conjRingEquiv]
      · change D.iso σ (conjRingEquiv _ X x) = D.iso τ (conjRingEquiv _ X x)
        change D.iso (τ⁻¹ * σ) (conjRingEquiv _ X x) = x at hσ
        have h' := D.iso_mul τ (τ⁻¹ * σ) x
        rwa [mul_inv_cancel_left, hσ] at h'
    rw [hpre]
    exact h.preimage (continuous_const.mul continuous_id)

/-- A descent datum `D` for `X` relative to `K` is **continuous** (or **discrete**) if for every
element `x` of the function field of `X`, the subgroup of `Gal(L/K)` fixing `x` under `D` is open
in the Krull topology; equivalently `σ ↦ f_σ(x)` is locally constant on `Gal(L/K)`
(`TauCeti.AlgebraicBelyiPair.DescentDatum.isContinuous_iff_isLocallyConstant`).

Over a finite extension `L / K` the Krull topology is discrete, so every descent datum is
continuous automatically. -/
class IsContinuous (D : DescentDatum K X) : Prop where
  /-- Every element of `X` has open stabilizer in `Gal(L/K)` under the descent datum. -/
  isOpen_iso_eq (x : X) :
    IsOpen {σ : L ≃ₐ[K] L | D.iso σ (conjRingEquiv (σ : L ≃+* L) X x) = x}

theorem isContinuous_iff :
    D.IsContinuous ↔
      ∀ x : X, IsOpen {σ : L ≃ₐ[K] L | D.iso σ (conjRingEquiv (σ : L ≃+* L) X x) = x} :=
  ⟨fun h ↦ h.isOpen_iso_eq, fun h ↦ ⟨h⟩⟩

/-- Over a finite extension the Krull topology is discrete, so every descent datum is continuous. -/
instance [FiniteDimensional K L] : D.IsContinuous :=
  ⟨fun _ ↦ isOpen_discrete _⟩

/-- A descent datum is continuous if and only if for every element `x` of `X`, the orbit map
`σ ↦ f_σ(x)` on `Gal(L/K)` is locally constant. -/
theorem isContinuous_iff_isLocallyConstant :
    D.IsContinuous ↔
      ∀ x : X, IsLocallyConstant fun σ : L ≃ₐ[K] L ↦ D.iso σ (conjRingEquiv (σ : L ≃+* L) X x) :=
  D.isContinuous_iff.trans <|
    forall_congr' fun x ↦ (D.isLocallyConstant_iff_isOpen_stabSubgroup x).symm

/-- When `L / K` is algebraic, the elements of `X` with open stabilizer under `D` form an
`L`-subfield of `X`. -/
private def openStabilizerSubfield [Algebra.IsAlgebraic K L] : IntermediateField L X where
  carrier := {x : X | IsOpen (D.stabSubgroup x : Set (L ≃ₐ[K] L))}
  algebraMap_mem' c := by
    change IsOpen (D.stabSubgroup (algebraMap L X c) : Set (L ≃ₐ[K] L))
    have heq : (D.stabSubgroup (algebraMap L X c) : Set (L ≃ₐ[K] L)) =
        MulAction.stabilizer (L ≃ₐ[K] L) c := by
      ext σ
      change D.ringEquiv σ (algebraMap L X c) = algebraMap L X c ↔ σ c = c
      rw [D.ringEquiv_algebraMap, (algebraMap L X).injective.eq_iff]
    rw [heq]
    exact stabilizer_isOpen_of_isIntegral c
  add_mem' {x y} hx hy :=
    Subgroup.isOpen_mono (H₁ := D.stabSubgroup x ⊓ D.stabSubgroup y)
      (fun σ ⟨h₁, h₂⟩ ↦ by
        change D.ringEquiv σ (x + y) = x + y
        rw [map_add]
        exact congrArg₂ (· + ·) h₁ h₂)
      (hx.inter hy)
  zero_mem' :=
    Subgroup.isOpen_mono (H₁ := ⊤) (fun σ _ ↦ map_zero (D.ringEquiv σ)) isOpen_univ
  mul_mem' {x y} hx hy :=
    Subgroup.isOpen_mono (H₁ := D.stabSubgroup x ⊓ D.stabSubgroup y)
      (fun σ ⟨h₁, h₂⟩ ↦ by
        change D.ringEquiv σ (x * y) = x * y
        rw [map_mul]
        exact congrArg₂ (· * ·) h₁ h₂)
      (hx.inter hy)
  one_mem' :=
    Subgroup.isOpen_mono (H₁ := ⊤) (fun σ _ ↦ map_one (D.ringEquiv σ)) isOpen_univ
  inv_mem' {x} hx :=
    Subgroup.isOpen_mono (H₁ := D.stabSubgroup x)
      (fun σ h ↦ by
        change D.ringEquiv σ x⁻¹ = x⁻¹
        rw [map_inv₀]
        exact congrArg Inv.inv h)
      hx

/-- Over an algebraic extension `L / K`, a descent datum is continuous as soon as the stabilizers
of a set of `L`-field generators of `X` are open. -/
theorem IsContinuous.of_adjoin_eq_top [Algebra.IsAlgebraic K L] {S : Set X}
    (hS : IntermediateField.adjoin L S = ⊤)
    (hopen : ∀ x ∈ S, IsOpen {σ : L ≃ₐ[K] L | D.iso σ (conjRingEquiv (σ : L ≃+* L) X x) = x}) :
    D.IsContinuous := by
  refine ⟨fun x ↦ ?_⟩
  have htop : D.openStabilizerSubfield = ⊤ :=
    eq_top_iff.mpr (hS ▸ IntermediateField.adjoin_le_iff.mpr hopen)
  exact (htop.symm ▸ mem_top : x ∈ D.openStabilizerSubfield)

/-- Relative to any model `M₀` of `X` over a subfield `E₀` of `L` with `L / K` algebraic, a
descent datum is continuous if and only if each orbit map `σ ↦ f_σ(y)` on elements `y` of `M₀` is
locally constant on `Gal(L/K)`. -/
theorem isContinuous_iff_isLocallyConstant_embedding
    {E₀ : Type*} [Field E₀] [CharZero E₀] [Algebra E₀ L] [Algebra.IsAlgebraic K L]
    (M₀ : Model E₀ X) :
    D.IsContinuous ↔
      ∀ y : M₀.pair,
        IsLocallyConstant fun σ : L ≃ₐ[K] L ↦
          D.iso σ (conjRingEquiv (σ : L ≃+* L) X (M₀.embedding y)) := by
  refine ⟨fun h y ↦ (D.isContinuous_iff_isLocallyConstant.mp h) (M₀.embedding y), fun h ↦ ?_⟩
  refine IsContinuous.of_adjoin_eq_top D M₀.adjoin_range_embedding ?_
  rintro _ ⟨y, rfl⟩
  exact (D.isLocallyConstant_iff_isOpen_stabSubgroup (M₀.embedding y)).mp (h y)

/-- If an open subgroup `U` of `Gal(L/K)` fixes the image of a model `M₀` of `X` pointwise under
`D`, with `L / K` algebraic, then `D` is continuous. -/
theorem IsContinuous.of_openSubgroup_fixes_embedding
    {E₀ : Type*} [Field E₀] [CharZero E₀] [Algebra E₀ L] [Algebra.IsAlgebraic K L]
    (M₀ : Model E₀ X) {U : Subgroup (L ≃ₐ[K] L)} (hU : IsOpen (U : Set (L ≃ₐ[K] L)))
    (hfix : ∀ σ ∈ U, ∀ y : M₀.pair,
      D.iso σ (conjRingEquiv (σ : L ≃+* L) X (M₀.embedding y)) = M₀.embedding y) :
    D.IsContinuous := by
  refine IsContinuous.of_adjoin_eq_top D M₀.adjoin_range_embedding ?_
  rintro _ ⟨y, rfl⟩
  exact Subgroup.isOpen_mono (H₁ := U) (H₂ := D.stabSubgroup (M₀.embedding y))
    (fun σ hσ ↦ hfix σ hσ y) hU

/-- **Open-subgroup criterion for continuity.** Relative to a model `M₀` of `X` over a finite
intermediate extension `E₀ / K` inside an algebraic extension `L / K`, a descent datum `D` is
continuous if and only if some open subgroup `U ≤ Gal(L/E₀)` of `Gal(L/K)` fixes the embedded
model `M₀` pointwise under `D`. -/
theorem isContinuous_iff_exists_openSubgroup_fixes_embedding
    [Algebra.IsAlgebraic K L] (E₀ : IntermediateField K L) [FiniteDimensional K E₀]
    (M₀ : Model E₀ X) :
    D.IsContinuous ↔
      ∃ U : Subgroup (L ≃ₐ[K] L), IsOpen (U : Set (L ≃ₐ[K] L)) ∧ U ≤ E₀.fixingSubgroup ∧
        ∀ σ ∈ U, ∀ y : M₀.pair,
          D.iso σ (conjRingEquiv (σ : L ≃+* L) X (M₀.embedding y)) = M₀.embedding y := by
  refine ⟨fun h ↦ ?_,
    fun ⟨U, hU, _, hfix⟩ ↦ IsContinuous.of_openSubgroup_fixes_embedding D M₀ hU hfix⟩
  have hff : IsFunctionField E₀ M₀.pair := isFunctionField_iff_functionField.mpr inferInstance
  have := hff.essFiniteType
  obtain ⟨S, hS⟩ := fg_top E₀ M₀.pair
  let U : Subgroup (L ≃ₐ[K] L) :=
    { carrier := {σ | σ ∈ E₀.fixingSubgroup ∧ ∀ s ∈ S, σ ∈ D.stabSubgroup (M₀.embedding s)}
      one_mem' := ⟨E₀.fixingSubgroup.one_mem,
        fun s _ ↦ (D.stabSubgroup (M₀.embedding s)).one_mem⟩
      mul_mem' ha hb := ⟨E₀.fixingSubgroup.mul_mem ha.1 hb.1,
        fun s hs ↦ (D.stabSubgroup (M₀.embedding s)).mul_mem (ha.2 s hs) (hb.2 s hs)⟩
      inv_mem' ha := ⟨E₀.fixingSubgroup.inv_mem ha.1,
        fun s hs ↦ (D.stabSubgroup (M₀.embedding s)).inv_mem (ha.2 s hs)⟩ }
  have hU_open : IsOpen (U : Set (L ≃ₐ[K] L)) := by
    have hU_eq : (U : Set (L ≃ₐ[K] L)) =
        (E₀.fixingSubgroup : Set (L ≃ₐ[K] L)) ∩
          ⋂ s ∈ S, (D.stabSubgroup (M₀.embedding s) : Set (L ≃ₐ[K] L)) := by
      ext
      simp [U]
    rw [hU_eq]
    exact E₀.fixingSubgroup_isOpen.inter
      (S.finite_toSet.isOpen_biInter fun s _ ↦ h.isOpen_iso_eq (M₀.embedding s))
  refine ⟨U, hU_open, fun _ hσ ↦ hσ.1, fun σ hσ y ↦ ?_⟩
  have hσE : σ ∈ E₀.fixingSubgroup := hσ.1
  have hσS : ∀ s ∈ S, D.ringEquiv σ (M₀.embedding s) = M₀.embedding s := hσ.2
  -- The elements of `M₀.pair` fixed by `D.ringEquiv σ` form an `E₀`-subfield containing `S`.
  let Fσ : IntermediateField E₀ M₀.pair :=
    { carrier := {z : M₀.pair | D.ringEquiv σ (M₀.embedding z) = M₀.embedding z}
      algebraMap_mem' c := by
        change D.ringEquiv σ (M₀.embedding (algebraMap E₀ M₀.pair c)) = _
        rw [M₀.embedding_algebraMap, D.ringEquiv_algebraMap, IntermediateField.algebraMap_apply,
          (mem_fixingSubgroup_iff E₀ σ).mp hσE c c.2]
      add_mem' {a b} ha hb := by
        change D.ringEquiv σ (M₀.embedding (a + b)) = M₀.embedding (a + b)
        rw [map_add, map_add, ha, hb]
      zero_mem' := by simp
      mul_mem' {a b} ha hb := by
        change D.ringEquiv σ (M₀.embedding (a * b)) = M₀.embedding (a * b)
        rw [map_mul, map_mul, ha, hb]
      one_mem' := by simp
      inv_mem' {a} ha := by
        change D.ringEquiv σ (M₀.embedding a⁻¹) = M₀.embedding a⁻¹
        rw [map_inv₀, map_inv₀, ha] }
  have hFσ : Fσ = ⊤ := eq_top_iff.mpr (hS ▸ adjoin_le_iff.mpr hσS)
  exact (hFσ.symm ▸ mem_top : y ∈ Fσ)

/-- **Finite-level criterion for continuity.** Relative to a model `M₀` of `X` over a finite
intermediate extension `E₀ / K` inside a normal extension `L / K`, a descent datum `D` is
continuous if and only if there is a finite normal intermediate extension `E / K` containing `E₀`
whose fixing subgroup fixes the embedded model `M₀` pointwise under `D`. -/
theorem isContinuous_iff_exists_normal_fixes_embedding [Normal K L]
    (E₀ : IntermediateField K L) [FiniteDimensional K E₀] (M₀ : Model E₀ X) :
    D.IsContinuous ↔
      ∃ E : IntermediateField K L, FiniteDimensional K E ∧ Normal K E ∧ E₀ ≤ E ∧
        ∀ σ ∈ E.fixingSubgroup, ∀ y : M₀.pair,
          D.iso σ (conjRingEquiv (σ : L ≃+* L) X (M₀.embedding y)) = M₀.embedding y := by
  rw [D.isContinuous_iff_exists_openSubgroup_fixes_embedding E₀ M₀]
  refine ⟨fun ⟨U, hU, _, hfix⟩ ↦ ?_, fun ⟨E, hE, _, hle, hfix⟩ ↦
    ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, fixingSubgroup_antitone hle, hfix⟩⟩
  obtain ⟨E₁, hE₁_fin, _, hE₁_sub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal K L (U : Set (L ≃ₐ[K] L))).mp (hU.mem_nhds U.one_mem)
  let E₀₁ : IntermediateField K L := E₀ ⊔ E₁
  let E := normalClosure K E₀₁ L
  refine ⟨E, normalClosure.is_finiteDimensional K E₀₁ L, normalClosure.normal K E₀₁ L,
    le_sup_left.trans E₀₁.le_normalClosure, fun σ hσ y ↦ hfix σ ?_ y⟩
  exact hE₁_sub (fixingSubgroup_antitone (le_sup_right.trans E₀₁.le_normalClosure) hσ)

end Continuity

section Semilinear

variable {X : AlgebraicBelyiPair L} [Algebra K X] [IsScalarTower K L X] (D : DescentDatum K X)

/-- The **semilinear action** of `Gal(L/K)` on the function field of `X` given by a descent datum:
`σ` acts by the isomorphism `f_σ`, read as an automorphism of the underlying field. It acts on the
constants `L` by `σ` (`TauCeti.AlgebraicBelyiPair.DescentDatum.semilinearAction_algebraMap`), and
the cocycle condition makes it a group homomorphism. -/
noncomputable def semilinearAction : (L ≃ₐ[K] L) →* (X ≃ₐ[K] X) :=
  MonoidHom.mk' (fun σ ↦ AlgEquiv.ofRingEquiv
    (f := (conjRingEquiv (σ : L ≃+* L) X).trans (D.iso σ).toRingEquiv) fun c ↦ by
      simp [IsScalarTower.algebraMap_apply K L X, IsScalarTower.algebraMap_apply L (RatFunc L) X])
    fun σ τ ↦ AlgEquiv.ext fun x ↦ D.iso_mul σ τ x

theorem semilinearAction_apply (σ : L ≃ₐ[K] L) (x : X) :
    D.semilinearAction σ x = D.iso σ (conjRingEquiv _ X x) :=
  (rfl)

/-- The semilinear action of a descent datum acts on `L(t)` by the coefficient map of `σ`. -/
@[simp]
theorem semilinearAction_algebraMap_ratFunc (σ : L ≃ₐ[K] L) (r : RatFunc L) :
    D.semilinearAction σ (algebraMap (RatFunc L) X r) =
      algebraMap (RatFunc L) X (RatFunc.mapRingEquiv (σ : L ≃+* L) r) :=
  D.ringEquiv_algebraMap_ratFunc σ r

/-- The semilinear action of a descent datum acts on the constants `L` by `σ`. -/
@[simp]
theorem semilinearAction_algebraMap (σ : L ≃ₐ[K] L) (a : L) :
    D.semilinearAction σ (algebraMap L X a) = algebraMap L X (σ a) :=
  D.ringEquiv_algebraMap σ a

/-- For a continuous descent datum, every element of `X` has open stabilizer under
`semilinearAction`. -/
theorem IsContinuous.isOpen_semilinearAction [D.IsContinuous] (x : X) :
    IsOpen {σ : L ≃ₐ[K] L | D.semilinearAction σ x = x} :=
  IsContinuous.isOpen_iso_eq x

/-- A descent datum is continuous if and only if each orbit map `σ ↦ D.semilinearAction σ x` on
`Gal(L/K)` is locally constant. -/
theorem isContinuous_iff_isLocallyConstant_semilinearAction :
    D.IsContinuous ↔ ∀ x : X, IsLocallyConstant (D.semilinearAction · x) :=
  D.isContinuous_iff_isLocallyConstant

/-- The Belyi function `t`, as an element of the fixed field of the semilinear action. -/
private noncomputable def gen : fixedField D.semilinearAction.range :=
  ⟨algebraMap (RatFunc L) X RatFunc.X, (mem_fixedField_iff _ _).mpr <| by
    rintro _ ⟨σ, rfl⟩
    rw [semilinearAction_algebraMap_ratFunc, RatFunc.mapRingEquiv_X]⟩

private theorem transcendental_gen : Transcendental K D.gen := by
  have ht : Transcendental L (algebraMap (RatFunc L) X RatFunc.X) :=
    (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective (RatFunc L) X)).mpr
      RatFunc.transcendental_X
  exact (transcendental_algebraMap_iff
    (algebraMap (fixedField D.semilinearAction.range) X).injective).mp (ht.of_tower_top K)

/-- With `t` acting as itself, the Belyi function of `X` is the image of the variable of `K(t)`. -/
private theorem algebraMap_gen :
    letI := ratFuncAlgebraOfTranscendental D.transcendental_gen
    algebraMap (fixedField D.semilinearAction.range) X (algebraMap (RatFunc K) _ RatFunc.X) =
      algebraMap (RatFunc L) X RatFunc.X := by
  let := ratFuncAlgebraOfTranscendental D.transcendental_gen
  rw [algebraMap_ratFuncAlgebraOfTranscendental_X]
  rfl

variable [CharZero K] [IsGalois K L] [D.IsContinuous]

/-- The **descended Belyi pair** of a continuous descent datum: the fixed field `F₀` of its
semilinear action on the function field `F` of `X`, over `K(t)` through the Belyi function `t` of
`X`, which lies in `F₀`. It is an algebraic Belyi pair over `K` whose base change to `L` is `X`
(`TauCeti.AlgebraicBelyiPair.DescentDatum.constantCompositum_descend_eq_top`,
`TauCeti.AlgebraicBelyiPair.DescentDatum.baseChangeEquiv`). -/
noncomputable def descend : AlgebraicBelyiPair K :=
  letI := ratFuncAlgebraOfTranscendental D.transcendental_gen
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental D.transcendental_gen
  haveI := GaloisDescent.finiteDimensional_ratFunc_fixedField_of_isOpen
    D.semilinearAction_algebraMap (IsContinuous.isOpen_semilinearAction D)
    X.isAlgebraicBelyiPair.isIntegrallyClosedIn D.algebraMap_gen
  { carrier := fixedField D.semilinearAction.range
    isAlgebraicBelyiPair := (GaloisDescent.isAlgebraicBelyiPair_fixedField_iff_of_isOpen
      D.semilinearAction_algebraMap (IsContinuous.isOpen_semilinearAction D)
      D.algebraMap_gen).mpr X.isAlgebraicBelyiPair }

/-- The function field of the descended pair embeds in that of `X`, as the fixed field of the
semilinear action. -/
noncomputable instance : Algebra D.descend X :=
  inferInstanceAs (Algebra (fixedField D.semilinearAction.range) X)

instance : IsScalarTower K D.descend X :=
  inferInstanceAs (IsScalarTower K (fixedField D.semilinearAction.range) X)

/-- The function field of the descended pair is the field of elements of the function field of
`X` fixed by the semilinear action. -/
theorem mem_range_algebraMap_descend_iff {x : X} :
    x ∈ Set.range (algebraMap D.descend X) ↔ ∀ σ, D.semilinearAction σ x = x := by
  refine ⟨?_, fun h ↦ ⟨⟨x, (mem_fixedField_iff _ _).mpr ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩ σ
    exact (mem_fixedField_iff _ _).mp y.2 _ ⟨σ, rfl⟩
  · rintro _ ⟨σ, rfl⟩
    exact h σ

/-- The semilinear action of a continuous descent datum fixes the function field of the descended
pair. -/
@[simp]
theorem semilinearAction_algebraMap_descend (σ : L ≃ₐ[K] L) (y : D.descend) :
    D.semilinearAction σ (algebraMap D.descend X y) = algebraMap D.descend X y :=
  D.mem_range_algebraMap_descend_iff.mp ⟨y, rfl⟩ σ

/-- **The Belyi function descends**: the Belyi function of the descended pair is that of `X`. -/
@[simp]
theorem algebraMap_descend_X :
    algebraMap D.descend X (algebraMap (RatFunc K) D.descend RatFunc.X) =
      algebraMap (RatFunc L) X RatFunc.X :=
  D.algebraMap_gen

/-- **The descended pair base-changes back**: the function field of `X` is the compositum of that
of the descended pair with `L`. -/
theorem constantCompositum_descend_eq_top : constantCompositum D.descend L X = ⊤ :=
  GaloisDescent.constantCompositum_fixedField_eq_top_of_isOpen D.semilinearAction_algebraMap
    (IsContinuous.isOpen_semilinearAction D)

/-- The descended pair has the degree of `X`. -/
@[simp]
theorem finrank_descend :
    Module.finrank (RatFunc K) D.descend = Module.finrank (RatFunc L) X := by
  let := ratFuncAlgebraOfTranscendental D.transcendental_gen
  have := isScalarTower_ratFuncAlgebraOfTranscendental D.transcendental_gen
  -- Elaborated without the expected type, whose instances are the fields of `descend`.
  have h := GaloisDescent.finrank_ratFunc_fixedField_of_isOpen D.semilinearAction_algebraMap
    (IsContinuous.isOpen_semilinearAction D) X.isAlgebraicBelyiPair.isIntegrallyClosedIn
    D.algebraMap_gen
  exact h

/-- The **base-change isomorphism** of a continuous descent datum: extending the scalars of the
function field of the descended pair from `K` to `L` recovers the function field of `X`, by
`a ⊗ y ↦ a • y`. -/
noncomputable def baseChangeEquiv : L ⊗[K] D.descend ≃ₐ[L] X :=
  GaloisDescent.fixedFieldBaseChangeEquivOfIsOpen D.semilinearAction_algebraMap
    (IsContinuous.isOpen_semilinearAction D)

@[simp]
theorem baseChangeEquiv_tmul (a : L) (y : D.descend) :
    D.baseChangeEquiv (a ⊗ₜ y) = a • algebraMap D.descend X y :=
  GaloisDescent.fixedFieldBaseChangeEquivOfIsOpen_tmul D.semilinearAction_algebraMap
    (IsContinuous.isOpen_semilinearAction D) a y

@[simp]
theorem baseChangeEquiv_symm_algebraMap (y : D.descend) :
    D.baseChangeEquiv.symm (algebraMap D.descend X y) = 1 ⊗ₜ y :=
  GaloisDescent.fixedFieldBaseChangeEquivOfIsOpen_symm_apply_coe D.semilinearAction_algebraMap
    (IsContinuous.isOpen_semilinearAction D) y

/-- **A continuous descent datum gives a model**: the descended pair, embedded in the function
field of `X` as the fixed field of the semilinear action, is a model of `X` over `K`. -/
@[expose, simps pair embedding]
noncomputable def model : Model K X where
  pair := D.descend
  embedding := algebraMap D.descend X
  embedding_algebraMap c := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K L X]
  embedding_algebraMap_X := D.algebraMap_descend_X
  adjoin_range_embedding := by
    have h := D.constantCompositum_descend_eq_top
    rw [← IntermediateField.toSubfield_inj, IntermediateField.top_toSubfield,
      constantCompositum_def, IntermediateField.adjoin_toSubfield] at h
    rw [← IntermediateField.toSubfield_inj, IntermediateField.top_toSubfield,
      IntermediateField.adjoin_toSubfield, Set.union_comm, h]

include D in
/-- **Continuous descent data are effective**: an algebraic Belyi pair with a continuous descent
datum relative to `K` is defined over `K`. -/
theorem isDefinedOver_mk : (IsoClass.mk X).IsDefinedOver K :=
  IsoClass.isDefinedOver_mk_iff.mpr ⟨D.model⟩

end Semilinear

end DescentDatum

/-! ### Descent datum of a model and Weil's criterion -/

namespace Model

/-- The **canonical descent datum** of a model `M` of `X` over `K`: each `σ ∈ Gal(L/K)` acts by
`M.conjAlgEquiv σ : X^σ ≃ X`, corresponding to `id ⊗ σ` on `M.pair ⊗[K] L`. -/
noncomputable def descentDatum [CharZero K] [Algebra.IsAlgebraic K L] {X : AlgebraicBelyiPair L}
    (M : Model K X) : DescentDatum K X where
  iso σ := M.conjAlgEquiv σ
  iso_mul σ τ x := by
    rw [conjAlgEquiv_conjRingEquiv, conjAlgEquiv_conjRingEquiv, conjAlgEquiv_conjRingEquiv,
      baseChangeAut_mul, RingEquiv.trans_apply]

@[simp]
theorem descentDatum_iso [CharZero K] [Algebra.IsAlgebraic K L] {X : AlgebraicBelyiPair L}
    (M : Model K X) (σ : L ≃ₐ[K] L) :
    M.descentDatum.iso σ = M.conjAlgEquiv σ :=
  (rfl)

/-- The descent datum induced by a model over `K` is continuous: `Gal(L/K)` fixes the embedded
model pointwise. -/
instance [CharZero K] [Algebra.IsAlgebraic K L] {X : AlgebraicBelyiPair L} (M : Model K X) :
    M.descentDatum.IsContinuous :=
  DescentDatum.IsContinuous.of_openSubgroup_fixes_embedding M.descentDatum M (U := ⊤) isOpen_univ
    fun σ _ y ↦ by simp

end Model

/-- Recovering the descent datum of the model produced by a continuous descent datum gives back the
original descent datum. -/
@[simp]
theorem DescentDatum.descentDatum_model [CharZero K] [IsGalois K L] {X : AlgebraicBelyiPair L}
    [Algebra K X] [IsScalarTower K L X] (D : DescentDatum K X) [D.IsContinuous] :
    D.model.descentDatum = D := by
  ext σ z
  obtain ⟨x, rfl⟩ := (conjRingEquiv (σ : L ≃+* L) X).surjective z
  rw [Model.descentDatum_iso, Model.conjAlgEquiv_conjRingEquiv, ← D.semilinearAction_apply]
  obtain ⟨t, rfl⟩ := D.baseChangeEquiv.surjective x
  induction t using TensorProduct.inductionOn with
  | tmul c y =>
    rw [D.baseChangeEquiv_tmul, Algebra.smul_def, map_mul, Model.baseChangeAut_algebraMap,
      map_mul, D.semilinearAction_algebraMap, D.semilinearAction_algebraMap_descend]
    have hy : D.model.baseChangeAut σ (algebraMap D.descend X y) = algebraMap D.descend X y :=
      Model.baseChangeAut_embedding D.model σ y
    rw [hy]
  | add t u ht hu =>
    simp only [map_add, ht, hu]

/-- **Weil's criterion for algebraic Belyi pairs**: over a Galois extension `L / K` of fields of
characteristic zero, an algebraic Belyi pair `X` over `L` admits a model over `K` if and only if
it admits a continuous descent datum relative to `K`. -/
theorem nonempty_model_iff_exists_isContinuous [CharZero K] [IsGalois K L]
    {X : AlgebraicBelyiPair L} :
    Nonempty (Model K X) ↔ ∃ D : DescentDatum K X, D.IsContinuous := by
  refine ⟨fun ⟨M⟩ ↦ ⟨M.descentDatum, inferInstance⟩, fun ⟨D, _⟩ ↦ ?_⟩
  let : Algebra K X := ((algebraMap L X).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L X := .of_algebraMap_eq fun _ ↦ rfl
  exact ⟨D.model⟩

/-- **Weil's criterion over a finite Galois extension**: over a finite Galois extension `L / K` of
fields of characteristic zero, an algebraic Belyi pair `X` over `L` admits a model over `K` if and
only if it admits a descent datum relative to `K`. -/
theorem nonempty_model_iff_nonempty_descentDatum [CharZero K] [FiniteDimensional K L]
    [IsGalois K L] {X : AlgebraicBelyiPair L} :
    Nonempty (Model K X) ↔ Nonempty (DescentDatum K X) := by
  rw [nonempty_model_iff_exists_isContinuous]
  exact ⟨fun ⟨D, _⟩ ↦ ⟨D⟩, fun ⟨D⟩ ↦ ⟨D, inferInstance⟩⟩

namespace IsoClass

/-- Over a Galois extension `L / K` of fields of characteristic zero, the isomorphism class of `X`
is defined over `K` if and only if `X` admits a continuous descent datum relative to `K`. -/
theorem isDefinedOver_mk_iff_exists_isContinuous [CharZero K] [IsGalois K L]
    {X : AlgebraicBelyiPair L} :
    (mk X).IsDefinedOver K ↔ ∃ D : DescentDatum K X, D.IsContinuous :=
  isDefinedOver_mk_iff.trans nonempty_model_iff_exists_isContinuous

/-- Over a finite Galois extension `L / K` of fields of characteristic zero, the isomorphism class
of `X` is defined over `K` if and only if `X` admits a descent datum relative to `K`. -/
theorem isDefinedOver_mk_iff_nonempty_descentDatum [CharZero K] [FiniteDimensional K L]
    [IsGalois K L] {X : AlgebraicBelyiPair L} :
    (mk X).IsDefinedOver K ↔ Nonempty (DescentDatum K X) :=
  isDefinedOver_mk_iff.trans nonempty_model_iff_nonempty_descentDatum

end IsoClass

end AlgebraicBelyiPair

end TauCeti

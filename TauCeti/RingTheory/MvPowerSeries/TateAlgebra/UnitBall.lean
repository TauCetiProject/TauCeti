/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.Analysis.Normed.Ring.UnitBall
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# The Gauss unit ball of a Tate algebra and its reduction

Let `K` be a nontrivially normed ultrametric field with ring of integers `𝒪[K]` and residue
field `𝓀[K]`, and let `T = K⟨X⟩` be the Tate algebra of unit-radius restricted series in the
variables `σ`. Its Gauss unit ball `T° = {f | ‖f‖ ≤ 1}` consists of the series with integral
coefficients, and is identified isometrically with the ring `𝒪[K]⟨X⟩` of restricted series over
`𝒪[K]`. Reducing coefficients modulo the maximal ideal of `𝒪[K]` sends a series in `T°` to a
polynomial, because only finitely many of its coefficients have norm one. This gives a surjective
ring homomorphism `T° → 𝓀[K][X]` whose kernel is `T°° = {f | ‖f‖ < 1}`, hence
`T° ⧸ T°° ≃ 𝓀[K][X]`. The unit ball is also the subring of power-bounded elements of `T`.

Reduction is the basic tool for transferring statements about polynomials over the residue field
to Tate algebras: a series has norm one exactly when its reduction is nonzero. Over a complete
field it also detects units: the kernel `T°°` lies in the Jacobson radical of `T°`, so a series of
`T°` is a unit exactly when its reduction is, that is, when its constant coefficient has norm one
and all other coefficients have norm less than one. Units of `T°` are the units of `T` of norm
one; a nonzero constant of norm less than one is a unit of `T` but not of `T°`.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedIntegerEquiv`: the isometric ring isomorphism
  `𝒪[K]⟨X⟩ ≃ T°`.
* `TauCeti.MvPowerSeries.restrictedReduction`: coefficientwise reduction `T° →+* 𝓀[K][X]`.
* `TauCeti.MvPowerSeries.restrictedReductionQuotientEquiv`: `T° ⧸ T°° ≃+* 𝓀[K][X]`, where the
  kernel `T°°` is described by `TauCeti.MvPowerSeries.restrictedReduction_eq_zero_iff`.

## Main results

* `TauCeti.MvPowerSeries.mem_unitClosedBall_iff`: a restricted series lies in the unit ball
  exactly when all its coefficients have norm at most one.
* `TauCeti.MvPowerSeries.restrictedReduction_eq_zero_iff`: the reduction of `f` vanishes exactly
  when `‖f‖ < 1`.
* `TauCeti.MvPowerSeries.restrictedReduction_surjective`: every polynomial over `𝓀[K]` is a
  reduction.
* `TauCeti.MvPowerSeries.ker_restrictedReduction`: the kernel of reduction is the open-ball ideal
  `TauCeti.unitBallIdeal T`.
* `TauCeti.MvPowerSeries.isLocalHom_restrictedReduction`: over a complete field, a series whose
  reduction is a unit is a unit of `T°`.
* `TauCeti.MvPowerSeries.isUnit_iff_norm_constantCoeff_eq_one_and_norm_coeff_lt_one`: the
  coefficient criterion for the units of `T°`.
* `TauCeti.MvPowerSeries.isUnit_algebraMap_and_not_isUnit_of_norm_lt_one`: a nonzero constant
  of norm less than one is a unit of `T` but not of `T°`.
* `TauCeti.MvPowerSeries.powerBoundedSubring_eq_unitClosedBall`: the power-bounded elements of
  `T` form its Gauss unit ball.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§5.1.2–5.1.3.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries IsLocalRing Filter
open scoped NormedField Valued

section UnitBall

variable {σ R : Type*} [NormedRing R] [IsUltrametricDist R]

/-- **Coefficient criterion for the Gauss unit ball.** A unit-radius restricted series has norm
at most one exactly when all its coefficients do. -/
theorem mem_unitClosedBall_iff [NormOneClass R]
    {f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)} :
    f ∈ Subring.unitClosedBall (IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) ↔
      ∀ t, ‖coeff t (f : MvPowerSeries σ R)‖ ≤ 1 := by
  simp [norm_le_iff zero_le_one]

/-- **Coefficient criterion for the open Gauss unit ball.** A unit-radius restricted series has
norm less than one exactly when all its coefficients do. -/
theorem norm_lt_one_iff {f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)} :
    ‖f‖ < 1 ↔ ∀ t, ‖coeff t (f : MvPowerSeries σ R)‖ < 1 := by
  simp [norm_lt_iff]

/-- The coefficients of a series in the Gauss unit ball have norm at most one. -/
theorem norm_coeff_le_one [NormOneClass R]
    (f : Subring.unitClosedBall (IsRestricted.subring (R := R) (fun _ : σ ↦ 1))) (t : σ →₀ ℕ) :
    ‖coeff t ((f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : MvPowerSeries σ R)‖ ≤ 1 :=
  mem_unitClosedBall_iff.mp f.2 t

end UnitBall

variable {σ K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

local notation "T" => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)
local notation "T°" => Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))
local notation "Tint" => IsRestricted.subring (R := 𝒪[K]) (fun _ : σ ↦ 1)

/-- The coefficients of a series in the Gauss unit ball lie in `𝒪[K]`. -/
theorem coeff_mem_integer (f : T°) (t : σ →₀ ℕ) :
    coeff t ((f : T) : MvPowerSeries σ K) ∈ 𝒪[K] :=
  Valued.integer.mem_iff.mpr (norm_coeff_le_one f t)

section IntegerEquiv

/-- The inclusion of `𝒪[K]` into `K` is bounded with constant one. -/
private theorem norm_integer_subtype_le (x : 𝒪[K]) : ‖(𝒪[K]).subtype x‖ ≤ 1 * ‖x‖ :=
  (one_mul ‖x‖).symm.le

/-- The map `𝒪[K]⟨X⟩ → T°` including the coefficients. -/
private noncomputable def restrictedIntegerHom : Tint →+* T° :=
  (restrictedMap (𝒪[K]).subtype norm_integer_subtype_le).codRestrict _ fun f ↦
    mem_unitClosedBall_iff.mpr fun t ↦ by
      rw [coeff_restrictedMap]
      exact Valued.integer.norm_le_one _

private theorem restrictedIntegerHom_bijective :
    Function.Bijective (restrictedIntegerHom (σ := σ) (K := K)) := by
  refine ⟨fun f g h ↦ Subtype.ext <| MvPowerSeries.ext fun t ↦ Subtype.ext ?_, fun f ↦ ?_⟩
  · simpa [restrictedIntegerHom] using
      congrArg (fun g : T° ↦ coeff t ((g : T) : MvPowerSeries σ K)) h
  · let g : MvPowerSeries σ 𝒪[K] := fun t ↦ ⟨_, coeff_mem_integer f t⟩
    have hgc (t : σ →₀ ℕ) : coeff t g = ⟨_, coeff_mem_integer f t⟩ := (rfl)
    have hg : IsRestricted (fun _ : σ ↦ 1) g := by
      have hf : IsRestricted (fun _ : σ ↦ 1) ((f : T) : MvPowerSeries σ K) := (f : T).2
      simp only [IsRestricted] at hf ⊢
      simpa [hgc] using hf
    exact ⟨⟨g, hg⟩, Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun t ↦ by
      simp [restrictedIntegerHom, hgc]⟩

/-- **The Gauss unit ball as restricted series over the integers.** Including coefficients
identifies unit-radius restricted series over `𝒪[K]` with the series in `K⟨X⟩` of Gauss norm at
most one. -/
noncomputable def restrictedIntegerEquiv : Tint ≃+* T° :=
  RingEquiv.ofBijective _ restrictedIntegerHom_bijective

/-- `restrictedIntegerEquiv` includes each coefficient into `K`. -/
@[simp]
theorem coeff_restrictedIntegerEquiv (f : Tint) (t : σ →₀ ℕ) :
    coeff t ((restrictedIntegerEquiv f : T) : MvPowerSeries σ K) =
      coeff t (f : MvPowerSeries σ 𝒪[K]) := by
  simp [restrictedIntegerEquiv, restrictedIntegerHom]

/-- The coefficients of `restrictedIntegerEquiv.symm f` are those of `f`. -/
@[simp]
theorem coeff_restrictedIntegerEquiv_symm (f : T°) (t : σ →₀ ℕ) :
    ((coeff t (restrictedIntegerEquiv.symm f : MvPowerSeries σ 𝒪[K]) : 𝒪[K]) : K) =
      coeff t ((f : T) : MvPowerSeries σ K) := by
  conv_rhs => rw [← restrictedIntegerEquiv.apply_symm_apply f]
  rw [coeff_restrictedIntegerEquiv]

/-- `restrictedIntegerEquiv` preserves the Gauss norm. -/
@[simp]
theorem norm_restrictedIntegerEquiv (f : Tint) : ‖(restrictedIntegerEquiv f : T)‖ = ‖f‖ := by
  refine le_antisymm ((norm_le_iff (norm_nonneg f)).mpr fun t ↦ ?_)
    ((norm_le_iff (norm_nonneg _)).mpr fun t ↦ ?_)
  · simpa using norm_coeff_mul_prod_le f t
  · simpa using norm_coeff_mul_prod_le (restrictedIntegerEquiv f : T) t

end IntegerEquiv

section Reduction

/-- Only finitely many coefficients of a restricted series over `𝒪[K]` have nonzero residue. -/
private theorem finite_support_residue_coeff (f : Tint) :
    (Function.support fun t ↦ residue 𝒪[K] (coeff t (f : MvPowerSeries σ 𝒪[K]))).Finite := by
  have hfin : {t | 1 ≤ ‖coeff t (f : MvPowerSeries σ 𝒪[K])‖}.Finite := by
    simpa [eventually_cofinite, not_lt] using f.2.eventually (gt_mem_nhds one_pos)
  refine hfin.subset fun t ht ↦ ?_
  rw [Function.mem_support, Ne, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    not_not, Valued.integer.isUnit_iff_norm_eq_one] at ht
  exact ht.ge

/-- Coefficientwise reduction of a restricted series over `𝒪[K]`, a polynomial over `𝓀[K]`. -/
private noncomputable def integerReduction (f : Tint) : MvPolynomial σ 𝓀[K] :=
  .ofCoeff (Finsupp.ofSupportFinite _ (finite_support_residue_coeff f))

private theorem coe_integerReduction (f : Tint) :
    (integerReduction f : MvPowerSeries σ 𝓀[K]) =
      MvPowerSeries.map (residue 𝒪[K]) (f : MvPowerSeries σ 𝒪[K]) := by
  ext t
  simp [MvPolynomial.coeff_coe, integerReduction, Finsupp.ofSupportFinite_coe]

/-- Coefficientwise reduction `𝒪[K]⟨X⟩ →+* 𝓀[K][X]` as a ring homomorphism. -/
private noncomputable def integerReductionHom : Tint →+* MvPolynomial σ 𝓀[K] where
  toFun := integerReduction
  map_one' := MvPolynomial.coe_injective _ _ <| by simp [coe_integerReduction]
  map_mul' f g := MvPolynomial.coe_injective _ _ <| by simp [coe_integerReduction]
  map_zero' := MvPolynomial.coe_injective _ _ <| by simp [coe_integerReduction]
  map_add' f g := MvPolynomial.coe_injective _ _ <| by simp [coe_integerReduction]

/-- **Reduction of the Gauss unit ball.** A series of Gauss norm at most one in `K⟨X⟩` is sent to
the polynomial over the residue field `𝓀[K]` obtained by reducing each coefficient; only finitely
many coefficients have nonzero residue. -/
noncomputable def restrictedReduction : T° →+* MvPolynomial σ 𝓀[K] :=
  integerReductionHom.comp restrictedIntegerEquiv.symm.toRingHom

/-- The coefficients of the reduction are the residues of the coefficients. -/
@[simp]
theorem coeff_restrictedReduction (f : T°) (t : σ →₀ ℕ) :
    (restrictedReduction f).coeff t =
      residue 𝒪[K] ⟨coeff t ((f : T) : MvPowerSeries σ K), coeff_mem_integer f t⟩ := by
  rw [← MvPolynomial.coeff_coe]
  simp only [restrictedReduction, integerReductionHom, RingHom.comp_apply, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, coe_integerReduction, coeff_map]
  exact congrArg _ (Subtype.ext (by simp))

/-- A coefficient of the reduction vanishes exactly when the corresponding coefficient of the
series has norm less than one. -/
theorem coeff_restrictedReduction_eq_zero_iff {f : T°} {t : σ →₀ ℕ} :
    (restrictedReduction f).coeff t = 0 ↔ ‖coeff t ((f : T) : MvPowerSeries σ K)‖ < 1 := by
  rw [coeff_restrictedReduction, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    Valued.integer.isUnit_iff_norm_eq_one]
  exact ⟨fun h ↦ (norm_coeff_le_one f t).lt_of_ne h, ne_of_lt⟩

/-- The reduction of a series vanishes exactly when its Gauss norm is less than one: the kernel
of `restrictedReduction` is the open unit ball `T°°`. -/
theorem restrictedReduction_eq_zero_iff {f : T°} :
    restrictedReduction f = 0 ↔ ‖(f : T)‖ < 1 := by
  rw [norm_lt_one_iff, MvPolynomial.ext_iff]
  exact forall_congr' fun t ↦ by
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
      coeff_restrictedReduction_eq_zero_iff]

/-- A series in the Gauss unit ball has norm one exactly when its reduction is nonzero. -/
theorem restrictedReduction_ne_zero_iff {f : T°} :
    restrictedReduction f ≠ 0 ↔ ‖(f : T)‖ = 1 := by
  rw [Ne, restrictedReduction_eq_zero_iff, not_lt]
  exact ⟨fun h ↦ le_antisymm (Subring.mem_unitClosedBall.mp f.2) h, ge_of_eq⟩

/-- Membership in the kernel of `restrictedReduction` is the strict bound `‖f‖ < 1`. -/
theorem mem_ker_restrictedReduction {f : T°} :
    f ∈ RingHom.ker restrictedReduction ↔ ‖(f : T)‖ < 1 := by
  rw [RingHom.mem_ker, restrictedReduction_eq_zero_iff]

/-- **The kernel of reduction is the open-ball ideal** `T°° = TauCeti.unitBallIdeal T` of the
Gauss unit ball. -/
theorem ker_restrictedReduction :
    RingHom.ker (restrictedReduction (σ := σ) (K := K)) = unitBallIdeal T := by
  ext f
  rw [mem_ker_restrictedReduction, mem_unitBallIdeal]

/-- The reduction of a polynomial with integral coefficients is its coefficientwise reduction. -/
@[simp]
theorem restrictedReduction_restrictedIntegerEquiv (q : MvPolynomial σ 𝒪[K]) :
    restrictedReduction (restrictedIntegerEquiv
        ⟨(q : MvPowerSeries σ 𝒪[K]), MvPolynomial.isRestricted _ q⟩) =
      q.map (residue 𝒪[K]) := by
  refine MvPolynomial.ext _ _ fun t ↦ ?_
  simp only [coeff_restrictedReduction, coeff_restrictedIntegerEquiv, MvPolynomial.coeff_map,
    MvPolynomial.coeff_coe]

/-- **Every polynomial over the residue field is a reduction**: lift its coefficients to
`𝒪[K]`. -/
theorem restrictedReduction_surjective :
    Function.Surjective (restrictedReduction (σ := σ) (K := K)) := by
  intro p
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ (residue_surjective (R := 𝒪[K])) p
  exact ⟨_, restrictedReduction_restrictedIntegerEquiv q⟩

/-- **`T° ⧸ T°° ≃ 𝓀[K][X]`.** Reduction identifies the quotient of the Gauss unit ball by the
kernel of reduction, the series of norm less than one (`mem_ker_restrictedReduction`), with the
polynomial ring over the residue field. -/
noncomputable def restrictedReductionQuotientEquiv :
    T° ⧸ RingHom.ker (restrictedReduction (σ := σ) (K := K)) ≃+* MvPolynomial σ 𝓀[K] :=
  RingHom.quotientKerEquivOfSurjective restrictedReduction_surjective

/-- `restrictedReductionQuotientEquiv` sends the class of `f` to its reduction. -/
@[simp]
theorem restrictedReductionQuotientEquiv_mk (f : T°) :
    restrictedReductionQuotientEquiv (Ideal.Quotient.mk _ f) = restrictedReduction f := (rfl)

/-- A constant of norm at most one reduces to the constant polynomial on its residue. -/
@[simp]
theorem restrictedReduction_algebraMap (a : 𝒪[K]) (h : algebraMap K T a ∈ T°) :
    restrictedReduction ⟨algebraMap K T a, h⟩ = MvPolynomial.C (residue 𝒪[K] a) := by
  classical
  have : (⟨algebraMap K T a, h⟩ : T°) =
      restrictedIntegerEquiv
        ⟨((MvPolynomial.C a : MvPolynomial σ 𝒪[K]) : MvPowerSeries σ 𝒪[K]),
          MvPolynomial.isRestricted _ _⟩ :=
    Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun t ↦ by
      rw [coeff_restrictedIntegerEquiv]
      simp only [coe_algebraMap_isRestrictedSubring, MvPolynomial.coe_C, coeff_C]
      split_ifs <;> simp
  rw [this, restrictedReduction_restrictedIntegerEquiv, MvPolynomial.map_C]

/-- Each variable reduces to the corresponding variable. -/
@[simp]
theorem restrictedReduction_X (i : σ) (h : (⟨X i, isRestricted_X _ i⟩ : T) ∈ T°) :
    restrictedReduction ⟨⟨X i, isRestricted_X _ i⟩, h⟩ = MvPolynomial.X i := by
  classical
  have : (⟨⟨X i, isRestricted_X _ i⟩, h⟩ : T°) =
      restrictedIntegerEquiv
        ⟨((MvPolynomial.X i : MvPolynomial σ 𝒪[K]) : MvPowerSeries σ 𝒪[K]),
          MvPolynomial.isRestricted _ _⟩ :=
    Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun t ↦ by
      rw [coeff_restrictedIntegerEquiv]
      simp only [MvPolynomial.coe_X, coeff_X]
      split_ifs <;> simp
  rw [this, restrictedReduction_restrictedIntegerEquiv, MvPolynomial.map_X]

end Reduction

section Units

/-- **A unit of `T` that is not a unit of `T°`.** A nonzero constant of norm less than one is a
unit of the Tate algebra `T`, but not a unit of its Gauss unit ball `T°`. -/
theorem isUnit_algebraMap_and_not_isUnit_of_norm_lt_one {a : K} (ha0 : a ≠ 0) (ha : ‖a‖ < 1)
    (h : algebraMap K T a ∈ T°) :
    IsUnit (algebraMap K T a) ∧ ¬IsUnit (⟨algebraMap K T a, h⟩ : T°) :=
  ⟨(isUnit_iff_ne_zero.mpr ha0).map _, fun hu ↦ ha.ne <|
    (norm_algebraMap_isRestrictedSubring a).symm.trans (isUnit_unitClosedBall_iff.mp hu).2⟩

variable [CompleteSpace K]

/-- **Units lift along reduction.** Over a complete field, reduction `T° → 𝓀[K][X]` is a local
homomorphism: a series of Gauss norm at most one whose reduction is a unit is a unit of `T°`.
Together with `isUnit_map_iff`, a series of `T°` is a unit exactly when its reduction is a
unit. -/
instance isLocalHom_restrictedReduction :
    IsLocalHom (restrictedReduction (σ := σ) (K := K)) := by
  have hker :
      IsLocalHom (Ideal.Quotient.mk (RingHom.ker (restrictedReduction (σ := σ) (K := K)))) :=
    isLocalHom_of_le_jacobson_bot _ (ker_restrictedReduction.le.trans
      (unitBallIdeal_le_jacobson_bot T))
  have h : restrictedReduction (σ := σ) (K := K) =
      (restrictedReductionQuotientEquiv (σ := σ) (K := K) : _ →+* _).comp
        (Ideal.Quotient.mk (RingHom.ker (restrictedReduction (σ := σ) (K := K)))) :=
    RingHom.ext fun f ↦ (restrictedReductionQuotientEquiv_mk f).symm
  rw [h]
  infer_instance

/-- **The units of the Gauss unit ball.** Over a complete field, a series of Gauss norm at most
one is a unit of `T°` exactly when its constant coefficient has norm one and every other
coefficient has norm less than one, that is, when its reduction is a nonzero constant. Such a
series is in particular a unit of `T` of norm one; conversely, by
`TauCeti.isUnit_unitClosedBall_iff`, a unit of `T` lies in the units of `T°` only if it has
norm one, so a nonzero constant of norm less than one is a unit of `T` but not of `T°`
(`isUnit_algebraMap_and_not_isUnit_of_norm_lt_one`). -/
theorem isUnit_iff_norm_constantCoeff_eq_one_and_norm_coeff_lt_one {f : T°} :
    IsUnit f ↔ ‖constantCoeff ((f : T) : MvPowerSeries σ K)‖ = 1 ∧
      ∀ t ≠ 0, ‖coeff t ((f : T) : MvPowerSeries σ K)‖ < 1 := by
  rw [← isUnit_map_iff restrictedReduction, MvPolynomial.isUnit_iff, isUnit_iff_ne_zero,
    ← coeff_zero_eq_constantCoeff_apply, ne_eq, coeff_restrictedReduction_eq_zero_iff, not_lt,
    (norm_coeff_le_one f 0).ge_iff_eq]
  simp_rw [isNilpotent_iff_eq_zero, coeff_restrictedReduction_eq_zero_iff]

end Units

section PowerBounded

/-- **The power-bounded subring of `K⟨X⟩` is its Gauss unit ball.** The Gauss norm is
multiplicative, and a constant of norm strictly between zero and one is a pseudouniformiser. -/
theorem powerBoundedSubring_eq_unitClosedBall :
    Huber.powerBoundedSubring T = Subring.unitClosedBall T := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one K
  have hϖ : Huber.IsPseudoUniformizer (algebraMap K T ϖ) :=
    .of_norm_lt_one ((isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hϖ0)).map _)
      (by rwa [norm_algebraMap_isRestrictedSubring])
  exact SetLike.coe_injective <| (hϖ.coe_powerBoundedSubring_eq_closedBall
    fun f n _ ↦ norm_pow f n).trans (Subring.coe_unitClosedBall T).symm

end PowerBounded

end TauCeti.MvPowerSeries

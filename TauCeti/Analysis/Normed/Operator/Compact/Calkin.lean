/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Analysis.Normed.Operator.Compact.Basic

/-!
# The Calkin algebra

The compact operators on a normed space `E` form a two-sided ideal
`TauCeti.compactOperatorIdeal 𝕜 E` of the algebra `E →L[𝕜] E` of bounded operators, closed when
`E` is complete. The quotient `TauCeti.CalkinAlgebra 𝕜 E = (E →L[𝕜] E) ⧸ compactOperatorIdeal 𝕜 E`
is the **Calkin algebra** of `E`, and `TauCeti.CalkinAlgebra.mk` is the quotient map. Two
operators have the same image exactly when they differ by a compact operator, so the Calkin
algebra is the natural home of every statement that holds "modulo compact operators", such as
Atkinson's characterization of Fredholm operators as the operators invertible modulo compacts.

It carries the quotient norm, `‖mk T‖ = inf {‖T + K‖ : K compact}`, the *essential norm* of `T`.
For complete `E` it is a Banach algebra; the quotient-norm inequality
`‖mk (T * S)‖ ≤ ‖mk T‖ * ‖mk S‖` is `norm_mul_le` in it. For a complex Hilbert space `E` it is
moreover a unital C⋆-algebra, through the quotient C⋆-algebra structure of
`TauCeti.Analysis.CStarAlgebra.Quotient`, and the image of the adjoint `T†` is `star (mk T)`.

Whether the Calkin algebra is zero depends only on the dimension. If `E` is finite-dimensional
over a locally compact field, every operator is compact and the Calkin algebra is trivial, so all
its norms vanish. If `E` is infinite-dimensional (over a complete field), the identity is not
compact by Riesz's lemma, so the Calkin algebra is nontrivial and, for complete `E`, its identity
has norm exactly `1`.

## Main declarations

* `TauCeti.compactOperatorIdeal`: the compact operators as a two-sided ideal of `E →L[𝕜] E`.
* `TauCeti.CalkinAlgebra`: the Calkin algebra `(E →L[𝕜] E) ⧸ compactOperatorIdeal 𝕜 E`.
* `TauCeti.CalkinAlgebra.mk`: the quotient map, as a `𝕜`-algebra homomorphism.
* `TauCeti.CalkinAlgebra.mk_eq_zero_iff`, `TauCeti.CalkinAlgebra.mk_eq_mk_iff`,
  `TauCeti.CalkinAlgebra.ker_mk`: the kernel of the quotient map is the compact operators.
* `TauCeti.CalkinAlgebra.lift`, `TauCeti.CalkinAlgebra.algHom_ext`: the universal property of the
  quotient map among algebra homomorphisms.
* `TauCeti.CalkinAlgebra.continuous_mk`: the quotient map is continuous.
* `TauCeti.CalkinAlgebra.norm_mk_eq`, `TauCeti.CalkinAlgebra.norm_mk_le_norm_add` and
  `TauCeti.CalkinAlgebra.exists_norm_add_lt`: the quotient norm is the essential norm.
* `TauCeti.CalkinAlgebra.subsingleton_iff`, `TauCeti.CalkinAlgebra.nontrivial_iff`: the Calkin
  algebra is zero exactly for finite-dimensional `E`.
* `TauCeti.CalkinAlgebra.norm_one`: for infinite-dimensional complete `E`, `‖mk 1‖ = 1`.
* `TauCeti.CalkinAlgebra.mk_star`, `TauCeti.CalkinAlgebra.mk_adjoint`: on a Hilbert space,
  `mk T† = star (mk T)`.
* `TauCeti.CalkinAlgebra.mkStarAlgHom`: on a Hilbert space, the quotient map as a unital
  `⋆`-algebra homomorphism.

## References

* J. W. Calkin, *Two-sided ideals and congruences in the ring of bounded operators in Hilbert
  space*, Ann. of Math. **42** (1941), 839–873.
* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer, 1990, Chapter XI, §2.
-/

public section

open Module

namespace TauCeti

section Ideal

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The compact operators on `E` as a two-sided ideal of the algebra `E →L[𝕜] E` of bounded
operators. It is closed when `E` is complete (`TauCeti.isClosed_compactOperatorIdeal`). -/
def compactOperatorIdeal : TwoSidedIdeal (E →L[𝕜] E) :=
  .mk' (compactOperator (RingHom.id 𝕜) E E) (zero_mem _) add_mem neg_mem
    (fun {S _} hT ↦ IsCompactOperator.mul_left hT S)
    (fun {_ T} hS ↦ IsCompactOperator.mul_right hS T)

variable {𝕜 E}

@[simp]
theorem mem_compactOperatorIdeal {T : E →L[𝕜] E} :
    T ∈ compactOperatorIdeal 𝕜 E ↔ IsCompactOperator T :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ T

theorem coe_compactOperatorIdeal :
    (compactOperatorIdeal 𝕜 E : Set (E →L[𝕜] E)) = {T : E →L[𝕜] E | IsCompactOperator T} :=
  TwoSidedIdeal.coe_mk' _ _ _ _ _ _

instance isClosed_compactOperatorIdeal [CompleteSpace E] :
    IsClosed (compactOperatorIdeal 𝕜 E : Set (E →L[𝕜] E)) := by
  rw [coe_compactOperatorIdeal]
  exact isClosed_setOfPred_isCompactOperator

end Ideal

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The **Calkin algebra** of a normed space `E`: the bounded operators on `E` modulo the compact
operators, with the quotient norm. It is a Banach algebra when `E` is complete, and a C⋆-algebra
when `E` is a complex Hilbert space. -/
abbrev CalkinAlgebra : Type _ :=
  (E →L[𝕜] E) ⧸ compactOperatorIdeal 𝕜 E

namespace CalkinAlgebra

/-- The quotient map from the bounded operators on `E` to the Calkin algebra of `E`. -/
def mk : (E →L[𝕜] E) →ₐ[𝕜] CalkinAlgebra 𝕜 E :=
  Ideal.Quotient.mkₐ 𝕜 (compactOperatorIdeal 𝕜 E).asIdeal

variable {𝕜 E}

theorem mk_apply (T : E →L[𝕜] E) :
    mk 𝕜 E T = TwoSidedIdeal.Quotient.mk (compactOperatorIdeal 𝕜 E) T :=
  (congrFun (Ideal.Quotient.mkₐ_eq_mk 𝕜 _) T).trans
    (TwoSidedIdeal.Quotient.idealQuotientMk_asIdeal_eq_mk _ T)

theorem mk_surjective : Function.Surjective (mk 𝕜 E) :=
  Ideal.Quotient.mkₐ_surjective 𝕜 _

/-- An operator vanishes in the Calkin algebra exactly when it is compact. -/
@[simp]
theorem mk_eq_zero_iff {T : E →L[𝕜] E} : mk 𝕜 E T = 0 ↔ IsCompactOperator T := by
  rw [mk_apply, TwoSidedIdeal.Quotient.eq_zero_iff_mem, mem_compactOperatorIdeal]

/-- Two operators have the same image in the Calkin algebra exactly when they differ by a compact
operator. -/
theorem mk_eq_mk_iff {S T : E →L[𝕜] E} : mk 𝕜 E S = mk 𝕜 E T ↔ IsCompactOperator (S - T) := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff]

/-- The quotient map sends composition of operators to multiplication in the Calkin algebra. -/
@[simp]
theorem mk_comp (S T : E →L[𝕜] E) : mk 𝕜 E (S.comp T) = mk 𝕜 E S * mk 𝕜 E T := by
  rw [← ContinuousLinearMap.mul_def, map_mul]

/-- The kernel of the quotient map to the Calkin algebra is the ideal of compact operators. -/
@[simp]
theorem ker_mk : TwoSidedIdeal.ker (mk 𝕜 E) = compactOperatorIdeal 𝕜 E := by
  ext T
  rw [TwoSidedIdeal.mem_ker, mk_apply, ← TwoSidedIdeal.mem_ker, TwoSidedIdeal.Quotient.ker_mk]

/-! ### The universal property -/

section Lift

variable {A : Type*} [Semiring A] [Algebra 𝕜 A]

/-- Two algebra homomorphisms out of the Calkin algebra agree when their compositions with the
quotient map agree. -/
@[ext 1100]
theorem algHom_ext ⦃f g : CalkinAlgebra 𝕜 E →ₐ[𝕜] A⦄ (h : f.comp (mk 𝕜 E) = g.comp (mk 𝕜 E)) :
    f = g :=
  Ideal.Quotient.algHom_ext (I := (compactOperatorIdeal 𝕜 E).asIdeal) 𝕜 h

/-- An algebra homomorphism out of the bounded operators that vanishes on the compact operators
descends to the Calkin algebra. -/
def lift (f : (E →L[𝕜] E) →ₐ[𝕜] A) (hf : ∀ T : E →L[𝕜] E, IsCompactOperator T → f T = 0) :
    CalkinAlgebra 𝕜 E →ₐ[𝕜] A :=
  Ideal.Quotient.liftₐ (compactOperatorIdeal 𝕜 E).asIdeal f fun T hT ↦
    hf T (mem_compactOperatorIdeal.mp hT)

@[simp]
theorem lift_comp_mk (f : (E →L[𝕜] E) →ₐ[𝕜] A)
    (hf : ∀ T : E →L[𝕜] E, IsCompactOperator T → f T = 0) :
    (lift f hf).comp (mk 𝕜 E) = f :=
  Ideal.Quotient.liftₐ_comp _ f _

@[simp]
theorem lift_mk (f : (E →L[𝕜] E) →ₐ[𝕜] A)
    (hf : ∀ T : E →L[𝕜] E, IsCompactOperator T → f T = 0) (T : E →L[𝕜] E) :
    lift f hf (mk 𝕜 E T) = f T := by
  rw [← AlgHom.comp_apply, lift_comp_mk]

end Lift

/-! ### The essential norm -/

/-- The quotient map to the Calkin algebra does not increase norms. -/
theorem norm_mk_le (T : E →L[𝕜] E) : ‖mk 𝕜 E T‖ ≤ ‖T‖ := by
  rw [mk_apply]
  exact TwoSidedIdeal.Quotient.norm_mk_le _ T

/-- The quotient map to the Calkin algebra is continuous. -/
@[fun_prop]
theorem continuous_mk : Continuous (mk 𝕜 E) :=
  (TwoSidedIdeal.Quotient.continuous_mk _).congr fun T ↦ (mk_apply T).symm

/-- The norm of `T` in the Calkin algebra is at most the norm of every compact perturbation
of `T`. -/
theorem norm_mk_le_norm_add (T : E →L[𝕜] E) {K : E →L[𝕜] E} (hK : IsCompactOperator K) :
    ‖mk 𝕜 E T‖ ≤ ‖T + K‖ := by
  have h : mk 𝕜 E (T + K) = mk 𝕜 E T := by rw [map_add, mk_eq_zero_iff.mpr hK, add_zero]
  rw [← h]
  exact norm_mk_le _

/-- The norm of `T` in the Calkin algebra is its **essential norm**, the infimum of `‖T + K‖`
over the compact operators `K`. -/
theorem norm_mk_eq (T : E →L[𝕜] E) :
    ‖mk 𝕜 E T‖ = sInf ((‖T + ·‖) '' {K | IsCompactOperator K}) := by
  rw [mk_apply, TwoSidedIdeal.Quotient.norm_mk_eq, coe_compactOperatorIdeal]

/-- The essential norm of `T` is approached by compact perturbations of `T`. -/
theorem exists_norm_add_lt (T : E →L[𝕜] E) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : E →L[𝕜] E, IsCompactOperator K ∧ ‖T + K‖ < ‖mk 𝕜 E T‖ + ε := by
  obtain ⟨S, hS, hlt⟩ := TwoSidedIdeal.Quotient.exists_norm_mk_lt (mk 𝕜 E T) hε
  rw [← mk_apply] at hS
  refine ⟨S - T, mk_eq_mk_iff.mp hS, ?_⟩
  rwa [add_sub_cancel]

/-! ### Finite and infinite dimension -/

/-- If `E` is infinite-dimensional over a complete field, the identity of `E` is not compact, so
the Calkin algebra of `E` is nontrivial. -/
theorem nontrivial [CompleteSpace 𝕜] (hE : ¬ FiniteDimensional 𝕜 E) :
    Nontrivial (CalkinAlgebra 𝕜 E) := by
  refine ⟨0, 1, fun h ↦ hE (FiniteDimensional.of_isCompactOperator_id (𝕜 := 𝕜) ?_)⟩
  rwa [← map_one (mk 𝕜 E), eq_comm, mk_eq_zero_iff, ContinuousLinearMap.one_def,
    ContinuousLinearMap.coe_id'] at h

/-- Over a locally compact field, every operator on a finite-dimensional space is compact, so the
Calkin algebra of a finite-dimensional space is zero. -/
instance subsingleton [LocallyCompactSpace 𝕜] [FiniteDimensional 𝕜 E] :
    Subsingleton (CalkinAlgebra 𝕜 E) := by
  have : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
  have hid : IsCompactOperator (id : E → E) :=
    isCompactOperator_id_iff_finiteDimensional.mpr ‹_›
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨S, rfl⟩ := mk_surjective x
  obtain ⟨T, rfl⟩ := mk_surjective y
  exact mk_eq_mk_iff.mpr (by simpa using hid.comp_clm (S - T))

/-- Over a locally compact field, the Calkin algebra of `E` is zero exactly when `E` is
finite-dimensional. -/
theorem subsingleton_iff [LocallyCompactSpace 𝕜] :
    Subsingleton (CalkinAlgebra 𝕜 E) ↔ FiniteDimensional 𝕜 E := by
  have : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
  refine ⟨fun h ↦ ?_, fun _ ↦ subsingleton⟩
  by_contra hE
  have := nontrivial hE
  exact not_subsingleton _ h

/-- Over a locally compact field, the Calkin algebra of `E` is nontrivial exactly when `E` is
infinite-dimensional. -/
theorem nontrivial_iff [LocallyCompactSpace 𝕜] :
    Nontrivial (CalkinAlgebra 𝕜 E) ↔ ¬ FiniteDimensional 𝕜 E := by
  rw [← subsingleton_iff, not_subsingleton_iff_nontrivial]

/-- For an infinite-dimensional Banach space `E`, the identity of the Calkin algebra has norm
`1`: no compact perturbation of the identity has norm less than `1`. -/
theorem norm_one [CompleteSpace 𝕜] [CompleteSpace E] (hE : ¬ FiniteDimensional 𝕜 E) :
    ‖(1 : CalkinAlgebra 𝕜 E)‖ = 1 := by
  have := nontrivial hE
  refine le_antisymm ?_ (one_le_norm_one _)
  rw [← map_one (mk 𝕜 E), ContinuousLinearMap.one_def]
  exact (norm_mk_le _).trans ContinuousLinearMap.norm_id_le

/-! ### Hilbert spaces -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- On a complex Hilbert space, the quotient map to the Calkin algebra commutes with `star`. -/
@[simp]
theorem mk_star (T : H →L[ℂ] H) : mk ℂ H (star T) = star (mk ℂ H T) := by
  rw [mk_apply, mk_apply, TwoSidedIdeal.Quotient.mk_star]

/-- On a complex Hilbert space, the image of the adjoint in the Calkin algebra is the star of the
image. -/
@[simp]
theorem mk_adjoint (T : H →L[ℂ] H) :
    mk ℂ H (ContinuousLinearMap.adjoint T) = star (mk ℂ H T) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, mk_star]

variable (H) in
/-- On a complex Hilbert space, the quotient map to the Calkin algebra as a unital
`⋆`-algebra homomorphism. -/
noncomputable def mkStarAlgHom : (H →L[ℂ] H) →⋆ₐ[ℂ] CalkinAlgebra ℂ H :=
  { mk ℂ H with map_star' := mk_star }

@[simp]
theorem coe_mkStarAlgHom : ⇑(mkStarAlgHom H) = mk ℂ H :=
  (rfl)

noncomputable example : CStarAlgebra (CalkinAlgebra ℂ H) := inferInstance

end Hilbert

end CalkinAlgebra

end TauCeti

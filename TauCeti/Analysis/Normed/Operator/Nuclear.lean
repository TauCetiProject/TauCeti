/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.TensorProduct.Completion
public import TauCeti.Analysis.OperatorIdeal.Carrier
public import Mathlib.Analysis.Normed.Group.Quotient
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Nuclear operators

Let `E` be a normed space and `F` a Banach space over a nontrivially normed field `𝕜`, and write
`E* = StrongDual 𝕜 E`. The canonical operator `E* ⊗̂π F → (E →L[𝕜] F)` on the completed
projective tensor product sends `f ⊗ₜ y` to the rank-one operator `x ↦ f x • y`. It is the
contraction `TauCeti.CompletedProjectiveTensor.toContinuousLinearMap 𝕜 E F`, and its kernel is
closed. Its range is the submodule `TauCeti.nuclearOperators 𝕜 E F` of *nuclear operators*.

The *nuclear norm* `ν(T)` of a bounded operator `T` is the infimum of the projective norms of the
tensors representing `T`, and `∞` when `T` is not nuclear. As `TauCeti.nuclearGauge 𝕜 E F` it is
an operator gauge: it is subadditive, absolutely homogeneous and dominates the operator norm. On
the nuclear operators it is the quotient norm of `E* ⊗̂π F` by the kernel of the canonical
operator. It satisfies the two-sided ideal inequality `ν(A ∘ T ∘ B) ≤ ‖A‖ ν(T) ‖B‖`, and the
rank-one operator `x ↦ f x • y` has nuclear norm `‖f‖ ‖y‖`.

The normed space `TauCeti.NuclearOperator 𝕜 E F` is the carrier of this gauge: the nuclear
operators normed by the nuclear norm, a type distinct from the submodule `nuclearOperators 𝕜 E F`,
which carries the operator norm. Its inclusion into the bounded operators is a contraction. The
quotient of `E* ⊗̂π F` by the kernel of the canonical operator is isometrically isomorphic to it,
so it is a Banach space.

The nuclear norm is in general different from `ContinuousLinearMap.nuclearENorm`, the sum of the
approximation numbers, which is the trace-class gauge on Hilbert spaces.

The canonical operator and the submodule of nuclear operators follow Michał Pacholski's Mathlib
pull request <https://github.com/leanprover-community/mathlib4/pull/42197>
(`TensorProduct.toContinuousLinearMap` and `ContinuousLinearMap.nuclearOperators`), where the
factors appear in the order `F ⊗ E*`.

## Main declarations

* `TauCeti.CompletedProjectiveTensor.toContinuousLinearMap`: the canonical operator
  `E* ⊗̂π F → (E →L[𝕜] F)`.
* `TauCeti.CompletedProjectiveTensor.toContinuousLinearMap_mapL`: its naturality.
* `TauCeti.nuclearOperators`: the submodule of nuclear operators.
* `TauCeti.nuclearGauge`: the nuclear norm as an operator gauge.
* `TauCeti.nuclearGauge_toContinuousLinearMap`: the nuclear norm is the quotient norm.
* `TauCeti.nuclearGauge_comp_comp_le`: the ideal inequality.
* `TauCeti.nuclearGauge_smulRight`: the rank-one value `‖f‖ ‖y‖`.
* `TauCeti.NuclearOperator`: the Banach space of nuclear operators with the nuclear norm.
* `TauCeti.NuclearOperator.quotKerEquiv`: its isometric identification with the quotient of
  `E* ⊗̂π F` by the kernel of the canonical operator.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, Chapter 2.
* A. Grothendieck, *Produits tensoriels topologiques et espaces nucléaires*, Mem. Amer. Math.
  Soc. **16** (1955).
-/

public section

noncomputable section

open scoped TensorProduct ENNReal

open UniformSpace

namespace TauCeti

variable {𝕜 D E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

namespace CompletedProjectiveTensor

variable (𝕜 E F) in
/-- The canonical operator `E* ⊗̂π F → (E →L[𝕜] F)` sending `f ⊗ₜ y` to the rank-one operator
`x ↦ f x • y`. Its range is the submodule of nuclear operators. -/
def toContinuousLinearMap : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) F →L[𝕜] E →L[𝕜] F :=
  liftIsometry 𝕜 (StrongDual 𝕜 E) F (E →L[𝕜] F) (ContinuousLinearMap.smulRightL 𝕜 E F)

/-- The canonical operator sends `f ⊗ₜ y` to the rank-one operator `x ↦ f x • y`. -/
@[simp]
theorem toContinuousLinearMap_coe_tmul (f : StrongDual 𝕜 E) (y : F) :
    toContinuousLinearMap 𝕜 E F (⟨f ⊗ₜ y⟩ : ProjectiveTensor 𝕜 (StrongDual 𝕜 E) F) =
      f.smulRight y := by
  simp [toContinuousLinearMap]

/-- The canonical operator `E* ⊗̂π F → (E →L[𝕜] F)` is a contraction. -/
theorem norm_toContinuousLinearMap_le : ‖toContinuousLinearMap 𝕜 E F‖ ≤ 1 := by
  rw [toContinuousLinearMap, LinearIsometryEquiv.norm_map]
  exact ContinuousLinearMap.norm_smulRightL_le

/-- The kernel of the canonical operator `E* ⊗̂π F → (E →L[𝕜] F)` is closed, so the quotient of
`E* ⊗̂π F` by it is a normed space. -/
instance isClosed_ker_toContinuousLinearMap :
    IsClosed ((toContinuousLinearMap 𝕜 E F).ker :
      Set (CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) F)) :=
  (toContinuousLinearMap 𝕜 E F).isClosed_ker

/-- Naturality of the canonical operator: if `u` represents `T`, then the tensor induced from `u`
by the adjoint of `B` and by `A` represents `A ∘L T ∘L B`. -/
theorem toContinuousLinearMap_mapL (A : F →L[𝕜] G) (B : D →L[𝕜] E)
    (u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) F) :
    toContinuousLinearMap 𝕜 D G (mapL (ContinuousLinearMap.precomp 𝕜 B) A u) =
      A ∘L toContinuousLinearMap 𝕜 E F u ∘L B := by
  have h : toContinuousLinearMap 𝕜 D G ∘L mapL (ContinuousLinearMap.precomp 𝕜 B) A =
      ContinuousLinearMap.postcomp D A ∘L ContinuousLinearMap.precomp F B ∘L
        toContinuousLinearMap 𝕜 E F := by
    refine continuousLinearMap_ext fun f y ↦ ?_
    ext x
    simp
  exact congr($h u)

end CompletedProjectiveTensor

open CompletedProjectiveTensor

/-! ### The submodule of nuclear operators -/

variable (𝕜 E F) in
/-- The nuclear operators from `E` to `F`: the range of the canonical operator
`E* ⊗̂π F → (E →L[𝕜] F)`. -/
def nuclearOperators : Submodule 𝕜 (E →L[𝕜] F) :=
  (toContinuousLinearMap 𝕜 E F).range

/-- An operator is nuclear iff it is represented by a tensor in `E* ⊗̂π F`. -/
@[simp]
theorem mem_nuclearOperators {T : E →L[𝕜] F} :
    T ∈ nuclearOperators 𝕜 E F ↔ ∃ u, toContinuousLinearMap 𝕜 E F u = T :=
  LinearMap.mem_range

/-- Rank-one operators are nuclear. -/
theorem smulRight_mem_nuclearOperators (f : StrongDual 𝕜 E) (y : F) :
    f.smulRight y ∈ nuclearOperators 𝕜 E F :=
  ⟨_, toContinuousLinearMap_coe_tmul f y⟩

/-! ### The nuclear norm -/

/-- The infimum defining the nuclear norm of `T` is at most `c * ν(T)` as soon as every tensor `u`
representing `T` gives the bound `c * ‖u‖`, provided that the bound vanishes for `c = 0`. -/
private theorem le_mul_iInf_enorm {a c : ℝ≥0∞} {T : E →L[𝕜] F} (hc : c ≠ ∞) (ha : c = 0 → a = 0)
    (h : ∀ u, toContinuousLinearMap 𝕜 E F u = T → a ≤ c * ‖u‖ₑ) :
    a ≤ c * ⨅ (u) (_ : toContinuousLinearMap 𝕜 E F u = T), ‖u‖ₑ := by
  rcases eq_or_ne c 0 with rfl | hc₀
  · simp [ha rfl]
  · rw [ENNReal.mul_iInf_of_ne hc₀ hc]
    refine le_iInf fun u ↦ ?_
    rw [ENNReal.mul_iInf_of_ne hc₀ hc]
    exact le_iInf (h u)

/-- The infimum defining the nuclear norm is at most `‖c‖` times that of `T` for `c • T`. -/
private theorem iInf_enorm_smul_le (c : 𝕜) (T : E →L[𝕜] F) :
    ⨅ (u) (_ : toContinuousLinearMap 𝕜 E F u = c • T), ‖u‖ₑ ≤
      ‖c‖ₑ * ⨅ (u) (_ : toContinuousLinearMap 𝕜 E F u = T), ‖u‖ₑ := by
  refine le_mul_iInf_enorm enorm_ne_top (fun hc ↦ ?_) fun u hu ↦ ?_
  · rw [enorm_eq_zero] at hc
    subst hc
    exact le_antisymm ((iInf₂_le 0 (by simp)).trans_eq enorm_zero) bot_le
  · exact (iInf₂_le (c • u) (by rw [map_smul, hu])).trans_eq (enorm_smul c u)

variable (𝕜 E F) in
/-- The **nuclear norm** `ν(T)` as an operator gauge: the infimum of the projective norms of the
tensors in `E* ⊗̂π F` representing `T`, and `∞` when `T` is not nuclear.

This is different in general from `ContinuousLinearMap.nuclearENorm`, the sum of the
approximation numbers. -/
def nuclearGauge : OperatorGauge 𝕜 E F where
  toFun T := ⨅ (u) (_ : toContinuousLinearMap 𝕜 E F u = T), ‖u‖ₑ
  map_add_le' S T := ENNReal.le_iInf₂_add_iInf₂ fun u hu v hv ↦
    (iInf₂_le (u + v) (by rw [map_add, hu, hv])).trans (enorm_add_le u v)
  map_smul' c T := by
    refine le_antisymm (iInf_enorm_smul_le c T) ?_
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    calc
      _ ≤ ‖c‖ₑ * (‖c⁻¹‖ₑ * ⨅ (u) (_ : toContinuousLinearMap 𝕜 E F u = c • T), ‖u‖ₑ) := by
        gcongr
        simpa [smul_smul, inv_mul_cancel₀ hc] using iInf_enorm_smul_le c⁻¹ (c • T)
      _ = _ := by rw [← mul_assoc, ← enorm_mul, mul_inv_cancel₀ hc, enorm_one, one_mul]
  enorm_le' T := le_iInf₂ fun u hu ↦ hu ▸ enorm_le_iff_norm_le.2
    (((toContinuousLinearMap 𝕜 E F).le_of_opNorm_le norm_toContinuousLinearMap_le u).trans_eq
      (one_mul _))

/-- The nuclear norm of `T` is the infimum of the projective norms of the tensors representing
`T`. -/
theorem nuclearGauge_apply (T : E →L[𝕜] F) :
    nuclearGauge 𝕜 E F T = ⨅ (u) (_ : toContinuousLinearMap 𝕜 E F u = T), ‖u‖ₑ :=
  (rfl)

/-- The projective norm of a tensor bounds the nuclear norm of the operator it represents. -/
theorem nuclearGauge_toContinuousLinearMap_le (u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) F) :
    nuclearGauge 𝕜 E F (toContinuousLinearMap 𝕜 E F u) ≤ ‖u‖ₑ := by
  rw [nuclearGauge_apply]
  refine iInf₂_le u ?_
  rfl

/-- If `ν(T) < c`, then `T` is represented by a tensor of projective norm less than `c`. -/
theorem exists_toContinuousLinearMap_eq_of_nuclearGauge_lt {T : E →L[𝕜] F} {c : ℝ≥0∞}
    (h : nuclearGauge 𝕜 E F T < c) : ∃ u, toContinuousLinearMap 𝕜 E F u = T ∧ ‖u‖ₑ < c := by
  simpa only [nuclearGauge_apply, iInf_lt_iff, exists_prop] using h

/-- The nuclear norm is finite exactly on the nuclear operators. -/
theorem nuclearGauge_lt_top_iff {T : E →L[𝕜] F} :
    nuclearGauge 𝕜 E F T < ∞ ↔ T ∈ nuclearOperators 𝕜 E F := by
  refine ⟨fun h ↦ ?_, fun ⟨u, hu⟩ ↦
    hu ▸ (nuclearGauge_toContinuousLinearMap_le u).trans_lt enorm_lt_top⟩
  obtain ⟨u, hu, -⟩ := exists_toContinuousLinearMap_eq_of_nuclearGauge_lt h
  exact ⟨u, hu⟩

/-- The operators of finite nuclear norm are the nuclear operators. -/
@[simp]
theorem finiteSubmodule_nuclearGauge :
    (nuclearGauge 𝕜 E F).finiteSubmodule = nuclearOperators 𝕜 E F :=
  Submodule.ext fun _ ↦ OperatorGauge.mem_finiteSubmodule.trans nuclearGauge_lt_top_iff

/-- On the nuclear operators, the nuclear norm is the quotient norm of `E* ⊗̂π F` by the kernel of
the canonical operator. -/
theorem nuclearGauge_toContinuousLinearMap
    (u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) F) :
    nuclearGauge 𝕜 E F (toContinuousLinearMap 𝕜 E F u) =
      ENNReal.ofReal ‖(Submodule.Quotient.mk u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) F ⧸
        (toContinuousLinearMap 𝕜 E F).ker)‖ := by
  have hmk {v : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) F} :
      (Submodule.Quotient.mk v : _ ⧸ (toContinuousLinearMap 𝕜 E F).ker) =
          Submodule.Quotient.mk u ↔
        toContinuousLinearMap 𝕜 E F v = toContinuousLinearMap 𝕜 E F u := by
    rw [Submodule.Quotient.eq, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, sub_eq_zero]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) (le_iInf₂ fun v hv ↦ ?_)
  · -- A representative of the coset that is almost optimal for the quotient norm.
    obtain ⟨v, hv, hlt⟩ := Submodule.Quotient.norm_mk_lt
      (Submodule.Quotient.mk u : _ ⧸ (toContinuousLinearMap 𝕜 E F).ker)
      (NNReal.coe_pos.2 hε)
    refine (iInf₂_le v (hmk.1 hv)).trans ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_le_ofReal hlt.le).trans ENNReal.ofReal_add_le
  · rw [← hmk.2 hv, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (Submodule.Quotient.norm_mk_le _ v)

/-- The **ideal inequality** for the nuclear norm: `ν(A ∘ T ∘ B) ≤ ‖A‖ ν(T) ‖B‖`. -/
theorem nuclearGauge_comp_comp_le (A : F →L[𝕜] G) (T : E →L[𝕜] F) (B : D →L[𝕜] E) :
    nuclearGauge 𝕜 D G (A ∘L T ∘L B) ≤ ‖A‖ₑ * nuclearGauge 𝕜 E F T * ‖B‖ₑ := by
  rw [mul_right_comm, nuclearGauge_apply T]
  refine le_mul_iInf_enorm (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top) (fun h ↦ ?_)
    fun u hu ↦ ?_
  · -- If `‖A‖ ‖B‖ = 0`, then `A ∘L T ∘L B = 0`.
    have hle : ‖A ∘L T ∘L B‖ₑ ≤ ‖A‖ₑ * ‖T‖ₑ * ‖B‖ₑ :=
      (ContinuousLinearMap.opENorm_comp_le _ _).trans <| by
        rw [mul_assoc]; gcongr; exact ContinuousLinearMap.opENorm_comp_le _ _
    rw [mul_right_comm, h, zero_mul, nonpos_iff_eq_zero,
      ContinuousLinearMap.opENorm_eq_zero_iff] at hle
    rw [hle, OperatorGauge.map_zero]
  · subst hu
    rw [← toContinuousLinearMap_mapL]
    refine (nuclearGauge_toContinuousLinearMap_le _).trans ?_
    simp only [← ofReal_norm]
    rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc
      _ ≤ ‖mapL (ContinuousLinearMap.precomp 𝕜 B) A‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖B‖ * ‖A‖ * ‖u‖ := by
        gcongr
        exact (norm_mapL_le _ _).trans (by gcongr; exact ContinuousLinearMap.norm_precomp_le B)
      _ = _ := by ring

/-- Nuclear operators are stable under composition on the left. -/
theorem comp_left_mem_nuclearOperators (A : F →L[𝕜] G) {T : E →L[𝕜] F}
    (hT : T ∈ nuclearOperators 𝕜 E F) : A ∘L T ∈ nuclearOperators 𝕜 E G := by
  rw [← nuclearGauge_lt_top_iff] at hT ⊢
  simpa using (nuclearGauge_comp_comp_le A T (ContinuousLinearMap.id 𝕜 E)).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top hT) enorm_lt_top)

/-- Nuclear operators are stable under composition on the right. -/
theorem comp_right_mem_nuclearOperators {T : E →L[𝕜] F} (hT : T ∈ nuclearOperators 𝕜 E F)
    (B : D →L[𝕜] E) : T ∘L B ∈ nuclearOperators 𝕜 D F := by
  rw [← nuclearGauge_lt_top_iff] at hT ⊢
  simpa using (nuclearGauge_comp_comp_le (ContinuousLinearMap.id 𝕜 F) T B).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top hT) enorm_lt_top)

/-- The rank-one operator `x ↦ f x • y` has nuclear norm `‖f‖ ‖y‖`. -/
@[simp]
theorem nuclearGauge_smulRight (f : StrongDual 𝕜 E) (y : F) :
    nuclearGauge 𝕜 E F (f.smulRight y) = ‖f‖ₑ * ‖y‖ₑ := by
  refine le_antisymm ?_ ?_
  · rw [← toContinuousLinearMap_coe_tmul]
    refine (nuclearGauge_toContinuousLinearMap_le _).trans ?_
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      Completion.norm_coe, ProjectiveTensor.norm_def]
    exact ENNReal.ofReal_le_ofReal (TensorProduct.projectiveSeminorm_tmul_le f y)
  · simpa [enorm_eq_nnnorm] using (nuclearGauge 𝕜 E F).enorm_le (f.smulRight y)

/-! ### The Banach space of nuclear operators -/

variable (𝕜 E F) in
/-- The normed space of **nuclear operators** from `E` to `F`, normed by the nuclear norm. It is a
Banach space, isometrically isomorphic to the quotient of `E* ⊗̂π F` by the kernel of the canonical
operator (`NuclearOperator.quotKerEquiv`), and its inclusion
`OperatorGauge.Carrier.toContinuousLinearMapL` into the bounded operators is a contraction. -/
abbrev NuclearOperator := (nuclearGauge 𝕜 E F).Carrier

namespace NuclearOperator

/-- The underlying operators of `NuclearOperator 𝕜 E F` are nuclear. -/
theorem toContinuousLinearMap_mem (T : NuclearOperator 𝕜 E F) :
    T.toContinuousLinearMap ∈ nuclearOperators 𝕜 E F :=
  nuclearGauge_lt_top_iff.1 T.gauge_lt_top

/-- A nuclear operator as an element of `NuclearOperator 𝕜 E F`. -/
def mk' {T : E →L[𝕜] F} (hT : T ∈ nuclearOperators 𝕜 E F) : NuclearOperator 𝕜 E F :=
  ⟨T, OperatorGauge.mem_finiteSubmodule.2 (nuclearGauge_lt_top_iff.2 hT)⟩

@[simp]
theorem toContinuousLinearMap_mk' {T : E →L[𝕜] F} (hT : T ∈ nuclearOperators 𝕜 E F) :
    (mk' hT).toContinuousLinearMap = T :=
  (rfl)

/-- The nuclear operator represented by a tensor in `E* ⊗̂π F`, as a linear map. -/
private def ofTensor :
    CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) F →ₗ[𝕜] NuclearOperator 𝕜 E F where
  toFun u := mk' ⟨u, rfl⟩
  map_add' _ _ := OperatorGauge.Carrier.ext (map_add _ _ _)
  map_smul' _ _ := OperatorGauge.Carrier.ext (map_smul _ _ _)

@[simp]
private theorem toContinuousLinearMap_ofTensor
    (u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) F) :
    (ofTensor u).toContinuousLinearMap = toContinuousLinearMap 𝕜 E F u :=
  (rfl)

private theorem ker_ofTensor :
    LinearMap.ker (ofTensor (𝕜 := 𝕜) (E := E) (F := F)) =
      (toContinuousLinearMap 𝕜 E F).ker := by
  ext u
  simp [← OperatorGauge.Carrier.toContinuousLinearMap_inj]

variable (𝕜 E F) in
/-- The quotient of `E* ⊗̂π F` by the kernel of the canonical operator is isometrically isomorphic
to the space of nuclear operators with the nuclear norm. -/
def quotKerEquiv :
    (CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) F ⧸ (toContinuousLinearMap 𝕜 E F).ker)
      ≃ₗᵢ[𝕜] NuclearOperator 𝕜 E F :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (toContinuousLinearMap 𝕜 E F).ker.liftQ ofTensor ker_ofTensor.ge
      norm_map' q := by
        induction q using Submodule.Quotient.induction_on with | H u => ?_
        simp only [Submodule.liftQ_apply, OperatorGauge.Carrier.norm_def,
          toContinuousLinearMap_ofTensor, nuclearGauge_toContinuousLinearMap]
        exact ENNReal.toReal_ofReal (norm_nonneg _) }
    fun T ↦ by
      obtain ⟨u, hu⟩ := T.toContinuousLinearMap_mem
      exact ⟨Submodule.Quotient.mk u, OperatorGauge.Carrier.ext (by simpa using hu)⟩

/-- The isometric isomorphism `quotKerEquiv` sends the class of a tensor to the operator it
represents. -/
@[simp]
theorem toContinuousLinearMap_quotKerEquiv_mk
    (u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) F) :
    (quotKerEquiv 𝕜 E F (Submodule.Quotient.mk u)).toContinuousLinearMap =
      toContinuousLinearMap 𝕜 E F u :=
  (rfl)

/-- The space of nuclear operators with the nuclear norm is a Banach space. -/
instance : CompleteSpace (NuclearOperator 𝕜 E F) :=
  (quotKerEquiv 𝕜 E F).symm.toIsometryEquiv.completeSpace

/-- The rank-one operator `x ↦ f x • y` in `NuclearOperator 𝕜 E F`. -/
def smulRight (f : StrongDual 𝕜 E) (y : F) : NuclearOperator 𝕜 E F :=
  mk' (smulRight_mem_nuclearOperators f y)

@[simp]
theorem toContinuousLinearMap_smulRight (f : StrongDual 𝕜 E) (y : F) :
    (smulRight f y).toContinuousLinearMap = f.smulRight y :=
  (rfl)

/-- The rank-one operator `x ↦ f x • y` has nuclear norm `‖f‖ ‖y‖`. -/
@[simp]
theorem norm_smulRight (f : StrongDual 𝕜 E) (y : F) : ‖smulRight f y‖ = ‖f‖ * ‖y‖ := by
  rw [OperatorGauge.Carrier.norm_def, toContinuousLinearMap_smulRight, nuclearGauge_smulRight,
    ENNReal.toReal_mul, toReal_enorm, toReal_enorm]

end NuclearOperator

end TauCeti

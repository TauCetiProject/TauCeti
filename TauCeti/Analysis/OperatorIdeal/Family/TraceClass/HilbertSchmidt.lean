/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
public import TauCeti.Analysis.OperatorIdeal.Family.TraceClass.Trace

/-!
# Products of Hilbert–Schmidt operators

Let `E`, `F`, `G` be Hilbert spaces over `𝕜 = ℝ` or `ℂ`. The composite `S T` of Hilbert–Schmidt
operators `T : E → F` and `S : F → G` is trace class, with

`‖S T‖₁ ≤ ‖S‖_HS ‖T‖_HS`.

Expanding the middle space in a Hilbert basis `(cᵢ)` writes the composite as the nuclear series
`S T = ∑ᵢ ⟪T† cᵢ, ·⟫ S cᵢ`, and Cauchy–Schwarz bounds `∑ᵢ ‖T† cᵢ‖ ‖S cᵢ‖` by the square roots of
the Hilbert–Schmidt energies of `T†` and `S`. The trace of a product of two Hilbert–Schmidt
operators `S : F → E`, `T : E → F` is then the absolutely convergent sum

`Tr (S T) = ∑ᵢ ⟪T† cᵢ, S cᵢ⟫ = ∑ⱼ ⟪S† eⱼ, T eⱼ⟫`

along any Hilbert basis `(cᵢ)` of `F` or `(eⱼ)` of `E`, and `Tr (S T) = Tr (T S)`. For
`S, T : E → F` the trace `Tr (S† T) = ∑ⱼ ⟪S eⱼ, T eⱼ⟫` is the Hilbert–Schmidt pairing, and
`Tr (T† T) = ‖T‖_HS²`.

## Main results

* `ContinuousLinearMap.hasSum_rankOne_comp`: `S T = ∑ᵢ ⟪T† cᵢ, ·⟫ S cᵢ` in operator norm when the
  coefficients are absolutely summable.
* `ContinuousLinearMap.nuclearENorm_comp_le`: `ν(S T) ≤ E_c(S)^(1/2) E_b(T)^(1/2)`, with no
  hypothesis on `S` or `T`.
* `TauCeti.OperatorIdealFamily.gauge_traceClass_comp_le`: the same bound for the trace-class and
  Hilbert–Schmidt gauges.
* `TauCeti.OperatorIdealFamily.comp_mem_traceClass`: the composite of two Hilbert–Schmidt
  operators is trace class.
* `ContinuousLinearMap.toReal_nuclearENorm_comp_le`: `‖S T‖₁ ≤ ‖S‖_HS ‖T‖_HS`.
* `TauCeti.hilbertSchmidtCompL`: composition as a bounded bilinear map from the normed
  Hilbert–Schmidt carriers into the normed trace-class carrier, of norm at most `1`.
* `ContinuousLinearMap.hasSum_inner_adjoint_apply_apply_trace_comp`:
  `Tr (S T) = ∑ᵢ ⟪T† cᵢ, S cᵢ⟫` along a Hilbert basis of the middle space.
* `ContinuousLinearMap.hasSum_inner_adjoint_apply_trace_comp`: `Tr (S T) = ∑ⱼ ⟪S† eⱼ, T eⱼ⟫`,
  and `ContinuousLinearMap.summable_norm_inner_adjoint_apply`: the sum converges absolutely.
* `ContinuousLinearMap.trace_comp_comm_of_mem_hilbertSchmidt`: `Tr (S T) = Tr (T S)`, and
  `ContinuousLinearMap.norm_trace_comp_le`: `|Tr (S T)| ≤ ‖S‖_HS ‖T‖_HS`.
* `ContinuousLinearMap.hasSum_inner_apply_apply_trace_adjoint_comp`: the Hilbert–Schmidt pairing
  `Tr (S† T) = ∑ⱼ ⟪S eⱼ, T eⱼ⟫`, and `ContinuousLinearMap.trace_adjoint_comp_self`:
  `Tr (T† T) = ‖T‖_HS²`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, first edition, AMS, 2009, §6.3,
  Lemma 6.13.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  edition, Academic Press, 1980, §VI.6.
-/

public section

open InnerProductSpace TauCeti TauCeti.OperatorIdealFamily
open scoped InnerProductSpace ENNReal NNReal

universe u v w x

variable {𝕜 : Type u} [RCLike 𝕜]

namespace ContinuousLinearMap

/-! ### The composite as a nuclear series -/

variable {E : Type v} {F : Type w} {G : Type x}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G] {ι κ : Type*}

/-- **A composite as a nuclear series.** For `T : E → F`, `S : F → G` and a Hilbert basis `(cᵢ)` of
`F` with `∑ᵢ ‖T† cᵢ‖ ‖S cᵢ‖ < ∞`, the composite is the operator-norm sum
`S T = ∑ᵢ ⟪T† cᵢ, ·⟫ S cᵢ`. -/
theorem hasSum_rankOne_comp (S : F →L[𝕜] G) (T : E →L[𝕜] F) (c : HilbertBasis κ 𝕜 F)
    (h : Summable fun i ↦ ‖adjoint T (c i)‖ * ‖S (c i)‖) :
    HasSum (fun i ↦ rankOne 𝕜 (S (c i)) (adjoint T (c i))) (S ∘L T) := by
  have hs : Summable fun i ↦ rankOne 𝕜 (S (c i)) (adjoint T (c i)) :=
    Summable.of_norm (by simpa [mul_comm] using h)
  convert hs.hasSum using 1
  ext y
  -- Expanding `T y = ∑ᵢ ⟪cᵢ, T y⟫ cᵢ` and applying `S` gives the series evaluated at `y`.
  have h₁ : HasSum (fun i ↦ rankOne 𝕜 (S (c i)) (adjoint T (c i)) y) (S (T y)) := by
    simpa [adjoint_inner_left, c.repr_apply_apply] using (c.hasSum_repr (T y)).mapL S
  exact h₁.unique (hs.hasSum.mapL (apply 𝕜 G y))

/-- **The trace norm of a composite.** For `T : E → F`, `S : F → G` and Hilbert bases `b` of `E`
and `c` of `F`, `ν(S T) ≤ E_c(S)^(1/2) E_b(T)^(1/2)`. There is no hypothesis on `S` or `T`: the
right-hand side is infinite unless both have finite Hilbert–Schmidt energy or one of them is
zero. -/
theorem nuclearENorm_comp_le (S : F →L[𝕜] G) (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis κ 𝕜 F) :
    (S ∘L T).nuclearENorm ≤
      S.hilbertSchmidtEnergy c ^ (1 / 2 : ℝ) * T.hilbertSchmidtEnergy b ^ (1 / 2 : ℝ) := by
  have hbound := tsum_enorm_apply_mul_enorm_apply_le (adjoint T) S c
  rw [hilbertSchmidtEnergy_adjoint T b c, mul_comm] at hbound
  rcases eq_or_ne (∑' i, ‖adjoint T (c i)‖ₑ * ‖S (c i)‖ₑ) ∞ with htop | hne
  · rw [htop, top_le_iff] at hbound
    exact hbound ▸ le_top
  have h : Summable fun i ↦ ‖adjoint T (c i)‖ * ‖S (c i)‖ := by
    simpa using ENNReal.summable_toReal hne
  calc (S ∘L T).nuclearENorm
      ≤ ∑' i, (rankOne 𝕜 (S (c i)) (adjoint T (c i))).nuclearENorm :=
        nuclearENorm_le_tsum_of_hasSum (hasSum_rankOne_comp S T c h)
    _ = ∑' i, ‖adjoint T (c i)‖ₑ * ‖S (c i)‖ₑ := by simp [nuclearENorm_rankOne, mul_comm]
    _ ≤ _ := hbound

end ContinuousLinearMap

/-! ### Membership and the ideal bound -/

namespace TauCeti.OperatorIdealFamily

variable {E : Type v} {F : Type w} {G : Type x}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- **The Hilbert–Schmidt product bound** for the ideal gauges: the trace-class gauge of `S T` is
at most the product of the Hilbert–Schmidt gauges of `S` and `T`. -/
theorem gauge_traceClass_comp_le (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    (traceClass.{u, v, x} 𝕜).gauge (S ∘L T) ≤
      (hilbertSchmidt.{u, w, x} 𝕜).gauge S * (hilbertSchmidt.{u, v, w} 𝕜).gauge T := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨_, c, -⟩ := exists_hilbertBasis 𝕜 F
  rw [gauge_traceClass, gauge_hilbertSchmidt S c, gauge_hilbertSchmidt T b]
  exact S.nuclearENorm_comp_le T b c

/-- **Products of Hilbert–Schmidt operators are trace class.** -/
theorem comp_mem_traceClass {S : F →L[𝕜] G} {T : E →L[𝕜] F}
    (hS : S ∈ ((hilbertSchmidt.{u, w, x} 𝕜).operatorGauge F G).finiteSubmodule)
    (hT : T ∈ ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule) :
    S ∘L T ∈ ((traceClass.{u, v, x} 𝕜).operatorGauge E G).finiteSubmodule := by
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] at hS hT ⊢
  exact (gauge_traceClass_comp_le S T).trans_lt (ENNReal.mul_lt_top hS hT)

end TauCeti.OperatorIdealFamily

namespace ContinuousLinearMap

variable {E : Type v} {F : Type w} {G : Type x}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- **The Hilbert–Schmidt product bound** `‖S T‖₁ ≤ ‖S‖_HS ‖T‖_HS` for Hilbert–Schmidt operators
`T : E → F` and `S : F → G`. -/
theorem toReal_nuclearENorm_comp_le {S : F →L[𝕜] G} {T : E →L[𝕜] F}
    (hS : S ∈ ((hilbertSchmidt.{u, w, x} 𝕜).operatorGauge F G).finiteSubmodule)
    (hT : T ∈ ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule) :
    (S ∘L T).nuclearENorm.toReal ≤ S.hilbertSchmidtNorm * T.hilbertSchmidtNorm := by
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] at hS hT
  rw [← toReal_gauge_hilbertSchmidt.{u, w, x} S, ← toReal_gauge_hilbertSchmidt.{u, v, w} T,
    ← ENNReal.toReal_mul, ← gauge_traceClass.{u, v, x}]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hS.ne hT.ne) (gauge_traceClass_comp_le S T)

end ContinuousLinearMap

/-! ### Composition on the normed carriers -/

namespace TauCeti

variable (𝕜)
variable (E : Type v) (F : Type w) (G : Type x)
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- **Composition of Hilbert–Schmidt operators** as a bounded bilinear map from the normed
Hilbert–Schmidt carriers into the normed trace-class carrier, of norm at most `1`
(`TauCeti.norm_hilbertSchmidtCompL_le`). -/
noncomputable def hilbertSchmidtCompL :
    ((hilbertSchmidt.{u, w, x} 𝕜).operatorGauge F G).Carrier →L[𝕜]
      ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).Carrier →L[𝕜]
        ((traceClass.{u, v, x} 𝕜).operatorGauge E G).Carrier :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜
      (fun S T ↦ ⟨S.toContinuousLinearMap ∘L T.toContinuousLinearMap,
        comp_mem_traceClass S.mem_finiteSubmodule T.mem_finiteSubmodule⟩)
      (fun _ _ _ ↦ OperatorGauge.Carrier.ext (ContinuousLinearMap.add_comp _ _ _))
      (fun _ _ _ ↦ OperatorGauge.Carrier.ext (ContinuousLinearMap.smul_comp _ _ _))
      (fun _ _ _ ↦ OperatorGauge.Carrier.ext (ContinuousLinearMap.comp_add _ _ _))
      (fun _ _ _ ↦ OperatorGauge.Carrier.ext (ContinuousLinearMap.comp_smul _ _ _)))
    1 fun S T ↦ by
      simpa [OperatorGauge.Carrier.norm_def] using
        ContinuousLinearMap.toReal_nuclearENorm_comp_le S.mem_finiteSubmodule
          T.mem_finiteSubmodule

variable {𝕜 E F G}

/-- `TauCeti.hilbertSchmidtCompL` composes the underlying operators. -/
@[simp]
theorem toContinuousLinearMap_hilbertSchmidtCompL
    (S : ((hilbertSchmidt.{u, w, x} 𝕜).operatorGauge F G).Carrier)
    (T : ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).Carrier) :
    (hilbertSchmidtCompL 𝕜 E F G S T).toContinuousLinearMap =
      S.toContinuousLinearMap ∘L T.toContinuousLinearMap :=
  (rfl)

/-- Composition of Hilbert–Schmidt operators has norm at most `1` into the trace class. -/
theorem norm_hilbertSchmidtCompL_le : ‖hilbertSchmidtCompL 𝕜 E F G‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

end TauCeti

/-! ### The trace of a product of Hilbert–Schmidt operators -/

namespace ContinuousLinearMap

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] {ι κ : Type*}
  {S : F →L[𝕜] E} {T : E →L[𝕜] F}

/-- **The trace of a product through the middle space.** For Hilbert–Schmidt operators `T : E → F`
and `S : F → E` and any Hilbert basis `(cᵢ)` of `F`, `Tr (S T) = ∑ᵢ ⟪T† cᵢ, S cᵢ⟫`, and the sum
converges absolutely. -/
theorem hasSum_inner_adjoint_apply_apply_trace_comp
    (hS : S ∈ ((hilbertSchmidt.{u, w, v} 𝕜).operatorGauge F E).finiteSubmodule)
    (hT : T ∈ ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule)
    (c : HilbertBasis κ 𝕜 F) :
    HasSum (fun i ↦ ⟪adjoint T (c i), S (c i)⟫_𝕜) (S ∘L T).trace := by
  have h := summable_norm_apply_mul_norm_apply (adjoint T) S c
    ((mem_finiteSubmodule_hilbertSchmidt_iff _ c).1 (adjoint_mem_hilbertSchmidt hT))
    ((mem_finiteSubmodule_hilbertSchmidt_iff _ c).1 hS)
  rw [trace_eq_tsum_of_hasSum_rankOne h (hasSum_rankOne_comp S T c h)]
  exact (h.of_norm_bounded fun _ ↦ norm_inner_le_norm _ _).hasSum

/-- **The trace of a product of Hilbert–Schmidt operators.** For Hilbert–Schmidt operators
`T : E → F` and `S : F → E` and any Hilbert basis `(eⱼ)` of `E`,
`Tr (S T) = ∑ⱼ ⟪S† eⱼ, T eⱼ⟫`. The sum converges absolutely by
`ContinuousLinearMap.summable_norm_inner_adjoint_apply`. -/
theorem hasSum_inner_adjoint_apply_trace_comp
    (hS : S ∈ ((hilbertSchmidt.{u, w, v} 𝕜).operatorGauge F E).finiteSubmodule)
    (hT : T ∈ ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule)
    (b : HilbertBasis ι 𝕜 E) :
    HasSum (fun j ↦ ⟪adjoint S (b j), T (b j)⟫_𝕜) (S ∘L T).trace := by
  simpa [adjoint_inner_left] using hasSum_inner_apply_trace b (comp_mem_traceClass hS hT)

/-- The sum `∑ⱼ ⟪S† eⱼ, T eⱼ⟫` computing `Tr (S T)` converges absolutely. -/
theorem summable_norm_inner_adjoint_apply
    (hS : S ∈ ((hilbertSchmidt.{u, w, v} 𝕜).operatorGauge F E).finiteSubmodule)
    (hT : T ∈ ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule)
    (b : HilbertBasis ι 𝕜 E) :
    Summable fun j ↦ ‖⟪adjoint S (b j), T (b j)⟫_𝕜‖ :=
  (summable_norm_apply_mul_norm_apply (adjoint S) T b
    ((mem_finiteSubmodule_hilbertSchmidt_iff _ b).1 (adjoint_mem_hilbertSchmidt hS))
    ((mem_finiteSubmodule_hilbertSchmidt_iff _ b).1 hT)).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun _ ↦ norm_inner_le_norm _ _

/-- **Cyclicity for Hilbert–Schmidt operators.** For Hilbert–Schmidt operators `T : E → F` and
`S : F → E`, `Tr (S T) = Tr (T S)`. Neither factor need be trace class. -/
theorem trace_comp_comm_of_mem_hilbertSchmidt
    (hS : S ∈ ((hilbertSchmidt.{u, w, v} 𝕜).operatorGauge F E).finiteSubmodule)
    (hT : T ∈ ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule) :
    (S ∘L T).trace = (T ∘L S).trace := by
  obtain ⟨_, c, -⟩ := exists_hilbertBasis 𝕜 F
  refine (hasSum_inner_adjoint_apply_apply_trace_comp hS hT c).unique ?_
  simpa [adjoint_inner_left] using hasSum_inner_apply_trace c (comp_mem_traceClass hT hS)

/-- The trace of a product of Hilbert–Schmidt operators is bounded by the product of their
Hilbert–Schmidt norms: `|Tr (S T)| ≤ ‖S‖_HS ‖T‖_HS`. -/
theorem norm_trace_comp_le
    (hS : S ∈ ((hilbertSchmidt.{u, w, v} 𝕜).operatorGauge F E).finiteSubmodule)
    (hT : T ∈ ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule) :
    ‖(S ∘L T).trace‖ ≤ S.hilbertSchmidtNorm * T.hilbertSchmidtNorm :=
  (norm_trace_le (comp_mem_traceClass hS hT)).trans (toReal_nuclearENorm_comp_le hS hT)

/-! ### The Hilbert–Schmidt pairing -/

variable {S T : E →L[𝕜] F}

/-- **The Hilbert–Schmidt pairing as a trace.** For Hilbert–Schmidt operators `S, T : E → F` and
any Hilbert basis `(eⱼ)` of `E`, `Tr (S† T) = ∑ⱼ ⟪S eⱼ, T eⱼ⟫`, and the sum converges absolutely
(`ContinuousLinearMap.summable_norm_inner_apply_apply`). -/
theorem hasSum_inner_apply_apply_trace_adjoint_comp
    (hS : S ∈ ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule)
    (hT : T ∈ ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule)
    (b : HilbertBasis ι 𝕜 E) :
    HasSum (fun j ↦ ⟪S (b j), T (b j)⟫_𝕜) (adjoint S ∘L T).trace := by
  simpa using hasSum_inner_adjoint_apply_trace_comp (adjoint_mem_hilbertSchmidt hS) hT b

/-- The sum `∑ⱼ ⟪S eⱼ, T eⱼ⟫` of the Hilbert–Schmidt pairing converges absolutely. -/
theorem summable_norm_inner_apply_apply
    (hS : S ∈ ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule)
    (hT : T ∈ ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule)
    (b : HilbertBasis ι 𝕜 E) :
    Summable fun j ↦ ‖⟪S (b j), T (b j)⟫_𝕜‖ := by
  simpa using summable_norm_inner_adjoint_apply (adjoint_mem_hilbertSchmidt hS) hT b

/-- **The trace of `T† T`** is the squared Hilbert–Schmidt norm of `T`. -/
theorem trace_adjoint_comp_self
    (hT : T ∈ ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule) :
    (adjoint T ∘L T).trace = ((T.hilbertSchmidtNorm ^ 2 : ℝ) : 𝕜) := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 E
  have hE := (mem_finiteSubmodule_hilbertSchmidt_iff T b).1 hT
  have hfin (i : _) : ‖T (b i)‖ₑ ^ 2 ≠ ∞ := by simp
  -- In `ℝ`, the squared column norms sum to the squared Hilbert–Schmidt norm.
  have hsum : HasSum (fun i ↦ ‖T (b i)‖ ^ 2) (T.hilbertSchmidtNorm ^ 2) := by
    rw [T.sq_hilbertSchmidtNorm b, hilbertSchmidtEnergy_def, ENNReal.tsum_toReal_eq hfin]
    have := ENNReal.summable_toReal (hilbertSchmidtEnergy_def T b ▸ hE)
    simpa using this.hasSum
  refine (hasSum_inner_apply_apply_trace_adjoint_comp hT hT b).unique ?_
  simpa [inner_self_eq_norm_sq_to_K] using hsum.mapL (RCLike.ofRealCLM (K := 𝕜))

end ContinuousLinearMap

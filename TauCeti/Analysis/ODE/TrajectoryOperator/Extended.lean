/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Parametric
public import TauCeti.Analysis.Fredholm.Stabilization
public import TauCeti.Analysis.ODE.EnergyEstimate.Lyapunov
public import TauCeti.Analysis.ODE.TrajectoryOperator.Kernel
import Mathlib.MeasureTheory.Integral.ExpDecay
import TauCeti.Analysis.ODE.Caratheodory
import TauCeti.Analysis.Sobolev.GraphStep.ZeroAtInfty

/-!
# Weighted trajectory operators extended by free endpoint variables

Let `A : ℝ → End(F)` be a continuous family of operators, `D_A u = u' + A u` its trajectory
operator, and `w : ℝ → ℝ` a weight with derivative `w'`. Multiplication by `exp w` identifies the
weighted space `{u | exp w • u ∈ L²}` with `L²` and conjugates `D_A` to the trajectory operator of
`A - w' • id` (see `TauCeti.Analysis.ODE.EnergyEstimate.Weighted`). A decay weight, with `w'`
tending to `δ > 0` at `+∞`, makes the weighted operator Fredholm even when the limit `A⁺` is not
invertible, as long as `A⁺ - δ • id` is, but the solutions it sees must then decay to `0` at the
rate `δ`. The solutions that converge to a nonzero vector of `ker A⁺`, which are the ones a
Morse–Bott end produces, are recovered by adjoining that vector as a free endpoint variable.

For a finite family of ends `i`, each with a finite-dimensional space `V i` of endpoint vectors and
a cutoff `χ i` with derivative `χ' i`, the **extended operator**
(`TauCeti.WeakDerivStep.extendedTrajectoryOperator`) is

`D_ext (ξ, v) = D_{A - w'} ξ + ∑ i, exp w • D_A (χ i • v i)`,

acting on `W^{1,2}(ℝ, F) × ∏ i, V i`. In terms of `u = exp (-w) • ξ + ∑ i, χ i • v i`, it is the
weighted image `exp w • D_A u`. The extra term is
`exp w • D_A (χ v) = exp w • (χ' v + χ A v)` (`TauCeti.weightedCutoffTerm`). It must be square
integrable, the weighted-tail condition; then it is a bounded linear map of the endpoint vectors
(`TauCeti.weightedCutoffExtension`). For `v ∈ ker A⁺` and a cutoff equal to `1` near
`+∞`, the tail is `exp w • χ (A - A⁺) v` there, so the condition says that `A` converges to `A⁺`
on `V` faster than the weight grows. With `‖A s v‖ ≤ C exp (-κ s)` and `w s ≤ δ s + c` for large
`s`, it holds as soon as `δ < κ` (`TauCeti.memLp_weightedCutoffTerm_of_le_exp_atTop`, with the
mirror image `TauCeti.memLp_weightedCutoffTerm_of_le_exp_atBot` at `-∞`).

The main results are:

* **Fredholm property and index**
  (`TauCeti.WeakDerivStep.isFredholm_extendedTrajectoryOperator`,
  `TauCeti.WeakDerivStep.index_extendedTrajectoryOperator`). If the weighted operator is Fredholm,
  so is the extended one, and adjoining the endpoint variables raises the index by their total
  dimension: `ind D_ext = ind D_{A - w'} + ∑ i, dim V i`. For a continuous family on a
  finite-dimensional inner product space this applies whenever the shifted limits `A± - δ± • id`
  have Lyapunov forms
  (`TauCeti.WeakDerivStep.isFredholm_extendedTrajectoryOperator_of_hasLyapunovForm`).
* **The kernel consists of solutions with weighted asymptotics**
  (`TauCeti.WeakDerivStep.extendedTrajectoryOperator_eq_zero_iff`). A pair `(ξ, v)` lies in the
  kernel exactly when `ξ` is the weighted difference `exp w • (u - ∑ i, χ i • v i)` for a classical
  solution `u` of `u' + A u = 0`, and every such solution whose weighted difference is square
  integrable comes from the kernel
  (`TauCeti.WeakDerivStep.exists_extendedTrajectoryOperator_eq_zero_of_hasDerivAt`). Reading off
  the initial value of `u` and the endpoint vectors identifies the kernel with the space
  `TauCeti.weightedAsymptoticSolutions` of such solutions
  (`TauCeti.WeakDerivStep.kerExtendedTrajectoryOperatorEquiv`,
  `TauCeti.WeakDerivStep.finrank_ker_extendedTrajectoryOperator`).

Which endpoint vectors to adjoin is part of the data: the kernel description does not ask `V i` to
lie in a kernel of a limit, which is only what makes the weighted-tail condition hold. The exact
kernel and cokernel sequence relating `D_ext` to `D_{A - w'}` is the general one of a
stabilization by finitely many parameters (`ContinuousLinearMap.exact_kerCoprodHom_parameterProj`
and `ContinuousLinearMap.exact_parameterToCoker_cokerCoprodHom`).

## References

* R. B. Lockhart and R. C. McOwen, *Elliptic differential operators on noncompact manifolds*,
  Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) **12** (1985), 409–447 (exponentially weighted
  spaces, and the extension of weighted spaces by the asymptotic kernel at the ends).
* D. M. Austin and P. J. Braam, *Morse–Bott theory and equivariant cohomology*, in *The Floer
  memorial volume*, Progr. Math. **133**, Birkhäuser, 1995, 123–183 (weighted spaces with free
  endpoint variables for trajectories between critical manifolds).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter Real
open scoped ENNReal Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The weighted cutoff term -/

/-- The **weighted cutoff term** `exp (w s) • (χ' s • v + χ s • A s v)`. When `χ'` is the
derivative of `χ`, it is the weighted image `exp w • D_A (χ v)` of the path `s ↦ χ s • v` under
the trajectory operator `D_A u = u' + A u`: the term that adjoining the endpoint vector `v` with
the cutoff `χ` adds to a weighted trajectory operator. -/
def weightedCutoffTerm (A : ℝ → F →L[ℝ] F) (w χ χ' : ℝ → ℝ) (v : F) (s : ℝ) : F :=
  exp (w s) • (χ' s • v + χ s • A s v)

theorem weightedCutoffTerm_def (A : ℝ → F →L[ℝ] F) (w χ χ' : ℝ → ℝ) (v : F) (s : ℝ) :
    weightedCutoffTerm A w χ χ' v s = exp (w s) • (χ' s • v + χ s • A s v) := (rfl)

variable {A : ℝ → F →L[ℝ] F} {w : ℝ → ℝ}

section Term

variable {χ χ' : ℝ → ℝ}

@[simp]
theorem weightedCutoffTerm_zero : weightedCutoffTerm A w χ χ' 0 = 0 := by
  ext s
  simp [weightedCutoffTerm]

theorem weightedCutoffTerm_add (v v' : F) :
    weightedCutoffTerm A w χ χ' (v + v') =
      weightedCutoffTerm A w χ χ' v + weightedCutoffTerm A w χ χ' v' := by
  ext s
  simp only [weightedCutoffTerm, map_add, smul_add, Pi.add_apply]
  abel

theorem weightedCutoffTerm_smul (c : ℝ) (v : F) :
    weightedCutoffTerm A w χ χ' (c • v) = c • weightedCutoffTerm A w χ χ' v := by
  ext s
  simp only [weightedCutoffTerm, map_smul, Pi.smul_apply, smul_add, smul_comm c]

theorem continuous_weightedCutoffTerm (hA : Continuous A) (hw : Continuous w)
    (hχ : Continuous χ) (hχ' : Continuous χ') (v : F) :
    Continuous (weightedCutoffTerm A w χ χ' v) :=
  (continuous_exp.comp hw).smul ((hχ'.smul continuous_const).add
    (hχ.smul (hA.clm_apply continuous_const)))

/-- **The weighted-tail condition at `+∞`.** Let `χ` vanish below `a` and be bounded by `M` beyond
`b`, and let `χ'` be supported in `[a, b]`. If beyond `b` the coefficient decays on `v` at the rate
`κ`,
`‖A s v‖ ≤ C exp (-κ s)`, and the weight grows at most at the rate `δ < κ`, `w s ≤ δ s + c`, then
the weighted cutoff term is square integrable. -/
theorem memLp_weightedCutoffTerm_of_le_exp_atTop (hA : Continuous A) (hw : Continuous w)
    (hχ : Continuous χ) (hχ' : Continuous χ') {v : F} {a b c C M δ κ : ℝ} (hδκ : δ < κ)
    (hχa : ∀ s < a, χ s = 0) (hχM : ∀ s > b, |χ s| ≤ M) (hχ'ab : ∀ s ∉ Icc a b, χ' s = 0)
    (hAv : ∀ s > b, ‖A s v‖ ≤ C * exp (-(κ * s))) (hwb : ∀ s > b, w s ≤ δ * s + c) :
    MemLp (weightedCutoffTerm A w χ χ' v) 2 := by
  set f := weightedCutoffTerm A w χ χ' v
  have hf : Continuous f := continuous_weightedCutoffTerm hA hw hχ hχ' v
  -- On the compact window `[a, b]` the term is bounded; beyond `b` only `χ A v` survives.
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) hf.continuousOn
  set g : ℝ → ℝ := (Icc a b).indicator (fun _ ↦ K) +
    (Ioi b).indicator (fun s ↦ M * C * exp c * exp (-((κ - δ) * s)))
  have hg : MemLp g 2 := by
    refine (memLp_indicator_const 2 measurableSet_Icc.nullMeasurableSet K
      (Or.inr measure_Icc_lt_top.ne)).add ?_
    rw [memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet,
      memLp_two_iff_integrable_sq (by fun_prop)]
    have h : IntegrableOn (fun s ↦ (M * C * exp c) ^ 2 * exp (-(2 * (κ - δ)) * s)) (Ioi b) :=
      (exp_neg_integrableOn_Ioi b (mul_pos two_pos (sub_pos.2 hδκ))).const_mul _
    refine h.congr_fun (fun s _ ↦ ?_) measurableSet_Ioi
    simp only [mul_pow, ← exp_nat_mul]
    push_cast
    ring_nf
  refine hg.of_le hf.aestronglyMeasurable (.of_forall fun s ↦ ?_)
  refine (?_ : ‖f s‖ ≤ g s).trans ((le_abs_self _).trans_eq (Real.norm_eq_abs _).symm)
  rcases lt_or_ge b s with hbs | hsb
  · have hχ's : χ' s = 0 := hχ'ab s fun h ↦ hbs.not_ge h.2
    have hgs : g s = M * C * exp c * exp (-((κ - δ) * s)) := by
      simp [g, indicator_of_mem (show s ∈ Ioi b from hbs),
        indicator_of_notMem (show s ∉ Icc a b from fun h ↦ hbs.not_ge h.2)]
    have hM : 0 ≤ M := (abs_nonneg _).trans (hχM s hbs)
    rw [hgs, show f s = exp (w s) • χ s • A s v by simp [f, weightedCutoffTerm, hχ's], norm_smul,
      norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _), Real.norm_eq_abs]
    calc exp (w s) * (|χ s| * ‖A s v‖) ≤ exp (δ * s + c) * (M * (C * exp (-(κ * s)))) := by
          gcongr
          · exact hwb s hbs
          · exact hχM s hbs
          · exact hAv s hbs
      _ = M * C * exp c * exp (-((κ - δ) * s)) := by
          rw [show -((κ - δ) * s) = δ * s - κ * s by ring, exp_add, exp_sub, exp_neg]
          field_simp
  · rcases lt_or_ge s a with has | has
    · have hfs : f s = 0 := by
        simp [f, weightedCutoffTerm, hχa s has, hχ'ab s fun h ↦ has.not_ge h.1]
      have hgs : g s = 0 := by
        simp [g, indicator_of_notMem (show s ∉ Icc a b from fun h ↦ has.not_ge h.1),
          indicator_of_notMem (show s ∉ Ioi b from hsb.not_gt)]
      simp [hfs, hgs]
    · have hgs : g s = K := by
        simp [g, indicator_of_mem (show s ∈ Icc a b from ⟨has, hsb⟩),
          indicator_of_notMem (show s ∉ Ioi b from hsb.not_gt)]
      rw [hgs]
      exact hK s ⟨has, hsb⟩

/-- **The weighted-tail condition at `-∞`**, the mirror image of
`TauCeti.memLp_weightedCutoffTerm_of_le_exp_atTop`. Let `χ` vanish above `a` and be bounded by `M`
below `b`, and let `χ'` be supported in `[b, a]`. If below `b` the coefficient decays on `v` at the
rate `κ`,
`‖A s v‖ ≤ C exp (κ s)`, and the weight grows at most at the rate `δ < κ`, `w s ≤ -δ s + c`, then
the weighted cutoff term is square integrable. -/
theorem memLp_weightedCutoffTerm_of_le_exp_atBot (hA : Continuous A) (hw : Continuous w)
    (hχ : Continuous χ) (hχ' : Continuous χ') {v : F} {a b c C M δ κ : ℝ} (hδκ : δ < κ)
    (hχa : ∀ s > a, χ s = 0) (hχM : ∀ s < b, |χ s| ≤ M) (hχ'ab : ∀ s ∉ Icc b a, χ' s = 0)
    (hAv : ∀ s < b, ‖A s v‖ ≤ C * exp (κ * s)) (hwb : ∀ s < b, w s ≤ -(δ * s) + c) :
    MemLp (weightedCutoffTerm A w χ χ' v) 2 := by
  -- Reflect `s ↦ -s` and apply the statement at `+∞`.
  have h := memLp_weightedCutoffTerm_of_le_exp_atTop (A := fun s ↦ A (-s)) (w := fun s ↦ w (-s))
    (χ := fun s ↦ χ (-s)) (χ' := fun s ↦ χ' (-s)) (v := v) (a := -a) (b := -b) (c := c) (C := C)
    (M := M) (hA.comp continuous_neg) (hw.comp continuous_neg) (hχ.comp continuous_neg)
    (hχ'.comp continuous_neg) hδκ (fun s hs ↦ hχa _ (by linarith))
    (fun s hs ↦ hχM _ (by linarith))
    (fun s hs ↦ hχ'ab _ fun h ↦ hs ⟨by linarith [h.2], by linarith [h.1]⟩)
    (fun s hs ↦ by simpa using hAv (-s) (by linarith))
    (fun s hs ↦ by linarith [hwb (-s) (by linarith)])
  convert h.comp_measurePreserving (Measure.measurePreserving_neg volume) using 1
  ext s
  simp [weightedCutoffTerm]

end Term

/-! ### The free endpoint term -/

variable {ι : Type*} [Fintype ι] {V : ι → Submodule ℝ F} {χ χ' : ι → ℝ → ℝ}

private theorem memLp_sum_weightedCutoffTerm
    (htail : ∀ i, ∀ v ∈ V i, MemLp (weightedCutoffTerm A w (χ i) (χ' i) v) 2)
    (v : (i : ι) → V i) :
    MemLp (fun s ↦ ∑ i, weightedCutoffTerm A w (χ i) (χ' i) (v i) s) 2
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by
  rw [Opens.coe_top, Measure.restrict_univ]
  exact memLp_finsetSum _ fun i _ ↦ htail i _ (v i).2

variable (A w V χ) in
/-- The **solutions with weighted asymptotics**: the pairs `(x, v)` of an initial value `x` and a
family `v` of endpoint vectors in the spaces `V i` for which some solution `u` of `u' + A u = 0`
with `u 0 = x` has square-integrable weighted difference `exp w • (u - ∑ i, χ i • v i)`. This is a
model of the kernel of the extended trajectory operator
(`TauCeti.WeakDerivStep.kerExtendedTrajectoryOperatorEquiv`), as
`TauCeti.squareIntegrableSolutions` is of the kernel of the trajectory operator. -/
def weightedAsymptoticSolutions : Submodule ℝ (F × ((i : ι) → V i)) where
  carrier := {p | ∃ u : ℝ → F, u 0 = p.1 ∧ (∀ s, HasDerivAt u (-A s (u s)) s) ∧
    MemLp (fun s ↦ exp (w s) • (u s - ∑ i, χ i s • (p.2 i : F))) 2}
  zero_mem' := ⟨0, rfl, fun s ↦ by simp, by simp⟩
  add_mem' := by
    rintro ⟨_, v⟩ ⟨_, v'⟩ ⟨u, rfl, hu, hu2⟩ ⟨u', rfl, hu', hu'2⟩
    refine ⟨u + u', rfl, fun s ↦ by simpa [add_comm] using (hu s).add (hu' s), ?_⟩
    convert hu2.add hu'2 using 1
    ext s
    simp only [Prod.snd_add, Pi.add_apply, Submodule.coe_add, smul_add, Finset.sum_add_distrib]
    module
  smul_mem' := by
    rintro c ⟨_, v⟩ ⟨u, rfl, hu, hu2⟩
    refine ⟨c • u, rfl, fun s ↦ by simpa using (hu s).const_smul c, ?_⟩
    convert hu2.const_smul c using 1
    ext s
    simp only [Prod.smul_snd, Pi.smul_apply, SetLike.val_smul, Finset.smul_sum, smul_sub,
      smul_comm c]

/-- A pair lies in `TauCeti.weightedAsymptoticSolutions A w V χ` when its first component is the
initial value of a solution of `u' + A u = 0` whose weighted difference from its endpoint vectors
is square integrable. -/
theorem mem_weightedAsymptoticSolutions {p : F × ((i : ι) → V i)} :
    p ∈ weightedAsymptoticSolutions A w V χ ↔
      ∃ u : ℝ → F, u 0 = p.1 ∧ (∀ s, HasDerivAt u (-A s (u s)) s) ∧
        MemLp (fun s ↦ exp (w s) • (u s - ∑ i, χ i s • (p.2 i : F))) 2 :=
  Iff.rfl

variable [∀ i, FiniteDimensional ℝ (V i)]

variable (A w χ χ') in
/-- The **free endpoint term** of an extended trajectory operator. For finitely many ends `i`,
each with a finite-dimensional space `V i` of endpoint vectors and a cutoff `χ i` with derivative
`χ' i`, it sends a family `v` of endpoint vectors to the square-integrable path
`s ↦ ∑ i, exp (w s) • (χ' i s • v i + χ i s • A s (v i))`, the weighted image under
`D_A u = u' + A u` of `∑ i, χ i • v i`. The weighted-tail condition `htail` asks each summand to
be square integrable. -/
def weightedCutoffExtension
    (htail : ∀ i, ∀ v ∈ V i, MemLp (weightedCutoffTerm A w (χ i) (χ' i) v) 2) :
    ((i : ι) → V i) →L[ℝ] Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  LinearMap.toContinuousLinearMap
    { toFun v := (memLp_sum_weightedCutoffTerm htail v).toLp _
      map_add' v v' := by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (.of_forall fun s ↦ ?_)
        simp [weightedCutoffTerm_add, Finset.sum_add_distrib]
      map_smul' c v := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (.of_forall fun s ↦ ?_)
        simp [weightedCutoffTerm_smul, Finset.smul_sum] }

/-- The free endpoint term is, almost everywhere, the sum over the ends of the weighted cutoff
terms. -/
theorem coeFn_weightedCutoffExtension
    (htail : ∀ i, ∀ v ∈ V i, MemLp (weightedCutoffTerm A w (χ i) (χ' i) v) 2)
    (v : (i : ι) → V i) :
    ⇑(weightedCutoffExtension A w χ χ' htail v) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ ∑ i, weightedCutoffTerm A w (χ i) (χ' i) (v i) s :=
  (memLp_sum_weightedCutoffTerm htail v).coeFn_toLp

/-! ### The extended operator -/

namespace WeakDerivStep

variable [CompleteSpace F]

/-- The **extended trajectory operator** `D_ext (ξ, v) = D_{AL} ξ + ∑ i, exp w • D_A (χ i • v i)`
on `W^{1,2}(ℝ, F) × ∏ i, V i`, the weighted operator `D_{AL}` extended by the free endpoint
variables `v` through `TauCeti.weightedCutoffExtension`. Its results take `AL` to be an `L∞`
class of the weighted coefficient `A - w' • id`, `w'` the derivative of `w`: then, writing
`u = exp (-w) • ξ + ∑ i, χ i • v i`, the operator sends `(ξ, v)` to `exp w • (u' + A u)`. -/
def extendedTrajectoryOperator (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (htail : ∀ i, ∀ v ∈ V i, MemLp (weightedCutoffTerm A w (χ i) (χ' i) v) 2) :
    (WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ×
      ((i : ι) → V i)) →L[ℝ] Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  (trajectoryOperator AL).coprod (weightedCutoffExtension A w χ χ' htail)

variable {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
  {htail : ∀ i, ∀ v ∈ V i, MemLp (weightedCutoffTerm A w (χ i) (χ' i) v) 2}

/-- The extended operator is the weighted operator on the path plus the free endpoint term on
the endpoint vectors. -/
theorem extendedTrajectoryOperator_apply
    (ξ : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (v : (i : ι) → V i) :
    extendedTrajectoryOperator AL htail (ξ, v) =
      trajectoryOperator AL ξ + weightedCutoffExtension A w χ χ' htail v :=
  (rfl)

/-- **The extended operator is Fredholm** when the weighted operator is: the free endpoint
variables are finitely many domain directions. -/
theorem isFredholm_extendedTrajectoryOperator (h : (trajectoryOperator (p := 2) AL).IsFredholm) :
    (extendedTrajectoryOperator AL htail).IsFredholm :=
  h.coprod_of_finiteDimensional _

/-- **The index of the extended operator.** Adjoining the free endpoint variables raises the index
of a Fredholm weighted operator by their total dimension,
`ind D_ext = ind D_{AL} + ∑ i, dim V i`. -/
theorem index_extendedTrajectoryOperator (h : (trajectoryOperator (p := 2) AL).IsFredholm) :
    (extendedTrajectoryOperator AL htail).index =
      (trajectoryOperator (p := 2) AL).index + ∑ i, (Module.finrank ℝ (V i) : ℤ) := by
  have := h.finite_ker
  have := h.finite_coker
  rw [extendedTrajectoryOperator, ContinuousLinearMap.index_coprod, Module.finrank_pi_fintype]
  push_cast
  congr 1

/-- **The kernel from classical solutions.** Let `AL` be an `L∞` class of `A - w' • id`, where `w'`
is the derivative of `w` and `χ' i` that of `χ i`. If `u` solves `u' + A u = 0` and its weighted
difference `exp w • (u - ∑ i, χ i • v i)` from the endpoint vectors `v` is square integrable,
then that difference is the value of an element `ξ` with `(ξ, v)` in the kernel of the extended
operator. -/
theorem exists_extendedTrajectoryOperator_eq_zero_of_hasDerivAt {w' : ℝ → ℝ}
    (hw : ∀ s, HasDerivAt w (w' s) s) (hχ : ∀ i s, HasDerivAt (χ i) (χ' i s) s)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    {u : ℝ → F} (hu : ∀ s, HasDerivAt u (-A s (u s)) s) (v : (i : ι) → V i)
    (hv : MemLp (fun s ↦ exp (w s) • (u s - ∑ i, χ i s • (v i : F))) 2) :
    ∃ ξ, extendedTrajectoryOperator AL htail (ξ, v) = 0 ∧
      ⇑(prev (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ξ)
        =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
          fun s ↦ exp (w s) • (u s - ∑ i, χ i s • (v i : F)) := by
  set ψ : ℝ → F := fun s ↦ exp (w s) • (u s - ∑ i, χ i s • (v i : F))
  set g : ℝ → F := fun s ↦ -∑ i, weightedCutoffTerm A w (χ i) (χ' i) (v i) s
  -- `ψ` solves the weighted equation `ψ' = g - (A - w') ψ`.
  have hψ (s : ℝ) : HasDerivAt ψ (g s - (A s - w' s • ContinuousLinearMap.id ℝ F) (ψ s)) s := by
    have hsum : HasDerivAt (fun y ↦ ∑ i, χ i y • (v i : F)) (∑ i, χ' i s • (v i : F)) s :=
      HasDerivAt.fun_sum fun i _ ↦ (hχ i s).smul_const (v i : F)
    have hd := (hw s).exp.smul ((hu s).sub hsum)
    convert hd using 1
    have hc (i : ι) (x : F) : χ i s • w' s • x = w' s • χ i s • x := smul_comm _ _ x
    simp only [g, ψ, weightedCutoffTerm, FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply,
      Pi.smul_apply, ContinuousLinearMap.id_apply, map_sub, map_sum, map_smul, smul_sub, smul_add,
      Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_smul, smul_neg, hc]
    abel
  have hg : MemLp g 2 := (memLp_finsetSum _ fun i _ ↦ htail i _ (v i).2).neg
  obtain ⟨ξ, hξ, hξψ⟩ := exists_trajectoryOperator_ae_eq_of_hasDerivAt hAL hψ hv hg
  refine ⟨ξ, ?_, hξψ⟩
  rw [extendedTrajectoryOperator_apply, Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [Lp.coeFn_add (trajectoryOperator AL ξ) (weightedCutoffExtension A w χ χ' htail v),
    hξ, coeFn_weightedCutoffExtension htail v] with s hs h1 h2
  rw [hs, Pi.add_apply, h1, h2, neg_add_cancel, Pi.zero_apply]

/-- **The kernel of the extended operator consists of solutions with weighted asymptotics.** Let
`A` be continuous, `w` and the cutoffs `χ i` differentiable with continuous derivatives `w'` and
`χ' i`, and `AL` an `L∞` class of `A - w' • id`. Then `(ξ, v)` lies in the kernel of the extended
operator exactly when `ξ` is, almost everywhere, the weighted difference
`exp w • (u - ∑ i, χ i • v i)` of a classical solution `u` of `u' + A u = 0` from the endpoint
vectors `v`. -/
theorem extendedTrajectoryOperator_eq_zero_iff {w' : ℝ → ℝ} (hA : Continuous A)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w')
    (hχ : ∀ i s, HasDerivAt (χ i) (χ' i s) s) (hχ' : ∀ i, Continuous (χ' i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    (ξ : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (v : (i : ι) → V i) :
    extendedTrajectoryOperator AL htail (ξ, v) = 0 ↔
      ∃ u : ℝ → F, (∀ s, HasDerivAt u (-A s (u s)) s) ∧
        ⇑(prev (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ξ)
          =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
            fun s ↦ exp (w s) • (u s - ∑ i, χ i s • (v i : F)) := by
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun s ↦ (hw s).continuousAt
  have hχc (i : ι) : Continuous (χ i) :=
    continuous_iff_continuousAt.2 fun s ↦ (hχ i s).continuousAt
  constructor
  · intro h0
    set g : ℝ → F := fun s ↦ -∑ i, weightedCutoffTerm A w (χ i) (χ' i) (v i) s
    have hgc : Continuous g := (continuous_finsetSum _ fun i _ ↦
      continuous_weightedCutoffTerm hA hwc (hχc i) (hχ' i) _).neg
    -- The weighted operator sends `ξ` to `g`, so `ξ` is a classical solution of the weighted
    -- equation, which `exp (-w)` turns back into a solution of `u' + A u = 0`.
    have hξg : ⇑(trajectoryOperator AL ξ) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] g := by
      rw [extendedTrajectoryOperator_apply, add_eq_zero_iff_eq_neg] at h0
      filter_upwards [h0 ▸ Lp.coeFn_neg (weightedCutoffExtension A w χ χ' htail v),
        coeFn_weightedCutoffExtension htail v] with s hs h2
      rw [hs, Pi.neg_apply, h2]
    obtain ⟨ψ, hψ, hξψ⟩ := exists_hasDerivAt_of_trajectoryOperator_ae_eq
      (A := fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F) (hA.sub (hw'.smul continuous_const))
      hgc hAL hξg
    refine ⟨fun s ↦ exp (-w s) • ψ s + ∑ i, χ i s • (v i : F), fun s ↦ ?_, ?_⟩
    · have hsum : HasDerivAt (fun y ↦ ∑ i, χ i y • (v i : F)) (∑ i, χ' i s • (v i : F)) s :=
        HasDerivAt.fun_sum fun i _ ↦ (hχ i s).smul_const (v i : F)
      have he (x : F) : exp (-w s) • exp (w s) • x = x := by
        rw [smul_smul, ← exp_add, neg_add_cancel, exp_zero, one_smul]
      convert ((hw s).neg.exp.smul (hψ s)).add hsum using 1
      simp only [g, weightedCutoffTerm, Pi.neg_apply, FunLike.coe_sub, FunLike.coe_smul,
        Pi.sub_apply, Pi.smul_apply, ContinuousLinearMap.id_apply, map_add, map_sum, map_smul,
        smul_sub, smul_add, smul_neg, Finset.smul_sum, he, Finset.sum_add_distrib, mul_neg,
        neg_smul, mul_smul]
      abel
    · filter_upwards [hξψ] with s hs
      rw [hs, add_sub_cancel_right, smul_smul, ← exp_add, add_neg_cancel, exp_zero, one_smul]
  · rintro ⟨u, hu, hξu⟩
    have hv : MemLp (fun s ↦ exp (w s) • (u s - ∑ i, χ i s • (v i : F))) 2 := by
      simpa using (Lp.memLp (prev (ContinuousLinearMap.id ℝ
        (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ξ)).ae_eq hξu
    obtain ⟨ξ', h0, hξ'u⟩ :=
      exists_extendedTrajectoryOperator_eq_zero_of_hasDerivAt (htail := htail) hw hχ hAL hu v hv
    have hξ : ξ = ξ' := ext (Lp.ext (hξu.trans hξ'u.symm))
    rwa [hξ]

section Kernel

variable (w χ) in
/-- Evaluation `(ξ, v) ↦ (exp (-w 0) • ξ 0 + ∑ i, χ i 0 • v i, v)` at time `0`, through the
continuous representative of `ξ`: on the kernel of the extended operator, the initial value of
the solution `u = exp (-w) • ξ + ∑ i, χ i • v i` together with the endpoint vectors. -/
private def extendedEval :
    (WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ×
      ((i : ι) → V i)) →ₗ[ℝ] F × ((i : ι) → V i) where
  toFun p := (exp (-w 0) • toZeroAtInfty ENNReal.ofNat_ne_top p.1 0 + ∑ i, χ i 0 • (p.2 i : F), p.2)
  map_add' p q := by
    rw [Prod.mk_add_mk]
    congr 1
    simp only [map_add, add_apply,
      Pi.add_apply, Submodule.coe_add, smul_add, Finset.sum_add_distrib]
    abel
  map_smul' c p := by
    rw [RingHom.id_apply, Prod.smul_mk]
    congr 1
    simp only [map_smul, smul_apply,
      Pi.smul_apply, SetLike.val_smul, smul_add, Finset.smul_sum, smul_comm c]

variable {w' : ℝ → ℝ}

omit [∀ i, FiniteDimensional ℝ (V i)] in
/-- The continuous representative of the first component of a kernel element is the weighted
difference `exp w • (u - ∑ i, χ i • v i)` of the corresponding solution. -/
private theorem coe_toZeroAtInfty_of_ae_eq (hw : ∀ s, HasDerivAt w (w' s) s)
    (hχ : ∀ i s, HasDerivAt (χ i) (χ' i s) s)
    {ξ : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    {v : (i : ι) → V i} {u : ℝ → F} (hu : ∀ s, HasDerivAt u (-A s (u s)) s)
    (hξu : ⇑(prev (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ξ)
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ exp (w s) • (u s - ∑ i, χ i s • (v i : F))) :
    ⇑(toZeroAtInfty ENNReal.ofNat_ne_top ξ) =
      fun s ↦ exp (w s) • (u s - ∑ i, χ i s • (v i : F)) := by
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun s ↦ (hw s).continuousAt
  have huc : Continuous u := continuous_iff_continuousAt.2 fun s ↦ (hu s).continuousAt
  have hχc (i : ι) : Continuous (χ i) :=
    continuous_iff_continuousAt.2 fun s ↦ (hχ i s).continuousAt
  refine coe_toZeroAtInfty_eq_of_ae_eq ENNReal.ofNat_ne_top ((continuous_exp.comp hwc).smul (huc.sub
    (continuous_finsetSum _ fun i _ ↦ (hχc i).smul continuous_const))) ?_
  simpa using hξu

omit [∀ i, FiniteDimensional ℝ (V i)] in
private theorem extendedEval_eq (hw : ∀ s, HasDerivAt w (w' s) s)
    (hχ : ∀ i s, HasDerivAt (χ i) (χ' i s) s)
    {ξ : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    {v : (i : ι) → V i} {u : ℝ → F} (hu : ∀ s, HasDerivAt u (-A s (u s)) s)
    (hξu : ⇑(prev (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ξ)
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ exp (w s) • (u s - ∑ i, χ i s • (v i : F))) :
    extendedEval w χ (ξ, v) = (u 0, v) := by
  have h := congrFun (coe_toZeroAtInfty_of_ae_eq hw hχ hu hξu) 0
  simp only [extendedEval, LinearMap.coe_mk, AddHom.coe_mk, h, smul_smul, ← exp_add,
    neg_add_cancel, exp_zero, one_smul, sub_add_cancel]

/-- Hypotheses shared by the kernel description: `A` is continuous, `w` and the cutoffs `χ i`
have continuous derivatives `w'` and `χ' i`, and `AL` is an `L∞` class of `A - w' • id`. -/
private theorem extendedEval_mem (hA : Continuous A) (hw : ∀ s, HasDerivAt w (w' s) s)
    (hw' : Continuous w') (hχ : ∀ i s, HasDerivAt (χ i) (χ' i s) s)
    (hχ' : ∀ i, Continuous (χ' i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    {q : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ×
      ((i : ι) → V i)} (h0 : extendedTrajectoryOperator AL htail q = 0) :
    extendedEval w χ q ∈ weightedAsymptoticSolutions A w V χ := by
  obtain ⟨ξ, v⟩ := q
  obtain ⟨u, hu, hξu⟩ := (extendedTrajectoryOperator_eq_zero_iff hA hw hw' hχ hχ' hAL ξ v).1 h0
  rw [extendedEval_eq hw hχ hu hξu]
  refine ⟨u, rfl, hu, ?_⟩
  simpa using (Lp.memLp (prev (ContinuousLinearMap.id ℝ
    (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ξ)).ae_eq hξu

/-- A kernel element with zero evaluation vanishes: its solution has zero initial value, hence
vanishes, and its endpoint vectors are zero. -/
private theorem eq_zero_of_extendedEval_eq_zero (hA : Continuous A)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w')
    (hχ : ∀ i s, HasDerivAt (χ i) (χ' i s) s) (hχ' : ∀ i, Continuous (χ' i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    {q : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ×
      ((i : ι) → V i)} (h0 : extendedTrajectoryOperator AL htail q = 0)
    (he : extendedEval w χ q = 0) : q = 0 := by
  obtain ⟨ξ, v⟩ := q
  obtain ⟨u, hu, hξu⟩ := (extendedTrajectoryOperator_eq_zero_iff hA hw hw' hχ hχ' hAL ξ v).1 h0
  rw [extendedEval_eq hw hχ hu hξu, Prod.mk_eq_zero] at he
  have hu0 : u = 0 := hA.neg.eq_of_hasDerivAt_clm_apply hu (fun s ↦ by simp) (t₀ := 0)
    (by simpa using he.1)
  have hprev : prev (ContinuousLinearMap.id ℝ
      (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ξ = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hξu] with s hs
    rw [hs, hu0, he.2]
    simp
  rw [Prod.mk_eq_zero]
  exact ⟨ext (by rw [hprev, prev_zero]), he.2⟩

/-- Evaluation on the kernel of the extended operator, with values in the solutions with weighted
asymptotics. -/
private def kerExtendedEval (hA : Continuous A) (hw : ∀ s, HasDerivAt w (w' s) s)
    (hw' : Continuous w') (hχ : ∀ i s, HasDerivAt (χ i) (χ' i s) s)
    (hχ' : ∀ i, Continuous (χ' i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F) :
    (extendedTrajectoryOperator AL htail).ker →ₗ[ℝ] weightedAsymptoticSolutions A w V χ :=
  ((extendedEval w χ).domRestrict (extendedTrajectoryOperator AL htail).ker).codRestrict _
    fun p ↦ extendedEval_mem hA hw hw' hχ hχ' hAL p.2

private theorem coe_kerExtendedEval (hA : Continuous A) (hw : ∀ s, HasDerivAt w (w' s) s)
    (hw' : Continuous w') (hχ : ∀ i s, HasDerivAt (χ i) (χ' i s) s)
    (hχ' : ∀ i, Continuous (χ' i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    (p : (extendedTrajectoryOperator AL htail).ker) :
    (kerExtendedEval hA hw hw' hχ hχ' hAL p : F × ((i : ι) → V i)) = extendedEval w χ p :=
  rfl

private theorem bijective_kerExtendedEval (hA : Continuous A) (hw : ∀ s, HasDerivAt w (w' s) s)
    (hw' : Continuous w') (hχ : ∀ i s, HasDerivAt (χ i) (χ' i s) s)
    (hχ' : ∀ i, Continuous (χ' i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F) :
    Function.Bijective (kerExtendedEval (htail := htail) hA hw hw' hχ hχ' hAL) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun p he ↦ Subtype.ext ?_, fun q ↦ ?_⟩
  · have he' := congrArg Subtype.val he
    rw [coe_kerExtendedEval, ZeroMemClass.coe_zero] at he'
    exact eq_zero_of_extendedEval_eq_zero hA hw hw' hχ hχ' hAL p.2 he'
  · obtain ⟨⟨x, v⟩, hq⟩ := q
    -- Unification of these membership and existence statements against their uses is slow, so
    -- their implicit arguments are given and the existential is used through `choose`.
    have hq' := (mem_weightedAsymptoticSolutions (A := A) (w := w) (V := V) (χ := χ)
      (p := (x, v))).1 hq
    obtain ⟨u, hu0, hu, hv⟩ := hq'
    dsimp only at hu0 hv
    have key := exists_extendedTrajectoryOperator_eq_zero_of_hasDerivAt (A := A) (w := w) (V := V)
      (χ := χ) (χ' := χ') (AL := AL) (htail := htail) (w' := w') hw hχ hAL hu v hv
    refine ⟨⟨(key.choose, v), key.choose_spec.1⟩, Subtype.ext ?_⟩
    rw [coe_kerExtendedEval, extendedEval_eq hw hχ hu key.choose_spec.2, hu0]

/-- **The kernel of the extended operator is the space of solutions with weighted asymptotics.**
Under the hypotheses of `TauCeti.WeakDerivStep.extendedTrajectoryOperator_eq_zero_iff`, sending a
kernel element `(ξ, v)` to the initial value of the solution `u = exp (-w) • ξ + ∑ i, χ i • v i`
together with `v` is a linear equivalence onto `TauCeti.weightedAsymptoticSolutions A w V χ`. -/
def kerExtendedTrajectoryOperatorEquiv (hA : Continuous A) (hw : ∀ s, HasDerivAt w (w' s) s)
    (hw' : Continuous w') (hχ : ∀ i s, HasDerivAt (χ i) (χ' i s) s)
    (hχ' : ∀ i, Continuous (χ' i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F) :
    (extendedTrajectoryOperator AL htail).ker ≃ₗ[ℝ] weightedAsymptoticSolutions A w V χ :=
  LinearEquiv.ofBijective _ (bijective_kerExtendedEval hA hw hw' hχ hχ' hAL)

/-- The equivalence `kerExtendedTrajectoryOperatorEquiv` sends a kernel element `(ξ, v)` to
`(u 0, v)`, for the solution `u` of `u' + A u = 0` whose weighted difference
`exp w • (u - ∑ i, χ i • v i)` represents `ξ`. -/
theorem kerExtendedTrajectoryOperatorEquiv_apply (hA : Continuous A)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w')
    (hχ : ∀ i s, HasDerivAt (χ i) (χ' i s) s) (hχ' : ∀ i, Continuous (χ' i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F)
    (p : (extendedTrajectoryOperator AL htail).ker) {u : ℝ → F}
    (hu : ∀ s, HasDerivAt u (-A s (u s)) s)
    (hξu : ⇑(prev (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
      p.1.1) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ exp (w s) • (u s - ∑ i, χ i s • (p.1.2 i : F))) :
    (kerExtendedTrajectoryOperatorEquiv hA hw hw' hχ hχ' hAL p : F × ((i : ι) → V i)) =
      (u 0, p.1.2) :=
  extendedEval_eq hw hχ hu hξu

/-- The kernel of the extended operator has the dimension of the space of solutions with weighted
asymptotics. -/
theorem finrank_ker_extendedTrajectoryOperator (hA : Continuous A)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w')
    (hχ : ∀ i s, HasDerivAt (χ i) (χ' i s) s) (hχ' : ∀ i, Continuous (χ' i))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ F) :
    Module.finrank ℝ (extendedTrajectoryOperator AL htail).ker =
      Module.finrank ℝ (weightedAsymptoticSolutions A w V χ) :=
  (kerExtendedTrajectoryOperatorEquiv hA hw hw' hχ hχ' hAL).finrank_eq

end Kernel

/-- **The extended operator with hyperbolic shifted limits is Fredholm.** Let `A` be a continuous
family of operators on a finite-dimensional real inner product space with limits `A±` at `±∞`, and
`w'` a continuous weight slope with limits `δ±`. If the shifted limits `A± - δ± • id` have Lyapunov
forms, that is, have no purely imaginary eigenvalue, then for any `L∞` class `AL` of
`A - w' • id` the extended operator is Fredholm. -/
theorem isFredholm_extendedTrajectoryOperator_of_hasLyapunovForm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {A : ℝ → E →L[ℝ] E}
    {w : ℝ → ℝ} {V : ι → Submodule ℝ E} {χ χ' : ι → ℝ → ℝ} {w' : ℝ → ℝ}
    (hA : Continuous A) (hw' : Continuous w') {Aminus Aplus : E →L[ℝ] E} {δminus δplus : ℝ}
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hw'bot : Tendsto w' atBot (𝓝 δminus)) (hw'top : Tendsto w' atTop (𝓝 δplus))
    (hminus : (Aminus - δminus • ContinuousLinearMap.id ℝ E).HasLyapunovForm)
    (hplus : (Aplus - δplus • ContinuousLinearMap.id ℝ E).HasLyapunovForm)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - w' s • ContinuousLinearMap.id ℝ E)
    (htail : ∀ i, ∀ v ∈ V i, MemLp (weightedCutoffTerm A w (χ i) (χ' i) v) 2) :
    (extendedTrajectoryOperator AL htail).IsFredholm :=
  isFredholm_extendedTrajectoryOperator <| isFredholm_trajectoryOperator_of_hasLyapunovForm
    (hA.sub (hw'.smul continuous_const)) hminus hplus
    (hbot.sub (hw'bot.smul tendsto_const_nhds)) (htop.sub (hw'top.smul tendsto_const_nhds)) AL hAL

end WeakDerivStep

end TauCeti

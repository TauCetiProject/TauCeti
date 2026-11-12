/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.IonescuTulcea.Traj
public import TauCeti.MeasureTheory.OptimalTransport.Coupling
public import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# Gluing a countable chain of transport plans

This file turns a sequence of finite measures on consecutive products
`X n × X (n + 1)`, with matching adjacent marginals, into a finite measure on the path
space `∀ n, X n`. Its projection to every consecutive pair is the prescribed measure.
Probability plans give a probability path law.

The construction uses Mathlib's Ionescu--Tulcea trajectory measure. At step `n`, the conditional
kernel of the prescribed `(n, n + 1)`-plan is pulled back along evaluation at the last point of the
current finite trajectory. The main result is `TauCeti.Measure.map_adjacent_chainMeasure`.

For a chain of couplings on a fixed space,
`TauCeti.Measure.map_adjacent_chainMeasure_of_isCoupling` packages the matching-marginal
hypothesis, while `TauCeti.Measure.exists_measurable_isCoupling_map_chainMeasure` extracts a
measurable pathwise limit when almost every trajectory is Cauchy.

The finite-prefix results project this path law to any initial segment of the supplied countable
chain; see `TauCeti.Measure.map_adjacent_prefixChainMeasure`. Complementing sequential chains,
`MeasureTheory.Measure.starMeasure` glues a countable star of finite plans sharing a common first
marginal onto `X₀ × (∀ n, Y n)`, realizing every plan simultaneously as the `(w.1, w.2 n)`-marginal.
This supplies the countable gluing constructions needed by optimal transport without rebuilding
Mathlib's trajectory-measure construction.
-/

public section

open Filter Finset MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Measure

universe u

variable {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]

section Chain

variable [∀ n, StandardBorelSpace (X (n + 1))] [∀ n, Nonempty (X (n + 1))]

/-- The transition kernel associated to a chain of consecutive plans. It disintegrates the
`n`th plan over its first coordinate and depends on a finite trajectory only through its last
coordinate. -/
private noncomputable def chainKernel (pi : ∀ n, Measure (X n × X (n + 1)))
    [∀ n, IsFiniteMeasure (pi n)] (n : ℕ) :
    Kernel ((i : Iic n) → X i) (X (n + 1)) :=
  (pi n).condKernel.comap
    (fun x : (i : Iic n) → X i ↦ x ⟨n, mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply (X := fun i : Iic n ↦ X i) ⟨n, mem_Iic.mpr le_rfl⟩)

private instance chainKernel.instIsMarkovKernel (pi : ∀ n, Measure (X n × X (n + 1)))
    [∀ n, IsFiniteMeasure (pi n)] (n : ℕ) : IsMarkovKernel (chainKernel pi n) := by
  rw [chainKernel]
  infer_instance

/-- The path law obtained by disintegrating and iterating a countable chain of consecutive
finite plans. -/
noncomputable def chainMeasure (pi : ∀ n, Measure (X n × X (n + 1)))
    [∀ n, IsFiniteMeasure (pi n)] : Measure ((n : ℕ) → X n) :=
  Kernel.trajMeasure (pi 0).fst (chainKernel pi)

instance chainMeasure.instIsFiniteMeasure
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (pi n)] :
    IsFiniteMeasure (chainMeasure pi) := by
  rw [chainMeasure]
  infer_instance

instance chainMeasure.instIsProbabilityMeasure
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (pi n)]
    [IsProbabilityMeasure (pi 0)] : IsProbabilityMeasure (chainMeasure pi) := by
  rw [chainMeasure]
  infer_instance

/-- The initial coordinate has the first marginal of the initial plan, without any
matching-marginal assumption. -/
@[simp]
theorem map_eval_zero_chainMeasure
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (pi n)] :
    (chainMeasure pi).map (fun x ↦ x 0) = (pi 0).fst := by
  let e : ((i : Iic 0) → X i) ≃ᵐ X 0 := MeasurableEquiv.piUnique _
  have heval : (fun x : (n : ℕ) → X n ↦ x 0) = e ∘ frestrictLe 0 := by
    funext x
    rfl
  have hprefix : (chainMeasure pi).map (frestrictLe 0) = (pi 0).fst.map e.symm := by
    simp [chainMeasure, Kernel.trajMeasure, e,
      MeasureTheory.Measure.map_comp _ _ (measurable_frestrictLe 0),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, MeasureTheory.Measure.id_comp]
  calc
    (chainMeasure pi).map (fun x ↦ x 0)
        = ((chainMeasure pi).map (frestrictLe 0)).map e := by
            rw [heval]
            exact (MeasureTheory.Measure.map_map e.measurable (measurable_frestrictLe 0)).symm
    _ = (pi 0).fst := by simp [hprefix]

/-- The path law has the total mass of the initial plan, even if later marginals do not match. -/
@[simp]
theorem chainMeasure_univ
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (pi n)] :
    chainMeasure pi Set.univ = pi 0 Set.univ := by
  simpa only [MeasureTheory.Measure.map_apply (measurable_pi_apply 0) MeasurableSet.univ,
    Set.preimage_univ, MeasureTheory.Measure.fst_univ] using
    congrArg (fun μ : Measure (X 0) ↦ μ Set.univ) (map_eval_zero_chainMeasure pi)

private theorem map_adjacent_chainMeasure_of_map_eval
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (pi n)] (n : ℕ)
    (hn : (chainMeasure pi).map (fun x ↦ x n) = (pi n).fst) :
    (chainMeasure pi).map (fun x ↦ (x n, x (n + 1))) = pi n := by
  let last : ((i : Iic n) → X i) → X n := fun x ↦ x ⟨n, mem_Iic.mpr le_rfl⟩
  have hlast : Measurable last := measurable_pi_apply _
  have hpair : (fun x : (k : ℕ) → X k ↦ (x n, x (n + 1))) =
      Prod.map last id ∘ (fun x ↦ (frestrictLe n x, x (n + 1))) := by
    funext x
    rfl
  have heval : last ∘ frestrictLe n = fun x : (k : ℕ) → X k ↦ x n := rfl
  have htraj : (chainMeasure pi).map (fun x ↦ (frestrictLe n x, x (n + 1))) =
      (chainMeasure pi).map (frestrictLe n) ⊗ₘ chainKernel pi n := by
    simpa only [chainMeasure] using
      (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure_of_sFinite
        (μ₀ := (pi 0).fst) (κ := chainKernel pi) n).symm
  have hmarginal : ((chainMeasure pi).map (frestrictLe n)).map last = (pi n).fst := by
    simpa only [MeasureTheory.Measure.map_map hlast (measurable_frestrictLe n), heval] using hn
  calc
    (chainMeasure pi).map (fun x ↦ (x n, x (n + 1)))
        = ((chainMeasure pi).map (fun x ↦ (frestrictLe n x, x (n + 1)))).map
            (Prod.map last id) := by
              rw [hpair]
              exact (MeasureTheory.Measure.map_map (hlast.prodMap measurable_id)
                (by fun_prop)).symm
    _ = ((chainMeasure pi).map (frestrictLe n) ⊗ₘ chainKernel pi n).map
          (Prod.map last id) := by rw [htraj]
    _ = ((chainMeasure pi).map (frestrictLe n)).map last ⊗ₘ (pi n).condKernel := by
          simpa only [chainKernel, last] using
            Measure.map_prodMap_compProd_comap ((chainMeasure pi).map (frestrictLe n))
              (pi n).condKernel hlast
    _ = (pi n).fst ⊗ₘ (pi n).condKernel := by rw [hmarginal]
    _ = pi n := MeasureTheory.Measure.disintegrate _ _

/-- The time-`n` marginal is the first marginal of `pi n`, provided neighboring plans have
matching marginals before time `n`. -/
theorem map_eval_chainMeasure (pi : ∀ n, Measure (X n × X (n + 1)))
    [∀ n, IsFiniteMeasure (pi n)] (n : ℕ)
    (hpi : ∀ k < n, (pi k).snd = (pi (k + 1)).fst) :
    (chainMeasure pi).map (fun x ↦ x n) = (pi n).fst := by
  induction n with
  | zero => exact map_eval_zero_chainMeasure pi
  | succ n ih =>
      have hn := ih (fun k hk ↦ hpi k (Nat.lt_trans hk n.lt_succ_self))
      rw [← MeasureTheory.Measure.snd_map_prodMk (measurable_pi_apply n)
        (measurable_pi_apply (n + 1)), map_adjacent_chainMeasure_of_map_eval pi n hn,
        hpi n n.lt_succ_self]

/-- **Countable chain gluing.** The consecutive-coordinate projection at time `n` is `pi n`,
provided neighboring plans have matching marginals before time `n`. -/
theorem map_adjacent_chainMeasure (pi : ∀ n, Measure (X n × X (n + 1)))
    [∀ n, IsFiniteMeasure (pi n)] (n : ℕ)
    (hpi : ∀ k < n, (pi k).snd = (pi (k + 1)).fst) :
    (chainMeasure pi).map (fun x ↦ (x n, x (n + 1))) = pi n :=
  map_adjacent_chainMeasure_of_map_eval pi n (map_eval_chainMeasure pi n hpi)

/-- The finite trajectory law obtained by projecting `chainMeasure pi` to coordinates at most
`N`. -/
noncomputable def prefixChainMeasure (pi : ∀ n, Measure (X n × X (n + 1)))
    [∀ n, IsFiniteMeasure (pi n)] (N : ℕ) : Measure ((i : Iic N) → X i) :=
  (chainMeasure pi).map (frestrictLe N)

instance prefixChainMeasure.instIsFiniteMeasure
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (pi n)] (N : ℕ) :
    IsFiniteMeasure (prefixChainMeasure pi N) := by
  rw [prefixChainMeasure]
  infer_instance

instance prefixChainMeasure.instIsProbabilityMeasure
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (pi n)]
    [IsProbabilityMeasure (pi 0)] (N : ℕ) : IsProbabilityMeasure (prefixChainMeasure pi N) := by
  rw [prefixChainMeasure]
  infer_instance

/-- Projecting a finite prefix further gives the corresponding shorter prefix. -/
@[simp]
theorem map_frestrictLe₂_prefixChainMeasure
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (pi n)]
    {M N : ℕ} (hMN : M ≤ N) :
    (prefixChainMeasure pi N).map (frestrictLe₂ hMN) = prefixChainMeasure pi M := by
  rw [prefixChainMeasure, MeasureTheory.Measure.map_map (measurable_frestrictLe₂ hMN)
    (measurable_frestrictLe N), frestrictLe₂_comp_frestrictLe]
  rfl

/-- The adjacent projection at time `n` of a finite prefix agrees with `pi n`, as long as both
coordinates occur in the prefix and neighboring plans match before time `n`. -/
theorem map_adjacent_prefixChainMeasure
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (pi n)]
    {n N : ℕ} (hpi : ∀ k < n, (pi k).snd = (pi (k + 1)).fst) (hn : n < N) :
    (prefixChainMeasure pi N).map
        (fun x ↦ (x ⟨n, mem_Iic.mpr (Nat.le_of_lt hn)⟩, x ⟨n + 1, mem_Iic.mpr hn⟩)) = pi n := by
  let adjacent : ((i : Iic N) → X i) → X n × X (n + 1) :=
    fun x ↦ (x ⟨n, mem_Iic.mpr (Nat.le_of_lt hn)⟩, x ⟨n + 1, mem_Iic.mpr hn⟩)
  have hrestrict : adjacent ∘ frestrictLe N = fun x : (k : ℕ) → X k ↦ (x n, x (n + 1)) := by
    funext x
    rfl
  calc
    (prefixChainMeasure pi N).map adjacent
        = (chainMeasure pi).map (adjacent ∘ frestrictLe N) := by
            rw [prefixChainMeasure, MeasureTheory.Measure.map_map (by fun_prop)
              (measurable_frestrictLe N)]
    _ = (chainMeasure pi).map (fun x ↦ (x n, x (n + 1))) := by rw [hrestrict]
    _ = pi n := map_adjacent_chainMeasure pi n hpi

end Chain

section CouplingChain

variable {Y : Type u} [MeasurableSpace Y]

/-- Along the countable gluing `chainMeasure pi` of couplings `pi n` of consecutive laws, the
`n`th and `(n + 1)`st coordinates have joint law `pi n`. -/
theorem map_adjacent_chainMeasure_of_isCoupling [StandardBorelSpace Y] [Nonempty Y]
    {mu : ℕ → Measure Y} {pi : ℕ → Measure (Y × Y)}
    [∀ n, IsFiniteMeasure (pi n)]
    (hpi : ∀ n, IsCoupling (pi n) (mu n) (mu (n + 1))) (n : ℕ) :
    (chainMeasure (X := fun _ ↦ Y) pi).map (fun x ↦ (x n, x (n + 1))) = pi n :=
  map_adjacent_chainMeasure pi n
    (fun k _ ↦ by rw [(hpi k).snd_eq, (hpi (k + 1)).fst_eq])

/-- **The pathwise limit of a glued chain.** If finite couplings `pi n` of consecutive laws
are glued by `chainMeasure` and almost every path is Cauchy, then some measurable `Z` is the
almost-sure limit of the coordinates, and the joint law of the `n`th coordinate and `Z` couples
`mu n` with the law of `Z`. -/
theorem exists_measurable_isCoupling_map_chainMeasure [UniformSpace Y]
    [TopologicalSpace.PseudoMetrizableSpace Y] [BorelSpace Y] [CompleteSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] {mu : ℕ → Measure Y}
    {pi : ℕ → Measure (Y × Y)} [∀ n, IsFiniteMeasure (pi n)]
    (hpi : ∀ n, IsCoupling (pi n) (mu n) (mu (n + 1)))
    (hcauchy : ∀ᵐ x ∂chainMeasure (X := fun _ ↦ Y) pi, CauchySeq fun n ↦ x n) :
    ∃ Z : (ℕ → Y) → Y, Measurable Z ∧
      (∀ᵐ x ∂chainMeasure (X := fun _ ↦ Y) pi,
        Tendsto (fun n ↦ x n) atTop (nhds (Z x))) ∧
      ∀ n, IsCoupling ((chainMeasure (X := fun _ ↦ Y) pi).map fun x ↦ (x n, Z x))
        (mu n) ((chainMeasure (X := fun _ ↦ Y) pi).map Z) := by
  have hev : ∀ n, Measurable fun x : ℕ → Y ↦ x n := fun n ↦ measurable_pi_apply n
  obtain ⟨Z, hZ, hZtendsto⟩ := measurable_limit_of_tendsto_metrizable_ae
    (fun n ↦ (hev n).aemeasurable) (hcauchy.mono fun _ hx ↦ cauchySeq_tendsto_of_complete hx)
  refine ⟨Z, hZ, hZtendsto, fun n ↦ ⟨?_, ?_⟩⟩
  · rw [Measure.fst_map_prodMk (hev n) hZ, ← (hpi n).fst_eq]
    exact map_eval_chainMeasure pi n
      (fun k _ ↦ by rw [(hpi k).snd_eq, (hpi (k + 1)).fst_eq])
  · exact Measure.snd_map_prodMk (hev n) hZ

end CouplingChain

end Measure

end TauCeti

namespace MeasureTheory.Measure

open TauCeti (IsCoupling)

universe u

section Star

variable {X₀ : Type u} [MeasurableSpace X₀] {Y : ℕ → Type u} [∀ n, MeasurableSpace (Y n)]

private abbrev starCarrier (X₀ : Type u) (Y : ℕ → Type u) : ℕ → Type u
  | 0 => X₀
  | n + 1 => Y n

private instance instMeasurableSpaceStarCarrier : ∀ k, MeasurableSpace (starCarrier X₀ Y k)
  | 0 => inferInstanceAs (MeasurableSpace X₀)
  | n + 1 => inferInstanceAs (MeasurableSpace (Y n))

private theorem measurable_toStar :
    Measurable (fun x : (k : ℕ) → starCarrier X₀ Y k ↦ (x 0, fun n ↦ x (n + 1))) :=
  (measurable_pi_apply 0).prodMk (Measurable.of_eval fun n ↦ measurable_pi_apply (n + 1))

variable [∀ n, StandardBorelSpace (Y n)] [∀ n, Nonempty (Y n)]

private noncomputable def starKernel (pi : ∀ n, Measure (X₀ × Y n)) [∀ n, IsFiniteMeasure (pi n)]
    (n : ℕ) : Kernel ((i : Iic n) → starCarrier X₀ Y i) (starCarrier X₀ Y (n + 1)) :=
  (pi n).condKernel.comap
    (fun x : (i : Iic n) → starCarrier X₀ Y i ↦ x ⟨0, mem_Iic.mpr (Nat.zero_le n)⟩)
    (measurable_pi_apply (X := fun i : Iic n ↦ starCarrier X₀ Y i)
      ⟨0, mem_Iic.mpr (Nat.zero_le n)⟩)

private instance starKernel.instIsMarkovKernel (pi : ∀ n, Measure (X₀ × Y n))
    [∀ n, IsFiniteMeasure (pi n)] (n : ℕ) : IsMarkovKernel (starKernel pi n) := by
  rw [starKernel]
  infer_instance

/-- The joint law on `X₀ × (∀ n, Y n)` obtained by disintegrating each finite plan `pi n` over
`X₀` and gluing the conditional kernels conditionally independently over `μ₀`. -/
noncomputable def starMeasure (μ₀ : Measure X₀) (pi : ∀ n, Measure (X₀ × Y n))
    [∀ n, IsFiniteMeasure (pi n)] : Measure (X₀ × ((n : ℕ) → Y n)) :=
  (Kernel.trajMeasure (X := starCarrier X₀ Y) μ₀ (starKernel pi)).map
    fun x ↦ (x 0, fun n ↦ x (n + 1))

instance starMeasure.instIsFiniteMeasure (μ₀ : Measure X₀) [IsFiniteMeasure μ₀]
    (pi : ∀ n, Measure (X₀ × Y n)) [∀ n, IsFiniteMeasure (pi n)] :
    IsFiniteMeasure (starMeasure μ₀ pi) := by
  rw [starMeasure]
  infer_instance

instance starMeasure.instIsProbabilityMeasure (μ₀ : Measure X₀) [IsProbabilityMeasure μ₀]
    (pi : ∀ n, Measure (X₀ × Y n)) [∀ n, IsFiniteMeasure (pi n)] :
    IsProbabilityMeasure (starMeasure μ₀ pi) := by
  rw [starMeasure]
  exact (Measure.isProbabilityMeasure_map_iff measurable_toStar.aemeasurable).2 inferInstance

private theorem map_eval_zero_trajMeasure_starKernel (μ₀ : Measure X₀)
    (pi : ∀ n, Measure (X₀ × Y n)) [∀ n, IsFiniteMeasure (pi n)] :
    (Kernel.trajMeasure (X := starCarrier X₀ Y) μ₀ (starKernel pi)).map (fun x ↦ x 0) = μ₀ := by
  let e : ((i : Iic 0) → starCarrier X₀ Y i) ≃ᵐ X₀ :=
    MeasurableEquiv.piUnique (fun i : Iic 0 ↦ starCarrier X₀ Y i)
  have heval : (fun x : (k : ℕ) → starCarrier X₀ Y k ↦ x 0) = e ∘ frestrictLe 0 := rfl
  have hprefix :
      (Kernel.trajMeasure (X := starCarrier X₀ Y) μ₀ (starKernel pi)).map (frestrictLe 0) =
        μ₀.map e.symm := by
    simp [Kernel.trajMeasure, e, MeasureTheory.Measure.map_comp _ _ (measurable_frestrictLe 0),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, MeasureTheory.Measure.id_comp]
  rw [heval, ← MeasureTheory.Measure.map_map e.measurable (measurable_frestrictLe 0), hprefix]
  simp

/-- The first marginal of `starMeasure μ₀ pi` is `μ₀`, with no compatibility assumption on `pi`. -/
@[simp]
theorem fst_starMeasure (μ₀ : Measure X₀) (pi : ∀ n, Measure (X₀ × Y n))
    [∀ n, IsFiniteMeasure (pi n)] :
    (starMeasure μ₀ pi).fst = μ₀ := by
  rw [starMeasure, Measure.fst, MeasureTheory.Measure.map_map measurable_fst measurable_toStar]
  exact map_eval_zero_trajMeasure_starKernel μ₀ pi

/-- The first projection from `starMeasure μ₀ pi` to `μ₀` is measure-preserving. -/
theorem measurePreserving_fst_starMeasure (μ₀ : Measure X₀) (pi : ∀ n, Measure (X₀ × Y n))
    [∀ n, IsFiniteMeasure (pi n)] :
    MeasurePreserving Prod.fst (starMeasure μ₀ pi) μ₀ :=
  ⟨measurable_fst, fst_starMeasure μ₀ pi⟩

/-- **Countable star gluing.** Whenever `(pi n).fst = μ₀`, projecting `starMeasure μ₀ pi` to the
base coordinate and the `n`th fiber coordinate recovers `pi n`. -/
theorem map_prodMk_starMeasure (μ₀ : Measure X₀)
    (pi : ∀ n, Measure (X₀ × Y n)) [∀ n, IsFiniteMeasure (pi n)] {n : ℕ}
    (hn : (pi n).fst = μ₀) :
    (starMeasure μ₀ pi).map (fun w ↦ (w.1, w.2 n)) = pi n := by
  have : IsFiniteMeasure μ₀ := hn ▸ inferInstance
  let Q := Kernel.trajMeasure (X := starCarrier X₀ Y) μ₀ (starKernel pi)
  let first : ((i : Iic n) → starCarrier X₀ Y i) → X₀ :=
    fun x ↦ x ⟨0, mem_Iic.mpr (Nat.zero_le n)⟩
  have hfirst : Measurable first := measurable_pi_apply _
  have hproj : Measurable (fun w : X₀ × ((k : ℕ) → Y k) ↦ (w.1, w.2 n)) :=
    measurable_fst.prodMk ((measurable_pi_apply n).comp measurable_snd)
  have hpair : (fun x : (k : ℕ) → starCarrier X₀ Y k ↦ (x 0, x (n + 1))) =
      Prod.map first id ∘ (fun x ↦ (frestrictLe n x, x (n + 1))) := rfl
  have htraj : Q.map (fun x ↦ (frestrictLe n x, x (n + 1))) =
      Q.map (frestrictLe n) ⊗ₘ starKernel pi n :=
    (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure_of_sFinite
      (μ₀ := μ₀) (κ := starKernel pi) n).symm
  have hmarginal : (Q.map (frestrictLe n)).map first = (pi n).fst := by
    rw [MeasureTheory.Measure.map_map hfirst (measurable_frestrictLe n)]
    exact (map_eval_zero_trajMeasure_starKernel μ₀ pi).trans hn.symm
  calc
    (starMeasure μ₀ pi).map (fun w ↦ (w.1, w.2 n))
        = Q.map (fun x ↦ (x 0, x (n + 1))) := by
            rw [starMeasure, MeasureTheory.Measure.map_map hproj measurable_toStar]
            rfl
    _ = (Q.map (fun x ↦ (frestrictLe n x, x (n + 1)))).map (Prod.map first id) := by
          rw [hpair, ← MeasureTheory.Measure.map_map (hfirst.prodMap measurable_id) (by fun_prop)]
    _ = (Q.map (frestrictLe n) ⊗ₘ starKernel pi n).map (Prod.map first id) := by rw [htraj]
    _ = (Q.map (frestrictLe n)).map first ⊗ₘ (pi n).condKernel :=
          Measure.map_prodMap_compProd_comap _ _ hfirst
    _ = (pi n).fst ⊗ₘ (pi n).condKernel := by rw [hmarginal]
    _ = pi n := MeasureTheory.Measure.disintegrate _ _

/-- Along `starMeasure μ₀ pi`, if each `pi n` couples `μ₀` with `ν n`, then `(w.1, w.2 n)` has
joint law `pi n`. -/
theorem map_prodMk_starMeasure_of_isCoupling {μ₀ : Measure X₀}
    {ν : ∀ n, Measure (Y n)} {pi : ∀ n, Measure (X₀ × Y n)} [∀ n, IsFiniteMeasure (pi n)]
    (hpi : ∀ n, IsCoupling (pi n) μ₀ (ν n)) (n : ℕ) :
    (starMeasure μ₀ pi).map (fun w ↦ (w.1, w.2 n)) = pi n :=
  map_prodMk_starMeasure μ₀ pi (hpi n).fst_eq

/-- Whenever each `pi n` couples `μ₀` with `ν n`, the `n`th fiber coordinate `w ↦ w.2 n` on
`starMeasure μ₀ pi` is measure-preserving to `ν n`. -/
theorem measurePreserving_eval_snd_starMeasure {μ₀ : Measure X₀}
    {ν : ∀ n, Measure (Y n)} {pi : ∀ n, Measure (X₀ × Y n)} [∀ n, IsFiniteMeasure (pi n)]
    (hpi : ∀ n, IsCoupling (pi n) μ₀ (ν n)) (n : ℕ) :
    MeasurePreserving (fun w ↦ w.2 n) (starMeasure μ₀ pi) (ν n) := by
  have hm : Measurable fun w : X₀ × ((k : ℕ) → Y k) ↦ w.2 n :=
    (measurable_pi_apply n).comp measurable_snd
  refine ⟨hm, ?_⟩
  rw [← Measure.snd_map_prodMk measurable_fst hm,
    map_prodMk_starMeasure_of_isCoupling hpi n, (hpi n).snd_eq]

end Star

end MeasureTheory.Measure

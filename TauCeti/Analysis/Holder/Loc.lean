/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.UniformFilterBasis
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Topology.Sets.Opens
public import TauCeti.Analysis.Holder.Normed
public import TauCeti.Analysis.Holder.OpenSet.Basic
import TauCeti.Analysis.Calculus.ContDiff.FTaylorSeries
import TauCeti.Analysis.LocallyConvex.WithSeminorms
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Holder.Jet.Bounds
import TauCeti.Topology.MetricSpace.Holder

/-!
# The local Hölder spaces `C^{k,α}_loc(Ω)`

For an open set `Ω` of a real normed space `E`, an integer `k ≥ 0` and an exponent `α`, this file
constructs the space `C^{k,α}_loc(Ω, F)` of maps that are `C^k` on `Ω` and whose `k`-th iterated
Fréchet derivative is `α`-Hölder on every compact subset of `Ω`. Its topology is that of uniform
convergence on compact subsets of `Ω` of all derivatives through order `k`, together with the
Hölder quotients of the `k`-th one. This is the space in which interior regularity is stated:
interior Schauder estimates bound a solution in `C^{2,α}` on compact subsets of its domain, with
no bound up to the boundary.

Nothing global is imposed. For `α ≤ 1`, `1 / x` on `(0, 1)` lies in `C^{k,α}_loc((0, 1))` for every
`k`, although it is unbounded, and `sign x` on `(-1, 0) ∪ (0, 1)` lies in every
`C^{k,α}_loc((-1, 0) ∪ (0, 1))`, although its Hölder quotients between the two components are
unbounded; both follow from `TauCeti.CkHolderLocSpace.exists_eqOn_of_contDiffOn_succ`. So
`C^{k,α}_loc(Ω)` is not the Banach space of bounded `C^{k,α}` maps on `Ω`, and its topology is
given by a family of seminorms rather than by one norm: for each compact `K ⊆ Ω`,

`p_K(f) = ∑_{i ≤ k} sup_{x ∈ K} ‖D^i f x‖ + [D^k f]_{α, K}`

(`TauCeti.CkHolderLocSpace.seminorm_eq`). When `E` is finite-dimensional, the space is a Fréchet
space: its topology is already given by the countably many seminorms of a compact exhaustion of
`Ω`, and it is complete when `F` is.

An element is a map `f : E → F` that vanishes off `Ω`, so that it is determined by its values on
`Ω`. Its derivatives at points of `Ω` are Mathlib's `iteratedFDeriv ℝ i f`, which only depend on
the values of `f` near the point.

## Main declarations

* `TauCeti.CkHolderLocSpace k α Ω F`: the maps in `C^{k,α}_loc(Ω, F)`, vanishing off `Ω`.
* `TauCeti.CkHolderLocSpace.ofContDiffOn`: the element agreeing on `Ω` with a map that is `C^k` on
  `Ω` with `k`-th derivative `α`-Hölder on compact subsets of `Ω`; and
  `TauCeti.CkHolderLocSpace.exists_eqOn_of_contDiffOn_succ`: for `α ≤ 1`, every map of class
  `C^{k+1}` on `Ω` gives one.
* `TauCeti.CkHolderLocSpace.restrictBCFL` and `TauCeti.CkHolderLocSpace.restrictHolderL`: the
  derivative field of order `i ≤ k` on a compact `K ⊆ Ω`, as a continuous linear map into the
  bounded continuous fields on `K`, and the `k`-th one into the bounded Hölder space of `K`.
* `TauCeti.CkHolderLocSpace.seminorm` and `TauCeti.CkHolderLocSpace.seminorm_eq`: the seminorm
  `p_K` of a compact `K ⊆ Ω`.
* `TauCeti.CkHolderLocSpace.withSeminorms` and `TauCeti.CkHolderLocSpace.tendsto_nhds`: the
  topology is that of the seminorms `p_K`, and convergence means convergence in every `p_K`.
* `TauCeti.CkHolderLocSpace.withSeminorms_compactExhaustion` and
  `TauCeti.CkHolderLocSpace.instFirstCountableTopology`: the seminorms of the compact sets of a
  compact exhaustion of `Ω` suffice, so for finite-dimensional `E` the space is first countable;
  `TauCeti.CkHolderLocSpace.instMetrizableSpace`: it is then metrizable.
* `TauCeti.CkHolderLocSpace.instCompleteSpace`: completeness when `E` is finite-dimensional and
  `F` is complete.
* `TauCeti.CkHolderSpaceOn.toCkHolderLocSpaceCLM`: the injective continuous linear inclusion of
  the Banach space `C^{k,α}(Ω)` of `TauCeti.CkHolderSpaceOn` into `C^{k,α}_loc(Ω)`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.1 (the spaces `C^{k,α}(Ω)` of maps whose derivatives through order `k` are Hölder on
  compact subsets of `Ω`).
-/
public section

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped NNReal BoundedContinuousFunction Uniformity

namespace TauCeti

/-- The local Hölder space `C^{k,α}_loc(Ω, F)`: maps `E → F` vanishing off the open set `Ω`, of
class `C^k` on `Ω`, whose `k`-th iterated Fréchet derivative is `α`-Hölder on every compact subset
of `Ω`. -/
structure CkHolderLocSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (α : ℝ≥0) (Ω : Opens E) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- The underlying map. Use the coercion instead. -/
  protected toFun : E → F
  protected contDiffOn' : ContDiffOn ℝ k toFun Ω
  protected holderOnWith' :
    ∀ K ⊆ (Ω : Set E), IsCompact K → ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k toFun) K
  protected eq_zero_of_notMem' : ∀ x ∉ Ω, toFun x = 0

namespace CkHolderLocSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {α : ℝ≥0} {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on a compact set of
`E`. Without it, instance search for the norm of these fields, indexed by the order `n`, exceeds
the default synthesis depth. It is local, so the instance path outside this file is unchanged. -/
local instance instNormedAddCommGroupBCF (K : Compacts E) (n : ℕ) :
    NormedAddCommGroup (K →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on a compact set of
`E`, local for the same reason. -/
local instance instNormedSpaceBCF (K : Compacts E) (n : ℕ) :
    NormedSpace ℝ (K →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

instance instFunLike : FunLike (CkHolderLocSpace k α Ω F) E F where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr

@[simp]
theorem toFun_eq_coe (f : CkHolderLocSpace k α Ω F) : f.toFun = ⇑f :=
  rfl

@[ext]
theorem ext {f g : CkHolderLocSpace k α Ω F} (h : ∀ x ∈ Ω, f x = g x) : f = g := by
  refine DFunLike.ext _ _ fun x ↦ ?_
  by_cases hx : x ∈ Ω
  · exact h x hx
  · rw [← toFun_eq_coe, ← toFun_eq_coe, f.eq_zero_of_notMem' x hx, g.eq_zero_of_notMem' x hx]

/-- An element is of class `C^k` on `Ω`. -/
theorem contDiffOn (f : CkHolderLocSpace k α Ω F) : ContDiffOn ℝ k f Ω :=
  f.contDiffOn'

/-- The `k`-th derivative of an element is `α`-Hölder on each compact subset of `Ω`. -/
theorem exists_holderOnWith (f : CkHolderLocSpace k α Ω F) {K : Set E} (hKΩ : K ⊆ Ω)
    (hK : IsCompact K) : ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k f) K :=
  f.holderOnWith' K hKΩ hK

/-- An element vanishes off `Ω`. -/
theorem apply_eq_zero_of_notMem (f : CkHolderLocSpace k α Ω F) {x : E} (hx : x ∉ Ω) : f x = 0 :=
  f.eq_zero_of_notMem' x hx

/-- An element is of class `C^k` at each point of `Ω`. -/
theorem contDiffAt (f : CkHolderLocSpace k α Ω F) {x : E} (hx : x ∈ Ω) : ContDiffAt ℝ k f x :=
  f.contDiffOn.contDiffAt (Ω.isOpen.mem_nhds hx)

/-- The derivatives of an element through order `k` are continuous on `Ω`. -/
theorem continuousOn_iteratedFDeriv (f : CkHolderLocSpace k α Ω F) {i : ℕ} (hi : i ≤ k) :
    ContinuousOn (iteratedFDeriv ℝ i f) Ω :=
  ContinuousOn.continuousOn_iteratedFDeriv f.contDiffOn Ω.isOpen (by exact_mod_cast hi)

/-! ### The vector space structure -/

private theorem holderOnWith_iteratedFDeriv_add (f g : CkHolderLocSpace k α Ω F) {K : Set E}
    (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
    ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k (⇑f + ⇑g)) K := by
  obtain ⟨C, hC⟩ := f.exists_holderOnWith hKΩ hK
  obtain ⟨D, hD⟩ := g.exists_holderOnWith hKΩ hK
  refine ⟨C + D, fun x hx y hy ↦ ?_⟩
  rw [iteratedFDeriv_add_apply (f.contDiffAt (hKΩ hx)) (g.contDiffAt (hKΩ hx)),
    iteratedFDeriv_add_apply (f.contDiffAt (hKΩ hy)) (g.contDiffAt (hKΩ hy))]
  exact HolderOnWith.add hC hD x hx y hy

private theorem holderOnWith_iteratedFDeriv_sub (f g : CkHolderLocSpace k α Ω F) {K : Set E}
    (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
    ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k (⇑f - ⇑g)) K := by
  obtain ⟨C, hC⟩ := f.exists_holderOnWith hKΩ hK
  obtain ⟨D, hD⟩ := g.exists_holderOnWith hKΩ hK
  refine ⟨C + D, fun x hx y hy ↦ ?_⟩
  rw [iteratedFDeriv_sub_apply (f.contDiffAt (hKΩ hx)) (g.contDiffAt (hKΩ hx)),
    iteratedFDeriv_sub_apply (f.contDiffAt (hKΩ hy)) (g.contDiffAt (hKΩ hy))]
  exact HolderOnWith.sub hC hD x hx y hy

private theorem holderOnWith_iteratedFDeriv_smul (c : ℝ) (f : CkHolderLocSpace k α Ω F)
    {K : Set E} (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
    ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k (c • ⇑f)) K := by
  obtain ⟨C, hC⟩ := f.exists_holderOnWith hKΩ hK
  refine ⟨C * ‖c‖₊, fun x hx y hy ↦ ?_⟩
  rw [iteratedFDeriv_const_smul_apply (f.contDiffAt (hKΩ hx)),
    iteratedFDeriv_const_smul_apply (f.contDiffAt (hKΩ hy))]
  exact hC.smul c x hx y hy

instance instZero : Zero (CkHolderLocSpace k α Ω F) where
  zero :=
    { toFun := 0
      contDiffOn' := contDiffOn_const
      holderOnWith' := fun _ _ _ ↦ ⟨0, fun x _ y _ ↦ by simp [iteratedFDeriv_zero]⟩
      eq_zero_of_notMem' := fun _ _ ↦ rfl }

instance : IsZeroApply (CkHolderLocSpace k α Ω F) where

@[no_expose] instance instAdd : Add (CkHolderLocSpace k α Ω F) where
  add f g :=
    { toFun := f + g
      contDiffOn' := f.contDiffOn.add g.contDiffOn
      holderOnWith' := fun _ hKΩ hK ↦ holderOnWith_iteratedFDeriv_add f g hKΩ hK
      eq_zero_of_notMem' := fun x hx ↦ by
        simp [f.apply_eq_zero_of_notMem hx, g.apply_eq_zero_of_notMem hx] }

instance : IsAddApply (CkHolderLocSpace k α Ω F) where

@[no_expose] instance instSMul : SMul ℝ (CkHolderLocSpace k α Ω F) where
  smul c f :=
    { toFun := c • ⇑f
      contDiffOn' := f.contDiffOn.const_smul c
      holderOnWith' := fun _ hKΩ hK ↦ holderOnWith_iteratedFDeriv_smul c f hKΩ hK
      eq_zero_of_notMem' := fun x hx ↦ by simp [f.apply_eq_zero_of_notMem hx] }

instance : IsSMulApply ℝ (CkHolderLocSpace k α Ω F) where

@[no_expose] instance instNeg : Neg (CkHolderLocSpace k α Ω F) where
  neg f :=
    { toFun := -f
      contDiffOn' := f.contDiffOn.neg
      holderOnWith' := fun _ hKΩ hK ↦ by
        simpa using holderOnWith_iteratedFDeriv_smul (-1) f hKΩ hK
      eq_zero_of_notMem' := fun x hx ↦ by simp [f.apply_eq_zero_of_notMem hx] }

instance : IsNegApply (CkHolderLocSpace k α Ω F) where

@[no_expose] instance instSub : Sub (CkHolderLocSpace k α Ω F) where
  sub f g :=
    { toFun := f - g
      contDiffOn' := f.contDiffOn.sub g.contDiffOn
      holderOnWith' := fun _ hKΩ hK ↦ holderOnWith_iteratedFDeriv_sub f g hKΩ hK
      eq_zero_of_notMem' := fun x hx ↦ by
        simp [f.apply_eq_zero_of_notMem hx, g.apply_eq_zero_of_notMem hx] }

instance : IsSubApply (CkHolderLocSpace k α Ω F) where

@[no_expose] instance instNSMul : SMul ℕ (CkHolderLocSpace k α Ω F) where
  smul c f :=
    { toFun := c • ⇑f
      contDiffOn' := f.contDiffOn.const_smul c
      holderOnWith' := fun _ hKΩ hK ↦ by
        rw [← Nat.cast_smul_eq_nsmul ℝ]
        exact holderOnWith_iteratedFDeriv_smul c f hKΩ hK
      eq_zero_of_notMem' := fun x hx ↦ by simp [f.apply_eq_zero_of_notMem hx] }

instance : IsSMulApply ℕ (CkHolderLocSpace k α Ω F) where

@[no_expose] instance instZSMul : SMul ℤ (CkHolderLocSpace k α Ω F) where
  smul c f :=
    { toFun := c • ⇑f
      contDiffOn' := f.contDiffOn.const_smul c
      holderOnWith' := fun _ hKΩ hK ↦ by
        rw [← Int.cast_smul_eq_zsmul ℝ]
        exact holderOnWith_iteratedFDeriv_smul c f hKΩ hK
      eq_zero_of_notMem' := fun x hx ↦ by simp [f.apply_eq_zero_of_notMem hx] }

instance : IsSMulApply ℤ (CkHolderLocSpace k α Ω F) where

instance instAddCommGroup : AddCommGroup (CkHolderLocSpace k α Ω F) :=
  fast_instance% FunLike.addCommGroup

instance instModule : Module ℝ (CkHolderLocSpace k α Ω F) := fast_instance% FunLike.module

/-- The derivatives of an element through order `k` are additive at points of `Ω`. -/
theorem iteratedFDeriv_add_apply (f g : CkHolderLocSpace k α Ω F) {i : ℕ} (hi : i ≤ k) {x : E}
    (hx : x ∈ Ω) :
    iteratedFDeriv ℝ i ⇑(f + g) x = iteratedFDeriv ℝ i f x + iteratedFDeriv ℝ i g x := by
  rw [FunLike.coe_add]
  exact _root_.iteratedFDeriv_add_apply ((f.contDiffAt hx).of_le (by exact_mod_cast hi))
    ((g.contDiffAt hx).of_le (by exact_mod_cast hi))

/-- The derivatives of an element through order `k` are homogeneous at points of `Ω`. -/
theorem iteratedFDeriv_smul_apply (c : ℝ) (f : CkHolderLocSpace k α Ω F) {i : ℕ} (hi : i ≤ k)
    {x : E} (hx : x ∈ Ω) :
    iteratedFDeriv ℝ i ⇑(c • f) x = c • iteratedFDeriv ℝ i f x := by
  rw [FunLike.coe_smul]
  exact iteratedFDeriv_const_smul_apply ((f.contDiffAt hx).of_le (by exact_mod_cast hi))

/-! ### Elements from maps on `Ω` -/

section OfContDiffOn

variable {g : E → F}

/-- The element of `C^{k,α}_loc(Ω)` agreeing on `Ω` with a map `g` that is `C^k` on `Ω` and whose
`k`-th derivative is `α`-Hölder on each compact subset of `Ω`. -/
def ofContDiffOn (g : E → F) (hg : ContDiffOn ℝ k g Ω)
    (hH : ∀ K ⊆ (Ω : Set E), IsCompact K → ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k g) K) :
    CkHolderLocSpace k α Ω F where
  toFun := (Ω : Set E).indicator g
  contDiffOn' := hg.congr fun _ hx ↦ indicator_of_mem hx g
  holderOnWith' K hKΩ hK := by
    obtain ⟨C, hC⟩ := hH K hKΩ hK
    refine ⟨C, fun x hx y hy ↦ ?_⟩
    rw [iteratedFDeriv_indicator_of_mem_nhds (Ω.isOpen.mem_nhds (hKΩ hx)) k,
      iteratedFDeriv_indicator_of_mem_nhds (Ω.isOpen.mem_nhds (hKΩ hy)) k]
    exact hC x hx y hy
  eq_zero_of_notMem' _ hx := indicator_of_notMem hx g

variable {hg : ContDiffOn ℝ k g Ω}
  {hH : ∀ K ⊆ (Ω : Set E), IsCompact K → ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k g) K}

/-- `ofContDiffOn g` is the indicator of `Ω` applied to `g`. -/
theorem coe_ofContDiffOn : ⇑(ofContDiffOn g hg hH) = (Ω : Set E).indicator g :=
  (rfl)

/-- `ofContDiffOn g` agrees with `g` on `Ω`. -/
@[simp]
theorem ofContDiffOn_apply_of_mem {x : E} (hx : x ∈ Ω) : ofContDiffOn g hg hH x = g x := by
  rw [coe_ofContDiffOn]
  exact indicator_of_mem hx g

/-- `ofContDiffOn g` vanishes off `Ω`. -/
@[simp]
theorem ofContDiffOn_apply_of_notMem {x : E} (hx : x ∉ Ω) : ofContDiffOn g hg hH x = 0 := by
  rw [coe_ofContDiffOn]
  exact indicator_of_notMem hx g

/-- `ofContDiffOn g` has the derivatives of `g` at points of `Ω`. -/
@[simp]
theorem iteratedFDeriv_ofContDiffOn (i : ℕ) {x : E} (hx : x ∈ Ω) :
    iteratedFDeriv ℝ i (ofContDiffOn g hg hH) x = iteratedFDeriv ℝ i g x := by
  rw [coe_ofContDiffOn]
  exact iteratedFDeriv_indicator_of_mem_nhds (Ω.isOpen.mem_nhds hx) i

/-- Every element is `ofContDiffOn` of its own underlying map. -/
@[simp]
theorem ofContDiffOn_coe (f : CkHolderLocSpace k α Ω F) :
    ofContDiffOn f f.contDiffOn (fun _ hKΩ hK ↦ f.exists_holderOnWith hKΩ hK) = f :=
  ext fun _ hx ↦ ofContDiffOn_apply_of_mem hx

/-- For `α ≤ 1`, every map of class `C^{k+1}` on `Ω` agrees on `Ω` with an element of
`C^{k,α}_loc(Ω)`. -/
theorem exists_eqOn_of_contDiffOn_succ (hα : α ≤ 1) (hg : ContDiffOn ℝ (k + 1) g Ω) :
    ∃ f : CkHolderLocSpace k α Ω F, EqOn f g Ω :=
  ⟨ofContDiffOn g (hg.of_le (by exact_mod_cast k.le_succ))
      fun _ hKΩ hK ↦ hg.exists_holderOnWith_iteratedFDeriv Ω.isOpen hα hK hKΩ,
    fun _ hx ↦ ofContDiffOn_apply_of_mem hx⟩

end OfContDiffOn

/-! ### Derivative fields on compact subsets -/

section Restrict

variable (K : Compacts E) (hK : (K : Set E) ⊆ Ω)

/-- The `i`-th derivative field of an element, for `i ≤ k`, on a compact set `K ⊆ Ω`, as a bounded
continuous field on `K`. -/
def restrictBCF {i : ℕ} (hi : i ≤ k) (f : CkHolderLocSpace k α Ω F) : K →ᵇ (E [×i]→L[ℝ] F) :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ iteratedFDeriv ℝ i f x,
      (f.continuousOn_iteratedFDeriv hi).comp_continuous continuous_subtypeVal
        fun x ↦ hK x.property⟩

@[simp]
theorem restrictBCF_apply {i : ℕ} (hi : i ≤ k) (f : CkHolderLocSpace k α Ω F) (x : K) :
    restrictBCF K hK hi f x = iteratedFDeriv ℝ i f x :=
  (rfl)

/-- `restrictBCF` is the restriction of the `i`-th derivative to `K`. -/
theorem coe_restrictBCF {i : ℕ} (hi : i ≤ k) (f : CkHolderLocSpace k α Ω F) :
    ⇑(restrictBCF K hK hi f) = (K : Set E).domRestrict (iteratedFDeriv ℝ i f) :=
  funext (restrictBCF_apply K hK hi f)

/-- The `k`-th derivative field of an element on a compact set `K ⊆ Ω` is `α`-Hölder. -/
theorem memHolder_restrictBCF (f : CkHolderLocSpace k α Ω F) :
    MemHolder α (restrictBCF K hK le_rfl f : K → E [×k]→L[ℝ] F) := by
  obtain ⟨C, hC⟩ := f.exists_holderOnWith hK K.isCompact
  rw [coe_restrictBCF]
  exact ⟨C, hC.holderWith⟩

/-- The `k`-th derivative field of an element on a compact set `K ⊆ Ω`, as an element of the
bounded Hölder space of `K`. -/
def restrictHolder (f : CkHolderLocSpace k α Ω F) : HolderSpace α K (E [×k]→L[ℝ] F) :=
  HolderSpace.ofBoundedContinuousFunction (restrictBCF K hK le_rfl f)
    (memHolder_restrictBCF K hK f)

@[simp]
theorem restrictHolder_apply (f : CkHolderLocSpace k α Ω F) (x : K) :
    restrictHolder K hK f x = iteratedFDeriv ℝ k f x :=
  HolderSpace.ofBoundedContinuousFunction_apply _ _ _

/-- The bounded continuous field underlying `restrictHolder` is `restrictBCF` at order `k`. -/
theorem toBoundedContinuousFunction_restrictHolder (f : CkHolderLocSpace k α Ω F) :
    (restrictHolder K hK f).toBoundedContinuousFunction = restrictBCF K hK le_rfl f :=
  HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction _ _

/-- `restrictBCF` as a linear map. -/
private def restrictBCFₗ {i : ℕ} (hi : i ≤ k) :
    CkHolderLocSpace k α Ω F →ₗ[ℝ] (K →ᵇ (E [×i]→L[ℝ] F)) where
  toFun := restrictBCF K hK hi
  map_add' f g := by
    ext x : 1
    simpa only [restrictBCF_apply, FunLike.coe_add, Pi.add_apply] using
      iteratedFDeriv_add_apply f g hi (hK x.property)
  map_smul' c f := by
    ext x : 1
    simpa only [restrictBCF_apply, FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply] using
      iteratedFDeriv_smul_apply c f hi (hK x.property)

/-- `restrictHolder` as a linear map. -/
private def restrictHolderₗ :
    CkHolderLocSpace k α Ω F →ₗ[ℝ] HolderSpace α K (E [×k]→L[ℝ] F) where
  toFun := restrictHolder K hK
  map_add' f g := HolderSpace.ext fun x ↦ by
    simp only [restrictHolder_apply, HolderSpace.add_apply]
    exact iteratedFDeriv_add_apply f g le_rfl (hK x.property)
  map_smul' c f := HolderSpace.ext fun x ↦ by
    simp only [restrictHolder_apply, HolderSpace.smul_apply, RingHom.id_apply]
    exact iteratedFDeriv_smul_apply c f le_rfl (hK x.property)

/-- The seminorm `p_K(f) = ∑_{i ≤ k} sup_{x ∈ K} ‖D^i f x‖ + [D^k f]_{α, K}` of a compact set
`K ⊆ Ω` (`TauCeti.CkHolderLocSpace.seminorm_eq`). -/
protected def seminorm : Seminorm ℝ (CkHolderLocSpace k α Ω F) :=
  ∑ i : Fin k, (normSeminorm ℝ (K →ᵇ (E [×i]→L[ℝ] F))).comp (restrictBCFₗ K hK i.is_lt.le) +
    (normSeminorm ℝ (HolderSpace α K (E [×k]→L[ℝ] F))).comp (restrictHolderₗ K hK)

/-- The seminorm `p_K` as the sum of the norms of the derivative fields on `K`, the top one in the
bounded Hölder space of `K`. -/
theorem seminorm_apply (f : CkHolderLocSpace k α Ω F) :
    CkHolderLocSpace.seminorm K hK f =
      ∑ i : Fin k, ‖restrictBCF K hK i.is_lt.le f‖ + ‖restrictHolder K hK f‖ := by
  simp [CkHolderLocSpace.seminorm, restrictBCFₗ, restrictHolderₗ]

/-- `restrictHolder` is the restriction of the `k`-th derivative to `K`. -/
theorem coe_restrictHolder (f : CkHolderLocSpace k α Ω F) :
    ⇑(restrictHolder K hK f) = (K : Set E).domRestrict (iteratedFDeriv ℝ k f) :=
  funext (restrictHolder_apply K hK f)

/-- The seminorm of a compact set `K ⊆ Ω` is the sum of the supremum norms on `K` of the
derivatives through order `k` and the `α`-Hölder seminorm on `K` of the `k`-th one. -/
theorem seminorm_eq (f : CkHolderLocSpace k α Ω F) :
    CkHolderLocSpace.seminorm K hK f =
      ∑ i : Fin k, ‖restrictBCF K hK i.is_lt.le f‖ + ‖restrictBCF K hK le_rfl f‖ +
        nnHolderNorm α ((K : Set E).domRestrict (iteratedFDeriv ℝ k f)) := by
  rw [seminorm_apply, HolderSpace.norm_def, toBoundedContinuousFunction_restrictHolder,
    coe_restrictBCF, add_assoc]

/-- On a compact set `K ⊆ Ω`, the seminorm `p_K f` bounds the supremum norms of the derivative
fields of `f` through order `k`. -/
theorem norm_restrictBCF_le_seminorm (f : CkHolderLocSpace k α Ω F) {i : ℕ} (hi : i ≤ k) :
    ‖restrictBCF K hK hi f‖ ≤ CkHolderLocSpace.seminorm K hK f := by
  have hsum : ‖restrictBCF K hK hi f‖ ≤
      ∑ j : Fin k, ‖restrictBCF K hK j.is_lt.le f‖ + ‖restrictBCF K hK le_rfl f‖ := by
    rcases hi.lt_or_eq with hik | rfl
    · have h1 := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin k ↦ ‖restrictBCF K hK j.is_lt.le f‖) (fun _ _ ↦ norm_nonneg _)
        (Finset.mem_univ (⟨i, hik⟩ : Fin k))
      have h2 : 0 ≤ ‖restrictBCF K hK le_rfl f‖ := norm_nonneg _
      exact le_add_of_le_of_nonneg h1 h2
    · have h1 : 0 ≤ ∑ j : Fin i, ‖restrictBCF K hK j.is_lt.le f‖ :=
        Finset.sum_nonneg fun j _ ↦ norm_nonneg (restrictBCF K hK j.is_lt.le f)
      exact le_add_of_nonneg_left h1
  rw [seminorm_eq]
  exact le_add_of_le_of_nonneg hsum (NNReal.coe_nonneg _)

/-- On a compact set `K ⊆ Ω`, the seminorm `p_K f` bounds the derivatives of `f` through order
`k`. -/
theorem norm_iteratedFDeriv_le_seminorm (f : CkHolderLocSpace k α Ω F) {i : ℕ} (hi : i ≤ k)
    {x : E} (hx : x ∈ K) : ‖iteratedFDeriv ℝ i f x‖ ≤ CkHolderLocSpace.seminorm K hK f :=
  ((restrictBCF K hK hi f).norm_coe_le_norm ⟨x, hx⟩).trans (norm_restrictBCF_le_seminorm K hK f hi)

/-- The seminorm `p_K f` bounds the norm of the `k`-th derivative field in the bounded Hölder
space of `K`. -/
theorem norm_restrictHolder_le_seminorm (f : CkHolderLocSpace k α Ω F) :
    ‖restrictHolder K hK f‖ ≤ CkHolderLocSpace.seminorm K hK f := by
  rw [seminorm_apply]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)

/-- On a compact set `K ⊆ Ω`, the seminorm `p_K f` is a Hölder constant of the `k`-th derivative. -/
theorem holderOnWith_seminorm (f : CkHolderLocSpace k α Ω F) :
    HolderOnWith (CkHolderLocSpace.seminorm K hK f).toNNReal α (iteratedFDeriv ℝ k f) K := by
  rw [← HolderWith.restrict_iff, ← coe_restrictHolder]
  refine (restrictHolder K hK f).holderWith_nnnorm.mono ?_
  rw [← NNReal.coe_le_coe, coe_nnNorm, Real.coe_toNNReal _ (apply_nonneg _ _)]
  exact norm_restrictHolder_le_seminorm K hK f

/-- The seminorms increase with the compact set. -/
theorem seminorm_mono {L : Compacts E} (hL : (L : Set E) ⊆ Ω) (hKL : K ≤ L)
    (f : CkHolderLocSpace k α Ω F) :
    CkHolderLocSpace.seminorm K hK f ≤ CkHolderLocSpace.seminorm L hL f := by
  have hsup {i : ℕ} (hi : i ≤ k) : ‖restrictBCF K hK hi f‖ ≤ ‖restrictBCF L hL hi f‖ :=
    (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x ↦
      (restrictBCF L hL hi f).norm_coe_le_norm ⟨x, hKL x.property⟩
  rw [seminorm_eq, seminorm_eq]
  gcongr with i
  · exact hsup _
  · exact hsup _
  · have hL' := (memHolder_restrictBCF L hL f).holderWith
    rw [coe_restrictBCF, HolderWith.restrict_iff] at hL'
    exact HolderWith.nnholderNorm_le (HolderWith.restrict_iff.2 (hL'.mono hKL))

end Restrict

/-! ### The topology -/

section Topology

variable (k α Ω F) in
/-- The family of the seminorms `p_K` of the compact sets `K ⊆ Ω`. -/
def seminormFamily :
    SeminormFamily ℝ (CkHolderLocSpace k α Ω F) {K : Compacts E // (K : Set E) ⊆ Ω} :=
  fun K ↦ CkHolderLocSpace.seminorm K.val K.property

@[simp]
theorem seminormFamily_apply (K : {K : Compacts E // (K : Set E) ⊆ Ω}) :
    seminormFamily k α Ω F K = CkHolderLocSpace.seminorm K.val K.property :=
  (rfl)

/-- The topology of `C^{k,α}_loc(Ω)`: the locally convex topology of the seminorms `p_K` of the
compact sets `K ⊆ Ω`. -/
instance instTopologicalSpace : TopologicalSpace (CkHolderLocSpace k α Ω F) :=
  (seminormFamily k α Ω F).moduleFilterBasis.topology'

/-- The topology of `C^{k,α}_loc(Ω)` is induced by the seminorms `p_K`. -/
theorem withSeminorms : WithSeminorms (seminormFamily k α Ω F) :=
  ⟨rfl⟩

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (CkHolderLocSpace k α Ω F) :=
  (seminormFamily k α Ω F).addGroupFilterBasis.isTopologicalAddGroup

instance instContinuousSMul : ContinuousSMul ℝ (CkHolderLocSpace k α Ω F) :=
  (withSeminorms (k := k) (α := α) (Ω := Ω) (F := F)).continuousSMul

instance instUniformSpace : UniformSpace (CkHolderLocSpace k α Ω F) :=
  fast_instance% (seminormFamily k α Ω F).addGroupFilterBasis.uniformSpace

instance instIsUniformAddGroup : IsUniformAddGroup (CkHolderLocSpace k α Ω F) :=
  (seminormFamily k α Ω F).addGroupFilterBasis.isUniformAddGroup

instance instLocallyConvexSpace : LocallyConvexSpace ℝ (CkHolderLocSpace k α Ω F) :=
  (withSeminorms (k := k) (α := α) (Ω := Ω) (F := F)).toLocallyConvexSpace

/-- `C^{k,α}_loc(Ω)` is T1, hence Hausdorff as a topological group: the seminorms of the points
of `Ω` already separate elements. -/
instance instT1Space : T1Space (CkHolderLocSpace k α Ω F) := by
  refine (withSeminorms (k := k) (α := α) (Ω := Ω) (F := F)).T1_of_separating fun f hf ↦ ?_
  obtain ⟨x, hx, hfx⟩ : ∃ x ∈ Ω, f x ≠ 0 := by
    by_contra! h
    exact hf (ext fun x hx ↦ by simpa using h x hx)
  refine ⟨⟨⟨{x}, isCompact_singleton⟩, singleton_subset_iff.2 hx⟩, fun h0 ↦ hfx ?_⟩
  have h := norm_iteratedFDeriv_le_seminorm (Ω := Ω) ⟨{x}, isCompact_singleton⟩
    (singleton_subset_iff.2 hx) f (Nat.zero_le k) (mem_singleton x)
  rw [norm_iteratedFDeriv_zero] at h
  rw [seminormFamily_apply] at h0
  exact norm_le_zero_iff.1 (h.trans_eq h0)

/-- Convergence in `C^{k,α}_loc(Ω)` is convergence in the seminorm `p_K` of every compact set
`K ⊆ Ω`. -/
theorem tendsto_nhds {ι : Type*} {l : Filter ι} {u : ι → CkHolderLocSpace k α Ω F}
    {f : CkHolderLocSpace k α Ω F} :
    Tendsto u l (𝓝 f) ↔ ∀ (K : Compacts E) (hK : (K : Set E) ⊆ Ω),
      Tendsto (fun i ↦ CkHolderLocSpace.seminorm K hK (u i - f)) l (𝓝 0) := by
  rw [(withSeminorms (k := k) (α := α) (Ω := Ω) (F := F)).tendsto_nhds_iff_tendsto_zero]
  exact ⟨fun h K hK ↦ h ⟨K, hK⟩, fun h K ↦ h K.val K.property⟩

section Restrict

variable (K : Compacts E) (hK : (K : Set E) ⊆ Ω)

/-- The `i`-th derivative field, `i ≤ k`, on a compact set `K ⊆ Ω`, as a continuous linear map
into the bounded continuous fields on `K`. -/
def restrictBCFL {i : ℕ} (hi : i ≤ k) :
    CkHolderLocSpace k α Ω F →L[ℝ] (K →ᵇ (E [×i]→L[ℝ] F)) where
  toLinearMap := restrictBCFₗ K hK hi
  cont := WithSeminorms.continuous_normedSpace_rng (K →ᵇ (E [×i]→L[ℝ] F)) withSeminorms _
    ⟨{⟨K, hK⟩}, 1, fun f ↦ by
      rw [Seminorm.comp_apply, coe_normSeminorm, Finset.sup_singleton, one_smul,
        seminormFamily_apply]
      exact norm_restrictBCF_le_seminorm K hK f hi⟩

@[simp]
theorem restrictBCFL_apply {i : ℕ} (hi : i ≤ k) (f : CkHolderLocSpace k α Ω F) :
    restrictBCFL K hK hi f = restrictBCF K hK hi f :=
  (rfl)

/-- The `k`-th derivative field on a compact set `K ⊆ Ω`, as a continuous linear map into the
bounded Hölder space of `K`. -/
def restrictHolderL : CkHolderLocSpace k α Ω F →L[ℝ] HolderSpace α K (E [×k]→L[ℝ] F) where
  toLinearMap := restrictHolderₗ K hK
  cont := WithSeminorms.continuous_normedSpace_rng (HolderSpace α K (E [×k]→L[ℝ] F))
    withSeminorms _
    ⟨{⟨K, hK⟩}, 1, fun f ↦ by
      rw [Seminorm.comp_apply, coe_normSeminorm, Finset.sup_singleton, one_smul,
        seminormFamily_apply]
      exact norm_restrictHolder_le_seminorm K hK f⟩

@[simp]
theorem restrictHolderL_apply (f : CkHolderLocSpace k α Ω F) :
    restrictHolderL K hK f = restrictHolder K hK f :=
  (rfl)

/-- `restrictBCF` sends differences to differences. -/
@[simp]
theorem restrictBCF_sub {i : ℕ} (hi : i ≤ k) (f g : CkHolderLocSpace k α Ω F) :
    restrictBCF K hK hi (f - g) = restrictBCF K hK hi f - restrictBCF K hK hi g :=
  map_sub (restrictBCFL K hK hi) f g

/-- `restrictHolder` sends differences to differences. -/
@[simp]
theorem restrictHolder_sub (f g : CkHolderLocSpace k α Ω F) :
    restrictHolder K hK (f - g) = restrictHolder K hK f - restrictHolder K hK g :=
  map_sub (restrictHolderL K hK) f g

end Restrict

/-- The seminorms of the compact sets of a compact exhaustion of `Ω` already induce the topology of
`C^{k,α}_loc(Ω)`. -/
theorem withSeminorms_compactExhaustion (K : CompactExhaustion Ω) :
    WithSeminorms fun n : ℕ ↦ (CkHolderLocSpace.seminorm (k := k) (α := α) (F := F)
      ⟨Subtype.val '' K n, (K.isCompact n).image continuous_subtypeVal⟩
      (Subtype.coe_image_subset _ _)) := by
  refine (withSeminorms (k := k) (α := α) (Ω := Ω) (F := F)).congr
    (fun n ↦ ⟨{⟨⟨Subtype.val '' K n, (K.isCompact n).image continuous_subtypeVal⟩,
      Subtype.coe_image_subset _ _⟩}, 1, fun f ↦ by simp⟩) fun L ↦ ?_
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact
    (Topology.IsInducing.subtypeVal.isCompact_preimage' L.val.isCompact (by simpa using L.property))
  refine ⟨{n}, 1, fun f ↦ ?_⟩
  simp only [Finset.sup_singleton, one_smul, Seminorm.comp_id, seminormFamily_apply]
  refine seminorm_mono L.val L.property _ (fun x hx ↦ ?_) f
  exact ⟨⟨x, L.property hx⟩, hn hx, rfl⟩

/-- For finite-dimensional `E`, `C^{k,α}_loc(Ω)` is first countable, hence metrizable. -/
instance instFirstCountableTopology [FiniteDimensional ℝ E] :
    FirstCountableTopology (CkHolderLocSpace k α Ω F) :=
  have := Ω.isOpen.locallyCompactSpace
  (withSeminorms_compactExhaustion (CompactExhaustion.choice Ω)).firstCountableTopology

/-- For finite-dimensional `E`, `C^{k,α}_loc(Ω)` is metrizable; with completeness for complete `F`
(`TauCeti.CkHolderLocSpace.instCompleteSpace`), it is a Fréchet space. -/
instance instMetrizableSpace [FiniteDimensional ℝ E] :
    MetrizableSpace (CkHolderLocSpace k α Ω F) :=
  have : (𝓤 (CkHolderLocSpace k α Ω F)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  UniformSpace.metrizableSpace

end Topology

/-! ### Completeness

The derivative fields of a Cauchy sequence converge uniformly on compact subsets of `Ω`, in
`K →ᵇ (E [×i]→L[ℝ] F)` and, for the top order, in the bounded Hölder space of `K`. Locally
uniform limits of Taylor series are Taylor series
(`HasFTaylorSeriesUpToOn.of_tendstoLocallyUniformlyOn`), so the limit fields are the derivatives
of the limit function on `Ω`; it lies in `C^{k,α}_loc(Ω)` and is the limit in every seminorm. -/

section Complete

variable [CompleteSpace F] {u : ℕ → CkHolderLocSpace k α Ω F}

/-- The pointwise limit of the `i`-th derivatives of a sequence. -/
private def limitField (u : ℕ → CkHolderLocSpace k α Ω F) (i : ℕ) (x : E) : E [×i]→L[ℝ] F :=
  limUnder atTop fun n ↦ iteratedFDeriv ℝ i (u n) x

private theorem exists_tendsto_restrictBCF (hu : CauchySeq u) (K : Compacts E)
    (hK : (K : Set E) ⊆ Ω) {i : ℕ} (hi : i ≤ k) :
    ∃ φ, Tendsto (fun n ↦ restrictBCF K hK hi (u n)) atTop (𝓝 φ) :=
  cauchySeq_tendsto_of_complete ((restrictBCFL K hK hi).uniformContinuous.comp_cauchySeq hu)

private theorem tendsto_limitField (hu : CauchySeq u) {i : ℕ} (hi : i ≤ k) {x : E} (hx : x ∈ Ω) :
    Tendsto (fun n ↦ iteratedFDeriv ℝ i (u n) x) atTop (𝓝 (limitField u i x)) := by
  obtain ⟨φ, hφ⟩ := exists_tendsto_restrictBCF hu ⟨{x}, isCompact_singleton⟩
    (singleton_subset_iff.2 hx) hi
  exact tendsto_nhds_limUnder ⟨φ ⟨x, mem_singleton x⟩,
    ((continuous_eval_const (⟨x, mem_singleton x⟩ : ({x} : Set E))).tendsto _).comp hφ⟩

private theorem exists_tendsto_restrictBCF_eq (hu : CauchySeq u) (K : Compacts E)
    (hK : (K : Set E) ⊆ Ω) {i : ℕ} (hi : i ≤ k) :
    ∃ φ, Tendsto (fun n ↦ restrictBCF K hK hi (u n)) atTop (𝓝 φ) ∧
      ∀ x : K, φ x = limitField u i x := by
  obtain ⟨φ, hφ⟩ := exists_tendsto_restrictBCF hu K hK hi
  exact ⟨φ, hφ, fun x ↦ tendsto_nhds_unique (((continuous_eval_const x).tendsto _).comp hφ)
    (tendsto_limitField hu hi (hK x.property))⟩

/-- The limit function of a Cauchy sequence: its pointwise limit on `Ω`, and `0` off `Ω`. -/
private def limitFun (u : ℕ → CkHolderLocSpace k α Ω F) : E → F :=
  (Ω : Set E).indicator fun x ↦ (limitField u 0 x).curry0

private theorem tendsto_limitFun (hu : CauchySeq u) {x : E} (hx : x ∈ Ω) :
    Tendsto (fun n ↦ u n x) atTop (𝓝 (limitFun u x)) := by
  rw [limitFun, indicator_of_mem hx]
  simpa [Function.comp_def] using ((continuousMultilinearCurryFin0 ℝ E F).continuous.tendsto _).comp
    (tendsto_limitField hu (Nat.zero_le k) hx)

variable [FiniteDimensional ℝ E]

private theorem tendstoLocallyUniformlyOn_limitField (hu : CauchySeq u) {i : ℕ} (hi : i ≤ k) :
    TendstoLocallyUniformlyOn (fun n ↦ iteratedFDeriv ℝ i (u n)) (limitField u i) atTop Ω := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Ω.isOpen]
  intro K hKΩ hK
  obtain ⟨φ, hφ, hφG⟩ := exists_tendsto_restrictBCF_eq hu ⟨K, hK⟩ hKΩ hi
  have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 hφ
  rw [show ⇑φ = limitField u i ∘ (↑) from funext hφG] at h
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.2 h

/-- The limit fields form a Taylor series of the limit function on `Ω`, as locally uniform limits
of the Taylor series of the elements of the sequence. -/
private theorem hasFTaylorSeriesUpToOn_limitFun (hu : CauchySeq u) :
    HasFTaylorSeriesUpToOn (k : ℕ∞) (limitFun u) (fun x m ↦ limitField u m x) Ω :=
  HasFTaylorSeriesUpToOn.of_tendstoLocallyUniformlyOn Ω.isOpen
    (fun n ↦ (u n).contDiffOn.ftaylorSeriesWithin Ω.isOpen.uniqueDiffOn)
    (fun m hm ↦ (tendstoLocallyUniformlyOn_limitField hu (by exact_mod_cast hm)).congr
      fun _ _ hy ↦ (iteratedFDerivWithin_of_isOpen m Ω.isOpen hy).symm)
    (fun _ hx ↦ tendsto_limitFun hu hx)

private theorem iteratedFDeriv_limitFun (hu : CauchySeq u) {i : ℕ} (hi : i ≤ k) {x : E}
    (hx : x ∈ Ω) : iteratedFDeriv ℝ i (limitFun u) x = limitField u i x := by
  rw [← iteratedFDerivWithin_of_isOpen i Ω.isOpen hx,
    ← (hasFTaylorSeriesUpToOn_limitFun hu).eq_iteratedFDerivWithin_of_uniqueDiffOn
      (by exact_mod_cast hi) Ω.isOpen.uniqueDiffOn hx]

private theorem exists_tendsto_restrictHolder_eq (hu : CauchySeq u) (K : Compacts E)
    (hK : (K : Set E) ⊆ Ω) :
    ∃ ψ, Tendsto (fun n ↦ restrictHolder K hK (u n)) atTop (𝓝 ψ) ∧
      ∀ x : K, ψ x = iteratedFDeriv ℝ k (limitFun u) x := by
  obtain ⟨ψ, hψ⟩ := cauchySeq_tendsto_of_complete
    ((restrictHolderL K hK).uniformContinuous.comp_cauchySeq hu)
  refine ⟨ψ, hψ, fun x ↦ ?_⟩
  rw [iteratedFDeriv_limitFun hu le_rfl (hK x.property)]
  refine tendsto_nhds_unique ?_ (tendsto_limitField hu le_rfl (hK x.property))
  simpa [Function.comp_def] using
    ((HolderSpace.evalCLM (α := α) (Y := E [×k]→L[ℝ] F) x).continuous.tendsto _).comp hψ

private theorem holderOnWith_limitFun (hu : CauchySeq u) {K : Set E} (hKΩ : K ⊆ Ω)
    (hK : IsCompact K) : ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k (limitFun u)) K := by
  obtain ⟨ψ, -, hψ⟩ := exists_tendsto_restrictHolder_eq hu ⟨K, hK⟩ hKΩ
  refine ⟨nnHolderNorm α (ψ : K → E [×k]→L[ℝ] F), fun x hx y hy ↦ ?_⟩
  have h := ψ.holderWith ⟨x, hx⟩ ⟨y, hy⟩
  rwa [hψ, hψ] at h

/-- The limit of a Cauchy sequence in `C^{k,α}_loc(Ω)`. -/
private def limit (hu : CauchySeq u) : CkHolderLocSpace k α Ω F where
  toFun := limitFun u
  contDiffOn' := (hasFTaylorSeriesUpToOn_limitFun hu).contDiffOn
  holderOnWith' _ hKΩ hK := holderOnWith_limitFun hu hKΩ hK
  eq_zero_of_notMem' _ hx := indicator_of_notMem hx _

private theorem coe_limit (hu : CauchySeq u) : ⇑(limit hu) = limitFun u :=
  rfl

private theorem tendsto_limit (hu : CauchySeq u) : Tendsto u atTop (𝓝 (limit hu)) := by
  rw [tendsto_nhds]
  intro K hK
  have hBCF {i : ℕ} (hi : i ≤ k) :
      Tendsto (fun n ↦ ‖restrictBCF K hK hi (u n - limit hu)‖) atTop (𝓝 0) := by
    obtain ⟨φ, hφ, hφG⟩ := exists_tendsto_restrictBCF_eq hu K hK hi
    have hlim : restrictBCF K hK hi (limit hu) = φ := by
      ext1 x
      rw [restrictBCF_apply, hφG, coe_limit, iteratedFDeriv_limitFun hu hi (hK x.property)]
    rw [← hlim] at hφ
    simpa using tendsto_iff_norm_sub_tendsto_zero.1 hφ
  have hHolder : Tendsto (fun n ↦ ‖restrictHolder K hK (u n - limit hu)‖) atTop (𝓝 0) := by
    obtain ⟨ψ, hψ, hψG⟩ := exists_tendsto_restrictHolder_eq hu K hK
    have hlim : restrictHolder K hK (limit hu) = ψ :=
      HolderSpace.ext fun x ↦ by rw [restrictHolder_apply, hψG, coe_limit]
    rw [← hlim] at hψ
    simpa using tendsto_iff_norm_sub_tendsto_zero.1 hψ
  simp_rw [seminorm_apply]
  simpa using (tendsto_finsetSum Finset.univ fun (j : Fin k) _ ↦ hBCF j.is_lt.le).add hHolder

/-- For finite-dimensional `E` and complete `F`, `C^{k,α}_loc(Ω, F)` is complete: a Fréchet
space. -/
instance instCompleteSpace : CompleteSpace (CkHolderLocSpace k α Ω F) := by
  have : (𝓤 (CkHolderLocSpace k α Ω F)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.complete_of_cauchySeq_tendsto fun u hu ↦ ⟨limit hu, tendsto_limit hu⟩

end Complete

end CkHolderLocSpace

/-! ### The inclusion of `C^{k,α}(Ω)` -/

namespace CkHolderSpaceOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {α : ℝ≥0} {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An element of `C^{k,α}(Ω)` as an element of `C^{k,α}_loc(Ω)`: its extension by zero. -/
private def toCkHolderLocSpace (f : CkHolderSpaceOn k α Ω F) : CkHolderLocSpace k α Ω F :=
  CkHolderLocSpace.ofContDiffOn f.extend f.contDiffOn_extend
    fun _ hKΩ _ ↦ ⟨_, f.holderOnWith_iteratedFDeriv_extend.mono hKΩ⟩

private theorem toCkHolderLocSpace_apply_of_mem (f : CkHolderSpaceOn k α Ω F) {x : E}
    (hx : x ∈ Ω) : toCkHolderLocSpace f x = f ⟨x, hx⟩ :=
  (CkHolderLocSpace.ofContDiffOn_apply_of_mem hx).trans (f.extend_apply ⟨x, hx⟩)

private theorem iteratedFDeriv_toCkHolderLocSpace (f : CkHolderSpaceOn k α Ω F) (i : ℕ) {x : E}
    (hx : x ∈ Ω) :
    _root_.iteratedFDeriv ℝ i (toCkHolderLocSpace f) x = _root_.iteratedFDeriv ℝ i f.extend x :=
  CkHolderLocSpace.iteratedFDeriv_ofContDiffOn i hx

/-- The seminorm `p_K` of a compact set `K ⊆ Ω` of the inclusion of `f ∈ C^{k,α}(Ω)` is at most
`(k + 2) ‖f‖`. -/
private theorem seminorm_toCkHolderLocSpace_le (K : Compacts E) (hK : (K : Set E) ⊆ Ω)
    (f : CkHolderSpaceOn k α Ω F) :
    CkHolderLocSpace.seminorm K hK (toCkHolderLocSpace f) ≤ (k + 2) * ‖f‖ := by
  have hBCF {i : ℕ} (hi : i ≤ k) :
      ‖CkHolderLocSpace.restrictBCF K hK hi (toCkHolderLocSpace f)‖ ≤ ‖f‖ :=
    (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x ↦ by
      rw [CkHolderLocSpace.restrictBCF_apply, iteratedFDeriv_toCkHolderLocSpace f i (hK x.property)]
      exact f.norm_iteratedFDeriv_extend_le hi ⟨x, hK x.property⟩
  have hH : HolderOnWith (nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F)) α
      (_root_.iteratedFDeriv ℝ k (toCkHolderLocSpace f)) K := fun x hx y hy ↦ by
    rw [iteratedFDeriv_toCkHolderLocSpace f k (hK hx),
      iteratedFDeriv_toCkHolderLocSpace f k (hK hy)]
    exact f.holderOnWith_iteratedFDeriv_extend x (hK hx) y (hK hy)
  have hHK : (nnHolderNorm α ((K : Set E).domRestrict
      (_root_.iteratedFDeriv ℝ k (toCkHolderLocSpace f))) : ℝ) ≤ ‖f‖ :=
    (NNReal.coe_le_coe.2 (HolderWith.restrict_iff.2 hH).nnholderNorm_le).trans
      f.nnHolderNorm_iteratedFDeriv_le
  rw [CkHolderLocSpace.seminorm_eq]
  calc _ ≤ ∑ _ : Fin k, ‖f‖ + ‖f‖ + ‖f‖ := by
        gcongr with i
        · exact hBCF i.is_lt.le
        · exact hBCF le_rfl
    _ = (k + 2) * ‖f‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- `toCkHolderLocSpace` as a linear map. -/
private def toCkHolderLocSpaceₗ : CkHolderSpaceOn k α Ω F →ₗ[ℝ] CkHolderLocSpace k α Ω F where
  toFun := toCkHolderLocSpace
  map_add' f g := CkHolderLocSpace.ext fun x hx ↦ by
    simp only [toCkHolderLocSpace_apply_of_mem _ hx, FunLike.coe_add, Pi.add_apply, coe_add]
  map_smul' c f := CkHolderLocSpace.ext fun x hx ↦ by
    simp only [toCkHolderLocSpace_apply_of_mem _ hx, FunLike.coe_smul, Pi.smul_apply, coe_smul,
      RingHom.id_apply]

/-- The inclusion `C^{k,α}(Ω) → C^{k,α}_loc(Ω)`, sending an element to its extension by zero, as a
continuous linear map. -/
def toCkHolderLocSpaceCLM : CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderLocSpace k α Ω F where
  toLinearMap := toCkHolderLocSpaceₗ
  cont := WithSeminorms.continuous_normedSpace_dom (CkHolderSpaceOn k α Ω F)
    CkHolderLocSpace.withSeminorms toCkHolderLocSpaceₗ fun K ↦ ⟨(k + 2 : ℝ≥0), fun f ↦ by
      rw [Seminorm.comp_apply, smul_apply, coe_normSeminorm, NNReal.smul_def,
        smul_eq_mul, CkHolderLocSpace.seminormFamily_apply]
      exact_mod_cast seminorm_toCkHolderLocSpace_le K.val K.property f⟩

/-- The inclusion `C^{k,α}(Ω) → C^{k,α}_loc(Ω)` does not change the values on `Ω`. -/
@[simp]
theorem toCkHolderLocSpaceCLM_apply_of_mem (f : CkHolderSpaceOn k α Ω F) {x : E} (hx : x ∈ Ω) :
    toCkHolderLocSpaceCLM f x = f ⟨x, hx⟩ :=
  toCkHolderLocSpace_apply_of_mem f hx

/-- The inclusion `C^{k,α}(Ω) → C^{k,α}_loc(Ω)` does not change the derivatives on `Ω`. -/
theorem iteratedFDeriv_toCkHolderLocSpaceCLM (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1))
    {x : E} (hx : x ∈ Ω) :
    _root_.iteratedFDeriv ℝ i (toCkHolderLocSpaceCLM f) x = f.iteratedFDeriv i ⟨x, hx⟩ :=
  (iteratedFDeriv_toCkHolderLocSpace f i hx).trans (f.iteratedFDeriv_extend i ⟨x, hx⟩)

/-- The inclusion `C^{k,α}(Ω) → C^{k,α}_loc(Ω)` is injective. -/
theorem toCkHolderLocSpaceCLM_injective :
    Function.Injective (toCkHolderLocSpaceCLM (k := k) (α := α) (Ω := Ω) (F := F)) :=
  fun f g h ↦ ext fun x ↦ by
    rw [← toCkHolderLocSpaceCLM_apply_of_mem f x.property,
      ← toCkHolderLocSpaceCLM_apply_of_mem g x.property, h]

end CkHolderSpaceOn

end TauCeti

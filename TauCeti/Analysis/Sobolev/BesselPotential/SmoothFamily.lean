/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.Exp
import TauCeti.Analysis.Sobolev.BesselPotential.Operator
import TauCeti.Analysis.Sobolev.BesselPotential.SmoothMultiplier
import TauCeti.Analysis.Sobolev.WeakDeriv.TemperedDistribution

/-!
# Families of functions that are smooth in a Bessel-potential space

Let `f : X → E → G` be a family of functions on `E`, indexed by a real normed space `X` of
parameters. The family is *smooth in `H^{s,p}(E, G)` at `c₀`*
(`BesselPotentialSpace.IsSmoothFamilyAt`) when some family of elements of `H^{s,p}(E, G)`, `C^∞`
at `c₀`, has `Lᵖ` function almost everywhere `f c` for every `c` near `c₀`. Since an element of
`H^{s,p}`, `s ≥ 0`, is determined by its `Lᵖ` function, every family of elements representing `f`
near `c₀` is then `C^∞` at `c₀` (`BesselPotentialSpace.IsSmoothFamilyAt.contDiffAt`), and a family
that is smooth at every point is represented by one globally smooth family
(`BesselPotentialSpace.exists_contDiff_of_forall_isSmoothFamilyAt`).

This is the bookkeeping for proofs that a family of functions built pointwise from simpler ones,
such as the fields of plane vortices over a space of divisors, depends smoothly on its parameter
in a Sobolev space: sums, differences, products by smooth scalar functions of the parameter and
lowering of the order preserve the property. So do products by a fixed function with bounded
derivatives (`BesselPotentialSpace.IsSmoothFamilyAt.smulLeft`), directional derivatives, which
lower the order by one (`BesselPotentialSpace.IsSmoothFamilyAt.lineDeriv`), and, in the algebra
`H^s(E)`, `s > dim E / 2`, products and `exp - 1` (`BesselPotentialSpace.IsSmoothFamilyAt.mul`,
`BesselPotentialSpace.IsSmoothFamilyAt.cexp_sub_one`). A smooth family of `Lᵖ` functions is smooth
in `H^{0,p} = Lᵖ` (`BesselPotentialSpace.IsSmoothFamilyAt.of_contDiff_Lp`), and a family of `C¹`
functions that is smooth in `H^s` at every point together with its first derivatives is smooth in
`H^{s+1}` (`BesselPotentialSpace.isSmoothFamilyAt_add_one`).

## Main declarations

* `BesselPotentialSpace.IsSmoothFamilyAt`: the family `f c` is smooth in `H^{s,p}(E, G)` at `c₀`.
* `BesselPotentialSpace.IsSmoothFamilyAt.contDiffAt`: every family of elements of `H^{s,p}(E, G)`
  representing `f` near `c₀` is `C^∞` at `c₀`.
* `BesselPotentialSpace.exists_contDiff_of_forall_isSmoothFamilyAt`: a family that is smooth at
  every point is represented by a smooth family of elements of `H^{s,p}(E, G)`.
* `BesselPotentialSpace.isSmoothFamilyAt_add_one`: a family smooth in `H^s` together with its first
  derivatives is smooth in `H^{s+1}`.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal BesselPotentialSpace

namespace BesselPotentialSpace

variable {E G X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  {s t : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The family `f c` of functions on `E` is **smooth in `H^{s,p}(E, G)` at `c₀`**: some family of
elements of `H^{s,p}(E, G)`, `C^∞` at `c₀`, has `Lᵖ` function almost everywhere `f c` for every
`c` near `c₀`. -/
def IsSmoothFamilyAt (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs : 0 ≤ s) (c₀ : X) (f : X → E → G) :
    Prop :=
  ∃ D : X → H^{s, p}(E, G), ContDiffAt ℝ ∞ D c₀ ∧
    ∀ᶠ c in 𝓝 c₀, ⇑(inclusionLp hs (D c)) =ᵐ[volume] f c

variable {hs : 0 ≤ s} {c₀ : X} {f g : X → E → G}

/-- Unfolds `IsSmoothFamilyAt` into a representing family that is `C^∞` at `c₀`. -/
theorem isSmoothFamilyAt_iff : IsSmoothFamilyAt s p hs c₀ f ↔ ∃ D : X → H^{s, p}(E, G),
    ContDiffAt ℝ ∞ D c₀ ∧ ∀ᶠ c in 𝓝 c₀, ⇑(inclusionLp hs (D c)) =ᵐ[volume] f c :=
  Iff.rfl

namespace IsSmoothFamilyAt

/-- A smooth family of elements of `H^{s,p}(E, G)` represents a family that is smooth at every
point. -/
theorem of_contDiff {D : X → H^{s, p}(E, G)} (hD : ContDiff ℝ ∞ D)
    (hDf : ∀ c, ⇑(inclusionLp hs (D c)) =ᵐ[volume] f c) : IsSmoothFamilyAt s p hs c₀ f :=
  ⟨D, hD.contDiffAt, .of_forall hDf⟩

/-- **Uniqueness of the representing family.** If `f` is smooth in `H^{s,p}(E, G)` at `c₀`, then
every family of elements of `H^{s,p}(E, G)` whose `Lᵖ` functions are `f c` near `c₀` is `C^∞` at
`c₀`. -/
theorem contDiffAt (hf : IsSmoothFamilyAt s p hs c₀ f) {D : X → H^{s, p}(E, G)}
    (hD : ∀ᶠ c in 𝓝 c₀, ⇑(inclusionLp hs (D c)) =ᵐ[volume] f c) : ContDiffAt ℝ ∞ D c₀ := by
  obtain ⟨D', hD', hD'f⟩ := hf
  refine hD'.congr_of_eventuallyEq ?_
  filter_upwards [hD, hD'f] with c h₁ h₂
  exact ext_of_ae_eq_inclusionLp hs (h₁.trans h₂.symm)

/-- Families that agree near `c₀` are smooth at `c₀` together. -/
theorem congr (hf : IsSmoothFamilyAt s p hs c₀ f) (h : ∀ᶠ c in 𝓝 c₀, f c = g c) :
    IsSmoothFamilyAt s p hs c₀ g := by
  obtain ⟨D, hD, hDf⟩ := hf
  refine ⟨D, hD, ?_⟩
  filter_upwards [hDf, h] with c h₁ h₂
  exact h₂ ▸ h₁

/-- Sums of families smooth at `c₀`. -/
theorem add (hf : IsSmoothFamilyAt s p hs c₀ f) (hg : IsSmoothFamilyAt s p hs c₀ g) :
    IsSmoothFamilyAt s p hs c₀ fun c x ↦ f c x + g c x := by
  obtain ⟨D, hD, hDf⟩ := hf
  obtain ⟨D', hD', hD'g⟩ := hg
  refine ⟨D + D', hD.add hD', ?_⟩
  filter_upwards [hDf, hD'g] with c h₁ h₂
  exact coeFn_inclusionLp_add_ae_eq hs h₁ h₂

/-- Differences of families smooth at `c₀`. -/
theorem sub (hf : IsSmoothFamilyAt s p hs c₀ f) (hg : IsSmoothFamilyAt s p hs c₀ g) :
    IsSmoothFamilyAt s p hs c₀ fun c x ↦ f c x - g c x := by
  obtain ⟨D, hD, hDf⟩ := hf
  obtain ⟨D', hD', hD'g⟩ := hg
  refine ⟨D - D', hD.sub hD', ?_⟩
  filter_upwards [hDf, hD'g] with c h₁ h₂
  exact coeFn_inclusionLp_sub_ae_eq hs h₁ h₂

/-- Products by a scalar function of the parameter that is `C^∞` at `c₀`. -/
theorem smul {γ : X → ℂ} (hγ : ContDiffAt ℝ ∞ γ c₀) (hf : IsSmoothFamilyAt s p hs c₀ f) :
    IsSmoothFamilyAt s p hs c₀ fun c x ↦ γ c • f c x := by
  obtain ⟨D, hD, hDf⟩ := hf
  refine ⟨fun c ↦ γ c • D c, hγ.smul hD, ?_⟩
  filter_upwards [hDf] with c h
  exact coeFn_inclusionLp_smul_ae_eq hs _ h

/-- Lowering the order. -/
theorem mono {ht : 0 ≤ t} (hf : IsSmoothFamilyAt t p ht c₀ f) (hst : s ≤ t) :
    IsSmoothFamilyAt s p hs c₀ f := by
  obtain ⟨D, hD, hDf⟩ := hf
  refine ⟨fun c ↦ inclusion hst (D c),
    ((inclusion hst).restrictScalars ℝ).contDiff.contDiffAt.comp c₀ hD, ?_⟩
  filter_upwards [hDf] with c h
  rwa [inclusionLp_inclusion]

end IsSmoothFamilyAt

/-- The zero family is smooth everywhere. -/
theorem isSmoothFamilyAt_zero : IsSmoothFamilyAt s p hs c₀ fun (_ : X) (_ : E) ↦ (0 : G) :=
  .of_contDiff (D := 0) contDiff_const fun _ ↦ by
    rw [Pi.zero_apply, map_zero]
    exact Lp.coeFn_zero G p volume

/-- Finite sums of families smooth at `c₀`. -/
theorem IsSmoothFamilyAt.sum {ι : Type*} (u : Finset ι) {f : ι → X → E → G}
    (hf : ∀ a ∈ u, IsSmoothFamilyAt s p hs c₀ (f a)) :
    IsSmoothFamilyAt s p hs c₀ fun c x ↦ ∑ a ∈ u, f a c x := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using isSmoothFamilyAt_zero
  | insert a u ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a u)).add
      (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))

/-- **Smooth at every point.** A family that is smooth in `H^{s,p}(E, G)` at every point is
represented by one smooth family of elements of `H^{s,p}(E, G)`. -/
theorem exists_contDiff_of_forall_isSmoothFamilyAt {f : X → E → G}
    (h : ∀ c₀, IsSmoothFamilyAt s p hs c₀ f) :
    ∃ D : X → H^{s, p}(E, G), ContDiff ℝ ∞ D ∧ ∀ c, ⇑(inclusionLp hs (D c)) =ᵐ[volume] f c := by
  choose D hD hDf using h
  have hf (c : X) : ⇑(inclusionLp hs (D c c)) =ᵐ[volume] f c := (hDf c).self_of_nhds
  exact ⟨fun c ↦ D c c, contDiff_iff_contDiffAt.2 fun c₀ ↦
    IsSmoothFamilyAt.contDiffAt ⟨D c₀, hD c₀, hDf c₀⟩ (.of_forall hf), hf⟩

/-- **Smooth families of `Lᵖ` functions.** A smooth family of elements of `Lᵖ(E, G)` represents a
family that is smooth in `H^{0,p}(E, G) = Lᵖ(E, G)` at every point. -/
theorem IsSmoothFamilyAt.of_contDiff_Lp {g : X → Lp G p (volume : Measure E)}
    (hg : ContDiff ℝ ∞ g) (hgf : ∀ c, ⇑(g c) =ᵐ[volume] f c) :
    IsSmoothFamilyAt 0 p le_rfl c₀ f := by
  set J := (toLpₗᵢ E G 0 p).symm.toContinuousLinearEquiv.toContinuousLinearMap
  refine .of_contDiff (D := fun c ↦ J (g c)) ((J.restrictScalars ℝ).contDiff.comp hg) fun c ↦ ?_
  have hJ : (J (g c)).toLp = g c :=
    (toLpₗᵢ_apply _).symm.trans ((toLpₗᵢ E G 0 p).apply_symm_apply (g c))
  rw [inclusionLp_zero, hJ]
  exact hgf c

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {u : X → E → F}

/-- **Raising the order by one.** A family of `C¹` functions that is smooth in `H^s(E, F)` at every
point, together with its first derivatives along an orthonormal basis `b` of `E`, is smooth in
`H^{s+1}(E, F)` at every point. -/
theorem isSmoothFamilyAt_add_one {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (hu₁ : ∀ c, ContDiff ℝ 1 (u c)) (hu : ∀ c₀, IsSmoothFamilyAt s 2 hs c₀ u)
    (hu' : ∀ i c₀, IsSmoothFamilyAt s 2 hs c₀ fun c x ↦ fderiv ℝ (u c) x (b i)) (c₀ : X) :
    IsSmoothFamilyAt (s + 1) 2 (by linarith) c₀ u := by
  obtain ⟨D, hD, hDu⟩ := exists_contDiff_of_forall_isSmoothFamilyAt hu
  choose D' hD' hD'u using fun i ↦ exists_contDiff_of_forall_isSmoothFamilyAt (hu' i)
  obtain ⟨w, hw, hwD⟩ := exists_contDiff_inclusion_eq_of_lineDerivOp_eq b hD hD' fun c i ↦ by
    rw [← toTemperedDistribution_inclusionLp hs, ← toTemperedDistribution_inclusionLp hs]
    exact TauCeti.lineDerivOp_toTemperedDistribution_eq_of_contDiff (hu₁ c) (hDu c) (hD'u i c)
  refine .of_contDiff hw fun c ↦ ?_
  rw [← inclusionLp_inclusion (by linarith : s ≤ s + 1) hs, hwD]
  exact hDu c

namespace IsSmoothFamilyAt

/-- Products by a fixed function `g` on `E` with bounded derivatives of order at most `k`, at an
integer order `k` and for `1 < p < ∞`. -/
theorem smulLeft (hp : 1 < p) (hp_top : p ≠ ⊤) {k : ℕ} {g : E → ℂ}
    (hbd : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) (hg : g.HasTemperateGrowth)
    (hu : IsSmoothFamilyAt k p k.cast_nonneg c₀ u) :
    IsSmoothFamilyAt k p k.cast_nonneg c₀ fun c x ↦ g x • u c x := by
  obtain ⟨D, hD, hDu⟩ := hu
  set M := smulLeftCLMOfNormIteratedFDerivLe (F := F) hp hp_top hbd
  refine ⟨fun c ↦ M (D c), (M.restrictScalars ℝ).contDiff.contDiffAt.comp c₀ hD, ?_⟩
  filter_upwards [hDu] with c h
  filter_upwards [coeFn_inclusionLp_smulLeftCLMOfNormIteratedFDerivLe_ae_eq hp hp_top hbd hg (D c),
    h] with x h₁ h₂
  rw [h₁, h₂]

/-- Directional derivatives, from `H^{s+1,p}(E, F)` to `H^{s,p}(E, F)`, for `1 < p < ∞`, of a family
of functions that are `C¹` near `c₀`. -/
theorem lineDeriv (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hu : IsSmoothFamilyAt (s + 1) p (by linarith) c₀ u)
    (hu₁ : ∀ᶠ c in 𝓝 c₀, ContDiff ℝ 1 (u c)) (v : E) :
    IsSmoothFamilyAt s p hs c₀ fun c x ↦ fderiv ℝ (u c) x v := by
  obtain ⟨D, hD, hDu⟩ := hu
  set L := lineDerivCLM (F := F) (s := s) hp hp_top v
  refine ⟨fun c ↦ L (D c), (L.restrictScalars ℝ).contDiff.contDiffAt.comp c₀ hD, ?_⟩
  filter_upwards [hDu, hu₁] with c h₁ h₂
  exact coeFn_inclusionLp_lineDerivCLM_ae_eq_fderiv hp hp_top hs h₂ h₁ v

end IsSmoothFamilyAt

end InnerProductSpace

namespace IsSmoothFamilyAt

open Module

variable {u v : X → E → ℂ}

/-- Products, in the algebra `H^s(E)`, `s > dim E / 2`. -/
theorem mul (hs' : finrank ℝ E < 2 * s) (hu : IsSmoothFamilyAt s 2 hs c₀ u)
    (hv : IsSmoothFamilyAt s 2 hs c₀ v) : IsSmoothFamilyAt s 2 hs c₀ fun c x ↦ u c x * v c x := by
  obtain ⟨D, hD, hDu⟩ := hu
  obtain ⟨D', hD', hD'v⟩ := hv
  refine ⟨fun c ↦ mulCLM hs' (D c) (D' c),
    ((mulCLM hs').isBoundedBilinearMap.contDiff.restrict_scalars ℝ).contDiffAt.comp c₀
      (hD.prodMk hD'), ?_⟩
  filter_upwards [hDu, hD'v] with c h₁ h₂
  filter_upwards [coeFn_inclusionLp_mulCLM hs' hs (D c) (D' c), h₁, h₂] with x hx h₁ h₂
  rw [hx, h₁, h₂]

/-- Exponentials `exp u - 1`, in the algebra `H^s(E)`, `s > dim E / 2`. -/
theorem cexp_sub_one (hs' : finrank ℝ E < 2 * s) (hu : IsSmoothFamilyAt s 2 hs c₀ u) :
    IsSmoothFamilyAt s 2 hs c₀ fun c x ↦ Complex.exp (u c x) - 1 := by
  obtain ⟨D, hD, hDu⟩ := hu
  refine ⟨fun c ↦ BesselPotentialSpace.expSubOne hs' (D c),
    ((contDiff_expSubOne hs').restrict_scalars ℝ).contDiffAt.comp c₀ hD, ?_⟩
  filter_upwards [hDu] with c h
  have he := coeFn_toLp_inclusion_expSubOne hs' hs (D c)
  rw [toLp_inclusion, toLp_inclusion] at he
  filter_upwards [he, h] with x h₁ h₂
  rw [h₁, h₂]

end IsSmoothFamilyAt

end BesselPotentialSpace

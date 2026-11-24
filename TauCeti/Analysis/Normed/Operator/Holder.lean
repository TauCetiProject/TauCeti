/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.MetricSpace.Holder
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Topology.MetricSpace.Holder

/-!
# Linear and bilinear operations on bounded Hölder functions

A continuous bilinear map sends two bounded Hölder functions of the same exponent to a Hölder
function. The estimate keeps the uniform bounds separate from the Hölder constants, so it also
applies to restrictions and yields the product estimate for the supremum-plus-Hölder norm. On a
compact set the uniform bounds are automatic for a positive exponent
(`ContinuousLinearMap.exists_holderOnWith_comp₂_of_isCompact`).

If one argument vanishes off a set `s`, the other need only be Hölder and bounded on `s`
(`ContinuousLinearMap.holderWith_comp₂_of_eq_zero`, and `HolderWith.smul_of_eq_zero` for scalar
multiplication): this is how a cutoff extends a function given on `s` to the whole space, and how
freezing a coefficient on the support of a localized function is estimated. The relative form
`HolderOnWith.smul_of_eq_zero` extends it from `s` to a larger set `t` instead. When both factors
are Hölder and bounded on the same set, so is their product (`HolderOnWith.smul_of_norm_le`).

A continuous linear map applied after a Hölder function is Hölder, the constant multiplied by
the operator norm (`ContinuousLinearMap.holderWith_comp`). Evaluating a Hölder family of
continuous linear maps at a vector of norm at most one keeps the Hölder constant
(`HolderOnWith.clm_apply_of_norm_le_one`).

Composing a family of bilinear maps with two families of linear maps, `(f x).bilinearComp (g x)
(h x)`, preserves Hölder continuity when the three families are bounded
(`ContinuousLinearMap.holderOnWith_bilinearComp`); this is how a second derivative transforms
under a change of variables. Likewise the bilinear maps `(h, k) ↦ B x h k • c x` form a Hölder
family when `B` and `c` are Hölder and bounded
(`ContinuousLinearMap.holderOnWith_smulRightL_flip_comp`).

For a scalar-valued continuous multilinear map `L`, the map `L.smulRight (g x - g y)` has norm at
most `‖L‖` times the Hölder bound on the increment of `g` (`HolderWith.norm_smulRight_sub_le`).

The argument is adapted from `holderWith_bilinear_of_norm_le` in
[DifferentialGeometry, Holder/Bilinear.lean](https://github.com/qinz1yang/differential-geometry/blob/7a48598d35109aa99d1cc678e2724c213cdf4ff3/DifferentialGeometry/Analysis/Schauder/Holder/Bilinear.lean).
Here the map may be semilinear over arbitrary nontrivially normed fields, the spaces are
seminormed, the domain is a pseudo-emetric space, and the operator norm is explicit.
-/

public section

open Set
open scoped NNReal ENNReal

namespace ContinuousLinearMap

variable {𝕜 𝕜₂ 𝕜₃ X E F G : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NontriviallyNormedField 𝕜₃] [PseudoEMetricSpace X]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜₃ G]
  {σ₁₃ : 𝕜 →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃} [RingHomIsometric σ₁₃] [RingHomIsometric σ₂₃]

/-- A continuous (semi)linear map applied after a Hölder function is Hölder with the same exponent,
the constant multiplied by the operator norm. -/
theorem holderWith_comp (L : E →SL[σ₁₃] G) {C r : ℝ≥0} {f : X → E} (hf : HolderWith C r f) :
    HolderWith (‖L‖₊ * C) r fun x ↦ L (f x) := by
  have h := (holderWith_one.2 L.lipschitzWith).comp hf
  rwa [NNReal.coe_one, NNReal.rpow_one, one_mul, Function.comp_def] at h

/-- A bilinear map preserves Hölder continuity on a set when both input functions are bounded
there. The constant is `‖B‖ * (Mf * Kg + Mg * Kf)`. -/
theorem holderOnWith_comp₂ (B : E →SL[σ₁₃] F →SL[σ₂₃] G)
    {α Kf Kg Mf Mg : ℝ≥0} {f : X → E} {g : X → F} {s : Set X}
    (hf : HolderOnWith Kf α f s) (hg : HolderOnWith Kg α g s)
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ Mf) (hgnorm : ∀ x ∈ s, ‖g x‖ ≤ Mg) :
    HolderOnWith (‖B‖₊ * (Mf * Kg + Mg * Kf)) α (fun x ↦ B (f x) (g x)) s := by
  intro x hx y hy
  have hsplit : B (f x) (g x) - B (f y) (g y) =
      B (f x) (g x - g y) + B (f x - f y) (g y) := by
    simp only [map_sub, sub_apply]
    abel
  have hle : ‖B (f x) (g x) - B (f y) (g y)‖ ≤
      ‖B‖ * ‖f x‖ * ‖g x - g y‖ + ‖B‖ * ‖f x - f y‖ * ‖g y‖ := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _))
  calc
    edist (B (f x) (g x)) (B (f y) (g y)) ≤
        ‖B‖₊ * ‖f x‖₊ * edist (g x) (g y) + ‖B‖₊ * edist (f x) (f y) * ‖g y‖₊ := by
      simp only [edist_nndist, nnDist_eq_nnNorm]
      exact_mod_cast hle
    _ ≤ ‖B‖₊ * Mf * (Kg * edist x y ^ (α : ℝ)) + ‖B‖₊ * (Kf * edist x y ^ (α : ℝ)) * Mg := by
      gcongr
      · exact_mod_cast hfnorm x hx
      · exact hg.edist_le hx hy
      · exact hf.edist_le hx hy
      · exact_mod_cast hgnorm y hy
    _ = _ := by
      push_cast
      ring

/-- On a compact set, a bilinear map sends two functions that are `α`-Hölder there, with
`0 < α`, to an `α`-Hölder function: Hölder functions of positive exponent are continuous, hence
bounded on the compact set. -/
theorem exists_holderOnWith_comp₂_of_isCompact (B : E →SL[σ₁₃] F →SL[σ₂₃] G)
    {α Kf Kg : ℝ≥0} {f : X → E} {g : X → F} {s : Set X} (hs : IsCompact s) (hα : 0 < α)
    (hf : HolderOnWith Kf α f s) (hg : HolderOnWith Kg α g s) :
    ∃ C, HolderOnWith C α (fun x ↦ B (f x) (g x)) s := by
  obtain ⟨Mf, hMf⟩ := hs.exists_bound_of_continuousOn (hf.continuousOn hα)
  obtain ⟨Mg, hMg⟩ := hs.exists_bound_of_continuousOn (hg.continuousOn hα)
  exact ⟨_, B.holderOnWith_comp₂ hf hg (Mf := Mf.toNNReal) (Mg := Mg.toNNReal)
    (fun x hx ↦ (hMf x hx).trans (Real.le_coe_toNNReal Mf))
    (fun x hx ↦ (hMg x hx).trans (Real.le_coe_toNNReal Mg))⟩

/-- A bilinear map preserves global Hölder continuity for uniformly bounded functions. -/
theorem holderWith_comp₂ (B : E →SL[σ₁₃] F →SL[σ₂₃] G)
    {α Kf Kg Mf Mg : ℝ≥0} {f : X → E} {g : X → F}
    (hf : HolderWith Kf α f) (hg : HolderWith Kg α g)
    (hfnorm : ∀ x, ‖f x‖ ≤ Mf) (hgnorm : ∀ x, ‖g x‖ ≤ Mg) :
    HolderWith (‖B‖₊ * (Mf * Kg + Mg * Kf)) α (fun x ↦ B (f x) (g x)) :=
  holderOnWith_univ.mp (B.holderOnWith_comp₂ (hf.holderOnWith univ)
    (hg.holderOnWith univ) (fun x _ ↦ hfnorm x) (fun x _ ↦ hgnorm x))

/-- A bilinear map preserves global Hölder continuity when its second argument vanishes off a set
`s` on which both arguments are bounded and the first one is Hölder. Nothing is assumed about `f`
off `s`: there the product vanishes, and across the boundary of `s` only the bound on `f` and the
Hölder bound on `g` enter. -/
theorem holderWith_comp₂_of_eq_zero (B : E →SL[σ₁₃] F →SL[σ₂₃] G)
    {α Kf Kg Mf Mg : ℝ≥0} {f : X → E} {g : X → F} {s : Set X}
    (hf : HolderOnWith Kf α f s) (hg : HolderWith Kg α g)
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ Mf) (hgnorm : ∀ x ∈ s, ‖g x‖ ≤ Mg) (hg0 : ∀ x ∉ s, g x = 0) :
    HolderWith (‖B‖₊ * (Mf * Kg + Mg * Kf)) α (fun x ↦ B (f x) (g x)) := by
  -- Across the boundary of `s`, the product at `x ∈ s` is `B (f x) (g x - g y)`.
  have hcross : ∀ x ∈ s, ∀ y ∉ s, edist (B (f x) (g x)) (B (f y) (g y)) ≤
      (‖B‖₊ * (Mf * Kg + Mg * Kf)) * edist x y ^ (α : ℝ) := by
    intro x hx y hy
    have hle : ‖B (f x) (g x) - B (f y) (g y)‖ ≤ ‖B‖ * ‖f x‖ * ‖g x - g y‖ := by
      rw [hg0 y hy, map_zero, sub_zero, sub_zero]
      exact B.le_opNorm₂ _ _
    calc
      edist (B (f x) (g x)) (B (f y) (g y)) ≤ ‖B‖₊ * ‖f x‖₊ * edist (g x) (g y) := by
        simp only [edist_nndist, nnDist_eq_nnNorm]
        exact_mod_cast hle
      _ ≤ ‖B‖₊ * Mf * (Kg * edist x y ^ (α : ℝ)) := by
        gcongr
        · exact_mod_cast hfnorm x hx
        · exact hg.edist_le x y
      _ ≤ (‖B‖₊ * (Mf * Kg + Mg * Kf)) * edist x y ^ (α : ℝ) := by
        rw [← mul_assoc, mul_assoc (‖B‖₊ : ℝ≥0∞)]
        gcongr
        exact_mod_cast le_self_add
  have hboth := B.holderOnWith_comp₂ hf (hg.holderOnWith s) hfnorm hgnorm
  intro x y
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
  · exact hboth.edist_le hx hy
  · exact hcross x hx y hy
  · rw [edist_comm, edist_comm x]
    exact hcross y hy x hx
  · simp [hg0 x hx, hg0 y hy]

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 X E E' E'' F F' G H : Type*} [NontriviallyNormedField 𝕜] [PseudoMetricSpace X]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Composing a family of bilinear maps with two families of linear maps preserves Hölder
continuity on a set when all three families are bounded there. The constant is
`Kf Mg Mh + Mf Kg Mh + Mf Mg Kh`. -/
theorem holderOnWith_bilinearComp {α Kf Kg Kh Mf Mg Mh : ℝ≥0} {f : X → E →L[𝕜] F →L[𝕜] G}
    {g : X → E' →L[𝕜] E} {h : X → F' →L[𝕜] F} {s : Set X}
    (hf : HolderOnWith Kf α f s) (hg : HolderOnWith Kg α g s) (hh : HolderOnWith Kh α h s)
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ Mf) (hgnorm : ∀ x ∈ s, ‖g x‖ ≤ Mg)
    (hhnorm : ∀ x ∈ s, ‖h x‖ ≤ Mh) :
    HolderOnWith (Kf * Mg * Mh + Mf * Kg * Mh + Mf * Mg * Kh) α
      (fun x ↦ (f x).bilinearComp (g x) (h x)) s := by
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  have hsplit : (f x).bilinearComp (g x) (h x) - (f y).bilinearComp (g y) (h y) =
      (f x - f y).bilinearComp (g x) (h x) + (f y).bilinearComp (g x - g y) (h x) +
        (f y).bilinearComp (g y) (h x - h y) := by
    ext a b
    simp only [bilinearComp_apply, add_apply, sub_apply, map_sub]
    abel
  have hfd := hf.dist_le hx hy
  have hgd := hg.dist_le hx hy
  have hhd := hh.dist_le hx hy
  rw [dist_eq_norm (f x) (f y)] at hfd
  rw [dist_eq_norm (g x) (g y)] at hgd
  rw [dist_eq_norm (h x) (h y)] at hhd
  rw [dist_eq_norm ((f x).bilinearComp (g x) (h x)) ((f y).bilinearComp (g y) (h y)), hsplit]
  refine (norm_add₃_le (E := E' →L[𝕜] F' →L[𝕜] G)).trans ?_
  refine (add_le_add_three (norm_bilinearComp_le _ _ _) (norm_bilinearComp_le _ _ _)
    (norm_bilinearComp_le _ _ _)).trans ?_
  calc _ ≤ Kf * dist x y ^ (α : ℝ) * Mg * Mh + Mf * (Kg * dist x y ^ (α : ℝ)) * Mh +
          Mf * Mg * (Kh * dist x y ^ (α : ℝ)) := by
        have := hgnorm x hx
        have := hhnorm x hx
        have := hfnorm y hy
        have := hgnorm y hy
        gcongr
    _ = _ := by
      push_cast
      ring

section SMulRight

variable [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The bilinear maps `(h, k) ↦ B x h k • c x` form a Hölder family on `s` when `c` and `B` are
Hölder and bounded there. The constant is `Mc KB + MB Kc`. -/
theorem holderOnWith_smulRightL_flip_comp {α Kc KB Mc MB : ℝ≥0} {c : X → H}
    {B : X → E →L[𝕜] StrongDual 𝕜 E''} {s : Set X}
    (hc : HolderOnWith Kc α c s) (hB : HolderOnWith KB α B s) (hcn : ∀ x ∈ s, ‖c x‖ ≤ Mc)
    (hBn : ∀ x ∈ s, ‖B x‖ ≤ MB) :
    HolderOnWith (Mc * KB + MB * Kc) α
      (fun x => ((StrongDual.smulRightL 𝕜 E'' H).flip (c x)).comp (B x)) s := by
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  have hsplit : ((StrongDual.smulRightL 𝕜 E'' H).flip (c x)).comp (B x) -
      ((StrongDual.smulRightL 𝕜 E'' H).flip (c y)).comp (B y) =
      ((StrongDual.smulRightL 𝕜 E'' H).flip (c x)).comp (B x - B y) +
        ((StrongDual.smulRightL 𝕜 E'' H).flip (c x - c y)).comp (B y) := by
    ext h k
    simp
  have hcd := hc.dist_le hx hy
  have hBd := hB.dist_le hx hy
  rw [dist_eq_norm (c x)] at hcd
  rw [dist_eq_norm (B x)] at hBd
  rw [dist_eq_norm (E := E →L[𝕜] E'' →L[𝕜] H), hsplit]
  refine (norm_add_le (E := E →L[𝕜] E'' →L[𝕜] H) _ _).trans ?_
  refine (add_le_add (norm_smulRightL_flip_comp_le _ _) (norm_smulRightL_flip_comp_le _ _)).trans ?_
  calc _ ≤ Mc * (KB * dist x y ^ (α : ℝ)) + Kc * dist x y ^ (α : ℝ) * MB := by
        have := hcn x hx
        have := hBn y hy
        gcongr
    _ = _ := by push_cast; ring

end SMulRight

end ContinuousLinearMap

namespace HolderWith

variable {𝕜 X G : Type*} [NontriviallyNormedField 𝕜] [PseudoEMetricSpace X]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A scalar factor that is Hölder on the whole space and vanishes off a set `s` turns a function
that is Hölder and bounded only on `s` into a function that is Hölder on the whole space. Nothing
is assumed about `f` off `s`: there the product vanishes, and across the boundary of `s` only the
bound on `f` and the Hölder bound on `c` enter. This is how a cutoff `c` extends a function given
on `s`. -/
theorem smul_of_eq_zero {α Kc Kf Mc Mf : ℝ≥0} {c : X → 𝕜} {f : X → G} {s : Set X}
    (hc : HolderWith Kc α c) (hf : HolderOnWith Kf α f s) (hcnorm : ∀ x, ‖c x‖ ≤ Mc)
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ Mf) (hc0 : ∀ x ∉ s, c x = 0) :
    HolderWith (Mc * Kf + Mf * Kc) α (fun x ↦ c x • f x) := by
  have h := (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] G →L[𝕜] G).flip.holderWith_comp₂_of_eq_zero
    hf hc hfnorm (fun x _ ↦ hcnorm x) hc0
  refine h.mono ?_
  rw [ContinuousLinearMap.opNNNorm_flip, add_comm]
  exact mul_le_of_le_one_left zero_le ContinuousLinearMap.opNNNorm_lsmul_le

/-- For a scalar-valued continuous multilinear map `L` and an `α`-Hölder function `g` with
constant `H`, `‖L.smulRight (g x - g y)‖ ≤ H (‖L‖ dist(x, y)^α)`. -/
theorem norm_smulRight_sub_le {ι Y : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [PseudoMetricSpace Y]
    {H α : ℝ≥0} {g : Y → G} (hg : HolderWith H α g) (L : ContinuousMultilinearMap 𝕜 E 𝕜)
    (x y : Y) : ‖L.smulRight (g x - g y)‖ ≤ H * (‖L‖ * dist x y ^ (α : ℝ)) := by
  rw [ContinuousMultilinearMap.norm_smulRight, mul_left_comm, ← dist_eq_norm]
  exact mul_le_mul_of_nonneg_left (hg.dist_le x y) (norm_nonneg _)

end HolderWith

namespace HolderOnWith

variable {𝕜 X F G : Type*} [NontriviallyNormedField 𝕜] [PseudoEMetricSpace X]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The form of `HolderWith.smul_of_eq_zero` relative to a set `t`: a scalar factor that is Hölder
and bounded on `t` and vanishes at the points of `t` outside `s` turns a function that is Hölder
and bounded only on `s` into a function that is Hölder on `t`. -/
theorem smul_of_eq_zero {α Kc Kf Mc Mf : ℝ≥0} {c : X → 𝕜} {f : X → G} {s t : Set X}
    (hc : HolderOnWith Kc α c t) (hf : HolderOnWith Kf α f s) (hcnorm : ∀ x ∈ t, ‖c x‖ ≤ Mc)
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ Mf) (hc0 : ∀ x ∈ t, x ∉ s → c x = 0) :
    HolderOnWith (Mc * Kf + Mf * Kc) α (fun x ↦ c x • f x) t :=
  HolderWith.restrict_iff.1 <| HolderWith.smul_of_eq_zero (X := t) (c := fun x ↦ c x)
    (f := fun x ↦ f x) (s := {x : t | (x : X) ∈ s}) hc.holderWith (fun x hx y hy ↦ hf x hx y hy)
    (fun x ↦ hcnorm x x.property) (fun x hx ↦ hfnorm x hx) (fun x hx ↦ hc0 x x.property hx)

/-- The product `c • f` of a scalar factor and a function that are both Hölder and bounded on the
same set `s` is Hölder on `s`, with constant `Mc Kf + Mf Kc`. -/
theorem smul_of_norm_le {α Kc Kf Mc Mf : ℝ≥0} {c : X → 𝕜} {f : X → G} {s : Set X}
    (hc : HolderOnWith Kc α c s) (hf : HolderOnWith Kf α f s) (hcnorm : ∀ x ∈ s, ‖c x‖ ≤ Mc)
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ Mf) :
    HolderOnWith (Mc * Kf + Mf * Kc) α (fun x ↦ c x • f x) s :=
  ((ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] G →L[𝕜] G).holderOnWith_comp₂ hc hf hcnorm
    hfnorm).mono_const (mul_le_of_le_one_left zero_le ContinuousLinearMap.opNNNorm_lsmul_le)

/-- Evaluating a family of continuous linear maps, Hölder on `s`, at a vector of norm at most `1`
keeps the Hölder constant. -/
theorem clm_apply_of_norm_le_one [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {C α : ℝ≥0}
    {f : X → F →L[𝕜] G} {s : Set X} (hf : HolderOnWith C α f s) {v : F} (hv : ‖v‖ ≤ 1) :
    HolderOnWith C α (fun x ↦ f x v) s := fun x hx y hy ↦ by
  refine le_trans ?_ (hf x hx y hy)
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← sub_apply]
  exact ENNReal.ofReal_le_ofReal ((f x - f y).unit_le_opNorm _ hv)

end HolderOnWith

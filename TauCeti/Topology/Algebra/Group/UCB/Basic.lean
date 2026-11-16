/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UniformSpace.HeineCantor
public import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Bounded functions uniformly continuous under small left multiplication

For a topological group `G`, `TauCeti.ucb G` is the subalgebra of real bounded continuous
functions `f` such that `f (u * x)` is uniformly close to `f x` for all `u` near `1`:

```text
∀ ε > 0,  ∀ᶠ u in 𝓝 1,  ∀ x,  |f (u * x) - f x| < ε.
```

`TauCeti.UCB G` is the corresponding type. It inherits the supremum norm, the unital algebra
structure and the pointwise order of `G →ᵇ ℝ`, and it is a lattice for the pointwise maximum and
minimum. This is the function space on which invariant means of a topological group are defined.

No separation, local compactness or countability hypothesis on `G` is used. Bekka, de la Harpe and
Valette call this condition *left* uniform continuity, while it is uniform continuity for Mathlib's
*right* uniformity `IsTopologicalGroup.rightUniformSpace`, whose entourages compare `(x, y)` through
`y * x⁻¹`; the formula, not the label, is authoritative. The left and right uniformities of a
general group can differ, so no `IsUniformGroup` structure is used.

## Main definitions

* `TauCeti.ucbSubalgebra 𝕜 G`, `TauCeti.addUCBSubalgebra 𝕜 A`: the subalgebra of `G →ᵇ 𝕜` (or
  `A →ᵇ 𝕜`) defined by the same condition with `‖·‖` in place of `|·|`, for a normed field `𝕜`.
* `TauCeti.ucb G`, `TauCeti.addUCB A`: the real subalgebra of bounded right-uniformly continuous
  functions, the case `𝕜 = ℝ`.
* `TauCeti.UCB G`, `TauCeti.AddUCB A`: their carrier types, real Banach algebras and lattices.
* `TauCeti.AddUCB.toMultiplicativeAlgEquiv`, `TauCeti.AddUCB.toMultiplicativeLinearIsometryEquiv`,
  `TauCeti.UCB.toAdditiveAlgEquiv`, `TauCeti.UCB.toAdditiveLinearIsometryEquiv`: canonical algebra
  and linear-isometry identifications across `Multiplicative` and `Additive`.

## Main results

* `TauCeti.compLeftContinuousBounded_mem_ucbSubalgebra`: postcomposition with a continuous linear
  map `𝕜 → 𝕜'` sends `ucbSubalgebra 𝕜 G` to `ucbSubalgebra 𝕜' G`.
* `TauCeti.mem_ucb_iff_tendsto`, `TauCeti.mem_addUCB_iff_tendsto`: the condition says that the
  left-translation orbit tends to `f` in supremum norm as `u → 1` (or `u → 0`).
* `TauCeti.mem_ucb_iff_uniformContinuous`, `TauCeti.mem_addUCB_iff_uniformContinuous`: the
  condition is uniform continuity for the right uniformity.
* `TauCeti.mem_ucbSubalgebra_of_hasCompactSupport`, `TauCeti.mem_ucb_of_hasCompactSupport`,
  `TauCeti.mem_addUCBSubalgebra_of_hasCompactSupport`, `TauCeti.mem_addUCB_of_hasCompactSupport`:
  bounded continuous functions with compact support satisfy the condition.
* `TauCeti.isClosed_ucb`, `TauCeti.isClosed_addUCB`: `ucb G` and `addUCB A` are closed under
  uniform limits, so `UCB G` and `AddUCB A` are complete.
* `TauCeti.sup_mem_ucb`, `TauCeti.inf_mem_ucb`, `TauCeti.abs_mem_ucb`, `TauCeti.sup_mem_addUCB`,
  `TauCeti.inf_mem_addUCB`, `TauCeti.abs_mem_addUCB`: closure under the lattice operations.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix A.3 and
  Definition G.1.4.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction

namespace BoundedContinuousFunction

variable {M β : Type*} [MulOneClass M] [TopologicalSpace M] [SeparatelyContinuousMul M]
  [PseudoMetricSpace β]

/-- The left-multiplication orbit `u ↦ f (u * ·)` of a bounded continuous function tends to `f`
in supremum distance as `u → 1` exactly when `f (u * x)` is uniformly close to `f x` for all `u`
near `1`. -/
@[to_additive /-- The left-addition orbit `u ↦ f (u + ·)` of a bounded continuous function tends
to `f` in supremum distance as `u → 0` exactly when `f (u + x)` is uniformly close to `f x` for all
`u` near `0`. -/]
theorem tendsto_compContinuous_mulLeft_iff (f : M →ᵇ β) :
    Tendsto (fun u => f.compContinuous (ContinuousMap.mulLeft u)) (𝓝 1) (𝓝 f) ↔
      ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : M), ∀ x, dist (f (u * x)) (f x) < ε := by
  rw [Metric.tendsto_nhds]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
  · filter_upwards [h ε hε] with u hu x
    exact (dist_coe_le_dist x).trans_lt hu
  · filter_upwards [h (ε / 2) (half_pos hε)] with u hu
    exact ((dist_le (half_pos hε).le).2 fun x => (hu x).le).trans_lt (half_lt_self hε)

end BoundedContinuousFunction

namespace TauCeti

section Multiplicative

variable {𝕜 G : Type*} [NormedField 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section UniformContinuous

variable {β : Type*} [PseudoMetricSpace β]

/-- A function on a topological group is uniformly continuous for the right uniformity exactly
when `f (u * x)` is uniformly close to `f x` for all `u` near `1`. -/
@[to_additive uniformContinuous_rightUniformSpace_add_iff
  /-- A function on a topological additive group is uniformly continuous for the right uniformity
  exactly when `f (u + x)` is uniformly close to `f x` for all `u` near `0`. -/]
theorem uniformContinuous_rightUniformSpace_iff (f : G → β) :
    (letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
     UniformContinuous f) ↔
      ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, dist (f (u * x)) (f x) < ε := by
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  rw [UniformContinuous, uniformity_eq_comap_nhds_one',
    ((𝓝 (1 : G)).basis_sets.comap _).tendsto_iff Metric.uniformity_basis_dist]
  refine forall₂_congr fun ε _ => ⟨fun ⟨U, hU, h⟩ => ?_, fun h => ?_⟩
  · filter_upwards [hU] with u hu x
    rw [dist_comm]
    exact h (x, u * x) (by simpa using hu)
  · refine ⟨_, h, fun p hp => ?_⟩
    simpa [dist_comm] using hp p.1

/-- A function on a topological group whose values `f (u * x)` are uniformly close to `f x` for
all `u` near `1` is continuous. -/
@[to_additive /-- A function on a topological additive group whose values `f (u + x)` are uniformly
close to `f x` for all `u` near `0` is continuous. -/]
theorem continuous_of_forall_eventually_dist_mul_lt {f : G → β}
    (h : ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, dist (f (u * x)) (f x) < ε) : Continuous f :=
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  ((uniformContinuous_rightUniformSpace_iff f).2 h).continuous

end UniformContinuous

section UCB

variable (𝕜 G) in
/-- The bounded continuous functions `f : G →ᵇ 𝕜` such that `f (u * x)` is uniformly close to
`f x` for all `u` near `1`, as a subalgebra of `G →ᵇ 𝕜`. The real space `ucb G` is the case
`𝕜 = ℝ`. -/
def ucbSubalgebra : Subalgebra 𝕜 (G →ᵇ 𝕜) where
  carrier := {f | ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, ‖f (u * x) - f x‖ < ε}
  mul_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_mulLeft_iff] at hf hg ⊢
    exact hf.mul hg
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_mulLeft_iff] at hf hg ⊢
    exact hf.add hg
  algebraMap_mem' c := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_mulLeft_iff]
    exact tendsto_const_nhds

/-- The defining condition of `ucbSubalgebra 𝕜 G`. -/
theorem mem_ucbSubalgebra_iff {f : G →ᵇ 𝕜} :
    f ∈ ucbSubalgebra 𝕜 G ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, ‖f (u * x) - f x‖ < ε :=
  Iff.rfl

/-- Membership in `ucbSubalgebra 𝕜 G` says that `u ↦ f (u * ·)` tends to `f` in supremum norm as
`u → 1`. -/
theorem mem_ucbSubalgebra_iff_tendsto {f : G →ᵇ 𝕜} :
    f ∈ ucbSubalgebra 𝕜 G ↔
      Tendsto (fun u => f.compContinuous (ContinuousMap.mulLeft u)) (𝓝 1) (𝓝 f) := by
  simp only [mem_ucbSubalgebra_iff, ← dist_eq_norm,
    BoundedContinuousFunction.tendsto_compContinuous_mulLeft_iff]

/-- Postcomposing a function in `ucbSubalgebra 𝕜 G` with a continuous linear map `L : 𝕜 → 𝕜'`,
such as the real or imaginary part `ℂ → ℝ` or the inclusion `ℝ → ℂ`, gives a function in
`ucbSubalgebra 𝕜' G`. -/
theorem compLeftContinuousBounded_mem_ucbSubalgebra {𝕜' 𝕜'' : Type*} [NormedField 𝕜']
    [NontriviallyNormedField 𝕜''] [NormedSpace 𝕜'' 𝕜] [NormedSpace 𝕜'' 𝕜'] (L : 𝕜 →L[𝕜''] 𝕜')
    {f : G →ᵇ 𝕜} (hf : f ∈ ucbSubalgebra 𝕜 G) :
    L.compLeftContinuousBounded G f ∈ ucbSubalgebra 𝕜' G :=
  mem_ucbSubalgebra_iff_tendsto.2 <|
    (((L.compLeftContinuousBounded G).continuous.tendsto f).comp
      (mem_ucbSubalgebra_iff_tendsto.1 hf)).congr fun _ =>
        L.compLeftContinuousBounded_compContinuous ..

/-- A bounded continuous function with compact support belongs to `ucbSubalgebra 𝕜 G`: by the
Heine–Cantor theorem it is uniformly continuous for the right uniformity of `G`. -/
theorem mem_ucbSubalgebra_of_hasCompactSupport {f : G →ᵇ 𝕜} (hf : HasCompactSupport f) :
    f ∈ ucbSubalgebra 𝕜 G := by
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  simpa only [mem_ucbSubalgebra_iff, dist_eq_norm] using
    (uniformContinuous_rightUniformSpace_iff f).1 (hf.uniformContinuous_of_continuous f.continuous)

variable (G) in
/-- The real bounded continuous functions `f` on `G` such that `f (u * x)` is uniformly close to
`f x` for all `u` near `1`, as a subalgebra of `G →ᵇ ℝ`. -/
@[expose]
def ucb : Subalgebra ℝ (G →ᵇ ℝ) :=
  ucbSubalgebra ℝ G

variable (G) in
/-- The real Banach algebra of bounded functions on `G` that are uniformly continuous under small
left multiplication, with the supremum norm, algebra operations and order of `G →ᵇ ℝ`. -/
abbrev UCB : Type _ := ucb G

variable (G) in
/-- `ucb G` is the case `𝕜 = ℝ` of `ucbSubalgebra 𝕜 G`. -/
theorem ucb_eq_ucbSubalgebra : ucb G = ucbSubalgebra ℝ G :=
  rfl

/-- The defining condition of `ucb G`. -/
theorem mem_ucb_iff {f : G →ᵇ ℝ} :
    f ∈ ucb G ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, |f (u * x) - f x| < ε := by
  simp only [ucb_eq_ucbSubalgebra, mem_ucbSubalgebra_iff, Real.norm_eq_abs]

/-- Membership in `ucb G` says that `u ↦ f (u * ·)` tends to `f` in supremum norm as `u → 1`. -/
theorem mem_ucb_iff_tendsto {f : G →ᵇ ℝ} :
    f ∈ ucb G ↔ Tendsto (fun u => f.compContinuous (ContinuousMap.mulLeft u)) (𝓝 1) (𝓝 f) := by
  rw [ucb_eq_ucbSubalgebra, mem_ucbSubalgebra_iff_tendsto]

/-- Membership in `ucb G` is uniform continuity for the right uniformity of `G`. -/
theorem mem_ucb_iff_uniformContinuous {f : G →ᵇ ℝ} :
    f ∈ ucb G ↔
      (letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
       UniformContinuous f) := by
  simp only [mem_ucb_iff, ← Real.dist_eq, uniformContinuous_rightUniformSpace_iff]

/-- A bounded continuous function with compact support belongs to `ucb G`. -/
theorem mem_ucb_of_hasCompactSupport {f : G →ᵇ ℝ} (hf : HasCompactSupport f) : f ∈ ucb G :=
  mem_ucbSubalgebra_of_hasCompactSupport hf

/-- `ucb G` is closed in `G →ᵇ ℝ`: a uniform limit of functions in `ucb G` lies in `ucb G`. -/
theorem isClosed_ucb : IsClosed (ucb G : Set (G →ᵇ ℝ)) := by
  refine isClosed_of_closure_subset fun f hf ε hε => ?_
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.1 hf (ε / 3) (by positivity)
  filter_upwards [hg (ε / 3) (by positivity)] with u hu x
  simp only [← dist_eq_norm] at hu ⊢
  calc dist (f (u * x)) (f x)
      ≤ dist (f (u * x)) (g (u * x)) + dist (g (u * x)) (g x) + dist (g x) (f x) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact (BoundedContinuousFunction.dist_coe_le_dist _).trans_lt hfg
        · exact hu x
        · exact (BoundedContinuousFunction.dist_coe_le_dist _).trans_lt (by rwa [dist_comm])
    _ = ε := by ring

/-- `UCB G` is a real normed group for the supremum norm of `G →ᵇ ℝ`. This inherited instance is
restated so that typeclass search finds it directly when `UCB G` occurs inside another type, such
as the continuous dual `UCB G →L[ℝ] ℝ`; the search through `Subalgebra` and `G →ᵇ ℝ` fails
there. -/
instance : NormedAddCommGroup (UCB G) :=
  inferInstance

/-- `UCB G` is a real Banach space. -/
instance : CompleteSpace (UCB G) :=
  isClosed_ucb.completeSpace_coe

/-- Scalar multiplication on `UCB G` scales the supremum norm: `‖c • f‖ = ‖c‖ * ‖f‖`. Typeclass
search does not derive this from the inherited normed space structure, because the norm on
`UCB G` is found through the normed ring structure of the subalgebra. -/
instance : NormSMulClass ℝ (UCB G) :=
  ⟨fun c f => norm_smul c (f : G →ᵇ ℝ)⟩

/-- Constant functions belong to `ucb G`. -/
@[simp]
theorem const_mem_ucb (c : ℝ) : BoundedContinuousFunction.const G c ∈ ucb G :=
  fun ε hε => .of_forall fun _ _ => by simpa using hε

/-- `ucb G` is closed under the pointwise maximum. -/
theorem sup_mem_ucb {f g : G →ᵇ ℝ} (hf : f ∈ ucb G) (hg : g ∈ ucb G) : f ⊔ g ∈ ucb G := by
  rw [mem_ucb_iff_tendsto] at hf hg ⊢
  exact hf.sup_nhds hg

/-- `ucb G` is closed under the pointwise minimum. -/
theorem inf_mem_ucb {f g : G →ᵇ ℝ} (hf : f ∈ ucb G) (hg : g ∈ ucb G) : f ⊓ g ∈ ucb G := by
  rw [mem_ucb_iff_tendsto] at hf hg ⊢
  exact hf.inf_nhds hg

/-- `ucb G` is closed under the pointwise absolute value. -/
theorem abs_mem_ucb {f : G →ᵇ ℝ} (hf : f ∈ ucb G) : |f| ∈ ucb G :=
  sup_mem_ucb hf (neg_mem hf)

/-- `UCB G` is a lattice for the pointwise maximum and minimum. -/
instance : Lattice (UCB G) :=
  Subtype.lattice (fun _ _ => sup_mem_ucb) (fun _ _ => inf_mem_ucb)

/-- The supremum norm of `UCB G` is solid for its pointwise order, as in `G →ᵇ ℝ`. -/
instance : HasSolidNorm (UCB G) where
  solid _ _ h := HasSolidNorm.solid (α := G →ᵇ ℝ) h

namespace UCB

@[simp, norm_cast]
theorem coe_sup (f g : UCB G) : ((f ⊔ g : UCB G) : G →ᵇ ℝ) = (f : G →ᵇ ℝ) ⊔ (g : G →ᵇ ℝ) :=
  rfl

@[simp, norm_cast]
theorem coe_inf (f g : UCB G) : ((f ⊓ g : UCB G) : G →ᵇ ℝ) = (f : G →ᵇ ℝ) ⊓ (g : G →ᵇ ℝ) :=
  rfl

@[simp, norm_cast]
theorem coe_abs (f : UCB G) : ((|f| : UCB G) : G →ᵇ ℝ) = |(f : G →ᵇ ℝ)| :=
  rfl

/-- Two elements of `UCB G` are equal when they agree at every point. -/
@[ext]
theorem ext {f g : UCB G} (h : ∀ x, (f : G →ᵇ ℝ) x = (g : G →ᵇ ℝ) x) : f = g :=
  Subtype.ext (BoundedContinuousFunction.ext h)

/-- The order on `UCB G` is the pointwise order. -/
theorem le_def {f g : UCB G} : f ≤ g ↔ ∀ x, (f : G →ᵇ ℝ) x ≤ (g : G →ᵇ ℝ) x :=
  Iff.rfl

/-- Each value of an element of `UCB G` is bounded by its supremum norm. -/
theorem abs_apply_le_norm (f : UCB G) (x : G) : |(f : G →ᵇ ℝ) x| ≤ ‖f‖ :=
  (f : G →ᵇ ℝ).norm_coe_le_norm x

/-- Every element of `UCB G` lies below the constant function with value its supremum norm. -/
theorem le_norm_smul_one (f : UCB G) : f ≤ ‖f‖ • 1 :=
  le_def.2 fun x => by simpa using (f : G →ᵇ ℝ).apply_le_norm x

end UCB

end UCB

end Multiplicative

section AddUCB

section Subalgebra

variable {𝕜 A : Type*} [NormedField 𝕜] [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

variable (𝕜 A) in
/-- The bounded continuous functions `f : A →ᵇ 𝕜` such that `f (u + x)` is uniformly close to
`f x` for all `u` near `0`, as a subalgebra of `A →ᵇ 𝕜`. -/
def addUCBSubalgebra : Subalgebra 𝕜 (A →ᵇ 𝕜) where
  carrier := {f | ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : A), ∀ x, ‖f (u + x) - f x‖ < ε}
  mul_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff] at hf hg ⊢
    exact hf.mul hg
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff] at hf hg ⊢
    exact hf.add hg
  algebraMap_mem' _ := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff]
    exact tendsto_const_nhds

attribute [to_additive existing addUCBSubalgebra] ucbSubalgebra

/-- The defining condition of `addUCBSubalgebra 𝕜 A`. -/
theorem mem_addUCBSubalgebra_iff {f : A →ᵇ 𝕜} :
    f ∈ addUCBSubalgebra 𝕜 A ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : A), ∀ x, ‖f (u + x) - f x‖ < ε :=
  Iff.rfl

attribute [to_additive existing mem_addUCBSubalgebra_iff] mem_ucbSubalgebra_iff

/-- Membership in `addUCBSubalgebra 𝕜 A` says that `u ↦ f (u + ·)` tends to `f` in supremum norm as
`u → 0`. -/
theorem mem_addUCBSubalgebra_iff_tendsto {f : A →ᵇ 𝕜} :
    f ∈ addUCBSubalgebra 𝕜 A ↔
      Tendsto (fun u => f.compContinuous (ContinuousMap.addLeft u)) (𝓝 0) (𝓝 f) := by
  simp only [mem_addUCBSubalgebra_iff, ← dist_eq_norm,
    BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff]

attribute [to_additive existing mem_addUCBSubalgebra_iff_tendsto] mem_ucbSubalgebra_iff_tendsto

/-- A bounded continuous function with compact support belongs to `addUCBSubalgebra 𝕜 A`. -/
theorem mem_addUCBSubalgebra_of_hasCompactSupport {f : A →ᵇ 𝕜} (hf : HasCompactSupport f) :
    f ∈ addUCBSubalgebra 𝕜 A := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  simpa only [mem_addUCBSubalgebra_iff, dist_eq_norm] using
    (uniformContinuous_rightUniformSpace_add_iff f).1
      (hf.uniformContinuous_of_continuous f.continuous)

attribute [to_additive existing mem_addUCBSubalgebra_of_hasCompactSupport]
  mem_ucbSubalgebra_of_hasCompactSupport

end Subalgebra

section Real

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

variable (A) in
/-- The real bounded continuous functions `f` on `A` such that `f (u + x)` is uniformly close to
`f x` for all `u` near `0`, as a subalgebra of `A →ᵇ ℝ`. -/
@[expose]
def addUCB : Subalgebra ℝ (A →ᵇ ℝ) :=
  addUCBSubalgebra ℝ A

attribute [to_additive existing addUCB] ucb

variable (A) in
/-- The real Banach algebra of bounded functions on `A` that are uniformly continuous under small
left addition, with the supremum norm, algebra operations and order of `A →ᵇ ℝ`. -/
abbrev AddUCB : Type _ := addUCB A

attribute [to_additive existing AddUCB] UCB
attribute [to_additive_dont_translate] UCB AddUCB

variable (A) in
/-- `addUCB A` is the case `𝕜 = ℝ` of `addUCBSubalgebra 𝕜 A`. -/
theorem addUCB_eq_addUCBSubalgebra : addUCB A = addUCBSubalgebra ℝ A :=
  rfl

/-- The defining condition of `addUCB A`. -/
theorem mem_addUCB_iff {f : A →ᵇ ℝ} :
    f ∈ addUCB A ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : A), ∀ x, |f (u + x) - f x| < ε := by
  simp only [addUCB_eq_addUCBSubalgebra, mem_addUCBSubalgebra_iff, Real.norm_eq_abs]

attribute [to_additive existing mem_addUCB_iff] mem_ucb_iff

/-- Membership in `addUCB A` says that `u ↦ f (u + ·)` tends to `f` in supremum norm as `u → 0`. -/
theorem mem_addUCB_iff_tendsto {f : A →ᵇ ℝ} :
    f ∈ addUCB A ↔ Tendsto (fun u => f.compContinuous (ContinuousMap.addLeft u)) (𝓝 0) (𝓝 f) := by
  rw [addUCB_eq_addUCBSubalgebra, mem_addUCBSubalgebra_iff_tendsto]

attribute [to_additive existing mem_addUCB_iff_tendsto] mem_ucb_iff_tendsto

/-- Membership in `addUCB A` is uniform continuity for the right uniformity of `A`. -/
theorem mem_addUCB_iff_uniformContinuous {f : A →ᵇ ℝ} :
    f ∈ addUCB A ↔
      (letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
       UniformContinuous f) := by
  simp only [mem_addUCB_iff, ← Real.dist_eq, uniformContinuous_rightUniformSpace_add_iff]

attribute [to_additive existing mem_addUCB_iff_uniformContinuous] mem_ucb_iff_uniformContinuous

/-- A bounded continuous function with compact support belongs to `addUCB A`. -/
theorem mem_addUCB_of_hasCompactSupport {f : A →ᵇ ℝ} (hf : HasCompactSupport f) : f ∈ addUCB A :=
  mem_addUCBSubalgebra_of_hasCompactSupport hf

attribute [to_additive existing mem_addUCB_of_hasCompactSupport] mem_ucb_of_hasCompactSupport

/-- Precomposing `f : A →ᵇ ℝ` with `Multiplicative.toAdd` lands in `ucb (Multiplicative A)`
precisely when `f` belongs to `addUCB A`. -/
@[simp]
theorem compContinuous_toAdd_mem_ucb_iff {f : A →ᵇ ℝ} :
    f.compContinuous ⟨Multiplicative.toAdd, continuous_toAdd⟩ ∈ ucb (Multiplicative A) ↔
      f ∈ addUCB A := by
  have h1 : (1 : Multiplicative A) = Multiplicative.ofAdd 0 := rfl
  rw [mem_ucb_iff, mem_addUCB_iff, h1, nhds_ofAdd]
  simp only [Filter.eventually_map]
  exact forall₂_congr fun _ _ => eventually_congr <| .of_forall fun u =>
    ⟨fun h x => h (Multiplicative.ofAdd x), fun h x => h x.toAdd⟩

/-- Precomposing `f : Multiplicative A →ᵇ ℝ` with `Multiplicative.ofAdd` lands in `addUCB A`
precisely when `f` belongs to `ucb (Multiplicative A)`. -/
@[simp]
theorem compContinuous_ofAdd_mem_addUCB_iff {f : Multiplicative A →ᵇ ℝ} :
    f.compContinuous ⟨Multiplicative.ofAdd, continuous_ofAdd⟩ ∈ addUCB A ↔
      f ∈ ucb (Multiplicative A) := by
  rw [← compContinuous_toAdd_mem_ucb_iff]
  rfl

/-- `addUCB A` is closed in `A →ᵇ ℝ`: a uniform limit of functions in `addUCB A` lies in
`addUCB A`. -/
theorem isClosed_addUCB : IsClosed (addUCB A : Set (A →ᵇ ℝ)) := by
  let c : C(Multiplicative A, A) := ⟨Multiplicative.toAdd, continuous_toAdd⟩
  have hpre : (addUCB A : Set (A →ᵇ ℝ)) =
      (fun f : A →ᵇ ℝ => f.compContinuous c) ⁻¹'
        (ucb (Multiplicative A) : Set (Multiplicative A →ᵇ ℝ)) := by
    ext f
    exact compContinuous_toAdd_mem_ucb_iff.symm
  rw [hpre]
  exact isClosed_ucb.preimage (BoundedContinuousFunction.continuous_compContinuous c)

/-- `AddUCB A` is a real normed group for the supremum norm of `A →ᵇ ℝ`. -/
instance : NormedAddCommGroup (AddUCB A) :=
  inferInstance

attribute [to_additive existing instNormedAddCommGroupAddUCB] instNormedAddCommGroupUCB

/-- `AddUCB A` is a real Banach space. -/
instance : CompleteSpace (AddUCB A) :=
  isClosed_addUCB.completeSpace_coe

attribute [to_additive existing instCompleteSpaceAddUCB] instCompleteSpaceUCB

/-- Scalar multiplication on `AddUCB A` scales the supremum norm. -/
instance : NormSMulClass ℝ (AddUCB A) :=
  ⟨fun c f => norm_smul c (f : A →ᵇ ℝ)⟩

attribute [to_additive existing instNormSMulClassRealAddUCB] instNormSMulClassRealUCB

/-- Constant functions belong to `addUCB A`. -/
@[simp]
theorem const_mem_addUCB (c : ℝ) : BoundedContinuousFunction.const A c ∈ addUCB A :=
  fun ε hε => .of_forall fun _ _ => by simpa using hε

/-- `addUCB A` is closed under the pointwise maximum. -/
theorem sup_mem_addUCB {f g : A →ᵇ ℝ} (hf : f ∈ addUCB A) (hg : g ∈ addUCB A) :
    f ⊔ g ∈ addUCB A := by
  rw [mem_addUCB_iff_tendsto] at hf hg ⊢
  exact hf.sup_nhds hg

/-- `addUCB A` is closed under the pointwise minimum. -/
theorem inf_mem_addUCB {f g : A →ᵇ ℝ} (hf : f ∈ addUCB A) (hg : g ∈ addUCB A) :
    f ⊓ g ∈ addUCB A := by
  rw [mem_addUCB_iff_tendsto] at hf hg ⊢
  exact hf.inf_nhds hg

/-- `addUCB A` is closed under the pointwise absolute value. -/
theorem abs_mem_addUCB {f : A →ᵇ ℝ} (hf : f ∈ addUCB A) : |f| ∈ addUCB A :=
  sup_mem_addUCB hf (neg_mem hf)

/-- `AddUCB A` is a lattice for the pointwise maximum and minimum. -/
instance : Lattice (AddUCB A) :=
  Subtype.lattice (fun _ _ => sup_mem_addUCB) (fun _ _ => inf_mem_addUCB)

attribute [to_additive existing instLatticeAddUCB] instLatticeUCB

/-- The supremum norm of `AddUCB A` is solid for its pointwise order, as in `A →ᵇ ℝ`. -/
instance : HasSolidNorm (AddUCB A) where
  solid _ _ h := HasSolidNorm.solid (α := A →ᵇ ℝ) h

attribute [to_additive existing instHasSolidNormAddUCB] instHasSolidNormUCB

namespace AddUCB

@[simp, norm_cast]
theorem coe_sup (f g : AddUCB A) : ((f ⊔ g : AddUCB A) : A →ᵇ ℝ) = (f : A →ᵇ ℝ) ⊔ (g : A →ᵇ ℝ) :=
  rfl

@[simp, norm_cast]
theorem coe_inf (f g : AddUCB A) : ((f ⊓ g : AddUCB A) : A →ᵇ ℝ) = (f : A →ᵇ ℝ) ⊓ (g : A →ᵇ ℝ) :=
  rfl

@[simp, norm_cast]
theorem coe_abs (f : AddUCB A) : ((|f| : AddUCB A) : A →ᵇ ℝ) = |(f : A →ᵇ ℝ)| :=
  rfl

/-- Two elements of `AddUCB A` are equal when they agree at every point. -/
@[ext]
theorem ext {f g : AddUCB A} (h : ∀ x, (f : A →ᵇ ℝ) x = (g : A →ᵇ ℝ) x) : f = g :=
  Subtype.ext (BoundedContinuousFunction.ext h)

/-- The order on `AddUCB A` is the pointwise order. -/
theorem le_def {f g : AddUCB A} : f ≤ g ↔ ∀ x, (f : A →ᵇ ℝ) x ≤ (g : A →ᵇ ℝ) x :=
  Iff.rfl

/-- Each value of an element of `AddUCB A` is bounded by its supremum norm. -/
theorem abs_apply_le_norm (f : AddUCB A) (x : A) : |(f : A →ᵇ ℝ) x| ≤ ‖f‖ :=
  (f : A →ᵇ ℝ).norm_coe_le_norm x

/-- Every element of `AddUCB A` lies below the constant function with value its supremum norm. -/
theorem le_norm_smul_one (f : AddUCB A) : f ≤ ‖f‖ • 1 :=
  le_def.2 fun x => by simpa using (f : A →ᵇ ℝ).apply_le_norm x

variable (A) in
/-- The canonical unital algebra isomorphism between `AddUCB A` and `UCB (Multiplicative A)`. -/
def toMultiplicativeAlgEquiv : AddUCB A ≃ₐ[ℝ] UCB (Multiplicative A) where
  toFun f := ⟨(f : A →ᵇ ℝ).compContinuous ⟨Multiplicative.toAdd, continuous_toAdd⟩,
    compContinuous_toAdd_mem_ucb_iff.2 f.2⟩
  invFun f := ⟨(f : Multiplicative A →ᵇ ℝ).compContinuous ⟨Multiplicative.ofAdd, continuous_ofAdd⟩,
    compContinuous_ofAdd_mem_addUCB_iff.2 f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem toMultiplicativeAlgEquiv_apply (f : AddUCB A) (x : Multiplicative A) :
    (toMultiplicativeAlgEquiv A f : Multiplicative A →ᵇ ℝ) x = (f : A →ᵇ ℝ) x.toAdd :=
  (rfl)

@[simp]
theorem toMultiplicativeAlgEquiv_symm_apply (f : UCB (Multiplicative A)) (x : A) :
    ((toMultiplicativeAlgEquiv A).symm f : A →ᵇ ℝ) x =
      (f : Multiplicative A →ᵇ ℝ) (Multiplicative.ofAdd x) :=
  (rfl)

@[simp]
theorem toMultiplicativeAlgEquiv_le_iff {f g : AddUCB A} :
    toMultiplicativeAlgEquiv A f ≤ toMultiplicativeAlgEquiv A g ↔ f ≤ g :=
  ⟨fun h => le_def.2 fun x => UCB.le_def.1 h (Multiplicative.ofAdd x),
    fun h => UCB.le_def.2 fun x => le_def.1 h x.toAdd⟩

@[simp]
theorem toMultiplicativeAlgEquiv_symm_le_iff {f g : UCB (Multiplicative A)} :
    (toMultiplicativeAlgEquiv A).symm f ≤ (toMultiplicativeAlgEquiv A).symm g ↔ f ≤ g :=
  ⟨fun h => UCB.le_def.2 fun x => le_def.1 h x.toAdd,
    fun h => le_def.2 fun x => UCB.le_def.1 h (Multiplicative.ofAdd x)⟩

variable (A) in
/-- The canonical linear isometry equivalence between `AddUCB A` and `UCB (Multiplicative A)`. -/
def toMultiplicativeLinearIsometryEquiv : AddUCB A ≃ₗᵢ[ℝ] UCB (Multiplicative A) where
  toLinearEquiv := (toMultiplicativeAlgEquiv A).toLinearEquiv
  norm_map' f := by
    rw [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_norm]
    refine le_antisymm ((f : A →ᵇ ℝ).norm_compContinuous_le _) ?_
    exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x =>
      ((toMultiplicativeAlgEquiv A f : Multiplicative A →ᵇ ℝ).norm_coe_le_norm
        (Multiplicative.ofAdd x))

@[simp]
theorem coe_toMultiplicativeLinearIsometryEquiv (f : AddUCB A) :
    toMultiplicativeLinearIsometryEquiv A f = toMultiplicativeAlgEquiv A f :=
  (rfl)

@[simp]
theorem coe_toMultiplicativeLinearIsometryEquiv_symm (f : UCB (Multiplicative A)) :
    (toMultiplicativeLinearIsometryEquiv A).symm f = (toMultiplicativeAlgEquiv A).symm f :=
  (rfl)

end AddUCB

end Real

end AddUCB

section ToAdditive

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace UCB

variable (G) in
/-- The canonical unital algebra isomorphism between `UCB G` and `AddUCB (Additive G)`. -/
def toAdditiveAlgEquiv : UCB G ≃ₐ[ℝ] AddUCB (Additive G) where
  toFun f := ⟨(f : G →ᵇ ℝ).compContinuous ⟨Additive.toMul, continuous_toMul⟩, by
    have h0 : (0 : Additive G) = Additive.ofMul 1 := rfl
    rw [mem_addUCB_iff, h0, nhds_ofMul]
    intro ε hε
    rw [Filter.eventually_map]
    filter_upwards [mem_ucb_iff.1 f.2 ε hε] with u hu x
    exact hu x.toMul⟩
  invFun f := ⟨(f : Additive G →ᵇ ℝ).compContinuous ⟨Additive.ofMul, continuous_ofMul⟩, by
    have h1 : (1 : G) = (0 : Additive G).toMul := rfl
    rw [mem_ucb_iff, h1, nhds_toMul]
    intro ε hε
    rw [Filter.eventually_map]
    filter_upwards [mem_addUCB_iff.1 f.2 ε hε] with u hu x
    exact hu (Additive.ofMul x)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem toAdditiveAlgEquiv_apply (f : UCB G) (x : Additive G) :
    (toAdditiveAlgEquiv G f : Additive G →ᵇ ℝ) x = (f : G →ᵇ ℝ) x.toMul :=
  (rfl)

@[simp]
theorem toAdditiveAlgEquiv_symm_apply (f : AddUCB (Additive G)) (x : G) :
    ((toAdditiveAlgEquiv G).symm f : G →ᵇ ℝ) x = (f : Additive G →ᵇ ℝ) (Additive.ofMul x) :=
  (rfl)

@[simp]
theorem toAdditiveAlgEquiv_le_iff {f g : UCB G} :
    toAdditiveAlgEquiv G f ≤ toAdditiveAlgEquiv G g ↔ f ≤ g :=
  ⟨fun h => le_def.2 fun x => AddUCB.le_def.1 h (Additive.ofMul x),
    fun h => AddUCB.le_def.2 fun x => le_def.1 h x.toMul⟩

@[simp]
theorem toAdditiveAlgEquiv_symm_le_iff {f g : AddUCB (Additive G)} :
    (toAdditiveAlgEquiv G).symm f ≤ (toAdditiveAlgEquiv G).symm g ↔ f ≤ g :=
  ⟨fun h => AddUCB.le_def.2 fun x => le_def.1 h x.toMul,
    fun h => le_def.2 fun x => AddUCB.le_def.1 h (Additive.ofMul x)⟩

variable (G) in
/-- The canonical linear isometry equivalence between `UCB G` and `AddUCB (Additive G)`. -/
def toAdditiveLinearIsometryEquiv : UCB G ≃ₗᵢ[ℝ] AddUCB (Additive G) where
  toLinearEquiv := (toAdditiveAlgEquiv G).toLinearEquiv
  norm_map' f := by
    rw [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_norm]
    refine le_antisymm ((f : G →ᵇ ℝ).norm_compContinuous_le _) ?_
    exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x =>
      ((toAdditiveAlgEquiv G f : Additive G →ᵇ ℝ).norm_coe_le_norm (Additive.ofMul x))

@[simp]
theorem coe_toAdditiveLinearIsometryEquiv (f : UCB G) :
    toAdditiveLinearIsometryEquiv G f = toAdditiveAlgEquiv G f :=
  (rfl)

@[simp]
theorem coe_toAdditiveLinearIsometryEquiv_symm (f : AddUCB (Additive G)) :
    (toAdditiveLinearIsometryEquiv G).symm f = (toAdditiveAlgEquiv G).symm f :=
  (rfl)

end UCB

end ToAdditive

end TauCeti

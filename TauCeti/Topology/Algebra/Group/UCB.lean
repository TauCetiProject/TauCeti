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

The group acts on `UCB G` by left translation `(L_g f) x = f (g⁻¹ * x)`, so that
`L_(g * h) = L_g ∘ L_h`; invariant means are taken with respect to this action. Left translation
preserves `ucb G` because conjugation by `g` is continuous. Right translations
`(R_g f) x = f (x * g)` also preserve `ucb G` and commute with left translations.

No separation, local compactness or countability hypothesis on `G` is used. Bekka, de la Harpe and
Valette call this condition *left* uniform continuity, while it is uniform continuity for Mathlib's
*right* uniformity `IsTopologicalGroup.rightUniformSpace`, whose entourages compare `(x, y)` through
`y * x⁻¹`; the formula, not the label, is authoritative. The left and right uniformities of a
general group can differ, so no `IsUniformGroup` structure is used.

## Main definitions

* `TauCeti.ucb G`: the subalgebra of `G →ᵇ ℝ` defined by the condition above.
* `TauCeti.UCB G`: its carrier type, a real Banach algebra and lattice.
* `TauCeti.UCB.translate`: left translation `L_g`, a homomorphism from `G` to the linear isometry
  equivalences of `UCB G`.
* `TauCeti.UCB.rightTranslate`: right translation `R_g`, likewise.

## Main results

* `TauCeti.mem_ucb_iff_tendsto`: the condition says that the left-multiplication orbit
  `u ↦ f (u * ·)` tends to `f` in supremum norm as `u → 1`.
* `TauCeti.mem_ucb_iff_uniformContinuous`: the condition is uniform continuity for the right
  uniformity of `G`.
* `TauCeti.isClosed_ucb`: `ucb G` is closed under uniform limits, so `UCB G` is complete.
* `TauCeti.sup_mem_ucb`, `TauCeti.inf_mem_ucb`, `TauCeti.abs_mem_ucb`: closure under the lattice
  operations.
* `TauCeti.UCB.continuous_translate_apply`: each orbit `g ↦ L_g f` is continuous in supremum norm.
* `TauCeti.UCB.commute_translate_rightTranslate`: left and right translations commute.

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

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section UniformContinuous

variable {β : Type*} [PseudoMetricSpace β]

/-- A function on a topological group is uniformly continuous for the right uniformity exactly
when `f (u * x)` is uniformly close to `f x` for all `u` near `1`. -/
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
theorem continuous_of_forall_eventually_dist_mul_lt {f : G → β}
    (h : ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, dist (f (u * x)) (f x) < ε) : Continuous f :=
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  ((uniformContinuous_rightUniformSpace_iff f).2 h).continuous

end UniformContinuous

section UCB

variable (G) in
/-- The real bounded continuous functions `f` on `G` such that `f (u * x)` is uniformly close to
`f x` for all `u` near `1`, as a subalgebra of `G →ᵇ ℝ`. -/
def ucb : Subalgebra ℝ (G →ᵇ ℝ) where
  carrier := {f | ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, |f (u * x) - f x| < ε}
  mul_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← Real.dist_eq,
      ← BoundedContinuousFunction.tendsto_compContinuous_mulLeft_iff] at hf hg ⊢
    exact hf.mul hg
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← Real.dist_eq,
      ← BoundedContinuousFunction.tendsto_compContinuous_mulLeft_iff] at hf hg ⊢
    exact hf.add hg
  algebraMap_mem' c := by
    simp only [Set.mem_ofPred_eq, ← Real.dist_eq,
      ← BoundedContinuousFunction.tendsto_compContinuous_mulLeft_iff]
    exact tendsto_const_nhds

variable (G) in
/-- The real Banach algebra of bounded functions on `G` that are uniformly continuous under small
left multiplication, with the supremum norm, algebra operations and order of `G →ᵇ ℝ`. -/
abbrev UCB : Type _ := ucb G

/-- The defining condition of `ucb G`. -/
theorem mem_ucb_iff {f : G →ᵇ ℝ} :
    f ∈ ucb G ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, |f (u * x) - f x| < ε :=
  Iff.rfl

/-- Membership in `ucb G` says that `u ↦ f (u * ·)` tends to `f` in supremum norm as `u → 1`. -/
theorem mem_ucb_iff_tendsto {f : G →ᵇ ℝ} :
    f ∈ ucb G ↔ Tendsto (fun u => f.compContinuous (ContinuousMap.mulLeft u)) (𝓝 1) (𝓝 f) := by
  simp only [mem_ucb_iff, ← Real.dist_eq,
    BoundedContinuousFunction.tendsto_compContinuous_mulLeft_iff]

/-- Membership in `ucb G` is uniform continuity for the right uniformity of `G`. -/
theorem mem_ucb_iff_uniformContinuous {f : G →ᵇ ℝ} :
    f ∈ ucb G ↔
      (letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
       UniformContinuous f) := by
  simp only [mem_ucb_iff, ← Real.dist_eq, uniformContinuous_rightUniformSpace_iff]

/-- `ucb G` is closed in `G →ᵇ ℝ`: a uniform limit of functions in `ucb G` lies in `ucb G`. -/
theorem isClosed_ucb : IsClosed (ucb G : Set (G →ᵇ ℝ)) := by
  refine isClosed_of_closure_subset fun f hf ε hε => ?_
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.1 hf (ε / 3) (by positivity)
  filter_upwards [hg (ε / 3) (by positivity)] with u hu x
  simp only [← Real.dist_eq] at hu ⊢
  calc dist (f (u * x)) (f x)
      ≤ dist (f (u * x)) (g (u * x)) + dist (g (u * x)) (g x) + dist (g x) (f x) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact (BoundedContinuousFunction.dist_coe_le_dist _).trans_lt hfg
        · exact hu x
        · exact (BoundedContinuousFunction.dist_coe_le_dist _).trans_lt (by rwa [dist_comm])
    _ = ε := by ring

/-- `UCB G` is a real Banach space. -/
instance : CompleteSpace (UCB G) :=
  isClosed_ucb.completeSpace_coe

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

end UCB

end UCB

section Translate

/-- Left translation by `g` preserves `ucb G`: since conjugation by `g` is continuous, small left
multiplication commutes past `g` up to a small left multiplication. -/
theorem compContinuous_mulLeft_mem_ucb (g : G) {f : G →ᵇ ℝ} (hf : f ∈ ucb G) :
    f.compContinuous (ContinuousMap.mulLeft g) ∈ ucb G := by
  have hconj : Tendsto (fun u => g * u * g⁻¹) (𝓝 1) (𝓝 1) :=
    (IsTopologicalGroup.continuous_conj g).tendsto' 1 1 (by simp)
  intro ε hε
  filter_upwards [hconj.eventually (hf ε hε)] with u hu x
  simpa [mul_assoc] using hu (g * x)

/-- Right translation by `g` preserves `ucb G`. -/
theorem compContinuous_mulRight_mem_ucb (g : G) {f : G →ᵇ ℝ} (hf : f ∈ ucb G) :
    f.compContinuous (ContinuousMap.mulRight g) ∈ ucb G := by
  intro ε hε
  filter_upwards [hf ε hε] with u hu x
  simpa [mul_assoc] using hu (x * g)

namespace UCB

/-- Precomposition with mutually inverse continuous self-maps of `G` which preserve `ucb G`, as a
linear isometry equivalence of `UCB G`. -/
private def compEquiv (φ ψ : C(G, G)) (hφψ : ∀ x, φ (ψ x) = x) (hψφ : ∀ x, ψ (φ x) = x)
    (hφ : ∀ f ∈ ucb G, f.compContinuous φ ∈ ucb G) (hψ : ∀ f ∈ ucb G, f.compContinuous ψ ∈ ucb G) :
    UCB G ≃ₗᵢ[ℝ] UCB G where
  toFun f := ⟨(f : G →ᵇ ℝ).compContinuous φ, hφ _ f.2⟩
  invFun f := ⟨(f : G →ᵇ ℝ).compContinuous ψ, hψ _ f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := UCB.ext fun x => by simp [hφψ]
  right_inv f := UCB.ext fun x => by simp [hψφ]
  norm_map' f := by
    simp only [LinearEquiv.coe_mk, AddSubgroupClass.coe_norm]
    refine le_antisymm (BoundedContinuousFunction.norm_compContinuous_le _ _) ?_
    calc ‖(f : G →ᵇ ℝ)‖
        = ‖((f : G →ᵇ ℝ).compContinuous φ).compContinuous ψ‖ := by
          congr 1
          ext x
          simp [hφψ]
      _ ≤ ‖(f : G →ᵇ ℝ).compContinuous φ‖ := BoundedContinuousFunction.norm_compContinuous_le _ _

private theorem coe_compEquiv (φ ψ : C(G, G)) (hφψ : ∀ x, φ (ψ x) = x) (hψφ : ∀ x, ψ (φ x) = x)
    (hφ : ∀ f ∈ ucb G, f.compContinuous φ ∈ ucb G) (hψ : ∀ f ∈ ucb G, f.compContinuous ψ ∈ ucb G)
    (f : UCB G) : (compEquiv φ ψ hφψ hψφ hφ hψ f : G →ᵇ ℝ) = (f : G →ᵇ ℝ).compContinuous φ :=
  rfl

/-- Left translation `L_g f = f (g⁻¹ * ·)` on `UCB G`, as a monoid homomorphism from `G` to the
group of linear isometry equivalences of `UCB G`, so that `L_(g * h) = L_g ∘ L_h`. -/
def translate : G →* (UCB G ≃ₗᵢ[ℝ] UCB G) where
  toFun g := compEquiv (.mulLeft g⁻¹) (.mulLeft g) (by simp) (by simp)
    (fun _ => compContinuous_mulLeft_mem_ucb g⁻¹) (fun _ => compContinuous_mulLeft_mem_ucb g)
  map_one' := by
    ext f x
    simp [coe_compEquiv]
  map_mul' g h := by
    ext f x
    simp [coe_compEquiv, mul_assoc]

theorem coe_translate (g : G) (f : UCB G) :
    (translate g f : G →ᵇ ℝ) = (f : G →ᵇ ℝ).compContinuous (.mulLeft g⁻¹) :=
  (rfl)

@[simp]
theorem translate_apply (g : G) (f : UCB G) (x : G) :
    (translate g f : G →ᵇ ℝ) x = (f : G →ᵇ ℝ) (g⁻¹ * x) :=
  (rfl)

/-- Composition of left translations: `L_g (L_h f) = L_(g * h) f`. -/
@[simp]
theorem translate_translate (g h : G) (f : UCB G) :
    translate g (translate h f) = translate (g * h) f := by
  ext x
  simp

/-- The inverse of `L_g` is `L_(g⁻¹)`. -/
@[simp]
theorem translate_symm (g : G) : (translate g).symm = translate g⁻¹ := by
  ext f x
  simp

/-- Left translation preserves and reflects the pointwise order. -/
@[simp]
theorem translate_le_translate_iff (g : G) {f f' : UCB G} :
    translate g f ≤ translate g f' ↔ f ≤ f' := by
  simp only [le_def, translate_apply]
  exact ⟨fun h x => by simpa using h (g * x), fun h x => h _⟩

@[simp]
theorem translate_nonneg_iff (g : G) {f : UCB G} : 0 ≤ translate g f ↔ 0 ≤ f := by
  simp only [le_def, translate_apply, ZeroMemClass.coe_zero, BoundedContinuousFunction.coe_zero,
    Pi.zero_apply]
  exact ⟨fun h x => by simpa using h (g * x), fun h x => h _⟩

/-- Left translation fixes constant functions. -/
@[simp]
theorem translate_algebraMap (g : G) (c : ℝ) :
    translate g (algebraMap ℝ (UCB G) c) = algebraMap ℝ (UCB G) c := by
  ext x
  simp

@[simp]
theorem translate_apply_one (g : G) : translate g (1 : UCB G) = 1 := by
  simpa using translate_algebraMap g 1

/-- The left-translation orbit `u ↦ L_u f` of `f ∈ UCB G` tends to `f` in supremum norm as
`u → 1`. -/
theorem tendsto_translate_nhds_one (f : UCB G) :
    Tendsto (fun u => translate u f) (𝓝 1) (𝓝 f) := by
  refine tendsto_subtype_rng.2 ?_
  simp only [coe_translate]
  exact (mem_ucb_iff_tendsto.1 f.2).comp (continuous_inv.tendsto' 1 1 inv_one)

/-- The left-translation orbit `g ↦ L_g f` of `f ∈ UCB G` is continuous in supremum norm. -/
theorem continuous_translate_apply (f : UCB G) : Continuous fun g => translate g f := by
  refine continuous_iff_continuousAt.2 fun h => ?_
  have := ((translate h).continuous.tendsto f).comp <| (tendsto_translate_nhds_one f).comp <|
    (continuous_const_mul h⁻¹).tendsto' h 1 (inv_mul_cancel h)
  simpa [ContinuousAt, Function.comp_def] using this

/-- Right translation `R_g f = f (· * g)` on `UCB G`, as a monoid homomorphism from `G` to the
group of linear isometry equivalences of `UCB G`, so that `R_(g * h) = R_g ∘ R_h`. -/
def rightTranslate : G →* (UCB G ≃ₗᵢ[ℝ] UCB G) where
  toFun g := compEquiv (.mulRight g) (.mulRight g⁻¹) (by simp) (by simp)
    (fun _ => compContinuous_mulRight_mem_ucb g) (fun _ => compContinuous_mulRight_mem_ucb g⁻¹)
  map_one' := by
    ext f x
    simp [coe_compEquiv]
  map_mul' g h := by
    ext f x
    simp [coe_compEquiv, mul_assoc]

@[simp]
theorem rightTranslate_apply (g : G) (f : UCB G) (x : G) :
    (rightTranslate g f : G →ᵇ ℝ) x = (f : G →ᵇ ℝ) (x * g) :=
  (rfl)

/-- Composition of right translations: `R_g (R_h f) = R_(g * h) f`. -/
@[simp]
theorem rightTranslate_rightTranslate (g h : G) (f : UCB G) :
    rightTranslate g (rightTranslate h f) = rightTranslate (g * h) f := by
  ext x
  simp [mul_assoc]

/-- The inverse of `R_g` is `R_(g⁻¹)`. -/
@[simp]
theorem rightTranslate_symm (g : G) : (rightTranslate g).symm = rightTranslate g⁻¹ := by
  ext f x
  simp

/-- Left and right translations of `UCB G` commute. -/
theorem translate_rightTranslate (g h : G) (f : UCB G) :
    translate g (rightTranslate h f) = rightTranslate h (translate g f) := by
  ext x
  simp [mul_assoc]

/-- Left and right translations of `UCB G` commute in the group of linear isometry
equivalences. -/
theorem commute_translate_rightTranslate (g h : G) : Commute (translate g) (rightTranslate h) :=
  LinearIsometryEquiv.ext fun f => translate_rightTranslate g h f

end UCB

end Translate

end TauCeti

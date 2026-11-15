/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ContinuousMonoidHom.TypeTags
public import TauCeti.Topology.Algebra.Group.UCB.Discrete

/-!
# Bounded functions uniformly continuous under small left addition

For a topological additive group `G`, `TauCeti.addUcb G` is the subalgebra of real bounded
continuous functions `f` such that `f (u + x)` is uniformly close to `f x` for all `u` near `0`:

```text
∀ ε > 0,  ∀ᶠ u in 𝓝 0,  ∀ x,  |f (u + x) - f x| < ε.
```

`TauCeti.AddUCB G` is the corresponding carrier type. It is a real Banach algebra and lattice for
the supremum norm, unital algebra operations, and pointwise order of `G →ᵇ ℝ`. Left translation
`(L_g f)(x) = f (-g + x)` and right translation `(R_g f)(x) = f (x + g)` act on `AddUCB G` by
linear isometries, and the orbit map `g ↦ L_g f` is norm-continuous.

Because `LinearIsometryEquiv` is a multiplicative group under composition (with no `AddGroup`
structure) and Mathlib's `BoundedContinuousFunction` operations register the domain type as the
target of `@[to_additive]`, `AddUCB G` is stated natively for additive groups and bridged to
`TauCeti.UCB (Multiplicative G)` (and conversely from `AddUCB (Additive H)` to `UCB H`) by
precomposition with `Multiplicative.ofAdd` and `Additive.ofMul`. These identifications preserve the
algebra structure, supremum norm, pointwise order, translations, and functorial pullbacks, so
analytic properties transfer between additive and multiplicative groups without duplicating proofs.

## Main definitions

* `TauCeti.addUcbSubalgebra 𝕜 G`: the subalgebra of `G →ᵇ 𝕜` of bounded functions `f` such that
  `f (u + x)` is uniformly close to `f x` for `u` near `0`.
* `TauCeti.addUcb G`, `TauCeti.AddUCB G`: the real subalgebra (`𝕜 = ℝ`) and its carrier type.
* `TauCeti.UCB.ofMultiplicative G`, `TauCeti.UCB.ofMultiplicativeₗᵢ G`: the canonical algebra and
  linear isometry equivalences `UCB (Multiplicative G) ≃ AddUCB G`.
* `TauCeti.AddUCB.ofAdditive H`, `TauCeti.AddUCB.ofAdditiveₗᵢ H`: the canonical algebra and linear
  isometry equivalences `AddUCB (Additive H) ≃ UCB H`.
* `TauCeti.AddUCB.leftTranslation`, `TauCeti.AddUCB.rightTranslation`: left and right translations
  `(L_g f)(x) = f (-g + x)` and `(R_g f)(x) = f (x + g)` as linear isometry equivalences of
  `AddUCB G`.
* `TauCeti.AddUCB.compRightAlgHom φ`: pullback `f ↦ f ∘ φ` along `φ : G →ₜ+ A`.
* `TauCeti.AddUCB.discreteAlgEquiv G`: identification `AddUCB G ≃ₐ[ℝ] (G →ᵇ ℝ)` for discrete `G`.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix A.3 and G.1.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction

namespace TauCeti

section AddUCB

variable {𝕜 G : Type*} [NormedField 𝕜] [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- A function on a topological additive group is uniformly continuous for the right uniformity
exactly when `f (u + x)` is uniformly close to `f x` for all `u` near `0`. -/
theorem uniformContinuous_addRightUniformSpace_iff {β : Type*} [PseudoMetricSpace β] (f : G → β) :
    (letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
     UniformContinuous f) ↔
      ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : G), ∀ x, dist (f (u + x)) (f x) < ε := by
  let : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  rw [UniformContinuous, uniformity_eq_comap_nhds_zero',
    ((𝓝 (0 : G)).basis_sets.comap _).tendsto_iff Metric.uniformity_basis_dist]
  refine forall₂_congr fun ε _ => ⟨fun ⟨U, hU, h⟩ => ?_, fun h => ⟨_, h, fun p hp => ?_⟩⟩
  · filter_upwards [hU] with u hu x
    rw [dist_comm]
    exact h (x, u + x) (by simpa using hu)
  · simpa [dist_comm] using hp p.1

private theorem addUcb_tendsto {f : G →ᵇ 𝕜} :
    (∀ ε > 0, ∀ᶠ u in 𝓝 (0 : G), ∀ x, ‖f (u + x) - f x‖ < ε) ↔
      Tendsto (fun u => f.compContinuous (ContinuousMap.addLeft u)) (𝓝 0) (𝓝 f) := by
  simp only [← dist_eq_norm, BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff]

variable (𝕜 G) in
/-- The bounded continuous functions `f : G →ᵇ 𝕜` on a topological additive group such that
`f (u + x)` is uniformly close to `f x` for all `u` near `0`, as a subalgebra of `G →ᵇ 𝕜`. -/
def addUcbSubalgebra : Subalgebra 𝕜 (G →ᵇ 𝕜) where
  carrier := {f | ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : G), ∀ x, ‖f (u + x) - f x‖ < ε}
  mul_mem' hf hg := addUcb_tendsto.2 ((addUcb_tendsto.1 hf).mul (addUcb_tendsto.1 hg))
  add_mem' hf hg := addUcb_tendsto.2 ((addUcb_tendsto.1 hf).add (addUcb_tendsto.1 hg))
  algebraMap_mem' _ := addUcb_tendsto.2 tendsto_const_nhds

/-- The defining condition of `addUcbSubalgebra 𝕜 G`. -/
theorem mem_addUcbSubalgebra_iff {f : G →ᵇ 𝕜} :
    f ∈ addUcbSubalgebra 𝕜 G ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : G), ∀ x, ‖f (u + x) - f x‖ < ε :=
  Iff.rfl

/-- Membership in `addUcbSubalgebra 𝕜 G` says that `u ↦ f (u + ·)` tends to `f` in supremum norm as
`u → 0`. -/
theorem mem_addUcbSubalgebra_iff_tendsto {f : G →ᵇ 𝕜} :
    f ∈ addUcbSubalgebra 𝕜 G ↔
      Tendsto (fun u => f.compContinuous (ContinuousMap.addLeft u)) (𝓝 0) (𝓝 f) :=
  addUcb_tendsto

/-- Precomposition with `Multiplicative.toAdd` identifies `addUcbSubalgebra 𝕜 G` with
`ucbSubalgebra 𝕜 (Multiplicative G)`. -/
theorem mem_addUcbSubalgebra_iff_multiplicative {f : G →ᵇ 𝕜} :
    f ∈ addUcbSubalgebra 𝕜 G ↔
      f.compContinuous ⟨Multiplicative.toAdd, continuous_toAdd⟩ ∈
        ucbSubalgebra 𝕜 (Multiplicative G) := by
  have h1 : (1 : Multiplicative G) = Multiplicative.ofAdd 0 := rfl
  simp only [mem_addUcbSubalgebra_iff, mem_ucbSubalgebra_iff, h1, nhds_ofAdd, eventually_map,
    Multiplicative.forall, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    toAdd_mul, toAdd_ofAdd]

/-- Precomposition with `Multiplicative.ofAdd` identifies `ucbSubalgebra 𝕜 (Multiplicative G)` with
`addUcbSubalgebra 𝕜 G`. -/
theorem mem_ucbSubalgebra_multiplicative_iff {f : Multiplicative G →ᵇ 𝕜} :
    f ∈ ucbSubalgebra 𝕜 (Multiplicative G) ↔
      f.compContinuous ⟨Multiplicative.ofAdd, continuous_ofAdd⟩ ∈ addUcbSubalgebra 𝕜 G := by
  rw [mem_addUcbSubalgebra_iff_multiplicative]
  exact Iff.of_eq (congrArg (· ∈ _) (BoundedContinuousFunction.ext fun _ => rfl))

/-- A bounded continuous function with compact support belongs to `addUcbSubalgebra 𝕜 G`. -/
theorem mem_addUcbSubalgebra_of_hasCompactSupport {f : G →ᵇ 𝕜} (hf : HasCompactSupport f) :
    f ∈ addUcbSubalgebra 𝕜 G := by
  let : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  simpa only [mem_addUcbSubalgebra_iff, dist_eq_norm] using
    (uniformContinuous_addRightUniformSpace_iff f).1
      (hf.uniformContinuous_of_continuous f.continuous)

variable (G) in
/-- The real bounded continuous functions `f` on `G` such that `f (u + x)` is uniformly close to
`f x` for all `u` near `0`, as a subalgebra of `G →ᵇ ℝ`. -/
@[expose] def addUcb : Subalgebra ℝ (G →ᵇ ℝ) := addUcbSubalgebra ℝ G

variable (G) in
/-- The real Banach algebra of bounded functions on an additive topological group `G` that are
uniformly continuous under small left addition, with the supremum norm, algebra operations, and
pointwise order of `G →ᵇ ℝ`. -/
abbrev AddUCB : Type _ := addUcb G

theorem addUcb_eq_addUcbSubalgebra (G : Type*) [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] : addUcb G = addUcbSubalgebra ℝ G := rfl

/-- The defining condition of `addUcb G`. -/
theorem mem_addUcb_iff {f : G →ᵇ ℝ} :
    f ∈ addUcb G ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : G), ∀ x, |f (u + x) - f x| < ε := by
  simp only [addUcb_eq_addUcbSubalgebra, mem_addUcbSubalgebra_iff, Real.norm_eq_abs]

/-- Membership in `addUcb G` says that `u ↦ f (u + ·)` tends to `f` in supremum norm as `u → 0`. -/
theorem mem_addUcb_iff_tendsto {f : G →ᵇ ℝ} :
    f ∈ addUcb G ↔ Tendsto (fun u => f.compContinuous (ContinuousMap.addLeft u)) (𝓝 0) (𝓝 f) := by
  rw [addUcb_eq_addUcbSubalgebra, mem_addUcbSubalgebra_iff_tendsto]

/-- Membership in `addUcb G` is uniform continuity for the right uniformity of `G`. -/
theorem mem_addUcb_iff_uniformContinuous {f : G →ᵇ ℝ} :
    f ∈ addUcb G ↔
      (letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
       UniformContinuous f) := by
  simp only [mem_addUcb_iff, ← Real.dist_eq, uniformContinuous_addRightUniformSpace_iff]

theorem mem_addUcb_of_hasCompactSupport {f : G →ᵇ ℝ} (hf : HasCompactSupport f) : f ∈ addUcb G :=
  mem_addUcbSubalgebra_of_hasCompactSupport hf

/-- `addUcb G` is closed in `G →ᵇ ℝ`: a uniform limit of functions in `addUcb G` lies in
`addUcb G`. -/
theorem isClosed_addUcb : IsClosed (addUcb G : Set (G →ᵇ ℝ)) := by
  have h : (addUcb G : Set (G →ᵇ ℝ)) =
      (fun f : G →ᵇ ℝ => f.compContinuous ⟨Multiplicative.toAdd, continuous_toAdd⟩) ⁻¹'
        (ucb (Multiplicative G) : Set (Multiplicative G →ᵇ ℝ)) :=
    Set.ext fun _ => mem_addUcbSubalgebra_iff_multiplicative
  rw [h]
  refine isClosed_ucb.preimage (LipschitzWith.of_dist_le_mul (K := 1) fun f g => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  exact (f - g).norm_compContinuous_le ⟨Multiplicative.toAdd, continuous_toAdd⟩

instance : NormedAddCommGroup (AddUCB G) := inferInstance
instance : CompleteSpace (AddUCB G) := isClosed_addUcb.completeSpace_coe
instance : NormSMulClass ℝ (AddUCB G) := ⟨fun c f => norm_smul c (f : G →ᵇ ℝ)⟩

@[simp] theorem const_mem_addUcb (c : ℝ) : BoundedContinuousFunction.const G c ∈ addUcb G :=
  fun _ hε => .of_forall fun _ _ => by simpa using hε

/-- `addUcb G` is closed under the pointwise maximum, minimum, and absolute value. -/
theorem sup_mem_addUcb {f g : G →ᵇ ℝ} (hf : f ∈ addUcb G) (hg : g ∈ addUcb G) :
    f ⊔ g ∈ addUcb G :=
  mem_addUcb_iff_tendsto.2 ((mem_addUcb_iff_tendsto.1 hf).sup_nhds (mem_addUcb_iff_tendsto.1 hg))

theorem inf_mem_addUcb {f g : G →ᵇ ℝ} (hf : f ∈ addUcb G) (hg : g ∈ addUcb G) :
    f ⊓ g ∈ addUcb G :=
  mem_addUcb_iff_tendsto.2 ((mem_addUcb_iff_tendsto.1 hf).inf_nhds (mem_addUcb_iff_tendsto.1 hg))

theorem abs_mem_addUcb {f : G →ᵇ ℝ} (hf : f ∈ addUcb G) : |f| ∈ addUcb G :=
  sup_mem_addUcb hf (neg_mem hf)

instance : Lattice (AddUCB G) :=
  Subtype.lattice (fun _ _ => sup_mem_addUcb) (fun _ _ => inf_mem_addUcb)

instance : HasSolidNorm (AddUCB G) where
  solid _ _ h := HasSolidNorm.solid (α := G →ᵇ ℝ) h

/-- Left and right translates of functions in `addUcbSubalgebra 𝕜 G` stay in
`addUcbSubalgebra 𝕜 G`. -/
theorem compContinuous_addLeft_mem_addUcbSubalgebra {f : G →ᵇ 𝕜} (hf : f ∈ addUcbSubalgebra 𝕜 G)
    (g : G) : f.compContinuous (ContinuousMap.addLeft g) ∈ addUcbSubalgebra 𝕜 G := by
  rw [mem_addUcbSubalgebra_iff_multiplicative] at hf ⊢
  exact compContinuous_mulLeft_mem_ucbSubalgebra hf (Multiplicative.ofAdd g)

theorem compContinuous_addRight_mem_addUcbSubalgebra {f : G →ᵇ 𝕜} (hf : f ∈ addUcbSubalgebra 𝕜 G)
    (g : G) : f.compContinuous (ContinuousMap.addRight g) ∈ addUcbSubalgebra 𝕜 G := by
  rw [mem_addUcbSubalgebra_iff_multiplicative] at hf ⊢
  exact compContinuous_mulRight_mem_ucbSubalgebra hf (Multiplicative.ofAdd g)

theorem compContinuous_addLeft_mem_addUcb {f : G →ᵇ ℝ} (hf : f ∈ addUcb G) (g : G) :
    f.compContinuous (ContinuousMap.addLeft g) ∈ addUcb G :=
  compContinuous_addLeft_mem_addUcbSubalgebra hf g

theorem compContinuous_addRight_mem_addUcb {f : G →ᵇ ℝ} (hf : f ∈ addUcb G) (g : G) :
    f.compContinuous (ContinuousMap.addRight g) ∈ addUcb G :=
  compContinuous_addRight_mem_addUcbSubalgebra hf g

end AddUCB

namespace AddUCB

section Basic

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

@[simp, norm_cast] theorem coe_sup (f g : AddUCB G) :
    ((f ⊔ g : AddUCB G) : G →ᵇ ℝ) = (f : G →ᵇ ℝ) ⊔ (g : G →ᵇ ℝ) := rfl

@[simp, norm_cast] theorem coe_inf (f g : AddUCB G) :
    ((f ⊓ g : AddUCB G) : G →ᵇ ℝ) = (f : G →ᵇ ℝ) ⊓ (g : G →ᵇ ℝ) := rfl

@[simp, norm_cast] theorem coe_abs (f : AddUCB G) :
    ((|f| : AddUCB G) : G →ᵇ ℝ) = |(f : G →ᵇ ℝ)| := rfl

/-- Two elements of `AddUCB G` are equal when they agree at every point. -/
@[ext] theorem ext {f g : AddUCB G} (h : ∀ x, (f : G →ᵇ ℝ) x = (g : G →ᵇ ℝ) x) : f = g :=
  Subtype.ext (BoundedContinuousFunction.ext h)

theorem le_def {f g : AddUCB G} : f ≤ g ↔ ∀ x, (f : G →ᵇ ℝ) x ≤ (g : G →ᵇ ℝ) x := Iff.rfl

/-- Each value of an element of `AddUCB G` is bounded by its supremum norm. -/
theorem abs_apply_le_norm (f : AddUCB G) (x : G) : |(f : G →ᵇ ℝ) x| ≤ ‖f‖ :=
  (f : G →ᵇ ℝ).norm_coe_le_norm x

/-- Every element of `AddUCB G` lies below the constant function with value its supremum norm. -/
theorem le_norm_smul_one (f : AddUCB G) : f ≤ ‖f‖ • 1 :=
  le_def.2 fun x => by simpa using (f : G →ᵇ ℝ).apply_le_norm x

/-! ### Left and right translations -/

/-- Left translation `L_g`, where `(L_g f)(x) = f (-g + x)`, as a linear isometry equivalence of
`AddUCB G`. -/
def leftTranslation (g : G) : AddUCB G ≃ₗᵢ[ℝ] AddUCB G :=
  BoundedContinuousFunction.compContinuousₗᵢ (addUcb G)
    (ContinuousMap.addLeft (-g)) (ContinuousMap.addLeft g) (by simp) (by simp)
    (fun _ hf => compContinuous_addLeft_mem_addUcb hf _)
    (fun _ hf => compContinuous_addLeft_mem_addUcb hf _)

/-- Right translation `R_g`, where `(R_g f)(x) = f (x + g)`, as a linear isometry equivalence of
`AddUCB G`. -/
def rightTranslation (g : G) : AddUCB G ≃ₗᵢ[ℝ] AddUCB G :=
  BoundedContinuousFunction.compContinuousₗᵢ (addUcb G)
    (ContinuousMap.addRight g) (ContinuousMap.addRight (-g)) (by simp) (by simp)
    (fun _ hf => compContinuous_addRight_mem_addUcb hf _)
    (fun _ hf => compContinuous_addRight_mem_addUcb hf _)

/-- The left translate `L_g f` is the precomposition of `f` with `x ↦ -g + x`. -/
theorem coe_leftTranslation (g : G) (f : AddUCB G) :
    (leftTranslation g f : G →ᵇ ℝ) = (f : G →ᵇ ℝ).compContinuous (ContinuousMap.addLeft (-g)) :=
  BoundedContinuousFunction.compContinuousₗᵢ_apply ..

/-- The right translate `R_g f` is the precomposition of `f` with `x ↦ x + g`. -/
theorem coe_rightTranslation (g : G) (f : AddUCB G) :
    (rightTranslation g f : G →ᵇ ℝ) = (f : G →ᵇ ℝ).compContinuous (ContinuousMap.addRight g) :=
  BoundedContinuousFunction.compContinuousₗᵢ_apply ..

@[simp] theorem leftTranslation_apply (g : G) (f : AddUCB G) (x : G) :
    (leftTranslation g f : G →ᵇ ℝ) x = (f : G →ᵇ ℝ) (-g + x) :=
  DFunLike.congr_fun (coe_leftTranslation g f) x

@[simp] theorem rightTranslation_apply (g : G) (f : AddUCB G) (x : G) :
    (rightTranslation g f : G →ᵇ ℝ) x = (f : G →ᵇ ℝ) (x + g) :=
  DFunLike.congr_fun (coe_rightTranslation g f) x

@[simp] theorem leftTranslation_zero :
    leftTranslation (0 : G) = LinearIsometryEquiv.refl ℝ (AddUCB G) :=
  LinearIsometryEquiv.ext fun _ => ext fun _ => by simp

theorem leftTranslation_add (g h : G) :
    leftTranslation (g + h) = (leftTranslation h).trans (leftTranslation g) :=
  LinearIsometryEquiv.ext fun _ => ext fun _ => by simp [add_assoc]

theorem leftTranslation_add_apply (g h : G) (f : AddUCB G) :
    leftTranslation (g + h) f = leftTranslation g (leftTranslation h f) := by
  rw [leftTranslation_add, LinearIsometryEquiv.trans_apply]

@[simp] theorem leftTranslation_symm (g : G) : (leftTranslation g).symm = leftTranslation (-g) :=
  LinearIsometryEquiv.ext fun _ => ext fun _ => by simp [leftTranslation]

@[simp] theorem rightTranslation_zero :
    rightTranslation (0 : G) = LinearIsometryEquiv.refl ℝ (AddUCB G) :=
  LinearIsometryEquiv.ext fun _ => ext fun _ => by simp

theorem rightTranslation_add (g h : G) :
    rightTranslation (g + h) = (rightTranslation h).trans (rightTranslation g) :=
  LinearIsometryEquiv.ext fun _ => ext fun _ => by simp [add_assoc]

theorem rightTranslation_add_apply (g h : G) (f : AddUCB G) :
    rightTranslation (g + h) f = rightTranslation g (rightTranslation h f) := by
  rw [rightTranslation_add, LinearIsometryEquiv.trans_apply]

@[simp] theorem rightTranslation_symm (g : G) : (rightTranslation g).symm = rightTranslation (-g) :=
  LinearIsometryEquiv.ext fun _ => ext fun _ => by simp [rightTranslation]

@[simp] theorem leftTranslation_le_leftTranslation_iff {g : G} {f f' : AddUCB G} :
    leftTranslation g f ≤ leftTranslation g f' ↔ f ≤ f' :=
  ⟨fun h => le_def.2 fun x => by simpa using le_def.1 h (g + x),
    fun h => le_def.2 fun _ => by simpa using le_def.1 h _⟩

@[simp] theorem leftTranslation_apply_one (g : G) : leftTranslation g 1 = 1 := ext fun _ => by simp

@[simp] theorem leftTranslation_apply_algebraMap (g : G) (c : ℝ) :
    leftTranslation g (algebraMap ℝ (AddUCB G) c) = algebraMap ℝ (AddUCB G) c := by
  simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem rightTranslation_le_rightTranslation_iff {g : G} {f f' : AddUCB G} :
    rightTranslation g f ≤ rightTranslation g f' ↔ f ≤ f' :=
  ⟨fun h => le_def.2 fun x => by simpa using le_def.1 h (x + -g),
    fun h => le_def.2 fun _ => by simpa using le_def.1 h _⟩

@[simp] theorem rightTranslation_apply_one (g : G) : rightTranslation g 1 = 1 :=
  ext fun _ => by simp

@[simp] theorem rightTranslation_apply_algebraMap (g : G) (c : ℝ) :
    rightTranslation g (algebraMap ℝ (AddUCB G) c) = algebraMap ℝ (AddUCB G) c := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- The left translates `L_u f` of `f ∈ AddUCB G` tend to `f` in supremum norm as `u → 0`. -/
theorem tendsto_leftTranslation_apply_nhds_zero (f : AddUCB G) :
    Tendsto (fun u : G => leftTranslation u f) (𝓝 0) (𝓝 f) := by
  simp only [tendsto_subtype_rng, coe_leftTranslation]
  exact (mem_addUcb_iff_tendsto.1 f.2).comp (by simpa using tendsto_neg (0 : G))

/-- The orbit map `g ↦ L_g f` of `f ∈ AddUCB G` is continuous for the supremum norm. -/
theorem continuous_leftTranslation_apply (f : AddUCB G) :
    Continuous fun g : G => leftTranslation g f :=
  continuous_iff_continuousAt.2 fun g =>
    (((leftTranslation g).continuous.tendsto f).comp <|
      (tendsto_leftTranslation_apply_nhds_zero f).comp <| by
        simpa using (continuous_const_add (-g)).tendsto g).congr fun _ => ext fun _ => by simp

/-- Left and right translations of `AddUCB G` commute. -/
theorem commute_leftTranslation_rightTranslation (g h : G) :
    Commute (leftTranslation g) (rightTranslation h) :=
  LinearIsometryEquiv.ext fun _ => ext fun _ => by simp [add_assoc]

/-- On a finite additive group, the sum of the left translates `L_g f` is the constant function
`∑ x, f x`. -/
theorem sum_leftTranslation [Fintype G] (f : AddUCB G) :
    ∑ g, leftTranslation g f = algebraMap ℝ (AddUCB G) (∑ x, (f : G →ᵇ ℝ) x) := by
  refine ext fun x => ?_
  simp only [AddSubmonoidClass.coe_finsetSum, FunLike.coe_sum, Finset.sum_apply,
    leftTranslation_apply, SubalgebraClass.coe_algebraMap,
    BoundedContinuousFunction.algebraMap_apply, smul_eq_mul, mul_one]
  exact Fintype.sum_equiv ((Equiv.neg G).trans (Equiv.addRight x)) _ _ fun _ => rfl

end Basic

/-! ### Pullback along continuous additive homomorphisms -/

section CompRight

variable {G A B : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- The pullback `x ↦ f (φ x)` of a function in `addUcb A` along `φ : G →ₜ+ A` lies in
`addUcb G`. -/
theorem _root_.TauCeti.compContinuous_mem_addUcb {f : A →ᵇ ℝ} (hf : f ∈ addUcb A) (φ : G →ₜ+ A) :
    f.compContinuous (φ : C(G, A)) ∈ addUcb G := by
  rw [addUcb_eq_addUcbSubalgebra, mem_addUcbSubalgebra_iff_multiplicative] at hf ⊢
  exact compContinuous_mem_ucb hf φ.toMultiplicative

/-- The pullback `f ↦ f ∘ φ` along a continuous additive homomorphism `φ : G →ₜ+ A`, as a unital
algebra homomorphism from `AddUCB A` to `AddUCB G`. -/
def compRightAlgHom (φ : G →ₜ+ A) : AddUCB A →ₐ[ℝ] AddUCB G :=
  { toFun f := ⟨(f : A →ᵇ ℝ).compContinuous (φ : C(G, A)), compContinuous_mem_addUcb f.2 φ⟩
    map_one' := rfl, map_mul' _ _ := rfl, map_zero' := rfl, map_add' _ _ := rfl
    commutes' _ := rfl }

@[simp] theorem compRightAlgHom_apply (φ : G →ₜ+ A) (f : AddUCB A) (x : G) :
    (compRightAlgHom φ f : G →ᵇ ℝ) x = (f : A →ᵇ ℝ) (φ x) := (rfl)

@[simp] theorem compRightAlgHom_id :
    compRightAlgHom (ContinuousAddMonoidHom.id G) = AlgHom.id ℝ (AddUCB G) := (rfl)

theorem compRightAlgHom_comp (ψ : A →ₜ+ B) (φ : G →ₜ+ A) :
    compRightAlgHom (ψ.comp φ) = (compRightAlgHom φ).comp (compRightAlgHom ψ) := (rfl)

theorem monotone_compRightAlgHom (φ : G →ₜ+ A) : Monotone (compRightAlgHom φ) :=
  fun _ _ h => le_def.2 fun x => le_def.1 h (φ x)

@[simp] theorem compRightAlgHom_le_compRightAlgHom_iff {φ : G →ₜ+ A} (hφ : Function.Surjective φ)
    {f f' : AddUCB A} : compRightAlgHom φ f ≤ compRightAlgHom φ f' ↔ f ≤ f' :=
  ⟨fun h => le_def.2 fun y => have ⟨x, hx⟩ := hφ y; hx ▸ le_def.1 h x,
    fun h => monotone_compRightAlgHom φ h⟩

theorem norm_compRightAlgHom_apply_le (φ : G →ₜ+ A) (f : AddUCB A) :
    ‖compRightAlgHom φ f‖ ≤ ‖f‖ :=
  (f : A →ᵇ ℝ).norm_compContinuous_le _

/-- Along a surjective continuous additive homomorphism, the pullback preserves the supremum
norm. -/
theorem norm_compRightAlgHom_apply {φ : G →ₜ+ A} (hφ : Function.Surjective φ) (f : AddUCB A) :
    ‖compRightAlgHom φ f‖ = ‖f‖ :=
  le_antisymm (norm_compRightAlgHom_apply_le φ f) <| by
    rw [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_norm]
    exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun y =>
      have ⟨x, hx⟩ := hφ y; hx ▸ (compRightAlgHom φ f : G →ᵇ ℝ).norm_coe_le_norm x

theorem compRightAlgHom_leftTranslation (φ : G →ₜ+ A) (g : G) (f : AddUCB A) :
    compRightAlgHom φ (leftTranslation (φ g) f) = leftTranslation g (compRightAlgHom φ f) :=
  ext fun _ => by simp

theorem compRightAlgHom_rightTranslation (φ : G →ₜ+ A) (g : G) (f : AddUCB A) :
    compRightAlgHom φ (rightTranslation (φ g) f) = rightTranslation g (compRightAlgHom φ f) :=
  ext fun _ => by simp

end CompRight

/-! ### Discrete additive groups -/

section Discrete

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [DiscreteTopology G]

/-- On a discrete additive group the `addUcb` subalgebra is the entire bounded-function algebra. -/
@[simp] theorem _root_.TauCeti.addUcb_eq_top : addUcb G = ⊤ :=
  Subalgebra.ext fun f => by simp [mem_addUcb_iff, nhds_discrete]

variable (G) in
/-- The canonical algebra equivalence from `AddUCB G` to all bounded functions on a discrete
additive group. -/
def discreteAlgEquiv : AddUCB G ≃ₐ[ℝ] (G →ᵇ ℝ) :=
  (Subalgebra.equivOfEq _ _ addUcb_eq_top).trans Subalgebra.topEquiv

@[simp] theorem discreteAlgEquiv_apply (f : AddUCB G) : discreteAlgEquiv G f = (f : G →ᵇ ℝ) := (rfl)

@[simp] theorem coe_discreteAlgEquiv_symm (f : G →ᵇ ℝ) :
    ((discreteAlgEquiv G).symm f : G →ᵇ ℝ) = f :=
  (discreteAlgEquiv G).apply_symm_apply f

@[simp] theorem discreteAlgEquiv_symm_compContinuous_addLeft (g : G) (f : G →ᵇ ℝ) :
    (discreteAlgEquiv G).symm (f.compContinuous (ContinuousMap.addLeft (-g))) =
      leftTranslation g ((discreteAlgEquiv G).symm f) :=
  (discreteAlgEquiv G).injective (by simp [coe_leftTranslation])

@[simp] theorem discreteAlgEquiv_symm_le_discreteAlgEquiv_symm_iff {f h : G →ᵇ ℝ} :
    (discreteAlgEquiv G).symm f ≤ (discreteAlgEquiv G).symm h ↔ f ≤ h := Iff.rfl

variable (G) in
/-- The discrete identification as a linear isometry equivalence for the supremum norm. -/
def discreteLinearIsometryEquiv : AddUCB G ≃ₗᵢ[ℝ] (G →ᵇ ℝ) :=
  { (discreteAlgEquiv G).toLinearEquiv with norm_map' _ := rfl }

@[simp] theorem discreteLinearIsometryEquiv_apply (f : AddUCB G) :
    discreteLinearIsometryEquiv G f = (f : G →ᵇ ℝ) := (rfl)

@[simp] theorem discreteLinearIsometryEquiv_symm_apply (f : G →ᵇ ℝ) :
    (discreteLinearIsometryEquiv G).symm f = (discreteAlgEquiv G).symm f := (rfl)

end Discrete

end AddUCB

/-! ### Equivalences with `UCB (Multiplicative G)` and `UCB H` -/

section TypeTags

namespace UCB

variable {G A : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

variable (G) in
/-- Precomposition with `Multiplicative.ofAdd` identifies `UCB (Multiplicative G)` with `AddUCB G`
as a real unital algebra. -/
def ofMultiplicative : UCB (Multiplicative G) ≃ₐ[ℝ] AddUCB G :=
  { toFun f := ⟨(f : Multiplicative G →ᵇ ℝ).compContinuous ⟨Multiplicative.ofAdd, continuous_ofAdd⟩,
      (mem_ucbSubalgebra_multiplicative_iff (𝕜 := ℝ)).1 f.2⟩
    invFun f := ⟨(f : G →ᵇ ℝ).compContinuous ⟨Multiplicative.toAdd, continuous_toAdd⟩,
      (mem_addUcbSubalgebra_iff_multiplicative (𝕜 := ℝ)).1 f.2⟩
    left_inv _ := ext fun _ => rfl, right_inv _ := AddUCB.ext fun _ => rfl
    map_mul' _ _ := rfl, map_add' _ _ := rfl, commutes' _ := rfl }

@[simp] theorem ofMultiplicative_apply (f : UCB (Multiplicative G)) (x : G) :
    (ofMultiplicative G f : G →ᵇ ℝ) x = (f : Multiplicative G →ᵇ ℝ) (.ofAdd x) := (rfl)

@[simp] theorem ofMultiplicative_symm_apply (f : AddUCB G) (x : Multiplicative G) :
    ((ofMultiplicative G).symm f : Multiplicative G →ᵇ ℝ) x = (f : G →ᵇ ℝ) x.toAdd := (rfl)

@[simp] theorem norm_ofMultiplicative (f : UCB (Multiplicative G)) :
    ‖(ofMultiplicative G f : G →ᵇ ℝ)‖ = ‖(f : Multiplicative G →ᵇ ℝ)‖ :=
  le_antisymm ((f : Multiplicative G →ᵇ ℝ).norm_compContinuous_le _)
    ((ofMultiplicative G f : G →ᵇ ℝ).norm_compContinuous_le
      ⟨Multiplicative.toAdd, continuous_toAdd⟩)

@[simp] theorem norm_ofMultiplicative_symm (f : AddUCB G) :
    ‖((ofMultiplicative G).symm f : Multiplicative G →ᵇ ℝ)‖ = ‖(f : G →ᵇ ℝ)‖ := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (norm_ofMultiplicative ((ofMultiplicative G).symm f)).symm

variable (G) in
/-- `UCB.ofMultiplicative` as a linear isometry equivalence for the supremum norm. -/
def ofMultiplicativeₗᵢ : UCB (Multiplicative G) ≃ₗᵢ[ℝ] AddUCB G :=
  { (ofMultiplicative G).toLinearEquiv with norm_map' _ := by simp }

@[simp] theorem ofMultiplicativeₗᵢ_apply (f : UCB (Multiplicative G)) :
    ofMultiplicativeₗᵢ G f = ofMultiplicative G f := (rfl)

@[simp] theorem ofMultiplicativeₗᵢ_symm_apply (f : AddUCB G) :
    (ofMultiplicativeₗᵢ G).symm f = (ofMultiplicative G).symm f := (rfl)

@[simp] theorem ofMultiplicative_le_ofMultiplicative_iff {f g : UCB (Multiplicative G)} :
    ofMultiplicative G f ≤ ofMultiplicative G g ↔ f ≤ g := by simp [AddUCB.le_def, UCB.le_def]

@[simp] theorem ofMultiplicative_symm_le_ofMultiplicative_symm_iff {f g : AddUCB G} :
    (ofMultiplicative G).symm f ≤ (ofMultiplicative G).symm g ↔ f ≤ g := by
  simp [AddUCB.le_def, UCB.le_def]

@[simp] theorem ofMultiplicative_leftTranslation (g : G) (f : UCB (Multiplicative G)) :
    ofMultiplicative G (leftTranslation (.ofAdd g) f) =
      AddUCB.leftTranslation g (ofMultiplicative G f) := AddUCB.ext fun _ => by simp

@[simp] theorem ofMultiplicative_symm_leftTranslation (g : G) (f : AddUCB G) :
    (ofMultiplicative G).symm (AddUCB.leftTranslation g f) =
      leftTranslation (.ofAdd g) ((ofMultiplicative G).symm f) := ext fun _ => by simp

@[simp] theorem ofMultiplicative_rightTranslation (g : G) (f : UCB (Multiplicative G)) :
    ofMultiplicative G (rightTranslation (.ofAdd g) f) =
      AddUCB.rightTranslation g (ofMultiplicative G f) := AddUCB.ext fun _ => by simp

@[simp] theorem ofMultiplicative_compRightAlgHom (φ : G →ₜ+ A) (f : UCB (Multiplicative A)) :
    ofMultiplicative G (compRightAlgHom φ.toMultiplicative f) =
      AddUCB.compRightAlgHom φ (ofMultiplicative A f) := AddUCB.ext fun _ => by simp

end UCB

namespace AddUCB

variable {H K : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- Precomposition with `Additive.toMul` sends `ucbSubalgebra 𝕜 H` to
`addUcbSubalgebra 𝕜 (Additive H)`. -/
theorem _root_.TauCeti.mem_ucbSubalgebra_iff_additive {𝕜 : Type*} [NormedField 𝕜] {f : H →ᵇ 𝕜} :
    f ∈ ucbSubalgebra 𝕜 H ↔
      f.compContinuous ⟨Additive.toMul, continuous_toMul⟩ ∈ addUcbSubalgebra 𝕜 (Additive H) := by
  have h0 : (0 : Additive H) = Additive.ofMul 1 := rfl
  simp only [mem_ucbSubalgebra_iff, mem_addUcbSubalgebra_iff, h0, nhds_ofMul, eventually_map,
    Additive.forall, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    toMul_add, toMul_ofMul]

/-- Precomposition with `Additive.ofMul` sends `addUcbSubalgebra 𝕜 (Additive H)` to
`ucbSubalgebra 𝕜 H`. -/
theorem _root_.TauCeti.mem_addUcbSubalgebra_additive_iff {𝕜 : Type*} [NormedField 𝕜]
    {f : Additive H →ᵇ 𝕜} :
    f ∈ addUcbSubalgebra 𝕜 (Additive H) ↔
      f.compContinuous ⟨Additive.ofMul, continuous_ofMul⟩ ∈ ucbSubalgebra 𝕜 H := by
  rw [mem_ucbSubalgebra_iff_additive]
  exact Iff.of_eq (congrArg (· ∈ _) (BoundedContinuousFunction.ext fun _ => rfl))

variable (H) in
/-- Precomposition with `Additive.ofMul` identifies `AddUCB (Additive H)` with `UCB H` as a real
unital algebra. -/
def ofAdditive : AddUCB (Additive H) ≃ₐ[ℝ] UCB H :=
  { toFun f := ⟨(f : Additive H →ᵇ ℝ).compContinuous ⟨Additive.ofMul, continuous_ofMul⟩,
      (mem_addUcbSubalgebra_additive_iff (𝕜 := ℝ)).1 f.2⟩
    invFun f := ⟨(f : H →ᵇ ℝ).compContinuous ⟨Additive.toMul, continuous_toMul⟩,
      (mem_ucbSubalgebra_iff_additive (𝕜 := ℝ)).1 f.2⟩
    left_inv _ := ext fun _ => rfl, right_inv _ := UCB.ext fun _ => rfl
    map_mul' _ _ := rfl, map_add' _ _ := rfl, commutes' _ := rfl }

@[simp] theorem ofAdditive_apply (f : AddUCB (Additive H)) (x : H) :
    (ofAdditive H f : H →ᵇ ℝ) x = (f : Additive H →ᵇ ℝ) (Additive.ofMul x) := (rfl)

@[simp] theorem ofAdditive_symm_apply (f : UCB H) (x : Additive H) :
    ((ofAdditive H).symm f : Additive H →ᵇ ℝ) x = (f : H →ᵇ ℝ) x.toMul := (rfl)

@[simp] theorem norm_ofAdditive (f : AddUCB (Additive H)) :
    ‖(ofAdditive H f : H →ᵇ ℝ)‖ = ‖(f : Additive H →ᵇ ℝ)‖ :=
  le_antisymm ((f : Additive H →ᵇ ℝ).norm_compContinuous_le _)
    ((ofAdditive H f : H →ᵇ ℝ).norm_compContinuous_le ⟨Additive.toMul, continuous_toMul⟩)

@[simp] theorem norm_ofAdditive_symm (f : UCB H) :
    ‖((ofAdditive H).symm f : Additive H →ᵇ ℝ)‖ = ‖(f : H →ᵇ ℝ)‖ := by
  simpa only [AlgEquiv.apply_symm_apply] using (norm_ofAdditive ((ofAdditive H).symm f)).symm

variable (H) in
/-- `AddUCB.ofAdditive` as a linear isometry equivalence for the supremum norm. -/
def ofAdditiveₗᵢ : AddUCB (Additive H) ≃ₗᵢ[ℝ] UCB H :=
  { (ofAdditive H).toLinearEquiv with norm_map' _ := by simp }

@[simp] theorem ofAdditiveₗᵢ_apply (f : AddUCB (Additive H)) :
    ofAdditiveₗᵢ H f = ofAdditive H f := (rfl)

@[simp] theorem ofAdditiveₗᵢ_symm_apply (f : UCB H) :
    (ofAdditiveₗᵢ H).symm f = (ofAdditive H).symm f := (rfl)

@[simp] theorem ofAdditive_le_ofAdditive_iff {f g : AddUCB (Additive H)} :
    ofAdditive H f ≤ ofAdditive H g ↔ f ≤ g := by simp [AddUCB.le_def, UCB.le_def]

@[simp] theorem ofAdditive_symm_le_ofAdditive_symm_iff {f g : UCB H} :
    (ofAdditive H).symm f ≤ (ofAdditive H).symm g ↔ f ≤ g := by simp [AddUCB.le_def, UCB.le_def]

@[simp] theorem ofAdditive_leftTranslation (h : H) (f : AddUCB (Additive H)) :
    ofAdditive H (leftTranslation (.ofMul h) f) = UCB.leftTranslation h (ofAdditive H f) :=
  UCB.ext fun _ => by simp

@[simp] theorem ofAdditive_symm_leftTranslation (h : H) (f : UCB H) :
    (ofAdditive H).symm (UCB.leftTranslation h f) =
      leftTranslation (.ofMul h) ((ofAdditive H).symm f) := ext fun _ => by simp

@[simp] theorem ofAdditive_compRightAlgHom (φ : H →ₜ* K) (f : AddUCB (Additive K)) :
    ofAdditive H (compRightAlgHom φ.toAdditive f) = UCB.compRightAlgHom φ (ofAdditive K f) :=
  UCB.ext fun _ => by simp

end AddUCB

end TypeTags

end TauCeti

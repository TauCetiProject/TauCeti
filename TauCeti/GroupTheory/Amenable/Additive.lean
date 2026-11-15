/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import TauCeti.GroupTheory.Amenable.Content
public import TauCeti.GroupTheory.Amenable.DirectedUnion
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
public import TauCeti.GroupTheory.Amenable.Extension
public import TauCeti.GroupTheory.Amenable.Linfty
public import TauCeti.GroupTheory.Amenable.Prod
public import TauCeti.Topology.Algebra.Group.UCB.Additive

/-!
# Amenable topological additive groups

A mean `m` on `TauCeti.AddUCB G` is a positive real linear functional with `m 1 = 1`; it is *left
invariant* when `m (L_g f) = m f` for every `g : G` and `f : AddUCB G`, where
`(L_g f)(x) = f (-g + x)`. A topological additive group `G` is *additively amenable*
(`TauCeti.AddAmenable G`) when `AddUCB G` carries a left-invariant mean.

Mathlib states commutative groups, modules, vector spaces, and `ℤ` additively (`AddCommGroup`,
`AddCircle`, `Fin n → ℤ`), so an additive amenability class lets typeclass search find amenability
on those types directly without wrapping them in `Multiplicative`. At the same time, the canonical
order-preserving isometric algebra equivalences `TauCeti.UCB.ofMultiplicative` and
`TauCeti.AddUCB.ofAdditive` induce homeomorphisms of weak-* mean spaces

```text
TauCeti.Mean.multiplicativeHomeomorph G : Mean (Multiplicative G) ≃ₜ AddMean G,
TauCeti.AddMean.additiveHomeomorph H    : AddMean (Additive H) ≃ₜ Mean H
```

that intertwine left invariance. Consequently `Amenable (Multiplicative G) ↔ AddAmenable G` and
`AddAmenable (Additive H) ↔ Amenable H`, and all permanence properties, compact and finite
instances, invariant-content characterizations, Reiter's condition, and Følner characterizations
transfer between `Amenable` and `AddAmenable` without duplicating analytic arguments.

## Main definitions

* `TauCeti.AddMean G`: a positive normalized linear functional on `AddUCB G`, equipped with the
  weak-* topology from `WeakDual ℝ (AddUCB G)`.
* `TauCeti.AddMean.IsLeftInvariant`: `m (L_g f) = m f` for all `g` and `f`.
* `TauCeti.AddMean.map φ`: pushforward of means along `φ : G →ₜ+ A`.
* `TauCeti.AddAmenable G`: `AddUCB G` carries a left-invariant mean.
* `TauCeti.Mean.multiplicativeEquiv G`, `TauCeti.Mean.multiplicativeHomeomorph G`: the canonical
  equivalence and weak-* homeomorphism `Mean (Multiplicative G) ≃ₜ AddMean G`.
* `TauCeti.AddMean.additiveEquiv H`, `TauCeti.AddMean.additiveHomeomorph H`: the canonical
  equivalence and weak-* homeomorphism `AddMean (Additive H) ≃ₜ Mean H`.

## Main results

* `TauCeti.amenable_multiplicative_iff`, `TauCeti.addAmenable_additive_iff`: equivalence of
  `Amenable` and `AddAmenable` across `Multiplicative` and `Additive`.
* `TauCeti.hasFoelnerSets_multiplicative_iff`, `TauCeti.hasAddFoelnerSets_additive_iff`:
  equivalence of `HasFoelnerSets` and `HasAddFoelnerSets` across `Multiplicative` and `Additive`.
* Permanence of `AddAmenable` under dense-range homomorphisms, coarser topologies, subgroups,
  extensions, binary and finite products, directed suprema of additive subgroups, and local finite
  generation (`AddAmenable.of_forall_fg`).
* Instances `AddAmenable.of_finite` and `AddAmenable.of_compactSpace`, and discrete equivalences
  with left-invariant finitely additive probabilities (`addAmenable_iff_exists_invariantContent`),
  Reiter's condition (`addAmenable_iff_exists_sum_tsum_abs_sub_lt`), and additive Følner sets
  (`addAmenable_iff_hasAddFoelnerSets`).

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.
* A. Garrido, *An introduction to amenable groups*, §§1–3.
-/

public section

noncomputable section

open Filter Finset Function MeasureTheory Set Topology
open scoped BoundedContinuousFunction BigOperators ENNReal Pointwise symmDiff

universe u v

namespace TauCeti

section AddMean

variable {G A B : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

variable (G) in
/-- A mean on `AddUCB G`: a positive real linear functional taking the value `1` at the constant
function `1`. -/
structure AddMean extends AddUCB G →ₚ[ℝ] ℝ where
  /-- A mean takes the value `1` at the constant function `1`. -/
  map_one' : toFun 1 = 1

namespace AddMean

instance : FunLike (AddMean G) (AddUCB G) ℝ where
  coe m := m.toFun
  coe_injective := by
    rintro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (AddMean G) ℝ (AddUCB G) ℝ where
  map_add m := map_add m.toPositiveLinearMap
  map_smulₛₗ m := map_smul m.toPositiveLinearMap

instance : OrderHomClass (AddMean G) (AddUCB G) ℝ where
  map_rel m _ _ h := OrderHomClass.mono m.toPositiveLinearMap h

/-- Two means on `AddUCB G` are equal when they agree on every function. -/
@[ext]
theorem ext {m n : AddMean G} (h : ∀ f, m f = n f) : m = n :=
  DFunLike.ext m n h

@[simp]
theorem coe_toPositiveLinearMap (m : AddMean G) : ⇑m.toPositiveLinearMap = ⇑m :=
  (rfl)

/-- A mean takes the value `1` at the constant function `1`. -/
@[simp]
theorem map_one (m : AddMean G) : m 1 = 1 :=
  m.map_one'

/-- Build a mean on `AddUCB G` from a linear functional nonnegative on nonnegative functions and
normalized at `1`. -/
def mk₀ (φ : AddUCB G →ₗ[ℝ] ℝ) (hφ : ∀ f, 0 ≤ f → 0 ≤ φ f) (h₁ : φ 1 = 1) : AddMean G :=
  { PositiveLinearMap.mk₀ φ hφ with map_one' := h₁ }

@[simp]
theorem mk₀_apply (φ : AddUCB G →ₗ[ℝ] ℝ) (hφ : ∀ f, 0 ≤ f → 0 ≤ φ f) (h₁ : φ 1 = 1)
    (f : AddUCB G) : mk₀ φ hφ h₁ f = φ f :=
  (rfl)

variable (m : AddMean G)

@[simp]
theorem map_algebraMap (c : ℝ) : m (algebraMap ℝ (AddUCB G) c) = c := by
  simp [Algebra.algebraMap_eq_smul_one]

theorem apply_le_of_forall_le {f : AddUCB G} {c : ℝ} (h : ∀ x, (f : G →ᵇ ℝ) x ≤ c) : m f ≤ c := by
  have hf : f ≤ algebraMap ℝ (AddUCB G) c := AddUCB.le_def.2 (by simpa)
  simpa using OrderHomClass.mono m hf

theorem le_apply_of_forall_le {f : AddUCB G} {c : ℝ} (h : ∀ x, c ≤ (f : G →ᵇ ℝ) x) : c ≤ m f := by
  have hf : algebraMap ℝ (AddUCB G) c ≤ f := AddUCB.le_def.2 (by simpa)
  simpa using OrderHomClass.mono m hf

theorem abs_apply_le_norm (f : AddUCB G) : |m f| ≤ ‖f‖ := by
  simpa using PositiveLinearMap.abs_apply_le_mul_norm m (AddUCB.le_norm_smul_one (G := G)) f

theorem lipschitzWith : LipschitzWith 1 m := by
  simpa using
    PositiveLinearMap.lipschitzWith_of_forall_le_norm_smul m (AddUCB.le_norm_smul_one (G := G))

instance : ContinuousLinearMapClass (AddMean G) ℝ (AddUCB G) ℝ where
  map_continuous m := m.lipschitzWith.continuous

/-- The continuous linear functional underlying an `AddMean G`. -/
def toContinuousLinearMap : AddUCB G →L[ℝ] ℝ where
  toLinearMap := m.toPositiveLinearMap.toLinearMap
  cont := map_continuous m

@[simp]
theorem coe_toContinuousLinearMap : ⇑m.toContinuousLinearMap = ⇑m :=
  (rfl)

theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : AddMean G → AddUCB G →L[ℝ] ℝ) :=
  fun _ _ h => ext fun f => DFunLike.congr_fun h f

@[simp]
theorem norm_toContinuousLinearMap : ‖m.toContinuousLinearMap‖ = 1 := by
  rw [m.toContinuousLinearMap.opNorm_eq_apply_of_monotone (OrderHomClass.mono m)
    AddUCB.le_norm_smul_one norm_one.le]
  simp

theorem mem_range_toContinuousLinearMap_iff {φ : AddUCB G →L[ℝ] ℝ} :
    φ ∈ Set.range (toContinuousLinearMap : AddMean G → AddUCB G →L[ℝ] ℝ) ↔
      (∀ f, 0 ≤ f → 0 ≤ φ f) ∧ φ 1 = 1 := by
  refine ⟨?_, fun ⟨hφ, h₁⟩ => ⟨mk₀ φ.toLinearMap hφ h₁, rfl⟩⟩
  rintro ⟨m, rfl⟩
  exact ⟨fun f hf => by simpa using map_nonneg m hf, by simp⟩

variable (G) in
/-- Evaluation at a point of `G` as a mean on `AddUCB G`. -/
def eval (x : G) : AddMean G :=
  mk₀ ((BoundedContinuousFunction.evalCLM ℝ x).toLinearMap ∘ₗ (addUcb G).val.toLinearMap)
    (fun _ hf => AddUCB.le_def.1 hf x) rfl

@[simp]
theorem eval_apply (x : G) (f : AddUCB G) : eval G x f = (f : G →ᵇ ℝ) x :=
  (rfl)

instance : Nonempty (AddMean G) :=
  ⟨eval G 0⟩

/-- The average `f ↦ 𝔼 x ∈ F, f x` over a finite nonempty set `F ⊆ G`, as a mean on `AddUCB G`. -/
def average (F : Finset G) (hF : F.Nonempty) : AddMean G :=
  mk₀
    { toFun f := 𝔼 x ∈ F, (f : G →ᵇ ℝ) x
      map_add' _ _ := by simp [Finset.expect_add_distrib]
      map_smul' _ _ := by simp [Finset.mul_expect] }
    (fun f hf => Finset.expect_nonneg fun x _ => AddUCB.le_def.1 hf x)
    (by simp [hF])

@[simp]
theorem average_apply {F : Finset G} (hF : F.Nonempty) (f : AddUCB G) :
    average F hF f = 𝔼 x ∈ F, (f : G →ᵇ ℝ) x :=
  mk₀_apply _ _ _ f

variable (G) in
/-- The normalized counting mean `f ↦ 𝔼 x, f x` on a finite topological additive group `G`. -/
def uniform [Finite G] : AddMean G :=
  letI := Fintype.ofFinite G
  average Finset.univ Finset.univ_nonempty

@[simp]
theorem uniform_apply [Fintype G] (f : AddUCB G) : uniform G f = 𝔼 x, (f : G →ᵇ ℝ) x := by
  simp only [uniform, average_apply]
  congr!

/-! ### Weak-* topology on `AddMean G` -/

/-- A mean on `AddUCB G`, as an element of `WeakDual ℝ (AddUCB G)`. -/
def toWeakDual (m : AddMean G) : WeakDual ℝ (AddUCB G) :=
  StrongDual.toWeakDual m.toContinuousLinearMap

@[simp]
theorem toWeakDual_apply (m : AddMean G) (f : AddUCB G) : m.toWeakDual f = m f := by
  simp [toWeakDual, StrongDual.toWeakDual_apply]

@[simp]
theorem toStrongDual_toWeakDual (m : AddMean G) :
    WeakDual.toStrongDual m.toWeakDual = m.toContinuousLinearMap :=
  StrongDual.toStrongDual_toWeakDual _

theorem toWeakDual_injective :
    Function.Injective (toWeakDual : AddMean G → WeakDual ℝ (AddUCB G)) :=
  StrongDual.toWeakDual.injective.comp toContinuousLinearMap_injective

theorem mem_range_toWeakDual_iff {φ : WeakDual ℝ (AddUCB G)} :
    φ ∈ Set.range (toWeakDual : AddMean G → WeakDual ℝ (AddUCB G)) ↔
      (∀ f, 0 ≤ f → 0 ≤ φ f) ∧ φ 1 = 1 := by
  have : φ ∈ Set.range (toWeakDual : AddMean G → WeakDual ℝ (AddUCB G)) ↔
      WeakDual.toStrongDual φ ∈
        Set.range (toContinuousLinearMap : AddMean G → AddUCB G →L[ℝ] ℝ) := by
    refine exists_congr fun m => ?_
    rw [← toStrongDual_toWeakDual, WeakDual.toStrongDual_inj]
  rw [this, mem_range_toContinuousLinearMap_iff]
  simp [WeakDual.toStrongDual_apply]

theorem isClosed_range_toWeakDual :
    IsClosed (Set.range (toWeakDual : AddMean G → WeakDual ℝ (AddUCB G))) := by
  have h : Set.range (toWeakDual : AddMean G → WeakDual ℝ (AddUCB G)) =
      (⋂ (f : AddUCB G) (_ : 0 ≤ f), {φ | 0 ≤ φ f}) ∩ {φ | φ 1 = 1} := by
    ext φ
    rw [mem_range_toWeakDual_iff]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [h]
  exact (isClosed_iInter fun f => isClosed_iInter fun _ =>
    isClosed_le continuous_const (WeakDual.eval_continuous (𝕜 := ℝ) f)).inter
      (isClosed_eq (WeakDual.eval_continuous (𝕜 := ℝ) (1 : AddUCB G)) continuous_const)

theorem isCompact_range_toWeakDual :
    IsCompact (Set.range (toWeakDual : AddMean G → WeakDual ℝ (AddUCB G))) :=
  (WeakDual.isCompact_closedBall 0 1).of_isClosed_subset isClosed_range_toWeakDual <| by
    rintro _ ⟨m, rfl⟩
    simp

/-- The weak-* topology on `AddMean G`, induced from `WeakDual ℝ (AddUCB G)`. -/
instance instTopologicalSpace : TopologicalSpace (AddMean G) :=
  .induced toWeakDual inferInstance

theorem isEmbedding_toWeakDual :
    IsEmbedding (toWeakDual : AddMean G → WeakDual ℝ (AddUCB G)) :=
  ⟨⟨rfl⟩, toWeakDual_injective⟩

instance : ContinuousEvalConst (AddMean G) (AddUCB G) ℝ where
  continuous_eval_const f := by
    simpa only [Function.comp_def, toWeakDual_apply] using
      (WeakDual.eval_continuous f).comp isEmbedding_toWeakDual.continuous

instance : T2Space (AddMean G) :=
  isEmbedding_toWeakDual.t2Space

instance : CompactSpace (AddMean G) :=
  isCompact_univ_iff.1 <| isEmbedding_toWeakDual.isCompact_iff.2 <| by
    simpa [Set.image_univ] using isCompact_range_toWeakDual

/-- Weak-* convergence in `AddMean G` is pointwise convergence on `AddUCB G`. -/
theorem tendsto_iff_forall_apply_tendsto {ι : Type*} {l : Filter ι} {ms : ι → AddMean G}
    {m : AddMean G} : Tendsto ms l (𝓝 m) ↔ ∀ f, Tendsto (fun i => ms i f) l (𝓝 (m f)) := by
  rw [isEmbedding_toWeakDual.isInducing.tendsto_nhds_iff,
    tendsto_iff_forall_eval_tendsto_topDualPairing]
  exact forall_congr' fun f => by simp only [← toWeakDual_apply]; rfl

/-! ### Left invariance and functorial pushforward -/

/-- A mean `m` on `AddUCB G` is left invariant when `m (L_g f) = m f` for every `g` and `f`, where
`(L_g f)(x) = f (-g + x)`. -/
def IsLeftInvariant (m : AddMean G) : Prop :=
  ∀ (g : G) (f : AddUCB G), m (AddUCB.leftTranslation g f) = m f

theorem isLeftInvariant_iff {m : AddMean G} :
    m.IsLeftInvariant ↔ ∀ (g : G) (f : AddUCB G), m (AddUCB.leftTranslation g f) = m f :=
  Iff.rfl

@[simp]
theorem IsLeftInvariant.apply_leftTranslation {m : AddMean G} (hm : m.IsLeftInvariant) (g : G)
    (f : AddUCB G) : m (AddUCB.leftTranslation g f) = m f :=
  hm g f

/-- Pushforward `f ↦ m (f ∘ φ)` of a mean on `AddUCB G` along `φ : G →ₜ+ A`. -/
def map (φ : G →ₜ+ A) (m : AddMean G) : AddMean A :=
  mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.compRightAlgHom φ).toLinearMap)
    (fun f hf => map_nonneg m (by simpa using AddUCB.monotone_compRightAlgHom φ hf)) (by simp)

@[simp]
theorem map_apply (φ : G →ₜ+ A) (m : AddMean G) (f : AddUCB A) :
    m.map φ f = m (AddUCB.compRightAlgHom φ f) :=
  mk₀_apply _ _ _ f

@[simp]
theorem map_id (m : AddMean G) : m.map (ContinuousAddMonoidHom.id G) = m :=
  ext fun _ => by simp

@[simp]
theorem map_map (ψ : A →ₜ+ B) (φ : G →ₜ+ A) (m : AddMean G) :
    (m.map φ).map ψ = m.map (ψ.comp φ) :=
  ext fun _ => by simp [AddUCB.compRightAlgHom_comp]

theorem IsLeftInvariant.map_apply_leftTranslation {m : AddMean G} (hm : m.IsLeftInvariant)
    (φ : G →ₜ+ A) (g : G) (f : AddUCB A) :
    m.map φ (AddUCB.leftTranslation (φ g) f) = m.map φ f := by
  rw [map_apply, map_apply, AddUCB.compRightAlgHom_leftTranslation, hm]

/-- Pushforward along a continuous additive homomorphism with dense range preserves left
invariance. -/
theorem IsLeftInvariant.map {m : AddMean G} (hm : m.IsLeftInvariant) {φ : G →ₜ+ A}
    (hφ : DenseRange φ) : (m.map φ).IsLeftInvariant := by
  intro a f
  have hc : Continuous fun k : A => m.map φ (AddUCB.leftTranslation k f) :=
    (map_continuous (m.map φ)).comp (AddUCB.continuous_leftTranslation_apply f)
  exact hφ.induction_on (p := fun k => m.map φ (AddUCB.leftTranslation k f) = m.map φ f) a
    (isClosed_eq hc continuous_const) fun g => hm.map_apply_leftTranslation φ g f

end AddMean

variable (G) in
/-- A topological additive group `G` is amenable when `AddUCB G` carries a left-invariant mean. -/
class AddAmenable : Prop where
  /-- An amenable additive group has a left-invariant mean on `AddUCB G`. -/
  exists_isLeftInvariant : ∃ m : AddMean G, m.IsLeftInvariant

variable (G) in
/-- A topological additive group is amenable exactly when `AddUCB G` carries a left-invariant
mean. -/
theorem addAmenable_iff : AddAmenable G ↔ ∃ m : AddMean G, m.IsLeftInvariant :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- Amenability of topological additive groups passes to targets of continuous homomorphisms with
dense range. -/
theorem AddAmenable.of_denseRange [AddAmenable G] (φ : G →ₜ+ A) (hφ : DenseRange φ) :
    AddAmenable A :=
  have ⟨m, hm⟩ := AddAmenable.exists_isLeftInvariant (G := G)
  ⟨⟨m.map φ, hm.map hφ⟩⟩

omit [TopologicalSpace G] [IsTopologicalAddGroup G] in
/-- Additive amenability passes from a finer additive group topology to a coarser one. -/
theorem AddAmenable.of_le {t₁ t₂ : TopologicalSpace G}
    [@IsTopologicalAddGroup G t₁ _] [@IsTopologicalAddGroup G t₂ _] (h : t₁ ≤ t₂)
    (ha : @AddAmenable G _ t₁ _) : @AddAmenable G _ t₂ _ := by
  let φ : @ContinuousAddMonoidHom G G _ _ t₁ t₂ :=
    @ContinuousAddMonoidHom.mk G G _ _ t₁ t₂ (AddMonoidHom.id G) (continuous_id_of_le h)
  exact @AddAmenable.of_denseRange G G _ t₁ _ _ t₂ _ ha φ
    (@Function.Surjective.denseRange G t₂ G _ fun x => ⟨x, AddMonoidHom.id_apply G x⟩)

end AddMean

/-! ### Transport across `Multiplicative` and `Additive` -/

section TypeTags

variable {G A : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

variable (G) in
/-- Means on `UCB (Multiplicative G)` correspond bijectively to means on `AddUCB G` along
`UCB.ofMultiplicative G`. -/
def Mean.multiplicativeEquiv : Mean (Multiplicative G) ≃ AddMean G where
  toFun m := AddMean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.ofMultiplicative G).symm.toLinearMap)
    (fun _ hf => map_nonneg m (UCB.le_def.2 fun y => by simpa using AddUCB.le_def.1 hf y.toAdd))
    (by simp)
  invFun m := Mean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.ofMultiplicative G).toLinearMap)
    (fun _ hf => map_nonneg m
      (AddUCB.le_def.2 fun y => by simpa using UCB.le_def.1 hf (Multiplicative.ofAdd y)))
    (by simp)
  left_inv m := Mean.ext fun f => by simp
  right_inv m := AddMean.ext fun f => by simp

@[simp]
theorem Mean.multiplicativeEquiv_apply (m : Mean (Multiplicative G)) (f : AddUCB G) :
    Mean.multiplicativeEquiv G m f = m ((UCB.ofMultiplicative G).symm f) :=
  (rfl)

@[simp]
theorem Mean.multiplicativeEquiv_symm_apply (m : AddMean G) (f : UCB (Multiplicative G)) :
    (Mean.multiplicativeEquiv G).symm m f = m (UCB.ofMultiplicative G f) :=
  Mean.mk₀_apply _ _ _ f

variable (G) in
/-- `Mean.multiplicativeEquiv G` is a weak-* homeomorphism. -/
def Mean.multiplicativeHomeomorph : Mean (Multiplicative G) ≃ₜ AddMean G where
  toEquiv := Mean.multiplicativeEquiv G
  continuous_toFun := continuous_iff_continuousAt.2 fun m =>
    AddMean.tendsto_iff_forall_apply_tendsto.2 fun f =>
      (continuous_eval_const ((UCB.ofMultiplicative G).symm f)).continuousAt.tendsto
  continuous_invFun := continuous_iff_continuousAt.2 fun m =>
    Mean.tendsto_iff_forall_apply_tendsto.2 fun f => by
      simpa only [Equiv.invFun_as_coe, Mean.multiplicativeEquiv_symm_apply] using
        (continuous_eval_const (UCB.ofMultiplicative G f)).continuousAt.tendsto

@[simp]
theorem Mean.multiplicativeHomeomorph_apply (m : Mean (Multiplicative G)) :
    Mean.multiplicativeHomeomorph G m = Mean.multiplicativeEquiv G m :=
  (rfl)

@[simp]
theorem Mean.multiplicativeHomeomorph_symm_apply (m : AddMean G) :
    (Mean.multiplicativeHomeomorph G).symm m = (Mean.multiplicativeEquiv G).symm m :=
  (rfl)

@[simp]
theorem Mean.isLeftInvariant_multiplicativeEquiv_iff {m : Mean (Multiplicative G)} :
    (Mean.multiplicativeEquiv G m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  refine ⟨fun hm => Mean.isLeftInvariant_iff.2 fun g f => ?_,
    fun hm => AddMean.isLeftInvariant_iff.2 fun g f => ?_⟩
  · simpa using hm g.toAdd (UCB.ofMultiplicative G f)
  · simp [hm.apply_leftTranslation]

@[simp]
theorem Mean.isLeftInvariant_multiplicativeEquiv_symm_iff {m : AddMean G} :
    ((Mean.multiplicativeEquiv G).symm m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [← Mean.isLeftInvariant_multiplicativeEquiv_iff, Equiv.apply_symm_apply]

/-- `Multiplicative G` is amenable if and only if `G` is additively amenable. -/
@[simp]
theorem amenable_multiplicative_iff : Amenable (Multiplicative G) ↔ AddAmenable G := by
  rw [amenable_iff, addAmenable_iff, ← (Mean.multiplicativeEquiv G).exists_congr_right]
  simp

section AdditiveTag

variable {H K : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

variable (H) in
/-- Means on `AddUCB (Additive H)` correspond bijectively to means on `UCB H` along
`AddUCB.ofAdditive H`. -/
def AddMean.additiveEquiv : AddMean (Additive H) ≃ Mean H where
  toFun m := Mean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.ofAdditive H).symm.toLinearMap)
    (fun _ hf => map_nonneg m (AddUCB.le_def.2 fun y => by simpa using UCB.le_def.1 hf y.toMul))
    (by simp)
  invFun m := AddMean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.ofAdditive H).toLinearMap)
    (fun _ hf => map_nonneg m
      (UCB.le_def.2 fun y => by simpa using AddUCB.le_def.1 hf (Additive.ofMul y)))
    (by simp)
  left_inv m := AddMean.ext fun f => by simp
  right_inv m := Mean.ext fun f => by simp

@[simp]
theorem AddMean.additiveEquiv_apply (m : AddMean (Additive H)) (f : UCB H) :
    AddMean.additiveEquiv H m f = m ((AddUCB.ofAdditive H).symm f) :=
  Mean.mk₀_apply _ _ _ f

@[simp]
theorem AddMean.additiveEquiv_symm_apply (m : Mean H) (f : AddUCB (Additive H)) :
    (AddMean.additiveEquiv H).symm m f = m (AddUCB.ofAdditive H f) :=
  (rfl)

variable (H) in
/-- `AddMean.additiveEquiv H` is a weak-* homeomorphism. -/
def AddMean.additiveHomeomorph : AddMean (Additive H) ≃ₜ Mean H where
  toEquiv := AddMean.additiveEquiv H
  continuous_toFun := continuous_iff_continuousAt.2 fun m =>
    Mean.tendsto_iff_forall_apply_tendsto.2 fun f => by
      simpa only [Equiv.toFun_as_coe, AddMean.additiveEquiv_apply] using
        (continuous_eval_const ((AddUCB.ofAdditive H).symm f)).continuousAt.tendsto
  continuous_invFun := continuous_iff_continuousAt.2 fun m =>
    AddMean.tendsto_iff_forall_apply_tendsto.2 fun f =>
      (continuous_eval_const (AddUCB.ofAdditive H f)).continuousAt.tendsto

@[simp]
theorem AddMean.additiveHomeomorph_apply (m : AddMean (Additive H)) :
    AddMean.additiveHomeomorph H m = AddMean.additiveEquiv H m :=
  (rfl)

@[simp]
theorem AddMean.additiveHomeomorph_symm_apply (m : Mean H) :
    (AddMean.additiveHomeomorph H).symm m = (AddMean.additiveEquiv H).symm m :=
  (rfl)

@[simp]
theorem AddMean.isLeftInvariant_additiveEquiv_iff {m : AddMean (Additive H)} :
    (AddMean.additiveEquiv H m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  refine ⟨fun hm => AddMean.isLeftInvariant_iff.2 fun g f => ?_,
    fun hm => Mean.isLeftInvariant_iff.2 fun h f => ?_⟩
  · simpa using hm.apply_leftTranslation g.toMul (AddUCB.ofAdditive H f)
  · simp [hm.apply_leftTranslation]

@[simp]
theorem AddMean.isLeftInvariant_additiveEquiv_symm_iff {m : Mean H} :
    ((AddMean.additiveEquiv H).symm m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [← AddMean.isLeftInvariant_additiveEquiv_iff, Equiv.apply_symm_apply]

/-- `Additive H` is additively amenable if and only if `H` is amenable. -/
@[simp]
theorem addAmenable_additive_iff : AddAmenable (Additive H) ↔ Amenable H := by
  rw [addAmenable_iff, amenable_iff, ← (AddMean.additiveEquiv H).exists_congr_right]
  simp

end AdditiveTag

section FoelnerTags

/-- `Multiplicative B` has Følner sets if and only if `B` has additive Følner sets. -/
@[simp]
theorem hasFoelnerSets_multiplicative_iff {B : Type*} [AddGroup B] :
    HasFoelnerSets (Multiplicative B) ↔ HasAddFoelnerSets B := by
  classical
  rw [hasFoelnerSets_iff, hasAddFoelnerSets_iff]
  refine ⟨fun h K ε hε => ?_, fun h K ε hε => ?_⟩
  · obtain ⟨F, hFne, hF⟩ := h (K.image Multiplicative.ofAdd) ε hε
    refine ⟨F.image Multiplicative.toAdd, hFne.image _, fun g hg => ?_⟩
    have hsmul : g +ᵥ F.image Multiplicative.toAdd =
        (Multiplicative.ofAdd g • F).image Multiplicative.toAdd := by
      rw [vadd_finset_def, smul_finset_def, Finset.image_image, Finset.image_image]; congr 1
    rw [hsmul, ← Finset.image_symmDiff _ _ Multiplicative.toAdd.injective,
      Finset.card_image_of_injective _ Multiplicative.toAdd.injective,
      Finset.card_image_of_injective _ Multiplicative.toAdd.injective]
    exact hF (Multiplicative.ofAdd g) (Finset.mem_image_of_mem _ hg)
  · obtain ⟨F, hFne, hF⟩ := h (K.image Multiplicative.toAdd) ε hε
    refine ⟨F.image Multiplicative.ofAdd, hFne.image _, fun g hg => ?_⟩
    have hsmul : g • F.image Multiplicative.ofAdd =
        (g.toAdd +ᵥ F).image Multiplicative.ofAdd := by
      rw [smul_finset_def, vadd_finset_def, Finset.image_image, Finset.image_image]; congr 1
    rw [hsmul, ← Finset.image_symmDiff _ _ Multiplicative.ofAdd.injective,
      Finset.card_image_of_injective _ Multiplicative.ofAdd.injective,
      Finset.card_image_of_injective _ Multiplicative.ofAdd.injective]
    exact hF g.toAdd (Finset.mem_image_of_mem _ hg)

/-- `Additive H` has additive Følner sets if and only if `H` has Følner sets. -/
@[simp]
theorem hasAddFoelnerSets_additive_iff {H : Type*} [Group H] :
    HasAddFoelnerSets (Additive H) ↔ HasFoelnerSets H := by
  classical
  rw [hasAddFoelnerSets_iff, hasFoelnerSets_iff]
  refine ⟨fun h K ε hε => ?_, fun h K ε hε => ?_⟩
  · obtain ⟨F, hFne, hF⟩ := h (K.image Additive.ofMul) ε hε
    refine ⟨F.image Additive.toMul, hFne.image _, fun g hg => ?_⟩
    have hsmul : g • F.image Additive.toMul =
        (Additive.ofMul g +ᵥ F).image Additive.toMul := by
      rw [smul_finset_def, vadd_finset_def, Finset.image_image, Finset.image_image]; congr 1
    rw [hsmul, ← Finset.image_symmDiff _ _ Additive.toMul.injective,
      Finset.card_image_of_injective _ Additive.toMul.injective,
      Finset.card_image_of_injective _ Additive.toMul.injective]
    exact hF (Additive.ofMul g) (Finset.mem_image_of_mem _ hg)
  · obtain ⟨F, hFne, hF⟩ := h (K.image Additive.toMul) ε hε
    refine ⟨F.image Additive.ofMul, hFne.image _, fun g hg => ?_⟩
    have hsmul : g +ᵥ F.image Additive.ofMul =
        (g.toMul • F).image Additive.ofMul := by
      rw [vadd_finset_def, smul_finset_def, Finset.image_image, Finset.image_image]; congr 1
    rw [hsmul, ← Finset.image_symmDiff _ _ Additive.ofMul.injective,
      Finset.card_image_of_injective _ Additive.ofMul.injective,
      Finset.card_image_of_injective _ Additive.ofMul.injective]
    exact hF g.toMul (Finset.mem_image_of_mem _ hg)

end FoelnerTags

end TypeTags

end TauCeti

namespace ContinuousAddEquiv

open TauCeti

/-- Additive amenability is invariant under continuous additive isomorphisms. -/
theorem addAmenable_iff {G A : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] (e : G ≃ₜ+ A) :
    AddAmenable G ↔ AddAmenable A :=
  ⟨fun _ => .of_denseRange (e : G →ₜ+ A) e.surjective.denseRange,
    fun _ => .of_denseRange (e.symm : A →ₜ+ G) e.symm.surjective.denseRange⟩

end ContinuousAddEquiv

namespace TauCeti

/-! ### Permanence properties, instances, and discrete characterizations -/

section Permanence

/-- An abstract additive group which is additively amenable in the discrete topology is additively
amenable for every additive group topology. -/
theorem AddAmenable.of_discrete {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G]
    (h : letI : TopologicalSpace G := ⊥;
      letI := discreteTopology_bot G; AddAmenable G) :
    AddAmenable G := by
  let : @DiscreteTopology G ⊥ := discreteTopology_bot G
  exact AddAmenable.of_le (t₁ := ⊥) bot_le h

/-- Every finite topological additive group is additively amenable. -/
instance (priority := 100) AddAmenable.of_finite {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [Finite G] : AddAmenable G :=
  amenable_multiplicative_iff.1 inferInstance

/-- Every compact topological additive group is additively amenable. -/
instance (priority := 100) AddAmenable.of_compactSpace {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] : AddAmenable G :=
  amenable_multiplicative_iff.1 inferInstance

/-- An additive group embedding by an injective homomorphism into an amenable discrete additive
group is additively amenable, for every additive group topology on the source. -/
theorem AddAmenable.of_injective {G A : Type*} [AddGroup G] [TopologicalSpace G]
    [DiscreteTopology G] [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [AddAmenable G] (φ : A →+ G) (hφ : Function.Injective φ) : AddAmenable A := by
  have : Amenable (Multiplicative G) := amenable_multiplicative_iff.2 ‹_›
  exact amenable_multiplicative_iff.1 <|
    .of_injective φ.toMultiplicative
      (Multiplicative.ofAdd.injective.comp (hφ.comp Multiplicative.toAdd.injective))

/-- Every additive subgroup of an amenable discrete additive group is additively amenable. -/
instance AddAmenable.addSubgroup {G : Type*} [AddGroup G] [TopologicalSpace G]
    [DiscreteTopology G] [AddAmenable G] (K : AddSubgroup G) : AddAmenable K :=
  .of_injective K.subtype K.subtype_injective

/-- If `ψ : K →+ G` and `φ : G →+ Q` are homomorphisms of discrete additive groups with
`φ.ker ≤ ψ.range`, and `K` and `Q` are additively amenable, then `G` is additively amenable. -/
theorem AddAmenable.of_ker_le_range {G K Q : Type*} [AddGroup G] [TopologicalSpace G]
    [DiscreteTopology G] [AddGroup K] [TopologicalSpace K] [DiscreteTopology K]
    [AddGroup Q] [TopologicalSpace Q] [DiscreteTopology Q] [AddAmenable K] [AddAmenable Q]
    (ψ : K →+ G) (φ : G →+ Q) (h : φ.ker ≤ ψ.range) : AddAmenable G := by
  have : Amenable (Multiplicative K) := amenable_multiplicative_iff.2 ‹_›
  have : Amenable (Multiplicative Q) := amenable_multiplicative_iff.2 ‹_›
  refine amenable_multiplicative_iff.1
    (.of_ker_le_range ψ.toMultiplicative φ.toMultiplicative fun x hx => ?_)
  have hx' : x.toAdd ∈ φ.ker := by
    simpa [MonoidHom.mem_ker, AddMonoidHom.mem_ker] using congrArg Multiplicative.toAdd hx
  obtain ⟨k, hk⟩ := h hx'
  exact ⟨Multiplicative.ofAdd k, by simp [hk]⟩

/-- A discrete additive group with a normal additive subgroup `N` is additively amenable if and only
if `N` and `G ⧸ N` are additively amenable. -/
theorem addAmenable_iff_addSubgroup_quotient {G : Type*} [AddGroup G] [TopologicalSpace G]
    [DiscreteTopology G] (N : AddSubgroup G) [N.Normal] :
    AddAmenable G ↔ AddAmenable N ∧ AddAmenable (G ⧸ N) := by
  have := QuotientAddGroup.discreteTopology (isOpen_discrete (N : Set G))
  refine ⟨fun _ => ⟨inferInstance, ?_⟩, fun ⟨_, _⟩ =>
    .of_ker_le_range N.subtype (QuotientAddGroup.mk' N) (by simp)⟩
  exact .of_denseRange ⟨QuotientAddGroup.mk' N, continuous_of_discreteTopology⟩
    (QuotientAddGroup.mk'_surjective N).denseRange

/-- A discrete additive group is additively amenable when it has an additively amenable normal
subgroup with additively amenable quotient. -/
theorem AddAmenable.of_addSubgroup_quotient {G : Type*} [AddGroup G] [TopologicalSpace G]
    [DiscreteTopology G] (N : AddSubgroup G) [N.Normal] [AddAmenable N] [AddAmenable (G ⧸ N)] :
    AddAmenable G :=
  (addAmenable_iff_addSubgroup_quotient N).2 ⟨‹_›, ‹_›⟩

/-- The product of two additively amenable topological additive groups is additively amenable. -/
instance AddAmenable.prod {G A : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [AddAmenable G] [AddAmenable A] :
    AddAmenable (G × A) := by
  have : Amenable (Multiplicative G) := amenable_multiplicative_iff.2 ‹_›
  have : Amenable (Multiplicative A) := amenable_multiplicative_iff.2 ‹_›
  exact amenable_multiplicative_iff.1
    ((ContinuousMulEquiv.prodMultiplicative G A).amenable_iff.2 inferInstance)

/-- A product of two topological additive groups is additively amenable if and only if both factors
are. -/
theorem addAmenable_prod_iff (G A : Type*) [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] :
    AddAmenable (G × A) ↔ AddAmenable G ∧ AddAmenable A :=
  ⟨fun _ => ⟨.of_denseRange (ContinuousAddMonoidHom.fst G A) Prod.fst_surjective.denseRange,
      .of_denseRange (ContinuousAddMonoidHom.snd G A) Prod.snd_surjective.denseRange⟩,
    fun ⟨_, _⟩ => inferInstance⟩

/-- The product of a finite family of additively amenable topological additive groups is additively
amenable. -/
instance AddAmenable.pi {ι : Type u} [Finite ι] {G : ι → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalAddGroup (G i)] [∀ i, AddAmenable (G i)] :
    AddAmenable (∀ i, G i) := by
  have (i : ι) : Amenable (Multiplicative (G i)) := amenable_multiplicative_iff.2 inferInstance
  exact amenable_multiplicative_iff.1
    ((ContinuousMulEquiv.piMultiplicative G).amenable_iff.2 inferInstance)

/-- A finite product of topological additive groups is additively amenable if and only if every
factor is. -/
theorem addAmenable_pi_iff {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalAddGroup (G i)] :
    AddAmenable (∀ i, G i) ↔ ∀ i, AddAmenable (G i) :=
  ⟨fun _ i => .of_denseRange ⟨Pi.evalAddMonoidHom G i, continuous_apply i⟩
      (Function.surjective_eval i).denseRange,
    fun _ => inferInstance⟩

/-- A topological additive group `G` is additively amenable if every finite subset of `G` lies in
the range of one of a family of continuous homomorphisms `φ i : K i →ₜ+ G` from additively amenable
topological additive groups. -/
theorem AddAmenable.of_forall_finset_subset_range {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {ι : Type*} {K : ι → Type*} [∀ i, AddGroup (K i)]
    [∀ i, TopologicalSpace (K i)] [∀ i, IsTopologicalAddGroup (K i)] [∀ i, AddAmenable (K i)]
    (φ : ∀ i, K i →ₜ+ G) (h : ∀ s : Finset G, ∃ i, (s : Set G) ⊆ Set.range (φ i)) :
    AddAmenable G := by
  classical
  have (i : ι) : Amenable (Multiplicative (K i)) := amenable_multiplicative_iff.2 inferInstance
  refine amenable_multiplicative_iff.1
    (.of_forall_finset_subset_range (fun i => (φ i).toMultiplicative) fun s => ?_)
  obtain ⟨i, hi⟩ := h (s.map Multiplicative.toAdd.toEmbedding)
  refine ⟨i, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hi (Finset.mem_coe.2 (Finset.mem_map_of_mem _ (Finset.mem_coe.1 hx)))
  exact ⟨Multiplicative.ofAdd k, by simp [hk]⟩

/-- The supremum `⨆ i, H i` of a directed family of additively amenable subgroups of a topological
additive group is an additively amenable subgroup. -/
theorem addAmenable_iSup_of_directed {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {ι : Type*} {H : ι → AddSubgroup G}
    (hH : Directed (· ≤ ·) H) [∀ i, AddAmenable (H i)] : AddAmenable ↥(⨆ i, H i) := by
  classical
  obtain hι | hι := isEmpty_or_nonempty ι
  · rw [iSup_of_empty]
    infer_instance
  refine .of_forall_finset_subset_range
    (fun i => ⟨AddSubgroup.inclusion (le_iSup H i), continuous_subtype_val.subtype_mk _⟩)
    fun s => ?_
  have hH' : Directed (· ⊆ ·) fun i => (H i : Set G) :=
    hH.mono_comp _ fun _ _ => SetLike.coe_subset_coe.2
  obtain ⟨i, hi⟩ := hH'.exists_mem_subset_of_finset_subset_biUnion (s := s.image Subtype.val) <| by
    rw [Finset.coe_image, ← AddSubgroup.coe_iSup_of_directed hH]
    exact Set.image_subset_iff.2 fun x _ => x.2
  exact ⟨i, fun x hx => ⟨⟨x, hi (Finset.mem_image_of_mem _ hx)⟩, rfl⟩⟩

/-- A topological additive group which is the supremum of a directed family of additively amenable
subgroups is additively amenable. -/
theorem AddAmenable.of_directed_of_iSup_eq_top {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {ι : Type*} {H : ι → AddSubgroup G}
    (hH : Directed (· ≤ ·) H) (htop : ⨆ i, H i = ⊤) [∀ i, AddAmenable (H i)] : AddAmenable G :=
  have := addAmenable_iSup_of_directed hH
  .of_denseRange ⟨(⨆ i, H i).subtype, continuous_subtype_val⟩
    (Function.Surjective.denseRange fun x => ⟨⟨x, htop ▸ AddSubgroup.mem_top x⟩, rfl⟩)

/-- A topological additive group all of whose finitely generated additive subgroups are additively
amenable is additively amenable. -/
theorem AddAmenable.of_forall_fg {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (h : ∀ K : AddSubgroup G, K.FG → AddAmenable K) : AddAmenable G := by
  have : ∀ K : {K : AddSubgroup G // K.FG}, AddAmenable K.1 := fun K => h K.1 K.2
  refine .of_forall_finset_subset_range
    (fun K : {K : AddSubgroup G // K.FG} => ⟨K.1.subtype, continuous_subtype_val⟩) fun s => ?_
  refine ⟨⟨AddSubgroup.closure s, (AddGroup.fg_iff_addSubgroup_fg _).1 inferInstance⟩,
    fun x hx => ?_⟩
  exact ⟨⟨x, AddSubgroup.subset_closure hx⟩, rfl⟩

end Permanence

/-! ### Discrete invariant contents, Reiter's condition, and Følner sets -/

section DiscreteAndFoelner

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- A topological additive group is additively amenable when it has finite nonempty sets `F i` with
`|(g +ᵥ F i) △ F i| / |F i| → 0` for every `g` along a nontrivial filter. -/
theorem AddAmenable.of_tendsto_card_vadd_symmDiff_div_card [DecidableEq G] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Finset G} (hne : ∀ i, (F i).Nonempty)
    (h : ∀ g : G, Tendsto (fun i => (#((g +ᵥ F i) ∆ F i) : ℝ) / #(F i)) l (𝓝 0)) :
    AddAmenable G := by
  refine amenable_multiplicative_iff.1 <|
    Amenable.of_tendsto_card_smul_symmDiff_div_card (l := l)
      (F := fun i => (F i).image Multiplicative.ofAdd)
      (fun i => (hne i).image _) fun g => ?_
  have hsmul (i : ι) : g • (F i).image Multiplicative.ofAdd =
      (g.toAdd +ᵥ F i).image Multiplicative.ofAdd := by
    rw [smul_finset_def, vadd_finset_def, Finset.image_image, Finset.image_image]; congr 1
  simpa only [hsmul, ← Finset.image_symmDiff _ _ Multiplicative.ofAdd.injective,
    Finset.card_image_of_injective _ Multiplicative.ofAdd.injective] using h g.toAdd

/-- A topological additive group is additively amenable when it has an additive Følner family for
counting measure along a nontrivial filter. -/
theorem AddAmenable.of_isAddFoelner [MeasurableSpace G] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Set G}
    (hF : IsAddFoelner G MeasureTheory.Measure.count l F) : AddAmenable G := by
  classical
  let s := {i | MeasurableSet (F i) ∧ MeasureTheory.Measure.count (F i) ≠ 0 ∧
    MeasureTheory.Measure.count (F i) ≠ ⊤}
  have : (comap ((↑) : s → ι) l).NeBot := comap_coe_neBot_of_le_principal <| le_principal_iff.2 <|
    hF.eventually_measurableSet.and (hF.eventually_meas_ne_zero.and hF.eventually_meas_ne_top)
  obtain ⟨F', hF'⟩ : ∃ F' : s → Finset G, ∀ i, (F' i : Set G) = F i := ⟨fun i =>
    ((MeasureTheory.Measure.count_apply_lt_top' i.2.1).1
      (lt_top_iff_ne_top.2 i.2.2.2)).toFinset, by simp⟩
  have hne (i : s) : (F' i).Nonempty := by
    simpa [← coe_nonempty, hF', Set.nonempty_iff_ne_empty] using i.2.2.1
  refine .of_tendsto_card_vadd_symmDiff_div_card (l := comap (↑) l) hne fun g => ?_
  have hF's : IsAddFoelner G MeasureTheory.Measure.count (comap ((↑) : s → ι) l)
      (fun i => (F' i : Set G)) := by
    simpa only [hF', Function.comp_def] using
      hF.comp_tendsto (tendsto_comap (f := ((↑) : s → ι)))
  exact hF's.tendsto_card_vadd_symmDiff_div_card g

/-- An additive group with additive Følner sets is additively amenable for every additive group
topology. -/
theorem AddAmenable.of_hasAddFoelnerSets (h : HasAddFoelnerSets G) : AddAmenable G :=
  amenable_multiplicative_iff.1 (.of_hasFoelnerSets (hasFoelnerSets_multiplicative_iff.2 h))

/-- An additively amenable discrete group has additive Følner sets. -/
theorem AddAmenable.hasAddFoelnerSets [DiscreteTopology G] [AddAmenable G] :
    HasAddFoelnerSets G := by
  have : Amenable (Multiplicative G) := amenable_multiplicative_iff.2 ‹_›
  exact hasFoelnerSets_multiplicative_iff.1 Amenable.hasFoelnerSets

/-- A discrete additive group is additively amenable if and only if it has additive Følner sets. -/
theorem addAmenable_iff_hasAddFoelnerSets [DiscreteTopology G] :
    AddAmenable G ↔ HasAddFoelnerSets G :=
  ⟨fun _ => AddAmenable.hasAddFoelnerSets, .of_hasAddFoelnerSets⟩

/-- A discrete additive group is additively amenable if and only if for every finite `K ⊆ G` and
`ε > 0` there is a finite nonempty `F ⊆ G` with `|(g +ᵥ F) △ F| < ε · |F|` for all `g ∈ K`. -/
theorem addAmenable_iff_exists_finset [DiscreteTopology G] [DecidableEq G] :
    AddAmenable G ↔ ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset G, F.Nonempty ∧ ∀ g ∈ K, (#((g +ᵥ F) ∆ F) : ℝ) < ε * #F := by
  rw [addAmenable_iff_hasAddFoelnerSets, hasAddFoelnerSets_iff]

/-- **Reiter's condition for discrete additive groups.** In an additively amenable discrete group,
for every finite `K ⊆ G` and `ε > 0` there is a finitely supported probability density `p : G → ℝ`
with `∑_{g ∈ K} ∑_x |p (-g + x) - p x| < ε`. -/
theorem AddAmenable.exists_sum_tsum_abs_sub_lt [DiscreteTopology G] [AddAmenable G] (K : Finset G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
      ∑ g ∈ K, ∑' x, |p (-g + x) - p x| < ε := by
  classical
  have : Amenable (Multiplicative G) := amenable_multiplicative_iff.2 ‹_›
  obtain ⟨p, hp0, hpsupp, hp1, hpε⟩ :=
    Amenable.exists_sum_tsum_abs_sub_lt (K.map Multiplicative.ofAdd.toEmbedding) hε
  refine ⟨p ∘ Multiplicative.ofAdd, fun x => hp0 _, ?_, ?_, ?_⟩
  · rw [HasFiniteSupport, Function.support_comp_eq_preimage]
    exact hpsupp.preimage Multiplicative.ofAdd.injective.injOn
  · exact (Multiplicative.ofAdd.tsum_eq p).trans hp1
  · rw [Finset.sum_map] at hpε
    have htsum (g : G) :
        (∑' x : G, |p (Multiplicative.ofAdd (-g + x)) - p (Multiplicative.ofAdd x)|) =
        ∑' y : Multiplicative G, |p ((Multiplicative.ofAdd g)⁻¹ * y) - p y| :=
      Multiplicative.ofAdd.tsum_eq fun y => |p ((Multiplicative.ofAdd g)⁻¹ * y) - p y|
    simpa only [Function.comp_apply, Function.Embedding.coeFn_mk, Equiv.coe_fn_mk, htsum]
      using hpε

/-- A discrete additive group is additively amenable if and only if it satisfies Reiter's
condition. -/
theorem addAmenable_iff_exists_sum_tsum_abs_sub_lt [DiscreteTopology G] :
    AddAmenable G ↔ ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
        ∑ g ∈ K, ∑' x, |p (-g + x) - p x| < ε := by
  classical
  refine ⟨fun _ K _ hε => AddAmenable.exists_sum_tsum_abs_sub_lt K hε, fun h => ?_⟩
  refine amenable_multiplicative_iff.1 (amenable_iff_exists_sum_tsum_abs_sub_lt.2 fun K ε hε => ?_)
  obtain ⟨p, hp0, hpsupp, hp1, hpε⟩ := h (K.map Multiplicative.toAdd.toEmbedding) ε hε
  refine ⟨p ∘ Multiplicative.toAdd, fun x => hp0 _, ?_, ?_, ?_⟩
  · rw [HasFiniteSupport, Function.support_comp_eq_preimage]
    exact hpsupp.preimage Multiplicative.toAdd.injective.injOn
  · exact (Multiplicative.toAdd.tsum_eq p).trans hp1
  · rw [Finset.sum_map] at hpε
    have htsum (g : Multiplicative G) :
        (∑' y : Multiplicative G, |p ((g⁻¹ * y).toAdd) - p y.toAdd|) =
        ∑' x : G, |p (-g.toAdd + x) - p x| :=
      Multiplicative.toAdd.tsum_eq fun x => |p (-g.toAdd + x) - p x|
    simpa only [Function.comp_apply, Function.Embedding.coeFn_mk, Equiv.coe_fn_mk, htsum]
      using hpε

variable (G) in
/-- **Discrete additive amenability by finitely additive probabilities.** A discrete additive group
is additively amenable if and only if it admits a left-invariant finitely additive probability on
all subsets. -/
theorem addAmenable_iff_exists_invariantContent [DiscreteTopology G] :
    AddAmenable G ↔ ∃ ν : AddContent ℝ≥0∞ (univ : Set (Set G)),
      ν univ = 1 ∧ ∀ (g : G) (s : Set G), ν (g +ᵥ s) = ν s := by
  rw [← amenable_multiplicative_iff, amenable_iff_exists_invariantContent]
  refine ⟨fun ⟨ν, h1, hν⟩ => ?_, fun ⟨ν, h1, hν⟩ => ?_⟩
  · refine ⟨ν.map (D := univ) Multiplicative.toAdd (fun _ _ => mem_univ _), by simpa using h1,
      fun g s => ?_⟩
    have hpre : Multiplicative.toAdd ⁻¹' (g +ᵥ s) =
        Multiplicative.ofAdd g • (Multiplicative.toAdd ⁻¹' s) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_vadd_set, Set.mem_smul_set, Multiplicative.exists]
      refine ⟨fun ⟨a, ha, hax⟩ => ⟨a, ha, Multiplicative.toAdd.injective ?_⟩,
        fun ⟨a, ha, hax⟩ => ⟨a, ha, ?_⟩⟩
      · simpa [smul_eq_mul, vadd_eq_add] using hax
      · simpa [smul_eq_mul, vadd_eq_add] using congrArg Multiplicative.toAdd hax
    rw [AddContent.map_apply, AddContent.map_apply, hpre, hν]
  · refine ⟨ν.map (D := univ) Multiplicative.ofAdd (fun _ _ => mem_univ _), by simpa using h1,
      fun g s => ?_⟩
    have hpre : Multiplicative.ofAdd ⁻¹' (g • s) =
        g.toAdd +ᵥ (Multiplicative.ofAdd ⁻¹' s) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_smul_set, Set.mem_vadd_set, Multiplicative.exists]
      refine ⟨fun ⟨a, ha, hax⟩ => ⟨a, ha, ?_⟩,
        fun ⟨a, ha, hax⟩ => ⟨a, ha, Multiplicative.toAdd.injective ?_⟩⟩
      · simpa [smul_eq_mul, vadd_eq_add] using congrArg Multiplicative.toAdd hax
      · simpa [smul_eq_mul, vadd_eq_add] using hax
    rw [AddContent.map_apply, AddContent.map_apply, hpre, hν]

/-- An additively amenable discrete group admits a left-invariant finitely additive probability on
all subsets. -/
theorem AddAmenable.exists_invariantContent [DiscreteTopology G] [AddAmenable G] :
    ∃ ν : AddContent ℝ≥0∞ (univ : Set (Set G)),
      ν univ = 1 ∧ ∀ (g : G) (s : Set G), ν (g +ᵥ s) = ν s :=
  (addAmenable_iff_exists_invariantContent G).1 ‹_›

end DiscreteAndFoelner

end TauCeti

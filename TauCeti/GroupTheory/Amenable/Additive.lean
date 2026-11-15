/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ContinuousMulEquiv
public import TauCeti.Topology.Algebra.Group.UCB.Additive
public import TauCeti.GroupTheory.Amenable.DirectedUnion
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
public import TauCeti.GroupTheory.Amenable.Extension
public import TauCeti.GroupTheory.Amenable.Prod
public import TauCeti.GroupTheory.Amenable.Sequence

/-!
# Amenable additive topological groups

An additive topological group `A` is *amenable* (`TauCeti.AddAmenable A`) when `TauCeti.AddUCB A`
carries a left-invariant mean (`TauCeti.AddMean A`).

Through `AddUCB.toMultiplicativeAlgEquiv`, means on `AddUCB A` correspond bijectively to means on
`UCB (Multiplicative A)` (`AddMean.toMultiplicativeEquiv`), preserving and reflecting left
invariance. Consequently `Amenable (Multiplicative A) ↔ AddAmenable A` and
`AddAmenable (Additive G) ↔ Amenable G`. This file provides `AddMean`, `AddAmenable`, the
compatibility equivalences across `Multiplicative` and `Additive`, and the additive closure and
discrete Følner API matching the multiplicative theory.

## Main definitions

* `TauCeti.AddMean A`: positive unital real linear functionals on `AddUCB A`.
* `TauCeti.AddMean.IsLeftInvariant`: invariance under `AddUCB.leftTranslation`.
* `TauCeti.AddMean.map`: pushforward of additive means along `φ : A →ₜ+ B`.
* `TauCeti.AddMean.toMultiplicativeEquiv`, `TauCeti.Mean.toAdditiveEquiv`: bijections between
  additive and multiplicative means across `Multiplicative` and `Additive`.
* `TauCeti.AddAmenable A`: `AddUCB A` carries a left-invariant mean.

## Main results

* `TauCeti.amenable_multiplicative_iff`, `TauCeti.addAmenable_additive_iff`: `AddAmenable` and
  `Amenable` correspond under `Multiplicative` and `Additive`.
* `TauCeti.AddAmenable.of_denseRange`, `TauCeti.AddAmenable.quotient`,
  `ContinuousAddEquiv.addAmenable_iff`, `TauCeti.AddAmenable.of_le`,
  `TauCeti.AddAmenable.of_discrete`: image, quotient, and topology closure.
* `TauCeti.AddAmenable.of_finite`, `TauCeti.AddAmenable.prod`, `TauCeti.AddAmenable.pi`,
  `TauCeti.addAmenable_prod_iff`, `TauCeti.addAmenable_pi_iff`: finite groups and arbitrary
  products.
* `TauCeti.AddAmenable.of_hasAddFoelnerSets`, `TauCeti.AddAmenable.of_isAddFoelner`,
  `TauCeti.AddAmenable.of_tendsto_card_vadd_symmDiff_div_card`,
  `TauCeti.addAmenable_iff_hasAddFoelnerSets`, `TauCeti.addAmenable_iff_exists_finset`,
  `TauCeti.addAmenable_iff_exists_seq`: Følner criteria.
* `TauCeti.AddAmenable.of_injective`, `TauCeti.AddAmenable.addSubgroup`,
  `TauCeti.AddAmenable.of_ker_le_range`: subgroups and extensions of discrete additive groups.
* `TauCeti.AddAmenable.of_forall_finset_subset_range`, `TauCeti.addAmenable_iSup_of_directed`,
  `TauCeti.AddAmenable.of_directed_of_iSup_eq_top`, `TauCeti.AddAmenable.of_forall_fg`:
  directed unions and reduction to finitely generated additive subgroups.
-/

public section

noncomputable section

open Filter Finset Topology
open scoped BoundedContinuousFunction Pointwise symmDiff

namespace TauCeti

section AddMean

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

variable (A) in
/-- A mean on `AddUCB A`: a positive real linear functional taking the value `1` at the constant
function `1`. -/
structure AddMean extends AddUCB A →ₚ[ℝ] ℝ where
  /-- An additive mean takes the value `1` at the constant function `1`. -/
  map_one' : toFun 1 = 1

namespace AddMean

instance : FunLike (AddMean A) (AddUCB A) ℝ where
  coe m := m.toFun
  coe_injective := by
    rintro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (AddMean A) ℝ (AddUCB A) ℝ where
  map_add m := map_add m.toPositiveLinearMap
  map_smulₛₗ m := map_smul m.toPositiveLinearMap

instance : OrderHomClass (AddMean A) (AddUCB A) ℝ where
  map_rel m _ _ h := OrderHomClass.mono m.toPositiveLinearMap h

/-- Two additive means are equal when they agree on every function. -/
@[ext]
theorem ext {m n : AddMean A} (h : ∀ f, m f = n f) : m = n :=
  DFunLike.ext m n h

@[simp]
theorem coe_toPositiveLinearMap (m : AddMean A) : ⇑m.toPositiveLinearMap = ⇑m :=
  (rfl)

/-- An additive mean takes the value `1` at the constant function `1`. -/
@[simp]
theorem map_one (m : AddMean A) : m 1 = 1 :=
  m.map_one'

/-- Build an `AddMean` from a linear functional nonnegative on nonnegative functions and sending
`1` to `1`. -/
def mk₀ (φ : AddUCB A →ₗ[ℝ] ℝ) (hφ : ∀ f, 0 ≤ f → 0 ≤ φ f) (h₁ : φ 1 = 1) : AddMean A :=
  { PositiveLinearMap.mk₀ φ hφ with map_one' := h₁ }

@[simp]
theorem mk₀_apply (φ : AddUCB A →ₗ[ℝ] ℝ) (hφ : ∀ f, 0 ≤ f → 0 ≤ φ f) (h₁ : φ 1 = 1)
    (f : AddUCB A) : mk₀ φ hφ h₁ f = φ f :=
  (rfl)

@[simp]
theorem map_algebraMap (m : AddMean A) (c : ℝ) : m (algebraMap ℝ (AddUCB A) c) = c := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- An additive mean is `1`-Lipschitz for the supremum norm. -/
theorem lipschitzWith (m : AddMean A) : LipschitzWith 1 m := by
  simpa using
    PositiveLinearMap.lipschitzWith_of_forall_le_norm_smul m (AddUCB.le_norm_smul_one (A := A))

/-- An additive mean is continuous for the supremum norm. -/
instance : ContinuousLinearMapClass (AddMean A) ℝ (AddUCB A) ℝ where
  map_continuous m := m.lipschitzWith.continuous

variable (A) in
/-- Evaluation at a point of `A` is a mean on `AddUCB A`. -/
def eval (x : A) : AddMean A :=
  mk₀ ((BoundedContinuousFunction.evalCLM ℝ x).toLinearMap ∘ₗ (addUCB A).val.toLinearMap)
    (fun _ hf => AddUCB.le_def.1 hf x) rfl

@[simp]
theorem eval_apply (x : A) (f : AddUCB A) : eval A x f = (f : A →ᵇ ℝ) x :=
  (rfl)

instance : Nonempty (AddMean A) :=
  ⟨eval A 0⟩

/-- A mean `m` on `AddUCB A` is left invariant when `m (L_a f) = m f` for every `a : A` and `f`,
where `(L_a f)(x) = f (-a + x)`. -/
def IsLeftInvariant (m : AddMean A) : Prop :=
  ∀ (a : A) (f : AddUCB A), m (AddUCB.leftTranslation a f) = m f

theorem isLeftInvariant_iff {m : AddMean A} :
    m.IsLeftInvariant ↔ ∀ (a : A) (f : AddUCB A), m (AddUCB.leftTranslation a f) = m f :=
  Iff.rfl

@[simp]
theorem IsLeftInvariant.apply_leftTranslation {m : AddMean A} (hm : m.IsLeftInvariant) (a : A)
    (f : AddUCB A) : m (AddUCB.leftTranslation a f) = m f :=
  hm a f

section Map

variable {B : Type*} [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- Pushforward `f ↦ m (f ∘ φ)` of a mean on `AddUCB A` along a continuous additive homomorphism
`φ : A →ₜ+ B`. -/
def map (φ : A →ₜ+ B) (m : AddMean A) : AddMean B :=
  mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.compRightAlgHom φ).toLinearMap)
    (fun f hf => map_nonneg m (by simpa using AddUCB.monotone_compRightAlgHom φ hf)) (by simp)

@[simp]
theorem map_apply (φ : A →ₜ+ B) (m : AddMean A) (f : AddUCB B) :
    m.map φ f = m (AddUCB.compRightAlgHom φ f) :=
  mk₀_apply _ _ _ f

@[simp]
theorem map_id (m : AddMean A) : m.map (ContinuousAddMonoidHom.id A) = m :=
  ext fun _ => by simp

@[simp]
theorem map_map {C : Type*} [AddGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]
    (ψ : B →ₜ+ C) (φ : A →ₜ+ B) (m : AddMean A) :
    (m.map φ).map ψ = m.map (ψ.comp φ) :=
  ext fun _ => by simp [AddUCB.compRightAlgHom_comp]

theorem IsLeftInvariant.map_apply_leftTranslation {m : AddMean A} (hm : m.IsLeftInvariant)
    (φ : A →ₜ+ B) (a : A) (f : AddUCB B) :
    m.map φ (AddUCB.leftTranslation (φ a) f) = m.map φ f := by
  rw [map_apply, map_apply, AddUCB.compRightAlgHom_leftTranslation, hm]

/-- Pushforward along a continuous additive homomorphism with dense range preserves left
invariance. -/
theorem IsLeftInvariant.map {m : AddMean A} (hm : m.IsLeftInvariant) {φ : A →ₜ+ B}
    (hφ : DenseRange φ) : (m.map φ).IsLeftInvariant := by
  intro b f
  have hc : Continuous fun k : B => m.map φ (AddUCB.leftTranslation k f) :=
    (map_continuous (m.map φ)).comp (AddUCB.continuous_leftTranslation_apply f)
  exact hφ.induction_on (p := fun k => m.map φ (AddUCB.leftTranslation k f) = m.map φ f) b
    (isClosed_eq hc continuous_const) fun a => hm.map_apply_leftTranslation φ a f

end Map

variable (A) in
/-- Bijection between means on `AddUCB A` and means on `UCB (Multiplicative A)`. -/
def toMultiplicativeEquiv : AddMean A ≃ Mean (Multiplicative A) where
  toFun m := Mean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.toMultiplicativeAlgEquiv A).symm.toLinearMap)
    (fun f hf => map_nonneg m <|
      AddUCB.le_def.2 fun x => by simpa using UCB.le_def.1 hf (Multiplicative.ofAdd x))
    (by simp)
  invFun m := mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.toMultiplicativeAlgEquiv A).toLinearMap)
    (fun f hf => map_nonneg m <|
      UCB.le_def.2 fun x => by simpa using AddUCB.le_def.1 hf x.toAdd)
    (by simp)
  left_inv m := ext fun f => by simp [Mean.mk₀_apply, mk₀_apply]
  right_inv m := Mean.ext fun f => by simp [Mean.mk₀_apply, mk₀_apply]

@[simp]
theorem toMultiplicativeEquiv_apply (m : AddMean A) (f : UCB (Multiplicative A)) :
    toMultiplicativeEquiv A m f = m ((AddUCB.toMultiplicativeAlgEquiv A).symm f) :=
  Mean.mk₀_apply _ _ _ f

@[simp]
theorem toMultiplicativeEquiv_symm_apply (m : Mean (Multiplicative A)) (f : AddUCB A) :
    (toMultiplicativeEquiv A).symm m f = m (AddUCB.toMultiplicativeAlgEquiv A f) :=
  mk₀_apply _ _ _ f

/-- `toMultiplicativeEquiv` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_toMultiplicativeEquiv_iff {m : AddMean A} :
    (toMultiplicativeEquiv A m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [Mean.isLeftInvariant_iff, isLeftInvariant_iff]
  constructor
  · intro hm a f
    simpa using hm (Multiplicative.ofAdd a) (AddUCB.toMultiplicativeAlgEquiv A f)
  · intro hm g f
    simpa using hm g.toAdd ((AddUCB.toMultiplicativeAlgEquiv A).symm f)

end AddMean

end AddMean

section ToAdditiveMean

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace Mean

variable (G) in
/-- Bijection between means on `UCB G` and means on `AddUCB (Additive G)`. -/
def toAdditiveEquiv : Mean G ≃ AddMean (Additive G) where
  toFun m := AddMean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.toAdditiveAlgEquiv G).symm.toLinearMap)
    (fun f hf => map_nonneg m <|
      UCB.le_def.2 fun x => by simpa using AddUCB.le_def.1 hf (Additive.ofMul x))
    (by simp)
  invFun m := mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.toAdditiveAlgEquiv G).toLinearMap)
    (fun f hf => map_nonneg m <|
      AddUCB.le_def.2 fun x => by simpa using UCB.le_def.1 hf x.toMul)
    (by simp)
  left_inv m := ext fun f => by simp [Mean.mk₀_apply, AddMean.mk₀_apply]
  right_inv m := AddMean.ext fun f => by simp [Mean.mk₀_apply, AddMean.mk₀_apply]

@[simp]
theorem toAdditiveEquiv_apply (m : Mean G) (f : AddUCB (Additive G)) :
    toAdditiveEquiv G m f = m ((UCB.toAdditiveAlgEquiv G).symm f) :=
  AddMean.mk₀_apply _ _ _ f

@[simp]
theorem toAdditiveEquiv_symm_apply (m : AddMean (Additive G)) (f : UCB G) :
    (toAdditiveEquiv G).symm m f = m (UCB.toAdditiveAlgEquiv G f) :=
  mk₀_apply _ _ _ f

/-- `toAdditiveEquiv` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_toAdditiveEquiv_iff {m : Mean G} :
    (toAdditiveEquiv G m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [AddMean.isLeftInvariant_iff, isLeftInvariant_iff]
  constructor
  · intro hm g f
    have htr : (UCB.toAdditiveAlgEquiv G).symm
        (AddUCB.leftTranslation (Additive.ofMul g) (UCB.toAdditiveAlgEquiv G f)) =
        UCB.leftTranslation g f := by
      apply (UCB.toAdditiveAlgEquiv G).injective
      simp
    simpa [htr] using hm (Additive.ofMul g) (UCB.toAdditiveAlgEquiv G f)
  · intro hm a f
    have htr : (UCB.toAdditiveAlgEquiv G).symm (AddUCB.leftTranslation a f) =
        UCB.leftTranslation a.toMul ((UCB.toAdditiveAlgEquiv G).symm f) := by
      apply (UCB.toAdditiveAlgEquiv G).injective
      simp
    simpa [htr] using hm a.toMul ((UCB.toAdditiveAlgEquiv G).symm f)

end Mean

end ToAdditiveMean

section AddAmenable

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

variable (A) in
/-- An additive topological group `A` is amenable when `AddUCB A` carries a left-invariant mean. -/
class AddAmenable : Prop where
  /-- An amenable additive group has a left-invariant mean on `AddUCB A`. -/
  exists_isLeftInvariant : ∃ m : AddMean A, m.IsLeftInvariant

variable (A) in
/-- An additive topological group is amenable exactly when `AddUCB A` carries a left-invariant
mean. -/
theorem addAmenable_iff : AddAmenable A ↔ ∃ m : AddMean A, m.IsLeftInvariant :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- `Multiplicative A` is amenable if and only if the additive topological group `A` is
amenable. -/
@[simp]
theorem amenable_multiplicative_iff : Amenable (Multiplicative A) ↔ AddAmenable A := by
  rw [amenable_iff, addAmenable_iff]
  exact ((AddMean.toMultiplicativeEquiv A).exists_congr
    fun _ => AddMean.isLeftInvariant_toMultiplicativeEquiv_iff.symm).symm

/-- `Additive G` is amenable if and only if the topological group `G` is amenable. -/
@[simp]
theorem addAmenable_additive_iff {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : AddAmenable (Additive G) ↔ Amenable G := by
  rw [addAmenable_iff, amenable_iff]
  exact ((Mean.toAdditiveEquiv G).exists_congr
    fun _ => Mean.isLeftInvariant_toAdditiveEquiv_iff.symm).symm

instance [AddAmenable A] : Amenable (Multiplicative A) :=
  amenable_multiplicative_iff.2 ‹_›

instance {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Amenable G] :
    AddAmenable (Additive G) :=
  addAmenable_additive_iff.2 ‹_›

/-- The target of a continuous additive homomorphism with dense range from an amenable additive
topological group is amenable; in particular, so is the image under a surjective continuous
additive homomorphism. -/
theorem AddAmenable.of_denseRange {B : Type*} [AddGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [AddAmenable A] (φ : A →ₜ+ B) (hφ : DenseRange φ) :
    AddAmenable B :=
  have ⟨m, hm⟩ := AddAmenable.exists_isLeftInvariant (A := A)
  ⟨⟨m.map φ, hm.map hφ⟩⟩

/-- Every quotient of an amenable additive topological group by a normal additive subgroup is
amenable. -/
instance AddAmenable.quotient [AddAmenable A] (N : AddSubgroup A) [N.Normal] :
    AddAmenable (A ⧸ N) :=
  .of_denseRange ⟨QuotientAddGroup.mk' N, continuous_quot_mk⟩
    (QuotientAddGroup.mk'_surjective N).denseRange

omit [TopologicalSpace A] [IsTopologicalAddGroup A] in
/-- Additive amenability passes from a finer additive group topology to a coarser one. -/
theorem AddAmenable.of_le {t₁ t₂ : TopologicalSpace A}
    [@IsTopologicalAddGroup A t₁ _] [@IsTopologicalAddGroup A t₂ _] (h : t₁ ≤ t₂)
    (ha : @AddAmenable A _ t₁ _) : @AddAmenable A _ t₂ _ := by
  let φ : @ContinuousAddMonoidHom A A _ _ t₁ t₂ :=
    @ContinuousAddMonoidHom.mk A A _ _ t₁ t₂ (AddMonoidHom.id A) (continuous_id_of_le h)
  exact @AddAmenable.of_denseRange A _ t₁ _ A _ t₂ _ ha φ
    (@Function.Surjective.denseRange A t₂ A _ fun x => ⟨x, AddMonoidHom.id_apply A x⟩)

/-- An abstract additive group which is amenable with the discrete topology is amenable with any
additive group topology. -/
theorem AddAmenable.of_discrete
    (h : letI : TopologicalSpace A := ⊥;
      letI := discreteTopology_bot A; AddAmenable A) :
    AddAmenable A := by
  let : @DiscreteTopology A ⊥ := discreteTopology_bot A
  exact AddAmenable.of_le (t₁ := ⊥) bot_le h

/-- A finite additive topological group is amenable, for any additive group topology. -/
instance (priority := 100) AddAmenable.of_finite [Finite A] : AddAmenable A :=
  amenable_multiplicative_iff.1 inferInstance

/-- An additive group with Følner sets is amenable, for every additive group topology. -/
theorem AddAmenable.of_hasAddFoelnerSets (h : HasAddFoelnerSets A) : AddAmenable A :=
  amenable_multiplicative_iff.1 (.of_hasFoelnerSets (hasFoelnerSets_multiplicative_iff.2 h))

/-- An additive topological group is amenable when it has eventually nonempty finite sets `F i`
with `|(a +ᵥ F i) △ F i| / |F i| → 0` for every `a`, along a nontrivial filter. -/
theorem AddAmenable.of_tendsto_card_vadd_symmDiff_div_card [DecidableEq A] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Finset A} (hne : ∀ᶠ i in l, (F i).Nonempty)
    (h : ∀ a : A, Tendsto (fun i => (#((a +ᵥ F i) ∆ F i) : ℝ) / #(F i)) l (𝓝 0)) :
    AddAmenable A :=
  .of_hasAddFoelnerSets (.of_tendsto_card_vadd_symmDiff_div_card hne h)

/-- An additive topological group is amenable when it has an additive Følner family for counting
measure, along a nontrivial filter. -/
theorem AddAmenable.of_isAddFoelner [MeasurableSpace A] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Set A}
    (hF : IsAddFoelner A MeasureTheory.Measure.count l F) : AddAmenable A := by
  classical
  exact .of_hasAddFoelnerSets
    (hasAddFoelnerSets_iff.2 fun K _ hε => hF.exists_finset_card_vadd_symmDiff_lt K hε)

/-- The product of two amenable additive topological groups is amenable. -/
instance AddAmenable.prod {B : Type*} [AddGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [AddAmenable A] [AddAmenable B] : AddAmenable (A × B) :=
  amenable_multiplicative_iff.1 <|
    (ContinuousMulEquiv.prodMultiplicative A B).amenable_iff.2 inferInstance

/-- A product of two additive topological groups is amenable exactly when both factors are. -/
theorem addAmenable_prod_iff (A B : Type*) [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] :
    AddAmenable (A × B) ↔ AddAmenable A ∧ AddAmenable B := by
  rw [← amenable_multiplicative_iff, (ContinuousMulEquiv.prodMultiplicative A B).amenable_iff,
    amenable_prod_iff, amenable_multiplicative_iff, amenable_multiplicative_iff]

/-- An additive topological group `A` is amenable if, for a family of continuous additive
homomorphisms `φ i : K i →ₜ+ A` from amenable additive topological groups, every finite subset of
`A` lies in the range of some `φ i`. -/
theorem AddAmenable.of_forall_finset_subset_range {ι : Type*} {K : ι → Type*}
    [∀ i, AddGroup (K i)] [∀ i, TopologicalSpace (K i)] [∀ i, IsTopologicalAddGroup (K i)]
    [∀ i, AddAmenable (K i)] (φ : ∀ i, K i →ₜ+ A)
    (h : ∀ s : Finset A, ∃ i, (s : Set A) ⊆ Set.range (φ i)) : AddAmenable A := by
  classical
  let φ' (i : ι) : Multiplicative (K i) →ₜ* Multiplicative A :=
    ⟨(φ i).toAddMonoidHom.toMultiplicative,
      continuous_ofAdd.comp ((φ i).continuous.comp continuous_toAdd)⟩
  refine amenable_multiplicative_iff.1 (.of_forall_finset_subset_range φ' fun s => ?_)
  obtain ⟨i, hi⟩ := h (s.image Multiplicative.toAdd)
  refine ⟨i, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hi (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx))
  exact ⟨Multiplicative.ofAdd y, by simp [φ', hy]⟩

/-- The product of a family of amenable additive topological groups is amenable. -/
instance AddAmenable.pi {ι : Type*} {K : ι → Type*} [∀ i, AddGroup (K i)]
    [∀ i, TopologicalSpace (K i)] [∀ i, IsTopologicalAddGroup (K i)] [∀ i, AddAmenable (K i)] :
    AddAmenable (∀ i, K i) := by
  classical
  let H : AddSubgroup (∀ i, K i) :=
    { carrier := {x : ∀ i, K i | {i | x i ≠ 0}.Finite}
      zero_mem' := by simp
      add_mem' {x y} hx hy := (hx.union hy).subset fun i hi => by
        simp only [Set.mem_union, Set.mem_ofPred_eq, Pi.add_apply] at hi ⊢
        contrapose! hi
        simp [hi]
      neg_mem' {x} hx := by simpa using hx }
  have hfin (s : Finset ι) : AddAmenable (∀ i : s, K i) :=
    amenable_multiplicative_iff.1 <|
      (ContinuousMulEquiv.piMultiplicative fun i : s => K i).amenable_iff.2 inferInstance
  let φ (s : Finset ι) : (∀ i : s, K i) →+ (∀ i, K i) :=
    { toFun x i := if hi : i ∈ s then x ⟨i, hi⟩ else 0
      map_zero' := by ext i; split_ifs <;> rfl
      map_add' x y := by ext i; by_cases hi : i ∈ s <;> simp [hi] }
  have hφc (s : Finset ι) : Continuous (φ s) :=
    continuous_pi fun i => by
      by_cases hi : i ∈ s
      · simpa [φ, hi] using continuous_apply (⟨i, hi⟩ : s)
      · simpa [φ, hi] using continuous_const
  let ψ (s : Finset ι) : (∀ i : s, K i) →ₜ+ H :=
    ⟨(φ s).codRestrict H fun x => s.finite_toSet.subset fun i hi =>
        Finset.mem_coe.2 (by by_contra hni; exact hi (by simp [φ, hni])),
      (hφc s).subtype_mk _⟩
  have : AddAmenable H := .of_forall_finset_subset_range ψ fun F => by
    let s : Finset ι := F.biUnion fun x => x.2.toFinset
    refine ⟨s, fun x hx => ⟨fun i => x.1 i.1, Subtype.ext <| funext fun i => ?_⟩⟩
    change (if _ : i ∈ s then x.1 i else 0) = x.1 i
    split_ifs with hi
    · rfl
    · symm
      by_contra hne
      exact hi (Finset.mem_biUnion.2 ⟨x, hx, x.2.mem_toFinset.2 hne⟩)
  refine .of_denseRange ⟨H.subtype, continuous_subtype_val⟩ fun y => ?_
  have ht : Tendsto (fun s : Finset ι => (fun i => if i ∈ s then y i else 0 : ∀ i, K i))
      atTop (𝓝 y) := tendsto_pi_nhds.2 fun i => tendsto_const_nhds.congr' <| by
    filter_upwards [eventually_ge_atTop {i}] with s hs
    simp [hs (Finset.mem_singleton_self i)]
  have hmem : ∀ᶠ s : Finset ι in atTop,
      (fun i => if i ∈ s then y i else 0 : ∀ i, K i) ∈ (H : Set (∀ i, K i)) :=
    .of_forall fun s => s.finite_toSet.subset fun i hi =>
      Finset.mem_coe.2 (by by_contra hni; exact hi (by simp [hni]))
  change y ∈ closure (Set.range (Subtype.val : H → ∀ i, K i))
  rw [Subtype.range_coe]
  exact mem_closure_of_tendsto ht hmem

/-- A product of additive topological groups is amenable exactly when every factor is. -/
theorem addAmenable_pi_iff {ι : Type*} {K : ι → Type*} [∀ i, AddGroup (K i)]
    [∀ i, TopologicalSpace (K i)] [∀ i, IsTopologicalAddGroup (K i)] :
    AddAmenable (∀ i, K i) ↔ ∀ i, AddAmenable (K i) :=
  ⟨fun _ i => .of_denseRange ⟨Pi.evalAddMonoidHom K i, continuous_apply i⟩
      (Function.surjective_eval i).denseRange,
    fun _ => inferInstance⟩

/-- The supremum `⨆ i, H i` of a directed family of amenable additive subgroups `H i` of an
additive topological group is an amenable additive subgroup. -/
theorem addAmenable_iSup_of_directed {ι : Type*} {H : ι → AddSubgroup A}
    (hH : Directed (· ≤ ·) H) [∀ i, AddAmenable (H i)] : AddAmenable ↥(⨆ i, H i) := by
  classical
  obtain hι | hι := isEmpty_or_nonempty ι
  · rw [iSup_of_empty]
    infer_instance
  refine .of_forall_finset_subset_range
    (fun i => ⟨AddSubgroup.inclusion (le_iSup H i), continuous_subtype_val.subtype_mk _⟩)
    fun s => ?_
  have hH' : Directed (· ⊆ ·) fun i => (H i : Set A) :=
    hH.mono_comp _ fun _ _ => SetLike.coe_subset_coe.2
  obtain ⟨i, hi⟩ := hH'.exists_mem_subset_of_finset_subset_biUnion (s := s.image Subtype.val) <| by
    rw [Finset.coe_image, ← AddSubgroup.coe_iSup_of_directed hH]
    exact Set.image_subset_iff.2 fun x _ => x.2
  exact ⟨i, fun x hx => ⟨⟨x, hi (Finset.mem_image_of_mem _ hx)⟩, rfl⟩⟩

/-- An additive topological group which is the supremum of a directed family of amenable additive
subgroups is amenable. -/
theorem AddAmenable.of_directed_of_iSup_eq_top {ι : Type*} {H : ι → AddSubgroup A}
    (hH : Directed (· ≤ ·) H) (htop : ⨆ i, H i = ⊤) [∀ i, AddAmenable (H i)] : AddAmenable A :=
  have := addAmenable_iSup_of_directed hH
  .of_denseRange ⟨(⨆ i, H i).subtype, continuous_subtype_val⟩
    (Function.Surjective.denseRange fun x => ⟨⟨x, htop ▸ AddSubgroup.mem_top x⟩, rfl⟩)

/-- An additive topological group all of whose finitely generated additive subgroups are amenable
is amenable. -/
theorem AddAmenable.of_forall_fg (h : ∀ K : AddSubgroup A, K.FG → AddAmenable K) :
    AddAmenable A := by
  have : ∀ K : {K : AddSubgroup A // K.FG}, AddAmenable K.1 := fun K => h K.1 K.2
  refine .of_forall_finset_subset_range
    (fun K : {K : AddSubgroup A // K.FG} => ⟨K.1.subtype, continuous_subtype_val⟩) fun s => ?_
  refine ⟨⟨AddSubgroup.closure s, (AddGroup.fg_iff_addSubgroup_fg _).1 inferInstance⟩,
    fun x hx => ?_⟩
  exact ⟨⟨x, AddSubgroup.subset_closure hx⟩, rfl⟩

end AddAmenable

section DiscreteAddAmenable

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- An amenable discrete additive group has Følner sets. -/
theorem AddAmenable.hasAddFoelnerSets [AddAmenable A] : HasAddFoelnerSets A := by
  have : DiscreteTopology (Multiplicative A) := Homeomorph.ofAdd.symm.discreteTopology
  exact hasFoelnerSets_multiplicative_iff.1 Amenable.hasFoelnerSets

/-- A discrete additive group is amenable exactly when it has Følner sets. -/
theorem addAmenable_iff_hasAddFoelnerSets : AddAmenable A ↔ HasAddFoelnerSets A :=
  ⟨fun _ => AddAmenable.hasAddFoelnerSets, .of_hasAddFoelnerSets⟩

/-- A discrete additive group is amenable exactly when for every finite `K ⊆ A` and `ε > 0` there is
a finite nonempty `F ⊆ A` with `|(a +ᵥ F) △ F| < ε · |F|` for all `a ∈ K`. -/
theorem addAmenable_iff_exists_finset [DecidableEq A] :
    AddAmenable A ↔ ∀ K : Finset A, ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset A, F.Nonempty ∧ ∀ a ∈ K, (#((a +ᵥ F) ∆ F) : ℝ) < ε * #F := by
  rw [addAmenable_iff_hasAddFoelnerSets, hasAddFoelnerSets_iff]

/-- A countable discrete additive group is amenable exactly when it admits an additive Følner
sequence of finite nonempty sets. -/
theorem addAmenable_iff_exists_seq [DecidableEq A] [Countable A] :
    AddAmenable A ↔ ∃ F : ℕ → Finset A, (∀ n, (F n).Nonempty) ∧
      ∀ a : A, Tendsto (fun n => (#((a +ᵥ F n) ∆ F n) : ℝ) / #(F n)) atTop (𝓝 0) := by
  rw [addAmenable_iff_hasAddFoelnerSets, hasAddFoelnerSets_iff_exists_seq]

/-- An additive group `B` embedding by an injective homomorphism into an amenable discrete additive
group is amenable, for every additive group topology on `B`. -/
theorem AddAmenable.of_injective {B : Type*} [AddGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [AddAmenable A] (φ : B →+ A) (hφ : Function.Injective φ) :
    AddAmenable B := by
  have : DiscreteTopology (Multiplicative A) := Homeomorph.ofAdd.symm.discreteTopology
  exact amenable_multiplicative_iff.1 <|
    Amenable.of_injective (G := Multiplicative A) φ.toMultiplicative fun x y hxy =>
      Multiplicative.toAdd.injective <| hφ <| Multiplicative.ofAdd.injective hxy

/-- Every additive subgroup of an amenable discrete additive group is amenable. -/
instance AddAmenable.addSubgroup [AddAmenable A] (K : AddSubgroup A) : AddAmenable K :=
  .of_injective K.subtype K.subtype_injective

/-- If `ψ : B →+ A` and `φ : A →+ C` are additive homomorphisms with `φ.ker ≤ ψ.range`, where `B`
and `C` are amenable discrete additive groups, then `A` is amenable for every additive group
topology on `A`. -/
theorem AddAmenable.of_ker_le_range {A B C : Type*}
    [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [AddGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [AddGroup C] [TopologicalSpace C] [DiscreteTopology C] [AddAmenable B] [AddAmenable C]
    (ψ : B →+ A) (φ : A →+ C) (h : φ.ker ≤ ψ.range) : AddAmenable A := by
  refine AddAmenable.of_discrete ?_
  let _ : TopologicalSpace A := ⊥
  let _ : DiscreteTopology A := discreteTopology_bot A
  have : DiscreteTopology (Multiplicative A) := Homeomorph.ofAdd.symm.discreteTopology
  have : DiscreteTopology (Multiplicative B) := Homeomorph.ofAdd.symm.discreteTopology
  have : DiscreteTopology (Multiplicative C) := Homeomorph.ofAdd.symm.discreteTopology
  refine amenable_multiplicative_iff.1 <|
    Amenable.of_ker_le_range ψ.toMultiplicative φ.toMultiplicative fun x hx => ?_
  have hx' : x.toAdd ∈ φ.ker := by
    simpa [MonoidHom.mem_ker, AddMonoidHom.mem_ker] using hx
  obtain ⟨b, hb⟩ := h hx'
  exact ⟨Multiplicative.ofAdd b, by simp [hb]⟩

end DiscreteAddAmenable

end TauCeti

namespace ContinuousAddEquiv

open TauCeti

variable {A B : Type*}
  [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- Additive amenability is invariant under topological additive group isomorphisms. -/
theorem addAmenable_iff (e : A ≃ₜ+ B) : AddAmenable A ↔ AddAmenable B := by
  rw [← amenable_multiplicative_iff, ← amenable_multiplicative_iff (A := B),
    e.toMultiplicative.amenable_iff]

end ContinuousAddEquiv

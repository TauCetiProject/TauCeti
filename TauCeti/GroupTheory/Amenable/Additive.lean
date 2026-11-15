/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ContinuousMulEquiv
public import TauCeti.Topology.Algebra.Group.UCB.Additive
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
public import TauCeti.GroupTheory.Amenable.DirectedUnion
public import TauCeti.GroupTheory.Amenable.Extension
public import TauCeti.GroupTheory.Amenable.Prod

/-!
# Additive amenable topological groups

For a topological additive group `A`, an *additive mean* on `TauCeti.AddUCB A` is a positive real
linear functional `m` taking the value `1` at `1`. It is *left invariant* when `m (L_a f) = m f`
for every `a : A` and `f : AddUCB A`, where `(L_a f)(x) = f (-a + x)`. A topological additive group
is *amenable* (`TauCeti.AddAmenable A`) when `AddUCB A` carries a left-invariant additive mean.

Precomposition with `Multiplicative.toAdd` identifies `AddUCB A` with
`TauCeti.UCB (Multiplicative A)` as an ordered normed unital ℝ-algebra intertwining additive and
multiplicative left translations (`TauCeti.AddUCB.equivMultiplicative`). Dually, means on `AddUCB A`
correspond bijectively to means on `UCB (Multiplicative A)` preserving left invariance, so
`AddAmenable A ↔ Amenable (Multiplicative A)`. This transports the closure properties of
amenability—dense-range homomorphisms, finite groups, binary and finite products, subgroups and
extensions of discrete groups, directed unions, and Følner characterizations—to additive groups
without duplicating their proofs.

## Main definitions

* `TauCeti.AddMean A`: a positive normalized linear functional on `AddUCB A`.
* `TauCeti.AddMean.IsLeftInvariant`: `m (L_a f) = m f` for all `a` and `f`.
* `TauCeti.AddMean.map φ`: pushforward of additive means along `φ : A →ₜ+ B`.
* `TauCeti.AddMean.equivMultiplicative`: the bijection `AddMean A ≃ Mean (Multiplicative A)`.
* `TauCeti.Mean.equivAdditive`: the bijection `Mean G ≃ AddMean (Additive G)`.
* `TauCeti.AddAmenable A`: `AddUCB A` carries a left-invariant additive mean.

## Main results

* `TauCeti.addAmenable_iff_amenable_multiplicative`,
  `TauCeti.amenable_iff_addAmenable_additive`: compatibility of `AddAmenable` and `Amenable` across
  `Multiplicative` and `Additive`.
* `TauCeti.AddAmenable.of_denseRange`, `ContinuousAddEquiv.addAmenable_iff`,
  `TauCeti.AddAmenable.of_finite`, `TauCeti.AddAmenable.prod`, `TauCeti.AddAmenable.pi`:
  permanence properties for topological additive groups.
* `TauCeti.AddAmenable.addSubgroup`, `TauCeti.addAmenable_iff_addSubgroup_quotient`,
  `TauCeti.AddAmenable.of_forall_fg`: permanence under subgroups, discrete extensions, and directed
  unions of finitely generated subgroups.
* `TauCeti.addAmenable_iff_hasAddFoelnerSets`: a discrete additive group is amenable if and only if
  it has additive Følner sets.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1, Proposition G.2.2,
  and Theorem G.5.1.
* A. Garrido, *An introduction to amenable groups*, Proposition 2.2 and Theorem 3.6.
-/

public section

noncomputable section

open Filter Finset Multiplicative Additive
open scoped BoundedContinuousFunction Pointwise symmDiff

namespace TauCeti

variable {A B C : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]

variable (A) in
/-- A mean on `AddUCB A`: a positive real linear functional taking the value `1` at the constant
function `1`. -/
structure AddMean extends AddUCB A →ₚ[ℝ] ℝ where
  /-- A mean takes the value `1` at the constant function `1`. -/
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

/-- An additive mean built from a linear functional which is nonnegative on nonnegative functions
and takes the value `1` at `1`. -/
def mk₀ (φ : AddUCB A →ₗ[ℝ] ℝ) (hφ : ∀ f, 0 ≤ f → 0 ≤ φ f) (h₁ : φ 1 = 1) : AddMean A :=
  { PositiveLinearMap.mk₀ φ hφ with map_one' := h₁ }

@[simp]
theorem mk₀_apply (φ : AddUCB A →ₗ[ℝ] ℝ) (hφ : ∀ f, 0 ≤ f → 0 ≤ φ f) (h₁ : φ 1 = 1)
    (f : AddUCB A) : mk₀ φ hφ h₁ f = φ f :=
  (rfl)

variable (m : AddMean A)

/-- An additive mean takes the value `c` at the constant function `c`. -/
@[simp]
theorem map_algebraMap (c : ℝ) : m (algebraMap ℝ (AddUCB A) c) = c := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- An additive mean of a function is bounded in absolute value by its supremum norm. -/
theorem abs_apply_le_norm (f : AddUCB A) : |m f| ≤ ‖f‖ := by
  simpa using PositiveLinearMap.abs_apply_le_mul_norm m (AddUCB.le_norm_smul_one (A := A)) f

/-- An additive mean is `1`-Lipschitz for the supremum norm. -/
theorem lipschitzWith : LipschitzWith 1 m := by
  simpa using
    PositiveLinearMap.lipschitzWith_of_forall_le_norm_smul m (AddUCB.le_norm_smul_one (A := A))

/-- An additive mean is continuous for the supremum norm. -/
instance : ContinuousLinearMapClass (AddMean A) ℝ (AddUCB A) ℝ where
  map_continuous m := m.lipschitzWith.continuous

/-- The continuous linear functional underlying an additive mean. -/
def toContinuousLinearMap : AddUCB A →L[ℝ] ℝ where
  toLinearMap := m.toPositiveLinearMap.toLinearMap
  cont := map_continuous m

@[simp]
theorem coe_toContinuousLinearMap : ⇑m.toContinuousLinearMap = ⇑m :=
  (rfl)

/-- An additive mean has operator norm one. -/
@[simp]
theorem norm_toContinuousLinearMap : ‖m.toContinuousLinearMap‖ = 1 := by
  rw [m.toContinuousLinearMap.opNorm_eq_apply_of_monotone (OrderHomClass.mono m)
    AddUCB.le_norm_smul_one norm_one.le]
  simp

variable (A) in
/-- Evaluation at a point of `A` is an additive mean on `AddUCB A`. -/
def eval (x : A) : AddMean A :=
  mk₀ ((BoundedContinuousFunction.evalCLM ℝ x).toLinearMap ∘ₗ (addUcb A).val.toLinearMap)
    (fun _ hf => AddUCB.le_def.1 hf x) rfl

@[simp]
theorem eval_apply (x : A) (f : AddUCB A) : eval A x f = (f : A →ᵇ ℝ) x :=
  (rfl)

instance : Nonempty (AddMean A) :=
  ⟨eval A 0⟩

/-! ### Left invariance and pushforward -/

/-- An additive mean `m` on `AddUCB A` is left invariant when `m (L_a f) = m f` for every `a` and
`f`, where `(L_a f)(x) = f (-a + x)`. -/
def IsLeftInvariant (m : AddMean A) : Prop :=
  ∀ (a : A) (f : AddUCB A), m (AddUCB.leftTranslation a f) = m f

/-- The defining property of a left-invariant additive mean. -/
theorem isLeftInvariant_iff {m : AddMean A} :
    m.IsLeftInvariant ↔ ∀ (a : A) (f : AddUCB A), m (AddUCB.leftTranslation a f) = m f :=
  Iff.rfl

/-- A left-invariant additive mean takes the same value at a function and at its left translates. -/
@[simp]
theorem IsLeftInvariant.apply_leftTranslation {m : AddMean A} (hm : m.IsLeftInvariant) (a : A)
    (f : AddUCB A) : m (AddUCB.leftTranslation a f) = m f :=
  hm a f

/-- The pushforward `f ↦ m (f ∘ φ)` of an additive mean `m` on `AddUCB A` along a continuous
additive homomorphism `φ : A →ₜ+ B`, as an additive mean on `AddUCB B`. -/
def map (φ : A →ₜ+ B) (m : AddMean A) : AddMean B :=
  mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.compRightAlgHom φ).toLinearMap)
    (fun f hf => map_nonneg m (by simpa using AddUCB.monotone_compRightAlgHom φ hf)) (by simp)

@[simp]
theorem map_apply (φ : A →ₜ+ B) (m : AddMean A) (f : AddUCB B) :
    m.map φ f = m (AddUCB.compRightAlgHom φ f) :=
  mk₀_apply _ _ _ f

/-- The pushforward along the identity is the identity. -/
@[simp]
theorem map_id (m : AddMean A) : m.map (ContinuousAddMonoidHom.id A) = m :=
  ext fun f => by simp

/-- Pushing forward along `φ` and then along `ψ` is pushing forward along `ψ ∘ φ`. -/
@[simp]
theorem map_map (ψ : B →ₜ+ C) (φ : A →ₜ+ B) (m : AddMean A) :
    (m.map φ).map ψ = m.map (ψ.comp φ) :=
  ext fun f => by simp [AddUCB.compRightAlgHom_comp]

/-- The pushforward of a left-invariant additive mean along `φ` is invariant under left translation
by elements in the range of `φ`. -/
theorem IsLeftInvariant.map_apply_leftTranslation {m : AddMean A} (hm : m.IsLeftInvariant)
    (φ : A →ₜ+ B) (a : A) (f : AddUCB B) :
    m.map φ (AddUCB.leftTranslation (φ a) f) = m.map φ f := by
  rw [map_apply, map_apply, AddUCB.compRightAlgHom_leftTranslation, hm]

/-- The pushforward of a left-invariant additive mean along a continuous additive homomorphism with
dense range is left invariant. -/
theorem IsLeftInvariant.map {m : AddMean A} (hm : m.IsLeftInvariant) {φ : A →ₜ+ B}
    (hφ : DenseRange φ) : (m.map φ).IsLeftInvariant := by
  intro b f
  have hc : Continuous fun k : B => m.map φ (AddUCB.leftTranslation k f) :=
    (map_continuous (m.map φ)).comp (AddUCB.continuous_leftTranslation_apply f)
  exact hφ.induction_on (p := fun k => m.map φ (AddUCB.leftTranslation k f) = m.map φ f) b
    (isClosed_eq hc continuous_const) fun a => hm.map_apply_leftTranslation φ a f

/-! ### Equivalence with multiplicative means -/

/-- Pullback along `AddUCB.equivMultiplicative` identifies additive means on `AddUCB A` with
multiplicative means on `UCB (Multiplicative A)`. -/
def equivMultiplicative : AddMean A ≃ Mean (Multiplicative A) where
  toFun m := Mean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ AddUCB.equivMultiplicative.symm.toLinearMap)
    (fun _ hf => by
      simp only [LinearMap.comp_apply, PositiveLinearMap.coe_toLinearMap, coe_toPositiveLinearMap,
        AlgEquiv.toLinearMap_apply]
      exact map_nonneg m (by
        simpa only [map_zero] using
          AddUCB.equivMultiplicative_symm_le_equivMultiplicative_symm_iff.2 hf))
    (by simp)
  invFun m := mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ AddUCB.equivMultiplicative.toLinearMap)
    (fun _ hf => by
      simp only [LinearMap.comp_apply, PositiveLinearMap.coe_toLinearMap,
        Mean.coe_toPositiveLinearMap, AlgEquiv.toLinearMap_apply]
      exact map_nonneg m (by
        simpa only [map_zero] using
          AddUCB.equivMultiplicative_le_equivMultiplicative_iff.2 hf))
    (by simp)
  left_inv m := ext fun f => by simp [Mean.mk₀_apply]
  right_inv m := Mean.ext fun f => by simp [Mean.mk₀_apply]

@[simp]
theorem equivMultiplicative_apply (m : AddMean A) (f : UCB (Multiplicative A)) :
    equivMultiplicative m f = m (AddUCB.equivMultiplicative.symm f) :=
  Mean.mk₀_apply _ _ _ f

@[simp]
theorem equivMultiplicative_symm_apply (m : Mean (Multiplicative A)) (f : AddUCB A) :
    equivMultiplicative.symm m f = m (AddUCB.equivMultiplicative f) :=
  (rfl)

/-- `equivMultiplicative` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_equivMultiplicative_iff {m : AddMean A} :
    (equivMultiplicative m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  simp only [Mean.isLeftInvariant_iff, isLeftInvariant_iff, equivMultiplicative_apply,
    AddUCB.equivMultiplicative_symm_leftTranslation]
  exact ⟨fun h a f => by simpa using h (ofAdd a) (AddUCB.equivMultiplicative f),
    fun h g f => h g.toAdd (AddUCB.equivMultiplicative.symm f)⟩

/-- `equivMultiplicative.symm` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_equivMultiplicative_symm_iff {m : Mean (Multiplicative A)} :
    (equivMultiplicative.symm m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [← isLeftInvariant_equivMultiplicative_iff, Equiv.apply_symm_apply]

end AddMean

namespace Mean

section Additive

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Pullback along `UCB.equivAdditive` identifies means on `UCB G` with additive means on
`AddUCB (Additive G)`. -/
def equivAdditive : Mean G ≃ AddMean (Additive G) where
  toFun m := AddMean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ UCB.equivAdditive.symm.toLinearMap)
    (fun _ hf => by
      simp only [LinearMap.comp_apply, PositiveLinearMap.coe_toLinearMap, coe_toPositiveLinearMap,
        AlgEquiv.toLinearMap_apply]
      exact map_nonneg m (by
        simpa only [map_zero] using
          UCB.equivAdditive_symm_le_equivAdditive_symm_iff.2 hf))
    (by simp)
  invFun m := mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ UCB.equivAdditive.toLinearMap)
    (fun _ hf => by
      simp only [LinearMap.comp_apply, PositiveLinearMap.coe_toLinearMap,
        AddMean.coe_toPositiveLinearMap, AlgEquiv.toLinearMap_apply]
      exact map_nonneg m (by
        simpa only [map_zero] using
          UCB.equivAdditive_le_equivAdditive_iff.2 hf))
    (by simp)
  left_inv m := ext fun f => by simp [Mean.mk₀_apply]
  right_inv m := AddMean.ext fun f => by simp [Mean.mk₀_apply]

@[simp]
theorem equivAdditive_apply (m : Mean G) (f : AddUCB (Additive G)) :
    equivAdditive m f = m (UCB.equivAdditive.symm f) :=
  (rfl)

@[simp]
theorem equivAdditive_symm_apply (m : AddMean (Additive G)) (f : UCB G) :
    equivAdditive.symm m f = m (UCB.equivAdditive f) :=
  Mean.mk₀_apply _ _ _ f

/-- `equivAdditive` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_equivAdditive_iff {m : Mean G} :
    (equivAdditive m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  simp only [AddMean.isLeftInvariant_iff, isLeftInvariant_iff, equivAdditive_apply,
    UCB.equivAdditive_symm_leftTranslation]
  exact ⟨fun h g f => by simpa using h (ofMul g) (UCB.equivAdditive f),
    fun h a f => h a.toMul (UCB.equivAdditive.symm f)⟩

/-- `equivAdditive.symm` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_equivAdditive_symm_iff {m : AddMean (Additive G)} :
    (equivAdditive.symm m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [← isLeftInvariant_equivAdditive_iff, Equiv.apply_symm_apply]

end Additive

end Mean

/-! ### Additive amenability -/

variable (A) in
/-- A topological additive group `A` is amenable when `AddUCB A` carries a left-invariant additive
mean. -/
class AddAmenable : Prop where
  /-- An amenable additive group has a left-invariant mean on `AddUCB A`. -/
  exists_isLeftInvariant : ∃ m : AddMean A, m.IsLeftInvariant

variable (A) in
/-- A topological additive group is amenable if and only if `AddUCB A` carries a left-invariant
additive mean. -/
theorem addAmenable_iff : AddAmenable A ↔ ∃ m : AddMean A, m.IsLeftInvariant :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

variable (A) in
/-- A topological additive group `A` is amenable if and only if `Multiplicative A` is amenable. -/
theorem addAmenable_iff_amenable_multiplicative : AddAmenable A ↔ Amenable (Multiplicative A) :=
  ⟨fun ⟨⟨_, hm⟩⟩ => ⟨⟨_, AddMean.isLeftInvariant_equivMultiplicative_iff.2 hm⟩⟩,
    fun ⟨⟨_, hm⟩⟩ => ⟨⟨_, AddMean.isLeftInvariant_equivMultiplicative_symm_iff.2 hm⟩⟩⟩

/-- A topological group `G` is amenable if and only if `Additive G` is additively amenable. -/
theorem amenable_iff_addAmenable_additive (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Amenable G ↔ AddAmenable (Additive G) :=
  ⟨fun ⟨⟨_, hm⟩⟩ => ⟨⟨_, Mean.isLeftInvariant_equivAdditive_iff.2 hm⟩⟩,
    fun ⟨⟨_, hm⟩⟩ => ⟨⟨_, Mean.isLeftInvariant_equivAdditive_symm_iff.2 hm⟩⟩⟩

instance [AddAmenable A] : Amenable (Multiplicative A) :=
  (addAmenable_iff_amenable_multiplicative A).1 ‹_›

instance {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Amenable G] :
    AddAmenable (Additive G) :=
  (amenable_iff_addAmenable_additive G).1 ‹_›

/-! ### Permanence properties -/

/-- The target of a continuous additive homomorphism with dense range from an amenable topological
additive group is amenable; in particular, so is the image under a surjective continuous additive
homomorphism. -/
theorem AddAmenable.of_denseRange [AddAmenable A] (φ : A →ₜ+ B) (hφ : DenseRange φ) :
    AddAmenable B :=
  have ⟨m, hm⟩ := AddAmenable.exists_isLeftInvariant (A := A)
  ⟨⟨m.map φ, hm.map hφ⟩⟩

omit [TopologicalSpace A] [IsTopologicalAddGroup A] in
/-- Amenability passes from a finer additive group topology to a coarser additive group topology. -/
theorem AddAmenable.of_le {t₁ t₂ : TopologicalSpace A}
    [@IsTopologicalAddGroup A t₁ _] [@IsTopologicalAddGroup A t₂ _] (h : t₁ ≤ t₂)
    (ha : @AddAmenable A _ t₁ _) : @AddAmenable A _ t₂ _ := by
  let φ : @ContinuousAddMonoidHom A A _ _ t₁ t₂ :=
    @ContinuousAddMonoidHom.mk A A _ _ t₁ t₂ (AddMonoidHom.id A) (continuous_id_of_le h)
  exact @AddAmenable.of_denseRange A A _ t₁ _ _ t₂ _ ha φ
    (@Function.Surjective.denseRange A t₂ A _ fun x => ⟨x, AddMonoidHom.id_apply A x⟩)

/-- An abstract additive group which is amenable with the discrete topology is amenable with every
additive group topology. -/
theorem AddAmenable.of_discrete
    (h : letI : TopologicalSpace A := ⊥;
      letI := discreteTopology_bot A; AddAmenable A) :
    AddAmenable A := by
  let : @DiscreteTopology A ⊥ := discreteTopology_bot A
  exact AddAmenable.of_le (t₁ := ⊥) bot_le h

/-- Finite topological additive groups are amenable. -/
instance AddAmenable.of_finite [Finite A] : AddAmenable A :=
  (addAmenable_iff_amenable_multiplicative A).2 inferInstance

/-- The product of two amenable topological additive groups is amenable. -/
instance AddAmenable.prod [AddAmenable A] [AddAmenable B] : AddAmenable (A × B) :=
  (addAmenable_iff_amenable_multiplicative (A × B)).2 <|
    (ContinuousMulEquiv.prodMultiplicative A B).amenable_iff.2 inferInstance

variable (A B) in
/-- A product of two topological additive groups is amenable if and only if both factors are. -/
theorem addAmenable_prod_iff : AddAmenable (A × B) ↔ AddAmenable A ∧ AddAmenable B := by
  rw [addAmenable_iff_amenable_multiplicative,
    (ContinuousMulEquiv.prodMultiplicative A B).amenable_iff, amenable_prod_iff,
    ← addAmenable_iff_amenable_multiplicative, ← addAmenable_iff_amenable_multiplicative]

/-- The product of a finite family of amenable topological additive groups is amenable. -/
instance AddAmenable.pi {ι : Type*} [Finite ι] {K : ι → Type*} [∀ i, AddGroup (K i)]
    [∀ i, TopologicalSpace (K i)] [∀ i, IsTopologicalAddGroup (K i)] [∀ i, AddAmenable (K i)] :
    AddAmenable (∀ i, K i) :=
  (addAmenable_iff_amenable_multiplicative (∀ i, K i)).2 <|
    (ContinuousMulEquiv.piMultiplicative K).amenable_iff.2 inferInstance

/-- A product of a finite family of topological additive groups is amenable if and only if every
factor is. -/
theorem addAmenable_pi_iff {ι : Type*} [Finite ι] {K : ι → Type*} [∀ i, AddGroup (K i)]
    [∀ i, TopologicalSpace (K i)] [∀ i, IsTopologicalAddGroup (K i)] :
    AddAmenable (∀ i, K i) ↔ ∀ i, AddAmenable (K i) := by
  rw [addAmenable_iff_amenable_multiplicative,
    (ContinuousMulEquiv.piMultiplicative K).amenable_iff, amenable_pi_iff]
  exact forall_congr' fun i => (addAmenable_iff_amenable_multiplicative (K i)).symm

section Discrete

variable {D K Q : Type*} [AddGroup D] [TopologicalSpace D] [DiscreteTopology D]
  [AddGroup K] [TopologicalSpace K] [DiscreteTopology K]
  [AddGroup Q] [TopologicalSpace Q] [DiscreteTopology Q]

/-- An additive group `A` which embeds by an injective homomorphism in an amenable discrete additive
group is amenable, for every additive group topology on `A`. -/
theorem AddAmenable.of_injective [AddAmenable D] (φ : A →+ D) (hφ : Function.Injective φ) :
    AddAmenable A :=
  (addAmenable_iff_amenable_multiplicative A).2 <|
    Amenable.of_injective (AddMonoidHom.toMultiplicative φ)
      (ofAdd.injective.comp (hφ.comp toAdd.injective))

/-- Every additive subgroup of an amenable discrete additive group is amenable. -/
instance AddAmenable.addSubgroup [AddAmenable D] (H : AddSubgroup D) : AddAmenable H :=
  .of_injective H.subtype H.subtype_injective

/-- If `ψ : K →+ D` and `φ : D →+ Q` are homomorphisms of discrete additive groups with
`φ.ker ≤ ψ.range`, and `K` and `Q` are amenable, then `D` is amenable. -/
theorem AddAmenable.of_ker_le_range [AddAmenable K] [AddAmenable Q] (ψ : K →+ D) (φ : D →+ Q)
    (h : φ.ker ≤ ψ.range) : AddAmenable D := by
  refine (addAmenable_iff_amenable_multiplicative D).2 <|
    Amenable.of_ker_le_range (AddMonoidHom.toMultiplicative ψ)
      (AddMonoidHom.toMultiplicative φ) fun x hx => ?_
  obtain ⟨k, hk⟩ := h (show x.toAdd ∈ φ.ker by simpa [AddMonoidHom.mem_ker] using hx)
  exact ⟨ofAdd k, by simp [hk]⟩

/-- A discrete additive group with a normal additive subgroup `N` is amenable if and only if `N` and
`D ⧸ N` are amenable. -/
theorem addAmenable_iff_addSubgroup_quotient (N : AddSubgroup D) [N.Normal] :
    AddAmenable D ↔ AddAmenable N ∧ AddAmenable (D ⧸ N) := by
  have := QuotientAddGroup.discreteTopology (isOpen_discrete (N : Set D))
  refine ⟨fun _ => ⟨inferInstance, ?_⟩, fun ⟨_, _⟩ =>
    .of_ker_le_range N.subtype (QuotientAddGroup.mk' N) (by simp)⟩
  exact .of_denseRange ⟨QuotientAddGroup.mk' N, continuous_of_discreteTopology⟩
    (QuotientAddGroup.mk'_surjective N).denseRange

/-- A discrete additive group is amenable when it has an amenable normal additive subgroup with
amenable quotient. -/
theorem AddAmenable.of_addSubgroup_quotient (N : AddSubgroup D) [N.Normal] [AddAmenable N]
    [AddAmenable (D ⧸ N)] : AddAmenable D :=
  (addAmenable_iff_addSubgroup_quotient N).2 ⟨‹_›, ‹_›⟩

end Discrete

/-! ### Directed unions and finitely generated subgroups -/

/-- A topological additive group `A` is amenable if, for a family of continuous additive
homomorphisms `φ i : K i →ₜ+ A` from amenable topological additive groups, every finite subset of
`A` lies in the range of some `φ i`. -/
theorem AddAmenable.of_forall_finset_subset_range {ι : Type*} {K : ι → Type*}
    [∀ i, AddGroup (K i)] [∀ i, TopologicalSpace (K i)] [∀ i, IsTopologicalAddGroup (K i)]
    [∀ i, AddAmenable (K i)] (φ : ∀ i, K i →ₜ+ A)
    (h : ∀ s : Finset A, ∃ i, (s : Set A) ⊆ Set.range (φ i)) : AddAmenable A := by
  classical
  let φ' (i : ι) : Multiplicative (K i) →ₜ* Multiplicative A :=
    ⟨AddMonoidHom.toMultiplicative (φ i).toAddMonoidHom,
      continuous_ofAdd.comp ((φ i).continuous.comp continuous_toAdd)⟩
  refine (addAmenable_iff_amenable_multiplicative A).2 <|
    Amenable.of_forall_finset_subset_range φ' fun s => ?_
  obtain ⟨i, hi⟩ := h (s.image toAdd)
  refine ⟨i, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hi (Finset.mem_coe.2 (Finset.mem_image_of_mem toAdd hx))
  refine ⟨ofAdd k, ?_⟩
  change ofAdd (φ i (toAdd (ofAdd k))) = x
  simp [hk]

/-- The supremum `⨆ i, H i` of a directed family of amenable additive subgroups `H i` of a
topological additive group is an amenable additive subgroup. -/
theorem addAmenable_iSup_of_directed {ι : Type*} {H : ι → AddSubgroup A}
    (hH : Directed (· ≤ ·) H) [∀ i, AddAmenable (H i)] : AddAmenable ↥(⨆ i, H i) := by
  classical
  obtain hι | hι := isEmpty_or_nonempty ι
  · rw [iSup_of_empty]
    infer_instance
  refine .of_forall_finset_subset_range
    (fun i => ⟨AddSubgroup.inclusion (le_iSup H i), continuous_inclusion (le_iSup H i)⟩) fun s => ?_
  have hH' : Directed (· ⊆ ·) fun i => (H i : Set A) :=
    hH.mono_comp _ fun _ _ => SetLike.coe_subset_coe.2
  obtain ⟨i, hi⟩ := hH'.exists_mem_subset_of_finset_subset_biUnion (s := s.image Subtype.val) <| by
    rw [Finset.coe_image, ← AddSubgroup.coe_iSup_of_directed hH]
    exact Set.image_subset_iff.2 fun x _ => x.2
  exact ⟨i, fun x hx => ⟨⟨x, hi (Finset.mem_image_of_mem _ hx)⟩, rfl⟩⟩

/-- A topological additive group which is the supremum of a directed family of amenable additive
subgroups is amenable. -/
theorem AddAmenable.of_directed_of_iSup_eq_top {ι : Type*} {H : ι → AddSubgroup A}
    (hH : Directed (· ≤ ·) H) (htop : ⨆ i, H i = ⊤) [∀ i, AddAmenable (H i)] : AddAmenable A :=
  have := addAmenable_iSup_of_directed hH
  .of_denseRange ⟨(⨆ i, H i).subtype, continuous_subtype_val⟩
    (Function.Surjective.denseRange fun x => ⟨⟨x, htop ▸ AddSubgroup.mem_top x⟩, rfl⟩)

/-- A topological additive group all of whose finitely generated additive subgroups are amenable is
amenable. -/
theorem AddAmenable.of_forall_fg (h : ∀ K : AddSubgroup A, K.FG → AddAmenable K) :
    AddAmenable A := by
  have : ∀ K : {K : AddSubgroup A // K.FG}, AddAmenable K.1 := fun K => h K.1 K.2
  refine .of_forall_finset_subset_range
    (fun K : {K : AddSubgroup A // K.FG} => ⟨K.1.subtype, continuous_subtype_val⟩) fun s => ?_
  refine ⟨⟨AddSubgroup.closure s, (AddGroup.fg_iff_addSubgroup_fg _).1 inferInstance⟩,
    fun x hx => ?_⟩
  exact ⟨⟨x, AddSubgroup.subset_closure hx⟩, rfl⟩

/-! ### Følner characterizations -/

/-- An additive group with additive Følner sets is amenable, for every additive group topology. -/
theorem AddAmenable.of_hasAddFoelnerSets (h : HasAddFoelnerSets A) : AddAmenable A :=
  (addAmenable_iff_amenable_multiplicative A).2
    (.of_hasFoelnerSets (hasAddFoelnerSets_iff_hasFoelnerSets_multiplicative.1 h))

/-- A topological additive group is amenable when it has an additive Følner family for counting
measure, along a nontrivial filter. -/
theorem AddAmenable.of_isAddFoelner [MeasurableSpace A] {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → Set A} (hF : IsAddFoelner A MeasureTheory.Measure.count l F) : AddAmenable A :=
  .of_hasAddFoelnerSets (.of_isAddFoelner hF)

/-- An amenable discrete additive group has additive Følner sets. -/
theorem AddAmenable.hasAddFoelnerSets [DiscreteTopology A] [AddAmenable A] :
    HasAddFoelnerSets A :=
  hasAddFoelnerSets_iff_hasFoelnerSets_multiplicative.2 Amenable.hasFoelnerSets

/-- A discrete additive group is amenable if and only if it has additive Følner sets. -/
theorem addAmenable_iff_hasAddFoelnerSets [DiscreteTopology A] :
    AddAmenable A ↔ HasAddFoelnerSets A :=
  ⟨fun _ => AddAmenable.hasAddFoelnerSets, .of_hasAddFoelnerSets⟩

/-- A discrete additive group is amenable if and only if for every finite `K ⊆ A` and every `ε > 0`
there is a finite nonempty `F ⊆ A` with `|(a +ᵥ F) △ F| < ε · |F|` for all `a ∈ K`. -/
theorem addAmenable_iff_exists_finset [DiscreteTopology A] [DecidableEq A] :
    AddAmenable A ↔ ∀ K : Finset A, ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset A, F.Nonempty ∧ ∀ a ∈ K, (#((a +ᵥ F) ∆ F) : ℝ) < ε * #F := by
  rw [addAmenable_iff_hasAddFoelnerSets, hasAddFoelnerSets_iff]

end TauCeti

namespace ContinuousAddEquiv

open TauCeti

variable {A B : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- Amenability is invariant under isomorphisms of topological additive groups. -/
theorem addAmenable_iff (e : A ≃ₜ+ B) : AddAmenable A ↔ AddAmenable B := by
  rw [addAmenable_iff_amenable_multiplicative, addAmenable_iff_amenable_multiplicative]
  exact e.toMultiplicative.amenable_iff

end ContinuousAddEquiv

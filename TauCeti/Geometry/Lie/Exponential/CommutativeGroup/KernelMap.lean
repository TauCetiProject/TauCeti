/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.ContinuousFunctor
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Basic
import TauCeti.Algebra.Module.ZLattice.BaseChange

/-!
# Homomorphisms of commutative Lie groups and the kernels of their exponentials

Let `G` be a commutative finite-dimensional real Lie group with Lie algebra `𝔤`, exponential
`exp : 𝔤 → G` and kernel `Λ = ker(exp)`. A continuous homomorphism `f : G → G'` is differentiated
to its Lie map `df : 𝔤 → 𝔤'`, which satisfies `f ∘ exp = exp ∘ df`. So `df` carries `Λ` into
`Λ' = ker(exp')`, functorially in `f`, and descends to `𝔤 / Λ → 𝔤' / Λ'`, which is `f` under the
identifications `𝔤 / Λ ≃ G` of preconnected groups.

Conversely, for preconnected `G` every real-linear map `φ : 𝔤 → 𝔤'` with `φ(Λ) ⊆ Λ'` is the Lie
map of a unique continuous homomorphism, so continuous homomorphisms `G → G'` correspond exactly
to linear maps carrying `Λ` into `Λ'` (`ContinuousMonoidHom.lieMapKerEquiv`). When `G` is
moreover compact, `Λ` is a full lattice, so every additive map `Λ → Λ'` extends uniquely to a
real-linear map, and the continuous homomorphisms `G → G'` are exactly the additive maps `Λ → Λ'`
(`TauCeti.existsUnique_continuousMonoidHom_lieMap_ker`). This is the full faithfulness of
`T ↦ ker(exp_T)` on compact connected commutative Lie groups.

The converse direction uses that the Lie map is characterized by the identity
`f ∘ exp = exp ∘ φ` (`ContinuousMonoidHom.lieMap_apply_eq_of_lieExp`). As examples, the Lie map
of the `n`-th power map of a commutative Lie group is multiplication by `n`, so on the kernel of
the exponential it acts as `λ ↦ n λ`.

## Main definitions

* `ContinuousMonoidHom.lieMapKer f : ker(exp) →+ ker(exp')`: the restriction of the Lie map.
* `ContinuousMonoidHom.lieMapQuotient f : 𝔤 / Λ →+ 𝔤' / Λ'`: the map it induces.
* `ContinuousMonoidHom.ofLieLinearMap φ hφ : G →ₜ* G'`: the homomorphism with Lie map `φ`.
* `ContinuousMonoidHom.lieMapKerEquiv`: continuous homomorphisms out of a preconnected `G` are
  the linear maps of Lie algebras carrying `Λ` into `Λ'`.

## Main results

* `ContinuousMonoidHom.lieMapKer_id`, `ContinuousMonoidHom.lieMapKer_comp`,
  `ContinuousMonoidHom.lieMapQuotient_id`, `ContinuousMonoidHom.lieMapQuotient_comp`:
  functoriality.
* `ContinuousMonoidHom.lieExpQuotientKerContinuousAddEquiv_lieMapQuotient`: the induced map of
  quotients is `f` under the exponential identifications.
* `ContinuousMonoidHom.lieMap_ofLieLinearMap`: the Lie map of `ofLieLinearMap φ hφ` is `φ`.
* `TauCeti.existsUnique_continuousMonoidHom_lieMap_ker`: for compact connected `G`, every
  additive map `ker(exp) → ker(exp')` is the restriction of the Lie map of exactly one continuous
  homomorphism `G → G'`.
* `ContinuousMonoidHom.lieMap_id_pow`, `ContinuousMonoidHom.lieMapKer_id_pow`: the `n`-th power
  map `ContinuousMonoidHom.id G ^ n` differentiates to multiplication by `n`, on `𝔤` and on `Λ`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser (2002), Cor. 1.103(c)
  and Prop. 4.58, for continuous homomorphisms of tori as maps of exponential lattices.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map).
* *Complex theory of abelian varieties*, Stanford VIGRE seminar notes (2004), Theorem 1.8 and
  § 1.2, pp. 2–4, for homomorphisms of complex tori as linear maps carrying lattice into lattice,
  <https://math.stanford.edu/~conrad/vigregroup/vigre04/abvaran.pdf>.
-/

public section

noncomputable section

open Filter Topology
open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace ContinuousMonoidHom

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [LieGroup I ∞ G] [LieGroup I' ∞ G']
  [T2Space G] [BoundarylessManifold I G] [T2Space G'] [BoundarylessManifold I' G']

variable [IsMulCommutative G] [IsMulCommutative G']

/-! ### The Lie map on the kernel of the exponential -/

/-- **The Lie map carries the kernel of the exponential into the kernel of the exponential.** -/
theorem lieMap_mem_ker_lieExpAddMonoidHom (f : G →ₜ* G') {X : LeftInvariantDerivation I G}
    (hX : X ∈ (lieExpAddMonoidHom (I := I) (G := G)).ker) :
    lieMap (I := I) (I' := I') f X ∈ (lieExpAddMonoidHom (I := I') (G := G')).ker := by
  rw [mem_ker_lieExpAddMonoidHom] at hX ⊢
  rw [← map_lieExp, hX, map_one]

/-- The restriction of the Lie map of `f` to the kernels of the exponentials,
`ker(exp) → ker(exp')`. -/
def lieMapKer (f : G →ₜ* G') :
    (lieExpAddMonoidHom (I := I) (G := G)).ker →+ (lieExpAddMonoidHom (I := I') (G := G')).ker where
  toFun X := ⟨lieMap (I := I) (I' := I') f X, lieMap_mem_ker_lieExpAddMonoidHom f X.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[simp]
theorem coe_lieMapKer_apply (f : G →ₜ* G') (X : (lieExpAddMonoidHom (I := I) (G := G)).ker) :
    (lieMapKer (I := I) (I' := I') f X : LeftInvariantDerivation I' G') =
      lieMap (I := I) (I' := I') f X :=
  (rfl)

/-- The restriction of the Lie map to the kernels is functorial: the identity. -/
@[simp]
theorem lieMapKer_id :
    lieMapKer (I := I) (I' := I) (ContinuousMonoidHom.id G) = AddMonoidHom.id _ := by
  ext X
  simp

/-- The restriction of the Lie map to the kernels is functorial: composition. -/
theorem lieMapKer_comp
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Group G'']
    [FiniteDimensional ℝ E''] [LieGroup I'' ∞ G''] [T2Space G''] [BoundarylessManifold I'' G'']
    [IsMulCommutative G''] (f : G →ₜ* G') (g : G' →ₜ* G'') :
    lieMapKer (I := I) (I' := I'') (g.comp f) =
      (lieMapKer (I := I') (I' := I'') g).comp (lieMapKer (I := I) (I' := I') f) := by
  ext X
  simp [lieMap_comp (I' := I')]

/-! ### The induced map of quotients -/

/-- The map `𝔤 / ker(exp) → 𝔤' / ker(exp')` induced by the Lie map of `f`. -/
def lieMapQuotient (f : G →ₜ* G') :
    LeftInvariantDerivation I G ⧸ (lieExpAddMonoidHom (I := I) (G := G)).ker →+
      LeftInvariantDerivation I' G' ⧸ (lieExpAddMonoidHom (I := I') (G := G')).ker :=
  QuotientAddGroup.map _ _ (lieMap (I := I) (I' := I') f).toLinearMap.toAddMonoidHom
    fun _ hX ↦ lieMap_mem_ker_lieExpAddMonoidHom f hX

@[simp]
theorem lieMapQuotient_mk (f : G →ₜ* G') (X : LeftInvariantDerivation I G) :
    lieMapQuotient (I := I) (I' := I') f (QuotientAddGroup.mk X) =
      QuotientAddGroup.mk (lieMap (I := I) (I' := I') f X) :=
  (rfl)

/-- The induced map of quotients is functorial: the identity. -/
@[simp]
theorem lieMapQuotient_id :
    lieMapQuotient (I := I) (I' := I) (ContinuousMonoidHom.id G) = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun q ↦ ?_
  induction q using QuotientAddGroup.induction_on with
  | H X => simp

/-- The induced map of quotients is functorial: composition. -/
theorem lieMapQuotient_comp
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Group G'']
    [FiniteDimensional ℝ E''] [LieGroup I'' ∞ G''] [T2Space G''] [BoundarylessManifold I'' G'']
    [IsMulCommutative G''] (f : G →ₜ* G') (g : G' →ₜ* G'') :
    lieMapQuotient (I := I) (I' := I'') (g.comp f) =
      (lieMapQuotient (I := I') (I' := I'') g).comp (lieMapQuotient (I := I) (I' := I') f) := by
  refine AddMonoidHom.ext fun q ↦ ?_
  induction q using QuotientAddGroup.induction_on with
  | H X => simp [lieMap_comp (I' := I')]

variable [IsTopologicalGroup G]

/-- **The induced map of quotients is `f`** under the identifications `𝔤 / ker(exp) ≃ G` of
preconnected commutative Lie groups. -/
theorem lieExpQuotientKerContinuousAddEquiv_lieMapQuotient [PreconnectedSpace G]
    [IsTopologicalGroup G'] [PreconnectedSpace G'] (f : G →ₜ* G')
    (q : LeftInvariantDerivation I G ⧸ (lieExpAddMonoidHom (I := I) (G := G)).ker) :
    lieExpQuotientKerContinuousAddEquiv (I := I') (G := G')
        (lieMapQuotient (I := I) (I' := I') f q) =
      Additive.ofMul (f (Additive.toMul
        (lieExpQuotientKerContinuousAddEquiv (I := I) (G := G) q))) := by
  induction q using QuotientAddGroup.induction_on with
  | H X => simp [map_lieExp (I' := I')]

/-! ### Homomorphisms from linear maps preserving the kernels -/

variable [PreconnectedSpace G]

/-- The continuous homomorphism `G → G'` of a preconnected commutative Lie group with Lie map
`φ`, for a real-linear map `φ : 𝔤 → 𝔤'` carrying `ker(exp)` into `ker(exp')`: it sends `exp X` to
`exp (φ X)`. -/
def ofLieLinearMap (φ : LeftInvariantDerivation I G →ₗ[ℝ] LeftInvariantDerivation I' G')
    (hφ : ∀ X ∈ (lieExpAddMonoidHom (I := I) (G := G)).ker,
      φ X ∈ (lieExpAddMonoidHom (I := I') (G := G')).ker) : G →ₜ* G' :=
  -- The kernel inclusion goes through `AddMonoidHom.mem_ker` to elaborate at the type
  -- `X ∈ (exp' ∘ φ).ker`: passing `hφ` directly leaves a term that `simp` no longer reduces in
  -- `ofLieLinearMap_lieExp`.
  lieExpLift ((lieExpAddMonoidHom (I := I') (G := G')).comp φ.toAddMonoidHom)
    ((continuous_lieExpAddMonoidHom (I := I') (G := G')).comp φ.continuous_of_finiteDimensional)
    fun X hX ↦ AddMonoidHom.mem_ker.2 (AddMonoidHom.mem_ker.1 (hφ X hX))

/-- The homomorphism `ofLieLinearMap φ hφ` sends `exp X` to `exp (φ X)`. -/
@[simp]
theorem ofLieLinearMap_lieExp
    (φ : LeftInvariantDerivation I G →ₗ[ℝ] LeftInvariantDerivation I' G')
    (hφ : ∀ X ∈ (lieExpAddMonoidHom (I := I) (G := G)).ker,
      φ X ∈ (lieExpAddMonoidHom (I := I') (G := G')).ker) (X : LeftInvariantDerivation I G) :
    ofLieLinearMap φ hφ (lieExp X) = lieExp (φ X) := by
  simp [ofLieLinearMap]

/-- **The Lie map of `ofLieLinearMap φ hφ` is `φ`.** -/
@[simp]
theorem lieMap_ofLieLinearMap
    (φ : LeftInvariantDerivation I G →ₗ[ℝ] LeftInvariantDerivation I' G')
    (hφ : ∀ X ∈ (lieExpAddMonoidHom (I := I) (G := G)).ker,
      φ X ∈ (lieExpAddMonoidHom (I := I') (G := G')).ker) (X : LeftInvariantDerivation I G) :
    lieMap (I := I) (I' := I') (ofLieLinearMap φ hφ) X = φ X :=
  lieMap_apply_eq_of_lieExp _ φ (fun Y ↦ (ofLieLinearMap_lieExp φ hφ Y).symm) X

/-- **Continuous homomorphisms are linear maps preserving the exponential kernels.** For a
preconnected commutative Lie group `G`, differentiation identifies continuous homomorphisms
`G → G'` with the real-linear maps `𝔤 → 𝔤'` carrying `ker(exp)` into `ker(exp')`. -/
def lieMapKerEquiv :
    (G →ₜ* G') ≃ {φ : LeftInvariantDerivation I G →ₗ[ℝ] LeftInvariantDerivation I' G' //
      ∀ X ∈ (lieExpAddMonoidHom (I := I) (G := G)).ker,
        φ X ∈ (lieExpAddMonoidHom (I := I') (G := G')).ker} where
  toFun f := ⟨(lieMap (I := I) (I' := I') f).toLinearMap,
    fun _ hX ↦ lieMap_mem_ker_lieExpAddMonoidHom f hX⟩
  invFun φ := ofLieLinearMap φ.val φ.property
  left_inv _ :=
    lieMap_injective (I := I) (I' := I') (LieHom.ext fun X ↦ lieMap_ofLieLinearMap _ _ X)
  right_inv φ := Subtype.ext (LinearMap.ext fun X ↦ lieMap_ofLieLinearMap φ.val φ.property X)

@[simp]
theorem coe_lieMapKerEquiv_apply (f : G →ₜ* G') :
    ((lieMapKerEquiv (I := I) (I' := I') f : LeftInvariantDerivation I G →ₗ[ℝ]
      LeftInvariantDerivation I' G') : LeftInvariantDerivation I G →
        LeftInvariantDerivation I' G') = lieMap (I := I) (I' := I') f :=
  (rfl)

@[simp]
theorem lieMapKerEquiv_symm_apply
    (φ : {φ : LeftInvariantDerivation I G →ₗ[ℝ] LeftInvariantDerivation I' G' //
      ∀ X ∈ (lieExpAddMonoidHom (I := I) (G := G)).ker,
        φ X ∈ (lieExpAddMonoidHom (I := I') (G := G')).ker}) :
    (lieMapKerEquiv (I := I) (I' := I')).symm φ = ofLieLinearMap φ.val φ.property :=
  (rfl)

end ContinuousMonoidHom

namespace TauCeti

open ContinuousMonoidHom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [LieGroup I ∞ G] [LieGroup I' ∞ G']
  [T2Space G] [BoundarylessManifold I G] [T2Space G'] [BoundarylessManifold I' G']
  [IsMulCommutative G] [IsMulCommutative G'] [CompactSpace G] [PreconnectedSpace G]

/-- **Tori and their exponential lattices** (full faithfulness): for a compact connected
commutative Lie group `G` and a commutative Lie group `G'`, every additive map between the kernels
of their exponentials is the restriction of the Lie map of exactly one continuous homomorphism
`G →ₜ* G'`. For `Circle` the kernel is `2πℤ`, and `z ↦ z²` restricts to multiplication by `2`. -/
theorem existsUnique_continuousMonoidHom_lieMap_ker
    (g : (lieExpAddMonoidHom (I := I) (G := G)).ker →+
      (lieExpAddMonoidHom (I := I') (G := G')).ker) :
    ∃! f : G →ₜ* G', ∀ X : (lieExpAddMonoidHom (I := I) (G := G)).ker,
      lieMap (I := I) (I' := I') f X = g X := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  -- The real-linear extension of `g` along the full lattice `ker(exp)`, whose inclusion exhibits
  -- the Lie algebra as its base change to `ℝ`.
  set φ := (ZLattice.isBaseChange_subtype ℝ (lieExpLattice (I := I) (G := G))).lift
    ((lieExpAddMonoidHom (I := I') (G := G')).ker.subtype.comp g).toIntLinearMap
  have hφ (X : (lieExpAddMonoidHom (I := I) (G := G)).ker) : φ X = g X := by
    -- `lieExpLattice` is `ker(exp)` as a `ℤ`-submodule, with the same elements.
    exact (ZLattice.isBaseChange_subtype ℝ (lieExpLattice (I := I) (G := G))).lift_eq
      ((lieExpAddMonoidHom (I := I') (G := G')).ker.subtype.comp g).toIntLinearMap
      ⟨X.val, X.property⟩
  have hL (X) (hX : X ∈ (lieExpAddMonoidHom (I := I) (G := G)).ker) :
      φ X ∈ (lieExpAddMonoidHom (I := I') (G := G')).ker := by
    rw [hφ ⟨X, hX⟩]
    exact (g ⟨X, hX⟩).property
  refine ⟨ofLieLinearMap φ hL, fun X ↦ ?_, fun f hf ↦ ?_⟩
  · rw [lieMap_ofLieLinearMap, hφ]
  · refine (lieMapKerEquiv (I := I) (I' := I')).injective (Subtype.ext ?_)
    -- Both Lie maps agree with `φ` on the kernel, a full lattice in the Lie algebra.
    refine LinearMap.ext_on (IsZLattice.span_top (K := ℝ) (L := lieExpLattice (I := I) (G := G)))
      fun X hX ↦ ?_
    simp only [coe_lieMapKerEquiv_apply, lieMap_ofLieLinearMap]
    rw [hφ ⟨X, hX⟩]
    exact hf ⟨X, hX⟩

end TauCeti
/-! ### Multiplication by `n` -/

namespace ContinuousMonoidHom

open TauCeti
open scoped IsMulCommutative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  [IsMulCommutative G] [ContinuousMul G]

/-- **The `n`-th power map `ContinuousMonoidHom.id G ^ n` differentiates to multiplication by
`n`.** -/
@[simp]
theorem lieMap_id_pow (n : ℕ) (X : LeftInvariantDerivation I G) :
    lieMap (I := I) (I' := I) (ContinuousMonoidHom.id G ^ n) X = n • X := by
  refine lieMap_apply_eq_of_lieExp _ ((n : ℝ) • LinearMap.id) (fun Y ↦ ?_) X |>.trans ?_ <;>
    simp [Nat.cast_smul_eq_nsmul, lieExp_nsmul]

/-- On the kernel of the exponential, the `n`-th power map acts as `λ ↦ n λ`; in particular
multiplication by two acts as `λ ↦ 2 λ` on the kernel of the exponential. -/
theorem lieMapKer_id_pow (n : ℕ) :
    lieMapKer (I := I) (I' := I) (ContinuousMonoidHom.id G ^ n) = n • AddMonoidHom.id _ := by
  ext X
  simp

end ContinuousMonoidHom

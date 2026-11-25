/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.ContinuousFunctor
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Basic

/-!
# Homomorphisms of commutative Lie groups and the kernels of their exponentials

Let `G` be a commutative finite-dimensional real Lie group with Lie algebra `𝔤`, exponential
`exp : 𝔤 → G` and kernel `Λ = ker(exp)`. A continuous homomorphism `f : G → G'` is differentiated
to its Lie map `df : 𝔤 → 𝔤'`, which satisfies `f ∘ exp = exp ∘ df`. So `df` carries `Λ` into
`Λ' = ker(exp')`, functorially in `f`, and descends to `𝔤 / Λ → 𝔤' / Λ'`, which is `f` under the
identifications `𝔤 / Λ ≃ G` of preconnected groups.

Conversely, for preconnected `G` every real-linear map `φ : 𝔤 → 𝔤'` with `φ(Λ) ⊆ Λ'` is the Lie
map of a unique continuous homomorphism, so continuous homomorphisms `G → G'` correspond exactly
to linear maps carrying lattice into lattice (`ContinuousMonoidHom.lieMapKerEquiv`). This is the
generic part of the lattice map of a complex torus in AbelianSchemesAndArithmeticModuli §A5.1:
for `G = V / Λ` a homomorphism is a linear map `V → W` with `φ(Λ) ⊆ Λ'`.

The Lie map is characterized by the identity `f ∘ exp = exp ∘ φ`
(`ContinuousMonoidHom.lieMap_apply_eq_of_lieExp`), for any finite-dimensional real Lie groups.
As examples, the Lie map of the `n`-th power map of a commutative Lie group is multiplication by
`n`, so on the kernel of the exponential it acts as `λ ↦ n λ`.

## Main definitions

* `ContinuousMonoidHom.lieMapKer f : ker(exp) →+ ker(exp')`: the restriction of the Lie map.
* `ContinuousMonoidHom.lieMapQuotient f : 𝔤 / Λ →+ 𝔤' / Λ'`: the map it induces.
* `ContinuousMonoidHom.ofLieLinearMap φ hφ : G →ₜ* G'`: the homomorphism with Lie map `φ`.
* `ContinuousMonoidHom.lieMapKerEquiv`: continuous homomorphisms out of a preconnected `G` are
  the linear maps of Lie algebras carrying `Λ` into `Λ'`.
* `TauCeti.powContinuousMonoidHom n`: the `n`-th power map of a commutative topological group.

## Main results

* `ContinuousMonoidHom.lieMap_apply_eq_of_lieExp`: a linear map `φ` with
  `exp ∘ φ = f ∘ exp` is the Lie map of `f`.
* `ContinuousMonoidHom.lieMapKer_id`, `ContinuousMonoidHom.lieMapKer_comp`: functoriality.
* `ContinuousMonoidHom.lieExpQuotientKerContinuousAddEquiv_lieMapQuotient`: the induced map of
  quotients is `f` under the exponential identifications.
* `ContinuousMonoidHom.lieMap_ofLieLinearMap`: the Lie map of `ofLieLinearMap φ hφ` is `φ`.
* `ContinuousMonoidHom.lieMap_powContinuousMonoidHom`, `ContinuousMonoidHom.coe_lieMapKer_pow`:
  the `n`-th power map differentiates to multiplication by `n`, on `𝔤` and on `Λ`.
* `TauCeti.ker_lieExpAddMonoidHom_eq_bot_of_subsingleton`: in dimension zero the kernel is zero.
-/

public section

noncomputable section

open Filter Topology
open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace TauCeti

variable {G : Type*} [Group G] [IsMulCommutative G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (G) in
/-- The `n`-th power map `g ↦ gⁿ` of a commutative topological group, as a continuous
homomorphism. -/
@[expose] def powContinuousMonoidHom (n : ℕ) : G →ₜ* G where
  toFun g := g ^ n
  map_one' := one_pow n
  map_mul' a b := (Commute.mul_pow (mul_comm' a b) n)
  continuous_toFun := continuous_pow n

@[simp]
theorem powContinuousMonoidHom_apply (n : ℕ) (g : G) : powContinuousMonoidHom G n g = g ^ n :=
  rfl

end TauCeti

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

/-! ### The Lie map is characterized by the exponential -/

/-- **The Lie map is determined by the exponential.** A real-linear map `φ : 𝔤 → 𝔤'` with
`exp(φ X) = f(exp X)` for every `X` is the Lie map of `f`. -/
theorem lieMap_apply_eq_of_lieExp (f : G →ₜ* G')
    (φ : LeftInvariantDerivation I G →ₗ[ℝ] LeftInvariantDerivation I' G')
    (h : ∀ X, lieExp (φ X) = f (lieExp X)) (X : LeftInvariantDerivation I G) :
    lieMap (I := I) (I' := I') f X = φ X := by
  -- Compare `t ↦ exp(t • df X)` and `t ↦ exp(t • φ X)` near `t = 0`, where `exp` is injective.
  have hlim (Y : LeftInvariantDerivation I' G') :
      Tendsto (fun t : ℝ ↦ t • Y) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ ↦ t • Y) (𝓝 0) (𝓝 ((0 : ℝ) • Y)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have heq := eventuallyEq_of_tendsto_of_lieExp_eventuallyEq (hlim (lieMap (I := I) (I' := I') f X))
    (hlim (φ X)) (Eventually.of_forall fun t ↦ by
      simp only
      rw [← map_smul, ← map_lieExp, ← map_smul, h])
  obtain ⟨t, ht, ht0⟩ := (heq.and self_mem_nhdsWithin).exists
  exact smul_right_injective _ ht0 ht

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
@[expose] def lieMapKer (f : G →ₜ* G') :
    (lieExpAddMonoidHom (I := I) (G := G)).ker →+ (lieExpAddMonoidHom (I := I') (G := G')).ker where
  toFun X := ⟨lieMap (I := I) (I' := I') f X, lieMap_mem_ker_lieExpAddMonoidHom f X.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[simp]
theorem coe_lieMapKer_apply (f : G →ₜ* G') (X : (lieExpAddMonoidHom (I := I) (G := G)).ker) :
    (lieMapKer (I := I) (I' := I') f X : LeftInvariantDerivation I' G') =
      lieMap (I := I) (I' := I') f X :=
  rfl

/-- The restriction of the Lie map to the kernels is functorial: the identity. -/
@[simp]
theorem lieMapKer_id :
    lieMapKer (I := I) (I' := I) (ContinuousMonoidHom.id G) = AddMonoidHom.id _ := by
  ext X
  rw [coe_lieMapKer_apply, lieMap_id]
  rfl

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
  rw [coe_lieMapKer_apply, lieMap_comp (I' := I')]
  rfl

/-! ### The induced map of quotients -/

/-- The map `𝔤 / ker(exp) → 𝔤' / ker(exp')` induced by the Lie map of `f`. -/
@[expose] def lieMapQuotient (f : G →ₜ* G') :
    LeftInvariantDerivation I G ⧸ (lieExpAddMonoidHom (I := I) (G := G)).ker →+
      LeftInvariantDerivation I' G' ⧸ (lieExpAddMonoidHom (I := I') (G := G')).ker :=
  QuotientAddGroup.map _ _ (lieMap (I := I) (I' := I') f).toLinearMap.toAddMonoidHom
    fun _ hX ↦ lieMap_mem_ker_lieExpAddMonoidHom f hX

@[simp]
theorem lieMapQuotient_mk (f : G →ₜ* G') (X : LeftInvariantDerivation I G) :
    lieMapQuotient (I := I) (I' := I') f (QuotientAddGroup.mk X) =
      QuotientAddGroup.mk (lieMap (I := I) (I' := I') f X) :=
  rfl

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
  | H X =>
    rw [lieMapQuotient_mk, lieExpQuotientKerContinuousAddEquiv_apply,
      lieExpQuotientKerContinuousAddEquiv_apply, toMul_ofMul, map_lieExp (I' := I')]

/-! ### Homomorphisms from linear maps preserving the kernels -/

variable [PreconnectedSpace G]

/-- The continuous homomorphism `G → G'` of a preconnected commutative Lie group with Lie map
`φ`, for a real-linear map `φ : 𝔤 → 𝔤'` carrying `ker(exp)` into `ker(exp')`: it sends `exp X` to
`exp (φ X)`. -/
@[expose] def ofLieLinearMap (φ : LeftInvariantDerivation I G →ₗ[ℝ] LeftInvariantDerivation I' G')
    (hφ : ∀ X ∈ (lieExpAddMonoidHom (I := I) (G := G)).ker,
      φ X ∈ (lieExpAddMonoidHom (I := I') (G := G')).ker) : G →ₜ* G' where
  toFun g := Additive.toMul (QuotientAddGroup.lift _
    ((lieExpAddMonoidHom (I := I') (G := G')).comp φ.toAddMonoidHom)
    (fun X hX ↦ AddMonoidHom.mem_ker.2 (AddMonoidHom.mem_ker.1 (hφ X hX)))
    ((lieExpQuotientKerContinuousAddEquiv (I := I) (G := G)).symm
      (Additive.ofMul g)))
  map_one' := by
    rw [ofMul_one, map_zero, map_zero, toMul_zero]
  map_mul' a b := by
    rw [ofMul_mul, map_add, map_add, toMul_add]
  continuous_toFun := by
    refine continuous_toMul.comp (Continuous.comp ?_
      ((lieExpQuotientKerContinuousAddEquiv (I := I) (G := G)).symm.continuous.comp
        continuous_ofMul))
    exact continuous_quot_lift _ ((continuous_lieExpAddMonoidHom (I := I') (G := G')).comp
      φ.continuous_of_finiteDimensional)

/-- The homomorphism `ofLieLinearMap φ hφ` sends `exp X` to `exp (φ X)`. -/
@[simp]
theorem ofLieLinearMap_lieExp
    (φ : LeftInvariantDerivation I G →ₗ[ℝ] LeftInvariantDerivation I' G')
    (hφ : ∀ X ∈ (lieExpAddMonoidHom (I := I) (G := G)).ker,
      φ X ∈ (lieExpAddMonoidHom (I := I') (G := G')).ker) (X : LeftInvariantDerivation I G) :
    ofLieLinearMap φ hφ (lieExp X) = lieExp (φ X) := by
  have h : ofLieLinearMap φ hφ (lieExp X) = Additive.toMul (QuotientAddGroup.lift _
      ((lieExpAddMonoidHom (I := I') (G := G')).comp φ.toAddMonoidHom)
      (fun Y hY ↦ AddMonoidHom.mem_ker.2 (AddMonoidHom.mem_ker.1 (hφ Y hY)))
      ((lieExpQuotientKerContinuousAddEquiv (I := I) (G := G)).symm
        (Additive.ofMul (lieExp X)))) :=
    rfl
  rw [h, lieExpQuotientKerContinuousAddEquiv_symm_apply, QuotientAddGroup.lift_mk',
    AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, lieExpAddMonoidHom_apply, toMul_ofMul]

/-- **The Lie map of `ofLieLinearMap φ hφ` is `φ`.** -/
@[simp]
theorem lieMap_ofLieLinearMap
    (φ : LeftInvariantDerivation I G →ₗ[ℝ] LeftInvariantDerivation I' G')
    (hφ : ∀ X ∈ (lieExpAddMonoidHom (I := I) (G := G)).ker,
      φ X ∈ (lieExpAddMonoidHom (I := I') (G := G')).ker) (X : LeftInvariantDerivation I G) :
    lieMap (I := I) (I' := I') (ofLieLinearMap φ hφ) X = φ X :=
  lieMap_apply_eq_of_lieExp _ φ (fun Y ↦ (ofLieLinearMap_lieExp φ hφ Y).symm) X

/-- **Continuous homomorphisms of commutative Lie groups are lattice maps.** For a preconnected
commutative Lie group `G`, differentiation identifies continuous homomorphisms `G → G'` with the
real-linear maps `𝔤 → 𝔤'` carrying `ker(exp)` into `ker(exp')`. -/
@[expose] def lieMapKerEquiv :
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
  rfl

end ContinuousMonoidHom

/-! ### Checks: multiplication by `n` and dimension zero -/

namespace ContinuousMonoidHom

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  [IsMulCommutative G] [IsTopologicalGroup G]

/-- **The `n`-th power map differentiates to multiplication by `n`.** -/
@[simp]
theorem lieMap_powContinuousMonoidHom (n : ℕ) (X : LeftInvariantDerivation I G) :
    lieMap (I := I) (I' := I) (powContinuousMonoidHom G n) X = n • X := by
  refine lieMap_apply_eq_of_lieExp _ ((n : ℝ) • LinearMap.id) (fun Y ↦ ?_) X |>.trans ?_
  · rw [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, lieExp_nsmul,
      powContinuousMonoidHom_apply]
  · rw [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul]

/-- On the kernel of the exponential, the `n`-th power map acts as `λ ↦ n λ`; for `n = 2` this
is the Check of AbelianSchemesAndArithmeticModuli §A5.1 that multiplication by two acts as
`λ ↦ 2 λ` on the lattice. -/
theorem lieMapKer_powContinuousMonoidHom (n : ℕ) :
    lieMapKer (I := I) (I' := I) (powContinuousMonoidHom G n) = n • AddMonoidHom.id _ := by
  ext X
  rw [coe_lieMapKer_apply, lieMap_powContinuousMonoidHom]
  rfl

/-- Under the identification `𝔤 / ker(exp) ≃ G` of a preconnected commutative Lie group,
multiplication by `n` on the quotient, which descends from `X ↦ n X`, is the `n`-th power map. -/
theorem lieExpQuotientKerContinuousAddEquiv_nsmul [PreconnectedSpace G] (n : ℕ)
    (q : LeftInvariantDerivation I G ⧸ (lieExpAddMonoidHom (I := I) (G := G)).ker) :
    lieExpQuotientKerContinuousAddEquiv (I := I) (G := G) (n • q) =
      Additive.ofMul (Additive.toMul (lieExpQuotientKerContinuousAddEquiv (I := I) q) ^ n) := by
  rw [map_nsmul, ofMul_pow, ofMul_toMul]

end ContinuousMonoidHom

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  [IsMulCommutative G]

/-- **Dimension zero.** If the Lie algebra is zero, so is the kernel of the exponential. -/
theorem ker_lieExpAddMonoidHom_eq_bot_of_subsingleton
    [Subsingleton (LeftInvariantDerivation I G)] :
    (lieExpAddMonoidHom (I := I) (G := G)).ker = ⊥ :=
  Subsingleton.elim _ _

end TauCeti

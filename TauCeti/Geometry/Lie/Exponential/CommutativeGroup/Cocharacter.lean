/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Complex.Circle.ContinuousMonoidHom
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Character

/-!
# Cocharacters and the period lattice

A **cocharacter** of a Lie group `G` is a continuous homomorphism `ψ : Circle → G`. With the
circle period `2π` of `Circle.exp t = e^{it}`, its **coweight** is the Lie-algebra vector

`X_ψ = dψ(∂_θ)`

(`ContinuousMonoidHom.lieCoweight`), the image under the Lie map of `ψ` of the generator
`circleExpGenerator` of `Circle.exp`. It is characterized by

`ψ (Circle.exp t) = exp (t X_ψ)`

(`ContinuousMonoidHom.apply_circleExp_eq_lieExp_lieCoweight`,
`ContinuousMonoidHom.eq_lieCoweight`), so a cocharacter is determined by its coweight
(`ContinuousMonoidHom.lieCoweight_injective`). Coweights are natural: the coweight of `f ∘ ψ` is
`df(X_ψ)`.

**Characters pair integrally with cocharacters.** For a character `χ : G → Circle` with real
weight `α_χ = (1/i) dχ` (`ContinuousMonoidHom.lieWeight`), the composite `χ ∘ ψ` is a continuous
endomorphism of the circle, and the number `α_χ(X_ψ)` is the integer `n` with
`χ (ψ z) = z ^ n` (`ContinuousMonoidHom.lieWeight_lieCoweight_eq_intCast_iff`,
`ContinuousMonoidHom.exists_lieWeight_lieCoweight_eq_intCast`). For `G` the circle and `χ` the
identity this says that the continuous endomorphisms of the circle are the powers `z ↦ z ^ n`, with
weight `n` (`ContinuousMonoidHom.lieWeight_circleExpGenerator_eq_intCast_iff`). By naturality of
weights and coweights, restriction of characters along a homomorphism `f` is dual to pushforward of
cocharacters: `α_(χ ∘ f)(X_ψ) = α_χ(X_(f ∘ ψ))`
(`ContinuousMonoidHom.lieWeight_comp_apply_lieCoweight`). None of this needs `G` to be
commutative.

**The cocharacters of a commutative Lie group are its period lattice.** For commutative `G`,
coweights lie in the period lattice `Λ_ℤ = (2π)⁻¹ ker(exp)` (`TauCeti.periodLattice`), since
`exp(2π X_ψ) = ψ(Circle.exp 2π) = 1`, and conversely every `X ∈ Λ_ℤ` is the coweight of the
cocharacter `Circle.exp t ↦ exp(t X)`, which is well defined because `t ↦ exp(t X)` has period
`2π` (`ContinuousMonoidHom.circleLift`). This gives the isomorphism of groups
`Λ_ℤ ≃+ Additive (Circle →ₜ* G)` (`TauCeti.periodLatticeEquivCocharacter`): addition in `Λ_ℤ` is
the pointwise product of cocharacters, so zero, negation and integer multiples are the trivial
cocharacter and pointwise inverses and powers.
Correspondingly, the coweight of the trivial cocharacter is zero, and the coweight of a pointwise
product, inverse or power of cocharacters is the sum, negative or integer multiple of coweights
(`ContinuousMonoidHom.lieCoweight_one`, `ContinuousMonoidHom.lieCoweight_eq_add_of_apply_eq_mul`,
`ContinuousMonoidHom.lieCoweight_eq_neg_of_apply_eq_inv`,
`ContinuousMonoidHom.lieCoweight_eq_zsmul_of_apply_eq_zpow`). On a connected commutative
Lie group the weights of characters are exactly the functionals integral on `Λ_ℤ`
(`ContinuousMonoidHom.range_lieWeight`), so under the pairing above the characters are identified
with the integral functionals on the cocharacters.

## Main definitions

* `ContinuousMonoidHom.lieCoweight`: the coweight `X_ψ = dψ(∂_θ)` of a cocharacter.
* `TauCeti.periodLatticeEquivCocharacter`: the period lattice of a commutative Lie group is
  isomorphic, as a group, to the group of its cocharacters.

## Main results

* `ContinuousMonoidHom.apply_circleExp_eq_lieExp_lieCoweight`, `ContinuousMonoidHom.eq_lieCoweight`:
  the identity `ψ (Circle.exp t) = exp (t X_ψ)`, and uniqueness of a vector satisfying it.
* `ContinuousMonoidHom.lieCoweight_comp`: naturality of coweights.
* `ContinuousMonoidHom.lieCoweight_one`, `ContinuousMonoidHom.lieCoweight_eq_add_of_apply_eq_mul`,
  `ContinuousMonoidHom.lieCoweight_eq_neg_of_apply_eq_inv`,
  `ContinuousMonoidHom.lieCoweight_eq_zsmul_of_apply_eq_zpow`: coweights of the trivial cocharacter
  and of pointwise products, inverses and powers of cocharacters.
* `ContinuousMonoidHom.lieWeight_lieCoweight_eq_intCast_iff`,
  `ContinuousMonoidHom.exists_lieWeight_lieCoweight_eq_intCast`: the pairing of a character with a
  cocharacter is the integer degree of their composite.
* `ContinuousMonoidHom.lieWeight_comp_apply_lieCoweight`: restriction of characters is dual to
  pushforward of cocharacters.
* `ContinuousMonoidHom.lieCoweight_mem_periodLattice`, `ContinuousMonoidHom.range_lieCoweight`:
  for commutative `G`, the coweights are exactly the elements of the period lattice.
* `TauCeti.periodLatticeEquivCocharacter_apply_circleExp`,
  `TauCeti.lieCoweight_periodLatticeEquivCocharacter`: the cocharacter of `X ∈ Λ_ℤ` sends
  `Circle.exp t` to `exp (t X)`, and its coweight is `X`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map).
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 15 (Tori).
-/

public section

noncomputable section

open Real
open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace ContinuousMonoidHom

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E'] [LieGroup I' ∞ G']

/-! ### The coweight of a cocharacter -/

/-- The **coweight** `X_ψ = dψ(∂_θ)` of a cocharacter `ψ : Circle → G`: the image under the Lie map
of `ψ` of the generator of `Circle.exp`. It is characterized by
`ψ (Circle.exp t) = exp (t X_ψ)` (`ContinuousMonoidHom.apply_circleExp_eq_lieExp_lieCoweight`). -/
def lieCoweight (ψ : Circle →ₜ* G) : LeftInvariantDerivation I G :=
  lieMap (I := 𝓡 1) (I' := I) ψ circleExpGenerator

theorem lieCoweight_def (ψ : Circle →ₜ* G) :
    lieCoweight (I := I) ψ = lieMap (I := 𝓡 1) (I' := I) ψ circleExpGenerator :=
  (rfl)

/-- **Naturality of coweights.** The coweight of `f ∘ ψ` is the image of the coweight of `ψ` under
the Lie map of `f`. -/
theorem lieCoweight_comp (f : G →ₜ* G') (ψ : Circle →ₜ* G) :
    lieCoweight (I := I') (f.comp ψ) = lieMap (I := I) (I' := I') f (lieCoweight ψ) := by
  rw [lieCoweight_def, lieMap_comp (I := 𝓡 1) (I' := I) (I'' := I'), LieHom.comp_apply,
    lieCoweight_def]

/-- The identity cocharacter of the circle has the generator of `Circle.exp` as coweight. -/
@[simp]
theorem lieCoweight_id_circle :
    lieCoweight (I := 𝓡 1) (ContinuousMonoidHom.id Circle) = circleExpGenerator := by
  rw [lieCoweight_def, lieMap_id, one_apply_eq_self]

/-- The pairing of a character with the coweight of a cocharacter is the weight of their composite,
an endomorphism of the circle, at the generator of `Circle.exp`. -/
theorem lieWeight_lieCoweight (χ : G →ₜ* Circle) (ψ : Circle →ₜ* G) :
    lieWeight (I := I) χ (lieCoweight ψ) =
      lieWeight (I := 𝓡 1) (χ.comp ψ) circleExpGenerator := by
  rw [lieWeight_comp (I := 𝓡 1) (I' := I), LinearMap.comp_apply, LieHom.coe_toLinearMap,
    lieCoweight_def]

/-- **Restriction of characters is dual to pushforward of cocharacters**:
`α_(χ ∘ f)(X_ψ) = α_χ(X_(f ∘ ψ))`. -/
theorem lieWeight_comp_apply_lieCoweight (χ : G' →ₜ* Circle) (f : G →ₜ* G')
    (ψ : Circle →ₜ* G) :
    lieWeight (I := I) (χ.comp f) (lieCoweight ψ) =
      lieWeight (I := I') χ (lieCoweight (I := I') (f.comp ψ)) := by
  rw [lieWeight_comp (I := I) (I' := I'), LinearMap.comp_apply, LieHom.coe_toLinearMap,
    lieCoweight_comp (I := I) (I' := I')]

/-! ### The integral pairing of characters and cocharacters -/

/-- **Characters pair integrally with cocharacters**: `α_χ(X_ψ)` is an integer. -/
theorem exists_lieWeight_lieCoweight_eq_intCast (χ : G →ₜ* Circle) (ψ : Circle →ₜ* G) :
    ∃ n : ℤ, lieWeight (I := I) χ (lieCoweight ψ) = n := by
  rw [lieWeight_lieCoweight]
  exact exists_lieWeight_apply_eq_intCast_of_mem_periodLattice _
    circleExpGenerator_mem_periodLattice

/-- **The pairing of a character with a cocharacter is the degree of their composite**:
`α_χ(X_ψ) = n` exactly when `χ (ψ z) = z ^ n` for every `z` on the circle. -/
theorem lieWeight_lieCoweight_eq_intCast_iff (χ : G →ₜ* Circle) (ψ : Circle →ₜ* G) (n : ℤ) :
    lieWeight (I := I) χ (lieCoweight ψ) = n ↔ ∀ z, χ (ψ z) = z ^ n := by
  rw [lieWeight_lieCoweight, lieWeight_circleExpGenerator_eq_intCast_iff, coe_comp]
  simp only [Function.comp_apply]

variable [T2Space G] [BoundarylessManifold I G]

/-- **The defining identity of the coweight**: `ψ (Circle.exp t) = exp (t X_ψ)`. -/
theorem apply_circleExp_eq_lieExp_lieCoweight (ψ : Circle →ₜ* G) (t : ℝ) :
    ψ (Circle.exp t) = lieExp (I := I) (t • lieCoweight ψ) := by
  rw [← lieExp_circleExpGenerator, map_lieExp (I := 𝓡 1) (I' := I), map_smul, lieCoweight_def]

/-- **Uniqueness of the coweight.** A vector `X` with `ψ (Circle.exp t) = exp (t X)` for every `t`
is the coweight of `ψ`. -/
theorem eq_lieCoweight {ψ : Circle →ₜ* G} {X : LeftInvariantDerivation I G}
    (h : ∀ t : ℝ, ψ (Circle.exp t) = lieExp (t • X)) : X = lieCoweight ψ := by
  apply oneParameterSubgroup_injective (I := I) (G := G)
  refine DFunLike.ext _ _ fun t ↦ ?_
  rw [← ofAdd_toAdd t, oneParameterSubgroup_apply, oneParameterSubgroup_apply, ← h,
    apply_circleExp_eq_lieExp_lieCoweight (I := I)]

/-- **Cocharacters are determined by their coweights.** -/
theorem lieCoweight_injective :
    Function.Injective (lieCoweight (I := I) : (Circle →ₜ* G) → LeftInvariantDerivation I G) := by
  intro ψ φ h
  exact ext_circleExp fun t ↦ by
    rw [apply_circleExp_eq_lieExp_lieCoweight (I := I),
      apply_circleExp_eq_lieExp_lieCoweight (I := I), h]

/-- The trivial cocharacter has coweight zero. -/
@[simp]
theorem lieCoweight_one : lieCoweight (I := I) (1 : Circle →ₜ* G) = 0 :=
  (eq_lieCoweight fun t ↦ by rw [smul_zero, lieExp_zero, one_toFun]).symm

/-- The coweight of the pointwise inverse of a cocharacter is the negative of its coweight. -/
theorem lieCoweight_eq_neg_of_apply_eq_inv {ψ φ : Circle →ₜ* G} (h : ∀ z, φ z = (ψ z)⁻¹) :
    lieCoweight (I := I) φ = -lieCoweight ψ :=
  (eq_lieCoweight fun t ↦ by
    rw [h, apply_circleExp_eq_lieExp_lieCoweight (I := I), smul_neg, lieExp_neg]).symm

/-- The coweight of the pointwise `n`-th power of a cocharacter is `n` times its coweight. -/
theorem lieCoweight_eq_zsmul_of_apply_eq_zpow {ψ φ : Circle →ₜ* G} {n : ℤ}
    (h : ∀ z, φ z = ψ z ^ n) :
    lieCoweight (I := I) φ = n • lieCoweight ψ :=
  (eq_lieCoweight fun t ↦ by
    rw [h, ← map_zpow, ← Circle.exp_zsmul, apply_circleExp_eq_lieExp_lieCoweight (I := I),
      smul_assoc, smul_comm n t]).symm

/-- The coweight of a pointwise product of cocharacters is the sum of their coweights. -/
theorem lieCoweight_eq_add_of_apply_eq_mul {ψ₁ ψ₂ ψ : Circle →ₜ* G}
    (h : ∀ z, ψ z = ψ₁ z * ψ₂ z) :
    lieCoweight (I := I) ψ = lieCoweight ψ₁ + lieCoweight ψ₂ := by
  -- Expanding `ψ (z * z)` in two ways shows that `ψ₁ z` and `ψ₂ z` commute.
  have hc : ∀ z, Commute (ψ₁ z) (ψ₂ z) := fun z ↦ by
    have hzz := h (z * z)
    rw [map_mul, map_mul, map_mul, h z, mul_assoc, mul_assoc] at hzz
    have := mul_left_cancel hzz
    rw [← mul_assoc, ← mul_assoc] at this
    exact (mul_right_cancel this).symm
  refine (eq_lieCoweight fun t ↦ ?_).symm
  rw [h, apply_circleExp_eq_lieExp_lieCoweight (I := I),
    apply_circleExp_eq_lieExp_lieCoweight (I := I), smul_add, lieExp_add_of_commute fun s ↦ ?_]
  rw [smul_smul, smul_smul, ← apply_circleExp_eq_lieExp_lieCoweight (I := I),
    ← apply_circleExp_eq_lieExp_lieCoweight (I := I)]
  exact hc _

/-! ### Cocharacters of commutative Lie groups -/

section Commutative

variable [IsMulCommutative G]

/-- **Coweights lie in the period lattice**: `exp(2π X_ψ) = ψ (Circle.exp 2π) = 1`. This is the
preservation of period lattices by `ψ`, applied to the generator of `Circle.exp`. -/
theorem lieCoweight_mem_periodLattice (ψ : Circle →ₜ* G) :
    lieCoweight (I := I) ψ ∈ periodLattice I G :=
  lieMap_mem_periodLattice (I := 𝓡 1) (I' := I) ψ circleExpGenerator_mem_periodLattice

end Commutative

end ContinuousMonoidHom

open ContinuousMonoidHom
open scoped IsMulCommutative

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  [IsMulCommutative G]

/-- The cocharacter `Circle.exp t ↦ exp (t X)` of an element `X` of the period lattice. -/
private def periodLatticeCocharacter (X : periodLattice I G) : Circle →ₜ* G :=
  circleLift (oneParameterSubgroup (X : LeftInvariantDerivation I G))
    (by rw [oneParameterSubgroup_apply]; exact mem_periodLattice.1 X.property)

private theorem periodLatticeCocharacter_circleExp (X : periodLattice I G) (t : ℝ) :
    periodLatticeCocharacter X (Circle.exp t) = lieExp (t • (X : LeftInvariantDerivation I G)) :=
  (circleLift_circleExp _ _ t).trans (oneParameterSubgroup_apply _ t)

variable [IsTopologicalGroup G]

variable (I G) in
/-- **The cocharacters of a commutative Lie group are its period lattice**, as groups. An element
`X` of the period lattice `Λ_ℤ = (2π)⁻¹ ker(exp)` corresponds to the cocharacter
`Circle.exp t ↦ exp (t X)`, and a cocharacter to its coweight. Addition in `Λ_ℤ` is the pointwise
product of cocharacters, so zero, negation and integer multiples are the trivial cocharacter and
pointwise inverses and powers. -/
def periodLatticeEquivCocharacter : periodLattice I G ≃+ Additive (Circle →ₜ* G) where
  toFun X := .ofMul (periodLatticeCocharacter X)
  invFun ψ := ⟨lieCoweight ψ.toMul, lieCoweight_mem_periodLattice ψ.toMul⟩
  left_inv X := Subtype.ext (eq_lieCoweight (periodLatticeCocharacter_circleExp X)).symm
  right_inv ψ := Additive.toMul.injective (circleLift_unique _ _ fun t ↦ by
    rw [oneParameterSubgroup_apply, apply_circleExp_eq_lieExp_lieCoweight (I := I)]).symm
  map_add' X Y := Additive.toMul.injective <| ext_circleExp fun t ↦ by
    simp only [toMul_add, toMul_ofMul, ContinuousMonoidHom.mul_apply,
      periodLatticeCocharacter_circleExp, AddSubgroup.coe_add, smul_add, lieExp_add]

/-- The cocharacter of an element `X` of the period lattice sends `Circle.exp t` to `exp (t X)`. -/
@[simp]
theorem periodLatticeEquivCocharacter_apply_circleExp (X : periodLattice I G) (t : ℝ) :
    (periodLatticeEquivCocharacter I G X).toMul (Circle.exp t) =
      lieExp (t • (X : LeftInvariantDerivation I G)) :=
  periodLatticeCocharacter_circleExp X t

/-- The inverse of `periodLatticeEquivCocharacter` sends a cocharacter to its coweight. -/
@[simp]
theorem coe_periodLatticeEquivCocharacter_symm_apply (ψ : Additive (Circle →ₜ* G)) :
    ((periodLatticeEquivCocharacter I G).symm ψ : LeftInvariantDerivation I G) =
      lieCoweight ψ.toMul :=
  (rfl)

/-- The coweight of the cocharacter of an element of the period lattice is that element. -/
@[simp]
theorem lieCoweight_periodLatticeEquivCocharacter (X : periodLattice I G) :
    lieCoweight (I := I) (periodLatticeEquivCocharacter I G X).toMul =
      (X : LeftInvariantDerivation I G) := by
  rw [← coe_periodLatticeEquivCocharacter_symm_apply, AddEquiv.symm_apply_apply]

end TauCeti

namespace ContinuousMonoidHom

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  [IsMulCommutative G]

/-- **The coweights of a commutative Lie group are exactly the elements of its period lattice.** -/
theorem range_lieCoweight :
    Set.range (lieCoweight (I := I) : (Circle →ₜ* G) → LeftInvariantDerivation I G) =
      periodLattice I G := by
  ext X
  refine ⟨?_, fun hX ↦ ?_⟩
  · rintro ⟨ψ, rfl⟩
    exact lieCoweight_mem_periodLattice ψ
  · let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    exact ⟨(periodLatticeEquivCocharacter I G ⟨X, hX⟩).toMul,
      lieCoweight_periodLatticeEquivCocharacter ⟨X, hX⟩⟩

end ContinuousMonoidHom

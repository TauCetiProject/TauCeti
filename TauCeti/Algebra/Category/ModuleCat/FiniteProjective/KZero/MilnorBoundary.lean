/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable
public import TauCeti.RingTheory.MilnorSquare.PatchedModule

/-!
# The boundary of a Milnor square

Let `π₁ : A₁ →+* Q` and `π₂ : A₂ →+* Q` be ring homomorphisms between arbitrary (possibly
noncommutative) rings, one of which is surjective, and let `D = A₁ ×_Q A₂` be their fibre product,
Mathlib's `RingHom.pullback π₁ π₂`. For `u ∈ GLₙ(Q)` the patched module
`M(u) = {(a, b) ∈ A₁ⁿ × A₂ⁿ | u π₁(a) = π₂(b)}` (`RingHom.patchedSubgroup`) is a finitely
generated projective right `D`-module. Its class `[M(u)] - n[D]` in `K₀(D)` is additive in `u`,
invariant under stabilization, and trivial on the images of invertible matrices over `A₁` and
`A₂`. It therefore descends to the **boundary homomorphism** `δ : K₁(Q) → K₀(D)` of the
Mayer–Vietoris sequence of the Milnor square, `δ([u]) = [M(u)] - n[D]`, which vanishes on the
images of `K₁(A₁)` and `K₁(A₂)`.

The sequence `K₁(A₁) × K₁(A₂) → K₁(Q) → K₀(D)` is exact at `K₁(Q)`, the first map being
`(y₁, y₂) ↦ K₁(π₁) y₁ / K₁(π₂) y₂`. If `δ([u]) = 0` then, after stabilizing `u`, the patched module
`M(u)` is free, `M(u) ≅ M(1)`. An isomorphism of patched modules is given by invertible matrices
`g₁` over `A₁` and `g₂` over `A₂` with `π₁(g₁) = π₂(g₂) u`
(`RingHom.nonempty_patchedSubgroup_equiv_iff`), so `[u] = K₁(π₁)[g₁] / K₁(π₂)[g₂]`.

Here `K₁` is Tau Ceti's multiplicative `TauCeti.AlgebraicK1`; the boundary is stated on its
additive form `Additive (AlgebraicK1 Q)`, so that `δ([uv]) = δ([u]) + δ([v])`.

## Main definitions

* `RingHom.patchedFiniteProjective π₁ π₂ h u`: `M(u)` as an object of
  `TauCeti.FiniteProjectiveRight D`, when one leg is surjective.
* `RingHom.milnorBoundary π₁ π₂ h`: the boundary `δ : K₁(Q) → K₀(D)`.

## Main results

* `RingHom.milnorBoundary_mk`: `δ([u]) = [M(u)] - n[D]`.
* `RingHom.milnorBoundary_mk_eq_zero_iff`: `δ([u]) = 0` if and only if `M(u)` is stably free of
  rank `n`.
* `RingHom.milnorBoundary_map_fst`, `RingHom.milnorBoundary_map_snd`: `δ` vanishes on the images
  of `K₁(A₁)` and `K₁(A₂)`.
* `RingHom.ker_milnorBoundary`, `RingHom.milnorBoundary_ofMul_eq_zero_iff`: exactness of the
  Mayer–Vietoris sequence at `K₁(Q)`, the kernel of `δ` being the image of `K₁(A₁) × K₁(A₂)`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §2
  (the projective modules `M(P₁, P₂, h)` over a fibre product, shown projective first for free
  `P₁`, `P₂` by lifting Whitehead's elementary matrix `h ⊕ h⁻¹`), and Theorem 6.4 (the boundary
  `K₁(Q) → K₀(D)` of the Mayer–Vietoris sequence).
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2, the
  Mayer–Vietoris paragraph before Theorem 2.9 (the boundary `∂ₙ(g) = [P] - [Rⁿ]`), and Chapter
  III, Theorem 2.6.
-/

public section

noncomputable section

open CategoryTheory Matrix TauCeti

namespace RingHom

universe u₁ u₂ v

variable {A₁ : Type u₁} {A₂ : Type u₂} {Q : Type v} [Ring A₁] [Ring A₂] [Ring Q]
  {π₁ : A₁ →+* Q} {π₂ : A₂ →+* Q} {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The class of a patched module in `K₀` -/

section KZero

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable (π₁ π₂) in
/-- With one surjective leg, the patched module `M(u)` as an object of the category
`TauCeti.FiniteProjectiveRight` of finitely generated projective right modules over the fibre
product `π₁.pullback π₂`. -/
def patchedFiniteProjective (h : Function.Surjective π₁ ∨ Function.Surjective π₂) (u : GL ι Q) :
    FiniteProjectiveRight (π₁.pullback π₂) :=
  ⟨ModuleCat.of _ (π₁.patchedSubgroup π₂ u),
    finiteProjectiveModules_iff.2 ⟨finite_patchedSubgroup h u, projective_patchedSubgroup h u⟩⟩

@[simp]
theorem patchedFiniteProjective_obj (h : Function.Surjective π₁ ∨ Function.Surjective π₂)
    (u : GL ι Q) :
    (patchedFiniteProjective π₁ π₂ h u).obj = ModuleCat.of _ (π₁.patchedSubgroup π₂ u) :=
  (rfl)

section Fact

/-! The class `[M(u)] - n[D]` and its properties only make sense when one leg is surjective. This
hypothesis is carried by a `Fact`, so that the finiteness and projectivity of the patched modules
are found by instance search. -/

variable [Fact (Function.Surjective π₁ ∨ Function.Surjective π₂)]

@[local instance]
private theorem finite_patchedSubgroup_of_fact (u : GL n Q) :
    Module.Finite (π₁.pullback π₂)ᵐᵒᵖ (π₁.patchedSubgroup π₂ u) :=
  finite_patchedSubgroup Fact.out u

@[local instance]
private theorem projective_patchedSubgroup_of_fact (u : GL n Q) :
    Module.Projective (π₁.pullback π₂)ᵐᵒᵖ (π₁.patchedSubgroup π₂ u) :=
  projective_patchedSubgroup Fact.out u

variable (π₁ π₂) in
/-- The class `[M(u)] - n[D]` in `K₀(D)` of the patched module of `u ∈ GLₙ(Q)`. -/
private def patchedClass (u : GL ι Q) : KZero (π₁.pullback π₂) :=
  FiniteProjectiveModules.classOf _ (π₁.patchedSubgroup π₂ u) (Fintype.card ι)

/-- Isomorphic patched modules of matrices of the same size have the same class. -/
private theorem patchedClass_congr {u u' : GL ι Q}
    (e : π₁.patchedSubgroup π₂ u ≃ₗ[(π₁.pullback π₂)ᵐᵒᵖ] π₁.patchedSubgroup π₂ u') :
    patchedClass π₁ π₂ u = patchedClass π₁ π₂ u' :=
  FiniteProjectiveModules.classOf_congr e _

/-- The patched module of the identity is free, so its class vanishes. -/
private theorem patchedClass_one : patchedClass π₁ π₂ (1 : GL ι Q) = 0 := by
  rw [patchedClass, FiniteProjectiveModules.classOf_congr ((patchedSubgroupOneEquiv π₁ π₂ ι).trans
    (LinearEquiv.funCongrLeft _ _ (Fintype.equivFin ι).symm)), FiniteProjectiveModules.classOf_free]

/-- The class of the patched module of a block sum is the sum of the classes. -/
private theorem patchedClass_fromBlocksGL (u : GL ι Q) (v : GL κ Q) :
    patchedClass π₁ π₂ (fromBlocksGL (u, v)) = patchedClass π₁ π₂ u + patchedClass π₁ π₂ v := by
  rw [patchedClass, patchedClass, patchedClass,
    FiniteProjectiveModules.classOf_congr (patchedSubgroupProdEquiv π₁ π₂ u v).symm,
    Fintype.card_sum, FiniteProjectiveModules.classOf_prod]

/-- Relabelling the indices does not change the class of the patched module. -/
private theorem patchedClass_reindexGL (e : ι ≃ κ) (u : GL ι Q) :
    patchedClass π₁ π₂ (e.reindexGL Q u) = patchedClass π₁ π₂ u := by
  rw [patchedClass, patchedClass, Fintype.card_congr e,
    FiniteProjectiveModules.classOf_congr (patchedSubgroupReindexEquiv π₁ π₂ e u).symm]

/-- **Additivity of the class of the patched module**: `[M(uv)] - n[D]` is the sum of the classes
of `M(u)` and `M(v)`. The block matrix `uv ⊕ 1` is `(u ⊕ v)(v ⊕ v⁻¹)` and also
`(u ⊕ u⁻¹)(v ⊕ u)`, and the elementary factor lifts along whichever leg is surjective. -/
private theorem patchedClass_mul (u v : GL ι Q) :
    patchedClass π₁ π₂ (u * v) = patchedClass π₁ π₂ u + patchedClass π₁ π₂ v := by
  rw [← add_zero (patchedClass π₁ π₂ (u * v)), ← patchedClass_one (ι := ι),
    ← patchedClass_fromBlocksGL]
  rcases (Fact.out : Function.Surjective π₁ ∨ Function.Surjective π₂) with hπ₁ | hπ₂
  · have hw : fromBlocksGL (u * v, 1) = fromBlocksGL (u, v) * fromBlocksGL (v, v⁻¹) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel]
    obtain ⟨e⟩ := nonempty_patchedSubgroup_mul_elementary_equiv (π₂ := π₂) hπ₁ (fromBlocksGL (u, v))
      (fromBlocksGL_inv_mem_elementarySubgroup v)
    rw [hw, patchedClass_congr e, patchedClass_fromBlocksGL]
  · have hw : fromBlocksGL (u * v, 1) = fromBlocksGL (u, u⁻¹) * fromBlocksGL (v, u) := by
      rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel]
    obtain ⟨e⟩ := nonempty_patchedSubgroup_elementary_mul_equiv (π₁ := π₁) hπ₂ (fromBlocksGL (v, u))
      (fromBlocksGL_inv_mem_elementarySubgroup u)
    rw [hw, patchedClass_congr e, patchedClass_fromBlocksGL, add_comm]

/-- Stabilization `u ↦ u ⊕ 1` does not change the class of the patched module. -/
private theorem patchedClass_stabilizeGL {m k : ℕ} (hmk : m ≤ k) (u : GL (Fin m) Q) :
    patchedClass π₁ π₂ (stabilizeGL Q hmk u) = patchedClass π₁ π₂ u := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmk
  rw [stabilizeGL_eq_reindexGL_fromBlocksGL, patchedClass_reindexGL, patchedClass_fromBlocksGL,
    patchedClass_one, add_zero]

end Fact

/-! ## The boundary homomorphism -/

variable (π₁ π₂) in
/-- **The boundary of a Milnor square**: for ring homomorphisms `π₁ : A₁ →+* Q` and
`π₂ : A₂ →+* Q`, one of which is surjective, the homomorphism `δ : K₁(Q) → K₀(D)` to the
projective `K₀` of the fibre product `D = π₁.pullback π₂`, sending the class of `u ∈ GLₙ(Q)` to
`[M(u)] - n[D]` (`RingHom.milnorBoundary_mk`). Algebraic `K₁` is written additively, as
`Additive (TauCeti.AlgebraicK1 Q)`. -/
def milnorBoundary (h : Function.Surjective π₁ ∨ Function.Surjective π₂) :
    Additive (AlgebraicK1 Q) →+ KZero (π₁.pullback π₂) :=
  have : Fact (Function.Surjective π₁ ∨ Function.Surjective π₂) := ⟨h⟩
  MonoidHom.toAdditiveLeft <| AlgebraicK1.lift
    (fun _ ↦
      { toFun u := Multiplicative.ofAdd (patchedClass π₁ π₂ u)
        map_one' := congrArg Multiplicative.ofAdd patchedClass_one
        map_mul' u v := congrArg Multiplicative.ofAdd (patchedClass_mul u v) })
    fun _ _ hmk u ↦ congrArg Multiplicative.ofAdd (patchedClass_stabilizeGL hmk u)

variable (h : Function.Surjective π₁ ∨ Function.Surjective π₂)

private theorem milnorBoundary_mk_eq_patchedClass [Fact (Function.Surjective π₁ ∨
    Function.Surjective π₂)] (k : ℕ) (u : GL (Fin k) Q) :
    milnorBoundary π₁ π₂ h (Additive.ofMul (AlgebraicK1.mk Q k u)) = patchedClass π₁ π₂ u := by
  simp [milnorBoundary]

/-- **The boundary formula** `δ([u]) = [M(u)] - n[D]` for `u ∈ GLₙ(Q)`. -/
@[simp]
theorem milnorBoundary_mk (k : ℕ) (u : GL (Fin k) Q) :
    milnorBoundary π₁ π₂ h (Additive.ofMul (AlgebraicK1.mk Q k u)) =
      SplitK0.of.{max u₁ u₂} (patchedFiniteProjective π₁ π₂ h u) -
        k • SplitK0.of.{max u₁ u₂} (finiteProjectiveModulesRegular (π₁.pullback π₂)ᵐᵒᵖ) := by
  have : Fact (Function.Surjective π₁ ∨ Function.Surjective π₂) := ⟨h⟩
  -- Unfolding `patchedFiniteProjective` and `finiteProjectiveModulesRegular` exhibits them as the
  -- two objects of `classOf_def`.
  rw [milnorBoundary_mk_eq_patchedClass, patchedClass, FiniteProjectiveModules.classOf_def,
    Fintype.card_fin, patchedFiniteProjective, finiteProjectiveModulesRegular]

/-- **The kernel of the boundary**: `δ([u]) = 0` for `u ∈ GLₙ(Q)` if and only if the patched
module `M(u)` is stably free of rank `n`, that is `M(u) × Dʲ ≅ Dⁿ⁺ʲ` for some `j`. -/
theorem milnorBoundary_mk_eq_zero_iff (k : ℕ) (u : GL (Fin k) Q) :
    milnorBoundary π₁ π₂ h (Additive.ofMul (AlgebraicK1.mk Q k u)) = 0 ↔
      ∃ j : ℕ, Nonempty ((π₁.patchedSubgroup π₂ u × (Fin j → (π₁.pullback π₂)ᵐᵒᵖ)) ≃ₗ[
        (π₁.pullback π₂)ᵐᵒᵖ] (Fin (k + j) → (π₁.pullback π₂)ᵐᵒᵖ)) := by
  have : Fact (Function.Surjective π₁ ∨ Function.Surjective π₂) := ⟨h⟩
  have := finite_patchedSubgroup h u
  have := projective_patchedSubgroup h u
  rw [milnorBoundary_mk_eq_patchedClass, patchedClass, Fintype.card_fin]
  exact FiniteProjectiveModules.classOf_eq_zero_iff k

/-- **The boundary vanishes on the image of `K₁(A₁)`**: for `g ∈ GLₙ(A₁)` the patched module of
`π₁(g)` is free, `M(π₁(g)) ≅ M(1) ≅ Dⁿ`. -/
@[simp]
theorem milnorBoundary_map_fst (x : AlgebraicK1 A₁) :
    milnorBoundary π₁ π₂ h (Additive.ofMul (AlgebraicK1.map π₁ x)) = 0 := by
  have : Fact (Function.Surjective π₁ ∨ Function.Surjective π₂) := ⟨h⟩
  obtain ⟨k, g, rfl⟩ := AlgebraicK1.exists_mk x
  obtain ⟨e⟩ := nonempty_patchedSubgroup_map_fst_equiv (π₂ := π₂) g
  rw [AlgebraicK1.map_mk, milnorBoundary_mk_eq_patchedClass, patchedClass_congr e,
    patchedClass_one]

/-- **The boundary vanishes on the image of `K₁(A₂)`**: for `g ∈ GLₙ(A₂)` the patched module of
`π₂(g)` is free, `M(π₂(g)) ≅ M(1) ≅ Dⁿ`. -/
@[simp]
theorem milnorBoundary_map_snd (x : AlgebraicK1 A₂) :
    milnorBoundary π₁ π₂ h (Additive.ofMul (AlgebraicK1.map π₂ x)) = 0 := by
  have : Fact (Function.Surjective π₁ ∨ Function.Surjective π₂) := ⟨h⟩
  obtain ⟨k, g, rfl⟩ := AlgebraicK1.exists_mk x
  obtain ⟨e⟩ := nonempty_patchedSubgroup_map_snd_equiv (π₁ := π₁) g
  rw [AlgebraicK1.map_mk, milnorBoundary_mk_eq_patchedClass, patchedClass_congr e,
    patchedClass_one]

/-! ## Exactness at `K₁(Q)` -/

/-- If `M(u) × Dʲ ≅ Dᵏ⁺ʲ` for `u ∈ GLₖ(Q)`, then the patched module of the stabilization `u ⊕ 1` of
`u` to size `k + j` is isomorphic to `M(1) ≅ Dᵏ⁺ʲ`. -/
private theorem nonempty_patchedSubgroup_stabilizeGL_equiv {k j : ℕ} {u : GL (Fin k) Q}
    (e : (π₁.patchedSubgroup π₂ u × (Fin j → (π₁.pullback π₂)ᵐᵒᵖ)) ≃ₗ[(π₁.pullback π₂)ᵐᵒᵖ]
      (Fin (k + j) → (π₁.pullback π₂)ᵐᵒᵖ)) :
    Nonempty (π₁.patchedSubgroup π₂ (stabilizeGL Q (Nat.le_add_right k j) u) ≃ₗ[
      (π₁.pullback π₂)ᵐᵒᵖ] π₁.patchedSubgroup π₂ (1 : GL (Fin (k + j)) Q)) := by
  rw [stabilizeGL_eq_reindexGL_fromBlocksGL]
  exact ⟨(patchedSubgroupReindexEquiv π₁ π₂ finSumFinEquiv _).symm ≪≫ₗ
    (patchedSubgroupProdEquiv π₁ π₂ u 1).symm ≪≫ₗ
    (LinearEquiv.refl _ _).prodCongr (patchedSubgroupOneEquiv π₁ π₂ (Fin j)) ≪≫ₗ e ≪≫ₗ
    (patchedSubgroupOneEquiv π₁ π₂ (Fin (k + j))).symm⟩

/-- **Exactness of the Mayer–Vietoris sequence at `K₁(Q)`, elementwise.** With one surjective leg,
the boundary `δ` vanishes on a class `x` of `K₁(Q)` if and only if `x = K₁(π₁) y₁ / K₁(π₂) y₂` for
classes `y₁` of `K₁(A₁)` and `y₂` of `K₁(A₂)`. -/
theorem milnorBoundary_ofMul_eq_zero_iff (x : AlgebraicK1 Q) :
    milnorBoundary π₁ π₂ h (Additive.ofMul x) = 0 ↔
      x ∈ ((AlgebraicK1.map π₁).comp (MonoidHom.fst _ _) /
        (AlgebraicK1.map π₂).comp (MonoidHom.snd _ _)).range := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · -- If `δ([u]) = 0` then `M(u ⊕ 1) ≅ M(1)` for a stabilization `u ⊕ 1` of `u`, so `u ⊕ 1` lies in
    -- the double coset of `1`, that is, `u ⊕ 1 = π₂(g₂)⁻¹ π₁(g₁)`.
    obtain ⟨k, u, rfl⟩ := AlgebraicK1.exists_mk x
    obtain ⟨j, ⟨e⟩⟩ := (milnorBoundary_mk_eq_zero_iff h k u).1 hx
    obtain ⟨g₁, g₂, hg⟩ :=
      (nonempty_patchedSubgroup_equiv_iff h).1 (nonempty_patchedSubgroup_stabilizeGL_equiv e)
    refine ⟨(AlgebraicK1.mk A₁ (k + j) g₁, AlgebraicK1.mk A₂ (k + j) g₂), ?_⟩
    rw [← AlgebraicK1.mk_stabilizeGL (Nat.le_add_right k j), eq_inv_mul_of_mul_eq hg.symm]
    simp [AlgebraicK1.map_mk, inv_mul_eq_div]
  · rintro ⟨⟨y₁, y₂⟩, rfl⟩
    simp [ofMul_div]

/-- **Exactness of the Mayer–Vietoris sequence at `K₁(Q)`.** For ring homomorphisms
`π₁ : A₁ →+* Q` and `π₂ : A₂ →+* Q`, at least one of which is surjective, the kernel of the
boundary `δ : K₁(Q) → K₀(A₁ ×_Q A₂)` is the image of `K₁(A₁) × K₁(A₂) → K₁(Q)`,
`(y₁, y₂) ↦ K₁(π₁) y₁ / K₁(π₂) y₂`. Algebraic `K₁` is multiplicative, so this image is a
subgroup of `K₁(Q)`, viewed as an additive subgroup of `Additive (AlgebraicK1 Q)`. -/
theorem ker_milnorBoundary :
    (milnorBoundary π₁ π₂ h).ker = Subgroup.toAddSubgroup
      ((AlgebraicK1.map π₁).comp (MonoidHom.fst _ _) /
        (AlgebraicK1.map π₂).comp (MonoidHom.snd _ _)).range := by
  ext x
  rw [AddMonoidHom.mem_ker, Additive.mem_toAddSubgroup, ← milnorBoundary_ofMul_eq_zero_iff,
    ofMul_toMul]

end KZero

end RingHom

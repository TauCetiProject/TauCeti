/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Neg
public import TauCeti.LinearAlgebra.RootSystem.Opposition.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.BasedAut
import TauCeti.LinearAlgebra.RootSystem.Weyl.Automorphism

/-!
# The opposition involution as a based automorphism

Let `P` be a finite reduced crystallographic root pairing over a characteristic-zero domain, with
a base `b` and longest Weyl element `w₀`. The opposition involution `TauCeti.opposition` is the
action of `-w₀` on root indices. This file shows that `-w₀` is an actual automorphism of the root
pairing fixing `b`, the **opposition automorphism** `δ = -w₀`, and records its equations.

The automorphism is the product of the central automorphism `-1`
(`RootPairing.Equiv.neg`) with `w₀`. It acts on weights by `x ↦ -(w₀ • x)`, on root indices by
`TauCeti.opposition`, and it carries the simple roots of `b` onto themselves. Since it is an
automorphism, it preserves the root pairings, so the induced permutation `TauCeti.oppositionPerm`
of the simple roots is a symmetry of the Cartan matrix, read with its orientation
(`RootPairing.pairing_opposition` and `RootPairing.cartanMatrix_oppositionPerm`, which need only
the opposition involution and are proved in
`TauCeti/LinearAlgebra/RootSystem/Opposition/Basic.lean`). On the coroot functionals it matches the
coroot of `opposition i` after `δ` with the coroot of `i` before: in particular `δ` carries a weight
whose simple coroot values are those of the fundamental weight `ϖᵢ` to one with the values of
`ϖ_{opposition i}`.

In the decomposition `Aut(P) = W ⋊ Aut(P, b)` of `RootPairing.Base.semidirectProductMulEquiv`,
the automorphism `-1` has Weyl factor `w₀` and based factor `δ`. This characterises `δ` without
reference to `w₀`: it is the only based automorphism `g` with `-g` in the Weyl group. The
characterisation gives the change of base: the opposition automorphism of the base `b.map e`
transported along an equivalence `e` of root pairings is the conjugate `e δ e⁻¹`; for an
automorphism `g` this is `g δ g⁻¹`.

Finally `δ` is the identity exactly when `w₀ = -1`, and for a root system this happens exactly
when the opposition involution fixes every simple root. This is the root-system side of the
criterion that every finite-dimensional module of a semisimple Lie algebra is self-dual.

## Main definitions

* `RootPairing.oppositionAut`: the opposition automorphism `δ = -w₀` of a base.

## Main results

* `RootPairing.oppositionAut_smul`, `RootPairing.oppositionAut_indexEquiv_apply`: `δ` acts on
  weights by `x ↦ -(w₀ • x)` and on root indices by the opposition involution.
* `RootPairing.oppositionAut_mem_basedAut`: **`δ` is a based automorphism.**
* `RootPairing.oppositionAut_mul_self`: `δ` is an involution.
* `RootPairing.coroot'_oppositionAut_smul` and
  `RootPairing.coroot'_oppositionAut_smul_eq_ite`: the coroot values of `δ x`, and the image of a
  fundamental weight.
* `RootPairing.semidirectProductMulEquiv_symm_neg`: the factors of `-1` are `w₀` and `δ`.
* `RootPairing.eq_oppositionAut_iff_neg_mul_mem_weylGroup`: `δ` is the only based automorphism
  whose negative is in the Weyl group.
* `RootPairing.oppositionAut_map`, `RootPairing.oppositionAut_map_eq_mul_mul_inv`,
  `RootPairing.opposition_map`: change of base.
* `RootPairing.oppositionAut_eq_one_iff`,
  `RootPairing.oppositionAut_eq_one_iff_forall_longestElement_smul_eq_neg` and
  `RootPairing.oppositionAut_eq_one_iff_forall_opposition_eq`: `δ = 1` exactly when `w₀ = -1`,
  and, for a root system, exactly when the opposition involution fixes every simple root.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Ch. VI, §1.6 (the longest element `w₀` and the
  involution `-w₀` of a base).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §10.3 (the
  longest element) and §13.1 (fundamental weights).
-/

public section

namespace RootPairing

open TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N)
  [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- **The opposition automorphism** `δ = -w₀` of a base: the product of the central automorphism
`-1` with the longest element `w₀` of the Weyl group. It acts on root indices by the opposition
involution `TauCeti.opposition` (`RootPairing.oppositionAut_indexEquiv_apply`) and fixes the base
(`RootPairing.oppositionAut_mem_basedAut`). -/
noncomputable def oppositionAut : P.Aut :=
  Equiv.neg P * (longestElement P b : P.Aut)

/-- The opposition automorphism is `-1` times the longest element. -/
theorem oppositionAut_def : oppositionAut P b = Equiv.neg P * (longestElement P b : P.Aut) :=
  (rfl)

/-- **The opposition automorphism acts on weights by `x ↦ -(w₀ • x)`.** -/
@[simp]
theorem oppositionAut_smul (x : M) : oppositionAut P b • x = -(longestElement P b • x) := by
  rw [oppositionAut_def, mul_smul, Equiv.neg_smul_eq_neg, Subgroup.smul_def]

/-- The opposition automorphism acts on weights by the longest element followed by `-1`. -/
@[simp]
theorem oppositionAut_weightEquiv :
    (oppositionAut P b).weightEquiv =
      (longestElement P b : P.Aut).weightEquiv ≪≫ₗ LinearEquiv.neg R := by
  rw [oppositionAut_def, Equiv.mul_eq_comp, Equiv.weightEquiv_comp_toLin,
    Equiv.neg_weightEquiv]

/-- The opposition automorphism acts on coweights by `-1` followed by the action of the longest
element, `RootPairing.Equiv.coweightEquiv` being contravariant. -/
@[simp]
theorem oppositionAut_coweightEquiv :
    (oppositionAut P b).coweightEquiv =
      LinearEquiv.neg R ≪≫ₗ (longestElement P b : P.Aut).coweightEquiv := by
  rw [oppositionAut_def, Equiv.mul_eq_comp, Equiv.coweightEquiv_comp_toLin,
    Equiv.neg_coweightEquiv]

/-- **The opposition automorphism acts on root indices by the opposition involution.** -/
@[simp]
theorem oppositionAut_indexEquiv_apply (i : ι) :
    (oppositionAut P b).indexEquiv i = opposition P b i :=
  P.root.injective <| by rw [Equiv.root_indexEquiv_eq_smul, oppositionAut_smul, root_opposition]

/-- The inverse of the action of the opposition automorphism on root indices is again the
opposition involution. -/
@[simp]
theorem oppositionAut_indexEquiv_symm_apply (i : ι) :
    (oppositionAut P b).indexEquiv.symm i = opposition P b i := by
  rw [_root_.Equiv.symm_apply_eq, oppositionAut_indexEquiv_apply, opposition_opposition]

/-- **The opposition automorphism is a based automorphism**: it carries the simple roots of `b`
onto themselves. -/
theorem oppositionAut_mem_basedAut : oppositionAut P b ∈ b.basedAut :=
  Base.mem_basedAut_iff_forall_mem_support.mpr fun i hi ↦ by
    simpa using opposition_mem_support P b hi

/-- The opposition automorphism fixes the base. -/
@[simp]
theorem map_oppositionAut : b.map (oppositionAut P b) = b :=
  Base.map_eq_of_mem_basedAut (oppositionAut_mem_basedAut P b)

/-- **The opposition automorphism is an involution.**

Not a `simp` lemma: `RootPairing.Equiv.mul_eq_comp` rewrites the product in `P.Aut` first. -/
theorem oppositionAut_mul_self : oppositionAut P b * oppositionAut P b = 1 := by
  rw [oppositionAut_def, (Equiv.commute_neg _).symm.mul_mul_mul_comm, Equiv.neg_mul_neg,
    longestElement_mul_longestElement, one_mul]

/-- The opposition automorphism is an involution, stated with `RootPairing.Equiv.comp`, the `simp`
normal form of products in `P.Aut`. -/
@[simp]
theorem oppositionAut_comp_self : (oppositionAut P b).comp (oppositionAut P b) = 1 := by
  rw [← Equiv.mul_eq_comp, oppositionAut_mul_self]

/-- The square of the opposition automorphism is trivial. -/
@[simp]
theorem oppositionAut_sq : oppositionAut P b ^ 2 = 1 := by
  rw [sq, oppositionAut_mul_self]

/-- The opposition automorphism is its own inverse. -/
@[simp]
theorem oppositionAut_inv : (oppositionAut P b)⁻¹ = oppositionAut P b :=
  inv_eq_of_mul_eq_one_right (oppositionAut_mul_self P b)

/-! ### Coroots and fundamental weights -/

/-- **The coroot values of `δ x` are those of `x`, permuted by the opposition involution.** Like
`TauCeti.coroot'_opposition` it is stated with `P.coroot'` and tagged `@[grind =]` rather than
`@[simp]`, `P.coroot' j x` not being in simp-normal form. -/
@[grind =]
theorem coroot'_oppositionAut_smul (j : ι) (x : M) :
    P.coroot' j (oppositionAut P b • x) = P.coroot' (opposition P b j) x := by
  rw [coroot'_smul, oppositionAut_indexEquiv_symm_apply]

/-- **The opposition automorphism carries the fundamental weight `ϖᵢ` to `ϖ_{opposition i}`**: if
the simple coroot values of `x` are those of `ϖᵢ`, then the simple coroot values of `δ x` are those
of `ϖ_{opposition i}`. -/
theorem coroot'_oppositionAut_smul_eq_ite [DecidableEq ι] {i : ι} {x : M}
    (hx : ∀ j ∈ b.support, P.coroot' j x = if j = i then 1 else 0) {j : ι} (hj : j ∈ b.support) :
    P.coroot' j (oppositionAut P b • x) = if j = opposition P b i then 1 else 0 := by
  rw [coroot'_oppositionAut_smul, hx _ (opposition_mem_support P b hj)]
  exact if_congr ⟨fun h ↦ by rw [← h, opposition_opposition], fun h ↦ by
    rw [h, opposition_opposition]⟩ rfl rfl

/-! ### The based factor of `-1` -/

/-- `-1` times the opposition automorphism is the longest element. -/
theorem neg_mul_oppositionAut :
    Equiv.neg P * oppositionAut P b = longestElement P b := by
  rw [oppositionAut_def, ← mul_assoc, Equiv.neg_mul_neg, one_mul]

/-- **`-1` is the longest element times the opposition automorphism.** -/
theorem longestElement_mul_oppositionAut :
    (longestElement P b : P.Aut) * oppositionAut P b = Equiv.neg P := by
  rw [oppositionAut_def, ← mul_assoc, ← (Equiv.commute_neg _).eq, mul_assoc,
    longestElement_mul_longestElement, mul_one]

/-- **The factors of `-1` in `W ⋊ Aut(P, b)` are `w₀` and the opposition automorphism.** -/
@[simp]
theorem semidirectProductMulEquiv_symm_neg :
    b.semidirectProductMulEquiv.symm (Equiv.neg P) =
      ⟨longestElement P b, ⟨oppositionAut P b, oppositionAut_mem_basedAut P b⟩⟩ := by
  rw [← longestElement_mul_oppositionAut]
  exact Base.semidirectProductMulEquiv_symm_mul _ ⟨_, oppositionAut_mem_basedAut P b⟩

/-- **The opposition automorphism is the only based automorphism whose negative lies in the Weyl
group.** This characterises it without reference to the longest element. -/
theorem eq_oppositionAut_iff_neg_mul_mem_weylGroup {g : P.Aut} (hg : g ∈ b.basedAut) :
    g = oppositionAut P b ↔ Equiv.neg P * g ∈ P.weylGroup := by
  refine ⟨fun h ↦ h ▸ neg_mul_oppositionAut P b ▸ (longestElement P b).property, fun h ↦ ?_⟩
  -- `δ⁻¹ g = w₀ (-g)` is both in the Weyl group and based, hence trivial.
  have hW : (oppositionAut P b)⁻¹ * g ∈ P.weylGroup := by
    rw [oppositionAut_inv, oppositionAut_def, (Equiv.commute_neg _).eq, mul_assoc]
    exact mul_mem (longestElement P b).property h
  have hB : (oppositionAut P b)⁻¹ * g ∈ b.basedAut :=
    mul_mem (inv_mem (oppositionAut_mem_basedAut P b)) hg
  exact (inv_mul_eq_one.mp
    (Subgroup.disjoint_def.mp (Base.isComplement'_weylGroup_basedAut b).disjoint hW hB)).symm

section Map

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {Q : RootPairing ι₂ R M₂ N₂} [Finite ι₂] [Q.IsCrystallographic] [Q.IsReduced]

/-- **Change of base**: the opposition automorphism of the base `b.map e` transported along an
equivalence `e` of root pairings is the conjugate of that of `b` by `e`. -/
theorem oppositionAut_map (e : P.Equiv Q) :
    oppositionAut Q (b.map e) = e.autCongr (oppositionAut P b) := by
  refine ((eq_oppositionAut_iff_neg_mul_mem_weylGroup Q (b.map e)
    ((Base.autCongr_mem_basedAut_map_iff e).mpr (oppositionAut_mem_basedAut P b))).mpr ?_).symm
  rw [← Equiv.autCongr_neg e, ← map_mul, neg_mul_oppositionAut]
  simpa using (e.weylGroupEquiv (longestElement P b)).property

/-- **Change of base for the opposition involution**: the opposition involution of `b.map e` is
that of `b`, transported along the action of the equivalence `e` on root indices. -/
@[simp]
theorem opposition_map (e : P.Equiv Q) (i : ι) :
    opposition Q (b.map e) (e.indexEquiv i) = e.indexEquiv (opposition P b i) := by
  rw [← oppositionAut_indexEquiv_apply, oppositionAut_map, Equiv.indexEquiv_autCongr_apply,
    _root_.Equiv.symm_apply_apply, oppositionAut_indexEquiv_apply]

end Map

/-- **Change of base along an automorphism**: the opposition automorphism of `b.map g` is the
conjugate `g δ g⁻¹` of that of `b`. -/
theorem oppositionAut_map_eq_mul_mul_inv (g : P.Aut) :
    oppositionAut P (b.map g) = g * oppositionAut P b * g⁻¹ := by
  rw [oppositionAut_map, Equiv.autCongr_apply, mul_assoc, Equiv.mul_eq_comp, Equiv.mul_eq_comp]
  -- The inverse in `P.Aut` is `RootPairing.Equiv.symm` by definition of Mathlib's group structure.
  rfl

/-! ### When the opposition automorphism is trivial -/

/-- **The opposition automorphism is trivial exactly when `w₀ = -1`.** -/
theorem oppositionAut_eq_one_iff :
    oppositionAut P b = 1 ↔ (longestElement P b : P.Aut) = Equiv.neg P := by
  rw [oppositionAut_def, mul_eq_one_iff_inv_eq, Equiv.neg_inv, eq_comm]

/-- **The opposition automorphism is trivial exactly when `w₀` acts on weights by `-1`.** -/
theorem oppositionAut_eq_one_iff_forall_longestElement_smul_eq_neg :
    oppositionAut P b = 1 ↔ ∀ x : M, longestElement P b • x = -x := by
  refine ⟨fun h x ↦ ?_, fun h ↦ Equiv.weightHom_injective P (LinearEquiv.ext fun x ↦ ?_)⟩
  · rw [← neg_neg (longestElement P b • x), ← oppositionAut_smul, h, one_smul]
  · -- The action of `P.Aut` on weights is `g • x = Equiv.weightHom P g x` by definition.
    exact (oppositionAut_smul P b x).trans (by simp [h])

/-- **For a root system, the opposition automorphism is trivial exactly when the opposition
involution fixes every simple root**, that is, exactly when `-w₀` induces the trivial automorphism
of the Dynkin diagram. -/
theorem oppositionAut_eq_one_iff_forall_opposition_eq [P.IsRootSystem] :
    oppositionAut P b = 1 ↔ ∀ i ∈ b.support, opposition P b i = i := by
  refine ⟨fun h i _ ↦ ?_, fun h ↦ b.eq_one_of_forall_indexEquiv_eq fun i hi ↦ ?_⟩
  · simpa [h] using (oppositionAut_indexEquiv_apply P b i).symm
  · rw [oppositionAut_indexEquiv_apply, h i hi]

end RootPairing

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Neg
import TauCeti.LinearAlgebra.RootSystem.CoweightLattice.Automorphism
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
of the simple roots is a symmetry of the Cartan matrix, read with its orientation. On the coroot
functionals it matches the coroot of `opposition i` after `δ` with the coroot of `i` before: in
particular `δ` carries a weight whose simple coroot values are those of the fundamental weight
`ϖᵢ` to one with the values of `ϖ_{opposition i}`.

In the decomposition `Aut(P) = W ⋊ Aut(P, b)` of `RootPairing.Base.semidirectProductMulEquiv`,
the automorphism `-1` has Weyl factor `w₀` and based factor `δ`. This characterises `δ` without
reference to `w₀`: it is the only based automorphism `g` with `-g` in the Weyl group. The
characterisation gives the change of base: for an automorphism `g`, the opposition automorphism of
the base `b.map g` is the conjugate `g δ g⁻¹`.

Finally `δ` is the identity exactly when `w₀ = -1`, and for a root system this happens exactly
when the opposition involution fixes every simple root. This is the root-system side of the
criterion that every finite-dimensional module of a semisimple Lie algebra is self-dual.

## Main definitions

* `TauCeti.oppositionAut`: the opposition automorphism `δ = -w₀` of a base.

## Main results

* `TauCeti.oppositionAut_smul`, `TauCeti.oppositionAut_indexEquiv_apply`: `δ` acts on weights by
  `x ↦ -(w₀ • x)` and on root indices by the opposition involution.
* `TauCeti.oppositionAut_mem_basedAut`: **`δ` is a based automorphism.**
* `TauCeti.oppositionAut_mul_self`: `δ` is an involution.
* `TauCeti.coroot_opposition`: the coroot of `opposition i` is `-w₀` applied to the coroot of `i`.
* `TauCeti.coroot'_oppositionAut_smul` and
  `TauCeti.coroot'_oppositionAut_smul_eq_ite`: the coroot values of `δ x`, and the image of a
  fundamental weight.
* `TauCeti.pairing_opposition`, `TauCeti.cartanMatrix_oppositionPerm`: the opposition involution
  preserves the root pairings and the Cartan matrix.
* `TauCeti.semidirectProductMulEquiv_symm_neg`: the factors of `-1` are `w₀` and `δ`.
* `TauCeti.eq_oppositionAut_iff_neg_mul_mem_weylGroup`: `δ` is the only based automorphism whose
  negative is in the Weyl group.
* `TauCeti.oppositionAut_map`, `TauCeti.opposition_map`: change of base.
* `TauCeti.oppositionAut_eq_one_iff`, `TauCeti.oppositionAut_eq_one_iff_forall_smul` and
  `TauCeti.oppositionAut_eq_one_iff_forall_opposition_eq`: `δ = 1` exactly when `w₀ = -1`, and,
  for a root system, exactly when the opposition involution fixes every simple root.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Ch. VI, §1.6 (the longest element `w₀` and the
  involution `-w₀` of a base).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §10.3 (the
  longest element) and §13.1 (fundamental weights).
-/

public section

namespace TauCeti

open RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N)
  [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- **The opposition automorphism** `δ = -w₀` of a base: the product of the central automorphism
`-1` with the longest element `w₀` of the Weyl group. It acts on root indices by the opposition
involution `TauCeti.opposition` (`TauCeti.oppositionAut_indexEquiv_apply`) and fixes the base
(`TauCeti.oppositionAut_mem_basedAut`). -/
noncomputable def oppositionAut : P.Aut :=
  RootPairing.Equiv.neg P * (longestElement P b : P.Aut)

/-- **The opposition automorphism acts on weights by `x ↦ -(w₀ • x)`.** -/
@[simp]
theorem oppositionAut_smul (x : M) : oppositionAut P b • x = -(longestElement P b • x) := by
  rw [oppositionAut, mul_smul, RootPairing.Equiv.neg_smul_eq_neg, Subgroup.smul_def]

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
  rw [oppositionAut, (RootPairing.Equiv.commute_neg P _).symm.mul_mul_mul_comm,
    RootPairing.Equiv.neg_mul_neg, one_mul, ← Subgroup.coe_mul, ← pow_two, longestElement_sq,
    Subgroup.coe_one]

/-- The opposition automorphism is its own inverse. -/
@[simp]
theorem oppositionAut_inv : (oppositionAut P b)⁻¹ = oppositionAut P b :=
  inv_eq_of_mul_eq_one_right (oppositionAut_mul_self P b)

/-! ### Coroots, fundamental weights and the Cartan matrix -/

/-- **The coroot of `opposition i` is `-w₀` applied to the coroot of `i`**, where an automorphism
`g` acts on coweights by `g.coweightEquiv.symm`, the contragredient of its action on weights. This
is the coroot companion of `TauCeti.root_opposition`. -/
theorem coroot_opposition (i : ι) :
    P.coroot (opposition P b i) =
      -(longestElement P b : P.Aut).coweightEquiv.symm (P.coroot i) := by
  rw [Equiv.coweightEquiv_symm_coroot, P.coroot_eq_neg_iff, ← P.root_eq_neg_iff, root_opposition,
    Equiv.root_indexEquiv_eq_smul, Subgroup.smul_def]

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

/-- **The opposition involution preserves the root pairings.** -/
@[simp]
theorem pairing_opposition (i j : ι) :
    P.pairing (opposition P b i) (opposition P b j) = P.pairing i j := by
  simpa using (oppositionAut P b).toHom.pairing (i := i) (j := j)

/-- **The opposition involution is a symmetry of the Cartan matrix**, with its orientation: the
entry at `(δ i, δ j)` is the entry at `(i, j)`. -/
@[simp]
theorem cartanMatrix_oppositionPerm (i j : b.support) :
    b.cartanMatrix (oppositionPerm P b i) (oppositionPerm P b j) = b.cartanMatrix i j :=
  FaithfulSMul.algebraMap_injective ℤ R <| by
    simp only [Base.algebraMap_cartanMatrixIn_apply, coe_oppositionPerm, pairing_opposition]

/-! ### The based factor of `-1` -/

/-- `-1` times the opposition automorphism is the longest element. -/
theorem neg_mul_oppositionAut :
    RootPairing.Equiv.neg P * oppositionAut P b = longestElement P b := by
  rw [oppositionAut, ← mul_assoc, RootPairing.Equiv.neg_mul_neg, one_mul]

/-- **`-1` is the longest element times the opposition automorphism.** -/
theorem longestElement_mul_oppositionAut :
    (longestElement P b : P.Aut) * oppositionAut P b = RootPairing.Equiv.neg P := by
  rw [oppositionAut, ← mul_assoc, ← (RootPairing.Equiv.commute_neg P _).eq, mul_assoc,
    ← Subgroup.coe_mul, ← pow_two, longestElement_sq, Subgroup.coe_one, mul_one]

/-- **The factors of `-1` in `W ⋊ Aut(P, b)` are `w₀` and the opposition automorphism.** -/
theorem semidirectProductMulEquiv_symm_neg :
    b.semidirectProductMulEquiv.symm (RootPairing.Equiv.neg P) =
      ⟨longestElement P b, ⟨oppositionAut P b, oppositionAut_mem_basedAut P b⟩⟩ := by
  rw [← longestElement_mul_oppositionAut]
  exact Base.semidirectProductMulEquiv_symm_mul _ ⟨_, oppositionAut_mem_basedAut P b⟩

/-- **The opposition automorphism is the only based automorphism whose negative lies in the Weyl
group.** This characterises it without reference to the longest element. -/
theorem eq_oppositionAut_iff_neg_mul_mem_weylGroup {g : P.Aut} (hg : g ∈ b.basedAut) :
    g = oppositionAut P b ↔ RootPairing.Equiv.neg P * g ∈ P.weylGroup := by
  refine ⟨fun h ↦ h ▸ neg_mul_oppositionAut P b ▸ (longestElement P b).2, fun h ↦ ?_⟩
  -- `δ⁻¹ g = w₀ (-g)` is both in the Weyl group and based, hence trivial.
  have hW : (oppositionAut P b)⁻¹ * g ∈ P.weylGroup := by
    rw [oppositionAut_inv, oppositionAut, (RootPairing.Equiv.commute_neg P _).eq, mul_assoc]
    exact mul_mem (longestElement P b).2 h
  have hB : (oppositionAut P b)⁻¹ * g ∈ b.basedAut :=
    mul_mem (inv_mem (oppositionAut_mem_basedAut P b)) hg
  exact (inv_mul_eq_one.mp
    (Subgroup.disjoint_def.mp (Base.isComplement'_weylGroup_basedAut b).disjoint hW hB)).symm

/-- **Change of base**: the opposition automorphism of the transported base `b.map g` is the
conjugate of that of `b` by `g`. -/
theorem oppositionAut_map (g : P.Aut) :
    oppositionAut P (b.map g) = g * oppositionAut P b * g⁻¹ := by
  refine ((eq_oppositionAut_iff_neg_mul_mem_weylGroup P (b.map g) ?_).mpr ?_).symm
  · rw [Base.mem_basedAut_iff_map_eq, ← Base.map_mul, inv_mul_cancel_right, Base.map_mul,
      map_oppositionAut]
  · rw [← mul_assoc, ← mul_assoc, (RootPairing.Equiv.commute_neg P g).eq, mul_assoc g,
      neg_mul_oppositionAut]
    exact RootPairing.weylGroup_normal.conj_mem _ (longestElement P b).2 g

/-- **Change of base for the opposition involution**: the opposition involution of `b.map g` is
that of `b`, transported along the action of `g` on root indices. -/
theorem opposition_map (g : P.Aut) (i : ι) :
    opposition P (b.map g) (g.indexEquiv i) = g.indexEquiv (opposition P b i) := by
  rw [← oppositionAut_indexEquiv_apply, oppositionAut_map, ← oppositionAut_indexEquiv_apply]
  simp

/-! ### When the opposition automorphism is trivial -/

/-- **The opposition automorphism is trivial exactly when `w₀ = -1`.** -/
theorem oppositionAut_eq_one_iff :
    oppositionAut P b = 1 ↔ (longestElement P b : P.Aut) = RootPairing.Equiv.neg P := by
  rw [oppositionAut, mul_eq_one_iff_inv_eq, RootPairing.Equiv.neg_inv, eq_comm]

/-- **The opposition automorphism is trivial exactly when `w₀` acts on weights by `-1`.** -/
theorem oppositionAut_eq_one_iff_forall_smul :
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

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.HomExt
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Frobenius and Weyl–Frobenius composites as standard endomorphisms

Frobenius endomorphisms of a Chevalley datum are based whenever the iterated Frobenius on the
scalar ring is surjective (`isBasedEndomorphism_frobenius_of_surjective`), and in particular over
every perfect ring of exponential characteristic `p` (`isBasedEndomorphism_frobenius`).

Composing Frobenius with conjugation by a pinned simple Weyl representative yields a composite
`Int(nᵢ) ∘ Frob_{p^k}` that is standard whenever `iterateFrobenius A p k` is surjective
(`isStandardEndomorphism_conj_weylElement_comp_frobenius`) and is not based whenever `A` is
nontrivial (`not_isBasedEndomorphism_conj_weylElement_comp_frobenius`). In type `A₁`, its character
map is `-(p ^ k) • 1` and its square agrees with `frobenius p (2 * k)` on `D.rootTorusSubgroup A`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.isBasedEndomorphism_frobenius`: Frobenius is based over every
  perfect ring of exponential characteristic `p`.
* `ChevalleyDatum.isStandardEndomorphism_conj_weylElement_comp_frobenius`: `Int(nᵢ) ∘ Frob_{p^k}`
  is standard whenever `iterateFrobenius A p k` is surjective.
* `ChevalleyDatum.not_isBasedEndomorphism_conj_weylElement_comp_frobenius`: `Int(nᵢ) ∘ Frob_{p^k}`
  is never based over a nontrivial commutative ring (no surjectivity assumption needed).
* `ChevalleyDatum.conj_weylElement_comp_frobenius_comp_self_eq_on_rootTorusSubgroup_typeA1`:
  specialization of the square formula for `Int(nᵢ) ∘ Frob_{p^k}` to `D.rootTorusSubgroup A` in
  type `A₁`.

## References

* R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, Mem. Amer. Math. Soc. **80** (1968),
  §§10–11.
* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 10.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  §§1.15–1.17.
-/

public section

open Multiplicative

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (A : Type v) [CommRing A]

/-- Frobenius is a based endomorphism whenever the iterated Frobenius on `A` is surjective. -/
theorem isBasedEndomorphism_frobenius_of_surjective (p k : ℕ) [ExpChar A p]
    (hsurj : Function.Surjective (iterateFrobenius A p k)) :
    D.IsBasedEndomorphism A (D.frobenius p k A) := by
  have hmap (α : Fin t.numRoots) :
      (D.rootSubgroupPoints α A).range.map (D.frobenius p k A) =
        (D.rootSubgroupPoints α A).range :=
    MonoidHom.map_range_eq_range_of_comp_eq _ _ _
      ((ofAdd.surjective.comp hsurj).comp toAdd.surjective) fun u => by
        rw [← ofAdd_toAdd u, D.frobenius_rootSubgroupPoints, Function.comp_apply,
          Function.comp_apply, toAdd_ofAdd, iterateFrobenius_def]
  exact isBasedEndomorphism_iff.mpr
    ⟨isStandardEndomorphism_iff.mpr fun α => ⟨α, hmap α⟩, fun α hα => ⟨α, hα, hmap α⟩⟩

/-- Over a perfect ring of exponential characteristic `p`, every Frobenius endomorphism of a
Chevalley datum is based. -/
theorem isBasedEndomorphism_frobenius (p k : ℕ) [ExpChar A p] [PerfectRing A p] :
    D.IsBasedEndomorphism A (D.frobenius p k A) :=
  D.isBasedEndomorphism_frobenius_of_surjective A p k (bijective_iterateFrobenius A p k).surjective

/-- Composing Frobenius with conjugation by a pinned simple Weyl representative is standard
whenever the iterated Frobenius on `A` is surjective. -/
theorem isStandardEndomorphism_conj_weylElement_comp_frobenius (i : Fin t.rank) (p k : ℕ)
    [ExpChar A p] (hsurj : Function.Surjective (iterateFrobenius A p k)) :
    D.IsStandardEndomorphism A
      ((MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
        (D.frobenius p k A)) :=
  (D.isStandardEndomorphism_conj_weylElement A i).comp
    (D.isBasedEndomorphism_frobenius_of_surjective A p k hsurj).isStandardEndomorphism

/-- Composing Frobenius with conjugation by a pinned simple Weyl representative is never based over
a nontrivial ring. -/
theorem not_isBasedEndomorphism_conj_weylElement_comp_frobenius [Nontrivial A] (i : Fin t.rank)
    (p k : ℕ) [ExpChar A p] :
    ¬ D.IsBasedEndomorphism A
      ((MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
        (D.frobenius p k A)) := fun hbased => by
  have hmem :
      ((MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
          (D.frobenius p k A))
        (D.rootSubgroupPoints (t.simpleIndex ht i) A (ofAdd 1)) ∈ D.borelSubgroup A :=
    D.positivePoints_le_borelSubgroup A <| hbased.map_positivePoints_le
      ⟨_, D.rootSubgroupPoints_mem_positivePoints A
        (support_subset_posRoots _ _ (t.simpleIndex_mem_support i)) (ofAdd 1), rfl⟩
  simp only [MonoidHom.comp_apply, D.frobenius_rootSubgroupPoints, one_pow,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    D.weylElement_conj_rootSubgroupPoints_simpleIndex_mem_borelSubgroup_iff] at hmem
  exact D.rootSubgroupPoints_ofAdd_one_ne_one A (t.simpleIndex ht i) hmem

/-- The character map of `Int(nᵢ) ∘ Frob_{p^k}` is `(p ^ k) • sᵢ` on the actual character
lattice. -/
theorem isCharacterMap_conj_weylElement_comp_frobenius (i : Fin t.rank) (p k : ℕ) [ExpChar A p] :
    IsCharacterMap (D.torusPoints A)
      ((MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
        (D.frobenius p k A))
      ((p ^ k : ℕ) •
        (D.weylCharacterAut
          (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht)
            (t.simpleIndex ht i))).toLinearMap) := by
  simpa only [smul_mul_assoc, one_mul] using
    (D.isCharacterMap_conj_weylElement i A).comp (D.isCharacterMap_frobenius p k A)

/-- For every Chevalley datum and every ring `A` of exponential characteristic `p`, squaring
`Int(nᵢ) ∘ Frob_{p^k}` equals `Int(nᵢ²) ∘ Frob_{p^(2k)}` on all of `D.points A`. -/
theorem conj_weylElement_comp_frobenius_comp_self (i : Fin t.rank) (p k : ℕ) [ExpChar A p] :
    let F := (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
      (D.frobenius p k A)
    F.comp F =
      (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom.comp
        (D.frobenius p (2 * k) A) := by
  intro F
  ext1 y
  have hadd : D.frobenius p (2 * k) A y = D.frobenius p k A (D.frobenius p k A y) := by
    have h := D.frobenius_add p k A k
    rw [← two_mul] at h
    exact DFunLike.congr_fun h y
  dsimp only [F, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    D.frobenius_weylElement, one_pow, ← hadd, mul_inv_rev]
  simp only [mul_assoc]

/-! ### Regression example in type `A₁` -/

section TypeA1

/-- In type `A₁`, the unique simple reflection acts as negation on the actual character lattice
of every Chevalley datum. -/
theorem weylCharacterAut_simpleIndex_typeA1 {h1 : (DynkinType.A 1).Valid}
    (D : ChevalleyDatum (DynkinType.A 1) h1) (i : Fin (DynkinType.A 1).rank) :
    (D.weylCharacterAut
      (RootPairing.weylGroup.ofIdx ((DynkinType.A 1).simplyConnectedRootDatum h1)
        ((DynkinType.A 1).simpleIndex h1 i))).toLinearMap = -1 := by
  refine LinearMap.ext fun χ => D.weightLatticeEmbedding_injective ?_
  rw [LinearEquiv.coe_coe, D.weightLatticeEmbedding_weylCharacterAut,
    RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul,
    RootPairing.reflection_apply, (DynkinType.A 1).coroot'_simpleIndex_apply h1]
  ext j
  obtain rfl : j = i := (Fin.eq_zero j).trans (Fin.eq_zero i).symm
  simp only [LinearMap.neg_apply, one_apply_eq_self, map_neg, Pi.sub_apply, Pi.smul_apply,
    Pi.neg_apply, smul_eq_mul, DynkinType.root_simpleIndex, DynkinType.cartanMatrix_apply_same]
  ring

/-- In type `A₁`, the composite `Int(n₀) ∘ Frob_{p^k}` has character map `-(p ^ k : ℤ) • 1`. -/
theorem isCharacterMap_conj_weylElement_comp_frobenius_typeA1 {h1 : (DynkinType.A 1).Valid}
    (D : ChevalleyDatum (DynkinType.A 1) h1) (i : Fin (DynkinType.A 1).rank)
    (p k : ℕ) [ExpChar A p] :
    IsCharacterMap (D.torusPoints A)
      ((MulAut.conj (D.weylElement ((DynkinType.A 1).simpleIndex h1 i) A 1)).toMonoidHom.comp
        (D.frobenius p k A))
      (-(p ^ k : ℤ) • 1) := by
  have h := D.isCharacterMap_conj_weylElement_comp_frobenius A i p k
  rw [D.weylCharacterAut_simpleIndex_typeA1 i, smul_neg, ← natCast_zsmul, Nat.cast_pow,
    ← neg_smul] at h
  exact h

private theorem torusCharacter_simpleCorootParameter_neg_one_typeA1 {h1 : (DynkinType.A 1).Valid}
    (D : ChevalleyDatum (DynkinType.A 1) h1) (i : Fin (DynkinType.A 1).rank) :
    torusCharacter (D.simpleCorootParameter i A (-1))
      (D.coordinateRoot ((DynkinType.A 1).simpleIndex h1 i)) = 1 := by
  have h := D.torusCharacter_simpleCorootParameter i A (-1)
    ⟨_, D.root_mem_weightLattice ((DynkinType.A 1).simpleIndex h1 i)⟩
  rw [← D.coordinateRoot_def] at h
  simpa only [Submodule.coe_mk, DynkinType.root_simpleIndex,
    DynkinType.cartanMatrix_apply_same, zpow_ofNat, neg_one_sq] using h

private theorem conj_weylElement_sq_eq_on_rootTorusSubgroup_typeA1 {h1 : (DynkinType.A 1).Valid}
    (D : ChevalleyDatum (DynkinType.A 1) h1) (i : Fin (DynkinType.A 1).rank) :
    let n := D.weylElement ((DynkinType.A 1).simpleIndex h1 i) A 1
    (MulAut.conj (n * n)).toMonoidHom.comp (D.rootTorusSubgroup A).subtype =
      (D.rootTorusSubgroup A).subtype := by
  intro n
  have hch := torusCharacter_simpleCorootParameter_neg_one_typeA1 A D i
  refine D.rootTorusSubgroup_hom_ext _ _ (fun j u => ?_) (fun j u => ?_) (fun s => ?_)
  all_goals simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, n, D.weylElement_mul_self, D.simpleCorootPoints_eq_torusPoints]
  · obtain rfl : j = i := (Fin.eq_zero j).trans (Fin.eq_zero i).symm
    rw [← ofAdd_toAdd u, D.torusPoints_conj_rootSubgroupPoints, hch, Units.val_one, one_mul]
  · obtain rfl : j = i := (Fin.eq_zero j).trans (Fin.eq_zero i).symm
    rw [← ofAdd_toAdd u, D.torusPoints_conj_rootSubgroupPoints,
      D.coordinateRoot_reflectionPerm_self, torusCharacter_neg, hch, inv_one, Units.val_one,
      one_mul]
  · exact ((Commute.all (D.simpleCorootParameter i A (-1)) s).map
      (D.torusPoints A)).mul_inv_cancel

/-- In type `A₁`, the square of the composite `Int(n₀) ∘ Frob_{p^k}` agrees with
`D.frobenius p (2 * k) A` on `D.rootTorusSubgroup A`, because `n₀² = h₀(-1)` is central on every
root subgroup and on the torus. -/
theorem conj_weylElement_comp_frobenius_comp_self_eq_on_rootTorusSubgroup_typeA1
    {h1 : (DynkinType.A 1).Valid} (D : ChevalleyDatum (DynkinType.A 1) h1)
    (i : Fin (DynkinType.A 1).rank) (p k : ℕ) [ExpChar A p]
    {x : D.points A} (hx : x ∈ D.rootTorusSubgroup A) :
    let F := (MulAut.conj (D.weylElement ((DynkinType.A 1).simpleIndex h1 i) A 1)).toMonoidHom.comp
      (D.frobenius p k A)
    F (F x) = D.frobenius p (2 * k) A x := by
  intro F
  have hsq := DFunLike.congr_fun (D.conj_weylElement_comp_frobenius_comp_self A i p k) x
  have hmem := D.map_frobenius_rootTorusSubgroup_le p (2 * k) A ⟨x, hx, rfl⟩
  have hcent := DFunLike.congr_fun
    (conj_weylElement_sq_eq_on_rootTorusSubgroup_typeA1 A D i)
    ⟨D.frobenius p (2 * k) A x, hmem⟩
  simpa only [F, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] using hsq.trans hcent

end TypeA1

end TauCeti.DynkinType.ChevalleyDatum

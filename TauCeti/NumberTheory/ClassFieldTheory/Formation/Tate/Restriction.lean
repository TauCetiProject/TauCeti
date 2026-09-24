/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Corestriction
import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Trans

/-!
# Restriction of finite-layer Tate cohomology

For a restriction of finite normal layers `K/E` inside `K/F`, this file defines restriction

`Hhatʳ(Gal(K/F), A^V) ⟶ Hhatʳ(Gal(K/E), A^V)`

in every integer degree, with formation coefficients and with trivial integral coefficients. In
positive degrees it is the ordinary cohomological restriction `LayerRestriction.cohomologyRes`;
in degree zero it is induced by the inclusion of invariants, which on ground levels is the
inclusion `A^U ⊆ A^{U'}`; in degree minus one it is induced by the relative transfer; and in
degrees at most minus two it is the transfer on group homology. In degrees at most zero the smaller
Galois group is identified with the image of its inclusion into the larger one, exactly as for
`LayerRestriction.tateCor`.

The comparison lemmas below identify each branch with the corresponding established map. On
representatives, degree-zero restriction is the ground-level inclusion and degree-minus-one
restriction is the relative transfer of norm kernels, and restriction is functorial along a tower
`F ⊆ E ⊆ E' ⊆ K` in every degree. Corestriction after restriction is multiplication by the
relative degree `[E : F]` in every degree.

## Main definitions

* `TauCeti.ClassFieldTheory.LayerRestriction.tateRes`: restriction of layer Tate cohomology.
* `TauCeti.ClassFieldTheory.LayerRestriction.trivialTateRes`: restriction of Tate cohomology with
  trivial integral coefficients.
* `TauCeti.ClassFieldTheory.LayerRestriction.kerNormTransfer`: the relative transfer of norm
  kernels along a restriction. It is the degree-minus-one shadow of `tateRes`, and the wrong-way
  partner of `LayerRestriction.kerNormInclusion`.

## Main results

* `TauCeti.ClassFieldTheory.LayerRestriction.tateRes_comp_tateHIsoH_hom` and
  `TauCeti.ClassFieldTheory.LayerRestriction.trivialTateRes_comp_isoGroupCohomology_hom`: in
  positive degrees, Tate restriction is ordinary cohomological restriction.
* `TauCeti.ClassFieldTheory.LayerRestriction.tateRes_zero_H0π` and
  `TauCeti.ClassFieldTheory.LayerRestriction.tateHZeroEquivNormQuotient_tateRes_H0π`: in degree
  zero, restriction is the ground-level inclusion on representatives and norm quotients.
* `TauCeti.ClassFieldTheory.LayerRestriction.tateRes_neg_one_HNegOneπ`: in degree minus one,
  restriction is the relative transfer `kerNormTransfer` on representatives.
* `TauCeti.ClassFieldTheory.LayerRestriction.tateCor_tateRes`: `cor ∘ res = [E : F]` in every
  degree.
* `TauCeti.ClassFieldTheory.LayerRestriction.kerNormTransfer_trans_sub_mem`: the relative transfer
  of norm kernels is transitive along a tower modulo the augmentation submodule.
* `TauCeti.ClassFieldTheory.LayerRestriction.tateRes_trans_of_neg_one_le`: Tate restriction is
  functorial along towers in every degree at least minus one.
* `TauCeti.ClassFieldTheory.LayerRestriction.tateRes_trans_eq_comp` and
  `TauCeti.ClassFieldTheory.LayerRestriction.tateRes_trans`: Tate restriction is functorial along
  towers of layers in every degree.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6 and Chapter XIV, §4.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9 and Chapter VI, §5.
-/

public noncomputable section

open CategoryTheory Rep Representation

namespace TauCeti.ClassFieldTheory.LayerRestriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {small big : NormalLayer G}

attribute [local instance] instFintypeRange Subgroup.fintypeQuotientOfFiniteIndex

/-- **Restriction between the Tate cohomology groups of finite normal layers, in every integer
degree.** Positive degrees use ordinary cohomological restriction, degrees zero and minus one use
the low-degree descriptions by invariants and norm kernels, and lower degrees use the transfer on
group homology. -/
def tateRes (T : LayerRestriction small big) (F : Formation G) :
    (r : ℤ) → big.TateH F r ⟶ small.TateH F r
  | .ofNat 0 =>
      TauCeti.TateCohomology.H0Res (big.rep F) T.galHom.range ≫ (T.tateRangeIso F 0).inv
  | .ofNat (n + 1) =>
      (big.tateHIsoH F (n + 1)).hom ≫ T.cohomologyRes F (n + 1) ≫
        (small.tateHIsoH F (n + 1)).inv
  | .negSucc 0 =>
      TauCeti.TateCohomology.HNegOneRes (big.rep F) T.galHom.range ≫
        (T.tateRangeIso F (-1)).inv
  | .negSucc (n + 1) =>
      TauCeti.TateCohomology.negSuccRes (big.rep F) T.galHom.range (n + 1) ≫
        (T.tateRangeIso F (Int.negSucc (n + 1))).inv

/-- In degree zero, layer Tate restriction is restriction of invariants to the image subgroup,
followed by the range comparison. -/
@[simp]
theorem tateRes_zero (T : LayerRestriction small big) (F : Formation G) :
    T.tateRes F 0 =
      TauCeti.TateCohomology.H0Res (big.rep F) T.galHom.range ≫ (T.tateRangeIso F 0).inv :=
  (rfl)

/-- In a positive degree, layer Tate restriction is ordinary cohomological restriction read
through the canonical positive-degree comparisons. -/
@[simp]
theorem tateRes_ofNat_succ (T : LayerRestriction small big) (F : Formation G) (n : ℕ) :
    T.tateRes F ((n : ℤ) + 1) =
      (big.tateHIsoH F (n + 1)).hom ≫ T.cohomologyRes F (n + 1) ≫
        (small.tateHIsoH F (n + 1)).inv :=
  (rfl)

/-- Positive-degree Tate restriction commutes with the canonical comparison to ordinary
cohomology. -/
@[reassoc]
theorem tateRes_comp_tateHIsoH_hom (T : LayerRestriction small big) (F : Formation G)
    (n : ℕ) [NeZero n] :
    T.tateRes F n ≫ (small.tateHIsoH F n).hom =
      (big.tateHIsoH F n).hom ≫ T.cohomologyRes F n := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k =>
    simp only [tateRes, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- In degree minus one, layer Tate restriction is the relative transfer on norm kernels,
followed by the range comparison. -/
@[simp]
theorem tateRes_neg_one (T : LayerRestriction small big) (F : Formation G) :
    T.tateRes F (-1) =
      TauCeti.TateCohomology.HNegOneRes (big.rep F) T.galHom.range ≫
        (T.tateRangeIso F (-1)).inv :=
  (rfl)

/-- In degree `-(n+2)`, layer Tate restriction is the transfer in group homology of degree `n+1`,
followed by the range comparison. -/
@[simp]
theorem tateRes_negSucc_succ (T : LayerRestriction small big) (F : Formation G) (n : ℕ) :
    T.tateRes F (Int.negSucc (n + 1)) =
      TauCeti.TateCohomology.negSuccRes (big.rep F) T.galHom.range (n + 1) ≫
        (T.tateRangeIso F (Int.negSucc (n + 1))).inv :=
  (rfl)

/-- **In degree zero, restriction is the ground-level inclusion.** Read through the identification
of `Hhat⁰` with the norm quotient `A^U / N(A^V)`, restricting the class of an element of the ground
level `A^U` of `K/F` gives the class of the same element in the ground level `A^{U'}` of `K/E`. -/
theorem tateHZeroEquivNormQuotient_tateRes_H0π (T : LayerRestriction small big) (F : Formation G)
    (x : (big.rep F).ρ.invariants) :
    small.tateHZeroEquivNormQuotient F (T.tateRes F 0 (TateCohomology.H0π (big.rep F) x)) =
      small.normQuotientMk F (T.groundInclusion F (big.groundLevelEquiv F x)) := by
  rw [tateRes_zero, ModuleCat.comp_apply, TauCeti.TateCohomology.H0π_comp_H0Res_apply,
    tateRangeIso_inv_H0π, NormalLayer.tateHZeroEquivNormQuotient_H0π]
  congr 1
  ext
  rw [NormalLayer.groundLevelEquiv_apply_coe, groundInclusion_apply_coe,
    NormalLayer.groundLevelEquiv_apply_coe]
  exact T.repIso_inv_apply_coe F _

/-- **In degree zero, restriction is the ground-level inclusion on representatives.** The
representative of a class in the ground level `A^U` of `K/F` gives the class of the same element in
the ground level `A^{U'}` of `K/E`. -/
theorem tateRes_zero_H0π (T : LayerRestriction small big) (F : Formation G)
    (x : (big.rep F).ρ.invariants) :
    T.tateRes F 0 (TateCohomology.H0π (big.rep F) x) =
      TateCohomology.H0π (small.rep F)
        ((small.groundLevelEquiv F).symm (T.groundInclusion F (big.groundLevelEquiv F x))) := by
  apply (small.tateHZeroEquivNormQuotient F).injective
  rw [tateHZeroEquivNormQuotient_tateRes_H0π,
    NormalLayer.tateHZeroEquivNormQuotient_H0π, LinearEquiv.apply_symm_apply]

/-- The **relative transfer of norm kernels** along a restriction: the transfer of the image of
`Gal(K/E)` in `Gal(K/F)`, read back into the smaller layer through `repIso`. On representatives,
degree `-1` restriction is this map (`tateRes_neg_one_HNegOneπ`); it is the wrong-way partner of
`LayerRestriction.kerNormInclusion`. -/
def kerNormTransfer (T : LayerRestriction small big) (F : Formation G) :
    LinearMap.ker (big.rep F).ρ.norm →ₗ[ℤ] LinearMap.ker (small.rep F).ρ.norm :=
  (TauCeti.TateCohomology.mapKerNorm
      (Representation.IsIntertwiningMap.symm (T.isIntertwiningMap_repIso_range F))).comp
    (Representation.relTransferKerNorm (big.rep F).ρ T.galHom.range)

-- `dsimp% only` on the left-hand side: see the implementation notes of `Formation/Basic.lean`.
/-- The norm-kernel transfer is the relative transfer of the image subgroup, read back through
the identification of coefficient modules. -/
@[simp]
theorem kerNormTransfer_apply (T : LayerRestriction small big) (F : Formation G)
    (x : LinearMap.ker (big.rep F).ρ.norm) :
    (dsimp% only (T.kerNormTransfer F x : F.level small.top)) =
      (T.repIso F).inv.hom (Representation.relTransfer (big.rep F).ρ T.galHom.range x) := by
  rw [kerNormTransfer, LinearMap.comp_apply, TauCeti.TateCohomology.mapKerNorm_apply_coe,
    Representation.coe_relTransferKerNorm]
  -- The linear part of `IsIntertwiningMap.symm (T.isIntertwiningMap_repIso_range F)` is
  -- `(T.repIso F).inv.hom` by definition of `Representation.equivOfIso`.
  rfl

/-- **In degree minus one, layer Tate restriction is the relative transfer** on representatives. -/
theorem tateRes_neg_one_HNegOneπ (T : LayerRestriction small big) (F : Formation G)
    (x : LinearMap.ker (big.rep F).ρ.norm) :
    T.tateRes F (-1) (TauCeti.TateCohomology.HNegOneπ (big.rep F) x) =
      TauCeti.TateCohomology.HNegOneπ (small.rep F) (T.kerNormTransfer F x) := by
  rw [tateRes_neg_one, ModuleCat.comp_apply, TauCeti.TateCohomology.HNegOneπ_comp_HNegOneRes_apply,
    tateRangeIso_inv_HNegOneπ, kerNormTransfer, LinearMap.comp_apply]

/-! ### Towers -/

section Towers

variable {a b c : NormalLayer G}

/-- **The norm-kernel transfer is transitive along a tower, modulo the augmentation submodule.**
The transfer is transitive only up to the choice of coset representatives, and that choice is
invisible in degree `-1` Tate cohomology, which is the norm kernel modulo exactly this
submodule. -/
theorem kerNormTransfer_trans_sub_mem (T : LayerRestriction a b) (T' : LayerRestriction b c)
    (F : Formation G) (y : LinearMap.ker (c.rep F).ρ.norm) :
    (((T.trans T').kerNormTransfer F y : LinearMap.ker (a.rep F).ρ.norm) : F.level a.top) -
      ((T.kerNormTransfer F (T'.kerNormTransfer F y) : LinearMap.ker (a.rep F).ρ.norm) :
        F.level a.top) ∈ Representation.Coinvariants.ker (a.rep F).ρ := by
  have hKH := galHom_range_trans_le T T'
  set w := Representation.relTransfer (c.rep F).ρ T'.galHom.range ((y : F.level c.top)) with hw
  -- Transport the inner transfer from the middle layer to the image of its Galois group.
  have htrans := Representation.relTransfer_map_sub_mem (ρ := (b.rep F).ρ) (H := T.galHom.range)
    (ρ' := (c.rep F).ρ.comp T'.galHom.range.subtype)
    (MonoidHom.ofInjective T'.galHom_injective) ((T'.repIso F).hom.hom.toLinearMap)
    (Rep.hom_comm_apply (T'.repIso F).hom)
    (galHom_range_map_ofInjective T T') ((T'.repIso F).inv.hom w)
  -- `Iso.inv_hom_id_apply` is stated for the `ConcreteCategory.hom` coercion, so it is named
  -- here at the `ModuleCat.Hom.toLinearMap` form the transport lemma produces.
  have hid : (T'.repIso F).hom.hom.toLinearMap ((T'.repIso F).inv.hom w) = w :=
    (T'.repIso F).inv_hom_id_apply w
  rw [hid] at htrans
  -- Then compose the two transfers inside the largest Galois group.
  have htower := Representation.relTransfer_relTransfer_sub_relTransfer_mem
    (ρ := (c.rep F).ρ) (H := T'.galHom.range) hKH ((y : F.level c.top))
  rw [← hw] at htower
  -- Read the augmentation submodule in `htrans` over the image of the smallest Galois group
  -- directly, rather than through the image of the middle one.
  rw [MonoidHom.comp_assoc, ← Subgroup.subtype_comp_subgroupOfEquivOfLe hKH,
    Representation.coinvariantsKer_comp_comp_of_surjective
      ((T.trans T').galHom.range.subtype) _
      (Subgroup.subgroupOfEquivOfLe hKH).surjective] at htrans
  -- Reading an element of the middle layer back to the smallest one directly agrees with going
  -- across to the largest and back along the composite.
  have hrep : ∀ u : F.level b.top, (T.repIso F).inv.hom u =
      ((T.trans T').repIso F).inv.hom ((T'.repIso F).hom.hom.toLinearMap u) := fun u => by
    rw [repIso_inv_hom_trans_apply T T' F]
    exact congrArg (T.repIso F).inv.hom ((T'.repIso F).hom_inv_id_apply u).symm
  rw [kerNormTransfer_apply, kerNormTransfer_apply, kerNormTransfer_apply, hrep, ← map_sub]
  refine Representation.coinvariantsKer_map_le
    (ρ := (c.rep F).ρ.comp ((T.trans T').galHom.range).subtype)
    (MonoidHom.ofInjective (T.trans T').galHom_injective).symm
    (((T.trans T').repIso F).inv.hom.toLinearMap) (repIso_inv_comm_apply (T.trans T') F)
    (Submodule.mem_map_of_mem ?_)
  have hsum := add_mem htrans htower
  rw [sub_add_sub_cancel, hw] at hsum
  rw [← neg_sub]
  exact Submodule.neg_mem _ hsum

-- The nonnegative degrees of `tateRes_trans_of_neg_one_le`.
private theorem tateRes_trans_of_nonneg (T : LayerRestriction a b) (T' : LayerRestriction b c)
    (F : Formation G) (r : ℤ) (hr : 0 ≤ r) :
    (T.trans T').tateRes F r = T'.tateRes F r ≫ T.tateRes F r := by
  obtain rfl | ⟨n, rfl⟩ : r = 0 ∨ ∃ n : ℕ, r = n + 1 := by
    rcases r with (_ | n) | (_ | n)
    · exact .inl rfl
    · exact .inr ⟨n, rfl⟩
    · omega
    · omega
  · ext x
    induction x using TauCeti.TateCohomology.H0_induction_on with
    | h y =>
      rw [ModuleCat.comp_apply, tateRes_zero_H0π, tateRes_zero_H0π, tateRes_zero_H0π,
        LinearEquiv.apply_symm_apply, groundInclusion_trans T T', LinearMap.comp_apply]
  · rw [tateRes_ofNat_succ, tateRes_ofNat_succ, tateRes_ofNat_succ,
      cohomologyRes_trans T T']
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **Tate restriction is functorial along a tower in every degree at least minus one.**
Restricting from `K/F` to `K/E` and then to `K/E'` agrees with direct restriction from `K/F` to
`K/E'`.

Unlike the nonnegative degrees, degree `-1` is not a formal consequence
of functoriality of some change-of-group map: there restriction is the relative transfer, which is
transitive only modulo the augmentation submodule — exactly the submodule degree `-1` Tate
cohomology divides by. See `kerNormTransfer_trans_sub_mem`. -/
theorem tateRes_trans_of_neg_one_le (T : LayerRestriction a b) (T' : LayerRestriction b c)
    (F : Formation G) (r : ℤ) (hr : -1 ≤ r) :
    (T.trans T').tateRes F r = T'.tateRes F r ≫ T.tateRes F r := by
  obtain rfl | hr := hr.eq_or_lt
  · ext x
    induction x using TauCeti.TateCohomology.HNegOne_induction_on with
    | h y =>
      rw [ModuleCat.comp_apply, tateRes_neg_one_HNegOneπ, tateRes_neg_one_HNegOneπ,
        tateRes_neg_one_HNegOneπ, TauCeti.TateCohomology.HNegOneπ_eq_iff]
      exact kerNormTransfer_trans_sub_mem T T' F y
  · exact tateRes_trans_of_nonneg T T' F r (by omega)

-- The degrees below `-1` of `tateRes_trans`, where restriction is the transfer in group homology.
attribute [local instance] Subgroup.fintypeOfFinite in
private theorem tateRes_negSucc_succ_trans (T : LayerRestriction a b) (T' : LayerRestriction b c)
    (F : Formation G) (n : ℕ) : (T.trans T').tateRes F (Int.negSucc (n + 1)) =
      T'.tateRes F (Int.negSucc (n + 1)) ≫ T.tateRes F (Int.negSucc (n + 1)) := by
  simp only [tateRes_negSucc_succ, Category.assoc]
  -- The transfer is transitive along the image of the tower of Galois groups...
  rw [← TauCeti.TateCohomology.negSuccRes_trans_assoc (c.rep F) (galHom_range_trans_le T T')]
  refine congrArg (_ ≫ ·) ((Iso.eq_inv_comp _).2 ?_)
  -- ...and compatible with the identification of the middle Galois group with its image.
  simp only [tateRangeIso_hom, TauCeti.TateCohomology.map_comp_negSuccRes_assoc (b.rep F)
    (MonoidHom.ofInjective T'.galHom_injective) (isIntertwiningMap_repIso_range T' F)
    (galHom_range_map_ofInjective T T') (n + 1)]
  refine congrArg (_ ≫ ·) ?_
  -- It remains to compose the identifications of Galois groups and coefficients along the tower.
  rw [TauCeti.TateCohomology.map_comp_assoc, Iso.comp_inv_eq, Iso.eq_inv_comp]
  -- `rw [tateRangeIso_hom]` would be far slower here than `simp only`.
  simp only [tateRangeIso_hom, TauCeti.TateCohomology.map_comp]
  refine TauCeti.TateCohomology.map_congr (MulEquiv.ext fun γ ↦ Subtype.ext ?_)
    (LinearMap.ext fun x ↦ Subtype.ext ?_) _
  · simp [TauCeti.Subgroup.coe_congrOfMapEq_apply, MonoidHom.ofInjective_apply, galHom_trans T T']
  · exact (T'.repIso_hom_apply_coe F _).trans
      ((T.repIso_hom_apply_coe F x).trans ((T.trans T').repIso_hom_apply_coe F x).symm)

/-- **Tate restriction is functorial along a tower, in every integer degree**, as an identity of
morphisms: restricting from `K/F` to `K/E'` is restricting from `K/F` to `K/E` and then from `K/E`
to `K/E'`. -/
@[reassoc]
theorem tateRes_trans_eq_comp (T : LayerRestriction a b) (T' : LayerRestriction b c)
    (F : Formation G) (r : ℤ) : (T.trans T').tateRes F r = T'.tateRes F r ≫ T.tateRes F r := by
  -- The degrees are left to unification: instantiating at the literal `-1` rather than
  -- `Int.negSucc 0` makes `exact` markedly slower.
  rcases r with _ | (_ | n)
  · exact tateRes_trans_of_neg_one_le T T' F _ (by lia)
  · exact tateRes_trans_of_neg_one_le T T' F _ le_rfl
  · exact tateRes_negSucc_succ_trans T T' F n

/-- **Tate restriction is functorial along a tower, in every integer degree.** Restricting from
`K/F` to `K/E` and then to `K/E'` agrees with direct restriction from `K/F` to `K/E'`. -/
-- Not `@[simp]`: `LayerRestriction` is a `Prop`, so the left-hand side does not mention `T`, `T'`
-- or the middle layer, and `simp` could never instantiate them.
theorem tateRes_trans (T : LayerRestriction a b) (T' : LayerRestriction b c) (F : Formation G)
    (r : ℤ) (x : c.TateH F r) : (T.trans T').tateRes F r x = T.tateRes F r (T'.tateRes F r x) := by
  rw [tateRes_trans_eq_comp, ModuleCat.comp_apply]

end Towers

/-- **Corestriction after restriction is multiplication by the relative degree** `[E : F]`, in
every Tate degree. -/
@[reassoc, elementwise]
theorem tateCor_tateRes (T : LayerRestriction small big) (F : Formation G) (r : ℤ) :
    T.tateRes F r ≫ T.tateCor F r = T.relativeDegree • 𝟙 (big.TateH F r) := by
  obtain ⟨n, rfl⟩ | rfl | rfl | ⟨n, rfl⟩ :
      (∃ n : ℕ, r = n + 1) ∨ r = 0 ∨ r = -1 ∨ ∃ n : ℕ, r = Int.negSucc (n + 1) := by
    rcases lt_trichotomy r 0 with h | rfl | h
    · have hr : r ≤ -1 := by omega
      rcases eq_or_lt_of_le hr with rfl | h'
      · exact .inr (.inr (.inl rfl))
      · exact .inr (.inr (.inr ⟨(-r - 2).toNat, by omega⟩))
    · exact .inr (.inl rfl)
    · exact .inl ⟨(r - 1).toNat, by omega⟩
  · simp only [tateRes_ofNat_succ, tateCor_ofNat_succ, Category.assoc, Iso.inv_hom_id_assoc,
      cohomologyCor_cohomologyRes_assoc, Linear.smul_comp, Category.id_comp, Linear.comp_smul,
      Iso.hom_inv_id]
  · rw [← T.index_range_galHom]
    simpa using TauCeti.TateCohomology.H0Res_comp_H0Cor (big.rep F) T.galHom.range
  · rw [← T.index_range_galHom]
    simpa using
      TauCeti.TateCohomology.HNegOneRes_comp_HNegOneCor (big.rep F) T.galHom.range
  · rw [← T.index_range_galHom]
    simpa using
      TauCeti.TateCohomology.negSuccRes_comp_negSuccCor (big.rep F) T.galHom.range (n + 1)

/-! ### Trivial coefficients -/

/-- **Restriction on the Tate cohomology of finite normal layers with trivial integral
coefficients, in every integer degree.** It uses cohomological restriction in positive degrees,
the low-degree maps in degrees zero and minus one, and the homological transfer below them. -/
def trivialTateRes (T : LayerRestriction small big) :
    (r : ℤ) → big.TrivialTateH r ⟶ small.TrivialTateH r
  | .ofNat 0 =>
      TauCeti.TateCohomology.H0Res (Rep.trivial ℤ big.Gal ℤ) T.galHom.range ≫
        (T.trivialTateRangeIso 0).inv
  | .ofNat (n + 1) =>
      (TateCohomology.isoGroupCohomology (n + 1)).hom.app (Rep.trivial ℤ big.Gal ℤ) ≫
        groupCohomology.map T.galHom.range.subtype
          (𝟙 (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))) (n + 1) ≫
        (T.trivialTateRangeIso ((n + 1 : ℕ) : ℤ) ≪≫
          (TateCohomology.isoGroupCohomology (n + 1)).app
          (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))).inv
  | .negSucc 0 =>
      TauCeti.TateCohomology.HNegOneRes (Rep.trivial ℤ big.Gal ℤ) T.galHom.range ≫
        (T.trivialTateRangeIso (-1)).inv
  | .negSucc (n + 1) =>
      TauCeti.TateCohomology.negSuccRes (Rep.trivial ℤ big.Gal ℤ) T.galHom.range (n + 1) ≫
        (T.trivialTateRangeIso (Int.negSucc (n + 1))).inv

/-- In degree zero, trivial-coefficient Tate restriction is restriction of invariants to the image
subgroup, followed by the range comparison. -/
@[simp]
theorem trivialTateRes_zero (T : LayerRestriction small big) :
    T.trivialTateRes 0 =
      TauCeti.TateCohomology.H0Res (Rep.trivial ℤ big.Gal ℤ) T.galHom.range ≫
        (T.trivialTateRangeIso 0).inv :=
  (rfl)

/-- In a positive degree, trivial-coefficient Tate restriction is ordinary cohomological
restriction to the image subgroup, followed by the range comparison. -/
@[simp]
theorem trivialTateRes_ofNat_succ (T : LayerRestriction small big) (n : ℕ) :
    T.trivialTateRes ((n : ℤ) + 1) =
      (TateCohomology.isoGroupCohomology (n + 1)).hom.app (Rep.trivial ℤ big.Gal ℤ) ≫
        groupCohomology.map T.galHom.range.subtype
          (𝟙 (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))) (n + 1) ≫
        (T.trivialTateRangeIso ((n + 1 : ℕ) : ℤ) ≪≫
          (TateCohomology.isoGroupCohomology (n + 1)).app
          (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))).inv :=
  (rfl)

/-- Positive-degree trivial-coefficient Tate restriction is ordinary cohomological restriction to
the image subgroup, read through the canonical comparisons with ordinary cohomology. -/
@[reassoc]
theorem trivialTateRes_comp_isoGroupCohomology_hom (T : LayerRestriction small big) (n : ℕ)
    [NeZero n] :
    T.trivialTateRes n ≫ (T.trivialTateRangeIso n ≪≫ (TateCohomology.isoGroupCohomology n).app
        (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))).hom =
      (TateCohomology.isoGroupCohomology n).hom.app (Rep.trivial ℤ big.Gal ℤ) ≫
        groupCohomology.map T.galHom.range.subtype
          (𝟙 (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))) n := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k =>
    simp only [trivialTateRes]
    -- The comparison maps are composed across the semireducible group-cohomology carrier, where
    -- `simp`/`rw` cannot reassociate; the cancellation is applied as a term.
    exact (Category.assoc _ _ _).trans (congrArg _ ((Category.assoc _ _ _).trans
      ((congrArg _ (Iso.inv_hom_id _)).trans (Category.comp_id _))))

/-- In degree minus one, trivial-coefficient Tate restriction is the relative transfer on norm
kernels, followed by the range comparison. -/
@[simp]
theorem trivialTateRes_neg_one (T : LayerRestriction small big) :
    T.trivialTateRes (-1) =
      TauCeti.TateCohomology.HNegOneRes (Rep.trivial ℤ big.Gal ℤ) T.galHom.range ≫
        (T.trivialTateRangeIso (-1)).inv :=
  (rfl)

/-- In degree `-(n+2)`, trivial-coefficient Tate restriction is the transfer in group homology of
degree `n+1`, followed by the range comparison. -/
@[simp]
theorem trivialTateRes_negSucc_succ (T : LayerRestriction small big) (n : ℕ) :
    T.trivialTateRes (Int.negSucc (n + 1)) =
      TauCeti.TateCohomology.negSuccRes (Rep.trivial ℤ big.Gal ℤ) T.galHom.range (n + 1) ≫
        (T.trivialTateRangeIso (Int.negSucc (n + 1))).inv :=
  (rfl)

end TauCeti.ClassFieldTheory.LayerRestriction

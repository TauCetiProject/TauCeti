/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Orders
public import TauCeti.Combinatorics.PermutationTriple.Regular
public import TauCeti.GroupTheory.GroupAction.Stabilizer

/-!
# Regular triples and normal subgroups of triangle groups

A permutation triple `t` of degree `n` whose components have orders dividing `a`, `b`, `c` is a
permutation representation `TauCeti.TriangleGroup.toPerm t : Δ(a, b, c) →* Equiv.Perm (Fin n)`.
The preimage of the stabilizer of a sheet `i` is the point stabilizer of this action.

This file proves the *normality criterion*: for a connected triple, the point stabilizer is a
normal subgroup of `Δ(a, b, c)` exactly when the triple is regular. In that case the point
stabilizer is the kernel of the representation, a normal subgroup whose index is the degree
`n`, the order of the monodromy group.

Conversely the action of `Δ(a, b, c)` on the cosets of a normal subgroup `N` of index `n` is a
regular triple, the coset triple of `N`, and a regular triple is the coset triple of its kernel.
So regular triples up to relabeling are the same thing as finite-index normal subgroups of the
triangle group, the quotient by the subgroup being the monodromy group of the triple (the image of
the representation, `TauCeti.TriangleGroup.range_toPerm`).

## Main definitions

* `TauCeti.TriangleGroup.regularIsoClasses`: the isomorphism classes of regular triples of degree
  `n` with component orders dividing `a`, `b`, `c`.
* `TauCeti.TriangleGroup.regularIsoClassEquiv`: for `n ≠ 0`, the bijection between these classes
  and the normal subgroups of index `n` of `Δ(a, b, c)`.
* `TauCeti.TriangleGroup.automorphismGroupMulEquivQuotientKer`: the automorphism group of a regular
  triple is the opposite of the triangle group modulo the kernel of its representation.

## Main results

* `TauCeti.TriangleGroup.normal_comap_stabilizer_toPerm_iff`: for a connected triple, the point
  stabilizer of its representation is normal exactly when the triple is regular.
* `TauCeti.TriangleGroup.comap_stabilizer_toPerm_eq_ker`: when a sheet has trivial monodromy
  stabilizer (e.g. for a regular triple), its point stabilizer is the kernel of the representation.
* `TauCeti.TriangleGroup.index_ker_toPerm`: the kernel of the representation has index the order
  of the monodromy group, and `TauCeti.TriangleGroup.index_ker_toPerm_of_isRegular`: for a
  regular triple this is the degree.
* `TauCeti.TriangleGroup.isRegular_cosetTriple_iff`: the coset triple of a subgroup is regular
  exactly when the subgroup is normal, and `TauCeti.TriangleGroup.ker_toPerm_cosetTriple_of_normal`:
  the kernel of its representation is then the subgroup itself.
* `TauCeti.TriangleGroup.equivalent_cosetTriple_ker_toPerm`: a regular triple is isomorphic to the
  coset triple of its kernel.
* `TauCeti.TriangleGroup.coe_regularIsoClassEquiv_mk` and
  `TauCeti.TriangleGroup.coe_regularIsoClassEquiv_symm_apply`: the two directions of
  `TauCeti.TriangleGroup.regularIsoClassEquiv`.
* `TauCeti.TriangleGroup.kerLift_automorphismGroupMulEquivQuotientKer_apply`: the coset that
  `TauCeti.TriangleGroup.automorphismGroupMulEquivQuotientKer` assigns to an automorphism `τ` moves
  the sheet `0` to `τ 0`.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  LMS Student Texts 79, Cambridge University Press, 2012, Definition 2.64 and Proposition 2.66.
* G. A. Jones, D. Singerman, *Belyi functions, hypermaps and Galois groups*, Bull. London Math.
  Soc. 28 (1996), 561–590.
-/

open Equiv

public section

namespace TauCeti

namespace TriangleGroup

variable {a b c n : ℕ} (t : PermutationTriple n) (ha : t.σ0 ^ a = 1) (hb : t.σ1 ^ b = 1)
  (hc : t.σinf ^ c = 1)

/-- If a sheet has trivial monodromy stabilizer, its point stabilizer under the representation of
the triangle group is the kernel of the representation. -/
theorem comap_stabilizer_toPerm_eq_ker (i : Fin n)
    (hi : MulAction.stabilizer t.monodromyGroup i = ⊥) :
    (MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t ha hb hc) =
      (toPerm t ha hb hc).ker :=
  (toPerm t ha hb hc).comap_stabilizer_eq_ker i (by
    rw [range_toPerm]
    exact hi)

/-- **The normality criterion.** For a connected triple, the point stabilizer of a sheet under the
representation of the triangle group is a normal subgroup exactly when the triple is regular. -/
theorem normal_comap_stabilizer_toPerm_iff (ht : t.IsConnected) (i : Fin n) :
    ((MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t ha hb hc)).Normal ↔ t.IsRegular := by
  rw [(toPerm t ha hb hc).normal_comap_stabilizer_iff_isCancelSMul
      (by rw [range_toPerm]; exact ht.isPretransitive) i,
    range_toPerm, PermutationTriple.isRegular_iff_isCancelSMul, and_iff_right ht]

/-- The kernel of the representation of a triple has index the order of its monodromy group, the
image of the representation. -/
theorem index_ker_toPerm : (toPerm t ha hb hc).ker.index = Nat.card t.monodromyGroup := by
  rw [Subgroup.index_ker, range_toPerm]

/-- The kernel of the representation of a regular triple has index the degree. -/
theorem index_ker_toPerm_of_isRegular (ht : t.IsRegular) : (toPerm t ha hb hc).ker.index = n :=
  (index_ker_toPerm t ha hb hc).trans (PermutationTriple.isRegular_iff_card_monodromyGroup.mp ht).2

/-! ### Regular triples and normal subgroups of finite index -/

section NormalSubgroup

open PermutationTriple

variable (H : Subgroup (TriangleGroup a b c)) (e : TriangleGroup a b c ⧸ H ≃ Fin n)

/-- The components of a coset triple have orders dividing `a`, `b`, `c`. -/
theorem hasDividingOrders_cosetTriple : (cosetTriple H e).HasDividingOrders a b c :=
  (hasDividingOrders_iff _).mpr
    ⟨cosetTriple_σ0_pow H e, cosetTriple_σ1_pow H e, cosetTriple_σinf_pow H e⟩

/-- The coset triple of a subgroup is regular exactly when the subgroup is normal. -/
@[simp]
theorem isRegular_cosetTriple_iff : (cosetTriple H e).IsRegular ↔ H.Normal := by
  rw [← normal_comap_stabilizer_toPerm_iff _ (cosetTriple_σ0_pow H e) (cosetTriple_σ1_pow H e)
    (cosetTriple_σinf_pow H e) (isConnected_cosetTriple H e) (e (1 : TriangleGroup a b c)),
    comap_stabilizer_toPerm_cosetTriple]

/-- The kernel of the representation of the coset triple of a normal subgroup is that subgroup. -/
theorem ker_toPerm_cosetTriple_of_normal [H.Normal] {ha hb hc} :
    (toPerm (cosetTriple H e) ha hb hc).ker = H := by
  rw [ker_toPerm_cosetTriple, Subgroup.normalCore_eq_self]

/-- **A regular triple is the coset triple of its kernel**: the action of `Δ(a, b, c)` on the
sheets of a regular triple is its action on the cosets of the kernel of the representation. -/
theorem equivalent_cosetTriple_ker_toPerm (ht : t.IsRegular)
    (e : TriangleGroup a b c ⧸ (toPerm t ha hb hc).ker ≃ Fin n) :
    (cosetTriple _ e).Equivalent t :=
  have : NeZero n := ⟨ht.isConnected.ne_zero⟩
  -- A regular triple has trivial monodromy stabilisers, so its kernel is a point stabiliser.
  equivalent_cosetTriple_of_comap_stabilizer_eq _ _ ht.isConnected ha hb hc 0
    (comap_stabilizer_toPerm_eq_ker _ _ _ _ 0 (ht.isCancelSMul.stabilizer_eq_bot 0))

variable (a b c n) in
/-- The isomorphism classes of regular triples of degree `n` whose component orders divide `a`,
`b` and `c`. -/
def regularIsoClasses : Set (IsoClass n) :=
  IsoClass.mk '' {t | t.IsRegular ∧ t.HasDividingOrders a b c}

/-- The class of a triple is in `regularIsoClasses a b c n` exactly when the triple is regular
with component orders dividing `a`, `b`, `c`. -/
@[simp]
theorem mk_mem_regularIsoClasses_iff {t : PermutationTriple n} :
    IsoClass.mk t ∈ regularIsoClasses a b c n ↔ t.IsRegular ∧ t.HasDividingOrders a b c := by
  refine ⟨?_, fun h ↦ ⟨t, h, rfl⟩⟩
  rintro ⟨t', ⟨hr, hd⟩, h⟩
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp (IsoClass.mk_eq_mk_iff.mp h)
  exact ⟨(isRegular_smul_iff τ t').mpr hr, by simpa [hasDividingOrders_iff] using hd⟩

/-- A numbering of the cosets of a subgroup of index `n ≠ 0`. -/
private noncomputable def cosetEquivFin [NeZero n] (N : Subgroup (TriangleGroup a b c))
    (hN : N.index = n) : TriangleGroup a b c ⧸ N ≃ Fin n :=
  have hN : Nat.card (TriangleGroup a b c ⧸ N) = n := (Subgroup.index_eq_card _).symm.trans hN
  have : Finite (TriangleGroup a b c ⧸ N) :=
    Nat.finite_of_card_ne_zero (by rw [hN]; exact NeZero.ne n)
  Finite.equivFinOfCardEq hN

/-- The class of the coset triple of a normal subgroup of index `n`. -/
private noncomputable def cosetRegularIsoClass [NeZero n]
    (N : {N : Subgroup (TriangleGroup a b c) // N.Normal ∧ N.index = n}) :
    regularIsoClasses a b c n :=
  ⟨IsoClass.mk (cosetTriple N.1 (cosetEquivFin N.1 N.2.2)),
    mk_mem_regularIsoClasses_iff.mpr
      ⟨(isRegular_cosetTriple_iff _ _).mpr N.2.1, hasDividingOrders_cosetTriple _ _⟩⟩

private theorem coe_cosetRegularIsoClass [NeZero n]
    (N : {N : Subgroup (TriangleGroup a b c) // N.Normal ∧ N.index = n})
    (e : TriangleGroup a b c ⧸ N.1 ≃ Fin n) :
    (cosetRegularIsoClass N : IsoClass n) = IsoClass.mk (cosetTriple N.1 e) :=
  IsoClass.mk_eq_mk_iff.mpr (equivalent_cosetTriple _ _ _)

private theorem bijective_cosetRegularIsoClass [NeZero n] :
    Function.Bijective (cosetRegularIsoClass (a := a) (b := b) (c := c) (n := n)) := by
  refine ⟨fun N N' h ↦ Subtype.ext ?_, fun C ↦ ?_⟩
  · -- Isomorphic coset triples have the same kernel, which is the normal subgroup.
    have := N.2.1
    have := N'.2.1
    calc N.1 = (toPerm (cosetTriple N.1 (cosetEquivFin N.1 N.2.2)) (cosetTriple_σ0_pow _ _)
          (cosetTriple_σ1_pow _ _) (cosetTriple_σinf_pow _ _)).ker :=
          (ker_toPerm_cosetTriple_of_normal _ _).symm
      _ = (toPerm (cosetTriple N'.1 (cosetEquivFin N'.1 N'.2.2)) (cosetTriple_σ0_pow _ _)
          (cosetTriple_σ1_pow _ _) (cosetTriple_σinf_pow _ _)).ker :=
          ker_toPerm_eq_of_equivalent (IsoClass.mk_eq_mk_iff.mp (congrArg Subtype.val h)) ..
      _ = N'.1 := ker_toPerm_cosetTriple_of_normal _ _
  · -- A regular class is the class of the coset triple of the kernel of any of its triples.
    obtain ⟨t, ⟨hr, hd⟩, hC⟩ := C.2
    obtain ⟨ha, hb, hc⟩ := (hasDividingOrders_iff _).mp hd
    let N : {N : Subgroup (TriangleGroup a b c) // N.Normal ∧ N.index = n} :=
      ⟨(toPerm t ha hb hc).ker, inferInstance, index_ker_toPerm_of_isRegular _ _ _ _ hr⟩
    refine ⟨N, Subtype.ext ?_⟩
    rw [coe_cosetRegularIsoClass N (cosetEquivFin N.1 N.2.2), ← hC, IsoClass.mk_eq_mk_iff]
    exact equivalent_cosetTriple_ker_toPerm t ha hb hc hr _

/-- **Regular triples are finite-index normal subgroups of the triangle group.** For `n ≠ 0`, the
isomorphism classes of regular triples of degree `n` with component orders dividing `a`, `b`, `c`
correspond to the normal subgroups of index `n` of `Δ(a, b, c)`. A class goes to the kernel of the
representation of any of its triples (`TauCeti.TriangleGroup.coe_regularIsoClassEquiv_mk`), and a
normal subgroup `N` to the class of the coset triple of `N`, the action of `Δ(a, b, c)` on
`Δ(a, b, c) ⧸ N` (`TauCeti.TriangleGroup.coe_regularIsoClassEquiv_symm_apply`). -/
noncomputable def regularIsoClassEquiv [NeZero n] :
    regularIsoClasses a b c n ≃
      {N : Subgroup (TriangleGroup a b c) // N.Normal ∧ N.index = n} :=
  (Equiv.ofBijective _ bijective_cosetRegularIsoClass).symm

/-- The class of a normal subgroup `N` of index `n` is the class of its coset triple, for any
numbering `e` of the cosets. -/
theorem coe_regularIsoClassEquiv_symm_apply [NeZero n]
    (N : {N : Subgroup (TriangleGroup a b c) // N.Normal ∧ N.index = n})
    (e : TriangleGroup a b c ⧸ N.1 ≃ Fin n) :
    (regularIsoClassEquiv.symm N : IsoClass n) = IsoClass.mk (cosetTriple N.1 e) := by
  rw [regularIsoClassEquiv, Equiv.symm_symm, Equiv.ofBijective_apply, coe_cosetRegularIsoClass]

/-- The normal subgroup of the class of a regular triple `t` is the kernel of the representation
of `t`. -/
@[simp]
theorem coe_regularIsoClassEquiv_mk [NeZero n] (h : IsoClass.mk t ∈ regularIsoClasses a b c n) :
    (regularIsoClassEquiv ⟨IsoClass.mk t, h⟩ : Subgroup (TriangleGroup a b c)) =
      (toPerm t ha hb hc).ker := by
  have hr := (mk_mem_regularIsoClasses_iff.mp h).1
  have hN : (toPerm t ha hb hc).ker.index = n := index_ker_toPerm_of_isRegular _ _ _ _ hr
  let N : {N : Subgroup (TriangleGroup a b c) // N.Normal ∧ N.index = n} :=
    ⟨(toPerm t ha hb hc).ker, inferInstance, hN⟩
  have key : regularIsoClassEquiv ⟨IsoClass.mk t, h⟩ = N :=
    (Equiv.eq_symm_apply _).mp <| Subtype.ext <|
      ((coe_regularIsoClassEquiv_symm_apply N (cosetEquivFin N.1 N.2.2)).trans
        (IsoClass.mk_eq_mk_iff.mpr (equivalent_cosetTriple_ker_toPerm t ha hb hc hr _))).symm
  rw [key]

/-- The automorphism group of a regular triple is the opposite of the triangle group modulo the
kernel of its representation. This kernel is the normal subgroup selected by
`TauCeti.TriangleGroup.regularIsoClassEquiv`, by
`TauCeti.TriangleGroup.coe_regularIsoClassEquiv_mk`. The opposite occurs because automorphisms act
on the right of the regular monodromy action. An automorphism `τ` goes to the coset of the elements
moving the sheet `0` to `τ 0`
(`TauCeti.TriangleGroup.kerLift_automorphismGroupMulEquivQuotientKer_apply`). -/
noncomputable def automorphismGroupMulEquivQuotientKer (ht : t.IsRegular) :
    t.automorphismGroup ≃* (TriangleGroup a b c ⧸ (toPerm t ha hb hc).ker)ᵐᵒᵖ := by
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero ht.isConnected.ne_zero⟩
  let quotientKerMulEquivMonodromyGroup :=
    (QuotientGroup.quotientKerEquivRange (toPerm t ha hb hc)).trans
      (MulEquiv.subgroupCongr (range_toPerm t ha hb hc))
  exact (PermutationTriple.automorphismGroupMulEquivMonodromyGroupMulOpposite ht i).trans <|
    (MulEquiv.op quotientKerMulEquivMonodromyGroup).symm

/-- The characteristic property of `TauCeti.TriangleGroup.automorphismGroupMulEquivQuotientKer`:
the coset that an automorphism `τ` goes to moves the sheet `0` to `τ 0`. -/
@[simp]
theorem kerLift_automorphismGroupMulEquivQuotientKer_apply (ht : t.IsRegular)
    (τ : t.automorphismGroup) :
    QuotientGroup.kerLift (toPerm t ha hb hc)
        (automorphismGroupMulEquivQuotientKer t ha hb hc ht τ).unop
          ⟨0, Nat.pos_of_ne_zero ht.isConnected.ne_zero⟩ =
      (τ : Perm (Fin n)) ⟨0, Nat.pos_of_ne_zero ht.isConnected.ne_zero⟩ := by
  have hq (x : TriangleGroup a b c ⧸ (toPerm t ha hb hc).ker) :
      (((QuotientGroup.quotientKerEquivRange (toPerm t ha hb hc)).trans
        (MulEquiv.subgroupCongr (range_toPerm t ha hb hc)) x : t.monodromyGroup) :
          Perm (Fin n)) = QuotientGroup.kerLift (toPerm t ha hb hc) x :=
    -- The first isomorphism theorem sends the coset of `g` to `toPerm t ha hb hc g` by definition.
    QuotientGroup.induction_on x fun _ ↦ rfl
  rw [automorphismGroupMulEquivQuotientKer, MulEquiv.trans_apply, MulEquiv.op_apply_symm_apply,
    Function.comp_apply, Function.comp_apply, MulOpposite.unop_op, ← hq,
    MulEquiv.apply_symm_apply]
  simpa only [Subgroup.smul_def, Perm.smul_def] using
    PermutationTriple.unop_automorphismGroupMulEquivMonodromyGroupMulOpposite_smul ht _ τ

end NormalSubgroup

end TriangleGroup

end TauCeti

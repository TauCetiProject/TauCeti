/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.AutomorphismOrder
public import TauCeti.Combinatorics.PermutationTriple.Orders.IsoClass
public import TauCeti.GroupTheory.QuotientGroup.CosetAction
public import TauCeti.GroupTheory.TriangleGroup.Regular

/-!
# Classification of finite-index subgroups of triangle groups by coset triples

`TauCeti.TriangleGroup.Regular` classifies finite-index *normal* subgroups of `Δ(a, b, c)` by
isomorphism classes of regular permutation triples with component orders dividing `(a, b, c)`. This
file removes the normality assumption and classifies all finite-index subgroups of `Δ(a, b, c)`:

* **Conjugacy and pointedness.** Two coset triples `cosetTriple H₁ e₁` and `cosetTriple H₂ e₂` are
  isomorphic if and only if `H₁` and `H₂` are conjugate in `Δ(a, b, c)`
  (`TauCeti.TriangleGroup.equivalent_cosetTriple_iff`), and define the same marked class at the base
  cosets `e₁ 1` and `e₂ 1` if and only if `H₁ = H₂`
  (`TauCeti.TriangleGroup.markedIsoClass_cosetConnectedTriple_eq_iff`).
* **Marked and unmarked bijections.** For `n ≠ 0`, index-`n` subgroups of `Δ(a, b, c)` correspond
  bijectively to marked connected triple classes of degree `n` with dividing orders `(a, b, c)`
  (`TauCeti.TriangleGroup.markedSubgroupEquiv`), while conjugacy classes of index-`n` subgroups
  correspond bijectively to unmarked connected triple classes with dividing orders `(a, b, c)`
  (`TauCeti.TriangleGroup.conjClassesConnectedIsoClassEquiv` and
  `TauCeti.TriangleGroup.conjClassesIsoClassEquiv`).
* **Monodromy, automorphisms, and finiteness.** For any enumeration `e : Δ(a, b, c) ⧸ H ≃ Fin n`,
  the monodromy group is isomorphic to `Δ(a, b, c) ⧸ H.normalCore` of order `H.normalCore.index`,
  the automorphism group of `cosetTriple H e` is canonically isomorphic to `N(H) ⧸ H`, the number
  of conjugates of `H` is `n / #(cosetTriple H e).automorphismGroup`, and for `n ≠ 0` there are
  only finitely many subgroups of index `n` in `Δ(a, b, c)`, counted by summing
  `n / C.automorphismOrder` over `connectedIsoClassesWithDividingOrders n a b c`.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  LMS Student Texts 79, Cambridge University Press, 2012, §4.2.
* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer, 2004, §1.5.
-/

open Equiv MulAction
open scoped Pointwise

public section

namespace TauCeti.TriangleGroup

variable {a b c n : ℕ}

/-! ### Monodromy group and normal core of a coset triple -/

section Monodromy

variable (H : Subgroup (TriangleGroup a b c)) (e : TriangleGroup a b c ⧸ H ≃ Fin n)

/-- `cosetTriple H e` is the triple associated by `permutationTripleEquiv` to
`e.permutationRepresentation`. -/
theorem cosetTriple_eq_permutationTripleEquiv :
    cosetTriple H e =
      (permutationTripleEquiv (e.permutationRepresentation (G := TriangleGroup a b c))).1 :=
  PermutationTriple.ext_of_two (by simp) (by simp)

/-- The monodromy group of `cosetTriple H e` is the image of `e.permutationRepresentation`. -/
@[simp]
theorem monodromyGroup_cosetTriple :
    (cosetTriple H e).monodromyGroup =
      (e.permutationRepresentation (G := TriangleGroup a b c)).range := by
  rw [cosetTriple_eq_permutationTripleEquiv, monodromyGroup_permutationTripleEquiv]

/-- The quotient of `Δ(a, b, c)` by the normal core of `H` is canonically isomorphic to the
monodromy group of `cosetTriple H e`. -/
noncomputable def quotientNormalCoreMulEquivMonodromyGroup :
    TriangleGroup a b c ⧸ H.normalCore ≃* (cosetTriple H e).monodromyGroup :=
  (QuotientGroup.quotientMulEquivOfEq
      (H.normalCore_eq_ker.trans e.ker_permutationRepresentation.symm)).trans <|
    (QuotientGroup.quotientKerEquivRange
      (e.permutationRepresentation (G := TriangleGroup a b c))).trans <|
      MulEquiv.subgroupCongr (monodromyGroup_cosetTriple H e).symm

@[simp]
theorem coe_quotientNormalCoreMulEquivMonodromyGroup_mk (g : TriangleGroup a b c) :
    (quotientNormalCoreMulEquivMonodromyGroup H e (g : TriangleGroup a b c ⧸ H.normalCore) :
        Perm (Fin n)) =
      e.permutationRepresentation g :=
  (rfl)

/-- The order of the monodromy group of `cosetTriple H e` equals the index of `H.normalCore`. -/
theorem card_monodromyGroup_cosetTriple :
    Nat.card (cosetTriple H e).monodromyGroup = H.normalCore.index := by
  rw [← Nat.card_congr (quotientNormalCoreMulEquivMonodromyGroup H e).toEquiv,
    Subgroup.index_eq_card]

/-- A subgroup `H` with coset enumeration `e : Δ(a, b, c) ⧸ H ≃ Fin n` is normal if and only if
the monodromy group of `cosetTriple H e` has order `n`. -/
theorem normal_iff_card_monodromyGroup_cosetTriple_eq :
    H.Normal ↔ Nat.card (cosetTriple H e).monodromyGroup = n := by
  rw [← isRegular_cosetTriple_iff H e, PermutationTriple.isRegular_iff_card_monodromyGroup,
    and_iff_right (isConnected_cosetTriple H e)]

/-- `cosetTriple H e` bundled as a connected permutation triple. -/
noncomputable def cosetConnectedTriple : ConnectedTriple n :=
  ⟨cosetTriple H e, isConnected_cosetTriple H e⟩

@[simp]
theorem coe_cosetConnectedTriple :
    (cosetConnectedTriple H e : PermutationTriple n) = cosetTriple H e :=
  (rfl)

theorem hasDividingOrders_cosetConnectedTriple :
    (ConnectedIsoClass.mk (cosetConnectedTriple H e)).HasDividingOrders a b c := by
  rw [ConnectedIsoClass.hasDividingOrders_mk]
  exact hasDividingOrders_cosetTriple H e

end Monodromy

/-! ### Conjugacy, pointedness, and surjectivity -/

/-- **Conjugacy criterion for coset triples.** Two subgroups `H₁, H₂ ≤ Δ(a, b, c)` with coset
enumerations of the same degree give isomorphic coset triples if and only if `H₁` and `H₂` are
conjugate in `Δ(a, b, c)`. -/
theorem equivalent_cosetTriple_iff {H₁ H₂ : Subgroup (TriangleGroup a b c)}
    (e₁ : TriangleGroup a b c ⧸ H₁ ≃ Fin n) (e₂ : TriangleGroup a b c ⧸ H₂ ≃ Fin n) :
    (cosetTriple H₁ e₁).Equivalent (cosetTriple H₂ e₂) ↔
      ∃ g : ConjAct (TriangleGroup a b c), g • H₁ = H₂ := by
  rw [cosetTriple_eq_permutationTripleEquiv, cosetTriple_eq_permutationTripleEquiv,
    equivalent_permutationTripleEquiv_iff,
    ← e₁.exists_conj_permutationRepresentation_quotient_iff e₂]
  simp only [MulEquiv.toMonoidHom_eq_coe]

/-- **Pointed classification for coset triples.** Marking the base cosets `e₁ 1` and `e₂ 1`
determines the subgroup on the nose, not merely up to conjugacy. -/
theorem markedIsoClass_cosetConnectedTriple_eq_iff {H₁ H₂ : Subgroup (TriangleGroup a b c)}
    (e₁ : TriangleGroup a b c ⧸ H₁ ≃ Fin n) (e₂ : TriangleGroup a b c ⧸ H₂ ≃ Fin n) :
    MarkedIsoClass.mk (cosetConnectedTriple H₁ e₁) (e₁ (1 : TriangleGroup a b c)) =
      MarkedIsoClass.mk (cosetConnectedTriple H₂ e₂) (e₂ (1 : TriangleGroup a b c)) ↔
        H₁ = H₂ := by
  rw [MarkedIsoClass.mk_eq_mk_iff_exists_smul, eq_comm,
    ← e₂.exists_conj_permutationRepresentation_quotient_eq_and_apply_one_iff e₁]
  refine exists_congr fun τ ↦ and_congr_left fun _ ↦ ?_
  rw [Subtype.ext_iff, ConnectedTriple.coe_smul, coe_cosetConnectedTriple,
    coe_cosetConnectedTriple, cosetTriple_eq_permutationTripleEquiv,
    cosetTriple_eq_permutationTripleEquiv, ← permutationTripleEquiv_conj, ← Subtype.ext_iff,
    permutationTripleEquiv.apply_eq_iff_eq, MulEquiv.toMonoidHom_eq_coe]

/-- For a connected triple `t` of degree `n` with dividing orders `(a, b, c)`, the stabilizer of any
sheet `i` under `toPerm t` has index `n` in `Δ(a, b, c)`. -/
theorem index_comap_stabilizer_toPerm {t : PermutationTriple n} (ht : t.IsConnected)
    (ha : t.σ0 ^ a = 1) (hb : t.σ1 ^ b = 1) (hc : t.σinf ^ c = 1) (i : Fin n) :
    ((MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t ha hb hc)).index = n := by
  have hρ := (isConnected_iff_isPretransitive_range_toPerm t ha hb hc).mp ht |>.2
  exact Subgroup.index_eq_of_equiv_fin _ ((toPerm t ha hb hc).quotientComapStabilizerEquiv hρ i)

/-- **Surjectivity of `cosetTriple` at a chosen sheet.** Every connected triple `t` of degree `n`
with dividing orders `(a, b, c)` and chosen sheet `i` is literally equal to `cosetTriple H e` for
an index-`n` subgroup `H` and coset enumeration `e` sending `1` to `i`. -/
theorem exists_cosetTriple_eq {t : PermutationTriple n} (ht : t.IsConnected)
    (ha : t.σ0 ^ a = 1) (hb : t.σ1 ^ b = 1) (hc : t.σinf ^ c = 1) (i : Fin n) :
    ∃ (H : Subgroup (TriangleGroup a b c)) (e : TriangleGroup a b c ⧸ H ≃ Fin n),
      H.index = n ∧ e (1 : TriangleGroup a b c) = i ∧ cosetTriple H e = t := by
  have hρ := (isConnected_iff_isPretransitive_range_toPerm t ha hb hc).mp ht |>.2
  let H := (MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t ha hb hc)
  let e : TriangleGroup a b c ⧸ H ≃ Fin n := (toPerm t ha hb hc).quotientComapStabilizerEquiv hρ i
  have he : e.permutationRepresentation = toPerm t ha hb hc :=
    Equiv.permutationRepresentation_eq_of_map_smul e
      ((toPerm t ha hb hc).quotientComapStabilizerEquiv_smul hρ i)
  refine ⟨H, e, Subgroup.index_eq_of_equiv_fin H e, ?_, ?_⟩
  · -- Expose `e` on `1` to apply `quotientComapStabilizerEquiv_mk`.
    change (toPerm t ha hb hc).quotientComapStabilizerEquiv hρ i (QuotientGroup.mk 1) = i
    simp
  · rw [cosetTriple_eq_permutationTripleEquiv, he, permutationTripleEquiv_toPerm]

/-- Every connected triple of degree `n` with dividing orders `(a, b, c)` is isomorphic to the
coset triple of an index-`n` subgroup of `Δ(a, b, c)`. -/
theorem exists_cosetTriple_equivalent {t : PermutationTriple n} (ht : t.IsConnected)
    (ha : t.σ0 ^ a = 1) (hb : t.σ1 ^ b = 1) (hc : t.σinf ^ c = 1) :
    ∃ (H : Subgroup (TriangleGroup a b c)) (e : TriangleGroup a b c ⧸ H ≃ Fin n),
      H.index = n ∧ (cosetTriple H e).Equivalent t := by
  obtain ⟨H, e, hH, -, rfl⟩ := exists_cosetTriple_eq ht ha hb hc ⟨0, Nat.pos_of_ne_zero ht.ne_zero⟩
  exact ⟨H, e, hH, PermutationTriple.equivalent_iff_exists_smul_eq.mpr ⟨1, one_smul _ _⟩⟩

/-! ### Marked and unmarked classification equivalences -/

section Classification

/-- Assigning to an index-`n` subgroup the marked class of its coset triple at the base coset. -/
private noncomputable def toMarkedSubgroupClass [NeZero n]
    (H : {H : Subgroup (TriangleGroup a b c) // H.index = n}) :
    {m : MarkedIsoClass n // m.HasDividingOrders a b c} :=
  let e := H.1.quotientEquivFin H.2
  ⟨MarkedIsoClass.mk (cosetConnectedTriple H.1 e) (e (1 : TriangleGroup a b c)),
    (MarkedIsoClass.hasDividingOrders_mk _ _).mpr (hasDividingOrders_cosetTriple H.1 e)⟩

private theorem bijective_toMarkedSubgroupClass [NeZero n] :
    Function.Bijective (toMarkedSubgroupClass (a := a) (b := b) (c := c) (n := n)) := by
  refine ⟨fun H₁ H₂ h ↦ Subtype.ext ?_, fun ⟨m, hm⟩ ↦ ?_⟩
  · exact (markedIsoClass_cosetConnectedTriple_eq_iff _ _).mp (congrArg Subtype.val h)
  · obtain ⟨t, i, rfl⟩ := MarkedIsoClass.mk_surjective m
    obtain ⟨ha, hb, hc⟩ := (PermutationTriple.hasDividingOrders_iff _).mp
      ((MarkedIsoClass.hasDividingOrders_mk t i).mp hm)
    obtain ⟨H, e, hH, he1, het⟩ := exists_cosetTriple_eq t.2 ha hb hc i
    refine ⟨⟨H, hH⟩, Subtype.ext ?_⟩
    have hconn : cosetConnectedTriple H e = t := Subtype.ext het
    have hindep :
        MarkedIsoClass.mk (cosetConnectedTriple H (H.quotientEquivFin hH))
          (H.quotientEquivFin hH (1 : TriangleGroup a b c)) =
        MarkedIsoClass.mk (cosetConnectedTriple H e) (e (1 : TriangleGroup a b c)) :=
      (markedIsoClass_cosetConnectedTriple_eq_iff _ _).mpr rfl
    exact hindep.trans (by rw [hconn, he1])

/-- **Marked subgroup classification for `Δ(a, b, c)`.** For `n ≠ 0`, subgroups of index `n` in
`Δ(a, b, c)` biject with marked isomorphism classes of connected degree-`n` triples whose component
orders divide `(a, b, c)`. -/
noncomputable def markedSubgroupEquiv [NeZero n] :
    {H : Subgroup (TriangleGroup a b c) // H.index = n} ≃
      {m : MarkedIsoClass n // m.HasDividingOrders a b c} :=
  Equiv.ofBijective toMarkedSubgroupClass bijective_toMarkedSubgroupClass

/-- For any coset enumeration `e`, `markedSubgroupEquiv` sends `H` to the class of
`cosetConnectedTriple H e` marked at `e 1`. -/
theorem coe_markedSubgroupEquiv_apply [NeZero n]
    (H : {H : Subgroup (TriangleGroup a b c) // H.index = n})
    (e : TriangleGroup a b c ⧸ H.1 ≃ Fin n) :
    (markedSubgroupEquiv H : MarkedIsoClass n) =
      MarkedIsoClass.mk (cosetConnectedTriple H.1 e) (e (1 : TriangleGroup a b c)) :=
  (markedIsoClass_cosetConnectedTriple_eq_iff _ _).mpr rfl

/-- The inverse of `markedSubgroupEquiv` recovers the stabilizer of the marked sheet `i` under
`toPerm`. -/
@[simp]
theorem coe_markedSubgroupEquiv_symm_mk [NeZero n] (t : ConnectedTriple n) (i : Fin n)
    (hm : (MarkedIsoClass.mk t i).HasDividingOrders a b c) (ha : t.1.σ0 ^ a = 1)
    (hb : t.1.σ1 ^ b = 1) (hc : t.1.σinf ^ c = 1) :
    (markedSubgroupEquiv.symm ⟨MarkedIsoClass.mk t i, hm⟩ : Subgroup (TriangleGroup a b c)) =
      (MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t.1 ha hb hc) := by
  let H : {H : Subgroup (TriangleGroup a b c) // H.index = n} :=
    ⟨(MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t.1 ha hb hc),
      index_comap_stabilizer_toPerm t.2 ha hb hc i⟩
  suffices markedSubgroupEquiv.symm ⟨MarkedIsoClass.mk t i, hm⟩ = H from congrArg Subtype.val this
  rw [Equiv.symm_apply_eq]
  apply Subtype.ext
  have hρ := (isConnected_iff_isPretransitive_range_toPerm t.1 ha hb hc).mp t.2 |>.2
  let e : TriangleGroup a b c ⧸ H.1 ≃ Fin n :=
    (toPerm t.1 ha hb hc).quotientComapStabilizerEquiv hρ i
  have he : e.permutationRepresentation = toPerm t.1 ha hb hc :=
    Equiv.permutationRepresentation_eq_of_map_smul e
      ((toPerm t.1 ha hb hc).quotientComapStabilizerEquiv_smul hρ i)
  have hconn : cosetConnectedTriple H.1 e = t := Subtype.ext <| by
    rw [coe_cosetConnectedTriple, cosetTriple_eq_permutationTripleEquiv, he,
      permutationTripleEquiv_toPerm]
  have he1 : e (1 : TriangleGroup a b c) = i := by
    -- Unfold `e` on `1` to evaluate `quotientComapStabilizerEquiv` on the trivial coset.
    change (toPerm t.1 ha hb hc).quotientComapStabilizerEquiv hρ i (QuotientGroup.mk 1) = i
    simp
  rw [coe_markedSubgroupEquiv_apply H e, hconn, he1]

/-- Assigning to an index-`n` subgroup the connected isomorphism class of its coset triple. -/
private noncomputable def toConnectedClass [NeZero n]
    (H : {H : Subgroup (TriangleGroup a b c) // H.index = n}) :
    {C : ConnectedIsoClass n // C.HasDividingOrders a b c} :=
  let e := H.1.quotientEquivFin H.2
  ⟨ConnectedIsoClass.mk (cosetConnectedTriple H.1 e), hasDividingOrders_cosetConnectedTriple H.1 e⟩

private theorem toConnectedClass_eq_iff [NeZero n]
    {H₁ H₂ : {H : Subgroup (TriangleGroup a b c) // H.index = n}} :
    toConnectedClass H₁ = toConnectedClass H₂ ↔
      MulAction.orbitRel (ConjAct (TriangleGroup a b c)) _ H₁ H₂ := by
  rw [Subtype.ext_iff]
  -- Unfold `toConnectedClass` to its underlying `ConnectedIsoClass.mk` equality.
  change ConnectedIsoClass.mk _ = ConnectedIsoClass.mk _ ↔ _
  rw [ConnectedIsoClass.mk_eq_mk_iff_equivalent, coe_cosetConnectedTriple,
    coe_cosetConnectedTriple, equivalent_cosetTriple_iff, MulAction.orbitRel_apply,
    MulAction.mem_orbit_symm, MulAction.mem_orbit_iff]
  exact exists_congr fun g ↦ by rw [← Subgroup.coe_conjAct_smul_subtypeIndex, Subtype.ext_iff]

/-- **Unmarked conjugacy-class classification for `Δ(a, b, c)`.** For `n ≠ 0`, conjugacy classes of
index-`n` subgroups of `Δ(a, b, c)` biject with connected isomorphism classes of degree-`n` triples
whose component orders divide `(a, b, c)`. -/
noncomputable def conjClassesConnectedIsoClassEquiv [NeZero n] :
    MulAction.orbitRel.Quotient (ConjAct (TriangleGroup a b c))
      {H : Subgroup (TriangleGroup a b c) // H.index = n} ≃
      {C : ConnectedIsoClass n // C.HasDividingOrders a b c} :=
  Equiv.ofBijective
    (Quotient.liftOn' · toConnectedClass fun _ _ h ↦ toConnectedClass_eq_iff.mpr h)
    ⟨Quotient.ind₂' fun _ _ h ↦ Quotient.eq''.mpr (toConnectedClass_eq_iff.mp h), fun ⟨C, hC⟩ ↦ by
      obtain ⟨t, rfl⟩ := ConnectedIsoClass.mk_surjective C
      obtain ⟨ha, hb, hc⟩ := (PermutationTriple.hasDividingOrders_iff _).mp
        ((ConnectedIsoClass.hasDividingOrders_mk t).mp hC)
      obtain ⟨H, e, hH, -, het⟩ :=
        exists_cosetTriple_eq t.2 ha hb hc ⟨0, Nat.pos_of_ne_zero t.2.ne_zero⟩
      refine ⟨Quotient.mk'' ⟨H, hH⟩, Subtype.ext ?_⟩
      -- Expose the underlying `ConnectedIsoClass.mk` image of `Quotient.mk''`.
      change ConnectedIsoClass.mk _ = ConnectedIsoClass.mk t
      rw [ConnectedIsoClass.mk_eq_mk_iff_equivalent, coe_cosetConnectedTriple, ← het]
      exact equivalent_cosetTriple H _ e⟩

/-- For any coset enumeration `e`, `conjClassesConnectedIsoClassEquiv` sends the conjugacy class of
`H` to `ConnectedIsoClass.mk (cosetConnectedTriple H e)`. -/
theorem coe_conjClassesConnectedIsoClassEquiv_mk [NeZero n]
    (H : {H : Subgroup (TriangleGroup a b c) // H.index = n})
    (e : TriangleGroup a b c ⧸ H.1 ≃ Fin n) :
    (conjClassesConnectedIsoClassEquiv (Quotient.mk'' H) : ConnectedIsoClass n) =
      ConnectedIsoClass.mk (cosetConnectedTriple H.1 e) := by
  -- Expose the quotient lift on `Quotient.mk'' H` to compare coset enumerations.
  change ConnectedIsoClass.mk _ = ConnectedIsoClass.mk (cosetConnectedTriple H.1 e)
  rw [ConnectedIsoClass.mk_eq_mk_iff_equivalent]
  exact equivalent_cosetTriple H.1 _ e

/-- Conjugacy classes of index-`n` subgroups of `Δ(a, b, c)` also biject with the subtype of
`PermutationTriple.IsoClass n` cut out by connectedness and dividing orders `(a, b, c)`. -/
noncomputable def conjClassesIsoClassEquiv [NeZero n] :
    MulAction.orbitRel.Quotient (ConjAct (TriangleGroup a b c))
      {H : Subgroup (TriangleGroup a b c) // H.index = n} ≃
      {C : PermutationTriple.IsoClass n // C.IsConnected ∧ C.HasDividingOrders a b c} :=
  conjClassesConnectedIsoClassEquiv.trans
    (ConnectedIsoClass.equivIsoClassSubtypeDividingOrders n a b c)

theorem coe_conjClassesIsoClassEquiv_mk [NeZero n]
    (H : {H : Subgroup (TriangleGroup a b c) // H.index = n})
    (e : TriangleGroup a b c ⧸ H.1 ≃ Fin n) :
    (conjClassesIsoClassEquiv (Quotient.mk'' H) : PermutationTriple.IsoClass n) =
      PermutationTriple.IsoClass.mk (cosetTriple H.1 e) := by
  rw [conjClassesIsoClassEquiv, Equiv.trans_apply,
    ConnectedIsoClass.coe_equivIsoClassSubtypeDividingOrders_apply,
    coe_conjClassesConnectedIsoClassEquiv_mk H e, ConnectedIsoClass.forget_mk,
    coe_cosetConnectedTriple]

end Classification

/-! ### Normalizer, automorphism group, and subgroup counts at fixed index -/

section NormalizerAndCounting

/-- **The deck-transformation isomorphism for `cosetTriple`.** Right multiplication on cosets
identifies `N(H) ⧸ H` with the automorphism group of `cosetTriple H e`. -/
noncomputable def normalizerQuotientEquivAutomorphismGroup
    (H : Subgroup (TriangleGroup a b c)) (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    Subgroup.normalizer (H : Set (TriangleGroup a b c)) ⧸
        H.subgroupOf (Subgroup.normalizer (H : Set (TriangleGroup a b c))) ≃*
      (cosetTriple H e).automorphismGroup :=
  (H.normalizerQuotientEquivCentralizer e).trans <|
    MulEquiv.subgroupCongr <| by
      rw [(cosetTriple H e).automorphismGroup_eq_centralizer_monodromyGroup,
        monodromyGroup_cosetTriple]

@[simp]
theorem coe_normalizerQuotientEquivAutomorphismGroup_mk_apply
    (H : Subgroup (TriangleGroup a b c)) (e : TriangleGroup a b c ⧸ H ≃ Fin n)
    (m : Subgroup.normalizer (H : Set (TriangleGroup a b c))) (g : TriangleGroup a b c) :
    (normalizerQuotientEquivAutomorphismGroup H e (m : _ ⧸ _) : Perm (Fin n))
        (e (g : TriangleGroup a b c ⧸ H)) =
      e ((g * (m : TriangleGroup a b c)⁻¹ : TriangleGroup a b c) : TriangleGroup a b c ⧸ H) :=
  H.coe_normalizerQuotientEquivCentralizer_mk_apply e m g

/-- The automorphism group of `cosetTriple H e` has order `[N(H) : H]`. -/
theorem card_automorphismGroup_cosetTriple
    (H : Subgroup (TriangleGroup a b c)) (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    Nat.card (cosetTriple H e).automorphismGroup =
      H.relIndex (Subgroup.normalizer (H : Set (TriangleGroup a b c))) := by
  rw [(cosetTriple H e).automorphismGroup_eq_centralizer_monodromyGroup,
    monodromyGroup_cosetTriple, H.card_centralizer_permutationRepresentation e]

/-- The number of conjugates of `H` in `Δ(a, b, c)` is
`n / #(cosetTriple H e).automorphismGroup`. -/
theorem card_orbit_conjAct_eq_div_automorphismGroup
    (H : Subgroup (TriangleGroup a b c)) (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    Nat.card (MulAction.orbit (ConjAct (TriangleGroup a b c)) H) =
      n / Nat.card (cosetTriple H e).automorphismGroup := by
  rw [(cosetTriple H e).automorphismGroup_eq_centralizer_monodromyGroup,
    monodromyGroup_cosetTriple, H.card_orbit_conjAct_eq_index_div_card_centralizer e,
    H.index_eq_of_equiv_fin e]

/-- For `n ≠ 0`, a triangle group `Δ(a, b, c)` has only finitely many subgroups of index `n`. -/
instance [NeZero n] : Finite {H : Subgroup (TriangleGroup a b c) // H.index = n} :=
  Finite.of_equiv _ markedSubgroupEquiv.symm

/-- The number of subgroups in an index-`n` conjugacy class `ω` of `Δ(a, b, c)` is `n` divided by
the automorphism order of the corresponding connected triple class. -/
theorem card_orbit_eq_div_automorphismOrder [NeZero n]
    (ω : MulAction.orbitRel.Quotient (ConjAct (TriangleGroup a b c))
      {H : Subgroup (TriangleGroup a b c) // H.index = n}) :
    Nat.card (MulAction.orbitRel.Quotient.orbit ω) =
      n / (conjClassesConnectedIsoClassEquiv ω).1.automorphismOrder := by
  induction ω using Quotient.inductionOn' with
  | h H =>
    let e := H.1.quotientEquivFin H.2
    rw [MulAction.orbitRel.Quotient.orbit_mk,
      Nat.card_congr (Subgroup.orbitConjActSubtypeIndexEquiv H),
      card_orbit_conjAct_eq_div_automorphismGroup H.1 e,
      coe_conjClassesConnectedIsoClassEquiv_mk H e, ConnectedIsoClass.automorphismOrder_mk,
      coe_cosetConnectedTriple]

/-- The number of conjugacy classes of index-`n` subgroups of `Δ(a, b, c)` equals the cardinality of
`connectedIsoClassesWithDividingOrders n a b c`. -/
theorem card_conjClasses_eq_card_connectedIsoClassesWithDividingOrders [NeZero n] :
    Nat.card (MulAction.orbitRel.Quotient (ConjAct (TriangleGroup a b c))
      {H : Subgroup (TriangleGroup a b c) // H.index = n}) =
      (connectedIsoClassesWithDividingOrders n a b c).card := by
  rw [card_connectedIsoClassesWithDividingOrders]
  exact Nat.card_congr conjClassesConnectedIsoClassEquiv

/-- **Index-`n` subgroup count for `Δ(a, b, c)`.** For `n ≠ 0`, the number of index-`n` subgroups of
`Δ(a, b, c)` is the sum of `n / C.automorphismOrder` over all connected isomorphism classes `C` of
degree `n` with dividing orders `(a, b, c)`. -/
theorem card_subgroups_index_eq_sum_div_automorphismOrder [NeZero n] :
    Nat.card {H : Subgroup (TriangleGroup a b c) // H.index = n} =
      ∑ C ∈ connectedIsoClassesWithDividingOrders n a b c, n / C.automorphismOrder := by
  classical
  let _ : Fintype (MulAction.orbitRel.Quotient (ConjAct (TriangleGroup a b c))
      {H : Subgroup (TriangleGroup a b c) // H.index = n}) := Fintype.ofFinite _
  rw [(Nat.card_congr (MulAction.selfEquivSigmaOrbits' (ConjAct (TriangleGroup a b c))
    {H : Subgroup (TriangleGroup a b c) // H.index = n})).trans Nat.card_sigma]
  simp_rw [card_orbit_eq_div_automorphismOrder]
  rw [Fintype.sum_equiv conjClassesConnectedIsoClassEquiv _
    (fun C : {C : ConnectedIsoClass n // C.HasDividingOrders a b c} ↦ n / C.1.automorphismOrder)
    fun _ ↦ rfl]
  exact (Finset.sum_subtype (connectedIsoClassesWithDividingOrders n a b c)
    (fun _ ↦ mem_connectedIsoClassesWithDividingOrders)
    (fun C ↦ n / C.automorphismOrder)).symm

end NormalizerAndCounting

end TauCeti.TriangleGroup

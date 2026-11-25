/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Conjugates
public import TauCeti.Algebra.GroupAction.CosetRepresentation
public import TauCeti.Combinatorics.PermutationTriple.AutomorphismOrder
public import TauCeti.Combinatorics.PermutationTriple.Mirror
public import TauCeti.Combinatorics.PermutationTriple.Orders.IsoClass
public import TauCeti.GroupTheory.TriangleGroup.Regular

/-!
# Millington's dictionary and subgroup counts at fixed index for triangle groups

Every subgroup `H` of `Δ(a, b, c)` of finite index `n ≠ 0`, together with a numbering
`e : Δ(a, b, c) ⧸ H ≃ Fin n` of its left cosets, determines a connected permutation triple
`TauCeti.TriangleGroup.cosetTriple H e` (bundled as `cosetConnectedTriple H e`) of degree `n` whose
component orders divide `a`, `b`, `c`. Combining `TauCeti.TriangleGroup.permutationTripleEquiv` with
`TauCeti.Algebra.GroupAction.CosetRepresentation` gives the coset dictionary for `Δ(a, b, c)`:

* **Millington's theorem (`TauCeti.TriangleGroup.cosetTriple_equivalent_cosetTriple_iff`,
  `TauCeti.TriangleGroup.cosetIsoClassEquiv`, `cosetConnectedIsoClassEquiv`).** Two coset triples
  are isomorphic iff their subgroups are conjugate in `Δ(a, b, c)`, identifying conjugacy classes of
  index-`n` subgroups for `n ≠ 0` with `connectedIsoClasses a b c n` and with
  `{C : ConnectedIsoClass n // C.HasDividingOrders a b c}`.
* **Pointed Millington (`TauCeti.TriangleGroup.markedIsoClass_cosetTriple_eq_iff`,
  `TauCeti.TriangleGroup.exists_cosetTriple_eq`, `cosetMarkedIsoClassEquiv`).** Marking the base
  coset `e 1` realizes every pointed connected triple on the nose and identifies index-`n` subgroups
  of `Δ(a, b, c)` for `n ≠ 0` with `markedIsoClasses a b c n`.
* **Monodromy, automorphisms, and fixed-index counts.** The monodromy group of `cosetTriple H e` is
  `Δ(a, b, c) ⧸ H.normalCore`
  (`TauCeti.TriangleGroup.monodromyGroupCosetTripleMulEquivQuotientNormalCore`), its automorphism
  group is `(H.normalizerQuotient)ᵐᵒᵖ`
  (`TauCeti.TriangleGroup.automorphismGroupCosetTripleMulEquiv`), the conjugacy orbit of `H` has
  size `n / #Aut` (`TauCeti.TriangleGroup.natCard_orbit_conjAct_eq_div_automorphismGroup`), and for
  `n ≠ 0` the number of index-`n` subgroups is
  `∑ C ∈ connectedIsoClassesWithDividingOrders n a b c, n / C.automorphismOrder`
  (`TauCeti.TriangleGroup.natCard_ofIndex_eq_sum_div_automorphismOrder`).

## References

* M. H. Millington, *Subgroups of the classical modular group*, J. London Math. Soc. (2) 1 (1969),
  351–357.
* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  LMS Student Texts 79, Cambridge University Press, 2012, §4.
-/

open Equiv
open scoped Pointwise

public section

namespace TauCeti

namespace TriangleGroup

open PermutationTriple

variable {a b c n : ℕ}

/-- Expresses `cosetTriple H e` as `permutationTripleEquiv` applied to `e.permutationRepresentation`
across module boundaries. -/
theorem cosetTriple_eq_permutationTripleEquiv (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    cosetTriple H e =
      (permutationTripleEquiv (e.permutationRepresentation (G := TriangleGroup a b c))).val := by
  rw [← permutationTripleEquiv_toPerm (cosetTriple H e) (cosetTriple_σ0_pow H e)
    (cosetTriple_σ1_pow H e) (cosetTriple_σinf_pow H e), toPerm_cosetTriple]

/-- Reconstructing the coset triple of the stabilizer of `i` under `toPerm t` via
`MonoidHom.quotientComapStabilizerEquiv` recovers `t` itself. -/
@[simp] theorem cosetTriple_quotientComapStabilizerEquiv (t : PermutationTriple n)
    (ha : t.σ0 ^ a = 1) (hb : t.σ1 ^ b = 1) (hc : t.σinf ^ c = 1)
    (hρ : MulAction.IsPretransitive (toPerm t ha hb hc).range (Fin n)) (i : Fin n) :
    cosetTriple ((MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t ha hb hc))
      ((toPerm t ha hb hc).quotientComapStabilizerEquiv hρ i) = t := by
  rw [cosetTriple_eq_permutationTripleEquiv,
    Equiv.permutationRepresentation_eq_of_map_smul _
      ((toPerm t ha hb hc).quotientComapStabilizerEquiv_smul hρ i),
    permutationTripleEquiv_toPerm]

/-- `cosetTriple H e` bundled as a `ConnectedTriple n`. -/
noncomputable def cosetConnectedTriple (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) : ConnectedTriple n :=
  ⟨cosetTriple H e, isConnected_cosetTriple H e⟩

/-- The underlying permutation triple of `cosetConnectedTriple H e` is `cosetTriple H e`. -/
@[simp] theorem coe_cosetConnectedTriple (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    (cosetConnectedTriple H e : PermutationTriple n) = cosetTriple H e := (rfl)

/-- The connected isomorphism class of `cosetConnectedTriple H e` has dividing orders
`(a, b, c)`. -/
theorem hasDividingOrders_cosetConnectedTriple (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    (ConnectedIsoClass.mk (cosetConnectedTriple H e)).HasDividingOrders a b c :=
  (ConnectedIsoClass.hasDividingOrders_mk _).mpr (hasDividingOrders_cosetTriple H e)

/-! ### Mirror compatibility -/

/-- Precomposing a permutation representation of `Δ(a, b, c)` with `TriangleGroup.mirror` mirrors
its permutation triple. -/
@[simp] theorem permutationTripleEquiv_comp_mirror (ρ : TriangleGroup a b c →* Perm (Fin n)) :
    (permutationTripleEquiv
      (ρ.comp ((mirror : TriangleGroup a b c ≃* _) : TriangleGroup a b c →* _))).val =
      (permutationTripleEquiv ρ).val.mirror := by
  ext1 <;> simp

/-- The permutation representation of the mirror of a triple is the representation of the triple
precomposed with `TriangleGroup.mirror`. -/
theorem toPerm_mirror (t : PermutationTriple n) (ha : t.σ0 ^ a = 1) (hb : t.σ1 ^ b = 1)
    (hc : t.σinf ^ c = 1) {ha' hb' hc'} :
    toPerm t.mirror ha' hb' hc' = (toPerm t ha hb hc).comp
      (mirror : TriangleGroup a b c ≃* TriangleGroup a b c).toMonoidHom := by
  ext <;> simp

/-- Transporting a coset numbering along `TriangleGroup.mirror` mirrors the coset triple. -/
theorem cosetTriple_congrOfMapEq_mirror {K H : Subgroup (TriangleGroup a b c)}
    (h : K.map (mirror : TriangleGroup a b c ≃* TriangleGroup a b c).toMonoidHom = H)
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    cosetTriple K ((TauCeti.QuotientGroup.congrOfMapEq mirror h).trans e) =
      (cosetTriple H e).mirror := by
  rw [cosetTriple_eq_permutationTripleEquiv, cosetTriple_eq_permutationTripleEquiv,
    Equiv.permutationRepresentation_congrOfMapEq mirror h e]
  exact permutationTripleEquiv_comp_mirror _

/-- For any coset numberings, the coset triple of the mirror subgroup `H.map mirror` is isomorphic
to the mirror of the coset triple of `H`. -/
theorem equivalent_mirror_cosetTriple (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n)
    (e' : TriangleGroup a b c ⧸
      H.map (mirror : TriangleGroup a b c ≃* TriangleGroup a b c).toMonoidHom ≃ Fin n) :
    (cosetTriple (H.map (mirror : TriangleGroup a b c ≃* TriangleGroup a b c).toMonoidHom)
      e').Equivalent (cosetTriple H e).mirror := by
  let μ : TriangleGroup a b c ≃* TriangleGroup a b c := mirror
  have hmap : (H.map μ.toMonoidHom).map μ.toMonoidHom = H := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id H
    exact MonoidHom.ext mirror_mirror
  rw [← IsoClass.mk_eq_mk_iff,
    IsoClass.mk_eq_mk_iff.mpr
      (equivalent_cosetTriple _ e' ((TauCeti.QuotientGroup.congrOfMapEq μ hmap).trans e)),
    cosetTriple_congrOfMapEq_mirror hmap e]

/-! ### Monodromy and normal core of a coset triple -/

/-- The monodromy group of `cosetTriple H e` is the image of the coset permutation representation.
-/
theorem monodromyGroup_cosetTriple (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    (cosetTriple H e).monodromyGroup =
      (e.permutationRepresentation (G := TriangleGroup a b c)).range := by
  rw [← range_toPerm (cosetTriple H e) (cosetTriple_σ0_pow H e) (cosetTriple_σ1_pow H e)
    (cosetTriple_σinf_pow H e), toPerm_cosetTriple]

/-- By the first isomorphism theorem, the monodromy group of `cosetTriple H e` is canonically
isomorphic to `Δ(a, b, c) ⧸ H.normalCore`. -/
noncomputable def monodromyGroupCosetTripleMulEquivQuotientNormalCore
    (H : Subgroup (TriangleGroup a b c)) (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    (cosetTriple H e).monodromyGroup ≃* TriangleGroup a b c ⧸ H.normalCore :=
  (MulEquiv.subgroupCongr (monodromyGroup_cosetTriple H e)).trans
    e.rangePermutationRepresentationQuotientMulEquiv

/-- The order of the monodromy group of `cosetTriple H e` equals the index of the normal core of
`H` in `Δ(a, b, c)`. -/
theorem natCard_monodromyGroup_cosetTriple (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    Nat.card (cosetTriple H e).monodromyGroup = H.normalCore.index := by
  rw [monodromyGroup_cosetTriple, Equiv.natCard_range_permutationRepresentation_quotient]

/-- `H` is normal in `Δ(a, b, c)` if and only if the monodromy group of `cosetTriple H e` has
order `n`. -/
theorem normal_iff_card_monodromyGroup_cosetTriple (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    H.Normal ↔ Nat.card (cosetTriple H e).monodromyGroup = n := by
  rw [← isRegular_cosetTriple_iff H e, isRegular_iff_card_monodromyGroup,
    and_iff_right (isConnected_cosetTriple H e)]

/-! ### Millington's theorem and pointed Millington for `Δ(a, b, c)` -/

/-- **Millington's theorem for `Δ(a, b, c)` (relational form).** Two coset triples of degree `n`
are isomorphic if and only if the subgroups are conjugate in `Δ(a, b, c)`. -/
theorem cosetTriple_equivalent_cosetTriple_iff {H₁ H₂ : Subgroup (TriangleGroup a b c)}
    (e₁ : TriangleGroup a b c ⧸ H₁ ≃ Fin n) (e₂ : TriangleGroup a b c ⧸ H₂ ≃ Fin n) :
    (cosetTriple H₁ e₁).Equivalent (cosetTriple H₂ e₂) ↔
      ∃ g : ConjAct (TriangleGroup a b c), g • H₁ = H₂ := by
  rw [cosetTriple_eq_permutationTripleEquiv, cosetTriple_eq_permutationTripleEquiv,
    equivalent_permutationTripleEquiv_iff]
  exact e₁.exists_conj_permutationRepresentation_quotient_iff e₂

/-- **Pointed Millington criterion for `Δ(a, b, c)`.** Two coset triples marked at their base
cosets `e₁ 1` and `e₂ 1` define the same marked isomorphism class if and only if their subgroups
are equal. -/
theorem markedIsoClass_cosetTriple_eq_iff {H₁ H₂ : Subgroup (TriangleGroup a b c)}
    (e₁ : TriangleGroup a b c ⧸ H₁ ≃ Fin n) (e₂ : TriangleGroup a b c ⧸ H₂ ≃ Fin n) :
    MarkedIsoClass.mk ⟨cosetTriple H₁ e₁, isConnected_cosetTriple H₁ e₁⟩
        (e₁ ((1 : TriangleGroup a b c) : TriangleGroup a b c ⧸ H₁)) =
      MarkedIsoClass.mk ⟨cosetTriple H₂ e₂, isConnected_cosetTriple H₂ e₂⟩
        (e₂ ((1 : TriangleGroup a b c) : TriangleGroup a b c ⧸ H₂)) ↔
      H₁ = H₂ := by
  rw [MarkedIsoClass.mk_eq_mk_iff_exists_smul, eq_comm,
    ← Equiv.exists_conj_permutationRepresentation_quotient_apply_eq_iff e₂ e₁]
  refine exists_congr fun τ ↦ ?_
  rw [and_comm, Subtype.ext_iff, ConnectedTriple.coe_smul]
  dsimp only
  rw [cosetTriple_eq_permutationTripleEquiv, cosetTriple_eq_permutationTripleEquiv,
    ← permutationTripleEquiv_conj, ← Subtype.ext_iff, permutationTripleEquiv.apply_eq_iff_eq]
  rfl

/-- For a connected permutation triple `t` of degree `n` whose component powers `a`, `b`, `c`
are trivial, the stabilizer of any sheet `i` under `toPerm t` has index `n` in `Δ(a, b, c)`. -/
theorem index_comap_stabilizer_toPerm {t : PermutationTriple n} (ht : t.IsConnected)
    (ha : t.σ0 ^ a = 1) (hb : t.σ1 ^ b = 1) (hc : t.σinf ^ c = 1) (i : Fin n) :
    ((MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t ha hb hc)).index = n := by
  have hρ := ((isConnected_iff_isPretransitive_range_toPerm t ha hb hc).mp ht).2
  exact Subgroup.index_eq_of_equiv _ ((toPerm t ha hb hc).quotientComapStabilizerEquiv hρ i)

/-- **Pointed surjectivity of `cosetTriple`.** Every connected permutation triple `t` of degree `n`
whose component orders divide `a`, `b`, `c` and chosen sheet `i : Fin n` is literally equal to
`cosetTriple H e` for a finite-index subgroup `H` of `Δ(a, b, c)` of index `n` and a coset
numbering `e` sending `1` to `i`. -/
theorem exists_cosetTriple_eq {t : PermutationTriple n} (ht : t.IsConnected)
    (hd : t.HasDividingOrders a b c) (i : Fin n) :
    ∃ (H : Subgroup (TriangleGroup a b c)) (_ : H.FiniteIndex)
      (e : TriangleGroup a b c ⧸ H ≃ Fin n),
      H.index = n ∧ e ((1 : TriangleGroup a b c) : TriangleGroup a b c ⧸ H) = i ∧
        cosetTriple H e = t := by
  obtain ⟨ha, hb, hc⟩ := (hasDividingOrders_iff t).mp hd
  have hρ := ((isConnected_iff_isPretransitive_range_toPerm t ha hb hc).mp ht).2
  let H := (MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t ha hb hc)
  let e : TriangleGroup a b c ⧸ H ≃ Fin n :=
    (toPerm t ha hb hc).quotientComapStabilizerEquiv hρ i
  refine ⟨H, H.finiteIndex_of_equiv e, e, H.index_eq_of_equiv e, ?_,
    cosetTriple_quotientComapStabilizerEquiv t ha hb hc hρ i⟩
  exact ((toPerm t ha hb hc).quotientComapStabilizerEquiv_mk hρ i 1).trans (by simp)

/-- Every connected permutation triple of degree `n` whose component orders divide `a`, `b`, `c`
is isomorphic to the coset triple of a finite-index subgroup of `Δ(a, b, c)` of index `n`. -/
theorem exists_cosetTriple_equivalent {t : PermutationTriple n} (ht : t.IsConnected)
    (hd : t.HasDividingOrders a b c) :
    ∃ (H : Subgroup (TriangleGroup a b c)) (_ : H.FiniteIndex)
      (e : TriangleGroup a b c ⧸ H ≃ Fin n),
      H.index = n ∧ (cosetTriple H e).Equivalent t := by
  obtain ⟨H, hfin, e, hH, -, rfl⟩ :=
    exists_cosetTriple_eq ht hd ⟨0, Nat.pos_of_ne_zero ht.ne_zero⟩
  exact ⟨H, hfin, e, hH, IsoClass.mk_eq_mk_iff.mp rfl⟩

variable (a b c n) in
/-- The isomorphism classes of connected permutation triples of degree `n` whose component orders
divide `a`, `b`, and `c`. -/
def connectedIsoClasses : Set (IsoClass n) :=
  IsoClass.mk '' {t | t.IsConnected ∧ t.HasDividingOrders a b c}

/-- The isomorphism class of `t` lies in `connectedIsoClasses a b c n` if and only if `t` is
connected with component orders dividing `a`, `b`, and `c`. -/
@[simp] theorem mk_mem_connectedIsoClasses_iff {t : PermutationTriple n} :
    IsoClass.mk t ∈ connectedIsoClasses a b c n ↔ t.IsConnected ∧ t.HasDividingOrders a b c := by
  refine ⟨?_, fun h ↦ ⟨t, h, rfl⟩⟩
  rintro ⟨t', ⟨hc, hd⟩, h⟩
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp (IsoClass.mk_eq_mk_iff.mp h)
  exact ⟨(isConnected_smul_iff τ t').mpr hc, by simpa [hasDividingOrders_iff] using hd⟩

/-- `connectedIsoClasses a b c n` is the set of `IsoClass n` elements that are connected and have
dividing orders `(a, b, c)`. -/
theorem connectedIsoClasses_eq :
    connectedIsoClasses a b c n =
      {C : IsoClass n | C.IsConnected ∧ C.HasDividingOrders a b c} := by
  ext C
  obtain ⟨t, rfl⟩ := IsoClass.mk_surjective C
  simp

variable (a b c n) in
/-- The marked isomorphism classes of connected permutation triples of degree `n` whose component
orders divide `a`, `b`, and `c`. -/
def markedIsoClasses : Set (MarkedIsoClass n) :=
  {m | ∃ (t : ConnectedTriple n) (i : Fin n),
    t.val.HasDividingOrders a b c ∧ MarkedIsoClass.mk t i = m}

/-- The marked class of `(t, i)` lies in `markedIsoClasses a b c n` if and only if the component
orders of `t` divide `a`, `b`, and `c`. -/
@[simp] theorem mk_mem_markedIsoClasses_iff {t : ConnectedTriple n} {i : Fin n} :
    MarkedIsoClass.mk t i ∈ markedIsoClasses a b c n ↔ t.val.HasDividingOrders a b c := by
  refine ⟨?_, fun hd ↦ ⟨t, i, hd, rfl⟩⟩
  rintro ⟨t', i', hd, h⟩
  obtain ⟨τ, rfl, -⟩ := MarkedIsoClass.mk_eq_mk_iff_exists_smul.mp h.symm
  simpa [hasDividingOrders_iff] using hd

/-- `markedIsoClasses a b c n` is the set of `MarkedIsoClass n` elements with dividing orders
`(a, b, c)`. -/
theorem markedIsoClasses_eq :
    markedIsoClasses a b c n = {m : MarkedIsoClass n | m.HasDividingOrders a b c} := by
  ext m
  obtain ⟨t, i, rfl⟩ := MarkedIsoClass.mk_surjective m
  simp

private noncomputable def cosetIsoClassAux [NeZero n]
    (q : MulAction.orbitRel.Quotient (ConjAct (TriangleGroup a b c))
      (Subgroup.ofIndex (TriangleGroup a b c) n)) : connectedIsoClasses a b c n :=
  Quotient.liftOn' q
    (fun H ↦ ⟨IsoClass.mk
        (cosetTriple H.val (H.val.quotientEquivFin (Subgroup.mem_ofIndex.mp H.property))),
      mk_mem_connectedIsoClasses_iff.mpr
        ⟨isConnected_cosetTriple _ _, hasDividingOrders_cosetTriple _ _⟩⟩)
    fun H₁ H₂ ⟨g, hg⟩ ↦ by
      have hval : g • H₂.val = H₁.val := congrArg Subtype.val hg
      exact Subtype.ext <| IsoClass.mk_eq_mk_iff.mpr <|
        (cosetTriple_equivalent_cosetTriple_iff _ _).mpr ⟨g⁻¹, by rw [← hval, inv_smul_smul]⟩

private theorem coe_cosetIsoClassAux_mk [NeZero n]
    (H : Subgroup.ofIndex (TriangleGroup a b c) n) :
    (cosetIsoClassAux (Quotient.mk'' H) : IsoClass n) =
      IsoClass.mk (cosetTriple H.val (H.val.quotientEquivFin (Subgroup.mem_ofIndex.mp H.property)))
          := (rfl)

private theorem bijective_cosetIsoClassAux [NeZero n] :
    Function.Bijective (cosetIsoClassAux (a := a) (b := b) (c := c) (n := n)) := by
  refine ⟨fun q₁ q₂ h ↦ ?_, fun C ↦ ?_⟩
  · induction q₁ using Quotient.inductionOn' with | h H₁ =>
    induction q₂ using Quotient.inductionOn' with | h H₂ =>
    have hmk :
        IsoClass.mk (cosetTriple H₁.val (H₁.val.quotientEquivFin
            (Subgroup.mem_ofIndex.mp H₁.property))) =
          IsoClass.mk (cosetTriple H₂.val (H₂.val.quotientEquivFin
              (Subgroup.mem_ofIndex.mp H₂.property))) :=
      congrArg Subtype.val h
    obtain ⟨g, hg⟩ := (cosetTriple_equivalent_cosetTriple_iff _ _).mp (IsoClass.mk_eq_mk_iff.mp hmk)
    exact Quotient.eq''.mpr ⟨g⁻¹, Subtype.ext (by
      rw [SubMulAction.val_smul_of_tower, ← hg, inv_smul_smul])⟩
  · obtain ⟨t, ⟨ht, hd⟩, hC⟩ := C.property
    obtain ⟨H, _, e, hH, heq⟩ := exists_cosetTriple_equivalent ht hd
    refine ⟨Quotient.mk'' ⟨H, Subgroup.mem_ofIndex.mpr hH⟩, Subtype.ext ?_⟩
    rw [coe_cosetIsoClassAux_mk, ← hC,
      IsoClass.mk_eq_mk_iff.mpr (equivalent_cosetTriple H _ e), IsoClass.mk_eq_mk_iff.mpr heq]

/-- **Millington's theorem for `Δ(a, b, c)` (bundled bijection).** For `n ≠ 0`, conjugacy classes
of index-`n` subgroups of `Δ(a, b, c)` are in bijection with isomorphism classes of connected
degree-`n` permutation triples whose component orders divide `a`, `b`, and `c`. -/
noncomputable def cosetIsoClassEquiv [NeZero n] :
    MulAction.orbitRel.Quotient (ConjAct (TriangleGroup a b c))
      (Subgroup.ofIndex (TriangleGroup a b c) n) ≃ connectedIsoClasses a b c n :=
  Equiv.ofBijective _ bijective_cosetIsoClassAux

/-- `cosetIsoClassEquiv` sends the conjugacy class of `H` to the isomorphism class of
`cosetTriple H e`, for any numbering `e` of the cosets of `H`. -/
theorem coe_cosetIsoClassEquiv_mk [NeZero n] (H : Subgroup.ofIndex (TriangleGroup a b c) n)
    (e : TriangleGroup a b c ⧸ H.val ≃ Fin n) :
    (cosetIsoClassEquiv (Quotient.mk'' H) : IsoClass n) = IsoClass.mk (cosetTriple H.val e) := by
  rw [cosetIsoClassEquiv, Equiv.ofBijective_apply, coe_cosetIsoClassAux_mk, IsoClass.mk_eq_mk_iff]
  exact equivalent_cosetTriple H.val _ e

/-- **Millington's theorem on `ConnectedIsoClass`.** For `n ≠ 0`, conjugacy classes of index-`n`
subgroups of `Δ(a, b, c)` biject with `{C : ConnectedIsoClass n // C.HasDividingOrders a b c}`. -/
noncomputable def cosetConnectedIsoClassEquiv [NeZero n] :
    MulAction.orbitRel.Quotient (ConjAct (TriangleGroup a b c))
      (Subgroup.ofIndex (TriangleGroup a b c) n) ≃
      {C : ConnectedIsoClass n // C.HasDividingOrders a b c} :=
  cosetIsoClassEquiv.trans <| (Set.equivOfEq connectedIsoClasses_eq).trans
    (ConnectedIsoClass.equivIsoClassSubtypeDividingOrders n a b c).symm

/-- `cosetConnectedIsoClassEquiv` sends the conjugacy class of `H` to
`ConnectedIsoClass.mk (cosetConnectedTriple H.1 e)`, for any coset numbering `e`. -/
theorem coe_cosetConnectedIsoClassEquiv_mk [NeZero n]
    (H : Subgroup.ofIndex (TriangleGroup a b c) n) (e : TriangleGroup a b c ⧸ H.val ≃ Fin n) :
    (cosetConnectedIsoClassEquiv (Quotient.mk'' H) : ConnectedIsoClass n) =
      ConnectedIsoClass.mk (cosetConnectedTriple H.val e) := by
  apply ConnectedIsoClass.forget_injective
  have key := (ConnectedIsoClass.equivIsoClassSubtypeDividingOrders n a b c).apply_symm_apply
    (Set.equivOfEq connectedIsoClasses_eq (cosetIsoClassEquiv (Quotient.mk'' H)))
  exact (ConnectedIsoClass.coe_equivIsoClassSubtypeDividingOrders_apply _).symm.trans <|
    (congrArg Subtype.val key).trans <| (coe_cosetIsoClassEquiv_mk H e).trans
      (ConnectedIsoClass.forget_mk (cosetConnectedTriple H.val e)).symm

private noncomputable def cosetMarkedIsoClassAux [NeZero n]
    (H : Subgroup.ofIndex (TriangleGroup a b c) n) : markedIsoClasses a b c n :=
  let e := H.val.quotientEquivFin (Subgroup.mem_ofIndex.mp H.property)
  ⟨MarkedIsoClass.mk ⟨cosetTriple H.val e, isConnected_cosetTriple H.val e⟩
      (e ((1 : TriangleGroup a b c) : TriangleGroup a b c ⧸ H.val)),
    mk_mem_markedIsoClasses_iff.mpr (hasDividingOrders_cosetTriple H.val e)⟩

private theorem coe_cosetMarkedIsoClassAux [NeZero n]
    (H : Subgroup.ofIndex (TriangleGroup a b c) n) (e : TriangleGroup a b c ⧸ H.val ≃ Fin n) :
    (cosetMarkedIsoClassAux H : MarkedIsoClass n) =
      MarkedIsoClass.mk ⟨cosetTriple H.val e, isConnected_cosetTriple H.val e⟩
        (e ((1 : TriangleGroup a b c) : TriangleGroup a b c ⧸ H.val)) :=
  (markedIsoClass_cosetTriple_eq_iff _ e).mpr rfl

private theorem coe_cosetMarkedIsoClassAux_comap_stabilizer [NeZero n] (t : ConnectedTriple n)
    (i : Fin n) (ha : t.val.σ0 ^ a = 1) (hb : t.val.σ1 ^ b = 1) (hc : t.val.σinf ^ c = 1) :
    let hρ := ((isConnected_iff_isPretransitive_range_toPerm t.val ha hb hc).mp t.property).2
    let H := (MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t.val ha hb hc)
    let e := (toPerm t.val ha hb hc).quotientComapStabilizerEquiv hρ i
    (cosetMarkedIsoClassAux ⟨H, Subgroup.mem_ofIndex.mpr (H.index_eq_of_equiv e)⟩ :
      MarkedIsoClass n) = MarkedIsoClass.mk t i := by
  intro hρ H e
  rw [coe_cosetMarkedIsoClassAux ⟨H, Subgroup.mem_ofIndex.mpr (H.index_eq_of_equiv e)⟩ e]
  have hct : (⟨cosetTriple H e, isConnected_cosetTriple H e⟩ : ConnectedTriple n) = t :=
    Subtype.ext (cosetTriple_quotientComapStabilizerEquiv t.val ha hb hc hρ i)
  have hi : e ((1 : TriangleGroup a b c) : TriangleGroup a b c ⧸ H) = i :=
    ((toPerm t.val ha hb hc).quotientComapStabilizerEquiv_mk hρ i 1).trans (by simp)
  rw [hct, hi]

private theorem bijective_cosetMarkedIsoClassAux [NeZero n] :
    Function.Bijective (cosetMarkedIsoClassAux (a := a) (b := b) (c := c) (n := n)) := by
  refine ⟨fun H₁ H₂ h ↦ Subtype.ext ((markedIsoClass_cosetTriple_eq_iff _ _).mp
    (congrArg Subtype.val h)), fun M ↦ ?_⟩
  obtain ⟨t, i, hd, hM⟩ := M.property
  obtain ⟨ha, hb, hc⟩ := (hasDividingOrders_iff t.val).mp hd
  exact ⟨_, Subtype.ext ((coe_cosetMarkedIsoClassAux_comap_stabilizer t i ha hb hc).trans hM)⟩

/-- **Pointed Millington bijection for `Δ(a, b, c)`.** For `n ≠ 0`, subgroups of `Δ(a, b, c)` of
index `n` are in bijection with marked isomorphism classes of connected triples of degree `n` whose
component orders divide `a`, `b`, and `c`. -/
noncomputable def cosetMarkedIsoClassEquiv [NeZero n] :
    Subgroup.ofIndex (TriangleGroup a b c) n ≃ markedIsoClasses a b c n :=
  Equiv.ofBijective _ bijective_cosetMarkedIsoClassAux

/-- `cosetMarkedIsoClassEquiv` sends `H` to the class of `cosetTriple H e` marked at the base
coset `e 1`, independently of `e`. -/
theorem coe_cosetMarkedIsoClassEquiv_apply [NeZero n]
    (H : Subgroup.ofIndex (TriangleGroup a b c) n) (e : TriangleGroup a b c ⧸ H.val ≃ Fin n) :
    (cosetMarkedIsoClassEquiv H : MarkedIsoClass n) =
      MarkedIsoClass.mk ⟨cosetTriple H.val e, isConnected_cosetTriple H.val e⟩
        (e ((1 : TriangleGroup a b c) : TriangleGroup a b c ⧸ H.val)) :=
  coe_cosetMarkedIsoClassAux H e

/-- The inverse of `cosetMarkedIsoClassEquiv` sends the marked class of `(t, i)` to the stabilizer
of the marked sheet `i` under `toPerm t`. -/
@[simp] theorem coe_cosetMarkedIsoClassEquiv_symm_mk [NeZero n] (t : ConnectedTriple n) (i : Fin n)
    (ha : t.val.σ0 ^ a = 1) (hb : t.val.σ1 ^ b = 1) (hc : t.val.σinf ^ c = 1) :
    (cosetMarkedIsoClassEquiv.symm
      ⟨MarkedIsoClass.mk t i,
        mk_mem_markedIsoClasses_iff.mpr ((hasDividingOrders_iff t.val).mpr ⟨ha, hb, hc⟩)⟩ :
        Subgroup (TriangleGroup a b c)) =
      (MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t.val ha hb hc) := by
  have key := cosetMarkedIsoClassEquiv.injective <|
    (cosetMarkedIsoClassEquiv.apply_symm_apply
      ⟨MarkedIsoClass.mk t i,
        mk_mem_markedIsoClasses_iff.mpr ((hasDividingOrders_iff t.val).mpr ⟨ha, hb, hc⟩)⟩).trans
      (Subtype.ext (coe_cosetMarkedIsoClassAux_comap_stabilizer t i ha hb hc).symm)
  exact congrArg Subtype.val key

/-! ### Automorphism group, conjugate count, and finiteness at fixed index -/

/-- The automorphism group of `cosetTriple H e` is canonically isomorphic to
`(H.normalizerQuotient)ᵐᵒᵖ`, generalizing `automorphismGroupMulEquivQuotientKer` from normal to
arbitrary subgroups. -/
noncomputable def automorphismGroupCosetTripleMulEquiv (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    (cosetTriple H e).automorphismGroup ≃* (H.normalizerQuotient)ᵐᵒᵖ :=
  (MulEquiv.subgroupCongr <| by
    rw [automorphismGroup_eq_centralizer_monodromyGroup, monodromyGroup_cosetTriple,
      MonoidHom.coe_range]).trans
    e.centralizerPermutationRepresentationQuotientMulEquiv

/-- The order of the automorphism group of `cosetTriple H e` is the relative index
`[N_{Δ(a,b,c)}(H) : H]`. -/
theorem natCard_automorphismGroup_cosetTriple (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    Nat.card (cosetTriple H e).automorphismGroup =
      H.relIndex (Subgroup.normalizer (H : Set (TriangleGroup a b c))) := by
  rw [Nat.card_congr (automorphismGroupCosetTripleMulEquiv H e).toEquiv,
    ← e.natCard_centralizer_permutationRepresentation_quotient,
    Nat.card_congr e.centralizerPermutationRepresentationQuotientMulEquiv.toEquiv]

/-- The subgroups `K` of `Δ(a, b, c)` admitting a degree-`n` coset triple isomorphic to
`cosetTriple H e` are precisely the conjugates of `H` in `Δ(a, b, c)`. -/
theorem setOf_exists_cosetTriple_equivalent_eq_orbit (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    {K : Subgroup (TriangleGroup a b c) |
      ∃ e' : TriangleGroup a b c ⧸ K ≃ Fin n, (cosetTriple K e').Equivalent (cosetTriple H e)} =
      MulAction.orbit (ConjAct (TriangleGroup a b c)) H := by
  ext K
  rw [Set.mem_ofPred, MulAction.mem_orbit_iff]
  refine ⟨fun ⟨e', heq⟩ ↦ ?_, fun ⟨g, hg⟩ ↦ ?_⟩
  · obtain ⟨g, hg⟩ := (cosetTriple_equivalent_cosetTriple_iff e' e).mp heq
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  · obtain ⟨c, rfl⟩ := ConjAct.toConjAct.surjective g
    exact ⟨(Subgroup.quotientEquivOfConjAct hg).symm.trans e,
      (cosetTriple_equivalent_cosetTriple_iff _ e).mpr ⟨(ConjAct.toConjAct c)⁻¹,
        by rw [← hg, inv_smul_smul]⟩⟩

/-- **Subgroup count in an isomorphism class.** The number of subgroups of `Δ(a, b, c)` realizing
the isomorphism class of `cosetTriple H e` times the order of `(cosetTriple H e).automorphismGroup`
equals the degree `n`. -/
theorem ncard_subgroups_of_cosetTriple_class_mul_card_automorphismGroup
    (H : Subgroup (TriangleGroup a b c)) (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    {K : Subgroup (TriangleGroup a b c) |
      ∃ e' : TriangleGroup a b c ⧸ K ≃ Fin n,
        (cosetTriple K e').Equivalent (cosetTriple H e)}.ncard *
      Nat.card (cosetTriple H e).automorphismGroup = n := by
  rw [setOf_exists_cosetTriple_equivalent_eq_orbit H e, natCard_automorphismGroup_cosetTriple H e,
    H.ncard_orbit_mul_relIndex_normalizer, H.index_eq_of_equiv e]

/-- The number of conjugates of `H` in `Δ(a, b, c)` equals `n` divided by the order of
`(cosetTriple H e).automorphismGroup`. -/
theorem natCard_orbit_conjAct_eq_div_automorphismGroup
    (H : Subgroup (TriangleGroup a b c)) (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    Nat.card (MulAction.orbit (ConjAct (TriangleGroup a b c)) H) =
      n / Nat.card (cosetTriple H e).automorphismGroup := by
  rw [(cosetTriple H e).automorphismGroup_eq_centralizer_monodromyGroup,
    monodromyGroup_cosetTriple, MonoidHom.coe_range,
    e.natCard_orbit_conjAct_eq_index_div_natCard_centralizer, H.index_eq_of_equiv e]

/-- **Finiteness at fixed index for `Δ(a, b, c)`.** For every `n ≠ 0`, `Δ(a, b, c)` has only
finitely many subgroups of index `n`. -/
instance finite_ofIndex (a b c n : ℕ) [NeZero n] :
    Finite (Subgroup.ofIndex (TriangleGroup a b c) n) :=
  Finite.of_equiv (markedIsoClasses a b c n) cosetMarkedIsoClassEquiv.symm

/-- Unbundled form of `finite_ofIndex`: `{H : Subgroup (TriangleGroup a b c) // H.index = n}` is
finite for `n ≠ 0`. -/
instance finite_subgroups_of_index (a b c n : ℕ) [NeZero n] :
    Finite {H : Subgroup (TriangleGroup a b c) // H.index = n} :=
  Finite.of_equiv (Subgroup.ofIndex (TriangleGroup a b c) n)
    (Equiv.subtypeEquivRight fun _ ↦ Subgroup.mem_ofIndex)

/-- For every `n ≠ 0`, `Δ(a, b, c)` has only finitely many conjugacy classes of subgroups of
index `n`. -/
theorem finite_orbitRel_quotient_ofIndex (a b c n : ℕ) [NeZero n] :
    Finite (MulAction.orbitRel.Quotient (ConjAct (TriangleGroup a b c))
      (Subgroup.ofIndex (TriangleGroup a b c) n)) :=
  Quotient.finite _

/-- The number of subgroups in an index-`n` conjugacy class `ω` of `Δ(a, b, c)` is `n` divided by
the automorphism order of the corresponding connected triple class. -/
theorem natCard_orbit_ofIndex_eq_div_automorphismOrder [NeZero n]
    (ω : MulAction.orbitRel.Quotient (ConjAct (TriangleGroup a b c))
      (Subgroup.ofIndex (TriangleGroup a b c) n)) :
    Nat.card (MulAction.orbitRel.Quotient.orbit ω) =
      n / (cosetConnectedIsoClassEquiv ω).val.automorphismOrder :=
  Quotient.inductionOn' ω fun H ↦ by
    let e := H.val.quotientEquivFin (Subgroup.mem_ofIndex.mp H.property)
    rw [MulAction.orbitRel.Quotient.orbit_mk, Nat.card_congr (Subgroup.orbitOfIndexEquiv H),
      natCard_orbit_conjAct_eq_div_automorphismGroup H.val e,
      coe_cosetConnectedIsoClassEquiv_mk H e, ConnectedIsoClass.automorphismOrder_mk,
      coe_cosetConnectedTriple]

/-- For `n ≠ 0`, the number of conjugacy classes of index-`n` subgroups of `Δ(a, b, c)` equals the
cardinality of `connectedIsoClassesWithDividingOrders n a b c`. -/
theorem natCard_orbitRel_quotient_ofIndex_eq_card_connectedIsoClassesWithDividingOrders
    (a b c n : ℕ) [NeZero n] :
    Nat.card (MulAction.orbitRel.Quotient (ConjAct (TriangleGroup a b c))
      (Subgroup.ofIndex (TriangleGroup a b c) n)) =
      (connectedIsoClassesWithDividingOrders n a b c).card := by
  rw [card_connectedIsoClassesWithDividingOrders]
  exact Nat.card_congr cosetConnectedIsoClassEquiv

/-- **Index-`n` subgroup count for `Δ(a, b, c)`.** For `n ≠ 0`, the number of index-`n` subgroups
of `Δ(a, b, c)` is the sum of `n / C.automorphismOrder` over all connected isomorphism classes `C`
of degree `n` with dividing orders `(a, b, c)`. -/
theorem natCard_ofIndex_eq_sum_div_automorphismOrder (a b c n : ℕ) [NeZero n] :
    Nat.card (Subgroup.ofIndex (TriangleGroup a b c) n) =
      ∑ C ∈ connectedIsoClassesWithDividingOrders n a b c, n / C.automorphismOrder := by
  classical
  let _ : Fintype (MulAction.orbitRel.Quotient (ConjAct (TriangleGroup a b c))
      (Subgroup.ofIndex (TriangleGroup a b c) n)) := Fintype.ofFinite _
  rw [(Nat.card_congr (MulAction.selfEquivSigmaOrbits' (ConjAct (TriangleGroup a b c))
    (Subgroup.ofIndex (TriangleGroup a b c) n))).trans Nat.card_sigma]
  simp_rw [natCard_orbit_ofIndex_eq_div_automorphismOrder]
  rw [Fintype.sum_equiv cosetConnectedIsoClassEquiv _
    (fun C : {C : ConnectedIsoClass n // C.HasDividingOrders a b c} ↦ n / C.val.automorphismOrder)
    fun _ ↦ rfl]
  exact (Finset.sum_subtype (connectedIsoClassesWithDividingOrders n a b c)
    (fun _ ↦ mem_connectedIsoClassesWithDividingOrders)
    (fun C ↦ n / C.automorphismOrder)).symm

/-- Unbundled form of `natCard_ofIndex_eq_sum_div_automorphismOrder` on
`{H : Subgroup (TriangleGroup a b c) // H.index = n}`. -/
theorem natCard_subgroups_of_index_eq_sum_div_automorphismOrder (a b c n : ℕ) [NeZero n] :
    Nat.card {H : Subgroup (TriangleGroup a b c) // H.index = n} =
      ∑ C ∈ connectedIsoClassesWithDividingOrders n a b c, n / C.automorphismOrder :=
  (Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ Subgroup.mem_ofIndex.symm)).trans
    (natCard_ofIndex_eq_sum_div_automorphismOrder a b c n)

end TriangleGroup

end TauCeti

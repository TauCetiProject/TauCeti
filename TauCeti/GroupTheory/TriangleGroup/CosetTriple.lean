/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Conjugates
public import TauCeti.Algebra.GroupAction.CosetRepresentation
public import TauCeti.Combinatorics.PermutationTriple.IsoClass
public import TauCeti.Combinatorics.PermutationTriple.Mirror
public import TauCeti.GroupTheory.TriangleGroup.Regular

/-!
# Millington's dictionary and finiteness at fixed index for triangle groups

Every subgroup `H` of `Δ(a, b, c)` of finite index `n ≠ 0`, together with a numbering
`e : Δ(a, b, c) ⧸ H ≃ Fin n` of its left cosets, determines a connected permutation triple
`TauCeti.TriangleGroup.cosetTriple H e` of degree `n` whose component orders divide `a`, `b`, `c`.
Combining `TauCeti.TriangleGroup.permutationTripleEquiv` with the coset-representation theorems of
`TauCeti.Algebra.GroupAction.CosetRepresentation`, this file establishes the full coset dictionary
for arbitrary triangle groups `Δ(a, b, c)`:

* **Millington's theorem (`TauCeti.TriangleGroup.cosetTriple_equivalent_cosetTriple_iff`,
  `TauCeti.TriangleGroup.cosetIsoClassEquiv`).** Two coset triples of degree `n` are isomorphic if
  and only if their subgroups are conjugate in `Δ(a, b, c)`, giving for `n ≠ 0` a bijection between
  conjugacy classes of index-`n` subgroups of `Δ(a, b, c)` and isomorphism classes of connected
  degree-`n` triples with component orders dividing `(a, b, c)`.
* **Pointed Millington (`TauCeti.TriangleGroup.markedIsoClass_cosetTriple_eq_iff`,
  `TauCeti.TriangleGroup.cosetMarkedIsoClassEquiv`).** Marking the base coset `e 1` removes the
  conjugacy ambiguity: for `n ≠ 0`, subgroups of `Δ(a, b, c)` of index `n` are in bijection with
  marked isomorphism classes of connected triples of degree `n` whose component orders divide
  `a`, `b`, `c`.
* **Monodromy, automorphisms, and conjugate count.** The monodromy group of `cosetTriple H e` is
  canonically isomorphic to `Δ(a, b, c) ⧸ H.normalCore` via the first isomorphism theorem
  (`TauCeti.TriangleGroup.monodromyGroupCosetTripleMulEquivQuotientNormalCore`), its automorphism
  group is isomorphic to `(H.normalizerQuotient)ᵐᵒᵖ`
  (`TauCeti.TriangleGroup.automorphismGroupCosetTripleMulEquiv`), and the number of subgroups
  realizing the isomorphism class of `cosetTriple H e` times the order of its automorphism group
  equals `n`
  (`TauCeti.TriangleGroup.ncard_subgroups_of_cosetTriple_class_mul_card_automorphismGroup`).
* **Finiteness at fixed index (`TauCeti.TriangleGroup.finite_subgroups_of_index`,
  `TauCeti.TriangleGroup.finite_orbitRel_quotient_ofIndex`).** Because `MarkedIsoClass n` is finite,
  `Δ(a, b, c)` has only finitely many subgroups of any nonzero finite index `n`.

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
      (permutationTripleEquiv (e.permutationRepresentation (G := TriangleGroup a b c))).1 := by
  rw [← permutationTripleEquiv_toPerm (cosetTriple H e) (cosetTriple_σ0_pow H e)
    (cosetTriple_σ1_pow H e) (cosetTriple_σinf_pow H e), toPerm_cosetTriple]

/-! ### Mirror compatibility -/

/-- Precomposing a permutation representation of `Δ(a, b, c)` with `TriangleGroup.mirror` mirrors
its permutation triple. -/
@[simp]
theorem permutationTripleEquiv_comp_mirror (ρ : TriangleGroup a b c →* Perm (Fin n)) :
    (permutationTripleEquiv
      (ρ.comp (mirror (a := a) (b := b) (c := c) :
        TriangleGroup a b c →* TriangleGroup a b c))).1 =
      (permutationTripleEquiv ρ).1.mirror := by
  ext1 <;> simp

/-- The permutation representation of the mirror of a triple is the representation of the triple
precomposed with `TriangleGroup.mirror`. -/
theorem toPerm_mirror (t : PermutationTriple n) (ha : t.σ0 ^ a = 1) (hb : t.σ1 ^ b = 1)
    (hc : t.σinf ^ c = 1) {ha' hb' hc'} :
    toPerm t.mirror ha' hb' hc' =
      (toPerm t ha hb hc).comp
        (mirror (a := a) (b := b) (c := c) : TriangleGroup a b c →* TriangleGroup a b c) := by
  ext <;> simp

/-- Transporting a coset numbering along `TriangleGroup.mirror` mirrors the coset triple. -/
theorem cosetTriple_congrOfMapEq_mirror {K H : Subgroup (TriangleGroup a b c)}
    (h : K.map ((mirror (a := a) (b := b) (c := c)) :
      TriangleGroup a b c →* TriangleGroup a b c) = H)
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) :
    cosetTriple K
        ((TauCeti.QuotientGroup.congrOfMapEq (mirror (a := a) (b := b) (c := c)) h).trans e) =
      (cosetTriple H e).mirror := by
  rw [cosetTriple_eq_permutationTripleEquiv, cosetTriple_eq_permutationTripleEquiv,
    Equiv.permutationRepresentation_congrOfMapEq (mirror (a := a) (b := b) (c := c)) h e]
  exact permutationTripleEquiv_comp_mirror _

/-- For any coset numberings, the coset triple of the mirror subgroup `H.map mirror` is isomorphic
to the mirror of the coset triple of `H`. -/
theorem equivalent_mirror_cosetTriple (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n)
    (e' : TriangleGroup a b c ⧸
      H.map ((mirror (a := a) (b := b) (c := c)) :
        TriangleGroup a b c →* TriangleGroup a b c) ≃ Fin n) :
    (cosetTriple
      (H.map ((mirror (a := a) (b := b) (c := c)) :
        TriangleGroup a b c →* TriangleGroup a b c)) e').Equivalent
      (cosetTriple H e).mirror := by
  let μ : TriangleGroup a b c ≃* TriangleGroup a b c := mirror
  have hmap : (H.map (μ : TriangleGroup a b c →* TriangleGroup a b c)).map
      (μ : TriangleGroup a b c →* TriangleGroup a b c) = H := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id H
    exact MonoidHom.ext mirror_mirror
  rw [← IsoClass.mk_eq_mk_iff,
    IsoClass.mk_eq_mk_iff.mpr
      (equivalent_cosetTriple _ e' ((TauCeti.QuotientGroup.congrOfMapEq μ hmap).trans e)),
    cosetTriple_congrOfMapEq_mirror hmap e]

/-! ### Index, monodromy, and normal core of a coset triple -/

/-- A coset numbering `Δ(a, b, c) ⧸ H ≃ Fin n` witnesses that `H` has index `n`. -/
theorem index_eq_of_equiv (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) : H.index = n := by
  rw [Subgroup.index_eq_card, Nat.card_congr e, Nat.card_fin]

/-- A coset space `Δ(a, b, c) ⧸ H` is nonempty, so any `Fin n` numbering forces `n ≠ 0`. -/
theorem ne_zero_of_equiv (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) : n ≠ 0 :=
  (isConnected_cosetTriple H e).ne_zero

/-- A subgroup whose coset space is numbered by `Fin n` has finite index. -/
theorem finiteIndex_of_equiv (H : Subgroup (TriangleGroup a b c))
    (e : TriangleGroup a b c ⧸ H ≃ Fin n) : H.FiniteIndex :=
  ⟨by rw [index_eq_of_equiv H e]; exact ne_zero_of_equiv H e⟩

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
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (monodromyGroupCosetTripleMulEquivQuotientNormalCore H e).toEquiv

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

/-- Every connected permutation triple of degree `n` whose component orders divide `a`, `b`, `c`
is isomorphic to the coset triple of a finite-index subgroup of `Δ(a, b, c)` of index `n`. -/
theorem exists_cosetTriple_equivalent {t : PermutationTriple n} (ht : t.IsConnected)
    (hd : t.HasDividingOrders a b c) :
    ∃ (H : Subgroup (TriangleGroup a b c)) (_ : H.FiniteIndex)
      (e : TriangleGroup a b c ⧸ H ≃ Fin n),
      H.index = n ∧ (cosetTriple H e).Equivalent t := by
  obtain ⟨ha, hb, hc⟩ := (hasDividingOrders_iff t).mp hd
  have hρ := (isConnected_iff_isPretransitive_range_toPerm t ha hb hc).mp ht |>.2
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero ht.ne_zero⟩
  let H := (MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t ha hb hc)
  let e : TriangleGroup a b c ⧸ H ≃ Fin n := (toPerm t ha hb hc).quotientComapStabilizerEquiv hρ i
  exact ⟨H, finiteIndex_of_equiv H e, e, index_eq_of_equiv H e,
    equivalent_cosetTriple_of_comap_stabilizer_eq H e ht ha hb hc i rfl⟩

variable (a b c n) in
/-- The isomorphism classes of connected permutation triples of degree `n` whose component orders
divide `a`, `b`, and `c`. -/
def connectedIsoClasses : Set (IsoClass n) :=
  IsoClass.mk '' {t | t.IsConnected ∧ t.HasDividingOrders a b c}

/-- The isomorphism class of `t` lies in `connectedIsoClasses a b c n` if and only if `t` is
connected with component orders dividing `a`, `b`, and `c`. -/
@[simp]
theorem mk_mem_connectedIsoClasses_iff {t : PermutationTriple n} :
    IsoClass.mk t ∈ connectedIsoClasses a b c n ↔ t.IsConnected ∧ t.HasDividingOrders a b c := by
  refine ⟨?_, fun h ↦ ⟨t, h, rfl⟩⟩
  rintro ⟨t', ⟨hc, hd⟩, h⟩
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp (IsoClass.mk_eq_mk_iff.mp h)
  exact ⟨(isConnected_smul_iff τ t').mpr hc, by simpa [hasDividingOrders_iff] using hd⟩

variable (a b c n) in
/-- The marked isomorphism classes of connected permutation triples of degree `n` whose component
orders divide `a`, `b`, and `c`. -/
def markedIsoClasses : Set (MarkedIsoClass n) :=
  {m | ∃ (t : ConnectedTriple n) (i : Fin n),
    t.1.HasDividingOrders a b c ∧ MarkedIsoClass.mk t i = m}

/-- The marked class of `(t, i)` lies in `markedIsoClasses a b c n` if and only if the component
orders of `t` divide `a`, `b`, and `c`. -/
@[simp]
theorem mk_mem_markedIsoClasses_iff {t : ConnectedTriple n} {i : Fin n} :
    MarkedIsoClass.mk t i ∈ markedIsoClasses a b c n ↔ t.1.HasDividingOrders a b c := by
  refine ⟨?_, fun hd ↦ ⟨t, i, hd, rfl⟩⟩
  rintro ⟨t', i', hd, h⟩
  obtain ⟨τ, rfl, -⟩ := MarkedIsoClass.mk_eq_mk_iff_exists_smul.mp h.symm
  simpa [hasDividingOrders_iff] using hd

/-- A numbering of the cosets of a subgroup of index `n ≠ 0`. -/
private noncomputable def cosetEquivFinOfIndex [NeZero n]
    (H : Subgroup.ofIndex (TriangleGroup a b c) n) : TriangleGroup a b c ⧸ H.1 ≃ Fin n :=
  have hH : Nat.card (TriangleGroup a b c ⧸ H.1) = n :=
    (Subgroup.index_eq_card H.1).symm.trans (Subgroup.mem_ofIndex.mp H.2)
  have : Finite (TriangleGroup a b c ⧸ H.1) :=
    Nat.finite_of_card_ne_zero (by rw [hH]; exact NeZero.ne n)
  Finite.equivFinOfCardEq hH

private noncomputable def cosetIsoClassAux [NeZero n]
    (q : MulAction.orbitRel.Quotient (ConjAct (TriangleGroup a b c))
      (Subgroup.ofIndex (TriangleGroup a b c) n)) : connectedIsoClasses a b c n :=
  Quotient.liftOn' q
    (fun H ↦ ⟨IsoClass.mk (cosetTriple H.1 (cosetEquivFinOfIndex H)),
      mk_mem_connectedIsoClasses_iff.mpr
        ⟨isConnected_cosetTriple _ _, hasDividingOrders_cosetTriple _ _⟩⟩)
    fun H₁ H₂ hrel ↦ by
      obtain ⟨g, hg⟩ := hrel
      refine Subtype.ext (IsoClass.mk_eq_mk_iff.mpr ?_)
      refine (cosetTriple_equivalent_cosetTriple_iff _ _).mpr ⟨g⁻¹, ?_⟩
      have hval : g • H₂.1 = H₁.1 := congrArg Subtype.val hg
      rw [← hval, inv_smul_smul]

private theorem coe_cosetIsoClassAux_mk [NeZero n]
    (H : Subgroup.ofIndex (TriangleGroup a b c) n) :
    (cosetIsoClassAux (Quotient.mk'' H) : IsoClass n) =
      IsoClass.mk (cosetTriple H.1 (cosetEquivFinOfIndex H)) := (rfl)

private theorem bijective_cosetIsoClassAux [NeZero n] :
    Function.Bijective (cosetIsoClassAux (a := a) (b := b) (c := c) (n := n)) := by
  refine ⟨fun q₁ q₂ h ↦ ?_, fun C ↦ ?_⟩
  · induction q₁ using Quotient.inductionOn' with | h H₁ =>
    induction q₂ using Quotient.inductionOn' with | h H₂ =>
    have hmk : IsoClass.mk (cosetTriple H₁.1 (cosetEquivFinOfIndex H₁)) =
        IsoClass.mk (cosetTriple H₂.1 (cosetEquivFinOfIndex H₂)) :=
      congrArg Subtype.val h
    obtain ⟨g, hg⟩ := (cosetTriple_equivalent_cosetTriple_iff _ _).mp
      (IsoClass.mk_eq_mk_iff.mp hmk)
    exact Quotient.eq''.mpr ⟨g⁻¹, Subtype.ext (by
      rw [SubMulAction.val_smul_of_tower, ← hg, inv_smul_smul])⟩
  · obtain ⟨t, ⟨ht, hd⟩, hC⟩ := C.2
    obtain ⟨H, _, e, hH, heq⟩ := exists_cosetTriple_equivalent ht hd
    let H' : Subgroup.ofIndex (TriangleGroup a b c) n := ⟨H, Subgroup.mem_ofIndex.mpr hH⟩
    refine ⟨Quotient.mk'' H', Subtype.ext ?_⟩
    rw [coe_cosetIsoClassAux_mk, ← hC,
      IsoClass.mk_eq_mk_iff.mpr (equivalent_cosetTriple H _ e),
      IsoClass.mk_eq_mk_iff.mpr heq]

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
    (e : TriangleGroup a b c ⧸ H.1 ≃ Fin n) :
    (cosetIsoClassEquiv (Quotient.mk'' H) : IsoClass n) = IsoClass.mk (cosetTriple H.1 e) := by
  rw [cosetIsoClassEquiv, Equiv.ofBijective_apply, coe_cosetIsoClassAux_mk,
    IsoClass.mk_eq_mk_iff]
  exact equivalent_cosetTriple H.1 _ e

private noncomputable def cosetMarkedIsoClassAux [NeZero n]
    (H : Subgroup.ofIndex (TriangleGroup a b c) n) : markedIsoClasses a b c n :=
  let e := cosetEquivFinOfIndex H
  ⟨MarkedIsoClass.mk ⟨cosetTriple H.1 e, isConnected_cosetTriple H.1 e⟩
      (e ((1 : TriangleGroup a b c) : TriangleGroup a b c ⧸ H.1)),
    mk_mem_markedIsoClasses_iff.mpr (hasDividingOrders_cosetTriple H.1 e)⟩

private theorem coe_cosetMarkedIsoClassAux [NeZero n]
    (H : Subgroup.ofIndex (TriangleGroup a b c) n) (e : TriangleGroup a b c ⧸ H.1 ≃ Fin n) :
    (cosetMarkedIsoClassAux H : MarkedIsoClass n) =
      MarkedIsoClass.mk ⟨cosetTriple H.1 e, isConnected_cosetTriple H.1 e⟩
        (e ((1 : TriangleGroup a b c) : TriangleGroup a b c ⧸ H.1)) :=
  (markedIsoClass_cosetTriple_eq_iff _ e).mpr rfl

private theorem bijective_cosetMarkedIsoClassAux [NeZero n] :
    Function.Bijective (cosetMarkedIsoClassAux (a := a) (b := b) (c := c) (n := n)) := by
  refine ⟨fun H₁ H₂ h ↦ Subtype.ext ((markedIsoClass_cosetTriple_eq_iff _ _).mp
    (congrArg Subtype.val h)), fun M ↦ ?_⟩
  obtain ⟨t, i, hd, hM⟩ := M.2
  obtain ⟨ha, hb, hc⟩ := (hasDividingOrders_iff t.1).mp hd
  have hρ := (isConnected_iff_isPretransitive_range_toPerm t.1 ha hb hc).mp t.2 |>.2
  let H := (MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t.1 ha hb hc)
  let e : TriangleGroup a b c ⧸ H ≃ Fin n := (toPerm t.1 ha hb hc).quotientComapStabilizerEquiv hρ i
  let H' : Subgroup.ofIndex (TriangleGroup a b c) n :=
    ⟨H, Subgroup.mem_ofIndex.mpr (index_eq_of_equiv H e)⟩
  refine ⟨H', Subtype.ext ?_⟩
  rw [coe_cosetMarkedIsoClassAux H' e, ← hM]
  have he : e.permutationRepresentation = toPerm t.1 ha hb hc :=
    Equiv.permutationRepresentation_eq_of_map_smul e
      ((toPerm t.1 ha hb hc).quotientComapStabilizerEquiv_smul hρ i)
  have hct : (⟨cosetTriple H e, isConnected_cosetTriple H e⟩ : ConnectedTriple n) = t := by
    apply Subtype.ext
    dsimp only
    rw [cosetTriple_eq_permutationTripleEquiv, he, permutationTripleEquiv_toPerm]
  have hi : e ((1 : TriangleGroup a b c) : TriangleGroup a b c ⧸ H) = i :=
    ((toPerm t.1 ha hb hc).quotientComapStabilizerEquiv_mk hρ i 1).trans (by simp)
  rw [hct, hi]

/-- **Pointed Millington bijection for `Δ(a, b, c)`.** For `n ≠ 0`, subgroups of `Δ(a, b, c)` of
index `n` are in bijection with marked isomorphism classes of connected triples of degree `n` whose
component orders divide `a`, `b`, and `c`. -/
noncomputable def cosetMarkedIsoClassEquiv [NeZero n] :
    Subgroup.ofIndex (TriangleGroup a b c) n ≃ markedIsoClasses a b c n :=
  Equiv.ofBijective _ bijective_cosetMarkedIsoClassAux

/-- `cosetMarkedIsoClassEquiv` sends `H` to the class of `cosetTriple H e` marked at the base
coset `e 1`, independently of `e`. -/
theorem coe_cosetMarkedIsoClassEquiv_apply [NeZero n]
    (H : Subgroup.ofIndex (TriangleGroup a b c) n) (e : TriangleGroup a b c ⧸ H.1 ≃ Fin n) :
    (cosetMarkedIsoClassEquiv H : MarkedIsoClass n) =
      MarkedIsoClass.mk ⟨cosetTriple H.1 e, isConnected_cosetTriple H.1 e⟩
        (e ((1 : TriangleGroup a b c) : TriangleGroup a b c ⧸ H.1)) :=
  coe_cosetMarkedIsoClassAux H e

/-- The inverse of `cosetMarkedIsoClassEquiv` sends the marked class of `(t, i)` to the stabilizer
of the marked sheet `i` under `toPerm t`. -/
@[simp]
theorem coe_cosetMarkedIsoClassEquiv_symm_mk [NeZero n] (t : ConnectedTriple n) (i : Fin n)
    (ha : t.1.σ0 ^ a = 1) (hb : t.1.σ1 ^ b = 1) (hc : t.1.σinf ^ c = 1) :
    (cosetMarkedIsoClassEquiv.symm
      ⟨MarkedIsoClass.mk t i,
        mk_mem_markedIsoClasses_iff.mpr ((hasDividingOrders_iff t.1).mpr ⟨ha, hb, hc⟩)⟩ :
        Subgroup (TriangleGroup a b c)) =
      (MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t.1 ha hb hc) := by
  have hρ := (isConnected_iff_isPretransitive_range_toPerm t.1 ha hb hc).mp t.2 |>.2
  let H := (MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t.1 ha hb hc)
  let e : TriangleGroup a b c ⧸ H ≃ Fin n := (toPerm t.1 ha hb hc).quotientComapStabilizerEquiv hρ i
  let H' : Subgroup.ofIndex (TriangleGroup a b c) n :=
    ⟨H, Subgroup.mem_ofIndex.mpr (index_eq_of_equiv H e)⟩
  suffices cosetMarkedIsoClassEquiv.symm ⟨MarkedIsoClass.mk t i, _⟩ = H' by rw [this]
  apply cosetMarkedIsoClassEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_cosetMarkedIsoClassEquiv_apply H' e]
  have he : e.permutationRepresentation = toPerm t.1 ha hb hc :=
    Equiv.permutationRepresentation_eq_of_map_smul e
      ((toPerm t.1 ha hb hc).quotientComapStabilizerEquiv_smul hρ i)
  have hct : (⟨cosetTriple H e, isConnected_cosetTriple H e⟩ : ConnectedTriple n) = t := by
    apply Subtype.ext
    dsimp only
    rw [cosetTriple_eq_permutationTripleEquiv, he, permutationTripleEquiv_toPerm]
  have hi : e ((1 : TriangleGroup a b c) : TriangleGroup a b c ⧸ H) = i :=
    ((toPerm t.1 ha hb hc).quotientComapStabilizerEquiv_mk hρ i 1).trans (by simp)
  rw [hct, hi]

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
    H.ncard_orbit_mul_relIndex_normalizer, index_eq_of_equiv H e]

/-- **Finiteness at fixed index for `Δ(a, b, c)`.** For every `n ≠ 0`, `Δ(a, b, c)` has only
finitely many subgroups of index `n`. -/
theorem finite_ofIndex (a b c n : ℕ) [NeZero n] :
    Finite (Subgroup.ofIndex (TriangleGroup a b c) n) := by
  have : Finite (MarkedIsoClass n) :=
    Finite.of_surjective (fun p : ConnectedTriple n × Fin n ↦ MarkedIsoClass.mk p.1 p.2)
      fun m ↦ let ⟨t, i, h⟩ := MarkedIsoClass.mk_surjective m; ⟨(t, i), h⟩
  exact Finite.of_equiv (markedIsoClasses a b c n) cosetMarkedIsoClassEquiv.symm

/-- Unbundled form of `finite_ofIndex`: `{H : Subgroup (TriangleGroup a b c) // H.index = n}` is
finite for `n ≠ 0`. -/
theorem finite_subgroups_of_index (a b c n : ℕ) [NeZero n] :
    Finite {H : Subgroup (TriangleGroup a b c) // H.index = n} :=
  have := finite_ofIndex a b c n
  Finite.of_equiv (Subgroup.ofIndex (TriangleGroup a b c) n)
    (Equiv.subtypeEquivRight fun _ ↦ Subgroup.mem_ofIndex)

/-- For every `n ≠ 0`, `Δ(a, b, c)` has only finitely many conjugacy classes of subgroups of
index `n`. -/
theorem finite_orbitRel_quotient_ofIndex (a b c n : ℕ) [NeZero n] :
    Finite (MulAction.orbitRel.Quotient (ConjAct (TriangleGroup a b c))
      (Subgroup.ofIndex (TriangleGroup a b c) n)) := by
  have := finite_ofIndex a b c n
  exact Quotient.finite _

end TriangleGroup

end TauCeti

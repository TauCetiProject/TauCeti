/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.Associativity

import Mathlib.Tactic.Group
import TauCeti.GroupTheory.Coset.Basic
import TauCeti.NumberTheory.HeckeRing.StabConjugation

/-!
# Transporting Hecke multiplicities along group equivalences and inclusions

The double-coset multiplicity is unchanged when the ambient group, its three subgroups, and
the three elements are transported along a group equivalence, when representatives are varied
within their double cosets (including along `HeckeCoset.map`), or when a subgroup `H'` is
intersected with an ambient subgroup `P` containing the representatives and meeting all
stabilizer cosets.

## Main results

* `DoubleCoset.multiplicity_map_equiv`: transport of Shimura's multiplicity along a group
  equivalence.
* `DoubleCoset.multiplicity_doubleCoset_congr_first` and
  `DoubleCoset.multiplicity_doubleCoset_congr_second`: invariance in the first and second inputs,
  with `HeckeCoset.multiplicity_map_rep` for chosen representatives of mapped cosets.
* `DoubleCoset.multiplicity_eq_of_inf`: equality of Shimura's multiplicities for `H = H' ⊓ P` and
  `H'` on elements of `P`.
-/

public section

open Subgroup
open scoped Pointwise

namespace DoubleCoset

variable {G K : Type*} [Group G] [Group K]

/-- A group equivalence carries the decomposition quotient of `g` to that of its image. The
special case of `decompQuotientEquivMapOfInjective` at an isomorphism, which is the only
injective homomorphism the multiplicity transport needs. -/
noncomputable def decompQuotientEquivMap (e : G ≃* K) (H₁ H₂ : Subgroup G) (g : G) :
    DecompQuotient H₁ H₂ g ≃
      DecompQuotient (H₁.map (e : G →* K)) (H₂.map (e : G →* K)) (e g) :=
  decompQuotientEquivMapOfInjective (e : G →* K) e.injective H₁ H₂ g

/-- The image of a decomposition class represented by `x` is represented by `e x`. -/
@[simp] lemma decompQuotientEquivMap_mk (e : G ≃* K) (H₁ H₂ : Subgroup G) (g : G) (x : H₁) :
    decompQuotientEquivMap e H₁ H₂ g (QuotientGroup.mk x) =
      QuotientGroup.mk (e.subgroupMap H₁ x) := by
  unfold decompQuotientEquivMap
  exact (decompQuotientEquivMapOfInjective_mk _ _ _ _ _ x).trans
    (congrArg QuotientGroup.mk (Subtype.ext (by simp)))

/-- The chosen representative after transport differs from the transported representative by
an element of the stabilizer. -/
lemma decompQuotientEquivMap_out (e : G ≃* K) (H₁ H₂ : Subgroup G) (g : G)
    (i : DecompQuotient H₁ H₂ g) :
    ((e : G →* K) g)⁻¹ * (((decompQuotientEquivMap e H₁ H₂ g i).out : K)⁻¹ *
      (e : G →* K) (i.out : G)) * (e : G →* K) g ∈ H₂.map (e : G →* K) := by
  have hmk :
      ((decompQuotientEquivMap e H₁ H₂ g i).out :
          DecompQuotient (H₁.map (e : G →* K)) (H₂.map (e : G →* K)) ((e : G →* K) g)) =
        (e.subgroupMap H₁ i.out :
          DecompQuotient (H₁.map (e : G →* K)) (H₂.map (e : G →* K)) ((e : G →* K) g)) := by
    calc
      _ = decompQuotientEquivMap e H₁ H₂ g i := QuotientGroup.out_eq' _
      _ = decompQuotientEquivMap e H₁ H₂ g (i.out : DecompQuotient H₁ H₂ g) :=
        congrArg (decompQuotientEquivMap e H₁ H₂ g) (QuotientGroup.out_eq' i).symm
      _ = _ := decompQuotientEquivMap_mk e H₁ H₂ g i.out
  exact conj_mem_of_mk_eq ((e : G →* K) g) hmk

/-- Shimura's multiplicity is unchanged when all of its data are transported along a group
equivalence, without any finiteness hypothesis. -/
@[simp] theorem multiplicity_map_equiv (e : G ≃* K) (H₁ H₂ H₃ : Subgroup G) (g h d : G) :
    multiplicity (H₁.map (e : G →* K)) (H₂.map (e : G →* K)) (H₃.map (e : G →* K))
        (e g) (e h) (e d) =
      multiplicity H₁ H₂ H₃ g h d := by
  let eg := decompQuotientEquivMap e H₁ H₂ g
  let eh := decompQuotientEquivMap e H₂ H₃ h
  let c : DecompQuotient H₁ H₂ g → H₂.map (e : G →* K) := fun i ↦
    ⟨((e : G →* K) g)⁻¹ * (((eg i).out : K)⁻¹ * (e : G →* K) (i.out : G)) *
      (e : G →* K) g, decompQuotientEquivMap_out e H₁ H₂ g i⟩
  -- Transporting the first representative introduces the middle-subgroup correction `c i`.
  -- Shearing the transported second quotient by it matches the full defining fibres directly.
  let epairs := Equiv.prodShear eg fun i ↦ eh.trans (MulAction.toPerm (c i))
  rw [multiplicity_def, multiplicity_def]
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv epairs fun ⟨i, j⟩ ↦ ?_)
  let q := c i • eh j
  have hprod :
      (((eg i).out : K) * (e : G →* K) g * ((q.out : K) * (e : G →* K) h) :
          K ⧸ (H₃.map (e : G →* K))) =
        ((e : G →* K) ((i.out : G) * g * ((j.out : G) * h)) :
          K ⧸ (H₃.map (e : G →* K))) := by
    rw [QuotientGroup.eq]
    have hm := (H₃.map (e : G →* K)).mul_mem
      (conj_mem_of_mk_eq ((e : G →* K) h) (QuotientGroup.mk_out_smul (c i) (eh j)))
      (decompQuotientEquivMap_out e H₂ H₃ h j)
    dsimp only [q, c, eh, Subtype.coe_mk] at hm ⊢
    simpa only [Subgroup.coe_mul, map_mul, mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hm
  -- Unfold only the pair equivalence so its second component is the named quotient `q` above.
  dsimp only [epairs, Equiv.prodShear_apply, Equiv.trans_apply, MulAction.toPerm_apply]
  change
    (((i.out : G) * g * ((j.out : G) * h) : G ⧸ H₃) = (d : G ⧸ H₃)) ↔
      ((((eg i).out : K) * (e : G →* K) g * ((q.out : K) * (e : G →* K) h) :
          K ⧸ (H₃.map (e : G →* K))) =
        ((e : G →* K) d : K ⧸ (H₃.map (e : G →* K))))
  rw [hprod, QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul,
    Subgroup.mem_map_iff_mem (f := (e : G →* K)) e.injective]

/-- Shimura's multiplicity depends on its second input only through its double coset, without
any finiteness or Hecke-triple hypothesis. -/
theorem multiplicity_doubleCoset_congr_second (H₁ H₂ H₃ : Subgroup G)
    (g : G) {h h' : G} (d : G) (hh : h' ∈ doubleCoset h H₂ H₃) :
    multiplicity H₁ H₂ H₃ g h' d = multiplicity H₁ H₂ H₃ g h d := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hh
  let aN : Subgroup.normalizer (H₂ : Set G) := ⟨a, Subgroup.le_normalizer ha⟩
  let eh := decompQuotientEquivMulLeftRight H₂ H₃ h aN (Subgroup.le_normalizer hb)
  let epairs := Equiv.prodCongr (Equiv.refl (DecompQuotient H₁ H₂ g))
    (eh.trans (MulAction.toPerm (⟨a, ha⟩ : H₂)))
  rw [multiplicity_def, multiplicity_def]
  refine Nat.card_congr (Equiv.subtypeEquiv epairs fun p ↦ ?_)
  obtain ⟨i, j⟩ := p
  simp only [Set.mem_ofPred_eq]
  let q := (⟨a, ha⟩ : H₂) • eh j
  have hq : (QuotientGroup.mk q.out : DecompQuotient H₂ H₃ h) =
      QuotientGroup.mk (j.out * (⟨a, ha⟩ : H₂)) := by
    calc
      _ = q := QuotientGroup.out_eq' q
      _ = (⟨a, ha⟩ : H₂) • eh j := rfl
      _ = (⟨a, ha⟩ : H₂) • eh (QuotientGroup.mk j.out) :=
        congrArg (fun x ↦ (⟨a, ha⟩ : H₂) • eh x) (QuotientGroup.out_eq' j).symm
      _ = (⟨a, ha⟩ : H₂) • QuotientGroup.mk
          ((H₂.normalizerMonoidHom aN).symm j.out) := by
        rw [decompQuotientEquivMulLeftRight_mk]
      _ = _ := by
        rw [MulAction.Quotient.smul_mk, smul_eq_mul]
        apply congrArg QuotientGroup.mk
        ext
        dsimp only [aN]
        simp [Subgroup.normalizerMonoidHom, HSMul.hSMul, mul_assoc]
  have hqmem := conj_mem_of_mk_eq h hq
  have hprod :
      ((i.out : G) * g * ((j.out : G) * (a * h * b)) : G ⧸ H₃) =
        ((i.out : G) * g * ((q.out : G) * h) : G ⧸ H₃) := by
    rw [QuotientGroup.eq]
    have hm := H₃.mul_mem (H₃.inv_mem hb) (H₃.inv_mem hqmem)
    simpa [mul_inv_rev, mul_assoc] using hm
  -- As above, expose only the product equivalence and name its transported component `q`.
  dsimp only [epairs, Equiv.prodCongr_apply, Equiv.refl_apply, Equiv.trans_apply,
    MulAction.toPerm_apply]
  change
    (((i.out : G) * g * ((j.out : G) * (a * h * b)) : G ⧸ H₃) = (d : G ⧸ H₃)) ↔
      (((i.out : G) * g * ((q.out : G) * h) : G ⧸ H₃) = (d : G ⧸ H₃))
  rw [hprod]

/-- Shimura's multiplicity depends on its first input only through its double coset, without
any finiteness or Hecke-triple hypothesis. -/
theorem multiplicity_doubleCoset_congr_first (H₁ H₂ H₃ : Subgroup G)
    {g g' : G} (h d : G) (hg : g' ∈ doubleCoset g H₁ H₂) :
    multiplicity H₁ H₂ H₃ g' h d = multiplicity H₁ H₂ H₃ g h d := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hg
  let aN : Subgroup.normalizer (H₁ : Set G) := ⟨a, Subgroup.le_normalizer ha⟩
  let e₀ := decompQuotientEquivMulLeftRight H₁ H₂ g aN (Subgroup.le_normalizer hb)
  let eg := e₀.trans (MulAction.toPerm (⟨a, ha⟩ : H₁))
  have heg (i : DecompQuotient H₁ H₂ (a * g * b)) :
      (QuotientGroup.mk (eg i).out : DecompQuotient H₁ H₂ g) =
        QuotientGroup.mk (i.out * (⟨a, ha⟩ : H₁)) := by
    calc (QuotientGroup.mk (eg i).out : DecompQuotient H₁ H₂ g)
      _ = (⟨a, ha⟩ : H₁) • e₀ (QuotientGroup.mk i.out) :=
        (QuotientGroup.out_eq' (eg i)).trans (congrArg eg (QuotientGroup.out_eq' i).symm)
      _ = QuotientGroup.mk (i.out * (⟨a, ha⟩ : H₁)) := by
        rw [decompQuotientEquivMulLeftRight_mk, MulAction.Quotient.smul_mk, smul_eq_mul]
        exact congrArg QuotientGroup.mk (Subtype.ext (by
          simp [aN, Subgroup.normalizerMonoidHom_apply_symm_apply_coe, mul_assoc]))
  let c : DecompQuotient H₁ H₂ (a * g * b) → H₂ := fun i ↦
    ⟨g⁻¹ * (((eg i).out : G)⁻¹ * ((i.out : G) * a)) * g * b,
      H₂.mul_mem (conj_mem_of_mk_eq g (heg i)) hb⟩
  let epairs : DecompQuotient H₁ H₂ (a * g * b) × DecompQuotient H₂ H₃ h ≃
      DecompQuotient H₁ H₂ g × DecompQuotient H₂ H₃ h :=
    Equiv.prodShear eg fun i ↦ MulAction.toPerm (c i)
  rw [multiplicity_def, multiplicity_def]
  refine Nat.card_congr (Equiv.subtypeEquiv epairs fun ⟨i, j⟩ ↦ ?_)
  let q := c i • j
  have hprod : ((i.out : G) * (a * g * b) * ((j.out : G) * h) : G ⧸ H₃) =
      (((eg i).out : G) * g * ((q.out : G) * h) : G ⧸ H₃) := by
    rw [QuotientGroup.eq]
    have hm := H₃.inv_mem (conj_mem_of_mk_eq h (QuotientGroup.mk_out_smul (c i) j))
    dsimp only [q, c, Subtype.coe_mk] at hm ⊢
    simpa only [Subgroup.coe_mul, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using hm
  -- As above, expose only the shear equivalence so its second component is the named quotient `q`.
  dsimp only [epairs, Equiv.prodShear_apply, MulAction.toPerm_apply]
  change (((i.out : G) * (a * g * b) * ((j.out : G) * h) : G ⧸ H₃) = (d : G ⧸ H₃)) ↔
    ((((eg i).out : G) * g * ((q.out : G) * h) : G ⧸ H₃) = (d : G ⧸ H₃))
  rw [hprod]

/-- When `H = H' ⊓ P` and `H` meets all relevant stabilizer cosets in `H'`, Shimura's multiplicity
for `H'` agrees with that for `H` on elements `g, h, d ∈ P`. -/
theorem multiplicity_eq_of_inf {H H' P : Subgroup G} (hHP : H = H' ⊓ P) {g h d : G}
    (hgP : g ∈ P) (hhP : h ∈ P) (hdP : d ∈ P)
    (hstab_g : ∀ u ∈ H', ∃ x ∈ H, x⁻¹ * u ∈ ConjAct.toConjAct g • H')
    (hstab_h : ∀ u ∈ H', ∃ x ∈ H, x⁻¹ * u ∈ ConjAct.toConjAct h • H') :
    multiplicity H' H' H' g h d = multiplicity H H H g h d := by
  have hmem_iff (w : G) : w ∈ H ↔ w ∈ H' ∧ w ∈ P := by rw [hHP, Subgroup.mem_inf]
  have hle : H ≤ H' := hHP ▸ inf_le_left
  have hleP : H ≤ P := hHP ▸ inf_le_right
  let eg := decompQuotientEquivOfInf hHP hgP hstab_g
  let eh := decompQuotientEquivOfInf hHP hhP hstab_h
  have heg (i : DecompQuotient H H g) :
      (QuotientGroup.mk (eg i).out : DecompQuotient H' H' g) =
        QuotientGroup.mk (Subgroup.inclusion hle i.out) := by
    rw [QuotientGroup.out_eq', ← QuotientGroup.out_eq' i, decompQuotientEquivOfInf_mk]
    simp only [QuotientGroup.out_eq']
  let c : DecompQuotient H H g → H' := fun i ↦
    ⟨g⁻¹ * (((eg i).out : G)⁻¹ * (i.out : G)) * g, conj_mem_of_mk_eq g (heg i)⟩
  -- Passing from `(i.out : G) * g` to `((eg i).out : G) * g` introduces the factor `c i ∈ H'`,
  -- which is absorbed by shearing the second quotient `DecompQuotient H' H' h`.
  let epairs : DecompQuotient H H g × DecompQuotient H H h ≃
      DecompQuotient H' H' g × DecompQuotient H' H' h :=
    (Equiv.prodShear (Equiv.refl _) fun i ↦ eh.trans (MulAction.toPerm (c i))).trans
      (Equiv.prodCongr eg (Equiv.refl _))
  symm
  rw [multiplicity_def, multiplicity_def]
  refine Nat.card_congr (Equiv.subtypeEquiv epairs fun ⟨i, j⟩ ↦ ?_)
  set q : DecompQuotient H' H' h := c i • eh j with hq_def
  have hq : (QuotientGroup.mk q.out : DecompQuotient H' H' h) =
      QuotientGroup.mk (c i * Subgroup.inclusion hle j.out) := by
    conv_lhs => rw [QuotientGroup.out_eq', hq_def, ← QuotientGroup.out_eq' j]
    rw [decompQuotientEquivOfInf_mk, MulAction.Quotient.smul_mk, smul_eq_mul]
  have hprodH' : (((eg i).out : G) * g * ((q.out : G) * h) : G ⧸ H') =
      ((i.out : G) * g * ((j.out : G) * h) : G ⧸ H') :=
    QuotientGroup.eq.mpr (by
      convert conj_mem_of_mk_eq h hq using 1
      simp only [c, Subgroup.coe_mul, Subgroup.coe_inclusion]; group)
  have hzP : ((i.out : G) * g * ((j.out : G) * h))⁻¹ * d ∈ P :=
    P.mul_mem (P.inv_mem (P.mul_mem (P.mul_mem (hleP i.out.2) hgP)
      (P.mul_mem (hleP j.out.2) hhP))) hdP
  -- Unfold only the pair equivalence `epairs` so its second component is the named quotient `q`
  -- without unfolding `eg` or `q`, and expose the defining fibre equations.
  dsimp only [epairs, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodShear_apply,
    Equiv.refl_apply, MulAction.toPerm_apply]
  change (((i.out : G) * g * ((j.out : G) * h) : G ⧸ H) = (d : G ⧸ H)) ↔
    ((((eg i).out : G) * g * ((q.out : G) * h) : G ⧸ H') = (d : G ⧸ H'))
  rw [hprodH', QuotientGroup.eq, QuotientGroup.eq, hmem_iff]
  exact and_iff_left hzP

end DoubleCoset

namespace HeckeCoset

/-- Replacing the chosen representatives of mapped Hecke cosets by the source representatives
leaves Shimura's `(H₁', H₂', H₃')`-multiplicity unchanged. -/
theorem multiplicity_map_rep {G : Type*} [Group G] {Δ₁ Δ₂ : Submonoid G}
    {H₁ H₂ H₃ H₁' H₂' H₃' : Subgroup G}
    (hΔ : Δ₁ ≤ Δ₂) (h₁ : H₁ ≤ H₁') (h₂ : H₂ ≤ H₂') (h₃ : H₃ ≤ H₃')
    (D₁ : HeckeCoset Δ₁ H₁ H₂) (D₂ : HeckeCoset Δ₁ H₂ H₃) (D : HeckeCoset Δ₁ H₁ H₃) :
    DoubleCoset.multiplicity H₁' H₂' H₃' ((D₁.map hΔ h₁ h₂).rep : G) ((D₂.map hΔ h₂ h₃).rep : G)
        ((D.map hΔ h₁ h₃).rep : G) =
      DoubleCoset.multiplicity H₁' H₂' H₃' (D₁.rep : G) (D₂.rep : G) (D.rep : G) := by
  rw [DoubleCoset.multiplicity_doubleCoset_congr_first H₁' H₂' H₃' _ _
        (rep_map_mem_doubleCoset hΔ h₁ h₂ D₁),
    DoubleCoset.multiplicity_doubleCoset_congr_second H₁' H₂' H₃' _ _
        (rep_map_mem_doubleCoset hΔ h₂ h₃ D₂),
    DoubleCoset.multiplicity_doubleCoset_congr _ _ (rep_map_mem_doubleCoset hΔ h₁ h₃ D)]

end HeckeCoset

end

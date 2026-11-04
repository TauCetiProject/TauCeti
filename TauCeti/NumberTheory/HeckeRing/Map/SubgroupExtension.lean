/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import TauCeti.NumberTheory.HeckeRing.Map.Submonoid
public import TauCeti.NumberTheory.HeckeRing.Multiplicity.Equiv
import Mathlib.Tactic.Group

/-!
# Extending both subgroup and submonoid along a subgroup intersection

Suppose `H, H', P ≤ G` are subgroups with `H = H' ⊓ P`, and `Δ ≤ Δ'` are submonoids of `G` with
`Δ ≤ P`, such that:
1. every element of `Δ'` can be translated into `Δ` on the left by `H'`
   (`∀ δ' : Δ', ∃ u ∈ H', u * δ' ∈ Δ`), and
2. for every `g : Δ`, left cosets of `H' ∩ g H' g⁻¹` in `H'` all meet `H`
   (`∀ g : Δ, ∀ u ∈ H', ∃ x ∈ H, x⁻¹ * u ∈ g H' g⁻¹`).

Then `HeckeCoset.map` gives a bijection `HeckeCoset Δ H H ≃ HeckeCoset Δ' H' H'`, the decomposition
quotients `H ⧸ (H ∩ g H g⁻¹)` and `H' ⧸ (H' ∩ g H' g⁻¹)` correspond bijectively for every `g ∈ Δ`,
Shimura's multiplicities agree on `Δ`, and pushing coefficients forward along the coset equivalence
yields a ring isomorphism `𝕋 Δ H R ≃+* 𝕋 Δ' H' R` over any coefficient semiring `R`.

This is the abstract group-theoretic core of Proposition 3.16 of [Shimura][shimura1971] and §2 of
[Rhodes–Shemanske][rhodes1999], which identifies `H(SL_n(ℤ), GL_n^+(ℚ))` with `H(GL_n(ℤ), GL_n(ℚ))`
via `SL_n(ℤ) = GL_n(ℤ) ⊓ GL_n^+(ℚ)`.

## Main definitions and results

* `DoubleCoset.decompQuotientEquivOfInf`: the bijection
  `DecompQuotient H H g ≃ DecompQuotient H' H' g` for `g ∈ P` when `H = H' ⊓ P` meets every left
  coset of `H' ∩ g H' g⁻¹` in `H'`.
* `DoubleCoset.multiplicity_eq_of_inf`: equality of Shimura's multiplicities
  `multiplicity H' H' H' g h d = multiplicity H H H g h d` for `g, h, d ∈ P`.
* `HeckeCoset.mapEquivOfInf`: the bijection `HeckeCoset Δ H H ≃ HeckeCoset Δ' H' H'`.
* `HeckeCosetModule.mapSubgroupRingEquiv`: the ring isomorphism `𝕋 Δ H R ≃+* 𝕋 Δ' H' R`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.16.
* [J. A. Rhodes and T. R. Shemanske,
  *Rationality theorems for Hecke operators on GL_n*][rhodes1999], §2.
-/

public section

open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G] {H H' P : Subgroup G}

/-- When `H = H' ⊓ P`, `g ∈ P`, and `H` meets every left coset of `H' ∩ g H' g⁻¹` in `H'`,
inclusion `H ≤ H'` induces a bijection `DecompQuotient H H g ≃ DecompQuotient H' H' g`. -/
noncomputable def decompQuotientEquivOfInf (hHP : H = H' ⊓ P) {g : G} (hgP : g ∈ P)
    (hstab : ∀ u ∈ H', ∃ x ∈ H, x⁻¹ * u ∈ ConjAct.toConjAct g • H') :
    DecompQuotient H H g ≃ DecompQuotient H' H' g :=
  have hsub : (ConjAct.toConjAct g • H).subgroupOf H =
      ((ConjAct.toConjAct g • H').subgroupOf H').comap
        (Subgroup.inclusion (hHP ▸ inf_le_left)) := by
    have hmem_iff (w : G) : w ∈ H ↔ w ∈ H' ∧ w ∈ P := by rw [hHP, Subgroup.mem_inf]
    ext x
    have hxP : (x : G) ∈ P := ((hmem_iff (x : G)).mp x.2).2
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv]
    rw [hmem_iff]
    exact and_iff_left (P.mul_mem (P.mul_mem (P.inv_mem hgP) hxP) hgP)
  (Subgroup.quotientEquivOfEq hsub).trans
    (TauCeti.QuotientGroup.congrComapOfSurjectiveMk (Subgroup.inclusion (hHP ▸ inf_le_left))
      ((ConjAct.toConjAct g • H').subgroupOf H') fun q ↦ by
        induction q using QuotientGroup.induction_on with
        | _ u =>
          obtain ⟨x, hxH, hxu⟩ := hstab (u : G) u.2
          exact ⟨⟨x, hxH⟩, QuotientGroup.eq.mpr (by
            simpa [Subgroup.mem_subgroupOf] using hxu)⟩)

/-- `decompQuotientEquivOfInf` sends the coset of `x : H` to the coset of `x` in `H'`. -/
@[simp]
theorem decompQuotientEquivOfInf_mk (hHP : H = H' ⊓ P) {g : G} (hgP : g ∈ P)
    (hstab : ∀ u ∈ H', ∃ x ∈ H, x⁻¹ * u ∈ ConjAct.toConjAct g • H') (x : H) :
    decompQuotientEquivOfInf hHP hgP hstab (QuotientGroup.mk x) =
      QuotientGroup.mk (Subgroup.inclusion (hHP ▸ inf_le_left) x) := by
  rw [decompQuotientEquivOfInf, Equiv.trans_apply, Subgroup.quotientEquivOfEq_mk]
  exact TauCeti.QuotientGroup.congrComapOfSurjectiveMk_mk _ _ _ x

/-- When `H = H' ⊓ P` and `H` meets all relevant stabilizer cosets in `H'`, Shimura's multiplicity
for `H'` agrees with that for `H` on elements `g, h, d ∈ P`. -/
theorem multiplicity_eq_of_inf (hHP : H = H' ⊓ P) {g h d : G}
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
  let q : DecompQuotient H' H' h := c i • eh j
  have hq : (QuotientGroup.mk q.out : DecompQuotient H' H' h) =
      QuotientGroup.mk (c i * Subgroup.inclusion hle j.out) := by
    rw [QuotientGroup.out_eq', show q = c i • eh (QuotientGroup.mk j.out) by
      dsimp only [q]; rw [QuotientGroup.out_eq'], decompQuotientEquivOfInf_mk,
      MulAction.Quotient.smul_mk, smul_eq_mul]
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

open DoubleCoset

variable {G : Type*} [Group G] {Δ Δ' : Submonoid G} {H H' P : Subgroup G}
  (hHP : H = H' ⊓ P) (hΔ : Δ ≤ Δ') (hΔP : Δ ≤ P.toSubmonoid)
  (hsurj : ∀ δ' : Δ', ∃ u ∈ H', u * (δ' : G) ∈ Δ)
  (hstab : ∀ g : Δ, ∀ u ∈ H', ∃ x ∈ H, x⁻¹ * u ∈ ConjAct.toConjAct (g : G) • H')

include hΔP hsurj hstab in
/-- Under `H = H' ⊓ P`, `Δ ≤ Δ'`, `Δ ≤ P`, left-coset surjectivity of `Δ` in `Δ'` modulo `H'`, and
the stabilizer condition `hstab`, the natural map `HeckeCoset Δ H H → HeckeCoset Δ' H' H'` is
bijective. -/
theorem map_bijective_of_inf :
    Function.Bijective
      (HeckeCoset.map hΔ (hHP ▸ inf_le_left : H ≤ H') (hHP ▸ inf_le_left : H ≤ H')) := by
  have hmem_iff (w : G) : w ∈ H ↔ w ∈ H' ∧ w ∈ P := by rw [hHP, Subgroup.mem_inf]
  have hleP : H ≤ P := hHP ▸ inf_le_right
  constructor
  · intro D₁ D₂ hEq
    induction D₁ using HeckeCoset.induction with | h g₁ =>
    induction D₂ using HeckeCoset.induction with | h g₂ =>
    rw [map_mk, map_mk, eq_iff, Submonoid.coe_inclusion, Submonoid.coe_inclusion] at hEq
    have hmem : (g₁ : G) ∈ doubleCoset (g₂ : G) H' H' := hEq ▸ mem_doubleCoset_self H' H' _
    obtain ⟨u₁, hu₁, u₂, hu₂, hg₁⟩ := mem_doubleCoset.mp hmem
    obtain ⟨x, hxH, hxu₁⟩ := hstab g₂ u₁ hu₁
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv] at hxu₁
    set v : G := (g₂ : G)⁻¹ * (x⁻¹ * u₁) * (g₂ : G)
    have hfact : x * (g₂ : G) * (v * u₂) = (g₁ : G) := by rw [hg₁]; dsimp only [v]; group
    have hvu₂P : v * u₂ ∈ P := by
      rw [show v * u₂ = (g₂ : G)⁻¹ * x⁻¹ * (g₁ : G) by rw [← hfact]; group]
      exact P.mul_mem (P.mul_mem (P.inv_mem (hΔP g₂.2)) (P.inv_mem (hleP hxH))) (hΔP g₁.2)
    exact mk_eq_mk_of_mem (mem_doubleCoset.mpr
      ⟨x, hxH, v * u₂, (hmem_iff _).mpr ⟨H'.mul_mem hxu₁ hu₂, hvu₂P⟩, hfact.symm⟩)
  · intro E
    induction E using HeckeCoset.induction with | h δ' =>
    obtain ⟨u, huH', huΔ⟩ := hsurj δ'
    exact ⟨mk H H ⟨u * (δ' : G), huΔ⟩, by
      rw [map_mk]; exact mk_eq_mk_of_mem (mem_doubleCoset.mpr ⟨u, huH', 1, H'.one_mem, by simp⟩)⟩

include hHP hΔ hΔP hsurj hstab in
/-- The bijection `HeckeCoset Δ H H ≃ HeckeCoset Δ' H' H'` bundled as an `Equiv`. -/
noncomputable def mapEquivOfInf : HeckeCoset Δ H H ≃ HeckeCoset Δ' H' H' :=
  Equiv.ofBijective _ (map_bijective_of_inf hHP hΔ hΔP hsurj hstab)

/-- `mapEquivOfInf` acts via `HeckeCoset.map`. -/
@[simp]
theorem mapEquivOfInf_apply (D : HeckeCoset Δ H H) :
    mapEquivOfInf hHP hΔ hΔP hsurj hstab D =
      D.map hΔ (hHP ▸ inf_le_left) (hHP ▸ inf_le_left) :=
  (rfl)

end HeckeCoset

namespace HeckeCosetModule

open DoubleCoset
open scoped HeckeCosetModule

variable {G : Type*} [Group G] {Δ Δ' : Submonoid G} {H H' P : Subgroup G}

section LinearEquiv

variable (R : Type*) [Semiring R] (hHP : H = H' ⊓ P) (hΔ : Δ ≤ Δ') (hΔP : Δ ≤ P.toSubmonoid)
  (hsurj : ∀ δ' : Δ', ∃ u ∈ H', u * (δ' : G) ∈ Δ)
  (hstab : ∀ g : Δ, ∀ u ∈ H', ∃ x ∈ H, x⁻¹ * u ∈ ConjAct.toConjAct (g : G) • H')

include hHP hΔ hΔP hsurj hstab in
/-- The `R`-linear equivalence `𝕋 Δ H R ≃ₗ[R] 𝕋 Δ' H' R` induced by `HeckeCoset.mapEquivOfInf`. -/
noncomputable def mapSubgroupLinearEquiv : 𝕋 Δ H R ≃ₗ[R] 𝕋 Δ' H' R :=
  Finsupp.mapDomain.linearEquiv R R (HeckeCoset.mapEquivOfInf hHP hΔ hΔP hsurj hstab)

/-- Evaluating `mapSubgroupLinearEquiv` at a mapped coset recovers the source coefficient. -/
@[simp]
theorem mapSubgroupLinearEquiv_apply_map (f : 𝕋 Δ H R) (D : HeckeCoset Δ H H) :
    mapSubgroupLinearEquiv R hHP hΔ hΔP hsurj hstab f
        (D.map hΔ (hHP ▸ inf_le_left) (hHP ▸ inf_le_left)) = f D :=
  Finsupp.mapDomain_apply_of_injective
    (HeckeCoset.map_bijective_of_inf hHP hΔ hΔP hsurj hstab).1 f D

/-- `mapSubgroupLinearEquiv` sends each basis element `single R D b` to the mapped basis element. -/
@[simp]
theorem mapSubgroupLinearEquiv_single (D : HeckeCoset Δ H H) (b : R) :
    mapSubgroupLinearEquiv R hHP hΔ hΔP hsurj hstab (single R D b) =
      single R (D.map hΔ (hHP ▸ inf_le_left) (hHP ▸ inf_le_left)) b :=
  mapDomain_single R _ D b

end LinearEquiv

section RingEquiv

variable (R : Type*) [Semiring R] [IsHeckeTriple Δ H H] [IsHeckeTriple Δ' H' H']
  (hHP : H = H' ⊓ P) (hΔ : Δ ≤ Δ') (hΔP : Δ ≤ P.toSubmonoid)
  (hsurj : ∀ δ' : Δ', ∃ u ∈ H', u * (δ' : G) ∈ Δ)
  (hstab : ∀ g : Δ, ∀ u ∈ H', ∃ x ∈ H, x⁻¹ * u ∈ ConjAct.toConjAct (g : G) • H')

/-- `mapSubgroupLinearEquiv` sends structure constants on `H` to structure constants on `H'`. -/
theorem mapSubgroupLinearEquiv_structureConstants (D₁ D₂ : HeckeCoset Δ H H) :
    mapSubgroupLinearEquiv R hHP hΔ hΔP hsurj hstab
        (structureConstants R H H H D₁.rep D₂.rep) =
      structureConstants R H' H' H'
        (D₁.map hΔ (hHP ▸ inf_le_left) (hHP ▸ inf_le_left)).rep
        (D₂.map hΔ (hHP ▸ inf_le_left) (hHP ▸ inf_le_left)).rep := by
  ext E
  obtain ⟨D, rfl⟩ := (HeckeCoset.map_bijective_of_inf hHP hΔ hΔP hsurj hstab).2 E
  rw [mapSubgroupLinearEquiv_apply_map, structureConstants_apply, structureConstants_apply,
    HeckeCoset.multiplicity_map_rep hΔ (hHP ▸ inf_le_left) (hHP ▸ inf_le_left) (hHP ▸ inf_le_left)
      D₁ D₂ D,
    multiplicity_eq_of_inf hHP (hΔP D₁.rep.2) (hΔP D₂.rep.2) (hΔP D.rep.2)
      (hstab D₁.rep) (hstab D₂.rep)]

/-- `mapSubgroupLinearEquiv` preserves the Hecke product. -/
theorem mapSubgroupLinearEquiv_mul (f g : 𝕋 Δ H R) :
    mapSubgroupLinearEquiv R hHP hΔ hΔP hsurj hstab (f * g) =
      mapSubgroupLinearEquiv R hHP hΔ hΔP hsurj hstab f *
        mapSubgroupLinearEquiv R hHP hΔ hΔP hsurj hstab g := by
  let L := (mapSubgroupLinearEquiv R hHP hΔ hΔP hsurj hstab).toLinearMap
  rw [mul_def, mul_def]
  exact map_mul_of_structureConstants R hΔ (hHP ▸ inf_le_left) (hHP ▸ inf_le_left)
    (hHP ▸ inf_le_left) L L L
    (mapSubgroupLinearEquiv_single R hHP hΔ hΔP hsurj hstab)
    (mapSubgroupLinearEquiv_single R hHP hΔ hΔP hsurj hstab)
    (mapSubgroupLinearEquiv_structureConstants R hHP hΔ hΔP hsurj hstab) f g

include hHP hΔ hΔP hsurj hstab in
/-- **Subgroup-extension isomorphism for Hecke rings** (Shimura Proposition 3.16 /
Rhodes–Shemanske §2): when `H = H' ⊓ P` and `Δ ≤ P` satisfy left-coset surjectivity in `Δ'` and the
stabilizer condition in `H'`, `HeckeCoset.map` induces a ring isomorphism `𝕋 Δ H R ≃+* 𝕋 Δ' H' R`
over any coefficient semiring `R`. -/
noncomputable def mapSubgroupRingEquiv : 𝕋 Δ H R ≃+* 𝕋 Δ' H' R :=
  { mapSubgroupLinearEquiv R hHP hΔ hΔP hsurj hstab with
    map_mul' := mapSubgroupLinearEquiv_mul R hHP hΔ hΔP hsurj hstab }

/-- `mapSubgroupRingEquiv` coerces to `mapSubgroupLinearEquiv`. -/
@[simp]
theorem coe_mapSubgroupRingEquiv :
    ⇑(mapSubgroupRingEquiv R hHP hΔ hΔP hsurj hstab) =
      mapSubgroupLinearEquiv R hHP hΔ hΔP hsurj hstab :=
  (rfl)

/-- `mapSubgroupRingEquiv` sends a basis element `single R D b` to the mapped basis element. -/
@[simp]
theorem mapSubgroupRingEquiv_single (D : HeckeCoset Δ H H) (b : R) :
    mapSubgroupRingEquiv R hHP hΔ hΔP hsurj hstab (single R D b) =
      single R (D.map hΔ (hHP ▸ inf_le_left) (hHP ▸ inf_le_left)) b :=
  mapSubgroupLinearEquiv_single R hHP hΔ hΔP hsurj hstab D b

/-- The inverse of `mapSubgroupRingEquiv` sends a mapped basis element back to `single R D b`. -/
@[simp]
theorem mapSubgroupRingEquiv_symm_single_map (D : HeckeCoset Δ H H) (b : R) :
    (mapSubgroupRingEquiv R hHP hΔ hΔP hsurj hstab).symm
        (single R (D.map hΔ (hHP ▸ inf_le_left) (hHP ▸ inf_le_left)) b) =
      single R D b :=
  (mapSubgroupRingEquiv R hHP hΔ hΔP hsurj hstab).injective (by simp)

end RingEquiv

end HeckeCosetModule

end

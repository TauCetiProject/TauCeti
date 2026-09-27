/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.PadicIntegers
public import TauCeti.NumberTheory.Padics.PrincipalUnits
public import TauCeti.RingTheory.Henselian.Basic
public import TauCeti.RingTheory.Henselian.Teichmuller

/-!
# The Teichmüller splitting of `ℤ_pˣ`

The unit group of the `p`-adic integers splits as the direct product of the group `μ_{p-1}` of
`(p - 1)`-st roots of unity and the principal unit group `1 + pℤ_p`:

`ℤ_pˣ ≃ₜ* μ_{p-1} × (1 + pℤ_p)`,

where a unit `u` goes to the Teichmüller representative of its residue class modulo `p`, the
unique root of unity congruent to `u` modulo `p`, together with `u` divided by it, and where the
inverse is multiplication. This is the Teichmüller splitting of the Henselian local ring `ℤ_p`
(`TauCeti.unitsMulEquivRootsOfUnityProdKerResidue`), whose residue field is `ℤ/pℤ`, so that the
kernel of reduction on units is the principal unit group `TauCeti.unitsPrincipal p 1`; the
inverse multiplication map is continuous, and `ℤ_pˣ` is compact, so the splitting is a
topological isomorphism. The first factor `μ_{p-1}` is cyclic of order `p - 1`.

The prime-to-`p` factor `μ_{p-1}` is what keeps a subgroup of `ℤ_pˣ` from being pro-`p`; the
resulting characterization of the pro-`p` subgroups of `ℤ_pˣ` as the subgroups of `1 + pℤ_p`
is `TauCeti.isProP_iff_le_unitsPrincipal_one` in `TauCeti.NumberTheory.Padics.PrincipalUnits`.

## Main declarations

* `TauCeti.isComplement'_rootsOfUnity_unitsPrincipal_one`: `μ_{p-1}` and `1 + pℤ_p` are
  complementary subgroups of `ℤ_pˣ`.
* `TauCeti.padicIntUnitsEquivProd`: the Teichmüller splitting `ℤ_pˣ ≃ₜ* μ_{p-1} × (1 + pℤ_p)`,
  with `TauCeti.padicIntUnitsEquivProd_symm_apply`,
  `TauCeti.coe_padicIntUnitsEquivProd_apply_fst`, `TauCeti.toZMod_padicIntUnitsEquivProd_apply_fst`
  and `TauCeti.coe_padicIntUnitsEquivProd_apply_snd` describing its two components.
* `TauCeti.card_rootsOfUnity_padicInt`: `μ_{p-1}` has `p - 1` elements.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition 5.3 and Proposition 5.7.
* J.-P. Serre, *Corps Locaux*, Chapter II, §4.
-/

public section

open IsLocalRing

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

variable (p) in
/-- **The Teichmüller splitting of `ℤ_pˣ`, as complementary subgroups**: every unit of `ℤ_p` is
uniquely the product of a `(p - 1)`-st root of unity and a principal unit. -/
theorem isComplement'_rootsOfUnity_unitsPrincipal_one :
    (rootsOfUnity (p - 1) ℤ_[p]).IsComplement' (unitsPrincipal p 1) := by
  have h := isComplement'_rootsOfUnity_ker_unitsMap_residue ℤ_[p]
  rwa [PadicInt.card_residueField, ← unitsPrincipal_one_eq_ker_unitsMap_residue] at h

variable (p) in
/-- The Henselian multiplication map transported to roots of unity and principal units. -/
private noncomputable def padicIntUnitsProdMulEquiv :
    rootsOfUnity (p - 1) ℤ_[p] × unitsPrincipal p 1 ≃* ℤ_[p]ˣ :=
  have h₁ : rootsOfUnity (p - 1) ℤ_[p] =
      rootsOfUnity (Nat.card (ResidueField ℤ_[p]) - 1) ℤ_[p] := by
    rw [PadicInt.card_residueField]
  (MulEquiv.prodCongr (MulEquiv.subgroupCongr h₁)
    (MulEquiv.subgroupCongr (unitsPrincipal_one_eq_ker_unitsMap_residue p))).trans
    (unitsMulEquivRootsOfUnityProdKerResidue ℤ_[p]).symm

/-- Transport changes the membership proofs, leaving the underlying units unchanged. -/
private theorem padicIntUnitsProdMulEquiv_apply
    (x : rootsOfUnity (p - 1) ℤ_[p] × unitsPrincipal p 1) :
    padicIntUnitsProdMulEquiv p x = x.1 * x.2 := by
  simp only [padicIntUnitsProdMulEquiv, MulEquiv.trans_apply,
    unitsMulEquivRootsOfUnityProdKerResidue_symm_apply]
  rfl

/-- The inverse has the same underlying components as the Henselian splitting. -/
private theorem padicIntUnitsProdMulEquiv_symm_apply (u : ℤ_[p]ˣ) :
    (padicIntUnitsProdMulEquiv p).symm u =
      (⟨(unitsMulEquivRootsOfUnityProdKerResidue ℤ_[p] u).1, by
          simpa only [PadicInt.card_residueField] using
            (unitsMulEquivRootsOfUnityProdKerResidue ℤ_[p] u).1.2⟩,
        ⟨(unitsMulEquivRootsOfUnityProdKerResidue ℤ_[p] u).2, by
          rw [unitsPrincipal_one_eq_ker_unitsMap_residue]
          exact (unitsMulEquivRootsOfUnityProdKerResidue ℤ_[p] u).2.2⟩) := by
  apply (padicIntUnitsProdMulEquiv p).injective
  rw [MulEquiv.apply_symm_apply, padicIntUnitsProdMulEquiv_apply]
  simpa only [unitsMulEquivRootsOfUnityProdKerResidue_symm_apply] using
    ((unitsMulEquivRootsOfUnityProdKerResidue ℤ_[p]).symm_apply_apply u).symm

variable (p) in
/-- **The Teichmüller splitting of `ℤ_pˣ`**, `ℤ_pˣ ≃ₜ* μ_{p-1} × (1 + pℤ_p)`: a unit `u` goes to
the unique `(p - 1)`-st root of unity congruent to `u` modulo `p` together with `u` divided by it,
and the inverse is multiplication. This is the Teichmüller splitting
`TauCeti.unitsMulEquivRootsOfUnityProdKerResidue` of the Henselian local ring `ℤ_p`, with the
residue field of cardinality `p` and the kernel of reduction identified with `1 + pℤ_p`, made
topological. -/
noncomputable def padicIntUnitsEquivProd :
    ℤ_[p]ˣ ≃ₜ* rootsOfUnity (p - 1) ℤ_[p] × unitsPrincipal p 1 :=
  have : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩
  have : CompactSpace (unitsPrincipal p 1) :=
    isCompact_iff_compactSpace.mp (isClosed_unitsPrincipal p 1).isCompact
  let e := padicIntUnitsProdMulEquiv p
  -- Multiplication is continuous, and a continuous bijection from a compact space to a Hausdorff
  -- space is a homeomorphism.
  have he : Continuous e :=
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).congr fun x ↦
        (padicIntUnitsProdMulEquiv_apply x).symm
  (ContinuousMulEquiv.mk e he (he.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv))).symm

/-- The inverse of the Teichmüller splitting of `ℤ_pˣ` is multiplication, `(ζ, v) ↦ ζ * v`. -/
@[simp]
theorem padicIntUnitsEquivProd_symm_apply (x : rootsOfUnity (p - 1) ℤ_[p] × unitsPrincipal p 1) :
    (padicIntUnitsEquivProd p).symm x = x.1 * x.2 := by
  simpa only [padicIntUnitsEquivProd, ContinuousMulEquiv.symm_symm,
    ContinuousMulEquiv.coe_mk] using padicIntUnitsProdMulEquiv_apply x

/-- The Teichmüller splitting is the inverse of the transported multiplication map. -/
private theorem padicIntUnitsEquivProd_apply (u : ℤ_[p]ˣ) :
    padicIntUnitsEquivProd p u = (padicIntUnitsProdMulEquiv p).symm u := by
  apply (padicIntUnitsProdMulEquiv p).injective
  rw [MulEquiv.apply_symm_apply, padicIntUnitsProdMulEquiv_apply,
    ← padicIntUnitsEquivProd_symm_apply, ContinuousMulEquiv.symm_apply_apply]

/-- The root-of-unity component of a unit `u` is the Teichmüller representative of its residue
class modulo `p`. -/
@[simp]
theorem coe_padicIntUnitsEquivProd_apply_fst (u : ℤ_[p]ˣ) :
    ((padicIntUnitsEquivProd p u).1 : ℤ_[p]ˣ) =
      teichmuller ℤ_[p] (Units.map (residue ℤ_[p] : ℤ_[p] →* ResidueField ℤ_[p]) u) := by
  rw [padicIntUnitsEquivProd_apply, padicIntUnitsProdMulEquiv_symm_apply]
  exact coe_unitsMulEquivRootsOfUnityProdKerResidue_apply_fst ℤ_[p] u

/-- The principal-unit component of a unit `u` is `u` divided by the Teichmüller representative
of its residue class modulo `p`. -/
@[simp]
theorem coe_padicIntUnitsEquivProd_apply_snd (u : ℤ_[p]ˣ) :
    ((padicIntUnitsEquivProd p u).2 : ℤ_[p]ˣ) =
      (teichmuller ℤ_[p] (Units.map (residue ℤ_[p] : ℤ_[p] →* ResidueField ℤ_[p]) u))⁻¹ * u := by
  rw [padicIntUnitsEquivProd_apply, padicIntUnitsProdMulEquiv_symm_apply]
  exact coe_unitsMulEquivRootsOfUnityProdKerResidue_apply_snd ℤ_[p] u

/-- The root-of-unity component of a unit `u` is congruent to `u` modulo `p`. -/
-- Not a `simp` lemma: `coe_padicIntUnitsEquivProd_apply_fst` rewrites its left-hand side.
theorem toZMod_padicIntUnitsEquivProd_apply_fst (u : ℤ_[p]ˣ) :
    PadicInt.toZMod (((padicIntUnitsEquivProd p u).1 : ℤ_[p]ˣ) : ℤ_[p]) =
      PadicInt.toZMod (u : ℤ_[p]) := by
  have h := mem_unitsPrincipal_one_iff_toZMod.mp (padicIntUnitsEquivProd p u).2.2
  have hu := (padicIntUnitsEquivProd p).symm_apply_apply u
  rw [padicIntUnitsEquivProd_symm_apply] at hu
  conv_rhs => rw [← hu, Units.val_mul, map_mul, h, mul_one]

variable (p) in
/-- The group `μ_{p-1}` of `(p - 1)`-st roots of unity of `ℤ_p` has `p - 1` elements. -/
theorem card_rootsOfUnity_padicInt : Nat.card (rootsOfUnity (p - 1) ℤ_[p]) = p - 1 := by
  have h := card_rootsOfUnity ℤ_[p]
  rwa [PadicInt.card_residueField] at h

end TauCeti

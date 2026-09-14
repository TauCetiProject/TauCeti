/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Finite.RootsOfUnity
public import TauCeti.NumberTheory.LocalField.Henselian
public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import TauCeti.RingTheory.RootsOfUnity.Henselian

/-!
# The Teichmüller lift of a nonarchimedean local field

For a nonarchimedean local field `K` with residue field `𝓀[K]` of cardinality `q`, reduction
modulo the maximal ideal has a canonical multiplicative section

`TauCeti.teichmuller K : 𝓀[K]ˣ →* 𝒪[K]ˣ`,

the **Teichmüller lift**: `teichmuller K α` is the unique unit of `𝒪[K]` that reduces to `α` and
satisfies `x ^ (q - 1) = 1`. Its image is exactly the group `μ_{q-1}` of `(q-1)`-st roots of
unity, which reduction therefore identifies with `𝓀[K]ˣ`.

The lift is the standard device for choosing multiplicative representatives of the residue
field, and it carries the prime-to-`p` torsion of `𝒪[K]ˣ`: it is what splits the reduction map
`𝒪[K]ˣ → 𝓀[K]ˣ`, whose kernel is the pro-`p` group of principal units.

The construction is Hensel's lemma applied to `X ^ (q - 1) - 1`, packaged in
`TauCeti.rootsOfUnityEquivResidueField`: the integer ring of a local field is a Henselian local
domain, and `q - 1` is invertible in it because it reduces to `-1`.

## Implementation notes

The lift is built from Hensel's lemma rather than from Mathlib's `Perfection.teichmuller`, which
produces a map out of the perfection of `R ⧸ I` for an `I`-adically complete ring `R` with
`p ∈ I`. The route taken here needs no characteristic hypothesis and no perfection, and it
delivers the uniqueness characterization below directly.

## Main definitions

* `TauCeti.teichmuller`: the Teichmüller lift `𝓀[K]ˣ →* 𝒪[K]ˣ`.
* `TauCeti.rootsOfUnityEquivResidueFieldUnits` and
  `TauCeti.rootsOfUnityFieldEquivResidueFieldUnits`: reduction identifies `μ_{q-1}`, inside
  `𝒪[K]ˣ` and inside `Kˣ`, with `𝓀[K]ˣ`.

## Main results

* `TauCeti.residue_teichmuller`: the Teichmüller lift is a section of reduction.
* `TauCeti.eq_teichmuller` and `TauCeti.eq_teichmuller_of_residue_eq`: a `(q-1)`-torsion lift of
  `α` is the Teichmüller lift, so it is the unique `(q-1)`-torsion-valued section.
* `TauCeti.range_teichmuller`: its image is `μ_{q-1} ⊆ 𝒪[K]ˣ`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

noncomputable section

open IsLocalRing ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- One less than the residue cardinality is invertible in `𝒪[K]`: it reduces to `-1`. -/
theorem isUnit_natCard_residueField_sub_one :
    IsUnit ((Nat.card 𝓀[K] - 1 : ℕ) : 𝒪[K]) := by
  rw [← residue_ne_zero_iff_isUnit, map_natCast, natCast_natCard_sub_one_eq_neg_one,
    neg_ne_zero]
  exact one_ne_zero

/-- **Reduction identifies the `(q-1)`-st roots of unity of `𝒪[K]` with `𝓀[K]ˣ`**, where `q` is
the residue cardinality. -/
def rootsOfUnityEquivResidueFieldUnits :
    rootsOfUnity (Nat.card 𝓀[K] - 1) 𝒪[K] ≃* 𝓀[K]ˣ :=
  (rootsOfUnityEquivResidueField (isUnit_natCard_residueField_sub_one K)).trans
    (rootsOfUnityEquivUnits 𝓀[K])

/-- The value of `rootsOfUnityEquivResidueFieldUnits` is the reduction of the root of unity. -/
@[simp]
theorem coe_rootsOfUnityEquivResidueFieldUnits
    (ζ : rootsOfUnity (Nat.card 𝓀[K] - 1) 𝒪[K]) :
    ((rootsOfUnityEquivResidueFieldUnits K ζ : 𝓀[K]ˣ) : 𝓀[K]) =
      residue 𝒪[K] ((ζ : 𝒪[K]ˣ) : 𝒪[K]) := by
  have h : rootsOfUnityEquivResidueFieldUnits K ζ =
      rootsOfUnityEquivUnits 𝓀[K]
        (rootsOfUnityEquivResidueField (isUnit_natCard_residueField_sub_one K) ζ) := (rfl)
  rw [h, rootsOfUnityEquivUnits_apply]
  exact coe_rootsOfUnityEquivResidueField _ ζ

/-- The **Teichmüller lift** of a nonarchimedean local field: the multiplicative section of
reduction that sends a unit of the residue field to the unique `(q-1)`-st root of unity of
`𝒪[K]` above it. -/
def teichmuller : 𝓀[K]ˣ →* 𝒪[K]ˣ :=
  (rootsOfUnity (Nat.card 𝓀[K] - 1) 𝒪[K]).subtype.comp
    (rootsOfUnityEquivResidueFieldUnits K).symm.toMonoidHom

/-- The Teichmüller lift, read off the identification of `μ_{q-1}` with `𝓀[K]ˣ`. -/
theorem teichmuller_apply (α : 𝓀[K]ˣ) :
    teichmuller K α = ((rootsOfUnityEquivResidueFieldUnits K).symm α : 𝒪[K]ˣ) :=
  (rfl)

/-- The Teichmüller lift takes values in the `(q-1)`-torsion. -/
@[simp]
theorem teichmuller_pow (α : 𝓀[K]ˣ) :
    teichmuller K α ^ (@Fintype.card 𝓀[K] (Fintype.ofFinite 𝓀[K]) - 1) = 1 := by
  rw [teichmuller_apply]
  rw [← @Nat.card_eq_fintype_card 𝓀[K] (Fintype.ofFinite 𝓀[K])]
  exact ((rootsOfUnityEquivResidueFieldUnits K).symm α).2

/-- The Teichmüller lift, viewed in `𝒪[K]ˣ`, belongs to the group of `(q-1)`-st roots of unity
indexed by the residue field's `Nat.card`. -/
theorem teichmuller_mem_rootsOfUnity (α : 𝓀[K]ˣ) :
    teichmuller K α ∈ rootsOfUnity (Nat.card 𝓀[K] - 1) 𝒪[K] := by
  rw [teichmuller_apply]
  exact ((rootsOfUnityEquivResidueFieldUnits K).symm α).2

/-- **The Teichmüller lift is a section of reduction.** -/
@[simp]
theorem residue_teichmuller (α : 𝓀[K]ˣ) :
    residue 𝒪[K] ((teichmuller K α : 𝒪[K]ˣ) : 𝒪[K]) = (α : 𝓀[K]) := by
  have h := coe_rootsOfUnityEquivResidueFieldUnits K
    ((rootsOfUnityEquivResidueFieldUnits K).symm α)
  rw [MulEquiv.apply_symm_apply] at h
  rw [teichmuller_apply]
  exact h.symm

/-- The Teichmüller lift is a section of reduction, in unit-group form. -/
@[simp]
theorem unitsMap_residue_teichmuller (α : 𝓀[K]ˣ) :
    Units.map (residue 𝒪[K]) (teichmuller K α) = α :=
  Units.ext (residue_teichmuller K α)

/-- The Teichmüller lift is a section of reduction, as an identity of homomorphisms. -/
theorem unitsMap_residue_comp_teichmuller :
    ((Units.map (residue 𝒪[K]).toMonoidHom).comp (teichmuller K)) = .id 𝓀[K]ˣ :=
  MonoidHom.ext (unitsMap_residue_teichmuller K)

/-- The Teichmüller lift is injective: it is a section of reduction. -/
theorem teichmuller_injective : Function.Injective (teichmuller K) := fun α β h ↦ by
  have h' := congrArg (fun u : 𝒪[K]ˣ ↦ residue 𝒪[K] (u : 𝒪[K])) h
  simpa only [residue_teichmuller, Units.ext_iff] using h'

/-- **The Teichmüller lift is the unique `(q-1)`-torsion lift.** A unit of `𝒪[K]` killed by
`q - 1` that reduces to `α` is `teichmuller K α`. -/
theorem eq_teichmuller {α : 𝓀[K]ˣ} {u : 𝒪[K]ˣ} (hpow : u ^ (Nat.card 𝓀[K] - 1) = 1)
    (hres : residue 𝒪[K] (u : 𝒪[K]) = (α : 𝓀[K])) : u = teichmuller K α := by
  have hmem : u ∈ rootsOfUnity (Nat.card 𝓀[K] - 1) 𝒪[K] := hpow
  have h : (⟨u, hmem⟩ : rootsOfUnity (Nat.card 𝓀[K] - 1) 𝒪[K]) =
      ⟨teichmuller K α, teichmuller_mem_rootsOfUnity K α⟩ := by
    refine rootsOfUnityResidue_injective (isUnit_natCard_residueField_sub_one K) ?_
    ext
    simp [hres]
  exact congrArg (fun x : rootsOfUnity (Nat.card 𝓀[K] - 1) 𝒪[K] ↦ (x : 𝒪[K]ˣ)) h

/-- **The Teichmüller lift is the unique `(q-1)`-torsion-valued section of reduction.** -/
theorem eq_teichmuller_of_residue_eq {s : 𝓀[K]ˣ → 𝒪[K]ˣ}
    (hpow : ∀ α, s α ^ (Nat.card 𝓀[K] - 1) = 1)
    (hres : ∀ α, residue 𝒪[K] ((s α : 𝒪[K])) = (α : 𝓀[K])) : s = teichmuller K :=
  funext fun α ↦ eq_teichmuller K (hpow α) (hres α)

/-- **The image of the Teichmüller lift is `μ_{q-1}`.** -/
theorem range_teichmuller :
    (teichmuller K).range = rootsOfUnity (Nat.card 𝓀[K] - 1) 𝒪[K] := by
  ext u
  refine ⟨?_, fun hu ↦ ⟨rootsOfUnityEquivResidueFieldUnits K ⟨u, hu⟩, ?_⟩⟩
  · rintro ⟨α, rfl⟩
    exact teichmuller_mem_rootsOfUnity K α
  · rw [teichmuller_apply, MulEquiv.symm_apply_apply]

/-! ### Roots of unity of the field itself

Every root of unity of `K` has valuation one, so the roots of unity of `K` are exactly those of
`𝒪[K]`. -/

/-- **The roots of unity of a nonarchimedean local field are those of its integer ring**: a root
of unity has valuation one, so it is a unit of `𝒪[K]`. -/
theorem map_rootsOfUnity_integer {n : ℕ} (hn : n ≠ 0) :
    (rootsOfUnity n 𝒪[K]).map (Units.map (Subring.subtype 𝒪[K]).toMonoidHom) =
      rootsOfUnity n K := by
  refine le_antisymm (map_rootsOfUnity _ n) fun ζ hζ ↦ ?_
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hζ⟩
  have hval : valuation K (ζ : K) = 1 :=
    (normalizedValuation_eq_one_iff ζ).mp (normalizedValuation_eq_one_of_isOfFinOrder hfin)
  have hu : IsUnit (⟨(ζ : K), (Valuation.mem_integer_iff (valuation K) (ζ : K)).mpr hval.le⟩
      : 𝒪[K]) := (Valuation.integer.integers (valuation K)).isUnit_of_one' hval
  have hcoe : ((hu.unit : 𝒪[K]) : K) = (ζ : K) := congrArg Subtype.val hu.unit_spec
  refine ⟨hu.unit, ?_, Units.ext hcoe⟩
  rw [SetLike.mem_coe, mem_rootsOfUnity']
  apply Subtype.ext
  push_cast [hcoe]
  exact_mod_cast (mem_rootsOfUnity' n ζ).mp hζ

/-- The `n`-th roots of unity of `𝒪[K]` and of `K` agree, for `n ≠ 0`. -/
def rootsOfUnityIntegerEquiv {n : ℕ} (hn : n ≠ 0) :
    rootsOfUnity n 𝒪[K] ≃* rootsOfUnity n K :=
  (Subgroup.equivMapOfInjective _ _
      (Units.map_injective (f := (Subring.subtype 𝒪[K]).toMonoidHom) Subtype.val_injective)).trans
    (MulEquiv.subgroupCongr (map_rootsOfUnity_integer K hn))

/-- The equivalence between roots of unity in `𝒪[K]` and `K` is induced by inclusion. -/
@[simp]
theorem coe_rootsOfUnityIntegerEquiv {n : ℕ} (hn : n ≠ 0) (ζ : rootsOfUnity n 𝒪[K]) :
    (((rootsOfUnityIntegerEquiv K hn ζ : rootsOfUnity n K) : Kˣ) : K) =
      (((ζ : 𝒪[K]ˣ) : 𝒪[K]) : K) := by
  rfl

/-- **Reduction identifies the `(q-1)`-st roots of unity of `K` with `𝓀[K]ˣ`**: the group
`μ_{q-1}(K)` is isomorphic to the multiplicative group of the residue field. -/
def rootsOfUnityFieldEquivResidueFieldUnits :
    rootsOfUnity (Nat.card 𝓀[K] - 1) K ≃* 𝓀[K]ˣ :=
  (rootsOfUnityIntegerEquiv K
      (Nat.sub_ne_zero_of_lt Finite.one_lt_card)).symm.trans
    (rootsOfUnityEquivResidueFieldUnits K)

/-- The field-level roots-of-unity equivalence applies the inverse integral equivalence and then
reduces the resulting root of unity modulo the maximal ideal. -/
@[simp]
theorem coe_rootsOfUnityFieldEquivResidueFieldUnits
    (ζ : rootsOfUnity (Nat.card 𝓀[K] - 1) K) :
    ((rootsOfUnityFieldEquivResidueFieldUnits K ζ : 𝓀[K]ˣ) : 𝓀[K]) =
      residue 𝒪[K]
        ((((rootsOfUnityIntegerEquiv K
          (Nat.sub_ne_zero_of_lt Finite.one_lt_card)).symm ζ :
            rootsOfUnity (Nat.card 𝓀[K] - 1) 𝒪[K]) : 𝒪[K]ˣ) : 𝒪[K]) := by
  exact coe_rootsOfUnityEquivResidueFieldUnits K _

end TauCeti

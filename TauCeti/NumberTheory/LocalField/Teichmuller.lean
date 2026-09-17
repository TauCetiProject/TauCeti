/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Finite.RootsOfUnity
public import TauCeti.NumberTheory.LocalField.Henselian
public import TauCeti.RingTheory.RootsOfUnity.Henselian
public import TauCeti.RingTheory.RootsOfUnity.ValuativeRel
public import Mathlib.RingTheory.Teichmuller

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
delivers the uniqueness characterization below directly. The zero-preserving extension
`teichmullerLift` is instead obtained from `Perfection.teichmuller₀`, and
`coe_teichmuller_apply` shows that the two constructions agree on units.

## Main definitions

* `TauCeti.teichmuller`: the Teichmüller lift `𝓀[K]ˣ →* 𝒪[K]ˣ`.
* `TauCeti.teichmullerLift`: its zero-preserving extension `𝓀[K] →*₀ 𝒪[K]`.
* `TauCeti.rootsOfUnityEquivResidueFieldUnits` and
  `TauCeti.rootsOfUnityFieldEquivResidueFieldUnits`: reduction identifies `μ_{q-1}`, inside
  `𝒪[K]ˣ` and inside `Kˣ`, with `𝓀[K]ˣ`.

## Main results

* `TauCeti.residue_teichmuller`: the Teichmüller lift is a section of reduction.
* `TauCeti.eq_teichmuller` and `TauCeti.eq_teichmuller_of_residue_eq`: a `(q-1)`-torsion lift of
  `α` is the Teichmüller lift, so it is the unique `(q-1)`-torsion-valued section.
* `TauCeti.eq_teichmuller_iff`: a unit is `teichmuller K α` exactly when it reduces to `α` and is
  killed by `q - 1`.
* `TauCeti.eq_teichmullerLift_iff`: an element of `𝒪[K]` is `teichmullerLift K a` exactly when
  it reduces to `a` and is fixed by the `q`-th power map.
* `TauCeti.teichmuller_unique` and `TauCeti.teichmullerLift_unique`: the Teichmüller lift is the
  only multiplicative section of reduction, on unit groups and on the whole residue field.
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
-- This is not a `simp` lemma because `Nat.card_eq_fintype_card` rewrites its left-hand side.
theorem teichmuller_pow (α : 𝓀[K]ˣ) : teichmuller K α ^ (Nat.card 𝓀[K] - 1) = 1 := by
  rw [teichmuller_apply]
  exact ((rootsOfUnityEquivResidueFieldUnits K).symm α).2

/-- The simplifier-normalized form of the characteristic torsion equation for the Teichmüller
lift. -/
@[simp]
theorem teichmuller_pow_fintype_card (α : 𝓀[K]ˣ) :
    teichmuller K α ^ (@Fintype.card 𝓀[K] (Fintype.ofFinite 𝓀[K]) - 1) = 1 := by
  rw [← @Nat.card_eq_fintype_card 𝓀[K] (Fintype.ofFinite 𝓀[K])]
  exact teichmuller_pow K α

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

/-- The inverse field-level roots-of-unity equivalence is the inclusion of the Teichmüller
lift into the field. -/
@[simp]
theorem coe_rootsOfUnityFieldEquivResidueFieldUnits_symm_apply (α : 𝓀[K]ˣ) :
    ((((rootsOfUnityFieldEquivResidueFieldUnits K).symm α :
        rootsOfUnity (Nat.card 𝓀[K] - 1) K) : Kˣ) : K) =
      (((teichmuller K α : 𝒪[K]ˣ) : 𝒪[K]) : K) := by
  rw [rootsOfUnityFieldEquivResidueFieldUnits, MulEquiv.symm_trans_apply,
    teichmuller_apply]
  exact coe_rootsOfUnityIntegerEquiv K (Nat.sub_ne_zero_of_lt Finite.one_lt_card) _

/-- **The Teichmüller lift is characterized by its residue and torsion.** A unit of `𝒪[K]` is
`teichmuller K α` exactly when it reduces to `α` and is killed by `q - 1`. -/
theorem eq_teichmuller_iff {α : 𝓀[K]ˣ} {u : 𝒪[K]ˣ} :
    u = teichmuller K α ↔
      residue 𝒪[K] (u : 𝒪[K]) = (α : 𝓀[K]) ∧ u ^ (Nat.card 𝓀[K] - 1) = 1 := by
  refine ⟨?_, fun h ↦ eq_teichmuller K h.2 h.1⟩
  rintro rfl
  exact ⟨residue_teichmuller K α, teichmuller_pow K α⟩

/-- **The Teichmüller lift is the unique multiplicative section of reduction** on unit groups.
The torsion condition of `eq_teichmuller_of_residue_eq` is automatic for a homomorphism, since
`𝓀[K]ˣ` is killed by `q - 1`. -/
theorem teichmuller_unique (f : 𝓀[K]ˣ →* 𝒪[K]ˣ)
    (hsection : ∀ α, residue 𝒪[K] ((f α : 𝒪[K]ˣ) : 𝒪[K]) = (α : 𝓀[K])) :
    f = teichmuller K :=
  MonoidHom.ext fun α ↦ eq_teichmuller K
    (by rw [← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]) (hsection α)

-- Provenance: this is the finite-residue-field specialization of Mathlib's
-- `Perfection.teichmuller₀`, using `PerfectionMap.id` to identify a perfect field with its
-- perfection.
/-- The zero-preserving **Teichmüller lift** `𝓀[K] →*₀ 𝒪[K]`, extending `teichmuller K` by
`0 ↦ 0`. -/
def teichmullerLift : 𝓀[K] →*₀ 𝒪[K] := by
  let p := ringChar 𝓀[K]
  letI : Fact p.Prime := ⟨CharP.prime_ringChar 𝓀[K]⟩
  letI : PerfectRing 𝓀[K] p := PerfectField.toPerfectRing p
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  have h : Perfection 𝓀[K] p →*₀ 𝒪[K] := Perfection.teichmuller₀ p 𝓂[K]
  exact h.comp (PerfectionMap.id p 𝓀[K]).equiv.toMonoidWithZeroHom

/-- The zero-preserving Teichmüller lift is a section of reduction. -/
@[simp]
theorem residue_teichmullerLift (a : 𝓀[K]) : residue 𝒪[K] (teichmullerLift K a) = a := by
  let p := ringChar 𝓀[K]
  let _ : Fact p.Prime := ⟨CharP.prime_ringChar 𝓀[K]⟩
  let _ : PerfectRing 𝓀[K] p := PerfectField.toPerfectRing p
  let _ := IsTopologicalAddGroup.rightUniformSpace K
  let _ := isUniformAddGroup_of_addCommGroup (G := K)
  exact (Perfection.mk_teichmuller₀ ((PerfectionMap.id p 𝓀[K]).equiv a)).trans
    (PerfectionMap.comp_equiv (PerfectionMap.id p 𝓀[K]) a)

/-- Each Teichmüller representative is fixed by the `q`-th power map.

This is not a `simp` lemma: `simp` normalizes `Nat.card 𝓀[K]` to `Fintype.card 𝓀[K]`, so the
left-hand side is not in `simp`-normal form. -/
theorem teichmullerLift_pow_natCard (a : 𝓀[K]) :
    teichmullerLift K a ^ Nat.card 𝓀[K] = teichmullerLift K a := by
  classical
  let _ := Fintype.ofFinite 𝓀[K]
  rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

/-- The simplifier-normalized form of the characteristic Frobenius equation for the
zero-preserving Teichmüller lift. -/
@[simp]
theorem teichmullerLift_pow_fintype_card (a : 𝓀[K]) :
    teichmullerLift K a ^ @Fintype.card 𝓀[K] (Fintype.ofFinite 𝓀[K]) = teichmullerLift K a := by
  rw [← @Nat.card_eq_fintype_card 𝓀[K] (Fintype.ofFinite 𝓀[K])]
  exact teichmullerLift_pow_natCard K a

/-- On units, the zero-preserving Teichmüller lift is `teichmuller K`. -/
theorem coe_teichmuller_apply (α : 𝓀[K]ˣ) :
    ((teichmuller K α : 𝒪[K]ˣ) : 𝒪[K]) = teichmullerLift K (α : 𝓀[K]) := by
  have hsection (β : 𝓀[K]ˣ) :
      residue 𝒪[K]
          ((Units.map (teichmullerLift K : 𝓀[K] →* 𝒪[K]) β : 𝒪[K]ˣ) : 𝒪[K]) =
        (β : 𝓀[K]) := by
    rw [Units.coe_map, MonoidHom.coe_coe]
    exact residue_teichmullerLift K β
  have h : Units.map (teichmullerLift K : 𝓀[K] →* 𝒪[K]) α = teichmuller K α :=
    congrArg (fun f : 𝓀[K]ˣ →* 𝒪[K]ˣ ↦ f α)
      (teichmuller_unique K (Units.map (teichmullerLift K : 𝓀[K] →* 𝒪[K])) hsection)
  rw [← h, Units.coe_map, MonoidHom.coe_coe]

/-- **The zero-preserving Teichmüller lift is characterized by its residue and Frobenius
equation.** An element of `𝒪[K]` is `teichmullerLift K a` exactly when it reduces to `a` and is
fixed by the `q`-th power map. -/
theorem eq_teichmullerLift_iff {a : 𝓀[K]} {x : 𝒪[K]} :
    x = teichmullerLift K a ↔ residue 𝒪[K] x = a ∧ x ^ Nat.card 𝓀[K] = x := by
  refine ⟨?_, fun ⟨hres, hpow⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨residue_teichmullerLift K a, teichmullerLift_pow_natCard K a⟩
  rcases eq_or_ne x 0 with rfl | hx
  · rw [← hres, map_zero, map_zero]
  have hq : Nat.card 𝓀[K] ≠ 0 := Nat.card_pos.ne'
  have hq₁ : Nat.card 𝓀[K] - 1 ≠ 0 := Nat.sub_ne_zero_of_lt Finite.one_lt_card
  have hunit : x ^ (Nat.card 𝓀[K] - 1) = 1 :=
    mul_right_cancel₀ hx (by rw [pow_sub_one_mul hq, hpow, one_mul])
  let u := Units.ofPowEqOne x _ hunit hq₁
  have ha : a ≠ 0 := by
    rw [← hres]
    exact (residue_ne_zero_iff_isUnit x).2 u.isUnit
  have h := eq_teichmuller K (α := Units.mk0 a ha) (Units.pow_ofPowEqOne hunit hq₁) hres
  rw [← Units.val_mk0 ha, ← coe_teichmuller_apply, ← h, Units.val_ofPowEqOne]

/-- **The zero-preserving Teichmüller lift is the unique multiplicative section of reduction.** -/
theorem teichmullerLift_unique (f : 𝓀[K] →*₀ 𝒪[K])
    (hsection : ∀ a, residue 𝒪[K] (f a) = a) : f = teichmullerLift K := by
  have hunits : Units.map (f : 𝓀[K] →* 𝒪[K]) = teichmuller K :=
    teichmuller_unique K _ fun α ↦ hsection α
  ext a
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, map_zero]
  · simpa [coe_teichmuller_apply] using
      congrArg (fun g : 𝓀[K]ˣ →* 𝒪[K]ˣ ↦ ((g (Units.mk0 a ha) : 𝒪[K]ˣ) : 𝒪[K])) hunits

end TauCeti

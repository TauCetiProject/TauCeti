/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Factorization
public import TauCeti.NumberTheory.LocalField.Unramified.Maximal

/-!
# The residue degree and the unramified part of a subextension

Let `K` be a nonarchimedean local field and `Ω` an extension of `K`. A subextension `L` of `Ω / K`
carries no topology or valuation of its own; when `L / K` is finite, the structures
`TauCeti.finiteIntermediateFieldValuativeRel` and `TauCeti.finiteIntermediateFieldTopology` make it
a nonarchimedean local field extending `K`. This file extends the residue degree
`TauCeti.inertiaDegree K L` to arbitrary subextensions, as `IntermediateField.inertiaDegree L`,
with the junk value `0` when `L / K` is infinite; this is the same totalization as
`IntermediateField.discriminantExponent`.

For `Ω` separably closed, the maximal unramified subextension of a finite subextension is then read
inside `Ω`: the intersection `L ⊓ K^ur` of `L` with the maximal unramified extension is the
unramified extension `K_f = TauCeti.unramifiedExtension K Ω f` of degree `f = f(L / K)`, and the
unramified extensions contained in `L` are exactly the `K_g` with `g ∣ f`. This is the form of
`TauCeti.eq_unramifiedExtension_inertiaDegree_iff` that applies to subextensions of a fixed
separable closure: with the invariance of `f` under `K`-isomorphism, it lets the subextensions of
residue degree `f` be studied as extensions of the single field `K_f`, as in Bhargava's mass formula
for étale algebras.

## Main definitions

* `IntermediateField.inertiaDegree L`: the residue degree `f(L / K)` of a finite subextension, `0`
  for an infinite one.

## Main results

* `IntermediateField.inertiaDegree_eq_of_algEquiv`: the residue degree is an invariant of the
  `K`-isomorphism class, junk case included.
* `IntermediateField.inertiaDegree_dvd_finrank`: `f(L / K)` divides `[L : K]`.
* `IntermediateField.unramifiedExtension_inertiaDegree_le`: `K_{f(L/K)} ≤ L`.
* `IntermediateField.unramifiedExtension_le_iff_dvd_inertiaDegree`: for `Ω` separably closed and
  `g ≠ 0`, `K_g ≤ L` exactly when `g ∣ f(L / K)`.
* `IntermediateField.inf_maximalUnramifiedExtension`: for `Ω` separably closed,
  `L ⊓ K^ur = K_{f(L/K)}`.
* `IntermediateField.finrank_inf_maximalUnramifiedExtension`: `[L ⊓ K^ur : K] = f(L / K)`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
-/

public section
noncomputable section

open ValuativeRel TauCeti

namespace IntermediateField

variable {K Ω : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]

open Classical in
/-- The residue degree `f(L / K)` of a subextension `L` of `Ω / K`: for `L / K` finite,
`TauCeti.inertiaDegree K L` for the local-field structure `finiteIntermediateFieldValuativeRel` and
`finiteIntermediateFieldTopology`; for `L / K` infinite, the junk value `0`. -/
def inertiaDegree (L : IntermediateField K Ω) : ℕ :=
  if _ : Module.Finite K L then
    letI := finiteIntermediateFieldValuativeRel K Ω L
    letI := finiteIntermediateFieldTopology K Ω L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K Ω L
    haveI := finiteIntermediateField_valuativeExtension K Ω L
    TauCeti.inertiaDegree K L
  else 0

/-- On a finite subextension, `IntermediateField.inertiaDegree` is `TauCeti.inertiaDegree` for the
local-field structure `finiteIntermediateFieldValuativeRel` and
`finiteIntermediateFieldTopology`. -/
theorem inertiaDegree_eq (L : IntermediateField K Ω) [hfin : Module.Finite K L] :
    L.inertiaDegree =
      (letI := finiteIntermediateFieldValuativeRel K Ω L
      letI := finiteIntermediateFieldTopology K Ω L
      haveI := finiteIntermediateField_isNonarchimedeanLocalField K Ω L
      haveI := finiteIntermediateField_valuativeExtension K Ω L
      TauCeti.inertiaDegree K L) :=
  dite_eq_left hfin

/-- On an infinite subextension, `IntermediateField.inertiaDegree` takes the junk value `0`. -/
theorem inertiaDegree_of_not_finite {L : IntermediateField K Ω} (h : ¬ Module.Finite K L) :
    L.inertiaDegree = 0 :=
  dite_eq_right h

/-- The residue degree of a finite subextension is positive. -/
theorem inertiaDegree_pos (L : IntermediateField K Ω) [Module.Finite K L] :
    0 < L.inertiaDegree := by
  rw [inertiaDegree_eq]
  let _ := finiteIntermediateFieldValuativeRel K Ω L
  let _ := finiteIntermediateFieldTopology K Ω L
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω L
  have := finiteIntermediateField_valuativeExtension K Ω L
  exact TauCeti.inertiaDegree_pos

/-- The residue degree divides the degree, with cofactor the ramification index. The junk case is
included, both sides being `0` for an infinite subextension. -/
theorem inertiaDegree_dvd_finrank (L : IntermediateField K Ω) :
    L.inertiaDegree ∣ Module.finrank K L := by
  by_cases hL : Module.Finite K L
  · rw [inertiaDegree_eq]
    let _ := finiteIntermediateFieldValuativeRel K Ω L
    let _ := finiteIntermediateFieldTopology K Ω L
    have := finiteIntermediateField_isNonarchimedeanLocalField K Ω L
    have := finiteIntermediateField_valuativeExtension K Ω L
    exact Dvd.intro_left _ (ramificationIndex_mul_inertiaDegree K L)
  · rw [inertiaDegree_of_not_finite hL, Module.finrank_of_not_finite hL]

/-- The bottom subextension has residue degree `1`. -/
@[simp]
theorem inertiaDegree_bot : (⊥ : IntermediateField K Ω).inertiaDegree = 1 := by
  simpa using inertiaDegree_dvd_finrank (⊥ : IntermediateField K Ω)

/-- **The residue degree is an invariant of the `K`-isomorphism class**, junk case included. -/
theorem inertiaDegree_eq_of_algEquiv {L M : IntermediateField K Ω} (e : L ≃ₐ[K] M) :
    L.inertiaDegree = M.inertiaDegree := by
  by_cases hL : Module.Finite K L
  · have : Module.Finite K M := Module.Finite.equiv e.toLinearEquiv
    rw [inertiaDegree_eq, inertiaDegree_eq]
    let _ := finiteIntermediateFieldValuativeRel K Ω L
    let _ := finiteIntermediateFieldTopology K Ω L
    have := finiteIntermediateField_isNonarchimedeanLocalField K Ω L
    have := finiteIntermediateField_valuativeExtension K Ω L
    let _ := finiteIntermediateFieldValuativeRel K Ω M
    let _ := finiteIntermediateFieldTopology K Ω M
    have := finiteIntermediateField_isNonarchimedeanLocalField K Ω M
    have := finiteIntermediateField_valuativeExtension K Ω M
    -- `e` restricts to the rings of integers, so the residue fields, of cardinalities `q ^ f`,
    -- are isomorphic.
    refine Nat.pow_right_injective (Finite.one_lt_card (α := 𝓀[K])) ?_
    simp only [← natCard_residueField]
    exact Nat.card_congr
      (IsLocalRing.ResidueField.mapEquiv e.integerRingEquiv.toRingEquiv).toEquiv
  · rw [inertiaDegree_of_not_finite hL,
      inertiaDegree_of_not_finite fun h ↦ hL (Module.Finite.equiv e.symm.toLinearEquiv)]

/-- **The unramified part lies in the subextension**: a finite subextension `L` of `Ω / K`
contains the unramified extension of `K` of degree `f(L / K)` inside `Ω`. -/
theorem unramifiedExtension_inertiaDegree_le (L : IntermediateField K Ω) [Module.Finite K L] :
    unramifiedExtension K Ω L.inertiaDegree ≤ L := by
  have hf := (inertiaDegree_pos L).ne'
  rw [inertiaDegree_eq] at hf ⊢
  let _ := finiteIntermediateFieldValuativeRel K Ω L
  let _ := finiteIntermediateFieldTopology K Ω L
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω L
  have := finiteIntermediateField_valuativeExtension K Ω L
  -- `L` contains a primitive `(q ^ f − 1)`-st root of unity, which generates `K_f`.
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_natCard_pow_inertiaDegree_sub_one K L
  rw [unramifiedExtension_eq_adjoin_simple hf (IsPrimitiveRoot.coe_submonoidClass_iff.2 hζ),
    adjoin_simple_le_iff]
  exact ζ.2

variable [IsSepClosed Ω]

/-- **The unramified extensions inside a subextension**: for `Ω` separably closed, `g ≠ 0` and `L`
finite over `K`, the unramified extension `K_g` of degree `g` lies in `L` exactly when `g` divides
the residue degree `f(L / K)`. -/
theorem unramifiedExtension_le_iff_dvd_inertiaDegree {g : ℕ} (hg : g ≠ 0)
    (L : IntermediateField K Ω) [Module.Finite K L] :
    unramifiedExtension K Ω g ≤ L ↔ g ∣ L.inertiaDegree := by
  refine ⟨fun h ↦ ?_, fun h ↦ (unramifiedExtension_le_of_dvd (inertiaDegree_pos L).ne' h).trans
    (unramifiedExtension_inertiaDegree_le L)⟩
  -- `K_g` contains a primitive `(q ^ g − 1)`-st root of unity, which then lies in `L`.
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_natCard_pow_sub_one (K := K) Ω hg
  have hζL : ζ ∈ L := h (unramifiedExtension_eq_adjoin_simple hg hζ ▸ mem_adjoin_simple_self K ζ)
  rw [inertiaDegree_eq]
  let _ := finiteIntermediateFieldValuativeRel K Ω L
  let _ := finiteIntermediateFieldTopology K Ω L
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω L
  have := finiteIntermediateField_valuativeExtension K Ω L
  exact dvd_inertiaDegree_of_isPrimitiveRoot hg
    ((IsPrimitiveRoot.coe_submonoidClass_iff (ζ := (⟨ζ, hζL⟩ : L))).1 hζ)

/-- **The unramified part of a subextension** is the unramified extension of degree its residue
degree: for `Ω` separably closed and `L` finite over `K`, the intersection of `L` with the maximal
unramified extension `K^ur` is `K_{f(L/K)}`. This is the subfield form of `L^ur ≅ K_f`. -/
theorem inf_maximalUnramifiedExtension (L : IntermediateField K Ω) [Module.Finite K L] :
    L ⊓ maximalUnramifiedExtension K Ω = unramifiedExtension K Ω L.inertiaDegree := by
  refine le_antisymm ?_ (le_inf (unramifiedExtension_inertiaDegree_le L)
    (unramifiedExtension_le_maximalUnramifiedExtension K Ω _))
  -- `E = L ⊓ K^ur` is unramified, hence it is `K_d` for `d = [E : K]`, and `K_d ≤ L` forces
  -- `d ∣ f(L / K)`.
  set E := L ⊓ maximalUnramifiedExtension K Ω
  have : Module.Finite K E :=
    Module.Finite.of_injective (inclusion inf_le_left).toLinearMap (inclusion inf_le_left).injective
  let _ := finiteIntermediateFieldValuativeRel K Ω E
  let _ := finiteIntermediateFieldTopology K Ω E
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω E
  have := finiteIntermediateField_valuativeExtension K Ω E
  have : IsUnramified K E := (le_maximalUnramifiedExtension_iff E).1 inf_le_right
  have hd : Module.finrank K E ≠ 0 := Module.finrank_pos.ne'
  have hE : E = unramifiedExtension K Ω (Module.finrank K E) := E.eq_unramifiedExtension_finrank
  rw [hE]
  refine unramifiedExtension_le_of_dvd (inertiaDegree_pos L).ne' ?_
  exact (unramifiedExtension_le_iff_dvd_inertiaDegree hd L).1 (hE ▸ inf_le_left)

/-- The unramified part `L ⊓ K^ur` of a finite subextension of a separably closed `Ω` has degree
`f(L / K)` over `K`. -/
@[simp]
theorem finrank_inf_maximalUnramifiedExtension (L : IntermediateField K Ω) [Module.Finite K L] :
    Module.finrank K ↥(L ⊓ maximalUnramifiedExtension K Ω) = L.inertiaDegree := by
  rw [inf_maximalUnramifiedExtension, finrank_unramifiedExtension (inertiaDegree_pos L).ne']

end IntermediateField

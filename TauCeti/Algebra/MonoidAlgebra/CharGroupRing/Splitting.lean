/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Lattice
public import TauCeti.RepresentationTheory.GroupAlgebra.CharIdempotent

/-!
# Splitting of commutative group algebras at characters

Let `G` be a finite commutative group and `O` a domain in which `#G` is a unit. Every function on a
set `Ψ` of `O`-valued characters of `G` already belongs to `#G⁻¹ • R_Ψ = R_Ψ`
(`Set.jointEval_surjective`, `Set.charGroupRing_eq_top`), with no roots-of-unity assumption.

When `O` moreover has enough roots of unity of exponent `exp(G)`, joint evaluation at all characters
is also injective (`Set.jointEval_injective`), giving the integral character splitting
`MonoidAlgebra.charEvalEquiv : O[G] ≃ₐ[O] ((G →* Oˣ) → O)` that sends each character idempotent
`TauCeti.charIdempotent χ` to the basis idempotent `Pi.single χ 1`, together with the induced
coefficientwise splitting `MonoidAlgebra.powerSeriesCharEvalEquiv` of `O[G]⟦X⟧`.

## Main definitions

* `MonoidAlgebra.charEvalEquiv`: the `O`-algebra isomorphism `O[G] ≃ₐ[O] ((G →* Oˣ) → O)` when
  `#G` is a unit of the domain `O` and `O` has enough roots of unity for `G`.
* `MonoidAlgebra.powerSeriesCharEvalEquiv`: the induced `O`-algebra isomorphism
  `O[G]⟦X⟧ ≃ₐ[O] ((G →* Oˣ) → O⟦X⟧)`.

## Main results

* `MonoidHom.charEval_charIdempotent`: for `χ, ψ : G →* Oˣ`, `ψ(e_χ) = δ_{χψ}` when `#G` is a unit.
* `Set.jointEval_surjective`, `Set.charGroupRing_eq_top`: when `#G` is a unit in the domain `O`,
  joint evaluation on any character set `Ψ` is surjective.
* `Set.jointEval_univ_bijective`: with enough roots of unity, joint evaluation on `Set.univ` is
  bijective.
* `MonoidAlgebra.charEvalEquiv_charIdempotent`, `MonoidAlgebra.charEvalEquiv_symm_single`,
  `MonoidAlgebra.charEvalEquiv_symm_apply`: interaction of `charEvalEquiv` with character
  idempotents.
-/

public section

section Surjective

variable {O G : Type*} [CommRing O] [IsDomain O] [CommGroup G]

/-- When `#G` is a unit in the domain `O`, evaluating `χ`'s character idempotent at `ψ` gives `1`
for `χ = ψ` and `0` otherwise. -/
theorem MonoidHom.charEval_charIdempotent [Fintype G] [DecidableEq (G →* Oˣ)]
    (hG : IsUnit (Nat.card G : O)) (χ ψ : G →* Oˣ) :
    ψ.charEval (TauCeti.charIdempotent χ) = if χ = ψ then 1 else 0 := by
  rw [TauCeti.charIdempotent_eq_sum, map_smul, map_sum]
  simp only [map_smul, MonoidAlgebra.of_apply, TauCeti.DiagonalizableGroup.point_single_one,
    smul_eq_mul]
  split_ifs with h
  · subst h
    simp only [Nat.card_eq_fintype_card, Units.inv_mul, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] at hG ⊢
    exact Ring.inverse_mul_cancel _ hG
  · have hne : (Units.coeHom O).comp (χ⁻¹ * ψ) ≠ 1 := fun h1 ↦ h <| inv_mul_eq_one.mp <|
      MonoidHom.ext fun a ↦ Units.ext <| by simpa using DFunLike.congr_fun h1 a
    have hsum : ∑ a : G, (((χ a)⁻¹ : Oˣ) : O) * (ψ a : O) = 0 := by
      simpa using sum_hom_units_eq_zero _ hne
    rw [hsum, mul_zero]

/-- When `#G` is a unit in the domain `O`, the joint evaluation `O[G] → (Ψ → O)` on any set `Ψ` of
characters is surjective; no roots-of-unity hypothesis is needed. -/
theorem Set.jointEval_surjective [Finite G] (Ψ : Set (G →* Oˣ)) (hG : IsUnit (Nat.card G : O)) :
    Function.Surjective Ψ.jointEval := by
  intro y
  have hmem : (Nat.card G : O) • (Ring.inverse (Nat.card G : O) • y) ∈ Ψ.charGroupRing :=
    Set.charGroupRing.card_smul_mem Ψ _
  rwa [smul_smul, Ring.mul_inverse_cancel _ hG, one_smul, Set.charGroupRing_def] at hmem

/-- When `#G` is a unit in the domain `O`, the character group ring `R_Ψ` is the full product
`Ψ → O`. -/
theorem Set.charGroupRing_eq_top [Finite G] (Ψ : Set (G →* Oˣ)) (hG : IsUnit (Nat.card G : O)) :
    Ψ.charGroupRing = ⊤ :=
  eq_top_iff.mpr fun y _ ↦ Set.charGroupRing_def Ψ ▸ Set.jointEval_surjective Ψ hG y

/-- For a finite commutative group `G` whose order is a unit in a domain `O` with enough roots of
unity, joint evaluation at all characters is bijective. -/
theorem Set.jointEval_univ_bijective [Finite G] [HasEnoughRootsOfUnity O (Monoid.exponent G)]
    (hG : IsUnit (Nat.card G : O)) :
    Function.Bijective (Set.jointEval (Set.univ : Set (G →* Oˣ))) :=
  ⟨Set.jointEval_injective, Set.jointEval_surjective _ hG⟩

end Surjective

namespace MonoidAlgebra

variable {O G : Type*} [CommRing O] [IsDomain O] [CommGroup G]

section Finite

variable [Finite G] [HasEnoughRootsOfUnity O (Monoid.exponent G)]

/-- **Character splitting of a finite commutative group algebra.** When `#G` is a unit in a domain
`O` with enough roots of unity for `G`, joint character evaluation identifies `O[G]` as an
`O`-algebra with the product `(G →* Oˣ) → O`. -/
noncomputable def charEvalEquiv (hG : IsUnit (Nat.card G : O)) :
    MonoidAlgebra O G ≃ₐ[O] ((G →* Oˣ) → O) :=
  AlgEquiv.ofBijective (AlgHom.pi fun ψ : G →* Oˣ ↦ ψ.charEval)
    ⟨fun _ _ h ↦ TauCeti.eq_of_forall_charEval_eq (congrFun h), fun y ↦ by
      obtain ⟨x, hx⟩ := Set.jointEval_surjective (Set.univ : Set (G →* Oˣ)) hG (fun ψ ↦ y ψ.1)
      exact ⟨x, funext fun ψ ↦ by simpa [AlgHom.pi_apply] using congrFun hx ⟨ψ, Set.mem_univ ψ⟩⟩⟩

@[simp]
theorem charEvalEquiv_apply (hG : IsUnit (Nat.card G : O)) (x : MonoidAlgebra O G)
    (ψ : G →* Oˣ) :
    charEvalEquiv hG x ψ = ψ.charEval x :=
  (rfl)

theorem charEvalEquiv_single (hG : IsUnit (Nat.card G : O)) (g : G) (a : O) (ψ : G →* Oˣ) :
    charEvalEquiv hG (single g a) ψ = a * ψ g := by
  simp [smul_eq_mul]

/-- **Character splitting of power series over a finite commutative group algebra.** Applying
`MonoidHom.charEval` coefficientwise identifies `O[G]⟦X⟧` with `(G →* Oˣ) → O⟦X⟧`. -/
noncomputable def powerSeriesCharEvalEquiv (hG : IsUnit (Nat.card G : O)) :
    PowerSeries (MonoidAlgebra O G) ≃ₐ[O] ((G →* Oˣ) → PowerSeries O) :=
  { AlgHom.pi fun ψ : G →* Oˣ ↦ PowerSeries.mapAlgHom ψ.charEval with
    invFun := fun F ↦ PowerSeries.mk fun n ↦
      (charEvalEquiv hG).symm (fun ψ ↦ PowerSeries.coeff n (F ψ))
    left_inv := fun φ ↦ PowerSeries.ext fun n ↦ by
      simp only [PowerSeries.coeff_mk]
      exact (charEvalEquiv hG).symm_apply_apply (PowerSeries.coeff n φ)
    right_inv := fun F ↦ funext fun ψ ↦ PowerSeries.ext fun n ↦ by
      simpa only [AlgHom.toFun_eq_coe, AlgHom.pi_apply, PowerSeries.mapAlgHom_apply,
        PowerSeries.coeff_map, PowerSeries.coeff_mk, RingHom.coe_coe, ← charEvalEquiv_apply hG]
        using congrFun ((charEvalEquiv hG).apply_symm_apply fun χ ↦ PowerSeries.coeff n (F χ)) ψ }

@[simp]
theorem powerSeriesCharEvalEquiv_apply (hG : IsUnit (Nat.card G : O))
    (φ : PowerSeries (MonoidAlgebra O G)) (ψ : G →* Oˣ) :
    powerSeriesCharEvalEquiv hG φ ψ = PowerSeries.map ψ.charEval.toRingHom φ :=
  (rfl)

@[simp]
theorem coeff_powerSeriesCharEvalEquiv_symm (hG : IsUnit (Nat.card G : O))
    (F : (G →* Oˣ) → PowerSeries O) (n : ℕ) :
    PowerSeries.coeff n ((powerSeriesCharEvalEquiv hG).symm F) =
      (charEvalEquiv hG).symm (fun ψ ↦ PowerSeries.coeff n (F ψ)) := by
  simp [powerSeriesCharEvalEquiv]

@[simp]
theorem powerSeriesCharEvalEquiv_X (hG : IsUnit (Nat.card G : O)) :
    powerSeriesCharEvalEquiv hG PowerSeries.X = fun _ ↦ PowerSeries.X := by
  ext ψ n
  simp

@[simp]
theorem powerSeriesCharEvalEquiv_C (hG : IsUnit (Nat.card G : O)) (x : MonoidAlgebra O G) :
    powerSeriesCharEvalEquiv hG (PowerSeries.C x) = fun ψ ↦ PowerSeries.C (ψ.charEval x) := by
  ext ψ n
  simp [PowerSeries.coeff_C]

end Finite

section Fintype

variable [Fintype G] [HasEnoughRootsOfUnity O (Monoid.exponent G)]

/-- `charEvalEquiv` sends the character idempotent `e_χ` to the coordinate idempotent at `χ`. -/
@[simp]
theorem charEvalEquiv_charIdempotent [DecidableEq (G →* Oˣ)] (hG : IsUnit (Nat.card G : O))
    (χ : G →* Oˣ) :
    charEvalEquiv hG (TauCeti.charIdempotent χ) = Pi.single χ 1 := by
  ext ψ
  simp [Pi.single_apply, eq_comm, MonoidHom.charEval_charIdempotent hG]

/-- The inverse of `charEvalEquiv` sends `Pi.single χ r` to `r • e_χ`. -/
@[simp]
theorem charEvalEquiv_symm_single [DecidableEq (G →* Oˣ)] (hG : IsUnit (Nat.card G : O))
    (χ : G →* Oˣ) (r : O) :
    (charEvalEquiv hG).symm (Pi.single χ r) = r • TauCeti.charIdempotent χ := by
  apply (charEvalEquiv hG).injective
  rw [AlgEquiv.apply_symm_apply, map_smul, charEvalEquiv_charIdempotent]
  ext ψ
  simp [Pi.single_apply]

/-- The inverse of `charEvalEquiv` expands a tuple along the character idempotents. -/
theorem charEvalEquiv_symm_apply (hG : IsUnit (Nat.card G : O)) (y : (G →* Oˣ) → O) :
    (charEvalEquiv hG).symm y = ∑ χ : G →* Oˣ, y χ • TauCeti.charIdempotent χ := by
  classical
  let _ : Fintype (G →* Oˣ) := Fintype.ofFinite _
  conv_lhs => rw [← Finset.univ_sum_single y]
  simp [map_sum]

end Fintype

end MonoidAlgebra

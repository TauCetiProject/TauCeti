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

Let `G` be a finite commutative group and `O` a domain in which `#G` is a unit. Inverting `#G` in
`O` collapses the lattice containment `#G • (Ψ → O) ≤ R_Ψ` from `Set.charGroupRing.card_smul_mem`
(`TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Lattice`), so joint evaluation `Ψ.jointEval` on any
set `Ψ` of `O`-valued characters is surjective and `R_Ψ = ⊤` (`Set.jointEval_surjective`,
`Set.charGroupRing_eq_top`), with no roots-of-unity assumption.

When `O` also has enough roots of unity of exponent `exp(G)`, joint evaluation at all characters is
bijective (`TauCeti.jointEval_univ_bijective`), giving `TauCeti.charEvalEquiv : O[G] ≃ₐ[O]
((G →* Oˣ) → O)` sending `TauCeti.charIdempotent χ` to `Pi.single χ 1`. Applying this
coefficientwise yields `TauCeti.powerSeriesCharEvalEquiv : O[G]⟦X⟧ ≃ₐ[O] ((G →* Oˣ) → O⟦X⟧)`,
which decomposes power-series and completed group algebras with a tame finite factor (such as
`ℤ_p[[ℤ_pˣ]]` for odd `p`) into character branches.
-/

public section

section Surjective

variable {O G : Type*} [CommRing O] [IsDomain O] [CommGroup G]

/-- When `#G` is a unit in the domain `O`, evaluating `χ`'s character idempotent at `ψ` gives `1`
for `χ = ψ` and `0` otherwise. -/
theorem MonoidHom.charEval_charIdempotent [Fintype G] [DecidableEq (G →* Oˣ)] (χ ψ : G →* Oˣ)
    (hG : IsUnit (Nat.card G : O)) :
    ψ.charEval (TauCeti.charIdempotent χ) = if χ = ψ then 1 else 0 := by
  let _ : Fintype (⊤ : Subgroup G) := Fintype.ofFinite _
  have hdef : TauCeti.charIdempotent χ =
      Ring.inverse (Nat.card G : O) • TauCeti.subgroupCharSum ((Units.coeHom O).comp χ⁻¹) ⊤ := by
    rw [TauCeti.charIdempotent_eq_sum, TauCeti.subgroupCharSum_eq_sum_of_eq_top _ _ rfl]; simp
  rw [hdef, map_smul, MonoidHom.charEval_subgroupCharSum_inv_top, smul_ite, smul_eq_mul, smul_zero,
    Ring.inverse_mul_cancel _ hG]

/-- When `#G` is a unit in the domain `O`, the joint evaluation `O[G] → (Ψ → O)` on any set `Ψ` of
characters is surjective; no roots-of-unity hypothesis is needed. -/
theorem Set.jointEval_surjective [Finite G] (Ψ : Set (G →* Oˣ)) (hG : IsUnit (Nat.card G : O)) :
    Function.Surjective Ψ.jointEval := fun y ↦ by
  have hmem := Set.charGroupRing.card_smul_mem Ψ (Ring.inverse (Nat.card G : O) • y)
  rwa [smul_smul, Ring.mul_inverse_cancel _ hG, one_smul, Set.charGroupRing_def] at hmem

/-- When `#G` is a unit in the domain `O`, the character group ring `R_Ψ` is `⊤`. -/
theorem Set.charGroupRing_eq_top [Finite G] (Ψ : Set (G →* Oˣ)) (hG : IsUnit (Nat.card G : O)) :
    Ψ.charGroupRing = ⊤ :=
  eq_top_iff.mpr fun y _ ↦ Set.charGroupRing_def Ψ ▸ Set.jointEval_surjective Ψ hG y

end Surjective

namespace TauCeti

variable {O G : Type*} [CommRing O] [IsDomain O] [CommGroup G]

section Finite

variable [Finite G] [HasEnoughRootsOfUnity O (Monoid.exponent G)]

/-- For a finite commutative group `G` whose order is a unit in a domain `O` with enough roots of
unity, joint evaluation at all characters is bijective. -/
theorem jointEval_univ_bijective (hG : IsUnit (Nat.card G : O)) :
    Function.Bijective (Set.jointEval (Set.univ : Set (G →* Oˣ))) :=
  ⟨Set.jointEval_injective, Set.jointEval_surjective _ hG⟩

/-- **Character splitting of a finite commutative group algebra.** Joint character evaluation
identifies `O[G]` as an `O`-algebra with `(G →* Oˣ) → O`. -/
noncomputable def charEvalEquiv (hG : IsUnit (Nat.card G : O)) :
    MonoidAlgebra O G ≃ₐ[O] ((G →* Oˣ) → O) :=
  AlgEquiv.ofBijective (AlgHom.pi fun ψ : G →* Oˣ ↦ ψ.charEval)
    ⟨fun _ _ h ↦ TauCeti.eq_of_forall_charEval_eq (congrFun h), fun y ↦ by
      obtain ⟨x, hx⟩ := Set.jointEval_surjective (Set.univ : Set (G →* Oˣ)) hG (fun ψ ↦ y ψ.val)
      exact ⟨x, funext fun ψ ↦ by simpa [AlgHom.pi_apply] using congrFun hx ⟨ψ, Set.mem_univ ψ⟩⟩⟩

@[simp] theorem charEvalEquiv_apply (hG : IsUnit (Nat.card G : O)) (x : MonoidAlgebra O G)
    (ψ : G →* Oˣ) : charEvalEquiv hG x ψ = ψ.charEval x := (rfl)
theorem charEvalEquiv_single (hG : IsUnit (Nat.card G : O)) (g : G) (a : O) (ψ : G →* Oˣ) :
    charEvalEquiv hG (MonoidAlgebra.single g a) ψ = a * ψ g := by simp [smul_eq_mul]

/-- **Character splitting of power series over a finite commutative group algebra.** Applying
`MonoidHom.charEval` coefficientwise identifies `O[G]⟦X⟧` with `(G →* Oˣ) → O⟦X⟧`. -/
noncomputable def powerSeriesCharEvalEquiv (hG : IsUnit (Nat.card G : O)) :
    PowerSeries (MonoidAlgebra O G) ≃ₐ[O] ((G →* Oˣ) → PowerSeries O) :=
  { AlgHom.pi fun ψ : G →* Oˣ ↦ PowerSeries.mapAlgHom ψ.charEval with
    invFun F := PowerSeries.mk fun n ↦ (charEvalEquiv hG).symm (fun ψ ↦ PowerSeries.coeff n (F ψ))
    left_inv φ := PowerSeries.ext fun n ↦ by
      simp only [PowerSeries.coeff_mk, AlgHom.toFun_eq_coe, AlgHom.pi_apply,
        PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map, RingHom.coe_coe,
        ← charEvalEquiv_apply hG]
      exact (charEvalEquiv hG).symm_apply_apply _
    right_inv F := funext fun ψ ↦ PowerSeries.ext fun n ↦ by
      simpa only [AlgHom.toFun_eq_coe, AlgHom.pi_apply, PowerSeries.mapAlgHom_apply,
        PowerSeries.coeff_map, PowerSeries.coeff_mk, RingHom.coe_coe, ← charEvalEquiv_apply hG]
        using congrFun ((charEvalEquiv hG).apply_symm_apply fun χ ↦ PowerSeries.coeff n (F χ)) ψ }

@[simp] theorem powerSeriesCharEvalEquiv_apply (hG : IsUnit (Nat.card G : O))
    (φ : PowerSeries (MonoidAlgebra O G)) (ψ : G →* Oˣ) :
    powerSeriesCharEvalEquiv hG φ ψ = PowerSeries.map ψ.charEval.toRingHom φ := (rfl)
@[simp] theorem coeff_powerSeriesCharEvalEquiv_symm (hG : IsUnit (Nat.card G : O))
    (F : (G →* Oˣ) → PowerSeries O) (n : ℕ) :
    PowerSeries.coeff n ((powerSeriesCharEvalEquiv hG).symm F) =
      (charEvalEquiv hG).symm (fun ψ ↦ PowerSeries.coeff n (F ψ)) := by
  simp [powerSeriesCharEvalEquiv]
@[simp] theorem powerSeriesCharEvalEquiv_X (hG : IsUnit (Nat.card G : O)) :
    powerSeriesCharEvalEquiv hG PowerSeries.X = fun _ ↦ PowerSeries.X := by ext; simp
@[simp] theorem powerSeriesCharEvalEquiv_C (hG : IsUnit (Nat.card G : O)) (x : MonoidAlgebra O G) :
    powerSeriesCharEvalEquiv hG (PowerSeries.C x) = fun ψ ↦ PowerSeries.C (ψ.charEval x) := by
  ext; simp [PowerSeries.coeff_C]

end Finite

section Fintype

variable [Fintype G] [HasEnoughRootsOfUnity O (Monoid.exponent G)]

/-- `charEvalEquiv` sends `e_χ` to the coordinate idempotent `Pi.single χ 1`. -/
@[simp] theorem charEvalEquiv_charIdempotent [DecidableEq (G →* Oˣ)] (hG : IsUnit (Nat.card G : O))
    (χ : G →* Oˣ) : charEvalEquiv hG (charIdempotent χ) = Pi.single χ 1 := by
  ext ψ; simp [Pi.single_apply, eq_comm, MonoidHom.charEval_charIdempotent _ _ hG]

/-- The inverse of `charEvalEquiv` sends `Pi.single χ r` to `r • e_χ`. -/
@[simp] theorem charEvalEquiv_symm_single [DecidableEq (G →* Oˣ)] (hG : IsUnit (Nat.card G : O))
    (χ : G →* Oˣ) (r : O) : (charEvalEquiv hG).symm (Pi.single χ r) = r • charIdempotent χ := by
  apply (charEvalEquiv hG).injective
  rw [AlgEquiv.apply_symm_apply, map_smul, charEvalEquiv_charIdempotent]
  ext ψ; simp [Pi.single_apply]

/-- The inverse of `charEvalEquiv` expands a tuple along the character idempotents. -/
theorem charEvalEquiv_symm_apply (hG : IsUnit (Nat.card G : O)) (y : (G →* Oˣ) → O) :
    (charEvalEquiv hG).symm y = ∑ χ : G →* Oˣ, y χ • charIdempotent χ := by
  classical
  let _ : Fintype (G →* Oˣ) := Fintype.ofFinite _
  conv_lhs => rw [← Finset.univ_sum_single y]
  simp [map_sum]

end Fintype

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Elliptic.LocalMultiplicity
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Fiber

/-!
# Degree of a finite-index quotient map over an interior point

The local multiplicities in the fibre over an interior orbit add up to the index of the
subgroup. The cosets of the smaller group are partitioned by their images in the fibre;
each part has as many elements as the local ramification index at its image. This is the
interior-fibre calculation used to identify the degree of a finite-index map of compactified
Fuchsian quotients.
-/

public noncomputable section

open MulAction TauCeti.RiemannSurface UpperHalfPlane
open Subgroup.CompactifiedQuotient
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)}

private theorem sum_localMultiplicity_compactifiedQuotientMap_fiber_mk
    [DiscreteTopology Γ] (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] (z : ℍ) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    ∑ᶠ y : {y : Δ.CompactifiedQuotient //
        compactifiedQuotientMap h y = .ofQuotient (Quotient.mk'' z)},
      localMultiplicity (compactifiedQuotientMap h) y.1 =
        (Δ.subgroupOf Γ).index := by
  classical
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  let C := Γ ⧸ Δ.subgroupOf Γ
  let F := {y : Δ.CompactifiedQuotient //
    compactifiedQuotientMap h y = .ofQuotient (Quotient.mk'' z)}
  let φ : C → F := fun c =>
    orbitFiberEquivCompactifiedFiber h (Quotient.mk'' z)
      (TauCeti.cosetToOrbitRelMapFiber h z c)
  have : Finite C := inferInstance
  have : Finite F := finite_fiber_compactifiedQuotientMap h _
  let : Fintype C := Fintype.ofFinite C
  let : Fintype F := Fintype.ofFinite F
  have hcard : (∑ y : F, Nat.card {c : C // φ c = y}) = Nat.card C := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
        (f := φ) (by simp)).symm
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨q, rfl⟩ := (orbitFiberEquivCompactifiedFiber h (Quotient.mk'' z)).surjective y
    obtain ⟨c, rfl⟩ := TauCeti.cosetToOrbitRelMapFiber_surjective h z q
    exact ⟨c, rfl⟩
  have hweight (y : F) : Nat.card {c : C // φ c = y} =
      localMultiplicity (compactifiedQuotientMap h) y.1 := by
    obtain ⟨c, rfl⟩ := hφsurj y
    induction c using QuotientGroup.induction_on with
    | H g =>
      have hfiber : Nat.card {r : C // φ r = φ ((g : Γ) : C)} =
          Nat.card {r : C // TauCeti.orbitOfCosetTranslate z r =
            TauCeti.orbitOfCosetTranslate z ((g : Γ) : C)} := by
        apply Nat.card_congr
        apply Equiv.subtypeEquivProp
        funext r
        apply propext
        simp only [φ, (orbitFiberEquivCompactifiedFiber h (Quotient.mk'' z)).injective.eq_iff]
        constructor
        · intro heq
          simpa only [TauCeti.cosetToOrbitRelMapFiber_apply] using congrArg Subtype.val heq
        · intro heq
          apply Subtype.ext
          simpa only [TauCeti.cosetToOrbitRelMapFiber_apply] using heq
      rw [hfiber]
      have hcount := TauCeti.card_fiber_orbitOfCosetTranslate_mul_card_stabilizer_inv_smul
        h z g
      have hram := card_stabilizer_mul_ellipticRamificationIndex h (g⁻¹ • z)
      rw [TauCeti.card_stabilizer_smul] at hram
      have hsmall : 0 < Nat.card (stabilizer Δ (g⁻¹ • z)) := Nat.card_pos
      have hindex : Nat.card {r : C // TauCeti.orbitOfCosetTranslate z r =
          TauCeti.orbitOfCosetTranslate z ((g : Γ) : C)} =
          ellipticRamificationIndex h (g⁻¹ • z) := by
        nlinarith
      rw [hindex]
      simpa only [φ, orbitFiberEquivCompactifiedFiber_apply,
        TauCeti.cosetToOrbitRelMapFiber_apply, TauCeti.orbitOfCosetTranslate_mk,
        Subgroup.smul_def, Subgroup.coe_inv] using
        (localMultiplicity_compactifiedQuotientMap_ofQuotient_eq_ellipticRamificationIndex
          h (g⁻¹ • z)).symm
  rw [finsum_eq_sum_of_fintype]
  simpa only [F, C, Subgroup.index_eq_card] using
    (calc
      (∑ y : F, localMultiplicity (compactifiedQuotientMap h) y.1) =
          ∑ y : F, Nat.card {c : C // φ c = y} := Finset.sum_congr rfl fun y _ => (hweight y).symm
      _ = Nat.card C := hcard)

/-- The sum of local multiplicities over an interior fibre of a finite-index quotient map is
its subgroup index. This includes elliptic fibres, where the number of points can be smaller
than the index. -/
theorem sum_localMultiplicity_compactifiedQuotientMap_fiber_ofQuotient
    [DiscreteTopology Γ] (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ]
    (p : orbitRel.Quotient Γ ℍ) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    ∑ᶠ y : {y : Δ.CompactifiedQuotient // compactifiedQuotientMap h y = .ofQuotient p},
      localMultiplicity (compactifiedQuotientMap h) y.1 =
        (Δ.subgroupOf Γ).index := by
  induction p using Quotient.inductionOn' with
  | _ z => exact sum_localMultiplicity_compactifiedQuotientMap_fiber_mk h z

end Subgroup

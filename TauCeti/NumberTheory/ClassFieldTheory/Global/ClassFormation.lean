/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SecondInequality
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LiftIndependence
import TauCeti.NumberTheory.ClassFieldTheory.Formation.InvariantKernel
import TauCeti.NumberTheory.ClassFieldTheory.Formation.PrimeDegree
import TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.LocalizationKernel
import TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula
import TauCeti.NumberTheory.ClassFieldTheory.Global.PrescribedInvariant

/-!
# Toward the global invariant of the idele classes, from two arithmetic inputs

Let `K` be a number field. Tate's construction of the invariant map of the idele classes defines,
on a finite normal layer `L/F` inside `Kˢ`, the invariant of a class of `H²(Gal(L/F), C_L)` as the
sum of the local invariants `ideleSumLocalInv` of a lift of its inflation to the ideles of some
refinement of the layer. This file proves the steps of that construction for the idele-class
formation `globalFormation K` as conditional reductions, assuming two arithmetic inputs:

* **the Kummer case of the second inequality** (`hK`): for every cyclic extension `L/F` of number
  fields of prime degree `p` with `F ∋ μ_p`, the idele-class norm group `N_{L/F}(C_L)` has index at
  most `p` in `C_F`;
* **generators on layers of prime degree** (`hgen`): every layer of `globalFormation K` of prime
  degree `p` carries a class of `H²(Gal(L/F), I_L)` whose local invariants sum to `1/p`.

The names of the results record these inputs: `_of_forall_index_le` for `hK`, as in
`SecondInequality.lean`, and `_of_prime_degree` for `hgen`.

From `hK` alone the file derives the sum formula for the Brauer group of `K`, and from it that
the sum of the local invariants vanishes on the kernel of
`H²(Gal(L/F), I_L) → H²(Gal(L/F), C_L)` and does not depend on the choice of lift and
refinement. With `hgen` as well, that kernel is exactly the set of classes whose local invariants
sum to zero, and every class of `H²(Gal(L/F), C_L)` lifts to the ideles after inflation to a
suitable refinement.

## Main statements

All in the namespace `TauCeti.ClassFieldTheory`:

* `ideleToClassH2_eq_zero_iff_of_forall_index_le_of_prime_degree`: a class of
  `H²(Gal(L/F), I_L)` dies in the idele classes exactly when its local invariants sum to zero.
* `exists_refinement_mem_range_ideleToClassH2_of_forall_index_le_of_prime_degree`: after
  inflation to a refinement, every class of `H²(Gal(L/F), C_L)` lifts to the ideles.
* `ideleSumLocalInv_eq_of_ideleToClassH2_eq_of_forall_index_le`: two lifts of the inflations of
  one class to two refinements have the same sum of local invariants.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §§5–8, and Chapter VIII, §4
  (Theorem 4.7).
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §11.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]
  (hK : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [IsGalois F L] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p],
    Module.finrank F L = p → (GlobalNumberFields.ideleClassNormMap F L).range.index ≤ p)

/-! ### Consequences of the Kummer case -/

include hK in
/-- **The sum formula, from the Kummer case.** If the Kummer case of the second inequality holds,
the local invariants of every Brauer class of `K` sum to zero. -/
theorem sumLocalInv_brLocalization_eq_zero_of_forall_index_le (x : Br K) :
    sumLocalInv K (brLocalization K x) = 0 :=
  sumLocalInv_brLocalization_eq_zero_of_brLocalization_injective K
    (fun E _ _ _ ↦ brLocalization_injective_of_subsingleton_h1_globalFormation E fun _ ↦
      subsingleton_h1_globalFormation_of_forall_index_le hK _) x

include hK in
/-- **The sum of the local invariants vanishes on the classes that die in the idele classes**, if
the Kummer case of the second inequality holds. -/
theorem ideleSumLocalInv_eq_zero_of_ideleToClassH2_eq_zero_of_forall_index_le
    {L : NormalLayer (AbsoluteGaloisGroup K)} {y : L.H (ideleFormation K) 2}
    (hy : ideleToClassH2 K L y = 0) : ideleSumLocalInv K L y = 0 := by
  obtain ⟨w, rfl⟩ : y ∈ (multiplicativeToIdeleH2 K L).range := ker_ideleToClassH2 K L ▸ hy
  rw [ideleSumLocalInv_multiplicativeToIdeleH2]
  exact sumLocalInv_brLocalization_eq_zero_of_forall_index_le hK _

include hK in
/-- **Independence of the lift and of the refinement**, if the Kummer case of the second inequality
holds: two lifts to the ideles of the inflations of one class of `H²(Gal(L/F), C_L)`, to two
refinements of the layer, have the same sum of local invariants. -/
theorem ideleSumLocalInv_eq_of_ideleToClassH2_eq_of_forall_index_le
    {Lay Lay₁ Lay₂ : NormalLayer (AbsoluteGaloisGroup K)}
    (T₁ : LayerRefinement Lay Lay₁) (T₂ : LayerRefinement Lay Lay₂)
    (x : Lay.H (globalFormation K) 2)
    (y₁ : Lay₁.H (ideleFormation K) 2) (y₂ : Lay₂.H (ideleFormation K) 2)
    (h₁ : ideleToClassH2 K Lay₁ y₁ = T₁.cohomologyInfl (globalFormation K) 2 x)
    (h₂ : ideleToClassH2 K Lay₂ y₂ = T₂.cohomologyInfl (globalFormation K) 2 x) :
    ideleSumLocalInv K Lay₁ y₁ = ideleSumLocalInv K Lay₂ y₂ := by
  obtain ⟨b, hb⟩ := exists_ideleSumLocalInv_eq_add_sumLocalInv_of_ideleToClassH2_eq K T₁ T₂ x y₁ y₂
    h₁ h₂
  rw [hb, sumLocalInv_brLocalization_eq_zero_of_forall_index_le hK, add_zero]

/-! ### The kernel of the passage to idele classes -/

variable (hgen : ∀ L : NormalLayer (AbsoluteGaloisGroup K), L.degree.Prime →
    ∃ z : L.H (ideleFormation K) 2,
      ideleSumLocalInv K L z = ((1 / L.degree : ℚ) : AddCircle (1 : ℚ)))

include hK hgen in
/-- **A class of the idele layer dies in the idele classes exactly when its local invariants sum to
zero**, if the Kummer case of the second inequality holds and every layer of prime degree `p`
carries a class whose local invariants sum to `1/p`. -/
theorem ideleToClassH2_eq_zero_iff_of_forall_index_le_of_prime_degree
    {L : NormalLayer (AbsoluteGaloisGroup K)} {y : L.H (ideleFormation K) 2} :
    ideleToClassH2 K L y = 0 ↔ ideleSumLocalInv K L y = 0 := by
  refine ⟨ideleSumLocalInv_eq_zero_of_ideleToClassH2_eq_zero_of_forall_index_le hK, fun hy ↦ ?_⟩
  have hker (L : NormalLayer (AbsoluteGaloisGroup K)) (y : L.H (ideleFormation K) 2)
      (hy : groupCohomology.map (MonoidHom.id L.Gal) (L.repMap (ideleClassHom K)) 2 y = 0) :
      ideleSumLocalInv K L y = 0 :=
    ideleSumLocalInv_eq_zero_of_ideleToClassH2_eq_zero_of_forall_index_le hK
      (by rw [ideleToClassH2_apply]; exact hy)
  -- On a layer of prime degree the image of the given class generates `H²(Gal(L/F), C_L)`; the
  -- Sylow and tower reduction carries the statement to every layer.
  rw [ideleToClassH2_apply]
  refine NormalLayer.map_eq_zero_of_prime_degree (ideleClassHom K) (fun L ↦ ideleSumLocalInv K L)
    (fun T y ↦ ideleSumLocalInv_infl K T y) (fun R y ↦ ideleSumLocalInv_res K R y) hker
    (subsingleton_h1_globalFormation_of_forall_index_le hK) (fun L hp x ↦ ?_)
    (fun L hp y hy ↦ NormalLayer.map_eq_zero_of_natCard_H2_dvd_degree (ideleClassHom K) _ hker
      (natCard_H2_globalFormation_dvd_degree_of_forall_index_le hK L) (hgen L hp) hy) L hy
  have := NormalLayer.isCyclic_gal_of_prime_degree hp
  exact (surjective_ideleToClassH2_of_isCyclic K L x).imp fun y hy ↦
    by rw [ideleToClassH2_apply] at hy; exact hy

include hK hgen in
/-- **Killing the obstruction**, if the Kummer case of the second inequality holds and every layer
of prime degree `p` carries a class whose local invariants sum to `1/p`: some refinement of every
layer `L/F` is such that the inflation of every class of `H²(Gal(L/F), C_L)` to it lifts to the
ideles. -/
theorem exists_refinement_mem_range_ideleToClassH2_of_forall_index_le_of_prime_degree
    (Lay : NormalLayer (AbsoluteGaloisGroup K)) :
    ∃ (Lay' : NormalLayer (AbsoluteGaloisGroup K)) (T : LayerRefinement Lay Lay'),
      ∀ x : Lay.H (globalFormation K) 2,
        T.cohomologyInfl (globalFormation K) 2 x ∈ (ideleToClassH2 K Lay').range := by
  obtain ⟨Lay', T, hT⟩ := NormalLayer.exists_refinement_forall_exists_map_eq_cohomologyInfl
    (ideleClassHom K) (fun L ↦ ideleSumLocalInv K L) (fun R y ↦ ideleSumLocalInv_res K R y)
    (fun L y hy ↦ by
      have h := ideleToClassH2_eq_zero_iff_of_forall_index_le_of_prime_degree
        hK hgen (L := L) (y := y)
      rw [ideleToClassH2_apply] at h
      exact h.1 hy)
    (fun L y hy ↦ by
      have h := ideleToClassH2_eq_zero_iff_of_forall_index_le_of_prime_degree
        hK hgen (L := L) (y := y)
      rw [ideleToClassH2_apply] at h
      exact h.2 hy)
    (subsingleton_h1_globalFormation_of_forall_index_le hK)
    (natCard_H2_globalFormation_dvd_degree_of_forall_index_le hK Lay)
    (exists_refinement_ideleSumLocalInv_eq Lay)
  exact ⟨Lay', T, fun x ↦ (hT x).imp fun y hy ↦ by rw [ideleToClassH2_apply]; exact hy⟩

end TauCeti.ClassFieldTheory

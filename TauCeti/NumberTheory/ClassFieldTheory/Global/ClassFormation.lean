/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.DescendedInvariant
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SecondInequality
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LiftIndependence
import TauCeti.NumberTheory.ClassFieldTheory.Formation.InvariantKernel
import TauCeti.NumberTheory.ClassFieldTheory.Formation.PrimeDegree
import TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.LocalizationKernel
import TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula
import TauCeti.NumberTheory.ClassFieldTheory.Global.PrescribedInvariant

/-!
# The global invariant and the idele-class formation

Let `K` be a number field. Tate's construction of the invariant map of the idele classes defines,
on a finite normal layer `L/F` inside `Kˢ`, the invariant of a class of `H²(Gal(L/F), C_L)` as the
sum of the local invariants `ideleSumLocalInv` of a lift of its inflation to the ideles of some
refinement of the layer. This file carries out that construction for the idele-class formation
`globalFormation K` and shows that it makes `globalFormation K` a class formation.

From the sum formula for the Brauer group of `K` (`sumLocalInv_brLocalization_eq_zero`), the sum
of the local invariants vanishes on the kernel of `H²(Gal(L/F), I_L) → H²(Gal(L/F), C_L)` and does
not depend on the choice of lift and refinement. Every layer of prime degree `p` carries a class of
`H²(Gal(L/F), I_L)` whose local invariants sum to `1/p`
(`exists_ideleSumLocalInv_eq_one_div_degree_of_prime`); its image generates `H²(Gal(L/F), C_L)`,
whose order divides `p` by the second inequality. The reduction to layers of prime degree then
shows that the kernel above is exactly the set of classes whose local invariants sum to zero, and
that every class of `H²(Gal(L/F), C_L)` lifts to the ideles after inflation to a suitable
refinement.

These are the hypotheses of `descendedInv` and `ClassFormation.ofDescendedInv`: the global
invariant `globalInv K L` is the invariant descended from `ideleSumLocalInv`, and the global class
formation is the class formation it defines. The idele-class `H¹` vanishes by the first and second
inequalities (`subsingleton_h1_globalFormation`), and the cyclotomic input
`exists_refinement_ideleSumLocalInv_eq` supplies a class of invariant `1/[L:F]` on a refinement of
every layer, which makes the invariant of a layer of degree `n` an isomorphism onto the `n`-torsion
of `ℚ/ℤ`.

## Main definitions

* `TauCeti.ClassFieldTheory.globalInv`: the invariant `H²(Gal(L/F), C_L) → ℚ/ℤ` of a layer.
* `TauCeti.ClassFieldTheory.globalClassFormation`: the idele-class formation of `K` as a class
  formation, with invariant `globalInv` (`globalClassFormation_inv`).

## Main statements

All in the namespace `TauCeti.ClassFieldTheory`:

* `ideleToClassH2_eq_zero_iff`: a class of `H²(Gal(L/F), I_L)` dies in the idele classes exactly
  when its local invariants sum to zero.
* `exists_refinement_mem_range_ideleToClassH2`: after inflation to a refinement, every class of
  `H²(Gal(L/F), C_L)` lifts to the ideles.
* `ideleSumLocalInv_eq_of_ideleToClassH2_eq`: two lifts of the inflations of
  one class to two refinements have the same sum of local invariants.
* `globalInv_eq`: the global invariant of a class is the sum of the local invariants of any lift of
  any of its inflations.
* `globalInv_ideleToClassH2`, `globalInv_infl` and `globalInv_unique`: the two equations that
  determine the global invariant.
* `globalInv_res`, `globalInv_conj`: its restriction and conjugation laws.
* `globalInv_injective`, `range_globalInv`: the global invariant of a layer of degree `n` is
  injective with image the `n`-torsion of `ℚ/ℤ`.
* `ideleSumLocalInv_fundamentalClass`: the local invariants of any idele lift of the fundamental
  class of the global class formation sum to `1/[L:F]`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §§5–8, and Chapter VIII, §4
  (Theorem 4.7).
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §11.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-! ### Consequences of the sum formula -/

/-- **The sum of the local invariants vanishes on the classes that die in the idele classes.** -/
theorem ideleSumLocalInv_eq_zero_of_ideleToClassH2_eq_zero
    {L : NormalLayer (AbsoluteGaloisGroup K)} {y : L.H (ideleFormation K) 2}
    (hy : ideleToClassH2 K L y = 0) : ideleSumLocalInv K L y = 0 := by
  obtain ⟨w, rfl⟩ : y ∈ (multiplicativeToIdeleH2 K L).range := ker_ideleToClassH2 K L ▸ hy
  rw [ideleSumLocalInv_multiplicativeToIdeleH2]
  exact sumLocalInv_brLocalization_eq_zero K _

/-- **Independence of the lift and of the refinement**: two lifts to the ideles of the inflations
of one class of `H²(Gal(L/F), C_L)`, to two refinements of the layer, have the same sum of local
invariants. -/
theorem ideleSumLocalInv_eq_of_ideleToClassH2_eq
    {Lay Lay₁ Lay₂ : NormalLayer (AbsoluteGaloisGroup K)}
    (T₁ : LayerRefinement Lay Lay₁) (T₂ : LayerRefinement Lay Lay₂)
    (x : Lay.H (globalFormation K) 2)
    (y₁ : Lay₁.H (ideleFormation K) 2) (y₂ : Lay₂.H (ideleFormation K) 2)
    (h₁ : ideleToClassH2 K Lay₁ y₁ = T₁.cohomologyInfl (globalFormation K) 2 x)
    (h₂ : ideleToClassH2 K Lay₂ y₂ = T₂.cohomologyInfl (globalFormation K) 2 x) :
    ideleSumLocalInv K Lay₁ y₁ = ideleSumLocalInv K Lay₂ y₂ := by
  obtain ⟨b, hb⟩ := exists_ideleSumLocalInv_eq_add_sumLocalInv_of_ideleToClassH2_eq K T₁ T₂ x y₁ y₂
    h₁ h₂
  rw [hb, sumLocalInv_brLocalization_eq_zero, add_zero]

/-! ### The kernel of the passage to idele classes -/

/-- **A class of the idele layer dies in the idele classes exactly when its local invariants sum to
zero.** -/
theorem ideleToClassH2_eq_zero_iff {L : NormalLayer (AbsoluteGaloisGroup K)}
    {y : L.H (ideleFormation K) 2} :
    ideleToClassH2 K L y = 0 ↔ ideleSumLocalInv K L y = 0 := by
  refine ⟨ideleSumLocalInv_eq_zero_of_ideleToClassH2_eq_zero, fun hy ↦ ?_⟩
  have hker (L : NormalLayer (AbsoluteGaloisGroup K)) (y : L.H (ideleFormation K) 2)
      (hy : groupCohomology.map (MonoidHom.id L.Gal) (L.repMap (ideleClassHom K)) 2 y = 0) :
      ideleSumLocalInv K L y = 0 :=
    ideleSumLocalInv_eq_zero_of_ideleToClassH2_eq_zero (by rw [ideleToClassH2_apply]; exact hy)
  -- On a layer of prime degree the class of invariant `1/p` maps to a generator of
  -- `H²(Gal(L/F), C_L)`; the Sylow and tower reduction carries the statement to every layer.
  rw [ideleToClassH2_apply]
  refine NormalLayer.map_eq_zero_of_prime_degree (ideleClassHom K) (fun L ↦ ideleSumLocalInv K L)
    (fun T y ↦ ideleSumLocalInv_infl K T y) (fun R y ↦ ideleSumLocalInv_res K R y) hker
    subsingleton_h1_globalFormation (fun L hp x ↦ ?_)
    (fun L hp y hy ↦ NormalLayer.map_eq_zero_of_natCard_H2_dvd_degree (ideleClassHom K) _ hker
      (natCard_H2_globalFormation_dvd_degree L)
      (exists_ideleSumLocalInv_eq_one_div_degree_of_prime L hp) hy) L hy
  have := NormalLayer.isCyclic_gal_of_prime_degree hp
  exact (surjective_ideleToClassH2_of_isCyclic K L x).imp fun y hy ↦
    by rw [ideleToClassH2_apply] at hy; exact hy

/-- **Killing the obstruction**: some refinement of every layer `L/F` is such that the inflation of
every class of `H²(Gal(L/F), C_L)` to it lifts to the ideles. -/
theorem exists_refinement_mem_range_ideleToClassH2 (Lay : NormalLayer (AbsoluteGaloisGroup K)) :
    ∃ (Lay' : NormalLayer (AbsoluteGaloisGroup K)) (T : LayerRefinement Lay Lay'),
      ∀ x : Lay.H (globalFormation K) 2,
        T.cohomologyInfl (globalFormation K) 2 x ∈ (ideleToClassH2 K Lay').range := by
  obtain ⟨Lay', T, hT⟩ := NormalLayer.exists_refinement_forall_exists_map_eq_cohomologyInfl
    (ideleClassHom K) (fun L ↦ ideleSumLocalInv K L) (fun R y ↦ ideleSumLocalInv_res K R y)
    (fun L y hy ↦ by
      have h := ideleToClassH2_eq_zero_iff (L := L) (y := y)
      rw [ideleToClassH2_apply] at h
      exact h.1 hy)
    (fun L y hy ↦ by
      have h := ideleToClassH2_eq_zero_iff (L := L) (y := y)
      rw [ideleToClassH2_apply] at h
      exact h.2 hy)
    subsingleton_h1_globalFormation (natCard_H2_globalFormation_dvd_degree Lay)
    (exists_refinement_ideleSumLocalInv_eq Lay)
  exact ⟨Lay', T, fun x ↦ (hT x).imp fun y hy ↦ by rw [ideleToClassH2_apply]; exact hy⟩

/-! ### The global invariant -/

/-- `exists_refinement_mem_range_ideleToClassH2`, for each class separately, in the form that
`descendedInv` takes. -/
private theorem exists_refinement_map_ideleClassHom_eq (L : NormalLayer (AbsoluteGaloisGroup K))
    (x : L.H (globalFormation K) 2) :
    ∃ (L' : NormalLayer (AbsoluteGaloisGroup K)) (T : LayerRefinement L L')
      (y : L'.H (ideleFormation K) 2),
      groupCohomology.map (MonoidHom.id L'.Gal) (L'.repMap (ideleClassHom K)) 2 y =
        T.cohomologyInfl (globalFormation K) 2 x := by
  obtain ⟨L', T, hT⟩ := exists_refinement_mem_range_ideleToClassH2 L
  obtain ⟨y, hy⟩ := hT x
  exact ⟨L', T, y, (ideleToClassH2_apply K L' y).symm.trans hy⟩

variable (K) in
/-- **The global invariant** `H²(Gal(L/F), C_L) → ℚ/ℤ` of a finite normal layer `L/F` inside
`Kˢ`: the invariant of a class is the sum of the local invariants of a lift to the ideles of its
inflation to some refinement of the layer. By `globalInv_eq` it does not depend on the refinement
or on the lift, and `globalInv_unique` characterizes it by the equations `globalInv_ideleToClassH2`
and `globalInv_infl`. -/
def globalInv (L : NormalLayer (AbsoluteGaloisGroup K)) :
    L.H (globalFormation K) 2 →+ AddCircle (1 : ℚ) :=
  descendedInv (ideleClassHom K) (fun L ↦ ideleSumLocalInv K L) (ideleSumLocalInv_infl K)
    exists_refinement_map_ideleClassHom_eq
    (fun _ _ h ↦ ideleToClassH2_eq_zero_iff.1 ((ideleToClassH2_apply K _ _).trans h)) L

/-- The global invariant is the invariant descended from the sum of the local invariants. -/
private theorem globalInv_eq_descendedInv :
    globalInv K = descendedInv (ideleClassHom K) (fun L ↦ ideleSumLocalInv K L)
      (ideleSumLocalInv_infl K) exists_refinement_map_ideleClassHom_eq
      (fun _ _ h ↦ ideleToClassH2_eq_zero_iff.1 ((ideleToClassH2_apply K _ _).trans h)) :=
  rfl

/-- **The global invariant of a class is the sum of the local invariants of a lift of an
inflation of it**: if the inflation of `x` to a refinement `L'` of `L` is the idele class of `y`,
then `globalInv K L x` is the sum of the local invariants of `y`. -/
theorem globalInv_eq {L L' : NormalLayer (AbsoluteGaloisGroup K)} (T : LayerRefinement L L')
    {x : L.H (globalFormation K) 2} {y : L'.H (ideleFormation K) 2}
    (h : ideleToClassH2 K L' y = T.cohomologyInfl (globalFormation K) 2 x) :
    globalInv K L x = ideleSumLocalInv K L' y := by
  rw [globalInv_eq_descendedInv]
  exact descendedInv_eq _ _ _ _ _ T ((ideleToClassH2_apply K L' y).symm.trans h)

/-- **The sum formula**, the first defining equation of the global invariant: the invariant of the
idele class of a class of `H²(Gal(L/F), I_L)` is the sum of its local invariants. -/
@[simp]
theorem globalInv_ideleToClassH2 (L : NormalLayer (AbsoluteGaloisGroup K))
    (y : L.H (ideleFormation K) 2) :
    globalInv K L (ideleToClassH2 K L y) = ideleSumLocalInv K L y := by
  rw [globalInv_eq_descendedInv, ideleToClassH2_apply, descendedInv_map]

/-- **Inflation invariance**, the second defining equation of the global invariant. -/
@[simp]
theorem globalInv_infl {L L' : NormalLayer (AbsoluteGaloisGroup K)} (T : LayerRefinement L L')
    (x : L.H (globalFormation K) 2) :
    globalInv K L' (T.cohomologyInfl (globalFormation K) 2 x) = globalInv K L x := by
  rw [globalInv_eq_descendedInv, descendedInv_infl]

/-- **The global invariant is determined by its two equations**: a family of homomorphisms
`H²(Gal(L/F), C_L) → ℚ/ℤ` that is the sum of the local invariants on idele classes and does not
change under inflation is the global invariant. -/
theorem globalInv_unique
    (f : ∀ L : NormalLayer (AbsoluteGaloisGroup K), L.H (globalFormation K) 2 →+ AddCircle (1 : ℚ))
    (hdesc : ∀ (L : NormalLayer (AbsoluteGaloisGroup K)) (y : L.H (ideleFormation K) 2),
      f L (ideleToClassH2 K L y) = ideleSumLocalInv K L y)
    (hinfl : ∀ {L L' : NormalLayer (AbsoluteGaloisGroup K)} (T : LayerRefinement L L')
      (x : L.H (globalFormation K) 2),
      f L' (T.cohomologyInfl (globalFormation K) 2 x) = f L x) :
    f = globalInv K := by
  rw [globalInv_eq_descendedInv]
  exact descendedInv_unique _ _ _ _ _ f
    (fun L y ↦ by rw [← ideleToClassH2_apply]; exact hdesc L y) hinfl

/-- **Restriction multiplies the global invariant by the relative degree.** -/
@[simp]
theorem globalInv_res {small big : NormalLayer (AbsoluteGaloisGroup K)}
    (R : LayerRestriction small big) (x : big.H (globalFormation K) 2) :
    globalInv K small (R.cohomologyRes (globalFormation K) 2 x) =
      R.relativeDegree • globalInv K big x := by
  rw [globalInv_eq_descendedInv,
    descendedInv_res _ _ _ _ _ (fun R y ↦ ideleSumLocalInv_res K R y)]

/-- **Conjugation preserves the global invariant.** -/
@[simp]
theorem globalInv_conj (L : NormalLayer (AbsoluteGaloisGroup K)) (g : AbsoluteGaloisGroup K)
    (x : L.H (globalFormation K) 2) :
    globalInv K (L.conjugate g) ((L.conjugateCohomologyIso (globalFormation K) g 2).hom x) =
      globalInv K L x := by
  rw [globalInv_eq_descendedInv,
    descendedInv_conj _ _ _ _ _ (fun L g y ↦ ideleSumLocalInv_conj K L g y)]

/-- **The global invariant is injective**, because the idele-class `H¹` vanishes and the sum of
the local invariants vanishes only on the classes that die in the idele classes. -/
theorem globalInv_injective (L : NormalLayer (AbsoluteGaloisGroup K)) :
    Function.Injective (globalInv K L) := by
  rw [globalInv_eq_descendedInv]
  exact descendedInv_injective _ _ _ _ _ subsingleton_h1_globalFormation
    (fun _ _ h ↦ (ideleToClassH2_apply K _ _).symm.trans (ideleToClassH2_eq_zero_iff.2 h)) L

/-- **The image of the global invariant of a layer of degree `n` is the `n`-torsion of `ℚ/ℤ`.** -/
theorem range_globalInv (L : NormalLayer (AbsoluteGaloisGroup K)) :
    Set.range (globalInv K L) =
      (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) L.degree : Set (AddCircle (1 : ℚ))) := by
  rw [globalInv_eq_descendedInv]
  exact range_descendedInv _ _ _ _ _ subsingleton_h1_globalFormation
    (fun _ _ h ↦ (ideleToClassH2_apply K _ _).symm.trans (ideleToClassH2_eq_zero_iff.2 h))
    (fun R y ↦ ideleSumLocalInv_res K R y) exists_refinement_ideleSumLocalInv_eq L

/-! ### The global class formation -/

variable (K) in
/-- **The global class formation**: the idele-class formation of `K` is a class formation, whose
invariant on a layer is the global invariant (`globalClassFormation_inv`). -/
def globalClassFormation : ClassFormation (globalFormation K) :=
  ClassFormation.ofDescendedInv (ideleClassHom K) (fun L ↦ ideleSumLocalInv K L)
    (ideleSumLocalInv_infl K) exists_refinement_map_ideleClassHom_eq
    (fun _ _ h ↦ ideleToClassH2_eq_zero_iff.1 ((ideleToClassH2_apply K _ _).trans h))
    subsingleton_h1_globalFormation
    (fun _ _ h ↦ (ideleToClassH2_apply K _ _).symm.trans (ideleToClassH2_eq_zero_iff.2 h))
    (fun R y ↦ ideleSumLocalInv_res K R y) (fun L g y ↦ ideleSumLocalInv_conj K L g y)
    exists_refinement_ideleSumLocalInv_eq

/-- **The invariant of the global class formation is the global invariant**, the sum of the local
invariants of a lift to the ideles. -/
@[simp]
theorem globalClassFormation_inv (L : NormalLayer (AbsoluteGaloisGroup K)) :
    (globalClassFormation K).inv L = globalInv K L := by
  rw [globalClassFormation, ClassFormation.ofDescendedInv_inv, globalInv_eq_descendedInv]

/-- **The local invariants of an idele lift of the fundamental class sum to `1/[L:F]`**: if the
idele class of `y` is the fundamental class of the layer `L/F` in the global class formation, then
the local invariants of `y` sum to `1/[L:F]`. -/
theorem ideleSumLocalInv_fundamentalClass {L : NormalLayer (AbsoluteGaloisGroup K)}
    {y : L.H (ideleFormation K) 2}
    (hy : ideleToClassH2 K L y = (globalClassFormation K).fundamentalClass L) :
    ideleSumLocalInv K L y = ((1 / L.degree : ℚ) : AddCircle (1 : ℚ)) := by
  rw [← globalInv_ideleToClassH2, hy, ← globalClassFormation_inv,
    ClassFormation.inv_fundamentalClass]

end TauCeti.ClassFieldTheory

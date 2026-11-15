/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.NoetherianCech.Topology

/-!
# The filtration of the rational-localization Čech complex is a subcomplex

Restriction to a larger intersection preserves each power of the ideal of definition, not
just sufficiently deep powers. Consequently the alternating Čech differential preserves
Huber's filtration `K_i^p`. This allows the differentials to be restricted to each level,
as required when estimating coboundaries of deep cocycles.

No finiteness, noetherianity or completeness hypothesis is needed. The generating set of the
module is arbitrary; in particular the result applies before choosing a finite spanning lattice.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, proof of Theorem 2.5, Case I, the subcomplexes preceding (1.3.1).
-/

public section

open LocalizedModule

namespace TauCeti.Huber.NoetherianCech

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  {ι : Type*} (f : ι → B) (P : PairOfDefinition B)
  (M : Type*) [AddCommGroup M] [Module B M]
  (hf : Ideal.span (Set.range f) = ⊤)

private theorem map_erase_faceIdeal_pow_le [DecidableEq ι]
    (p : ℕ) (S : Finset ι) (a : S) (i : ℕ) :
    letI := faceTopology f P hf p (S.erase a.1)
    letI := faceTopology f P hf (p + 1) S
    ((facePair f P hf p (S.erase a.1)).idealOfDefinition ^ i).map
      ((cechLocalizationEraseRingHom f S a).restrict _ _
        fun _ hr ↦ eraseRingHom_mem_ringOfDefinition f P hf p S a hr) ≤
      (facePair f P hf (p + 1) S).idealOfDefinition ^ i := by
  let _ := faceTopology f P hf p (S.erase a.1)
  let _ := faceTopology f P hf (p + 1) S
  rw [Ideal.map_pow]
  exact pow_le_pow_left' (map_eraseRingHom_idealOfDefinition_le f P hf p S a) i

/-- Restriction from a deleted face preserves every level of the face filtration. -/
theorem cechLocalizationRestriction_erase_mem_faceFiltration [DecidableEq ι]
    (N : Set M) (p : ℕ) (S : Finset ι) (a : S) (i : ℕ)
    {x : LocalizedModule (.powers (∏ j ∈ S.erase a.1, f j)) M}
    (hx : x ∈ faceFiltration f P M hf N p (S.erase a.1) i) :
    cechLocalizationRestriction M f (S.erase_subset a.1) x ∈
      faceFiltration f P M hf N (p + 1) S i := by
  let R := Localization.Away (∏ j ∈ S.erase a.1, f j)
  let T := Localization.Away (∏ j ∈ S, f j)
  let Q := LocalizedModule (.powers (∏ j ∈ S, f j)) M
  let φ : R →+* T := cechLocalizationEraseRingHom f S a
  let _ := faceTopology f P hf p (S.erase a.1)
  let _ := faceTopology f P hf (p + 1) S
  let D := (facePair f P hf p (S.erase a.1)).ringOfDefinition
  let E := (facePair f P hf (p + 1) S).ringOfDefinition
  have hφ : ∀ r ∈ D, φ r ∈ E :=
    fun _ hr ↦ eraseRingHom_mem_ringOfDefinition f P hf p S a hr
  let ψ : D →+* E := φ.restrict D E hφ
  have hψ (r : D) : (ψ r : T) = φ r := rfl
  -- Restriction preserves the ideal power acting on the lattice.
  have hI r hr := map_erase_faceIdeal_pow_le f P hf p S a i
    (Ideal.mem_map_of_mem ψ (x := r) hr)
  let _ : Module R Q := Module.compHom Q φ
  have : IsScalarTower B R Q := isScalarTower_compHom_cechLocalizationEraseRingHom M f S a
  let u := (cechLocalizationRestriction M f (S.erase_subset a.1)).extendScalarsOfIsLocalization
    (.powers (∏ j ∈ S.erase a.1, f j)) R
  have hu (r : D) (y : LocalizedModule (.powers (∏ j ∈ S.erase a.1, f j)) M) :
      u (r • y) = (ψ r : T) • u y := by
    rw [Subring.smul_def, hψ]
    exact u.map_smul (r : R) y
  -- It also preserves the lattice: generators map to the same localized generators,
  -- and scalar multiplication is transported along the map of rings of definition.
  have hspan : ∀ y ∈ Submodule.span D (mkLinearMap _ M '' N),
      u y ∈ Submodule.span E (mkLinearMap _ M '' N) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      exact Submodule.subset_span ⟨m, hm, (cechLocalizationRestriction_mk M f _ m).symm⟩
    | zero => simp
    | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [hu]
      exact Submodule.smul_mem _ (ψ r) hy
  -- Combine lattice preservation with ideal-power preservation on each simple product.
  rw [mem_faceFiltration] at hx ⊢
  refine Submodule.smul_induction_on hx (fun r hr y hy ↦ ?_) (fun y z hy hz ↦ ?_)
  · rw [← LinearMap.extendScalarsOfIsLocalization_apply'
      (.powers (∏ j ∈ S.erase a.1, f j)) R _ (r • y), hu]
    exact Submodule.smul_mem_smul (hI r hr) (hspan y hy)
  · simpa using Submodule.add_mem _ hy hz

/-- The alternating differential preserves each level of Huber's filtration. -/
theorem cechLocalizationDifferential_mem_filtration [LinearOrder ι]
    (N : Set M) (p i : ℕ) {x : cechLocalizationTerm M f p}
    (hx : x ∈ filtration f P M hf N p i) :
    cechLocalizationDifferential M f p x ∈ filtration f P M hf N (p + 1) i := by
  rw [mem_filtration] at hx ⊢
  intro S
  rw [cechLocalizationDifferential_apply]
  apply AddSubgroup.sum_mem
  intro a _
  have h := cechLocalizationRestriction_erase_mem_faceFiltration f P M hf N p S.1 a i
    (hx ⟨S.1.erase a.1, by rw [Finset.card_erase_of_mem a.2, S.2]; rfl⟩)
  rcases neg_one_pow_eq_or (R := B) (S.1.filter (· < a.1)).card with hs | hs <;>
    simp [hs, h]

section Differential

variable [LinearOrder ι] (N : Set M)

/-- The differential restricted to level `i` of the filtration. These maps form the
nonaugmented Čech subcomplex `K_i`. -/
noncomputable def filtrationDifferential (p i : ℕ) :
    filtration f P M hf N p i →+ filtration f P M hf N (p + 1) i :=
  ((cechLocalizationDifferential M f p).toAddMonoidHom.domRestrict
    (filtration f P M hf N p i)).codRestrict (filtration f P M hf N (p + 1) i)
      fun x ↦ cechLocalizationDifferential_mem_filtration f P M hf N p i x.property

/-- The restricted differential is the original differential on the underlying cochain. -/
@[simp]
theorem coe_filtrationDifferential (p i : ℕ) (x : filtration f P M hf N p i) :
    (filtrationDifferential f P M hf N p i x : cechLocalizationTerm M f (p + 1)) =
      cechLocalizationDifferential M f p x :=
  (rfl)

/-- Consecutive restricted differentials compose to zero. -/
@[simp]
theorem filtrationDifferential_comp_differential (p i : ℕ) :
    (filtrationDifferential f P M hf N (p + 1) i).comp
      (filtrationDifferential f P M hf N p i) = 0 := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  simpa only [AddMonoidHom.comp_apply, coe_filtrationDifferential, AddMonoidHom.zero_apply,
    ZeroMemClass.coe_zero, LinearMap.comp_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun (cechLocalizationDifferential_comp_differential M f p) x

/-- Inclusions between filtration levels commute with the restricted differentials. -/
theorem filtrationDifferential_comp_inclusion (p : ℕ) {i j : ℕ} (hij : i ≤ j) :
    (filtrationDifferential f P M hf N p i).comp
        (AddSubgroup.inclusion (filtration_antitone f P M hf N p hij)) =
      (AddSubgroup.inclusion (filtration_antitone f P M hf N (p + 1) hij)).comp
        (filtrationDifferential f P M hf N p j) := by
  ext x
  rfl

end Differential

end TauCeti.Huber.NoetherianCech

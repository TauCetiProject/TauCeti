/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.HigmanSims.Basic
public import TauCeti.GroupTheory.TriangleGroup.Perfect

/-!
# Perfectness of the Higman--Sims presentation and permutation model

The exact Higman--Sims presentation is perfect, already from its first three relations
`a² = b⁵ = (ab)¹¹ = 1`: it is a quotient of the perfect oriented triangle group `Δ(5, 2, 11)`.
The canonical ATLAS permutation model is consequently perfect through the existing presentation
surjection. Neither statement assumes finiteness or simplicity of the presented group.

The reversed assignment of the two triangle generators respects the triangle presentation's
product `y * x`; no change of permutation multiplication convention is involved.

## References

* J. N. Bray, ATLAS presentation `HSG1-P1`, demonstration of correctness,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/HSG1-P1>.
-/

public section

namespace TauCeti.Sporadic

/-- The exact thirteen-relator Higman--Sims presentation is perfect. -/
instance isPerfect_hsPresentation : Group.IsPerfect hsPresentation.Group := by
  let a : hsPresentation.Group := PresentedGroup.of ⟨0, by simp⟩
  let b : hsPresentation.Group := PresentedGroup.of ⟨1, by simp⟩
  have rel (t : Relator (Fin hsPresentation.generatorCount))
      (ht : t ∈ hsPresentation.transcribed) :
      t.eval (PresentedGroup.of : Fin hsPresentation.generatorCount → hsPresentation.Group) =
        1 := by
    simpa only [Relator.lift_toFreeGroup, GroupPresentation.homEquiv_apply,
      MonoidHom.id_apply] using (hsPresentation.homEquiv (MonoidHom.id _)).property t ht
  have ha : a ^ 2 = 1 := by
    simpa only [Relator.eval_pow, Relator.eval_gen] using
      rel (.pow (.gen ⟨0, by simp⟩) 2) (by rw [hsPresentation_transcribed]; simp)
  have hb : b ^ 5 = 1 := by
    simpa only [Relator.eval_pow, Relator.eval_gen] using
      rel (.pow (.gen ⟨1, by simp⟩) 5) (by rw [hsPresentation_transcribed]; simp)
  have hab : (a * b) ^ 11 = 1 := by
    simpa only [Relator.eval_pow, Relator.eval_mul, Relator.eval_gen] using
      rel (.pow (.mul (.gen ⟨0, by simp⟩) (.gen ⟨1, by simp⟩)) 11)
        (by rw [hsPresentation_transcribed]; simp)
  let f : TriangleGroup 5 2 11 →* hsPresentation.Group :=
    TriangleGroup.lift b a (a * b)⁻¹ hb ha
      (by rw [inv_pow, hab, inv_one]) (by simp [mul_assoc])
  have hf : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, TriangleGroup.range_eq_closure]
    simp only [f, TriangleGroup.lift_x, TriangleGroup.lift_y]
    apply top_unique
    rw [← PresentedGroup.closure_range_of]
    apply Subgroup.closure_mono
    rintro _ ⟨i, rfl⟩
    have hi : i.val < 2 := by simpa using i.isLt
    have hcases : i = ⟨0, by simp⟩ ∨ i = ⟨1, by simp⟩ := by
      rcases (by omega : i.val = 0 ∨ i.val = 1) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hcases with rfl | rfl <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    · exact Or.inr rfl
    · exact Or.inl rfl
  have := TriangleGroup.isPerfect_of_coprime (a := 5) (b := 2) (c := 11)
    (by decide) (by decide) (by decide)
  exact Group.IsPerfect.ofSurjective hf

/-- The exact carrier attached to the Higman--Sims sporadic name is perfect. -/
instance isPerfect_HS_group : Group.IsPerfect SporadicName.HS.Group := by
  exact (congrArg (fun P : GroupPresentation => Group.IsPerfect P.Group)
    SporadicName.presentation_HS).mpr isPerfect_hsPresentation

/-- The canonical ATLAS Higman--Sims permutation model is perfect. -/
instance HS.isPerfect : Group.IsPerfect HS := by
  obtain ⟨f, hf⟩ := exists_surjective_HS
  exact Group.IsPerfect.ofSurjective hf

end TauCeti.Sporadic

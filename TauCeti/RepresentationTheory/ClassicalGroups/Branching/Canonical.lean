/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Branching.Decomposition
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight
import TauCeti.RepresentationTheory.Rep.DirectSum.Basic

/-!
# Canonical summands in the branching of rational Weyl modules

The restriction of the rational Weyl module `V_λ` from `GL (n + 1) ℂ` to `GL n ℂ` has
exactly one subrepresentation isomorphic to `V_μ` for each dominant weight `μ` interlacing `λ`.
This strengthens an abstract branching equivalence to a uniqueness statement about subspaces
inside the given module. Iterating these unique summands is the construction of the canonical
lines underlying a Gelfand–Tsetlin basis; choosing vectors and their normalization is additional
data.

The multiplicity calculation is made in the space of intertwining maps: its dimension is one
for an interlacing weight and zero otherwise. Consequently every nonzero intertwiner from a
fixed `V_μ` has the same image.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants* (2009), Section 8.1.
-/

public section

open CategoryTheory Module Representation

namespace TauCeti

variable {n : ℕ}

/-- The multiplicity of `V_μ` in the restriction of `V_λ` to `GL n ℂ` is one exactly when
`μ` interlaces `λ`, and zero otherwise. This includes arbitrary integer dominant weights. -/
@[simp]
theorem finrank_intertwiningMap_rationalWeylRep_comp_glBlockSucc
    (l : DominantWeight (n + 1)) (m : DominantWeight n) :
    finrank ℂ (IntertwiningMap (rationalWeylRep ℂ n m)
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n))) =
        if m ∈ interlacingWeights l then 1 else 0 := by
  classical
  -- Supply the additive groups under the dependent direct-sum binder, as in the branching
  -- equivalence, so that its carrier can be bundled by `Rep.of`.
  let _ (j : interlacingWeights l) :
      AddCommGroup (weylModuleOfShape ℂ n (j : DominantWeight n).detShiftShape).toSubmodule :=
    inferInstance
  let A := Rep.of (X := ↥(weylModuleOfShape ℂ n m.detShiftShape).toSubmodule)
    (rationalWeylRep ℂ n m)
  let B (j : interlacingWeights l) := Rep.of
    (X := ↥(weylModuleOfShape ℂ n (j : DominantWeight n).detShiftShape).toSubmodule)
    (rationalWeylRep ℂ n j)
  have (j : interlacingWeights l) : Module.Finite ℂ (A ⟶ B j) :=
    Module.Finite.equiv (Rep.homLinearEquiv A (B j)).symm
  obtain ⟨e⟩ := nonempty_equiv_rationalWeylRep_comp_glBlockSucc n l
  have hdim (j : interlacingWeights l) :
      finrank ℂ (A ⟶ B j) = if m = (j : DominantWeight n) then 1 else 0 := by
    rw [(Rep.homLinearEquiv A (B j)).finrank_eq]
    by_cases h : m = (j : DominantWeight n)
    · subst m
      simp [A, B, IsIrreducible.finrank_intertwiningMap_self]
    · have : IsEmpty ((rationalWeylRep ℂ n m).Equiv (rationalWeylRep ℂ n j)) :=
        ⟨fun f => h ((nonempty_equiv_rationalWeylRep_iff ℂ).mp ⟨f⟩)⟩
      simp [A, B, h, finrank_zero_of_subsingleton]
  rw [← (Rep.homLinearEquiv A
    (Rep.of (X := ↥(weylModuleOfShape ℂ (n + 1) l.detShiftShape).toSubmodule)
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)))).finrank_eq,
    (Linear.homCongr ℂ (Iso.refl A) (Rep.mkIso e)).finrank_eq,
    (Rep.homDirectSumLinearEquiv A B).finrank_eq, Module.finrank_pi_fintype]
  simp_rw [hdim]
  rw [Finset.sum_coe_sort (interlacingWeights l)
    (fun j : DominantWeight n => if m = j then (1 : ℕ) else 0)]
  simp only [Finset.sum_ite_eq]

/-- An interlacing dominant weight specifies a unique subrepresentation of the restricted Weyl
module isomorphic to its Weyl module. The subspace is independent of any branching equivalence. -/
theorem existsUnique_subrepresentation_rationalWeylRep_comp_glBlockSucc
    (l : DominantWeight (n + 1)) (m : DominantWeight n) (hm : m ∈ interlacingWeights l) :
    ∃! S : Subrepresentation
        ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)),
      Nonempty ((rationalWeylRep ℂ n m).Equiv S.toRepresentation) := by
  -- Fix the additive groups of the two submodule carriers before inferring the additive
  -- group structure on their space of intertwining maps.
  let _ : AddCommGroup (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule := inferInstance
  let _ : AddCommGroup (weylModuleOfShape ℂ (n + 1) l.detShiftShape).toSubmodule := inferInstance
  have hdim : finrank ℂ (IntertwiningMap (rationalWeylRep ℂ n m)
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n))) = 1 := by
    simp [finrank_intertwiningMap_rationalWeylRep_comp_glBlockSucc, hm]
  have := Module.nontrivial_of_finrank_eq_succ hdim
  obtain ⟨f, hf⟩ := exists_ne (0 : IntertwiningMap (rationalWeylRep ℂ n m)
    ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)))
  have hinj : Function.Injective f :=
    (IsIrreducible.injective_or_eq_zero
      (V := ↥(weylModuleOfShape ℂ n m.detShiftShape).toSubmodule)
      (W := ↥(weylModuleOfShape ℂ (n + 1) l.detShiftShape).toSubmodule) f).resolve_right hf
  refine ⟨f.range, ⟨f.equivOfRange hinj
    (IntertwiningMap.range_toSubmodule _ _ f).symm⟩, ?_⟩
  intro S ⟨e⟩
  let g := S.subtype.comp e.toIntertwiningMap
  have hrange : LinearMap.range g.toLinearMap = S.toSubmodule := by
    simp only [g, IntertwiningMap.comp_toLinearMap, Subrepresentation.toLinearMap_subtype]
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range e.toLinearEquiv),
      Submodule.range_subtype]
  have := (isIrreducible_rationalWeylRep ℂ n m).nontrivial
  have hg : g ≠ 0 := by
    have hinj : Function.Injective g := by
      intro x y h
      apply EquivLike.injective e
      apply Subtype.ext
      simpa only [g, IntertwiningMap.comp_apply, Subrepresentation.coe_subtype,
        Representation.Equiv.coe_toIntertwiningMap] using h
    exact fun h => LinearMap.ne_zero_of_injective hinj
      (congrArg IntertwiningMap.toLinearMap h)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hf g
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hg (by simpa using hc.symm)
  apply Subrepresentation.toSubmodule_injective
  rw [← hrange, ← hc, IntertwiningMap.toLinearMap_smul,
    LinearMap.range_smul _ c hc0, IntertwiningMap.range_toSubmodule]

end TauCeti

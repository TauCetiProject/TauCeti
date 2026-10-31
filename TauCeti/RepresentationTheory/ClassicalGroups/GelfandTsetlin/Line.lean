/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DirectSum.Sigma
public import TauCeti.RepresentationTheory.ClassicalGroups.Branching.Canonical
import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Dimension
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Dimension

/-!
# The Gelfand–Tsetlin lines of a rational Weyl module

Restricting the rational Weyl module `V_λ` of `GL (n + 1) ℂ` along the block inclusion
`GL n ℂ ↪ GL (n + 1) ℂ` decomposes it, without multiplicity, into copies of the `V_μ` with `μ`
interlacing `λ`, and the copy of each `V_μ` is a canonical subspace of `V_λ`
(`TauCeti.existsUnique_subrepresentation_rationalWeylRep_comp_glBlockSucc`). Iterating down the
chain `GL 0 ⊂ GL 1 ⊂ ⋯ ⊂ GL n` splits `V_λ` into subspaces indexed by the successive choices of
interlacing weights, that is, by the Gelfand–Tsetlin patterns `P` with top weight `λ`. At the
bottom of the chain the module is a line, so every piece is a line: the **Gelfand–Tsetlin line**
`TauCeti.gtLine λ P`.

The line of a pattern with `n + 1` rows is the image of the line of its truncation under an
embedding of `V_μ` in the restriction of `V_λ`, where `μ` is the second row. Such an embedding is
unique up to a nonzero scalar, because `V_μ` occurs once, so the line does not depend on the
embedding: `TauCeti.gtLine_succ` holds for every nonzero intertwiner. The lines are canonical; a
basis of `V_λ` indexed by the patterns further requires a normalized vector in each line.

The decomposition into lines is an internal direct sum, `TauCeti.isInternal_gtLine`, so the
lines of the patterns with top weight `λ` are independent and span `V_λ`. This is the
decomposition underlying the Gelfand–Tsetlin basis, whose vectors are normalized generators of
these lines.

## Main definitions

* `TauCeti.gtLine`: the Gelfand–Tsetlin line of a pattern in the rational Weyl module of its top
  weight.

## Main results

* `TauCeti.gtLine_succ`: the line of a pattern is the image of the line of its truncation under
  any nonzero intertwiner from the Weyl module of the second row.
* `TauCeti.finrank_gtLine`: each Gelfand–Tsetlin line is one-dimensional.
* `TauCeti.isInternal_gtLine`: the rational Weyl module is the internal direct sum of the
  Gelfand–Tsetlin lines of the patterns with its top weight.

## References

* I. M. Gelfand and M. L. Tsetlin, *Finite-dimensional representations of the group of unimodular
  matrices*, Doklady Akad. Nauk SSSR **71** (1950), 825–828.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §15.3.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants* (2009), Section 8.1.
-/

public section

open Module Representation

namespace TauCeti

/-- **The Gelfand–Tsetlin line** of a pattern `P` with top weight `λ`, a subspace of the rational
Weyl module `V_λ` of `GL n ℂ`.

For `n = 0` it is the whole module, which is a line. For `n + 1` rows it is the image of the line
of the truncation of `P`, inside the Weyl module `V_μ` of the second row `μ`, under a nonzero
intertwiner from `V_μ` to the restriction of `V_λ` to `GL n ℂ`. The choice of intertwiner does not
matter (`TauCeti.gtLine_succ`). -/
noncomputable def gtLine : ∀ {n : ℕ} (l : DominantWeight n),
    {P : GTPattern n // P.topWeight = l} →
      Submodule ℂ (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule
  | 0, _, _ => ⊤
  | n + 1, l, P => (gtLine P.1.truncate.topWeight ⟨P.1.truncate, rfl⟩).map
      (Classical.epsilon fun f : IntertwiningMap (rationalWeylRep ℂ n P.1.truncate.topWeight)
        ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)) ↦ f ≠ 0).toLinearMap

/-- For `GL 0 ℂ` the Gelfand–Tsetlin line of the unique pattern is the whole Weyl module. -/
@[simp]
theorem gtLine_zero (l : DominantWeight 0) (P : {P : GTPattern 0 // P.topWeight = l}) :
    gtLine l P = ⊤ := by
  rw [gtLine]

variable {n : ℕ}

/-- An interlacing weight `μ` has a nonzero intertwiner from `V_μ` to the restriction of `V_λ`. -/
private theorem exists_intertwiningMap_ne_zero {l : DominantWeight (n + 1)}
    {m : DominantWeight n} (hm : m ∈ interlacingWeights l) :
    ∃ f : IntertwiningMap (rationalWeylRep ℂ n m)
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)), f ≠ 0 := by
  -- Fix the additive groups of the two submodule carriers before inferring the additive
  -- group structure on their space of intertwining maps.
  let _ : AddCommGroup (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule := inferInstance
  let _ : AddCommGroup (weylModuleOfShape ℂ (n + 1) l.detShiftShape).toSubmodule := inferInstance
  have hdim : finrank ℂ (IntertwiningMap (rationalWeylRep ℂ n m)
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n))) = 1 := by
    simp [finrank_intertwiningMap_rationalWeylRep_comp_glBlockSucc, hm]
  have := Module.nontrivial_of_finrank_eq_succ hdim
  exact exists_ne 0

/-- Two nonzero intertwiners from `V_μ` to the restriction of `V_λ`, for `μ` interlacing `λ`,
carry every subspace of `V_μ` to the same subspace of `V_λ`: they differ by a nonzero scalar. -/
private theorem map_eq_map_of_ne_zero {l : DominantWeight (n + 1)} {m : DominantWeight n}
    (hm : m ∈ interlacingWeights l)
    {f g : IntertwiningMap (rationalWeylRep ℂ n m)
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n))} (hf : f ≠ 0) (hg : g ≠ 0)
    (W : Submodule ℂ (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule) :
    W.map f.toLinearMap = W.map g.toLinearMap := by
  -- Fix the additive groups of the carriers, as in `exists_intertwiningMap_ne_zero`.
  let _ : AddCommGroup (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule := inferInstance
  let _ : AddCommGroup (weylModuleOfShape ℂ (n + 1) l.detShiftShape).toSubmodule := inferInstance
  have hdim : finrank ℂ (IntertwiningMap (rationalWeylRep ℂ n m)
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n))) = 1 := by
    simp [finrank_intertwiningMap_rationalWeylRep_comp_glBlockSucc, hm]
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hdim hf g
  have hc : c ≠ 0 := by
    rintro rfl
    exact hg (zero_smul ℂ f)
  rw [IntertwiningMap.toLinearMap_smul, Submodule.map_smul _ _ _ hc]

/-- **The Gelfand–Tsetlin line does not depend on the embedding.** The line of a pattern `P` with
`n + 1` rows is the image of the line of its truncation under *every* nonzero intertwiner from the
Weyl module of the second row of `P` to the restriction of `V_λ` to `GL n ℂ`. -/
theorem gtLine_succ (l : DominantWeight (n + 1)) (P : {P : GTPattern (n + 1) // P.topWeight = l})
    (f : IntertwiningMap (rationalWeylRep ℂ n P.1.truncate.topWeight)
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n))) (hf : f ≠ 0) :
    gtLine l P = (gtLine P.1.truncate.topWeight ⟨P.1.truncate, rfl⟩).map f.toLinearMap := by
  have hm : P.1.truncate.topWeight ∈ interlacingWeights l := by
    have h := P.1.topWeight_truncate_mem_interlacingWeights
    rwa [P.2] at h
  rw [gtLine]
  exact map_eq_map_of_ne_zero hm (Classical.epsilon_spec (exists_intertwiningMap_ne_zero hm))
    hf _

/-- **Each Gelfand–Tsetlin line is a line.** -/
@[simp]
theorem finrank_gtLine : ∀ {n : ℕ} (l : DominantWeight n)
    (P : {P : GTPattern n // P.topWeight = l}), finrank ℂ (gtLine l P) = 1
  | 0, l, P => by
    rw [gtLine_zero, finrank_top]
    exact (finrank_rationalWeylFDRep ℂ 0 l).trans
      ((GTPattern.card_topWeight_eq_weylDimension l).symm.trans Nat.card_unique)
  | n + 1, l, P => by
    have hm : P.1.truncate.topWeight ∈ interlacingWeights l := by
      have h := P.1.topWeight_truncate_mem_interlacingWeights
      rwa [P.2] at h
    obtain ⟨f, hf⟩ := exists_intertwiningMap_ne_zero hm
    have hinj : Function.Injective f :=
      (IsIrreducible.injective_or_eq_zero
        (V := ↥(weylModuleOfShape ℂ n P.1.truncate.topWeight.detShiftShape).toSubmodule)
        (W := ↥(weylModuleOfShape ℂ (n + 1) l.detShiftShape).toSubmodule) f).resolve_right hf
    rw [gtLine_succ l P f hf, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq]
    exact finrank_gtLine _ _

open scoped Classical in
/-- **The Gelfand–Tsetlin decomposition.** The rational Weyl module `V_λ` of `GL n ℂ` is the
internal direct sum of the Gelfand–Tsetlin lines of the patterns with top weight `λ`. -/
theorem isInternal_gtLine : ∀ {n : ℕ} (l : DominantWeight n), DirectSum.IsInternal (gtLine l)
  | 0, l =>
    -- The ring and the carrier are given explicitly: left to unification, the semiring structure
    -- of `ℂ` in `Submodule ℂ _` must be matched with `Ring.toSemiring` of an unknown ring, and
    -- elaboration times out.
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (R := ℂ)
      (M := (weylModuleOfShape ℂ 0 l.detShiftShape).toSubmodule) (iSupIndep_subsingleton _)
      (eq_top_iff.mpr (le_iSup_of_le default (gtLine_zero l _).ge))
  | n + 1, l => by
    obtain ⟨e⟩ := nonempty_equiv_rationalWeylRep_comp_glBlockSucc n l
    -- The embedding of each summand `V_μ` of the branching decomposition in `V_λ`.
    let ι (m : interlacingWeights l) : IntertwiningMap (rationalWeylRep ℂ n m)
        ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)) :=
      e.symm.toIntertwiningMap.comp
        ((DirectSum.lof ℂ _ (fun m : interlacingWeights l ↦
          ↥(weylModuleOfShape ℂ n (m : DominantWeight n).detShiftShape).toSubmodule) m
          ).intertwiningMap_of_isIntertwiningMap _ _ fun g v ↦ by
            simp [DirectSum.lmap_lof])
    have hι (m : interlacingWeights l) : ι m ≠ 0 := by
      have := (isIrreducible_rationalWeylRep ℂ n m).nontrivial
      obtain ⟨v, hv⟩ := exists_ne (0 : (weylModuleOfShape ℂ n
        (m : DominantWeight n).detShiftShape).toSubmodule)
      intro h
      refine hv (DirectSum.of_injective (β := fun m : interlacingWeights l ↦
        ↥(weylModuleOfShape ℂ n (m : DominantWeight n).detShiftShape).toSubmodule) m
        (e.symm.injective ?_))
      simpa [ι, DirectSum.lof_eq_of] using congrArg (fun f ↦ f v) h
    have hsigma := e.symm.toLinearEquiv.isInternal_sigma_map
      (B := fun m Q ↦ gtLine (m : DominantWeight n) Q) fun m ↦ isInternal_gtLine _
    have hline : gtLine l = (fun x ↦ (gtLine (x.1 : DominantWeight n) x.2).map
        (e.symm.toLinearEquiv.toLinearMap ∘ₗ DirectSum.lof ℂ _ _ x.1)) ∘
          GTPattern.truncateTopWeightSigmaEquiv l :=
      funext fun P ↦ by
        have hm : P.1.truncate.topWeight ∈ interlacingWeights l := by
          have h := P.1.topWeight_truncate_mem_interlacingWeights
          rwa [P.2] at h
        rw [Function.comp_apply, GTPattern.truncateTopWeightSigmaEquiv_apply l P hm]
        exact gtLine_succ l P (ι ⟨_, hm⟩) (hι _)
    rw [hline]
    exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (R := ℂ)
      (M := (weylModuleOfShape ℂ (n + 1) l.detShiftShape).toSubmodule)
      (hsigma.submodule_iSupIndep.comp (GTPattern.truncateTopWeightSigmaEquiv l).injective)
      ((GTPattern.truncateTopWeightSigmaEquiv l).iSup_comp.trans hsigma.submodule_iSup_eq_top)

end TauCeti

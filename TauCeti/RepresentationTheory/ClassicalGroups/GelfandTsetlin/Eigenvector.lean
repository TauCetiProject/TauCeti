/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.GelfandInvariant.HighestWeight
public import TauCeti.Algebra.Lie.UniversalEnveloping.Lift
public import TauCeti.RepresentationTheory.ClassicalGroups.Branching.Differential
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Line
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Differential
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight

/-!
# The Gelfand–Tsetlin lines are eigenlines of the Gelfand–Tsetlin generators

A rational representation `ρ` of `GL n ℂ` differentiates to a representation `dρ` of `𝔤𝔩ₙ(ℂ)`
(`TauCeti.IsRationalRep.differential`), and hence to an action
`UniversalEnvelopingAlgebra.lift ℂ dρ` of the universal enveloping algebra `U(𝔤𝔩ₙ)`. The
Gelfand–Tsetlin generators `TauCeti.gelfandTsetlinGenerator` of `U(𝔤𝔩ₙ)` are the images of the
Gelfand invariants `Cᵣ = trace (𝔼 ^ r)` of the upper-left corners `𝔤𝔩ₖ ⊆ 𝔤𝔩ₙ`.

This file proves that on the rational Weyl module `V_λ` they act diagonally in the
Gelfand–Tsetlin decomposition (`TauCeti.isInternal_gtLine`): every vector of the
Gelfand–Tsetlin line `TauCeti.gtLine λ P` of a pattern `P` is an eigenvector of the generator of
degree `r` at level `k`, with eigenvalue the highest-weight eigenvalue
`TauCeti.gelfandEigenvalue` of `Cᵣ` at the row `(P 0 k, …, P (k - 1) k)` of `P`. Since these
eigenvalues determine the pattern (`TauCeti.GTPattern.eq_of_forall_gelfandEigenvalue_eq`), the
lines are told apart by the joint eigencharacter of the generators.

## The argument

At the top level `k = n` the generator is the Gelfand invariant of `𝔤𝔩ₙ` itself. It is central
in `U(𝔤𝔩ₙ)`, the differential of `V_λ` is irreducible, and a highest weight vector of `V_λ` is one
of weight `λ` for `𝔤𝔩ₙ` (`TauCeti.IsRationalRep.isGlHighestWeightVector_differential`), so it acts
on the whole of `V_λ` by the scalar `gelfandEigenvalue λ r`
(`TauCeti.gelfandInvariant_smul_of_isGlHighestWeightVector_of_lieSpan_eq_top`). More generally
this holds for every irreducible rational representation with a highest weight vector of weight
`λ`.

Below the top level, the line of a pattern with `n + 1` rows is the image of the line of its
truncation under an intertwiner `f : V_μ → V_λ` of representations of `GL n ℂ`, where `μ` is the
second row. The differential of the restriction of `V_λ` to `GL n ℂ` is the differential of
`V_λ` on the upper-left corner `𝔤𝔩ₙ ⊆ 𝔤𝔩ₙ₊₁`
(`TauCeti.IsRationalRep.differential_comp_glBlockSucc`), so `f` intertwines the action of
`U(𝔤𝔩ₙ)` on `V_μ` with the action of its image in `U(𝔤𝔩ₙ₊₁)` on `V_λ`
(`TauCeti.UniversalEnvelopingAlgebra.map_lift_apply_of_map_apply`). The Gelfand–Tsetlin generators
at the levels `k ≤ n` lie in that image, and induction on `n` concludes.

## Main results

* `TauCeti.IsRationalRep.lift_differential_gelfandInvariant_apply`: on an irreducible rational
  representation with a highest weight vector of weight `λ`, the Gelfand invariant `Cᵣ` acts by
  `gelfandEigenvalue λ r`.
* `TauCeti.lift_differential_rationalWeylRep_gelfandInvariant_apply`: the same on the rational
  Weyl module `V_λ`.
* `TauCeti.lift_differential_gelfandTsetlinGenerator_apply_of_mem_gtLine`: **the Gelfand–Tsetlin
  generator of degree `r` at level `k` acts on the line of `P` by the eigenvalue of row `k`**.
* `TauCeti.gtLine_le_eigenspace_gelfandTsetlinGenerator`: the same, as an inclusion of the line
  in an eigenspace.

## References

* I. M. Gelfand and M. L. Tsetlin, *Finite-dimensional representations of the group of unimodular
  matrices*, Doklady Akad. Nauk SSSR **71** (1950), 825–828.
* A. Molev, *Yangians and Classical Lie Algebras* (2007), Chapter 7.
-/

public section

open Module Representation

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

namespace IsRationalRep

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **The Gelfand invariants act on an irreducible rational representation by their
highest-weight eigenvalues.** If `ρ` is irreducible and has a nonzero vector of weight `λ` fixed
by every transvection `xᵢⱼ(c)` with `i < j`, then the Gelfand invariant `Cᵣ = trace (𝔼 ^ r)` of
`U(𝔤𝔩ₙ)` acts on `ρ` through its differential by the scalar `gelfandEigenvalue λ r`. -/
theorem lift_differential_gelfandInvariant_apply (hρ : IsRationalRep ρ) [ρ.IsIrreducible]
    {l : Fin n → ℤ} {w : W} (hw0 : w ≠ 0) (hwl : w ∈ weightSpace ρ l)
    (hw : ∀ (i j : Fin n) (hij : i < j) (c : ℂ), ρ (transvectionUnit hij.ne c) w = w) (r : ℕ)
    (x : W) :
    UniversalEnvelopingAlgebra.lift ℂ hρ.differential (gelfandInvariant ℂ (Fin n) r) x =
      gelfandEigenvalue (fun i ↦ (l i : ℂ)) r • x := by
  let _ := LieRingModule.compLieHom W hρ.differential
  let _ := LieModule.compLieHom W hρ.differential
  have := hρ.isIrreducible_differential
  -- Through the Lie module structure given by `dρ`, the enveloping-algebra representation is the
  -- lift of `dρ`.
  have hrep : UniversalEnvelopingAlgebra.lift ℂ hρ.differential =
      TauCeti.UniversalEnvelopingAlgebra.representation ℂ (Matrix (Fin n) (Fin n) ℂ) W := by
    apply _root_.UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun X ↦ ?_
    simp only [LieHom.comp_apply, AlgHom.coe_toLieHom, UniversalEnvelopingAlgebra.lift_ι_apply,
      TauCeti.UniversalEnvelopingAlgebra.representation_ι]
    ext v
    rw [LieModule.toEnd_apply_apply, LieRingModule.compLieHom_apply, Module.End.lie_apply]
  have hgen : LieSubmodule.lieSpan ℂ (Matrix (Fin n) (Fin n) ℂ) {w} = ⊤ := by
    have : Nontrivial (LieSubmodule.lieSpan ℂ (Matrix (Fin n) (Fin n) ℂ) {w}) :=
      ⟨⟨0, ⟨w, LieSubmodule.subset_lieSpan rfl⟩, fun h ↦ hw0 (congrArg Subtype.val h).symm⟩⟩
    exact LieSubmodule.eq_top_of_isIrreducible ..
  rw [hrep]
  exact gelfandInvariant_smul_of_isGlHighestWeightVector_of_lieSpan_eq_top
    (hρ.isGlHighestWeightVector_differential hw0 hwl hw) hgen r x

end IsRationalRep

variable {n : ℕ}

/-- **The Gelfand invariants act on a rational Weyl module by the eigenvalues of its weight.** The
Gelfand invariant `Cᵣ` of `U(𝔤𝔩ₙ)` acts on `V_λ`, through the differential of the rational Weyl
representation, by the scalar `gelfandEigenvalue λ r`. -/
theorem lift_differential_rationalWeylRep_gelfandInvariant_apply (l : DominantWeight n) (r : ℕ)
    (x : (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule) :
    UniversalEnvelopingAlgebra.lift ℂ (isRationalRep_rationalWeylRep n l).differential
        (gelfandInvariant ℂ (Fin n) r) x =
      gelfandEigenvalue (fun i ↦ ((l : Fin n → ℤ) i : ℂ)) r • x := by
  obtain ⟨v, hvl, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (weightSpace_rationalWeylRep_self_ne_bot ℂ l)
  exact (isRationalRep_rationalWeylRep n l).lift_differential_gelfandInvariant_apply hv0 hvl
    (fun _ _ hij ↦ rationalWeylRep_apply_transvectionUnit_eq_self l hij hvl) r x

/-- **The Gelfand–Tsetlin generators act on the Gelfand–Tsetlin lines by the eigenvalues of the
rows.** Let `P` be a Gelfand–Tsetlin pattern with top weight `λ`. On every vector of the line
`TauCeti.gtLine λ P` of the rational Weyl module `V_λ`, the Gelfand–Tsetlin generator of degree
`r` at level `k ≤ n` acts, through the differential of `V_λ`, by the highest-weight eigenvalue
`gelfandEigenvalue (P 0 k, …, P (k - 1) k) r` of the Gelfand invariant `Cᵣ` of `𝔤𝔩ₖ` at the row of
length `k` of `P`. -/
theorem lift_differential_gelfandTsetlinGenerator_apply_of_mem_gtLine : ∀ {n : ℕ}
    (l : DominantWeight n) (P : {P : GTPattern n // P.topWeight = l}) {k : ℕ} (hk : k ≤ n)
    (r : ℕ) {v : (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule}, v ∈ gtLine l P →
    UniversalEnvelopingAlgebra.lift ℂ (isRationalRep_rationalWeylRep n l).differential
        (gelfandTsetlinGenerator ℂ hk r) v =
      gelfandEigenvalue (fun i : Fin k ↦ (P.1 i k : ℂ)) r • v
  | n, l, P, k, hk, r, v, hv => by
    -- The row of length `n` of `P` is its top row `λ`.
    have htop : (fun i : Fin n ↦ (P.1 i n : ℂ)) = fun i ↦ ((l : Fin n → ℤ) i : ℂ) := by
      funext i
      have h := congrArg (fun m : DominantWeight n ↦ (m : Fin n → ℤ) i) P.2
      simp only [GTPattern.topWeight_coe, GTPattern.topRow_apply] at h
      rw [h]
    rcases hk.eq_or_lt with rfl | hlt
    · rw [gelfandTsetlinGenerator_self, lift_differential_rationalWeylRep_gelfandInvariant_apply,
        htop]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hk' : k ≤ m := by omega
    -- The line of `P` is the image of the line of its truncation under a nonzero intertwiner.
    have hm : P.1.truncate.topWeight ∈ interlacingWeights l := by
      have h := P.1.topWeight_truncate_mem_interlacingWeights
      rwa [P.2] at h
    obtain ⟨f, hf0⟩ := exists_intertwiningMap_rationalWeylRep_comp_glBlockSucc_ne_zero hm
    rw [gtLine_succ l P f hf0] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    -- Fix the additive groups of the two submodule carriers before inferring the Lie ring
    -- structures on their endomorphisms.
    let _ : AddCommGroup (weylModuleOfShape ℂ m P.1.truncate.topWeight.detShiftShape).toSubmodule :=
      inferInstance
    let _ : AddCommGroup (weylModuleOfShape ℂ (m + 1) l.detShiftShape).toSubmodule := inferInstance
    -- `f` intertwines the differential of `V_μ` with that of `V_λ` on the corner `𝔤𝔩ₘ`.
    have hf (X : Matrix (Fin m) (Fin m) ℂ) (x) :
        f.toLinearMap ((isRationalRep_rationalWeylRep m P.1.truncate.topWeight).differential X x) =
          ((isRationalRep_rationalWeylRep (m + 1) l).differential.comp
            (glEmbedding ℂ Fin.castSuccEmb)) X (f.toLinearMap x) := by
      rw [← IsRationalRep.differential_comp_glBlockSucc _
        (isRationalRep_rationalWeylRep_comp_glBlockSucc m l)]
      exact ((IsRationalRep.isIntertwiningMap_iff_forall_map_differential _ _ _).mp
        ⟨f.isIntertwining⟩) X x
    have ih := lift_differential_gelfandTsetlinGenerator_apply_of_mem_gtLine
      P.1.truncate.topWeight ⟨P.1.truncate, rfl⟩ hk' r hw
    rw [← map_glEmbedding_castSuccEmb_gelfandTsetlinGenerator ℂ hk' r, ← AlgHom.comp_apply,
      UniversalEnvelopingAlgebra.lift_comp_map,
      ← UniversalEnvelopingAlgebra.map_lift_apply_of_map_apply f.toLinearMap hf, ih, map_smul]
    congr 2
    funext i
    simp only [GTPattern.truncate_apply, hk', ↓reduceIte]

/-- **Each Gelfand–Tsetlin line lies in an eigenspace of each Gelfand–Tsetlin generator**, for the
eigenvalue `gelfandEigenvalue (P 0 k, …, P (k - 1) k) r` read off the row of length `k` of the
pattern. -/
theorem gtLine_le_eigenspace_gelfandTsetlinGenerator (l : DominantWeight n)
    (P : {P : GTPattern n // P.topWeight = l}) {k : ℕ} (hk : k ≤ n) (r : ℕ) :
    gtLine l P ≤ End.eigenspace (R := ℂ) (M := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
      (UniversalEnvelopingAlgebra.lift ℂ (isRationalRep_rationalWeylRep n l).differential
        (gelfandTsetlinGenerator ℂ hk r))
      (gelfandEigenvalue (fun i : Fin k ↦ (P.1 i k : ℂ)) r) := fun _ hv ↦
  End.mem_eigenspace_iff.mpr
    (lift_differential_gelfandTsetlinGenerator_apply_of_mem_gtLine l P hk r hv)

end TauCeti

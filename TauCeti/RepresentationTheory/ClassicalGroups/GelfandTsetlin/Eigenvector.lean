/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.GelfandInvariant.HighestWeight
public import TauCeti.RepresentationTheory.ClassicalGroups.Differential.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Line
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rationality
import TauCeti.Algebra.Lie.Submodule.Atom
import TauCeti.RepresentationTheory.ClassicalGroups.Branching.Differential
import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Differential
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight

/-!
# The Gelfand–Tsetlin lines are joint eigenlines of the Gelfand–Tsetlin generators

The rational Weyl module `V_λ` of `GL n ℂ` is a module over `U(𝔤𝔩ₙ)` through the differential of
its action. The **Gelfand–Tsetlin generators** `TauCeti.gelfandTsetlinGenerator` are the images in
`U(𝔤𝔩ₙ)` of the Gelfand invariants `Cᵣ = trace (𝔼 ^ r)` of the upper-left corners
`𝔤𝔩₁ ⊂ 𝔤𝔩₂ ⊂ ⋯ ⊂ 𝔤𝔩ₙ`. This file proves that they are simultaneously diagonal on the
Gelfand–Tsetlin decomposition of `V_λ` (`TauCeti.isInternal_gtLine`), with eigenvalues explicit
in the pattern: on the line `TauCeti.gtLine λ P` of a pattern `P`, the generator of degree `r` at
level `k` acts by the scalar `TauCeti.gelfandEigenvalue` of the row `(P 0 k, …, P (k - 1) k)` of
`P` of length `k`.

The argument has two steps.

* **Central character.** The Gelfand invariants are central in `U(𝔤𝔩ₙ)`, and they act on a
  highest weight vector of weight `μ` by `gelfandEigenvalue μ r`. The differential of `V_λ` is an
  irreducible `𝔤𝔩ₙ`-module with a highest weight vector of weight `λ`, so `Cᵣ` acts on all of `V_λ`
  by `gelfandEigenvalue λ r`. This is the top level `k = n`, where the row of `P` is `λ`.
* **Branching.** Below the top level the generator is the image of a generator of `U(𝔤𝔩ₙ₋₁)`
  along the corner embedding, and differentiation commutes with restriction along the block
  inclusion (`TauCeti.IsRationalRep.lift_differential_comp_glBlockSucc`). The line of `P` is the
  image of the line of its truncation under an intertwiner `V_μ → V_λ`, which intertwines the
  enveloping-algebra actions (`TauCeti.IsRationalRep.map_lift_differential_apply`), so the
  eigenvalue is inherited from the truncation by induction on `n`.

Together with `TauCeti.GTPattern.eq_of_forall_gelfandEigenvalue_eq`, which says that these
eigenvalues determine the pattern, this identifies the Gelfand–Tsetlin decomposition as the joint
eigenspace decomposition of the Gelfand–Tsetlin generators.

## Main results

* `TauCeti.lift_differential_rationalWeylRep_gelfandInvariant_apply`: the Gelfand invariant `Cᵣ`
  of `𝔤𝔩ₙ` acts on `V_λ` by the scalar `gelfandEigenvalue λ r`.
* `TauCeti.lift_differential_gelfandTsetlinGenerator_apply_of_mem_gtLine`: on the
  Gelfand–Tsetlin line of a pattern `P`, the generator of degree `r` at level `k` acts by the
  scalar `gelfandEigenvalue` of the row of `P` of length `k`.

## References

* I. M. Gelfand and M. L. Tsetlin, *Finite-dimensional representations of the group of unimodular
  matrices*, Doklady Akad. Nauk SSSR **71** (1950), 825–828.
* A. Molev, *Gelfand-Tsetlin bases for classical Lie algebras*, in Handbook of Algebra, Vol. 4
  (2006), 109–170, §2.
* A. Molev, *Yangians and Classical Lie Algebras* (2007), Chapter 7.
-/

public section

open Representation

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- **The central character of a rational Weyl module.** The Gelfand invariant
`Cᵣ = trace (𝔼 ^ r)` of `U(𝔤𝔩ₙ)` acts on the rational Weyl module `V_λ`, through the differential
of its action, by the scalar `gelfandEigenvalue λ r`. -/
theorem lift_differential_rationalWeylRep_gelfandInvariant_apply {n : ℕ} (l : DominantWeight n)
    (r : ℕ) (v : (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule) :
    UniversalEnvelopingAlgebra.lift ℂ (isRationalRep_rationalWeylRep n l).differential
        (gelfandInvariant ℂ (Fin n) r) v =
      gelfandEigenvalue (fun i ↦ ((l : Fin n → ℤ) i : ℂ)) r • v := by
  let V := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule
  -- Fix the additive group of the submodule carrier before inferring the module structures.
  let _ : AddCommGroup V := inferInstance
  have hρ := isRationalRep_rationalWeylRep n l
  let _ := LieRingModule.compLieHom V hρ.differential
  let _ := LieModule.compLieHom V hρ.differential
  have _ := hρ.isIrreducible_differential
  obtain ⟨w, hwl, hw0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (weightSpace_rationalWeylRep_self_ne_bot ℂ l)
  have hw := hρ.isGlHighestWeightVector_differential hw0 hwl fun _ _ hij ↦
    rationalWeylRep_apply_transvectionUnit_eq_self l hij hwl
  have hrep : UniversalEnvelopingAlgebra.representation ℂ (Matrix (Fin n) (Fin n) ℂ) V =
      UniversalEnvelopingAlgebra.lift ℂ hρ.differential :=
    (UniversalEnvelopingAlgebra.lift_unique ℂ _ _).mp <| funext fun X ↦ LinearMap.ext fun x ↦ by
      rw [Function.comp_apply, UniversalEnvelopingAlgebra.representation_ι_apply,
        LieRingModule.compLieHom_apply, Module.End.lie_apply]
  rw [← hrep]
  exact gelfandInvariant_smul_of_isGlHighestWeightVector_of_lieSpan_eq_top hw
    (lieSpan_singleton_eq_top_of_ne_zero hw0) r v

/-- The top level of `TauCeti.lift_differential_gelfandTsetlinGenerator_apply_of_mem_gtLine`:
the Gelfand invariants of `𝔤𝔩ₙ` act on all of `V_λ` by the eigenvalue of the top row of a pattern
with top weight `λ`. -/
private theorem lift_differential_gelfandTsetlinGenerator_self_apply {n : ℕ}
    (l : DominantWeight n) (P : {P : GTPattern n // P.topWeight = l}) (r : ℕ)
    (v : (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule) :
    UniversalEnvelopingAlgebra.lift ℂ (isRationalRep_rationalWeylRep n l).differential
        (gelfandTsetlinGenerator ℂ le_rfl r) v =
      gelfandEigenvalue (fun i : Fin n ↦ (P.1 i n : ℂ)) r • v := by
  rw [gelfandTsetlinGenerator_self, lift_differential_rationalWeylRep_gelfandInvariant_apply]
  congr 2
  funext i
  obtain ⟨P, rfl⟩ := P
  rw [GTPattern.topWeight_coe, GTPattern.topRow_apply]

/-- **The Gelfand–Tsetlin lines are joint eigenlines of the Gelfand–Tsetlin generators.** On the
Gelfand–Tsetlin line of a pattern `P` with top weight `λ`, inside the rational Weyl module `V_λ`
of `GL n ℂ`, the Gelfand–Tsetlin generator of degree `r` at level `k ≤ n` acts through the
differential by the scalar `gelfandEigenvalue` of the row `(P 0 k, …, P (k - 1) k)` of `P`. -/
theorem lift_differential_gelfandTsetlinGenerator_apply_of_mem_gtLine {n : ℕ}
    (l : DominantWeight n) (P : {P : GTPattern n // P.topWeight = l}) {k : ℕ} (hk : k ≤ n) (r : ℕ)
    {v : (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule} (hv : v ∈ gtLine l P) :
    UniversalEnvelopingAlgebra.lift ℂ (isRationalRep_rationalWeylRep n l).differential
        (gelfandTsetlinGenerator ℂ hk r) v =
      gelfandEigenvalue (fun i : Fin k ↦ (P.1 i k : ℂ)) r • v := by
  induction n with
  | zero =>
    obtain rfl := Nat.le_zero.mp hk
    exact lift_differential_gelfandTsetlinGenerator_self_apply l P r v
  | succ m ih =>
    rcases hk.lt_or_eq with hk' | rfl
    · have hkm : k ≤ m := Nat.lt_succ_iff.mp hk'
      -- The line of `P` is the image of the line of its truncation under an intertwiner `f`.
      obtain ⟨f, hf0⟩ := exists_intertwiningMap_ne_zero_of_mem_interlacingWeights
        (P.2 ▸ P.1.topWeight_truncate_mem_interlacingWeights)
      rw [gtLine_succ l P f hf0] at hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      -- The generator acts on the restriction to `GL m ℂ` as a generator of `U(𝔤𝔩ₘ)`. Fix the
      -- additive group of the submodule carrier first, as in
      -- `TauCeti.lift_differential_rationalWeylRep_gelfandInvariant_apply`.
      let _ : AddCommGroup (weylModuleOfShape ℂ (m + 1) l.detShiftShape).toSubmodule :=
        inferInstance
      rw [← map_glEmbedding_castSuccEmb_gelfandTsetlinGenerator ℂ hkm r,
        ← (isRationalRep_rationalWeylRep (m + 1) l).lift_differential_comp_glBlockSucc,
        ← IsRationalRep.map_lift_differential_apply (isRationalRep_rationalWeylRep m _)
          (isRationalRep_rationalWeylRep_comp_glBlockSucc m l)
          ⟨fun g x ↦ LinearMap.congr_fun (f.isIntertwining' g) x⟩,
        ih _ _ hkm hw, map_smul]
      congr 2
      funext i
      simp only [GTPattern.truncate_apply, hkm, ite_true]
    · exact lift_differential_gelfandTsetlinGenerator_self_apply l P r v

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated
import TauCeti.GroupTheory.Index.Exact

/-!
# Finiteness and order of an isogeny Selmer group

For a separable isogeny `φ : E₁ → E₂`, the descent sequence gives

`#Sel_φ = [E₂(K) : φ(E₁(K))] · #Sha(E₁)[φ]`.

The kernel `Sha(E₁)[φ]` lies in `Sha(E₁)[deg φ]`, by composition with the dual. Thus finite
`deg φ`-torsion in Sha and finite generation of `E₂(K)` imply finiteness of `Sel_φ`.
Over a number field these hypotheses hold unconditionally, with local conditions imposed at
every finite and infinite place. In particular, this proves finiteness for both an isogeny and
its dual without assuming finiteness of either full Shafarevich–Tate group.

The order formula uses `Nat.card` and is valid without finiteness hypotheses; the finiteness
theorems ensure that its factors are positive integers in the number-field application.
These are the finite orders entering comparisons of isogeny Selmer groups in descent and in
Cassels' isogeny formula.

## Main results

* `TauCeti.Isogeny.card_selmerGroup`: the order formula from the descent sequence.
* `TauCeti.Isogeny.finite_selmerGroup_of_finite_torsionBy`: finiteness from the degree-torsion
  of Sha and finite generation of the target point group.
* `TauCeti.Isogeny.finite_selmerGroup_place`: unconditional finiteness over a number field.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, X.4.2.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology
open Hom (ofIsogeny)

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic]
  {ι : Type*} {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  (τ : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i))

/-- The part of Sha killed by an isogeny is finite whenever its degree-torsion is finite.
No separability or finiteness of the whole Sha group is required. -/
theorem finite_shafarevichTateGroupKer
    [Finite (AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) φ.degree)] :
    Finite (φ.shafarevichTateGroupKer τ) := by
  rw [φ.shafarevichTateGroupKer_eq_ker_shafarevichTateMap τ]
  have : Finite (AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) (ofIsogeny φ).degree) := by
    simpa only [Hom.degree_ofIsogeny] using
      (inferInstance : Finite (AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) φ.degree))
  exact Finite.of_injective _ (AddSubgroup.inclusion_injective
    ((ofIsogeny φ).ker_shafarevichTateMap_le_torsionBy τ))

section Separable

variable [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
  [DecidableEq K]

/-- The order of an isogeny Selmer group is the rational point cokernel index times the order
of the kernel on Sha. This `Nat.card` identity also holds when a term is infinite. -/
theorem card_selmerGroup :
    Nat.card (φ.selmerGroup τ) =
      (ofIsogeny φ).pointMapHom.range.index * Nat.card (φ.shafarevichTateGroupKer τ) := by
  have hker : Nat.card (φ.selmerShaMap τ).ker =
      Nat.card (W₂.toAffine.Point ⧸ (ofIsogeny φ).pointMapHom.range) := by
    rw [(φ.exact_kummerSelmerMap_selmerShaMap τ).addMonoidHom_ker_eq]
    exact Nat.card_congr (Equiv.ofInjective _ (φ.kummerSelmerMap_injective τ)).symm
  rw [← AddSubgroup.card_ker_mul_card_of_surjective (φ.selmerShaMap_surjective τ), hker,
    AddSubgroup.index_eq_card]

/-- Finite degree-torsion in Sha and finite generation of the target point group suffice for
finiteness of the isogeny Selmer group. The local conditions may be any family of extensions. -/
theorem finite_selmerGroup_of_finite_torsionBy [AddGroup.FG W₂.toAffine.Point]
    [Finite (AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) φ.degree)] :
    Finite (φ.selmerGroup τ) := by
  have := (ofIsogeny φ).finiteIndex_range_pointMapHom (Hom.ofIsogeny_ne_zero φ)
  have := φ.finite_shafarevichTateGroupKer τ
  exact (φ.exact_kummerSelmerMap_selmerShaMap τ).finite

end Separable

section NumberField

variable [NumberField K]

/-- The Selmer group of an isogeny over a number field is finite, with local conditions at all
finite and infinite places, for every choice of embeddings of separable closures. Finiteness
of the full Shafarevich–Tate group is not assumed. -/
theorem finite_selmerGroup_place
    (τ : ∀ v : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure v.Completion) :
    Finite (φ.selmerGroup τ) := by
  classical
  have : NeZero φ.degree := ⟨φ.degree_pos.ne'⟩
  have h := W₁.finite_torsionBy_sha φ.degree
  rw [W₁.sha_eq_shafarevichTateGroup τ] at h
  have := WeierstrassCurve.Affine.fg_point_of_numberField (W := W₂.toAffine)
  exact φ.finite_selmerGroup_of_finite_torsionBy τ

end NumberField

end TauCeti.Isogeny

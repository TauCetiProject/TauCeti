/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.GaloisCocycle.BrauerClass
public import TauCeti.Algebra.CrossedProduct.Inflation
import TauCeti.Algebra.CrossedProduct.Comap

/-!
# Galois cocycles over fields containing a prescribed subextension

A finite Galois cocycle can be refined to a finite Galois field containing any prescribed
finite subextension of the separable closure. The refinement preserves its Brauer class and
its inflated cocycle on the absolute Galois group, with equality of cocycles rather than only
equality of cohomology classes.

Consequently every Brauer class has a crossed-product presentation over a field containing
the prescribed subextension. This is the reduction needed to compare scalar extension with
restriction: the same finite field can then be regarded as Galois over either base field.

The prescribed subextension need not be normal. Its normal closure, composed with the
original cocycle's field, provides the refinement.

## References

* J.-P. Serre, *Local Fields*, Chapter X, §5.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, §4.4.
-/

public section

noncomputable section

universe u

namespace TauCeti

variable {K : Type u} [Field K]

namespace GaloisCocycle

/-- A Galois cocycle admits a refinement whose field contains both its original field and
any prescribed finite subextension. Both the Brauer class and the inflated absolute-Galois
cocycle are unchanged. No normality assumption on the prescribed subextension is needed. -/
theorem exists_refinement (g : GaloisCocycle K)
    (S : IntermediateField K (SeparableClosure K)) [FiniteDimensional K S] :
    ∃ h : GaloisCocycle K, g.extension ≤ h.extension ∧ S ≤ h.extension ∧
      h.brauerClass = g.brauerClass ∧
        h.cocycle.inflate h.extension = g.cocycle.inflate g.extension := by
  let M := g.extension ⊔ IntermediateField.normalClosure K S (SeparableClosure K)
  have : IsGalois K M := IsGalois.mk
  have hgM : g.extension ≤ M := le_sup_left
  let ι := IntermediateField.inclusion hgM
  let c := g.cocycle.comap ι.restrictNormalHom ι ι.restrictNormalHom_commutes
  refine ⟨⟨M, c⟩, hgM, S.le_normalClosure.trans le_sup_right, ?_, ?_⟩
  · simp only [brauerClass_def]
    exact BrauerGroup.crossedProductClass_comap ι.restrictNormalHom ι
      ι.restrictNormalHom_commutes g.cocycle
  · exact g.cocycle.inflate_comap ι.restrictNormalHom ι
      ι.restrictNormalHom_commutes (fun _ ↦ rfl)

end GaloisCocycle

end TauCeti

namespace BrauerGroup

open TauCeti

variable {K : Type u} [Field K]

/-- Every Brauer class is represented by a finite Galois cocycle over a field containing
any prescribed finite subextension of the separable closure. In particular, for a finite
separable extension embedded by `σ`, one may take the prescribed field to be `σ.fieldRange`. -/
theorem exists_galoisCocycle_brauerClass_eq_with_le
    (x : BrauerGroup K)
    (S : IntermediateField K (SeparableClosure K)) [FiniteDimensional K S]
    : ∃ g : GaloisCocycle K, S ≤ g.extension ∧ g.brauerClass = x := by
  obtain ⟨g, hg⟩ := TauCeti.BrauerGroup.exists_galoisCocycle_brauerClass_eq x
  obtain ⟨h, -, hS, hbrauer, -⟩ := g.exists_refinement S
  exact ⟨h, hS, hbrauer.trans hg⟩

end BrauerGroup

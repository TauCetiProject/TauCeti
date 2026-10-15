/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Quotient
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange

/-!
# Scalar extension of normal affine quotients

For a normal closed subgroup `N` of an affine group `G` over a field, the algebra of
coinvariants is a Hopf algebra. Its scalar extension is canonically isomorphic, as a Hopf
algebra, to the coinvariants of the scalar-extended subgroup. The comparison commutes with
the coordinate inclusions defining the quotient projections.

Consequently, the assertion that the quotient projection has kernel exactly `N` is preserved
and reflected by every field extension. This allows the exact-kernel theorem for a normal
quotient to be proved over an algebraic closure and then descended, without assuming
smoothness, reducedness, or finite type.

The construction upgrades `coinvariantsBaseChangeEquiv` using the corestriction of the
scalar-extended Hopf inclusion; it does not construct a second coinvariant algebra.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15.1 and 16.3.
* M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*, Manuscripta Math.
  **7** (1972), 251–270.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v w

noncomputable section

variable {k : Type u} {K : Type w} [Field k] [Field K] [Algebra k K]
variable {H : _root_.CommHopfAlgCat.{v} k} {I : HopfIdeal k H}

private theorem baseChangeMap_coinvariantsι_apply (hI : I.IsNormal)
    (z : K ⊗[k] I.coinvariants) :
    (baseChangeMap (K := K) (coinvariantsι hI)).hom z =
      Algebra.TensorProduct.map (AlgHom.id K K) I.coinvariants.val z := by
  induction z with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul s h =>
    rw [baseChangeMap_apply_tmul, coinvariantsι, hopfSubalgebraι_apply]
    rfl

/-- The scalar-extended quotient inclusion, corestricted to the extended coinvariant Hopf
algebra. -/
private def coinvariantsBaseChangeHom (hI : I.IsNormal) :
    baseChange (K := K) (coinvariants hI) ⟶
      coinvariants (isNormal_baseChangeHopfIdeal (K := K) hI) :=
  liftHopfSubalgebra (isNormal_baseChangeHopfIdeal hI).isHopfSubalgebra_coinvariants
    (baseChangeMap (coinvariantsι hI)) fun z ↦ by
      have hz := (coinvariantsBaseChangeEquiv (S := K) I z).property
      rw [coe_coinvariantsBaseChangeEquiv] at hz
      rwa [baseChangeMap_coinvariantsι_apply]

private theorem coinvariantsBaseChangeHom_apply (hI : I.IsNormal)
    (z : K ⊗[k] I.coinvariants) :
    (coinvariantsBaseChangeHom (K := K) hI).hom z = coinvariantsBaseChangeEquiv I z := by
  apply Subtype.ext
  rw [coinvariantsBaseChangeHom, coe_liftHopfSubalgebra_apply,
    coe_coinvariantsBaseChangeEquiv]
  exact baseChangeMap_coinvariantsι_apply hI z

/-- Scalar extension of the normal affine quotient, as an isomorphism of coordinate Hopf
algebras. Contravariantly, this identifies `(G/N)_K` with the quotient by `N_K`. -/
def coinvariantsBaseChangeIso (hI : I.IsNormal) :
    baseChange (K := K) (coinvariants hI) ≅
      coinvariants (isNormal_baseChangeHopfIdeal (K := K) hI) := by
  let f := coinvariantsBaseChangeHom (K := K) hI
  have hf : Function.Bijective f.hom := by
    have he : ⇑f.hom = ⇑(coinvariantsBaseChangeEquiv (S := K) I) :=
      funext (coinvariantsBaseChangeHom_apply hI)
    rw [he]
    exact (coinvariantsBaseChangeEquiv I).bijective
  -- Keep the bundled Hopf structure visible when the carrier is a subalgebra. In particular,
  -- it is not an instance on the unbundled subtype independently of the normality proof.
  letI := (coinvariants (isNormal_baseChangeHopfIdeal (K := K) hI)).hopfAlgebra
  let e : baseChange (K := K) (coinvariants hI) ≃ₐc[K]
      coinvariants (isNormal_baseChangeHopfIdeal (K := K) hI) :=
    BialgEquiv.ofBijective f.hom hf
  exact _root_.CommHopfAlgCat.isoMk e

/-- The Hopf comparison is the canonical flat-base-change comparison of invariant algebras. -/
@[simp]
theorem coinvariantsBaseChangeIso_hom_apply (hI : I.IsNormal)
    (z : K ⊗[k] I.coinvariants) :
    (coinvariantsBaseChangeIso (K := K) hI).hom.hom z = coinvariantsBaseChangeEquiv I z := by
  exact coinvariantsBaseChangeHom_apply hI z

/-- The inverse Hopf comparison is the inverse comparison of invariant algebras. -/
@[simp]
theorem coinvariantsBaseChangeIso_inv_apply (hI : I.IsNormal)
    (z : (baseChangeHopfIdeal (K := K) I).coinvariants) :
    (coinvariantsBaseChangeIso (K := K) hI).inv.hom z =
      (coinvariantsBaseChangeEquiv I).symm z := by
  apply (coinvariantsBaseChangeEquiv I).injective
  rw [← coinvariantsBaseChangeIso_hom_apply hI, Iso.inv_hom_id_apply,
    AlgEquiv.apply_symm_apply]

/-- The quotient projection after scalar extension agrees with the projection for the
scalar-extended subgroup under the canonical comparison. -/
@[reassoc (attr := simp)]
theorem coinvariantsBaseChangeIso_hom_comp_coinvariantsι (hI : I.IsNormal) :
    (coinvariantsBaseChangeIso (K := K) hI).hom ≫
        coinvariantsι (isNormal_baseChangeHopfIdeal (K := K) hI) =
      baseChangeMap (K := K) (coinvariantsι hI) := by
  ext z
  rw [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
    coinvariantsBaseChangeIso_hom_apply, coinvariantsι, hopfSubalgebraι_apply,
    coe_coinvariantsBaseChangeEquiv]
  exact (baseChangeMap_coinvariantsι_apply hI z).symm

/-- The inverse comparison also commutes with the quotient coordinate inclusion. -/
@[reassoc (attr := simp)]
theorem coinvariantsBaseChangeIso_inv_comp_baseChangeMap (hI : I.IsNormal) :
    (coinvariantsBaseChangeIso (K := K) hI).inv ≫
        baseChangeMap (K := K) (coinvariantsι hI) =
      coinvariantsι (isNormal_baseChangeHopfIdeal (K := K) hI) := by
  rw [← coinvariantsBaseChangeIso_hom_comp_coinvariantsι hI, Iso.inv_hom_id_assoc]

/-- The scheme-theoretic kernel of the normal quotient projection commutes with every field
extension. This equality retains the full Hopf ideal, including infinitesimal structure. -/
@[simp]
theorem kernelHopfIdeal_baseChangeMap_coinvariantsι (hI : I.IsNormal) :
    kernelHopfIdeal (baseChangeMap (K := K) (coinvariantsι hI)) =
      kernelHopfIdeal (coinvariantsι (isNormal_baseChangeHopfIdeal (K := K) hI)) := by
  rw [← coinvariantsBaseChangeIso_hom_comp_coinvariantsι hI]
  exact kernelHopfIdeal_comp_of_surjective _
    (ConcreteCategory.bijective_of_isIso _).2 _

/-- Exactness of the kernel of a normal quotient can be checked after any field extension.
In particular, an exact-kernel theorem over an algebraic closure descends to the base field. -/
@[simp]
theorem kernelHopfIdeal_coinvariantsι_baseChange_eq_iff (hI : I.IsNormal) :
    kernelHopfIdeal (coinvariantsι (isNormal_baseChangeHopfIdeal (K := K) hI)) =
        baseChangeHopfIdeal (K := K) I ↔
      kernelHopfIdeal (coinvariantsι hI) = I := by
  rw [← kernelHopfIdeal_baseChangeMap_coinvariantsι hI,
    ← baseChangeHopfIdeal_kernelHopfIdeal]
  exact (baseChangeHopfIdeal_injective (K := K)).eq_iff

end

end TauCeti.CommHopfAlgCat

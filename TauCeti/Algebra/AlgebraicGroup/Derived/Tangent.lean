/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Solvable
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.RingHom.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Derived.Abelianization
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Tangent
public import TauCeti.Algebra.Lie.Quotient
import TauCeti.Algebra.AlgebraicGroup.Derived.Geometric
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.FiniteType
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Smooth
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tangent
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.FormallySmooth

/-!
# Tangent spaces of the affine abelianization

For a geometrically reduced affine group of finite type over a field, the kernel of the
differential of the affine abelianization is the Lie algebra of the scheme-theoretic derived
subgroup. Consequently every bracket of ambient tangent vectors lies in that Lie algebra:
`[Lie G, Lie G] ⊆ Lie([G,G])`. If the ambient group is smooth, the abelianization projection
is smooth and its differential is surjective. Thus differentiating the abelianization gives
an exact sequence of Lie algebras, in every characteristic.

The containment does not assert equality with the derived Lie ideal. In positive
characteristic such an equality requires additional care. All tangent results allow values
in any commutative coefficient algebra, including nonreduced algebras.

The construction combines the affine abelianization of `Derived.Abelianization`, the exact
coinvariant-kernel theorem, and the tangent-kernel comparison. Smoothness uses the geometric
derived-subgroup theorem and the smooth-kernel criterion for faithfully flat homomorphisms.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d and Chapter 10.
* A. Borel, *Linear Algebraic Groups*, §§2 and 3.
* `LieHom.quotKerEquivOfSurjective` from `TauCeti.Algebra.Lie.Quotient`.
-/

public section

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u v w

variable {k : Type u} [Field k] (H : _root_.CommHopfAlgCat.{v} k)
variable [Algebra.FiniteType k H]
variable {B : Type w} [CommRing B] [Algebra k B]

section GeometricallyReduced

variable [Algebra.IsGeometricallyReduced k H]

/-- The kernel of the differential of the affine abelianization is exactly the tangent
Lie ideal of the scheme-theoretic derived subgroup. -/
@[simp]
theorem ker_derivationCompLieHom_coinvariantsι_derivedDefiningIdeal :
    let := (coinvariants (isNormal_derivedDefiningIdeal H)).hopfAlgebra
    (derivationCompLieHom (B := B)
      (coinvariantsι (isNormal_derivedDefiningIdeal H)).hom).ker =
        (isNormal_derivedDefiningIdeal H).lieIdeal (B := B) := by
  let := (coinvariants (isNormal_derivedDefiningIdeal H)).hopfAlgebra
  ext d
  rw [← LieIdeal.mem_toLieSubalgebra, ← lieSubalgebra_kernelHopfIdeal,
    kernelHopfIdeal_coinvariantsι_eq, HopfIdeal.mem_lieSubalgebra_iff,
    HopfIdeal.IsNormal.mem_lieIdeal_iff]

/-- Every Lie bracket of tangent vectors belongs to the tangent space of the derived
closed subgroup. The field and the coefficient algebra may have positive characteristic. -/
theorem lie_mem_lieSubalgebra_derivedDefiningIdeal
    (d e : Derivation k H (Bialgebra.CounitAlgebra k H B)) :
    ⁅d, e⁆ ∈ (derivedDefiningIdeal H).lieSubalgebra (B := B) := by
  let := (coinvariants (isNormal_derivedDefiningIdeal H)).hopfAlgebra
  rw [← HopfIdeal.IsNormal.lieIdeal_toLieSubalgebra (isNormal_derivedDefiningIdeal H),
    LieIdeal.mem_toLieSubalgebra,
    ← ker_derivationCompLieHom_coinvariantsι_derivedDefiningIdeal,
    LieHom.mem_ker, LieHom.map_lie]
  exact trivial_lie_zero _ _ _ _

/-- The derived ideal of the tangent Lie algebra is contained in the Lie ideal of the
scheme-theoretic derived subgroup. This is an inclusion, without a claim of equality. -/
theorem derivedSeries_le_lieIdeal_derivedDefiningIdeal :
    LieAlgebra.derivedSeries B (Derivation k H (Bialgebra.CounitAlgebra k H B)) 1 ≤
      (isNormal_derivedDefiningIdeal H).lieIdeal (B := B) := by
  rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ,
    LieAlgebra.derivedSeriesOfIdeal_zero]
  apply (LieSubmodule.lie_le_iff _ _ _).mpr
  intro d _ e _
  rw [← LieIdeal.mem_toLieSubalgebra, HopfIdeal.IsNormal.lieIdeal_toLieSubalgebra]
  exact lie_mem_lieSubalgebra_derivedDefiningIdeal H d e

end GeometricallyReduced

-- The faithful-flatness theorem for coinvariants uses a common base/coordinate universe.
variable (H : _root_.CommHopfAlgCat.{u} k) [Algebra.FiniteType k H]

/-- The affine abelianization projection of a smooth finite-type affine group is smooth,
without connectedness or characteristic assumptions. -/
theorem smooth_coinvariantsι_derivedDefiningIdeal [Algebra.Smooth k H] :
    (coinvariantsι (isNormal_derivedDefiningIdeal H)).hom.toAlgHom.toRingHom.Smooth := by
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  apply (_root_.CommHopfAlgCat.smooth_iff_algebraSmooth_quotient_kernelHopfIdeal _
    (faithfullyFlat_coinvariantsι (isNormal_derivedDefiningIdeal H))).mpr
  rw [kernelHopfIdeal_coinvariantsι_eq]
  exact (smoothCommHopfAlgProperty_iff _).mp
    ((smoothCommHopfAlgProperty_iff H).mpr inferInstance).derived

/-- Differentiating the affine abelianization of a smooth finite-type affine group is
surjective, even with values in a nonreduced coefficient algebra. Together with the kernel
formula this gives the tangent exact sequence of the abelianization. -/
theorem surjective_derivationCompLieHom_coinvariantsι_derivedDefiningIdeal
    [Algebra.Smooth k H] :
    let := (coinvariants (isNormal_derivedDefiningIdeal H)).hopfAlgebra
    Function.Surjective (derivationCompLieHom (B := B)
      (coinvariantsι (isNormal_derivedDefiningIdeal H)).hom) := by
  let := (coinvariants (isNormal_derivedDefiningIdeal H)).hopfAlgebra
  exact derivationCompLieHom_surjective_of_formallySmooth _
    (smooth_coinvariantsι_derivedDefiningIdeal H).formallySmooth

/-- The Lie algebra of the affine abelianization is the ambient Lie algebra modulo the
Lie algebra of the group-theoretic derived subgroup. This quotient is by `Lie([G,G])`,
without identifying it with the abstract derived ideal `[Lie G, Lie G]`. -/
noncomputable def abelianizationLieEquiv [Algebra.Smooth k H] :
    letI := (coinvariants (isNormal_derivedDefiningIdeal H)).hopfAlgebra
    (Derivation k H (Bialgebra.CounitAlgebra k H B) ⧸
      (isNormal_derivedDefiningIdeal H).lieIdeal (B := B)) ≃ₗ⁅B⁆
        Derivation k (coinvariants (isNormal_derivedDefiningIdeal H))
          (Bialgebra.CounitAlgebra k (coinvariants (isNormal_derivedDefiningIdeal H)) B) := by
  letI := (coinvariants (isNormal_derivedDefiningIdeal H)).hopfAlgebra
  let f := derivationCompLieHom (B := B) (coinvariantsι (isNormal_derivedDefiningIdeal H)).hom
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  have hker : f.ker = (isNormal_derivedDefiningIdeal H).lieIdeal (B := B) :=
    ker_derivationCompLieHom_coinvariantsι_derivedDefiningIdeal H
  exact hker ▸ f.quotKerEquivOfSurjective
    (surjective_derivationCompLieHom_coinvariantsι_derivedDefiningIdeal H)

/-- The tangent abelianization equivalence sends a tangent class to its restriction to
the derived coinvariants, namely the differential of the quotient projection. -/
@[simp]
theorem abelianizationLieEquiv_apply_mk [Algebra.Smooth k H]
    (d : Derivation k H (Bialgebra.CounitAlgebra k H B)) :
    let := (coinvariants (isNormal_derivedDefiningIdeal H)).hopfAlgebra
    abelianizationLieEquiv H (LieSubmodule.Quotient.mk d) =
      derivationComp (B := B) (coinvariantsι (isNormal_derivedDefiningIdeal H)).hom d := by
  let := (coinvariants (isNormal_derivedDefiningIdeal H)).hopfAlgebra
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  dsimp only [abelianizationLieEquiv]
  generalize ker_derivationCompLieHom_coinvariantsι_derivedDefiningIdeal H (B := B) = hker
  generalize (isNormal_derivedDefiningIdeal H).lieIdeal (B := B) = I at hker ⊢
  cases hker
  exact (LieHom.quotKerEquivOfSurjective_apply_mk _ _ d).trans
    (derivationCompLieHom_apply _ d)

/-- The inverse tangent abelianization equivalence recovers the class of a tangent
vector from its image under the quotient differential. -/
@[simp]
theorem abelianizationLieEquiv_symm_apply [Algebra.Smooth k H]
    (d : Derivation k H (Bialgebra.CounitAlgebra k H B)) :
    let := (coinvariants (isNormal_derivedDefiningIdeal H)).hopfAlgebra
    (abelianizationLieEquiv H).symm
        (derivationComp (B := B) (coinvariantsι (isNormal_derivedDefiningIdeal H)).hom d) =
      LieSubmodule.Quotient.mk d := by
  let := (coinvariants (isNormal_derivedDefiningIdeal H)).hopfAlgebra
  dsimp only
  rw [← abelianizationLieEquiv_apply_mk H, LieEquiv.symm_apply_apply]

end CommHopfAlgCat

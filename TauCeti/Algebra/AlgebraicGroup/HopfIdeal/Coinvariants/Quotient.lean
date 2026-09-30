/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import TauCeti.Algebra.HopfAlgebra.Subalgebra

/-!
# The quotient of an affine group by a normal subgroup

Let `H` be a commutative Hopf algebra over `R`, representing the affine group `G = Spec H`, and
let `I` be a normal Hopf ideal, cutting out a normal closed subgroup `N`. The coinvariants
`H^{co H/I}` of `I` are the functions on `G` invariant under right translation by `N`. When `H`,
the coinvariants, and `H ⧸ H^{co H/I}` are flat (for instance over a field), the coinvariants form
a Hopf subalgebra of `H`. This file packages them as a commutative Hopf algebra, the coordinate
ring of the quotient `G ⧸ N`, together with the coordinate map of the projection `G → G ⧸ N`.

The projection is the **quotient of `G` by `N` in the category of affine groups**: `N` lies in its
kernel, and every homomorphism out of `G` whose kernel contains `N` factors uniquely through it.
In coordinates, a morphism `f : K ⟶ H` of commutative Hopf algebras has image in the coinvariants
exactly when its kernel Hopf ideal is contained in `I`; this criterion needs neither flatness nor
normality.

Over a field, the projection is moreover faithfully flat with kernel exactly `N`, so that `G ⧸ N`
represents the fppf quotient sheaf `TauCeti.CommHopfAlgCat.fppfQuotientSheaf` (Takeuchi's
theorem). Those two facts are not proved here: only the inclusion of `N` in the kernel is.

## Main declarations

* `TauCeti.HopfIdeal.forall_hom_mem_coinvariants_iff`: a morphism lands in the coinvariants of
  `I` exactly when its kernel Hopf ideal is contained in `I`.
* `TauCeti.HopfIdeal.IsNormal.isHopfSubalgebra_coinvariants`: the coinvariants of a normal Hopf
  ideal form a Hopf subalgebra.
* `TauCeti.CommHopfAlgCat.coinvariants`: the coordinate Hopf algebra of `G ⧸ N`.
* `TauCeti.CommHopfAlgCat.coinvariantsι`: the coordinate map of the projection `G → G ⧸ N`.
* `TauCeti.CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_le`: `N` lies in the kernel of the
  projection.
* `TauCeti.CommHopfAlgCat.coinvariantsLift` and
  `TauCeti.CommHopfAlgCat.exists_comp_coinvariantsι_iff`: the universal property of the
  projection.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15.1 and 16.3.
* M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*, Manuscripta Math.
  **7** (1972), 251–270.
* J. S. Milne, *Algebraic Groups* (2017), §5.c.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v

namespace HopfIdeal

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R} {I : HopfIdeal R H}

/-- **Coinvariants and kernels.** A morphism `f : K ⟶ H` of commutative Hopf algebras takes values
in the coinvariants of `I` exactly when its kernel Hopf ideal is contained in `I`. Geometrically,
the pullbacks of functions along a homomorphism `φ` out of `G` are right invariant under the
subgroup `N` cut out by `I` exactly when `N` lies in the kernel of `φ`. -/
theorem forall_hom_mem_coinvariants_iff (f : K ⟶ H) :
    (∀ x, f.hom x ∈ I.coinvariants) ↔ CommHopfAlgCat.kernelHopfIdeal f ≤ I := by
  have hker := CommHopfAlgCat.kernelHopfIdeal_toIdeal_le_ker_iff f (Ideal.Quotient.mkₐ R I.toIdeal)
  rw [AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_ker, toIdeal_le_toIdeal] at hker
  rw [hker]
  constructor
  · intro h
    ext x
    simpa using mk_eq_algebraMap_counit_of_mem_coinvariants (h x)
  · intro h x
    -- Push the quotient map through `Δ (f x) = (f ⊗ f) (Δ x)`; on `N` the morphism `f` is
    -- trivial, so the second factor collapses to the counit.
    have key (t : K ⊗[R] K) :
        Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)
            (TensorProduct.map (f.hom : K →ₗ[R] H) (f.hom : K →ₗ[R] H) t) =
          TensorProduct.map (f.hom : K →ₗ[R] H) (Algebra.linearMap R (H ⧸ I.toIdeal))
            ((Coalgebra.counit (R := R) (A := K)).lTensor K t) := by
      have heq : (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap ∘ₗ
          (f.hom : K →ₗ[R] H) =
          (Algebra.linearMap R (H ⧸ I.toIdeal)) ∘ₗ
            (Coalgebra.counit (R := R) (A := K)) := by
        ext b
        have hb := AlgHom.congr_fun h b
        simp only [AlgHom.comp_apply, Algebra.ofId_apply, Bialgebra.counitAlgHom_apply] at hb
        exact hb
      -- `TensorProduct.map_map` is stated for linear maps. Unfold the algebra tensor map
      -- to that definition so the quotient map and `f` can be composed via `heq`.
      change TensorProduct.map (LinearMap.id : H →ₗ[R] H)
          (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap
            (TensorProduct.map (f.hom : K →ₗ[R] H) (f.hom : K →ₗ[R] H) t) = _
      rw [TensorProduct.map_map, LinearMap.map_lTensor]
      simp only [LinearMap.id_comp, heq]
    rw [mem_coinvariants_iff, ← CoalgHomClass.map_comp_comul_apply f.hom x, key,
      Coalgebra.lTensor_counit_comul]
    simp

variable [Module.Flat R H] [Module.Flat R (H ⧸ Subalgebra.toSubmodule I.coinvariants)]

/-- **The coinvariants of a normal Hopf ideal form a Hopf subalgebra**, when `H` and
`H ⧸ H^{co H/I}` are flat, for instance over a field. -/
theorem IsNormal.isHopfSubalgebra_coinvariants (hI : I.IsNormal) :
    IsHopfSubalgebra I.coinvariants where
  comul_mem _ hx := by
    have hcarrier : hI.coinvariantsSubcoalgebra.carrier =
        Subalgebra.toSubmodule I.coinvariants :=
      Submodule.ext fun _ ↦ hI.mem_coinvariantsSubcoalgebra
    rw [← hcarrier]
    exact (hI.coinvariantsSubcoalgebra).comul_mem
      ((hI.mem_coinvariantsSubcoalgebra).2 hx)
  antipode_mem _ hx := hI.antipode_mem_coinvariants hx

end HopfIdeal

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R} {I : HopfIdeal R H}
variable [Module.Flat R H] [Module.Flat R I.coinvariants]
  [Module.Flat R (H ⧸ Subalgebra.toSubmodule I.coinvariants)]

/-- The coordinate Hopf algebra of the quotient `G ⧸ N` of the affine group `G = Spec H` by the
normal closed subgroup `N` cut out by the normal Hopf ideal `I`: the coinvariants `H^{co H/I}`,
the functions on `G` invariant under right translation by `N`. -/
noncomputable abbrev coinvariants (hI : I.IsNormal) : _root_.CommHopfAlgCat.{v} R :=
  ofHopfSubalgebra hI.isHopfSubalgebra_coinvariants

/-- The coordinate map of the projection `G → G ⧸ N`: the inclusion of the coinvariants. -/
noncomputable abbrev coinvariantsι (hI : I.IsNormal) : coinvariants hI ⟶ H :=
  hopfSubalgebraι hI.isHopfSubalgebra_coinvariants

/-- The normal subgroup `N` lies in the kernel of the projection `G → G ⧸ N`. -/
theorem kernelHopfIdeal_coinvariantsι_le (hI : I.IsNormal) :
    kernelHopfIdeal (coinvariantsι hI) ≤ I :=
  (HopfIdeal.forall_hom_mem_coinvariants_iff _).mp fun x ↦
    (hopfSubalgebraι_apply hI.isHopfSubalgebra_coinvariants x).symm ▸ x.2

/-- A homomorphism out of `G` whose kernel contains `N` factors through `G → G ⧸ N`: in
coordinates, a morphism `f : K ⟶ H` whose kernel Hopf ideal is contained in `I` factors through
the coinvariants. -/
noncomputable def coinvariantsLift (hI : I.IsNormal) (f : K ⟶ H)
    (hf : kernelHopfIdeal f ≤ I) : K ⟶ coinvariants hI :=
  liftHopfSubalgebra hI.isHopfSubalgebra_coinvariants f
    ((HopfIdeal.forall_hom_mem_coinvariants_iff f).mpr hf)

/-- The factorization through `G → G ⧸ N` recovers the original morphism. -/
@[reassoc (attr := simp)]
theorem coinvariantsLift_comp_coinvariantsι (hI : I.IsNormal) (f : K ⟶ H)
    (hf : kernelHopfIdeal f ≤ I) : coinvariantsLift hI f hf ≫ coinvariantsι hI = f :=
  liftHopfSubalgebra_comp_hopfSubalgebraι _ f _

/-- The factorization through `G → G ⧸ N` is unique. -/
theorem coinvariantsLift_unique (hI : I.IsNormal) (f : K ⟶ H) (hf : kernelHopfIdeal f ≤ I)
    (g : K ⟶ coinvariants hI) (hg : g ≫ coinvariantsι hI = f) : g = coinvariantsLift hI f hf :=
  liftHopfSubalgebra_unique _ f _ g hg

/-- **Universal property of `G ⧸ N`.** A homomorphism out of `G` factors through the projection
`G → G ⧸ N` exactly when its kernel contains `N`: in coordinates, a morphism `f : K ⟶ H` factors
through the coinvariants exactly when its kernel Hopf ideal is contained in `I`. -/
theorem exists_comp_coinvariantsι_iff (hI : I.IsNormal) (f : K ⟶ H) :
    (∃ g : K ⟶ coinvariants hI, g ≫ coinvariantsι hI = f) ↔ kernelHopfIdeal f ≤ I := by
  rw [exists_comp_hopfSubalgebraι_iff, HopfIdeal.forall_hom_mem_coinvariants_iff]

end CommHopfAlgCat

end TauCeti

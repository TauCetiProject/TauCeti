/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.MuNRep
public import TauCeti.RepresentationTheory.Continuous.TopRep.Discrete
public import TauCeti.Topology.Algebra.GroupAction.Discrete

/-!
# Finite-quotient Galois coefficient representations

For an open normal subgroup `V` of `G_F`, `galRepOfQuotient` equips a representation of `G_F / V`
with the discrete topology and pulls its action back to `G_F`. Its values are smooth, and finite
modules remain finite. Conversely, every finite smooth discrete Galois representation is
isomorphic to a value of this functor for some `V`.

This is the coefficient reduction used to apply finite-group representation theory to local
Euler characteristics. Neither a local-field hypothesis nor a prime exponent is needed for the
reduction itself.

The functor uses `discreteTopRepFunctor` and Mathlib's `TopRep.resFunctor`. The converse uses the
existing finite-set open-stabilizer theorem, not a second finite-quotient or Galois carrier.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, §VII.3,
  proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, I, proof of Theorem 2.8.
-/

public section

namespace TauCeti.ClassFieldTheory

open CategoryTheory

universe u

variable (n : ℕ) (F : Type u) [Field F]

/-- Read a `ZMod n`-representation of a finite Galois quotient as a discrete representation of
`G_F`, by restriction along the canonical quotient map. The body is exposed so the pointwise
action and morphism equations can use the original algebraic carriers. -/
@[expose] noncomputable def galRepOfQuotient
    (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F)) :
    Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup) ⥤ GalRep n F :=
  discreteTopRepFunctor (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup) ⋙
    TopRep.resFunctor (QuotientGroup.mk' V.toSubgroup)

/-- Inflation preserves addition of coefficient morphisms, allowing short complexes to be mapped. -/
instance (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F)) :
    (galRepOfQuotient n F V).Additive where
  map_add := by intros; ext a; rfl

/-- The coefficient object is the discrete representation restricted along the quotient map. -/
theorem galRepOfQuotient_obj (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F))
    (A : Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) :
    (galRepOfQuotient n F V).obj A =
      TopRep.res (QuotientGroup.mk' V.toSubgroup)
        (discreteTopRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup) A) :=
  (rfl)

/-- Inflation does not change the underlying algebraic coefficient module. -/
@[simp]
theorem galRepOfQuotient_obj_V (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F))
    (A : Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) :
    ((galRepOfQuotient n F V).obj A).V = A.V :=
  (rfl)

/-- The inflated action is the quotient action evaluated on the class of the automorphism. -/
@[simp]
theorem galRepOfQuotient_ρ_apply (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F))
    (A : Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup))
    (g : Field.absoluteGaloisGroup F) (a : A.V) :
    ((galRepOfQuotient n F V).obj A).ρ g a = A.ρ (QuotientGroup.mk g) a :=
  (rfl)

/-- The functor leaves the underlying coefficient map unchanged. -/
@[simp]
theorem galRepOfQuotient_map_apply (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F))
    {A B : Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)} (f : A ⟶ B) (a : A.V) :
    ((galRepOfQuotient n F V).map f).hom a = f.hom a :=
  (rfl)

/-- The inflated coefficient object carries the discrete topology. -/
instance (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F))
    (A : Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) :
    DiscreteTopology ((galRepOfQuotient n F V).obj A).V :=
  ⟨rfl⟩

/-- Inflation preserves finiteness of the coefficient module. -/
instance (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F))
    (A : Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) [Finite A.V] :
    Finite ((galRepOfQuotient n F V).obj A).V :=
  inferInstanceAs (Finite A.V)

/-- The open kernel of the quotient action makes the inflated representation smooth. -/
theorem isSmoothDiscrete_galRepOfQuotient (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F))
    (A : Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) :
    IsSmoothDiscrete (ZMod n) ((galRepOfQuotient n F V).obj A) := by
  rw [galRepOfQuotient_obj]
  exact (isSmoothDiscrete_discreteTopRep (ZMod n) _ A).res
    (ContinuousMonoidHom.quotientMk V.toSubgroup).continuous

/-- Supply smoothness as the instance hypothesis used by local cohomology and duality. -/
instance (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F))
    (A : Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) :
    Fact (IsSmoothDiscrete (ZMod n) ((galRepOfQuotient n F V).obj A)) :=
  ⟨isSmoothDiscrete_galRepOfQuotient n F V A⟩

/-- A discrete Galois representation killed by `V` is isomorphic to an inflated representation
of the quotient by that particular subgroup. -/
theorem exists_galRepOfQuotient_iso_of_trivial
    (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F))
    (X : GalRep n F) [DiscreteTopology X.V]
    (hV : ∀ g ∈ V, ∀ x : X.V, X.ρ g x = x) :
    ∃ A : Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup),
      Nonempty ((galRepOfQuotient n F V).obj A ≅ X) :=
  exists_discreteTopRep_res_iso (ZMod n) (Field.absoluteGaloisGroup F) X V.toSubgroup hV

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- Every finite smooth discrete Galois representation comes from a finite module over a finite
Galois quotient. Thus finite-group representation theory applies without changing coefficients. -/
theorem exists_galRepOfQuotient_iso (X : GalRep n F) [Finite X.V]
    [DiscreteTopology X.V] [hX : Fact (IsSmoothDiscrete (ZMod n) X)] :
    ∃ (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F))
      (A : Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)),
      Finite A.V ∧ Nonempty ((galRepOfQuotient n F V).obj A ≅ X) := by
  have := hX.out.continuousSMul
  obtain ⟨V, hV⟩ := (Set.finite_univ (α := X.V)).exists_openNormalSubgroup_smul_eq_self
    (G := Field.absoluteGaloisGroup F)
  obtain ⟨A, ⟨e⟩⟩ := exists_galRepOfQuotient_iso_of_trivial n F V X fun g hg x ↦
    (TopRep.distribMulAction_smul X g x).symm.trans (hV g hg x (Set.mem_univ x))
  refine ⟨V, A, ?_, ⟨e⟩⟩
  have hfin : Finite ((galRepOfQuotient n F V).obj A).V :=
    Finite.of_equiv X.V ((forget (GalRep n F)).mapIso e).toEquiv.symm
  rwa [galRepOfQuotient_obj_V] at hfin

end TauCeti.ClassFieldTheory

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Cyclic.ActionKernel
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

The quotient can be enlarged so that it also sees the roots of unity: for `n` invertible in `F`,
every `V` contains an open normal subgroup acting trivially on `μₙ`, of index dividing
`[G_F : V] · φ n` and with commutative quotient when `G_F ⧸ V` is commutative
(`exists_openNormalSubgroup_le_muNRep_ρ_eq_self`). On fixed fields this replaces a finite Galois
extension `L` by `L(μₙ)`; for a prime `n = ℓ` it keeps the index prime to `ℓ`
(`exists_openNormalSubgroup_le_muNRep_ρ_eq_self_of_coprime`), which is what descent of
cohomology along the quotient requires.

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

variable {n F} in
/-- **Adjoining `μₙ` to a finite Galois layer.** For `n` invertible in `F`, every open normal
subgroup `V` of `G_F` contains an open normal subgroup `W` acting trivially on `μₙ`, of index
dividing `[G_F : V] · φ n`, and with `G_F ⧸ W` commutative when `G_F ⧸ V` is. On fixed fields this
replaces the layer `L` of `V` by `L(μₙ)`. The subgroup is `V` intersected with the kernel of the
action on `μₙ`, a cyclic group of order `n`. -/
theorem exists_openNormalSubgroup_le_muNRep_ρ_eq_self (hn : IsUnit (n : F))
    (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F)) :
    ∃ W : OpenNormalSubgroup (Field.absoluteGaloisGroup F), W ≤ V ∧
      (∀ g ∈ W, ∀ x : (muNRep n F).V, (muNRep n F).ρ g x = x) ∧
      W.toSubgroup.index ∣ V.toSubgroup.index * n.totient ∧
      (IsMulCommutative (Field.absoluteGaloisGroup F ⧸ V.toSubgroup) →
        IsMulCommutative (Field.absoluteGaloisGroup F ⧸ W.toSubgroup)) := by
  have hcard : Nat.card (muNRep n F).V = n :=
    (Nat.card_congr (kummerCoeffEquivMuNRep n F).toEquiv).symm.trans (natCard_kummerCoeff hn)
  have : NeZero n := NeZero.of_neZero_natCast F (h := ⟨hn.ne_zero⟩)
  have : Finite (muNRep n F).V := Nat.finite_of_card_ne_zero (hcard.trans_ne (NeZero.ne n))
  have : IsAddCyclic (muNRep n F).V :=
    isAddCyclic_of_surjective _
      ((kummerCoeffAddEquivZMod hn).symm.trans (kummerCoeffEquivMuNRep n F)).surjective
  set K := openActionKernel (Field.absoluteGaloisGroup F) (muNRep n F).V
  refine ⟨V ⊓ K, inf_le_left, fun g hg x => ?_, ?_, fun hV => ?_⟩
  · exact (TopRep.distribMulAction_smul _ g x).symm.trans
      (openActionKernel_smul_eq_self _ _ ⟨g, (Subgroup.mem_inf.1 hg).2⟩ x)
  · have hK := index_ker_toPermHom_dvd_totient (Field.absoluteGaloisGroup F) (muNRep n F).V
    rw [hcard, ← openActionKernel_toSubgroup] at hK
    rw [OpenNormalSubgroup.toSubgroup_inf, Subgroup.index_inf]
    exact mul_dvd_mul (Subgroup.relIndex_dvd_index_of_normal _ _) hK
  · have hK := isMulCommutative_quotient_ker_toPermHom (Field.absoluteGaloisGroup F)
      (muNRep n F).V
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, ← openActionKernel_toSubgroup]
      at hK
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le] at hV ⊢
    exact le_inf hV hK

variable {n F} in
/-- **Adjoining `μₗ` keeps the index prime to `ℓ`.** For a prime `ℓ` invertible in `F` and an
open normal subgroup `V` of `G_F` of index prime to `ℓ`, some open normal subgroup `W ≤ V` acts
trivially on `μₗ`, still has index prime to `ℓ`, and has commutative quotient when `V` has: its
index divides `[G_F : V] · (ℓ - 1)`. -/
theorem exists_openNormalSubgroup_le_muNRep_ρ_eq_self_of_coprime [Fact n.Prime]
    (hn : IsUnit (n : F)) (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F))
    (hV : V.toSubgroup.index.Coprime n) :
    ∃ W : OpenNormalSubgroup (Field.absoluteGaloisGroup F), W ≤ V ∧
      (∀ g ∈ W, ∀ x : (muNRep n F).V, (muNRep n F).ρ g x = x) ∧
      W.toSubgroup.index.Coprime n ∧
      (IsMulCommutative (Field.absoluteGaloisGroup F ⧸ V.toSubgroup) →
        IsMulCommutative (Field.absoluteGaloisGroup F ⧸ W.toSubgroup)) := by
  obtain ⟨W, hWV, hW, hdvd, hcomm⟩ := exists_openNormalSubgroup_le_muNRep_ρ_eq_self hn V
  refine ⟨W, hWV, hW,
    Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_mul_iff_left.2 ⟨hV, ?_⟩), hcomm⟩
  rw [Nat.totient_prime Fact.out]
  exact (Nat.coprime_self_sub_left (Fact.out : n.Prime).one_le).2 (Nat.coprime_one_left n)

end TauCeti.ClassFieldTheory

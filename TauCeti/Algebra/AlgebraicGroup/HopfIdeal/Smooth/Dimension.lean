/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.Containment
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Dimension
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType

/-!
# Comparing smooth connected closed subgroups by Lie dimension

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field. A closed
subgroup is encoded contravariantly by a Hopf ideal, so `I ≤ J` says that the subgroup cut out by
`I` contains the one cut out by `J`. Lie dimension is antitone in the defining ideal, and this
file proves that it detects equality among smooth connected closed subgroups: an inclusion which
does not drop the Lie dimension is an equality.

The proof is the conormal-sequence argument, stated first for any surjective coordinate map
between smooth connected affine groups and then applied to the quotient-to-quotient coordinate
map. A surjective coordinate map embeds tangent spaces, and equality of tangent-space dimensions
makes it bijective on tangent Lie algebras, hence its conormal space vanishes; smoothness and
connectedness then upgrade the infinitesimal statement to injectivity, that is, to equality of
Hopf ideals.

Two consequences follow formally. A member of maximal Lie dimension in a family of smooth
connected closed subgroups is a maximal member of that family, and every nonempty such family has
a maximal member. No closure hypothesis on the family is needed: unlike the product argument used
for the unipotent and solvable radicals, this gives maximality rather than a greatest element.

## Main declarations

* `TauCeti.CommHopfAlgCat.injective_of_surjective_of_finrank_le`,
  `TauCeti.CommHopfAlgCat.isIso_of_surjective_of_finrank_le`: a closed immersion of smooth
  connected affine groups which does not drop the Lie dimension is an isomorphism.
* `TauCeti.HopfIdeal.eq_of_le_of_finrank_quotientLie_le`: an inclusion of smooth connected closed
  subgroups which does not drop the Lie dimension is an equality.
* `TauCeti.HopfIdeal.minimal_of_finrank_quotientLie_maximal`: a maximal-dimensional member of a
  family of smooth connected closed subgroups is a maximal member.
* `TauCeti.HopfIdeal.exists_minimal_of_smooth_of_connected`: every nonempty family of smooth
  connected closed subgroups has a maximal member.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and §§5.a, 6.a, 10.a.
* A. Borel, *Linear Algebraic Groups*, §11.21.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace CommHopfAlgCat

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}

/-- **A closed immersion of smooth connected affine groups which does not drop the Lie dimension
is an isomorphism.** If the coordinate map `f : H ⟶ K` is surjective, so that `Spec K` is a
closed subgroup of `Spec H`, both are smooth and connected, and the Lie algebra of `Spec H` has
dimension at most that of `Spec K`, then the coordinate map `f` is also injective. The
isomorphism form is `isIso_of_surjective_of_finrank_le`. -/
theorem injective_of_surjective_of_finrank_le (f : H ⟶ K) (hf : Function.Surjective f.hom)
    (hH_smooth : smoothCommHopfAlgProperty k H) (hH_connected : ConnectedSpace (PrimeSpectrum H))
    (hK_smooth : smoothCommHopfAlgProperty k K) (hK_connected : ConnectedSpace (PrimeSpectrum K))
    (hfinrank :
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) ≤
        Module.finrank k (Derivation k K (Bialgebra.CounitAlgebra k K k))) :
    Function.Injective f.hom := by
  let _ : Algebra.Smooth k H := (smoothCommHopfAlgProperty_iff _).mp hH_smooth
  let q : H →ₐc[k] K := f.hom
  have hq : Function.Surjective q := hf
  -- A surjection embeds the tangent space of `K` into that of `H`, so the dimensions agree.
  have hfinrank_eq :
      Module.finrank k (Derivation k K (Bialgebra.CounitAlgebra k K k)) =
        Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) :=
    le_antisymm
      (LinearMap.finrank_le_finrank_of_injective
        (f := (derivationCompLieHom (B := k) q : _ →ₗ[k] _))
        (derivationCompLieHom_injective_of_surjective (B := k) q hq))
      hfinrank
  have hbij := derivationCompLieHom_bijective_of_surjective_of_finrank_eq q hq hfinrank_eq
  exact (HopfIdeal.ker_eq_bot_iff q).mp
    (HopfIdeal.ker_eq_bot_of_smooth_of_connected_of_conormalSubspace_eq_bot q hq
      hH_smooth hH_connected hK_smooth hK_connected
      (HopfIdeal.conormalSubspace_ker_eq_bot_of_derivationCompLieHom_surjective q hbij.2))

/-- **A closed immersion of smooth connected affine groups which does not drop the Lie dimension
is an isomorphism**, in categorical form: a surjective coordinate map `f : H ⟶ K` between smooth
connected affine groups with `dim Lie(Spec H) ≤ dim Lie(Spec K)` is an isomorphism. -/
theorem isIso_of_surjective_of_finrank_le (f : H ⟶ K) (hf : Function.Surjective f.hom)
    (hH_smooth : smoothCommHopfAlgProperty k H) (hH_connected : ConnectedSpace (PrimeSpectrum H))
    (hK_smooth : smoothCommHopfAlgProperty k K) (hK_connected : ConnectedSpace (PrimeSpectrum K))
    (hfinrank :
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) ≤
        Module.finrank k (Derivation k K (Bialgebra.CounitAlgebra k K k))) :
    CategoryTheory.IsIso f :=
  (CategoryTheory.ConcreteCategory.isIso_iff_bijective f).mpr
    ⟨injective_of_surjective_of_finrank_le f hf hH_smooth hH_connected hK_smooth hK_connected
      hfinrank, hf⟩

end CommHopfAlgCat

namespace HopfIdeal

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I J : HopfIdeal k H}

/-- An inclusion of smooth connected closed subgroups which does not drop the Lie dimension is an
equality.

The order on Hopf ideals reverses inclusion of the represented closed subgroups, so `I ≤ J` says
that the subgroup cut out by `I` contains the one cut out by `J`, and the dimension hypothesis is
the reverse of the automatic inequality. -/
theorem eq_of_le_of_finrank_quotientLie_le (hIJ : I ≤ J)
    (hI_smooth : smoothCommHopfAlgProperty k
      (_root_.CommHopfAlgCat.of k (H ⧸ I.toIdeal)))
    (hI_connected : ConnectedSpace (PrimeSpectrum (H ⧸ I.toIdeal)))
    (hJ_smooth : smoothCommHopfAlgProperty k
      (_root_.CommHopfAlgCat.of k (H ⧸ J.toIdeal)))
    (hJ_connected : ConnectedSpace (PrimeSpectrum (H ⧸ J.toIdeal)))
    (hfinrank :
      Module.finrank k
          (Derivation k (H ⧸ I.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)) ≤
        Module.finrank k
          (Derivation k (H ⧸ J.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ J.toIdeal) k))) :
    I = J :=
  (CommHopfAlgCat.quotientMapOfLe_injective_iff H.obj hIJ).mp
    (CommHopfAlgCat.injective_of_surjective_of_finrank_le _
      (CommHopfAlgCat.quotientMapOfLe_surjective H.obj hIJ) hI_smooth hI_connected hJ_smooth
      hJ_connected hfinrank)

/-- A member of maximal Lie dimension in a family of smooth connected closed subgroups is a
maximal member of that family.

Only the members containing the given subgroup (the Hopf ideals `K` with `K ≤ I`) need to be
dimension-dominated by it, which is what makes the statement usable for families cut out by an
auxiliary containment condition. -/
theorem minimal_of_finrank_quotientLie_maximal (P : HopfIdeal k H → Prop)
    (smooth : ∀ {K : HopfIdeal k H}, P K → smoothCommHopfAlgProperty k
      (_root_.CommHopfAlgCat.of k (H ⧸ K.toIdeal)))
    (connected : ∀ {K : HopfIdeal k H}, P K →
      ConnectedSpace (PrimeSpectrum (H ⧸ K.toIdeal)))
    (hI : P I)
    (hmax : ∀ K : HopfIdeal k H, P K → K ≤ I →
      Module.finrank k
          (Derivation k (H ⧸ K.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ K.toIdeal) k)) ≤
        Module.finrank k
          (Derivation k (H ⧸ I.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k))) :
    Minimal P I :=
  ⟨hI, fun K hK hKI ↦
    (eq_of_le_of_finrank_quotientLie_le hKI (smooth hK) (connected hK) (smooth hI)
      (connected hI) (hmax K hK hKI)).ge⟩

/-- Every nonempty family of smooth connected closed subgroups has a maximal member.

Maximality of the represented closed subgroup is minimality of its defining Hopf ideal. The Lie
dimensions attained by the family form a nonempty set of natural numbers bounded by the Lie
dimension of the ambient group, so a maximal-dimensional member exists and is maximal. -/
theorem exists_minimal_of_smooth_of_connected (P : HopfIdeal k H → Prop)
    (smooth : ∀ {K : HopfIdeal k H}, P K → smoothCommHopfAlgProperty k
      (_root_.CommHopfAlgCat.of k (H ⧸ K.toIdeal)))
    (connected : ∀ {K : HopfIdeal k H}, P K →
      ConnectedSpace (PrimeSpectrum (H ⧸ K.toIdeal)))
    (hP : ∃ I : HopfIdeal k H, P I) :
    ∃ I : HopfIdeal k H, Minimal P I := by
  obtain ⟨I, hI, hmax⟩ := exists_maximal_finrank_quotientLie P hP
  exact ⟨I, minimal_of_finrank_quotientLie_maximal P smooth connected hI
    fun K hK _ ↦ hmax K hK⟩

end HopfIdeal

end

end TauCeti

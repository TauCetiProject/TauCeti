/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Sheaf
public import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite

/-!
# Étale sheaves on a field as sheaves on finite étale schemes

Let `K` be a field. A scheme étale over `Spec K` is covered by affine opens, and an affine scheme
étale over a field is finite over it. Hence the finite étale `K`-schemes form a dense subsite of
the small étale site of `Spec K` (`TauCeti.FiniteEtaleScheme.toEtale`), and restriction is an
equivalence between étale sheaves on `Spec K` and sheaves on finite étale `K`-schemes for the
induced topology (`TauCeti.FiniteEtaleScheme.fieldSheafEquiv`). The coefficient category only
needs limits of size `u`, so sheaves of sets, abelian groups and modules are covered. Transporting
that topology along Galois theory for finite étale schemes,
`TauCeti.FiniteEtaleScheme.galoisEquivalence K Ω`, gives the topology
`TauCeti.FiniteEtaleScheme.galoisTopology K Ω` on finite continuous `Gal(Ω/K)`-sets, whose
coverings are described here.

This is the first half of the description of all étale sheaves on a field as continuous discrete
Galois sets and modules (SGA 4, Exposé VIII, §2). The file
`TauCeti.AlgebraicGeometry.FiniteEtale.Galois.SmoothSheaf` identifies `galoisTopology K Ω` with
the jointly surjective topology and composes with the identification of sheaves on finite
continuous `G`-sets with continuous discrete `G`-sets.

## Main definitions

* `TauCeti.FiniteEtaleScheme.fieldTopology K`: the topology on finite étale `K`-schemes induced by
  the small étale topology of `Spec K`.
* `TauCeti.FiniteEtaleScheme.fieldSheafEquiv K A`: étale sheaves on `Spec K` with values in `A`
  are sheaves on finite étale `K`-schemes.
* `TauCeti.FiniteEtaleScheme.galoisTopology K Ω`: the topology on finite continuous
  `Gal(Ω/K)`-sets transported from `fieldTopology K`.

## Main results

* `TauCeti.FiniteEtaleScheme.exists_ofArrows_toEtale_mem`: every scheme étale over a field is
  covered by finite étale schemes, indexed by a type in the same universe.
* `TauCeti.FiniteEtaleScheme.ofArrows_mem_fieldTopology_iff`: the coverings for
  `fieldTopology K` are the jointly surjective families.
* `TauCeti.FiniteEtaleScheme.ofArrows_mem_galoisTopology_iff`: the coverings for
  `galoisTopology K Ω` are the families whose corresponding finite étale `K`-scheme morphisms are
  jointly surjective.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2.
* The Stacks Project, Tag 03QQ.
-/

public section

open CategoryTheory Limits AlgebraicGeometry FintypeCatDiscrete

universe v u

namespace TauCeti.FiniteEtaleScheme

variable (K : Type u) [Field K]

/-- **Schemes étale over a field are covered by finite étale schemes.** The affine opens of a
scheme `U` étale over `Spec K` are finite étale over `Spec K`, and they cover `U` in the small
étale site. -/
theorem exists_ofArrows_toEtale_mem (U : (Spec (.of K)).Etale) :
    ∃ (ι : Type u) (V : ι → FiniteEtaleScheme (Spec (.of K)))
      (f : ∀ i, (toEtale _).obj (V i) ⟶ U),
      Sieve.ofArrows _ f ∈ Scheme.smallEtaleTopology _ U := by
  let 𝒰 := U.left.affineCover
  -- An affine scheme étale over a field is finite over it.
  have (i : 𝒰.I₀) : IsFinite (𝒰.f i ≫ U.hom) :=
    IsFinite.of_locallyQuasiFinite (𝒰.f i ≫ U.hom : 𝒰.X i ⟶ Spec (.of K))
  refine ⟨𝒰.I₀, fun i ↦ ⟨Over.mk (𝒰.f i ≫ U.hom),
      (finiteEtaleSchemeProperty_iff _).mpr ⟨this i, inferInstanceAs (Etale (𝒰.f i ≫ U.hom))⟩⟩,
    fun i ↦ MorphismProperty.Over.homMk (𝒰.f i) rfl trivial, ?_⟩
  exact (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ⟨_, 𝒰.covers x⟩)

instance isCoverDense_toEtale :
    (toEtale (Spec (.of K))).IsCoverDense (Scheme.smallEtaleTopology _) where
  is_cover U := by
    obtain ⟨ι, V, f, hf⟩ := exists_ofArrows_toEtale_mem K U
    refine GrothendieckTopology.superset_covering _ ?_ hf
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact fun i ↦ ⟨{ obj := V i, lift := 𝟙 _, map := f i }⟩

/-- The topology on finite étale `K`-schemes induced by the small étale topology of `Spec K`. -/
noncomputable abbrev fieldTopology : GrothendieckTopology (FiniteEtaleScheme (Spec (.of K))) :=
  (toEtale (Spec (.of K))).inducedTopology (Scheme.smallEtaleTopology _)

/-- **Coverings of finite étale schemes over a field.** A family of morphisms of finite étale
`K`-schemes generates a covering sieve for `fieldTopology K` exactly when it is jointly
surjective. -/
theorem ofArrows_mem_fieldTopology_iff {X : FiniteEtaleScheme (Spec (.of K))} {ι : Type*}
    {Y : ι → FiniteEtaleScheme (Spec (.of K))} (f : ∀ i, Y i ⟶ X) :
    Sieve.ofArrows Y f ∈ fieldTopology K X ↔ ⋃ i, Set.range (f i).hom.left = .univ := by
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense, Sieve.functorPushforward_ofArrows]
  exact Scheme.ofArrows_mem_smallEtaleTopology_iff _

instance isOneHypercoverDense_toEtale :
    (toEtale (Spec (.of K))).IsOneHypercoverDense.{u} (fieldTopology K)
      (Scheme.smallEtaleTopology _) :=
  Functor.IsOneHypercoverDense.of_hasPullbacks (exists_ofArrows_toEtale_mem K)

variable (A : Type v) [Category.{u} A] [HasLimitsOfSize.{u, u} A]

instance isEquivalence_sheafPushforwardContinuous_toEtale :
    ((toEtale (Spec (.of K))).sheafPushforwardContinuous A (fieldTopology K)
      (Scheme.smallEtaleTopology _)).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense.{u} _ _ _ _

/-- **Étale sheaves on a field are sheaves on finite étale schemes.** Restriction along the
inclusion of finite étale `K`-schemes into the small étale site of `Spec K` is an equivalence. -/
noncomputable def fieldSheafEquiv :
    Sheaf (Scheme.smallEtaleTopology (Spec (.of K))) A ≌ Sheaf (fieldTopology K) A :=
  ((toEtale (Spec (.of K))).sheafPushforwardContinuous A (fieldTopology K)
      (Scheme.smallEtaleTopology _)).asEquivalence

/-- The functor of `fieldSheafEquiv K A` restricts a sheaf to finite étale `K`-schemes. -/
@[simp] theorem fieldSheafEquiv_functor :
    (fieldSheafEquiv K A).functor =
      (toEtale (Spec (.of K))).sheafPushforwardContinuous A (fieldTopology K)
        (Scheme.smallEtaleTopology _) :=
  (rfl)

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosed Ω] [IsGalois K Ω]

/-- The topology on finite continuous `Gal(Ω/K)`-sets corresponding to `fieldTopology K` under
Galois theory for finite étale `K`-schemes. -/
noncomputable abbrev galoisTopology : GrothendieckTopology (ContAction FintypeCat.{u} Gal(Ω/K)) :=
  (galoisEquivalence K Ω).inverse.inducedTopology (fieldTopology K)

/-- **Coverings of finite Galois sets.** A family of morphisms of finite continuous
`Gal(Ω/K)`-sets generates a covering sieve for `galoisTopology K Ω` exactly when the corresponding
morphisms of finite étale `K`-schemes are jointly surjective. -/
theorem ofArrows_mem_galoisTopology_iff {X : ContAction FintypeCat.{u} Gal(Ω/K)} {ι : Type*}
    {Y : ι → ContAction FintypeCat.{u} Gal(Ω/K)} (f : ∀ i, Y i ⟶ X) :
    Sieve.ofArrows Y f ∈ galoisTopology K Ω X ↔
      ⋃ i, Set.range ((galoisEquivalence K Ω).inverse.map (f i)).hom.left = .univ := by
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense, Sieve.functorPushforward_ofArrows]
  exact ofArrows_mem_fieldTopology_iff K _

end TauCeti.FiniteEtaleScheme

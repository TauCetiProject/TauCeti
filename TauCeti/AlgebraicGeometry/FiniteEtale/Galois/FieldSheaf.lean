/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Connected
public import TauCeti.AlgebraicGeometry.FiniteEtale.Sheaf
public import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
public import TauCeti.AlgebraicGeometry.Sites.Etale.Localization
public import TauCeti.AlgebraicGeometry.Sites.Etale.Subcanonical
public import TauCeti.CategoryTheory.Galois.Sheaf

/-!
# Étale sheaves on a field as sheaves on finite étale schemes

Let `K` be a field. A scheme étale over `Spec K` is covered by affine opens, and an affine scheme
étale over a field is finite over it. Hence the finite étale `K`-schemes form a dense subsite of
the small étale site of `Spec K` (`TauCeti.FiniteEtaleScheme.toEtale`), and restriction is an
equivalence between étale sheaves on `Spec K` and sheaves on finite étale `K`-schemes for the
induced topology (`TauCeti.FiniteEtaleScheme.fieldSheafEquiv`). Transporting that topology along
Galois theory for finite étale schemes, `TauCeti.FiniteEtaleScheme.galoisEquivalence K Ω`, gives
étale sheaves on `Spec K` as sheaves on finite continuous `Gal(Ω/K)`-sets
(`TauCeti.FiniteEtaleScheme.galoisSheafEquiv`). The coefficient category only needs limits of
size `u`, so sheaves of sets, abelian groups and modules are covered.

This is the first half of the description of all étale sheaves on a field as continuous discrete
Galois sets and modules (SGA 4, Exposé VIII, §2): the second half identifies sheaves on finite
continuous `G`-sets with continuous discrete `G`-sets.

## Main definitions

* `TauCeti.FiniteEtaleScheme.fieldTopology K`: the topology on finite étale `K`-schemes induced by
  the small étale topology of `Spec K`.
* `TauCeti.FiniteEtaleScheme.fieldSheafEquiv K A`: étale sheaves on `Spec K` with values in `A`
  are sheaves on finite étale `K`-schemes.
* `TauCeti.FiniteEtaleScheme.galoisTopology K Ω`: the topology on finite continuous
  `Gal(Ω/K)`-sets transported from `fieldTopology K`.
* `TauCeti.FiniteEtaleScheme.galoisSheafEquiv K A Ω`: étale sheaves on `Spec K` with values in
  `A` are sheaves on finite continuous `Gal(Ω/K)`-sets.

## Main results

* `TauCeti.FiniteEtaleScheme.exists_ofArrows_toEtale_mem`: every scheme étale over a field is
  covered by finite étale schemes, indexed by a type in the same universe.
* `TauCeti.FiniteEtaleScheme.ofArrows_mem_fieldTopology_iff`: the coverings for
  `fieldTopology K` are the jointly surjective families.
* `TauCeti.FiniteEtaleScheme.ofArrows_mem_galoisTopology_iff`: the coverings for
  `galoisTopology K Ω` are the families whose corresponding finite étale `K`-scheme morphisms are
  jointly surjective.
* `TauCeti.FiniteEtaleScheme.nonempty_fiberFunctor_obj_iff`: a finite Galois set is nonempty
  exactly when the corresponding finite étale `K`-scheme is.
* `TauCeti.FiniteEtaleScheme.galoisTopology_le_jointlySurjectiveTopology`: coverings for
  `galoisTopology K Ω` are jointly surjective.
* `TauCeti.FiniteEtaleScheme.subcanonical_fieldTopology`,
  `TauCeti.FiniteEtaleScheme.subcanonical_galoisTopology`: these topologies are subcanonical, being
  induced from the subcanonical small étale topology of `Spec K`.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2.
* The Stacks Project, Tag 03QQ.
-/

public section

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory FintypeCatDiscrete

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

/-- The topology on finite étale `K`-schemes induced from the small étale site of `Spec K` is
subcanonical, as the small étale topology is. -/
instance subcanonical_fieldTopology : (fieldTopology K).Subcanonical :=
  GrothendieckTopology.subcanonical_of_full_of_faithful (toEtale _) _
    (Scheme.smallEtaleTopology _)

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

variable {K Ω} in
/-- A finite continuous `Gal(Ω/K)`-set is nonempty if and only if the corresponding finite étale
`K`-scheme is nonempty. -/
theorem nonempty_fiberFunctor_obj_iff (T : ContAction FintypeCat.{u} Gal(Ω/K)) :
    Nonempty ((ContAction.fiberFunctor Gal(Ω/K)).obj T) ↔
      Nonempty ((galoisEquivalence K Ω).inverse.obj T).obj.left := by
  -- Both sides say that `T` is not initial.
  rw [← not_isEmpty_iff, ← not_isEmpty_iff, ← isInitial_iff_isEmpty]
  refine not_congr ((initial_iff_fiber_empty
    (forget₂ (ContAction FintypeCat.{u} Gal(Ω/K)) FintypeCat.{u}) T).symm.trans
      ⟨fun ⟨h⟩ ↦ ⟨h.isInitialObj _ _⟩, fun ⟨h⟩ ↦ ⟨?_⟩⟩)
  exact (h.isInitialObj (galoisEquivalence K Ω).functor _).ofIso
    ((galoisEquivalence K Ω).counitIso.app T)

/-- **Galois coverings are jointly surjective.** A covering sieve of a finite continuous
`Gal(Ω/K)`-set for the topology transported from the small étale site of `Spec K` is jointly
surjective on underlying sets. -/
theorem galoisTopology_le_jointlySurjectiveTopology :
    galoisTopology K Ω ≤ ContAction.jointlySurjectiveTopology Gal(Ω/K) := by
  -- Every point lies in the image of a Galois object `A`; the sieve pulled back to `A` covers the
  -- nonempty scheme corresponding to `A`, so it contains a map from a nonempty Galois set to the
  -- connected `A`, which is surjective.
  intro X R hR
  rw [ContAction.mem_jointlySurjectiveTopology_iff]
  intro s
  obtain ⟨A, a, a₀, hA, rfl⟩ := exists_hom_from_galois_of_fiber
    (forget₂ (ContAction FintypeCat.{u} Gal(Ω/K)) FintypeCat.{u}) X s
  have hRA := (galoisTopology K Ω).pullback_stable a hR
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense,
    Functor.mem_inducedTopology_iff_of_isCoverDense, Scheme.mem_smallEtaleTopology_iff] at hRA
  obtain ⟨x⟩ := (nonempty_fiberFunctor_obj_iff A).1 ⟨a₀⟩
  obtain ⟨Y, f, y, ⟨Z, g, h, ⟨T, t, k, ht, rfl⟩, rfl⟩, -⟩ := hRA x
  obtain ⟨t₀⟩ := (nonempty_fiberFunctor_obj_iff T).2 ⟨k.hom.left (h.left y)⟩
  have : Nonempty ((forget₂ (ContAction FintypeCat.{u} Gal(Ω/K)) FintypeCat.{u}).obj T) := ⟨t₀⟩
  obtain ⟨t₁, ht₁⟩ := surjective_of_nonempty_fiber_of_isConnected
    (forget₂ (ContAction FintypeCat.{u} Gal(Ω/K)) FintypeCat.{u}) t a₀
  exact ⟨T, t ≫ a, ht, t₁, by simp [ht₁]⟩

/-- The topology on finite continuous `Gal(Ω/K)`-sets transported from the small étale site of
`Spec K` is subcanonical. -/
instance subcanonical_galoisTopology : (galoisTopology K Ω).Subcanonical :=
  GrothendieckTopology.subcanonical_of_full_of_faithful (galoisEquivalence K Ω).inverse _
    (fieldTopology K)

/-- **Étale sheaves on a field are sheaves on finite Galois sets.** For a separable closure `Ω` of
`K`, étale sheaves on `Spec K` are sheaves on finite continuous `Gal(Ω/K)`-sets for
`galoisTopology K Ω`. -/
noncomputable def galoisSheafEquiv :
    Sheaf (Scheme.smallEtaleTopology (Spec (.of K))) A ≌ Sheaf (galoisTopology K Ω) A :=
  (fieldSheafEquiv K A).trans
    ((galoisEquivalence K Ω).sheafCongr (fieldTopology K) (galoisTopology K Ω) A)

/-- The functor of `galoisSheafEquiv` restricts a sheaf to finite étale `K`-schemes and
transports it along `galoisEquivalence K Ω`. -/
@[simp] theorem galoisSheafEquiv_functor :
    (galoisSheafEquiv K A Ω).functor = (fieldSheafEquiv K A).functor ⋙
      ((galoisEquivalence K Ω).sheafCongr (fieldTopology K) (galoisTopology K Ω) A).functor :=
  (rfl)

/-- The underlying presheaf of `(galoisSheafEquiv K A Ω).functor.obj F` is that of `F` restricted
to finite étale `K`-schemes and composed with `galoisEquivalence K Ω`: both functors in
`galoisSheafEquiv` act on underlying presheaves by precomposition. -/
theorem galoisSheafEquiv_functor_obj_obj (F : Sheaf (Scheme.smallEtaleTopology (Spec (.of K))) A) :
    ((galoisSheafEquiv K A Ω).functor.obj F).obj =
      (galoisEquivalence K Ω).inverse.op ⋙ (toEtale _).op ⋙ F.obj :=
  (rfl)

end TauCeti.FiniteEtaleScheme

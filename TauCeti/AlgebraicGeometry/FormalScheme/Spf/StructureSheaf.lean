/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Topology.Sheaves.LocallySurjective
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Carrier
public import TauCeti.AlgebraicGeometry.StructureSheaf
public import TauCeti.RingTheory.AdicCompletion.Limit
public import TauCeti.RingTheory.AdicRing.CompletedAway

import TauCeti.RingTheory.Localization.Away.Quotient

/-!
# The structure sheaf of the formal spectrum

Let `A` be a topological ring whose topology is defined by an ideal `I`. The underlying space of
the formal spectrum `Spf A` is the set `TauCeti.FormalScheme.Spf.carrier A` of open primes, and
for every ideal of definition `J` it is identified with `Spec (A ⧸ J)`
(`TauCeti.FormalScheme.Spf.homeomorphSpecQuotient`). Transporting the structure sheaf of
`Spec (A ⧸ J)` along this identification gives a sheaf of rings `O_J` on `Spf A`, and for
ideals of definition `J ≤ K` the closed immersion `Spec (A ⧸ K) → Spec (A ⧸ J)` gives a
reduction map `O_J → O_K`. The structure sheaf of `Spf A` is the limit
`O_{Spf A} = lim_n O_{I ^ (n + 1)}` of the sheaves of the thickenings `Spec (A ⧸ I ^ (n + 1))`,
taken in sheaves of commutative rings (EGA I, Ch. I, 10.1.2).

If `A` is `I`-adically complete, the global sections of `O_{Spf A}` are `A` itself
(EGA I, Ch. I, 10.1.3): taking sections commutes with limits of sheaves, the global sections
of `O_{I ^ (n + 1)}` are `A ⧸ I ^ (n + 1)`, and `A` is the limit of these rings
(`IsAdicComplete.isLimitQuotientPowSuccCone`).

Over a basic open set `D(f)` the sections of `O_{Spf A}` are the completed localisation of `A`
at `f` (EGA I, Ch. I, 10.1.4). At a finite level nothing is completed: `D(f)` corresponds to the
basic open set `D(f mod J)` of `Spec (A ⧸ J)`, so the sections of `O_J` over `D(f)` are
`A_f ⧸ J A_f`, the localisation of `A ⧸ J` away from `f`. Taking the limit over the powers of `I`
gives `Γ(D(f), O_{Spf A}) ≅ AdicCompletion (I A_f) A_f`, because the adic completion is the limit
of the rings `A_f ⧸ I ^ (n + 1) A_f` (`AdicCompletion.isLimitQuotientPowSuccCone`). For an adic
ring `A` of finite ideal type these are the completed localisations
`TauCeti.AdicRing.CompletedAway A f`, the global section corresponding to `a ∈ A` restricts to the
image of `a`, and the restriction maps of `O_{Spf A}` between basic open sets are the restriction
maps `TauCeti.AdicRing.CompletedAway.restrict` of completed localisations.

For any ideal of definition `K`, some power `I ^ (n + 1)` lies in `K`, and composing the
projection `O_{Spf A} → O_{I ^ (n + 1)}` with the reduction map `O_{I ^ (n + 1)} → O_K` gives a
projection `O_{Spf A} → O_K`, independent of `n`. This is the sheaf map of the closed immersion
`Spec (A ⧸ K) → Spf A` (EGA I, Ch. I, 10.3.2). These projections are surjective on
basic opens, and hence locally surjective as morphisms of presheaves.

The construction is made with a chosen ideal of definition `I`; another ideal of definition gives a
canonically isomorphic sheaf (EGA I, Ch. I, 10.1.1).

## Main definitions

* `TauCeti.FormalScheme.Spf.quotientInclusion`: for an ideal of definition `J`, the continuous
  map `Spec (A ⧸ J) → Spf A`, inverse to `homeomorphSpecQuotient`.
* `TauCeti.FormalScheme.Spf.quotientSheaf`: the structure sheaf of `Spec (A ⧸ J)` transported to
  the underlying space of `Spf A`.
* `TauCeti.FormalScheme.Spf.quotientTransition`: the reduction map `O_J → O_K` for ideals of
  definition `J ≤ K`.
* `TauCeti.FormalScheme.Spf.quotientDiagram`: the diagram `n ↦ O_{I ^ (n + 1)}`.
* `TauCeti.FormalScheme.Spf.structureSheaf`: its limit, the structure sheaf of `Spf A`.
* `TauCeti.FormalScheme.Spf.quotientProjection`: the projection `O_{Spf A} → O_{I ^ (n + 1)}`.
* `TauCeti.FormalScheme.Spf.structureSheaf.lift`: the morphism into `O_{Spf A}` induced by
  morphisms to the thickenings compatible with the reduction maps.
* `TauCeti.FormalScheme.Spf.toQuotientSheaf`: for ideals of definition `I` and `K`, the
  projection `O_{Spf A} → O_K` from the structure sheaf built from `I`.
* `TauCeti.FormalScheme.Spf.globalSectionsIso`: for `I`-adically complete `A`, the isomorphism
  of the global sections of `O_{Spf A}` with `A`.
* `TauCeti.FormalScheme.Spf.quotientSheafBasicOpenIso`: the isomorphism of the sections of `O_J`
  over `D(f)` with `A_f ⧸ J A_f`.
* `TauCeti.FormalScheme.Spf.basicOpenSectionsAdicCompletionIso`: the isomorphism of the sections
  of `O_{Spf A}` over `D(f)` with `AdicCompletion (I A_f) A_f`.
* `TauCeti.FormalScheme.Spf.basicOpenSectionsIso`: for an adic ring of finite ideal type and a
  finitely generated ideal of definition, the isomorphism of the sections of `O_{Spf A}` over
  `D(f)` with the completed localisation `TauCeti.AdicRing.CompletedAway A f`.

## Main results

* `TauCeti.FormalScheme.Spf.quotientSheaf_obj_obj`,
  `TauCeti.FormalScheme.Spf.quotientSheaf_obj_map`,
  `TauCeti.FormalScheme.Spf.quotientTransition_hom_app`: the sections, restriction maps and
  reduction maps over an arbitrary open, in terms of the structure sheaves of the quotients.
* `TauCeti.FormalScheme.Spf.quotientTransition_self`,
  `TauCeti.FormalScheme.Spf.quotientTransition_comp`: the reduction maps are functorial.
* `TauCeti.FormalScheme.Spf.quotientSheafGlobalSectionsIso_inv_comp_quotientTransition`: on
  global sections the reduction map `O_J → O_K` is the quotient map `A ⧸ J → A ⧸ K`.
* `TauCeti.FormalScheme.Spf.quotientProjection_comp_quotientTransition`: the projections are
  compatible with the reduction maps.
* `TauCeti.FormalScheme.Spf.structureSheaf.lift_quotientProjection`,
  `TauCeti.FormalScheme.Spf.structureSheaf.hom_ext`: morphisms into the structure sheaf correspond
  to compatible families of morphisms to the thickenings.
* `TauCeti.FormalScheme.Spf.toQuotientSheaf_eq`: the projection to `O_K` factors through the
  projection to `O_{I ^ (n + 1)}` for every `n` with `I ^ (n + 1) ≤ K`.
* `TauCeti.FormalScheme.Spf.toQuotientSheaf_comp_quotientTransition`: the projections to
  arbitrary thickenings are compatible with the reduction maps.
* `TauCeti.FormalScheme.Spf.globalSectionsIso_inv_comp_quotientProjection`: the global section
  corresponding to `a ∈ A` projects to the class of `a` in every `A ⧸ I ^ (n + 1)`.
* `TauCeti.FormalScheme.Spf.globalSectionsIso_inv_comp_toQuotientSheaf`: the global section
  corresponding to `a ∈ A` projects to the class of `a` in `A ⧸ K`.
* `TauCeti.FormalScheme.Spf.quotientTransition_app_basicOpen_comp_quotientSheafBasicOpenIso_hom`:
  on `D(f)` the reduction map `O_J → O_K` is the quotient map `A_f ⧸ J A_f → A_f ⧸ K A_f`.
* `TauCeti.FormalScheme.Spf.basicOpenSectionsAdicCompletionIso_hom_comp_evalₐ`: a section over
  `D(f)` evaluates in `A_f ⧸ I ^ (n + 1) A_f` to its projection to the `n`-th thickening.
* `TauCeti.FormalScheme.Spf.quotientProjection_app_basicOpen_surjective`,
  `TauCeti.FormalScheme.Spf.quotientTransition_app_basicOpen_surjective`,
  `TauCeti.FormalScheme.Spf.toQuotientSheaf_app_basicOpen_surjective`: the projections and
  reduction maps are surjective on basic opens.
* `TauCeti.FormalScheme.Spf.toQuotientSheaf_isLocallySurjective`: projection to an
  ideal-of-definition quotient is locally surjective.
* `TauCeti.FormalScheme.Spf.globalSectionsIso_inv_comp_basicOpenSectionsAdicCompletionIso_hom`,
  `TauCeti.FormalScheme.Spf.globalSectionsIso_inv_comp_basicOpenSectionsIso_hom`: the global
  section corresponding to `a ∈ A` restricts on `D(f)` to the image of `a`.
* `TauCeti.FormalScheme.Spf.map_comp_basicOpenSectionsIso_hom`: for an adic ring, the restriction
  maps of `O_{Spf A}` between basic open sets are the restriction maps of completed localisations.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, §10.1
  (10.1.2, 10.1.3, 10.1.4) and §10.3 (10.3.2); Ch. 0, §7.6 (7.6.15).
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

namespace TauCeti.FormalScheme.Spf

variable {A : Type u} [CommRing A] [TopologicalSpace A] {J K L : Ideal A}

section QuotientSheaf

/-- For an ideal of definition `J`, the continuous map `Spec (A ⧸ J) → Spf A` sending a prime of
`A ⧸ J` to its preimage in `A`; it is the inverse of `homeomorphSpecQuotient`. -/
noncomputable def quotientInclusion (hJ : IsAdic J) :
    PrimeSpectrum.Top (A ⧸ J) ⟶ TopCat.of (carrier A) :=
  TopCat.ofHom ⟨_, (homeomorphSpecQuotient hJ).symm.continuous⟩

/-- `quotientInclusion` sends a prime of `A ⧸ J` to its image under the inverse of
`homeomorphSpecQuotient`. -/
@[simp]
theorem quotientInclusion_apply (hJ : IsAdic J) (q : PrimeSpectrum (A ⧸ J)) :
    quotientInclusion hJ q = (homeomorphSpecQuotient hJ).symm q := by
  simp [quotientInclusion]

/-- The structure sheaf of `Spec (A ⧸ J)`, for an ideal of definition `J`, transported to the
underlying space of `Spf A` along `quotientInclusion`. Its sections over an open `U` of `Spf A`
are the sections of the structure sheaf of `Spec (A ⧸ J)` over the corresponding open. It is
exposed so that its sections and restriction maps can be stated as those of `Spec (A ⧸ J)`. -/
@[expose] noncomputable def quotientSheaf (hJ : IsAdic J) :
    Sheaf (Opens.grothendieckTopology (TopCat.of (carrier A))) CommRingCat :=
  (TopCat.Sheaf.pushforward CommRingCat (quotientInclusion hJ)).obj (Spec.structureSheaf (A ⧸ J))

/-- The sections of `O_J` over an open `U` of `Spf A` are the sections of the structure sheaf of
`Spec (A ⧸ J)` over the preimage of `U` under `quotientInclusion`. This rewrites a type, so it is
not `@[simp]`. -/
theorem quotientSheaf_obj_obj (hJ : IsAdic J) (U : (Opens (carrier A))ᵒᵖ) :
    (quotientSheaf hJ).obj.obj U =
      (Spec.structureSheaf (A ⧸ J)).obj.obj ((Opens.map (quotientInclusion hJ)).op.obj U) :=
  rfl

/-- The restriction maps of `O_J` are those of the structure sheaf of `Spec (A ⧸ J)` along
`quotientInclusion`. -/
@[simp]
theorem quotientSheaf_obj_map (hJ : IsAdic J) {U V : (Opens (carrier A))ᵒᵖ} (i : U ⟶ V) :
    (quotientSheaf hJ).obj.map i =
      (Spec.structureSheaf (A ⧸ J)).obj.map ((Opens.map (quotientInclusion hJ)).op.map i) :=
  rfl

/-- For ideals of definition `J ≤ K`, the preimage of an open `U` of `Spf A` in `Spec (A ⧸ K)` lies
over its preimage in `Spec (A ⧸ J)` under the closed immersion `Spec (A ⧸ K) → Spec (A ⧸ J)`. -/
theorem map_quotientInclusion_subset (hJ : IsAdic J) (hK : IsAdic K) (hJK : J ≤ K)
    (U : Opens (carrier A)) :
    ((Opens.map (quotientInclusion hK)).obj U).1 ⊆
      PrimeSpectrum.comap (Ideal.Quotient.factor hJK) ⁻¹'
        ((Opens.map (quotientInclusion hJ)).obj U).1 := by
  intro q hq
  simpa [quotientInclusion, homeomorphSpecQuotient_symm_comap_factor hJ hK hJK] using hq

/-- For ideals of definition `J ≤ K`, the reduction map `O_J → O_K` between the transported
structure sheaves, induced on sections by the quotient map `A ⧸ J → A ⧸ K`. -/
noncomputable def quotientTransition (hJ : IsAdic J) (hK : IsAdic K) (hJK : J ≤ K) :
    quotientSheaf hJ ⟶ quotientSheaf hK :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (StructureSheaf.comap (Ideal.Quotient.factor hJK) _ _
        (map_quotientInclusion_subset hJ hK hJK U.unop))
      naturality _ _ _ := CommRingCat.hom_ext <|
        (StructureSheaf.comap_comp_map _ _ _ _).trans (StructureSheaf.map_comp_comap _ _ _ _).symm }

/-- On sections over an open `U`, the reduction map `O_J → O_K` is the map of structure sheaves
induced by the quotient map `A ⧸ J → A ⧸ K`. -/
@[simp]
theorem quotientTransition_hom_app (hJ : IsAdic J) (hK : IsAdic K) (hJK : J ≤ K)
    (U : (Opens (carrier A))ᵒᵖ) :
    (quotientTransition hJ hK hJK).hom.app U =
      CommRingCat.ofHom (StructureSheaf.comap (Ideal.Quotient.factor hJK) _ _
        (map_quotientInclusion_subset hJ hK hJK U.unop)) := by
  unfold quotientTransition
  rfl

/-- The reduction map `O_J → O_J` is the identity. -/
@[simp]
theorem quotientTransition_self (hJ : IsAdic J) : quotientTransition hJ hJ le_rfl = 𝟙 _ := by
  apply Sheaf.hom_ext
  ext U : 2
  exact CommRingCat.hom_ext <|
    (StructureSheaf.comap_congr Ideal.Quotient.factor_eq _ _ _ _).trans
      (StructureSheaf.comap_id' _)

/-- The reduction maps compose: `O_J → O_K → O_L` is `O_J → O_L`. -/
@[reassoc (attr := simp)]
theorem quotientTransition_comp (hJ : IsAdic J) (hK : IsAdic K) (hL : IsAdic L) (hJK : J ≤ K)
    (hKL : K ≤ L) :
    quotientTransition hJ hK hJK ≫ quotientTransition hK hL hKL =
      quotientTransition hJ hL (hJK.trans hKL) := by
  apply Sheaf.hom_ext
  ext U : 2
  exact CommRingCat.hom_ext <| (StructureSheaf.comap_comp _ _ _ _ _ _ _).symm.trans
    (StructureSheaf.comap_congr (Ideal.Quotient.factor_comp hJK hKL) _ _ _ _)

/-- The global sections of the transported structure sheaf `O_J` are `A ⧸ J`. -/
noncomputable def quotientSheafGlobalSectionsIso (hJ : IsAdic J) :
    (quotientSheaf hJ).obj.obj (op ⊤) ≅ CommRingCat.of (A ⧸ J) :=
  (StructureSheaf.globalSectionsIso (A ⧸ J)).symm

/-- The inverse of the identification of the global sections of `O_J` with `A ⧸ J` is the
canonical map from `A ⧸ J` to the global sections of the structure sheaf of `Spec (A ⧸ J)`. -/
theorem quotientSheafGlobalSectionsIso_inv (hJ : IsAdic J) :
    (quotientSheafGlobalSectionsIso hJ).inv = CommRingCat.ofHom (algebraMap _ _) :=
  (rfl)

/-- On global sections, the reduction map `O_J → O_K` is the quotient map `A ⧸ J → A ⧸ K`. -/
@[reassoc]
theorem quotientSheafGlobalSectionsIso_inv_comp_quotientTransition (hJ : IsAdic J) (hK : IsAdic K)
    (hJK : J ≤ K) :
    (quotientSheafGlobalSectionsIso hJ).inv ≫ (quotientTransition hJ hK hJK).hom.app (op ⊤) =
      CommRingCat.ofHom (Ideal.Quotient.factor hJK) ≫ (quotientSheafGlobalSectionsIso hK).inv :=
  StructureSheaf.toOpen_comp_comap _ _

/-- On global sections, the reduction map `O_J → O_K` is the quotient map `A ⧸ J → A ⧸ K`, in
the form transporting sections of `O_J` to `A ⧸ K`. -/
@[reassoc]
theorem quotientTransition_comp_quotientSheafGlobalSectionsIso_hom (hJ : IsAdic J) (hK : IsAdic K)
    (hJK : J ≤ K) :
    (quotientTransition hJ hK hJK).hom.app (op ⊤) ≫ (quotientSheafGlobalSectionsIso hK).hom =
      (quotientSheafGlobalSectionsIso hJ).hom ≫ CommRingCat.ofHom (Ideal.Quotient.factor hJK) := by
  rw [← cancel_epi (quotientSheafGlobalSectionsIso hJ).inv,
    quotientSheafGlobalSectionsIso_inv_comp_quotientTransition_assoc]
  simp

end QuotientSheaf

section StructureSheaf

variable [IsTopologicalRing A] {I : Ideal A}

/-- The diagram `O_I ← O_{I ^ 2} ← O_{I ^ 3} ← ⋯` of the structure sheaves of the thickenings
`Spec (A ⧸ I ^ (n + 1))`, transported to the underlying space of `Spf A`, with the reduction maps
as transitions. -/
noncomputable def quotientDiagram (hI : IsAdic I) :
    ℕᵒᵖ ⥤ Sheaf (Opens.grothendieckTopology (TopCat.of (carrier A))) CommRingCat where
  obj n := quotientSheaf (is_ideal_adic_pow hI n.unop.succ_pos)
  map f := quotientTransition _ _ (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop)))
  map_id _ := quotientTransition_self _
  map_comp _ _ := (quotientTransition_comp _ _ _ _ _).symm

/-- The **structure sheaf** `O_{Spf A} = lim_n O_{I ^ (n + 1)}` of the formal spectrum, the limit
in sheaves of commutative rings of the structure sheaves of the thickenings
`Spec (A ⧸ I ^ (n + 1))` (EGA I, Ch. I, 10.1.2). -/
noncomputable def structureSheaf (hI : IsAdic I) :
    Sheaf (Opens.grothendieckTopology (TopCat.of (carrier A))) CommRingCat :=
  limit (quotientDiagram hI)

/-- The projection `O_{Spf A} → O_{I ^ (n + 1)}` from the structure sheaf to the structure sheaf of
the `n`-th thickening. -/
noncomputable def quotientProjection (hI : IsAdic I) (n : ℕ) :
    structureSheaf hI ⟶ quotientSheaf (is_ideal_adic_pow hI n.succ_pos) :=
  limit.π (quotientDiagram hI) (op n)

/-- The projections to the thickenings are compatible with the reduction maps. -/
@[reassoc (attr := simp)]
theorem quotientProjection_comp_quotientTransition (hI : IsAdic I) {m n : ℕ} (h : m ≤ n) :
    quotientProjection hI n ≫ quotientTransition _ _
        (Ideal.pow_le_pow_right (Nat.succ_le_succ h)) =
      quotientProjection hI m :=
  limit.w (quotientDiagram hI) (homOfLE h).op

/-- The morphism into the structure sheaf of `Spf A` induced by a family of morphisms to the
thickenings that is compatible with the reduction maps. -/
noncomputable def structureSheaf.lift (hI : IsAdic I)
    {F : Sheaf (Opens.grothendieckTopology (TopCat.of (carrier A))) CommRingCat}
    (f : ∀ n : ℕ, F ⟶ quotientSheaf (is_ideal_adic_pow hI n.succ_pos))
    (hf : ∀ {m n : ℕ} (h : m ≤ n),
      f n ≫ quotientTransition _ _ (Ideal.pow_le_pow_right (Nat.succ_le_succ h)) = f m) :
    F ⟶ structureSheaf hI :=
  limit.lift (quotientDiagram hI)
    { pt := F
      π :=
        { app n := f n.unop
          naturality _ _ g := (Category.id_comp _).trans (hf (leOfHom g.unop)).symm } }

/-- The morphism `structureSheaf.lift` projects to the given morphisms to the thickenings. -/
@[reassoc (attr := simp)]
theorem structureSheaf.lift_quotientProjection (hI : IsAdic I)
    {F : Sheaf (Opens.grothendieckTopology (TopCat.of (carrier A))) CommRingCat}
    (f : ∀ n : ℕ, F ⟶ quotientSheaf (is_ideal_adic_pow hI n.succ_pos))
    (hf : ∀ {m n : ℕ} (h : m ≤ n),
      f n ≫ quotientTransition _ _ (Ideal.pow_le_pow_right (Nat.succ_le_succ h)) = f m)
    (n : ℕ) :
    structureSheaf.lift hI f hf ≫ quotientProjection hI n = f n :=
  limit.lift_π _ _

/-- Morphisms into the structure sheaf of `Spf A` are determined by their projections to the
thickenings. -/
theorem structureSheaf.hom_ext (hI : IsAdic I)
    {F : Sheaf (Opens.grothendieckTopology (TopCat.of (carrier A))) CommRingCat}
    {f g : F ⟶ structureSheaf hI}
    (h : ∀ n, f ≫ quotientProjection hI n = g ≫ quotientProjection hI n) : f = g :=
  limit.hom_ext fun n ↦ h n.unop

/-- For ideals of definition `I` and `K`, the projection `O_{Spf A} → O_K` from the structure
sheaf built from `I` to the structure sheaf of the thickening `Spec (A ⧸ K)`: the projection to
`O_{I ^ (n + 1)}` followed by the reduction map, for any `n` with `I ^ (n + 1) ≤ K`
(`toQuotientSheaf_eq`). It is the sheaf map of the closed immersion `Spec (A ⧸ K) → Spf A`. -/
noncomputable def toQuotientSheaf (hI : IsAdic I) (hK : IsAdic K) :
    structureSheaf hI ⟶ quotientSheaf hK :=
  quotientProjection hI (hI.exists_pow_succ_le (by simpa using hK.isOpen_pow 1)).choose ≫
    quotientTransition _ hK (hI.exists_pow_succ_le (by simpa using hK.isOpen_pow 1)).choose_spec

/-- The two-step composites `O_{Spf A} → O_{I ^ (n + 1)} → O_K` agree for all admissible `n`. -/
private theorem quotientProjection_comp_quotientTransition_eq (hI : IsAdic I) (hK : IsAdic K)
    {m n : ℕ} (hm : I ^ (m + 1) ≤ K) (hn : I ^ (n + 1) ≤ K) :
    quotientProjection hI m ≫ quotientTransition _ hK hm =
      quotientProjection hI n ≫ quotientTransition _ hK hn := by
  wlog hmn : m ≤ n generalizing m n
  · exact (this hn hm (le_of_not_ge hmn)).symm
  rw [← quotientProjection_comp_quotientTransition hI hmn, Category.assoc,
    quotientTransition_comp]

/-- The projection to `O_K` is the projection to `O_{I ^ (n + 1)}` followed by the reduction map,
for every `n` with `I ^ (n + 1) ≤ K`. -/
theorem toQuotientSheaf_eq (hI : IsAdic I) (hK : IsAdic K) {n : ℕ} (hn : I ^ (n + 1) ≤ K) :
    toQuotientSheaf hI hK = quotientProjection hI n ≫ quotientTransition _ hK hn :=
  quotientProjection_comp_quotientTransition_eq hI hK _ hn

/-- The projection to the thickening `O_{I ^ (n + 1)}` is `quotientProjection`. -/
@[simp]
theorem toQuotientSheaf_pow_succ (hI : IsAdic I) (n : ℕ) :
    toQuotientSheaf hI (is_ideal_adic_pow hI n.succ_pos) = quotientProjection hI n := by
  rw [toQuotientSheaf_eq hI _ le_rfl, quotientTransition_self, Category.comp_id]

/-- The projections to the thickenings are compatible with the reduction maps `O_K → O_L`. -/
@[reassoc (attr := simp)]
theorem toQuotientSheaf_comp_quotientTransition (hI : IsAdic I) (hK : IsAdic K) (hL : IsAdic L)
    (hKL : K ≤ L) :
    toQuotientSheaf hI hK ≫ quotientTransition hK hL hKL = toQuotientSheaf hI hL := by
  obtain ⟨n, hn⟩ := hI.exists_pow_succ_le (by simpa using hK.isOpen_pow 1)
  rw [toQuotientSheaf_eq hI hK hn, toQuotientSheaf_eq hI hL (hn.trans hKL), Category.assoc,
    quotientTransition_comp]

/-- The morphism `structureSheaf.lift` projects to every thickening `O_K` through the given
morphism to a thickening `O_{I ^ (n + 1)}` with `I ^ (n + 1) ≤ K`. -/
@[reassoc]
theorem structureSheaf.lift_toQuotientSheaf (hI : IsAdic I) (hK : IsAdic K)
    {F : Sheaf (Opens.grothendieckTopology (TopCat.of (carrier A))) CommRingCat}
    (f : ∀ n : ℕ, F ⟶ quotientSheaf (is_ideal_adic_pow hI n.succ_pos))
    (hf : ∀ {m n : ℕ} (h : m ≤ n),
      f n ≫ quotientTransition _ _ (Ideal.pow_le_pow_right (Nat.succ_le_succ h)) = f m)
    {n : ℕ} (hn : I ^ (n + 1) ≤ K) :
    structureSheaf.lift hI f hf ≫ toQuotientSheaf hI hK = f n ≫ quotientTransition _ hK hn := by
  rw [toQuotientSheaf_eq hI hK hn, structureSheaf.lift_quotientProjection_assoc]

/-- On global sections, the diagram of the thickenings is the diagram of the quotients
`A ⧸ I ^ (n + 1)`. -/
private noncomputable def quotientDiagramGlobalSectionsIso (hI : IsAdic I) :
    quotientDiagram hI ⋙ sheafToPresheaf _ CommRingCat ⋙ (evaluation _ CommRingCat).obj (op ⊤) ≅
      Ideal.quotientPowSuccDiagram I :=
  NatIso.ofComponents
    (fun n ↦ quotientSheafGlobalSectionsIso (is_ideal_adic_pow hI n.unop.succ_pos))
    fun _ ↦ quotientTransition_comp_quotientSheafGlobalSectionsIso_hom _ _ _

variable [IsAdicComplete I A]

/-- If `A` is `I`-adically complete, the global sections of the structure sheaf of `Spf A` are
`A` (EGA I, Ch. I, 10.1.3). -/
noncomputable def globalSectionsIso (hI : IsAdic I) :
    (structureSheaf hI).obj.obj (op ⊤) ≅ CommRingCat.of A :=
  preservesLimitIso (sheafToPresheaf _ CommRingCat ⋙ (evaluation _ CommRingCat).obj (op ⊤))
      (quotientDiagram hI) ≪≫
    HasLimit.isoOfNatIso (quotientDiagramGlobalSectionsIso hI) ≪≫
    (limit.isLimit _).conePointUniqueUpToIso (IsAdicComplete.isLimitQuotientPowSuccCone I)

/-- The global section of the structure sheaf of `Spf A` corresponding to `a ∈ A` projects to the
class of `a` in the global sections `A ⧸ I ^ (n + 1)` of the `n`-th thickening. -/
@[reassoc (attr := simp)]
theorem globalSectionsIso_inv_comp_quotientProjection (hI : IsAdic I) (n : ℕ) :
    (globalSectionsIso hI).inv ≫ (quotientProjection hI n).hom.app (op ⊤) =
      CommRingCat.ofHom (Ideal.Quotient.mk _) ≫
        (quotientSheafGlobalSectionsIso (is_ideal_adic_pow hI n.succ_pos)).inv := by
  have ha := preservesLimitIso_inv_π
    (sheafToPresheaf _ CommRingCat ⋙ (evaluation _ CommRingCat).obj (op ⊤)) (quotientDiagram hI)
    (op n)
  have hb := HasLimit.isoOfNatIso_inv_π (quotientDiagramGlobalSectionsIso hI) (op n)
  have hc := (limit.isLimit _).conePointUniqueUpToIso_inv_comp
    (IsAdicComplete.isLimitQuotientPowSuccCone I) (op n)
  -- Unfold the inverse along its three factors: sections commute with the limit, the diagram of
  -- sections is the diagram of quotients, and `A` is the limit of the quotients. `erw` is needed
  -- because the sections functor applied to `limit.π` is `(limit.π _ _).hom.app (op ⊤)` only
  -- up to unfolding `sheafToPresheaf` and evaluation.
  unfold globalSectionsIso quotientProjection
  erw [Iso.trans_inv, Iso.trans_inv, Category.assoc, Category.assoc, ha]
  refine (congrArg (_ ≫ ·) hb).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) hc

/-- The global section of the structure sheaf of `Spf A` corresponding to `a ∈ A` projects to the
class of `a` in the global sections `A ⧸ K` of the thickening `O_K`. -/
@[reassoc (attr := simp)]
theorem globalSectionsIso_inv_comp_toQuotientSheaf (hI : IsAdic I) (hK : IsAdic K) :
    (globalSectionsIso hI).inv ≫ (toQuotientSheaf hI hK).hom.app (op ⊤) =
      CommRingCat.ofHom (Ideal.Quotient.mk K) ≫ (quotientSheafGlobalSectionsIso hK).inv := by
  obtain ⟨n, hn⟩ := hI.exists_pow_succ_le (by simpa using hK.isOpen_pow 1)
  rw [toQuotientSheaf_eq hI hK hn, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    globalSectionsIso_inv_comp_quotientProjection_assoc,
    quotientSheafGlobalSectionsIso_inv_comp_quotientTransition, ← Category.assoc,
    ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]

end StructureSheaf

section QuotientSheafBasicOpen

/-- For an ideal of definition `J`, the basic open set `D(f)` of `Spf A` corresponds to the basic
open set `D(f mod J)` of `Spec (A ⧸ J)`. -/
theorem map_quotientInclusion_basicOpen (hJ : IsAdic J) (f : A) :
    (Opens.map (quotientInclusion hJ)).obj (basicOpen f) =
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk J f) := by
  ext q
  simp [quotientInclusion]
  -- membership in `PrimeSpectrum.basicOpen` is non-membership in the prime, by definition
  rfl

/-- The sections of the structure sheaf of `Spec (A ⧸ J)` over the open corresponding to `D(f)`
are a localisation of `A ⧸ J` away from the image of `f`. -/
private theorem isLocalization_quotientSheaf_basicOpen (hJ : IsAdic J) (f : A) :
    IsLocalization.Away (Ideal.Quotient.mk J f) ((Spec.structureSheaf (A ⧸ J)).obj.obj
      (op ((Opens.map (quotientInclusion hJ)).obj (basicOpen f)))) := by
  rw [map_quotientInclusion_basicOpen]
  infer_instance

/-- For an ideal of definition `J`, the sections over `D(f)` of the structure sheaf `O_J` of the
thickening `Spec (A ⧸ J)` are `A_f ⧸ J A_f`, the localisation of `A ⧸ J` away from `f`. -/
noncomputable def quotientSheafBasicOpenIso (hJ : IsAdic J) (f : A) :
    (quotientSheaf hJ).obj.obj (op (basicOpen f)) ≅
      CommRingCat.of (Localization.Away f ⧸ J.map (algebraMap A (Localization.Away f))) :=
  have := isLocalization_quotientSheaf_basicOpen hJ f
  (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk J f))
    ((Spec.structureSheaf (A ⧸ J)).obj.obj
      (op ((Opens.map (quotientInclusion hJ)).obj (basicOpen f))))
    (Localization.Away f ⧸ J.map (algebraMap A (Localization.Away f)))).toRingEquiv.toCommRingCatIso

/-- The global section of `O_J` corresponding to `a ∈ A ⧸ J` restricts on `D(f)` to the image of
`a` in `A_f ⧸ J A_f`. -/
@[reassoc]
theorem quotientSheafGlobalSectionsIso_inv_comp_quotientSheafBasicOpenIso_hom (hJ : IsAdic J)
    (f : A) :
    (quotientSheafGlobalSectionsIso hJ).inv ≫ (quotientSheaf hJ).obj.map (homOfLE le_top).op ≫
        (quotientSheafBasicOpenIso hJ f).hom =
      CommRingCat.ofHom (algebraMap (A ⧸ J)
        (Localization.Away f ⧸ J.map (algebraMap A (Localization.Away f)))) := by
  have := isLocalization_quotientSheaf_basicOpen hJ f
  -- `quotientSheafGlobalSectionsIso hJ` is inverse to Mathlib's `StructureSheaf.globalSectionsIso`,
  -- whose forward map is the algebra map, and restriction commutes with the algebra maps
  -- (`StructureSheaf.algebraMap_self_map`), so the composite is the algebra map into `A_f ⧸ J A_f`
  ext x
  exact (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk J f))
    ((Spec.structureSheaf (A ⧸ J)).obj.obj
      (op ((Opens.map (quotientInclusion hJ)).obj (basicOpen f))))
    (Localization.Away f ⧸ J.map (algebraMap A (Localization.Away f)))).commutes x

/-- Restriction of global sections of `O_J` to `D(f)` is an epimorphism of rings: up to
isomorphism it is the localisation map `A ⧸ J → A_f ⧸ J A_f`. -/
private theorem epi_quotientSheafGlobalSectionsIso_inv_comp_map (hJ : IsAdic J) (f : A) :
    Epi ((quotientSheafGlobalSectionsIso hJ).inv ≫
      (quotientSheaf hJ).obj.map (homOfLE (le_top : basicOpen f ≤ ⊤)).op) := by
  have h := quotientSheafGlobalSectionsIso_inv_comp_quotientSheafBasicOpenIso_hom hJ f
  rw [← Category.assoc, ← Iso.eq_comp_inv] at h
  rw [h]
  have := IsLocalization.epi (Submonoid.powers (Ideal.Quotient.mk J f))
    (Localization.Away f ⧸ J.map (algebraMap A (Localization.Away f)))
  exact epi_comp _ _

/-- On `D(f)`, the reduction map `O_J → O_K` for ideals of definition `J ≤ K` is the quotient map
`A_f ⧸ J A_f → A_f ⧸ K A_f`. -/
@[reassoc]
theorem quotientTransition_app_basicOpen_comp_quotientSheafBasicOpenIso_hom
    (hJ : IsAdic J) (hK : IsAdic K) (hJK : J ≤ K) (f : A) :
    (quotientTransition hJ hK hJK).hom.app (op (basicOpen f)) ≫
        (quotientSheafBasicOpenIso hK f).hom =
      (quotientSheafBasicOpenIso hJ f).hom ≫
        CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.map_mono hJK)) := by
  have := epi_quotientSheafGlobalSectionsIso_inv_comp_map hJ f
  rw [← cancel_epi ((quotientSheafGlobalSectionsIso hJ).inv ≫
    (quotientSheaf hJ).obj.map (homOfLE (le_top : basicOpen f ≤ ⊤)).op), Category.assoc,
    (quotientTransition hJ hK hJK).hom.naturality_assoc,
    quotientSheafGlobalSectionsIso_inv_comp_quotientTransition_assoc, Category.assoc,
    quotientSheafGlobalSectionsIso_inv_comp_quotientSheafBasicOpenIso_hom,
    quotientSheafGlobalSectionsIso_inv_comp_quotientSheafBasicOpenIso_hom_assoc]
  ext x
  simp [-Ideal.Quotient.mk_algebraMap]

/-- Reduction between two ideals of definition is surjective on every basic open. -/
theorem quotientTransition_app_basicOpen_surjective (hJ : IsAdic J) (hK : IsAdic K)
    (hJK : J ≤ K) (f : A) :
    Function.Surjective ((quotientTransition hJ hK hJK).hom.app (op (basicOpen f))) := by
  have h : Function.Surjective ((quotientSheafBasicOpenIso hJ f).hom ≫
      CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.map_mono hJK))) :=
    (Ideal.Quotient.factor_surjective (Ideal.map_mono hJK)).comp
      (ConcreteCategory.bijective_of_isIso (quotientSheafBasicOpenIso hJ f).hom).surjective
  rw [← quotientTransition_app_basicOpen_comp_quotientSheafBasicOpenIso_hom hJ hK hJK f] at h
  intro s
  obtain ⟨x, hx⟩ := h ((quotientSheafBasicOpenIso hK f).hom s)
  exact ⟨x, (ConcreteCategory.bijective_of_isIso (quotientSheafBasicOpenIso hK f).hom).injective hx⟩

end QuotientSheafBasicOpen

section BasicOpenSections

variable [IsTopologicalRing A] {I : Ideal A}

/-- On `D(f)`, the diagram of the thickenings is the diagram of the quotients
`A_f ⧸ I ^ (n + 1) A_f`. -/
private noncomputable def quotientDiagramBasicOpenIso (hI : IsAdic I) (f : A) :
    quotientDiagram hI ⋙ sheafToPresheaf _ CommRingCat ⋙
        (evaluation _ CommRingCat).obj (op (basicOpen f)) ≅
      Ideal.quotientPowSuccDiagram (I.map (algebraMap A (Localization.Away f))) :=
  NatIso.ofComponents
    (fun n ↦ quotientSheafBasicOpenIso (is_ideal_adic_pow hI n.unop.succ_pos) f ≪≫
      (Ideal.quotEquivOfEq (Ideal.map_pow _ I (n.unop + 1))).toCommRingCatIso)
    fun g ↦ (quotientTransition_app_basicOpen_comp_quotientSheafBasicOpenIso_hom_assoc _ _ _ f
      _).trans (congrArg (_ ≫ ·)
        (Ideal.factor_comp_quotEquivOfEq_map_pow I _ (leOfHom g.unop)))

/-- The sections over `D(f)` of the structure sheaf of `Spf A` are the completion
`AdicCompletion (I A_f) A_f` of the localisation `A_f` of `A` away from `f` (EGA I, Ch. I,
10.1.4). -/
noncomputable def basicOpenSectionsAdicCompletionIso (hI : IsAdic I) (f : A) :
    (structureSheaf hI).obj.obj (op (basicOpen f)) ≅
      CommRingCat.of (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
        (Localization.Away f)) :=
  preservesLimitIso (sheafToPresheaf _ CommRingCat ⋙
      (evaluation _ CommRingCat).obj (op (basicOpen f))) (quotientDiagram hI) ≪≫
    HasLimit.isoOfNatIso (quotientDiagramBasicOpenIso hI f) ≪≫
    (limit.isLimit _).conePointUniqueUpToIso (AdicCompletion.isLimitQuotientPowSuccCone _)

/-- A section of the structure sheaf of `Spf A` over `D(f)` evaluates in `A_f ⧸ I ^ (n + 1) A_f`
to its projection to the `n`-th thickening, read in `A_f ⧸ I ^ (n + 1) A_f`. -/
@[reassoc (attr := simp)]
theorem basicOpenSectionsAdicCompletionIso_hom_comp_evalₐ (hI : IsAdic I) (f : A) (n : ℕ) :
    (basicOpenSectionsAdicCompletionIso hI f).hom ≫
        CommRingCat.ofHom
          (AdicCompletion.evalₐ (I.map (algebraMap A (Localization.Away f))) (n + 1) : _ →+* _) =
      (quotientProjection hI n).hom.app (op (basicOpen f)) ≫
        (quotientSheafBasicOpenIso (is_ideal_adic_pow hI n.succ_pos) f).hom ≫
          CommRingCat.ofHom (Ideal.quotEquivOfEq (Ideal.map_pow _ I (n + 1))).toRingHom := by
  have ha := preservesLimitIso_hom_π (sheafToPresheaf _ CommRingCat ⋙
      (evaluation _ CommRingCat).obj (op (basicOpen f))) (quotientDiagram hI) (op n)
  have hb := HasLimit.isoOfNatIso_hom_π (quotientDiagramBasicOpenIso hI f) (op n)
  have hc := (limit.isLimit _).conePointUniqueUpToIso_hom_comp
    (AdicCompletion.isLimitQuotientPowSuccCone (I.map (algebraMap A (Localization.Away f)))) (op n)
  -- Unfold the isomorphism along its three factors: sections commute with the limit, the diagram
  -- of sections on `D(f)` is the diagram of the quotients of `A_f`, and the adic completion is
  -- the limit of these quotients.
  calc _ = (preservesLimitIso _ _).hom ≫ (HasLimit.isoOfNatIso _).hom ≫ limit.π _ (op n) :=
        congrArg (_ ≫ _ ≫ ·) hc
    _ = _ := (congrArg (_ ≫ ·) hb).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ha))

/-- Projection to an infinitesimal thickening is surjective on every basic open. -/
theorem quotientProjection_app_basicOpen_surjective (hI : IsAdic I) (f : A) (n : ℕ) :
    Function.Surjective ((quotientProjection hI n).hom.app (op (basicOpen f))) := by
  have h : Function.Surjective
      ((basicOpenSectionsAdicCompletionIso hI f).hom ≫ CommRingCat.ofHom
        (AdicCompletion.evalₐ (I.map (algebraMap A (Localization.Away f))) (n + 1)).toRingHom) :=
    (AdicCompletion.surjective_evalₐ _ _).comp
      (ConcreteCategory.bijective_of_isIso (basicOpenSectionsAdicCompletionIso hI f).hom).surjective
  simp only [AlgHom.toRingHom_eq_coe] at h
  rw [basicOpenSectionsAdicCompletionIso_hom_comp_evalₐ] at h
  intro s
  obtain ⟨x, hx⟩ := h ((Ideal.quotEquivOfEq (Ideal.map_pow _ I (n + 1)))
    ((quotientSheafBasicOpenIso (is_ideal_adic_pow hI n.succ_pos) f).hom s))
  refine ⟨x, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (quotientSheafBasicOpenIso (is_ideal_adic_pow hI n.succ_pos) f).hom).injective
  exact (Ideal.quotEquivOfEq (Ideal.map_pow _ I (n + 1))).injective hx

/-- The projection to the structure sheaf modulo any ideal of definition is surjective on
basic opens. This does not assert surjectivity on arbitrary opens. -/
theorem toQuotientSheaf_app_basicOpen_surjective (hI : IsAdic I) (hJ : IsAdic J) (f : A) :
    Function.Surjective ((toQuotientSheaf hI hJ).hom.app (op (basicOpen f))) := by
  obtain ⟨n, hn⟩ := hI.exists_pow_succ_le (by simpa using hJ.isOpen_pow 1)
  rw [toQuotientSheaf_eq hI hJ hn]
  exact (quotientTransition_app_basicOpen_surjective _ hJ hn f).comp
    (quotientProjection_app_basicOpen_surjective hI f n)

/-- The structure-sheaf projection to an ideal-of-definition quotient is locally surjective. -/
theorem toQuotientSheaf_isLocallySurjective (hI : IsAdic I) (hJ : IsAdic J) :
    TopCat.Presheaf.IsLocallySurjective (toQuotientSheaf hI hJ).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U s p hp
  obtain ⟨V, ⟨f, rfl⟩, hpf, hfU⟩ := (Opens.isBasis_iff_nbhd.mp isBasis_basicOpen) hp
  obtain ⟨t, ht⟩ := toQuotientSheaf_app_basicOpen_surjective hI hJ f
    ((quotientSheaf hJ).obj.map (homOfLE hfU).op s)
  exact ⟨basicOpen f, hfU, ⟨t, ht⟩, hpf⟩

variable [IsAdicComplete I A]

/-- If `A` is `I`-adically complete, the global section of the structure sheaf of `Spf A`
corresponding to `a ∈ A` restricts on `D(f)` to the image of `a` in `AdicCompletion (I A_f) A_f`. -/
@[reassoc (attr := simp)]
theorem globalSectionsIso_inv_comp_basicOpenSectionsAdicCompletionIso_hom (hI : IsAdic I) (f : A) :
    (globalSectionsIso hI).inv ≫
        (structureSheaf hI).obj.map (homOfLE (le_top : basicOpen f ≤ ⊤)).op ≫
          (basicOpenSectionsAdicCompletionIso hI f).hom =
      CommRingCat.ofHom (algebraMap A (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
        (Localization.Away f))) := by
  refine (AdicCompletion.isLimitQuotientPowSuccCone _).hom_ext fun n ↦ ?_
  -- the projections of the limit cone are the evaluation maps `evalₐ`; the `change` reads the
  -- cone's apex and the diagram's objects as the rings they are, so that `Category.assoc` applies
  rw [AdicCompletion.quotientPowSuccCone_π_app]
  change (_ : _ ⟶ CommRingCat.of (AdicCompletion _ _)) ≫ (_ : _ ⟶ CommRingCat.of (_ ⧸ _)) =
    (_ : _ ⟶ CommRingCat.of (AdicCompletion _ _)) ≫ (_ : _ ⟶ CommRingCat.of (_ ⧸ _))
  rw [Category.assoc, Category.assoc, basicOpenSectionsAdicCompletionIso_hom_comp_evalₐ,
    (quotientProjection hI n.unop).hom.naturality_assoc,
    globalSectionsIso_inv_comp_quotientProjection_assoc,
    quotientSheafGlobalSectionsIso_inv_comp_quotientSheafBasicOpenIso_hom_assoc]
  ext a
  simp [← Ideal.Quotient.mk_algebraMap, Ideal.quotEquivOfEq_mk]

end BasicOpenSections

section AdicRing

variable [IsTopologicalRing A] [IsAdicRing A] {I : Ideal A}

/-- For an adic ring `A` of finite ideal type and a finitely generated ideal of definition `I`,
the sections over `D(f)` of the structure sheaf of `Spf A` formed with `I` are the completed
localisation `A_{f} = TauCeti.AdicRing.CompletedAway A f` (EGA I, Ch. I, 10.1.4). It is
`basicOpenSectionsAdicCompletionIso` followed by the comparison
`TauCeti.AdicRing.CompletedAway.idealEquiv` of the completions along `I` and along the chosen
ideal of definition. -/
noncomputable def basicOpenSectionsIso (hI : IsAdic I) (hIfg : I.FG) (f : A) :
    (structureSheaf hI).obj.obj (op (basicOpen f)) ≅ CommRingCat.of (AdicRing.CompletedAway A f) :=
  basicOpenSectionsAdicCompletionIso hI f ≪≫
    (AdicRing.CompletedAway.idealEquiv f I hI hIfg).symm.toRingEquiv.toCommRingCatIso

/-- Followed by the comparison `TauCeti.AdicRing.CompletedAway.idealEquiv`, the identification
`basicOpenSectionsIso` of the sections over `D(f)` with `A_{f}` is
`basicOpenSectionsAdicCompletionIso`. -/
@[reassoc]
theorem basicOpenSectionsIso_hom_comp_idealEquiv (hI : IsAdic I) (hIfg : I.FG) (f : A) :
    (basicOpenSectionsIso hI hIfg f).hom ≫
        CommRingCat.ofHom (AdicRing.CompletedAway.idealEquiv f I hI hIfg : _ →+* _) =
      (basicOpenSectionsAdicCompletionIso hI f).hom := by
  rw [basicOpenSectionsIso, Iso.trans_hom, Category.assoc]
  refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  exact (AdicRing.CompletedAway.idealEquiv f I hI hIfg).apply_symm_apply _

/-- For an adic ring `A`, the global section of the structure sheaf of `Spf A` corresponding to
`a ∈ A` restricts on `D(f)` to the image of `a` in the completed localisation `A_{f}`. -/
@[reassoc (attr := simp)]
theorem globalSectionsIso_inv_comp_basicOpenSectionsIso_hom (hI : IsAdic I) (hIfg : I.FG)
    (f : A) :
    have := hI.isAdicComplete
    (globalSectionsIso hI).inv ≫
        (structureSheaf hI).obj.map (homOfLE (le_top : basicOpen f ≤ ⊤)).op ≫
          (basicOpenSectionsIso hI hIfg f).hom =
      CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A f)) := by
  intro
  rw [basicOpenSectionsIso, Iso.trans_hom,
    globalSectionsIso_inv_comp_basicOpenSectionsAdicCompletionIso_hom_assoc]
  ext a
  exact (AdicRing.CompletedAway.idealEquiv f I hI hIfg).symm.commutes a

/-- For an adic ring `A` and `D(g) ⊆ D(f)`, the restriction map of the structure sheaf of `Spf A`
from `D(f)` to `D(g)` is the restriction map `A_{f} → A_{g}` of completed localisations. -/
@[reassoc]
theorem map_comp_basicOpenSectionsIso_hom (hI : IsAdic I) (hIfg : I.FG) {f g : A}
    (h : basicOpen g ≤ basicOpen f) :
    (structureSheaf hI).obj.map (homOfLE h).op ≫ (basicOpenSectionsIso hI hIfg g).hom =
      (basicOpenSectionsIso hI hIfg f).hom ≫ CommRingCat.ofHom (AdicRing.CompletedAway.restrict
        ((basicOpen_le_basicOpen_iff (IsAdicRing.ideal_spec A).2.1).mp h) :
          AdicRing.CompletedAway A f →+* AdicRing.CompletedAway A g) := by
  have := hI.isAdicComplete
  have hfg := (basicOpen_le_basicOpen_iff (IsAdicRing.ideal_spec A).2.1).mp h
  rw [← Iso.inv_comp_eq]
  -- the transported restriction map fixes the image of `A`
  have hA : CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A f)) ≫
      (basicOpenSectionsIso hI hIfg f).inv ≫ (structureSheaf hI).obj.map (homOfLE h).op ≫
        (basicOpenSectionsIso hI hIfg g).hom =
      CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A g)) := by
    rw [← globalSectionsIso_inv_comp_basicOpenSectionsIso_hom hI hIfg f, Category.assoc,
      Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc]
    exact globalSectionsIso_inv_comp_basicOpenSectionsIso_hom hI hIfg g
  replace hA := congrArg CommRingCat.Hom.hom hA
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at hA
  ext1
  -- it is therefore continuous, and a continuous ring homomorphism out of `A_{f}` is determined
  -- by its values on `A`
  refine AdicRing.CompletedAway.ringHom_ext A f ?_ (AdicRing.CompletedAway.continuous_restrict hfg)
    (hA.trans (AdicRing.CompletedAway.restrict hfg).comp_algebraMap.symm)
  refine IsAdic.continuous_of_map_le_radical (AdicRing.CompletedAway.isAdic A f)
    (AdicRing.CompletedAway.isAdic A g) ((IsAdicRing.ideal_spec A).1.map _) ?_
  rw [Ideal.map_map, hA]
  exact Ideal.le_radical

end AdicRing

end TauCeti.FormalScheme.Spf

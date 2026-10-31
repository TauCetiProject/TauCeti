/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Limits
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Carrier
public import TauCeti.AlgebraicGeometry.StructureSheaf
public import TauCeti.RingTheory.AdicCompletion.Limit

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
* `TauCeti.FormalScheme.Spf.globalSectionsIso`: for `I`-adically complete `A`, the isomorphism
  of the global sections of `O_{Spf A}` with `A`.

## Main results

* `TauCeti.FormalScheme.Spf.quotientTransition_self`,
  `TauCeti.FormalScheme.Spf.quotientTransition_comp`: the reduction maps are functorial.
* `TauCeti.FormalScheme.Spf.quotientSheafGlobalSectionsIso_inv_comp_quotientTransition`: on
  global sections the reduction map `O_J → O_K` is the quotient map `A ⧸ J → A ⧸ K`.
* `TauCeti.FormalScheme.Spf.quotientProjection_comp_quotientTransition`: the projections are
  compatible with the reduction maps.
* `TauCeti.FormalScheme.Spf.structureSheaf.hom_ext`: morphisms into the structure sheaf are
  determined by their projections to the thickenings.
* `TauCeti.FormalScheme.Spf.globalSectionsIso_inv_comp_quotientProjection`: the global section
  corresponding to `a ∈ A` projects to the class of `a` in every `A ⧸ I ^ (n + 1)`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, §10.1
  (10.1.2, 10.1.3).
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

@[simp]
theorem coe_quotientInclusion_apply (hJ : IsAdic J) (q : PrimeSpectrum (A ⧸ J)) :
    (quotientInclusion hJ q : PrimeSpectrum A) = PrimeSpectrum.comap (Ideal.Quotient.mk J) q :=
  coe_homeomorphSpecQuotient_symm_apply hJ q

/-- For ideals of definition `J ≤ K`, the quotient inclusion of `Spec (A ⧸ K)` factors through
the closed immersion `Spec (A ⧸ K) → Spec (A ⧸ J)`. -/
theorem quotientInclusion_comap_factor (hJ : IsAdic J) (hK : IsAdic K) (hJK : J ≤ K)
    (q : PrimeSpectrum (A ⧸ K)) :
    quotientInclusion hJ (PrimeSpectrum.comap (Ideal.Quotient.factor hJK) q) =
      quotientInclusion hK q :=
  homeomorphSpecQuotient_symm_comap_factor hJ hK hJK q

/-- The structure sheaf of `Spec (A ⧸ J)`, for an ideal of definition `J`, transported to the
underlying space of `Spf A` along `quotientInclusion`. Its sections over an open `U` of `Spf A`
are the sections of the structure sheaf of `Spec (A ⧸ J)` over the corresponding open. -/
noncomputable def quotientSheaf (hJ : IsAdic J) :
    Sheaf (Opens.grothendieckTopology (TopCat.of (carrier A))) CommRingCat :=
  (TopCat.Sheaf.pushforward CommRingCat (quotientInclusion hJ)).obj (Spec.structureSheaf (A ⧸ J))

private theorem map_quotientInclusion_subset (hJ : IsAdic J) (hK : IsAdic K) (hJK : J ≤ K)
    (U : Opens (carrier A)) :
    ((Opens.map (quotientInclusion hK)).obj U).1 ⊆
      PrimeSpectrum.comap (Ideal.Quotient.factor hJK) ⁻¹'
        ((Opens.map (quotientInclusion hJ)).obj U).1 := by
  intro q hq
  simpa [quotientInclusion_comap_factor hJ hK hJK] using hq

/-- For ideals of definition `J ≤ K`, the reduction map `O_J → O_K` between the transported
structure sheaves, induced on sections by the quotient map `A ⧸ J → A ⧸ K`. -/
noncomputable def quotientTransition (hJ : IsAdic J) (hK : IsAdic K) (hJK : J ≤ K) :
    quotientSheaf hJ ⟶ quotientSheaf hK :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (StructureSheaf.comap (Ideal.Quotient.factor hJK) _ _
        (map_quotientInclusion_subset hJ hK hJK U.unop))
      naturality _ _ _ := CommRingCat.hom_ext <|
        (StructureSheaf.comap_comp_map _ _ _ _).trans (StructureSheaf.map_comp_comap _ _ _ _).symm }

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

/-- Morphisms into the structure sheaf of `Spf A` are determined by their projections to the
thickenings. -/
theorem structureSheaf.hom_ext (hI : IsAdic I)
    {F : Sheaf (Opens.grothendieckTopology (TopCat.of (carrier A))) CommRingCat}
    {f g : F ⟶ structureSheaf hI}
    (h : ∀ n, f ≫ quotientProjection hI n = g ≫ quotientProjection hI n) : f = g :=
  limit.hom_ext fun n ↦ h n.unop

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

end StructureSheaf

end TauCeti.FormalScheme.Spf

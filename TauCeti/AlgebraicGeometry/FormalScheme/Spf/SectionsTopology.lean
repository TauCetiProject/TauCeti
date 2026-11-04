/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Pi
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.IdealIndependence
public import TauCeti.RingTheory.AdicCompletion.InitialTopology

import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import TauCeti.Topology.Algebra.Ring.Basic
import TauCeti.Topology.Discrete

/-!
# The topology on rings of sections of the formal spectrum

Let `A` be a topological commutative ring whose topology is defined by an ideal `I`. The structure
sheaf `O_{Spf A}` (`TauCeti.FormalScheme.Spf.structureSheaf`) is the limit in sheaves of
commutative rings of the structure sheaves `O_{I ^ (n + 1)}` of the thickenings
`Spec (A ⧸ I ^ (n + 1))`. Its rings of sections carry a natural linear ring topology making `Spf A`
a topologically ringed space (EGA I, Ch. 0, §3.8.1 and Ch. I, §10.1.1–10.1.4):

* On a quasi-compact open `U`, `Γ(U, O_{Spf A})` carries the inverse-limit topology
  `TauCeti.FormalScheme.Spf.sectionsTopology` induced by the projections
  `Γ(U, O_{Spf A}) → Γ(U, O_{I ^ (n + 1)})` into the discrete rings `Γ(U, O_{I ^ (n + 1)})`.
* On an arbitrary open `U`, giving `Γ(U, O_{I ^ (n + 1)})` the discrete topology can produce a
  strictly finer topology that fails the topological sheaf gluing condition (for instance on a
  countably infinite disjoint union of points of a discrete product of fields; Stacks Tag 0AHY).
  Instead, `Γ(U, O_{Spf A})` carries the sheaf topology
  `TauCeti.FormalScheme.Spf.quotientSectionsTopology` (the limit of the pseudo-discrete sheaves
  attached to `O_{I ^ (n + 1)}`, EGA I, Ch. 0, 3.8.1): the initial topology for the restriction
  maps `Γ(U, O_{Spf A}) → Γ(D(f), O_{Spf A})` to the basic open subsets `D(f) ⊆ U`, each carrying
  `sectionsTopology`.

When `U` is quasi-compact, a finite cover by basic opens and the sheaf separatedness of each
thickening `O_{I ^ (n + 1)}` identify `quotientSectionsTopology` with `sectionsTopology`
(`quotientSectionsTopology_qc`). For every open `U`, `quotientSectionsTopology` makes
`Γ(U, O_{Spf A})` a complete Hausdorff linearly topologised ring, makes restriction maps
continuous (`quotientSectionsTopology_restrict`), embeds `Γ(U, O_{Spf A})` as a closed topological
subring of `∏ i, Γ(V i, O_{Spf A})` for every open cover `U = ⋃ i, V i`
(`quotientSectionsTopology_glue`), recovers the topology of `A` on global sections and of the
completed localisation `A_{f}` on `D(f)` (`isHomeomorph_globalSectionsIso`,
`quotientSectionsTopology_basic`), and does not depend on the chosen ideal of definition
(`quotientSectionsTopology_independent`).

## Main definitions

* `TauCeti.FormalScheme.Spf.sectionsTopology`: the initial topology on `Γ(U, O_{Spf A})` induced
  by the projections to the discrete rings `Γ(U, O_{I ^ (n + 1)})`.
* `TauCeti.FormalScheme.Spf.quotientSectionsTopology`: the sheaf topology on `Γ(U, O_{Spf A})`
  induced by the restrictions to basic opens `D(f) ⊆ U` carrying `sectionsTopology`.

## Main results

* `TauCeti.FormalScheme.Spf.sectionsTopology_isTopologicalRing`,
  `TauCeti.FormalScheme.Spf.sectionsTopology_isLinearTopology`,
  `TauCeti.FormalScheme.Spf.sectionsTopology_t2Space`,
  `TauCeti.FormalScheme.Spf.sectionsTopology_completeSpace`: `sectionsTopology` is a complete
  Hausdorff linear ring topology.
* `TauCeti.FormalScheme.Spf.quotientSectionsTopology_qc`: on a quasi-compact open `U`,
  `quotientSectionsTopology` agrees with `sectionsTopology`.
* `TauCeti.FormalScheme.Spf.quotientSectionsTopology_restrict`: every restriction map of
  `O_{Spf A}` is continuous for `quotientSectionsTopology`.
* `TauCeti.FormalScheme.Spf.quotientSectionsTopology_isTopologicalRing`,
  `TauCeti.FormalScheme.Spf.quotientSectionsTopology_isLinearTopology`,
  `TauCeti.FormalScheme.Spf.quotientSectionsTopology_t2Space`,
  `TauCeti.FormalScheme.Spf.quotientSectionsTopology_completeSpace`: `quotientSectionsTopology` is
  a complete Hausdorff linear ring topology on every open.
* `TauCeti.FormalScheme.Spf.quotientSectionsTopology_glue`: for every open cover `U = ⋃ i, V i`,
  the product of restrictions `Γ(U, O_{Spf A}) → ∏ i, Γ(V i, O_{Spf A})` is a closed embedding.
* `TauCeti.FormalScheme.Spf.isHomeomorph_globalSectionsIso`,
  `TauCeti.FormalScheme.Spf.quotientSectionsTopology_basic`: `globalSectionsIso` is a
  homeomorphism onto `A`, and `basicOpenSectionsIso` is a homeomorphism onto `CompletedAway A f`.
* `TauCeti.FormalScheme.Spf.quotientSectionsTopology_independent`,
  `TauCeti.FormalScheme.Spf.isHomeomorph_structureSheafIso`: `structureSheafIso hI hJ` is a
  homeomorphism on sections over every open `U`, and commutes with `basicOpenSectionsIso`
  (`TauCeti.FormalScheme.Spf.structureSheafIso_hom_app_basicOpen_comp_basicOpenSectionsIso_hom`).

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §3.8 (3.8.1–3.8.2)
  and Ch. I, §10.1 (10.1.1–10.1.4).
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

universe u

open CategoryTheory Limits TopologicalSpace Topology Filter Opposite

namespace TauCeti.FormalScheme.Spf

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {I J K : Ideal A}

section SectionsTopology

/-- On an open `U` of `Spf A`, `sectionsTopology hI U` is the initial topology on
`Γ(U, O_{Spf A})` induced by the projections `Γ(U, O_{Spf A}) → Γ(U, O_{I ^ (n + 1)})` into the
discrete section rings of the thickenings. On quasi-compact opens this agrees with the sheaf
topology `quotientSectionsTopology` (`quotientSectionsTopology_qc`; EGA I, Ch. I, 10.1.2). -/
@[instance_reducible]
noncomputable def sectionsTopology (hI : IsAdic I) (U : Opens (carrier A)) :
    TopologicalSpace ((structureSheaf hI).obj.obj (op U)) :=
  ⨅ n : ℕ, TopologicalSpace.induced ((quotientProjection hI n).hom.app (op U)) ⊥

/-- Each projection `Γ(U, O_{Spf A}) → Γ(U, O_{I ^ (n + 1)})` is continuous from
`sectionsTopology hI U` to the discrete topology. -/
theorem continuous_quotientProjection_app (hI : IsAdic I) (U : Opens (carrier A)) (n : ℕ) :
    @Continuous _ _ (sectionsTopology hI U) ⊥ ((quotientProjection hI n).hom.app (op U)) :=
  continuous_iInf_dom (i := n) (continuous_induced_dom (t := ⊥))

/-- For any ideal of definition `K`, the projection `Γ(U, O_{Spf A}) → Γ(U, O_K)` is continuous
from `sectionsTopology hI U` to the discrete topology. -/
theorem continuous_toQuotientSheaf_app (hI : IsAdic I) (hK : IsAdic K) (U : Opens (carrier A)) :
    @Continuous _ _ (sectionsTopology hI U) ⊥ ((toQuotientSheaf hI hK).hom.app (op U)) := by
  obtain ⟨n, hn⟩ := hI.exists_pow_succ_le (by simpa using hK.isOpen_pow 1)
  have hcomp : ((toQuotientSheaf hI hK).hom.app (op U) : _ → _) =
      ((quotientTransition _ hK hn).hom.app (op U)) ∘
        ((quotientProjection hI n).hom.app (op U)) := by
    rw [toQuotientSheaf_eq hI hK hn, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.coe_comp]
  rw [hcomp]
  exact @Continuous.comp _ _ _ (sectionsTopology hI U) ⊥ ⊥ _ _ continuous_bot
    (continuous_quotientProjection_app hI U n)

/-- Universal property of `sectionsTopology`: a map into `(Γ(U, O_{Spf A}), sectionsTopology hI U)`
is continuous if and only if its composites with all thickening projections are continuous into the
discrete topology. -/
theorem continuous_iff_sectionsTopology {X : Type*} [TopologicalSpace X] (hI : IsAdic I)
    (U : Opens (carrier A)) {g : X → (structureSheaf hI).obj.obj (op U)} :
    @Continuous _ _ _ (sectionsTopology hI U) g ↔
      ∀ n : ℕ, @Continuous _ _ _ ⊥ (((quotientProjection hI n).hom.app (op U)) ∘ g) := by
  rw [sectionsTopology, continuous_iInf_rng]
  exact forall_congr' fun _ ↦ continuous_induced_rng (t₂ := ⊥)

/-- The kernels of the projections `Γ(U, O_{Spf A}) → Γ(U, O_{I ^ (n + 1)})` form an antitone
sequence of ideals of `Γ(U, O_{Spf A})`. -/
private theorem antitone_ker_quotientProjection (hI : IsAdic I) (U : Opens (carrier A)) :
    Antitone fun n : ℕ ↦ RingHom.ker (((quotientProjection hI n).hom.app (op U)).hom) := by
  intro m n hmn x hx
  rw [RingHom.mem_ker] at hx ⊢
  have hcomp := congrArg (fun φ ↦ φ.hom.app (op U) x)
    (quotientProjection_comp_quotientTransition hI hmn).symm
  -- Unpack composition in `Sheaf` and `NatTrans` to apply `hx : ... x = 0`.
  change _ = ((quotientTransition _ _ _).hom.app (op U)).hom
    (((quotientProjection hI n).hom.app (op U)).hom x) at hcomp
  rw [hcomp, hx, map_zero]

/-- The kernels of the projections `Γ(U, O_{Spf A}) → Γ(U, O_{I ^ (n + 1)})` form a neighbourhood
basis of `0` in `sectionsTopology hI U`. -/
theorem sectionsTopology_hasBasis_nhds_zero (hI : IsAdic I) (U : Opens (carrier A)) :
    (@nhds _ (sectionsTopology hI U) 0).HasBasis (fun _ : ℕ ↦ True) fun n ↦
      (RingHom.ker (((quotientProjection hI n).hom.app (op U)).hom) : Set _) := by
  rw [sectionsTopology, nhds_iInf]
  have hnhds (n : ℕ) :
      @nhds _ (TopologicalSpace.induced ((quotientProjection hI n).hom.app (op U)) ⊥) 0 =
        𝓟 (RingHom.ker (((quotientProjection hI n).hom.app (op U)).hom) : Set _) := by
    rw [TauCeti.nhds_induced_bot]
    congr 1
    ext x
    simp [RingHom.mem_ker]
  simp only [hnhds]
  have hant : Antitone fun n : ℕ ↦
      (RingHom.ker (((quotientProjection hI n).hom.app (op U)).hom) :
        Set ((structureSheaf hI).obj.obj (op U))) := by
    intro m n h
    exact SetLike.coe_subset_coe.mpr (antitone_ker_quotientProjection hI U h)
  exact Filter.hasBasis_iInf_principal hant.directed_ge

/-- On every open `U`, `sectionsTopology hI U` makes `Γ(U, O_{Spf A})` a topological ring. -/
theorem sectionsTopology_isTopologicalRing (hI : IsAdic I) (U : Opens (carrier A)) :
    @IsTopologicalRing ((structureSheaf hI).obj.obj (op U)) (sectionsTopology hI U) _ := by
  refine TauCeti.isTopologicalRing_iInf fun n ↦ ?_
  let _ : TopologicalSpace ((quotientSheaf (is_ideal_adic_pow hI n.succ_pos)).obj.obj (op U)) := ⊥
  have := discreteTopology_bot ((quotientSheaf (is_ideal_adic_pow hI n.succ_pos)).obj.obj (op U))
  exact TauCeti.isTopologicalRing_induced (((quotientProjection hI n).hom.app (op U)).hom)

/-- On every open `U`, `sectionsTopology hI U` is a linear topology on `Γ(U, O_{Spf A})`. -/
theorem sectionsTopology_isLinearTopology (hI : IsAdic I) (U : Opens (carrier A)) :
    @IsLinearTopology ((structureSheaf hI).obj.obj (op U))
      ((structureSheaf hI).obj.obj (op U)) _ _ _ (sectionsTopology hI U) := by
  let _ := sectionsTopology hI U
  have := sectionsTopology_isTopologicalRing hI U
  exact IsLinearTopology.mk_of_hasBasis _ (sectionsTopology_hasBasis_nhds_zero hI U)

/-- On every open `U`, `sectionsTopology hI U` is Hausdorff. -/
theorem sectionsTopology_t2Space (hI : IsAdic I) (U : Opens (carrier A)) :
    @T2Space ((structureSheaf hI).obj.obj (op U)) (sectionsTopology hI U) := by
  let _ := sectionsTopology hI U
  refine ⟨fun x y hxy ↦ ?_⟩
  have hex : ∃ n : ℕ,
      (quotientProjection hI n).hom.app (op U) x ≠ (quotientProjection hI n).hom.app (op U) y := by
    by_contra! hall
    exact hxy (structureSheaf.sections_ext hI hall)
  obtain ⟨n, hn⟩ := hex
  let _ : TopologicalSpace ((quotientSheaf (is_ideal_adic_pow hI n.succ_pos)).obj.obj (op U)) := ⊥
  have := discreteTopology_bot ((quotientSheaf (is_ideal_adic_pow hI n.succ_pos)).obj.obj (op U))
  exact separated_by_continuous (continuous_quotientProjection_app hI U n) hn

/-- On every open `U`, `Γ(U, O_{Spf A})` is complete for every additive uniformity inducing
`sectionsTopology hI U`. -/
theorem sectionsTopology_completeSpace (hI : IsAdic I) (U : Opens (carrier A))
    [u : UniformSpace ((structureSheaf hI).obj.obj (op U))]
    [@IsUniformAddGroup ((structureSheaf hI).obj.obj (op U)) u _]
    (hu : u.toTopologicalSpace = sectionsTopology hI U) :
    CompleteSpace ((structureSheaf hI).obj.obj (op U)) := by
  let D (n : ℕ) := ((quotientSheaf (is_ideal_adic_pow hI n.succ_pos)).obj.obj (op U) : Type u)
  let _ (n : ℕ) : UniformSpace (D n) := ⊥
  let Φ : ((structureSheaf hI).obj.obj (op U) : Type u) →+ ∀ n : ℕ, D n :=
    AddMonoidHom.mk' (fun s n ↦ (quotientProjection hI n).hom.app (op U) s) fun s t ↦
      funext fun n ↦ map_add _ s t
  have hind : Topology.IsInducing Φ := by
    refine ⟨hu.trans ?_⟩
    rw [Pi.topologicalSpace, induced_iInf]
    exact iInf_congr fun n ↦ by
      rw [UniformSpace.toTopologicalSpace_bot, induced_compose]
      rfl
  have huind : IsUniformInducing Φ := AddMonoidHom.isUniformInducing_of_isInducing hind
  refine huind.completeSpace (IsClosed.isComplete ?_)
  have hrange : Set.range Φ = { y : ∀ n : ℕ, D n | ∀ ⦃m n : ℕ⦄ (h : m ≤ n),
      (quotientTransition (is_ideal_adic_pow hI n.succ_pos) (is_ideal_adic_pow hI m.succ_pos)
        (Ideal.pow_le_pow_right (Nat.succ_le_succ h))).hom.app (op U) (y n) = y m } := by
    ext y
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨s, rfl⟩ m n h
      exact congrArg (fun φ ↦ φ.hom.app (op U) s) (quotientProjection_comp_quotientTransition hI h)
    · exact ⟨structureSheaf.mkSection hI U y (fun h ↦ hy h),
        funext (structureSheaf.quotientProjection_mkSection hI U y _)⟩
  rw [hrange]
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun m ↦ isClosed_iInter fun n ↦ isClosed_iInter fun h ↦ ?_
  have hc1 : Continuous (fun y : ∀ k, D k ↦
      (quotientTransition _ _ (Ideal.pow_le_pow_right (Nat.succ_le_succ h))).hom.app
        (op U) (y n)) :=
    continuous_of_discreteTopology.comp (continuous_apply n)
  exact isClosed_eq hc1 (continuous_apply m)

/-- Restriction maps of `O_{Spf A}` are continuous for `sectionsTopology`. -/
theorem sectionsTopology_restrict (hI : IsAdic I) {U V : Opens (carrier A)} (h : V ≤ U) :
    @Continuous _ _ (sectionsTopology hI U) (sectionsTopology hI V)
      ((structureSheaf hI).obj.map (homOfLE h).op) := by
  let _ : TopologicalSpace ((structureSheaf hI).obj.obj (op U)) := sectionsTopology hI U
  rw [continuous_iff_sectionsTopology]
  intro n
  have hnat : ((quotientProjection hI n).hom.app (op V) : _ → _) ∘
      ((structureSheaf hI).obj.map (homOfLE h).op) =
      ((quotientSheaf (is_ideal_adic_pow hI n.succ_pos)).obj.map (homOfLE h).op) ∘
        ((quotientProjection hI n).hom.app (op U)) := by
    ext s
    exact NatTrans.naturality_apply (quotientProjection hI n).hom (homOfLE h).op s
  rw [hnat]
  exact @Continuous.comp _ _ _ (sectionsTopology hI U) ⊥ ⊥ _ _ continuous_bot
    (continuous_quotientProjection_app hI U n)

/-- For two ideals of definition `I` and `J`, the comparison map `(structureSheafIso hI hJ).hom`
is continuous for `sectionsTopology` over every open `U`. -/
theorem continuous_structureSheafIso_sectionsTopology (hI : IsAdic I) (hJ : IsAdic J)
    (U : Opens (carrier A)) :
    @Continuous _ _ (sectionsTopology hI U) (sectionsTopology hJ U)
      ((structureSheafIso hI hJ).hom.hom.app (op U)) := by
  let _ : TopologicalSpace ((structureSheaf hI).obj.obj (op U)) := sectionsTopology hI U
  rw [continuous_iff_sectionsTopology]
  intro n
  have hcomp : (((quotientProjection hJ n).hom.app (op U)) : _ → _) ∘
      ((structureSheafIso hI hJ).hom.hom.app (op U)) =
      ((toQuotientSheaf hI (is_ideal_adic_pow hJ n.succ_pos)).hom.app (op U)) := by
    rw [← structureSheafIso_hom_comp_quotientProjection hI hJ n,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.coe_comp]
  rw [hcomp]
  exact continuous_toQuotientSheaf_app hI (is_ideal_adic_pow hJ n.succ_pos) U

private noncomputable def structureSheafIsoApp (hI : IsAdic I) (hJ : IsAdic J)
    (U : Opens (carrier A)) :
    (structureSheaf hI).obj.obj (op U) ≅ (structureSheaf hJ).obj.obj (op U) where
  hom := (structureSheafIso hI hJ).hom.hom.app (op U)
  inv := (structureSheafIso hJ hI).hom.hom.app (op U)
  hom_inv_id := by
    rw [← structureSheafIso_inv hI hJ, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  inv_hom_id := by
    rw [← structureSheafIso_inv hJ hI, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]

private theorem isHomeomorph_structureSheafIso_of_continuous (hI : IsAdic I) (hJ : IsAdic J)
    (U : Opens (carrier A))
    {tI : TopologicalSpace ((structureSheaf hI).obj.obj (op U))}
    {tJ : TopologicalSpace ((structureSheaf hJ).obj.obj (op U))}
    (hIJ : @Continuous _ _ tI tJ ((structureSheafIso hI hJ).hom.hom.app (op U)))
    (hJI : @Continuous _ _ tJ tI ((structureSheafIso hJ hI).hom.hom.app (op U))) :
    @IsHomeomorph _ _ tI tJ ((structureSheafIso hI hJ).hom.hom.app (op U)) :=
  letI := tI; letI := tJ
  (Homeomorph.mk (structureSheafIsoApp hI hJ U).commRingCatIsoToRingEquiv.toEquiv hIJ
    hJI).isHomeomorph

/-- For two ideals of definition `I` and `J`, `(structureSheafIso hI hJ).hom` is a homeomorphism
on sections over every open `U` equipped with `sectionsTopology`. -/
theorem isHomeomorph_structureSheafIso_sectionsTopology (hI : IsAdic I) (hJ : IsAdic J)
    (U : Opens (carrier A)) :
    @IsHomeomorph _ _ (sectionsTopology hI U) (sectionsTopology hJ U)
      ((structureSheafIso hI hJ).hom.hom.app (op U)) :=
  isHomeomorph_structureSheafIso_of_continuous hI hJ U
    (continuous_structureSheafIso_sectionsTopology hI hJ U)
    (continuous_structureSheafIso_sectionsTopology hJ hI U)

/-- `sectionsTopology` is independent of the choice of ideal of definition: it pulls back across
`structureSheafIso hI hJ` on every open `U`. -/
theorem sectionsTopology_independent (hI : IsAdic I) (hJ : IsAdic J) (U : Opens (carrier A)) :
    sectionsTopology hI U =
      TopologicalSpace.induced ((structureSheafIso hI hJ).hom.hom.app (op U))
        (sectionsTopology hJ U) := by
  let _ := sectionsTopology hI U
  let _ := sectionsTopology hJ U
  exact (isHomeomorph_structureSheafIso_sectionsTopology hI hJ U).isInducing.eq_induced

/-- When the zero ideal defines the topology of `A` (that is, `A` is discrete),
`sectionsTopology` is the discrete topology on every open `U`. -/
theorem sectionsTopology_eq_bot_of_isAdic_bot (hI : IsAdic (⊥ : Ideal A)) (U : Opens (carrier A)) :
    sectionsTopology hI U = ⊥ := by
  refine eq_bot_iff.mpr ((iInf_le _ 0).trans ?_)
  have hinj : Function.Injective ((quotientProjection hI 0).hom.app (op U)) := by
    intro s t hst
    refine structureSheaf.sections_ext hI fun n ↦ ?_
    have heq : (⊥ : Ideal A) ^ (n + 1) = (⊥ : Ideal A) ^ (0 + 1) := by simp
    have hproj : quotientProjection hI n =
        quotientProjection hI 0 ≫ quotientTransition _ _ heq.ge := by
      rw [← quotientProjection_comp_quotientTransition hI (Nat.zero_le n)]
      have htr : quotientTransition (is_ideal_adic_pow hI n.succ_pos)
          (is_ideal_adic_pow hI Nat.one_pos) (Ideal.pow_le_pow_right (Nat.succ_le_succ
            (Nat.zero_le n))) ≫ quotientTransition _ _ heq.ge = 𝟙 _ := by
        rw [quotientTransition_comp, quotientTransition_self]
      rw [Category.assoc, htr, Category.comp_id]
    rw [hproj, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
    exact congrArg ((quotientTransition _ _ heq.ge).hom.app (op U)) hst
  exact (TauCeti.induced_bot_of_injective hinj).le

/-- When the zero ideal defines the topology of `A`, `sectionsTopology` is discrete on every open
`U`. -/
theorem discreteTopology_sectionsTopology_of_isAdic_bot (hI : IsAdic (⊥ : Ideal A))
    (U : Opens (carrier A)) :
    @DiscreteTopology ((structureSheaf hI).obj.obj (op U)) (sectionsTopology hI U) :=
  @DiscreteTopology.mk _ (sectionsTopology hI U) (sectionsTopology_eq_bot_of_isAdic_bot hI U)

/-- Over the empty open `⊥`, `sectionsTopology` is `⊥` (discrete). -/
@[simp]
theorem sectionsTopology_bot (hI : IsAdic I) :
    sectionsTopology hI (⊥ : Opens (carrier A)) = ⊥ := by
  let _ := sectionsTopology hI (⊥ : Opens (carrier A))
  exact DiscreteTopology.eq_bot

end SectionsTopology

section QuotientSectionsTopology

/-- On an arbitrary open `U` of `Spf A`, `quotientSectionsTopology hI U` is the sheaf topology on
`Γ(U, O_{Spf A})` (EGA I, Ch. 0, 3.8.1; Ch. I, 10.1.1): the initial topology for the restriction
maps `Γ(U, O_{Spf A}) → Γ(D(f), O_{Spf A})` over all basic open sets `D(f) ⊆ U`, where each
`Γ(D(f), O_{Spf A})` carries `sectionsTopology`. -/
@[instance_reducible]
noncomputable def quotientSectionsTopology (hI : IsAdic I) (U : Opens (carrier A)) :
    TopologicalSpace ((structureSheaf hI).obj.obj (op U)) :=
  ⨅ (f : A) (hf : basicOpen f ≤ U),
    TopologicalSpace.induced ((structureSheaf hI).obj.map (homOfLE hf).op)
      (sectionsTopology hI (basicOpen f))

/-- On every open `U`, `sectionsTopology hI U` is finer than or equal to
`quotientSectionsTopology hI U`. -/
theorem sectionsTopology_le_quotientSectionsTopology (hI : IsAdic I) (U : Opens (carrier A)) :
    sectionsTopology hI U ≤ quotientSectionsTopology hI U :=
  le_iInf₂ fun f hf ↦
    (continuous_iff_le_induced (t₁ := sectionsTopology hI U)
      (t₂ := sectionsTopology hI (basicOpen f))).mp (sectionsTopology_restrict hI hf)

/-- Core compactness lemma: if a quasi-compact open `U` of `Spf A` is covered by basic opens
`D(g) ⊆ U` with `g ∈ S`, then `sectionsTopology hI U` is the initial topology induced by the
restrictions to those `D(g)`. -/
private theorem sectionsTopology_eq_iInf_of_isCompact_cover (hI : IsAdic I)
    {U : Opens (carrier A)} (hU : IsCompact (U : Set (carrier A))) {S : Set A}
    (hS_le : ∀ g ∈ S, basicOpen g ≤ U)
    (hcov : (U : Set (carrier A)) ⊆ ⋃ g ∈ S, (basicOpen g : Set _)) :
    sectionsTopology hI U =
      ⨅ (g : A) (_ : g ∈ S),
        TopologicalSpace.induced ((structureSheaf hI).obj.map (homOfLE (hS_le g ‹_›)).op)
          (sectionsTopology hI (basicOpen g)) := by
  refine le_antisymm (le_iInf₂ fun g hg ↦ (continuous_iff_le_induced
    (t₁ := sectionsTopology hI U) (t₂ := sectionsTopology hI (basicOpen g))).mp
      (sectionsTopology_restrict hI (hS_le g hg))) ?_
  obtain ⟨F, hFS, hFfin, hFcov⟩ := hU.elim_finite_subcover_image
    (fun g _ ↦ (basicOpen g).isOpen) hcov
  have : Finite F := hFfin.to_subtype
  have hF_le (i : F) : basicOpen i.1 ≤ U := hS_le i.1 (Set.mem_of_subset_of_mem hFS i.2)
  refine le_iInf fun n ↦ ?_
  let _ : TopologicalSpace ((structureSheaf hI).obj.obj (op U)) :=
    ⨅ (g : A) (hg : g ∈ S),
      TopologicalSpace.induced ((structureSheaf hI).obj.map (homOfLE (hS_le g hg)).op)
        (sectionsTopology hI (basicOpen g))
  refine continuous_iff_le_induced.mp <| @IsLocallyConstant.continuous _ _ _ ⊥ _ <|
    (IsLocallyConstant.iff_eventually_eq _).mpr fun x ↦ ?_
  have hev : ∀ᶠ y in 𝓝 x, ∀ i : F,
      (quotientSheaf (is_ideal_adic_pow hI n.succ_pos)).obj.map (homOfLE (hF_le i)).op
        ((quotientProjection hI n).hom.app (op U) y) =
      (quotientSheaf (is_ideal_adic_pow hI n.succ_pos)).obj.map (homOfLE (hF_le i)).op
        ((quotientProjection hI n).hom.app (op U) x) := by
    refine Filter.eventually_all.mpr fun i ↦ ?_
    let _ : TopologicalSpace
      ((quotientSheaf (is_ideal_adic_pow hI n.succ_pos)).obj.obj (op (basicOpen i.1))) := ⊥
    have := discreteTopology_bot
      ((quotientSheaf (is_ideal_adic_pow hI n.succ_pos)).obj.obj (op (basicOpen i.1)))
    let _ := sectionsTopology hI (basicOpen i.1)
    have hcont : Continuous
        (((quotientProjection hI n).hom.app (op (basicOpen i.1))) ∘
          ((structureSheaf hI).obj.map (homOfLE (hF_le i)).op)) :=
      (continuous_quotientProjection_app hI (basicOpen i.1) n).comp
        (continuous_iInf_dom (i := i.1) <|
          continuous_iInf_dom (i := Set.mem_of_subset_of_mem hFS i.2) <|
            continuous_induced_dom (t := sectionsTopology hI (basicOpen i.1)))
    have hnat := NatTrans.naturality_apply (quotientProjection hI n).hom (homOfLE (hF_le i)).op
    exact (((IsLocallyConstant.iff_continuous _).mpr hcont).eventually_eq x).mono fun y hy ↦ by
      simpa only [Function.comp_apply, hnat] using hy
  refine hev.mono fun y hy ↦
    TopCat.Sheaf.eq_of_locally_eq' (quotientSheaf (is_ideal_adic_pow hI n.succ_pos))
      (fun i : F ↦ basicOpen i.1) U (fun i ↦ homOfLE (hF_le i)) ?_ _ _ hy
  intro p hp
  obtain ⟨g, hgF, hpg⟩ := Set.mem_iUnion₂.mp (hFcov hp)
  exact Opens.mem_iSup.mpr ⟨⟨g, hgF⟩, hpg⟩

/-- On a quasi-compact open `U` of `Spf A`, `quotientSectionsTopology` agrees with
`sectionsTopology`. -/
theorem quotientSectionsTopology_eq_of_isCompact (hI : IsAdic I) {U : Opens (carrier A)}
    (hU : IsCompact (U : Set (carrier A))) :
    quotientSectionsTopology hI U = sectionsTopology hI U := by
  symm
  refine sectionsTopology_eq_iInf_of_isCompact_cover hI hU (S := { f : A | basicOpen f ≤ U })
    (fun _ hf ↦ hf) fun p hp ↦ ?_
  obtain ⟨f, hpf, hfU⟩ := exists_basicOpen_le hp
  exact Set.mem_iUnion₂.mpr ⟨f, hfU, hpf⟩

/-- On a quasi-compact open `U` of `Spf A` (`[CompactSpace U]`), `quotientSectionsTopology` agrees
with `sectionsTopology` (EGA I, Ch. 0, 3.8.1; Ch. I, 10.1.2). -/
theorem quotientSectionsTopology_qc (hI : IsAdic I) (U : Opens (carrier A)) [CompactSpace U] :
    quotientSectionsTopology hI U = sectionsTopology hI U :=
  quotientSectionsTopology_eq_of_isCompact hI (isCompact_iff_compactSpace.mpr inferInstance)

/-- On every basic open `D(f)`, `quotientSectionsTopology` equals `sectionsTopology`. -/
@[simp]
theorem quotientSectionsTopology_basicOpen (hI : IsAdic I) (f : A) :
    quotientSectionsTopology hI (basicOpen f) = sectionsTopology hI (basicOpen f) :=
  quotientSectionsTopology_eq_of_isCompact hI (isCompact_basicOpen hI f)

/-- On `⊤ : Opens (carrier A)`, `quotientSectionsTopology` equals `sectionsTopology`. -/
@[simp]
theorem quotientSectionsTopology_top (hI : IsAdic I) :
    quotientSectionsTopology hI ⊤ = sectionsTopology hI ⊤ := by
  rw [← basicOpen_one, quotientSectionsTopology_basicOpen]

/-- Over the empty open `⊥`, `quotientSectionsTopology` is `⊥` (discrete). -/
@[simp]
theorem quotientSectionsTopology_bot (hI : IsAdic I) :
    quotientSectionsTopology hI (⊥ : Opens (carrier A)) = ⊥ := by
  rw [← basicOpen_zero, quotientSectionsTopology_basicOpen, basicOpen_zero, sectionsTopology_bot]

/-- Universal property of `quotientSectionsTopology`: a map into `Γ(U, O_{Spf A})` is continuous
for `quotientSectionsTopology hI U` if and only if its composites with the restrictions to all
basic opens `D(f) ⊆ U` are continuous into `sectionsTopology hI (basicOpen f)`. -/
theorem continuous_iff_quotientSectionsTopology {X : Type*} [TopologicalSpace X] (hI : IsAdic I)
    (U : Opens (carrier A)) {g : X → (structureSheaf hI).obj.obj (op U)} :
    @Continuous _ _ _ (quotientSectionsTopology hI U) g ↔
      ∀ (f : A) (hf : basicOpen f ≤ U),
        @Continuous _ _ _ (sectionsTopology hI (basicOpen f))
          (((structureSheaf hI).obj.map (homOfLE hf).op) ∘ g) := by
  rw [quotientSectionsTopology, continuous_iInf_rng]
  refine forall_congr' fun f ↦ ?_
  rw [continuous_iInf_rng]
  exact forall_congr' fun hf ↦
    continuous_induced_rng (t₂ := sectionsTopology hI (basicOpen f))

/-- Restriction maps of `O_{Spf A}` between arbitrary opens are continuous for
`quotientSectionsTopology`. -/
theorem quotientSectionsTopology_restrict (hI : IsAdic I) {U V : Opens (carrier A)} (h : V ≤ U) :
    @Continuous _ _ (quotientSectionsTopology hI U) (quotientSectionsTopology hI V)
      ((structureSheaf hI).obj.map (homOfLE h).op) := by
  let _ : TopologicalSpace ((structureSheaf hI).obj.obj (op U)) := quotientSectionsTopology hI U
  rw [continuous_iff_quotientSectionsTopology]
  intro f hf
  have hcomp : (((structureSheaf hI).obj.map (homOfLE hf).op) : _ → _) ∘
      ((structureSheaf hI).obj.map (homOfLE h).op) =
      ((structureSheaf hI).obj.map (homOfLE (hf.trans h)).op) := by
    ext s
    rw [Function.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      homOfLE_comp]
  rw [hcomp]
  exact continuous_iInf_dom (i := f) <| continuous_iInf_dom (i := hf.trans h) <|
    continuous_induced_dom (t := sectionsTopology hI (basicOpen f))

/-- On every open `U`, `quotientSectionsTopology hI U` makes `Γ(U, O_{Spf A})` a topological
ring. -/
theorem quotientSectionsTopology_isTopologicalRing (hI : IsAdic I) (U : Opens (carrier A)) :
    @IsTopologicalRing ((structureSheaf hI).obj.obj (op U)) (quotientSectionsTopology hI U) _ := by
  refine TauCeti.isTopologicalRing_iInf fun f ↦ TauCeti.isTopologicalRing_iInf fun hf ↦ ?_
  let _ := sectionsTopology hI (basicOpen f)
  have := sectionsTopology_isTopologicalRing hI (basicOpen f)
  exact TauCeti.isTopologicalRing_induced (((structureSheaf hI).obj.map (homOfLE hf).op).hom)

/-- On every open `U`, `quotientSectionsTopology hI U` is a linear topology on
`Γ(U, O_{Spf A})`: finite intersections of preimages of thickening kernels on basic opens form a
neighbourhood basis of `0` consisting of ideals. -/
theorem quotientSectionsTopology_isLinearTopology (hI : IsAdic I) (U : Opens (carrier A)) :
    @IsLinearTopology ((structureSheaf hI).obj.obj (op U))
      ((structureSheaf hI).obj.obj (op U)) _ _ _ (quotientSectionsTopology hI U) := by
  let _ := quotientSectionsTopology hI U
  have := quotientSectionsTopology_isTopologicalRing hI U
  let Idx := { f : A // basicOpen f ≤ U } × ℕ
  let J (q : Idx) : Ideal ((structureSheaf hI).obj.obj (op U)) :=
    (RingHom.ker (((quotientProjection hI q.2).hom.app (op (basicOpen q.1.1))).hom)).comap
      (((structureSheaf hI).obj.map (homOfLE q.1.2).op).hom)
  have heq : quotientSectionsTopology hI U =
      ⨅ q : Idx, TopologicalSpace.induced
        (((quotientProjection hI q.2).hom.app (op (basicOpen q.1.1))) ∘
          ((structureSheaf hI).obj.map (homOfLE q.1.2).op)) ⊥ := by
    simp only [Idx, quotientSectionsTopology, sectionsTopology, induced_iInf, induced_compose,
      iInf_prod, iInf_subtype]
  have hnhds : (𝓝 (0 : (structureSheaf hI).obj.obj (op U))).HasBasis
      (fun S : Set Idx ↦ S.Finite)
      fun S ↦ ((⨅ q ∈ S, J q : Ideal _) : Set _) := by
    -- Express `𝓝 0` directly via `quotientSectionsTopology` to rewrite by `heq`.
    change (@nhds _ (quotientSectionsTopology hI U) 0).HasBasis _ _
    rw [heq, nhds_iInf]
    have hq (q : Idx) :
        @nhds _ (TopologicalSpace.induced
          (((quotientProjection hI q.2).hom.app (op (basicOpen q.1.1))) ∘
            ((structureSheaf hI).obj.map (homOfLE q.1.2).op)) ⊥) 0 = 𝓟 (J q : Set _) := by
      rw [TauCeti.nhds_induced_bot]
      congr 1
      ext x
      simp [J, RingHom.mem_ker]
    simp only [hq]
    refine (Filter.hasBasis_iInf_principal_finite
      fun q : Idx ↦ (J q : Set ((structureSheaf hI).obj.obj (op U)))).congr
      (fun _ ↦ Iff.rfl) fun S _ ↦ ?_
    ext x
    simp
  exact IsLinearTopology.mk_of_hasBasis _ hnhds

/-- On every open `U`, `quotientSectionsTopology hI U` is Hausdorff. -/
theorem quotientSectionsTopology_t2Space (hI : IsAdic I) (U : Opens (carrier A)) :
    @T2Space ((structureSheaf hI).obj.obj (op U)) (quotientSectionsTopology hI U) := by
  let _ := quotientSectionsTopology hI U
  refine ⟨fun x y hxy ↦ ?_⟩
  have hex : ∃ (f : A) (hf : basicOpen f ≤ U),
      (structureSheaf hI).obj.map (homOfLE hf).op x ≠
        (structureSheaf hI).obj.map (homOfLE hf).op y := by
    by_contra! hall
    exact hxy <| TopCat.Sheaf.eq_of_locally_eq' (structureSheaf hI)
      (fun p : { f : A // basicOpen f ≤ U } ↦ basicOpen p.1) U (fun p ↦ homOfLE p.2)
      (le_iSup_basicOpen_le U) x y fun p ↦ hall p.1 p.2
  obtain ⟨f, hf, hne⟩ := hex
  let _ := sectionsTopology hI (basicOpen f)
  have := sectionsTopology_t2Space hI (basicOpen f)
  have hcont : @Continuous _ _ (quotientSectionsTopology hI U) (sectionsTopology hI (basicOpen f))
      ((structureSheaf hI).obj.map (homOfLE hf).op) :=
    quotientSectionsTopology_basicOpen hI f ▸ quotientSectionsTopology_restrict hI hf
  exact separated_by_continuous hcont hne

private theorem quotientSectionsTopology_isInducing_pi {ι : Type*} (hI : IsAdic I)
    {U : Opens (carrier A)} {V : ι → Opens (carrier A)} (hV : ∀ i, V i ≤ U)
    (hcov : U ≤ ⨆ i, V i) :
    @Topology.IsInducing ((structureSheaf hI).obj.obj (op U))
      (∀ i : ι, (structureSheaf hI).obj.obj (op (V i)))
      (quotientSectionsTopology hI U)
      (@Pi.topologicalSpace ι _ fun i ↦ quotientSectionsTopology hI (V i))
      (fun s i ↦ (structureSheaf hI).obj.map (homOfLE (hV i)).op s) := by
  let _ : TopologicalSpace ((structureSheaf hI).obj.obj (op U)) := quotientSectionsTopology hI U
  let _ (i : ι) : TopologicalSpace ((structureSheaf hI).obj.obj (op (V i))) :=
    quotientSectionsTopology hI (V i)
  let Φ := fun (s : (structureSheaf hI).obj.obj (op U)) (i : ι) ↦
    (structureSheaf hI).obj.map (homOfLE (hV i)).op s
  refine ⟨le_antisymm (continuous_iff_le_induced.mp (continuous_pi fun i ↦
    quotientSectionsTopology_restrict hI (hV i))) (le_iInf₂ fun f hf ↦ ?_)⟩
  have hS := sectionsTopology_eq_iInf_of_isCompact_cover hI (isCompact_basicOpen hI f)
    (S := { g : A | basicOpen g ≤ basicOpen f ∧ ∃ i : ι, basicOpen g ≤ V i })
    (fun _ hg ↦ hg.1) fun p hpf ↦ ?_
  · rw [hS, induced_iInf]
    refine le_iInf fun g ↦ ?_
    rw [induced_iInf]
    refine le_iInf fun ⟨hgf, i, hgi⟩ ↦ ?_
    rw [induced_compose]
    have hcomp : (((structureSheaf hI).obj.map (homOfLE hgf).op) : _ → _) ∘
        ((structureSheaf hI).obj.map (homOfLE hf).op) =
        ((structureSheaf hI).obj.map (homOfLE hgi).op) ∘
          (fun x : ∀ j : ι, (structureSheaf hI).obj.obj (op (V j)) ↦ x i) ∘ Φ := by
      ext s
      simp only [Φ, Function.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← op_comp, homOfLE_comp]
    rw [hcomp, ← induced_compose, ← induced_compose]
    refine induced_mono ?_
    rw [Pi.topologicalSpace]
    exact iInf_le_of_le i (induced_mono (iInf_le_of_le g (iInf_le _ hgi)))
  · obtain ⟨i, hpi⟩ := Opens.mem_iSup.mp (hcov (hf hpf))
    obtain ⟨g, hpg, hgW⟩ := exists_basicOpen_le (U := basicOpen f ⊓ V i) ⟨hpf, hpi⟩
    exact Set.mem_iUnion₂.mpr ⟨g, ⟨(le_inf_iff.mp hgW).1, i, (le_inf_iff.mp hgW).2⟩, hpg⟩

private theorem quotientSectionsTopology_isClosed_range_pi {ι : Type*} (hI : IsAdic I)
    {U : Opens (carrier A)} {V : ι → Opens (carrier A)} (hV : ∀ i, V i ≤ U)
    (hcov : U ≤ ⨆ i, V i) :
    @IsClosed (∀ i : ι, (structureSheaf hI).obj.obj (op (V i)))
      (@Pi.topologicalSpace ι _ fun i ↦ quotientSectionsTopology hI (V i))
      (Set.range fun (s : (structureSheaf hI).obj.obj (op U)) (i : ι) ↦
        (structureSheaf hI).obj.map (homOfLE (hV i)).op s) := by
  let _ (i : ι) : TopologicalSpace ((structureSheaf hI).obj.obj (op (V i))) :=
    quotientSectionsTopology hI (V i)
  let Φ := fun (s : (structureSheaf hI).obj.obj (op U)) (i : ι) ↦
    (structureSheaf hI).obj.map (homOfLE (hV i)).op s
  have hrange : Set.range Φ = { y : ∀ i : ι, (structureSheaf hI).obj.obj (op (V i)) |
      ∀ i j : ι,
        (structureSheaf hI).obj.map (homOfLE inf_le_left).op (y i) =
          (structureSheaf hI).obj.map (homOfLE inf_le_right).op (y j) } := by
    ext y
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨s, rfl⟩ i j
      simp only [Φ, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
    · obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (structureSheaf hI) V U
        (fun i ↦ homOfLE (hV i)) hcov y hy
      exact ⟨s, funext hs⟩
  rw [hrange]
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ ?_
  let _ : TopologicalSpace ((structureSheaf hI).obj.obj (op (V i ⊓ V j))) :=
    quotientSectionsTopology hI (V i ⊓ V j)
  have := quotientSectionsTopology_t2Space hI (V i ⊓ V j)
  have hc1 : Continuous (fun y : ∀ k : ι, (structureSheaf hI).obj.obj (op (V k)) ↦
      (structureSheaf hI).obj.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (y i)) :=
    (quotientSectionsTopology_restrict hI (inf_le_left : V i ⊓ V j ≤ V i)).comp
      (continuous_apply i)
  have hc2 : Continuous (fun y : ∀ k : ι, (structureSheaf hI).obj.obj (op (V k)) ↦
      (structureSheaf hI).obj.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (y j)) :=
    (quotientSectionsTopology_restrict hI (inf_le_right : V i ⊓ V j ≤ V j)).comp
      (continuous_apply j)
  exact isClosed_eq hc1 hc2

/-- For any open cover `U = ⋃ i, V i` of an open `U` of `Spf A`, the product of restriction maps
`Γ(U, O_{Spf A}) → ∏ i, Γ(V i, O_{Spf A})` is a closed topological embedding for
`quotientSectionsTopology` (EGA I, Ch. 0, 3.8.1). -/
theorem quotientSectionsTopology_glue {ι : Type*} (hI : IsAdic I) {U : Opens (carrier A)}
    {V : ι → Opens (carrier A)} (hV : ∀ i, V i ≤ U) (hcov : U ≤ ⨆ i, V i) :
    @Topology.IsClosedEmbedding ((structureSheaf hI).obj.obj (op U))
      (∀ i : ι, (structureSheaf hI).obj.obj (op (V i)))
      (quotientSectionsTopology hI U)
      (@Pi.topologicalSpace ι _ fun i ↦ quotientSectionsTopology hI (V i))
      (fun s i ↦ (structureSheaf hI).obj.map (homOfLE (hV i)).op s) := by
  let _ : TopologicalSpace ((structureSheaf hI).obj.obj (op U)) := quotientSectionsTopology hI U
  let _ (i : ι) : TopologicalSpace ((structureSheaf hI).obj.obj (op (V i))) :=
    quotientSectionsTopology hI (V i)
  exact ⟨⟨quotientSectionsTopology_isInducing_pi hI hV hcov, fun s t hst ↦
    TopCat.Sheaf.eq_of_locally_eq' (structureSheaf hI) V U (fun i ↦ homOfLE (hV i)) hcov s t
      (congrFun hst)⟩,
    quotientSectionsTopology_isClosed_range_pi hI hV hcov⟩

/-- On every open `U`, `Γ(U, O_{Spf A})` is complete for every additive uniformity inducing
`quotientSectionsTopology hI U`. -/
theorem quotientSectionsTopology_completeSpace (hI : IsAdic I) (U : Opens (carrier A))
    [u : UniformSpace ((structureSheaf hI).obj.obj (op U))]
    [@IsUniformAddGroup ((structureSheaf hI).obj.obj (op U)) u _]
    (hu : u.toTopologicalSpace = quotientSectionsTopology hI U) :
    CompleteSpace ((structureSheaf hI).obj.obj (op U)) := by
  let P := { f : A // basicOpen f ≤ U }
  let D (p : P) := ((structureSheaf hI).obj.obj (op (basicOpen p.1)) : Type u)
  let tD (p : P) : TopologicalSpace (D p) := quotientSectionsTopology hI (basicOpen p.1)
  have htr (p : P) : @IsTopologicalRing (D p) (tD p) _ :=
    quotientSectionsTopology_isTopologicalRing hI (basicOpen p.1)
  have htag (p : P) : @IsTopologicalAddGroup (D p) (tD p) _ := by
    let _ := tD p; have := htr p; exact inferInstance
  let _ (p : P) : UniformSpace (D p) :=
    let _ := tD p; have := htag p; IsTopologicalAddGroup.rightUniformSpace (D p)
  have _ (p : P) : IsUniformAddGroup (D p) := by
    let _ := tD p; have := htag p; exact isUniformAddGroup_of_addCommGroup
  have _ (p : P) : CompleteSpace (D p) :=
    sectionsTopology_completeSpace hI (basicOpen p.1) (quotientSectionsTopology_basicOpen hI p.1)
  obtain ⟨⟨⟨heq⟩, -⟩, hcl⟩ := quotientSectionsTopology_glue hI (V := fun p : P ↦ basicOpen p.1)
    (fun p ↦ p.2) (le_iSup_basicOpen_le U)
  let Φ : ((structureSheaf hI).obj.obj (op U) : Type u) →+ ∀ p : P, D p :=
    AddMonoidHom.mk' (fun s p ↦ (structureSheaf hI).obj.map (homOfLE p.2).op s) fun s t ↦
      funext fun p ↦ map_add _ s t
  have hind : Topology.IsInducing Φ := ⟨hu.trans heq⟩
  have huind : IsUniformInducing Φ := AddMonoidHom.isUniformInducing_of_isInducing hind
  exact huind.completeSpace hcl.isComplete

/-- For two ideals of definition `I` and `J`, `(structureSheafIso hI hJ).hom` is continuous on
sections over every open `U` equipped with `quotientSectionsTopology`. -/
theorem continuous_structureSheafIso (hI : IsAdic I) (hJ : IsAdic J) (U : Opens (carrier A)) :
    @Continuous _ _ (quotientSectionsTopology hI U) (quotientSectionsTopology hJ U)
      ((structureSheafIso hI hJ).hom.hom.app (op U)) := by
  let _ : TopologicalSpace ((structureSheaf hI).obj.obj (op U)) := quotientSectionsTopology hI U
  rw [continuous_iff_quotientSectionsTopology]
  intro f hf
  have hnat : (((structureSheaf hJ).obj.map (homOfLE hf).op) : _ → _) ∘
      ((structureSheafIso hI hJ).hom.hom.app (op U)) =
      ((structureSheafIso hI hJ).hom.hom.app (op (basicOpen f))) ∘
        ((structureSheaf hI).obj.map (homOfLE hf).op) := by
    ext s
    exact (NatTrans.naturality_apply (structureSheafIso hI hJ).hom.hom (homOfLE hf).op s).symm
  rw [hnat]
  have hres : @Continuous _ _ (quotientSectionsTopology hI U) (sectionsTopology hI (basicOpen f))
      ((structureSheaf hI).obj.map (homOfLE hf).op) :=
    quotientSectionsTopology_basicOpen hI f ▸ quotientSectionsTopology_restrict hI hf
  let _ : TopologicalSpace ((structureSheaf hI).obj.obj (op (basicOpen f))) :=
    sectionsTopology hI (basicOpen f)
  let _ : TopologicalSpace ((structureSheaf hJ).obj.obj (op (basicOpen f))) :=
    sectionsTopology hJ (basicOpen f)
  exact (continuous_structureSheafIso_sectionsTopology hI hJ (basicOpen f)).comp hres

/-- For two ideals of definition `I` and `J`, `(structureSheafIso hI hJ).hom` is a homeomorphism
on sections over every open `U` equipped with `quotientSectionsTopology`. -/
theorem isHomeomorph_structureSheafIso (hI : IsAdic I) (hJ : IsAdic J) (U : Opens (carrier A)) :
    @IsHomeomorph _ _ (quotientSectionsTopology hI U) (quotientSectionsTopology hJ U)
      ((structureSheafIso hI hJ).hom.hom.app (op U)) :=
  isHomeomorph_structureSheafIso_of_continuous hI hJ U
    (continuous_structureSheafIso hI hJ U) (continuous_structureSheafIso hJ hI U)

/-- `quotientSectionsTopology` is independent of the choice of ideal of definition: it pulls back
across `structureSheafIso hI hJ` on every open `U`. -/
theorem quotientSectionsTopology_independent (hI : IsAdic I) (hJ : IsAdic J)
    (U : Opens (carrier A)) :
    quotientSectionsTopology hI U =
      TopologicalSpace.induced ((structureSheafIso hI hJ).hom.hom.app (op U))
        (quotientSectionsTopology hJ U) := by
  let _ := quotientSectionsTopology hI U
  let _ := quotientSectionsTopology hJ U
  exact (isHomeomorph_structureSheafIso hI hJ U).isInducing.eq_induced

end QuotientSectionsTopology

section Identifications

/-- If `A` is `I`-adically complete, `globalSectionsIso hI` is a homeomorphism from
`(Γ(⊤, O_{Spf A}), quotientSectionsTopology hI ⊤)` onto `A` (EGA I, Ch. I, 10.1.3). -/
theorem isHomeomorph_globalSectionsIso [IsAdicComplete I A] (hI : IsAdic I) :
    @IsHomeomorph _ _ (quotientSectionsTopology hI ⊤) ‹TopologicalSpace A›
      ((globalSectionsIso hI).hom) := by
  rw [quotientSectionsTopology_top]
  let e := (globalSectionsIso hI).commRingCatIsoToRingEquiv.toEquiv
  have htop : sectionsTopology hI ⊤ = TopologicalSpace.induced e ‹TopologicalSpace A› := by
    refine Eq.symm ((congrArg (TopologicalSpace.induced e) hI.eq_iInf_induced).trans ?_)
    rw [sectionsTopology, induced_iInf]
    refine iInf_congr fun n ↦ ?_
    have hcomp : (Ideal.Quotient.mk (I ^ (n + 1)) : A → _) ∘ e =
        ((quotientSheafGlobalSectionsIso (is_ideal_adic_pow hI n.succ_pos)).hom) ∘
          ((quotientProjection hI n).hom.app (op ⊤)) := by
      have hhom : (globalSectionsIso hI).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))) =
          (quotientProjection hI n).hom.app (op ⊤) ≫
            (quotientSheafGlobalSectionsIso (is_ideal_adic_pow hI n.succ_pos)).hom := by
        rw [← cancel_epi (globalSectionsIso hI).inv, Iso.inv_hom_id_assoc,
          globalSectionsIso_inv_comp_quotientProjection_assoc, Iso.inv_hom_id, Category.comp_id]
      ext s
      exact congrArg (fun φ ↦ φ s) hhom
    have hbij : Function.Bijective
        ((quotientSheafGlobalSectionsIso (is_ideal_adic_pow hI n.succ_pos)).hom) :=
      ConcreteCategory.bijective_of_isIso _
    rw [induced_compose, hcomp, ← induced_compose, TauCeti.induced_bot_of_injective hbij.injective]
  let _ : TopologicalSpace ((structureSheaf hI).obj.obj (op ⊤)) := sectionsTopology hI ⊤
  exact (e.toHomeomorphOfIsInducing ⟨htop⟩).isHomeomorph

/-- For a finitely generated ideal of definition `I`, `basicOpenSectionsAdicCompletionIso hI f` is
a homeomorphism from `(Γ(D(f), O_{Spf A}), quotientSectionsTopology hI (basicOpen f))` onto
`AdicCompletion (I A_f) A_f` equipped with the adic topology of the extended ideal. -/
theorem isHomeomorph_basicOpenSectionsAdicCompletionIso (hI : IsAdic I) (hIfg : I.FG) (f : A) :
    @IsHomeomorph _ _ (quotientSectionsTopology hI (basicOpen f))
      (((I.map (algebraMap A (Localization.Away f))).map
        (algebraMap (Localization.Away f)
          (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
            (Localization.Away f)))).adicTopology)
      ((basicOpenSectionsAdicCompletionIso hI f).hom) := by
  rw [quotientSectionsTopology_basicOpen]
  set J := I.map (algebraMap A (Localization.Away f))
  let tAdic := (J.map (algebraMap (Localization.Away f)
    (AdicCompletion J (Localization.Away f)))).adicTopology
  let e := (basicOpenSectionsAdicCompletionIso hI f).commRingCatIsoToRingEquiv.toEquiv
  have htop : sectionsTopology hI (basicOpen f) = TopologicalSpace.induced e tAdic := by
    dsimp only [tAdic]
    rw [AdicCompletion.adicTopology_map_eq_iInf_induced (hIfg.map _), sectionsTopology,
      induced_iInf]
    refine iInf_congr fun n ↦ ?_
    let ψ := (quotientSheafBasicOpenIso (is_ideal_adic_pow hI n.succ_pos) f) ≪≫
      (Ideal.quotEquivOfEq (Ideal.map_pow _ I (n + 1))).toCommRingCatIso
    have hcomp : (AdicCompletion.evalₐ J (n + 1) : _ → _) ∘ e =
        (ψ.hom : _ → _) ∘ ((quotientProjection hI n).hom.app (op (basicOpen f))) := by
      ext s
      exact congrArg (fun φ ↦ φ s) (basicOpenSectionsAdicCompletionIso_hom_comp_evalₐ hI f n)
    have hbij : Function.Bijective ψ.hom := ConcreteCategory.bijective_of_isIso ψ.hom
    rw [induced_compose, hcomp, ← induced_compose, TauCeti.induced_bot_of_injective hbij.injective]
  let _ : TopologicalSpace ((structureSheaf hI).obj.obj (op (basicOpen f))) :=
    sectionsTopology hI (basicOpen f)
  let _ : TopologicalSpace (AdicCompletion J (Localization.Away f)) := tAdic
  exact (e.toHomeomorphOfIsInducing ⟨htop⟩).isHomeomorph

/-- For an adic ring `A` of finite ideal type and a finitely generated ideal of definition `I`,
`basicOpenSectionsIso hI hIfg f` is a homeomorphism from
`(Γ(D(f), O_{Spf A}), quotientSectionsTopology hI (basicOpen f))` onto the completed localisation
`CompletedAway A f` with its canonical adic topology (EGA I, Ch. I, 10.1.4). -/
theorem quotientSectionsTopology_basic [IsAdicRing A] (hI : IsAdic I) (hIfg : I.FG) (f : A) :
    @IsHomeomorph _ _ (quotientSectionsTopology hI (basicOpen f)) inferInstance
      ((basicOpenSectionsIso hI hIfg f).hom) := by
  let _ : TopologicalSpace
      (AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f)) :=
    ((I.map (algebraMap A (Localization.Away f))).map
      (algebraMap (Localization.Away f)
        (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
          (Localization.Away f)))).adicTopology
  let _ : TopologicalSpace ((structureSheaf hI).obj.obj (op (basicOpen f))) :=
    quotientSectionsTopology hI (basicOpen f)
  have h1 := isHomeomorph_basicOpenSectionsAdicCompletionIso hI hIfg f
  have h2 := (AdicRing.CompletedAway.idealEquiv f I hI hIfg).toEquiv.isHomeomorph_iff.mp
    (AdicRing.CompletedAway.isHomeomorph_idealEquiv f I hI hIfg)
  let hsymm := (Homeomorph.mk (AdicRing.CompletedAway.idealEquiv f I hI hIfg).toEquiv
    h2.1 h2.2).symm.isHomeomorph
  have hfun : ((basicOpenSectionsIso hI hIfg f).hom : _ → _) =
      (AdicRing.CompletedAway.idealEquiv f I hI hIfg).symm ∘
        ((basicOpenSectionsAdicCompletionIso hI f).hom) := by
    ext s
    exact (AdicRing.CompletedAway.idealEquiv f I hI hIfg).eq_symm_apply.mpr <|
      (congrArg (fun φ ↦ φ s) (basicOpenSectionsIso_hom_comp_idealEquiv hI hIfg f))
  rw [hfun]
  exact hsymm.comp h1

/-- For an adic ring `A` and two finitely generated ideals of definition `I` and `J`, the
ideal-independence isomorphism `structureSheafIso hI hJ` commutes on every basic open `D(f)` with
the identifications `basicOpenSectionsIso` of sections with `CompletedAway A f`. -/
@[reassoc (attr := simp)]
theorem structureSheafIso_hom_app_basicOpen_comp_basicOpenSectionsIso_hom [IsAdicRing A]
    (hI : IsAdic I) (hIfg : I.FG) (hJ : IsAdic J) (hJfg : J.FG) (f : A) :
    (structureSheafIso hI hJ).hom.hom.app (op (basicOpen f)) ≫
        (basicOpenSectionsIso hJ hJfg f).hom =
      (basicOpenSectionsIso hI hIfg f).hom := by
  have := hI.isAdicComplete
  have := hJ.isAdicComplete
  rw [← cancel_epi (basicOpenSectionsIso hI hIfg f).inv, Iso.inv_hom_id]
  have hA : CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A f)) ≫
      (basicOpenSectionsIso hI hIfg f).inv ≫
        (structureSheafIso hI hJ).hom.hom.app (op (basicOpen f)) ≫
          (basicOpenSectionsIso hJ hJfg f).hom =
      CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A f)) := by
    nth_rw 1 [← globalSectionsIso_inv_comp_basicOpenSectionsIso_hom hI hIfg f]
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
    have hnat := (structureSheafIso hI hJ).hom.hom.naturality
      (homOfLE (le_top : basicOpen f ≤ ⊤)).op
    rw [reassoc_of% hnat, globalSectionsIso_inv_comp_structureSheafIso_hom_assoc hI hJ,
      globalSectionsIso_inv_comp_basicOpenSectionsIso_hom]
  ext1
  let _ : TopologicalSpace ((structureSheaf hI).obj.obj (op (basicOpen f))) :=
    quotientSectionsTopology hI (basicOpen f)
  let _ : TopologicalSpace ((structureSheaf hJ).obj.obj (op (basicOpen f))) :=
    quotientSectionsTopology hJ (basicOpen f)
  have hc1 : Continuous ((basicOpenSectionsIso hI hIfg f).inv) := by
    have hh := ((basicOpenSectionsIso hI hIfg f).commRingCatIsoToRingEquiv.toEquiv
      ).isHomeomorph_iff.mp (quotientSectionsTopology_basic hI hIfg f)
    exact hh.2
  have hc2 : Continuous ((structureSheafIso hI hJ).hom.hom.app (op (basicOpen f))) :=
    continuous_structureSheafIso hI hJ (basicOpen f)
  have hc3 : Continuous ((basicOpenSectionsIso hJ hJfg f).hom) :=
    (quotientSectionsTopology_basic hJ hJfg f).continuous
  refine AdicRing.CompletedAway.ringHom_ext A f (hc3.comp (hc2.comp hc1)) continuous_id ?_
  have hA' := congrArg CommRingCat.Hom.hom hA
  simpa using hA'

end Identifications

end TauCeti.FormalScheme.Spf

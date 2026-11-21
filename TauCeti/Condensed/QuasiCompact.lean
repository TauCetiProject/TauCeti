/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.Condensed.Functors
public import Mathlib.Condensed.TopComparison

import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.Condensed.EffectiveEpi
import Mathlib.Condensed.Epi
import Mathlib.Topology.Category.Stonean.Basic

/-!
# Quasicompact and quasiseparated condensed sets

Quasicompact condensed sets admit a profinite epimorphic cover. Relative quasicompactness
can be tested over any quasicompact source, not just a representable one. In particular,
quasiseparatedness is equivalent to quasicompactness of the fibre products of pairs of profinite
test objects, the form used when cutting out a subfunctor by equations.

The definitions follow Paškūnas and Quast, *On local Galois deformation rings: generalised
reductive groups*, Appendix A.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CondensedSet

/-- A condensed set is quasicompact if it admits a profinite epimorphic cover. -/
def QuasiCompact (X : CondensedSet.{u}) : Prop :=
  ∃ (S : Profinite.{u}) (f : S.toCondensed ⟶ X), Epi f

/-- A map is quasicompact if its pullbacks to profinite test objects are quasicompact. -/
def QuasiCompactMap {X Y : CondensedSet.{u}} (f : X ⟶ Y) : Prop :=
  ∀ ⦃S : Profinite.{u}⦄ (g : S.toCondensed ⟶ Y), QuasiCompact (pullback f g)

/-- A condensed set is quasiseparated if its diagonal is a quasicompact map. -/
def QuasiSeparated (X : CondensedSet.{u}) : Prop :=
  QuasiCompactMap (pullback.diagonal (terminal.from X))

/-- A condensed set is qcqs if it is both quasicompact and quasiseparated. -/
def QuasiCompactQuasiSeparated (X : CondensedSet.{u}) : Prop :=
  X.QuasiCompact ∧ X.QuasiSeparated

/-- Quasicompactness is witnessed by a profinite epimorphic cover. -/
theorem quasiCompact_iff (X : CondensedSet.{u}) : X.QuasiCompact ↔
    ∃ (S : Profinite.{u}) (f : S.toCondensed ⟶ X), Epi f := (Iff.rfl)

/-- Relative quasicompactness is tested by base change to profinite spaces. -/
theorem quasiCompactMap_iff {X Y : CondensedSet.{u}} (f : X ⟶ Y) : QuasiCompactMap f ↔
    ∀ ⦃S : Profinite.{u}⦄ (g : S.toCondensed ⟶ Y), (pullback f g).QuasiCompact := (Iff.rfl)

/-- Quasiseparatedness is relative quasicompactness of the diagonal. -/
theorem quasiSeparated_iff_quasiCompactMap_diagonal (X : CondensedSet.{u}) :
    X.QuasiSeparated ↔ QuasiCompactMap (pullback.diagonal (terminal.from X)) := (Iff.rfl)

/-- The qcqs condition is the conjunction of the two separate conditions. -/
theorem quasiCompactQuasiSeparated_iff (X : CondensedSet.{u}) :
    X.QuasiCompactQuasiSeparated ↔ X.QuasiCompact ∧ X.QuasiSeparated := (Iff.rfl)

/-- The image of a quasicompact condensed set under an epimorphism is quasicompact. -/
theorem QuasiCompact.of_epi {X Y : CondensedSet.{u}} (hX : X.QuasiCompact)
    (f : X ⟶ Y) [Epi f] : Y.QuasiCompact := by
  obtain ⟨S, p, hp⟩ := hX
  exact ⟨S, p ≫ f, inferInstance⟩

/-- Quasicompactness is invariant under isomorphism. -/
theorem quasiCompact_iff_of_iso {X Y : CondensedSet.{u}} (e : X ≅ Y) :
    X.QuasiCompact ↔ Y.QuasiCompact :=
  ⟨fun h ↦ h.of_epi e.hom, fun h ↦ h.of_epi e.inv⟩

/-- Compact Hausdorff spaces give quasicompact condensed sets, via their Stonean covers. -/
@[simp]
theorem quasiCompact_toCondensed_compHaus (S : CompHaus.{u}) : S.toCondensed.QuasiCompact := by
  have hπ : Epi (CompHaus.presentation.π S) := CompHaus.presentation.epi_π S
  exact ⟨Stonean.toProfinite.obj S.presentation,
    compHausToCondensed.map (CompHaus.presentation.π S),
    @Functor.map_epi _ _ _ _ compHausToCondensed _ _ _ (CompHaus.presentation.π S) hπ⟩

/-- Profinite spaces give quasicompact condensed sets. -/
@[simp]
theorem quasiCompact_toCondensed (S : Profinite.{u}) : S.toCondensed.QuasiCompact :=
  ⟨S, 𝟙 _, inferInstance⟩

/-- Pulling back a condensed-set epimorphism gives an epimorphism: on Stonean test objects,
sections lift along the base-change projection. -/
theorem epi_pullback_fst {X Y Z : CondensedSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Epi g] : Epi (pullback.fst f g) := by
  rw [epi_iff_surjective_on_stonean]
  intro S x
  let J := coherentTopology CompHaus.{u}
  let a := J.uliftYonedaEquiv.{u + 1}.symm x
  obtain ⟨y, hy⟩ := (epi_iff_surjective_on_stonean g).mp inferInstance S (f.hom.app _ x)
  let b := J.uliftYonedaEquiv.{u + 1}.symm y
  have hab : a ≫ f = b ≫ g := J.uliftYonedaEquiv.injective (by
    simpa only [GrothendieckTopology.uliftYonedaEquiv_comp, Equiv.apply_symm_apply, a, b]
      using hy.symm)
  refine ⟨J.uliftYonedaEquiv (pullback.lift a b hab), ?_⟩
  simpa only [GrothendieckTopology.uliftYonedaEquiv_comp, a, Equiv.apply_symm_apply] using
    congrArg J.uliftYonedaEquiv (pullback.lift_fst a b hab)

/-- To test relative quasicompactness, one can allow any quasicompact base-change object. -/
theorem QuasiCompactMap.pullback {X Y T : CondensedSet.{u}} {f : X ⟶ Y}
    (hf : QuasiCompactMap f) (g : T ⟶ Y) (hT : T.QuasiCompact) :
    (pullback f g).QuasiCompact := by
  obtain ⟨S, p, hp⟩ := hT
  let : Epi (pullback.fst (pullback.snd f g) p) := epi_pullback_fst _ _
  exact (hf (p ≫ g)).of_epi
    ((pullbackLeftPullbackSndIso f g p).inv ≫ pullback.fst _ _)

/-- Relative quasicompactness is preserved by pullback. -/
theorem QuasiCompactMap.baseChange {X Y T : CondensedSet.{u}} {f : X ⟶ Y}
    (hf : QuasiCompactMap f) (g : T ⟶ Y) : QuasiCompactMap (pullback.snd f g) := by
  intro S p
  exact (quasiCompact_iff_of_iso (pullbackLeftPullbackSndIso f g p)).mpr (hf (p ≫ g))

/-- Isomorphisms are quasicompact maps. -/
@[simp]
theorem quasiCompactMap_of_isIso {X Y : CondensedSet.{u}} (f : X ⟶ Y) [IsIso f] :
    QuasiCompactMap f := fun {S} g ↦
  (quasiCompact_iff_of_iso (asIso (pullback.snd f g))).mpr (quasiCompact_toCondensed S)

/-- The composite of quasicompact maps is quasicompact. -/
theorem QuasiCompactMap.comp {X Y Z : CondensedSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : QuasiCompactMap f) (hg : QuasiCompactMap g) : QuasiCompactMap (f ≫ g) := by
  intro S p
  exact (quasiCompact_iff_of_iso (pullbackRightPullbackFstIso g p f)).mp
    (hf.pullback (pullback.fst g p) (hg p))

/-- Maps between representable compact Hausdorff condensed sets are quasicompact. -/
@[simp]
theorem quasiCompactMap_compHausToCondensed_map {S T : CompHaus.{u}} (f : S ⟶ T) :
    QuasiCompactMap (compHausToCondensed.map f) := by
  intro P g
  let G := compHausToCondensed.{u}
  let g' : profiniteToCompHaus.obj P ⟶ T := G.preimage g
  have hg : G.map g' = g := G.map_preimage g
  rw [← hg]
  let : PreservesLimit (cospan f g') G :=
    inferInstanceAs (PreservesLimit (cospan f g') ((coherentTopology CompHaus).uliftYoneda))
  exact (quasiCompact_iff_of_iso (PreservesPullback.iso G f g')).mp
    (quasiCompact_toCondensed_compHaus _)

/-- The product of the condensed sets represented by two compact Hausdorff spaces
is represented by their product. -/
private noncomputable def compHausPullbackOverTerminalIso {X : CondensedSet.{u}}
    {S T : CompHaus.{u}} (f : S.toCondensed ⟶ X) (g : T.toCondensed ⟶ X) :
    pullback (f ≫ terminal.from X) (g ≫ terminal.from X) ≅ (Limits.prod S T).toCondensed :=
  pullback.congrHom (terminal.hom_ext _ _) (terminal.hom_ext _ _) ≪≫
    (prodIsoPullback S.toCondensed T.toCondensed).symm ≪≫
    (PreservesLimitPair.iso ((coherentTopology CompHaus).uliftYoneda) S T).symm

/-- Quasiseparatedness can be tested by fibre products of two profinite objects. -/
theorem quasiSeparated_iff {X : CondensedSet.{u}} : X.QuasiSeparated ↔
    ∀ ⦃S T : Profinite.{u}⦄ (f : S.toCondensed ⟶ X) (g : T.toCondensed ⟶ X),
      QuasiCompact (pullback f g) := by
  constructor
  · intro h S T f g
    let t := terminal.from X
    have hc := (quasiCompact_iff_of_iso (compHausPullbackOverTerminalIso f g)).mpr
      (quasiCompact_toCondensed_compHaus _)
    exact (quasiCompact_iff_of_iso (pullbackDiagonalMapIdIso f g t)).mp
      (QuasiCompactMap.pullback h _ hc)
  · intro h S p
    -- Factor the pair of maps from S through the diagonal of S in the product of the tests.
    let t := terminal.from X
    let f := p ≫ pullback.fst t t
    let g := p ≫ pullback.snd t t
    let q : pullback (f ≫ t) (g ≫ t) ⟶ pullback t t :=
      pullback.map _ _ t t f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)
    let d : S.toCondensed ⟶ pullback (f ≫ t) (g ≫ t) :=
      pullback.lift (𝟙 _) (𝟙 _) (terminal.hom_ext _ _)
    have hdq : d ≫ q = p := by
      apply pullback.hom_ext <;> simp [d, q, f, g]
    let e := compHausPullbackOverTerminalIso f g
    have hd : QuasiCompactMap d := by
      let k := compHausToCondensed.preimage (d ≫ e.hom)
      have hk : compHausToCondensed.map k = d ≫ e.hom := compHausToCondensed.map_preimage _
      have he : (d ≫ e.hom) ≫ e.inv = d :=
        (Category.assoc ..).trans ((congrArg (d ≫ ·) e.hom_inv_id).trans (Category.comp_id d))
      exact (congrArg (fun m ↦ QuasiCompactMap m)
        ((congrArg (· ≫ e.inv) hk).trans he)) ▸
          (quasiCompactMap_compHausToCondensed_map k).comp (quasiCompactMap_of_isIso e.inv)
    have hc := (quasiCompact_iff_of_iso (pullbackDiagonalMapIdIso f g t)).mpr (h f g)
    have hpb := hd.pullback (pullback.snd (pullback.diagonal t) q) hc
    exact (quasiCompact_iff_of_iso ((pullbackSymmetry _ _) ≪≫
      pullbackLeftPullbackSndIso (pullback.diagonal t) q d ≪≫ pullback.congrHom rfl hdq)).mp hpb

/-- A condensed subobject of a quasiseparated condensed set is quasiseparated. -/
theorem QuasiSeparated.of_mono {X Y : CondensedSet.{u}} (hY : Y.QuasiSeparated)
    (i : X ⟶ Y) [Mono i] : X.QuasiSeparated := by
  rw [quasiSeparated_iff] at hY ⊢
  intro S T f g
  let h := pullbackIsPullbackOfCompMono f g i
  exact (hY (f ≫ i) (g ≫ i)).of_epi
    (h.conePointUniqueUpToIso (pullback.isLimit _ _)).inv

/-- Compact Hausdorff spaces give quasiseparated condensed sets. -/
@[simp]
theorem quasiSeparated_toCondensed_compHaus (S : CompHaus.{u}) : S.toCondensed.QuasiSeparated := by
  rw [quasiSeparated_iff]
  intro P Q f g
  let G := compHausToCondensed.{u}
  let f' : profiniteToCompHaus.obj P ⟶ S := G.preimage f
  have hf : G.map f' = f := G.map_preimage f
  rw [← hf]
  exact quasiCompactMap_compHausToCondensed_map f' g

/-- Profinite spaces give qcqs condensed sets, including the empty and singleton spaces. -/
@[simp]
theorem quasiCompactQuasiSeparated_toCondensed (S : Profinite.{u}) :
    S.toCondensed.QuasiCompactQuasiSeparated :=
  ⟨quasiCompact_toCondensed S, quasiSeparated_toCondensed_compHaus (profiniteToCompHaus.obj S)⟩

/-- A quasicompact condensed set is quasicompact over the point, and conversely. -/
@[simp]
theorem quasiCompactMap_terminal_from_iff (X : CondensedSet.{u}) :
    QuasiCompactMap (terminal.from X) ↔ X.QuasiCompact := by
  let G := (coherentTopology CompHaus.{u}).uliftYoneda.{u + 1}
  constructor
  · intro h
    let S := Profinite.of PUnit.{u + 1}
    let hS : IsTerminal S.toCondensed := CompHaus.isTerminalPUnit.isTerminalObj G
    have hfrom : terminal.from S.toCondensed = (hS.uniqueUpToIso terminalIsTerminal).hom :=
      terminal.hom_ext _ _
    let : IsIso (terminal.from S.toCondensed) := hfrom ▸ inferInstance
    exact (h (S := S) (terminal.from _)).of_epi (pullback.fst _ _)
  · intro h S g
    obtain ⟨P, p, hp⟩ := h
    let t := terminal.from X
    have hPS : (pullback (p ≫ t) g).QuasiCompact := by
      let f := p ≫ t
      exact (quasiCompact_iff_of_iso (pullback.congrHom (terminal.hom_ext f _)
        (terminal.hom_ext g _) ≪≫ compHausPullbackOverTerminalIso f g)).mpr
          (quasiCompact_toCondensed_compHaus _)
    let : Epi (pullback.fst (pullback.fst t g) p) := epi_pullback_fst _ _
    exact hPS.of_epi ((pullbackRightPullbackFstIso t g p).inv ≫ (pullbackSymmetry _ _).hom ≫
      pullback.fst (pullback.fst t g) p)

end CondensedSet

namespace TopCat

open CondensedSet

/-- Over a Hausdorff space, the fibre product of two representable condensed sets is
represented by the closed coincidence locus in the product of the two test spaces. -/
theorem exists_compHaus_iso_pullback_toCondensedSet (X : TopCat.{u + 1}) [T2Space X]
    {S T : CompHaus.{u}} (f : S.toCondensed ⟶ X.toCondensedSet)
    (g : T.toCondensed ⟶ X.toCondensedSet) :
    ∃ L : CompHaus.{u}, Nonempty (L.toCondensed ≅ pullback f g) := by
  let J := coherentTopology CompHaus.{u}
  let a : C(S, X) := J.uliftYonedaEquiv.{u + 1} f
  let b : C(T, X) := J.uliftYonedaEquiv.{u + 1} g
  let K : Set (S × T) := {x | a x.1 = b x.2}
  have hK : IsClosed K := isClosed_eq (a.continuous.comp continuous_fst)
    (b.continuous.comp continuous_snd)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  let L := CompHaus.of K
  let p : L ⟶ S := CompHausLike.ofHom _ ⟨fun k ↦ k.val.1, by fun_prop⟩
  let q : L ⟶ T := CompHausLike.ofHom _ ⟨fun k ↦ k.val.2, by fun_prop⟩
  let F := J.uliftYoneda.{u + 1}
  have comm : F.map p ≫ f = F.map q ≫ g := by
    apply J.uliftYonedaEquiv.{u + 1}.injective
    exact (J.uliftYonedaEquiv_naturality.{u + 1} f p).symm.trans
      ((ContinuousMap.ext fun k : L ↦ k.property).trans
        (J.uliftYonedaEquiv_naturality.{u + 1} g q))
  let c := PullbackCone.mk _ _ comm
  have hc : IsLimit c := by
    let U := sheafToPresheaf J (Type (u + 1))
    apply isLimitOfReflects U
    apply evaluationJointlyReflectsLimits
    intro R
    let E := U ⋙ ((evaluation _ _).obj R)
    refine (c.isLimitMapConeEquiv E).symm ?_
    refine (PullbackCone.isLimitEquivBijective _).symm ?_
    constructor
    · intro x y h
      have h₁ : (x.down : R.unop ⟶ L) ≫ p = (y.down : R.unop ⟶ L) ≫ p :=
        congrArg (fun z ↦ z.val.1.down) h
      have h₂ : (x.down : R.unop ⟶ L) ≫ q = (y.down : R.unop ⟶ L) ≫ q :=
        congrArg (fun z ↦ z.val.2.down) h
      have hxy : (x.down : R.unop ⟶ L) = (y.down : R.unop ⟶ L) :=
        ConcreteCategory.ext (ContinuousMap.ext fun r ↦
          Subtype.ext (Prod.ext (congrArg (fun m : R.unop ⟶ S ↦ m r) h₁)
            (congrArg (fun m : R.unop ⟶ T ↦ m r) h₂)))
      exact ULift.ext hxy
    · rintro ⟨⟨⟨v⟩, ⟨w⟩⟩, h⟩
      let v' : R.unop ⟶ S := v
      let w' : R.unop ⟶ T := w
      have h' : f.hom.app R ⟨v'⟩ = g.hom.app R ⟨w'⟩ := h
      have hw : (a.comp v'.hom.hom : C(R.unop, X)) = b.comp w'.hom.hom :=
        (J.map_uliftYonedaEquiv'.{u + 1} f v'.op).trans
          (h'.trans (J.map_uliftYonedaEquiv'.{u + 1} g w'.op).symm)
      let l : R.unop ⟶ L := CompHausLike.ofHom _
        ⟨fun r ↦ ⟨(v' r, w' r), DFunLike.congr_fun hw r⟩,
          (v'.hom.hom.continuous.prodMk w'.hom.hom.continuous).subtype_mk _⟩
      exact ⟨⟨l⟩, Subtype.ext (Prod.ext (ULift.ext rfl) (ULift.ext rfl))⟩
  exact ⟨L, ⟨hc.conePointUniqueUpToIso (pullback.isLimit f g)⟩⟩

/-- A Hausdorff space gives a quasiseparated condensed set. -/
theorem quasiSeparated_toCondensedSet (X : TopCat.{u + 1}) [T2Space X] :
    X.toCondensedSet.QuasiSeparated := by
  rw [quasiSeparated_iff]
  intro P Q f g
  obtain ⟨L, ⟨e⟩⟩ := X.exists_compHaus_iso_pullback_toCondensedSet f g
  exact (quasiCompact_iff_of_iso e).mp (quasiCompact_toCondensed_compHaus L)

/-- A space with quasicompact associated condensed set is compact: an epimorphic profinite cover
is already surjective on points. -/
theorem compactSpace_of_quasiCompact_toCondensedSet (X : TopCat.{u + 1})
    (hX : X.toCondensedSet.QuasiCompact) : CompactSpace X := by
  obtain ⟨S, f, hf⟩ := hX
  let T := profiniteToCompHaus.obj S
  let J := coherentTopology CompHaus.{u}
  let f' : C(T, X) := J.uliftYonedaEquiv.{u + 1} f
  suffices h : Function.Surjective f' from h.compactSpace f'.continuous
  intro x
  let P : CompHaus.{u} := CompHaus.of PUnit.{u + 1}
  let x' : C(P, X) := ContinuousMap.const _ x
  obtain ⟨Q, p, hp, a, ha⟩ := (epi_iff_locallySurjective_on_compHaus f).mp hf P x'
  obtain ⟨q, _⟩ := hp PUnit.unit
  let a' : Q ⟶ T := a.down
  have hmap := J.map_uliftYonedaEquiv.{u + 1} f a'
  exact ⟨a' q, congrArg (fun k : C(Q, X) ↦ k q) (hmap.trans ha)⟩

/-- The condensed set associated to an infinite discrete space is not quasicompact. -/
theorem not_quasiCompact_toCondensedSet_of_infinite_discrete (X : TopCat.{u + 1})
    [DiscreteTopology X] [Infinite X] : ¬ X.toCondensedSet.QuasiCompact := by
  intro h
  let : CompactSpace X := compactSpace_of_quasiCompact_toCondensedSet X h
  let : Finite X := Finite.of_finite_univ isCompact_univ.finite_of_discrete
  exact not_finite X

end TopCat

-- The discrete natural numbers distinguish quasiseparatedness from quasicompactness.
example : (TopCat.of (ULift.{1} ℕ)).toCondensedSet.QuasiSeparated ∧
    ¬ (TopCat.of (ULift.{1} ℕ)).toCondensedSet.QuasiCompact :=
  ⟨TopCat.quasiSeparated_toCondensedSet _,
    TopCat.not_quasiCompact_toCondensedSet_of_infinite_discrete _⟩

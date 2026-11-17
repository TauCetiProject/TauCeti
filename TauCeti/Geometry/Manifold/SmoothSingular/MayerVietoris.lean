/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.HomologicalComplex.Biprod
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Subcomplex
public import TauCeti.Geometry.Manifold.SmoothSingular.Subdivision

/-!
# Mayer–Vietoris sequence for smooth singular homology

For two open subsets `U` and `V` of a manifold `M`, a singular simplex in `U` is smooth in `U`
precisely when its image in `M` is smooth in `M`. Consequently the smooth singular subcomplexes of
`U ⊓ V`, `U`, and `V` form a pushout square with the subcomplex of smooth singular simplices of
`M` whose image lies in `U` or in `V`
(`TauCeti.isPushout_smoothSingularSubcomplex_inter_small`).

When `U ⊔ V = ⊤`, the small-chain theorem for the affinely stable subcomplex of smooth singular
simplices (`TauCeti.subcomplexSmallHomologyIso`) identifies the homology of that fourth corner
with the smooth singular homology of `M`, yielding the Mayer–Vietoris long exact sequence of
smooth singular homology (`TauCeti.smoothSingularMayerVietorisδ`,
`TauCeti.smoothSingularMayerVietoris_exact₁`, `TauCeti.smoothSingularMayerVietoris_exact₂`,
`TauCeti.smoothSingularMayerVietoris_exact₃`). The inclusion of smooth singular simplices into all
singular simplices induces a morphism from this pushout square to the singular pushout square
`TopCat.isPushout_toSSet_inter_smallSingularSubcomplex`, so it intertwines the smooth and singular
Mayer–Vietoris connecting morphisms (`TauCeti.smoothSingularMayerVietorisδ_naturality_ι`).

Comparing the Mayer–Vietoris short exact sequences of chain complexes by the five lemma gives the
binary-union step of the smoothing theorem: if smooth singular chains include into singular chains
by a quasi-isomorphism on `U`, on `V`, and on `U ⊓ V`, then they do so on `U ⊔ V`
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`). No smoothness of transition
maps on `M`, separation, or finite-dimensionality is needed here.

## Main results

* `TauCeti.isPushout_smoothSingularSubcomplex_inter_small`: the pushout square of smooth singular
  subcomplexes for `U ⊓ V`, `U`, `V`, and smooth simplices lying in `U` or in `V`.
* `TauCeti.smoothSingularMayerVietorisδ` and `TauCeti.smoothSingularMayerVietoris_exact₁`,
  `TauCeti.smoothSingularMayerVietoris_exact₂`, `TauCeti.smoothSingularMayerVietoris_exact₃`:
  the Mayer–Vietoris connecting morphism and exactness for smooth singular homology.
* `TauCeti.smoothSingularMayerVietorisδ_naturality_ι`: the inclusion of smooth into singular
  chains commutes with the Mayer–Vietoris connecting morphisms.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_of_equiv`: smooth bijections
  with smooth inverse preserve the smoothing quasi-isomorphism property.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_sup_eq_top` and
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`: the binary-union step of the
  smoothing theorem.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7.
* A. Hatcher, *Algebraic Topology*, Section 2.2, the Mayer–Vietoris sequence.
-/

public section

noncomputable section

open CategoryTheory Limits Set TopologicalSpace
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Pushout square of smooth singular subcomplexes -/

private lemma smoothSingularSubcomplexMap_inclusion_ι {U V : Opens M} (h : U ≤ V) :
    smoothSingularSubcomplexMap (I := I) (Opens.inclusion h) (contMDiff_inclusion h) ≫
        (smoothSingularSubcomplex I V).ι =
      (smoothSingularSubcomplex I U).ι ≫
        TopCat.toSSet.map (TopCat.ofHom (X := TopCat.of U) (Y := TopCat.of V)
          (ContinuousMap.inclusion (s := (U : Set M)) (t := (V : Set M)) h)) := by
  rw [smoothSingularSubcomplexMap_ι]
  rfl

/-- The map of smooth singular subcomplexes induced by an inclusion of open sets is a
monomorphism. -/
instance mono_smoothSingularSubcomplexMap_inclusion {U V : Opens M} (h : U ≤ V) :
    Mono (smoothSingularSubcomplexMap (I := I) (Opens.inclusion h) (contMDiff_inclusion h)) := by
  have hmono : Mono (smoothSingularSubcomplexMap (I := I) (Opens.inclusion h)
      (contMDiff_inclusion h) ≫ (smoothSingularSubcomplex I V).ι) := by
    rw [smoothSingularSubcomplexMap_inclusion_ι]
    have : Mono (TopCat.ofHom (X := TopCat.of U) (Y := TopCat.of V)
        (ContinuousMap.inclusion (s := (U : Set M)) (t := (V : Set M)) h)) :=
      (TopCat.mono_iff_injective _).2 (Set.inclusion_injective h)
    have := Functor.map_mono TopCat.toSSet (TopCat.ofHom (X := TopCat.of U) (Y := TopCat.of V)
      (ContinuousMap.inclusion (s := (U : Set M)) (t := (V : Set M)) h))
    exact mono_comp _ _
  exact mono_of_mono _ (smoothSingularSubcomplex I V).ι

variable (I) in
/-- A smooth singular simplex of an open set `U` lying in a member of `S` yields a smooth singular
simplex of `M` subordinate to `S`. -/
def toSmoothSmallSingularSubcomplex {ι : Type*} (S : ι → Set (TopCat.of M)) {U : Opens M} {i : ι}
    (hU : (U : Set (TopCat.of M)) ⊆ S i) :
    (smoothSingularSubcomplex I U : SSet) ⟶
      ((smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex S :
        (TopCat.toSSet.obj (TopCat.of M)).Subcomplex) : SSet) :=
  SSet.Subcomplex.lift
    ((smoothSingularSubcomplex I U).ι ≫
      TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (U : Set (TopCat.of M))))) (by
    rintro n _ ⟨σ, rfl⟩
    refine ⟨?_, ?_⟩
    · exact smoothSingularSubcomplex_le_preimage (contMDiff_subtype_val (I := I) (U := U)) n σ.2
    · rw [TopCat.mem_smallSingularSubcomplex_iff]
      refine ⟨i, ?_⟩
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Subfunctor.ι_app,
        TypeCat.ofHom_apply]
      rw [TopCat.toSSetObjEquiv_toSSet_map_app]
      rintro _ ⟨x, rfl⟩
      exact hU ((TopCat.of U).toSSetObjEquiv _ σ.1 x).2)

/-- Composing `toSmoothSmallSingularSubcomplex` with the inclusion into `TopCat.toSSet.obj M`
recovers the inclusion of `smoothSingularSubcomplex I U` followed by the subtype map. -/
@[reassoc (attr := simp)]
lemma toSmoothSmallSingularSubcomplex_ι {ι : Type*} (S : ι → Set (TopCat.of M)) {U : Opens M}
    {i : ι} (hU : (U : Set (TopCat.of M)) ⊆ S i) :
    toSmoothSmallSingularSubcomplex I S hU ≫
        (smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex S).ι =
      (smoothSingularSubcomplex I U).ι ≫
        TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (U : Set (TopCat.of M)))) :=
  SSet.Subcomplex.lift_ι _ _

/-- Composing `toSmoothSmallSingularSubcomplex` with the inclusion into
`smoothSingularSubcomplex I M` gives the smooth singular map induced by `Subtype.val : U → M`. -/
@[reassoc (attr := simp)]
lemma toSmoothSmallSingularSubcomplex_comp_homOfLE_left {ι : Type*} (S : ι → Set (TopCat.of M))
    {U : Opens M} {i : ι} (hU : (U : Set (TopCat.of M)) ⊆ S i) :
    toSmoothSmallSingularSubcomplex I S hU ≫
        SSet.Subcomplex.homOfLE (inf_le_left : smoothSingularSubcomplex I M ⊓
          (TopCat.of M).smallSingularSubcomplex S ≤ smoothSingularSubcomplex I M) =
      smoothSingularSubcomplexMap (Subtype.val : U → M) contMDiff_subtype_val := by
  rw [← cancel_mono (smoothSingularSubcomplex I M).ι, Category.assoc, SSet.Subcomplex.homOfLE_ι,
    toSmoothSmallSingularSubcomplex_ι, smoothSingularSubcomplexMap_ι]
  rfl

/-- Composing `toSmoothSmallSingularSubcomplex` with the inclusion into the small singular
subcomplex factors through `(smoothSingularSubcomplex I U).ι` and
`TopCat.toSmallSingularSubcomplex`. -/
@[reassoc (attr := simp)]
lemma toSmoothSmallSingularSubcomplex_comp_homOfLE_right {ι : Type*} (S : ι → Set (TopCat.of M))
    {U : Opens M} {i : ι} (hU : (U : Set (TopCat.of M)) ⊆ S i) :
    toSmoothSmallSingularSubcomplex I S hU ≫
        SSet.Subcomplex.homOfLE (inf_le_right : smoothSingularSubcomplex I M ⊓
          (TopCat.of M).smallSingularSubcomplex S ≤ (TopCat.of M).smallSingularSubcomplex S) =
      (smoothSingularSubcomplex I U).ι ≫
        TopCat.toSmallSingularSubcomplex (X := TopCat.of M) (S := (U : Set (TopCat.of M)))
          S hU := by
  rw [← cancel_mono ((TopCat.of M).smallSingularSubcomplex S).ι, Category.assoc,
    SSet.Subcomplex.homOfLE_ι, toSmoothSmallSingularSubcomplex_ι, Category.assoc,
    TopCat.toSmallSingularSubcomplex_ι]

/-- The image of the smooth singular subcomplex of an open set `U` inside `TopCat.toSSet.obj M`
consists of the smooth singular simplices of `M` whose image lies in `U`. -/
lemma range_smoothSingularSubcomplexMap_subtypeVal_comp_ι (U : Opens M) :
    SSet.Subcomplex.range
        (smoothSingularSubcomplexMap (I := I) (Subtype.val : U → M) contMDiff_subtype_val ≫
          (smoothSingularSubcomplex I M).ι) =
      smoothSingularSubcomplex I M ⊓
        SSet.Subcomplex.range
          (TopCat.toSSet.map
            (TopCat.ofHom (ContinuousMap.subtypeVal (U : Set (TopCat.of M))))) := by
  ext n σ
  constructor
  · rintro ⟨τ, rfl⟩
    refine ⟨?_, ⟨τ.1, ?_⟩⟩
    · exact ((smoothSingularSubcomplexMap (I := I) (Subtype.val : U → M) contMDiff_subtype_val).app
        n τ).2
    · exact (coe_smoothSingularSubcomplexMap_app (I := I) (J := I)
        (contMDiff_subtype_val (I := I) (U := U)) τ).symm
  · rintro ⟨hσ, ⟨τ, hτ⟩⟩
    let τ' : (TopCat.toSSet.obj (TopCat.of U)).obj n := τ
    have hτ' : τ' ∈ (smoothSingularSubcomplex I U).obj n := by
      rw [mem_smoothSingularSubcomplex_iff, ← ContMDiffOnSubset.subtypeVal_comp_iff]
      rw [mem_smoothSingularSubcomplex_iff] at hσ
      have hEq : (Subtype.val : U → M) ∘ ((TopCat.of U).toSSetObjEquiv n τ' ∘
            fullSimplexEquivStdSimplex (n.unop.len)) =
          (TopCat.of M).toSSetObjEquiv n σ ∘ fullSimplexEquivStdSimplex (n.unop.len) := by
        ext x
        rw [← hτ, Function.comp_apply, Function.comp_apply, Function.comp_apply,
          TopCat.toSSetObjEquiv_toSSet_map_app]
        rfl
      rwa [hEq]
    refine ⟨(⟨τ', hτ'⟩ : (smoothSingularSubcomplex I U : SSet).obj n), ?_⟩
    exact (coe_smoothSingularSubcomplexMap_app (I := I) (J := I)
      (contMDiff_subtype_val (I := I) (U := U)) ⟨τ', hτ'⟩).trans hτ

variable (I) in
/-- **The smooth singular subcomplexes of an intersection form a pushout square.** For open sets
`U` and `V` of `M`, the smooth singular subcomplexes of `U ⊓ V`, `U`, and `V` form a pushout
square with the subcomplex of smooth singular simplices of `M` whose image lies in `U` or in `V`. -/
theorem isPushout_smoothSingularSubcomplex_inter_small (U V : Opens M) :
    IsPushout
      (smoothSingularSubcomplexMap (I := I) (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
        (contMDiff_inclusion _))
      (smoothSingularSubcomplexMap (I := I) (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
        (contMDiff_inclusion _))
      (toSmoothSmallSingularSubcomplex I ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]
        (Matrix.cons_val_zero (U : Set (TopCat.of M)) ![(V : Set (TopCat.of M))]).superset)
      (toSmoothSmallSingularSubcomplex I ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]
        ((Matrix.cons_val_one (U : Set (TopCat.of M)) ![(V : Set (TopCat.of M))]).trans
          (Matrix.cons_val_zero (V : Set (TopCat.of M)) ![])).superset) := by
  let U' : Set (TopCat.of M) := (U : Set M)
  let V' : Set (TopCat.of M) := (V : Set M)
  let fI := smoothSingularSubcomplexMap (I := I) (Subtype.val : ↥(U ⊓ V) → M)
    contMDiff_subtype_val ≫ (smoothSingularSubcomplex I M).ι
  let fU := smoothSingularSubcomplexMap (I := I) (Subtype.val : U → M)
    contMDiff_subtype_val ≫ (smoothSingularSubcomplex I M).ι
  let fV := smoothSingularSubcomplexMap (I := I) (Subtype.val : V → M)
    contMDiff_subtype_val ≫ (smoothSingularSubcomplex I M).ι
  let A := SSet.Subcomplex.range fI
  let B := SSet.Subcomplex.range fU
  let C := SSet.Subcomplex.range fV
  let D := smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex ![U', V']
  have hA : A = smoothSingularSubcomplex I M ⊓
      SSet.Subcomplex.range
        (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (U' ∩ V')))) :=
    range_smoothSingularSubcomplexMap_subtypeVal_comp_ι (U ⊓ V)
  have hB : B = smoothSingularSubcomplex I M ⊓
      SSet.Subcomplex.range
        (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U'))) :=
    range_smoothSingularSubcomplexMap_subtypeVal_comp_ι U
  have hC : C = smoothSingularSubcomplex I M ⊓
      SSet.Subcomplex.range
        (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal V'))) :=
    range_smoothSingularSubcomplexMap_subtypeVal_comp_ι V
  have h_inf : B ⊓ C = A := by
    ext n σ
    -- Lattice operations on subcomplexes are computed pointwise on simplex sets.
    change (σ ∈ B.obj n ∧ σ ∈ C.obj n) ↔ σ ∈ A.obj n
    rw [hA, hB, hC]
    -- Unfold the pointwise meet of subcomplexes after rewriting `A`, `B`, `C`.
    change (σ ∈ (smoothSingularSubcomplex I M).obj n ∧
        σ ∈ (SSet.Subcomplex.range
          (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U')))).obj n) ∧
        (σ ∈ (smoothSingularSubcomplex I M).obj n ∧
        σ ∈ (SSet.Subcomplex.range
          (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal V')))).obj n) ↔
      σ ∈ (smoothSingularSubcomplex I M).obj n ∧
        σ ∈ (SSet.Subcomplex.range
          (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (U' ∩ V'))))).obj n
    rw [TopCat.mem_range_toSSet_subtypeVal_iff U',
      TopCat.mem_range_toSSet_subtypeVal_iff V',
      TopCat.mem_range_toSSet_subtypeVal_iff (U' ∩ V'), Set.subset_inter_iff]
    tauto
  have h_sup : B ⊔ C = D := by
    ext n σ
    -- Supremum of subcomplexes is also computed pointwise.
    change (σ ∈ B.obj n ∨ σ ∈ C.obj n) ↔ σ ∈ D.obj n
    rw [hB, hC]
    -- Unfold the pointwise meets on both sides after rewriting `B` and `C`.
    change (σ ∈ (smoothSingularSubcomplex I M).obj n ∧
        σ ∈ (SSet.Subcomplex.range
          (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U')))).obj n) ∨
        (σ ∈ (smoothSingularSubcomplex I M).obj n ∧
        σ ∈ (SSet.Subcomplex.range
          (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal V')))).obj n) ↔
      σ ∈ (smoothSingularSubcomplex I M).obj n ∧
        σ ∈ ((TopCat.of M).smallSingularSubcomplex ![U', V']).obj n
    rw [TopCat.mem_range_toSSet_subtypeVal_iff U',
      TopCat.mem_range_toSSet_subtypeVal_iff V', TopCat.mem_smallSingularSubcomplex_iff]
    simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    tauto
  have sq : SSet.Subcomplex.BicartSq A B C D := ⟨h_sup, h_inf⟩
  have hmono (W : Opens M) :
      Mono (smoothSingularSubcomplexMap (I := I) (Subtype.val : W → M) contMDiff_subtype_val ≫
        (smoothSingularSubcomplex I M).ι) := by
    rw [show smoothSingularSubcomplexMap (I := I) (Subtype.val : W → M) contMDiff_subtype_val ≫
          (smoothSingularSubcomplex I M).ι =
        (smoothSingularSubcomplex I W).ι ≫
          TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (W : Set (TopCat.of M)))) from
      smoothSingularSubcomplexMap_ι _]
    have := Functor.map_mono TopCat.toSSet
      (TopCat.ofHom (ContinuousMap.subtypeVal (W : Set (TopCat.of M))))
    exact mono_comp _ _
  have hi : Mono fI := hmono (U ⊓ V)
  have hu : Mono fU := hmono U
  have hv : Mono fV := hmono V
  refine sq.isPushout.of_iso'
    (asIso (SSet.Subcomplex.toRange fI))
    (asIso (SSet.Subcomplex.toRange fU))
    (asIso (SSet.Subcomplex.toRange fV)) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono B.ι]
    -- `toRange` followed by the range inclusion is the original smooth singular map.
    change fI = smoothSingularSubcomplexMap (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
      (contMDiff_inclusion _) ≫ fU
    rw [← Category.assoc, ← smoothSingularSubcomplexMap_comp]
    rfl
  · rw [← cancel_mono C.ι]
    -- `toRange` followed by the range inclusion is the original smooth singular map.
    change fI = smoothSingularSubcomplexMap (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
      (contMDiff_inclusion _) ≫ fV
    rw [← Category.assoc, ← smoothSingularSubcomplexMap_comp]
    rfl
  · rw [← cancel_mono D.ι]
    -- The range isomorphism reduces this side to the inclusion into `TopCat.toSSet.obj M`.
    change fU = toSmoothSmallSingularSubcomplex I ![U', V']
      (Matrix.cons_val_zero U' ![V']).superset ≫ D.ι
    rw [toSmoothSmallSingularSubcomplex_ι]
    exact smoothSingularSubcomplexMap_ι _
  · rw [← cancel_mono D.ι]
    -- The range isomorphism reduces this side to the inclusion into `TopCat.toSSet.obj M`.
    change fV = toSmoothSmallSingularSubcomplex I ![U', V']
      ((Matrix.cons_val_one U' ![V']).trans (Matrix.cons_val_zero V' ![])).superset ≫ D.ι
    rw [toSmoothSmallSingularSubcomplex_ι]
    exact smoothSingularSubcomplexMap_ι _

/-- The smooth singular inclusions of `U ⊓ V`, `U`, and `V` into `M` form a commutative square. -/
lemma commSq_smoothSingularSubcomplexMap_inter (U V : Opens M) :
    CommSq
      (smoothSingularSubcomplexMap (I := I) (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
        (contMDiff_inclusion _))
      (smoothSingularSubcomplexMap (I := I) (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
        (contMDiff_inclusion _))
      (smoothSingularSubcomplexMap (I := I) (Subtype.val : U → M) contMDiff_subtype_val)
      (smoothSingularSubcomplexMap (I := I) (Subtype.val : V → M) contMDiff_subtype_val) :=
  ⟨by rw [← smoothSingularSubcomplexMap_comp, ← smoothSingularSubcomplexMap_comp]; rfl⟩

/-! ### Mayer–Vietoris sequence of smooth singular homology -/

section MayerVietorisSequence

variable {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C] (R : C)

private lemma smooth_mayerVietorisFromBiprod_comp_homOfLE (U V : Opens M) (n : ℕ) :
    SSet.mayerVietorisFromBiprod R
        (toSmoothSmallSingularSubcomplex I ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]
          (Matrix.cons_val_zero (U : Set (TopCat.of M)) ![(V : Set (TopCat.of M))]).superset)
        (toSmoothSmallSingularSubcomplex I ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]
          ((Matrix.cons_val_one (U : Set (TopCat.of M)) ![(V : Set (TopCat.of M))]).trans
            (Matrix.cons_val_zero (V : Set (TopCat.of M)) ![])).superset) n ≫
      SSet.homologyMap
        (SSet.Subcomplex.homOfLE (inf_le_left : smoothSingularSubcomplex I M ⊓
          (TopCat.of M).smallSingularSubcomplex
            ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))] ≤
          smoothSingularSubcomplex I M)) R n =
    SSet.mayerVietorisFromBiprod R
      (smoothSingularSubcomplexMap (Subtype.val : U → M) contMDiff_subtype_val)
      (smoothSingularSubcomplexMap (Subtype.val : V → M) contMDiff_subtype_val) n := by
  ext <;> simp [← SSet.homologyMap_comp]

variable (I) in
/-- **The Mayer–Vietoris connecting morphism of smooth singular homology** for an open cover
`U ⊔ V = ⊤` of `M`: the connecting morphism of the pushout square of smooth singular subcomplexes,
precomposed with the inverse of the smooth small-chain isomorphism. -/
def smoothSingularMayerVietorisδ {U V : Opens M} (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    (smoothSingularSubcomplex I M : SSet).homology R n ⟶
      (smoothSingularSubcomplex I ↥(U ⊓ V) : SSet).homology R m :=
  (subcomplexSmallHomologyIso R (smoothSingularSubcomplex I M)
      ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]
      (U.isOpen.vecCons V.isOpen)
      (((U : Set M).iUnion_vecCons_pair (V : Set M)).trans (congrArg SetLike.coe hUV)) n).inv ≫
    SSet.mayerVietorisδ R (isPushout_smoothSingularSubcomplex_inter_small I U V) n m h

/-- The smooth Mayer–Vietoris connecting morphism restricts, on the homology of smooth simplices
lying in `U` or `V`, to the connecting morphism of the pushout square of smooth subcomplexes. -/
@[reassoc (attr := simp)]
lemma homologyMap_homOfLE_comp_smoothSingularMayerVietorisδ {U V : Opens M} (hUV : U ⊔ V = ⊤)
    (n m : ℕ) (h : m + 1 = n := by lia) :
    SSet.homologyMap
        (SSet.Subcomplex.homOfLE (inf_le_left : smoothSingularSubcomplex I M ⊓
          (TopCat.of M).smallSingularSubcomplex
            ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))] ≤
          smoothSingularSubcomplex I M)) R n ≫
      smoothSingularMayerVietorisδ I R hUV n m h =
    SSet.mayerVietorisδ R (isPushout_smoothSingularSubcomplex_inter_small I U V) n m h := by
  rw [smoothSingularMayerVietorisδ, SSet.homologyMap,
    ← subcomplexSmallHomologyIso_hom R (smoothSingularSubcomplex I M)
      ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]
      (U.isOpen.vecCons V.isOpen)
      (((U : Set M).iUnion_vecCons_pair (V : Set M)).trans (congrArg SetLike.coe hUV)),
    Iso.hom_inv_id_assoc]

/-- The composite of the smooth Mayer–Vietoris connecting morphism with the map into the biproduct
vanishes. -/
@[reassoc (attr := simp)]
lemma smoothSingularMayerVietorisδ_toBiprod {U V : Opens M} (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    smoothSingularMayerVietorisδ I R hUV n m h ≫
      SSet.mayerVietorisToBiprod R
        (smoothSingularSubcomplexMap (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
          (contMDiff_inclusion _))
        (smoothSingularSubcomplexMap (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
          (contMDiff_inclusion _)) m = 0 := by
  simp [smoothSingularMayerVietorisδ]

/-- The composite of the map from the biproduct with the smooth Mayer–Vietoris connecting morphism
vanishes. -/
@[reassoc (attr := simp)]
lemma smoothSingularMayerVietorisFromBiprod_δ {U V : Opens M} (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    SSet.mayerVietorisFromBiprod R
        (smoothSingularSubcomplexMap (Subtype.val : U → M) contMDiff_subtype_val)
        (smoothSingularSubcomplexMap (Subtype.val : V → M) contMDiff_subtype_val) n ≫
      smoothSingularMayerVietorisδ I R hUV n m h = 0 := by
  rw [← smooth_mayerVietorisFromBiprod_comp_homOfLE, Category.assoc,
    homologyMap_homOfLE_comp_smoothSingularMayerVietorisδ R hUV n m h,
    SSet.mayerVietorisFromBiprod_δ R _ n m h]

/-- **Exactness of the smooth Mayer–Vietoris sequence at `Hₘ^{∞}(U ⊓ V)`.** -/
lemma smoothSingularMayerVietoris_exact₁ {U V : Opens M} (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (smoothSingularMayerVietorisδ_toBiprod (I := I) R hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietoris_exact₁ R (isPushout_smoothSingularSubcomplex_inter_small I U V) n m h)
  refine ShortComplex.isoMk
    (subcomplexSmallHomologyIso R (smoothSingularSubcomplex I M)
      ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]
      (U.isOpen.vecCons V.isOpen)
      (((U : Set M).iUnion_vecCons_pair (V : Set M)).trans (congrArg SetLike.coe hUV)) n)
    (Iso.refl _) (Iso.refl _) ?_ (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
  dsimp only
  rw [Iso.refl_hom, Category.comp_id, subcomplexSmallHomologyIso_hom,
    homologyMap_homOfLE_comp_smoothSingularMayerVietorisδ R hUV n m h]

/-- **Exactness of the smooth Mayer–Vietoris sequence at `Hₙ^{∞}(U) ⊞ Hₙ^{∞}(V)`.** -/
lemma smoothSingularMayerVietoris_exact₂ {U V : Opens M} (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk _ _
      (SSet.mayerVietorisToBiprod_fromBiprod R
        (commSq_smoothSingularSubcomplexMap_inter (I := I) U V) n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietoris_exact₂ R (isPushout_smoothSingularSubcomplex_inter_small I U V) n)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (subcomplexSmallHomologyIso R (smoothSingularSubcomplex I M)
      ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]
      (U.isOpen.vecCons V.isOpen)
      (((U : Set M).iUnion_vecCons_pair (V : Set M)).trans (congrArg SetLike.coe hUV)) n)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]) ?_
  dsimp only
  rw [subcomplexSmallHomologyIso_hom, Iso.refl_hom, Category.id_comp,
    smooth_mayerVietorisFromBiprod_comp_homOfLE]

/-- **Exactness of the smooth Mayer–Vietoris sequence at `Hₙ^{∞}(M)`.** -/
lemma smoothSingularMayerVietoris_exact₃ {U V : Opens M} (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _
      (smoothSingularMayerVietorisFromBiprod_δ (I := I) R hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietoris_exact₃ R (isPushout_smoothSingularSubcomplex_inter_small I U V) n m h)
  refine ShortComplex.isoMk (Iso.refl _)
    (subcomplexSmallHomologyIso R (smoothSingularSubcomplex I M)
      ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]
      (U.isOpen.vecCons V.isOpen)
      (((U : Set M).iUnion_vecCons_pair (V : Set M)).trans (congrArg SetLike.coe hUV)) n)
    (Iso.refl _) ?_ ?_
  · dsimp only
    rw [subcomplexSmallHomologyIso_hom, Iso.refl_hom, Category.id_comp,
      smooth_mayerVietorisFromBiprod_comp_homOfLE]
  · dsimp only
    rw [Iso.refl_hom, Category.comp_id, subcomplexSmallHomologyIso_hom,
      homologyMap_homOfLE_comp_smoothSingularMayerVietorisδ R hUV n m h]

/-- **Compatibility of smooth and singular Mayer–Vietoris connecting morphisms.** The inclusion
of smooth singular chains into singular chains intertwines the smooth Mayer–Vietoris connecting
morphism with `TopCat.mayerVietorisδ`. -/
@[reassoc]
theorem smoothSingularMayerVietorisδ_naturality_ι {U V : Opens M} (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    smoothSingularMayerVietorisδ I R hUV n m h ≫
        SSet.homologyMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R m =
      SSet.homologyMap (smoothSingularSubcomplex I M).ι R n ≫
        TopCat.mayerVietorisδ R (U := (U : Set (TopCat.of M))) (V := (V : Set (TopCat.of M)))
          U.isOpen V.isOpen (congrArg SetLike.coe hUV) n m h := by
  have hnat := SSet.mayerVietorisδ_naturality R
    (smoothSingularSubcomplex I ↥(U ⊓ V)).ι
    (smoothSingularSubcomplex I U).ι
    (smoothSingularSubcomplex I V).ι
    (SSet.Subcomplex.homOfLE (inf_le_right : smoothSingularSubcomplex I M ⊓
      (TopCat.of M).smallSingularSubcomplex ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))] ≤
      (TopCat.of M).smallSingularSubcomplex ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]))
    (isPushout_smoothSingularSubcomplex_inter_small I U V)
    (TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (U : Set (TopCat.of M))
      (V : Set (TopCat.of M)))
    (smoothSingularSubcomplexMap_inclusion_ι (inf_le_left : U ⊓ V ≤ U))
    (smoothSingularSubcomplexMap_inclusion_ι (inf_le_right : U ⊓ V ≤ V))
    (toSmoothSmallSingularSubcomplex_comp_homOfLE_right _ _)
    (toSmoothSmallSingularSubcomplex_comp_homOfLE_right _ _) n m h
  let eS := subcomplexSmallHomologyIso R (smoothSingularSubcomplex I M)
    ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]
    (U.isOpen.vecCons V.isOpen)
    (((U : Set M).iUnion_vecCons_pair (V : Set M)).trans (congrArg SetLike.coe hUV)) n
  let eT := smallSingularHomologyIso R ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]
    (U.isOpen.vecCons V.isOpen)
    (((U : Set M).iUnion_vecCons_pair (V : Set M)).trans (congrArg SetLike.coe hUV)) n
  have hsmall :
      eS.hom ≫ SSet.homologyMap (smoothSingularSubcomplex I M).ι R n =
        SSet.homologyMap
          (SSet.Subcomplex.homOfLE (inf_le_right : smoothSingularSubcomplex I M ⊓
            (TopCat.of M).smallSingularSubcomplex
              ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))] ≤
            (TopCat.of M).smallSingularSubcomplex
              ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))])) R n ≫ eT.hom := by
    rw [subcomplexSmallHomologyIso_hom, smallSingularHomologyIso_hom,
      ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp]
    simp only [SSet.Subcomplex.homOfLE_ι]
  rw [← cancel_epi eS.hom]
  calc
    _ = (eS.hom ≫ smoothSingularMayerVietorisδ I R hUV n m h) ≫
        SSet.homologyMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R m :=
      (Category.assoc _ _ _).symm
    _ = SSet.mayerVietorisδ R (isPushout_smoothSingularSubcomplex_inter_small I U V) n m h ≫
        SSet.homologyMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R m := by
      rw [subcomplexSmallHomologyIso_hom,
        homologyMap_homOfLE_comp_smoothSingularMayerVietorisδ R hUV n m h]
    _ = SSet.homologyMap (SSet.Subcomplex.homOfLE (inf_le_right :
          smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex
            ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))] ≤
          (TopCat.of M).smallSingularSubcomplex
            ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))])) R n ≫
        SSet.mayerVietorisδ R (TopCat.isPushout_toSSet_inter_smallSingularSubcomplex
          (U : Set (TopCat.of M)) (V : Set (TopCat.of M))) n m h := hnat
    _ = SSet.homologyMap (SSet.Subcomplex.homOfLE (inf_le_right :
          smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex
            ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))] ≤
          (TopCat.of M).smallSingularSubcomplex
            ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))])) R n ≫
        (eT.hom ≫ TopCat.mayerVietorisδ R (U := (U : Set (TopCat.of M)))
          (V := (V : Set (TopCat.of M))) U.isOpen V.isOpen (congrArg SetLike.coe hUV) n m h) := by
      rw [smallSingularHomologyIso_hom, ← TopCat.homologyMap_ι_comp_mayerVietorisδ R U.isOpen
        V.isOpen (congrArg SetLike.coe hUV) n m h]
    _ = _ := by
      rw [← Category.assoc, ← hsmall, Category.assoc]

end MayerVietorisSequence

/-! ### Invariance under smooth bijections and binary-union step -/

section Equiv

variable {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Preadditive C]
  [CategoryWithHomology C]

/-- A smooth bijection with smooth inverse preserves whether the inclusion of smooth singular chains
into singular chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_of_equiv
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
    (R : C) (e : M ≃ N) (he : ContMDiff I J ∞ e) (hes : ContMDiff J I ∞ e.symm) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) ↔
      QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R) := by
  let eS : (smoothSingularSubcomplex I M : SSet) ≅ (smoothSingularSubcomplex J N : SSet) :=
    { hom := smoothSingularSubcomplexMap e he
      inv := smoothSingularSubcomplexMap e.symm hes
      hom_inv_id := by
        rw [← smoothSingularSubcomplexMap_comp]
        convert smoothSingularSubcomplexMap_id (I := I) (M := M)
        ext x
        exact e.symm_apply_apply x
      inv_hom_id := by
        rw [← smoothSingularSubcomplexMap_comp]
        convert smoothSingularSubcomplexMap_id (I := J) (M := N)
        ext y
        exact e.apply_symm_apply y }
  let eT : TopCat.toSSet.obj (TopCat.of M) ≅ TopCat.toSSet.obj (TopCat.of N) :=
    TopCat.toSSet.mapIso
      { hom := TopCat.ofHom ⟨e, he.continuous⟩
        inv := TopCat.ofHom ⟨e.symm, hes.continuous⟩
        hom_inv_id := by ext x; exact e.symm_apply_apply x
        inv_hom_id := by ext y; exact e.apply_symm_apply y }
  have hcomm : SSet.chainComplexMap eS.hom R ≫
        SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R =
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R ≫
        SSet.chainComplexMap eT.hom R := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (SSet.chainComplexMap · R) (smoothSingularSubcomplexMap_ι he)
  have : IsIso (SSet.chainComplexMap eS.hom R) :=
    (((SSet.chainComplexFunctor C).obj R).mapIso eS).isIso_hom
  have : IsIso (SSet.chainComplexMap eT.hom R) :=
    (((SSet.chainComplexFunctor C).obj R).mapIso eT).isIso_hom
  rw [← quasiIso_iff_comp_right (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)
      (SSet.chainComplexMap eT.hom R), ← hcomm,
    quasiIso_iff_comp_left (SSet.chainComplexMap eS.hom R)
      (SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R)]

end Equiv

section BinaryUnion

variable {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C] (R : C)

/-- **Binary-union step of the smoothing theorem for a cover of `M`.** If `U` and `V` are open sets
covering `M` such that the inclusion of smooth singular chains into singular chains is a
quasi-isomorphism on `U`, on `V`, and on `U ⊓ V`, then it is a quasi-isomorphism on `M`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_sup_eq_top {U V : Opens M}
    (hUV : U ⊔ V = ⊤)
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hI : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  let sqS := isPushout_smoothSingularSubcomplex_inter_small I U V
  let sqT := TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (U : Set (TopCat.of M))
    (V : Set (TopCat.of M))
  let φ₄ : ((smoothSingularSubcomplex I M ⊓
        (TopCat.of M).smallSingularSubcomplex
          ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))] :
        (TopCat.toSSet.obj (TopCat.of M)).Subcomplex) : SSet) ⟶
      ((TopCat.of M).smallSingularSubcomplex
        ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))] : SSet) :=
    SSet.Subcomplex.homOfLE inf_le_right
  let ψ := SSet.mayerVietorisShortComplexMap R sqS sqT
    (smoothSingularSubcomplexMap_inclusion_ι (inf_le_left : U ⊓ V ≤ U))
    (smoothSingularSubcomplexMap_inclusion_ι (inf_le_right : U ⊓ V ≤ V))
    (toSmoothSmallSingularSubcomplex_comp_homOfLE_right _ _)
    (toSmoothSmallSingularSubcomplex_comp_homOfLE_right _ _)
  have h₂ : QuasiIso ψ.τ₂ := by
    rw [SSet.mayerVietorisShortComplexMap_τ₂]
    exact HomologicalComplex.quasiIso_biprod_map _ _
  have h₃ : QuasiIso ψ.τ₃ := HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ
    (SSet.shortExact_mayerVietorisShortComplex R sqS)
    (SSet.shortExact_mayerVietorisShortComplex R sqT)
    (by rwa [SSet.mayerVietorisShortComplexMap_τ₁]) h₂
  rw [SSet.mayerVietorisShortComplexMap_τ₃] at h₃
  have hcov : ⋃ i, ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))] i = Set.univ :=
    ((U : Set M).iUnion_vecCons_pair (V : Set M)).trans (congrArg SetLike.coe hUV)
  have hsmallS : QuasiIso (SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (inf_le_left : smoothSingularSubcomplex I M ⊓
        (TopCat.of M).smallSingularSubcomplex
          ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))] ≤
        smoothSingularSubcomplex I M)) R) :=
    quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex R
      (smoothSingularSubcomplex I M) ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]
      (U.isOpen.vecCons V.isOpen) hcov
  have hsmallT : QuasiIso (SSet.chainComplexMap
      ((TopCat.of M).smallSingularSubcomplex
        ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]).ι R) :=
    quasiIso_chainComplexMap_smallSingularSubcomplex_ι R
      ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))] (U.isOpen.vecCons V.isOpen) hcov
  have hsq : SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : smoothSingularSubcomplex I M ⊓
          (TopCat.of M).smallSingularSubcomplex
            ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))] ≤
          smoothSingularSubcomplex I M)) R ≫
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R =
    SSet.chainComplexMap φ₄ R ≫
      SSet.chainComplexMap
        ((TopCat.of M).smallSingularSubcomplex
          ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))]).ι R := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    simp only [φ₄, SSet.Subcomplex.homOfLE_ι]
  have hcomp : QuasiIso (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : smoothSingularSubcomplex I M ⊓
          (TopCat.of M).smallSingularSubcomplex
            ![(U : Set (TopCat.of M)), (V : Set (TopCat.of M))] ≤
          smoothSingularSubcomplex I M)) R ≫
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
    rw [hsq]
    exact quasiIso_comp (hφ := h₃) (hφ' := hsmallT) _ _
  exact quasiIso_of_comp_left (hφ := hsmallS) (hφφ' := hcomp) _ _

/-- An open subset `W ≤ W'` viewed inside the open submanifold `W'` is smoothly equivalent to
`W`. -/
private theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_preimage_iff
    {W W' : Opens M} (h : W ≤ W') :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I
        (⟨Subtype.val ⁻¹' (W : Set M),
          W.isOpen.preimage continuous_subtype_val⟩ : Opens W')).ι R) ↔
      QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I W).ι R) := by
  let U₀ : Opens W' := ⟨Subtype.val ⁻¹' (W : Set M), W.isOpen.preimage continuous_subtype_val⟩
  let e : U₀ ≃ W :=
    { toFun := fun x ↦ ⟨x.1.1, x.2⟩
      invFun := fun x ↦ ⟨⟨x.1, h x.2⟩, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have he : ContMDiff I I ∞ e :=
    (ContMDiff.subtypeVal_comp_iff (I := I) (I' := I) W e).mp
      ((contMDiff_subtype_val (I := I) (U := W')).comp (contMDiff_subtype_val (I := I) (U := U₀)))
  have hes : ContMDiff I I ∞ e.symm :=
    (ContMDiff.subtypeVal_comp_iff (I := I) (I' := I) U₀ e.symm).mp
      ((ContMDiff.subtypeVal_comp_iff (I := I) (I' := I) W' (Subtype.val ∘ e.symm)).mp
        (contMDiff_subtype_val (I := I) (U := W)))
  exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_of_equiv R e he hes

/-- **The binary-union step of the smoothing theorem.** If the inclusion of smooth singular chains
into singular chains is a quasi-isomorphism on open sets `U`, `V`, and `U ⊓ V`, then it is a
quasi-isomorphism on `U ⊔ V`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup (U V : Opens M)
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hI : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊔ V)).ι R) := by
  let U' : Opens ↥(U ⊔ V) := ⟨Subtype.val ⁻¹' (U : Set M), U.isOpen.preimage continuous_subtype_val⟩
  let V' : Opens ↥(U ⊔ V) := ⟨Subtype.val ⁻¹' (V : Set M), V.isOpen.preimage continuous_subtype_val⟩
  have hcov : U' ⊔ V' = ⊤ := by
    ext ⟨x, hx⟩
    exact ⟨fun _ ↦ trivial, fun _ ↦ hx⟩
  have hU' : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U').ι R) :=
    (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_preimage_iff R
      (le_sup_left : U ≤ U ⊔ V)).2 hU
  have hV' : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V').ι R) :=
    (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_preimage_iff R
      (le_sup_right : V ≤ U ⊔ V)).2 hV
  have hI' : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U' ⊓ V')).ι R) :=
    (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_preimage_iff R
      (inf_le_left.trans le_sup_left : U ⊓ V ≤ U ⊔ V)).2 hI
  exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_sup_eq_top R hcov hU' hV' hI'

end BinaryUnion

end TauCeti

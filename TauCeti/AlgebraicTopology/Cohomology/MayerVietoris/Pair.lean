/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Relative

/-!
# The Mayer–Vietoris sequence of two pairs in singular cohomology

Let `C ⊆ A` and `D ⊆ B` be subsets of a topological space `X`, with `A` and `B` open in `A ∪ B`
and `C` and `D` open in `C ∪ D`, and write `Hⁿ(-)` for relative singular cohomology
`Hⁿ(-; R, M)`, the cohomology of `Hom(C(-; R), M)`. This file constructs the Mayer–Vietoris long
exact sequence of the pairs `(A, C)` and `(B, D)`,
`⋯ ⟶ Hⁿ(A ∪ B, C ∪ D) ⟶ Hⁿ(A, C) ⊞ Hⁿ(B, D) ⟶ Hⁿ(A ∩ B, C ∩ D) ⟶ Hⁿ⁺¹(A ∪ B, C ∪ D) ⟶ ⋯`,
whose first map is `(j_A^*, j_B^*)` and whose second map is `i_A^* - i_B^*`, the `i` and `j` being
the maps of pairs induced by the inclusions. These are the maps dual to the maps `j_A + j_B` and
`(i_A, -i_B)` of the sequence in singular homology (`TopCat.pairMayerVietorisδ`).

For the restrictions `(E|U, E₀|U)` and `(E|V, E₀|V)` of the Thom pair of a vector bundle to two
open sets `U` and `V` of its base, this is the sequence which glues classes of the Thom pairs over
`U` and over `V` that agree over `U ∩ V` to a class of the Thom pair over `U ∪ V`, as in the
construction of the Thom class by induction over trivializing open sets.

The construction dualizes the one in homology. For a commutative square of pairs of simplicial
sets whose squares of subobjects and of ambient simplicial sets are pushouts with monomorphic top
maps, the relative Mayer–Vietoris short exact sequence of chain complexes is split in each degree:
its last map has the section obtained from a section of the absolute sequence of the ambient
simplicial sets, since relative chains are a retract of ambient chains
(`SSetPair.isSplitEpi_mayerVietoris_g_f`). So applying `Hom(-, M)` keeps it short exact
(`SSetPair.shortExact_mayerVietorisCochainShortComplex`), and its cohomology sequence is the long
exact sequence `⋯ ⟶ Hⁿ(P₄) ⟶ Hⁿ(P₂) ⊞ Hⁿ(P₃) ⟶ Hⁿ(P₁) ⟶ Hⁿ⁺¹(P₄) ⟶ ⋯`. For the square of singular
pairs of `(A ∩ B, C ∩ D)`, `(A, C)`, `(B, D)` and the singular simplices of `X` lying in `A` or in
`B`, relative to those lying in `C` or in `D` (`TopCat.smallSingularPair`), the small-chain theorem
identifies the cohomology of the last pair with `Hⁿ(A ∪ B, C ∪ D)`: a map of pairs of simplicial
sets inducing quasi-isomorphisms on the cochains of both components induces one on relative
cochains (`SSetPair.quasiIso_cochainComplexMap`).

## Main definitions and results

* `SSetPair.shortExact_mayerVietorisCochainShortComplex`: the relative cochain Mayer–Vietoris
  sequence of a square of pairs of simplicial sets is short exact.
* `SSetPair.mayerVietorisCochainToBiprod`, `SSetPair.mayerVietorisCochainFromBiprod` and
  `SSetPair.mayerVietorisCochainδ`: the maps of its long exact cohomology sequence, exact by
  `SSetPair.mayerVietorisCochain_exact₁`, `SSetPair.mayerVietorisCochain_exact₂` and
  `SSetPair.mayerVietorisCochain_exact₃`.
* `TopCat.singularCohomologyPairMayerVietorisToBiprod` and
  `TopCat.singularCohomologyPairMayerVietorisFromBiprod`: the maps
  `Hⁿ(A ∪ B, C ∪ D) ⟶ Hⁿ(A, C) ⊞ Hⁿ(B, D)` and `Hⁿ(A, C) ⊞ Hⁿ(B, D) ⟶ Hⁿ(A ∩ B, C ∩ D)`.
* `TopCat.singularCohomologyPairMayerVietorisδ`: the connecting morphism
  `Hⁿ(A ∩ B, C ∩ D) ⟶ Hᵐ(A ∪ B, C ∪ D)`, `n + 1 = m`.
* `TopCat.singularCohomologyPairMayerVietoris_exact₁`,
  `TopCat.singularCohomologyPairMayerVietoris_exact₂`,
  `TopCat.singularCohomologyPairMayerVietoris_exact₃`: exactness at `Hᵐ(A ∪ B, C ∪ D)`, at
  `Hⁿ(A, C) ⊞ Hⁿ(B, D)` and at `Hⁿ(A ∩ B, C ∩ D)`.
* `TopCat.mono_singularCohomologyPairMayerVietorisToBiprod_zero`: injectivity at the degree-zero
  endpoint.
* `SSetPair.mayerVietorisCochainδ_naturality`: the relative cochain connecting morphism is natural
  in maps of squares of pairs of simplicial sets.
* `TopCat.singularCohomologyPairMayerVietorisδ_naturality`: the connecting morphism is natural in
  maps `f : X ⟶ Y` carrying `A`, `B`, `C` and `D` into `A'`, `B'`, `C'` and `D'`, and
  `TopCat.singularCohomologyPairMayerVietorisδ_naturality_of_subset` is the case of the inclusions
  for `A ⊆ A'`, `B ⊆ B'`, `C ⊆ C'` and `D ⊆ D'` in `X`.
* `TopCat.quasiIso_cochainComplexMap_smallSingularSubcomplexPairToUnion` and
  `TopCat.isIso_homologyMap_cochainComplexMap_smallSingularSubcomplexPairToUnion`: for `U` and `V`
  open in `U ∪ V`, the cochains of `X` relative to its singular simplices lying in `U` or in `V`
  compute the cohomology of `(X, U ∪ V)`.
* `TopCat.exists_singularCohomologyComplRestrict_eq_of_add_eq_zero`: exactness at the middle term
  of the Mayer–Vietoris sequence of the pairs `(X, X ∖ S)` and `(X, X ∖ T)` for closed sets `S`
  and `T`, stated with the restrictions `TopCat.singularCohomologyComplRestrict`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, the Mayer–Vietoris sequences in cohomology, including the relative ones.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, where the cohomological sequence of two pairs over open sets of a base is
  used to construct the Thom class.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TauCeti.ChainComplex

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

universe w v u

namespace SSetPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C}

/-! ### The relative cochain Mayer–Vietoris sequence -/

variable (R k M) {P₁ P₂ P₃ P₄ : SSetPair.{w}} {t : P₁ ⟶ P₂} {l : P₁ ⟶ P₃} {r : P₂ ⟶ P₄}
  {b : P₃ ⟶ P₄}

/-- The relative cochain Mayer–Vietoris sequence
`Hom(C(P₄), M) ⟶ Hom(C(P₂), M) ⊞ Hom(C(P₃), M) ⟶ Hom(C(P₁), M)` of a commutative square of pairs
of simplicial sets, with first map `(r^*, b^*)` and second map `t^* - l^*`. -/
abbrev mayerVietorisCochainShortComplex (w : t ≫ r = l ≫ b) :
    ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  ShortComplex.mk
    (biprod.lift (cochainComplexMap (R := R) (k := k) (M := M) r) (cochainComplexMap b))
    (biprod.desc (cochainComplexMap t) (-cochainComplexMap l))
    (by simp [← cochainComplexMap_comp, w])

/-! ### The maps of the sequence -/

variable (r b) in
/-- The first map `Hⁿ(P₄) ⟶ Hⁿ(P₂) ⊞ Hⁿ(P₃)` of the relative cochain Mayer–Vietoris sequence, with
components `r^*` and `b^*`. -/
def mayerVietorisCochainToBiprod (n : ℕ) :
    ((P₄.chainComplex R).linearYonedaObj k M).homology n ⟶
      ((P₂.chainComplex R).linearYonedaObj k M).homology n ⊞
        ((P₃.chainComplex R).linearYonedaObj k M).homology n :=
  biprod.lift (HomologicalComplex.homologyMap (cochainComplexMap r) n)
    (HomologicalComplex.homologyMap (cochainComplexMap b) n)

@[reassoc (attr := simp)]
lemma mayerVietorisCochainToBiprod_fst (n : ℕ) :
    mayerVietorisCochainToBiprod R k M r b n ≫ biprod.fst =
      HomologicalComplex.homologyMap (cochainComplexMap r) n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma mayerVietorisCochainToBiprod_snd (n : ℕ) :
    mayerVietorisCochainToBiprod R k M r b n ≫ biprod.snd =
      HomologicalComplex.homologyMap (cochainComplexMap b) n :=
  biprod.lift_snd _ _

variable (t l) in
/-- The second map `Hⁿ(P₂) ⊞ Hⁿ(P₃) ⟶ Hⁿ(P₁)` of the relative cochain Mayer–Vietoris sequence,
the difference `t^* - l^*`. -/
def mayerVietorisCochainFromBiprod (n : ℕ) :
    ((P₂.chainComplex R).linearYonedaObj k M).homology n ⊞
        ((P₃.chainComplex R).linearYonedaObj k M).homology n ⟶
      ((P₁.chainComplex R).linearYonedaObj k M).homology n :=
  biprod.desc (HomologicalComplex.homologyMap (cochainComplexMap t) n)
    (-HomologicalComplex.homologyMap (cochainComplexMap l) n)

@[reassoc (attr := simp)]
lemma inl_mayerVietorisCochainFromBiprod (n : ℕ) :
    biprod.inl ≫ mayerVietorisCochainFromBiprod R k M t l n =
      HomologicalComplex.homologyMap (cochainComplexMap t) n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_mayerVietorisCochainFromBiprod (n : ℕ) :
    biprod.inr ≫ mayerVietorisCochainFromBiprod R k M t l n =
      -HomologicalComplex.homologyMap (cochainComplexMap l) n :=
  biprod.inr_desc _ _

@[reassoc (attr := simp)]
lemma mayerVietorisCochainToBiprod_fromBiprod (w : t ≫ r = l ≫ b) (n : ℕ) :
    mayerVietorisCochainToBiprod R k M r b n ≫ mayerVietorisCochainFromBiprod R k M t l n = 0 := by
  simp [mayerVietorisCochainToBiprod, mayerVietorisCochainFromBiprod,
    ← HomologicalComplex.homologyMap_comp, ← cochainComplexMap_comp, w]

private lemma mayerVietorisCochainFromBiprod_eq (n : ℕ) :
    mayerVietorisCochainFromBiprod R k M t l n =
      biprod.desc (HomologicalComplex.homologyMap (cochainComplexMap t) n)
        (HomologicalComplex.homologyMap (-cochainComplexMap (R := R) (k := k) (M := M) l) n) := by
  rw [mayerVietorisCochainFromBiprod, HomologicalComplex.homologyMap_neg]

variable (sqL : IsPushout t.left l.left r.left b.left) [Mono t.left]
  (sqR : IsPushout t.right l.right r.right b.right) [Mono t.right]

/-- **The relative cochain Mayer–Vietoris short exact sequence.** For a commutative square of
pairs of simplicial sets whose squares of subobjects and of ambient simplicial sets are pushouts
with monomorphic top maps, the relative cochain Mayer–Vietoris sequence is short exact. -/
lemma shortExact_mayerVietorisCochainShortComplex :
    (mayerVietorisCochainShortComplex R k M
      (MorphismProperty.Arrow.Hom.ext sqL.w sqR.w)).ShortExact := by
  have hS := shortExact_mayerVietoris R sqL sqR
  have (i : ℕ) : IsSplitMono ((biprod.lift (chainComplexMap t R) (-chainComplexMap l R)).f i) :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hS
      i).isSplitMono_f_iff_isSplitEpi_g.2 (isSplitEpi_mayerVietoris_g_f R sqR i)
  -- Unfold `cochainComplexMap`, so that the terms of the sequence are written as
  -- `(linearYonedaFunctor k M).obj`, the form in which `Hom(-, M)` is applied to the chain
  -- Mayer–Vietoris sequence below.
  change (ShortComplex.mk
    (biprod.lift ((linearYonedaFunctor k M).map (chainComplexMap r R).op)
      ((linearYonedaFunctor k M).map (chainComplexMap b R).op))
    (biprod.desc ((linearYonedaFunctor k M).map (chainComplexMap t R).op)
      (-(linearYonedaFunctor k M).map (chainComplexMap l R).op)) _).ShortExact
  have he := (linearYonedaFunctor k M).mapIso_biprod_opIso_trans_mapBiprod_inv
    (P₂.chainComplex R) (P₃.chainComplex R)
  -- `Hom(-, M)` keeps the degreewise split chain sequence short exact; it remains to identify
  -- `Hom(C(P₂) ⊞ C(P₃), M)` with `Hom(C(P₂), M) ⊞ Hom(C(P₃), M)` compatibly with the maps.
  refine ShortComplex.shortExact_of_iso (Iso.symm ?_) (shortExact_map_linearYonedaFunctor k M hS)
  refine ShortComplex.isoMk (Iso.refl ((linearYonedaFunctor k M).obj (op (P₄.chainComplex R))))
    (((linearYonedaFunctor k M).mapIso (biprod.opIso _ _) ≪≫
      (linearYonedaFunctor k M).mapBiprod _ _).symm)
    (Iso.refl ((linearYonedaFunctor k M).obj (op (P₁.chainComplex R)))) ?_ ?_
  · rw [Iso.symm_hom]
    dsimp [ShortComplex.op, -linearYonedaFunctor_obj]
    rw [Category.id_comp]
    exact (Functor.biprod_lift_map_op_comp_mapIso_biprod_opIso_trans_mapBiprod_inv _ _ _).symm
  · rw [Iso.symm_hom, he]
    dsimp [ShortComplex.op, -linearYonedaFunctor_obj]
    apply biprod.hom_ext' <;>
      simp [← Functor.map_comp, ← op_comp, -linearYonedaFunctor_obj]

/-! ### The long exact sequence -/

/-- The relative cochain Mayer–Vietoris connecting morphism `Hⁿ(P₁) ⟶ Hᵐ(P₄)`, where
`n + 1 = m`: the connecting morphism of the relative cochain Mayer–Vietoris short exact
sequence. -/
def mayerVietorisCochainδ (n m : ℕ) (h : n + 1 = m := by lia) :
    ((P₁.chainComplex R).linearYonedaObj k M).homology n ⟶
      ((P₄.chainComplex R).linearYonedaObj k M).homology m :=
  (shortExact_mayerVietorisCochainShortComplex R k M sqL sqR).δ n m (by simpa)

/-- The relative cochain Mayer–Vietoris connecting morphism is the connecting morphism of the
relative cochain Mayer–Vietoris short exact sequence. -/
lemma mayerVietorisCochainδ_def (n m : ℕ) (h : n + 1 = m := by lia) :
    mayerVietorisCochainδ R k M sqL sqR n m h =
      (shortExact_mayerVietorisCochainShortComplex R k M sqL sqR).δ n m (by simpa) :=
  (rfl)

@[reassoc (attr := simp)]
lemma mayerVietorisCochainδ_toBiprod (n m : ℕ) (h : n + 1 = m := by lia) :
    mayerVietorisCochainδ R k M sqL sqR n m h ≫ mayerVietorisCochainToBiprod R k M r b m = 0 :=
  (shortExact_mayerVietorisCochainShortComplex R k M sqL sqR).δ_comp_biprod_lift_homologyMap
    n m _

@[reassoc (attr := simp)]
lemma mayerVietorisCochainFromBiprod_δ (n m : ℕ) (h : n + 1 = m := by lia) :
    mayerVietorisCochainFromBiprod R k M t l n ≫ mayerVietorisCochainδ R k M sqL sqR n m h = 0 := by
  rw [mayerVietorisCochainFromBiprod_eq]
  exact (shortExact_mayerVietorisCochainShortComplex R k M sqL sqR).biprod_desc_homologyMap_comp_δ
    n m _

/-- **Exactness of the relative cochain Mayer–Vietoris sequence at `Hᵐ(P₄)`.** -/
lemma mayerVietorisCochain_exact₁ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (mayerVietorisCochainδ_toBiprod R k M sqL sqR n m h)).Exact :=
  (shortExact_mayerVietorisCochainShortComplex R k M sqL sqR).biprod_homology_exact₁ n m _

include sqL sqR in
/-- **Exactness of the relative cochain Mayer–Vietoris sequence at `Hⁿ(P₂) ⊞ Hⁿ(P₃)`.** -/
lemma mayerVietorisCochain_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (mayerVietorisCochainToBiprod_fromBiprod R k M
      (MorphismProperty.Arrow.Hom.ext sqL.w sqR.w) n)).Exact := by
  convert (shortExact_mayerVietorisCochainShortComplex R k M sqL sqR).biprod_homology_exact₂ n
    using 2
  exacts [rfl, mayerVietorisCochainFromBiprod_eq R k M n]

/-- **Exactness of the relative cochain Mayer–Vietoris sequence at `Hⁿ(P₁)`.** -/
lemma mayerVietorisCochain_exact₃ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (mayerVietorisCochainFromBiprod_δ R k M sqL sqR n m h)).Exact := by
  convert (shortExact_mayerVietorisCochainShortComplex R k M sqL sqR).biprod_homology_exact₃ n m
    (by simpa) using 2
  exacts [mayerVietorisCochainFromBiprod_eq R k M n, rfl]

include sqR in
omit [Mono t.left] [Mono t.right] in
/-- The map `H⁰(P₄) ⟶ H⁰(P₂) ⊞ H⁰(P₃)` at the start of the relative cochain Mayer–Vietoris
sequence is a monomorphism. -/
lemma mono_mayerVietorisCochainToBiprod_zero :
    Mono (mayerVietorisCochainToBiprod R k M r b 0) := by
  have hepi := epi_biprod_desc_chainComplexMap R (r := r) (b := b) sqR
  have : Mono (biprod.lift (cochainComplexMap (R := R) (k := k) (M := M) r)
      (cochainComplexMap b)) :=
    mono_biprod_lift_linearYonedaFunctor_map_op_of_epi_f k M _ _ fun i ↦ inferInstance
  have : Mono (HomologicalComplex.homologyMap (biprod.lift
      (cochainComplexMap (R := R) (k := k) (M := M) r) (cochainComplexMap b)) 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel _ 0 fun i h ↦ by
      rw [ComplexShape.up_Rel] at h
      omega
  exact (HomologicalComplex.mono_biprod_lift_homologyMap_iff 0).2 inferInstance

variable {Q₁ Q₂ Q₃ Q₄ : SSetPair.{w}} {t' : Q₁ ⟶ Q₂} {l' : Q₁ ⟶ Q₃} {r' : Q₂ ⟶ Q₄}
  {b' : Q₃ ⟶ Q₄} (φ₁ : P₁ ⟶ Q₁) (φ₂ : P₂ ⟶ Q₂) (φ₃ : P₃ ⟶ Q₃) (φ₄ : P₄ ⟶ Q₄)

/-- **Naturality of the relative cochain Mayer–Vietoris connecting morphism** in maps of squares
of pairs. -/
@[reassoc]
lemma mayerVietorisCochainδ_naturality (sqL' : IsPushout t'.left l'.left r'.left b'.left)
    [Mono t'.left] (sqR' : IsPushout t'.right l'.right r'.right b'.right) [Mono t'.right]
    (ht : t ≫ φ₂ = φ₁ ≫ t') (hl : l ≫ φ₃ = φ₁ ≫ l') (hr : r ≫ φ₄ = φ₂ ≫ r')
    (hb : b ≫ φ₄ = φ₃ ≫ b') (n m : ℕ) (h : n + 1 = m := by lia) :
    mayerVietorisCochainδ R k M sqL' sqR' n m h ≫
        HomologicalComplex.homologyMap (cochainComplexMap φ₄) m =
      HomologicalComplex.homologyMap (cochainComplexMap φ₁) n ≫
        mayerVietorisCochainδ R k M sqL sqR n m h := by
  let ψ : mayerVietorisCochainShortComplex R k M (MorphismProperty.Arrow.Hom.ext sqL'.w sqR'.w) ⟶
      mayerVietorisCochainShortComplex R k M (MorphismProperty.Arrow.Hom.ext sqL.w sqR.w) :=
    { τ₁ := cochainComplexMap φ₄
      τ₂ := biprod.map (cochainComplexMap φ₂) (cochainComplexMap φ₃)
      τ₃ := cochainComplexMap φ₁
      comm₁₂ := by apply biprod.hom_ext <;> simp [← cochainComplexMap_comp, hr, hb]
      comm₂₃ := by apply biprod.hom_ext' <;> simp [← cochainComplexMap_comp, ht, hl] }
  exact HomologicalComplex.HomologySequence.δ_naturality ψ _ _ n m (by simpa)

end SSetPair

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C) {X : TopCat.{w}}

/-! ### The small-chain comparison on cochains -/

/-- The singular simplices of `X` lying in `U` or in `V` compute the cohomology of `U ∪ V`, by the
small-chain theorem for the cover of `U ∪ V` by `U` and `V`, which only needs to be open in
`U ∪ V`. -/
lemma quasiIso_cochainComplexMap_smallSingularSubcomplexToUnion (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) :
    QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexToUnion U V)) := by
  obtain ⟨e, he⟩ := exists_iso_comp_smallSingularSubcomplexToUnion U V
  have hcover : ∀ i, IsOpen (ofHom (ContinuousMap.subtypeVal (U ∪ V)) ⁻¹' ![U, V] i) := by
    intro i
    fin_cases i
    exacts [hU, hV]
  have hcov : ⋃ i, ofHom (ContinuousMap.subtypeVal (U ∪ V)) ⁻¹' ![U, V] i = Set.univ := by
    rw [← Set.preimage_iUnion, Set.iUnion_vecCons_pair]
    exact Set.eq_univ_of_forall fun x ↦ x.2
  -- Restricting cochains to the small simplices of `U ∪ V` is an isomorphism on cohomology.
  have hq : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
      ((of ↥(U ∪ V)).smallSingularSubcomplex
        (fun i ↦ ofHom (ContinuousMap.subtypeVal (U ∪ V)) ⁻¹' ![U, V] i)).ι) :=
    TauCeti.quasiIso_cochainComplexMap_smallSingularSubcomplex_ι R k M _ hcover hcov
  rw [← he, SSet.cochainComplexMap_comp] at hq
  have : IsIso (SSet.cochainComplexMap (R := R) (k := k) (M := M) e.hom) :=
    ⟨SSet.cochainComplexMap e.inv, by simp [← SSet.cochainComplexMap_comp],
      by simp [← SSet.cochainComplexMap_comp]⟩
  exact quasiIso_of_comp_right _ (SSet.cochainComplexMap e.hom)

/-- The cohomology of `X` relative to its singular simplices lying in `U` or in `V` is that of
`(X, U ∪ V)`, by the small-chain theorem for the cover of `U ∪ V` by `U` and `V`, which only needs
to be open in `U ∪ V`. -/
lemma quasiIso_cochainComplexMap_smallSingularSubcomplexPairToUnion (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) :
    QuasiIso (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexPairToUnion U V)) := by
  have : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexPairToUnion U V).left) := by
    rw [smallSingularSubcomplexPairToUnion_left]
    exact quasiIso_cochainComplexMap_smallSingularSubcomplexToUnion R k M U V hU hV
  have : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexPairToUnion U V).right) := by
    have : IsIso (SSet.chainComplexMap (smallSingularSubcomplexPairToUnion U V).right R) := by
      rw [chainComplexMap_smallSingularSubcomplexPairToUnion_right]
      exact IsIso.id _
    have : IsIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
        (smallSingularSubcomplexPairToUnion U V).right) :=
      Functor.map_isIso (linearYonedaFunctor k M) _
    exact quasiIso_of_isIso _
  exact SSetPair.quasiIso_cochainComplexMap _

/-- For `U` and `V` open in `U ∪ V`, restricting cochains of `(X, U ∪ V)` to the chains of `X`
relative to its singular simplices lying in `U` or in `V` is an isomorphism on cohomology. -/
lemma isIso_homologyMap_cochainComplexMap_smallSingularSubcomplexPairToUnion (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexPairToUnion U V)) n) := by
  have := quasiIso_cochainComplexMap_smallSingularSubcomplexPairToUnion R k M U V hU hV
  infer_instance

/-! ### The Mayer–Vietoris sequence of two pairs -/

variable {A B C D : Set X} (hCA : C ⊆ A) (hDB : D ⊆ B)

attribute [local instance] TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_left
  TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_right

/-- The first map `Hⁿ(A ∪ B, C ∪ D) ⟶ Hⁿ(A, C) ⊞ Hⁿ(B, D)` of the Mayer–Vietoris sequence of the
pairs `(A, C)` and `(B, D)` in singular cohomology, with components the restrictions `j_A^*` and
`j_B^*` along the maps of pairs induced by the inclusions. -/
def singularCohomologyPairMayerVietorisToBiprod (n : ℕ) :
    (TopPair.ofInclusion (Set.union_subset_union hCA hDB)).singularCohomology R k M n ⟶
      (TopPair.ofInclusion hCA).singularCohomology R k M n ⊞
        (TopPair.ofInclusion hDB).singularCohomology R k M n :=
  biprod.lift
    (TopPair.singularCohomologyMap (TopPair.ofInclusionMap hCA (Set.union_subset_union hCA hDB)
      (ContinuousMap.inclusion Set.subset_union_left) fun _ hx ↦ Set.subset_union_left hx) n)
    (TopPair.singularCohomologyMap (TopPair.ofInclusionMap hDB (Set.union_subset_union hCA hDB)
      (ContinuousMap.inclusion Set.subset_union_right) fun _ hx ↦ Set.subset_union_right hx) n)

@[reassoc (attr := simp)]
lemma singularCohomologyPairMayerVietorisToBiprod_fst (n : ℕ) :
    singularCohomologyPairMayerVietorisToBiprod R k M hCA hDB n ≫ biprod.fst =
      TopPair.singularCohomologyMap (TopPair.ofInclusionMap hCA (Set.union_subset_union hCA hDB)
        (ContinuousMap.inclusion Set.subset_union_left) fun _ hx ↦ Set.subset_union_left hx) n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma singularCohomologyPairMayerVietorisToBiprod_snd (n : ℕ) :
    singularCohomologyPairMayerVietorisToBiprod R k M hCA hDB n ≫ biprod.snd =
      TopPair.singularCohomologyMap (TopPair.ofInclusionMap hDB (Set.union_subset_union hCA hDB)
        (ContinuousMap.inclusion Set.subset_union_right) fun _ hx ↦ Set.subset_union_right hx) n :=
  biprod.lift_snd _ _

/-- The second map `Hⁿ(A, C) ⊞ Hⁿ(B, D) ⟶ Hⁿ(A ∩ B, C ∩ D)` of the Mayer–Vietoris sequence of the
pairs `(A, C)` and `(B, D)` in singular cohomology, the difference `i_A^* - i_B^*` of the
restrictions along the maps of pairs induced by the inclusions. -/
def singularCohomologyPairMayerVietorisFromBiprod (n : ℕ) :
    (TopPair.ofInclusion hCA).singularCohomology R k M n ⊞
        (TopPair.ofInclusion hDB).singularCohomology R k M n ⟶
      (TopPair.ofInclusion (Set.inter_subset_inter hCA hDB)).singularCohomology R k M n :=
  biprod.desc
    (TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hCA
      (ContinuousMap.inclusion Set.inter_subset_left) fun _ hx ↦ Set.inter_subset_left hx) n)
    (-TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hDB
      (ContinuousMap.inclusion Set.inter_subset_right) fun _ hx ↦ Set.inter_subset_right hx) n)

@[reassoc (attr := simp)]
lemma inl_singularCohomologyPairMayerVietorisFromBiprod (n : ℕ) :
    biprod.inl ≫ singularCohomologyPairMayerVietorisFromBiprod R k M hCA hDB n =
      TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hCA
        (ContinuousMap.inclusion Set.inter_subset_left) fun _ hx ↦ Set.inter_subset_left hx) n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_singularCohomologyPairMayerVietorisFromBiprod (n : ℕ) :
    biprod.inr ≫ singularCohomologyPairMayerVietorisFromBiprod R k M hCA hDB n =
      -TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hDB
        (ContinuousMap.inclusion Set.inter_subset_right) fun _ hx ↦ Set.inter_subset_right hx) n :=
  biprod.inr_desc _ _

/-! #### Comparison with the square of singular pairs -/

/-- The cohomology of `TopCat.smallSingularPair hCA hDB` is identified with that of
`(A ∪ B, C ∪ D)` by `TopCat.smallSingularPairToUnion`. -/
lemma isIso_homologyMap_cochainComplexMap_smallSingularPairToUnion
    (hA : IsOpen ((↑) ⁻¹' A : Set ↥(A ∪ B))) (hB : IsOpen ((↑) ⁻¹' B : Set ↥(A ∪ B)))
    (hC : IsOpen ((↑) ⁻¹' C : Set ↥(C ∪ D))) (hD : IsOpen ((↑) ⁻¹' D : Set ↥(C ∪ D))) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularPairToUnion hCA hDB)) n) := by
  have : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularPairToUnion hCA hDB).left) :=
    quasiIso_cochainComplexMap_smallSingularSubcomplexToUnion R k M C D hC hD
  have : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularPairToUnion hCA hDB).right) :=
    quasiIso_cochainComplexMap_smallSingularSubcomplexToUnion R k M A B hA hB
  have := SSetPair.quasiIso_cochainComplexMap (R := R) (k := k) (M := M)
    (smallSingularPairToUnion hCA hDB)
  infer_instance

private lemma homologyMap_smallSingularPairToUnion_comp_mayerVietorisCochainToBiprod (n : ℕ) :
    HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
        (smallSingularPairToUnion hCA hDB)) n ≫
      SSetPair.mayerVietorisCochainToBiprod R k M
        (toSmallSingularPair hCA hDB hCA (i := 0) (Matrix.cons_val_zero A ![B]).superset
          (Matrix.cons_val_zero C ![D]).superset)
        (toSmallSingularPair hCA hDB hDB (i := 1)
          ((Matrix.cons_val_one A ![B]).trans (Matrix.cons_val_zero B ![])).superset
          ((Matrix.cons_val_one C ![D]).trans (Matrix.cons_val_zero D ![])).superset) n =
    singularCohomologyPairMayerVietorisToBiprod R k M hCA hDB n := by
  apply biprod.hom_ext
  · rw [Category.assoc, SSetPair.mayerVietorisCochainToBiprod_fst,
      ← HomologicalComplex.homologyMap_comp, ← SSetPair.cochainComplexMap_comp,
      toSmallSingularPair_comp_smallSingularPairToUnion _ _ _ _ _ Set.subset_union_left
        Set.subset_union_left,
      singularCohomologyPairMayerVietorisToBiprod_fst, TopPair.singularCohomologyMap_eq]
  · rw [Category.assoc, SSetPair.mayerVietorisCochainToBiprod_snd,
      ← HomologicalComplex.homologyMap_comp, ← SSetPair.cochainComplexMap_comp,
      toSmallSingularPair_comp_smallSingularPairToUnion _ _ _ _ _ Set.subset_union_right
        Set.subset_union_right,
      singularCohomologyPairMayerVietorisToBiprod_snd, TopPair.singularCohomologyMap_eq]

private lemma mayerVietorisCochainFromBiprod_eq (n : ℕ) :
    SSetPair.mayerVietorisCochainFromBiprod R k M
        (TopPair.toSSetPair.map (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hCA
          (ContinuousMap.inclusion Set.inter_subset_left) fun _ hx ↦ Set.inter_subset_left hx))
        (TopPair.toSSetPair.map (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hDB
          (ContinuousMap.inclusion Set.inter_subset_right)
            fun _ hx ↦ Set.inter_subset_right hx)) n =
      singularCohomologyPairMayerVietorisFromBiprod R k M hCA hDB n := by
  apply biprod.hom_ext' <;> simp [TopPair.singularCohomologyMap_eq]

/-! #### The long exact sequence -/

/-- The first two maps of the Mayer–Vietoris sequence of two pairs in singular cohomology compose
to zero. -/
@[reassoc (attr := simp)]
lemma singularCohomologyPairMayerVietorisToBiprod_fromBiprod (n : ℕ) :
    singularCohomologyPairMayerVietorisToBiprod R k M hCA hDB n ≫
      singularCohomologyPairMayerVietorisFromBiprod R k M hCA hDB n = 0 := by
  rw [← homologyMap_smallSingularPairToUnion_comp_mayerVietorisCochainToBiprod,
    ← mayerVietorisCochainFromBiprod_eq, Category.assoc,
    SSetPair.mayerVietorisCochainToBiprod_fromBiprod R k M
      (MorphismProperty.Arrow.Hom.ext (isPushout_toSmallSingularPair_left hCA hDB).w
        (isPushout_toSmallSingularPair_right hCA hDB).w), comp_zero]

variable (hA : IsOpen ((↑) ⁻¹' A : Set ↥(A ∪ B)))
  (hB : IsOpen ((↑) ⁻¹' B : Set ↥(A ∪ B))) (hC : IsOpen ((↑) ⁻¹' C : Set ↥(C ∪ D)))
  (hD : IsOpen ((↑) ⁻¹' D : Set ↥(C ∪ D)))

/-- The connecting morphism `Hⁿ(A ∩ B, C ∩ D) ⟶ Hᵐ(A ∪ B, C ∪ D)`, `n + 1 = m`, of the
Mayer–Vietoris sequence of the pairs `(A, C)` and `(B, D)` in singular cohomology, for `A` and `B`
open in `A ∪ B` and `C` and `D` open in `C ∪ D`. It is the connecting morphism of the relative
cochain Mayer–Vietoris sequence of the singular pairs of `A ∩ B`, `A`, `B` and of the singular
simplices of `X` lying in `A` or in `B` (relative to those lying in `C` or in `D`), followed by the
inverse of the small-chain isomorphism identifying the cohomology of the last of these with
`Hᵐ(A ∪ B, C ∪ D)`. -/
def singularCohomologyPairMayerVietorisδ (n m : ℕ) (h : n + 1 = m := by lia) :
    (TopPair.ofInclusion (Set.inter_subset_inter hCA hDB)).singularCohomology R k M n ⟶
      (TopPair.ofInclusion (Set.union_subset_union hCA hDB)).singularCohomology R k M m :=
  have := isIso_homologyMap_cochainComplexMap_smallSingularPairToUnion R k M hCA hDB hA hB hC hD m
  SSetPair.mayerVietorisCochainδ R k M (isPushout_toSmallSingularPair_left hCA hDB)
      (isPushout_toSmallSingularPair_right hCA hDB) n m h ≫
    inv (HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularPairToUnion hCA hDB)) m)

/-- Followed by restriction to the singular simplices lying in `A` or in `B`, the connecting
morphism of the Mayer–Vietoris sequence of two pairs is the connecting morphism of the relative
cochain Mayer–Vietoris sequence of the square of singular pairs. Since that restriction is an
isomorphism on cohomology, this characterizes it. -/
@[reassoc (attr := simp)]
lemma singularCohomologyPairMayerVietorisδ_comp_homologyMap (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyPairMayerVietorisδ R k M hCA hDB hA hB hC hD n m h ≫
        HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
          (smallSingularPairToUnion hCA hDB)) m =
      SSetPair.mayerVietorisCochainδ R k M (isPushout_toSmallSingularPair_left hCA hDB)
        (isPushout_toSmallSingularPair_right hCA hDB) n m h := by
  have := isIso_homologyMap_cochainComplexMap_smallSingularPairToUnion R k M hCA hDB hA hB hC hD m
  rw [singularCohomologyPairMayerVietorisδ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

@[reassoc (attr := simp)]
lemma singularCohomologyPairMayerVietorisδ_toBiprod (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyPairMayerVietorisδ R k M hCA hDB hA hB hC hD n m h ≫
      singularCohomologyPairMayerVietorisToBiprod R k M hCA hDB m = 0 := by
  rw [← homologyMap_smallSingularPairToUnion_comp_mayerVietorisCochainToBiprod R k M hCA hDB m,
    ← Category.assoc,
    singularCohomologyPairMayerVietorisδ_comp_homologyMap R k M hCA hDB hA hB hC hD n m h]
  exact SSetPair.mayerVietorisCochainδ_toBiprod R k M _ _ n m h

@[reassoc (attr := simp)]
lemma singularCohomologyPairMayerVietorisFromBiprod_δ (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyPairMayerVietorisFromBiprod R k M hCA hDB n ≫
      singularCohomologyPairMayerVietorisδ R k M hCA hDB hA hB hC hD n m h = 0 := by
  rw [← mayerVietorisCochainFromBiprod_eq, singularCohomologyPairMayerVietorisδ,
    SSetPair.mayerVietorisCochainFromBiprod_δ_assoc R k M _ _ n m h, zero_comp]

/-- **Exactness of the Mayer–Vietoris sequence of two pairs at `Hᵐ(A ∪ B, C ∪ D)`.** -/
lemma singularCohomologyPairMayerVietoris_exact₁ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      (singularCohomologyPairMayerVietorisδ_toBiprod R k M hCA hDB hA hB hC hD n m h)).Exact := by
  have := isIso_homologyMap_cochainComplexMap_smallSingularPairToUnion R k M hCA hDB hA hB hC hD m
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSetPair.mayerVietorisCochain_exact₁ R k M (isPushout_toSmallSingularPair_left hCA hDB)
      (isPushout_toSmallSingularPair_right hCA hDB) n m h)
  refine ShortComplex.isoMk (Iso.refl _)
    (asIso (HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularPairToUnion hCA hDB)) m)).symm (Iso.refl _) ?_ ?_
  · simp [singularCohomologyPairMayerVietorisδ]
  · simp [← homologyMap_smallSingularPairToUnion_comp_mayerVietorisCochainToBiprod R k M hCA hDB m]

include hA hB hC hD in
/-- **Exactness of the Mayer–Vietoris sequence of two pairs at `Hⁿ(A, C) ⊞ Hⁿ(B, D)`.** -/
lemma singularCohomologyPairMayerVietoris_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _
      (singularCohomologyPairMayerVietorisToBiprod_fromBiprod R k M hCA hDB n)).Exact := by
  have := isIso_homologyMap_cochainComplexMap_smallSingularPairToUnion R k M hCA hDB hA hB hC hD n
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSetPair.mayerVietorisCochain_exact₂ R k M (isPushout_toSmallSingularPair_left hCA hDB)
      (isPushout_toSmallSingularPair_right hCA hDB) n)
  refine ShortComplex.isoMk
    (asIso (HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularPairToUnion hCA hDB)) n)).symm (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp [← homologyMap_smallSingularPairToUnion_comp_mayerVietorisCochainToBiprod R k M hCA hDB n]
  · simp [mayerVietorisCochainFromBiprod_eq]

/-- **Exactness of the Mayer–Vietoris sequence of two pairs at `Hⁿ(A ∩ B, C ∩ D)`.** -/
lemma singularCohomologyPairMayerVietoris_exact₃ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      (singularCohomologyPairMayerVietorisFromBiprod_δ R k M hCA hDB hA hB hC hD n m h)).Exact := by
  have := isIso_homologyMap_cochainComplexMap_smallSingularPairToUnion R k M hCA hDB hA hB hC hD m
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSetPair.mayerVietorisCochain_exact₃ R k M (isPushout_toSmallSingularPair_left hCA hDB)
      (isPushout_toSmallSingularPair_right hCA hDB) n m h)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (asIso (HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularPairToUnion hCA hDB)) m)).symm ?_ ?_
  · simp [mayerVietorisCochainFromBiprod_eq]
  · simp [singularCohomologyPairMayerVietorisδ]

include hA hB hC hD in
/-- The map `H⁰(A ∪ B, C ∪ D) ⟶ H⁰(A, C) ⊞ H⁰(B, D)` at the start of the Mayer–Vietoris sequence of
two pairs in singular cohomology is a monomorphism. -/
lemma mono_singularCohomologyPairMayerVietorisToBiprod_zero :
    Mono (singularCohomologyPairMayerVietorisToBiprod R k M hCA hDB 0) := by
  have := isIso_homologyMap_cochainComplexMap_smallSingularPairToUnion R k M hCA hDB hA hB hC hD 0
  have := SSetPair.mono_mayerVietorisCochainToBiprod_zero R k M
    (isPushout_toSmallSingularPair_right hCA hDB)
  rw [← homologyMap_smallSingularPairToUnion_comp_mayerVietorisCochainToBiprod R k M hCA hDB 0]
  infer_instance

/-! #### Naturality of the connecting morphism -/

section Naturality

variable {Y : TopCat.{w}} {A' B' C' D' : Set Y} (hCA' : C' ⊆ A') (hDB' : D' ⊆ B')
  (hA' : IsOpen ((↑) ⁻¹' A' : Set ↥(A' ∪ B'))) (hB' : IsOpen ((↑) ⁻¹' B' : Set ↥(A' ∪ B')))
  (hC' : IsOpen ((↑) ⁻¹' C' : Set ↥(C' ∪ D'))) (hD' : IsOpen ((↑) ⁻¹' D' : Set ↥(C' ∪ D')))
  (f : X ⟶ Y) (hfA : Set.MapsTo f A A') (hfB : Set.MapsTo f B B') (hfC : Set.MapsTo f C C')
  (hfD : Set.MapsTo f D D')

/-- **Naturality of the connecting morphism of the Mayer–Vietoris sequence of two pairs.** A map
`f : X ⟶ Y` carrying `A`, `B`, `C` and `D` into `A'`, `B'`, `C'` and `D'` commutes with the
connecting morphisms, where `(A ∩ B, C ∩ D) ⟶ (A' ∩ B', C' ∩ D')` and
`(A ∪ B, C ∪ D) ⟶ (A' ∪ B', C' ∪ D')` are the maps of pairs given by the restrictions of `f`. -/
@[reassoc]
lemma singularCohomologyPairMayerVietorisδ_naturality (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyPairMayerVietorisδ R k M hCA' hDB' hA' hB' hC' hD' n m h ≫
        TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.union_subset_union hCA hDB)
          (Set.union_subset_union hCA' hDB') ⟨(hfA.union_union hfB).restrict,
            f.hom.continuous.restrict (hfA.union_union hfB)⟩
          fun _ hx ↦ hfC.union_union hfD hx) m =
      TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB)
          (Set.inter_subset_inter hCA' hDB') ⟨(hfA.inter_inter hfB).restrict,
            f.hom.continuous.restrict (hfA.inter_inter hfB)⟩
          fun _ hx ↦ hfC.inter_inter hfD hx) n ≫
        singularCohomologyPairMayerVietorisδ R k M hCA hDB hA hB hC hD n m h := by
  have := isIso_homologyMap_cochainComplexMap_smallSingularPairToUnion R k M hCA hDB hA hB hC hD m
  have := isIso_homologyMap_cochainComplexMap_smallSingularPairToUnion R k M hCA' hDB' hA' hB' hC'
    hD' m
  have hnat := SSetPair.mayerVietorisCochainδ_naturality R k M
    (isPushout_toSmallSingularPair_left hCA hDB) (isPushout_toSmallSingularPair_right hCA hDB)
    (TopPair.toSSetPair.map (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB)
      (Set.inter_subset_inter hCA' hDB') ⟨(hfA.inter_inter hfB).restrict,
        f.hom.continuous.restrict (hfA.inter_inter hfB)⟩ fun _ hx ↦ hfC.inter_inter hfD hx))
    (TopPair.toSSetPair.map (TopPair.ofInclusionMap hCA hCA' ⟨hfA.restrict,
      f.hom.continuous.restrict hfA⟩ fun _ hx ↦ hfC hx))
    (TopPair.toSSetPair.map (TopPair.ofInclusionMap hDB hDB' ⟨hfB.restrict,
      f.hom.continuous.restrict hfB⟩ fun _ hx ↦ hfD hx))
    (smallSingularPairMap hCA hDB hCA' hDB' f hfA hfB hfC hfD)
    (isPushout_toSmallSingularPair_left hCA' hDB') (isPushout_toSmallSingularPair_right hCA' hDB')
    (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ (TopPair.ofInclusionMap_comp_ofInclusionMap_eq _ _ _ _ _ _ _ _ fun _ ↦ rfl))
    (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ (TopPair.ofInclusionMap_comp_ofInclusionMap_eq _ _ _ _ _ _ _ _ fun _ ↦ rfl))
    (toSmallSingularPair_comp_smallSingularPairMap _ _ _ _ f hfA hfB hfC hfD _ _ _ _ _ _ hfA hfC)
    (toSmallSingularPair_comp_smallSingularPairMap _ _ _ _ f hfA hfB hfC hfD _ _ _ _ _ _ hfB hfD)
    n m h
  have hsmall : inv (HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k)
        (M := M) (smallSingularPairToUnion hCA' hDB')) m) ≫
        HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (TopPair.toSSetPair.map
          (TopPair.ofInclusionMap (Set.union_subset_union hCA hDB)
            (Set.union_subset_union hCA' hDB') ⟨(hfA.union_union hfB).restrict,
              f.hom.continuous.restrict (hfA.union_union hfB)⟩
            fun _ hx ↦ hfC.union_union hfD hx))) m =
      HomologicalComplex.homologyMap (SSetPair.cochainComplexMap
          (smallSingularPairMap hCA hDB hCA' hDB' f hfA hfB hfC hfD)) m ≫
        inv (HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k)
          (M := M) (smallSingularPairToUnion hCA hDB)) m) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
    simp only [← HomologicalComplex.homologyMap_comp, ← SSetPair.cochainComplexMap_comp]
    rw [smallSingularPairToUnion_comp_ofInclusionMap]
  simp only [singularCohomologyPairMayerVietorisδ, TopPair.singularCohomologyMap_eq,
    Category.assoc, hsmall, reassoc_of% hnat]

end Naturality

variable {A' B' C' D' : Set X} (hCA' : C' ⊆ A') (hDB' : D' ⊆ B')
  (hA' : IsOpen ((↑) ⁻¹' A' : Set ↥(A' ∪ B'))) (hB' : IsOpen ((↑) ⁻¹' B' : Set ↥(A' ∪ B')))
  (hC' : IsOpen ((↑) ⁻¹' C' : Set ↥(C' ∪ D'))) (hD' : IsOpen ((↑) ⁻¹' D' : Set ↥(C' ∪ D')))
  (hAA' : A ⊆ A') (hBB' : B ⊆ B') (hCC' : C ⊆ C') (hDD' : D ⊆ D')

/-- **Naturality of the connecting morphism of the Mayer–Vietoris sequence of two pairs in
inclusions.** For `A ⊆ A'`, `B ⊆ B'`, `C ⊆ C'` and `D ⊆ D'`, the connecting morphisms commute with
the restrictions along the inclusions `(A ∩ B, C ∩ D) ⟶ (A' ∩ B', C' ∩ D')` and
`(A ∪ B, C ∪ D) ⟶ (A' ∪ B', C' ∪ D')`. -/
@[reassoc]
lemma singularCohomologyPairMayerVietorisδ_naturality_of_subset (n m : ℕ)
    (h : n + 1 = m := by lia) :
    singularCohomologyPairMayerVietorisδ R k M hCA' hDB' hA' hB' hC' hD' n m h ≫
        TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.union_subset_union hCA hDB)
          (Set.union_subset_union hCA' hDB') (ContinuousMap.inclusion
            (Set.union_subset_union hAA' hBB')) fun _ hx ↦ Set.union_subset_union hCC' hDD' hx) m =
      TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB)
          (Set.inter_subset_inter hCA' hDB') (ContinuousMap.inclusion
            (Set.inter_subset_inter hAA' hBB')) fun _ hx ↦ Set.inter_subset_inter hCC' hDD' hx) n ≫
        singularCohomologyPairMayerVietorisδ R k M hCA hDB hA hB hC hD n m h :=
  singularCohomologyPairMayerVietorisδ_naturality R k M hCA hDB hA hB hC hD hCA' hDB' hA' hB' hC'
    hD' (𝟙 X) hAA' hBB' hCC' hDD' n m h

/-! ### Mayer–Vietoris for the complements of two closed sets -/

section Compl

variable {R k M}

/-- **Mayer–Vietoris for the complements of two closed sets**, exactness at the middle term: if
`a ∈ Hⁿ(X, X ∖ S)` and `b ∈ Hⁿ(X, X ∖ T)` restrict to classes of `Hⁿ(X, X ∖ (S ∪ T))` with sum
zero, then `a` and `-b` are the restrictions of one class of `Hⁿ(X, X ∖ (S ∩ T))`. This is
`TopCat.singularCohomologyPairMayerVietoris_exact₂` for the pairs `(X, X ∖ S)` and
`(X, X ∖ T)`. -/
lemma exists_singularCohomologyComplRestrict_eq_of_add_eq_zero {S T : Set X} (hS : IsClosed S)
    (hT : IsClosed T) {n : ℕ} (a : (TopPair.ofSubset Sᶜ).singularCohomology R k M n)
    (b : (TopPair.ofSubset Tᶜ).singularCohomology R k M n)
    (h : singularCohomologyComplRestrict R k M Set.subset_union_left n a +
      singularCohomologyComplRestrict R k M Set.subset_union_right n b = 0) :
    ∃ z : (TopPair.ofSubset (S ∩ T)ᶜ).singularCohomology R k M n,
      singularCohomologyComplRestrict R k M Set.inter_subset_left n z = a ∧
        singularCohomologyComplRestrict R k M Set.inter_subset_right n z = -b := by
  -- identify the pairs `(univ, X ∖ S)`, `(univ, X ∖ T)` and their union and intersection with
  -- pairs of the form `(X, -)`
  have hCA : Sᶜ ⊆ (Set.univ : Set X) := Set.subset_univ _
  have hDB : Tᶜ ⊆ (Set.univ : Set X) := Set.subset_univ _
  let eC := TopPair.ofInclusionIsoOfSubset hCA Set.mem_univ (s₀ := Sᶜ) fun _ ↦ Iff.rfl
  let eD := TopPair.ofInclusionIsoOfSubset hDB Set.mem_univ (s₀ := Tᶜ) fun _ ↦ Iff.rfl
  let eU := TopPair.ofInclusionIsoOfSubset (Set.union_subset_union hCA hDB)
    (fun _ ↦ Or.inl (Set.mem_univ _)) (s₀ := (S ∩ T)ᶜ) fun _ ↦ by rw [Set.compl_inter]
  let eI := TopPair.ofInclusionIsoOfSubset (t := Set.univ ∩ Set.univ)
    (Set.inter_subset_inter hCA hDB) (fun _ ↦ ⟨Set.mem_univ _, Set.mem_univ _⟩)
    (s₀ := (S ∪ T)ᶜ) fun _ ↦ by rw [Set.compl_union]
  have hiA : _ ≫ eC.hom = eI.hom ≫ _ :=
    TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ Set.inter_subset_left
      (fun _ hx ↦ Set.inter_subset_left hx) (mapsTo_id_compl Set.subset_union_left)
  have hiB : _ ≫ eD.hom = eI.hom ≫ _ :=
    TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ Set.inter_subset_right
      (fun _ hx ↦ Set.inter_subset_right hx) (mapsTo_id_compl Set.subset_union_right)
  have hjA : _ ≫ eU.hom = eC.hom ≫ _ :=
    TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ Set.subset_union_left
      (fun _ hx ↦ Set.subset_union_left hx) (mapsTo_id_compl Set.inter_subset_left)
  have hjB : _ ≫ eU.hom = eD.hom ≫ _ :=
    TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ Set.subset_union_right
      (fun _ hx ↦ Set.subset_union_right hx) (mapsTo_id_compl Set.inter_subset_right)
  -- the four squares, evaluated at cohomology classes
  have hsq {P Q P' Q' : TopPair.{w}} {f : P ⟶ Q} {g : Q ⟶ Q'} {f' : P ⟶ P'} {g' : P' ⟶ Q'}
      (hfg : f ≫ g = f' ≫ g') (y : Q'.singularCohomology R k M n) :
      TopPair.singularCohomologyMap f n (TopPair.singularCohomologyMap g n y) =
        TopPair.singularCohomologyMap f' n (TopPair.singularCohomologyMap g' n y) := by
    simp only [← TopPair.singularCohomologyMap_comp_apply, hfg]
  -- apply the Mayer–Vietoris sequence of the pairs `(univ, X ∖ S)` and `(univ, X ∖ T)`
  have hA : IsOpen ((↑) ⁻¹' (Set.univ : Set X) : Set ↥((Set.univ : Set X) ∪ Set.univ)) := by
    simp
  have hex := (ShortComplex.moduleCat_exact_iff _).1
    (singularCohomologyPairMayerVietoris_exact₂ R k M hCA hDB hA hA
      (hS.isOpen_compl.preimage continuous_subtype_val)
      (hT.isOpen_compl.preimage continuous_subtype_val) n)
  let HC := (TopPair.ofInclusion hCA).singularCohomology R k M n
  let HD := (TopPair.ofInclusion hDB).singularCohomology R k M n
  have hinl (y : HC) := ConcreteCategory.congr_hom
    (inl_singularCohomologyPairMayerVietorisFromBiprod R k M hCA hDB n) y
  have hinr (y : HD) := ConcreteCategory.congr_hom
    (inr_singularCohomologyPairMayerVietorisFromBiprod R k M hCA hDB n) y
  have hfst := ConcreteCategory.congr_hom
    (singularCohomologyPairMayerVietorisToBiprod_fst R k M hCA hDB n)
  have hsnd := ConcreteCategory.congr_hom
    (singularCohomologyPairMayerVietorisToBiprod_snd R k M hCA hDB n)
  simp only [ConcreteCategory.comp_apply] at hinl hinr hfst hsnd
  obtain ⟨q, hq⟩ := hex ((biprod.inl : HC ⟶ HC ⊞ HD) (TopPair.singularCohomologyMap eC.hom n a) +
    (biprod.inr : HD ⟶ HC ⊞ HD) (-TopPair.singularCohomologyMap eD.hom n b)) (by
      dsimp only [HC, HD]
      simp only [map_add, map_neg, hinl, hinr, ModuleCat.hom_neg, LinearMap.neg_apply, neg_neg,
        hsq hiA, hsq hiB]
      rw [← map_add, h, map_zero])
  -- transport the solution back along the identifications of pairs
  let z := TopPair.singularCohomologyMap eU.inv n q
  have hz : TopPair.singularCohomologyMap eU.hom n z = q := by
    rw [← TopPair.singularCohomologyMap_comp_apply, eU.hom_inv_id,
      TopPair.singularCohomologyMap_id, ModuleCat.id_apply]
  have hinjC : Function.Injective (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      eC.hom n) :=
    ((TopPair.singularCohomologyFunctor R k M n).mapIso eC.op).toLinearEquiv.injective
  have hinjD : Function.Injective (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      eD.hom n) :=
    ((TopPair.singularCohomologyFunctor R k M n).mapIso eD.op).toLinearEquiv.injective
  refine ⟨z, hinjC ?_, hinjD ?_⟩
  · rw [← hsq hjA, hz, ← hfst, hq]
    simp [HC, HD]
  · rw [← hsq hjB, hz, ← hsnd, hq]
    simp [HC, HD]

end Compl

end TopCat

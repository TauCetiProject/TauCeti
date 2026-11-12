/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Sigma
public import TauCeti.AlgebraicTopology.Singular.Fibration.CellFiber
public import TauCeti.AlgebraicTopology.Singular.Fibration.Skeleton
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.Topology.CWComplex.Comparison
public import TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence

/-!
# Maps of Serre fibrations which are homology isomorphisms on the fibres

Let `p : E ⟶ B` and `p' : E' ⟶ B` be Serre fibrations and `f : E ⟶ E'` a map over `B`. If `f`
induces isomorphisms `Hq(p⁻¹(b); R) ≅ Hq(p'⁻¹(b); R)` on the homology of every fibre, then it
induces isomorphisms `Hₖ(E; R) ≅ Hₖ(E'; R)` (`TauCeti.TopCat.isIso_singularHomologyMap_of_commSq`).
In particular, if every fibre of a Serre fibration `p : E ⟶ B` has the `R`-homology of a point,
then `p` induces isomorphisms `Hₖ(E; R) ≅ Hₖ(B; R)`
(`TauCeti.TopCat.isIso_singularHomologyMap_of_isIso_fiber_to_point`). Only homology enters:
unlike `TauCeti.TopCat.isWeakHomotopyEquivalence_of_commSq`, nothing is assumed about homotopy
groups, and the base need not be simply connected. This is the comparison theorem for Serre
spectral sequences with an isomorphism on the first page, proved without assembling the spectral
sequences. For instance, a fibration over an arbitrary space with fibres that are acyclic modulo `2`
does not change homology modulo `2`.

Over a CW complex `B`, the proof filters the total spaces by the preimages `Eₙ = p⁻¹(Xⁿ)` of the
skeleta `Xⁿ` of `B`.

* Over the closed unit ball, the computation `Hq+n(P, P|Sⁿ⁻¹) ≅ Hq(P|0)` of
  `TauCeti.TopCat.singularHomologyPreimageSphereIso` is natural in maps of fibrations
  (`TauCeti.TopCat.singularHomologyPreimageSphereIso_hom_naturality`). Pulled back along the
  characteristic map of an `n`-cell `j`, the map induced by `f` on `Hq+n(Pⱼ, ∂Pⱼ)` is therefore an
  isomorphism when the fibre map over the centre of `j` is one on `Hq`; below degree `n` both groups
  vanish.
* `Hₖ(Eₙ, Eₙ₋₁)` is the coproduct of the `Hₖ(Pⱼ, ∂Pⱼ)` over the `n`-cells
  (`TauCeti.TopCat.isColimitCofanSingularHomologyPreimageSkeletonPair`), so `f` induces
  isomorphisms `Hₖ(Eₙ, Eₙ₋₁) ≅ Hₖ(E'ₙ, E'ₙ₋₁)`.
* By induction on `n`, starting from the empty `E₋₁`, the five lemma for the ambient space of a
  pair (`TopPair.isIso_homologyMap_fst_of_isIso`) gives isomorphisms `Hₖ(Eₙ) ≅ Hₖ(E'ₙ)`.
* `Hₖ(Eₙ) ⟶ Hₖ(E)` is an isomorphism once `n ≥ k + 2`, because `Hₘ(E, Eₙ) = 0` for `m < n`
  (`TauCeti.TopCat.isZero_singularHomology_preimage_skeletonLT`,
  `TopPair.isIso_homologyMap_fst_of_isZero`).

Over an arbitrary base, both fibrations are pulled back along a CW approximation of `B`
(`TauCeti.sigmaCWApproximationMap`). This does not change the fibres, and the projections of the
pullbacks to `E` and `E'` are weak homotopy equivalences
(`TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackSnd`), hence homology isomorphisms.

## Main results

* `TauCeti.TopCat.isIso_singularHomologyMap_of_commSq`: a map of Serre fibrations over `B` which
  is a homology isomorphism on every fibre is a homology isomorphism of the total spaces.
* `TauCeti.TopCat.isIso_singularHomologyMap_of_isIso_fiber_to_point`: a Serre fibration whose
  fibres have the homology of a point is a homology isomorphism.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 3.4 (the comparison theorem) and Section 5.1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 5.1 (the Serre spectral sequence).
-/

public section

noncomputable section

universe w v u

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

variable {E E' B : _root_.TopCat.{u}} {p : E ⟶ B} {p' : E' ⟶ B} {f : E ⟶ E'}

/-! ### Maps over the base -/

section Preimage

variable (hf : f ≫ p' = p)

/-- The map of pairs `(p⁻¹(T), p⁻¹(S)) ⟶ (p'⁻¹(T), p'⁻¹(S))` induced by a map `f` over `B`. -/
private def preimagePairMap {S T : Set B} (hST : S ⊆ T) :
    TopPair.ofInclusion (X := E) (preimage_mono (f := p) hST) ⟶
      TopPair.ofInclusion (X := E') (preimage_mono (f := p') hST) :=
  TopPair.ofHom (TopCat.Hom.preimageMap hf T) (TopCat.Hom.preimageMap hf S) rfl

end Preimage

/-! ### The cells -/

section Cells

variable [T2Space B] {C D : Set B} [RelCWComplex C D] (hf : f ≫ p' = p)

/-- The map `Pⱼ ⟶ P'ⱼ` of the pullbacks along the characteristic map of the `n`-cell `j` induced
by a map `f` over `B`. -/
private def cellDiskPullbackHom (n : ℕ) (j : cell C n) :
    (cellDiskPullbackPair p C n j).fst ⟶ (cellDiskPullbackPair p' C n j).fst :=
  _root_.TopCat.ofHom ⟨fun x ↦ ⟨(x.1.1, f x.1.2),
      x.2.trans (ConcreteCategory.congr_hom hf x.1.2).symm⟩,
    (by fun_prop : Continuous fun x : (cellDiskPullbackPair p C n j).fst ↦ (x.1.1, f x.1.2)
      ).subtype_mk _⟩

/-- The map of pairs `(Pⱼ, ∂Pⱼ) ⟶ (P'ⱼ, ∂P'ⱼ)` induced by a map `f` over `B`. -/
private def cellDiskPullbackPairHom (n : ℕ) (j : cell C n) :
    cellDiskPullbackPair p C n j ⟶ cellDiskPullbackPair p' C n j :=
  TopPair.ofSubsetMap (cellDiskPullbackHom hf n j) fun _ hx ↦ hx

/-- The map of pairs `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p'⁻¹(Xⁿ), p'⁻¹(Xⁿ⁻¹))` induced by a map `f` over
`B` commutes with the projections from the pullbacks along the characteristic maps of the cells. -/
private lemma cellDiskPullbackPairMap_comp_preimagePairMap (n : ℕ) (j : cell C n) :
    cellDiskPullbackPairMap p C n j ≫
        preimagePairMap hf (skeletonLT_subset_skeletonLT_succ C n) =
      cellDiskPullbackPairHom hf n j ≫ cellDiskPullbackPairMap p' C n j :=
  TopPair.hom_ext_of_fst _ (by
    ext x
    exact Subtype.ext (((TopCat.Hom.coe_preimageMap_apply hf _ _).trans
      (congrArg f (coe_cellDiskPullbackPairMap_fst_apply n j x))).trans
      ((coe_cellDiskPullbackPairMap_fst_apply (p := p') n j
        (TopPair.Hom.fst (cellDiskPullbackPairHom hf n j) x)).trans
        (congrArg (fun y : (cellDiskPullbackPair p' C n j).fst ↦ (y.1.2 : E'))
          (TopPair.ofSubsetMap_fst_apply (cellDiskPullbackHom hf n j) _ x))).symm))

variable (hp : serreFibrations p) (hp' : serreFibrations p') (R : Type u) [Ring R]
include hp hp'

omit [T2Space B] in
/-- Over a single `n`-cell, the map induced by `f` on `Hₘ(Pⱼ, ∂Pⱼ; R)` is an isomorphism if the map
of fibres over the centre of the cell is one on `Hq(-; R)` for `q + n = m`; below `n` both groups
vanish. -/
private lemma isIso_singularHomologyMap_cellDiskPullbackPairHom (sq : CommSq f p p' (𝟙 B))
    (n m : ℕ) (j : cell C n)
    (hfib : ∀ q, q + n = m → IsIso (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).map (sq.fiberMap (map n j 0)))) :
    IsIso (TopPair.singularHomologyMap
      (cellDiskPullbackPairHom (sq.w.trans (Category.comp_id p)) n j) (ModuleCat.of R R) m) := by
  have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
  -- The pullbacks are Serre fibrations over the disk, and `f` induces a map between them.
  have hP := mem_serreFibrations_pullbackFst hp (cellULiftMap C n j)
  have hP' := mem_serreFibrations_pullbackFst hp' (cellULiftMap C n j)
  rcases Nat.lt_or_ge m n with hm | hm
  · exact isIso_of_source_target_iso_zero _
      (isZero_singularHomology_preimage_sphere R hP (by simpa using hm)).isoZero
      (isZero_singularHomology_preimage_sphere R hP' (by simpa using hm)).isoZero
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hm
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)
  have hfP : cellDiskPullbackHom hf n j ≫ _root_.TopCat.pullbackFst (cellULiftMap C n j) p' =
      _root_.TopCat.pullbackFst (cellULiftMap C n j) p :=
    rfl
  -- The map of fibres over the centre of the disk.
  let g : _root_.TopCat.of (_root_.TopCat.pullbackFst (cellULiftMap C n j) p ⁻¹'
        {x | (x : ULift.{u} (Fin n → ℝ)) = 0}) ⟶
      _root_.TopCat.of (_root_.TopCat.pullbackFst (cellULiftMap C n j) p' ⁻¹'
        {x | (x : ULift.{u} (Fin n → ℝ)) = 0}) :=
    _root_.TopCat.ofHom ⟨fun x ↦ ⟨cellDiskPullbackHom hf n j x.1, x.2⟩,
      ((cellDiskPullbackHom hf n j).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  -- Through the identifications of the fibres over the centres, `g` is the fibre map of `f`.
  let e := _root_.TopCat.isoOfHomeo (X := _root_.TopCat.of
      (_root_.TopCat.pullbackFst (cellULiftMap C n j) p ⁻¹' {x | (x : ULift.{u} (Fin n → ℝ)) = 0}))
    (Y := p.fiber (map n j 0)) (cellDiskPullbackFiberHomeomorph p C n j)
  let e' := _root_.TopCat.isoOfHomeo (X := _root_.TopCat.of
      (_root_.TopCat.pullbackFst (cellULiftMap C n j) p' ⁻¹' {x | (x : ULift.{u} (Fin n → ℝ)) = 0}))
    (Y := p'.fiber (map n j 0)) (cellDiskPullbackFiberHomeomorph p' C n j)
  have hge : g ≫ e'.hom = e.hom ≫ sq.fiberMap (map n j 0) := by
    ext x
    exact (coe_cellDiskPullbackFiberHomeomorph_apply (p := p') n j (g x)).trans
      ((congrArg f (coe_cellDiskPullbackFiberHomeomorph_apply (p := p) n j x)).symm.trans
        (sq.fiberMap_apply_coe _ _).symm)
  have hHg : IsIso (H.map g) := by
    have : IsIso (H.map g ≫ H.map e'.hom) := by
      have h : H.map g ≫ H.map e'.hom = H.map e.hom ≫ H.map (sq.fiberMap (map n j 0)) :=
        (H.map_comp _ _).symm.trans ((congrArg H.map hge).trans (H.map_comp _ _))
      rw [h]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso H e.hom) (hfib q rfl)
    exact IsIso.of_isIso_comp_right (H.map g) (H.map e'.hom)
  have nat := singularHomologyPreimageSphereIso_hom_naturality R hP hP' hfP g (fun _ ↦ rfl) q
    (q + n) (by simp)
  have : TopPair.singularHomologyMap (cellDiskPullbackPairHom hf n j) (ModuleCat.of R R) (q + n) =
      (singularHomologyPreimageSphereIso R hP q (q + n) (by simp)).hom ≫ H.map g ≫
        (singularHomologyPreimageSphereIso R hP' q (q + n) (by simp)).inv := by
    rw [← reassoc_of% nat, Iso.hom_inv_id, Category.comp_id]
    -- The pair map of the cells is `TopPair.ofSubsetMap` of the same map, by definition.
    rfl
  rw [this]
  infer_instance

/-- **A map of Serre fibrations which is a homology isomorphism on the fibres is one on
consecutive stages of the skeletal filtration.** Let `p` and `p'` be Serre fibrations over `B`,
`C ⊆ B` a relative CW complex with skeleta `Xⁿ`, and `f` a map over `B` inducing isomorphisms on
`Hq(-; R)` of the fibres over the centres of the `n`-cells, for `q + n = m`. Then `f` induces an
isomorphism `Hₘ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) ≅ Hₘ(p'⁻¹(Xⁿ), p'⁻¹(Xⁿ⁻¹); R)`. -/
private lemma isIso_singularHomologyMap_preimagePairMap (sq : CommSq f p p' (𝟙 B)) (n m : ℕ)
    (hfib : ∀ j : cell C n, ∀ q, q + n = m → IsIso (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).map (sq.fiberMap (map n j 0)))) :
    IsIso (TopPair.singularHomologyMap (preimagePairMap (sq.w.trans (Category.comp_id p))
      (skeletonLT_subset_skeletonLT_succ C n)) (ModuleCat.of R R) m) := by
  have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
  have hc := isColimitCofanSingularHomologyPreimageSkeletonPair C hp R n m
  have hc' := isColimitCofanSingularHomologyPreimageSkeletonPair C hp' R n m
  have := fun j ↦ isIso_singularHomologyMap_cellDiskPullbackPairHom hp hp' R sq n m j (hfib j)
  -- The induced map is the isomorphism between the two coproducts given by the cells.
  let φ := hc.coconePointsIsoOfNatIso hc' (Discrete.natIso fun j ↦ asIso
    (TopPair.singularHomologyMap (cellDiskPullbackPairHom hf n j.as) (ModuleCat.of R R) m))
  have : TopPair.singularHomologyMap (preimagePairMap hf (skeletonLT_subset_skeletonLT_succ C n))
      (ModuleCat.of R R) m = φ.hom := hc.hom_ext fun ⟨j⟩ ↦ by
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    simp only [Cofan.mk_pt, Cofan.mk_ι_app, Discrete.natIso_hom_app, asIso_hom]
    rw [← TopPair.singularHomologyMap_comp, cellDiskPullbackPairMap_comp_preimagePairMap,
      TopPair.singularHomologyMap_comp]
  rw [this]
  infer_instance

end Cells

/-! ### The skeleta and the total space -/

section Skeleta

variable [T2Space B] {C : Set B} [CWComplex C] (hp : serreFibrations p)
  (hp' : serreFibrations p') (R : Type u) [Ring R] (sq : CommSq f p p' (𝟙 B))
include hp hp'

/-- A map of Serre fibrations which is a homology isomorphism on the fibres is one over every
skeleton. -/
private lemma isIso_singularHomologyMap_preimageMap_skeletonLT
    (hfib : ∀ b ∈ C, ∀ q, IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R)
      q).obj (ModuleCat.of R R)).map (sq.fiberMap b))) :
    ∀ (n k : ℕ), IsIso (SSet.homologyMap (_root_.TopCat.toSSet.map (TopCat.Hom.preimageMap
      (sq.w.trans (Category.comp_id p)) (skeletonLT C n : Set B))) (ModuleCat.of R R) k)
  | 0, k => by
    -- Over the empty `(-1)`-skeleton both spaces are empty.
    have hD : (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B) = ∅ := CWComplex.skeletonLT_zero_eq_empty
    have h₀ : IsEmpty (p ⁻¹' (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B)) := by
      rw [hD, preimage_empty]
      infer_instance
    have h₀' : IsEmpty (p' ⁻¹' (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B)) := by
      rw [hD, preimage_empty]
      infer_instance
    have : IsIso (TopCat.Hom.preimageMap (sq.w.trans (Category.comp_id p))
        (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B)) :=
      (_root_.TopCat.isIso_iff_isHomeomorph _).2
        ⟨by fun_prop, fun _ _ ↦ by simp [Set.eq_empty_of_isEmpty],
          ⟨fun x ↦ h₀.elim x, fun y ↦ h₀'.elim y⟩⟩
    exact Functor.map_isIso ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)) _
  | n + 1, k => by
    have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
    -- The map of pairs of consecutive stages is an isomorphism in every degree.
    have hrel (m : ℕ) : IsIso (TopPair.singularHomologyMap
        (preimagePairMap hf (skeletonLT_subset_skeletonLT_succ C n)) (ModuleCat.of R R) m) :=
      isIso_singularHomologyMap_preimagePairMap hp hp' R sq n m fun j q _ ↦
        hfib _ (closedCell_subset_complex n j ⟨0, mem_closedBall_self zero_le_one, rfl⟩) q
    exact TopPair.isIso_homologyMap_fst_of_isIso (ModuleCat.of R R)
      (preimagePairMap hf (skeletonLT_subset_skeletonLT_succ C n)) k inferInstance
      (isIso_singularHomologyMap_preimageMap_skeletonLT hfib n k) (hrel k)
      fun m _ ↦ @IsIso.mono_of_iso _ _ _ _ _
        (isIso_singularHomologyMap_preimageMap_skeletonLT hfib n m)

/-- **A map of Serre fibrations which is a homology isomorphism on the fibres is one over a CW
complex in the base.** Let `p : E ⟶ B` and `p' : E' ⟶ B` be Serre fibrations, `f : E ⟶ E'` a map
over `B` and `C ⊆ B` a CW complex. If for every `b ∈ C` the map of fibres `p⁻¹(b) ⟶ p'⁻¹(b)`
induces isomorphisms on `Hq(-; R)` in every degree, then `f` induces isomorphisms
`Hₖ(p⁻¹(C); R) ≅ Hₖ(p'⁻¹(C); R)`. -/
private theorem isIso_singularHomologyMap_preimage_of_commSq
    (hfib : ∀ b ∈ C, ∀ q, IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R)
      q).obj (ModuleCat.of R R)).map (sq.fiberMap b))) (k : ℕ) :
    IsIso (SSet.homologyMap (_root_.TopCat.toSSet.map
      (TopCat.Hom.preimageMap (sq.w.trans (Category.comp_id p)) C)) (ModuleCat.of R R) k) := by
  have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
  -- `Hₖ(p⁻¹(Xᵏ⁺¹)) ⟶ Hₖ(p⁻¹(C))` is an isomorphism, since `Hₘ(p⁻¹(C), p⁻¹(Xᵏ⁺¹)) = 0` for
  -- `m ≤ k + 1`, and likewise for `p'`.
  have hS := isIso_singularHomologyMap_preimageMap_skeletonLT hp hp' R sq hfib (k + 1 + 1) k
  rw [Nat.cast_succ (k + 1)] at hS
  have : IsIso (SSet.homologyMap (_root_.TopCat.toSSet.map
      (TopCat.Hom.preimageMap hf (skeletonLT C ⊤ : Set B))) (ModuleCat.of R R) k) :=
    TopPair.isIso_homologyMap_fst_of_isZero (ModuleCat.of R R)
      (preimagePairMap hf (skeletonLT_mono (C := C) (le_top : ((k + 1 : ℕ) : ℕ∞) + 1 ≤ ⊤)))
      (isZero_singularHomology_preimage_skeletonLT hp R le_top (by lia))
      (isZero_singularHomology_preimage_skeletonLT hp R le_top (by lia))
      (isZero_singularHomology_preimage_skeletonLT hp' R le_top (by lia))
      (isZero_singularHomology_preimage_skeletonLT hp' R le_top (by lia)) hS
  rw [skeletonLT_top] at this
  exact this

end Skeleta

/-! ### Over a CW complex -/

section Base

variable [T2Space B] [CWComplex (univ : Set B)] (hp : serreFibrations p)
  (hp' : serreFibrations p') (R : Type u) [Ring R]
include hp hp'

/-- A map of Serre fibrations over a CW complex which is a homology isomorphism on the fibres is
a homology isomorphism. -/
private theorem isIso_singularHomologyMap_of_commSq_of_cwComplex (sq : CommSq f p p' (𝟙 B))
    (hfib : ∀ b q, IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).map (sq.fiberMap b))) (k : ℕ) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).map f) := by
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)
  have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
  have h := isIso_singularHomologyMap_preimage_of_commSq (C := univ) hp hp' R sq
    (fun b _ ↦ hfib b) k
  -- The parts of the total spaces over the whole base are the total spaces.
  have hι (X : _root_.TopCat.{u}) (q : X ⟶ B) :
      IsIso (_root_.TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        _root_.TopCat.of (q ⁻¹' univ) ⟶ X) :=
    (_root_.TopCat.isIso_iff_isHomeomorph _).2
      ⟨continuous_subtype_val, (isOpen_univ.preimage q.hom.continuous).isOpenMap_subtype_val,
        Subtype.val_injective, fun x ↦ ⟨⟨x, trivial⟩, rfl⟩⟩
  have hsq : H.map (_root_.TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        _root_.TopCat.of (p ⁻¹' univ) ⟶ E) ≫ H.map f =
      H.map (TopCat.Hom.preimageMap hf univ) ≫
        H.map (_root_.TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
          _root_.TopCat.of (p' ⁻¹' univ) ⟶ E') := by
    have hcomm : (_root_.TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
          _root_.TopCat.of (p ⁻¹' univ) ⟶ E) ≫ f =
        TopCat.Hom.preimageMap hf univ ≫
          (_root_.TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
            _root_.TopCat.of (p' ⁻¹' univ) ⟶ E') :=
      rfl
    exact (H.map_comp _ _).symm.trans ((congrArg H.map hcomm).trans (H.map_comp _ _))
  have := hι E p
  have := hι E' p'
  have : IsIso (H.map (_root_.TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      _root_.TopCat.of (p ⁻¹' univ) ⟶ E) ≫ H.map f) := by
    rw [hsq]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h inferInstance
  exact IsIso.of_isIso_comp_left
    (H.map (_root_.TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      _root_.TopCat.of (p ⁻¹' univ) ⟶ E)) (H.map f)

end Base

/-! ### Over an arbitrary base -/

section Arbitrary

variable (hp : serreFibrations p) (hp' : serreFibrations p') (R : Type u) [Ring R]
include hp hp'

/-- **A map of Serre fibrations which is a homology isomorphism on the fibres is a homology
isomorphism.** Let `p : E ⟶ B` and `p' : E' ⟶ B` be Serre fibrations and `f : E ⟶ E'` a map over
`B`. If for every `b : B` the map of fibres `p⁻¹(b) ⟶ p'⁻¹(b)` induces isomorphisms on `Hq(-; R)`
in every degree, then `f` induces isomorphisms `Hₖ(E; R) ≅ Hₖ(E'; R)`. This is the homological
counterpart of `TauCeti.TopCat.isWeakHomotopyEquivalence_of_commSq`.

Over a CW complex this is proved by induction over the skeleta; in general, both fibrations are
pulled back along a CW approximation of `B`, which changes neither the fibres nor, up to weak
homotopy equivalence, the total spaces. -/
theorem isIso_singularHomologyMap_of_commSq (sq : CommSq f p p' (𝟙 B))
    (hfib : ∀ b q, IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).map (sq.fiberMap b))) (k : ℕ) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).map f) := by
  have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
  -- A CW complex `C` with a weak homotopy equivalence `g : C ⟶ B`.
  obtain ⟨Y, _, _, C, _, ⟨h⟩⟩ := (cwType_sigmaCWApproximation B).exists_homotopyEquiv
  let _ : CWComplex (univ : Set C) := cwComplexUniv C
  let g : _root_.TopCat.of C ⟶ B :=
    _root_.TopCat.ofHom h.symm.toFun ≫ sigmaCWApproximationMap B
  have hg : g.hom.IsWeakHomotopyEquivalence :=
    (isWeakHomotopyEquivalence_sigmaCWApproximationMap B).comp
      h.symm.isWeakHomotopyEquivalence
  -- The map of the pulled-back fibrations induced by `f`.
  let fP : _root_.TopCat.of {x : _root_.TopCat.of C × E // g x.1 = p x.2} ⟶
      _root_.TopCat.of {x : _root_.TopCat.of C × E' // g x.1 = p' x.2} :=
    _root_.TopCat.ofHom ⟨fun x ↦ ⟨(x.1.1, f x.1.2),
        x.2.trans (ConcreteCategory.congr_hom hf x.1.2).symm⟩,
      (by fun_prop : Continuous fun x : {x : _root_.TopCat.of C × E // g x.1 = p x.2} ↦
        (x.1.1, f x.1.2)).subtype_mk _⟩
  let sqP : CommSq fP (_root_.TopCat.pullbackFst g p) (_root_.TopCat.pullbackFst g p')
      (𝟙 _) := ⟨rfl⟩
  have hP := isIso_singularHomologyMap_of_commSq_of_cwComplex
    (mem_serreFibrations_pullbackFst hp g) (mem_serreFibrations_pullbackFst hp' g) R sqP
    (fun b q ↦ ?_) k
  · -- On total spaces, the projections from the pullbacks are weak homotopy equivalences.
    let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)
    have h₁ := (isWeakHomotopyEquivalence_pullbackSnd hp hg).isIso_singularHomologyMap
      (ModuleCat.of R R) k
    have h₂ := (isWeakHomotopyEquivalence_pullbackSnd hp' hg).isIso_singularHomologyMap
      (ModuleCat.of R R) k
    have hcomm : fP ≫ _root_.TopCat.pullbackSnd g p' = _root_.TopCat.pullbackSnd g p ≫ f := rfl
    have : IsIso (H.map (_root_.TopCat.pullbackSnd g p) ≫ H.map f) := by
      rw [(H.map_comp _ _).symm.trans ((congrArg H.map hcomm).symm.trans (H.map_comp _ _))]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hP h₂
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h₁ this
  · -- On fibres, the pullbacks have the fibres of `p` and `p'`.
    let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)
    have hcomm : sqP.fiberMap b ≫ (p'.fiberPullbackFstIso g b).hom =
        (p.fiberPullbackFstIso g b).hom ≫ sq.fiberMap (g b) := by
      ext x
      exact (TopCat.Hom.fiberPullbackFstIso_hom_apply_coe p' g b _).trans
        ((congrArg (fun y : {x : _root_.TopCat.of C × E' // g x.1 = p' x.2} ↦ y.1.2)
          (sqP.fiberMap_apply_coe b x)).trans
        ((congrArg f (TopCat.Hom.fiberPullbackFstIso_hom_apply_coe p g b x)).symm.trans
          (sq.fiberMap_apply_coe _ _).symm))
    have : IsIso (H.map (sqP.fiberMap b) ≫ H.map (p'.fiberPullbackFstIso g b).hom) := by
      rw [(H.map_comp _ _).symm.trans ((congrArg H.map hcomm).trans (H.map_comp _ _))]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ (H.mapIso (p.fiberPullbackFstIso g b)).isIso_hom
        (hfib (g b) q)
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
      (H.mapIso (p'.fiberPullbackFstIso g b)).isIso_hom this

omit hp' in
/-- **A Serre fibration whose fibres have the homology of a point is a homology isomorphism.** Let
`p : E ⟶ B` be a Serre fibration such that, for every
`b : B`, the map from the fibre `p⁻¹(b)` to a point induces isomorphisms on `Hq(-; R)` in every
degree. Then `p` induces isomorphisms `Hₖ(E; R) ≅ Hₖ(B; R)`. -/
theorem isIso_singularHomologyMap_of_isIso_fiber_to_point
    (hfib : ∀ b q, IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).map (_root_.TopCat.isTerminalPUnit.from (p.fiber b)))) (k : ℕ) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).map p) := by
  let sq : CommSq p p (𝟙 B) (𝟙 B) := ⟨rfl⟩
  refine isIso_singularHomologyMap_of_commSq hp (MorphismProperty.id_mem _ B) R sq
    (fun b q ↦ ?_) k
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)
  -- The fibre of the identity over `b` is a point.
  let F := TopCat.Hom.fiber (𝟙 B) ((𝟙 B) b)
  let t := _root_.TopCat.isTerminalPUnit.from F
  have : Unique F := ⟨⟨⟨b, rfl⟩⟩, fun x ↦ Subtype.ext x.2⟩
  have ht : IsIso t := by
    rw [_root_.TopCat.isTerminalPUnit.hom_ext t
      (_root_.TopCat.isoOfHomeo (Homeomorph.homeomorphOfUnique F PUnit)).hom]
    infer_instance
  -- The map from the fibre of `p` to a point factors through the fibre map.
  have hfac : sq.fiberMap b ≫ t = _root_.TopCat.isTerminalPUnit.from (p.fiber b) :=
    _root_.TopCat.isTerminalPUnit.hom_ext _ _
  have : IsIso (H.map (sq.fiberMap b) ≫ H.map t) := by
    rw [(H.map_comp _ _).symm.trans (congrArg H.map hfac)]
    exact hfib b q
  exact IsIso.of_isIso_comp_right _ (H.map t)

end Arbitrary

end TopCat

end TauCeti

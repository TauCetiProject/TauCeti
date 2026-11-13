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

Let `p : E ⟶ B` and `p' : E' ⟶ B'` be Serre fibrations and `f : E ⟶ E'` a map over a weak
homotopy equivalence `g : B ⟶ B'`. If `f` induces isomorphisms `Hq(p⁻¹(b); R) ≅ Hq(p'⁻¹(g b); R)`
on the homology of every fibre for `q ≤ k`, then it induces an isomorphism `Hₖ(E; R) ≅ Hₖ(E'; R)`
(`TauCeti.TopCat.isIso_singularHomologyMap_of_commSq`). In particular, if every fibre of a Serre
fibration `p : E ⟶ B` has the `R`-homology of a point in degrees `q ≤ k`, then `p` induces an
isomorphism `Hₖ(E; R) ≅ Hₖ(B; R)`
(`TauCeti.TopCat.isIso_singularHomologyMap_of_isIso_fiber_to_point`). Only homology enters:
unlike `TauCeti.TopCat.isWeakHomotopyEquivalence_of_commSq`, nothing is assumed about homotopy
groups, and the base need not be simply connected. This is the comparison theorem for Serre
spectral sequences with an isomorphism on the first page, proved without assembling the spectral
sequences. For instance, a fibration over an arbitrary space with fibres that are acyclic modulo `2`
does not change homology modulo `2`.

Over a CW complex `B` and a map `f` over `B`, the proof filters the total spaces by the preimages
`Eₙ = p⁻¹(Xⁿ)` of the skeleta `Xⁿ` of `B`, indexed so that `Xⁿ = skeletonLT _ (n + 1)` is the
union of the cells of dimension at most `n`.

* Over the closed unit ball, the computation `Hq+n(P, P|Sⁿ⁻¹) ≅ Hq(P|0)` of
  `TauCeti.TopCat.singularHomologyPreimageSphereIso` is natural in maps of fibrations
  (`TauCeti.TopCat.singularHomologyPreimageSphereIso_hom_naturality`). Pulled back along the
  characteristic map of an `n`-cell `j`, the map induced by `f` on `Hq+n(Pⱼ, ∂Pⱼ)` is therefore an
  isomorphism when the fibre map over the centre of `j` is one on `Hq`; below degree `n` both groups
  vanish.
* `Hₖ(Eₙ, Eₙ₋₁)` is the coproduct of the `Hₖ(Pⱼ, ∂Pⱼ)` over the `n`-cells
  (`TauCeti.TopCat.isColimitCofanSingularHomologyPreimageSkeletonPair`), so `f` induces
  isomorphisms `Hₘ(Eₙ, Eₙ₋₁) ≅ Hₘ(E'ₙ, E'ₙ₋₁)` for `m ≤ k + n`.
* By induction on `n`, `f` induces isomorphisms `Hₘ(Eₙ) ≅ Hₘ(E'ₙ)` for `m ≤ k`. Over the
  `0`-skeleton, `E₋₁` is empty and `Hₘ(E₀) ≅ Hₘ(E₀, E₋₁)`; afterwards the five lemma for the
  ambient space of a pair (`TopPair.isIso_homologyMap_fst_of_isIso`) applies.
* `Hₖ(Eₙ) ⟶ Hₖ(E)` is an isomorphism once `n ≥ k + 1`, because `Hₘ(E, Eₙ) = 0` for `m ≤ n`
  (`TauCeti.TopCat.isZero_singularHomology_preimage_skeletonLT`), so the isomorphism
  `Hₖ(Eₖ₊₁) ≅ Hₖ(E'ₖ₊₁)` transfers to `Hₖ(E) ≅ Hₖ(E')` (`TopPair.isIso_homologyMap_fst_of_isZero`).

Over an arbitrary base, both fibrations are pulled back along a CW approximation of `B`
(`TauCeti.sigmaCWApproximationMap`). This does not change the fibres, and the projections of the
pullbacks to `E` and `E'` are weak homotopy equivalences
(`TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackSnd`), hence homology isomorphisms. Finally, a
map over a weak homotopy equivalence `g : B ⟶ B'` factors as a map over `B` into the base change of
`p'` along `g`, followed by the projection to `E'`, which is again a weak homotopy equivalence.

## Main results

* `TauCeti.TopCat.isIso_singularHomologyMap_of_commSq`: a map of Serre fibrations over a weak
  homotopy equivalence which is a homology isomorphism on every fibre in degrees at most `k` is
  one of the total spaces in degree `k`.
* `TauCeti.TopCat.isIso_singularHomologyMap_of_isIso_fiber_to_point`: a Serre fibration whose
  fibres have the homology of a point in degrees at most `k` is a homology isomorphism in
  degree `k`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 3.4 (the comparison theorem) and Section 5.1.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1, Section 1.1 (the homology spectral sequence).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Proposition 4.13 (CW approximation).
-/

public section

noncomputable section

universe w v u

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

variable {E E' B : _root_.TopCat.{u}} {p : E ⟶ B} {p' : E' ⟶ B} {f : E ⟶ E'}

/-! ### The cells -/

section Cells

variable [T2Space B] {C D : Set B} [RelCWComplex C D]
  (hp : serreFibrations p) (hp' : serreFibrations p') (R : Type u) [Ring R]
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
  have hfP := _root_.TopCat.pullbackMapOfCompEq_comp_pullbackFst (cellULiftMap C n j) hf
  -- The map of fibres over the centre of the disk.
  let g := TopCat.Hom.preimageMap _ hfP {x | (x : ULift.{u} (Fin n → ℝ)) = 0}
  -- Through the identifications of the fibres over the centres, `g` is the fibre map of `f`.
  let e := _root_.TopCat.isoOfHomeo (X := _root_.TopCat.of
      (_root_.TopCat.pullbackFst (cellULiftMap C n j) p ⁻¹' {x | (x : ULift.{u} (Fin n → ℝ)) = 0}))
    (Y := p.fiber (map n j 0)) (cellDiskPullbackFiberHomeomorph p C n j)
  let e' := _root_.TopCat.isoOfHomeo (X := _root_.TopCat.of
      (_root_.TopCat.pullbackFst (cellULiftMap C n j) p' ⁻¹' {x | (x : ULift.{u} (Fin n → ℝ)) = 0}))
    (Y := p'.fiber ((𝟙 B : B ⟶ B) (map n j 0))) (cellDiskPullbackFiberHomeomorph p' C n j)
  have hge : g ≫ e'.hom = e.hom ≫ sq.fiberMap (map n j 0) := by
    ext x
    -- Both sides send `x` to `f x.1.1.2`.
    calc (cellDiskPullbackFiberHomeomorph p' C n j (g x) : E') = (g x).1.1.2 :=
          coe_cellDiskPullbackFiberHomeomorph_apply n j (g x)
      _ = (_root_.TopCat.pullbackMapOfCompEq (cellULiftMap C n j) hf x.1).1.2 := by
          rw [TopCat.Hom.coe_preimageMap_apply]
      _ = f x.1.1.2 := by rw [_root_.TopCat.coe_pullbackMapOfCompEq_apply]
      _ = f (cellDiskPullbackFiberHomeomorph p C n j x) :=
          congrArg f (coe_cellDiskPullbackFiberHomeomorph_apply n j x).symm
      _ = sq.fiberMap (map n j 0) (cellDiskPullbackFiberHomeomorph p C n j x) :=
          (sq.fiberMap_apply_coe _ _).symm
  have hHg : IsIso (H.map g) := by
    have := hfib q rfl
    rw [← isIso_comp_right_iff _ (H.map e'.hom), ← H.map_comp, hge, H.map_comp]
    infer_instance
  have nat := singularHomologyPreimageSphereIso_hom_naturality R hP hP' hfP g
    (TopCat.Hom.coe_preimageMap_apply _ hfP _) q (q + n) (by simp)
  have : TopPair.singularHomologyMap (cellDiskPullbackPairHom hf n j) (ModuleCat.of R R) (q + n) =
      (singularHomologyPreimageSphereIso R hP q (q + n) (by simp)).hom ≫ H.map g ≫
        (singularHomologyPreimageSphereIso R hP' q (q + n) (by simp)).inv := by
    -- The pair map of the cells is `TopPair.ofSubsetMap` of the same map, by definition.
    rw [← reassoc_of% nat, Iso.hom_inv_id, Category.comp_id]
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
    IsIso (TopPair.singularHomologyMap (TopCat.Hom.preimagePairMap f (sq.w.trans
      (Category.comp_id p)) (skeletonLT_subset_skeletonLT_succ C n)) (ModuleCat.of R R) m) := by
  have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
  have hc := isColimitCofanSingularHomologyPreimageSkeletonPair C hp R n m
  have hc' := isColimitCofanSingularHomologyPreimageSkeletonPair C hp' R n m
  have := fun j ↦ isIso_singularHomologyMap_cellDiskPullbackPairHom hp hp' R sq n m j (hfib j)
  -- The induced map is the isomorphism between the two coproducts given by the cells.
  let φ := hc.coconePointsIsoOfNatIso hc' (Discrete.natIso fun j ↦ asIso
    (TopPair.singularHomologyMap (cellDiskPullbackPairHom hf n j.as) (ModuleCat.of R R) m))
  have : TopPair.singularHomologyMap
      (TopCat.Hom.preimagePairMap f hf (skeletonLT_subset_skeletonLT_succ C n))
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

/-- A map of Serre fibrations which is a homology isomorphism on the fibres in degrees at most `k`
is one over every skeleton, in degrees at most `k`. -/
private lemma isIso_singularHomologyMap_preimageMap_skeletonLT {k : ℕ}
    (hfib : ∀ b ∈ C, ∀ q ≤ k, IsIso (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).map (sq.fiberMap b))) :
    ∀ (n m : ℕ), m ≤ k → IsIso (SSet.homologyMap (_root_.TopCat.toSSet.map (f.preimageMap
      (sq.w.trans (Category.comp_id p)) (skeletonLT C n : Set B))) (ModuleCat.of R R) m)
  | 0, m, _ => by
    -- Over the empty `(-1)`-skeleton both spaces are empty.
    have hD : (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B) = ∅ := CWComplex.skeletonLT_zero_eq_empty
    have h₀ : IsEmpty (p ⁻¹' (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B)) := by
      rw [hD, preimage_empty]
      infer_instance
    have h₀' : IsEmpty (p' ⁻¹' (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B)) := by
      rw [hD, preimage_empty]
      infer_instance
    have : IsIso (f.preimageMap (sq.w.trans (Category.comp_id p))
        (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B)) :=
      (_root_.TopCat.isIso_iff_isHomeomorph _).2
        ⟨by fun_prop, fun _ _ ↦ by simp [Set.eq_empty_of_isEmpty],
          ⟨fun x ↦ h₀.elim x, fun y ↦ h₀'.elim y⟩⟩
    exact Functor.map_isIso ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
      (ModuleCat.of R R)) _
  | n + 1, m, hm => by
    have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
    have hST := skeletonLT_subset_skeletonLT_succ C n
    -- The map of pairs of consecutive stages is an isomorphism in degrees at most `k + n`.
    have hrel (m' : ℕ) (hm' : m' ≤ k + n) : IsIso (TopPair.singularHomologyMap
        (TopCat.Hom.preimagePairMap f hf hST) (ModuleCat.of R R) m') :=
      isIso_singularHomologyMap_preimagePairMap hp hp' R sq n m' fun j q hq ↦
        hfib _ (closedCell_subset_complex n j ⟨0, mem_closedBall_self zero_le_one, rfl⟩) q
          (by lia)
    have ih := isIso_singularHomologyMap_preimageMap_skeletonLT hfib n
    have key : IsIso (SSet.homologyMap (_root_.TopCat.toSSet.map
        (TopPair.Hom.fst (TopCat.Hom.preimagePairMap f hf hST))) (ModuleCat.of R R) m) := by
      rcases n with _ | n
      · -- Over the `0`-skeleton, homology is relative homology modulo the empty preimage of the
        -- `(-1)`-skeleton.
        have hD : (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B) = ∅ := CWComplex.skeletonLT_zero_eq_empty
        have h₀ : IsEmpty (p ⁻¹' (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B)) := by
          rw [hD, preimage_empty]
          infer_instance
        have h₀' : IsEmpty (p' ⁻¹' (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B)) := by
          rw [hD, preimage_empty]
          infer_instance
        have hπ : IsIso (TopPair.singularHomologyπ
            (TopPair.ofInclusion (X := E) (preimage_mono (f := p) hST)) (ModuleCat.of R R) m) := by
          have : IsEmpty (TopPair.ofInclusion (X := E) (preimage_mono (f := p) hST)).snd := h₀
          infer_instance
        have hπ' : IsIso (TopPair.singularHomologyπ
            (TopPair.ofInclusion (X := E') (preimage_mono (f := p') hST))
            (ModuleCat.of R R) m) := by
          have : IsEmpty (TopPair.ofInclusion (X := E') (preimage_mono (f := p') hST)).snd := h₀'
          infer_instance
        have := hrel m (by lia)
        have : IsIso (SSet.homologyMap (_root_.TopCat.toSSet.map
            (TopPair.Hom.fst (TopCat.Hom.preimagePairMap f hf hST))) (ModuleCat.of R R) m ≫
              (TopPair.ofInclusion (X := E') (preimage_mono (f := p') hST)).singularHomologyπ
                (ModuleCat.of R R) m) := by
          rw [TopPair.singularHomologyπ_naturality]
          exact IsIso.comp_isIso' hπ inferInstance
        exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hπ' this
      · have hsnd (m' : ℕ) (hm' : m' ≤ k) : IsIso (SSet.homologyMap (_root_.TopCat.toSSet.map
            (TopPair.Hom.snd (TopCat.Hom.preimagePairMap f hf hST))) (ModuleCat.of R R) m') := by
          rw [TopCat.Hom.preimagePairMap_snd]
          exact ih m' hm'
        have := hrel (m + 1) (by lia)
        exact TopPair.isIso_homologyMap_fst_of_isIso (ModuleCat.of R R)
          (TopCat.Hom.preimagePairMap f hf hST) m inferInstance (hsnd m hm) (hrel m (by lia))
          fun m' _ ↦ by
            have := hsnd m' (by lia)
            infer_instance
    rw [TopCat.Hom.preimagePairMap_fst] at key
    exact key

/-- **A map of Serre fibrations which is a homology isomorphism on the fibres is one over a CW
complex in the base.** Let `p : E ⟶ B` and `p' : E' ⟶ B` be Serre fibrations, `f : E ⟶ E'` a map
over `B` and `C ⊆ B` a CW complex. If for every `b ∈ C` the map of fibres `p⁻¹(b) ⟶ p'⁻¹(b)`
induces isomorphisms on `Hq(-; R)` for `q ≤ k`, then `f` induces an isomorphism
`Hₖ(p⁻¹(C); R) ≅ Hₖ(p'⁻¹(C); R)`. -/
private theorem isIso_singularHomologyMap_preimage_of_commSq (k : ℕ)
    (hfib : ∀ b ∈ C, ∀ q ≤ k, IsIso (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).map (sq.fiberMap b))) :
    IsIso (SSet.homologyMap (_root_.TopCat.toSSet.map
      (f.preimageMap (sq.w.trans (Category.comp_id p)) C)) (ModuleCat.of R R) k) := by
  have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
  -- `Hₖ(p⁻¹(Xᵏ⁺¹)) ⟶ Hₖ(p⁻¹(C))` is an isomorphism, since `Hₘ(p⁻¹(C), p⁻¹(Xᵏ⁺¹)) = 0` for
  -- `m ≤ k + 1`, and likewise for `p'`.
  have hS := isIso_singularHomologyMap_preimageMap_skeletonLT hp hp' R sq hfib (k + 1 + 1) k le_rfl
  rw [Nat.cast_succ (k + 1)] at hS
  have hST := skeletonLT_mono (C := C) (le_top : ((k + 1 : ℕ) : ℕ∞) + 1 ≤ ⊤)
  have : IsIso (SSet.homologyMap (_root_.TopCat.toSSet.map
      (TopPair.Hom.fst (TopCat.Hom.preimagePairMap f hf hST))) (ModuleCat.of R R) k) :=
    TopPair.isIso_homologyMap_fst_of_isZero (ModuleCat.of R R)
      (TopCat.Hom.preimagePairMap f hf hST)
      (isZero_singularHomology_preimage_skeletonLT hp R le_top (by lia))
      (isZero_singularHomology_preimage_skeletonLT hp R le_top (by lia))
      (isZero_singularHomology_preimage_skeletonLT hp' R le_top (by lia))
      (isZero_singularHomology_preimage_skeletonLT hp' R le_top (by lia))
      (by rw [TopCat.Hom.preimagePairMap_snd]; exact hS)
  have h : IsIso (SSet.homologyMap (_root_.TopCat.toSSet.map
      (f.preimageMap hf (skeletonLT C ⊤ : Set B))) (ModuleCat.of R R) k) := by
    rwa [TopCat.Hom.preimagePairMap_fst] at this
  rw [skeletonLT_top] at h
  exact h

end Skeleta

/-! ### Over a CW complex -/

section Base

variable [T2Space B] [CWComplex (univ : Set B)] (hp : serreFibrations p)
  (hp' : serreFibrations p') (R : Type u) [Ring R]
include hp hp'

/-- A map of Serre fibrations over a CW complex which is a homology isomorphism on the fibres in
degrees at most `k` is one on the total spaces in degree `k`. -/
private theorem isIso_singularHomologyMap_of_commSq_of_cwComplex (sq : CommSq f p p' (𝟙 B))
    (k : ℕ) (hfib : ∀ b, ∀ q ≤ k, IsIso (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).map (sq.fiberMap b))) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).map f) := by
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)
  have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
  have h := isIso_singularHomologyMap_preimage_of_commSq (C := univ) hp hp' R sq k
    (fun b _ ↦ hfib b)
  -- The parts of the total spaces over the whole base are the total spaces.
  let ι (X : _root_.TopCat.{u}) (q : X ⟶ B) : _root_.TopCat.of (q ⁻¹' univ) ≅ X :=
    _root_.TopCat.isoOfHomeo (Homeomorph.Set.univ X)
  have hcomm : f.preimageMap hf univ ≫ (ι E' p').hom = (ι E p).hom ≫ f := by
    ext x
    exact f.coe_preimageMap_apply hf univ x
  rw [← isIso_comp_left_iff (H.map (ι E p).hom), ← H.map_comp, ← hcomm, H.map_comp]
  exact IsIso.comp_isIso' h inferInstance

end Base

/-! ### Over an arbitrary base -/

section Arbitrary

variable (hp : serreFibrations p) (hp' : serreFibrations p') (R : Type u) [Ring R]
include hp hp'

/-- A map over `B` of Serre fibrations over `B` which is a homology isomorphism on the fibres in
degrees at most `k` is one on the total spaces in degree `k`. -/
private theorem isIso_singularHomologyMap_of_commSq_id (sq : CommSq f p p' (𝟙 B)) (k : ℕ)
    (hfib : ∀ b, ∀ q ≤ k, IsIso (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).map (sq.fiberMap b))) :
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
  let sqP : CommSq (_root_.TopCat.pullbackMapOfCompEq g hf) (_root_.TopCat.pullbackFst g p)
      (_root_.TopCat.pullbackFst g p') (𝟙 _) :=
    ⟨(_root_.TopCat.pullbackMapOfCompEq_comp_pullbackFst g hf).trans (Category.comp_id _).symm⟩
  have hP := isIso_singularHomologyMap_of_commSq_of_cwComplex
    (mem_serreFibrations_pullbackFst hp g) (mem_serreFibrations_pullbackFst hp' g) R sqP k
    (fun b q hq ↦ ?_)
  · -- On total spaces, the projections from the pullbacks are weak homotopy equivalences.
    let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)
    have h₁ : IsIso (H.map (_root_.TopCat.pullbackSnd g p)) :=
      (isWeakHomotopyEquivalence_pullbackSnd hp hg).isIso_singularHomologyMap (ModuleCat.of R R) k
    have h₂ : IsIso (H.map (_root_.TopCat.pullbackSnd g p')) :=
      (isWeakHomotopyEquivalence_pullbackSnd hp' hg).isIso_singularHomologyMap (ModuleCat.of R R) k
    rw [← isIso_comp_left_iff (H.map (_root_.TopCat.pullbackSnd g p)), ← H.map_comp,
      ← _root_.TopCat.pullbackMapOfCompEq_comp_pullbackSnd g hf, H.map_comp]
    exact IsIso.comp_isIso' hP h₂
  · -- On fibres, the pullbacks have the fibres of `p` and `p'`.
    let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)
    -- Through the identifications of the fibres, the fibre map of the pullbacks is that of `f`.
    -- The fibre map of `sqP` lands over `(𝟙 _) b` rather than `b`, so `rw` cannot move `IsIso`
    -- across this square; compare the two maps as isomorphic arrows instead.
    have hcomm := (CommSq.mk (TopCat.Hom.fiberPullbackFstIso_hom_naturality g sq sqP b)).map H
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (Arrow.isoMk
      (H.mapIso (p.fiberPullbackFstIso g b)) (H.mapIso (p'.fiberPullbackFstIso g b))
      hcomm.w.symm)).2 (hfib (g b) q hq)

end Arbitrary

/-- **A map of Serre fibrations which is a homology isomorphism on the fibres is a homology
isomorphism.** Let `p : E ⟶ B` and `p' : E' ⟶ B'` be Serre fibrations and `f : E ⟶ E'` a map over
a weak homotopy equivalence `g : B ⟶ B'`. If for every `b : B` the map of fibres
`p⁻¹(b) ⟶ p'⁻¹(g b)` induces isomorphisms on `Hq(-; R)` for `q ≤ k`, then `f` induces an
isomorphism `Hₖ(E; R) ≅ Hₖ(E'; R)`. This is the homological counterpart of
`TauCeti.TopCat.isWeakHomotopyEquivalence_of_commSq`. -/
theorem isIso_singularHomologyMap_of_commSq {B' : _root_.TopCat.{u}} {p' : E' ⟶ B'} {g : B ⟶ B'}
    (hp : serreFibrations p) (hp' : serreFibrations p') (R : Type u) [Ring R]
    (sq : CommSq f p p' g) (hg : g.hom.IsWeakHomotopyEquivalence) (k : ℕ)
    (hfib : ∀ b, ∀ q ≤ k, IsIso (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).map (sq.fiberMap b))) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).map f) := by
  -- `f` factors through the base change `B ×_{B'} E'` of `p'` along `g`, by a map over `B`.
  let l : E ⟶ _root_.TopCat.of { x : B × E' // g x.1 = p' x.2 } :=
    PullbackCone.IsLimit.lift (_root_.TopCat.pullbackConeIsLimit g p') p f sq.w.symm
  have hl₁ : l ≫ _root_.TopCat.pullbackFst g p' = p :=
    PullbackCone.IsLimit.lift_fst _ _ _ _
  have hl₂ : l ≫ _root_.TopCat.pullbackSnd g p' = f :=
    PullbackCone.IsLimit.lift_snd _ _ _ _
  let sqL : CommSq l p (_root_.TopCat.pullbackFst g p') (𝟙 B) :=
    ⟨hl₁.trans (Category.comp_id p).symm⟩
  have hL := isIso_singularHomologyMap_of_commSq_id hp (mem_serreFibrations_pullbackFst hp' g) R
    sqL k (fun b q hq ↦ ?_)
  · -- The projection from the base change to `E'` is a weak homotopy equivalence.
    let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)
    have h₂ : IsIso (H.map (_root_.TopCat.pullbackSnd g p')) :=
      (isWeakHomotopyEquivalence_pullbackSnd hp' hg).isIso_singularHomologyMap (ModuleCat.of R R) k
    rw [← hl₂, H.map_comp]
    exact IsIso.comp_isIso' hL h₂
  · -- On fibres, `l` is the fibre map of `f`, through the identification of the fibres of the
    -- base change with those of `p'`.
    let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)
    have hcomm : sqL.fiberMap b ≫ (p'.fiberPullbackFstIso g b).hom = 𝟙 _ ≫ sq.fiberMap b := by
      ext x
      rw [Category.id_comp]
      -- The composite is typed over `(𝟙 B) b` rather than `b`, so `rw` cannot match it.
      erw [ConcreteCategory.comp_apply, TopCat.Hom.fiberPullbackFstIso_hom_apply_coe]
      rw [sq.fiberMap_apply_coe]
      exact (congrArg (fun y : _root_.TopCat.of { x : B × E' // g x.1 = p' x.2 } ↦ y.1.2)
        (sqL.fiberMap_apply_coe b x)).trans (ConcreteCategory.congr_hom hl₂ x.1)
    -- The fibre map of `sqL` lands over `(𝟙 B) b` rather than `b`, so compare the two maps as
    -- isomorphic arrows, as in `isIso_singularHomologyMap_of_commSq_id`.
    have hc := (CommSq.mk hcomm).map H
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (Arrow.isoMk
      (H.mapIso (Iso.refl _)) (H.mapIso (p'.fiberPullbackFstIso g b)) hc.w.symm)).2
      (hfib b q hq)

/-- **A Serre fibration whose fibres have the homology of a point is a homology isomorphism.** Let
`p : E ⟶ B` be a Serre fibration such that, for every `b : B`, the map from the fibre `p⁻¹(b)` to a
point induces isomorphisms on `Hq(-; R)` for `q ≤ k`. Then `p` induces an isomorphism
`Hₖ(E; R) ≅ Hₖ(B; R)`. -/
theorem isIso_singularHomologyMap_of_isIso_fiber_to_point (hp : serreFibrations p) (R : Type u)
    [Ring R] (k : ℕ)
    (hfib : ∀ b, ∀ q ≤ k, IsIso (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).map
        (_root_.TopCat.isTerminalPUnit.from (p.fiber b)))) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).map p) := by
  let sq : CommSq p p (𝟙 B) (𝟙 B) := ⟨rfl⟩
  refine isIso_singularHomologyMap_of_commSq hp (MorphismProperty.id_mem _ B) R sq
    ContinuousMap.IsWeakHomotopyEquivalence.id k (fun b q hq ↦ ?_)
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
  rw [← isIso_comp_right_iff _ (H.map t), ← H.map_comp, hfac]
  exact hfib b q hq

end TopCat

end TauCeti

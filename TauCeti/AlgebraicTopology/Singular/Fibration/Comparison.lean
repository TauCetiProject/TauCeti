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
public import TauCeti.AlgebraicTopology.Singular.SerreClass
public import TauCeti.CategoryTheory.Abelian.GrothendieckAxioms.ObjectProperty
public import TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence
import TauCeti.AlgebraicTopology.Singular.Contractible
import TauCeti.CategoryTheory.ObjectProperty.ArrowIso
import TauCeti.CategoryTheory.ObjectProperty.ColimitsOfShape
import TauCeti.AlgebraicTopology.Singular.Reduced

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

## Modulo a Serre class

The comparison theorem holds modulo a Serre class `P` of `R`-modules, as in Serre's theory of
classes of abelian groups. Let `Q ≤ P` be a property of `R`-modules closed under isomorphisms and
direct sums. If, for every fibre and every `q ≤ k`, the kernel and the cokernel of the map induced
on `Hq` lie in `Q`, then the map `Hₖ(E; R) ⟶ Hₖ(E'; R)` is an isomorphism modulo `P`
(`TauCeti.TopCat.isoModSerre_singularHomologyMap_of_commSq`). The class `Q` is needed because
the first page of the skeletal filtration is a direct sum over the cells of the base, and a Serre
class need not be closed under infinite direct sums: the groups killed by some power of an integer
`d ≥ 2` are a Serre class, but `⨁ₘ ℤ/dᵐ` is not killed by any power of `d`. The groups killed by
`dᵐ` for a fixed `m` are closed under direct sums (`CategoryTheory.ObjectProperty.isKilledBy`), and
are the class `Q` for that Serre class `P`; for a Serre class closed under direct sums, such as the
torsion groups, take `Q = P`. For the Serre class of zero modules, this is the comparison theorem
above.

The main application is to a Serre fibration whose total space is contractible, such as the
path-loop fibration `ΩX → PX → X`: if its fibres are path-connected with positive-degree homology
in `Q` up to degree `k`, then the homology of the base lies in `P` in the positive degrees up to
`k` (`TauCeti.TopCat.prop_singularHomology_of_contractibleSpace`). This is the step of Serre's
theory of classes that passes from the homology of a loop space to that of the space.

## Proof

Over a CW complex `B` and a map `f` over `B`, the proof filters the total spaces by the preimages
`Eₙ = p⁻¹(Xⁿ)` of the skeleta `Xⁿ` of `B`, indexed so that `Xⁿ = skeletonLT _ (n + 1)` is the
union of the cells of dimension at most `n`.

* `Hq+n(Eₙ, Eₙ₋₁)` is the direct sum of the homology `Hq(Fⱼ)` of the fibres over the centres of the
  `n`-cells `j`, naturally in maps over `B`
  (`TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma_hom_naturality`), and below
  degree `n` it vanishes. So `f` induces isomorphisms modulo `P` on `Hₘ(Eₙ, Eₙ₋₁)` for
  `m ≤ k + n`, because the kernel and the cokernel of a direct sum of maps are the direct sums of
  the kernels and of the cokernels (`CategoryTheory.ObjectProperty.prop_kernel_sigmaMap`).
* By induction on `n`, `f` induces isomorphisms modulo `P` on `Hₘ(Eₙ)` for `m ≤ k`. Over the
  `0`-skeleton, `E₋₁` is empty and `Hₘ(E₀) ≅ Hₘ(E₀, E₋₁)`
  (`TopPair.isoModSerre_homologyMap_fst_of_isEmpty`); afterwards the five lemma modulo `P` for the
  ambient space of a pair (`TopPair.isoModSerre_homologyMap_fst`) applies.
* `Hₘ(E, Eₖ₊₁) = 0` for `m ≤ k + 1` (`TauCeti.TopCat.isZero_singularHomology_preimage_skeletonLT`),
  so the five lemma again transfers the statement from `Eₖ₊₁` to `E` in degree `k`.

Over an arbitrary base, both fibrations are pulled back along a CW approximation of `B`
(`TauCeti.sigmaCWApproximationMap`). This does not change the fibres, and the projections of the
pullbacks to `E` and `E'` are weak homotopy equivalences
(`TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackSnd`), hence homology isomorphisms. Finally, a
map over a weak homotopy equivalence `g : B ⟶ B'` factors as a map over `B` into the base change of
`p'` along `g`, followed by the projection to `E'`, which is again a weak homotopy equivalence.

## Main results

* `TauCeti.TopCat.isoModSerre_singularHomologyMap_of_commSq`: a map of Serre fibrations over a
  weak homotopy equivalence whose maps on the homology of the fibres in degrees at most `k` have
  kernels and cokernels in `Q ≤ P` is an isomorphism modulo `P` on the total spaces in degree `k`.
* `TauCeti.TopCat.isoModSerre_singularHomologyMap_of_fiber_to_point`: a Serre fibration whose
  fibres have the homology of a point modulo `Q` in degrees at most `k` is an isomorphism modulo
  `P` in degree `k`.
* `TauCeti.TopCat.isoModSerre_singularHomologyMap_of_prop_fiber`: a Serre fibration whose fibres
  are path-connected with homology in `Q` in the positive degrees at most `k` is an isomorphism
  modulo `P` in degree `k`.
* `TauCeti.TopCat.prop_singularHomology_of_contractibleSpace`: if moreover the total space is
  contractible, the homology of the base lies in `P` in the positive degrees at most `k`.
* `TauCeti.TopCat.isIso_singularHomologyMap_of_commSq`: a map of Serre fibrations over a weak
  homotopy equivalence which is a homology isomorphism on every fibre in degrees at most `k` is
  one of the total spaces in degree `k`.
* `TauCeti.TopCat.isIso_singularHomologyMap_of_isIso_fiber_to_point`: a Serre fibration whose
  fibres have the homology of a point in degrees at most `k` is a homology isomorphism in
  degree `k`.
* `TauCeti.TopCat.isIso_singularHomologyMap_of_isZero_fiber`: the same, with the hypothesis on the
  fibres stated as path-connectedness and vanishing of positive-degree homology.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294, Chapter I.
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
  (P Q : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass] [Q.IsClosedUnderIsomorphisms]
  [∀ J : Type u, Q.IsClosedUnderColimitsOfShape (Discrete J)]
include hp hp'

/-- **A map of Serre fibrations which is an isomorphism modulo a Serre class on the homology of
the fibres is one on consecutive stages of the skeletal filtration.** Let `p` and `p'` be Serre
fibrations over `B`, `C ⊆ B` a relative CW complex with skeleta `Xⁿ`, and `f` a map over `B` whose
maps of fibres over the centres of the `n`-cells have kernels and cokernels in `Q ≤ P` on `Hq(-; R)`
for `q + n = m`. Then `f` induces an isomorphism modulo `P` on
`Hₘ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) ⟶ Hₘ(p'⁻¹(Xⁿ), p'⁻¹(Xⁿ⁻¹); R)`. -/
lemma isoModSerre_singularHomologyMap_preimagePairMap (hQP : Q ≤ P)
    (sq : CommSq f p p' (𝟙 B)) (n m : ℕ)
    (hfib : ∀ j : cell C n, ∀ q, q + n = m →
      Q (kernel (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (sq.fiberMap (map n j 0)))) ∧
      Q (cokernel (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (sq.fiberMap (map n j 0))))) :
    P.isoModSerre (TopPair.singularHomologyMap (TopCat.Hom.preimagePairMap f (sq.w.trans
      (Category.comp_id p)) (skeletonLT_subset_skeletonLT_succ C n)) (ModuleCat.of R R) m) := by
  have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
  rcases Nat.lt_or_ge m n with hm | hm
  · -- Below the dimension of the cells, both groups vanish: each summand over a cell does.
    have hz {X : _root_.TopCat.{u}} {r : X ⟶ B} (hr : serreFibrations r) :
        IsZero ((preimageSkeletonPair r C n).singularHomology (ModuleCat.of R R) m) := by
      rw [IsZero.iff_id_eq_zero]
      exact (isColimitCofanSingularHomologyPreimageSkeletonPair C hr R n m).hom_ext fun ⟨j⟩ ↦
        (isZero_singularHomology_preimage_sphere (ModuleCat.of R R)
          (mem_serreFibrations_pullbackFst hr (cellULiftMap C n j)) (by simpa using hm)).eq_of_src
          _ _
    have := (hz hp).isIso (hz hp') (TopPair.singularHomologyMap (TopCat.Hom.preimagePairMap f hf
      (skeletonLT_subset_skeletonLT_succ C n)) (ModuleCat.of R R) m)
    exact P.isomorphisms_le_isoModSerre _ this
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hm
  -- Through the identifications with the sums of the homology of the fibres over the centres of
  -- the cells, the map is the sum of the maps of fibres.
  have nat := preimageSkeletonPairSingularHomologyIsoSigma_hom_naturality (C := C) hp R hp' hf n q
    (fun j ↦ sq.fiberMap (map n j 0)) fun j x ↦ sq.fiberMap_apply_coe _ x
  rw [← Iso.eq_comp_inv, Category.assoc] at nat
  rw [nat]
  refine P.isoModSerre.comp_mem _ _ (P.isoModSerre_of_isIso _)
    (P.isoModSerre.comp_mem _ _ ⟨hQP _ ?_, hQP _ ?_⟩ (P.isoModSerre_of_isIso _))
  · exact Q.prop_kernel_sigmaMap _ fun j ↦ (hfib j q rfl).1
  · exact Q.prop_cokernel_sigmaMap _ fun j ↦ (hfib j q rfl).2

end Cells

/-! ### The skeleta and the total space -/

section Skeleta

variable [T2Space B] {C : Set B} [CWComplex C] (hp : serreFibrations p)
  (hp' : serreFibrations p') (R : Type u) [Ring R]
  (P Q : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass] [Q.IsClosedUnderIsomorphisms]
  [∀ J : Type u, Q.IsClosedUnderColimitsOfShape (Discrete J)] (hQP : Q ≤ P)
  (sq : CommSq f p p' (𝟙 B))
include hp hp' hQP

omit hp hp' hQP in
/-- Over the empty `(-1)`-skeleton `skeletonLT C 0`, the part of a space over `B` is empty. -/
private lemma isEmpty_preimage_skeletonLT_zero {X : _root_.TopCat.{u}} (q : X ⟶ B) :
    IsEmpty (q ⁻¹' (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B)) := by
  have hD : (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B) = ∅ := CWComplex.skeletonLT_zero_eq_empty
  rw [hD, preimage_empty]
  infer_instance

/-- A map of Serre fibrations whose maps on the homology of the fibres in degrees at most `k`
have kernels and cokernels in `Q ≤ P` is an isomorphism modulo `P` over every skeleton
`Xⁿ = skeletonLT C (n + 1)`, in degrees at most `k`. -/
private lemma isoModSerre_singularHomologyMap_preimageMap_skeletonLT {k : ℕ}
    (hfib : ∀ b ∈ C, ∀ q ≤ k,
      Q (kernel (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (sq.fiberMap b))) ∧
      Q (cokernel (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (sq.fiberMap b)))) (n m : ℕ) (hm : m ≤ k) :
    P.isoModSerre (SSet.homologyMap (_root_.TopCat.toSSet.map (f.preimageMap
      (sq.w.trans (Category.comp_id p)) (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B)))
      (ModuleCat.of R R) m) := by
  have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
  have hST := skeletonLT_subset_skeletonLT_succ C n
  -- The map of pairs `(Eₙ, Eₙ₋₁) ⟶ (E'ₙ, E'ₙ₋₁)` is an isomorphism modulo `P` in degrees at most
  -- `k + n`.
  have hrel (m' : ℕ) (hm' : m' ≤ k + n) : P.isoModSerre (TopPair.singularHomologyMap
      (TopCat.Hom.preimagePairMap f hf hST) (ModuleCat.of R R) m') :=
    isoModSerre_singularHomologyMap_preimagePairMap hp hp' R P Q hQP sq n m' fun j q hq ↦
      hfib _ (closedCell_subset_complex n j ⟨0, mem_closedBall_self zero_le_one, rfl⟩) q
        (by lia)
  have key : P.isoModSerre (SSet.homologyMap (_root_.TopCat.toSSet.map
      (TopPair.Hom.fst (TopCat.Hom.preimagePairMap f hf hST))) (ModuleCat.of R R) m) := by
    match n with
    | 0 =>
      -- Over the `0`-skeleton, homology is relative homology modulo the empty `E₋₁`.
      have : IsEmpty (TopPair.ofInclusion (X := E') (preimage_mono (f := p') hST)).snd :=
        isEmpty_preimage_skeletonLT_zero p'
      exact TopPair.isoModSerre_homologyMap_fst_of_isEmpty (ModuleCat.of R R) P _ m
        (hrel m (by lia))
    | n + 1 =>
      -- Afterwards the five lemma modulo `P` for the pair `(Eₙ, Eₙ₋₁)` applies, by induction on
      -- `n`.
      have hsnd (m' : ℕ) (hm' : m' ≤ k) : P.isoModSerre (SSet.homologyMap
          (_root_.TopCat.toSSet.map (TopPair.Hom.snd (TopCat.Hom.preimagePairMap f hf hST)))
          (ModuleCat.of R R) m') := by
        rw [TopCat.Hom.preimagePairMap_snd]
        exact isoModSerre_singularHomologyMap_preimageMap_skeletonLT hfib n m' hm'
      exact TopPair.isoModSerre_homologyMap_fst (ModuleCat.of R R) P
        (TopCat.Hom.preimagePairMap f hf hST) m (hrel (m + 1) (by lia)).2 (hsnd m hm)
        (hrel m (by lia)) fun m' hm' ↦ (hsnd m' (by lia)).1
  rwa [TopCat.Hom.preimagePairMap_fst] at key

/-- **A map of Serre fibrations which is an isomorphism modulo a Serre class on the homology of
the fibres is one over a CW complex in the base.** Let `p : E ⟶ B` and `p' : E' ⟶ B` be Serre
fibrations, `f : E ⟶ E'` a map over `B` and `C ⊆ B` a CW complex. If for every `b ∈ C` the map of
fibres `p⁻¹(b) ⟶ p'⁻¹(b)` has kernels and cokernels in `Q ≤ P` on `Hq(-; R)` for `q ≤ k`, then
`f` induces an isomorphism modulo `P` on `Hₖ(p⁻¹(C); R) ⟶ Hₖ(p'⁻¹(C); R)`. -/
private theorem isoModSerre_singularHomologyMap_preimage_of_commSq (k : ℕ)
    (hfib : ∀ b ∈ C, ∀ q ≤ k,
      Q (kernel (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (sq.fiberMap b))) ∧
      Q (cokernel (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (sq.fiberMap b)))) :
    P.isoModSerre (SSet.homologyMap (_root_.TopCat.toSSet.map
      (f.preimageMap (sq.w.trans (Category.comp_id p)) C)) (ModuleCat.of R R) k) := by
  have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
  -- `Hₘ(p⁻¹(C), p⁻¹(Xᵏ⁺¹)) = 0` for `m ≤ k + 1`, and likewise for `p'`, so the five lemma
  -- transfers the statement from `p⁻¹(Xᵏ⁺¹)` to `p⁻¹(C)`.
  have hST := skeletonLT_mono (C := C) (le_top : ((k + 1 : ℕ) : ℕ∞) + 1 ≤ ⊤)
  have hrel (m : ℕ) (hm : m ≤ k + 1) : P.isoModSerre (TopPair.singularHomologyMap
      (TopCat.Hom.preimagePairMap f hf hST) (ModuleCat.of R R) m) := by
    have := (isZero_singularHomology_preimage_skeletonLT hp R le_top (by lia)).isIso
      (isZero_singularHomology_preimage_skeletonLT hp' R le_top (by lia))
      (TopPair.singularHomologyMap (TopCat.Hom.preimagePairMap f hf hST) (ModuleCat.of R R) m)
    exact P.isomorphisms_le_isoModSerre _ this
  have hsnd (m : ℕ) (hm : m ≤ k) : P.isoModSerre (SSet.homologyMap (_root_.TopCat.toSSet.map
      (TopPair.Hom.snd (TopCat.Hom.preimagePairMap f hf hST))) (ModuleCat.of R R) m) := by
    have hS := isoModSerre_singularHomologyMap_preimageMap_skeletonLT hp hp' R P Q hQP sq hfib
      (k + 1) m hm
    rw [Nat.cast_succ (k + 1)] at hS
    rwa [TopCat.Hom.preimagePairMap_snd]
  have key := TopPair.isoModSerre_homologyMap_fst (ModuleCat.of R R) P
    (TopCat.Hom.preimagePairMap f hf hST) k (hrel (k + 1) le_rfl).2 (hsnd k le_rfl)
    (hrel k (by lia)) fun m hm ↦ (hsnd m (by lia)).1
  have h : P.isoModSerre (SSet.homologyMap (_root_.TopCat.toSSet.map
      (f.preimageMap hf (skeletonLT C ⊤ : Set B))) (ModuleCat.of R R) k) := by
    rwa [TopCat.Hom.preimagePairMap_fst] at key
  rw [skeletonLT_top] at h
  exact h

end Skeleta

/-! ### Over a CW complex -/

section Base

variable [T2Space B] [CWComplex (univ : Set B)] (hp : serreFibrations p)
  (hp' : serreFibrations p') (R : Type u) [Ring R]
  (P Q : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass] [Q.IsClosedUnderIsomorphisms]
  [∀ J : Type u, Q.IsClosedUnderColimitsOfShape (Discrete J)] (hQP : Q ≤ P)
include hp hp' hQP

/-- A map of Serre fibrations over a CW complex whose maps on the homology of the fibres in
degrees at most `k` have kernels and cokernels in `Q ≤ P` is an isomorphism modulo `P` on the
total spaces in degree `k`. -/
private theorem isoModSerre_singularHomologyMap_of_commSq_of_cwComplex
    (sq : CommSq f p p' (𝟙 B)) (k : ℕ)
    (hfib : ∀ b, ∀ q ≤ k,
      Q (kernel (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (sq.fiberMap b))) ∧
      Q (cokernel (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (sq.fiberMap b)))) :
    P.isoModSerre (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).map f) := by
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)
  have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
  have h := isoModSerre_singularHomologyMap_preimage_of_commSq (C := univ) hp hp' R P Q hQP sq k
    (fun b _ ↦ hfib b)
  -- The parts of the total spaces over the whole base are the total spaces.
  let ι (X : _root_.TopCat.{u}) (q : X ⟶ B) : _root_.TopCat.of (q ⁻¹' univ) ≅ X :=
    _root_.TopCat.isoOfHomeo (Homeomorph.Set.univ X)
  have hcomm : f.preimageMap hf univ ≫ (ι E' p').hom = (ι E p).hom ≫ f := by
    ext x
    exact f.coe_preimageMap_apply hf univ x
  refine P.isoModSerre.of_precomp (H.map (ι E p).hom) _ (P.isoModSerre_of_isIso _) ?_
  rw [← H.map_comp, ← hcomm, H.map_comp]
  exact P.isoModSerre.comp_mem _ _ h (P.isoModSerre_of_isIso _)

end Base

/-! ### Over an arbitrary base -/

section Arbitrary

variable (hp : serreFibrations p) (hp' : serreFibrations p') (R : Type u) [Ring R]
  (P Q : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass] [Q.IsClosedUnderIsomorphisms]
  [∀ J : Type u, Q.IsClosedUnderColimitsOfShape (Discrete J)] (hQP : Q ≤ P)
include hp hp' hQP

/-- A map over `B` of Serre fibrations over `B` whose maps on the homology of the fibres in degrees
at most `k` have kernels and cokernels in `Q ≤ P` is an isomorphism modulo `P` on the total spaces
in degree `k`. -/
private theorem isoModSerre_singularHomologyMap_of_commSq_id (sq : CommSq f p p' (𝟙 B)) (k : ℕ)
    (hfib : ∀ b, ∀ q ≤ k,
      Q (kernel (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (sq.fiberMap b))) ∧
      Q (cokernel (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (sq.fiberMap b)))) :
    P.isoModSerre (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).map f) := by
  have hf : f ≫ p' = p := sq.w.trans (Category.comp_id p)
  -- The CW approximation `g : ΓB ⟶ B` of `B`.
  let g := sigmaCWApproximationMap B
  have hg : g.hom.IsWeakHomotopyEquivalence := isWeakHomotopyEquivalence_sigmaCWApproximationMap B
  -- The map of the pulled-back fibrations induced by `f`.
  let sqP : CommSq (_root_.TopCat.pullbackMapOfCompEq g hf) (_root_.TopCat.pullbackFst g p)
      (_root_.TopCat.pullbackFst g p') (𝟙 _) :=
    ⟨(_root_.TopCat.pullbackMapOfCompEq_comp_pullbackFst g hf).trans (Category.comp_id _).symm⟩
  have hP := isoModSerre_singularHomologyMap_of_commSq_of_cwComplex
    (mem_serreFibrations_pullbackFst hp g) (mem_serreFibrations_pullbackFst hp' g) R P Q hQP sqP
    k (fun b q hq ↦ ?_)
  · -- On total spaces, the projections from the pullbacks are weak homotopy equivalences.
    let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)
    have h₁ : IsIso (H.map (_root_.TopCat.pullbackSnd g p)) :=
      (isWeakHomotopyEquivalence_pullbackSnd hp hg).isIso_singularHomologyMap (ModuleCat.of R R) k
    have h₂ : IsIso (H.map (_root_.TopCat.pullbackSnd g p')) :=
      (isWeakHomotopyEquivalence_pullbackSnd hp' hg).isIso_singularHomologyMap (ModuleCat.of R R) k
    refine P.isoModSerre.of_precomp (H.map (_root_.TopCat.pullbackSnd g p)) _
      (P.isoModSerre_of_isIso _) ?_
    rw [← H.map_comp, ← _root_.TopCat.pullbackMapOfCompEq_comp_pullbackSnd g hf, H.map_comp]
    exact P.isoModSerre.comp_mem _ _ hP (P.isoModSerre_of_isIso _)
  · -- On fibres, the pullbacks have the fibres of `p` and `p'`.
    let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)
    -- Through the identifications of the fibres, the fibre map of the pullbacks is that of `f`.
    -- The fibre map of `sqP` lands over `(𝟙 _) b` rather than `b`, so `rw` cannot move the
    -- hypothesis across this square; compare the two maps as isomorphic arrows instead.
    have hcomm := (CommSq.mk (TopCat.Hom.fiberPullbackFstIso_hom_naturality g sq sqP b)).map H
    let e : Arrow.mk (H.map (sqP.fiberMap b)) ≅ Arrow.mk (H.map (sq.fiberMap (g b))) :=
      Arrow.isoMk (H.mapIso (p.fiberPullbackFstIso g b)) (H.mapIso (p'.fiberPullbackFstIso g b))
        hcomm.w.symm
    exact ⟨Q.prop_kernel_of_arrowIso e.symm (hfib (g b) q hq).1,
      Q.prop_cokernel_of_arrowIso e.symm (hfib (g b) q hq).2⟩

end Arbitrary

/-- **A map of Serre fibrations over a weak homotopy equivalence which is an isomorphism modulo a
Serre class on the homology of the fibres is one on the total spaces.** Let `P` be a Serre class of
`R`-modules and `Q ≤ P` a property closed under isomorphisms and direct sums. Let
`p : E ⟶ B` and `p' : E' ⟶ B'` be Serre fibrations and `f : E ⟶ E'` a map over a weak homotopy
equivalence `g : B ⟶ B'`. If for every `b : B` and `q ≤ k` the map of fibres
`p⁻¹(b) ⟶ p'⁻¹(g b)` induces on `Hq(-; R)` a map whose kernel and cokernel lie in `Q`, then `f`
induces an isomorphism modulo `P` on `Hₖ(E; R) ⟶ Hₖ(E'; R)`. -/
theorem isoModSerre_singularHomologyMap_of_commSq {B' : _root_.TopCat.{u}} {p' : E' ⟶ B'}
    {g : B ⟶ B'} (hp : serreFibrations p) (hp' : serreFibrations p') (R : Type u) [Ring R]
    (P Q : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass] [Q.IsClosedUnderIsomorphisms]
    [∀ J : Type u, Q.IsClosedUnderColimitsOfShape (Discrete J)] (hQP : Q ≤ P)
    (sq : CommSq f p p' g) (hg : g.hom.IsWeakHomotopyEquivalence) (k : ℕ)
    (hfib : ∀ b, ∀ q ≤ k,
      Q (kernel (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (sq.fiberMap b))) ∧
      Q (cokernel (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (sq.fiberMap b)))) :
    P.isoModSerre (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
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
  have hL := isoModSerre_singularHomologyMap_of_commSq_id hp
    (mem_serreFibrations_pullbackFst hp' g) R P Q hQP sqL k (fun b q hq ↦ ?_)
  · -- The projection from the base change to `E'` is a weak homotopy equivalence.
    let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)
    have h₂ : IsIso (H.map (_root_.TopCat.pullbackSnd g p')) :=
      (isWeakHomotopyEquivalence_pullbackSnd hp' hg).isIso_singularHomologyMap (ModuleCat.of R R) k
    rw [← hl₂, H.map_comp]
    exact P.isoModSerre.comp_mem _ _ hL (P.isoModSerre_of_isIso _)
  · -- On fibres, `l` is the fibre map of `f`, through the identification of the fibres of the
    -- base change with those of `p'`.
    let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)
    have hcomm : sqL.fiberMap b ≫ (p'.fiberPullbackFstIso g b).hom = 𝟙 _ ≫ sq.fiberMap b := by
      ext x
      rw [Category.id_comp]
      -- The composite is typed over `(𝟙 B) b` rather than `b`, so `rw` cannot match it.
      erw [ConcreteCategory.comp_apply, TopCat.Hom.fiberPullbackFstIso_hom_apply_coe]
      rw [sq.fiberMap_apply_coe]
      exact (congrArg (fun y : _root_.TopCat.of { x : B × E' // g x.1 = p' x.2 } ↦ y.val.2)
        (sqL.fiberMap_apply_coe b x)).trans (ConcreteCategory.congr_hom hl₂ x.val)
    -- The fibre map of `sqL` lands over `(𝟙 B) b` rather than `b`, so compare the two maps as
    -- isomorphic arrows, as in `isoModSerre_singularHomologyMap_of_commSq_id`.
    have hc := (CommSq.mk hcomm).map H
    let e : Arrow.mk (H.map (sqL.fiberMap b)) ≅ Arrow.mk (H.map (sq.fiberMap b)) :=
      Arrow.isoMk (H.mapIso (Iso.refl _)) (H.mapIso (p'.fiberPullbackFstIso g b)) hc.w.symm
    exact ⟨Q.prop_kernel_of_arrowIso e.symm (hfib b q hq).1,
      Q.prop_cokernel_of_arrowIso e.symm (hfib b q hq).2⟩

/-! ### Fibres with the homology of a point modulo a Serre class -/

section Point

variable {R : Type u} [Ring R] (P Q : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
  [Q.IsClosedUnderIsomorphisms] [Q.ContainsZero]
  [∀ J : Type u, Q.IsClosedUnderColimitsOfShape (Discrete J)]

omit [Q.ContainsZero] in
/-- **A Serre fibration whose fibres have the homology of a point modulo a Serre class is a
homology isomorphism modulo that class.** Let `P` be a Serre class of `R`-modules and `Q ≤ P` a
property closed under isomorphisms and direct sums. Let `p : E ⟶ B` be a Serre fibration such
that, for every `b : B` and `q ≤ k`, the map from the fibre `p⁻¹(b)` to a point induces on
`Hq(-; R)` a map whose kernel and cokernel lie in `Q`. Then `p` induces an isomorphism modulo `P`
on `Hₖ(E; R) ⟶ Hₖ(B; R)`. -/
theorem isoModSerre_singularHomologyMap_of_fiber_to_point (hQP : Q ≤ P)
    (hp : serreFibrations p) (k : ℕ)
    (hfib : ∀ b, ∀ q ≤ k,
      Q (kernel (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (_root_.TopCat.isTerminalPUnit.from (p.fiber b)))) ∧
      Q (cokernel (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).map (_root_.TopCat.isTerminalPUnit.from (p.fiber b))))) :
    P.isoModSerre (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).map p) := by
  let sq : CommSq p p (𝟙 B) (𝟙 B) := ⟨rfl⟩
  refine isoModSerre_singularHomologyMap_of_commSq hp (MorphismProperty.id_mem _ B) R P Q hQP sq
    ContinuousMap.IsWeakHomotopyEquivalence.id k (fun b q hq ↦ ?_)
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)
  -- The fibre of the identity over `b` is a point.
  let F := TopCat.Hom.fiber (𝟙 B) ((𝟙 B) b)
  let t := _root_.TopCat.isTerminalPUnit.from F
  have : Unique F := ⟨⟨⟨b, rfl⟩⟩, fun x ↦ Subtype.ext x.property⟩
  have : IsIso t := by
    rw [_root_.TopCat.isTerminalPUnit.hom_ext t
      (_root_.TopCat.isoOfHomeo (Homeomorph.homeomorphOfUnique F PUnit)).hom]
    infer_instance
  -- The map from the fibre of `p` to a point factors through the fibre map, so the two maps are
  -- isomorphic arrows.
  have hfac : sq.fiberMap b ≫ t = 𝟙 _ ≫ _root_.TopCat.isTerminalPUnit.from (p.fiber b) :=
    _root_.TopCat.isTerminalPUnit.hom_ext _ _
  have hc := (CommSq.mk hfac).map H
  let e : Arrow.mk (H.map (sq.fiberMap b)) ≅
      Arrow.mk (H.map (_root_.TopCat.isTerminalPUnit.from (p.fiber b))) :=
    Arrow.isoMk (H.mapIso (Iso.refl _)) (H.mapIso (asIso t)) hc.w.symm
  exact ⟨Q.prop_kernel_of_arrowIso e.symm (hfib b q hq).1,
    Q.prop_cokernel_of_arrowIso e.symm (hfib b q hq).2⟩

/-- **A Serre fibration whose fibres are path-connected with the homology of a point modulo a
Serre class is a homology isomorphism modulo that class.** Let `P` be a Serre class of `R`-modules
and `Q ≤ P` a property containing zero and closed under isomorphisms and direct sums. Let
`p : E ⟶ B` be a Serre fibration whose fibres are path-connected and have their `R`-homology in
`Q` in the positive degrees `q ≤ k`. Then `p` induces an isomorphism modulo `P` on
`Hₖ(E; R) ⟶ Hₖ(B; R)`. -/
theorem isoModSerre_singularHomologyMap_of_prop_fiber (hQP : Q ≤ P) (hp : serreFibrations p)
    (k : ℕ) (hconn : ∀ b, PathConnectedSpace (p.fiber b))
    (hfib : ∀ b, ∀ q, q ≠ 0 → q ≤ k → Q (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj (p.fiber b))) :
    P.isoModSerre (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).map p) := by
  refine isoModSerre_singularHomologyMap_of_fiber_to_point P Q hQP hp k fun b q hq ↦ ?_
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)
  let t := _root_.TopCat.isTerminalPUnit.from (p.fiber b)
  have := hconn b
  rcases eq_or_ne q 0 with rfl | hq0
  · -- In degree zero the fibre and the point are path-connected, so the map is an isomorphism.
    have := IsIso.of_isIso_fac_right (singularHomologyMap_singularHomology₀ε (ModuleCat.of R R) t)
    exact ⟨Q.prop_of_isZero (isZero_kernel_of_mono _), Q.prop_of_isZero (isZero_cokernel_of_epi _)⟩
  · -- In positive degrees the homology of the point vanishes: the map is zero, its kernel is the
    -- homology of the fibre and its cokernel vanishes.
    have hz := isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of R R)
      (_root_.TopCat.of PUnit) hq0
    have h0 : H.map t = 0 := hz.eq_of_tgt _ _
    exact ⟨Q.prop_of_iso (kernelIsoOfEq h0 ≪≫ kernelZeroIsoSource).symm (hfib b q hq0 hq),
      Q.prop_of_isZero (hz.of_iso (cokernelIsoOfEq h0 ≪≫ cokernelZeroIsoTarget))⟩

/-- **The base of a fibration with contractible total space, modulo a Serre class.** Let `P` be a
Serre class of `R`-modules and `Q ≤ P` a property containing zero and closed under isomorphisms and
direct sums. Let `p : E ⟶ B` be a Serre fibration with contractible total space whose fibres are
path-connected and have their `R`-homology in `Q` in the positive degrees `q ≤ k`. Then the
`R`-homology of `B` lies in `P` in every positive degree `k`. For the path-loop fibration of a
space `X`, whose fibre is the loop space `ΩX`, this passes from the homology of `ΩX` to that of
`X`. -/
theorem prop_singularHomology_of_contractibleSpace (hQP : Q ≤ P) (hp : serreFibrations p)
    [ContractibleSpace E] {k : ℕ} (hk : k ≠ 0) (hconn : ∀ b, PathConnectedSpace (p.fiber b))
    (hfib : ∀ b, ∀ q, q ≠ 0 → q ≤ k → Q (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj (p.fiber b))) :
    P (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).obj B) := by
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)
  -- `Hₖ(E) = 0 ⟶ Hₖ(B) ⟶ coker` is exact, and the cokernel lies in `P`.
  exact P.prop_X₂_of_exact (ShortComplex.exact_cokernel (H.map p))
    (P.prop_of_isZero (isZero_singularHomologyFunctor_of_contractibleSpace _ E hk))
    (isoModSerre_singularHomologyMap_of_prop_fiber P Q hQP hp k hconn hfib).2

end Point

/-- **A map of Serre fibrations over a weak homotopy equivalence which is a homology isomorphism on
the fibres is a homology isomorphism.** Let `p : E ⟶ B` and `p' : E' ⟶ B'` be Serre fibrations and
`f : E ⟶ E'` a map over a weak homotopy equivalence `g : B ⟶ B'`. If for every `b : B` the map of
fibres `p⁻¹(b) ⟶ p'⁻¹(g b)` induces isomorphisms on `Hq(-; R)` for `q ≤ k`, then `f` induces an
isomorphism `Hₖ(E; R) ≅ Hₖ(E'; R)`. This is the homological counterpart of
`TauCeti.TopCat.isWeakHomotopyEquivalence_of_commSq`. -/
theorem isIso_singularHomologyMap_of_commSq {B' : _root_.TopCat.{u}} {p' : E' ⟶ B'} {g : B ⟶ B'}
    (hp : serreFibrations p) (hp' : serreFibrations p') (R : Type u) [Ring R]
    (sq : CommSq f p p' g) (hg : g.hom.IsWeakHomotopyEquivalence) (k : ℕ)
    (hfib : ∀ b, ∀ q ≤ k, IsIso (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).map (sq.fiberMap b))) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).map f) := by
  -- This is the case of the Serre class of zero modules.
  exact (ObjectProperty.isoModSerre_isZero_iff _).1 <|
    isoModSerre_singularHomologyMap_of_commSq hp hp' R IsZero IsZero le_rfl sq hg k
      fun b q hq ↦ (ObjectProperty.isoModSerre_isZero_iff _).2 (hfib b q hq)

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
  -- This is the case of the Serre class of zero modules.
  exact (ObjectProperty.isoModSerre_isZero_iff _).1 <|
    isoModSerre_singularHomologyMap_of_fiber_to_point IsZero IsZero le_rfl hp k
      fun b q hq ↦ (ObjectProperty.isoModSerre_isZero_iff _).2 (hfib b q hq)

/-- **A Serre fibration with acyclic fibres is a homology isomorphism.** Let `p : E ⟶ B` be a Serre
fibration whose fibres are path-connected and have no `R`-homology in the positive degrees
`q ≤ k`. Then `p` induces an isomorphism `Hₖ(E; R) ≅ Hₖ(B; R)`. -/
theorem isIso_singularHomologyMap_of_isZero_fiber (hp : serreFibrations p) (R : Type u) [Ring R]
    (k : ℕ) (hconn : ∀ b, PathConnectedSpace (p.fiber b))
    (hfib : ∀ b, ∀ q, q ≠ 0 → q ≤ k → IsZero (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj (p.fiber b))) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).map p) := by
  refine isIso_singularHomologyMap_of_isIso_fiber_to_point hp R k fun b q hq ↦ ?_
  have := hconn b
  rcases eq_or_ne q 0 with rfl | hq0
  · -- In degree zero both augmentations are isomorphisms, and the map commutes with them.
    exact IsIso.of_isIso_fac_right
      (singularHomologyMap_singularHomology₀ε (ModuleCat.of R R) _)
  · -- In positive degrees both groups vanish; the point is contractible.
    exact (hfib b q hq0 hq).isIso
      (isZero_singularHomologyFunctor_of_contractibleSpace _ (_root_.TopCat.of PUnit) hq0) _

end TopCat

end TauCeti

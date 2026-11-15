/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Homology
public import TauCeti.AlgebraicTopology.Singular.Twisted.CompactSupport
public import TauCeti.Topology.CWComplex.Classical.CompactSupport

/-!
# Cellular and singular homology with local coefficients of arbitrary CW complexes

Let `C ⊆ X` be a relative CW complex with skeleta `Xᵐ` and base `X⁻¹`, and let `L` be a local
coefficient system on `C`. The inclusion `(Xᵐ, X⁻¹) ⟶ (C, X⁻¹)` induces an isomorphism
`Hₖ(Xᵐ, X⁻¹; L) ≅ Hₖ(C, X⁻¹; L)` on twisted relative singular homology for every `k < m`
(`TauCeti.isIso_twistedHomologySkeletonBasePairToComplex`), with no finiteness condition on the
cells and no dimension bound. Composed with the computation of the homology of the cellular chain
complex with coefficients in `L`, this identifies cellular homology with local coefficients with
twisted relative singular homology for every relative CW complex
(`TauCeti.twistedCellularSingularHomologyIso`).

This is the local-coefficient form of `TauCeti.cellularSingularHomologyIso`. The bases of the
fibrations to which the identification `E²_{p,q} ≅ H_p(B; H_q(F))` of the second page of the
Serre spectral sequence is applied are in general infinite-dimensional; the Eilenberg--MacLane
spaces `K(A, n)` are an example.

The argument is the compact-support argument. A relative twisted chain of `(C, X⁻¹)` is the class
of a chain supported on finitely many simplices, whose images form a compact set; a compact subset
of a CW complex lies in a finite skeleton (`TauCeti.exists_subset_skeletonLT_of_isCompact`), so the
chain comes from `(Xᵐ, X⁻¹)` for every large `m`. The maps of relative chains induced by the
inclusions of the skeleta are injective (`TopPair.injective_twistedChainComplexMap_f`). So every
class of `Hₖ(C, X⁻¹; L)` comes from some skeleton, and a class of a skeleton vanishing in the
complex already vanishes in a larger skeleton
(`HomologicalComplex.exists_homologyMap_eq_of_injective`,
`HomologicalComplex.exists_homologyMap_eq_zero_of_injective`). The inclusions of the skeleta from
`Xᵐ` on induce isomorphisms on `Hₖ` for `k < m`
(`TauCeti.isIso_twistedHomologySkeletonBasePairToSucc`), so both statements already hold at `Xᵐ`.

## Main results

* `TauCeti.isIso_twistedHomologySkeletonBasePairToComplex`: `Hₖ(Xᵐ, X⁻¹; L) ≅ Hₖ(C, X⁻¹; L)` for
  `k < m`.
* `TauCeti.twistedCellularSingularHomologyIso`: cellular homology with coefficients in `L` is the
  twisted relative singular homology of the complex.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Lemma 2.34 and Theorem 2.35, Section 3.H, and
  Proposition A.1 of the Appendix for compact subsets of CW complexes.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VI.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {R : Type u} [Ring R] {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D] (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C))

/-! ### The relative chains of the skeleta

The coefficient system of this section lives on `(complexBasePair C).fst`, which is
`TopCat.of C` only after unfolding the pair constructors. Stating the auxiliary lemmas for such a
system keeps their statements type-correct at reducible transparency, so that they can be
rewritten with; the main theorem applies them to `L`. -/

section Skeleton

variable (M : LocalCoefficientSystem.{u, w, max w v} R (complexBasePair C).fst)

/-- The relative twisted chains of `(Xᵐ, X⁻¹)`, with `M` pulled back along the inclusion of the
`m`-skeleton. -/
private abbrev skeletonChains (m : ℕ) : ChainComplex (ModuleCat.{max w v} R) ℕ :=
  (skeletonBasePair C m).twistedChainComplex
    ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (skeletonBasePairToComplex C m)).hom).obj M)

/-- The map of relative twisted chains `(Xᵐ, X⁻¹) ⟶ (C, X⁻¹)`. -/
private abbrev skeletonChainsToComplex (m : ℕ) :
    skeletonChains C M m ⟶ (complexBasePair C).twistedChainComplex M :=
  TopPair.twistedChainComplexMap (skeletonBasePairToComplex C m) M

/-- The inclusion `(Xᵐ, X⁻¹) ⟶ (Xᵐ⁺¹, X⁻¹)` followed by the inclusion of `(Xᵐ⁺¹, X⁻¹)` into the
complex is the inclusion of `(Xᵐ, X⁻¹)`. -/
private lemma skeletonBasePairToSucc_comp_toComplex (m : ℕ) :
    skeletonBasePairToSucc C m ≫ skeletonBasePairToComplex C (m + 1) =
      skeletonBasePairToComplex C m := by
  rw [← skeletonBasePairInclusion_succ, skeletonBasePairInclusion_comp_toComplex]

/-- The map of relative twisted chains `(Xᵐ, X⁻¹) ⟶ (Xᵐ⁺¹, X⁻¹)`, after the identification of the
systems pulled back to `Xᵐ` along the two inclusions into the complex. -/
private def skeletonChainsSucc (m : ℕ) : skeletonChains C M m ⟶ skeletonChains C M (m + 1) :=
  (skeletonBasePair C m).twistedChainComplexCoefficientMap
      (eqToHom (congrArg (fun g : skeletonBasePair C m ⟶ complexBasePair C ↦
        (LocalCoefficientSystem.pullback (TopPair.Hom.fst g).hom).obj M)
          (skeletonBasePairToSucc_comp_toComplex C m).symm)) ≫
    (skeletonBasePair C m).twistedChainComplexCoefficientMap
      (TopPair.fstPullbackCompIso (skeletonBasePairToSucc C m)
        (skeletonBasePairToComplex C (m + 1)) M).hom ≫
    TopPair.twistedChainComplexMap (skeletonBasePairToSucc C m)
      ((LocalCoefficientSystem.pullback
        (TopPair.Hom.fst (skeletonBasePairToComplex C (m + 1))).hom).obj M)

private lemma skeletonChainsSucc_comp_skeletonChainsToComplex (m : ℕ) :
    skeletonChainsSucc C M m ≫ skeletonChainsToComplex C M (m + 1) =
      skeletonChainsToComplex C M m := by
  have h := TopPair.twistedChainComplexMap_congr M (skeletonBasePairToSucc_comp_toComplex C m).symm
  rw [TopPair.twistedChainComplexMap_comp] at h
  simp only [skeletonChainsSucc, skeletonChainsToComplex, h, Category.assoc]

/-- The inclusion `(Xᵐ, X⁻¹) ⟶ (Xᵐ⁺¹, X⁻¹)` induces an isomorphism on `Hₖ` for `k < m`. -/
private lemma isIso_homologyMap_skeletonChainsSucc {m k : ℕ} (hk : k < m) :
    IsIso (HomologicalComplex.homologyMap (skeletonChainsSucc C M m) k) := by
  have := isIso_twistedHomologySkeletonBasePairToSucc C M hk
  -- `M` is a system on `TopCat.of C` only up to unfolding the pair constructors, so the lemmas
  -- about `TauCeti.twistedHomologySkeletonBasePairToSucc` are applied by `erw`.
  erw [twistedHomologySkeletonBasePairToSucc_def] at this
  have h := @IsIso.of_isIso_comp_left _ _ _ _ _
    ((skeletonBasePair C m).twistedHomologyCoefficientMap
      (skeletonPairSubspaceSystemIso C M (m + 1)).inv k)
    (TopPair.twistedHomologyMap (TopTriple.innerToTotal.app (skeletonBaseTriple C m))
      (skeletonSystem C M (m + 1 + 1)) k)
    (@TopPair.isIso_twistedHomologyCoefficientMap _ _ (skeletonBasePair C m) _ _
      (skeletonPairSubspaceSystemIso C M (m + 1)).inv (Iso.isIso_inv _) k) this
  erw [skeletonSystem_eq_pullback C M (m + 1)] at h
  rw [skeletonChainsSucc, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  -- The inclusion of pairs is the map of the skeletal triple, by definition.
  have : IsIso (TopPair.twistedHomologyMap (skeletonBasePairToSucc C m)
      ((LocalCoefficientSystem.pullback
        (TopPair.Hom.fst (skeletonBasePairToComplex C (m + 1))).hom).obj M) k) := by
    rw [skeletonBasePairToSucc_def]
    exact h
  infer_instance

/-- The map of relative twisted chains `(Xᵐ, X⁻¹) ⟶ (Xᵐ⁺ᵈ, X⁻¹)`, composed of the maps of
consecutive skeleta. -/
private def skeletonChainsAdd (m : ℕ) :
    (d : ℕ) → (skeletonChains C M m ⟶ skeletonChains C M (m + d))
  | 0 => 𝟙 _
  | d + 1 => skeletonChainsAdd m d ≫ skeletonChainsSucc C M (m + d)

private lemma skeletonChainsAdd_comp_skeletonChainsToComplex (m d : ℕ) :
    skeletonChainsAdd C M m d ≫ skeletonChainsToComplex C M (m + d) =
      skeletonChainsToComplex C M m := by
  induction d with
  | zero => exact Category.id_comp _
  | succ d ih =>
    exact (Category.assoc _ _ _).trans ((congrArg (skeletonChainsAdd C M m d ≫ ·)
      (skeletonChainsSucc_comp_skeletonChainsToComplex C M (m + d))).trans ih)

private lemma isIso_homologyMap_skeletonChainsAdd {m k : ℕ} (hk : k < m) (d : ℕ) :
    IsIso (HomologicalComplex.homologyMap (skeletonChainsAdd C M m d) k) := by
  induction d with
  | zero =>
    rw [skeletonChainsAdd, HomologicalComplex.homologyMap_id]
    infer_instance
  | succ d ih =>
    rw [skeletonChainsAdd, HomologicalComplex.homologyMap_comp]
    have := isIso_homologyMap_skeletonChainsSucc C M (m := m + d) (k := k) (by lia)
    infer_instance

/-- On points, the inclusion of the `m`-skeleton into the complex is the identity. -/
private lemma coe_skeletonBasePairToComplex_fst_apply (m : ℕ)
    (x : (skeletonBasePair C m).fst) :
    (TopPair.Hom.fst (skeletonBasePairToComplex C m) x).1 = x.1 :=
  congrArg (fun g ↦ (g x).1) (skeletonBasePairToComplex_fst C m)

/-- The maps of relative twisted chains induced by the inclusions of the skeleta are injective. -/
private lemma injective_skeletonChainsToComplex_f (m k : ℕ) :
    Function.Injective ((skeletonChainsToComplex C M m).f k).hom := by
  have : Mono (TopPair.Hom.fst (skeletonBasePairToComplex C m)) :=
    (TopCat.mono_iff_injective _).2 fun x y h ↦ Subtype.ext <| by
      simpa only [coe_skeletonBasePairToComplex_fst_apply] using congrArg Subtype.val h
  refine TopPair.injective_twistedChainComplexMap_f _ M ?_ k
  -- Both subspaces are the base `X⁻¹`, and the inclusion of `Xᵐ` is the identity on points.
  rintro x ⟨y, hy⟩
  exact ⟨y, Subtype.ext ((congrArg Subtype.val hy).trans
    (coe_skeletonBasePairToComplex_fst_apply C m x))⟩

/-- **Relative twisted chains have compact supports.** Every relative twisted chain of
`(C, X⁻¹)` comes from `(Xᵐ, X⁻¹)` for every large enough `m`. -/
private lemma exists_forall_le_exists_skeletonChainsToComplex_f_eq {k : ℕ}
    (x : ((complexBasePair C).twistedChainComplex M).X k) :
    ∃ n, ∀ m, n ≤ m → ∃ y, ((skeletonChainsToComplex C M m).f k).hom y = x := by
  obtain ⟨c, rfl⟩ := (complexBasePair C).twistedChainComplexπ_f_surjective M x
  obtain ⟨K, hK, hc⟩ :=
    LocalCoefficientSystem.exists_isCompact_forall_mem_range_twistedChainComplexMap_f M c
  obtain ⟨n, hn⟩ := exists_subset_skeletonLT_of_isCompact (C := C)
    (hK.image continuous_subtype_val) (by rintro _ ⟨y, -, rfl⟩; exact y.2)
  refine ⟨n, fun m hm ↦ ?_⟩
  let ι := TopPair.Hom.fst (skeletonBasePairToComplex C m)
  have hι : IsInducing ι := by
    refine IsInducing.of_comp ι.hom.continuous
      (g := fun y : (complexBasePair C).fst ↦ (y.1 : X)) continuous_subtype_val ?_
    have : (fun y : (complexBasePair C).fst ↦ (y.1 : X)) ∘ ι =
        fun x : (skeletonBasePair C m).fst ↦ (x.1 : X) :=
      funext (coe_skeletonBasePairToComplex_fst_apply C m)
    rw [this]
    exact IsInducing.subtypeVal
  -- The chain `c` is supported in `K`, which lies in the image of the `m`-skeleton.
  have hKι : K ⊆ Set.range ι := fun y hy ↦
    ⟨⟨y.1, skeletonLT_mono (C := C) (show (n : ℕ∞) ≤ ((m + 1 : ℕ) : ℕ∞) by
      exact_mod_cast hm.trans m.le_succ) (hn ⟨y, hy, rfl⟩)⟩,
      Subtype.ext (coe_skeletonBasePairToComplex_fst_apply C m _)⟩
  have hcι : c ∈ LinearMap.range ((LocalCoefficientSystem.twistedChainComplexMap ι M).f k).hom := by
    rw [LocalCoefficientSystem.range_twistedChainComplexMap_f ι M hι,
      ← LocalCoefficientSystem.range_twistedChainComplexMap_subtypeVal_f]
    exact hc _ hKι
  obtain ⟨c', rfl⟩ := hcι
  exact ⟨_, TopPair.twistedChainComplexMap_f_twistedChainComplexπ_f_apply
    (skeletonBasePairToComplex C m) M c'⟩

/-- The inclusion `(Xᵐ, X⁻¹) ⟶ (C, X⁻¹)` induces an isomorphism on `Hₖ` for `k < m`, as a map of
relative twisted chains. -/
private lemma isIso_homologyMap_skeletonChainsToComplex {m k : ℕ} (hk : k < m) :
    IsIso (HomologicalComplex.homologyMap (skeletonChainsToComplex C M m) k) := by
  -- The skeleta `Xᵐ⁺ᵈ` from `m` on, with the maps `Xᵐ ⟶ Xᵐ⁺ᵈ` between them.
  have hφ (d j : ℕ) := injective_skeletonChainsToComplex_f C M (m + d) j
  have hcov (j : ℕ) (x : ((complexBasePair C).twistedChainComplex M).X j) :
      ∃ d y, ((skeletonChainsToComplex C M (m + d)).f j).hom y = x := by
    obtain ⟨n, hn⟩ := exists_forall_le_exists_skeletonChainsToComplex_f_eq C M x
    exact ⟨n, hn (m + n) (by lia)⟩
  have hfac (d : ℕ) := (HomologicalComplex.homologyMap_comp _ _ k).symm.trans
    (congrArg (HomologicalComplex.homologyMap · k)
      (skeletonChainsAdd_comp_skeletonChainsToComplex C M m d))
  have : Mono (HomologicalComplex.homologyMap (skeletonChainsToComplex C M m) k) := by
    refine (ModuleCat.mono_iff_injective _).2 ((injective_iff_map_eq_zero _).2 fun y hy ↦ ?_)
    -- A class vanishing in the complex vanishes in a larger skeleton, hence already in `Xᵐ`.
    obtain ⟨d, -, hd⟩ := HomologicalComplex.exists_homologyMap_eq_zero_of_injective k
      (fun d ↦ skeletonChainsToComplex C M (m + d)) (fun d ↦ hφ d k) rfl (i := 0)
      (P := fun _ ↦ True) (fun d _ ↦ skeletonChainsAdd C M m d)
      (fun d _ ↦ skeletonChainsAdd_comp_skeletonChainsToComplex C M m d)
      (fun x ↦ (hcov _ x).imp fun _ ↦ .intro trivial) y hy
    have := isIso_homologyMap_skeletonChainsAdd C M hk d
    exact (injective_iff_map_eq_zero _).1
      ((ModuleCat.mono_iff_injective _).1 inferInstance) y hd
  have : Epi (HomologicalComplex.homologyMap (skeletonChainsToComplex C M m) k) := by
    refine (ModuleCat.epi_iff_surjective _).2 fun z ↦ ?_
    -- A class of the complex comes from a larger skeleton, hence already from `Xᵐ`.
    obtain ⟨d, y, rfl⟩ := HomologicalComplex.exists_homologyMap_eq_of_injective k
      (fun d ↦ skeletonChainsToComplex C M (m + d)) (fun d ↦ hφ d _) (hcov k) z
    have := isIso_homologyMap_skeletonChainsAdd C M hk d
    refine ⟨inv (HomologicalComplex.homologyMap (skeletonChainsAdd C M m d) k) y, ?_⟩
    rw [← hfac d]
    simp
  exact isIso_of_mono_of_epi _

end Skeleton

/-! ### Comparison with the whole complex -/

/-- **The twisted homology of a relative CW complex is that of its skeleta in low degrees.** The
inclusion `(Xᵐ, X⁻¹) ⟶ (C, X⁻¹)` induces an isomorphism `Hₖ(Xᵐ, X⁻¹; L) ≅ Hₖ(C, X⁻¹; L)` for
`k < m`. The complex may have infinitely many cells and be infinite-dimensional. -/
theorem isIso_twistedHomologySkeletonBasePairToComplex {m k : ℕ} (hk : k < m) :
    IsIso (twistedHomologySkeletonBasePairToComplex C L m k) := by
  have := @TopPair.isIso_twistedHomologyCoefficientMap _ _ (skeletonBasePair C m) _ _
    (eqToHom (skeletonSystem_eq_pullback C L m))
    (Iso.isIso_hom (eqToIso (skeletonSystem_eq_pullback C L m))) k
  have := isIso_homologyMap_skeletonChainsToComplex C L hk
  rw [twistedHomologySkeletonBasePairToComplex_def]
  exact IsIso.comp_isIso

/-- The inclusion `(Xⁿ⁺¹, X⁻¹) ⟶ (C, X⁻¹)` induces an isomorphism on `Hₙ` with local
coefficients. -/
instance isIso_twistedHomologySkeletonBasePairToComplex_succ (n : ℕ) :
    IsIso (twistedHomologySkeletonBasePairToComplex C L (n + 1) n) :=
  isIso_twistedHomologySkeletonBasePairToComplex C L (by lia)

/-- **Cellular homology with local coefficients is twisted singular homology**: the homology of
the cellular chain complex with coefficients in `L` is the twisted relative singular homology
`Hₙ(C, X⁻¹; L)` of the complex, for every relative CW complex. The second map is induced by the
inclusion of the `(n + 1)`-skeleton into the complex. -/
def twistedCellularSingularHomologyIso (n : ℕ) :
    (twistedCellularChainComplex C L).homology n ≅ (complexBasePair C).twistedHomology L n :=
  twistedCellularHomologyIso C L n ≪≫
    asIso (twistedHomologySkeletonBasePairToComplex C L (n + 1) n)

/-- The cellular–singular comparison with local coefficients on cycles is the map induced by the
inclusion of the `n`-skeleton into the complex. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_twistedCellularSingularHomologyIso_hom (n : ℕ) :
    (twistedCellularChainComplex C L).homologyπ n ≫
        (twistedCellularSingularHomologyIso C L n).hom =
      (twistedCellularCyclesIso C L n).hom ≫ twistedHomologySkeletonBasePairToComplex C L n n := by
  rw [twistedCellularSingularHomologyIso, Iso.trans_hom, asIso_hom,
    homologyπ_comp_twistedCellularHomologyIso_hom_assoc,
    twistedHomologySkeletonBasePairToSucc_comp_twistedHomologySkeletonBasePairToComplex]

end TauCeti

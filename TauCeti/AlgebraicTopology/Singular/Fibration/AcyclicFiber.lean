/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Sigma
public import TauCeti.AlgebraicTopology.Singular.Fibration.CellFiber
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.Topology.Homotopy.MappingPath.Exact
public import TauCeti.Topology.Homotopy.SerreFibration.Connected
public import TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence

/-!
# Serre fibrations with acyclic fibres induce homology isomorphisms

Let `p : E ⟶ B` be a Serre fibration and `R` a ring. If every fibre `p⁻¹(b)` has the `R`-homology
of a point — that is, `p⁻¹(b)` is path-connected and `H_q(p⁻¹(b); R) = 0` for every `q > 0` — then
`p` induces an isomorphism `H_n(E; R) ≅ H_n(B; R)` in every degree `n`
(`TauCeti.TopCat.isIso_singularHomologyMap_of_forall_fiber`). No CW, separation, or connectivity
hypothesis is imposed on `B` or `E`.

When `B` is path-connected, the fibres of `p` over any two points of `B` are connected by a
zigzag of weak homotopy equivalences through the pullback of `p` along a path between them:
`p` pulls back to a Serre fibration over the contractible unit interval, and both endpoint fibre
inclusions are weak homotopy equivalences
(`TauCeti.TopCat.isNConnected_fiberι_of_mem_serreFibrations`). Hence path-connectedness and the
singular homology of `p⁻¹(b)` do not depend on `b`
(`TauCeti.TopCat.pathConnectedSpace_fiber_iff_of_joined`,
`TauCeti.TopCat.singularHomologyFiberIsoOfJoined`), and over a path-connected base it suffices to
check acyclicity on a single fibre (`TauCeti.TopCat.isIso_singularHomologyMap_of_fiber`).

Applied to the fixed-end path fibration `P_x X ⟶ X` of a simply connected space `(X, x)`, whose
total space is contractible and whose fibre over `x` is the loop space `Ω X x`, this shows that `X`
has vanishing positive-degree `R`-homology as soon as `Ω X x` does
(`TauCeti.isZero_singularHomology_of_loopSpace`).

## Proof outline

1. **Over a disk.** For two Serre fibrations `p₁ : E₁ ⟶ Dʳ` and `p₂ : E₂ ⟶ Dʳ` whose fibres over
   `0` have the `R`-homology of a point, any map `f : E₁ ⟶ E₂` over `Dʳ` induces isomorphisms
   `H_m(E₁, p₁⁻¹(Sʳ⁻¹); R) ≅ H_m(E₂, p₂⁻¹(Sʳ⁻¹); R)`. Both groups vanish for `m ≠ r` by
   `isZero_singularHomology_preimage_sphere` and `singularHomologyPreimageSphereIso`; in degree
   `m = r` naturality (`singularHomologyPreimageSphereIso_hom_naturality`) reduces to `H_0` of the
   map on zero-fibres, where the augmentation onto `R` is an isomorphism on both sides.
2. **Over a CW complex.** Comparing `p : E ⟶ B` with `𝟙 B : B ⟶ B` over a CW complex `B`,
   additivity over the `k`-cells (`isColimitCofanSingularHomologyPreimageSkeletonPair`) and Step 1
   show that `p` induces isomorphisms `H_m(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹); R) ≅ H_m(Xᵏ, Xᵏ⁻¹; R)`. Induction
   on `k` via the long exact sequence of a pair gives `H_m(p⁻¹(Xᵏ); R) ≅ H_m(Xᵏ; R)`, and in
   degree `n` the `(n + 1)`-skeleton already captures `H_n` of both total spaces by
   `isZero_singularHomology_preimage_skeletonLT`.
3. **Arbitrary base.** Pulling `p` back along the CW approximation `ΓB ⟶ B`
   (`sigmaCWApproximationMap`) reduces the general case to Step 2, since both `ΓB ⟶ B` and the
   pullback projection `ΓB ×_B E ⟶ E` (`isWeakHomotopyEquivalence_pullbackSnd`) are weak homotopy
   equivalences and therefore induce homology isomorphisms.

## Main results

* `TauCeti.TopCat.pathConnectedSpace_fiber_iff_of_joined`,
  `TauCeti.TopCat.singularHomologyFiberIsoOfJoined`,
  `TauCeti.TopCat.isZero_singularHomology_fiber_iff_of_joined`: invariance of path-connectedness
  and singular homology of the fibres of a Serre fibration along paths in the base.
* `TauCeti.TopCat.isIso_singularHomologyMap_of_forall_fiber`: a Serre fibration whose fibres have
  the `R`-homology of a point induces isomorphisms on `H_n(-; R)` for every `n`.
* `TauCeti.TopCat.isIso_singularHomologyMap_of_fiber`: the single-fibre form over a path-connected
  base.
* `TauCeti.isZero_singularHomology_of_loopSpace`: a simply connected space whose loop space has
  vanishing positive-degree `R`-homology itself has vanishing positive-degree `R`-homology.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 5.1, Corollary 5.4, and Section 5.3.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Metric Set Topology Topology.RelCWComplex
open scoped Topology.Homotopy unitInterval

universe u

namespace TauCeti

namespace TopCat

section JoinedFibers

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B}

/-- Pulling a Serre fibration `p : E ⟶ B` back along a path `γ : I → B` (lifted to `ULift.{u} I`)
produces a weak homotopy equivalence from `p⁻¹(γ t)` into the pullback over `ULift.{u} I`, because
the interval is contractible. -/
private theorem isWeakHomotopyEquivalence_fiberPullback (hp : serreFibrations p)
    {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ULift.{u} I) :
    let g : _root_.TopCat.of (ULift.{u} I) ⟶ B :=
      _root_.TopCat.ofHom ⟨fun s ↦ γ s.down, γ.continuous.comp continuous_uliftDown⟩
    ((p.fiberPullbackFstIso g t).inv ≫ (_root_.TopCat.pullbackFst g p).fiberι t).hom
      |>.IsWeakHomotopyEquivalence := by
  intro g
  have hI : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  have hUI : ContractibleSpace (ULift.{u} I) := Homeomorph.ulift.contractibleSpace
  have hι : ((_root_.TopCat.pullbackFst g p).fiberι t).hom.IsWeakHomotopyEquivalence :=
    ContinuousMap.isWeakHomotopyEquivalence_iff_forall_isNConnected.2 fun n ↦
      isNConnected_fiberι_of_mem_serreFibrations (mem_serreFibrations_pullbackFst hp g)
        fun _ _ ↦ inferInstance
  have he : (p.fiberPullbackFstIso g t).inv.hom.IsWeakHomotopyEquivalence :=
    (_root_.TopCat.homeoOfIso (p.fiberPullbackFstIso g t).symm).toHomotopyEquiv
      |>.isWeakHomotopyEquivalence
  exact hι.comp he

/-- **Fibres of a Serre fibration over points in the same path component are simultaneously
path-connected.** -/
theorem pathConnectedSpace_fiber_iff_of_joined (hp : serreFibrations p) {b₀ b₁ : B}
    (hb : Joined b₀ b₁) : PathConnectedSpace (p.fiber b₀) ↔ PathConnectedSpace (p.fiber b₁) := by
  let γ := hb.somePath
  let g : _root_.TopCat.of (ULift.{u} I) ⟶ B :=
    _root_.TopCat.ofHom ⟨fun s ↦ γ s.down, γ.continuous.comp continuous_uliftDown⟩
  have hg₀ : g ⟨0⟩ = b₀ := γ.source
  have hg₁ : g ⟨1⟩ = b₁ := γ.target
  have h₀ := (isWeakHomotopyEquivalence_fiberPullback hp γ ⟨0⟩).pathConnectedSpace_iff
  have h₁ := (isWeakHomotopyEquivalence_fiberPullback hp γ ⟨1⟩).pathConnectedSpace_iff
  rw [hg₀] at h₀
  rw [hg₁] at h₁
  exact h₀.trans h₁.symm

/-- **Fibres of a Serre fibration over points in the same path component have isomorphic singular
homology** with coefficients in any module `M`. -/
def singularHomologyFiberIsoOfJoined (hp : serreFibrations p) {b₀ b₁ : B} (hb : Joined b₀ b₁)
    {A : Type*} [Ring A] (M : ModuleCat.{u} A) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} A) n).obj M).obj (p.fiber b₀) ≅
      ((singularHomologyFunctor (ModuleCat.{u} A) n).obj M).obj (p.fiber b₁) := by
  let γ := hb.somePath
  let g : _root_.TopCat.of (ULift.{u} I) ⟶ B :=
    _root_.TopCat.ofHom ⟨fun s ↦ γ s.down, γ.continuous.comp continuous_uliftDown⟩
  let H := (singularHomologyFunctor (ModuleCat.{u} A) n).obj M
  have := (isWeakHomotopyEquivalence_fiberPullback hp γ ⟨0⟩).isIso_singularHomologyMap M n
  have := (isWeakHomotopyEquivalence_fiberPullback hp γ ⟨1⟩).isIso_singularHomologyMap M n
  exact H.mapIso (eqToIso (congrArg p.fiber γ.source.symm)) ≪≫
    asIso (H.map ((p.fiberPullbackFstIso g ⟨0⟩).inv ≫
      (_root_.TopCat.pullbackFst g p).fiberι ⟨0⟩)) ≪≫
    (asIso (H.map ((p.fiberPullbackFstIso g ⟨1⟩).inv ≫
      (_root_.TopCat.pullbackFst g p).fiberι ⟨1⟩))).symm ≪≫
    H.mapIso (eqToIso (congrArg p.fiber γ.target))

/-- **Vanishing of fibre homology is invariant along paths in the base** for any Serre fibration. -/
theorem isZero_singularHomology_fiber_iff_of_joined (hp : serreFibrations p) {b₀ b₁ : B}
    (hb : Joined b₀ b₁) {A : Type*} [Ring A] (M : ModuleCat.{u} A) (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} A) n).obj M).obj (p.fiber b₀)) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{u} A) n).obj M).obj (p.fiber b₁)) :=
  Iso.isZero_iff (singularHomologyFiberIsoOfJoined hp hb M n)

end JoinedFibers

namespace AcyclicFiber

/-- Any morphism between zero objects is an isomorphism. -/
private lemma isIso_of_isZero {C : Type*} [Category* C] [Preadditive C] {X Y : C} (f : X ⟶ Y)
    (hX : IsZero X) (hY : IsZero Y) : IsIso f :=
  ⟨0, hX.eq_of_src _ _, hY.eq_of_src _ _⟩

/-- A map between path-connected spaces induces an isomorphism on zeroth singular homology. -/
private lemma isIso_singularHomologyMap_zero_of_pathConnectedSpace (R : Type u) [Ring R]
    {X Y : _root_.TopCat.{u}} (hX : PathConnectedSpace X) (hY : PathConnectedSpace Y)
    (f : X ⟶ Y) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)).map f) := by
  have : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)).map f ≫
      Y.singularHomology₀ε (ModuleCat.of R R)) := by
    rw [singularHomologyMap_singularHomology₀ε]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (Y.singularHomology₀ε (ModuleCat.of R R))

/-- The singular homology of an empty space vanishes in every degree. -/
private lemma isZero_singularHomology_of_isEmpty (R : Type u) [Ring R] (X : _root_.TopCat.{u})
    (hX : IsEmpty X) (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj X) := by
  have : IsEmpty X := hX
  cases n with
  | zero => exact isZero_singularHomologyFunctor_zero_of_isEmpty (ModuleCat.of R R) X
  | succ n =>
    exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{u} R) (n + 1)
      (ModuleCat.of R R) X n.succ_ne_zero

/-- **Comparison over a single disk.** For two Serre fibrations `p₁ : E₁ ⟶ Dʳ` and `p₂ : E₂ ⟶ Dʳ`
whose zero-fibres are path-connected with vanishing positive `R`-homology, any map `f : E₁ ⟶ E₂`
over `Dʳ` induces an isomorphism on relative homology modulo the preimages of the boundary
sphere. -/
private lemma isIso_singularHomologyMap_disk {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {E₁ E₂ : _root_.TopCat.{u}}
    {p₁ : E₁ ⟶ _root_.TopCat.of (closedBall (0 : V) 1)}
    {p₂ : E₂ ⟶ _root_.TopCat.of (closedBall (0 : V) 1)}
    (hp₁ : serreFibrations p₁) (hp₂ : serreFibrations p₂) (R : Type u) [Ring R]
    (hF₁₀ : PathConnectedSpace (_root_.TopCat.of (p₁ ⁻¹' {x | (x : V) = 0})))
    (hF₂₀ : PathConnectedSpace (_root_.TopCat.of (p₂ ⁻¹' {x | (x : V) = 0})))
    (hF₁ : ∀ q > 0, IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).obj (_root_.TopCat.of (p₁ ⁻¹' {x | (x : V) = 0}))))
    (hF₂ : ∀ q > 0, IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).obj (_root_.TopCat.of (p₂ ⁻¹' {x | (x : V) = 0}))))
    (f : E₁ ⟶ E₂) (hf : ∀ e, p₂ (f e) = p₁ e)
    (hm : MapsTo f (p₁ ⁻¹' {x | (x : V) ∈ sphere (0 : V) 1})
      (p₂ ⁻¹' {x | (x : V) ∈ sphere (0 : V) 1})) (m : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopPair.ofSubsetMap f hm) (ModuleCat.of R R) m) := by
  by_cases hlt : m < Module.finrank ℝ V
  · exact isIso_of_isZero _ (isZero_singularHomology_preimage_sphere R hp₁ hlt)
      (isZero_singularHomology_preimage_sphere R hp₂ hlt)
  · obtain ⟨q, hqm⟩ : ∃ q, q + Module.finrank ℝ V = m := ⟨m - Module.finrank ℝ V, by omega⟩
    cases q with
    | zero =>
      have hf₀ (x : p₁ ⁻¹' {x | (x : V) = 0}) : f x.1 ∈ p₂ ⁻¹' {x | (x : V) = 0} := by
        simpa [hf x.1] using x.2
      let f₀ : _root_.TopCat.of (p₁ ⁻¹' {x | (x : V) = 0}) ⟶
          _root_.TopCat.of (p₂ ⁻¹' {x | (x : V) = 0}) :=
        _root_.TopCat.ofHom ⟨fun x ↦ ⟨f x.1, hf₀ x⟩,
          (f.hom.continuous.comp continuous_subtype_val).subtype_mk hf₀⟩
      have := isIso_singularHomologyMap_zero_of_pathConnectedSpace R hF₁₀ hF₂₀ f₀
      have hnat := singularHomologyPreimageSphereIso_hom_naturality R hp₁ hp₂ hf hm
        (f₀ := f₀) (fun _ ↦ rfl) 0 m hqm
      have : IsIso (TopPair.singularHomologyMap (TopPair.ofSubsetMap f hm) (ModuleCat.of R R) m ≫
          (singularHomologyPreimageSphereIso R hp₂ 0 m hqm).hom) := by
        rw [hnat]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (singularHomologyPreimageSphereIso R hp₂ 0 m hqm).hom
    | succ q =>
      exact isIso_of_isZero _
        ((hF₁ (q + 1) (Nat.succ_pos q)).of_iso
          (singularHomologyPreimageSphereIso R hp₁ (q + 1) m hqm))
        ((hF₂ (q + 1) (Nat.succ_pos q)).of_iso
          (singularHomologyPreimageSphereIso R hp₂ (q + 1) m hqm))

/-- If a map between colimit cofans intertwines the legs along objectwise isomorphisms, it is an
isomorphism. -/
private lemma isIso_of_isColimit_cofan {C : Type*} [Category* C] {J : Type*} {P₁ P₂ : J → C}
    {X₁ X₂ : C} {ι₁ : ∀ j, P₁ j ⟶ X₁} {ι₂ : ∀ j, P₂ j ⟶ X₂}
    (h₁ : IsColimit (Cofan.mk X₁ ι₁)) (h₂ : IsColimit (Cofan.mk X₂ ι₂))
    {φ : X₁ ⟶ X₂} (g : ∀ j, P₁ j ⟶ P₂ j) (hg : ∀ j, IsIso (g j))
    (hcomm : ∀ j, ι₁ j ≫ φ = g j ≫ ι₂ j) : IsIso φ := by
  let ψ := Cofan.IsColimit.desc h₂ fun j ↦ (have := hg j; inv (g j)) ≫ ι₁ j
  have hfac (j : J) : ι₂ j ≫ ψ = (have := hg j; inv (g j)) ≫ ι₁ j :=
    Cofan.IsColimit.fac h₂ _ j
  refine ⟨ψ,
    Cofan.IsColimit.hom_ext h₁ _ _ fun j ↦ ?_,
    Cofan.IsColimit.hom_ext h₂ _ _ fun j ↦ ?_⟩
  · have := hg j
    simp only [cofan_mk_inj]
    rw [← Category.assoc, hcomm j, Category.assoc, hfac j, IsIso.hom_inv_id_assoc]
    exact (Category.comp_id _).symm
  · have := hg j
    simp only [cofan_mk_inj]
    rw [← Category.assoc, hfac j, Category.assoc, hcomm j, IsIso.inv_hom_id_assoc]
    exact (Category.comp_id _).symm

section CWBase

variable {E B : _root_.TopCat.{u}} [T2Space B] [CWComplex (univ : Set B)] {p : E ⟶ B}

/-- The map of consecutive skeletal preimage pairs `(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹)) ⟶ (Xᵏ, Xᵏ⁻¹)` induced
by `p`, where `Xᵏ` is read as `(𝟙 B)⁻¹(Xᵏ)`. -/
private def skeletonPairProj (p : E ⟶ B) (k : ℕ) :
    preimageSkeletonPair p (univ : Set B) k ⟶ preimageSkeletonPair (𝟙 B) (univ : Set B) k :=
  TopPair.ofInclusionMap _ _
    ⟨fun x ↦ ⟨p x.1, x.2⟩, (p.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
    fun _ hx ↦ hx

/-- The ambient map `(q, e) ↦ (q, p e)` between the pullbacks of `p` and `𝟙 B` over the `k`-cell
`j`. -/
private def cellDiskPullbackProjFst (p : E ⟶ B) (k : ℕ) (j : cell (univ : Set B) k) :
    (cellDiskPullbackPair p (univ : Set B) k j).fst ⟶
      (cellDiskPullbackPair (𝟙 B) (univ : Set B) k j).fst :=
  _root_.TopCat.ofHom ⟨fun x ↦ ⟨(x.1.1, p x.1.2), x.2⟩,
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (p.hom.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _⟩

/-- The map of pairs between the pullbacks of `p` and `𝟙 B` over the `k`-cell `j`. -/
private def cellDiskPullbackProj (p : E ⟶ B) (k : ℕ) (j : cell (univ : Set B) k) :
    cellDiskPullbackPair p (univ : Set B) k j ⟶
      cellDiskPullbackPair (𝟙 B) (univ : Set B) k j :=
  TopPair.ofSubsetMap (cellDiskPullbackProjFst p k j) fun _ hx ↦ hx

/-- Over a CW complex `B`, a Serre fibration `p : E ⟶ B` whose fibres have the `R`-homology of a
point induces isomorphisms on the relative homology of consecutive skeletal preimage pairs. -/
private lemma isIso_singularHomologyMap_skeletonPairProj (hp : serreFibrations p) (R : Type u)
    [Ring R] (hF₀ : ∀ b : B, PathConnectedSpace (p.fiber b))
    (hF : ∀ b : B, ∀ q > 0, IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).obj (p.fiber b))) (k m : ℕ) :
    IsIso (TopPair.singularHomologyMap (skeletonPairProj p k) (ModuleCat.of R R) m) := by
  have hpId : serreFibrations (𝟙 B) := MorphismProperty.id_mem _ _
  have hdIso (j : cell (univ : Set B) k) :
      IsIso (TopPair.singularHomologyMap (cellDiskPullbackProj p k j) (ModuleCat.of R R) m) := by
    let b := map (C := (univ : Set B)) k j 0
    have e₁ := cellDiskPullbackFiberHomeomorph p (univ : Set B) k j
    have e₂ := cellDiskPullbackFiberHomeomorph (𝟙 B) (univ : Set B) k j
    have hSub₂ : Subsingleton ((𝟙 B) ⁻¹' {b} : Set B) :=
      ⟨fun x y ↦ Subtype.ext (x.2.trans y.2.symm)⟩
    have hPC₁ : PathConnectedSpace
        (_root_.TopCat.of (_root_.TopCat.pullbackFst (cellULiftMap (univ : Set B) k j) p ⁻¹'
          {x | (x : ULift.{u} (Fin k → ℝ)) = 0})) :=
      @Homeomorph.pathConnectedSpace _ _ _ _ (hF₀ b) e₁.symm
    have hPC₂ : PathConnectedSpace
        (_root_.TopCat.of (_root_.TopCat.pullbackFst (cellULiftMap (univ : Set B) k j) (𝟙 B) ⁻¹'
          {x | (x : ULift.{u} (Fin k → ℝ)) = 0})) := by
      have hPCb : PathConnectedSpace ((𝟙 B) ⁻¹' {b} : Set B) :=
        ⟨⟨⟨b, rfl⟩⟩, fun x y ↦ Subsingleton.elim x y ▸ Joined.refl x⟩
      exact @Homeomorph.pathConnectedSpace _ _ _ _ hPCb e₂.symm
    have hZ₁ (q : ℕ) (hq : q > 0) :
        IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
          (_root_.TopCat.of (_root_.TopCat.pullbackFst (cellULiftMap (univ : Set B) k j) p ⁻¹'
            {x | (x : ULift.{u} (Fin k → ℝ)) = 0}))) :=
      (hF b q hq).of_iso (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo e₁))
    have hZ₂ (q : ℕ) (hq : q > 0) :
        IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
          (_root_.TopCat.of (_root_.TopCat.pullbackFst (cellULiftMap (univ : Set B) k j) (𝟙 B) ⁻¹'
            {x | (x : ULift.{u} (Fin k → ℝ)) = 0}))) :=
      (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{u} R) q
        (ModuleCat.of R R) (_root_.TopCat.of ((𝟙 B) ⁻¹' {b} : Set B)) (by omega)).of_iso
          (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
            (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo e₂))
    exact isIso_singularHomologyMap_disk
      (mem_serreFibrations_pullbackFst hp (cellULiftMap (univ : Set B) k j))
      (mem_serreFibrations_pullbackFst hpId (cellULiftMap (univ : Set B) k j))
      R hPC₁ hPC₂ hZ₁ hZ₂ (cellDiskPullbackProjFst p k j) (fun _ ↦ rfl) (fun _ hx ↦ hx) m
  refine isIso_of_isColimit_cofan
    (isColimitCofanSingularHomologyPreimageSkeletonPair (univ : Set B) hp R k m)
    (isColimitCofanSingularHomologyPreimageSkeletonPair (univ : Set B) hpId R k m)
    (fun j ↦ TopPair.singularHomologyMap (cellDiskPullbackProj p k j) (ModuleCat.of R R) m)
    hdIso fun j ↦ ?_
  rw [← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp]
  refine congrArg (TopPair.singularHomologyMap · (ModuleCat.of R R) m)
    (TopPair.hom_ext_of_fst _ (_root_.TopCat.ext fun x ↦ Subtype.ext ?_))
  exact (congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _
      (TopPair.Hom.fst (cellDiskPullbackPairMap p (univ : Set B) k j) x))).trans
    ((congrArg p (coe_cellDiskPullbackPairMap_fst_apply k j x)).trans
      ((congrArg (fun y ↦ y.1.2)
        (TopPair.ofSubsetMap_fst_apply (cellDiskPullbackProjFst p k j) _ x)).symm.trans
        (coe_cellDiskPullbackPairMap_fst_apply (p := 𝟙 B) k j
          (TopPair.Hom.fst (cellDiskPullbackProj p k j) x)).symm))

/-- The map `p⁻¹(skeletonLT univ k) ⟶ (𝟙 B)⁻¹(skeletonLT univ k)` induced by `p`. -/
private def skeletonProj (p : E ⟶ B) (k : ℕ) :
    _root_.TopCat.of (p ⁻¹' (skeletonLT (univ : Set B) k : Set B)) ⟶
      _root_.TopCat.of ((𝟙 B) ⁻¹' (skeletonLT (univ : Set B) k : Set B)) :=
  _root_.TopCat.ofHom ⟨fun x ↦ ⟨p x.1, x.2⟩,
    (p.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- By induction on `k`, `p` induces homology isomorphisms on `p⁻¹(skeletonLT univ k)` for every
`k : ℕ`. -/
private lemma isIso_singularHomologyMap_skeletonProj (hp : serreFibrations p) (R : Type u)
    [Ring R] (hF₀ : ∀ b : B, PathConnectedSpace (p.fiber b))
    (hF : ∀ b : B, ∀ q > 0, IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).obj (p.fiber b))) :
    ∀ k m : ℕ, IsIso (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      (skeletonProj p k))
  | 0, m => by
    have hE : IsEmpty (_root_.TopCat.of (p ⁻¹' (skeletonLT (univ : Set B) 0 : Set B))) :=
      ⟨fun x ↦ by simpa [CWComplex.skeletonLT_zero_eq_empty] using x.2⟩
    have hB : IsEmpty (_root_.TopCat.of ((𝟙 B) ⁻¹' (skeletonLT (univ : Set B) 0 : Set B))) :=
      ⟨fun x ↦ by simpa [CWComplex.skeletonLT_zero_eq_empty] using x.2⟩
    exact isIso_of_isZero _ (isZero_singularHomology_of_isEmpty R _ hE m)
      (isZero_singularHomology_of_isEmpty R _ hB m)
  | k + 1, m => by
    let φ := SSetPair.chainComplexShortComplexMap
      (TopPair.toSSetPair.map (skeletonPairProj p k)) (ModuleCat.of R R)
    have hS₁ := (TopPair.toSSetPair.obj (preimageSkeletonPair p (univ : Set B) k))
      |>.shortExact_chainComplexShortComplex (ModuleCat.of R R)
    have hS₂ := (TopPair.toSSetPair.obj (preimageSkeletonPair (𝟙 B) (univ : Set B) k))
      |>.shortExact_chainComplexShortComplex (ModuleCat.of R R)
    have hτ₁ (d : ℕ) : IsIso (HomologicalComplex.homologyMap φ.τ₁ d) := by
      rw [TopPair.homologyMap_chainComplexShortComplexMap_τ₁]
      have hsnd : TopPair.Hom.snd (skeletonPairProj p k) = skeletonProj p k :=
        _root_.TopCat.ext fun x ↦ Subtype.ext (TopPair.ofInclusionMap_snd_apply _ _ x)
      rw [hsnd]
      exact isIso_singularHomologyMap_skeletonProj hp R hF₀ hF k d
    have hτ₃ (d : ℕ) : IsIso (HomologicalComplex.homologyMap φ.τ₃ d) := by
      rw [SSetPair.chainComplexShortComplexMap_τ₃]
      exact isIso_singularHomologyMap_skeletonPairProj hp R hF₀ hF k d
    have hτ₂ : IsIso (HomologicalComplex.homologyMap φ.τ₂ m) :=
      HomologicalComplex.HomologySequence.isIso_homologyMap_τ₂ φ hS₁ hS₂ m
        (fun i _ ↦ @IsIso.epi_of_iso _ _ _ _ _ (hτ₃ i)) (hτ₁ m) (hτ₃ m)
        (fun i _ ↦ @IsIso.mono_of_iso _ _ _ _ _ (hτ₁ i))
    have hfst : TopPair.Hom.fst (skeletonPairProj p k) = skeletonProj p (k + 1) :=
      TopPair.ofInclusionMap_fst _ _
    rwa [TopPair.homologyMap_chainComplexShortComplexMap_τ₂, hfst] at hτ₂

/-- For any Serre fibration `q : X ⟶ B` over a CW complex `B`, the inclusion
`q⁻¹(skeletonLT univ (n + 2)) ↪ X` induces an isomorphism on `H_n(-; R)`. -/
private lemma isIso_singularHomologyMap_skeletonSubtypeVal {X : _root_.TopCat.{u}} {q : X ⟶ B}
    (hq : serreFibrations q) (R : Type u) [Ring R] (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map
      (_root_.TopCat.ofHom (ContinuousMap.subtypeVal
        (q ⁻¹' (skeletonLT (univ : Set B) ((n + 2 : ℕ) : ℕ∞) : Set B))))) := by
  have hk : ((n + 1 + 1 : ℕ) : ℕ∞) ≤ ⊤ := le_top
  let P := TopPair.ofInclusion (X := X)
    (preimage_mono (f := q) (skeletonLT_mono (C := (univ : Set B)) hk))
  have h₁ : IsZero (P.singularHomology (ModuleCat.of R R) (n + 1)) :=
    isZero_singularHomology_preimage_skeletonLT hq R hk le_rfl
  have h₀ : IsZero (P.singularHomology (ModuleCat.of R R) n) :=
    isZero_singularHomology_preimage_skeletonLT hq R hk (Nat.le_succ n)
  have : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map
      P.map) := by
    rw [singularHomologyFunctor_obj_map]
    exact P.isIso_homologyMap_map_of_isZero (ModuleCat.of R R) h₁ h₀
  let u : P.fst ⟶ X := _root_.TopCat.ofHom (ContinuousMap.subtypeVal _)
  have hu : IsIso u := by
    rw [_root_.TopCat.isIso_iff_isHomeomorph]
    have htop : q ⁻¹' (skeletonLT (univ : Set B) ⊤ : Set B) = univ := by simp
    exact (Homeomorph.setCongr htop).trans (Homeomorph.Set.univ X) |>.isHomeomorph
  have hcomp_iso : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).map (P.map ≫ u)) := by
    rw [Functor.map_comp]
    infer_instance
  have hcomp : P.map ≫ u = _root_.TopCat.ofHom (ContinuousMap.subtypeVal
      (q ⁻¹' (skeletonLT (univ : Set B) ((n + 2 : ℕ) : ℕ∞) : Set B))) :=
    _root_.TopCat.ext fun _ ↦ rfl
  rwa [hcomp] at hcomp_iso

/-- Step 2: Over a CW complex `B`, a Serre fibration whose fibres have the `R`-homology of a point
induces homology isomorphisms in all degrees. -/
private lemma isIso_singularHomologyMap_of_cwComplex (hp : serreFibrations p) (R : Type u)
    [Ring R] (hF₀ : ∀ b : B, PathConnectedSpace (p.fiber b))
    (hF : ∀ b : B, ∀ q > 0, IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).obj (p.fiber b))) (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map p) := by
  let H := (singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)
  let ιE : _root_.TopCat.of (p ⁻¹' (skeletonLT (univ : Set B) ((n + 2 : ℕ) : ℕ∞) : Set B)) ⟶ E :=
    _root_.TopCat.ofHom (ContinuousMap.subtypeVal _)
  let ιB : _root_.TopCat.of ((𝟙 B) ⁻¹' (skeletonLT (univ : Set B) ((n + 2 : ℕ) : ℕ∞) : Set B)) ⟶
      B :=
    _root_.TopCat.ofHom (ContinuousMap.subtypeVal _)
  have : IsIso (H.map ιE) := isIso_singularHomologyMap_skeletonSubtypeVal hp R n
  have : IsIso (H.map ιB) :=
    isIso_singularHomologyMap_skeletonSubtypeVal (MorphismProperty.id_mem _ _) R n
  have : IsIso (H.map (skeletonProj p (n + 2))) :=
    isIso_singularHomologyMap_skeletonProj hp R hF₀ hF (n + 2) n
  have hcomm : ιE ≫ p = skeletonProj p (n + 2) ≫ ιB := _root_.TopCat.ext fun _ ↦ rfl
  have : IsIso (H.map ιE ≫ H.map p) := by
    rw [← H.map_comp, hcomm, H.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left (H.map ιE) (H.map p)

end CWBase

end AcyclicFiber

/-- **A Serre fibration whose fibres have the `R`-homology of a point induces isomorphisms on
singular homology.** Let `p : E ⟶ B` be a Serre fibration over an arbitrary topological space `B`,
and let `R` be a ring. If every fibre `p⁻¹(b)` is path-connected and has vanishing `R`-homology in
positive degrees, then `p` induces an isomorphism `H_n(E; R) ≅ H_n(B; R)` for every `n : ℕ`. -/
theorem isIso_singularHomologyMap_of_forall_fiber {E B : _root_.TopCat.{u}} {p : E ⟶ B}
    (hp : serreFibrations p) (R : Type u) [Ring R]
    (hF₀ : ∀ b : B, PathConnectedSpace (p.fiber b))
    (hF : ∀ b : B, ∀ q > 0, IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).obj (p.fiber b))) (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map p) := by
  let g := sigmaCWApproximationMap B
  let p' := _root_.TopCat.pullbackFst g p
  let H := (singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)
  have hp' : serreFibrations p' := mem_serreFibrations_pullbackFst hp g
  have hF'₀ (y : sigmaCWApproximation B) : PathConnectedSpace (p'.fiber y) :=
    @Homeomorph.pathConnectedSpace _ _ _ _ (hF₀ (g y))
      (_root_.TopCat.homeoOfIso (p.fiberPullbackFstIso g y)).symm
  have hF' (y : sigmaCWApproximation B) (q : ℕ) (hq : q > 0) :
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p'.fiber y)) :=
    (hF (g y) q hq).of_iso (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).mapIso (p.fiberPullbackFstIso g y))
  have : IsIso (H.map p') := AcyclicFiber.isIso_singularHomologyMap_of_cwComplex hp' R hF'₀ hF' n
  have : IsIso (H.map g) :=
    (isWeakHomotopyEquivalence_sigmaCWApproximationMap B).isIso_singularHomologyMap
      (ModuleCat.of R R) n
  have : IsIso (H.map (_root_.TopCat.pullbackSnd g p)) :=
    (isWeakHomotopyEquivalence_pullbackSnd hp
      (isWeakHomotopyEquivalence_sigmaCWApproximationMap B)).isIso_singularHomologyMap
        (ModuleCat.of R R) n
  have hcomm : _root_.TopCat.pullbackSnd g p ≫ p = p' ≫ g := _root_.TopCat.ext fun q ↦ q.2.symm
  have : IsIso (H.map (_root_.TopCat.pullbackSnd g p) ≫ H.map p) := by
    rw [← H.map_comp, hcomm, H.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left (H.map (_root_.TopCat.pullbackSnd g p)) (H.map p)

/-- **Single-fibre homology isomorphism criterion for a Serre fibration over a path-connected
base.** Let `p : E ⟶ B` be a Serre fibration over a path-connected space `B`, and let `b₀ : B`. If
the fibre `p⁻¹(b₀)` is path-connected and has vanishing `R`-homology in positive degrees, then `p`
induces an isomorphism `H_n(E; R) ≅ H_n(B; R)` for every `n : ℕ`. -/
theorem isIso_singularHomologyMap_of_fiber {E B : _root_.TopCat.{u}} [PathConnectedSpace B]
    {p : E ⟶ B} (hp : serreFibrations p) (b₀ : B) (R : Type u) [Ring R]
    (hF₀ : PathConnectedSpace (p.fiber b₀))
    (hF : ∀ q > 0, IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).obj (p.fiber b₀))) (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map p) :=
  isIso_singularHomologyMap_of_forall_fiber hp R
    (fun b ↦ (pathConnectedSpace_fiber_iff_of_joined hp (PathConnectedSpace.joined b₀ b)).1 hF₀)
    (fun b q hq ↦ (isZero_singularHomology_fiber_iff_of_joined hp (PathConnectedSpace.joined b₀ b)
      (ModuleCat.of R R) q).1 (hF q hq)) n

end TopCat

/-- **A simply connected space whose loop space is `R`-acyclic is itself `R`-acyclic.** Let `(X, x)`
be a path-connected space with trivial `π₁(X, x)`, and let `R` be a ring. If
`H_{q+1}(Ω X x; R) = 0` for every `q : ℕ`, then `H_{n+1}(X; R) = 0` for every `n : ℕ`. -/
theorem isZero_singularHomology_of_loopSpace {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) (hπ₁ : Subsingleton (π_ 1 X x)) (R : Type u) [Ring R]
    (hΩ : ∀ q : ℕ, IsZero (((singularChains R).obj (_root_.TopCat.of (Ω X x))).homology (q + 1)))
    (n : ℕ) :
    IsZero (((singularChains R).obj (_root_.TopCat.of X)).homology (n + 1)) := by
  let p := _root_.TopCat.Hom.homotopyFiberProj (𝟙 (_root_.TopCat.of X)) x
  let e := _root_.TopCat.Hom.homotopyFiberFiberHomeomorph (𝟙 (_root_.TopCat.of X)) x
  have hΩ₀ : PathConnectedSpace (Ω X x) :=
    (pathConnectedSpace_loopSpace_iff_subsingleton_pi1 x).2 hπ₁
  have hF₀ : PathConnectedSpace (p.fiber x) := @Homeomorph.pathConnectedSpace _ _ _ _ hΩ₀ e.symm
  have hF (q : ℕ) (hq : q > 0) :
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber x)) := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    exact (hΩ m).of_iso (((singularHomologyFunctor (ModuleCat.{u} R) (m + 1)).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo e))
  have : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) (n + 1)).obj
      (ModuleCat.of R R)).map p) :=
    TopCat.isIso_singularHomologyMap_of_fiber
      (_root_.TopCat.Hom.serreFibrations_homotopyFiberProj (𝟙 (_root_.TopCat.of X)) x)
      x R hF₀ hF (n + 1)
  have hEP : IsZero (((singularHomologyFunctor (ModuleCat.{u} R) (n + 1)).obj
      (ModuleCat.of R R)).obj (_root_.TopCat.of (MappingPathFiber (.id X) x))) :=
    isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of R R)
      (_root_.TopCat.of (MappingPathFiber (.id X) x)) (Nat.succ_ne_zero n)
  exact hEP.of_iso (asIso (((singularHomologyFunctor (ModuleCat.{u} R) (n + 1)).obj
    (ModuleCat.of R R)).map p)).symm

end TauCeti

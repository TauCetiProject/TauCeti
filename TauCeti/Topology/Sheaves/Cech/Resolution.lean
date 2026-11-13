/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import TauCeti.Algebra.Homology.Ext.AcyclicResolution
public import TauCeti.Algebra.Homology.Single.Kernel
public import TauCeti.Topology.Sheaves.Cech.LongExactSequence

/-!
# Flasque resolutions compute Čech cohomology on compact normal spaces

Let `X` be a compact normal space and `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` a resolution of a sheaf of
modules `F` by flasque sheaves. Write `Hⁿ(X, -)` for the cover-colimit Čech cohomology
`TauCeti.Topology.cechCohomology`, `Γ` for global sections and `Zⁿ` for the cycles of `K` in
degree `n`. The resolution splits into the short exact sequences `0 ⟶ F ⟶ K⁰ ⟶ Z¹ ⟶ 0` and
`0 ⟶ Zⁿ ⟶ Kⁿ ⟶ Zⁿ⁺¹ ⟶ 0`. Composing the connecting maps of their long exact Čech sequences gives
the iterated connecting map `Hᵏ(X, Zⁿ⁺¹) ⟶ Hᵏ⁺ⁿ⁺¹(X, F)` (`TauCeti.Topology.resolutionCechδ`).
As flasque sheaves have no higher Čech cohomology, it is an isomorphism for `k ≥ 1`, and for
`k = 0` it is onto with kernel the image of `H⁰(X, Kⁿ)`. In degree `0` Čech cohomology is the
module of global sections, so `Hⁿ⁺¹(X, F)` is the cokernel of `Γ(Kⁿ) ⟶ Γ(Zⁿ⁺¹)`, which is the
cohomology of the complex of global sections `Γ(K)` in degree `n + 1`. Hence
`Hⁿ(X, F) ≅ Hⁿ(Γ(K))` (`TauCeti.Topology.cechCohomologyObjIsoOfIsFlasque`), naturally in
morphisms of resolutions (`TauCeti.Topology.cechCohomologyObjIsoOfIsFlasque_hom_naturality`).

Combined with `CategoryTheory.Sheaf.rightDerivedΓObjIsoOfIsFlasque`, this identifies the
cover-colimit Čech cohomology of a sheaf of modules on a compact normal space, for instance a
compact Hausdorff space, with the right derived functors of global sections.

## Main definitions

* `TauCeti.Topology.resolutionCechδ`: the iterated connecting map
  `Hᵏ(X, Zⁿ⁺¹) ⟶ Hᵏ⁺ⁿ⁺¹(X, F)` of a resolution.
* `TauCeti.Topology.cechCohomologyObjIsoOfIsFlasque`: `Hⁿ(X, F) ≅ Hⁿ(Γ(K))` for a flasque
  resolution `K` of `F`.

## Main results

* `TauCeti.Topology.isIso_resolutionCechδ`: the iterated connecting map is an isomorphism in
  positive source degree.
* `TauCeti.Topology.cechCohomologyObjIsoOfIsFlasque_succ_hom`: in degree `n + 1` the comparison
  sends the image of a global section of `Zⁿ⁺¹` under the iterated connecting map to the
  cohomology class of that section; `TauCeti.Topology.cechCohomologyObjIsoOfIsFlasque_zero_hom` is
  the degree `0` statement.
* `TauCeti.Topology.cechCohomologyObjIsoOfIsFlasque_hom_naturality`: the comparison is natural
  in morphisms of resolutions.

## References

* The Stacks Project, Cohomology of Sheaves, Lemma 20.16.2 (tag 09V2), and Derived Categories,
  Lemma 13.15.6 (tag 05T8).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} {R : Type u} [Ring R]
  {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
  {K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
  (ι : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso ι]

-- `fromSingle₀Equiv` sends `ι` to `ι.f 0`, whose source `((single₀ _).obj F).X 0` is `F` by
-- unfolding `single₀`
private instance : Mono (CochainComplex.fromSingle₀Equiv K F ι).1 :=
  inferInstanceAs (Mono (ι.f 0))

/-- The short exact sequence `0 ⟶ F ⟶ K⁰ ⟶ Z¹ ⟶ 0` of a resolution. -/
private lemma shortExact_zero :
    (ShortComplex.mk (CochainComplex.fromSingle₀Equiv K F ι).1 (K.toCycles 0 1)
      (K.comp_toCycles_eq_zero 1 _ (CochainComplex.fromSingle₀Equiv K F ι).2)).ShortExact :=
  K.shortExact_resolution_zero (CochainComplex.fromSingle₀Equiv K F ι).1
    (CochainComplex.fromSingle₀Equiv K F ι).2
    (CochainComplex.exact_f_zero_of_quasiIsoAt ι)
    (fun j ↦ CochainComplex.exactAt_succ_of_quasiIsoAt ι j)

include ι in
/-- The short exact sequence `0 ⟶ Zⁿ⁺¹ ⟶ Kⁿ⁺¹ ⟶ Zⁿ⁺² ⟶ 0` of a resolution. -/
private lemma shortExact_succ (n : ℕ) :
    (ShortComplex.mk (K.iCycles (n + 1)) (K.toCycles (n + 1) (n + 2))
      (K.iCycles_toCycles _ _)).ShortExact :=
  K.shortExact_resolution_succ (fun j ↦ CochainComplex.exactAt_succ_of_quasiIsoAt ι j) n

/-- Global sections are degree `0` Čech cohomology. -/
private def sectionsIsoCechZero (G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj G ≅
      (cechCohomology X (ModuleCat.{u} R) 0).obj G.obj :=
  (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).app G ≪≫ cechCohomologyZeroIso G

@[reassoc]
private lemma sectionsIsoCechZero_hom_naturality
    {G G' : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (f : G ⟶ G') :
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map f ≫
        (sectionsIsoCechZero G').hom =
      (sectionsIsoCechZero G).hom ≫ (cechCohomology X (ModuleCat.{u} R) 0).map f.hom := by
  simp only [sectionsIsoCechZero, Iso.trans_hom, Iso.app_hom, Category.assoc,
    ← cechCohomologyZeroIso_hom_naturality]
  exact ((Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).hom.naturality_assoc f _)

/-- The cycles of `Γ(K)` in degree `n + 1` are the global sections of `Zⁿ⁺¹`. -/
private def isLimitSucc (n : ℕ) :
    IsLimit (KernelFork.ofι ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map
      (K.iCycles (n + 1))) (by simp [← Functor.map_comp]) :
        KernelFork ((((Sheaf.Γ (Opens.grothendieckTopology X)
          (ModuleCat.{u} R)).mapHomologicalComplex _).obj K).sc' n (n + 1) (n + 2)).g) :=
  KernelFork.mapIsLimit _ (K.cyclesIsKernel (n + 1) (n + 2) (by simp)) _

private lemma isLimitSucc_lift (n : ℕ) :
    (isLimitSucc (K := K) n).lift (KernelFork.ofι _ ((((Sheaf.Γ (Opens.grothendieckTopology X)
      (ModuleCat.{u} R)).mapHomologicalComplex _).obj K).sc' n (n + 1) (n + 2)).zero) =
      (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map (K.toCycles n (n + 1)) :=
  Fork.IsLimit.hom_ext (isLimitSucc n) (by
    rw [Fork.IsLimit.lift_ι]
    simp [← Functor.map_comp])

/-- The global sections of `F` are the kernel of `Γ(K⁰) ⟶ Γ(K¹)`. -/
private def isLimitZero :
    IsLimit (KernelFork.ofι ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map
      (CochainComplex.fromSingle₀Equiv K F ι).1)
      (by dsimp; rw [← Functor.map_comp, (CochainComplex.fromSingle₀Equiv K F ι).2,
        Functor.map_zero]) :
        KernelFork ((((Sheaf.Γ (Opens.grothendieckTopology X)
          (ModuleCat.{u} R)).mapHomologicalComplex _).obj K).sc' 0 0 1).g) :=
  KernelFork.mapIsLimit _ (CochainComplex.exact_f_zero_of_quasiIsoAt ι).fIsKernel _

private lemma isLimitZero_lift :
    (isLimitZero ι).lift (KernelFork.ofι _ ((((Sheaf.Γ (Opens.grothendieckTopology X)
      (ModuleCat.{u} R)).mapHomologicalComplex _).obj K).sc' 0 0 1).zero) = 0 :=
  Fork.IsLimit.hom_ext (isLimitZero ι) (by
    rw [Fork.IsLimit.lift_ι, zero_comp]
    simp)

private lemma isLimitZero_lift_comp :
    (isLimitZero ι).lift (KernelFork.ofι _ ((((Sheaf.Γ (Opens.grothendieckTopology X)
      (ModuleCat.{u} R)).mapHomologicalComplex _).obj K).sc' 0 0 1).zero) ≫
        (sectionsIsoCechZero F).hom = 0 := by
  rw [isLimitZero_lift, zero_comp]

/-- The left homology data of `0 ⟶ Γ(K⁰) ⟶ Γ(K¹)` with cycles `Γ(F)` and homology `H⁰(X, F)`. -/
private abbrev leftHomologyDataZero :
    ((((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj
      K).sc' 0 0 1).LeftHomologyData where
  K := (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj F
  H := (cechCohomology X (ModuleCat.{u} R) 0).obj F.obj
  i := (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map
    (CochainComplex.fromSingle₀Equiv K F ι).1
  π := (sectionsIsoCechZero F).hom
  wi := by
    dsimp
    rw [← Functor.map_comp, (CochainComplex.fromSingle₀Equiv K F ι).2, Functor.map_zero]
  hi := isLimitZero ι
  wπ := isLimitZero_lift_comp ι
  hπ := ((ShortComplex.exact_iff_mono (ShortComplex.mk _ _ (isLimitZero_lift_comp ι))
    (isLimitZero_lift ι)).2 (by dsimp; infer_instance)).gIsCokernel

@[reassoc]
private lemma leftHomologyDataZero_π_comp_homologyIso_inv :
    (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).hom.app F ≫ (cechCohomologyZeroIso F).hom ≫
        (leftHomologyDataZero ι).homologyIso.inv =
      (leftHomologyDataZero ι).cyclesIso.inv ≫ ShortComplex.homologyπ _ := by
  -- the projection of `leftHomologyDataZero ι` is `sectionsIsoCechZero F`
  simpa [leftHomologyDataZero, sectionsIsoCechZero] using
    (leftHomologyDataZero ι).π_comp_homologyIso_inv

private lemma leftHomologyDataZero_cyclesIso_inv :
    (leftHomologyDataZero ι).cyclesIso.inv ≫
      (HomologicalComplex.cyclesIsoSc' _ 0 0 1 (by simp) (by simp)).inv =
      (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj
        K).liftCycles ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map
          (CochainComplex.fromSingle₀Equiv K F ι).1) 1 (by simp)
          (by dsimp; rw [← Functor.map_comp, (CochainComplex.fromSingle₀Equiv K F ι).2,
            Functor.map_zero]) := by
  rw [← cancel_mono (HomologicalComplex.iCycles _ _), Category.assoc,
    HomologicalComplex.cyclesIsoSc'_inv_iCycles,
    ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles, HomologicalComplex.liftCycles_i]

variable [CompactSpace X] [NormalSpace X]

include ι in
/-- The iterated connecting map `Hᵏ(X, Zⁿ⁺¹) ⟶ Hᵐ(X, F)`, `m = k + n + 1`, of a resolution
`ι : F[0] ⟶ K` with cycles `Zʲ`: the composite of the connecting maps of the long exact Čech
sequences of `0 ⟶ Zⁿ ⟶ Kⁿ ⟶ Zⁿ⁺¹ ⟶ 0`, …, `0 ⟶ Z¹ ⟶ K¹ ⟶ Z² ⟶ 0` and
`0 ⟶ F ⟶ K⁰ ⟶ Z¹ ⟶ 0` for `n ≥ 1`, and the connecting map of `0 ⟶ F ⟶ K⁰ ⟶ Z¹ ⟶ 0` alone for
`n = 0` (`TauCeti.Topology.resolutionCechδ_zero` and `TauCeti.Topology.resolutionCechδ_succ`). -/
def resolutionCechδ : (n : ℕ) → {k m : ℕ} → k + n + 1 = m →
    ((cechCohomology X (ModuleCat.{u} R) k).obj (K.cycles (n + 1)).obj ⟶
      (cechCohomology X (ModuleCat.{u} R) m).obj F.obj)
  | 0, k, _, rfl => (shortExact_zero ι).cechCohomologyδ k
  | n + 1, k, _, h => (shortExact_succ ι n).cechCohomologyδ k ≫
      resolutionCechδ n (k := k + 1) (by omega)

/-- For `n = 0` the iterated connecting map is the connecting map of `0 ⟶ F ⟶ K⁰ ⟶ Z¹ ⟶ 0`. -/
lemma resolutionCechδ_zero (k : ℕ)
    (hS : (ShortComplex.mk (CochainComplex.fromSingle₀Equiv K F ι).1 (K.toCycles 0 1)
      (K.comp_toCycles_eq_zero 1 _ (CochainComplex.fromSingle₀Equiv K F ι).2)).ShortExact) :
    resolutionCechδ ι 0 (k := k) rfl = hS.cechCohomologyδ k := by
  rw [resolutionCechδ]

/-- The iterated connecting map starts with the connecting map of
`0 ⟶ Zⁿ⁺¹ ⟶ Kⁿ⁺¹ ⟶ Zⁿ⁺² ⟶ 0`. -/
lemma resolutionCechδ_succ (n : ℕ) {k m : ℕ} (h : k + (n + 1) + 1 = m)
    (hS : (ShortComplex.mk (K.iCycles (n + 1)) (K.toCycles (n + 1) (n + 2))
      (K.iCycles_toCycles _ _)).ShortExact) :
    resolutionCechδ ι (n + 1) h =
      hS.cechCohomologyδ k ≫ resolutionCechδ ι n (k := k + 1) (by omega) := by
  rw [resolutionCechδ]

/-- The composite `H⁰(X, Kⁿ) ⟶ H⁰(X, Zⁿ⁺¹) ⟶ Hⁿ⁺¹(X, F)` vanishes. -/
@[reassoc (attr := simp)]
theorem cechCohomology_map_toCycles_comp_resolutionCechδ (n : ℕ) {m : ℕ} (h : 0 + n + 1 = m) :
    (cechCohomology X (ModuleCat.{u} R) 0).map (K.toCycles n (n + 1)).hom ≫
      resolutionCechδ ι n h = 0 := by
  cases n with
  | zero =>
    subst h
    exact (shortExact_zero ι).cechCohomology_comp_δ 0
  | succ n =>
    rw [resolutionCechδ_succ ι n h (shortExact_succ ι n),
      (shortExact_succ ι n).cechCohomology_comp_δ_assoc 0, zero_comp]

private lemma isLimitSucc_lift_comp (n : ℕ) :
    (isLimitSucc (K := K) n).lift (KernelFork.ofι _ ((((Sheaf.Γ (Opens.grothendieckTopology X)
      (ModuleCat.{u} R)).mapHomologicalComplex _).obj K).sc' n (n + 1) (n + 2)).zero) ≫
        (sectionsIsoCechZero _).hom ≫ resolutionCechδ ι n (k := 0) (m := n + 1) (by omega) = 0 := by
  rw [isLimitSucc_lift, sectionsIsoCechZero_hom_naturality_assoc,
    cechCohomology_map_toCycles_comp_resolutionCechδ, comp_zero]

variable (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).obj)
include hK

/-- **Dimension shifting along a flasque resolution.** The iterated connecting map
`Hᵏ⁺¹(X, Zⁿ⁺¹) ⟶ Hᵏ⁺ⁿ⁺²(X, F)` of a flasque resolution is an isomorphism. -/
theorem isIso_resolutionCechδ (n : ℕ) {k m : ℕ} (h : k + 1 + n + 1 = m) :
    IsIso (resolutionCechδ ι n h) := by
  induction n generalizing k m with
  | zero =>
    subst h
    have := hK 0
    exact (shortExact_zero ι).isIso_cechCohomologyδ_succ_of_isFlasque k
  | succ n ih =>
    have := hK (n + 1)
    have := ih (k := k + 1) (m := m) (by omega)
    have := (shortExact_succ ι n).isIso_cechCohomologyδ_succ_of_isFlasque k
    rw [resolutionCechδ_succ ι n h (shortExact_succ ι n)]
    infer_instance

/-- The iterated connecting map `H⁰(X, Zⁿ⁺¹) ⟶ Hⁿ⁺¹(X, F)` of a flasque resolution is onto. -/
theorem epi_resolutionCechδ (n : ℕ) {m : ℕ} (h : 0 + n + 1 = m) :
    Epi (resolutionCechδ ι n h) := by
  cases n with
  | zero =>
    subst h
    have := hK 0
    exact (shortExact_zero ι).epi_cechCohomologyδ_zero_of_isFlasque
  | succ n =>
    have := hK (n + 1)
    have := isIso_resolutionCechδ ι hK n (k := 0) (m := m) (by omega)
    have := (shortExact_succ ι n).epi_cechCohomologyδ_zero_of_isFlasque
    rw [resolutionCechδ_succ ι n h (shortExact_succ ι n)]
    infer_instance

/-- The kernel of the iterated connecting map `H⁰(X, Zⁿ⁺¹) ⟶ Hⁿ⁺¹(X, F)` of a flasque resolution
is the image of `H⁰(X, Kⁿ)`. -/
theorem exact_resolutionCechδ (n : ℕ) {m : ℕ} (h : 0 + n + 1 = m) :
    (ShortComplex.mk _ _ (cechCohomology_map_toCycles_comp_resolutionCechδ ι n h)).Exact := by
  cases n with
  | zero =>
    subst h
    exact (shortExact_zero ι).cechCohomology_exact₃ 0
  | succ n =>
    have := isIso_resolutionCechδ ι hK n (k := 0) (m := m) (by omega)
    let φ : ShortComplex.mk _ _ ((shortExact_succ ι n).cechCohomology_comp_δ 0) ⟶
        ShortComplex.mk _ _ (cechCohomology_map_toCycles_comp_resolutionCechδ ι (n + 1) h) :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := resolutionCechδ ι n (k := 0 + 1) (m := m) (by omega)
        comm₂₃ := by simp [resolutionCechδ_succ ι n h (shortExact_succ ι n)] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
      ((shortExact_succ ι n).cechCohomology_exact₃ 0)

/-- The left homology data of `Γ(Kⁿ) ⟶ Γ(Kⁿ⁺¹) ⟶ Γ(Kⁿ⁺²)` with cycles `Γ(Zⁿ⁺¹)` and homology
`Hⁿ⁺¹(X, F)`, the projection being the iterated connecting map. -/
private abbrev leftHomologyDataSucc (n : ℕ) :
    ((((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj
      K).sc' n (n + 1) (n + 2)).LeftHomologyData where
  K := (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj (K.cycles (n + 1))
  H := (cechCohomology X (ModuleCat.{u} R) (n + 1)).obj F.obj
  i := (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map (K.iCycles (n + 1))
  π := (sectionsIsoCechZero _).hom ≫ resolutionCechδ ι n (k := 0) (by omega)
  wi := by simp [← Functor.map_comp]
  hi := isLimitSucc n
  wπ := isLimitSucc_lift_comp ι n
  hπ := by
    have := epi_resolutionCechδ ι hK n (m := n + 1) (by omega)
    have hex : (ShortComplex.mk _ _ (isLimitSucc_lift_comp ι n)).Exact := by
      let e : ShortComplex.mk _ _ (isLimitSucc_lift_comp ι n) ≅ ShortComplex.mk _ _
          (cechCohomology_map_toCycles_comp_resolutionCechδ ι n (m := n + 1) (by omega)) :=
        ShortComplex.isoMk (sectionsIsoCechZero _) (sectionsIsoCechZero _) (Iso.refl _)
          (by dsimp only; rw [isLimitSucc_lift, sectionsIsoCechZero_hom_naturality]) (by simp)
      exact (ShortComplex.exact_iff_of_iso e).2 (exact_resolutionCechδ ι hK n (by omega))
    exact hex.gIsCokernel

/-- **Flasque resolutions compute Čech cohomology on compact normal spaces.** For a flasque
resolution `ι : F[0] ⟶ K` of a sheaf of modules `F` on a compact normal space `X`, the
cover-colimit Čech cohomology `Hⁿ(X, F)` is the cohomology of the complex of global sections
`Γ(K)`. In positive degrees the comparison is described by the iterated connecting map
(`TauCeti.Topology.cechCohomologyObjIsoOfIsFlasque_succ_hom`), and in degree `0` by the
identification of `H⁰(X, F)` with the global sections of `F`
(`TauCeti.Topology.cechCohomologyObjIsoOfIsFlasque_zero_hom`). -/
def cechCohomologyObjIsoOfIsFlasque : (n : ℕ) →
    ((cechCohomology X (ModuleCat.{u} R) n).obj F.obj ≅
      (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj
        K).homology n)
  | 0 => (leftHomologyDataZero ι).homologyIso.symm ≪≫
      (HomologicalComplex.homologyIsoSc' _ 0 0 1 (by simp) (by simp)).symm
  | n + 1 => (leftHomologyDataSucc ι hK n).homologyIso.symm ≪≫
      (HomologicalComplex.homologyIsoSc' _ n (n + 1) (n + 2) (by simp) (by simp)).symm

@[reassoc]
private lemma leftHomologyDataSucc_π_comp_homologyIso_inv (n : ℕ) :
    (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).hom.app (K.cycles (n + 1)) ≫
      (cechCohomologyZeroIso (K.cycles (n + 1))).hom ≫
        resolutionCechδ ι n (k := 0) (m := n + 1) (by omega) ≫
          (leftHomologyDataSucc ι hK n).homologyIso.inv =
      (leftHomologyDataSucc ι hK n).cyclesIso.inv ≫ ShortComplex.homologyπ _ := by
  -- the projection of `leftHomologyDataSucc ι hK n` is `sectionsIsoCechZero` followed by the
  -- iterated connecting map
  simpa [leftHomologyDataSucc, sectionsIsoCechZero] using
    (leftHomologyDataSucc ι hK n).π_comp_homologyIso_inv

private lemma leftHomologyDataSucc_cyclesIso_inv (n : ℕ) :
    (leftHomologyDataSucc ι hK n).cyclesIso.inv ≫
      (HomologicalComplex.cyclesIsoSc' _ n (n + 1) (n + 2) (by simp) (by simp)).inv =
      (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj
        K).liftCycles ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map
          (K.iCycles (n + 1))) (n + 2) (by simp) (by simp [← Functor.map_comp]) := by
  rw [← cancel_mono (HomologicalComplex.iCycles _ _), Category.assoc,
    HomologicalComplex.cyclesIsoSc'_inv_iCycles,
    ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles, HomologicalComplex.liftCycles_i]

/-- In degree `n + 1`, the comparison `cechCohomologyObjIsoOfIsFlasque` sends the image of a
global section of `Zⁿ⁺¹` under the iterated connecting map to the cohomology class of that section
in `Γ(K)`. -/
theorem cechCohomologyObjIsoOfIsFlasque_succ_hom (n : ℕ) :
    (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).hom.app (K.cycles (n + 1)) ≫
      (cechCohomologyZeroIso (K.cycles (n + 1))).hom ≫
        resolutionCechδ ι n (k := 0) (m := n + 1) (by omega) ≫
          (cechCohomologyObjIsoOfIsFlasque ι hK (n + 1)).hom =
      (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj
        K).liftCycles ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map
          (K.iCycles (n + 1))) (n + 2) (by simp) (by simp [← Functor.map_comp]) ≫
        (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj
          K).homologyπ (n + 1) := by
  rw [cechCohomologyObjIsoOfIsFlasque, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    leftHomologyDataSucc_π_comp_homologyIso_inv_assoc, HomologicalComplex.π_homologyIsoSc'_inv,
    ← leftHomologyDataSucc_cyclesIso_inv ι hK n, Category.assoc]

/-- In degree `0`, the comparison `cechCohomologyObjIsoOfIsFlasque` sends the image in
`H⁰(X, F)` of a global section of `F` to the cohomology class of its image in `Γ(K⁰)`. -/
theorem cechCohomologyObjIsoOfIsFlasque_zero_hom :
    (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).hom.app F ≫ (cechCohomologyZeroIso F).hom ≫
        (cechCohomologyObjIsoOfIsFlasque ι hK 0).hom =
      (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj
        K).liftCycles ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map
          (CochainComplex.fromSingle₀Equiv K F ι).1) 1 (by simp)
          (by dsimp; rw [← Functor.map_comp, (CochainComplex.fromSingle₀Equiv K F ι).2,
            Functor.map_zero]) ≫
        (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj
          K).homologyπ 0 := by
  rw [cechCohomologyObjIsoOfIsFlasque, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    leftHomologyDataZero_π_comp_homologyIso_inv_assoc, HomologicalComplex.π_homologyIsoSc'_inv,
    ← leftHomologyDataZero_cyclesIso_inv ι, Category.assoc]

section Naturality

variable {G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
  {L : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
  (ι' : (CochainComplex.single₀ _).obj G ⟶ L) [QuasiIso ι'] {f : F ⟶ G} {φ : K ⟶ L}
  (hφ : ι ≫ φ = (CochainComplex.single₀ _).map f ≫ ι')

omit hK

include hφ in
/-- **Naturality of the iterated connecting map** in morphisms of resolutions: for a morphism
`φ : K ⟶ L` of resolutions over `f : F ⟶ G`, the iterated connecting maps commute with the maps
induced by `f` and by `φ` on cycles. -/
@[reassoc]
theorem resolutionCechδ_naturality (n : ℕ) {k m : ℕ} (h : k + n + 1 = m) :
    resolutionCechδ ι n h ≫ (cechCohomology X (ModuleCat.{u} R) m).map f.hom =
      (cechCohomology X (ModuleCat.{u} R) k).map (HomologicalComplex.cyclesMap φ (n + 1)).hom ≫
        resolutionCechδ ι' n h := by
  induction n generalizing k m with
  | zero =>
    subst h
    rw [resolutionCechδ_zero ι k (shortExact_zero ι),
      resolutionCechδ_zero ι' k (shortExact_zero ι')]
    exact (shortExact_zero ι).cechCohomologyδ_naturality (shortExact_zero ι')
      { τ₁ := f, τ₂ := φ.f 0, τ₃ := HomologicalComplex.cyclesMap φ 1
        comm₁₂ := (CochainComplex.fromSingle₀Equiv_comp_f_zero hφ).symm
        comm₂₃ := (HomologicalComplex.toCycles_cyclesMap φ 0 1).symm } k
  | succ n ih =>
    rw [resolutionCechδ_succ ι n h (shortExact_succ ι n),
      resolutionCechδ_succ ι' n h (shortExact_succ ι' n), Category.assoc, ih]
    exact (shortExact_succ ι n).cechCohomologyδ_naturality_assoc (shortExact_succ ι' n)
      { τ₁ := HomologicalComplex.cyclesMap φ (n + 1), τ₂ := φ.f (n + 1)
        τ₃ := HomologicalComplex.cyclesMap φ (n + 2)
        comm₁₂ := HomologicalComplex.cyclesMap_i φ (n + 1)
        comm₂₃ := (HomologicalComplex.toCycles_cyclesMap φ (n + 1) (n + 2)).symm } k _

include hK hφ in
/-- **Naturality of the comparison** `Hⁿ(X, F) ≅ Hⁿ(Γ(K))` in morphisms of flasque resolutions:
for a morphism `φ : K ⟶ L` of resolutions over `f : F ⟶ G`, the comparison intertwines the map
`Hⁿ(X, F) ⟶ Hⁿ(X, G)` induced by `f` with the map induced by `Γ(φ)` in cohomology. -/
@[reassoc]
theorem cechCohomologyObjIsoOfIsFlasque_hom_naturality
    (hL : ∀ n, TopCat.Presheaf.IsFlasque (L.X n).obj) (n : ℕ) :
    (cechCohomology X (ModuleCat.{u} R) n).map f.hom ≫
        (cechCohomologyObjIsoOfIsFlasque ι' hL n).hom =
      (cechCohomologyObjIsoOfIsFlasque ι hK n).hom ≫ HomologicalComplex.homologyMap
        (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).map
          φ) n := by
  cases n with
  | zero =>
    rw [← cancel_epi ((Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).hom.app F ≫
      (cechCohomologyZeroIso F).hom)]
    have e := sectionsIsoCechZero_hom_naturality f
    simp only [sectionsIsoCechZero, Iso.trans_hom, Iso.app_hom, Category.assoc] at e
    simp only [Category.assoc]
    rw [← reassoc_of% e, cechCohomologyObjIsoOfIsFlasque_zero_hom,
      reassoc_of% (cechCohomologyObjIsoOfIsFlasque_zero_hom ι hK),
      HomologicalComplex.homologyπ_naturality, HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
      HomologicalComplex.comp_liftCycles_assoc]
    congr 2
    simp only [Functor.mapHomologicalComplex_map_f, ← Functor.map_comp,
      CochainComplex.fromSingle₀Equiv_comp_f_zero hφ]
  | succ n =>
    have := epi_resolutionCechδ ι hK n (m := n + 1) (by omega)
    rw [← cancel_epi ((Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).hom.app
      (K.cycles (n + 1)) ≫ (cechCohomologyZeroIso (K.cycles (n + 1))).hom ≫
        resolutionCechδ ι n (k := 0) (m := n + 1) (by omega))]
    have e := sectionsIsoCechZero_hom_naturality (HomologicalComplex.cyclesMap φ (n + 1))
    simp only [sectionsIsoCechZero, Iso.trans_hom, Iso.app_hom, Category.assoc] at e
    simp only [Category.assoc]
    rw [resolutionCechδ_naturality_assoc ι ι' hφ, ← reassoc_of% e,
      cechCohomologyObjIsoOfIsFlasque_succ_hom,
      reassoc_of% (cechCohomologyObjIsoOfIsFlasque_succ_hom ι hK n),
      HomologicalComplex.homologyπ_naturality, HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
      HomologicalComplex.comp_liftCycles_assoc]
    congr 2
    simp only [Functor.mapHomologicalComplex_map_f, ← Functor.map_comp,
      HomologicalComplex.cyclesMap_i]

end Naturality

end TauCeti.Topology

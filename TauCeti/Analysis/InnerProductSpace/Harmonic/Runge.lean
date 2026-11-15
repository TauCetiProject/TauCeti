/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
import TauCeti.Analysis.LocallyConvex.Bipolar
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.CutoffPotential

/-!
# Harmonic Runge approximation on filled-in compact sets

Let `E` be a finite-dimensional real inner product space of dimension at least `3`, `Ω ⊆ E` an open
set, and `K ⊆ Ω` a compact subset that is filled-in within `Ω` (`IsFilledIn K Ω`, i.e., `Ω \ K` has
no nonempty relatively compact connected component in `Ω`). This file proves the harmonic Runge
approximation theorem of Walsh (for uniform convergence) and Lax–Malgrange (in `C^m` by duality and
fundamental solutions): every function `f : E → F` (with `F` finite-dimensional) harmonic on a
neighbourhood of `K` can be approximated in `C^m` norm on `K` by functions harmonic on all of `Ω`.

## Proof strategy

For scalar-valued functions on `EuclideanSpace ℝ (Fin d)` (`d ≥ 3`), we form the Banach space
`JetSpace E K m = Π k : Fin (m + 1), K →ᵇ (E [×k]→L[ℝ] ℝ)` of continuous `m`-jets on `K` and the
submodule `S` of `m`-jets of functions harmonic on `Ω`. By the Hahn–Banach separation criterion
(`Submodule.mem_topologicalClosure_iff_forall_dual_eq_zero`), `Jf ∈ S.topologicalClosure` reduces to
showing that any continuous linear functional `ℓ` on `JetSpace E K m` vanishing on `S` also vanishes
on `Jf`. Pulling `ℓ` back along the continuous `m`-jet restriction map
`𝓓(Ω, ℝ) →L[ℝ] JetSpace E K m` produces a compactly supported distribution `T ∈ 𝓓'(Ω, ℝ)` with
`dsupport T ⊆ K` that annihilates every test function agreeing near `K` with a global harmonic
function on `Ω`. By the Newtonian potential annihilation theorem
(`TauCeti.apply_eq_zero_of_isFilledIn_of_harmonicOnNhd`), `T` also
annihilates a smooth cutoff of `f` equal to `f` near `K`, whence `ℓ Jf = 0`. An orthonormal basis
transports the result to any finite-dimensional real inner product space of dimension `≥ 3`, and a
basis of `F` upgrades scalar approximation to finite-dimensional vector values.

## Main declarations

* `InnerProductSpace.HarmonicOnNhd.exists_harmonicOnNhd_norm_iteratedFDeriv_sub_lt`: harmonic Runge
  approximation in `C^m` on `K` for functions with values in a finite-dimensional real normed space.
* `InnerProductSpace.HarmonicOnNhd.exists_harmonicOnNhd_norm_sub_lt`: uniform (`C^0`) harmonic Runge
  approximation on `K`.

## References

* P. D. Lax, *A stability theorem for solutions of abstract differential equations, and its
  application to the study of the local behavior of solutions of elliptic equations*, Comm. Pure
  Appl. Math. 9 (1956), 747–766.
* B. Malgrange, *Existence et approximation des solutions des équations aux dérivées partielles et
  des équations de convolution*, Ann. Inst. Fourier (Grenoble) 6 (1955–1956), 271–355.
* J. L. Walsh, *The approximation of harmonic functions by harmonic polynomials and by harmonic
  rational functions*, Bull. Amer. Math. Soc. 35 (1929), 499–544.
* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer, 2001.
-/

public section

noncomputable section

open ContDiff Distribution Filter Metric Set TauCeti TopologicalSpace Topology
open scoped BoundedContinuousFunction ContDiff Distributions

namespace InnerProductSpace

section JetSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Space of continuous `m`-jets on `K`, realized as the finite product of bounded continuous
multilinear-map spaces up to order `m`. Defined as a `def` rather than `abbrev` so that all
topological and algebraic instances resolve through `NormedAddCommGroup`/`NormedSpace` without
synthesizing competing `Pi` topologies. -/
private def JetSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E)
    (m : ℕ) : Type _ :=
  Π k : Fin (m + 1), K →ᵇ (E [×(k : ℕ)]→L[ℝ] ℝ)

private instance (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) (m : ℕ) :
    NormedAddCommGroup (JetSpace E K m) :=
  Pi.normedAddCommGroup

private instance (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) (m : ℕ) :
    NormedSpace ℝ (JetSpace E K m) :=
  Pi.normedSpace

/-- Evaluate a continuous `m`-jet at derivative order `k`. -/
private def jetEval {K : Set E} {m : ℕ} (J : JetSpace E K m) (k : Fin (m + 1)) :
    K →ᵇ (E [×(k : ℕ)]→L[ℝ] ℝ) :=
  J k

private theorem jetSpace_ext {K : Set E} {m : ℕ} {J₁ J₂ : JetSpace E K m}
    (h : ∀ (k : Fin (m + 1)) (x : K), jetEval J₁ k x = jetEval J₂ k x) : J₁ = J₂ := by
  funext k
  exact BoundedContinuousFunction.ext (h k)

@[simp]
private theorem jetEval_zero {K : Set E} {m : ℕ} (k : Fin (m + 1)) (x : K) :
    jetEval (0 : JetSpace E K m) k x = 0 :=
  rfl

@[simp]
private theorem jetEval_add {K : Set E} {m : ℕ} (J₁ J₂ : JetSpace E K m) (k : Fin (m + 1))
    (x : K) :
    jetEval (J₁ + J₂) k x = jetEval J₁ k x + jetEval J₂ k x :=
  rfl

@[simp]
private theorem jetEval_sub {K : Set E} {m : ℕ} (J₁ J₂ : JetSpace E K m) (k : Fin (m + 1))
    (x : K) :
    jetEval (J₁ - J₂) k x = jetEval J₁ k x - jetEval J₂ k x :=
  rfl

@[simp]
private theorem jetEval_smul {K : Set E} {m : ℕ} (c : ℝ) (J : JetSpace E K m) (k : Fin (m + 1))
    (x : K) :
    jetEval (c • J) k x = c • jetEval J k x :=
  rfl

private theorem norm_jetEval_apply_le {K : Set E} {m : ℕ} (J : JetSpace E K m) (k : Fin (m + 1))
    (x : K) :
    ‖jetEval J k x‖ ≤ ‖J‖ :=
  (BoundedContinuousFunction.norm_coe_le_norm (J k) x).trans
    (norm_le_pi_norm (J : Π i : Fin (m + 1), K →ᵇ (E [×(i : ℕ)]→L[ℝ] ℝ)) k)

/-- The `k`-th iterated Fréchet derivative of a smooth function on an open neighbourhood of a
compact set `K`, bundled as a bounded continuous map on `K`. -/
private def jetOrderOfContDiffOn {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (k : ℕ) {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) :
    K →ᵇ (E [×k]→L[ℝ] ℝ) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hcont : ContinuousOn (iteratedFDeriv ℝ k g) U :=
    (hg.continuousOn_iteratedFDerivWithin (m := k) (mod_cast le_top) hU.uniqueDiffOn).congr
      fun y hy ↦ (iteratedFDerivWithin_of_isOpen k hU hy).symm
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun x : K ↦ iteratedFDeriv ℝ k g x.1,
      (hcont.mono hKU).comp_continuous continuous_subtype_val fun x ↦ x.2⟩

/-- The `m`-jet on `K` of a function smooth on an open neighbourhood `U` of `K`. -/
private def jetOfContDiffOn {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (m : ℕ) {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) :
    JetSpace E K m :=
  fun k ↦ jetOrderOfContDiffOn hK hU hKU k hg

@[simp]
private theorem jetEval_jetOfContDiffOn {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (m : ℕ) {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) (k : Fin (m + 1)) (x : K) :
    jetEval (jetOfContDiffOn hK hU hKU m hg) k x = iteratedFDeriv ℝ (k : ℕ) g x.1 :=
  rfl

/-- Continuous linear `m`-jet restriction from `𝓓_{L}(E, ℝ)` into `JetSpace E K m`. -/
private def jetRestrictionCLM (K : Set E) (m : ℕ) (L : Compacts E) :
    𝓓_{L}(E, ℝ) →L[ℝ] JetSpace E K m :=
  let compOrder (k : Fin (m + 1)) : 𝓓_{L}(E, ℝ) →L[ℝ] (K →ᵇ (E [×(k : ℕ)]→L[ℝ] ℝ)) :=
    BoundedContinuousFunction.compContinuousCLM (E [×(k : ℕ)]→L[ℝ] ℝ) ℝ
      ⟨Subtype.val, continuous_subtype_val⟩ ∘L ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k
  { toFun := fun φ k ↦ compOrder k φ
    map_add' := fun φ ψ ↦ funext fun k ↦ (compOrder k).map_add φ ψ
    map_smul' := fun c φ ↦ funext fun k ↦ (compOrder k).map_smul c φ
    cont := continuous_pi fun k ↦ (compOrder k).continuous }

/-- Pull back a continuous linear functional `ℓ` on `JetSpace E K m` along the `m`-jet restriction
to a scalar distribution in `𝓓'(Ω, ℝ)`. -/
private def pullbackJetDual (Ω : Opens E) {K : Set E} (hK : IsCompact K) (m : ℕ)
    (ℓ : StrongDual ℝ (JetSpace E K m)) : 𝓓'(Ω, ℝ) :=
  TestFunction.limitCLM ℝ
    (fun φ ↦ ℓ (jetOfContDiffOn hK isOpen_univ (subset_univ K) m φ.contDiff.contDiffOn))
    (fun L _ ↦ (ℓ : JetSpace E K m →L[ℝ] ℝ) ∘L jetRestrictionCLM K m L)
    (fun _ _ _ ↦ congrArg ℓ <| jetSpace_ext fun _ _ ↦ rfl)

@[simp]
private theorem pullbackJetDual_apply (Ω : Opens E) {K : Set E} (hK : IsCompact K) (m : ℕ)
    (ℓ : StrongDual ℝ (JetSpace E K m)) (φ : 𝓓(Ω, ℝ)) :
    pullbackJetDual Ω hK m ℓ φ =
      ℓ (jetOfContDiffOn hK isOpen_univ (subset_univ K) m φ.contDiff.contDiffOn) :=
  TestFunction.limitCLM_apply ..

private theorem jetOfContDiffOn_eq_of_eventuallyEq {Ω : Opens E} {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (m : ℕ) {g : E → ℝ}
    (hg : ContDiffOn ℝ ∞ g U) {ψ : 𝓓(Ω, ℝ)} (hψ : (ψ : E → ℝ) =ᶠ[𝓝ˢ K] g) :
    jetOfContDiffOn hK isOpen_univ (subset_univ K) m ψ.contDiff.contDiffOn =
      jetOfContDiffOn hK hU hKU m hg :=
  jetSpace_ext fun k x ↦ by
    simp only [jetEval_jetOfContDiffOn]
    exact ((hψ.filter_mono (nhds_le_nhdsSet x.2)).iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds

private theorem jetOfContDiffOn_eq_zero_of_tsupport_subset_compl {Ω : Opens E} {K : Set E}
    (hK : IsCompact K) (m : ℕ) {φ : 𝓓(Ω, ℝ)} (hφ : tsupport (φ : E → ℝ) ⊆ Kᶜ) :
    jetOfContDiffOn hK isOpen_univ (subset_univ K) m φ.contDiff.contDiffOn = 0 :=
  jetSpace_ext fun k x ↦ by
    simp only [jetEval_jetOfContDiffOn, jetEval_zero]
    have hx : x.1 ∉ tsupport (φ : E → ℝ) := fun hmem ↦ hφ hmem x.2
    have hev : (φ : E → ℝ) =ᶠ[𝓝 x.1] (0 : E → ℝ) := notMem_tsupport_iff_eventuallyEq.1 hx
    simpa using (hev.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds

/-- Multiply a cutoff `η : 𝓓(Ω, ℝ)` supported inside an open set `U` by a scalar function `g`
smooth on `U`, packaged as a test function in `𝓓(Ω, ℝ)`. -/
private def cutoffSmoothTestFunction {Ω : Opens E} (η : 𝓓(Ω, ℝ)) {U : Set E} (hU : IsOpen U)
    (hηU : tsupport (η : E → ℝ) ⊆ U) {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U) : 𝓓(Ω, ℝ) where
  toFun y := η y * g y
  contDiff' := contDiff_of_contDiffOn_union_of_isOpen (η.contDiff.contDiffOn.mul hg)
    ((contDiffOn_const (c := (0 : ℝ))).congr fun _ hy ↦ by
      simp [image_eq_zero_of_notMem_tsupport (f := (η : E → ℝ)) hy])
    (eq_univ_of_forall fun y ↦ (em (y ∈ tsupport (η : E → ℝ))).imp (hηU ·) id)
    hU (isClosed_tsupport (η : E → ℝ)).isOpen_compl
  hasCompactSupport' := η.hasCompactSupport.mul_right
  tsupport_subset' := tsupport_mul_subset_left.trans η.tsupport_subset

@[simp]
private theorem cutoffSmoothTestFunction_apply {Ω : Opens E} (η : 𝓓(Ω, ℝ)) {U : Set E}
    (hU : IsOpen U) (hηU : tsupport (η : E → ℝ) ⊆ U) {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (y : E) :
    cutoffSmoothTestFunction η hU hηU hg y = η y * g y :=
  rfl

end JetSpace

section Submodule

variable {d : ℕ}

private theorem contDiffOn_of_harmonicOnNhd_open {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : HarmonicOnNhd g U) :
    ContDiffOn ℝ ∞ g U :=
  hg.analyticOnNhd.contDiffOn hU.uniqueDiffOn

/-- Submodule of `JetSpace (EuclideanSpace ℝ (Fin d)) K m` consisting of `m`-jets on `K` of
real-valued functions harmonic on the open set `Ω`. -/
private def harmonicJetSubmodule {K Ω : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) (m : ℕ) :
    Submodule ℝ (JetSpace (EuclideanSpace ℝ (Fin d)) K m) where
  carrier := {J | ∃ H : EuclideanSpace ℝ (Fin d) → ℝ, ∃ hH : HarmonicOnNhd H Ω,
    J = jetOfContDiffOn hK hΩ hKΩ m (contDiffOn_of_harmonicOnNhd_open hΩ hH)}
  zero_mem' := ⟨0, harmonicOnNhd_const 0, jetSpace_ext fun k x ↦ by simp⟩
  add_mem' := by
    rintro _ _ ⟨H₁, hH₁, rfl⟩ ⟨H₂, hH₂, rfl⟩
    refine ⟨H₁ + H₂, hH₁.add hH₂, jetSpace_ext fun k x ↦ ?_⟩
    simp only [jetEval_add, jetEval_jetOfContDiffOn]
    exact (iteratedFDeriv_add_apply
      ((hH₁ x.1 (hKΩ x.2)).analyticAt.contDiffAt.of_le (mod_cast le_top))
      ((hH₂ x.1 (hKΩ x.2)).analyticAt.contDiffAt.of_le (mod_cast le_top))).symm
  smul_mem' := by
    rintro c _ ⟨H, hH, rfl⟩
    refine ⟨c • H, hH.const_smul, jetSpace_ext fun k x ↦ ?_⟩
    simp only [jetEval_smul, jetEval_jetOfContDiffOn]
    exact (iteratedFDeriv_const_smul_apply
      ((hH x.1 (hKΩ x.2)).analyticAt.contDiffAt.of_le (mod_cast le_top))).symm

end Submodule

section Approximation

/-- A continuous linear functional on `JetSpace _ K m` vanishing on all harmonic `m`-jets from `Ω`
also vanishes on the `m`-jet of any function harmonic on a neighbourhood of `K`, provided `K` is
filled-in within `Ω` and `d ≥ 3`. -/
private theorem mem_topologicalClosure_harmonicJetSubmodule {d : ℕ} (hd : 3 ≤ d)
    {K Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hfill : IsFilledIn K Ω) {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : HarmonicOnNhd f K)
    (m : ℕ) :
    jetOfContDiffOn hK (isOpen_setOfPred_harmonicAt (f := f)) hf m
        (contDiffOn_of_harmonicOnNhd_open (isOpen_setOfPred_harmonicAt (f := f)) fun _ hy ↦ hy) ∈
      (harmonicJetSubmodule hK hΩ hKΩ m).topologicalClosure := by
  set Uf : Set (EuclideanSpace ℝ (Fin d)) := {y | HarmonicAt f y}
  have hUf : IsOpen Uf := isOpen_setOfPred_harmonicAt (f := f)
  have hfU : HarmonicOnNhd f Uf := fun _ hy ↦ hy
  refine (Submodule.mem_topologicalClosure_iff_forall_dual_eq_zero _).2 fun ℓ hℓ ↦ ?_
  let Ωo : Opens (EuclideanSpace ℝ (Fin d)) := ⟨Ω, hΩ⟩
  let T : 𝓓'(Ωo, ℝ) := pullbackJetDual Ωo hK m ℓ
  have hTK : dsupport T ⊆ K := by
    have hvan : Distribution.IsVanishingOn T Kᶜ := fun φ hφ ↦ by
      rw [show T φ = pullbackJetDual Ωo hK m ℓ φ from rfl, pullbackJetDual_apply,
        jetOfContDiffOn_eq_zero_of_tsupport_subset_compl hK m hφ, map_zero]
    exact compl_compl K ▸ (hvan.disjoint_dsupport hK.isClosed.isOpen_compl).subset_compl_left
  have hT : ∀ (H : EuclideanSpace ℝ (Fin d) → ℝ) (ψ : 𝓓(Ωo, ℝ)),
      HarmonicOnNhd H Ωo → ((ψ : _ → ℝ) =ᶠ[𝓝ˢ K] H) → T ψ = 0 := fun H ψ hH hψ ↦ by
    rw [show T ψ = pullbackJetDual Ωo hK m ℓ ψ from rfl, pullbackJetDual_apply]
    exact hℓ _ ⟨H, hH, jetOfContDiffOn_eq_of_eventuallyEq hK hΩ hKΩ m
      (contDiffOn_of_harmonicOnNhd_open hΩ hH) hψ⟩
  obtain ⟨η, -, hη1, hηU⟩ := TestFunction.exists_cutoff_tsupport_subset (Ω := Ωo) (n := ⊤)
    hK (hΩ.inter hUf) (subset_inter hKΩ hf) inter_subset_left
  let ψf := cutoffSmoothTestFunction η hUf (hηU.trans inter_subset_right)
    (contDiffOn_of_harmonicOnNhd_open hUf hfU)
  have hψf : (ψf : _ → ℝ) =ᶠ[𝓝ˢ K] f := hη1.mono fun y hy ↦ by simp [ψf, hy]
  have hT0 : T ψf = 0 :=
    TauCeti.apply_eq_zero_of_isFilledIn_of_harmonicOnNhd hd hK hKΩ hfill hTK hT hf hψf
  rw [show T ψf = pullbackJetDual Ωo hK m ℓ ψf from rfl, pullbackJetDual_apply,
    jetOfContDiffOn_eq_of_eventuallyEq hK hUf hf m
      (contDiffOn_of_harmonicOnNhd_open hUf hfU) hψf] at hT0
  exact hT0

/-- Scalar harmonic Runge approximation on `EuclideanSpace ℝ (Fin d)` (`d ≥ 3`). -/
private theorem exists_harmonicOnNhd_norm_iteratedFDeriv_sub_lt_euclidean_real {d : ℕ}
    (hd : 3 ≤ d) {K Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : HarmonicOnNhd f K) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : EuclideanSpace ℝ (Fin d) → ℝ, HarmonicOnNhd H Ω ∧
      ∀ k ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (H - f) x‖ < ε := by
  set Jf := jetOfContDiffOn hK (isOpen_setOfPred_harmonicAt (f := f)) hf m
    (contDiffOn_of_harmonicOnNhd_open (isOpen_setOfPred_harmonicAt (f := f)) fun _ hy ↦ hy)
  have hclos : Jf ∈ closure (harmonicJetSubmodule hK hΩ hKΩ m : Set (JetSpace _ K m)) :=
    Submodule.topologicalClosure_coe (harmonicJetSubmodule hK hΩ hKΩ m) ▸
      mem_topologicalClosure_harmonicJetSubmodule hd hΩ hK hKΩ hfill hf m
  obtain ⟨_, ⟨H, hH, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1 hclos ε hε
  refine ⟨H, hH, fun k hk x hx ↦ ?_⟩
  set j : Fin (m + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  set JH := jetOfContDiffOn hK hΩ hKΩ m (contDiffOn_of_harmonicOnNhd_open hΩ hH)
  have hsub : iteratedFDeriv ℝ k (H - f) x = jetEval (JH - Jf) j ⟨x, hx⟩ :=
    iteratedFDeriv_sub_apply
      ((hH x (hKΩ hx)).analyticAt.contDiffAt.of_le (mod_cast le_top))
      ((hf x hx).analyticAt.contDiffAt.of_le (mod_cast le_top))
  rw [hsub]
  exact (norm_jetEval_apply_le (JH - Jf) j ⟨x, hx⟩).trans_lt
    ((dist_eq_norm' Jf JH).symm.trans_lt hdist)

/-- Scalar harmonic Runge approximation on any finite-dimensional real inner product space of
dimension at least `3`. -/
private theorem exists_harmonicOnNhd_norm_iteratedFDeriv_sub_lt_real
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : 3 ≤ Module.finrank ℝ E) {K Ω : Set E} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω) {f : E → ℝ} (hf : HarmonicOnNhd f K) (m : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : E → ℝ, HarmonicOnNhd H Ω ∧ ∀ k ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (H - f) x‖ < ε := by
  set d := Module.finrank ℝ E
  set e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) := (stdOrthonormalBasis ℝ E).repr
  have hΩ' : IsOpen (e '' Ω) := e.toHomeomorph.isOpenMap Ω hΩ
  have hK' : IsCompact (e '' K) := hK.image e.continuous
  have hK'Ω' : e '' K ⊆ e '' Ω := image_mono hKΩ
  have hfill' : IsFilledIn (e '' K) (e '' Ω) := e.toHomeomorph.isFilledIn_image.2 hfill
  have hf' : HarmonicOnNhd (f ∘ e.symm) (e '' K) := by
    have hpre : e.symm ⁻¹' K = e '' K := by
      ext y
      exact ⟨fun hy ↦ ⟨e.symm y, hy, by simp⟩, by rintro ⟨x, hx, rfl⟩; simpa using hx⟩
    rw [← hpre]
    exact (TauCeti.harmonicOnNhd_comp_linearIsometryEquiv_right_iff e.symm).2 hf
  obtain ⟨H', hH', hbound⟩ :=
    exists_harmonicOnNhd_norm_iteratedFDeriv_sub_lt_euclidean_real hd hΩ' hK' hK'Ω' hfill'
      hf' m hε
  refine ⟨H' ∘ e, ?_, fun k hk x hx ↦ ?_⟩
  · have hpre : e ⁻¹' (e '' Ω) = Ω := preimage_image_eq Ω e.injective
    rw [← hpre]
    exact (TauCeti.harmonicOnNhd_comp_linearIsometryEquiv_right_iff e).2 hH'
  · have hsub : H' ∘ e - f = (H' - f ∘ e.symm) ∘ e := by ext y; simp
    rw [hsub, e.norm_iteratedFDeriv_comp_right]
    exact hbound k hk (e x) (mem_image_of_mem e hx)

/-- **Harmonic Runge approximation in `C^m`** (Walsh; Lax–Malgrange). Let `E` be a
finite-dimensional real inner product space of dimension at least `3`, `Ω ⊆ E` an open set, and
`K ⊆ Ω` a compact set that is filled-in within `Ω` (`IsFilledIn K Ω`). Every function `f : E → F`
with values in a finite-dimensional real normed space that is harmonic on a neighbourhood of `K`
can be approximated uniformly up to order `m` on `K` by functions harmonic on `Ω`. -/
theorem HarmonicOnNhd.exists_harmonicOnNhd_norm_iteratedFDeriv_sub_lt
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {K Ω : Set E} {f : E → F} (hf : HarmonicOnNhd f K)
    (hd : 3 ≤ Module.finrank ℝ E) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hfill : IsFilledIn K Ω) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : E → F, HarmonicOnNhd H Ω ∧
      ∀ k ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (H - f) x‖ < ε := by
  classical
  let b := Module.finBasis ℝ F
  let M : ℝ := (∑ i, ‖b i‖) + 1
  have hM : 0 < M :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) zero_lt_one
  have hδ : 0 < ε / M := div_pos hε hM
  let coord (i : _) : F →L[ℝ] ℝ := (b.coord i).toContinuousLinearMap
  let spanB (i : _) : ℝ →L[ℝ] F := ContinuousLinearMap.toSpanSingleton ℝ (b i)
  have hi : ∀ i, ∃ H : E → ℝ, HarmonicOnNhd H Ω ∧
      ∀ k ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (H - coord i ∘ f) x‖ < ε / M := fun i ↦
    exists_harmonicOnNhd_norm_iteratedFDeriv_sub_lt_real hd hΩ hK hKΩ hfill
      (hf.comp_CLM (coord i)) m hδ
  choose H hH hbound using hi
  refine ⟨fun x ↦ ∑ i, spanB i (H i x),
    HarmonicOnNhd.sum fun i _ ↦ (hH i).comp_CLM (spanB i), fun k hk x hx ↦ ?_⟩
  have hsub : (fun y ↦ ∑ i, spanB i (H i y)) - f =
      ∑ i : _, (spanB i ∘ (H i - coord i ∘ f)) := by
    ext y
    simp only [Pi.sub_apply, Finset.sum_apply, Function.comp_apply, spanB, coord,
      ContinuousLinearMap.toSpanSingleton_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply, sub_smul, Finset.sum_sub_distrib, b.sum_repr (f y)]
  have hcd_diff : ∀ i, ContDiffAt ℝ ∞ (H i - coord i ∘ f) x := fun i ↦
    ((hH i x (hKΩ hx)).analyticAt.sub ((hf.comp_CLM (coord i) x hx).analyticAt)).contDiffAt
  have hcd : ∀ i ∈ (Finset.univ : Finset _),
      ContDiffAt ℝ (k : ℕ∞ω) (spanB i ∘ (H i - coord i ∘ f)) x := fun i _ ↦
    ((spanB i).contDiff.contDiffAt.comp x (hcd_diff i)).of_le (mod_cast le_top)
  rw [hsub, iteratedFDeriv_sum_apply hcd]
  calc ‖∑ i, iteratedFDeriv ℝ k (spanB i ∘ (H i - coord i ∘ f)) x‖
      ≤ ∑ i, ‖iteratedFDeriv ℝ k (spanB i ∘ (H i - coord i ∘ f)) x‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖spanB i‖ * ‖iteratedFDeriv ℝ k (H i - coord i ∘ f) x‖ :=
        Finset.sum_le_sum fun i _ ↦
          (spanB i).norm_iteratedFDeriv_comp_left (hcd_diff i) (mod_cast le_top)
    _ ≤ ∑ i, ‖b i‖ * (ε / M) := Finset.sum_le_sum fun i _ ↦ by
        rw [ContinuousLinearMap.norm_toSpanSingleton]
        exact mul_le_mul_of_nonneg_left (hbound i k hk x hx).le (norm_nonneg _)
    _ = (∑ i, ‖b i‖) * (ε / M) := (Finset.sum_mul _ _ _).symm
    _ < M * (ε / M) := mul_lt_mul_of_pos_right (lt_add_one _) hδ
    _ = ε := mul_div_cancel₀ ε hM.ne'

/-- **Uniform harmonic Runge approximation** (Walsh; Lax–Malgrange). Under the same hypotheses as
`HarmonicOnNhd.exists_harmonicOnNhd_norm_iteratedFDeriv_sub_lt`, any function harmonic on a
neighbourhood of the filled-in compact set `K ⊆ Ω` can be approximated uniformly on `K` by
functions harmonic on `Ω`. -/
theorem HarmonicOnNhd.exists_harmonicOnNhd_norm_sub_lt
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {K Ω : Set E} {f : E → F} (hf : HarmonicOnNhd f K)
    (hd : 3 ≤ Module.finrank ℝ E) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hfill : IsFilledIn K Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : E → F, HarmonicOnNhd H Ω ∧ ∀ x ∈ K, ‖H x - f x‖ < ε := by
  obtain ⟨H, hH, hbound⟩ :=
    hf.exists_harmonicOnNhd_norm_iteratedFDeriv_sub_lt hd hΩ hK hKΩ hfill 0 hε
  exact ⟨H, hH, fun x hx ↦ by simpa [norm_iteratedFDeriv_zero] using hbound 0 le_rfl x hx⟩

end Approximation

end InnerProductSpace

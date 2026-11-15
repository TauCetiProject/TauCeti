/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import TauCeti.Topology.Algebra.Module.AdicComplete
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Profinite flat modules

Following Chojecki–Hansen–Johansson (§6.1, Definition 6.1), a topological module `M` over a
compact topological commutative ring `O` (whose primary instance is the ring of integers of a
nonarchimedean local field, or `ℤ_p`) is **profinite flat** if `M` is profinite as a topological
`O`-module (`TauCeti.IsCompactModule O M`, i.e. compact, totally disconnected, and linearly
topologized with finite open quotients) and algebraically flat over `O` (`Module.Flat O M`).

In `SGA 3` (Exposé VII_B, §0.2) and Formal GAGA, profinite linear-topological modules arise as the
dual category of discrete torsion modules; flatness singles out those whose reductions modulo open
ideals behave well under completed tensor products. In particular, Chojecki–Hansen–Johansson form
mixed completed tensor products `A ⊗̂_O R` of Banach or affinoid algebras `A` with small
coefficient `O`-algebras `R` whose underlying topological `O`-module is profinite flat.

Over a Dedekind domain (and hence over any discrete valuation ring), flatness is equivalent to
torsion-freeness (`IsDedekindDomain.flat_iff_torsion_eq_bot`), and over a discrete valuation ring
with uniformizer `ϖ` it reduces further to `ϖ`-regularity (`IsSMulRegular M ϖ`). Consequently,
over a compact Hausdorff discrete valuation ring `O`, profinite flat `O`-modules are stable under
arbitrary products (`IsProfiniteFlat.pi`), closed submodules (`IsProfiniteFlat.submodule`), and
formal power series rings `MvPowerSeries σ O` and `PowerSeries O` equipped with the
coefficientwise topology (`IsProfiniteFlat.mvPowerSeries`, `IsProfiniteFlat.powerSeries`). When `σ`
is finite, `MvPowerSeries σ O` is a compact Hausdorff noetherian local ring, so its coefficientwise
topology agrees with the adic topology of its maximal ideal
(`MvPowerSeries.WithPiTopology.isAdic_maximalIdeal`).

## Main definitions

* `TauCeti.Huber.IsProfiniteFlat O M`: `M` is a compact (`TauCeti.IsCompactModule O M`) and flat
  (`Module.Flat O M`) topological `O`-module.
* `MvPowerSeries.WithPiTopology.coeffContinuousLinearEquiv`,
  `PowerSeries.WithPiTopology.coeffContinuousLinearEquiv`: the coefficient maps
  `MvPowerSeries σ O ≃L[O] ((σ →₀ ℕ) → O)` and `PowerSeries O ≃L[O] (ℕ → O)` in the
  coefficientwise topology.

## Main results

* `TauCeti.Huber.IsProfiniteFlat.isAdicComplete`: over a compact Hausdorff noetherian local ring
  `(O, 𝔪)`, every profinite flat `O`-module is `𝔪`-adically complete.
* `TauCeti.Huber.IsProfiniteFlat.iff_isCompactModule_and_isTorsionFree`,
  `TauCeti.Huber.IsProfiniteFlat.iff_isCompactModule_and_isSMulRegular`: over a Bézout domain or
  Dedekind domain, profinite flatness is compactness plus torsion-freeness; over a discrete
  valuation ring with uniformizer `ϖ`, it is compactness plus `IsSMulRegular M ϖ`.
* `TauCeti.Huber.IsProfiniteFlat.pi`, `TauCeti.Huber.IsProfiniteFlat.submodule`,
  `TauCeti.Huber.IsProfiniteFlat.mvPowerSeries`, `TauCeti.Huber.IsProfiniteFlat.powerSeries`:
  stability under products, closed submodules, and formal power series over a compact Dedekind /
  discrete valuation ring.
* `MvPowerSeries.WithPiTopology.isAdic_maximalIdeal`,
  `PowerSeries.WithPiTopology.isAdic_maximalIdeal`: for finite `σ` and compact Hausdorff
  noetherian local `O`, the coefficientwise topology on `MvPowerSeries σ O` (and `PowerSeries O`)
  is the adic topology of its maximal ideal.

## References

* P. Chojecki, D. Hansen, and C. Johansson, *Overconvergent modular forms and perfectoid Shimura
  curves*, Doc. Math. 22 (2017), §6.1, Definition 6.1.
* M. Demazure and A. Grothendieck, *Schémas en groupes* (`SGA 3`), Tome I, Exposé VII_B, §0.2.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 5.1.
-/

public section

open Filter Topology

namespace MvPowerSeries.WithPiTopology

open scoped MvPowerSeries.WithPiTopology

/-- In the coefficientwise topology, sending a multivariate power series to its coefficient
function is a continuous `R`-linear equivalence `MvPowerSeries σ R ≃L[R] ((σ →₀ ℕ) → R)`. -/
def coeffContinuousLinearEquiv (σ R : Type*) [Semiring R] [TopologicalSpace R] :
    MvPowerSeries σ R ≃L[R] ((σ →₀ ℕ) → R) where
  toFun := LinearMap.pi fun d ↦ MvPowerSeries.coeff (R := R) d
  map_add' x y := by
    ext d
    exact map_add (MvPowerSeries.coeff d) x y
  map_smul' r x := by
    ext d
    exact map_smul (MvPowerSeries.coeff d) r x
  invFun g := g
  left_inv f := by
    ext d
    rfl
  right_inv g := by
    ext d
    rfl
  continuous_toFun := continuous_pi fun d ↦ continuous_coeff R d
  continuous_invFun := continuous_iff_continuousAt.mpr fun g ↦
    (tendsto_iff_coeff_tendsto (fun h : (σ →₀ ℕ) → R ↦ (h : MvPowerSeries σ R)) (𝓝 g) g).mpr
      fun d ↦ (continuous_apply d).continuousAt

@[simp]
theorem coeffContinuousLinearEquiv_apply (σ R : Type*) [Semiring R] [TopologicalSpace R]
    (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeffContinuousLinearEquiv σ R f d = MvPowerSeries.coeff d f :=
  (rfl)

@[simp]
theorem coeff_coeffContinuousLinearEquiv_symm (σ R : Type*) [Semiring R] [TopologicalSpace R]
    (g : (σ →₀ ℕ) → R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d ((coeffContinuousLinearEquiv σ R).symm g) = g d :=
  (rfl)

/-- Over a compact semiring, `MvPowerSeries σ R` is compact in the coefficientwise topology. -/
@[scoped instance]
theorem instCompactSpace {σ R : Type*} [Semiring R] [TopologicalSpace R] [CompactSpace R] :
    CompactSpace (MvPowerSeries σ R) :=
  (coeffContinuousLinearEquiv σ R).symm.toHomeomorph.compactSpace

/-- For a finite set of variables `σ` over a compact Hausdorff noetherian local ring `R`, the
coefficientwise topology on `MvPowerSeries σ R` coincides with the adic topology of its maximal
ideal. -/
theorem isAdic_maximalIdeal (σ R : Type*) [Finite σ] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CompactSpace R] [T2Space R] [IsLocalRing R] [IsNoetherianRing R] :
    IsAdic (IsLocalRing.maximalIdeal (MvPowerSeries σ R)) :=
  IsLocalRing.isAdic_maximalIdeal (MvPowerSeries σ R)

end MvPowerSeries.WithPiTopology

namespace PowerSeries.WithPiTopology

open scoped PowerSeries.WithPiTopology

/-- In the coefficientwise topology, sending a univariate formal power series to its sequence of
coefficients is a continuous `R`-linear equivalence `PowerSeries R ≃L[R] (ℕ → R)`. -/
noncomputable def coeffContinuousLinearEquiv (R : Type*) [Semiring R] [TopologicalSpace R] :
    PowerSeries R ≃L[R] (ℕ → R) where
  toFun := LinearMap.pi fun n ↦ PowerSeries.coeff (R := R) n
  map_add' x y := by
    ext n
    exact map_add (PowerSeries.coeff n) x y
  map_smul' r x := by
    ext n
    exact map_smul (PowerSeries.coeff n) r x
  invFun g := PowerSeries.mk g
  left_inv f := by
    ext n
    simp
  right_inv g := by
    ext n
    simp
  continuous_toFun := continuous_pi fun n ↦ continuous_coeff R n
  continuous_invFun := continuous_iff_continuousAt.mpr fun g ↦
    (tendsto_iff_coeff_tendsto R (fun h : ℕ → R ↦ PowerSeries.mk h) (𝓝 g) (PowerSeries.mk g)).mpr
      fun n ↦ by simpa using (continuous_apply n).continuousAt.tendsto

@[simp]
theorem coeffContinuousLinearEquiv_apply (R : Type*) [Semiring R] [TopologicalSpace R]
    (f : PowerSeries R) (n : ℕ) :
    coeffContinuousLinearEquiv R f n = PowerSeries.coeff n f :=
  (rfl)

@[simp]
theorem coeff_coeffContinuousLinearEquiv_symm (R : Type*) [Semiring R] [TopologicalSpace R]
    (g : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n ((coeffContinuousLinearEquiv R).symm g) = g n := by
  change PowerSeries.coeff n (PowerSeries.mk g) = g n
  exact PowerSeries.coeff_mk n g

@[simp]
theorem coeffContinuousLinearEquiv_symm_single_one (R : Type*) [Semiring R] [TopologicalSpace R]
    (n : ℕ) :
    (coeffContinuousLinearEquiv R).symm (Pi.single n 1) = (PowerSeries.X : PowerSeries R) ^ n := by
  ext m
  simp [PowerSeries.coeff_X_pow, Pi.single_apply, eq_comm]

/-- Over a compact semiring, `PowerSeries R` is compact in the coefficientwise topology. -/
@[scoped instance]
theorem instCompactSpace {R : Type*} [Semiring R] [TopologicalSpace R] [CompactSpace R] :
    CompactSpace (PowerSeries R) :=
  (coeffContinuousLinearEquiv R).symm.toHomeomorph.compactSpace

/-- Over a compact Hausdorff noetherian local ring `R`, the coefficientwise topology on
`PowerSeries R` coincides with the adic topology of its maximal ideal. -/
theorem isAdic_maximalIdeal (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CompactSpace R] [T2Space R] [IsLocalRing R] [IsNoetherianRing R] :
    IsAdic (IsLocalRing.maximalIdeal (PowerSeries R)) :=
  MvPowerSeries.WithPiTopology.isAdic_maximalIdeal Unit R

end PowerSeries.WithPiTopology

namespace TauCeti.Huber

/-- A topological `O`-module `M` is **profinite flat** (Chojecki–Hansen–Johansson, Definition 6.1)
if it is a compact totally disconnected topological `O`-module (`TauCeti.IsCompactModule O M`) and
algebraically flat over `O` (`Module.Flat O M`). -/
structure IsProfiniteFlat (O M : Type*) [CommRing O] [TopologicalSpace O]
    [AddCommGroup M] [Module O M] [TopologicalSpace M] : Prop where
  /-- the module is a compact totally disconnected topological `O`-module -/
  isCompactModule : IsCompactModule O M
  /-- the underlying `O`-module is flat -/
  flat : Module.Flat O M

namespace IsProfiniteFlat

/-- A compact totally disconnected topological commutative ring is profinite flat over itself. -/
theorem self (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [TotallyDisconnectedSpace O] : IsProfiniteFlat O O :=
  ⟨.self, inferInstance⟩

/-- A compact Hausdorff noetherian local ring is profinite flat over itself. -/
theorem self_of_isLocalRing (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [IsLocalRing O] [IsNoetherianRing O] :
    IsProfiniteFlat O O :=
  ⟨IsLocalRing.isCompactModule_self O, inferInstance⟩

section Basic

variable {O M N : Type*} [CommRing O] [TopologicalSpace O]
  [AddCommGroup M] [Module O M] [TopologicalSpace M]
  [AddCommGroup N] [Module O N] [TopologicalSpace N]

/-- A profinite flat module is a topological additive group. -/
theorem isTopologicalAddGroup (hM : IsProfiniteFlat O M) : IsTopologicalAddGroup M :=
  hM.isCompactModule.isTopologicalAddGroup

/-- Scalar multiplication on a profinite flat module is jointly continuous. -/
theorem continuousSMul (hM : IsProfiniteFlat O M) : ContinuousSMul O M :=
  hM.isCompactModule.continuousSMul

/-- A profinite flat module is compact. -/
theorem compactSpace (hM : IsProfiniteFlat O M) : CompactSpace M :=
  hM.isCompactModule.compactSpace

/-- A profinite flat module is totally disconnected. -/
theorem totallyDisconnectedSpace (hM : IsProfiniteFlat O M) : TotallyDisconnectedSpace M :=
  hM.isCompactModule.totallyDisconnectedSpace

/-- A profinite flat module is a nonarchimedean additive group. -/
theorem nonarchimedeanAddGroup (hM : IsProfiniteFlat O M) : NonarchimedeanAddGroup M :=
  hM.isCompactModule.nonarchimedeanAddGroup

/-- A profinite flat module is Hausdorff. -/
theorem t2Space (hM : IsProfiniteFlat O M) : T2Space M :=
  hM.isCompactModule.t2Space

/-- Over a compact ring `O`, a profinite flat `O`-module is linearly topologized. -/
theorem isLinearTopology [CompactSpace O] (hM : IsProfiniteFlat O M) : IsLinearTopology O M :=
  hM.isCompactModule.isLinearTopology

/-- Every open submodule of a profinite flat module has finite index. -/
theorem finite_quotient_of_isOpen (hM : IsProfiniteFlat O M) (P : Submodule O M)
    (hP : IsOpen (P : Set M)) : Finite (M ⧸ P) :=
  hM.isCompactModule.finite_quotient_of_isOpen P hP

/-- A profinite flat module is torsion-free over `O` in the sense of regular elements. -/
theorem isTorsionFree (hM : IsProfiniteFlat O M) : Module.IsTorsionFree O M := by
  have := hM.flat
  infer_instance

/-- Every regular element of `O` acts injectively on a profinite flat `O`-module. -/
theorem isSMulRegular_of_isRegular (hM : IsProfiniteFlat O M) {r : O} (hr : IsRegular r) :
    IsSMulRegular M r := by
  have := hM.flat
  exact Module.Flat.isSMulRegular_of_isRegular hr

/-- Over an integral domain `O`, every nonzero scalar acts injectively on a profinite flat
`O`-module. -/
theorem isSMulRegular_of_ne_zero [IsDomain O] (hM : IsProfiniteFlat O M) {r : O} (hr : r ≠ 0) :
    IsSMulRegular M r :=
  hM.isSMulRegular_of_isRegular (isRegular_iff_ne_zero.mpr hr)

/-- Over a compact `I`-adic commutative ring with `I` finitely generated, every profinite flat
module is `I`-adically complete. -/
theorem isAdicComplete_of_isAdic [CompactSpace O] (hM : IsProfiniteFlat O M) {I : Ideal O}
    (hI : IsAdic I) (hIfg : I.FG) : IsAdicComplete I M :=
  hM.isCompactModule.isAdicComplete_of_isAdic hI hIfg

/-- Over a compact Hausdorff noetherian local ring `(O, 𝔪)` (in particular over any compact
Hausdorff discrete valuation ring), every profinite flat `O`-module is `𝔪`-adically complete. -/
theorem isAdicComplete [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [IsLocalRing O] [IsNoetherianRing O] (hM : IsProfiniteFlat O M) :
    IsAdicComplete (IsLocalRing.maximalIdeal O) M :=
  hM.isCompactModule.isAdicComplete

/-- Any subsingleton topological module is profinite flat. -/
theorem subsingleton [Subsingleton M] : IsProfiniteFlat O M :=
  ⟨.subsingleton, inferInstance⟩

/-- Profinite flatness transports along a continuous linear equivalence. -/
theorem of_continuousLinearEquiv (hM : IsProfiniteFlat O M) (e : M ≃L[O] N) :
    IsProfiniteFlat O N := by
  have := hM.flat
  exact ⟨hM.isCompactModule.of_continuousLinearEquiv e,
    Module.Flat.of_linearEquiv e.symm.toLinearEquiv⟩

/-- Two continuously linearly equivalent topological modules are simultaneously profinite flat. -/
theorem congr (e : M ≃L[O] N) : IsProfiniteFlat O M ↔ IsProfiniteFlat O N :=
  ⟨fun h ↦ h.of_continuousLinearEquiv e, fun h ↦ h.of_continuousLinearEquiv e.symm⟩

end Basic

section TorsionFreeCriteria

variable {O M : Type*} [CommRing O] [TopologicalSpace O]
  [AddCommGroup M] [Module O M] [TopologicalSpace M]

/-- Over a Bézout domain, a topological module is profinite flat if and only if it is a compact
module and torsion-free. -/
theorem iff_isCompactModule_and_isTorsionFree [IsBezout O] [IsDomain O] :
    IsProfiniteFlat O M ↔ IsCompactModule O M ∧ Module.IsTorsionFree O M where
  mp h := ⟨h.isCompactModule, h.isTorsionFree⟩
  mpr := fun ⟨hc, ht⟩ ↦
    ⟨hc, (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout (R := O) (M := M)).mpr
      (Submodule.isTorsionFree_iff_torsion_eq_bot.mp ht)⟩

/-- Over a Dedekind domain, any torsion-free compact module is profinite flat. -/
theorem of_isCompactModule_of_isTorsionFree [IsDedekindDomain O] (hc : IsCompactModule O M)
    [Module.IsTorsionFree O M] : IsProfiniteFlat O M :=
  ⟨hc, inferInstance⟩

/-- Over a Dedekind domain, profinite flatness is equivalent to being a torsion-free compact
module. -/
theorem iff_isCompactModule_and_isTorsionFree_of_isDedekindDomain [IsDedekindDomain O] :
    IsProfiniteFlat O M ↔ IsCompactModule O M ∧ Module.IsTorsionFree O M where
  mp h := ⟨h.isCompactModule, h.isTorsionFree⟩
  mpr := fun ⟨hc, ht⟩ ↦ by
    have := ht
    exact of_isCompactModule_of_isTorsionFree hc

/-- Over a discrete valuation ring `O` with uniformizer `ϖ`, profinite flatness is equivalent to
being a compact `O`-module on which `ϖ` acts injectively. -/
theorem iff_isCompactModule_and_isSMulRegular [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) :
    IsProfiniteFlat O M ↔ IsCompactModule O M ∧ IsSMulRegular M ϖ where
  mp h := ⟨h.isCompactModule, h.isSMulRegular_of_ne_zero hϖ.ne_zero⟩
  mpr := fun ⟨hc, hreg⟩ ↦ by
    refine (iff_isCompactModule_and_isTorsionFree_of_isDedekindDomain (O := O) (M := M)).mpr
      ⟨hc, ⟨fun r hr ↦ ?_⟩⟩
    have hr0 : r ≠ 0 := hr.ne_zero
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (mt Ideal.span_singleton_eq_bot.mp hr0) hϖ
    obtain ⟨u, rfl⟩ := Ideal.span_singleton_eq_span_singleton.mp hn.symm
    intro x y hxy
    apply hreg.pow n
    have hux : u • (ϖ ^ n • x) = u • (ϖ ^ n • y) := by
      simpa [Units.smul_def, mul_comm, mul_smul] using hxy
    simpa using congrArg (u⁻¹ • ·) hux

end TorsionFreeCriteria

section DedekindConstructions

variable {O : Type*} [CommRing O] [IsDedekindDomain O] [TopologicalSpace O]

/-- Over a Dedekind domain `O` (in particular over any discrete valuation ring), an arbitrary
product of profinite flat `O`-modules is profinite flat. -/
theorem pi {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module O (M i)]
    [∀ i, TopologicalSpace (M i)] (h : ∀ i, IsProfiniteFlat O (M i)) :
    IsProfiniteFlat O (∀ i, M i) := by
  have := fun i ↦ (h i).isTorsionFree
  exact of_isCompactModule_of_isTorsionFree (.pi fun i ↦ (h i).isCompactModule)

/-- Over a compact Hausdorff local Dedekind domain `O` (i.e. a compact Hausdorff discrete valuation
ring or field), every product `I → O` is profinite flat. -/
theorem pi_self (I : Type*) [IsLocalRing O] [IsTopologicalRing O] [CompactSpace O] [T2Space O] :
    IsProfiniteFlat O (I → O) :=
  pi fun _ ↦ self_of_isLocalRing O

/-- Over a Dedekind domain `O`, every closed submodule of a profinite flat `O`-module is profinite
flat. -/
theorem submodule {M : Type*} [AddCommGroup M] [Module O M] [TopologicalSpace M]
    (hM : IsProfiniteFlat O M) (P : Submodule O M) (hP : IsClosed (P : Set M)) :
    IsProfiniteFlat O P := by
  have := hM.isTorsionFree
  exact of_isCompactModule_of_isTorsionFree (hM.isCompactModule.submodule P hP)

end DedekindConstructions

open scoped MvPowerSeries.WithPiTopology in
/-- Over a compact Hausdorff local Dedekind domain `O`, the multivariate formal power series ring
`MvPowerSeries σ O` equipped with the coefficientwise topology is profinite flat over `O`. -/
theorem mvPowerSeries (σ O : Type*) [CommRing O] [IsDedekindDomain O] [IsLocalRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O] :
    IsProfiniteFlat O (MvPowerSeries σ O) :=
  (pi_self (O := O) (σ →₀ ℕ)).of_continuousLinearEquiv
    (MvPowerSeries.WithPiTopology.coeffContinuousLinearEquiv σ O).symm

open scoped PowerSeries.WithPiTopology in
/-- Over a compact Hausdorff local Dedekind domain `O`, the formal power series ring
`PowerSeries O` equipped with the coefficientwise topology is profinite flat over `O`. -/
theorem powerSeries (O : Type*) [CommRing O] [IsDedekindDomain O] [IsLocalRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O] :
    IsProfiniteFlat O (PowerSeries O) :=
  mvPowerSeries Unit O

end IsProfiniteFlat

end TauCeti.Huber

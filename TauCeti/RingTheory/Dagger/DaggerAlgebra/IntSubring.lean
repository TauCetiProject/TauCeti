/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.Ultra
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Continuity
public import TauCeti.RingTheory.Dagger.IntegralWashnitzer.Basic
public import TauCeti.RingTheory.Huber.Completion.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.Quotient

import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Huber.Normed

/-!
# The power-bounded subring of a dagger algebra

For a `K`-dagger algebra `A` with completion map `τ : A → completion K A`, this file defines the
**subring of power-bounded elements** `TauCeti.Dagger.intSubring K A` (`A°`) as the contraction of
`Huber.powerBoundedSubring (completion K A)` along `τ`, without installing a global
`TopologicalSpace` instance on `A`.

Over a complete nontrivially normed ultrametric field `K`, we establish the four equivalent
descriptions of `A°`:
* contraction of `(completion K A)°` along `toCompletion K A` (`mem_intSubring_iff`, by definition);
* supremum seminorm bound `|a|sup ≤ 1` (`mem_intSubring_iff_supSeminorm_le_one`), and pointwise
  bound `|a(x)| ≤ 1` at every classical point `x ∈ MaximalSpectrum A`
  (`mem_intSubring_iff_forall_pointNorm_le_one`);
* topological power-boundedness in `affinoidTopology K A` (`mem_intSubring_iff_isPowerBounded`,
  bundled as `intSubring_eq_powerBoundedSubring`);
* on the Monsky–Washnitzer algebra `K⟨X₁, …, Xₙ⟩†`, membership in the integral Monsky–Washnitzer
  algebra `K°⟨X₁, …, Xₙ⟩†` (`mem_intSubring_washnitzerAlgebra_iff`), and on `K` itself, the
  valuation ring `{c : K | ‖c‖ ≤ 1}` (`mem_intSubring_self_iff`).

We also prove that `intSubring K A` is integrally closed in `A` (`isIntegrallyClosedIn_intSubring`),
open and closed in `affinoidTopology K A` (`isOpen_intSubring`, `isClosed_intSubring`), dense in
`(completion K A)°` (`topologicalClosure_map_toCompletion_intSubring`), contains the nilradical
(`IsNilpotent.mem_intSubring`), and is functorial under arbitrary `K`-algebra homomorphisms of
dagger algebras (`map_mem_intSubring`, `intSubring.map`).

## Main definitions

* `TauCeti.Dagger.intSubring`: the subring `A°` of power-bounded elements of a `K`-dagger algebra.
* `TauCeti.Dagger.intSubring.map`: functoriality
  `(A →ₐ[K] B) → (intSubring K A →+* intSubring K B)`.

## Main results

* `TauCeti.Dagger.isIntegrallyClosedIn_intSubring`: `intSubring K A` is integrally closed in `A`.
* `TauCeti.Dagger.mem_intSubring_iff_supSeminorm_le_one`: `a ∈ intSubring K A ↔ |a|sup ≤ 1`.
* `TauCeti.Dagger.mem_intSubring_iff_isPowerBounded` and
  `TauCeti.Dagger.intSubring_eq_powerBoundedSubring`: `intSubring K A` coincides with
  `Huber.powerBoundedSubring A` for `affinoidTopology K A`.
* `TauCeti.Dagger.topologicalClosure_map_toCompletion_intSubring`: the closure of the image of
  `intSubring K A` in `completion K A` is `(completion K A)°`.
* `TauCeti.Dagger.mem_intSubring_washnitzerAlgebra_iff`: on `K⟨X₁, …, Xₙ⟩†`, `intSubring` recovers
  `intWashnitzerAlgebra`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.2.3.
-/

public section

open Topology

namespace TauCeti.Dagger

section General

variable (K : Type*) [NormedField K] [IsUltrametricDist K]
  (A : Type*) [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- **The subring `A°` of power-bounded elements of a `K`-dagger algebra**, defined without a
global `TopologicalSpace A` instance as `(completion K A)° ∩ A` along `toCompletion K A`. Over a
complete nontrivially normed ultrametric field it agrees both with `{a : A | supSeminorm K a ≤ 1}`
(`mem_intSubring_iff_supSeminorm_le_one`) and with `Huber.powerBoundedSubring A` in
`affinoidTopology K A` (`intSubring_eq_powerBoundedSubring`). -/
noncomputable def intSubring : Subring A :=
  (Huber.powerBoundedSubring (completion K A)).comap (toCompletion K A).toRingHom

variable {K A}

/-- Unfolding lemma for membership in `intSubring K A`. -/
theorem mem_intSubring_iff {a : A} :
    a ∈ intSubring K A ↔ Huber.IsPowerBounded (toCompletion K A a) :=
  Huber.mem_powerBoundedSubring

/-- Nilpotent elements of a dagger algebra lie in `intSubring K A`. -/
theorem _root_.IsNilpotent.mem_intSubring {a : A} (ha : IsNilpotent a) :
    a ∈ intSubring K A := by
  rw [mem_intSubring_iff]
  obtain ⟨n, hn⟩ := ha
  rcases eq_or_ne n 0 with rfl | hn₀
  · have h10 : (1 : completion K A) = 0 := by
      simpa using congrArg (toCompletion K A) hn
    rw [show toCompletion K A a = 0 by rw [← mul_one (toCompletion K A a), h10, mul_zero]]
    exact Huber.isPowerBounded_zero
  · refine Huber.IsPowerBounded.of_pow hn₀ ?_
    rw [← map_pow, hn, map_zero]
    exact Huber.isPowerBounded_zero

/-- `intSubring K A` is integrally closed in `A`. -/
instance isIntegrallyClosedIn_intSubring : IsIntegrallyClosedIn (intSubring K A) A := by
  refine Subring.isIntegrallyClosedIn_iff.mpr fun x ⟨p, hp, hpx⟩ ↦ ?_
  rw [mem_intSubring_iff]
  let j : intSubring K A →+* Huber.powerBoundedSubring (completion K A) :=
    (toCompletion K A).toRingHom.restrict (intSubring K A)
      (Huber.powerBoundedSubring (completion K A)) fun _ hb ↦ hb
  refine Huber.isPowerBounded_of_isIntegral ⟨p.map j, hp.map j, ?_⟩
  rw [Polynomial.eval₂_map,
    show (algebraMap ↥(Huber.powerBoundedSubring (completion K A)) (completion K A)).comp j =
      (toCompletion K A).toRingHom.comp (algebraMap ↥(intSubring K A) A) from rfl]
  exact (Polynomial.hom_eval₂ p (algebraMap ↥(intSubring K A) A)
    (toCompletion K A).toRingHom x).symm.trans (by rw [hpx, map_zero])

end General

section Complete

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  {B : Type*} [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]
  {C : Type*} [CommRing C] [Algebra K C] [IsDaggerAlgebra K C]

/-- **Spectral characterization of `intSubring K A`.** An element of a `K`-dagger algebra lies in
`intSubring K A` if and only if its supremum seminorm is at most `1`. -/
theorem mem_intSubring_iff_supSeminorm_le_one {a : A} :
    a ∈ intSubring K A ↔ supSeminorm K a ≤ 1 :=
  mem_intSubring_iff.trans <|
    (IsAffinoidAlgebra.isPowerBounded_iff_supSeminorm_le_one (K := K) (A := completion K A)
      isAffinoidAlgebra_completion (f := toCompletion K A a)).trans <|
      by rw [supSeminorm_toCompletion]

/-- **Pointwise characterization of `intSubring K A`.** An element lies in `intSubring K A` if and
only if `|a(x)| ≤ 1` at every classical point `x ∈ MaximalSpectrum A`. -/
theorem mem_intSubring_iff_forall_pointNorm_le_one {a : A} :
    a ∈ intSubring K A ↔ ∀ x : MaximalSpectrum A, pointNorm K x a ≤ 1 := by
  rw [mem_intSubring_iff_supSeminorm_le_one, IsDaggerAlgebra.supSeminorm_le_iff zero_le_one]

/-- Every element of residue norm at most `1` lies in `intSubring K A`. -/
theorem mem_intSubring_of_norm_le_one {a : A}
    (ha : (letI := residueNormedCommRing K A; ‖a‖ ≤ 1)) :
    a ∈ intSubring K A := by
  rw [mem_intSubring_iff_supSeminorm_le_one]
  exact (IsDaggerAlgebra.supSeminorm_le_norm (K := K) a).trans ha

/-- **Topological characterization of `intSubring K A`.** An element lies in `intSubring K A` if and
only if it is power-bounded for `affinoidTopology K A`. -/
theorem mem_intSubring_iff_isPowerBounded {a : A} :
    a ∈ intSubring K A ↔
      @Huber.IsPowerBounded A _ (affinoidTopology K A) a := by
  rw [affinoidTopology_eq_residueNorm K A, mem_intSubring_iff]
  let _ := residueNormedCommRing K A
  let _ := residueNormedAlgebra K A
  have hiso : Isometry (uniformCompletionAlgEquiv K A) := isometry_uniformCompletionAlgEquiv K A
  have hiso_symm : Isometry (uniformCompletionAlgEquiv K A).symm :=
    (AddMonoidHomClass.isometry_iff_norm (E := completion K A) (F := UniformSpace.Completion A)
      (uniformCompletionAlgEquiv K A).symm).mpr fun y ↦ by
      rw [← norm_uniformCompletionAlgEquiv K A ((uniformCompletionAlgEquiv K A).symm y),
        AlgEquiv.apply_symm_apply]
  rw [← uniformCompletionAlgEquiv_coe K A a]
  exact (Huber.isPowerBounded_ringEquiv_iff (uniformCompletionAlgEquiv K A).toRingEquiv
    hiso.continuous hiso_symm.continuous).trans Huber.isPowerBounded_completion_coe_iff

variable (K A) in
/-- Equipped with `affinoidTopology K A`, `intSubring K A` is equal to
`Huber.powerBoundedSubring A`. -/
theorem intSubring_eq_powerBoundedSubring :
    letI := affinoidTopology K A
    letI := isTopologicalRing_affinoidTopology K A
    haveI := isTateRing_affinoidTopology K A
    intSubring K A = Huber.powerBoundedSubring A := by
  let _ := affinoidTopology K A
  let _ := isTopologicalRing_affinoidTopology K A
  have _ := isTateRing_affinoidTopology K A
  ext a
  exact (mem_intSubring_iff_isPowerBounded (K := K) (A := A)).trans
    Huber.mem_powerBoundedSubring.symm

omit [CompleteSpace K] in
variable (K A) in
/-- `intSubring K A` is open in `affinoidTopology K A`. -/
theorem isOpen_intSubring :
    letI := affinoidTopology K A
    IsOpen (intSubring K A : Set A) :=
  letI := affinoidTopology K A
  by
    have _ := Huber.IsTateRing.of_normedAlgebra K (completion K A)
    exact (Huber.isOpen_powerBoundedSubring (completion K A)).preimage
      (continuous_toCompletion_affinoidTopology K A)

omit [CompleteSpace K] in
variable (K A) in
/-- `intSubring K A` is closed in `affinoidTopology K A`. -/
theorem isClosed_intSubring :
    letI := affinoidTopology K A
    IsClosed (intSubring K A : Set A) :=
  letI := affinoidTopology K A
  by
    have _ := Huber.IsTateRing.of_normedAlgebra K (completion K A)
    exact (AddSubgroup.isClosed_of_isOpen
      (Huber.powerBoundedSubring (completion K A)).toAddSubgroup
      (Huber.isOpen_powerBoundedSubring (completion K A))).preimage
      (continuous_toCompletion_affinoidTopology K A)

omit [CompleteSpace K] in
variable (K A) in
/-- **The closure of the image of `intSubring K A` in `completion K A` is `(completion K A)°`.** -/
theorem topologicalClosure_map_toCompletion_intSubring :
    ((intSubring K A).map (toCompletion K A).toRingHom).topologicalClosure =
      Huber.powerBoundedSubring (completion K A) := by
  have _ := Huber.IsTateRing.of_normedAlgebra K (completion K A)
  have hopen : IsOpen (Huber.powerBoundedSubring (completion K A) : Set (completion K A)) :=
    Huber.isOpen_powerBoundedSubring (completion K A)
  refine le_antisymm
    (Subring.topologicalClosure_minimal _ (Subring.map_le_iff_le_comap.mpr le_rfl)
      (AddSubgroup.isClosed_of_isOpen
        (Huber.powerBoundedSubring (completion K A)).toAddSubgroup hopen))
    fun y hy ↦ ?_
  change y ∈ closure (((intSubring K A).map (toCompletion K A).toRingHom : Subring _) : Set _)
  rw [mem_closure_iff]
  intro V hV hyV
  obtain ⟨a, ha⟩ := (denseRange_toCompletion (K := K) (A := A)).exists_mem_open
    (hV.inter hopen) ⟨y, hyV, hy⟩
  exact ⟨toCompletion K A a, ha.1, a, ha.2, rfl⟩

/-- On a nontrivial `K`-dagger algebra, `algebraMap K A c ∈ intSubring K A` iff `‖c‖ ≤ 1`. -/
@[simp]
theorem algebraMap_mem_intSubring_iff [Nontrivial A] {c : K} :
    algebraMap K A c ∈ intSubring K A ↔ ‖c‖ ≤ 1 := by
  rw [mem_intSubring_iff_supSeminorm_le_one, supSeminorm_algebraMap]

/-- Scalars in the valuation ring `{c : K | ‖c‖ ≤ 1}` map into `intSubring K A`. -/
theorem algebraMap_mem_intSubring {c : K} (hc : ‖c‖ ≤ 1) :
    algebraMap K A c ∈ intSubring K A := by
  rcases subsingleton_or_nontrivial A with _ | _
  · rw [Subsingleton.elim (algebraMap K A c) 0]
    exact zero_mem _
  · exact algebraMap_mem_intSubring_iff.mpr hc

/-- On `K` itself, `intSubring K K` is the valuation ring `{c : K | ‖c‖ ≤ 1}`. -/
@[simp]
theorem mem_intSubring_self_iff {c : K} :
    c ∈ intSubring K K ↔ ‖c‖ ≤ 1 :=
  algebraMap_mem_intSubring_iff (K := K) (A := K) (c := c)

/-- The carrier of `intSubring K K` is `Metric.closedBall 0 1`. -/
theorem coe_intSubring_self :
    (intSubring K K : Set K) = Metric.closedBall 0 1 := by
  ext c
  simp

/-- On the Monsky–Washnitzer algebra `K⟨X₁, …, Xₙ⟩†`, membership in `intSubring` is `‖f‖ ≤ 1` for
the unit Gauss norm. -/
theorem mem_intSubring_washnitzerAlgebra_iff_norm_le_one {σ : Type*} [Finite σ]
    {f : washnitzerAlgebra σ K} :
    f ∈ intSubring K (washnitzerAlgebra σ K) ↔ ‖f‖ ≤ 1 := by
  rw [mem_intSubring_iff_supSeminorm_le_one, washnitzerAlgebra.supSeminorm_eq_norm]

/-- **Comparison with `intWashnitzerAlgebra`.** On `K⟨X₁, …, Xₙ⟩†`, `intSubring` consists precisely
of the overconvergent series lying in `K°⟨X₁, …, Xₙ⟩†`. -/
theorem mem_intSubring_washnitzerAlgebra_iff {σ : Type*} [Finite σ]
    {f : washnitzerAlgebra σ K} :
    f ∈ intSubring K (washnitzerAlgebra σ K) ↔
      (f : MvPowerSeries σ K) ∈ intWashnitzerAlgebra σ K := by
  rw [mem_intSubring_washnitzerAlgebra_iff_norm_le_one, mem_intWashnitzerAlgebra_iff_norm_le_one]

/-- Every `K`-algebra homomorphism of dagger algebras maps `intSubring K A` into
`intSubring K B`. -/
theorem map_mem_intSubring (φ : A →ₐ[K] B) {a : A} (ha : a ∈ intSubring K A) :
    φ a ∈ intSubring K B := by
  rw [mem_intSubring_iff_supSeminorm_le_one] at ha ⊢
  exact (IsDaggerAlgebra.supSeminorm_map_le φ a).trans ha

/-- Bundled subring-image form of `map_mem_intSubring`. -/
theorem map_intSubring_le (φ : A →ₐ[K] B) :
    (intSubring K A).map φ.toRingHom ≤ intSubring K B :=
  Subring.map_le_iff_le_comap.mpr fun _ ha ↦ map_mem_intSubring φ ha

namespace intSubring

/-- **Functoriality of `intSubring`.** Every `K`-algebra homomorphism `φ : A →ₐ[K] B` of dagger
algebras restricts to a ring homomorphism `intSubring K A →+* intSubring K B`. -/
noncomputable def map (φ : A →ₐ[K] B) : intSubring K A →+* intSubring K B :=
  φ.toRingHom.restrict (intSubring K A) (intSubring K B) fun _ ha ↦ map_mem_intSubring φ ha

@[simp]
theorem coe_map_apply (φ : A →ₐ[K] B) (x : intSubring K A) :
    (map φ x : B) = φ x := by rfl

@[simp]
theorem map_id : map (AlgHom.id K A) = RingHom.id (intSubring K A) := by
  ext x
  rfl

@[simp]
theorem map_comp (ψ : B →ₐ[K] C) (φ : A →ₐ[K] B) :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  ext x
  rfl

end intSubring

end Complete

end TauCeti.Dagger

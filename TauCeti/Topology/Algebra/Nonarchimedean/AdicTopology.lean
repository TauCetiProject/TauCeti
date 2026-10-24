/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Powers of the ideal defining an adic topology

For an ideal `I` of a commutative ring `R`, Mathlib's `Ideal.openAddSubgroup` records that each
power `I ^ n` is an open additive subgroup **of `R` carried with the topology `I.adicTopology`**.
A ring is usually met the other way round: it comes with a topology already, and `IsAdic I` is
the statement that this topology *is* the `I`-adic one. The results here transport such facts
across that equation — the openness, the complementary closedness, and the topological
nilpotence of the elements of `I` — so that a ring satisfying `IsAdic I` may be used directly.

Closedness is the form these are wanted in: an infinite sum all of whose terms lie in `I ^ n`
again lies in `I ^ n`, because `I ^ n` is closed and `tsum_mem` applies. That is how a power
series evaluated at arguments of `I ^ n` is confined to `I ^ n`, in
`TauCeti.RingTheory.MvPowerSeries.Evaluation`.

## Main results

* `IsAdic.isOpen_pow` : in a ring whose topology is `I`-adic, every power of `I` is open.
* `IsAdic.isClosed_pow` : in a ring whose topology is `I`-adic, every power of `I` is closed —
  an open additive subgroup of a topological group being closed.
* `IsAdic.tendsto_zero_of_mem_pow` : a family whose members lie in growing powers of `I` tends to
  zero, provided the exponents tend to infinity.
* `IsAdic.isTopologicallyNilpotent_of_mem` : in a ring whose topology is `I`-adic, every element
  of `I` is topologically nilpotent.
* `IsAdic.isTopologicallyNilpotent_iff_mem_radical` : conversely, a topologically nilpotent
  element has a power in `I`, so the topologically nilpotent elements are exactly the radical
  of `I`.
* `IsAdic.isLinearTopology` : a ring whose topology is `I`-adic is linearly topologized, the
  `IsAdic` counterpart of `Ideal.isLinearTopology`.
* `IsAdic.continuous_of_map_le_radical` : a ring homomorphism from an `I`-adic ring to a `J`-adic
  ring is continuous when it carries the finitely generated ideal `I` into the radical of `J`.
* `IsAdic.continuous_iff_map_le_radical` and
  `IsAdic.continuous_iff_forall_isTopologicallyNilpotent` : when the source topology has some
  finitely generated ideal of definition, continuity can be tested on any ideals of definition,
  without requiring completeness or finite generation of the tested ideals.
* `IsAdic.of_radical_eq` and `Ideal.adicTopology_eq_of_radical_eq` : finitely generated ideals
  with the same radical define the same adic topology.
* `IsAdic.isAdic_iff_isOpen_and_exists_pow_le` : an ideal of definition is characterized by
  openness and containment of one of its powers in a fixed ideal of definition.
* `IsAdic.radical_eq`, `IsAdic.le_radical`, and `IsAdic.radical` : ideals of definition have
  the same radical, and a finitely generated radical is the largest ideal of definition.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` (`github.com/MichaelStollBayreuth/EllipticCurves`,
Apache-2.0) at commit `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, file
`EllipticCurves/Mathlib/Chabauty/AdicTopology.lean`, where these appear under the same names
among that development's Mathlib-bound material. That file describes its contents as the
`IsAdic` counterparts of `Ideal.isLinearTopology` and `WithIdeal.isTopologicallyNilpotent_of_mem`,
which is the reading taken here.

The ideal-of-definition criterion and the results about radicals additionally follow
A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.1.4–7.1.7.
-/

public section

namespace IsAdic

variable {R : Type*} [CommRing R] [TopologicalSpace R] {I : Ideal R}

/-- In a ring whose topology is the `I`-adic one, every power of `I` is open. -/
theorem isOpen_pow (hI : IsAdic I) (n : ℕ) : IsOpen ((I ^ n : Ideal R) : Set R) :=
  letI := I.adicTopology
  hI ▸ (I.openAddSubgroup n).isOpen

/-- In a ring whose topology is the `I`-adic one, every power of `I` is closed: it is an open
additive subgroup, and an open subgroup of a topological group is closed. -/
theorem isClosed_pow (hI : IsAdic I) (n : ℕ) : IsClosed ((I ^ n : Ideal R) : Set R) :=
  have : NonarchimedeanRing R := hI ▸ I.nonarchimedean
  AddSubgroup.isClosed_of_isOpen (I ^ n).toAddSubgroup (hI.isOpen_pow n)

open Filter Topology in
/-- In a ring whose topology is the `I`-adic one, a family whose members lie in growing powers of
`I` tends to zero, provided the exponents tend to infinity. Only eventual membership is needed,
since convergence along `l` cannot see failures outside an `l`-large set; a pointwise caller
supplies `Filter.Eventually.of_forall`. The index filter is arbitrary: `atTop` for a sequence,
`cofinite` for the decay condition of `MvPowerSeries.HasEval`. For the powers of a single element
of `I` use `IsAdic.isTopologicallyNilpotent_of_mem` instead. -/
theorem tendsto_zero_of_mem_pow (hI : IsAdic I) {γ : Type*} {l : Filter γ} {g : γ → R} {e : γ → ℕ}
    (hg : ∀ᶠ i in l, g i ∈ I ^ e i) (he : Tendsto e l atTop) : Tendsto g l (𝓝 0) :=
  hI.hasBasis_nhds_zero.tendsto_right_iff.2 fun k _ ↦ by
    filter_upwards [hg, he.eventually_ge_atTop k] with i hi hik
    exact Ideal.pow_le_pow_right hik hi

/-- In a ring whose topology is the `I`-adic one, every element of `I` is topologically
nilpotent. -/
theorem isTopologicallyNilpotent_of_mem (hI : IsAdic I) {a : R} (ha : a ∈ I) :
    IsTopologicallyNilpotent a :=
  hI.tendsto_zero_of_mem_pow (.of_forall (Ideal.pow_mem_pow ha)) Filter.tendsto_id

/-- In a ring whose topology is the `I`-adic one, the topologically nilpotent elements are exactly
the elements of the radical of `I`: a power of a topologically nilpotent element lies in the open
ideal `I`, and if `a ^ n ∈ I` then `a ^ m ∈ I ^ k` as soon as `m ≥ n * k`. -/
theorem isTopologicallyNilpotent_iff_mem_radical (hI : IsAdic I) {a : R} :
    IsTopologicallyNilpotent a ↔ a ∈ I.radical := by
  refine ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩
  · obtain ⟨n, hn⟩ := ha.exists_pow_mem_of_mem_nhds ((hI.isOpen_pow 1).mem_nhds (by simp))
    exact Ideal.mem_radical_iff.mpr ⟨n, by simpa using hn⟩
  · obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ha
    refine hI.hasBasis_nhds_zero.tendsto_right_iff.2 fun k _ ↦
      Filter.eventually_atTop.2 ⟨n * k, fun m hm ↦ ?_⟩
    rw [← Nat.add_sub_of_le hm, pow_add, pow_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hn k)

/-- Ideals defining the same adic topology have the same radical: both radicals consist of
the topologically nilpotent elements. -/
theorem radical_eq {J : Ideal R} (hI : IsAdic I) (hJ : IsAdic J) :
    I.radical = J.radical := by
  ext a
  exact hI.isTopologicallyNilpotent_iff_mem_radical.symm.trans
    hJ.isTopologicallyNilpotent_iff_mem_radical

/-- Every ideal of definition is contained in the radical of any other ideal of definition. -/
theorem le_radical {J : Ideal R} (hI : IsAdic I) (hJ : IsAdic J) : I ≤ J.radical := by
  rw [← hI.radical_eq hJ]
  exact Ideal.le_radical

/-- An ideal defines the `I`-adic topology exactly when it is open and some power lies in `I`.
No finite generation hypothesis is needed (EGA I, Ch. 0, 7.1.4). -/
theorem isAdic_iff_isOpen_and_exists_pow_le {J : Ideal R} (hI : IsAdic I) :
    IsAdic J ↔ IsOpen (J : Set R) ∧ ∃ n : ℕ, J ^ n ≤ I := by
  have : IsTopologicalRing R := hI ▸ I.nonarchimedean.toIsTopologicalRing
  constructor
  · intro hJ
    refine ⟨by simpa using hJ.isOpen_pow 1, ?_⟩
    obtain ⟨n, -, hn⟩ := hJ.hasBasis_nhds_zero.mem_iff.mp
      ((by simpa using hI.isOpen_pow 1 : IsOpen (I : Set R)).mem_nhds I.zero_mem)
    exact ⟨n, hn⟩
  · rintro ⟨hJ, k, hk⟩
    obtain ⟨m, -, hm⟩ := hI.hasBasis_nhds_zero.mem_iff.mp (hJ.mem_nhds J.zero_mem)
    rw [isAdic_iff]
    constructor
    · intro n
      refine Submodule.isOpen_mono ?_ (hI.isOpen_pow (m * n))
      rw [pow_mul]
      exact Ideal.pow_right_mono hm n
    · intro s hs
      obtain ⟨n, -, hn⟩ := hI.hasBasis_nhds_zero.mem_iff.mp hs
      refine ⟨k * n, subset_trans ?_ hn⟩
      rw [pow_mul]
      exact Ideal.pow_right_mono hk n

/-- The radical of an ideal of definition is again an ideal of definition whenever that
radical is finitely generated, in particular over a noetherian ring (EGA I, Ch. 0, 7.1.7). -/
theorem radical (hI : IsAdic I) (hfg : I.radical.FG) : IsAdic I.radical := by
  have : IsTopologicalRing R := hI ▸ I.nonarchimedean.toIsTopologicalRing
  apply hI.isAdic_iff_isOpen_and_exists_pow_le.mpr
  exact ⟨Submodule.isOpen_mono Ideal.le_radical (by simpa using hI.isOpen_pow 1),
    Ideal.exists_pow_le_of_le_radical_of_fg le_rfl hfg⟩

/-- A ring whose topology is the `I`-adic one is linearly topologized: the powers of `I` form a
neighbourhood basis of zero consisting of ideals. This is the `IsAdic` counterpart of
`Ideal.isLinearTopology`. -/
theorem isLinearTopology (hI : IsAdic I) : IsLinearTopology R R :=
  hI ▸ I.isLinearTopology

/-- A ring homomorphism from an `I`-adic ring to a `J`-adic ring is continuous as soon as it
carries `I` into the radical of `J`, provided `I` is finitely generated. Mapping `I` into `J`
itself is the special case `J ≤ J.radical`. -/
theorem continuous_of_map_le_radical {S : Type*} [CommRing S] [TopologicalSpace S] {J : Ideal S}
    (hI : IsAdic I) (hJ : IsAdic J) (hfg : I.FG) {f : R →+* S} (hf : I.map f ≤ J.radical) :
    Continuous f := by
  have : IsTopologicalRing R := hI ▸ I.nonarchimedean.toIsTopologicalRing
  have : IsTopologicalRing S := hJ ▸ J.nonarchimedean.toIsTopologicalRing
  -- the image of `I` is finitely generated, so some power `(f I) ^ k` lies in `J`, and `f`
  -- carries `I ^ (k * n)` into `J ^ n`
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hf (hfg.map f)
  refine continuous_of_tendsto_nhds_zero f ?_
  rw [hI.hasBasis_nhds_zero.tendsto_iff hJ.hasBasis_nhds_zero]
  refine fun n _ ↦ ⟨k * n, trivial, fun x hx ↦ ?_⟩
  have hmem : f x ∈ (I ^ (k * n)).map f := Ideal.mem_map_of_mem f hx
  rw [Ideal.map_pow, pow_mul] at hmem
  exact Ideal.pow_right_mono hk n hmem

/-- A continuous ring homomorphism carries an ideal of definition into the radical of every
ideal of definition of its target. Unlike the converse, this needs no finite generation. -/
theorem map_le_radical_of_continuous {S : Type*} [CommRing S] [TopologicalSpace S]
    {J : Ideal S} (hI : IsAdic I) (hJ : IsAdic J) {f : R →+* S} (hf : Continuous f) :
    I.map f ≤ J.radical := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact hJ.isTopologicallyNilpotent_iff_mem_radical.mp
    ((hI.isTopologicallyNilpotent_of_mem hx).map hf)

/-- Continuity can be tested on arbitrary ideals of definition, provided some finitely
generated ideal defines the source topology. The tested ideals need not be finitely generated,
and neither ring needs to be complete. -/
theorem continuous_iff_map_le_radical {S : Type*} [CommRing S] [TopologicalSpace S]
    {J : Ideal S} {K : Ideal R} (hI : IsAdic I) (hJ : IsAdic J) (hK : IsAdic K)
    (hKfg : K.FG) {f : R →+* S} : Continuous f ↔ I.map f ≤ J.radical := by
  refine ⟨hI.map_le_radical_of_continuous hJ, fun hf ↦ ?_⟩
  apply hK.continuous_of_map_le_radical hJ hKfg
  calc
    K.map f ≤ K.radical.map f := Ideal.map_mono Ideal.le_radical
    _ = I.radical.map f := congrArg (Ideal.map f) (hK.radical_eq hI)
    _ ≤ (I.map f).radical := Ideal.map_radical_le f
    _ ≤ J.radical := Ideal.radical_le_radical_iff.mpr hf

/-- When the source topology has a finitely generated ideal of definition, a ring homomorphism
is continuous exactly when it sends every element of any ideal of definition to a
topologically nilpotent element. Neither ring needs to be complete. -/
theorem continuous_iff_forall_isTopologicallyNilpotent {S : Type*} [CommRing S]
    [TopologicalSpace S] {J : Ideal S} {K : Ideal R} (hI : IsAdic I) (hJ : IsAdic J)
    (hK : IsAdic K) (hKfg : K.FG) {f : R →+* S} :
    Continuous f ↔ ∀ a ∈ I, IsTopologicallyNilpotent (f a) := by
  rw [hI.continuous_iff_map_le_radical hJ hK hKfg, Ideal.map_le_iff_le_comap]
  simp only [IsConcreteLE.le_iff, Ideal.mem_comap, hJ.isTopologicallyNilpotent_iff_mem_radical]

/-- A ring whose topology is the `I`-adic one is also `J`-adic for every finitely generated ideal
`J` with the same radical as the finitely generated ideal `I`: each power of either ideal contains
a power of the other. -/
theorem of_radical_eq {J : Ideal R} (hI : IsAdic I) (hIfg : I.FG) (hJfg : J.FG)
    (h : I.radical = J.radical) : IsAdic J := by
  have : IsTopologicalRing R := hI ▸ I.nonarchimedean.toIsTopologicalRing
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (Ideal.le_radical.trans h.le) hIfg
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (Ideal.le_radical.trans h.ge) hJfg
  rw [isAdic_iff]
  refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · -- `J ^ n` contains the open ideal `I ^ (k * n)`
    refine Submodule.isOpen_mono ?_ (hI.isOpen_pow (k * n))
    rw [pow_mul]
    exact Ideal.pow_right_mono hk n
  · -- `s` contains some `I ^ n`, which contains `J ^ (m * n)`
    obtain ⟨n, -, hn⟩ := hI.hasBasis_nhds_zero.mem_iff.mp hs
    refine ⟨m * n, subset_trans ?_ hn⟩
    rw [pow_mul]
    exact Ideal.pow_right_mono hm n

end IsAdic

/-- Finitely generated ideals with the same radical define the same adic topology. -/
theorem Ideal.adicTopology_eq_of_radical_eq {R : Type*} [CommRing R] {I J : Ideal R}
    (hIfg : I.FG) (hJfg : J.FG) (h : I.radical = J.radical) :
    I.adicTopology = J.adicTopology :=
  letI := I.adicTopology
  -- for the `I`-adic topology, `IsAdic I` is `rfl` by the definition of `IsAdic`
  IsAdic.of_radical_eq (I := I) rfl hIfg hJfg h

namespace TauCeti

/-- An ideal defining an adic topology is open. -/
theorem IsAdic.isOpen_ideal {R : Type*} [CommRing R] [TopologicalSpace R] {I : Ideal R}
    (hI : IsAdic I) : IsOpen (I : Set R) := by
  simpa only [pow_one] using hI.isOpen_pow 1

end TauCeti

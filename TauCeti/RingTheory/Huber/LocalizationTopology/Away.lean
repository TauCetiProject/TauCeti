/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.RingTheory.Localization.Away.Topology

/-!
# The Tate ring `A₀[1/π]` of an element `π`

Let `A₀` be a commutative ring, `π ∈ A₀`, and `A` a localisation of `A₀` away from `π`. The
*`π`-adic topology* on `A = A₀[1/π]` is the ring topology whose neighbourhoods of zero have basis
the images `πⁿ A₀` of the powers of the ideal `(π)`. The image `A⁺` of `A₀` is then an open
bounded subring on which the topology is the `π`-adic one, and `π` becomes a topologically
nilpotent unit, so `A` is a Tate ring. If `π` is a nonzerodivisor, then `A₀ → A` is injective, and
`A` is Hausdorff, resp. complete, as soon as `A₀` is `π`-adically separated, resp. precomplete.

This is how complete Tate rings are made out of `π`-adically complete rings: the untilt
`W(R⁺)[1/[ϖ]] ⧸ J` of a perfectoid Tate pair `(R, R⁺)` of characteristic `p` along a primitive
ideal `J`, with `A₀ = W(R⁺) ⧸ J` and `π` the class of `[ϖ]`, and more generally the Tate ring
`R₀[1/π]` of an integral perfectoid ring `R₀` with a nonzerodivisor `π`, carry this topology. It
is Wedhorn's localisation topology with numerator `π` and denominator `π` on the `π`-adic ring
`A₀`; here `A₀` need carry no topology, which is the situation of these constructions.

This is `TauCeti.localizedTopology π ⊤ A`, with basic subgroups
`TauCeti.localizedSubgroup π ⊤ A n`. The results are stated for any topology on `A` whose
neighbourhoods of zero have the basis `πⁿ A₀`, so they also apply to a carrier with its own
instance. `TauCeti.hasBasis_nhds_zero_localizedTopology` supplies this basis for the canonical
construction.

## Main results

* `TauCeti.Huber.algebraMap_mem_localizedSubgroup_top_iff`,
  `TauCeti.Huber.sModEq_iff_algebraMap_sub_mem_localizedSubgroup_top`: if `π` is a nonzerodivisor,
  `πⁿ A₀` restricts to the ideal `(πⁿ)` of `A₀`.
* `TauCeti.Huber.isOpen_range_algebraMap_of_hasBasis`,
  `TauCeti.Huber.isBounded_range_algebraMap_of_hasBasis`: the image of `A₀` is open and bounded.
* `TauCeti.Huber.isOpen_subring_of_hasBasis`, `TauCeti.Huber.isBounded_subring_of_hasBasis`: the
  same for a subring `S ⊆ A` with the topology of basis `ϖⁿ S`.
* `TauCeti.Huber.isPseudoUniformizer_algebraMap_of_hasBasis`: `π` is a pseudouniformiser of `A`.
* `TauCeti.Huber.isTateRing_of_hasBasis`: `A` is a Tate ring.
* `TauCeti.Huber.t2Space_of_hasBasis`: `A` is Hausdorff if `π` is a nonzerodivisor and `A₀` is
  `π`-adically separated.
* `TauCeti.Huber.completeSpace_of_hasBasis`: `A` is complete if `π` is a nonzerodivisor and `A₀`
  is `π`-adically precomplete.

## References

* P. Scholze, *Étale cohomology of diamonds*, Theorem 3.17 and its proof.
* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.21.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition and Definition 5.51.
-/

public section

open Filter Topology Uniformity
open scoped nonZeroDivisors

namespace TauCeti.Huber

variable {A₀ : Type*} [CommRing A₀] (π : A₀) (A : Type*) [CommRing A] [Algebra A₀ A]

variable {π A} [IsLocalization.Away π A]

/-- If `π` is a nonzerodivisor, the image of `a ∈ A₀` lies in `πⁿ A₀` exactly when `πⁿ` divides
`a`: the neighbourhoods `πⁿ A₀` restrict to the `π`-adic filtration of `A₀`. -/
theorem algebraMap_mem_localizedSubgroup_top_iff (hπ : π ∈ A₀⁰) {n : ℕ} {a : A₀} :
    algebraMap A₀ A a ∈ localizedSubgroup π ⊤ A n ↔ π ^ n ∣ a := by
  rw [mem_localizedSubgroup, Ideal.mul_top, Ideal.span_singleton_pow]
  simpa only [(IsLocalization.injective A (Submonoid.powers_le.mpr hπ)).eq_iff, exists_eq_right]
    using (Ideal.mem_span_singleton (x := a) (y := π ^ n))

/-- If `π` is a nonzerodivisor, `a ≡ b` modulo `(π)ⁿ` in `A₀` exactly when the image of `a - b`
lies in `πⁿ A₀`. -/
theorem sModEq_iff_algebraMap_sub_mem_localizedSubgroup_top (hπ : π ∈ A₀⁰) {n : ℕ} {a b : A₀} :
    a ≡ b [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule A₀ A₀)] ↔
      algebraMap A₀ A (a - b) ∈ localizedSubgroup π ⊤ A n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, algebraMap_mem_localizedSubgroup_top_iff hπ]

/-! ### Topologies with basis `πⁿ A₀` -/

section HasBasis

variable [TopologicalSpace A]
  (h : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (localizedSubgroup π ⊤ A n : Set A))
include h

omit [IsLocalization.Away π A] in
/-- **The image of `A₀` is open** in `A₀[1/π]` for the `π`-adic topology. -/
theorem isOpen_range_algebraMap_of_hasBasis [SeparatelyContinuousAdd A] :
    IsOpen ((algebraMap A₀ A).range : Set A) := by
  refine AddSubgroup.isOpen_of_mem_nhds (algebraMap A₀ A).range.toAddSubgroup (g := 0) ?_
  rw [Subring.coe_toAddSubgroup, RingHom.coe_range, ← coe_localizedSubgroup_zero_top]
  exact h.mem_of_mem trivial

omit [IsLocalization.Away π A] in
/-- **The image of `A₀` is bounded** in `A₀[1/π]` for the `π`-adic topology. -/
theorem isBounded_range_algebraMap_of_hasBasis :
    IsBounded ((algebraMap A₀ A).range : Set A) := isBounded_iff.mpr fun U hU ↦ by
  obtain ⟨n, -, hn⟩ := h.mem_iff.mp hU
  refine ⟨_, h.mem_of_mem (i := n) trivial, ?_⟩
  rintro _ ⟨x, hx, _, ⟨a, rfl⟩, rfl⟩
  dsimp only
  rw [mul_comm]
  simpa using hn (algebraMap_pow_mul_mul_mem_localizedSubgroup π ⊤ A (k := 0) a hx)

/-- **`π` is a pseudouniformiser** of `A₀[1/π]` for the `π`-adic topology: it is a unit, and its
powers tend to zero. -/
theorem isPseudoUniformizer_algebraMap_of_hasBasis :
    IsPseudoUniformizer (algebraMap A₀ A π) := by
  refine isPseudoUniformizer_iff.mpr
    ⟨IsLocalization.Away.algebraMap_isUnit π, h.tendsto_right_iff.mpr fun n _ ↦ ?_⟩
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [← map_pow, ← Nat.add_sub_cancel' hm, pow_add]
  exact (mem_localizedSubgroup_iff π ⊤ A n _).mpr ⟨π ^ (m - n), Submodule.mem_top, rfl⟩

/-- **`A₀[1/π]` is a Tate ring** for the `π`-adic topology, with pair of definition the image of
`A₀` and its ideal generated by `π` (`TauCeti.Huber.PairOfDefinition.ofIsPseudoUniformizer`). -/
theorem isTateRing_of_hasBasis [IsTopologicalRing A] : IsTateRing A :=
  IsTateRing.of_isOpen_isBounded _ (isOpen_range_algebraMap_of_hasBasis h)
    (isBounded_range_algebraMap_of_hasBasis h) (isPseudoUniformizer_algebraMap_of_hasBasis h)

/-- **`A₀[1/π]` is Hausdorff** for the `π`-adic topology when `π` is a nonzerodivisor and `A₀` is
`π`-adically separated. -/
theorem t2Space_of_hasBasis [IsTopologicalAddGroup A] (hπ : π ∈ A₀⁰)
    [IsHausdorff (Ideal.span {π}) A₀] : T2Space A := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx ↦ ?_
  by_contra! hU
  have hmem (n : ℕ) : x ∈ localizedSubgroup π ⊤ A n := hU _ (h.mem_of_mem trivial)
  obtain ⟨a, rfl⟩ := (coe_localizedSubgroup_zero_top π A ▸ hmem 0 :
    x ∈ Set.range (algebraMap A₀ A))
  refine hx ?_
  rw [IsHausdorff.haus (I := Ideal.span {π}) inferInstance a fun n ↦
    (sModEq_iff_algebraMap_sub_mem_localizedSubgroup_top (A := A) hπ).mpr
      (by simpa using hmem n), map_zero]

end HasBasis

section Subring

/-! ### A subring `S ⊆ A` with `A = S[1/π]`

For a subring `S` of `A` and `π ∈ S`, the image of `S` in `A` is `S` itself, so the results above
say that `S` is open and bounded in `A`. -/

variable [TopologicalSpace A] {S : Subring A} {ϖ : S}
  (h : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (localizedSubgroup ϖ ⊤ A n : Set A))
include h

/-- **A subring `S` is open** in `A` for the topology with basis `ϖⁿ S`. -/
theorem isOpen_subring_of_hasBasis [SeparatelyContinuousAdd A] : IsOpen (S : Set A) := by
  rw [← Subring.range_subtype S]
  exact isOpen_range_algebraMap_of_hasBasis h

/-- **A subring `S` is bounded** in `A` for the topology with basis `ϖⁿ S`. -/
theorem isBounded_subring_of_hasBasis : IsBounded (S : Set A) := by
  rw [← Subring.range_subtype S]
  exact isBounded_range_algebraMap_of_hasBasis h

end Subring

/-- **`A₀[1/π]` is complete** for the `π`-adic topology when `π` is a nonzerodivisor and `A₀` is
`π`-adically precomplete. Here `A` carries any uniform structure compatible with its additive group
whose neighbourhoods of zero have basis `πⁿ A₀`. -/
theorem completeSpace_of_hasBasis [UniformSpace A] [IsUniformAddGroup A]
    (h : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (localizedSubgroup π ⊤ A n : Set A))
    (hπ : π ∈ A₀⁰)
    [IsPrecomplete (Ideal.span {π}) A₀] : CompleteSpace A := by
  -- A Cauchy sequence eventually stays in a coset of the image of `A₀`, where it is the image of a
  -- `π`-adically Cauchy sequence of `A₀`; the image of its limit, translated back, is a limit of
  -- the sequence.
  have hu := h.uniformity_of_nhds_zero
  have : (𝓤 A).IsCountablyGenerated := hu.isCountablyGenerated
  refine UniformSpace.complete_of_cauchySeq_tendsto fun u hcau ↦ ?_
  -- `u n - u m ∈ πⁱ A₀` for all `n, m ≥ N₀ i`; make the thresholds monotone.
  have hN₀ (i : ℕ) : ∃ N, ∀ n ≥ N, u N - u n ∈ localizedSubgroup π ⊤ A i :=
    hu.cauchySeq_iff'.mp hcau i trivial
  choose N₀ hN₀ using hN₀
  have hsub {i n m : ℕ} (hn : N₀ i ≤ n) (hm : N₀ i ≤ m) :
      u n - u m ∈ localizedSubgroup π ⊤ A i := by
    simpa using sub_mem (hN₀ i m hm) (hN₀ i n hn)
  let N (i : ℕ) : ℕ := (Finset.range (i + 1)).sup N₀
  have hN {i j : ℕ} (hij : i ≤ j) : N₀ i ≤ N j :=
    Finset.le_sup (f := N₀) (Finset.mem_range.mpr (Nat.lt_succ_of_le hij))
  -- Write `u (N i) - u (N 0) = f i` with `f i ∈ A₀`; these are `π`-adically Cauchy.
  have hf (i : ℕ) : ∃ a : A₀, algebraMap A₀ A a = u (N i) - u (N 0) := by
    simpa using hsub (hN (Nat.zero_le i)) (hN le_rfl)
  choose f hf using hf
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {π}) inferInstance (f := f)
    fun {i j} hij ↦ by
      rw [sModEq_iff_algebraMap_sub_mem_localizedSubgroup_top (A := A) hπ,
        map_sub, hf, hf, sub_sub_sub_cancel_right]
      exact hsub (hN le_rfl) (hN hij)
  refine ⟨u (N 0) + algebraMap A₀ A L,
    tendsto_sub_nhds_zero_iff.mp (h.tendsto_right_iff.mpr fun i _ ↦ ?_)⟩
  filter_upwards [eventually_ge_atTop (N₀ i)] with n hn
  have hfL : algebraMap A₀ A (f i - L) ∈ localizedSubgroup π ⊤ A i :=
    (sModEq_iff_algebraMap_sub_mem_localizedSubgroup_top hπ).mp (hL i)
  have hdecomp : u n - (u (N 0) + algebraMap A₀ A L) =
      (u n - u (N i)) + algebraMap A₀ A (f i - L) := by
    rw [map_sub, hf]
    ring
  rw [hdecomp]
  exact add_mem (hsub hn (hN le_rfl)) hfL

end TauCeti.Huber

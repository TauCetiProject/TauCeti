/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import TauCeti.RingTheory.Huber.Basic

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

The topology `TauCeti.Huber.awayTopology` is a definition, not an instance, since `A` is an
arbitrary localisation. The results about it are stated for any topology on `A` whose
neighbourhoods of zero have the basis `πⁿ A₀`, so that they apply equally to a carrier with its
own topology instance; `TauCeti.Huber.hasBasis_nhds_zero_awayTopology` supplies the basis for
`awayTopology` itself.

## Main definitions

* `TauCeti.Huber.awayNhd π A n`: the additive subgroup `πⁿ A₀` of `A`.
* `TauCeti.Huber.awayTopology π A`: the ring topology on `A` with basis `πⁿ A₀`.

## Main results

* `TauCeti.Huber.isTopologicalRing_awayTopology`, `TauCeti.Huber.nonarchimedeanRing_awayTopology`:
  `awayTopology` is a nonarchimedean ring topology.
* `TauCeti.Huber.algebraMap_mem_awayNhd_iff`: if `π` is a nonzerodivisor, `πⁿ A₀` restricts to
  the ideal `(πⁿ)` of `A₀`.
* `TauCeti.Huber.isOpen_range_algebraMap_of_hasBasis`,
  `TauCeti.Huber.isBounded_range_algebraMap_of_hasBasis`: the image of `A₀` is open and bounded.
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

/-- The additive subgroup `πⁿ A₀` of `A`: the image of the ideal `(πⁿ)` of `A₀`. These are the
basic neighbourhoods of zero of the `π`-adic topology on `A₀[1/π]`. -/
def awayNhd (n : ℕ) : AddSubgroup A :=
  (Ideal.span {π ^ n}).toAddSubgroup.map (algebraMap A₀ A).toAddMonoidHom

variable {π A}

/-- An element of `A` lies in `πⁿ A₀` exactly when it is the image of a multiple of `πⁿ`. -/
@[simp]
theorem mem_awayNhd {n : ℕ} {x : A} :
    x ∈ awayNhd π A n ↔ ∃ a : A₀, algebraMap A₀ A (π ^ n * a) = x := by
  simp only [awayNhd, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, by rw [mul_comm]; rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨a, mul_comm a _⟩, rfl⟩

/-- The image of `πⁿ a` lies in `πⁿ A₀`. -/
theorem algebraMap_pow_mul_mem_awayNhd (n : ℕ) (a : A₀) :
    algebraMap A₀ A (π ^ n * a) ∈ awayNhd π A n :=
  mem_awayNhd.mpr ⟨a, rfl⟩

/-- The neighbourhood `π⁰ A₀` is the image of `A₀`. -/
theorem coe_awayNhd_zero : (awayNhd π A 0 : Set A) = Set.range (algebraMap A₀ A) := by
  ext x
  simp

/-- The neighbourhoods `πⁿ A₀` decrease. -/
theorem awayNhd_antitone : Antitone (awayNhd π A) := fun m n hmn x hx ↦ by
  obtain ⟨a, rfl⟩ := mem_awayNhd.mp hx
  rw [← Nat.add_sub_cancel' hmn, pow_add, mul_assoc]
  exact algebraMap_pow_mul_mem_awayNhd _ _

/-- Multiplication by the image of `πᵏ a` carries `πⁿ A₀` into `πⁿ⁺ᵏ A₀`. -/
theorem algebraMap_pow_mul_mul_mem_awayNhd {n k : ℕ} (a : A₀) {x : A} (hx : x ∈ awayNhd π A n) :
    algebraMap A₀ A (π ^ k * a) * x ∈ awayNhd π A (n + k) := by
  obtain ⟨b, rfl⟩ := mem_awayNhd.mp hx
  rw [← map_mul, show π ^ k * a * (π ^ n * b) = π ^ (n + k) * (a * b) by ring]
  exact algebraMap_pow_mul_mem_awayNhd _ _

/-- The product of two elements of `πⁿ A₀` lies in `πⁿ A₀`. -/
theorem mul_mem_awayNhd {n : ℕ} {x y : A} (hx : x ∈ awayNhd π A n) (hy : y ∈ awayNhd π A n) :
    x * y ∈ awayNhd π A n := by
  obtain ⟨a, rfl⟩ := mem_awayNhd.mp hx
  exact awayNhd_antitone (Nat.le_add_right n n) (algebraMap_pow_mul_mul_mem_awayNhd a hy)

variable [IsLocalization.Away π A]

/-- Multiplication by a fixed element `x = a / πᵏ` of `A₀[1/π]` carries `πⁿ⁺ᵏ A₀` into `πⁿ A₀`. -/
private theorem exists_mul_mem_awayNhd (x : A) (n : ℕ) :
    ∃ m, ∀ y ∈ awayNhd π A m, x * y ∈ awayNhd π A n := by
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj π x
  refine ⟨n + k, fun y hy ↦ ?_⟩
  obtain ⟨b, rfl⟩ := mem_awayNhd.mp hy
  have hx : x * algebraMap A₀ A (π ^ k) = algebraMap A₀ A a := by rw [map_pow, ha]
  rw [show π ^ (n + k) * b = π ^ k * (π ^ n * b) by ring, map_mul, ← mul_assoc, hx, ← map_mul,
    mul_left_comm]
  exact algebraMap_pow_mul_mem_awayNhd _ _

variable (π A) in
private theorem awayBasis : RingSubgroupsBasis (awayNhd π A) :=
  .of_comm _ (fun i j ↦ ⟨max i j, le_inf (awayNhd_antitone (le_max_left i j))
      (awayNhd_antitone (le_max_right i j))⟩)
    (fun i ↦ ⟨i, fun _ ⟨_, hx, _, hy, hxy⟩ ↦ hxy ▸ mul_mem_awayNhd hx hy⟩)
    fun x i ↦ (exists_mul_mem_awayNhd x i).imp fun _ h y hy ↦ h y hy

variable (π A) in
/-- **The `π`-adic topology on `A₀[1/π]`**: the ring topology on a localisation `A` of `A₀` away
from `π` whose neighbourhoods of zero have basis the images `πⁿ A₀` of the ideals `(πⁿ)`. It is not
an instance; `hasBasis_nhds_zero_awayTopology` is its contract. -/
@[instance_reducible] noncomputable def awayTopology : TopologicalSpace A :=
  (awayBasis π A).topology

/-- The contract of `awayTopology`: the subgroups `πⁿ A₀` are a basis of neighbourhoods of zero. -/
theorem hasBasis_nhds_zero_awayTopology :
    (@nhds A (awayTopology π A) 0).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (awayNhd π A n : Set A) :=
  (awayBasis π A).hasBasis_nhds_zero

/-- `awayTopology` is a ring topology. -/
theorem isTopologicalRing_awayTopology : @IsTopologicalRing A (awayTopology π A) _ :=
  (awayBasis π A).toRingFilterBasis.isTopologicalRing

/-- `awayTopology` is nonarchimedean. -/
theorem nonarchimedeanRing_awayTopology : @NonarchimedeanRing A _ (awayTopology π A) :=
  (awayBasis π A).nonarchimedean

/-- If `π` is a nonzerodivisor, the image of `a ∈ A₀` lies in `πⁿ A₀` exactly when `πⁿ` divides
`a`: the neighbourhoods `πⁿ A₀` restrict to the `π`-adic filtration of `A₀`. -/
theorem algebraMap_mem_awayNhd_iff (hπ : π ∈ A₀⁰) {n : ℕ} {a : A₀} :
    algebraMap A₀ A a ∈ awayNhd π A n ↔ π ^ n ∣ a := by
  refine ⟨fun ha ↦ ?_, fun ⟨b, hb⟩ ↦ hb ▸ algebraMap_pow_mul_mem_awayNhd _ _⟩
  obtain ⟨b, hb⟩ := mem_awayNhd.mp ha
  exact ⟨b, (IsLocalization.injective A (Submonoid.powers_le.mpr hπ) hb).symm⟩

/-! ### Topologies with basis `πⁿ A₀` -/

section HasBasis

variable [TopologicalSpace A]
  (h : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (awayNhd π A n : Set A))
include h

omit [IsLocalization.Away π A] in
/-- **The image of `A₀` is open** in `A₀[1/π]` for the `π`-adic topology. -/
theorem isOpen_range_algebraMap_of_hasBasis [SeparatelyContinuousAdd A] :
    IsOpen ((algebraMap A₀ A).range : Set A) := by
  refine AddSubgroup.isOpen_of_mem_nhds (algebraMap A₀ A).range.toAddSubgroup (g := 0) ?_
  rw [Subring.coe_toAddSubgroup, RingHom.coe_range, ← coe_awayNhd_zero]
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
  simpa using hn (algebraMap_pow_mul_mul_mem_awayNhd (k := 0) a hx)

/-- **`π` is a pseudouniformiser** of `A₀[1/π]` for the `π`-adic topology: it is a unit, and its
powers tend to zero. -/
theorem isPseudoUniformizer_algebraMap_of_hasBasis :
    IsPseudoUniformizer (algebraMap A₀ A π) := by
  refine isPseudoUniformizer_iff.mpr
    ⟨IsLocalization.Away.algebraMap_isUnit π, h.tendsto_right_iff.mpr fun n _ ↦ ?_⟩
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [← map_pow, ← Nat.add_sub_cancel' hm, pow_add]
  exact algebraMap_pow_mul_mem_awayNhd _ _

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
  have hmem (n : ℕ) : x ∈ awayNhd π A n := hU _ (h.mem_of_mem trivial)
  obtain ⟨a, rfl⟩ := mem_awayNhd.mp (hmem 0)
  refine hx ?_
  rw [IsHausdorff.haus (I := Ideal.span {π}) inferInstance (π ^ 0 * a) fun n ↦ ?_, map_zero]
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← algebraMap_mem_awayNhd_iff (A := A) hπ]
  exact hmem n

end HasBasis

/-- **`A₀[1/π]` is complete** for the `π`-adic topology when `π` is a nonzerodivisor and `A₀` is
`π`-adically precomplete. A Cauchy sequence eventually stays in a coset of the image of `A₀`, where
it is the image of a `π`-adically Cauchy sequence of `A₀`; the image of its limit, translated back,
is a limit of the sequence. -/
theorem completeSpace_of_hasBasis [UniformSpace A] [IsUniformAddGroup A]
    (h : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (awayNhd π A n : Set A)) (hπ : π ∈ A₀⁰)
    [IsPrecomplete (Ideal.span {π}) A₀] : CompleteSpace A := by
  have hu := h.uniformity_of_nhds_zero
  have : (𝓤 A).IsCountablyGenerated := hu.isCountablyGenerated
  refine UniformSpace.complete_of_cauchySeq_tendsto fun u hcau ↦ ?_
  -- `u n - u m ∈ πⁱ A₀` for all `n, m ≥ N₀ i`; make the thresholds monotone.
  have hN₀ (i : ℕ) : ∃ N, ∀ n ≥ N, u N - u n ∈ awayNhd π A i := hu.cauchySeq_iff'.mp hcau i trivial
  choose N₀ hN₀ using hN₀
  have hsub {i n m : ℕ} (hn : N₀ i ≤ n) (hm : N₀ i ≤ m) : u n - u m ∈ awayNhd π A i := by
    simpa using sub_mem (hN₀ i m hm) (hN₀ i n hn)
  let N (i : ℕ) : ℕ := (Finset.range (i + 1)).sup N₀
  have hN {i j : ℕ} (hij : i ≤ j) : N₀ i ≤ N j :=
    Finset.le_sup (f := N₀) (Finset.mem_range.mpr (Nat.lt_succ_of_le hij))
  -- Write `u (N i) - u (N 0) = f i` with `f i ∈ A₀`; these are `π`-adically Cauchy.
  have hf (i : ℕ) : ∃ a : A₀, algebraMap A₀ A a = u (N i) - u (N 0) := by
    simpa [mem_awayNhd] using hsub (hN (Nat.zero_le i)) (hN le_rfl)
  choose f hf using hf
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {π}) inferInstance (f := f)
    fun {i j} hij ↦ by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, ← algebraMap_mem_awayNhd_iff (A := A) hπ, map_sub, hf, hf,
        sub_sub_sub_cancel_right]
      exact hsub (hN le_rfl) (hN hij)
  refine ⟨u (N 0) + algebraMap A₀ A L,
    tendsto_sub_nhds_zero_iff.mp (h.tendsto_right_iff.mpr fun i _ ↦ ?_)⟩
  filter_upwards [eventually_ge_atTop (N₀ i)] with n hn
  have hfL : algebraMap A₀ A (f i - L) ∈ awayNhd π A i := by
    have := SModEq.sub_mem.mp (hL i)
    rwa [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      ← algebraMap_mem_awayNhd_iff (A := A) hπ] at this
  have hdecomp : u n - (u (N 0) + algebraMap A₀ A L) =
      (u n - u (N i)) + algebraMap A₀ A (f i - L) := by
    rw [map_sub, hf]
    ring
  rw [hdecomp]
  exact add_mem (hsub hn (hN le_rfl)) hfL


end TauCeti.Huber

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Bilinear
public import TauCeti.Algebra.Lie.Current.LeftIdeal

/-!
# The depth filtration of a congruence quotient

Let `U = U(ĝ) / (ι K - a)` be the enveloping algebra at the central value `a` of the residue
central extension of formal currents `L((t))`, and let `Q_M = U / I_M` be its congruence quotient,
the left module induced from the currents of order at least `M`, with cyclic vector `v`, the class
of `1`. A mode `x_m = tᵐ ⊗ x` of order `m < M` has *depth* `M - m ≥ 1`. The depth-`n` submodule
`TauCeti.CurrentAlgebra.depthSubmodule Φ hΦ hΦs a M n` is the `R`-span of the vectors

`x¹_{m₁} ⋯ xᵏ_{mₖ} · v` with `mᵢ < M` and `∑ᵢ (M - mᵢ) ≤ n`.

The bound involves both the length of a word and its mode indices. These submodules increase
with `n`, vanish for `n < 0`, contain `v` for `n ≥ 0` and exhaust `Q_M` when `M ≥ 0`
(`TauCeti.CurrentAlgebra.exists_mem_depthSubmodule`).

The main estimate is `TauCeti.CurrentAlgebra.envelopingι_smul_mem_depthSubmodule_sub`: for
`0 ≤ M ≤ N`, a current of order at least `N` maps depth `n` into depth `n - N`. It is proved by
commuting the current through a word: the commutator `[z, x_m]` of a current `z` of order at
least `N` has order at least `N + m`, and its part of order below `M` has depth at most
`M - N - m`, which is smaller than the depth `M - m` of `x_m` by `N`. Its part of order at least
`M` is treated by induction on the length of the word. The central term `a Res(z dx_m)` vanishes
unless `N + m ≤ 0`, when the depth of `x_m` alone is at least `N + M`. Consequently:

* the currents of order at least `M` preserve every depth submodule when `M ≥ 0`
  (`TauCeti.CurrentAlgebra.envelopingι_smul_mem_depthSubmodule`);
* the currents of order at least `N > n` kill depth `n`, so the action of the currents of order
  at least `M` on it factors through the finite jet quotient by those of order at least
  `max M (n + 1)` (`TauCeti.CurrentAlgebra.envelopingι_smul_eq_zero_of_mem_depthSubmodule`);
* every product of `k` currents of order at least `M` lowers the depth by `k M`, so for `M > 0`
  products of more than `n / M` of them kill depth `n`
  (`TauCeti.CurrentAlgebra.list_prod_smul_eq_zero_of_mem_depthSubmodule`).

When `L` is a finite `R`-module, each depth submodule is finitely generated
(`TauCeti.CurrentAlgebra.depthSubmodule_fg`). Together:
`TauCeti.CurrentAlgebra.exists_mem_fg_submodule_jet_nilpotent` puts every vector of `Q_M`, for
`M > 0`, in a finitely generated submodule stable under the currents of order at least `M`,
killed by the currents of some order `N`, and killed by every product of `N` currents of order at
least `M`. This is the finite-jet nilpotence needed to integrate the action of the positive
currents on finitely generated smooth modules to the congruence subgroups; no group action is
constructed here. A bound on the length of words alone would not suffice: in `Q_1` for `sl₂`,
`h_1^r e_{-r} v = 2^r e_0 v ≠ 0` for every `r ≥ 1`, while every `e_{-r} v` has length one.

## Main definitions

* `TauCeti.CurrentAlgebra.depthSubmodule`: the span of the words of depth at most `n` applied to
  the cyclic vector of `U / I_M`.

## Main results

* `TauCeti.CurrentAlgebra.envelopingι_smul_mem_depthSubmodule_sub`: currents of order at least
  `N ≥ M ≥ 0` lower the depth by `N`.
* `TauCeti.CurrentAlgebra.exists_mem_depthSubmodule`: every vector has finite depth.
* `TauCeti.CurrentAlgebra.depthSubmodule_fg`: depth submodules are finitely generated.
* `TauCeti.CurrentAlgebra.exists_mem_fg_submodule_jet_nilpotent`: every vector of `U / I_M`, for
  `M > 0`, lies in a finitely generated stable submodule on which the action of the currents of
  order at least `M` factors through a finite jet and is nilpotent.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3.1 and Lemma 1.3.1, for smooth
  representations of `ĝ` and their integration to the congruence subgroups of `G[[t]]`.
-/

public section

noncomputable section

open scoped TensorProduct LaurentSeries
open LieAlgebra TauCeti.UniversalEnvelopingAlgebra
open LieAlgebra.ofTwoCocycle (centralElement envelopingι adjoin_range_envelopingι)

-- Match the coefficientwise algebra structure used by formal currents.
attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

local notation "C" => currentAlgebra R L
local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "U" => CentralQuotient R (centralElement c) a

/-- The depth-`n` submodule of the congruence quotient `U / I_M`: the `R`-span of the products
`x¹_{m₁} ⋯ xᵏ_{mₖ}` of modes `xᵢ_{mᵢ} = t^{mᵢ} ⊗ xᵢ` with `mᵢ < M` and `∑ᵢ (M - mᵢ) ≤ n`, applied to
the class of `1`. -/
def depthSubmodule (M n : ℤ) : Submodule R (U ⧸ orderLeftIdeal Φ hΦ hΦs a M) :=
  Submodule.span R {q | ∃ l : List (ℤ × L), (∀ p ∈ l, p.1 < M) ∧
    (l.map fun p ↦ M - p.1).sum ≤ n ∧
    q = Submodule.Quotient.mk (l.map fun p ↦ envelopingι c a (HahnSeries.single p.1 1 ⊗ₜ p.2)).prod}

/-- The depth-`n` submodule is spanned by the words of modes of order below `M` and total depth
at most `n` applied to the class of `1`. -/
theorem depthSubmodule_def (M n : ℤ) : depthSubmodule Φ hΦ hΦs a M n =
    Submodule.span R {q | ∃ l : List (ℤ × L), (∀ p ∈ l, p.1 < M) ∧
      (l.map fun p ↦ M - p.1).sum ≤ n ∧
      q = Submodule.Quotient.mk
        (l.map fun p ↦ envelopingι c a (HahnSeries.single p.1 1 ⊗ₜ p.2)).prod} :=
  (rfl)

variable {Φ hΦ hΦs a}

/-- A word of modes of order below `M` and total depth at most `n`, applied to the class of `1`,
has depth at most `n`. -/
theorem mk_list_prod_mem_depthSubmodule {M n : ℤ} {l : List (ℤ × L)} (hl : ∀ p ∈ l, p.1 < M)
    (hn : (l.map fun p ↦ M - p.1).sum ≤ n) :
    Submodule.Quotient.mk (p := orderLeftIdeal Φ hΦ hΦs a M)
        (l.map fun p ↦ envelopingι c a (HahnSeries.single p.1 1 ⊗ₜ p.2)).prod ∈
      depthSubmodule Φ hΦ hΦs a M n :=
  Submodule.subset_span ⟨l, hl, hn, rfl⟩

variable (Φ hΦ hΦs a) in
/-- The depth submodules increase with the depth. -/
theorem depthSubmodule_mono (M : ℤ) : Monotone (depthSubmodule Φ hΦ hΦs a M) := fun _ _ h ↦
  Submodule.span_mono fun _ ⟨l, hl, hn, hq⟩ ↦ ⟨l, hl, hn.trans h, hq⟩

omit [LieRing L] in
/-- The depth of a word of modes of order below `M` is nonnegative. -/
private theorem sum_depth_nonneg {M : ℤ} {l : List (ℤ × L)} (hl : ∀ p ∈ l, p.1 < M) :
    0 ≤ (l.map fun p ↦ M - p.1).sum :=
  List.sum_nonneg fun _ hd ↦ by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
    exact sub_nonneg.mpr (hl p hp).le

/-- There are no vectors of negative depth. -/
theorem depthSubmodule_eq_bot {M n : ℤ} (hn : n < 0) : depthSubmodule Φ hΦ hΦs a M n = ⊥ := by
  rw [depthSubmodule_def, Submodule.span_eq_bot]
  rintro _ ⟨l, hl, hln, -⟩
  exact absurd (sum_depth_nonneg hl) (by omega)

/-- The class of `1` has depth zero. -/
theorem mk_one_mem_depthSubmodule {M n : ℤ} (hn : 0 ≤ n) :
    Submodule.Quotient.mk 1 ∈ depthSubmodule Φ hΦ hΦs a M n :=
  Submodule.subset_span ⟨[], by simp, by simpa using hn, by simp⟩

/-- **A mode of order `m < M` raises the depth by `M - m`.** -/
theorem envelopingι_single_smul_mem_depthSubmodule {M n m : ℤ} (hm : m < M) (x : L)
    {q : U ⧸ orderLeftIdeal Φ hΦ hΦs a M} (hq : q ∈ depthSubmodule Φ hΦ hΦs a M n) :
    envelopingι c a (HahnSeries.single m 1 ⊗ₜ x) • q ∈
      depthSubmodule Φ hΦ hΦs a M (n + (M - m)) := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨l, hl, hln, rfl⟩ := hq
    refine Submodule.subset_span ⟨(m, x) :: l, ?_, ?_, ?_⟩
    · simpa [hm] using hl
    · simp only [List.map_cons, List.sum_cons]
      omega
    · rw [← Submodule.Quotient.mk_smul, smul_eq_mul, List.map_cons, List.prod_cons]
  | zero => simp
  | add q q' _ _ hq hq' => simpa only [smul_add] using add_mem hq hq'
  | smul r q _ hq => simpa only [smul_algebra_smul_comm] using Submodule.smul_mem _ r hq

/-- **A polynomial current of order below `M` and at least `M - w` raises the depth by `w`.** -/
theorem envelopingι_smul_mem_depthSubmodule_add {M n w : ℤ} {u : C}
    (hu : u ∈ truncSubmodule R L M) (hu' : u ∈ orderSubmodule R L (M - w))
    {q : U ⧸ orderLeftIdeal Φ hΦ hΦs a M} (hq : q ∈ depthSubmodule Φ hΦ hΦs a M n) :
    envelopingι c a u • q ∈ depthSubmodule Φ hΦ hΦs a M (n + w) := by
  have hu'' : u ∈ truncSubmodule R L M ⊓ orderSubmodule R L (M - w) :=
    Submodule.mem_inf.mpr ⟨hu, hu'⟩
  rw [truncSubmodule_inf_orderSubmodule] at hu''
  clear hu hu'
  induction hu'' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨m, hm, hmM, x, rfl⟩ := hu
    exact depthSubmodule_mono Φ hΦ hΦs a M (by omega)
      (envelopingι_single_smul_mem_depthSubmodule hmM x hq)
  | zero => simp
  | add u v _ _ hu hv => simpa only [map_add, add_smul] using add_mem hu hv
  | smul r u _ hu => simpa only [map_smul, smul_assoc] using Submodule.smul_mem _ r hu

/-- The lowering estimate on a single word, by induction on its length. -/
private theorem envelopingι_smul_mk_list_prod_mem {M : ℤ} (hM : 0 ≤ M) (l : List (ℤ × L))
    (hl : ∀ p ∈ l, p.1 < M) {N n : ℤ} {u : C} (hN : M ≤ N) (hu : u ∈ orderSubmodule R L N)
    (hn : (l.map fun p ↦ M - p.1).sum ≤ n) :
    envelopingι c a u • Submodule.Quotient.mk (p := orderLeftIdeal Φ hΦ hΦs a M)
        (l.map fun p ↦ envelopingι c a (HahnSeries.single p.1 1 ⊗ₜ p.2)).prod ∈
      depthSubmodule Φ hΦ hΦs a M (n - N) := by
  induction l generalizing N n u with
  | nil =>
    rw [List.map_nil, List.prod_nil, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
      (Submodule.Quotient.mk_eq_zero _).mpr
        (envelopingι_mem_orderLeftIdeal (orderSubmodule_antitone R L hN hu))]
    exact zero_mem _
  | cons p l ih =>
    obtain ⟨m, x⟩ := p
    have hmM : m < M := hl _ List.mem_cons_self
    have hl' : ∀ p ∈ l, p.1 < M := fun p hp ↦ hl p (List.mem_cons_of_mem _ hp)
    have hs : M - m + (l.map fun p ↦ M - p.1).sum ≤ n := by simpa using hn
    have hy : HahnSeries.single m (1 : R) ⊗ₜ[R] x ∈ orderSubmodule R L m :=
      single_tmul_mem_orderSubmodule R L le_rfl 1 x
    have huy := lie_mem_orderSubmodule R L hu hy
    -- Commute `u` past the first letter `y = x_m`: `u y = y u + ⁅u, y⁆ + a Res(u dy)`.
    have hcomm :=
      envelopingι_mul_sub_mul_residuePairing Φ hΦ hΦs a u (HahnSeries.single m 1 ⊗ₜ x)
    rw [sub_eq_iff_eq_add'] at hcomm
    rw [List.map_cons, List.prod_cons, ← smul_eq_mul, Submodule.Quotient.mk_smul, ← mul_smul,
      hcomm, add_smul, add_smul, mul_smul, algebraMap_smul]
    refine add_mem ?_ (add_mem ?_ ?_)
    · exact depthSubmodule_mono Φ hΦ hΦs a M (by omega)
        (envelopingι_single_smul_mem_depthSubmodule hmM x (ih hl' hN hu le_rfl))
    · by_cases hNm : M ≤ N + m
      · exact depthSubmodule_mono Φ hΦ hΦs a M (by omega) (ih hl' hNm huy le_rfl)
      -- Otherwise split the commutator into its part below order `M` and the rest.
      set t := ofLoop R L (trunc R L M ⁅u, HahnSeries.single m 1 ⊗ₜ x⁆)
      have ht : t ∈ orderSubmodule R L (M - (M - (N + m))) := by
        rw [sub_sub_cancel]
        exact ofLoop_trunc_mem_orderSubmodule R L M huy
      rw [← sub_sub_cancel t ⁅u, _⁆, map_sub, sub_smul]
      have htW := envelopingι_smul_mem_depthSubmodule_add
        (ofLoop_trunc_mem_truncSubmodule R L M _) ht
        (mk_list_prod_mem_depthSubmodule (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a) hl' le_rfl)
      exact sub_mem (depthSubmodule_mono Φ hΦ hΦs a M (by omega) htW)
        (depthSubmodule_mono Φ hΦ hΦs a M (by omega)
          (ih hl' le_rfl (ofLoop_trunc_sub_mem_orderSubmodule R L M _) le_rfl))
    · by_cases hpos : 0 < N + m
      · rw [residuePairing_eq_zero_of_mem_orderSubmodule R L Φ hu hy hpos, mul_zero, zero_smul]
        exact zero_mem _
      · exact Submodule.smul_mem _ _ (depthSubmodule_mono Φ hΦ hΦs a M (by omega)
          (mk_list_prod_mem_depthSubmodule hl' le_rfl))

/-- **Currents of order at least `N` lower the depth by `N`**, when `0 ≤ M ≤ N`. -/
theorem envelopingι_smul_mem_depthSubmodule_sub {M N n : ℤ} (hM : 0 ≤ M) (hN : M ≤ N) {u : C}
    (hu : u ∈ orderSubmodule R L N) {q : U ⧸ orderLeftIdeal Φ hΦ hΦs a M}
    (hq : q ∈ depthSubmodule Φ hΦ hΦs a M n) :
    envelopingι c a u • q ∈ depthSubmodule Φ hΦ hΦs a M (n - N) := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨l, hl, hln, rfl⟩ := hq
    exact envelopingι_smul_mk_list_prod_mem hM l hl hN hu hln
  | zero => simp
  | add q q' _ _ hq hq' => simpa only [smul_add] using add_mem hq hq'
  | smul r q _ hq => simpa only [smul_algebra_smul_comm] using Submodule.smul_mem _ r hq

/-- **The depth submodules are stable** under the currents of order at least `M ≥ 0`. -/
theorem envelopingι_smul_mem_depthSubmodule {M n : ℤ} (hM : 0 ≤ M) {u : C}
    (hu : u ∈ orderSubmodule R L M) {q : U ⧸ orderLeftIdeal Φ hΦ hΦs a M}
    (hq : q ∈ depthSubmodule Φ hΦ hΦs a M n) :
    envelopingι c a u • q ∈ depthSubmodule Φ hΦ hΦs a M n :=
  depthSubmodule_mono Φ hΦ hΦs a M (by omega)
    (envelopingι_smul_mem_depthSubmodule_sub hM le_rfl hu hq)

/-- **The finite-jet estimate.** For `0 ≤ M ≤ N` and `n < N`, the currents of order at least `N`
kill the depth-`n` submodule. -/
theorem envelopingι_smul_eq_zero_of_mem_depthSubmodule {M N n : ℤ} (hM : 0 ≤ M) (hN : M ≤ N)
    (hn : n < N) {u : C} (hu : u ∈ orderSubmodule R L N) {q : U ⧸ orderLeftIdeal Φ hΦ hΦs a M}
    (hq : q ∈ depthSubmodule Φ hΦ hΦs a M n) : envelopingι c a u • q = 0 := by
  have h := envelopingι_smul_mem_depthSubmodule_sub hM hN hu hq
  rwa [depthSubmodule_eq_bot (by omega), Submodule.mem_bot] at h

/-- A product of `k` currents of order at least `M ≥ 0` lowers the depth by `k M`. -/
theorem list_prod_smul_mem_depthSubmodule {M n : ℤ} (hM : 0 ≤ M) {us : List C}
    (hus : ∀ u ∈ us, u ∈ orderSubmodule R L M) {q : U ⧸ orderLeftIdeal Φ hΦ hΦs a M}
    (hq : q ∈ depthSubmodule Φ hΦ hΦs a M n) :
    (us.map (envelopingι c a)).prod • q ∈ depthSubmodule Φ hΦ hΦs a M (n - us.length * M) := by
  induction us with
  | nil => simpa using hq
  | cons u us ih =>
    rw [List.map_cons, List.prod_cons, mul_smul]
    refine depthSubmodule_mono Φ hΦ hΦs a M (le_of_eq ?_)
      (envelopingι_smul_mem_depthSubmodule_sub hM le_rfl (hus u List.mem_cons_self)
        (ih fun v hv ↦ hus v (List.mem_cons_of_mem _ hv)))
    push_cast [List.length_cons]
    ring

/-- **Nilpotence on a depth submodule.** A product of `k` currents of order at least `M ≥ 0` with
`n < k M` kills the depth-`n` submodule. -/
theorem list_prod_smul_eq_zero_of_mem_depthSubmodule {M n : ℤ} (hM : 0 ≤ M) {us : List C}
    (hus : ∀ u ∈ us, u ∈ orderSubmodule R L M) (hn : n < us.length * M)
    {q : U ⧸ orderLeftIdeal Φ hΦ hΦs a M} (hq : q ∈ depthSubmodule Φ hΦ hΦs a M n) :
    (us.map (envelopingι c a)).prod • q = 0 := by
  have h := list_prod_smul_mem_depthSubmodule hM hus hq
  rwa [depthSubmodule_eq_bot (by omega), Submodule.mem_bot] at h

/-- Every current raises the depth by a bounded amount, when `M ≥ 0`. -/
theorem exists_forall_envelopingι_smul_mem_depthSubmodule {M : ℤ} (hM : 0 ≤ M) (u : C) :
    ∃ w : ℤ, ∀ (n : ℤ) (q : U ⧸ orderLeftIdeal Φ hΦ hΦs a M),
      q ∈ depthSubmodule Φ hΦ hΦs a M n →
        envelopingι c a u • q ∈ depthSubmodule Φ hΦ hΦs a M (n + w) := by
  obtain ⟨P, hP⟩ := exists_mem_orderSubmodule R L u
  have hP' : u ∈ orderSubmodule R L (M - (M - min P M)) := by
    rw [sub_sub_cancel]
    exact orderSubmodule_antitone R L (min_le_left P M) hP
  refine ⟨M - min P M, fun n q hq ↦ ?_⟩
  -- Split `u` into its part below order `M` and a current of order at least `M`.
  rw [← add_sub_cancel (ofLoop R L (trunc R L M u)) u, map_add, add_smul]
  refine add_mem (envelopingι_smul_mem_depthSubmodule_add (ofLoop_trunc_mem_truncSubmodule R L M u)
    (ofLoop_trunc_mem_orderSubmodule R L M hP') hq) ?_
  exact depthSubmodule_mono Φ hΦ hΦs a M (by omega)
    (envelopingι_smul_mem_depthSubmodule hM (sub_ofLoop_trunc_mem_orderSubmodule R L M u) hq)

/-- **The depth submodules exhaust the congruence quotient** `U / I_M` when `M ≥ 0`. -/
theorem exists_mem_depthSubmodule {M : ℤ} (hM : 0 ≤ M) (q : U ⧸ orderLeftIdeal Φ hΦ hΦs a M) :
    ∃ n : ℤ, q ∈ depthSubmodule Φ hΦ hΦs a M n := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  -- The elements raising the depth by a bounded amount form a subalgebra containing the currents.
  suffices h : ∀ b : U, ∃ w : ℤ, ∀ (n : ℤ) (q : U ⧸ orderLeftIdeal Φ hΦ hΦs a M),
      q ∈ depthSubmodule Φ hΦ hΦs a M n → b • q ∈ depthSubmodule Φ hΦ hΦs a M (n + w) by
    obtain ⟨w, hw⟩ := h b
    refine ⟨0 + w, ?_⟩
    simpa only [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one] using
      hw 0 _ (mk_one_mem_depthSubmodule le_rfl)
  intro b
  have hb : b ∈ Algebra.adjoin R (Set.range (envelopingι c a)) := by
    rw [adjoin_range_envelopingι]
    trivial
  induction hb using Algebra.adjoin_induction with
  | mem b hb =>
    obtain ⟨u, rfl⟩ := hb
    exact exists_forall_envelopingι_smul_mem_depthSubmodule hM u
  | algebraMap r =>
    refine ⟨0, fun n q hq ↦ ?_⟩
    rw [algebraMap_smul, add_zero]
    exact Submodule.smul_mem _ r hq
  | add b b' _ _ hb hb' =>
    obtain ⟨w, hw⟩ := hb
    obtain ⟨w', hw'⟩ := hb'
    refine ⟨max w w', fun n q hq ↦ ?_⟩
    rw [add_smul]
    exact add_mem (depthSubmodule_mono Φ hΦ hΦs a M (by omega) (hw n q hq))
      (depthSubmodule_mono Φ hΦ hΦs a M (by omega) (hw' n q hq))
  | mul b b' _ _ hb hb' =>
    obtain ⟨w, hw⟩ := hb
    obtain ⟨w', hw'⟩ := hb'
    refine ⟨w + w', fun n q hq ↦ ?_⟩
    rw [mul_smul]
    exact depthSubmodule_mono Φ hΦ hΦs a M (by omega) (hw _ _ (hw' n q hq))

/-- The depth-`n` submodule is spanned by the class of `1` and the images of the depth-`(n - d)`
submodules under the modes of depth `d ≤ n`. -/
private theorem depthSubmodule_eq_sup_iSup {M n : ℤ} (hn : 0 ≤ n) :
    depthSubmodule Φ hΦ hΦs a M n =
      (R ∙ Submodule.Quotient.mk 1) ⊔ ⨆ m ∈ Finset.Ico (M - n) M, Submodule.map₂
        ((Algebra.lsmul R R (U ⧸ orderLeftIdeal Φ hΦ hΦs a M)).toLinearMap ∘ₗ
          envelopingι c a ∘ₗ TensorProduct.mk R R⸨X⸩ L (HahnSeries.single m 1))
        ⊤ (depthSubmodule Φ hΦ hΦs a M (n - (M - m))) := by
  refine le_antisymm (Submodule.span_le.mpr ?_)
    (sup_le (Submodule.span_singleton_le_iff_mem _ _ |>.mpr (mk_one_mem_depthSubmodule hn))
      (iSup₂_le fun m hm ↦ Submodule.map₂_le.mpr fun x _ q hq ↦ ?_))
  · rintro _ ⟨l, hl, hln, rfl⟩
    cases l with
    | nil => exact Submodule.mem_sup_left (by simp)
    | cons p l =>
      obtain ⟨m, x⟩ := p
      have hmM : m < M := hl _ List.mem_cons_self
      have hl' : ∀ p ∈ l, p.1 < M := fun p hp ↦ hl p (List.mem_cons_of_mem _ hp)
      have hs : M - m + (l.map fun p ↦ M - p.1).sum ≤ n := by simpa using hln
      have hs' := sum_depth_nonneg hl'
      refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem m (Submodule.mem_iSup_of_mem
        (Finset.mem_Ico.mpr ⟨by omega, hmM⟩) ?_))
      have h := Submodule.apply_mem_map₂
        ((Algebra.lsmul R R (U ⧸ orderLeftIdeal Φ hΦ hΦs a M)).toLinearMap ∘ₗ
          envelopingι c a ∘ₗ TensorProduct.mk R R⸨X⸩ L (HahnSeries.single m 1))
        (Submodule.mem_top (x := x))
        (mk_list_prod_mem_depthSubmodule (n := n - (M - m)) hl' (by omega))
      simpa only [List.map_cons, List.prod_cons, LinearMap.coe_comp, AlgHom.coe_toLinearMap,
        Function.comp_apply, TensorProduct.mk_apply, Algebra.lsmul_coe,
        ← Submodule.Quotient.mk_smul, smul_eq_mul] using h
  · have hm := Finset.mem_Ico.mp hm
    simpa only [LinearMap.coe_comp, AlgHom.coe_toLinearMap, Function.comp_apply,
      TensorProduct.mk_apply, Algebra.lsmul_coe] using depthSubmodule_mono Φ hΦ hΦs a M (by omega)
        (envelopingι_single_smul_mem_depthSubmodule hm.2 x hq)

variable (Φ hΦ hΦs a) in
/-- **The depth submodules are finitely generated** when `L` is a finite `R`-module; over a field,
they are finite-dimensional. -/
theorem depthSubmodule_fg [Module.Finite R L] (M n : ℤ) :
    (depthSubmodule Φ hΦ hΦs a M n).FG := by
  induction h : n.toNat using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  rcases lt_or_ge n 0 with hn | hn
  · rw [depthSubmodule_eq_bot hn]
    exact Submodule.fg_bot
  rw [depthSubmodule_eq_sup_iSup hn]
  refine (Submodule.fg_span_singleton _).sup (Submodule.fg_biSup _ _ fun m hm ↦
    Module.Finite.fg_top.map₂ _ (ih _ ?_ _ rfl))
  have := Finset.mem_Ico.mp hm
  omega

/-- **Every vector of a positive congruence quotient lies in a finite jet-nilpotent submodule.**
For `M > 0` and `L` a finite `R`-module, every vector of `U / I_M` lies in a finitely generated
`R`-submodule `W` which is stable under the currents of order at least `M`, and for some `N` is
killed by the currents of order at least `N` and by every product of `N` currents of order at
least `M`. -/
theorem exists_mem_fg_submodule_jet_nilpotent {M : ℤ} (hM : 0 < M) [Module.Finite R L]
    (q : U ⧸ orderLeftIdeal Φ hΦ hΦs a M) :
    ∃ W : Submodule R (U ⧸ orderLeftIdeal Φ hΦ hΦs a M), q ∈ W ∧ W.FG ∧
      (∀ u ∈ orderSubmodule R L M, ∀ w ∈ W, envelopingι c a u • w ∈ W) ∧
      ∃ N : ℕ, (∀ u ∈ orderSubmodule R L N, ∀ w ∈ W, envelopingι c a u • w = 0) ∧
        ∀ us : List C, (∀ u ∈ us, u ∈ orderSubmodule R L M) → N ≤ us.length →
          ∀ w ∈ W, (us.map (envelopingι c a)).prod • w = 0 := by
  obtain ⟨n, hq⟩ := exists_mem_depthSubmodule hM.le q
  have hN : ((max M (n + 1)).toNat : ℤ) = max M (n + 1) := Int.toNat_of_nonneg (by omega)
  refine ⟨_, hq, depthSubmodule_fg Φ hΦ hΦs a M n,
    fun u hu w hw ↦ envelopingι_smul_mem_depthSubmodule hM.le hu hw, (max M (n + 1)).toNat,
    fun u hu w hw ↦ envelopingι_smul_eq_zero_of_mem_depthSubmodule hM.le (by omega) (by omega)
      (hN ▸ hu) hw, fun us hus hlen w hw ↦
      list_prod_smul_eq_zero_of_mem_depthSubmodule hM.le hus ?_ hw⟩
  have hle : (us.length : ℤ) ≤ us.length * M := le_mul_of_one_le_right (by omega) (by omega)
  omega

end TauCeti.CurrentAlgebra

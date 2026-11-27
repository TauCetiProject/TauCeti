/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.Ring.Basic
public import TauCeti.RingTheory.Ideal.Maps
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Algebra.Group.ContinuousDiv

/-!
# Profinite rings, through ultralimits of sequences

A commutative ring `R` is *profinite* (`TauCeti.IsProfiniteRing R`) if every sequence
`x : ℕ → R` has exactly one ultralimit for divisibility by nonzero integers along the fixed
non-principal ultrafilter `Filter.hyperfilter ℕ`: exactly one `L : R` such that, for every nonzero
`M : ℕ`, `(M : R) ∣ x N - L` for almost all `N`. This phrasing replaces the description of `R` as
the inverse limit of the finite rings `R ⧸ M R` by a limit operation on arbitrary sequences, which
is how it is used: a statement proved over the finite quotients `R ⧸ N! R` passes to `R` by taking
the ultralimit of lifts of solutions, and the solutions over the quotients need not be compatible.

The main results are:

* `TauCeti.isProfiniteRing_iff`: `R` is profinite if and only if every sequence has an ultralimit
  and only `0` is divisible by every nonzero integer.
* `TauCeti.IsProfiniteRing.finite_quotient`: the quotients `R ⧸ M R`, `M ≠ 0`, are finite.
* `TauCeti.IsProfiniteRing.ultralim`: the ultralimit of a sequence, with its characterization
  (`dvd_sub_ultralim`, `ultralim_eq`) and its compatibility with sums, products and ring
  homomorphisms.
* `TauCeti.IsProfiniteRing.ultralimRingHom`: the ring homomorphism from the product of the
  quotients `R ⧸ N! R` to `R` that takes the ultralimit of lifts. It retracts the diagonal map
  (`ultralimRingHom_mk`), commutes with every ring homomorphism between profinite rings
  (`RingHom.map_ultralimRingHom`), and preserves divisibility by elements of `R`
  (`dvd_ultralimRingHom`).
* `TauCeti.IsProfiniteRing.of_compactSpace`: a compact topological ring in which the ideals `M R`,
  `M ≠ 0`, are neighbourhoods of `0` and have intersection `0` is profinite. Finite rings and the
  `p`-adic integers `ℤ_[p]` are profinite, the latter in
  `TauCeti.NumberTheory.Padics.PadicIntegers`.
-/

public section

open Filter Topology

namespace TauCeti

/-- A commutative ring `R` is **profinite** if every sequence `x : ℕ → R` has exactly one
ultralimit for divisibility by nonzero integers along `Filter.hyperfilter ℕ`: exactly one `L : R`
such that, for every nonzero `M : ℕ`, `(M : R) ∣ x N - L` for `hyperfilter`-almost all `N`. -/
class IsProfiniteRing (R : Type*) [CommRing R] : Prop where
  /-- Every sequence has exactly one ultralimit. -/
  existsUnique_ultralim (x : ℕ → R) :
    ∃! L : R, ∀ M : ℕ, M ≠ 0 → ∀ᶠ N in (hyperfilter ℕ : Filter ℕ), (M : R) ∣ x N - L

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring is profinite if and only if every sequence has an ultralimit for divisibility by
nonzero integers, and only `0` is divisible by every nonzero integer. -/
theorem isProfiniteRing_iff :
    IsProfiniteRing R ↔
      (∀ x : ℕ → R, ∃ L : R, ∀ M : ℕ, M ≠ 0 →
        ∀ᶠ N in (hyperfilter ℕ : Filter ℕ), (M : R) ∣ x N - L) ∧
      ∀ z : R, (∀ M : ℕ, M ≠ 0 → (M : R) ∣ z) → z = 0 := by
  refine ⟨fun h ↦ ⟨fun x ↦ (h.existsUnique_ultralim x).exists, fun z hz ↦ ?_⟩,
    fun ⟨hex, hsep⟩ ↦ ⟨fun x ↦ ?_⟩⟩
  · obtain ⟨L, -, hL⟩ := h.existsUnique_ultralim fun _ ↦ 0
    have h0 : (0 : R) = L := hL 0 fun M _ ↦ .of_forall fun _ ↦ by simp
    have hz' : -z = L := hL (-z) fun M hM ↦ .of_forall fun _ ↦ by simpa using hz M hM
    exact neg_eq_zero.mp (hz'.trans h0.symm)
  · obtain ⟨L, hL⟩ := hex x
    refine ⟨L, hL, fun L' hL' ↦ sub_eq_zero.mp (hsep _ fun M hM ↦ ?_)⟩
    obtain ⟨N, hN, hN'⟩ := ((hL M hM).and (hL' M hM)).exists
    simpa using dvd_sub hN hN'

namespace IsProfiniteRing

/-- In a profinite ring, only `0` is divisible by every nonzero integer. -/
theorem eq_zero_of_forall_dvd [IsProfiniteRing R] {z : R} (h : ∀ M : ℕ, M ≠ 0 → (M : R) ∣ z) :
    z = 0 :=
  (isProfiniteRing_iff.mp ‹_›).2 z h

/-- In a profinite ring, two elements congruent modulo every nonzero integer are equal. -/
theorem eq_of_forall_dvd_sub [IsProfiniteRing R] {a b : R}
    (h : ∀ M : ℕ, M ≠ 0 → (M : R) ∣ a - b) : a = b :=
  sub_eq_zero.mp (eq_zero_of_forall_dvd h)

/-- The quotients of a profinite ring by nonzero integers are finite. -/
theorem finite_quotient [IsProfiniteRing R] {M : ℕ} (hM : M ≠ 0) :
    Finite (R ⧸ Ideal.span {(M : R)}) := by
  by_contra h
  rw [not_finite_iff_infinite] at h
  let f := Infinite.natEmbedding (R ⧸ Ideal.span {(M : R)})
  let x : ℕ → R := fun N ↦ Function.surjInv Ideal.Quotient.mk_surjective (f N)
  obtain ⟨L, hL, -⟩ := existsUnique_ultralim x
  refine notMem_hyperfilter_of_finite
    (Set.Subsingleton.finite (s := {N | f N = Ideal.Quotient.mk _ L})
      fun N₁ h₁ N₂ h₂ ↦ f.injective (h₁.trans h₂.symm))
    ((hL M hM).mono fun N hN ↦ Set.mem_ofPred.mpr ?_)
  rw [← Function.surjInv_eq Ideal.Quotient.mk_surjective (f N)]
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr hN)

/-- The **ultralimit** of a sequence in a profinite ring: the unique `L` such that, for every
nonzero `M : ℕ`, `(M : R) ∣ x N - L` for `hyperfilter`-almost all `N`. -/
noncomputable def ultralim [IsProfiniteRing R] (x : ℕ → R) : R :=
  (existsUnique_ultralim x).exists.choose

/-- Every nonzero integer divides `x N - ultralim x` for almost all `N`. -/
theorem dvd_sub_ultralim [IsProfiniteRing R] (x : ℕ → R) {M : ℕ} (hM : M ≠ 0) :
    ∀ᶠ N in (hyperfilter ℕ : Filter ℕ), (M : R) ∣ x N - ultralim x :=
  (existsUnique_ultralim x).exists.choose_spec M hM

/-- The ultralimit is characterized by `dvd_sub_ultralim`. -/
theorem ultralim_eq [IsProfiniteRing R] {x : ℕ → R} {L : R}
    (h : ∀ M : ℕ, M ≠ 0 → ∀ᶠ N in (hyperfilter ℕ : Filter ℕ), (M : R) ∣ x N - L) :
    ultralim x = L :=
  (existsUnique_ultralim x).unique (fun _ hM ↦ dvd_sub_ultralim x hM) h

/-- The ultralimit of a constant sequence is its value. -/
@[simp]
theorem ultralim_const [IsProfiniteRing R] (r : R) : ultralim (fun _ ↦ r) = r :=
  ultralim_eq fun _ _ ↦ .of_forall fun _ ↦ by simp

/-- The ultralimit of the zero sequence is zero. -/
@[simp]
theorem ultralim_zero [IsProfiniteRing R] : ultralim (0 : ℕ → R) = 0 :=
  ultralim_const 0

/-- The ultralimit of the constant sequence one is one. -/
@[simp]
theorem ultralim_one [IsProfiniteRing R] : ultralim (1 : ℕ → R) = 1 :=
  ultralim_const 1

/-- The ultralimit of a sum is the sum of the ultralimits. -/
@[simp]
theorem ultralim_add [IsProfiniteRing R] (x y : ℕ → R) :
    ultralim (x + y) = ultralim x + ultralim y :=
  ultralim_eq fun M hM ↦ by
    filter_upwards [dvd_sub_ultralim x hM, dvd_sub_ultralim y hM] with N hx hy
    convert dvd_add hx hy using 1
    simp only [Pi.add_apply]
    ring

/-- The ultralimit of a negated sequence is the negation of its ultralimit. -/
@[simp]
theorem ultralim_neg [IsProfiniteRing R] (x : ℕ → R) : ultralim (-x) = -ultralim x := by
  have h := ultralim_add (-x) x
  rw [neg_add_cancel, ultralim_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The ultralimit of a difference is the difference of the ultralimits. -/
@[simp]
theorem ultralim_sub [IsProfiniteRing R] (x y : ℕ → R) :
    ultralim (x - y) = ultralim x - ultralim y := by
  simp only [sub_eq_add_neg, ultralim_add, ultralim_neg]

/-- The ultralimit of a product is the product of the ultralimits. -/
@[simp]
theorem ultralim_mul [IsProfiniteRing R] (x y : ℕ → R) :
    ultralim (x * y) = ultralim x * ultralim y :=
  ultralim_eq fun M hM ↦ by
    filter_upwards [dvd_sub_ultralim x hM, dvd_sub_ultralim y hM] with N hx hy
    convert dvd_add (hx.mul_right (y N)) (hy.mul_left (ultralim x)) using 1
    simp only [Pi.mul_apply]
    ring

/-- Two sequences congruent modulo `N!` at every `N` have the same ultralimit. -/
theorem ultralim_congr [IsProfiniteRing R] {x y : ℕ → R}
    (h : ∀ N, (N.factorial : R) ∣ x N - y N) : ultralim x = ultralim y :=
  ultralim_eq fun M hM ↦ by
    filter_upwards [dvd_sub_ultralim y hM,
      (eventually_ge_atTop M).filter_mono Nat.hyperfilter_le_atTop] with N hy hN
    have hfac : (M : R) ∣ (N.factorial : R) :=
      Nat.cast_dvd_cast (Nat.dvd_factorial (Nat.pos_of_ne_zero hM) hN)
    have h_add := dvd_add (dvd_trans hfac (h N)) hy
    rwa [sub_add_sub_cancel] at h_add

/-- Ring homomorphisms between profinite rings commute with ultralimits. -/
theorem _root_.RingHom.map_ultralim [IsProfiniteRing R] [IsProfiniteRing S]
    (f : R →+* S) (x : ℕ → R) :
    f (ultralim x) = ultralim (f ∘ x) :=
  (ultralim_eq fun M hM ↦ (dvd_sub_ultralim x hM).mono fun N hN ↦ by
    simpa using map_dvd f hN).symm

/-- Lifts of the components of a family in the product of the quotients `R ⧸ N! R` have the same
ultralimit as any other family of lifts. -/
private theorem ultralim_surjInv_eq [IsProfiniteRing R]
    (a : ∀ N : ℕ, R ⧸ Ideal.span {(N.factorial : R)}) {y : ℕ → R}
    (hy : ∀ N, Ideal.Quotient.mk _ (y N) = a N) :
    ultralim (fun N ↦ Function.surjInv Ideal.Quotient.mk_surjective (a N)) = ultralim y :=
  ultralim_congr fun N ↦ Ideal.mem_span_singleton.mp <| Ideal.Quotient.eq.mp <| by
    rw [Function.surjInv_eq Ideal.Quotient.mk_surjective, hy]

/-- The ring homomorphism from the product of the quotients `R ⧸ N! R` to a profinite ring `R`
that sends a family to the ultralimit of lifts of its components. -/
noncomputable def ultralimRingHom [IsProfiniteRing R] :
    (∀ N : ℕ, R ⧸ Ideal.span {(N.factorial : R)}) →+* R where
  toFun a := ultralim fun N ↦ Function.surjInv Ideal.Quotient.mk_surjective (a N)
  map_one' := (ultralim_surjInv_eq 1 (y := fun _ ↦ 1) fun _ ↦ map_one _).trans (ultralim_const 1)
  map_mul' a b := by
    rw [← ultralim_mul]
    exact ultralim_surjInv_eq _ fun N ↦ by simp [Function.surjInv_eq Ideal.Quotient.mk_surjective]
  map_zero' := (ultralim_surjInv_eq 0 (y := fun _ ↦ 0) fun _ ↦ map_zero _).trans (ultralim_const 0)
  map_add' a b := by
    rw [← ultralim_add]
    exact ultralim_surjInv_eq _ fun N ↦ by simp [Function.surjInv_eq Ideal.Quotient.mk_surjective]

/-- `ultralimRingHom` takes the ultralimit of any family of lifts. -/
theorem ultralimRingHom_eq_ultralim [IsProfiniteRing R]
    (a : ∀ N : ℕ, R ⧸ Ideal.span {(N.factorial : R)}) {y : ℕ → R}
    (hy : ∀ N, Ideal.Quotient.mk _ (y N) = a N) : ultralimRingHom a = ultralim y :=
  ultralim_surjInv_eq a hy

/-- `ultralimRingHom` retracts the diagonal map to the product of the quotients `R ⧸ N! R`. -/
@[simp]
theorem ultralimRingHom_mk [IsProfiniteRing R] (r : R) :
    ultralimRingHom (fun N ↦ Ideal.Quotient.mk (Ideal.span {(N.factorial : R)}) r) = r :=
  (ultralimRingHom_eq_ultralim _ fun _ ↦ rfl).trans (ultralim_const r)

/-- An element dividing every component of a family in the product of the quotients `R ⧸ N! R`
divides its image under `ultralimRingHom`. -/
theorem dvd_ultralimRingHom [IsProfiniteRing R] {r : R}
    {a : ∀ N : ℕ, R ⧸ Ideal.span {(N.factorial : R)}} (h : ∀ N, Ideal.Quotient.mk _ r ∣ a N) :
    r ∣ ultralimRingHom a := by
  choose b hb using h
  refine ⟨ultralimRingHom b, ?_⟩
  rw [← ultralimRingHom_mk r, ← map_mul]
  exact congrArg ultralimRingHom (funext hb)

/-- The unit obtained by applying `ultralimRingHom` to a family of units in the quotients
`R ⧸ N! R`. -/
noncomputable def ultralimUnitsHom [IsProfiniteRing R] :
    (∀ N : ℕ, (R ⧸ Ideal.span {(N.factorial : R)})ˣ) →* Rˣ :=
  (Units.map (ultralimRingHom (R := R)).toMonoidHom).comp (MulEquiv.piUnits.symm).toMonoidHom

/-- The value of a glued unit is the image of its component values under `ultralimRingHom`. -/
@[simp]
theorem coe_ultralimUnitsHom [IsProfiniteRing R]
    (g : ∀ N : ℕ, (R ⧸ Ideal.span {(N.factorial : R)})ˣ) :
    (ultralimUnitsHom g : R) =
      ultralimRingHom (fun N ↦ (g N : R ⧸ Ideal.span {(N.factorial : R)})) := by
  simp [ultralimUnitsHom, MulEquiv.piUnits]

/-- Units congruent to `1` at a common level glue to a unit congruent to `1` at that level. -/
theorem dvd_ultralimUnitsHom_sub_one [IsProfiniteRing R] {m : R}
    {g : ∀ N : ℕ, (R ⧸ Ideal.span {(N.factorial : R)})ˣ}
    (h : ∀ N, Ideal.Quotient.mk _ m ∣ (g N : R ⧸ Ideal.span {(N.factorial : R)}) - 1) :
    m ∣ (ultralimUnitsHom g : R) - 1 := by
  rw [coe_ultralimUnitsHom, ← map_one (ultralimRingHom (R := R)), ← map_sub]
  exact dvd_ultralimRingHom h

/-- A ring homomorphism between profinite rings commutes with `ultralimRingHom`, acting on the
product of the quotients componentwise. -/
theorem _root_.RingHom.map_ultralimRingHom [IsProfiniteRing R] [IsProfiniteRing S] (f : R →+* S)
    (a : ∀ N : ℕ, R ⧸ Ideal.span {(N.factorial : R)}) :
    f (ultralimRingHom a) = ultralimRingHom fun N ↦
      Ideal.quotientMap _ f Ideal.span_natCast_le_comap (a N) := by
  rw [ultralimRingHom_eq_ultralim a fun N ↦ Function.surjInv_eq Ideal.Quotient.mk_surjective (a N),
    RingHom.map_ultralim, ultralimRingHom_eq_ultralim]
  intro N
  conv_rhs => rw [← Function.surjInv_eq Ideal.Quotient.mk_surjective (a N)]
  rw [Function.comp_apply, Ideal.quotientMap_mk]

/-- Iterates of a ring endomorphism commute with `ultralimRingHom`, acting on the factorial
quotients componentwise. -/
theorem _root_.RingHom.iterate_ultralimRingHom [IsProfiniteRing R] (σ : R →+* R) (i : ℕ)
    (a : ∀ N : ℕ, R ⧸ Ideal.span {(N.factorial : R)}) :
    σ^[i] (ultralimRingHom a) = ultralimRingHom fun N ↦
      (Ideal.quotientMap _ σ Ideal.span_natCast_le_comap)^[i] (a N) := by
  induction i generalizing a with
  | zero => rfl
  | succ i ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, RingHom.map_ultralimRingHom]

/-- A compact topological ring in which the ideals `M R`, `M ≠ 0`, are neighbourhoods of `0` and
only `0` is divisible by every nonzero integer is profinite. -/
theorem of_compactSpace [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
    (h_nhds : ∀ M : ℕ, M ≠ 0 → (Ideal.span {(M : R)} : Set R) ∈ 𝓝 0)
    (h_sep : ∀ z : R, (∀ M : ℕ, M ≠ 0 → (M : R) ∣ z) → z = 0) : IsProfiniteRing R := by
  refine isProfiniteRing_iff.mpr ⟨fun x ↦ ?_, h_sep⟩
  obtain ⟨L, -, hL⟩ :=
    isCompact_univ.ultrafilter_le_nhds (Ultrafilter.map x (hyperfilter ℕ)) (by simp)
  refine ⟨L, fun M hM ↦ ?_⟩
  have h_mem : {y : R | (M : R) ∣ y - L} ∈ 𝓝 L := by
    have h_tendsto : Tendsto (· - L) (𝓝 L) (𝓝 0) := by
      simpa using (continuous_sub_right L).tendsto L
    exact mem_of_superset (h_tendsto (h_nhds M hM)) fun y hy ↦ Ideal.mem_span_singleton.mp hy
  exact Filter.mem_map.mp (hL h_mem)

/-- Every finite commutative ring is profinite. -/
instance of_finite [Finite R] : IsProfiniteRing R := by
  refine isProfiniteRing_iff.mpr ⟨fun x ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨L, hL⟩ := Ultrafilter.eq_pure_of_finite (Ultrafilter.map x (hyperfilter ℕ))
    have h_ev : ∀ᶠ N in (hyperfilter ℕ : Filter ℕ), x N = L := by
      have : {L} ∈ Ultrafilter.map x (hyperfilter ℕ) := by simp [hL]
      exact Filter.mem_map.mp this
    exact ⟨L, fun M _ ↦ h_ev.mono fun N hN ↦ by simp [hN]⟩
  · have := Fintype.ofFinite R
    have h_card : ((Fintype.card R : ℕ) : R) = 0 := by simp
    simpa [h_card] using hz (Fintype.card R) Fintype.card_ne_zero

end IsProfiniteRing

end TauCeti

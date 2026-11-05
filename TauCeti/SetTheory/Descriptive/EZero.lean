/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Topology.Baire.BaireMeasurable
public import TauCeti.SetTheory.Descriptive.BorelReducibility
public import TauCeti.Topology.Instances.CantorSpace
import Mathlib.Topology.Baire.LocallyCompactRegular
import TauCeti.SetTheory.Descriptive.GenericErgodicity
import TauCeti.Topology.Baire.KuratowskiUlam
import TauCeti.Topology.Baire.Perfect
import TauCeti.Topology.Perfect

/-!
# The equivalence relation `E₀`

`E₀` is eventual equality on Cantor space `ℕ → Bool`: two sequences are `E₀`-equivalent when they
agree from some index on, that is, when they differ at only finitely many coordinates. It is
Mathlib's germ relation `Filter.germSetoid atTop Bool`, so its quotient is the type of germs
`Filter.Germ atTop Bool`.

`E₀` is the basic example of a Borel equivalence relation that is not smooth: its classes cannot
be separated by countably many invariant Borel sets. This file proves the facts about `E₀` that
make this so and that Borel reducibility arguments use:

* the graph of `E₀` is Borel, every class is countable and dense, and the graph is meagre in the
  square;
* **generic ergodicity**: an `E₀`-invariant set with the Baire property is meagre or comeagre. If
  such a set is comeagre in the cylinder of a word `s ++ [b]`, the coordinate flip at `s.length`,
  which changes a point only at one coordinate and so preserves the set, shows that it is comeagre
  in the cylinder of `s ++ [!b]`, hence in the cylinder of `s`. Shortening the word one letter at
  a time, it is comeagre;
* the quotient `Quotient E₀`, with Mathlib's quotient σ-algebra, is not countably separated:
  countably many invariant Borel sets are, by generic ergodicity, simultaneously constant on one
  comeagre set, which then lies in a single class, while classes are countable, hence meagre.
  So `E₀` is not smooth, and neither is any equivalence relation to which `E₀` is Borel reducible;
* the continuous map `x ↦ (n ↦ x (Nat.unpair n).1)` repeats each coordinate infinitely often, so
  it sends distinct points to `E₀`-inequivalent points; hence `E₀` has continuum many classes,
  and equality on Cantor space is Borel reducible to `E₀`. As `E₀` is not smooth, it lies strictly
  above equality on Cantor space in the Borel reducibility order.

## Main definitions

* `TauCeti.eZero`: eventual equality on `ℕ → Bool`.

## Main results

* `TauCeti.measurableSet_eZero`: the graph of `E₀` is Borel.
* `TauCeti.countable_setOf_eZero`, `TauCeti.dense_setOf_eZero`: every class is countable and
  dense.
* `TauCeti.isMeagre_eZero`: the graph of `E₀` is meagre in the square.
* `TauCeti.isMeagre_or_mem_residual_of_eZero_invariant`: generic ergodicity of `E₀`.
* `TauCeti.not_countablySeparated_quotient_eZero`: no countable family of invariant Borel sets
  separates the classes of `E₀`.
* `TauCeti.not_isSmooth_eZero`: `E₀` is not smooth, and
  `TauCeti.not_isSmooth_of_borelReducible_eZero`: nor is any relation above it.
* `TauCeti.hasCantorAntichainOn_eZero` and `TauCeti.mk_quotient_eZero`: a continuous Cantor
  antichain, and continuum many classes.
* `TauCeti.borelReducible_bot_eZero`: equality on Cantor space is Borel reducible to `E₀`.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Section 8.F (generic ergodicity of `E₀`).
* S. Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Section 6.1
  (`E₀` is not smooth).
-/

public section

open Cardinal Filter Set Topology PiNat

namespace TauCeti

/-- **Eventual equality** `E₀` on Cantor space: `x` and `y` are equivalent when `x n = y n` for
all sufficiently large `n`. It is Mathlib's germ relation along `atTop`. -/
def eZero : Setoid (ℕ → Bool) :=
  Filter.germSetoid atTop Bool

variable {x y : ℕ → Bool} {B : Set (ℕ → Bool)}

/-- Two points are `E₀`-equivalent iff they agree at all sufficiently large coordinates. -/
theorem eZero_iff : eZero x y ↔ ∀ᶠ n in atTop, x n = y n :=
  Iff.rfl

/-- On `ℕ`, eventually along `atTop` is eventually along the cofinite filter. -/
theorem eZero_iff_cofinite : eZero x y ↔ ∀ᶠ n in cofinite, x n = y n := by
  rw [eZero_iff, Nat.cofinite_eq_atTop]

/-- Two points are `E₀`-equivalent iff they differ at only finitely many coordinates. -/
theorem eZero_iff_finite : eZero x y ↔ {n | x n ≠ y n}.Finite := by
  rw [eZero_iff_cofinite, eventually_cofinite]

/-- A coordinate flip changes a point only at one coordinate. -/
theorem eZero_flipAt (n : ℕ) (x : ℕ → Bool) : eZero (flipAt n x) x :=
  eZero_iff.2 <| (eventually_gt_atTop n).mono fun _ hm => flipAt_apply_of_ne hm.ne' x

/-! ### Borelness and the classes of `E₀` -/

/-- The graph of `E₀` is Borel. -/
theorem measurableSet_eZero :
    MeasurableSet {p : (ℕ → Bool) × (ℕ → Bool) | eZero p.1 p.2} := by
  simp only [eZero_iff, eventually_atTop, ofPred_exists, ofPred_forall]
  exact .iUnion fun _ => .iInter fun n => .iInter fun _ =>
    measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_fst)
      ((measurable_pi_apply n).comp measurable_snd)

/-- Every class of `E₀` is countable: a point equivalent to `x` is `x` with the coordinates in a
finite set negated. -/
theorem countable_setOf_eZero (x : ℕ → Bool) : {y | eZero x y}.Countable := by
  refine (countable_range fun s : Finset ℕ => fun n => if n ∈ s then !x n else x n).mono ?_
  intro y hy
  refine ⟨(eZero_iff_finite.1 hy).toFinset, funext fun n => ?_⟩
  by_cases h : x n = y n <;> cases hx : x n <;> cases hy : y n <;> simp_all

/-- Every class of `E₀` is dense: a point `z` is the limit of the points that agree with `z` on
the first `N` coordinates and with `x` afterwards. -/
theorem dense_setOf_eZero (x : ℕ → Bool) : Dense {y | eZero x y} := by
  intro z
  refine mem_closure_of_tendsto (f := fun N n => if n < N then z n else x n)
    (b := atTop) (tendsto_pi_nhds.2 fun n => ?_) (Eventually.of_forall fun N => ?_)
  · exact tendsto_const_nhds.congr' <| (eventually_gt_atTop n).mono fun N hN => by simp [hN]
  · exact eZero_iff.2 <| (eventually_ge_atTop N).mono fun n hn => by simp [not_lt.2 hn]

/-- The graph of `E₀` is meagre in the square: it has the Baire property and its sections, the
classes, are countable, hence meagre (Kuratowski–Ulam). -/
theorem isMeagre_eZero : IsMeagre {p : (ℕ → Bool) × (ℕ → Bool) | eZero p.1 p.2} :=
  measurableSet_eZero.baireMeasurableSet.isMeagre_of_forall_isMeagre_curry_left fun x =>
    (countable_setOf_eZero x).isMeagre

/-! ### Generic ergodicity -/

/-- A point equivalent to a point of an `E₀`-invariant set lies in the set. -/
private theorem mem_of_eZero_invariant
    (hinv : Quotient.mk eZero ⁻¹' (Quotient.mk eZero '' B) = B) (hx : x ∈ B) (h : eZero x y) :
    y ∈ B :=
  hinv ▸ ⟨x, hx, Quotient.sound h⟩

/-- If an `E₀`-invariant set is comeagre in the cylinder of `s ++ [b]`, it is comeagre in the
cylinder of `s`: the coordinate flip at `s.length` carries the other half of the cylinder of `s`
onto the cylinder of `s ++ [b]` and preserves the set. -/
private theorem isMeagre_wordCylinder_diff_of_append
    (hinv : Quotient.mk eZero ⁻¹' (Quotient.mk eZero '' B) = B) (s : List Bool) (b : Bool)
    (h : IsMeagre (wordCylinder (s ++ [b]) \ B)) : IsMeagre (wordCylinder s \ B) := by
  refine (h.union (h.preimage_of_isOpenMap (flipAt s.length).continuous
    (flipAt s.length).isOpenMap)).mono ?_
  rintro y ⟨hy, hyB⟩
  rw [← iUnion_wordCylinder_append_singleton, mem_iUnion] at hy
  obtain ⟨c, hc⟩ := hy
  rcases Bool.eq_or_eq_not c b with rfl | rfl
  · exact .inl ⟨hc, hyB⟩
  · refine .inr ⟨?_, fun hfB => hyB (mem_of_eZero_invariant hinv hfB (eZero_flipAt _ y))⟩
    have := mem_image_of_mem (flipAt s.length) hc
    rwa [image_flipAt_wordCylinder_append_singleton, Bool.not_not] at this

/-- **Generic ergodicity of `E₀`.** An `E₀`-invariant set with the Baire property is meagre or
comeagre. -/
theorem isMeagre_or_mem_residual_of_eZero_invariant (hB : BaireMeasurableSet B)
    (hinv : Quotient.mk eZero ⁻¹' (Quotient.mk eZero '' B) = B) :
    IsMeagre B ∨ B ∈ residual (ℕ → Bool) := by
  obtain ⟨u, hu, hBu⟩ := hB.residualEq_isOpen
  rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact .inl <| mem_of_superset hBu.mem_iff fun y hy hyB => notMem_empty y (hy.1 hyB)
  refine .inr ?_
  -- `B` is comeagre in `u`, hence in a word cylinder inside `u`.
  obtain ⟨-, ⟨z, n, rfl⟩, -, hzu⟩ :=
    (isTopologicalBasis_cylinders fun _ : ℕ => Bool).exists_subset_of_mem_open hx hu
  have hw : IsMeagre (wordCylinder (res z n).reverse \ B) := by
    rw [wordCylinder_reverse_res]
    exact mem_of_superset hBu.mem_iff fun y hy hyuB => hyuB.2 (hy.2 (hzu hyuB.1))
  -- Shorten the word one letter at a time.
  suffices ∀ w : List Bool, IsMeagre (wordCylinder w \ B) → IsMeagre Bᶜ by
    simpa [IsMeagre] using this _ hw
  intro w
  induction w using List.reverseRecOn with
  | nil => simp [wordCylinder_nil, compl_eq_univ_sdiff]
  | append_singleton s b ih => exact fun h => ih (isMeagre_wordCylinder_diff_of_append hinv s b h)

/-- No countable family of `E₀`-invariant Borel sets separates the classes of `E₀`: the quotient
`Quotient eZero`, with Mathlib's quotient σ-algebra, is not countably separated. This is the
non-smoothness of `E₀`. -/
theorem not_countablySeparated_quotient_eZero :
    ¬ MeasurableSpace.CountablySeparated (Quotient eZero) :=
  eZero.not_countablySeparated_quotient_of_isMeagre_or_mem_residual
    (fun x => (countable_setOf_eZero x).isMeagre) fun s hs =>
      isMeagre_or_mem_residual_of_eZero_invariant
        (measurableSet_quotient.1 hs).baireMeasurableSet
        (by rw [image_preimage_eq s Quotient.mk_surjective])

/-- **`E₀` is not smooth**: no Borel map into Cantor space has the classes of `E₀` as its
fibres. -/
theorem not_isSmooth_eZero : ¬ eZero.IsSmooth :=
  Setoid.isSmooth_iff_countablySeparated.not.2 not_countablySeparated_quotient_eZero

/-- **The easy half of the Glimm–Effros dichotomy.** An equivalence relation to which `E₀` is
Borel reducible is not smooth. -/
theorem not_isSmooth_of_borelReducible_eZero {X : Type*} [MeasurableSpace X] {E : Setoid X}
    (h : eZero.BorelReducible E) : ¬ E.IsSmooth :=
  fun hE => not_isSmooth_eZero (h.isSmooth hE)

/-! ### A Cantor antichain -/

/-- `E₀` has a continuous **Cantor antichain**: the map `x ↦ (n ↦ x (Nat.unpair n).1)` repeats
each coordinate of `x` infinitely often, so distinct points have images that differ at infinitely
many coordinates. -/
theorem hasCantorAntichainOn_eZero : eZero.HasCantorAntichainOn univ := by
  refine Setoid.hasCantorAntichainOn_iff.2 ⟨fun x n => x (Nat.unpair n).1,
    continuous_pi fun _ => continuous_apply _, fun _ => mem_univ _,
    fun x y hxy h => hxy (funext fun m => ?_)⟩
  have ht : Tendsto (Nat.pair m) atTop atTop :=
    tendsto_atTop_mono (Nat.right_le_pair m) tendsto_id
  obtain ⟨k, hk⟩ := (ht.eventually (eZero_iff.1 h)).exists
  simpa using hk

/-- `E₀` has exactly continuum many classes. -/
theorem mk_quotient_eZero : #(Quotient eZero) = 𝔠 :=
  hasCantorAntichainOn_eZero.mk_quotient_eq_continuum

/-- Equality on Cantor space is Borel reducible to `E₀`, through its Cantor antichain. Since `E₀`
is not smooth (`TauCeti.not_isSmooth_eZero`), the converse reduction fails. -/
theorem borelReducible_bot_eZero : (⊥ : Setoid (ℕ → Bool)).BorelReducible eZero :=
  hasCantorAntichainOn_eZero.borelReducible_bot

end TauCeti

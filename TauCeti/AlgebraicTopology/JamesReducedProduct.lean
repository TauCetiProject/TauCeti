/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The James reduced product

For a pointed space `(X, x₀)`, the **James reduced product** `J X` is the space of finite words
`x₁ x₂ ⋯ xₙ` in the points of `X`, two words being identified when they agree after every
occurrence of the basepoint has been deleted. Concatenation of words makes it a monoid with the
empty word as unit, and as a monoid it is the free monoid on the points other than the basepoint
(`TauCeti.JamesReducedProduct.freeMonoidEquiv`). Its topology is the final topology of the maps
`Xⁿ → J X` sending a word of length `n` to its reduced word
(`TauCeti.JamesReducedProduct.mk`), for all `n`. For a connected CW complex `X`, James proved that
`J X` is a model for the loop space `ΩΣX` of the suspension; this is what makes it the basic tool
for computing the homology of loop spaces of suspensions and, through the word-length filtration,
for the EHP sequence and the James splitting.

This file sets up the construction for an arbitrary pointed topological space, with no separation
or connectivity hypothesis:

* the reduced word of a finite word, the letters `X → J X`, and the monoid structure;
* the universal property: a map `g : X → M` to a monoid with `g x₀ = 1` extends uniquely to a
  monoid homomorphism `J X →* M`, which is continuous when `g` is continuous and `M` is a
  topological monoid (`TauCeti.JamesReducedProduct.lift`);
* the quotient map from the words of all lengths, the characterization of continuous maps, open
  sets and closed sets out of `J X`, and the continuity of the letters and of the translations;
* the word-length filtration `J₀ X ⊆ J₁ X ⊆ ⋯`, where `J_r X` is the image of `Xʳ`; it is
  exhaustive, multiplicative, closed when the basepoint is closed, and compact when `X` is;
* the functoriality of `J` in based continuous maps, by continuous monoid homomorphisms that
  preserve the filtration;
* path-connectedness of `J X` for path-connected `X`.

Continuity of the multiplication `J X × J X → J X` for the product topology is not established
here; each left and right translation is continuous.

## Main definitions

* `TauCeti.JamesReducedProduct X x₀`: the James reduced product of `(X, x₀)`.
* `TauCeti.JamesReducedProduct.mk`: the reduced word `J X` of a word `v : Fin n → X`.
* `TauCeti.JamesReducedProduct.letter`: the one-letter words, the inclusion `X → J X`.
* `TauCeti.JamesReducedProduct.length`: the length of a reduced word.
* `TauCeti.JamesReducedProduct.filtration`: the word-length filtration `J_r X`.
* `TauCeti.JamesReducedProduct.liftMonoidHom`, `TauCeti.JamesReducedProduct.lift`: the universal
  property of `J X` among monoids and among topological monoids.
* `TauCeti.JamesReducedProduct.map`: the continuous monoid homomorphism `J X → J Y` induced by a
  based continuous map `X → Y`.

## Main results

* `TauCeti.JamesReducedProduct.isQuotientMap_sigmaMk`: the reduction of words of all lengths is a
  quotient map, and `TauCeti.JamesReducedProduct.continuous_iff` characterizes continuous maps
  out of `J X`.
* `TauCeti.JamesReducedProduct.range_mk`: the image of `Xʳ` is the set of reduced words of length
  at most `r`.
* `TauCeti.JamesReducedProduct.isClosed_filtration`,
  `TauCeti.JamesReducedProduct.isCompact_filtration`: closedness and compactness of `J_r X`.
* `TauCeti.JamesReducedProduct.hom_ext`: monoid homomorphisms out of `J X` agreeing on letters
  are equal.

## References

* I. M. James, *Reduced product spaces*, Ann. of Math. (2) 62 (1955), 170–197.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.C.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VII.2.
-/

public section

noncomputable section

universe u v w

open Set Topology

namespace TauCeti

/-- The **James reduced product** `J X` of a pointed set `(X, x₀)`: the finite words in the points
of `X`, two words being identified when they agree after every occurrence of the basepoint has
been deleted. Its elements are the reduced words, the finite sequences of points different from
`x₀`; concatenation makes it the free monoid on `X ∖ {x₀}`
(`TauCeti.JamesReducedProduct.freeMonoidEquiv`). For a topological space `X` it carries the final
topology of the maps from the powers `Xⁿ` (`TauCeti.JamesReducedProduct.instTopologicalSpace`). -/
def JamesReducedProduct (X : Type u) (x₀ : X) : Type u :=
  FreeMonoid {x : X // x ≠ x₀}

namespace JamesReducedProduct

variable {X : Type u} {x₀ : X}

instance : Monoid (JamesReducedProduct X x₀) :=
  inferInstanceAs (Monoid (FreeMonoid {x : X // x ≠ x₀}))

variable (X x₀) in
/-- As a monoid, the James reduced product is the free monoid on the points other than the
basepoint. -/
def freeMonoidEquiv : JamesReducedProduct X x₀ ≃* FreeMonoid {x : X // x ≠ x₀} :=
  MulEquiv.refl _

/-! ### Letters and reduced words -/

/-- The one-letter word on a point `x` of `X`; it is the empty word when `x` is the basepoint.
This is the inclusion `X → J X`. -/
def letter (x : X) : JamesReducedProduct X x₀ :=
  open Classical in
  if h : x = x₀ then 1 else (freeMonoidEquiv X x₀).symm (FreeMonoid.of ⟨x, h⟩)

@[simp]
theorem letter_basepoint : (letter x₀ : JamesReducedProduct X x₀) = 1 := by
  simp [letter]

theorem letter_of_ne {x : X} (h : x ≠ x₀) :
    (letter x : JamesReducedProduct X x₀) = (freeMonoidEquiv X x₀).symm (FreeMonoid.of ⟨x, h⟩) := by
  simp [letter, h]

@[simp]
theorem freeMonoidEquiv_symm_of (x : {x : X // x ≠ x₀}) :
    (freeMonoidEquiv X x₀).symm (FreeMonoid.of x) = letter (x : X) :=
  (letter_of_ne x.2).symm

@[simp]
theorem freeMonoidEquiv_letter_coe (x : {x : X // x ≠ x₀}) :
    freeMonoidEquiv X x₀ (letter x) = FreeMonoid.of x := by
  rw [letter_of_ne x.2, MulEquiv.apply_symm_apply]

@[simp]
theorem letter_eq_one_iff {x : X} : (letter x : JamesReducedProduct X x₀) = 1 ↔ x = x₀ := by
  refine ⟨fun h => by_contra fun hx => ?_, fun h => h ▸ letter_basepoint⟩
  rw [letter_of_ne hx, MulEquiv.symm_apply_eq, map_one] at h
  exact FreeMonoid.of_ne_one _ h

theorem letter_injective : Function.Injective (letter : X → JamesReducedProduct X x₀) := by
  intro x y h
  by_cases hx : x = x₀
  · rw [hx, letter_basepoint, eq_comm, letter_eq_one_iff] at h
    rw [hx, h]
  by_cases hy : y = x₀
  · rw [hy, letter_basepoint, letter_eq_one_iff] at h
    exact absurd h hx
  rw [letter_of_ne hx, letter_of_ne hy] at h
  exact congrArg Subtype.val (FreeMonoid.of_injective ((freeMonoidEquiv X x₀).symm.injective h))

@[simp]
theorem letter_inj {x y : X} : (letter x : JamesReducedProduct X x₀) = letter y ↔ x = y :=
  letter_injective.eq_iff

/-- The **reduced word** of a word `v = v 0 v 1 ⋯ v (n - 1)` of length `n` in the points of `X`:
the product of its letters, which deletes the occurrences of the basepoint. -/
def mk {n : ℕ} (v : Fin n → X) : JamesReducedProduct X x₀ :=
  (List.ofFn fun i => letter (v i)).prod

theorem mk_def {n : ℕ} (v : Fin n → X) :
    (mk v : JamesReducedProduct X x₀) = (List.ofFn fun i => letter (v i)).prod :=
  (rfl)

@[simp]
theorem mk_zero (v : Fin 0 → X) : (mk v : JamesReducedProduct X x₀) = 1 := by
  simp [mk_def]

@[simp]
theorem mk_cons {n : ℕ} (x : X) (v : Fin n → X) :
    (mk (Fin.cons x v) : JamesReducedProduct X x₀) = letter x * mk v := by
  simp [mk_def, List.ofFn_succ]

@[simp]
theorem mk_fin_one (v : Fin 1 → X) : (mk v : JamesReducedProduct X x₀) = letter (v 0) := by
  simp [mk_def]

@[simp]
theorem mk_append {m n : ℕ} (u : Fin m → X) (v : Fin n → X) :
    (mk (Fin.append u v) : JamesReducedProduct X x₀) = mk u * mk v := by
  simp only [mk_def]
  rw [← List.prod_append, ← List.ofFn_fin_append]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

@[simp]
theorem mk_const_basepoint (n : ℕ) :
    (mk (fun _ : Fin n => x₀) : JamesReducedProduct X x₀) = 1 := by
  simp [mk_def]

theorem mk_comp_cast {m n : ℕ} (h : m = n) (v : Fin n → X) :
    (mk (v ∘ Fin.cast h) : JamesReducedProduct X x₀) = mk v := by
  subst h
  rfl

/-- The reduced word given by a list of points different from the basepoint is the reduced word of
the word of the same length formed by these points. -/
private theorem exists_mk_eq_ofList (l : List {x : X // x ≠ x₀}) :
    ∃ v : Fin l.length → X,
      (mk v : JamesReducedProduct X x₀) = (freeMonoidEquiv X x₀).symm (FreeMonoid.ofList l) := by
  induction l with
  | nil => exact ⟨Fin.elim0, by simp⟩
  | cons a l ih =>
    obtain ⟨v, hmk⟩ := ih
    refine ⟨Fin.cons a.1 v, ?_⟩
    rw [FreeMonoid.ofList_cons, map_mul, ← hmk, mk_cons, freeMonoidEquiv_symm_of]

/-! ### Length -/

/-- The **length** of a reduced word: the number of its letters, each different from the
basepoint. -/
def length (w : JamesReducedProduct X x₀) : ℕ :=
  (freeMonoidEquiv X x₀ w).toList.length

@[simp]
theorem length_one : length (1 : JamesReducedProduct X x₀) = 0 := by
  simp [length]

@[simp]
theorem length_mul (w w' : JamesReducedProduct X x₀) :
    length (w * w') = length w + length w' := by
  simp [length]

@[simp]
theorem length_eq_zero {w : JamesReducedProduct X x₀} : length w = 0 ↔ w = 1 := by
  rw [length, List.length_eq_zero_iff, ← FreeMonoid.toList_one,
    ← FreeMonoid.ext_iff, MulEquiv.map_eq_one_iff]

theorem length_letter_of_ne {x : X} (h : x ≠ x₀) :
    length (letter x : JamesReducedProduct X x₀) = 1 := by
  rw [length, letter_of_ne h, MulEquiv.apply_symm_apply, FreeMonoid.toList_of,
    List.length_singleton]

/-- The length of the reduced word of `v` is the number of letters of `v` different from the
basepoint. -/
theorem length_mk [DecidableEq X] {n : ℕ} (v : Fin n → X) :
    length (mk v : JamesReducedProduct X x₀) = (Finset.univ.filter fun i => v i ≠ x₀).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fin.cons_self_tail v, mk_cons, length_mul, ih, Fin.card_filter_univ_succ']
    -- The two filtered sets differ only in their decidability instances.
    by_cases h : v 0 = x₀ <;> simp [h, length_letter_of_ne, Fin.tail] <;> congr 1

theorem length_mk_le {n : ℕ} (v : Fin n → X) : length (mk v : JamesReducedProduct X x₀) ≤ n := by
  classical
  exact (length_mk v).trans_le ((Finset.card_filter_le _ _).trans (Finset.card_fin n).le)

/-- Every reduced word is the reduced word of a word of each length at least its own. -/
theorem exists_mk_eq_of_length_le {w : JamesReducedProduct X x₀} {n : ℕ} (h : length w ≤ n) :
    ∃ v : Fin n → X, mk v = w := by
  obtain ⟨u, hu⟩ := exists_mk_eq_ofList (FreeMonoid.toList (freeMonoidEquiv X x₀ w))
  rw [FreeMonoid.ofList_toList, MulEquiv.symm_apply_apply] at hu
  have hn : (FreeMonoid.toList (freeMonoidEquiv X x₀ w)).length + (n - length w) = n := by
    rw [length] at h ⊢
    omega
  refine ⟨Fin.append u (fun _ : Fin (n - length w) => x₀) ∘ Fin.cast hn.symm, ?_⟩
  rw [mk_comp_cast, mk_append, mk_const_basepoint, mul_one, hu]

theorem exists_mk_eq (w : JamesReducedProduct X x₀) : ∃ (n : ℕ) (v : Fin n → X), mk v = w :=
  ⟨length w, exists_mk_eq_of_length_le le_rfl⟩

/-! ### The universal property among monoids -/

section Monoid

variable {M : Type w} [Monoid M]

/-- Monoid homomorphisms out of the James reduced product agreeing on letters are equal. -/
theorem hom_ext {f g : JamesReducedProduct X x₀ →* M}
    (h : ∀ x, f (letter x) = g (letter x)) : f = g := by
  refine MonoidHom.ext fun w => ?_
  obtain ⟨n, v, rfl⟩ := exists_mk_eq w
  simp [mk_def, map_list_prod, List.map_ofFn, Function.comp_def, h]

/-- The monoid homomorphism `J X →* M` sending a reduced word `x₁ ⋯ xₙ` to `g x₁ ⋯ g xₙ`. When
`g` sends the basepoint to `1`, it is the unique monoid homomorphism extending `g` along the
letters (`TauCeti.JamesReducedProduct.liftMonoidHom_letter`,
`TauCeti.JamesReducedProduct.hom_ext`). -/
def liftMonoidHom (g : X → M) : JamesReducedProduct X x₀ →* M :=
  (FreeMonoid.lift fun x : {x : X // x ≠ x₀} => g x).comp (freeMonoidEquiv X x₀).toMonoidHom

@[simp]
theorem liftMonoidHom_letter {g : X → M} (hg : g x₀ = 1) (x : X) :
    liftMonoidHom g (letter x : JamesReducedProduct X x₀) = g x := by
  by_cases hx : x = x₀
  · rw [hx, letter_basepoint, map_one, hg]
  · simp [liftMonoidHom, letter_of_ne hx, -freeMonoidEquiv_symm_of]

theorem liftMonoidHom_mk {g : X → M} (hg : g x₀ = 1) {n : ℕ} (v : Fin n → X) :
    liftMonoidHom g (mk v : JamesReducedProduct X x₀) = (List.ofFn fun i => g (v i)).prod := by
  simp [mk_def, map_list_prod, List.map_ofFn, Function.comp_def, hg]

theorem liftMonoidHom_unique {g : X → M} (hg : g x₀ = 1) {f : JamesReducedProduct X x₀ →* M}
    (hf : ∀ x, f (letter x) = g x) : f = liftMonoidHom g :=
  hom_ext fun x => by rw [hf, liftMonoidHom_letter hg]

end Monoid

/-! ### The word-length filtration -/

variable (X x₀) in
/-- The `r`-th stage `J_r X` of the **word-length filtration** of the James reduced product: the
reduced words of length at most `r`. It is the image of `Xʳ`
(`TauCeti.JamesReducedProduct.range_mk`). -/
def filtration (r : ℕ) : Set (JamesReducedProduct X x₀) :=
  {w | length w ≤ r}

@[simp]
theorem mem_filtration_iff {r : ℕ} {w : JamesReducedProduct X x₀} :
    w ∈ filtration X x₀ r ↔ length w ≤ r :=
  Iff.rfl

theorem range_mk (r : ℕ) :
    range (mk : (Fin r → X) → JamesReducedProduct X x₀) = filtration X x₀ r := by
  ext w
  exact ⟨fun ⟨v, hv⟩ => hv ▸ length_mk_le v, fun h => exists_mk_eq_of_length_le h⟩

theorem mk_mem_filtration {r : ℕ} (v : Fin r → X) :
    (mk v : JamesReducedProduct X x₀) ∈ filtration X x₀ r :=
  length_mk_le v

theorem filtration_mono : Monotone (filtration X x₀) :=
  fun _ _ hrs _ hw => le_trans hw hrs

@[simp]
theorem iUnion_filtration : ⋃ r, filtration X x₀ r = univ :=
  eq_univ_of_forall fun w => mem_iUnion.2 ⟨length w, mem_filtration_iff.2 le_rfl⟩

@[simp]
theorem filtration_zero : filtration X x₀ 0 = {1} := by
  ext w
  simp [mem_filtration_iff]

theorem filtration_one : filtration X x₀ 1 = range letter := by
  rw [← range_mk]
  ext w
  exact ⟨fun ⟨v, hv⟩ => ⟨v 0, by rw [← hv, mk_fin_one]⟩,
    fun ⟨x, hx⟩ => ⟨fun _ => x, by rw [mk_fin_one, hx]⟩⟩

theorem one_mem_filtration (r : ℕ) : (1 : JamesReducedProduct X x₀) ∈ filtration X x₀ r := by
  simp [mem_filtration_iff]

theorem letter_mem_filtration_one (x : X) :
    (letter x : JamesReducedProduct X x₀) ∈ filtration X x₀ 1 := by
  rw [filtration_one]
  exact mem_range_self x

theorem mul_mem_filtration {r s : ℕ} {w w' : JamesReducedProduct X x₀}
    (hw : w ∈ filtration X x₀ r) (hw' : w' ∈ filtration X x₀ s) :
    w * w' ∈ filtration X x₀ (r + s) := by
  rw [mem_filtration_iff, length_mul]
  exact Nat.add_le_add hw hw'

/-! ### The topology -/

section Topology

variable [TopologicalSpace X]

/-- The topology of the James reduced product: the final topology of the maps `Xⁿ → J X` sending
a word to its reduced word, for all `n`. -/
instance instTopologicalSpace : TopologicalSpace (JamesReducedProduct X x₀) :=
  TopologicalSpace.coinduced (fun p : Σ n, Fin n → X => mk p.2) inferInstance

theorem isQuotientMap_sigmaMk :
    IsQuotientMap fun p : Σ n, Fin n → X => (mk p.2 : JamesReducedProduct X x₀) :=
  ⟨⟨rfl⟩, fun w => let ⟨n, v, hv⟩ := exists_mk_eq w; ⟨⟨n, v⟩, hv⟩⟩

@[fun_prop]
theorem continuous_mk (n : ℕ) : Continuous (mk : (Fin n → X) → JamesReducedProduct X x₀) :=
  isQuotientMap_sigmaMk.continuous.comp continuous_sigmaMk

/-- A map out of the James reduced product is continuous if and only if its composite with the
reduction `Xⁿ → J X` is continuous for every `n`. -/
theorem continuous_iff {Y : Type v} [TopologicalSpace Y] {f : JamesReducedProduct X x₀ → Y} :
    Continuous f ↔ ∀ n, Continuous fun v : Fin n → X => f (mk v) := by
  rw [isQuotientMap_sigmaMk.continuous_iff, continuous_sigma_iff]
  rfl

/-- A set of reduced words is open if and only if its preimage in `Xⁿ` is open for every `n`. -/
theorem isOpen_iff {s : Set (JamesReducedProduct X x₀)} :
    IsOpen s ↔ ∀ n, IsOpen (mk ⁻¹' s : Set (Fin n → X)) := by
  rw [← isQuotientMap_sigmaMk.isOpen_preimage, isOpen_sigma_iff]
  rfl

/-- A set of reduced words is closed if and only if its preimage in `Xⁿ` is closed for every
`n`. -/
theorem isClosed_iff {s : Set (JamesReducedProduct X x₀)} :
    IsClosed s ↔ ∀ n, IsClosed (mk ⁻¹' s : Set (Fin n → X)) := by
  rw [← isQuotientMap_sigmaMk.isClosed_preimage, isClosed_sigma_iff]
  rfl

@[fun_prop]
theorem continuous_letter : Continuous (letter : X → JamesReducedProduct X x₀) := by
  have : (letter : X → JamesReducedProduct X x₀) = fun x => mk fun _ : Fin 1 => x := by
    ext x
    rw [mk_fin_one]
  rw [this]
  fun_prop

/-- Left translation by a reduced word is continuous. -/
theorem continuous_mul_left (w : JamesReducedProduct X x₀) : Continuous (w * ·) := by
  obtain ⟨m, u, rfl⟩ := exists_mk_eq w
  refine continuous_iff.2 fun n => ?_
  simp_rw [← mk_append]
  exact (continuous_mk _).comp ((Fin.continuous_append m n).comp
    (continuous_const.prodMk continuous_id))

/-- Right translation by a reduced word is continuous. -/
theorem continuous_mul_right (w : JamesReducedProduct X x₀) : Continuous (· * w) := by
  obtain ⟨m, u, rfl⟩ := exists_mk_eq w
  refine continuous_iff.2 fun n => ?_
  simp_rw [← mk_append]
  exact (continuous_mk _).comp ((Fin.continuous_append n m).comp
    (continuous_id.prodMk continuous_const))

/-- The stages of the word-length filtration are closed when the basepoint is closed. -/
theorem isClosed_filtration (h : IsClosed ({x₀} : Set X)) (r : ℕ) :
    IsClosed (filtration X x₀ r) := by
  classical
  refine isClosed_iff.2 fun n => ?_
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro v hv
  simp only [mem_compl_iff, mem_preimage, mem_filtration_iff, length_mk, not_le] at hv
  -- The words different from the basepoint at each position where `v` is form a neighbourhood
  -- of `v`, on which the length of the reduced word is at least that of `v`.
  have hnhds : (⋂ i ∈ Finset.univ.filter fun i => v i ≠ x₀,
      (fun u : Fin n → X => u i) ⁻¹' {x₀}ᶜ) ∈ 𝓝 v :=
    (Filter.biInter_finset_mem _).2 fun i hi => (continuous_apply i).continuousAt.preimage_mem_nhds
      (h.isOpen_compl.mem_nhds (Finset.mem_filter.1 hi).2)
  refine Filter.mem_of_superset hnhds fun u hu => ?_
  simp only [mem_iInter, mem_preimage, mem_compl_iff, mem_singleton_iff] at hu
  simp only [mem_compl_iff, mem_preimage, mem_filtration_iff, length_mk, not_le]
  exact hv.trans_le (Finset.card_le_card fun i hi =>
    Finset.mem_filter.2 ⟨Finset.mem_univ i, hu i hi⟩)

/-- The stages of the word-length filtration are compact when `X` is compact. -/
theorem isCompact_filtration [CompactSpace X] (r : ℕ) : IsCompact (filtration X x₀ r) := by
  rw [← range_mk]
  exact isCompact_range (continuous_mk r)

/-- The James reduced product of a path-connected space is path-connected. -/
instance [PathConnectedSpace X] : PathConnectedSpace (JamesReducedProduct X x₀) := by
  have hjoined (w : JamesReducedProduct X x₀) : Joined 1 w := by
    obtain ⟨n, v, rfl⟩ := exists_mk_eq w
    obtain ⟨γ⟩ := PathConnectedSpace.joined (fun _ : Fin n => x₀) v
    exact ⟨(γ.map (continuous_mk n)).cast (mk_const_basepoint n).symm rfl⟩
  exact ⟨⟨1⟩, fun w w' => (hjoined w).symm.trans (hjoined w')⟩

/-! ### The universal property among topological monoids -/

section Lift

variable {M : Type w} [Monoid M] [TopologicalSpace M] [ContinuousMul M]

/-- The **universal property** of the James reduced product: a continuous map `g : X → M` to a
topological monoid sending the basepoint to `1` extends to the continuous monoid homomorphism
`J X → M` sending a reduced word `x₁ ⋯ xₙ` to `g x₁ ⋯ g xₙ`. It is the only monoid homomorphism
extending `g` (`TauCeti.JamesReducedProduct.liftMonoidHom_unique`). -/
def lift (g : C(X, M)) (hg : g x₀ = 1) : JamesReducedProduct X x₀ →ₜ* M where
  toMonoidHom := liftMonoidHom g
  continuous_toFun := by
    refine continuous_iff.2 fun n => ?_
    simp only [MonoidHom.toOneHom_coe, OneHom.toFun_eq_coe, liftMonoidHom_mk hg, List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => g.continuous.comp (continuous_apply i)

@[simp]
theorem lift_letter (g : C(X, M)) (hg : g x₀ = 1) (x : X) :
    lift g hg (letter x : JamesReducedProduct X x₀) = g x :=
  liftMonoidHom_letter hg x

theorem lift_mk (g : C(X, M)) (hg : g x₀ = 1) {n : ℕ} (v : Fin n → X) :
    lift g hg (mk v : JamesReducedProduct X x₀) = (List.ofFn fun i => g (v i)).prod :=
  liftMonoidHom_mk hg v

theorem toMonoidHom_lift (g : C(X, M)) (hg : g x₀ = 1) :
    (lift g hg).toMonoidHom = liftMonoidHom (x₀ := x₀) g :=
  (rfl)

end Lift

/-! ### Functoriality -/

section Map

variable {Y : Type v} [TopologicalSpace Y] {y₀ : Y} {Z : Type w} [TopologicalSpace Z] {z₀ : Z}

private theorem liftMonoidHom_letter_comp_mk (f : C(X, Y)) (hf : f x₀ = y₀) {n : ℕ}
    (v : Fin n → X) :
    liftMonoidHom (fun x => (letter (f x) : JamesReducedProduct Y y₀))
      (mk v : JamesReducedProduct X x₀) = mk (f ∘ v) :=
  (liftMonoidHom_mk (g := fun x => letter (f x)) (by simp [hf]) v).trans (mk_def _).symm

/-- The continuous monoid homomorphism `J f : J X → J Y` induced by a based continuous map
`f : X → Y`: it applies `f` to each letter. -/
def map (f : C(X, Y)) (hf : f x₀ = y₀) :
    JamesReducedProduct X x₀ →ₜ* JamesReducedProduct Y y₀ where
  toMonoidHom := liftMonoidHom fun x => letter (f x)
  continuous_toFun := by
    refine continuous_iff.2 fun n => ?_
    simp only [MonoidHom.toOneHom_coe, OneHom.toFun_eq_coe, liftMonoidHom_letter_comp_mk f hf]
    -- The composite is the reduced word of `f ∘ v`, by definition of `mk`.
    exact (continuous_mk (x₀ := y₀) n).comp
      (continuous_pi fun i => f.continuous.comp (continuous_apply i))

@[simp]
theorem map_letter (f : C(X, Y)) (hf : f x₀ = y₀) (x : X) :
    map f hf (letter x : JamesReducedProduct X x₀) = letter (f x) :=
  liftMonoidHom_letter (by simp [hf]) x

@[simp]
theorem map_mk (f : C(X, Y)) (hf : f x₀ = y₀) {n : ℕ} (v : Fin n → X) :
    map f hf (mk v : JamesReducedProduct X x₀) = mk (f ∘ v) :=
  liftMonoidHom_letter_comp_mk f hf v

@[simp]
theorem map_id :
    map (ContinuousMap.id X) rfl = ContinuousMonoidHom.id (JamesReducedProduct X x₀) := by
  ext w
  obtain ⟨n, v, rfl⟩ := exists_mk_eq w
  rw [map_mk]
  rfl

theorem map_comp (g : C(Y, Z)) (hg : g y₀ = z₀) (f : C(X, Y)) (hf : f x₀ = y₀) :
    map (g.comp f) (by rw [ContinuousMap.comp_apply, hf, hg]) =
      (map g hg).comp (map f hf : JamesReducedProduct X x₀ →ₜ* JamesReducedProduct Y y₀) := by
  ext w
  obtain ⟨n, v, rfl⟩ := exists_mk_eq w
  simp [Function.comp_assoc]

theorem length_map_le (f : C(X, Y)) (hf : f x₀ = y₀) (w : JamesReducedProduct X x₀) :
    length (map f hf w) ≤ length w := by
  classical
  obtain ⟨n, v, rfl⟩ := exists_mk_eq w
  rw [map_mk, length_mk, length_mk]
  refine Finset.card_le_card fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ i, fun h => ?_⟩
  exact (Finset.mem_filter.1 hi).2 (by rw [Function.comp_apply, h, hf])

theorem mapsTo_map_filtration (f : C(X, Y)) (hf : f x₀ = y₀) (r : ℕ) :
    MapsTo (map f hf) (filtration X x₀ r) (filtration Y y₀ r) :=
  fun w hw => (length_map_le f hf w).trans hw

end Map

end Topology

end JamesReducedProduct

end TauCeti

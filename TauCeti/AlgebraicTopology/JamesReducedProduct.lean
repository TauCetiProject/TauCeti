/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The James reduced product

For a pointed space `(X, x₀)`, the **James reduced product** `J X` is the space of finite words
`x₁ x₂ ⋯ xₙ` in the points of `X`, two words being identified when they agree after every
occurrence of the basepoint has been deleted. Concatenation of words makes it a monoid with the
empty word as unit, and as a monoid it is the free monoid on the points other than the basepoint
(`TauCeti.JamesReducedProduct.freeMonoidEquiv`). Its topology is the final topology of the maps
`k(Xⁿ) → J X` sending a word of length `n` to its reduced word
(`TauCeti.JamesReducedProduct.mk`), for all `n`, where `k(Xⁿ)` is the power `Xⁿ` with its
compactly generated topology (`TopologicalSpace.compactlyGenerated`). So `J X` is formed in the
category of compactly generated spaces: it is compactly generated, and a map out of it is
continuous exactly when its composites with the continuous maps `S → Xⁿ` from compact Hausdorff
spaces are. For a connected CW complex `X`, James proved that `J X` is a model for the loop space
`ΩΣX` of the suspension; this is what makes it the basic tool for computing the homology of loop
spaces of suspensions and, through the word-length filtration, for the EHP sequence and the James
splitting.

This file sets up the construction for an arbitrary pointed topological space, with no separation
or connectivity hypothesis:

* the reduced word of a finite word, the letters `X → J X`, and the monoid structure;
* the universal property: a map `g : X → M` to a monoid with `g x₀ = 1` extends uniquely to a
  monoid homomorphism `J X →* M`, which is continuous when `g` is continuous and `M` is a
  topological monoid (`TauCeti.JamesReducedProduct.lift`);
* the characterization of continuous maps, open sets and closed sets out of `J X`, its compact
  generation, and the continuity of the letters (for compactly generated `X`) and of the
  translations;
* the word-length filtration `J₀ X ⊆ J₁ X ⊆ ⋯`, where `J_r X` is the image of `Xʳ`; it is
  exhaustive, multiplicative, closed when the basepoint is closed, and compact when `X` is compact
  Hausdorff;
* the functoriality of `J` in based continuous maps, by continuous monoid homomorphisms that
  preserve the filtration;
* path-connectedness of `J X` for path-connected `X`.

Continuity of the multiplication `k(J X × J X) → J X` on the compactly generated product is not
established here; each left and right translation is continuous.

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

* `TauCeti.JamesReducedProduct.continuous_iff`: a map out of `J X` is continuous if and only if
  its composites with the reduced words of the continuous families of words `S → Xⁿ` over compact
  Hausdorff spaces `S` are, and `J X` is compactly generated.
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
topology of the maps from the compactly generated powers `k(Xⁿ)`
(`TauCeti.JamesReducedProduct.instTopologicalSpace`). -/
def JamesReducedProduct (X : Type u) (x₀ : X) : Type u :=
  FreeMonoid {x : X // x ≠ x₀}

namespace JamesReducedProduct

variable {X : Type u} {x₀ : X}

instance : CancelMonoid (JamesReducedProduct X x₀) :=
  inferInstanceAs (CancelMonoid (FreeMonoid {x : X // x ≠ x₀}))

instance : Inhabited (JamesReducedProduct X x₀) :=
  ⟨1⟩

/-- The only unit of the James reduced product is the empty word. -/
instance : Unique (JamesReducedProduct X x₀)ˣ :=
  inferInstanceAs (Unique (FreeMonoid {x : X // x ≠ x₀})ˣ)

/-- The James reduced product of a one-point space is a point. -/
instance [Subsingleton X] : Unique (JamesReducedProduct X x₀) :=
  haveI : IsEmpty {x : X // x ≠ x₀} := ⟨fun x => x.2 (Subsingleton.elim _ _)⟩
  inferInstanceAs (Unique (FreeMonoid {x : X // x ≠ x₀}))

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
theorem mk_fin_zero (v : Fin 0 → X) : (mk v : JamesReducedProduct X x₀) = 1 := by
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

@[simp]
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
theorem length_toList_freeMonoidEquiv (w : JamesReducedProduct X x₀) :
    (freeMonoidEquiv X x₀ w).toList.length = length w :=
  (rfl)

@[simp]
theorem length_one : length (1 : JamesReducedProduct X x₀) = 0 := by
  simp [length, -length_toList_freeMonoidEquiv]

@[simp]
theorem length_mul (w w' : JamesReducedProduct X x₀) :
    length (w * w') = length w + length w' := by
  simp [length, -length_toList_freeMonoidEquiv]

@[simp]
theorem length_eq_zero_iff {w : JamesReducedProduct X x₀} : length w = 0 ↔ w = 1 := by
  rw [length, List.length_eq_zero_iff, ← FreeMonoid.toList_one,
    ← FreeMonoid.ext_iff, MulEquiv.map_eq_one_iff]

@[grind =]
theorem length_letter_of_ne {x : X} (h : x ≠ x₀) :
    length (letter x : JamesReducedProduct X x₀) = 1 := by
  rw [length, letter_of_ne h, MulEquiv.apply_symm_apply, FreeMonoid.toList_of,
    List.length_singleton]

@[simp]
theorem length_letter_le (x : X) : length (letter x : JamesReducedProduct X x₀) ≤ 1 := by
  by_cases h : x = x₀
  · simp [h]
  · exact (length_letter_of_ne h).le

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

@[simp]
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

/-- The letters of the reduced word of `v` are the letters of `v` different from the basepoint. -/
theorem mem_toList_freeMonoidEquiv_mk {n : ℕ} (v : Fin n → X) (a : {x : X // x ≠ x₀}) :
    a ∈ (freeMonoidEquiv X x₀ (mk v)).toList ↔ ∃ i, v i = a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fin.cons_self_tail v, mk_cons, map_mul, FreeMonoid.toList_mul, List.mem_append, ih,
      Fin.exists_fin_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    by_cases h : v 0 = x₀
    · simp [h, a.2.symm]
    · rw [letter_of_ne h, MulEquiv.apply_symm_apply, FreeMonoid.toList_of, List.mem_singleton,
        Subtype.ext_iff, eq_comm]

/-! ### The universal property among monoids -/

section Monoid

variable {M : Type w} [Monoid M]

/-- Monoid homomorphisms out of the James reduced product agreeing on the letters different from
the basepoint are equal. -/
theorem hom_ext {F : Type*} [FunLike F (JamesReducedProduct X x₀) M]
    [MonoidHomClass F (JamesReducedProduct X x₀) M] {f g : F}
    (h : ∀ x ≠ x₀, f (letter x) = g (letter x)) : f = g := by
  have h' (x : X) : f (letter x) = g (letter x) := by
    by_cases hx : x = x₀
    · simp [hx]
    · exact h x hx
  refine DFunLike.ext _ _ fun w => ?_
  obtain ⟨n, v, rfl⟩ := exists_mk_eq w
  simp [mk_def, map_list_prod, List.map_ofFn, Function.comp_def, h']

/-- The extensionality lemma `TauCeti.JamesReducedProduct.hom_ext` for monoid homomorphisms. -/
@[ext]
theorem monoidHom_ext {f g : JamesReducedProduct X x₀ →* M}
    (h : ∀ x ≠ x₀, f (letter x) = g (letter x)) : f = g :=
  hom_ext h

/-- The monoid homomorphism `J X →* M` sending a reduced word `x₁ ⋯ xₙ` to `g x₁ ⋯ g xₙ`, for a map
`g` sending the basepoint to `1`. It is the unique monoid homomorphism extending `g` along the
letters (`TauCeti.JamesReducedProduct.liftMonoidHom_letter`,
`TauCeti.JamesReducedProduct.liftMonoidHom_unique`). -/
def liftMonoidHom (g : X → M) (_hg : g x₀ = 1) : JamesReducedProduct X x₀ →* M :=
  (FreeMonoid.lift fun x : {x : X // x ≠ x₀} => g x).comp (freeMonoidEquiv X x₀).toMonoidHom

@[simp]
theorem liftMonoidHom_letter {g : X → M} (hg : g x₀ = 1) (x : X) :
    liftMonoidHom g hg (letter x : JamesReducedProduct X x₀) = g x := by
  by_cases hx : x = x₀
  · rw [hx, letter_basepoint, map_one, hg]
  · simp [liftMonoidHom, letter_of_ne hx, -freeMonoidEquiv_symm_of]

@[simp]
theorem liftMonoidHom_mk {g : X → M} (hg : g x₀ = 1) {n : ℕ} (v : Fin n → X) :
    liftMonoidHom g hg (mk v : JamesReducedProduct X x₀) = (List.ofFn fun i => g (v i)).prod := by
  simp [mk_def, map_list_prod, List.map_ofFn, Function.comp_def]

/-- The uniqueness half of the universal property: `liftMonoidHom g hg` is the only monoid
homomorphism out of `J X` extending `g` along the letters. -/
theorem liftMonoidHom_unique {g : X → M} (hg : g x₀ = 1) {f : JamesReducedProduct X x₀ →* M}
    (hf : ∀ x ≠ x₀, f (letter x) = g x) : f = liftMonoidHom g hg :=
  hom_ext fun x hx => by rw [hf x hx, liftMonoidHom_letter]

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

/-- The `r`-th stage `J_r X` of the word-length filtration is the image of `Xʳ` under the
reduction of words. -/
theorem range_mk (r : ℕ) :
    range (mk : (Fin r → X) → JamesReducedProduct X x₀) = filtration X x₀ r := by
  ext w
  exact ⟨fun ⟨v, hv⟩ => hv ▸ length_mk_le v, fun h => exists_mk_eq_of_length_le h⟩

theorem mk_mem_filtration {r : ℕ} (v : Fin r → X) :
    (mk v : JamesReducedProduct X x₀) ∈ filtration X x₀ r :=
  length_mk_le v

theorem filtration_monotone : Monotone (filtration X x₀) :=
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

/-- The word-length filtration is multiplicative: the product of a word of `J_r X` and a word of
`J_s X` lies in `J_(r + s) X`. -/
theorem mul_mem_filtration {r s : ℕ} {w w' : JamesReducedProduct X x₀}
    (hw : w ∈ filtration X x₀ r) (hw' : w' ∈ filtration X x₀ s) :
    w * w' ∈ filtration X x₀ (r + s) := by
  rw [mem_filtration_iff, length_mul]
  exact Nat.add_le_add hw hw'

/-! ### The topology -/

section Topology

variable [TopologicalSpace X]

/-- The topology of the James reduced product: the final topology of the maps `k(Xⁿ) → J X`
sending a word to its reduced word, for all `n`, where `k(Xⁿ)` is the power `Xⁿ` with its
compactly generated topology. -/
instance instTopologicalSpace : TopologicalSpace (JamesReducedProduct X x₀) :=
  ⨆ n, .coinduced (mk : (Fin n → X) → JamesReducedProduct X x₀)
    (TopologicalSpace.compactlyGenerated.{u} (Fin n → X))

/-- A map out of the compactly generated topology is continuous if and only if its composites with
the continuous maps from compact Hausdorff spaces are. -/
private theorem continuous_compactlyGenerated_iff {Z : Type u} [TopologicalSpace Z] {Y : Type v}
    [t : TopologicalSpace Y] {f : Z → Y} :
    Continuous[TopologicalSpace.compactlyGenerated.{u} Z, t] f ↔
      ∀ (S : CompHaus.{u}) (g : C(S, Z)), Continuous (f ∘ g) := by
  refine ⟨fun hf S g => ?_, continuous_from_compactlyGenerated f⟩
  rw [TopologicalSpace.compactlyGenerated, continuous_coinduced_dom, continuous_sigma_iff] at hf
  exact hf ⟨S, g⟩

/-- A map out of the James reduced product is continuous if and only if, for every `n`, its
composite with the reduced words of every continuous family of words `S → Xⁿ` parametrized by a
compact Hausdorff space `S` is continuous. -/
theorem continuous_iff {Y : Type v} [TopologicalSpace Y] {f : JamesReducedProduct X x₀ → Y} :
    Continuous f ↔
      ∀ (n : ℕ) (S : CompHaus.{u}) (g : C(S, Fin n → X)), Continuous fun s => f (mk (g s)) := by
  refine continuous_iSup_dom.trans (forall_congr' fun n => ?_)
  rw [continuous_coinduced_dom, continuous_compactlyGenerated_iff]
  rfl

/-- A set of reduced words is open if and only if its preimage under the reduced words of every
continuous family of words `S → Xⁿ` over a compact Hausdorff space `S` is open. -/
theorem isOpen_iff {s : Set (JamesReducedProduct X x₀)} :
    IsOpen s ↔ ∀ (n : ℕ) (S : CompHaus.{u}) (g : C(S, Fin n → X)),
      IsOpen ((fun t => (mk (g t) : JamesReducedProduct X x₀)) ⁻¹' s) := by
  simp only [isOpen_iff_continuous_mem, continuous_iff]
  rfl

/-- A set of reduced words is closed if and only if its preimage under the reduced words of every
continuous family of words `S → Xⁿ` over a compact Hausdorff space `S` is closed. -/
theorem isClosed_iff {s : Set (JamesReducedProduct X x₀)} :
    IsClosed s ↔ ∀ (n : ℕ) (S : CompHaus.{u}) (g : C(S, Fin n → X)),
      IsClosed ((fun t => (mk (g t) : JamesReducedProduct X x₀)) ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_iff, preimage_compl]

/-- The reduced words of a continuous family of words parametrized by a compactly generated space
depend continuously on the parameter. -/
@[fun_prop]
theorem continuous_mk {Z : Type v} [TopologicalSpace Z] [UCompactlyGeneratedSpace.{u} Z] {n : ℕ}
    {g : Z → Fin n → X} (hg : Continuous g) :
    Continuous fun z => (mk (g z) : JamesReducedProduct X x₀) :=
  continuous_from_uCompactlyGeneratedSpace _ fun S h =>
    continuous_iff.1 continuous_id n S ⟨g ∘ h, hg.comp h.continuous⟩

/-- The James reduced product is compactly generated. -/
instance : UCompactlyGeneratedSpace.{u} (JamesReducedProduct X x₀) :=
  uCompactlyGeneratedSpace_of_isOpen fun _ hs => isOpen_iff.2 fun _ S g =>
    hs S ⟨_, continuous_mk g.continuous⟩

/-- The letters of a compactly generated space depend continuously on the point. -/
@[fun_prop]
theorem continuous_letter [CompactlyGeneratedSpace X] :
    Continuous (letter : X → JamesReducedProduct X x₀) := by
  simpa only [mk_fin_one] using
    continuous_mk (x₀ := x₀) (g := fun (x : X) (_ : Fin 1) => x) (by fun_prop)

/-- The letters `X → J X` of a compactly generated space form a topological embedding. -/
theorem isEmbedding_letter [CompactlyGeneratedSpace X] :
    IsEmbedding (letter : X → JamesReducedProduct X x₀) := by
  refine ⟨⟨le_antisymm continuous_letter.le_induced fun U hU => ?_⟩, letter_injective⟩
  rw [isOpen_induced_iff]
  by_cases h₀ : x₀ ∈ U
  · -- The reduced words all of whose letters lie in `U`.
    let V : Set (JamesReducedProduct X x₀) := {w | ∀ a ∈ (freeMonoidEquiv X x₀ w).toList, ↑a ∈ U}
    have hV {n : ℕ} (v : Fin n → X) : mk v ∈ V ↔ ∀ i, v i ∈ U := by
      simp only [V, mem_ofPred_eq, mem_toList_freeMonoidEquiv_mk]
      refine ⟨fun hv i => ?_, fun hv a ⟨i, hi⟩ => hi ▸ hv i⟩
      by_cases hi : v i = x₀
      · exact hi ▸ h₀
      · exact hv ⟨v i, hi⟩ ⟨i, rfl⟩
    refine ⟨V, isOpen_iff.2 fun n _ g => ?_, ext fun x => ?_⟩
    · have hpre : (fun t => (mk (g t) : JamesReducedProduct X x₀)) ⁻¹' V =
          g ⁻¹' ⋂ i, (fun v : Fin n → X => v i) ⁻¹' U := ext fun t => by simp [hV]
      rw [hpre]
      exact (isOpen_iInter_of_finite fun i => hU.preimage (continuous_apply i)).preimage
        g.continuous
    · rw [mem_preimage, ← mk_fin_one (x₀ := x₀) (fun _ => x), hV]
      exact ⟨fun hx => hx 0, fun hx _ => hx⟩
  · -- The reduced words some letter of which lies in `U`.
    let V : Set (JamesReducedProduct X x₀) := {w | ∃ a ∈ (freeMonoidEquiv X x₀ w).toList, ↑a ∈ U}
    have hV {n : ℕ} (v : Fin n → X) : mk v ∈ V ↔ ∃ i, v i ∈ U := by
      simp only [V, mem_ofPred_eq, mem_toList_freeMonoidEquiv_mk]
      exact ⟨fun ⟨_, ⟨i, hi⟩, ha⟩ => ⟨i, hi ▸ ha⟩,
        fun ⟨i, hi⟩ => ⟨⟨v i, fun h => h₀ (h ▸ hi)⟩, ⟨i, rfl⟩, hi⟩⟩
    refine ⟨V, isOpen_iff.2 fun n _ g => ?_, ext fun x => ?_⟩
    · have hpre : (fun t => (mk (g t) : JamesReducedProduct X x₀)) ⁻¹' V =
          g ⁻¹' ⋃ i, (fun v : Fin n → X => v i) ⁻¹' U := ext fun t => by simp [hV]
      rw [hpre]
      exact (isOpen_iUnion fun i => hU.preimage (continuous_apply i)).preimage g.continuous
    · rw [mem_preimage, ← mk_fin_one (x₀ := x₀) (fun _ => x), hV]
      exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨0, hx⟩⟩

/-- Left and right translations by a reduced word are continuous. -/
instance : SeparatelyContinuousMul (JamesReducedProduct X x₀) where
  continuous_const_mul {w} := by
    obtain ⟨m, u, rfl⟩ := exists_mk_eq w
    refine continuous_iff.2 fun n S g => ?_
    simp_rw [← mk_append]
    exact continuous_mk ((Fin.continuous_append m n).comp (continuous_const.prodMk g.continuous))
  continuous_mul_const {w} := by
    obtain ⟨m, u, rfl⟩ := exists_mk_eq w
    refine continuous_iff.2 fun n S g => ?_
    simp_rw [← mk_append]
    exact continuous_mk ((Fin.continuous_append n m).comp (g.continuous.prodMk continuous_const))

/-- The words of length `n` whose reduced word lies in `J_r X` form a closed subset of the power
`Xⁿ` when the basepoint is closed. -/
private theorem isClosed_preimage_mk_filtration (h : IsClosed ({x₀} : Set X)) (r n : ℕ) :
    IsClosed (mk ⁻¹' filtration X x₀ r : Set (Fin n → X)) := by
  classical
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

/-- The stages of the word-length filtration are closed when the basepoint is closed. -/
theorem isClosed_filtration (h : IsClosed ({x₀} : Set X)) (r : ℕ) :
    IsClosed (filtration X x₀ r) :=
  isClosed_iff.2 fun n _ g => (isClosed_preimage_mk_filtration h r n).preimage g.continuous

/-- The letters `X → J X` of a compactly generated space with closed basepoint form a closed
embedding, onto the first stage `J₁ X` of the word-length filtration. -/
theorem isClosedEmbedding_letter [CompactlyGeneratedSpace X] (h : IsClosed ({x₀} : Set X)) :
    IsClosedEmbedding (letter : X → JamesReducedProduct X x₀) :=
  ⟨isEmbedding_letter, by rw [← filtration_one]; exact isClosed_filtration h 1⟩

/-- The stages of the word-length filtration are compact when `X` is compact Hausdorff. -/
theorem isCompact_filtration [CompactSpace X] [T2Space X] (r : ℕ) :
    IsCompact (filtration X x₀ r) := by
  rw [← range_mk]
  exact isCompact_range (continuous_mk continuous_id)

/-- The James reduced product of a path-connected space is path-connected. -/
instance [PathConnectedSpace X] : PathConnectedSpace (JamesReducedProduct X x₀) := by
  have hjoined (w : JamesReducedProduct X x₀) : Joined 1 w := by
    obtain ⟨n, v, rfl⟩ := exists_mk_eq w
    obtain ⟨γ⟩ := PathConnectedSpace.joined (fun _ : Fin n => x₀) v
    exact ⟨{ toFun t := mk (γ t)
             continuous_toFun := continuous_mk γ.continuous
             source' := by simp
             target' := by simp }⟩
  exact ⟨⟨1⟩, fun w w' => (hjoined w).symm.trans (hjoined w')⟩

/-! ### The universal property among topological monoids -/

section Lift

variable {M : Type w} [Monoid M] [TopologicalSpace M]

/-- The extensionality lemma `TauCeti.JamesReducedProduct.hom_ext` for continuous monoid
homomorphisms. -/
@[ext]
theorem continuousMonoidHom_ext {f g : JamesReducedProduct X x₀ →ₜ* M}
    (h : ∀ x ≠ x₀, f (letter x) = g (letter x)) : f = g :=
  hom_ext h

variable [ContinuousMul M]

/-- The **universal property** of the James reduced product: a continuous map `g : X → M` to a
topological monoid sending the basepoint to `1` extends to the continuous monoid homomorphism
`J X → M` sending a reduced word `x₁ ⋯ xₙ` to `g x₁ ⋯ g xₙ`. It is the only monoid homomorphism
extending `g` (`TauCeti.JamesReducedProduct.lift_unique`). -/
def lift (g : C(X, M)) (hg : g x₀ = 1) : JamesReducedProduct X x₀ →ₜ* M where
  toMonoidHom := liftMonoidHom g hg
  continuous_toFun := by
    refine continuous_iff.2 fun n S h => ?_
    simp only [MonoidHom.toOneHom_coe, OneHom.toFun_eq_coe, liftMonoidHom_mk, List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ =>
      g.continuous.comp ((continuous_apply i).comp h.continuous)

@[simp]
theorem lift_letter (g : C(X, M)) (hg : g x₀ = 1) (x : X) :
    lift g hg (letter x : JamesReducedProduct X x₀) = g x :=
  liftMonoidHom_letter hg x

@[simp]
theorem lift_mk (g : C(X, M)) (hg : g x₀ = 1) {n : ℕ} (v : Fin n → X) :
    lift g hg (mk v : JamesReducedProduct X x₀) = (List.ofFn fun i => g (v i)).prod :=
  liftMonoidHom_mk hg v

theorem toMonoidHom_lift (g : C(X, M)) (hg : g x₀ = 1) :
    (lift g hg).toMonoidHom = liftMonoidHom (x₀ := x₀) g hg :=
  (rfl)

/-- The uniqueness half of the universal property among topological monoids: `lift g hg` is the
only continuous monoid homomorphism out of `J X` extending `g` along the letters. -/
theorem lift_unique (g : C(X, M)) (hg : g x₀ = 1) {f : JamesReducedProduct X x₀ →ₜ* M}
    (hf : ∀ x ≠ x₀, f (letter x) = g x) : f = lift g hg :=
  hom_ext fun x hx => by rw [hf x hx, lift_letter]

end Lift

/-! ### Functoriality -/

section Map

-- The source and target live in one universe: `J` is a functor on the compactly generated spaces
-- of that universe, tested by the compact Hausdorff spaces of the same universe.
variable {Y : Type u} [TopologicalSpace Y] {y₀ : Y} {Z : Type u} [TopologicalSpace Z] {z₀ : Z}

private theorem liftMonoidHom_letter_comp_mk (f : C(X, Y)) (hf : f x₀ = y₀) {n : ℕ}
    (v : Fin n → X) :
    liftMonoidHom (fun x => (letter (f x) : JamesReducedProduct Y y₀)) (by simp [hf])
      (mk v : JamesReducedProduct X x₀) = mk (f ∘ v) :=
  (liftMonoidHom_mk _ v).trans (mk_def _).symm

/-- The continuous monoid homomorphism `J f : J X → J Y` induced by a based continuous map
`f : X → Y`: it applies `f` to each letter. -/
def map (f : C(X, Y)) (hf : f x₀ = y₀) :
    JamesReducedProduct X x₀ →ₜ* JamesReducedProduct Y y₀ where
  toMonoidHom := liftMonoidHom (fun x => letter (f x)) (by simp [hf])
  continuous_toFun := by
    refine continuous_iff.2 fun n S h => ?_
    simp only [MonoidHom.toOneHom_coe, OneHom.toFun_eq_coe, liftMonoidHom_letter_comp_mk f hf]
    -- The composite is the reduced word of `f ∘ v`, by definition of `mk`.
    exact continuous_mk (continuous_pi fun i =>
      f.continuous.comp ((continuous_apply i).comp h.continuous))

@[simp]
theorem map_letter (f : C(X, Y)) (hf : f x₀ = y₀) (x : X) :
    map f hf (letter x : JamesReducedProduct X x₀) = letter (f x) :=
  liftMonoidHom_letter _ x

@[simp]
theorem map_mk (f : C(X, Y)) (hf : f x₀ = y₀) {n : ℕ} (v : Fin n → X) :
    map f hf (mk v : JamesReducedProduct X x₀) = mk (f ∘ v) :=
  liftMonoidHom_letter_comp_mk f hf v

@[simp]
theorem map_id :
    map (ContinuousMap.id X) rfl = ContinuousMonoidHom.id (JamesReducedProduct X x₀) :=
  hom_ext fun _ _ => map_letter _ _ _

theorem map_comp (g : C(Y, Z)) (hg : g y₀ = z₀) (f : C(X, Y)) (hf : f x₀ = y₀) :
    map (g.comp f) (by rw [ContinuousMap.comp_apply, hf, hg]) =
      (map g hg).comp (map f hf : JamesReducedProduct X x₀ →ₜ* JamesReducedProduct Y y₀) :=
  hom_ext fun _ _ => by simp

theorem length_map_le (f : C(X, Y)) (hf : f x₀ = y₀) (w : JamesReducedProduct X x₀) :
    length (map f hf w) ≤ length w := by
  classical
  obtain ⟨n, v, rfl⟩ := exists_mk_eq w
  rw [map_mk, length_mk, length_mk]
  refine Finset.card_le_card fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ i, fun h => ?_⟩
  exact (Finset.mem_filter.1 hi).2 (by rw [Function.comp_apply, h, hf])

/-- The homomorphism `map f hf` induced by a based continuous map preserves each stage `J_r` of
the word-length filtration. -/
theorem mapsTo_map_filtration (f : C(X, Y)) (hf : f x₀ = y₀) (r : ℕ) :
    MapsTo (map f hf) (filtration X x₀ r) (filtration Y y₀ r) :=
  fun w hw => (length_map_le f hf w).trans hw

end Map

end Topology

end JamesReducedProduct

end TauCeti

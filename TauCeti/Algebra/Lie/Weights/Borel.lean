/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Character
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.LinearPMap
public import TauCeti.Algebra.Lie.Weights.Span
public import TauCeti.LinearAlgebra.RootSystem.Positive

/-!
# The nilradicals and the Borel subalgebra of a positive system

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero, and let `H` be a splitting Cartan subalgebra, so that
`LieAlgebra.IsKilling.rootSystem H` is the root system of `L` relative to `H`. A base `b` of that
root system singles out the positive roots, and this file builds the three subalgebras the base
determines: the positive nilradical `n⁺ = ⨁_{α > 0} Lα`, the negative nilradical
`n⁻ = ⨁_{α < 0} Lα`, and the Borel subalgebra `𝔟 = H + n⁺`.

Everything rests on one observation, isolated as `TauCeti.rootSpaceSubalgebra`: a special closed
set `S` of roots spans a Lie subalgebra, because `⁅Lα, Lβ⁆ ≤ L(α + β)`. Being closed under sums is
what puts the bracket back in the span when `α + β` is a root, and containing no opposite pair is
what rules out `α + β = 0`, whose weight space is the Cartan subalgebra rather than a root space.
The positive roots and the negative roots are two such sets, by the additivity of the height
function.

## Main definitions

* `TauCeti.rootSpaceSpan H S`: the `H`-submodule of `L` spanned by the root spaces indexed by a set
  `S` of roots, the instance of `TauCeti.genWeightSpaceSpan` at `M = L`.
* `TauCeti.IsSpecialClosedRootSet H S`: `S` is stable under those sums of its members that are
  again roots, and contains no root together with its negative.
* `TauCeti.rootSpaceSubalgebra H S hS`: the span of a special closed set of roots, as a Lie
  subalgebra.
* `TauCeti.positiveNilradical H b`, `TauCeti.negativeNilradical H b`: the nilradicals `n⁺` and `n⁻`
  of the positive system determined by a base `b`.
* `TauCeti.borelSubalgebra H b`: the Borel subalgebra `𝔟 = H + n⁺`.
* `TauCeti.borelCharacter H b lam`: the character `h + n ↦ lam h` of `𝔟`, for a linear form `lam`
  on `H`.

## Main results

* `TauCeti.rootSpaceSpan_le_iff` and `TauCeti.rootSpaceSubalgebra_le_iff` are the universal property
  of the span: it is contained in a given submodule, resp. Lie subalgebra, exactly when each of the
  root spaces it is spanned by is. `TauCeti.positiveNilradical_le_iff` and
  `TauCeti.negativeNilradical_le_iff` are its two specialisations to the nilradicals.
* `TauCeti.mem_positiveNilradical_of_mem_rootSpace` and
  `TauCeti.mem_negativeNilradical_of_mem_rootSpace` say the nilradicals contain the root spaces
  they are built from.
* `TauCeti.neg_mem_posRoots_of_mem_negRoots` and `TauCeti.neg_mem_negRoots_of_mem_posRoots` say
  that negation exchanges negative and positive roots.
* `TauCeti.borelSubalgebra_eq_sup`: the Borel subalgebra is the join `H ⊔ n⁺`.
* `TauCeti.le_borelSubalgebra` and `TauCeti.positiveNilradical_le_borelSubalgebra` are the two
  inclusions `H ≤ 𝔟` and `n⁺ ≤ 𝔟`.
* `TauCeti.lie_mem_positiveNilradical_of_mem_borelSubalgebra`: `⁅𝔟, n⁺⁆ ≤ n⁺`, so `n⁺` is a Lie
  ideal of `𝔟`.
* `TauCeti.lie_mem_positiveNilradical_of_mem_borelSubalgebra_of_mem_borelSubalgebra`:
  `⁅𝔟, 𝔟⁆ ≤ n⁺`, since the Cartan subalgebra is abelian.
* `TauCeti.negativeNilradical_sup_borelSubalgebra_eq_top`: the triangular decomposition
  `L = n⁻ + (H + n⁺)`, as an equality of submodules.
* `TauCeti.exists_mem_negativeNilradical_add_mem_borelSubalgebra`: the corresponding elementwise
  decomposition.
* `TauCeti.disjoint_cartan_positiveNilradical`: `H ∩ n⁺ = 0`, so `𝔟 = H ⊕ n⁺`.
* `TauCeti.borelCharacter_apply_of_mem_cartan` and
  `TauCeti.borelCharacter_apply_of_mem_positiveNilradical`: the character of weight `lam` is `lam`
  on `H` and vanishes on `n⁺`.

## Implementation notes

The nilradicals are built through `TauCeti.rootSpaceSpan`, which is valued in `LieSubmodule K H L`
rather than in `Submodule K L`: the root spaces are `H`-submodules by construction, so this records
for free that `⁅H, n⁺⁆ ≤ n⁺`, which is exactly what makes `H + n⁺` a subalgebra. Only the carrier
of a Lie subalgebra is a plain submodule, so the passage to `Submodule K L` happens at the last
moment, in `TauCeti.rootSpaceSubalgebra` and `TauCeti.borelSubalgebra`.

The root space product `⁅Lα, Lβ⁆ ≤ L(α + β)` enters the file only through
`TauCeti.lie_mem_rootSpaceSpan`; everything else about the bracket is derived from that lemma.

The two nilradicals are *not* obtained from one another by a symmetry of the base, Mathlib's
`RootPairing.Base` having no negation; instead both are instances of `TauCeti.rootSpaceSubalgebra`,
the negative case running the positive one through root negation, in the form of the self
reflection `P.reflectionPerm i i`.

## References

This file supplies the "Borel and the nilradicals" item of Layer 3 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, whose target signatures
`positiveNilradical`, `negativeNilradical` and `borelSubalgebra` are pinned in the accompanying
`Suggested.lean`. They are the subalgebras the Verma module `U(L) ⊗_{U(𝔟)} Kλ` of that layer is
induced from.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §10.1.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-! ### Spans of root spaces -/

/-- The `H`-submodule of `L` spanned by the root spaces indexed by a set `S` of roots: the weight
spaces of `L` itself at the weights the members of `S` name. -/
def rootSpaceSpan (S : Set H.root) : LieSubmodule K H L :=
  genWeightSpaceSpan H L ((fun α : H.root => (α : H → K)) '' S)

variable {H}

omit [IsKilling K L] [IsTriangularizable K H L] in
/-- A root space indexed by a member of `S` lies in the span of `S`. -/
theorem rootSpace_le_rootSpaceSpan {S : Set H.root} {α : H.root} (hα : α ∈ S) :
    rootSpace H (α : H → K) ≤ rootSpaceSpan H S :=
  genWeightSpace_le_genWeightSpaceSpan (Set.mem_image_of_mem _ hα)

omit [IsKilling K L] [IsTriangularizable K H L] in
/-- The span of the root spaces indexed by `S`, written as the supremum of those root spaces. -/
theorem rootSpaceSpan_eq_iSup (S : Set H.root) :
    rootSpaceSpan H S = ⨆ α : S, rootSpace H ((α : H.root) : H → K) := by
  refine le_antisymm (genWeightSpaceSpan_le_iff.mpr ?_) (iSup_le fun α => ?_)
  · rintro _ ⟨α, hα, rfl⟩
    exact le_iSup (fun β : S => rootSpace H ((β : H.root) : H → K)) ⟨α, hα⟩
  · exact rootSpace_le_rootSpaceSpan α.2

omit [IsKilling K L] [IsTriangularizable K H L] in
/-- Spans of root spaces are monotone in the indexing set. -/
theorem rootSpaceSpan_mono {S T : Set H.root} (h : S ⊆ T) :
    rootSpaceSpan H S ≤ rootSpaceSpan H T :=
  genWeightSpaceSpan_mono (Set.image_mono h)

omit [IsKilling K L] [IsTriangularizable K H L] in
/-- The span of the root spaces indexed by `S` is contained in an `H`-submodule exactly when each
of the root spaces it is spanned by is. -/
theorem rootSpaceSpan_le_iff {S : Set H.root} {N : LieSubmodule K H L} :
    rootSpaceSpan H S ≤ N ↔ ∀ α ∈ S, rootSpace H (α : H → K) ≤ N :=
  ⟨fun h _ hα => (rootSpace_le_rootSpaceSpan hα).trans h,
    fun h => genWeightSpaceSpan_le_iff.mpr (by rintro _ ⟨α, hα, rfl⟩; exact h α hα)⟩

omit [IsKilling K L] [IsTriangularizable K H L] in
/-- The span of the root spaces indexed by `S` is closed under the bracket as soon as the root
space of the sum of any two members of `S` lies back inside it. -/
theorem lie_mem_rootSpaceSpan {S : Set H.root}
    (hS : ∀ α ∈ S, ∀ β ∈ S,
      rootSpace H ((α : H → K) + (β : H → K)) ≤ rootSpaceSpan H S)
    {x y : L} (hx : x ∈ rootSpaceSpan H S) (hy : y ∈ rootSpaceSpan H S) :
    ⁅x, y⁆ ∈ rootSpaceSpan H S := by
  rw [rootSpaceSpan_eq_iSup] at hx hy
  refine LieSubmodule.iSup_induction (motive := fun x => ⁅x, y⁆ ∈ rootSpaceSpan H S) _ hx
    (fun α x hx => ?_) (by simp) (fun x z hx hz => by rw [add_lie]; exact add_mem hx hz)
  refine LieSubmodule.iSup_induction (motive := fun y => ⁅x, y⁆ ∈ rootSpaceSpan H S) _ hy
    (fun β y hy => ?_) (by simp) (fun y z hy hz => by rw [lie_add]; exact add_mem hy hz)
  exact hS α α.2 β β.2 (lie_mem_genWeightSpace_of_mem_genWeightSpace hx hy)

/-! ### Special closed sets of roots -/

variable (H) in
/-- A set `S` of roots is **special closed** when it is *closed*, that is stable under those sums
of its members that are again roots, and moreover contains no root together with its negative.

The second condition is what the first one alone does not give: without it the sum `α + (-α) = 0`
would contribute the zero weight space, which is the Cartan subalgebra and not a root space, and
the span of `S` would not be closed under the bracket. -/
structure IsSpecialClosedRootSet (S : Set H.root) : Prop where
  /-- A root that is the sum of two members of `S` is again a member of `S`. -/
  add_mem : ∀ α ∈ S, ∀ β ∈ S, ∀ k : H.root,
    (IsKilling.rootSystem H).root k =
      (IsKilling.rootSystem H).root α + (IsKilling.rootSystem H).root β → k ∈ S
  /-- No member of `S` has its negative in `S`. -/
  reflectionPerm_self_notMem : ∀ α ∈ S, (IsKilling.rootSystem H).reflectionPerm α α ∉ S

/-- The root space of the sum of two members of a special closed set of roots lies in the span of
that set. -/
theorem rootSpace_add_le_rootSpaceSpan {S : Set H.root} (hS : IsSpecialClosedRootSet H S)
    {α β : H.root} (hα : α ∈ S) (hβ : β ∈ S) :
    rootSpace H ((α : H → K) + (β : H → K)) ≤ rootSpaceSpan H S := by
  rcases eq_or_ne (rootSpace H ((α : H → K) + (β : H → K))) ⊥ with h | h
  · rw [h]; exact bot_le
  -- The sum is a weight; it is nonzero, since `α = -β` would put an opposite pair inside `S`.
  have hne : (⟨(α : H → K) + (β : H → K), h⟩ : Weight K H L).IsNonZero := by
    intro hzero
    have hroot : (IsKilling.rootSystem H).root α = -(IsKilling.rootSystem H).root β := by
      ext x
      have hx := congrFun hzero x
      simp only [Weight.coe_weight_mk, Pi.add_apply, Pi.zero_apply,
        Weight.toLinear_apply] at hx
      simp only [IsKilling.rootSystem_root_apply, LinearMap.neg_apply, Weight.toLinear_apply]
      linear_combination hx
    rw [RootPairing.root_eq_neg_iff] at hroot
    exact hS.reflectionPerm_self_notMem β hβ (hroot ▸ hα)
  set k : H.root := ⟨⟨(α : H → K) + (β : H → K), h⟩, by simpa [LieSubalgebra.root] using hne⟩
    with hk_def
  have hk : (IsKilling.rootSystem H).root k =
      (IsKilling.rootSystem H).root α + (IsKilling.rootSystem H).root β := by
    ext x
    simp [hk_def]
  exact rootSpace_le_rootSpaceSpan (S := S) (α := k) (hS.add_mem α hα β hβ k hk)

variable (b : (IsKilling.rootSystem H).Base)

/-- Negating a negative root gives a positive root. -/
theorem neg_mem_posRoots_of_mem_negRoots {i : H.root}
    (hi : i ∈ negRoots (IsKilling.rootSystem H) b) :
    -i ∈ posRoots (IsKilling.rootSystem H) b := by
  rw [← IsKilling.rootSystem_reflectionPerm_self_eq_neg i]
  exact (reflectionPerm_self_mem_posRoots_iff_mem_negRoots
    (IsKilling.rootSystem H) b i).mpr hi

/-- Negating a positive root gives a negative root. -/
theorem neg_mem_negRoots_of_mem_posRoots {i : H.root}
    (hi : i ∈ posRoots (IsKilling.rootSystem H) b) :
    -i ∈ negRoots (IsKilling.rootSystem H) b := by
  rw [← IsKilling.rootSystem_reflectionPerm_self_eq_neg i]
  exact (reflectionPerm_self_mem_negRoots_iff_mem_posRoots
    (IsKilling.rootSystem H) b i).mpr hi

/-- The positive roots are a special closed set of roots: heights add, and a positive root never
has a positive negative. -/
theorem isSpecialClosedRootSet_posRoots :
    IsSpecialClosedRootSet H (posRoots (IsKilling.rootSystem H) b) where
  add_mem _ hα _ hβ _ hk := add_mem_posRoots _ b hα hβ hk
  reflectionPerm_self_notMem _ hα := reflectionPerm_self_notMem_posRoots _ b hα

/-- The negative roots are a special closed set of roots. -/
theorem isSpecialClosedRootSet_negRoots :
    IsSpecialClosedRootSet H (negRoots (IsKilling.rootSystem H) b) where
  add_mem _ hα _ hβ _ hk := add_mem_negRoots _ b hα hβ hk
  reflectionPerm_self_notMem _ hα := reflectionPerm_self_notMem_negRoots _ b hα

variable (H) in
/-- The span of the root spaces indexed by a special closed set `S` of roots, as a Lie subalgebra
of `L`. -/
def rootSpaceSubalgebra (S : Set H.root) (hS : IsSpecialClosedRootSet H S) : LieSubalgebra K L where
  __ := (rootSpaceSpan H S : Submodule K L)
  lie_mem' hx hy :=
    lie_mem_rootSpaceSpan (fun _ hα _ hβ => rootSpace_add_le_rootSpaceSpan hS hα hβ) hx hy

@[simp]
theorem mem_rootSpaceSubalgebra {S : Set H.root} (hS : IsSpecialClosedRootSet H S) (x : L) :
    x ∈ rootSpaceSubalgebra H S hS ↔ x ∈ rootSpaceSpan H S :=
  Iff.rfl

/-- The carrier of the Lie subalgebra spanned by a special closed set `S` of roots is the span of
the root spaces indexed by `S`; the bracket-closure the definition supplies costs the carrier
nothing. -/
theorem rootSpaceSubalgebra_toSubmodule {S : Set H.root} (hS : IsSpecialClosedRootSet H S) :
    (rootSpaceSubalgebra H S hS : Submodule K L) = (rootSpaceSpan H S : Submodule K L) :=
  SetLike.ext fun _ => Iff.rfl

/-- The Lie subalgebra spanned by a special closed set `S` of roots is contained in a Lie
subalgebra `K'` exactly when each of the root spaces indexed by `S` is. -/
theorem rootSpaceSubalgebra_le_iff {S : Set H.root} (hS : IsSpecialClosedRootSet H S)
    {K' : LieSubalgebra K L} :
    rootSpaceSubalgebra H S hS ≤ K' ↔ ∀ α ∈ S, ∀ x ∈ rootSpace H (α : H → K), x ∈ K' := by
  refine ⟨fun h α hα _ hx => h (rootSpace_le_rootSpaceSpan hα hx), fun h => ?_⟩
  rw [← LieSubalgebra.toSubmodule_le_toSubmodule, rootSpaceSubalgebra_toSubmodule,
    rootSpaceSpan_eq_iSup, LieSubmodule.iSup_toSubmodule]
  exact iSup_le fun α => h α α.2

/-! ### The nilradicals and the Borel subalgebra -/

variable (H)

/-- The **positive nilradical** `n⁺ = ⨁_{α > 0} Lα` of the positive system determined by `b`. -/
def positiveNilradical : LieSubalgebra K L :=
  rootSpaceSubalgebra H _ (isSpecialClosedRootSet_posRoots b)

/-- The **negative nilradical** `n⁻ = ⨁_{α < 0} Lα` of the positive system determined by `b`. -/
def negativeNilradical : LieSubalgebra K L :=
  rootSpaceSubalgebra H _ (isSpecialClosedRootSet_negRoots b)

@[simp]
theorem mem_positiveNilradical (x : L) :
    x ∈ positiveNilradical H b ↔ x ∈ rootSpaceSpan H (posRoots (IsKilling.rootSystem H) b) :=
  Iff.rfl

@[simp]
theorem mem_negativeNilradical (x : L) :
    x ∈ negativeNilradical H b ↔ x ∈ rootSpaceSpan H (negRoots (IsKilling.rootSystem H) b) :=
  Iff.rfl

/-- The positive nilradical contains the root space of every positive root. -/
theorem mem_positiveNilradical_of_mem_rootSpace {α : H.root}
    (hα : α ∈ posRoots (IsKilling.rootSystem H) b) {x : L}
    (hx : x ∈ rootSpace H (α : H → K)) : x ∈ positiveNilradical H b :=
  rootSpace_le_rootSpaceSpan (S := posRoots (IsKilling.rootSystem H) b) hα hx

/-- The negative nilradical contains the root space of every negative root. -/
theorem mem_negativeNilradical_of_mem_rootSpace {α : H.root}
    (hα : α ∈ negRoots (IsKilling.rootSystem H) b) {x : L}
    (hx : x ∈ rootSpace H (α : H → K)) : x ∈ negativeNilradical H b :=
  rootSpace_le_rootSpaceSpan (S := negRoots (IsKilling.rootSystem H) b) hα hx

/-- The positive nilradical is contained in a Lie subalgebra `K'` exactly when the root space of
every positive root is. -/
theorem positiveNilradical_le_iff {K' : LieSubalgebra K L} :
    positiveNilradical H b ≤ K' ↔
      ∀ α ∈ posRoots (IsKilling.rootSystem H) b, ∀ x ∈ rootSpace H (α : H → K), x ∈ K' :=
  rootSpaceSubalgebra_le_iff (isSpecialClosedRootSet_posRoots b)

/-- The negative nilradical is contained in a Lie subalgebra `K'` exactly when the root space of
every negative root is. -/
theorem negativeNilradical_le_iff {K' : LieSubalgebra K L} :
    negativeNilradical H b ≤ K' ↔
      ∀ α ∈ negRoots (IsKilling.rootSystem H) b, ∀ x ∈ rootSpace H (α : H → K), x ∈ K' :=
  rootSpaceSubalgebra_le_iff (isSpecialClosedRootSet_negRoots b)

/-- The sum of the Cartan subalgebra and the positive nilradical is closed under the bracket: the
Cartan preserves each root space, and the positive root spaces bracket into one another. -/
private theorem lie_mem_sup_positiveNilradical {x y : L}
    (hx : x ∈ (H : Submodule K L) ⊔ (positiveNilradical H b : Submodule K L))
    (hy : y ∈ (H : Submodule K L) ⊔ (positiveNilradical H b : Submodule K L)) :
    ⁅x, y⁆ ∈ (H : Submodule K L) ⊔ (positiveNilradical H b : Submodule K L) := by
  rw [Submodule.mem_sup] at hx hy ⊢
  obtain ⟨u, hu, m, hm, rfl⟩ := hx
  obtain ⟨v, hv, n, hn, rfl⟩ := hy
  refine ⟨⁅u, v⁆, H.lie_mem hu hv, ⁅u, n⁆ + (⁅m, v⁆ + ⁅m, n⁆), ?_, by
    simp only [lie_add, add_lie]; abel⟩
  refine add_mem ?_ (add_mem ?_ ?_)
  · exact LieSubmodule.lie_mem _ (x := (⟨u, hu⟩ : H)) hn
  · rw [← lie_skew]
    exact neg_mem (LieSubmodule.lie_mem _ (x := (⟨v, hv⟩ : H)) hm)
  · exact (positiveNilradical H b).lie_mem hm hn

/-- The **Borel subalgebra** `𝔟 = H + n⁺` of the positive system determined by `b`.

It is a subalgebra because `H` is one, because `⁅H, n⁺⁆ ≤ n⁺` — the root spaces being
`H`-submodules — and because `n⁺` is one. -/
def borelSubalgebra : LieSubalgebra K L where
  __ := (H : Submodule K L) ⊔ (positiveNilradical H b : Submodule K L)
  lie_mem' hx hy := lie_mem_sup_positiveNilradical H b hx hy

/-- The carrier of the Borel subalgebra is the submodule sum `H + n⁺`; no closure is needed. This
is the concrete description the construction supplies, `TauCeti.mem_borelSubalgebra` being the
canonical membership criterion. -/
theorem borelSubalgebra_toSubmodule :
    (borelSubalgebra H b : Submodule K L)
      = (H : Submodule K L) ⊔ (positiveNilradical H b : Submodule K L) :=
  SetLike.ext fun _ => Iff.rfl

/-- The Cartan subalgebra is contained in the Borel subalgebra. -/
theorem le_borelSubalgebra : H ≤ borelSubalgebra H b :=
  fun _ hx => Submodule.mem_sup_left hx

/-- The positive nilradical is contained in the Borel subalgebra. -/
theorem positiveNilradical_le_borelSubalgebra :
    positiveNilradical H b ≤ borelSubalgebra H b :=
  fun _ hx => Submodule.mem_sup_right hx

/-- The Borel subalgebra is the join `H ⊔ n⁺` of the Cartan subalgebra and the positive nilradical
in the lattice of Lie subalgebras: no closure is needed, the submodule sum `H + n⁺` being already
a Lie subalgebra. -/
theorem borelSubalgebra_eq_sup : borelSubalgebra H b = H ⊔ positiveNilradical H b := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le (le_borelSubalgebra H b) (positiveNilradical_le_borelSubalgebra H b))
  rw [← LieSubalgebra.mem_toSubmodule, borelSubalgebra_toSubmodule, Submodule.mem_sup] at hx
  obtain ⟨u, hu, m, hm, rfl⟩ := hx
  exact add_mem (le_sup_left (a := H) hu) (le_sup_right (a := H) hm)

@[simp]
theorem mem_borelSubalgebra (x : L) :
    x ∈ borelSubalgebra H b ↔ x ∈ H ⊔ positiveNilradical H b := by
  rw [borelSubalgebra_eq_sup]

/-- The positive nilradical is a Lie ideal of the Borel subalgebra: `⁅𝔟, n⁺⁆ ≤ n⁺`. -/
theorem lie_mem_positiveNilradical_of_mem_borelSubalgebra {x y : L}
    (hx : x ∈ borelSubalgebra H b) (hy : y ∈ positiveNilradical H b) :
    ⁅x, y⁆ ∈ positiveNilradical H b := by
  rw [← LieSubalgebra.mem_toSubmodule, borelSubalgebra_toSubmodule, Submodule.mem_sup] at hx
  obtain ⟨u, hu, m, hm, rfl⟩ := hx
  rw [add_lie]
  exact add_mem (LieSubmodule.lie_mem _ (x := (⟨u, hu⟩ : H)) hy)
    ((positiveNilradical H b).lie_mem hm hy)

/-- The bracket of two elements of the Borel subalgebra lies in the positive nilradical:
`⁅𝔟, 𝔟⁆ ≤ n⁺`, the Cartan subalgebra being abelian. -/
theorem lie_mem_positiveNilradical_of_mem_borelSubalgebra_of_mem_borelSubalgebra
    {x y : L} (hx : x ∈ borelSubalgebra H b) (hy : y ∈ borelSubalgebra H b) :
    ⁅x, y⁆ ∈ positiveNilradical H b := by
  rw [← LieSubalgebra.mem_toSubmodule, borelSubalgebra_toSubmodule, Submodule.mem_sup] at hy
  obtain ⟨h, hh, n, hn, rfl⟩ := hy
  rw [lie_add, ← lie_skew x h]
  refine add_mem (neg_mem ?_) (lie_mem_positiveNilradical_of_mem_borelSubalgebra H b hx hn)
  rw [← LieSubalgebra.mem_toSubmodule, borelSubalgebra_toSubmodule, Submodule.mem_sup] at hx
  obtain ⟨h', hh', n', hn', rfl⟩ := hx
  have hab : ⁅(⟨h, hh⟩ : H), (⟨h', hh'⟩ : H)⁆ = 0 := trivial_lie_zero _ _ _ _
  rw [lie_add]
  refine add_mem ?_ (lie_mem_positiveNilradical_of_mem_borelSubalgebra H b
    (le_borelSubalgebra H b hh) hn')
  have hcoe := congrArg Subtype.val hab
  simp only [LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero] at hcoe
  rw [hcoe]
  exact zero_mem _

/-! ### The triangular decomposition -/

/-- Every root space lies in `n⁻ + 𝔟`: a positive root contributes to the Borel subalgebra and a
negative one to the negative nilradical. -/
private theorem rootSpace_le_negativeNilradical_sup_borelSubalgebra (α : H.root) :
    (rootSpace H (α : H → K) : Submodule K L) ≤
      (negativeNilradical H b : Submodule K L) ⊔ (borelSubalgebra H b : Submodule K L) := by
  intro x hx
  by_cases hα : α ∈ posRoots (IsKilling.rootSystem H) b
  · exact Submodule.mem_sup_right (positiveNilradical_le_borelSubalgebra H b
      (mem_positiveNilradical_of_mem_rootSpace H b hα hx))
  · exact Submodule.mem_sup_left (mem_negativeNilradical_of_mem_rootSpace H b
      ((not_mem_posRoots_iff_mem_negRoots _ b α).mp hα) hx)

/-- **The triangular decomposition** `L = n⁻ + (H + n⁺)`: the negative nilradical and the Borel
subalgebra together span `L`. This is the spanning half of `L = n⁻ ⊕ H ⊕ n⁺`, and it is exactly
what the root space decomposition of `L` supplies. -/
@[simp]
theorem negativeNilradical_sup_borelSubalgebra_eq_top :
    (negativeNilradical H b : Submodule K L) ⊔ (borelSubalgebra H b : Submodule K L) = ⊤ := by
  refine top_le_iff.mp ?_
  have htop : ((⊤ : LieSubmodule K H L) : Submodule K L) ≤
      (negativeNilradical H b : Submodule K L) ⊔ (borelSubalgebra H b : Submodule K L) := by
    rw [← LieModule.iSup_genWeightSpace_eq_top' K H L, LieSubmodule.iSup_toSubmodule]
    refine iSup_le fun χ => ?_
    by_cases hχ : χ.IsNonZero
    · exact rootSpace_le_negativeNilradical_sup_borelSubalgebra H b
        ⟨χ, by simpa [LieSubalgebra.root] using hχ⟩
    · rw [not_not] at hχ
      refine le_trans (le_of_eq ?_) (le_sup_of_le_right (le_borelSubalgebra H b))
      rw [hχ.eq]
      exact (congrArg LieSubmodule.toSubmodule (LieAlgebra.rootSpace_zero_eq K L H)).trans
        H.coe_toLieSubmodule
  simpa using htop

/-- **The triangular decomposition, as a splitting of an element of `L`**: every `x : L` is the sum
of an element of the negative nilradical and an element of the Borel subalgebra. -/
theorem exists_mem_negativeNilradical_add_mem_borelSubalgebra (x : L) :
    ∃ g ∈ negativeNilradical H b, ∃ y ∈ borelSubalgebra H b, g + y = x := by
  refine Submodule.mem_sup.mp ?_
  rw [negativeNilradical_sup_borelSubalgebra_eq_top]
  trivial

/-! ### The characters of the Borel subalgebra -/

/-- **The Cartan subalgebra meets the positive nilradical trivially**: `H` is the root space of
the zero weight, and the root spaces are independent. -/
theorem disjoint_cartan_positiveNilradical :
    Disjoint (H : Submodule K L) (positiveNilradical H b : Submodule K L) := by
  have h0 : (0 : H → K) ∉
      (fun α : H.root ↦ (α : H → K)) '' posRoots (IsKilling.rootSystem H) b := by
    rintro ⟨α, -, hα⟩
    exact (Finset.mem_filter.mp α.2).2 hα
  have hdisj :
      Disjoint (rootSpace H 0) (rootSpaceSpan H (posRoots (IsKilling.rootSystem H) b)) := by
    refine ((iSupIndep_genWeightSpace K H L).disjoint_biSup h0).mono_right ?_
    rw [rootSpaceSpan_eq_iSup]
    exact iSup_le fun α ↦ le_biSup (fun χ : H → K ↦ genWeightSpace L χ) ⟨α, α.2, rfl⟩
  rw [← LieSubmodule.disjoint_toSubmodule, rootSpace_zero_eq K L H, H.coe_toLieSubmodule] at hdisj
  exact hdisj.mono_right fun x hx ↦ (mem_positiveNilradical H b x).mp hx

attribute [local instance 100] LieRing.ofAssociativeRing

variable (lam : Dual K H)

/-- The partial linear map on `L` with domain `H + n⁺`, equal to `lam` on `H` and to `0` on
`n⁺`. -/
private noncomputable def borelPMap : L →ₗ.[K] K :=
  LinearPMap.sup ⟨(H : Submodule K L), lam⟩ ⟨(positiveNilradical H b : Submodule K L), 0⟩
    (LinearPMap.sup_h_of_disjoint _ _ (disjoint_cartan_positiveNilradical H b))

private theorem borelPMap_apply (x : (borelPMap H b lam).domain) (h : H)
    (n : positiveNilradical H b) (hx : (h : L) + n = x) :
    borelPMap H b lam x = lam h :=
  (LinearPMap.sup_apply _ (f := ⟨(H : Submodule K L), lam⟩)
    (g := ⟨(positiveNilradical H b : Submodule K L), 0⟩) h n x hx).trans (by simp)

/-- The **character of the Borel subalgebra of weight `lam`**: the linear form `h + n ↦ lam h` on
`𝔟 = H + n⁺`. It is a Lie algebra homomorphism to `K` because `⁅𝔟, 𝔟⁆ ≤ n⁺`, and it is the
character of the one-dimensional `𝔟`-module `K_lam` from which the Verma module of weight `lam`
is induced. -/
noncomputable def borelCharacter : LieCharacter K (borelSubalgebra H b) where
  toLinearMap := (borelPMap H b lam).toFun ∘ₗ
    (LinearEquiv.ofEq _ _ (borelSubalgebra_toSubmodule H b)).toLinearMap
  map_lie' {x y} := by
    rw [LieRing.of_associative_ring_bracket, mul_comm, sub_self]
    exact borelPMap_apply H b lam _ 0 ⟨⁅x, y⁆,
      lie_mem_positiveNilradical_of_mem_borelSubalgebra_of_mem_borelSubalgebra H b x.2 y.2⟩
      (zero_add _) |>.trans (map_zero lam)

private theorem borelCharacter_eq_borelPMap (x : borelSubalgebra H b) :
    borelCharacter H b lam x = borelPMap H b lam ⟨x, x.2⟩ :=
  (rfl)

/-- The character of weight `lam` restricts to `lam` on the Cartan subalgebra. -/
@[simp]
theorem borelCharacter_apply_of_mem_cartan {x : borelSubalgebra H b} (hx : (x : L) ∈ H) :
    borelCharacter H b lam x = lam ⟨x, hx⟩ := by
  rw [borelCharacter_eq_borelPMap]
  exact borelPMap_apply H b lam _ ⟨x, hx⟩ 0 (add_zero _)

/-- The character of weight `lam` vanishes on the positive nilradical. -/
@[simp]
theorem borelCharacter_apply_of_mem_positiveNilradical {x : borelSubalgebra H b}
    (hx : (x : L) ∈ positiveNilradical H b) : borelCharacter H b lam x = 0 := by
  rw [borelCharacter_eq_borelPMap]
  exact (borelPMap_apply H b lam _ 0 ⟨x, hx⟩ (zero_add _)).trans (map_zero lam)

end TauCeti

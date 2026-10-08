/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.C.Model
import TauCeti.Algebra.Group.Submonoid.Telescoping
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

/-!
# The simply connected root datum of type `Cₙ`

This file constructs, uniformly in the rank `n`, the pinned integral root datum of type `Cₙ` on the
character and cocharacter lattices `Fin n → ℤ`. The character lattice is written in the
fundamental-weight basis and the cocharacter lattice in the simple-coroot basis, so the `i`-th
simple root is the `i`-th row of the Bourbaki-numbered Cartan matrix `CartanMatrix.C n` and the
`i`-th simple coroot is the `i`-th standard basis vector. The coordinates themselves, and the
action of a reflection on the signed classical basis vectors `± e_a` out of which every root of
type `Cₙ` is a sum of two, are `TauCeti.DynkinType.TypeC` in the imported model file.

## The roots and their enumeration

A root index `(a, b, s) : Fin n × Fin n × Bool` denotes the pair of signed basis vectors
`p = (a, s)` and `q = (b, s)` with the sign of `q` flipped exactly when `a < b`; equivalently the
root is `(-1) ^ s * (e_a + e_b)` when `b ≤ a`, including the long root when `b = a`, and
`(-1) ^ s * (e_a - e_b)` when `a < b`. Every root arises from exactly one index, and `typeCMk` names
the index belonging to a given pair, which is how the reflected pair is turned back into an index.
`typeCIndexEquiv` encodes a root index as an index of the datum, and `root_typeCIndexEquiv_of_lt`
and its companions read off the root and the coroot there.

The roots are enumerated by `Fin (2 * n ^ 2)` by the first index `a` fastest, so that the first `n`
indices are the simple roots `α₀, …, α_{n-1}` in Bourbaki order, as `root_typeCSimpleIndex`
records. The `b` of the `a`-th simple root is the clamped successor `Order.succ a`, that is
`min (a + 1) (n - 1)`, which is `a + 1` except at the last node, where the simple root is the long
root `2 e_{n-1}`; `Equiv.swap` moves that successor to the first slot of the enumeration.

Only the coroots are asked to span their lattice, and only that half is recorded, in
`corootSpan_typeCSimplyConnectedRootDatum_eq_top`. The roots span the root lattice, which sits
inside the weight lattice with index `2` whenever `0 < n` (Bourbaki, Plate III; at `n = 0` both
lattices are trivial and the index is `1`), so the datum is a `RootDatum` carrying no
`RootPairing.IsRootSystem` instance. That asymmetry is what "simply connected" means here.

## Main definitions

* `TauCeti.DynkinType.typeCSimplyConnectedRootDatum`: the pinned root datum of type `Cₙ`.
* `TauCeti.DynkinType.TypeCIndex` and `TauCeti.DynkinType.typeCIndexEquiv`: the root index
  `(a, b, s)` and its pinned encoding as an index of the datum.
* `TauCeti.DynkinType.typeCSimpleIndex`: the first `n` root indices, the Bourbaki-numbered simple
  roots.
* `TauCeti.DynkinType.typeCSimplyConnectedBase`: the base they form.

## Main results

* `TauCeti.DynkinType.root_typeCIndexEquiv_of_lt` and its four companions: which classical vector
  the root and the coroot of the datum at an encoded index are.
* `TauCeti.DynkinType.root_typeCSimpleIndex` and `TauCeti.DynkinType.coroot_typeCSimpleIndex`: the
  `i`-th simple root is the `i`-th row of `CartanMatrix.C n` and the `i`-th simple coroot is
  `Pi.single i 1`, which is what pins the two lattices as the weight and coroot lattices.
* `TauCeti.DynkinType.mem_support_typeCSimplyConnectedBase`: the support of the pinned base is the
  set of the first `n` root indices.
* `TauCeti.DynkinType.hasCartanType_typeCSimplyConnectedRootDatum`: the pinned base has Cartan type
  `C n`.
* `TauCeti.DynkinType.corootSpan_typeCSimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice, the simply connected condition.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate III, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1.
-/

public section

namespace TauCeti

open Function Set

namespace DynkinType

open TypeC

variable {n : ℕ}

/-! ## The root index type -/

/-- A root index `(a, b, s)` of type `Cₙ`: it denotes the pair of signed basis vectors `(a, s)` and
`(b, s)`, the sign of the second being flipped exactly when `a < b`. Thus the root is
`(-1) ^ s * (e_a + e_b)` when `b ≤ a`, including the long root `(-1) ^ s * 2 e_a` when `b = a`, and
`(-1) ^ s * (e_a - e_b)` when `a < b`. -/
abbrev TypeCIndex (n : ℕ) := Fin n × Fin n × Bool

/-- The first signed basis vector of a root index. -/
private def typeCFst (i : TypeCIndex n) : Signed n := (i.1, i.2.2)

/-- The second signed basis vector of a root index. -/
private def typeCSnd (i : TypeCIndex n) : Signed n :=
  (i.2.1, if i.1 < i.2.1 then !i.2.2 else i.2.2)

private lemma typeCPair_injective :
    Injective (fun i : TypeCIndex n => (typeCFst i, typeCSnd i)) := by
  rintro ⟨a, b, s⟩ ⟨a', b', s'⟩ h
  simp only [typeCFst, typeCSnd, Prod.mk.injEq] at h
  obtain ⟨⟨ha, hs⟩, hb, -⟩ := h
  simp [ha, hb, hs]

private lemma typeCSnd_ne_signedNeg_typeCFst (i : TypeCIndex n) :
    typeCSnd i ≠ signedNeg (typeCFst i) := by
  obtain ⟨a, b, s⟩ := i
  intro hc
  simp only [typeCSnd, typeCFst, signedNeg_mk, Prod.mk.injEq] at hc
  obtain ⟨hba, hs⟩ := hc
  subst hba
  simp at hs

/-- Reading a root index back off its pair of signed basis vectors: the two are exchanged exactly
when the pair is presented in the other order. -/
private lemma typeCPair_swap_eq {i j : TypeCIndex n} (h1 : typeCFst i = typeCSnd j)
    (h2 : typeCSnd i = typeCFst j) : i = j := by
  obtain ⟨a, b, s⟩ := i
  obtain ⟨a', b', s'⟩ := j
  simp only [typeCFst, typeCSnd, Prod.mk.injEq] at h1 h2
  obtain ⟨ha, hs⟩ := h1
  obtain ⟨hb, hs'⟩ := h2
  subst ha
  subst hb
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [ite_eq_left hab] at hs'
    rw [ite_eq_right (not_lt.mpr hab.le)] at hs
    subst hs
    exact absurd hs' (by simp)
  · subst hab
    rw [ite_eq_right (lt_irrefl a)] at hs hs'
    rw [hs]
  · rw [ite_eq_right (not_lt.mpr hab.le)] at hs'
    rw [ite_eq_left hab] at hs
    subst hs'
    exact absurd hs (by simp)

/-- The root of a root index, in fundamental-weight coordinates. -/
private def typeCRoot (i : TypeCIndex n) : Fin n → ℤ := pairRoot (typeCFst i) (typeCSnd i)

/-- The coroot of a root index, in simple-coroot coordinates. -/
private def typeCCoroot (i : TypeCIndex n) : Fin n → ℤ := pairCoroot (typeCFst i) (typeCSnd i)

private lemma typeCFst_mk (a b : Fin n) (s : Bool) :
    typeCFst ((a, b, s) : TypeCIndex n) = (a, s) := rfl

private lemma typeCSnd_mk_of_lt {a b : Fin n} (h : a < b) (s : Bool) :
    typeCSnd ((a, b, s) : TypeCIndex n) = signedNeg (b, s) := by
  simp [typeCSnd, h]

private lemma typeCSnd_mk_of_not_lt {a b : Fin n} (h : ¬ a < b) (s : Bool) :
    typeCSnd ((a, b, s) : TypeCIndex n) = (b, s) := by
  simp [typeCSnd, h]

private lemma typeCRoot_mk_of_lt {a b : Fin n} (h : a < b) (s : Bool) :
    typeCRoot ((a, b, s) : TypeCIndex n) = signedWeight (a, s) - signedWeight (b, s) := by
  rw [typeCRoot, typeCFst_mk, typeCSnd_mk_of_lt h, pairRoot_def, signedWeight_signedNeg]
  exact (sub_eq_add_neg _ _).symm

private lemma typeCRoot_mk_of_not_lt {a b : Fin n} (h : ¬ a < b) (s : Bool) :
    typeCRoot ((a, b, s) : TypeCIndex n) = signedWeight (a, s) + signedWeight (b, s) := by
  rw [typeCRoot, typeCFst_mk, typeCSnd_mk_of_not_lt h, pairRoot_def]

private lemma typeCCoroot_mk_of_lt {a b : Fin n} (h : a < b) (s : Bool) :
    typeCCoroot ((a, b, s) : TypeCIndex n) = signedCoweight (a, s) - signedCoweight (b, s) := by
  have hne : ((a, s) : Signed n) ≠ signedNeg (b, s) := by
    simp [Prod.ext_iff]
  rw [typeCCoroot, typeCFst_mk, typeCSnd_mk_of_lt h, pairCoroot_of_ne hne,
    signedCoweight_signedNeg]
  exact (sub_eq_add_neg _ _).symm

private lemma typeCCoroot_mk_of_gt {a b : Fin n} (h : b < a) (s : Bool) :
    typeCCoroot ((a, b, s) : TypeCIndex n) = signedCoweight (a, s) + signedCoweight (b, s) := by
  have hne : ((a, s) : Signed n) ≠ (b, s) := by
    simp [Prod.ext_iff, h.ne']
  rw [typeCCoroot, typeCFst_mk, typeCSnd_mk_of_not_lt (not_lt.mpr h.le), pairCoroot_of_ne hne]

private lemma typeCCoroot_mk_diag (a : Fin n) (s : Bool) :
    typeCCoroot ((a, a, s) : TypeCIndex n) = signedCoweight (a, s) := by
  rw [typeCCoroot, typeCFst_mk, typeCSnd_mk_of_not_lt (lt_irrefl a), pairCoroot_self]

private lemma typeCRoot_dotProduct_typeCCoroot_self (i : TypeCIndex n) :
    typeCRoot i ⬝ᵥ typeCCoroot i = 2 :=
  pairRoot_dotProduct_pairCoroot_self (typeCSnd_ne_signedNeg_typeCFst i)

/-- The index of the root `x + y`, for a pair of signed basis vectors that are not opposite. -/
private def typeCMk (x y : Signed n) : TypeCIndex n :=
  if x.2 = y.2 then (max x.1 y.1, min x.1 y.1, x.2)
  else if x.1 < y.1 then (x.1, y.1, x.2) else (y.1, x.1, y.2)

private lemma typeCMk_pair {x y : Signed n} (h : y ≠ signedNeg x) :
    (typeCFst (typeCMk x y) = x ∧ typeCSnd (typeCMk x y) = y) ∨
      (typeCFst (typeCMk x y) = y ∧ typeCSnd (typeCMk x y) = x) := by
  obtain ⟨a, s⟩ := x
  obtain ⟨b, t⟩ := y
  by_cases hst : s = t
  · subst hst
    rcases le_or_gt a b with hab | hab
    · have hmk : typeCMk (a, s) (b, s) = (b, a, s) := by
        rw [typeCMk, ite_eq_left rfl, max_eq_right hab, min_eq_left hab]
      refine Or.inr ⟨by rw [hmk]; rfl, ?_⟩
      rw [hmk, typeCSnd, ite_eq_right (not_lt.mpr hab)]
    · have hmk : typeCMk (a, s) (b, s) = (a, b, s) := by
        rw [typeCMk, ite_eq_left rfl, max_eq_left hab.le, min_eq_right hab.le]
      refine Or.inl ⟨by rw [hmk]; rfl, ?_⟩
      rw [hmk, typeCSnd, ite_eq_right (not_lt.mpr hab.le)]
  · have ht : t = !s := by cases s <;> cases t <;> simp_all
    subst ht
    rcases lt_trichotomy a b with hab | hab | hab
    · have hmk : typeCMk (a, s) (b, !s) = (a, b, s) := by
        rw [typeCMk, ite_eq_right hst, ite_eq_left hab]
      refine Or.inl ⟨by rw [hmk]; rfl, ?_⟩
      rw [hmk, typeCSnd, ite_eq_left hab]
    · refine absurd ?_ h
      simp [hab]
    · have hmk : typeCMk (a, s) (b, !s) = (b, a, !s) := by
        rw [typeCMk, ite_eq_right hst, ite_eq_right (not_lt.mpr hab.le)]
      refine Or.inr ⟨by rw [hmk]; rfl, ?_⟩
      rw [hmk, typeCSnd, ite_eq_left hab, Bool.not_not]

private lemma typeCRoot_typeCMk {x y : Signed n} (h : y ≠ signedNeg x) :
    typeCRoot (typeCMk x y) = pairRoot x y := by
  rcases typeCMk_pair h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [typeCRoot, h1, h2]
  exact pairRoot_comm y x

private lemma typeCCoroot_typeCMk {x y : Signed n} (h : y ≠ signedNeg x) :
    typeCCoroot (typeCMk x y) = pairCoroot x y := by
  rcases typeCMk_pair h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [typeCCoroot, h1, h2]
  exact pairCoroot_comm y x

/-! ## Injectivity of the roots and of the coroots -/

private lemma typeCRoot_injective : Injective (typeCRoot (n := n)) := by
  intro i j hij
  have hi := typeCSnd_ne_signedNeg_typeCFst i
  have hj := typeCSnd_ne_signedNeg_typeCFst j
  have hmem : ∀ z, (z = typeCFst i ∨ z = typeCSnd i) ↔ (z = typeCFst j ∨ z = typeCSnd j) := by
    intro z
    rw [← one_le_pairRoot_dotProduct_iff hi z, ← one_le_pairRoot_dotProduct_iff hj z]
    exact Iff.of_eq (congrArg _ (congrArg (· ⬝ᵥ signedCoweight z) hij))
  rcases Set.pair_eq_pair_iff.mp (Set.ext fun z => by simpa using hmem z) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact typeCPair_injective (Prod.ext h1 h2)
  · exact typeCPair_swap_eq h1 h2

private lemma typeCCoroot_injective : Injective (typeCCoroot (n := n)) := by
  intro i j hij
  have hi := typeCSnd_ne_signedNeg_typeCFst i
  have hj := typeCSnd_ne_signedNeg_typeCFst j
  have hmem : ∀ z, (z = typeCFst i ∨ z = typeCSnd i) ↔ (z = typeCFst j ∨ z = typeCSnd j) := by
    intro z
    rw [← one_le_dotProduct_pairCoroot_iff hi z, ← one_le_dotProduct_pairCoroot_iff hj z]
    exact Iff.of_eq (congrArg _ (congrArg (signedWeight z ⬝ᵥ ·) hij))
  rcases Set.pair_eq_pair_iff.mp (Set.ext fun z => by simpa using hmem z) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact typeCPair_injective (Prod.ext h1 h2)
  · exact typeCPair_swap_eq h1 h2

/-! ## The reflection on root indices -/

/-- Reflection in the root indexed by `i`, acting on root indices. -/
private def typeCReflectionIdx (i j : TypeCIndex n) : TypeCIndex n :=
  typeCMk (signedReflection (typeCFst i) (typeCSnd i) (typeCFst j))
    (signedReflection (typeCFst i) (typeCSnd i) (typeCSnd j))

private lemma typeCReflectionIdx_pair_ne (i j : TypeCIndex n) :
    signedReflection (typeCFst i) (typeCSnd i) (typeCSnd j) ≠
      signedNeg (signedReflection (typeCFst i) (typeCSnd i) (typeCFst j)) := by
  intro hc
  rw [← signedReflection_signedNeg (typeCSnd_ne_signedNeg_typeCFst i)] at hc
  exact typeCSnd_ne_signedNeg_typeCFst j
    (signedReflection_injective (typeCSnd_ne_signedNeg_typeCFst i) hc)

private lemma typeCRoot_typeCReflectionIdx (i j : TypeCIndex n) :
    typeCRoot j - (typeCRoot j ⬝ᵥ typeCCoroot i) • typeCRoot i
      = typeCRoot (typeCReflectionIdx i j) := by
  rw [typeCReflectionIdx, typeCRoot_typeCMk (typeCReflectionIdx_pair_ne i j)]
  exact pairRoot_reflection (typeCSnd_ne_signedNeg_typeCFst i) (typeCFst j) (typeCSnd j)

private lemma typeCCoroot_typeCReflectionIdx (i j : TypeCIndex n) :
    typeCCoroot j - (typeCRoot i ⬝ᵥ typeCCoroot j) • typeCCoroot i
      = typeCCoroot (typeCReflectionIdx i j) := by
  rw [typeCReflectionIdx, typeCCoroot_typeCMk (typeCReflectionIdx_pair_ne i j)]
  exact pairCoroot_reflection (typeCSnd_ne_signedNeg_typeCFst i) (typeCFst j) (typeCSnd j)

private lemma typeCReflectionIdx_involutive (i : TypeCIndex n) :
    Involutive (typeCReflectionIdx i) := by
  intro j
  refine typeCRoot_injective ?_
  rw [← typeCRoot_typeCReflectionIdx, ← typeCRoot_typeCReflectionIdx]
  -- In these coordinates `Module.preReflection` in the `i`-th root is definitionally the map
  -- `v ↦ v - (v ⬝ᵥ typeCCoroot i) • typeCRoot i`, which is the goal left by the two rewrites.
  exact Module.involutive_preReflection (x := typeCRoot i)
    (f := (dotProductBilin ℤ ℤ).flip (typeCCoroot i))
    (typeCRoot_dotProduct_typeCCoroot_self i) (typeCRoot j)

/-- Reflection in the root indexed by `i`, as a permutation of the root indices. -/
private def typeCReflectionPerm (i : TypeCIndex n) : TypeCIndex n ≃ TypeCIndex n :=
  (typeCReflectionIdx_involutive i).toPerm _

@[simp] private lemma typeCReflectionPerm_apply (i j : TypeCIndex n) :
    typeCReflectionPerm i j = typeCReflectionIdx i j := rfl

/-! ## The Bourbaki enumeration of the roots -/

/-- The zero index of `Fin n`, available once a root index is in hand. -/
private def typeCZero (a : Fin n) : Fin n := ⟨0, by have := a.isLt; omega⟩

/-- The enumeration of the root indices by the first index fastest, with the second index twisted so
that the `a`-th simple root comes first. The `b` of that simple root is the clamped successor
`Order.succ a`: the next node, except at the last node, which is its own successor because its
simple root is the long root `2 e_{n-1}`. -/
private def typeCShapeEquiv (n : ℕ) : TypeCIndex n ≃ (Bool × Fin n) × Fin n where
  toFun i := ((i.2.2, Equiv.swap (typeCZero i.1) (Order.succ i.1) i.2.1), i.1)
  invFun p := (p.2, Equiv.swap (typeCZero p.2) (Order.succ p.2) p.1.2, p.1.1)
  left_inv i := by simp
  right_inv p := by simp

/-- The pinned enumeration of the roots of type `Cₙ` by `Fin (2 * n ^ 2)`. -/
def typeCIndexEquiv (n : ℕ) : TypeCIndex n ≃ Fin (2 * n ^ 2) :=
  ((typeCShapeEquiv n).trans
      (((finTwoEquiv.symm.prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv).prodCongr
        (Equiv.refl (Fin n)))).trans (finProdFinEquiv.trans (finCongr (by ring)))

/-- The pinned simply connected root datum of type `Cₙ`.

Both lattices are `Fin n → ℤ`: the character lattice in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. The `2 * n ^ 2` roots are the classical
`± e_a ± e_b` with `a ≠ b` and `± 2 e_a`, enumerated with the simple roots first; see
`TauCeti.DynkinType.root_typeCSimpleIndex`. -/
def typeCSimplyConnectedRootDatum (n : ℕ) :
    RootDatum (Fin (2 * n ^ 2)) (Fin n → ℤ) (Fin n → ℤ) where
  toLinearMap := dotProductBilin ℤ ℤ
  root := ⟨fun k => typeCRoot ((typeCIndexEquiv n).symm k),
    typeCRoot_injective.comp (typeCIndexEquiv n).symm.injective⟩
  coroot := ⟨fun k => typeCCoroot ((typeCIndexEquiv n).symm k),
    typeCCoroot_injective.comp (typeCIndexEquiv n).symm.injective⟩
  root_coroot_two k := typeCRoot_dotProduct_typeCCoroot_self _
  reflectionPerm k := ((typeCIndexEquiv n).symm.trans
    (typeCReflectionPerm ((typeCIndexEquiv n).symm k))).trans (typeCIndexEquiv n)
  reflectionPerm_root k l := by
    simpa using
      typeCRoot_typeCReflectionIdx ((typeCIndexEquiv n).symm k) ((typeCIndexEquiv n).symm l)
  reflectionPerm_coroot k l := by
    simpa using
      typeCCoroot_typeCReflectionIdx ((typeCIndexEquiv n).symm k) ((typeCIndexEquiv n).symm l)

/-- The pinned pairing of type `Cₙ` is the dot product of the two lattices. -/
@[simp] theorem toLinearMap_typeCSimplyConnectedRootDatum (x y : Fin n → ℤ) :
    (typeCSimplyConnectedRootDatum n).toLinearMap x y = x ⬝ᵥ y := (rfl)

private lemma root_typeCSimplyConnectedRootDatum (k : Fin (2 * n ^ 2)) :
    (typeCSimplyConnectedRootDatum n).root k = typeCRoot ((typeCIndexEquiv n).symm k) :=
  rfl

private lemma coroot_typeCSimplyConnectedRootDatum (k : Fin (2 * n ^ 2)) :
    (typeCSimplyConnectedRootDatum n).coroot k = typeCCoroot ((typeCIndexEquiv n).symm k) :=
  rfl

private lemma pairing_typeCSimplyConnectedRootDatum (k l : Fin (2 * n ^ 2)) :
    (typeCSimplyConnectedRootDatum n).pairing k l =
      (typeCSimplyConnectedRootDatum n).root k ⬝ᵥ (typeCSimplyConnectedRootDatum n).coroot l :=
  rfl

/-- Every Cartan integer between roots of the pinned type `C` datum has absolute value at most
two. -/
theorem abs_pairing_typeCSimplyConnectedRootDatum_le_two (k l : Fin (2 * n ^ 2)) :
    |(typeCSimplyConnectedRootDatum n).pairing k l| ≤ 2 := by
  rw [pairing_typeCSimplyConnectedRootDatum, root_typeCSimplyConnectedRootDatum,
    coroot_typeCSimplyConnectedRootDatum]
  exact abs_pairRoot_dotProduct_pairCoroot_le_two (typeCSnd_ne_signedNeg_typeCFst _)

/-! ## The root and the coroot at an arbitrary index

Away from the simple indices, a root of the datum is named by encoding a root index with
`typeCIndexEquiv`, and the five lemmas below say which vector the encoded index denotes. Together
they cover every index, since `typeCIndexEquiv` is a bijection. -/

/-- The root at the encoded index `(a, b, s)` with `a < b`: the short root `± (e_a - e_b)`. -/
@[simp]
theorem root_typeCIndexEquiv_of_lt {a b : Fin n} (h : a < b) (s : Bool) :
    (typeCSimplyConnectedRootDatum n).root (typeCIndexEquiv n (a, b, s))
      = signedWeight (a, s) - signedWeight (b, s) := by
  rw [root_typeCSimplyConnectedRootDatum, Equiv.symm_apply_apply, typeCRoot_mk_of_lt h]

/-- The root at the encoded index `(a, b, s)` with `b ≤ a`: the short root `± (e_a + e_b)`, and the
long root `± 2 e_a` on the diagonal `b = a`. -/
@[simp]
theorem root_typeCIndexEquiv_of_not_lt {a b : Fin n} (h : ¬ a < b) (s : Bool) :
    (typeCSimplyConnectedRootDatum n).root (typeCIndexEquiv n (a, b, s))
      = signedWeight (a, s) + signedWeight (b, s) := by
  rw [root_typeCSimplyConnectedRootDatum, Equiv.symm_apply_apply, typeCRoot_mk_of_not_lt h]

/-- The coroot at the encoded index `(a, b, s)` with `a < b`, that of a short root: the root
itself, in the cocharacter coordinates. -/
@[simp]
theorem coroot_typeCIndexEquiv_of_lt {a b : Fin n} (h : a < b) (s : Bool) :
    (typeCSimplyConnectedRootDatum n).coroot (typeCIndexEquiv n (a, b, s))
      = signedCoweight (a, s) - signedCoweight (b, s) := by
  rw [coroot_typeCSimplyConnectedRootDatum, Equiv.symm_apply_apply, typeCCoroot_mk_of_lt h]

/-- The coroot at the encoded index `(a, b, s)` with `b < a`, that of a short root: the root
itself, in the cocharacter coordinates. -/
@[simp]
theorem coroot_typeCIndexEquiv_of_gt {a b : Fin n} (h : b < a) (s : Bool) :
    (typeCSimplyConnectedRootDatum n).coroot (typeCIndexEquiv n (a, b, s))
      = signedCoweight (a, s) + signedCoweight (b, s) := by
  rw [coroot_typeCSimplyConnectedRootDatum, Equiv.symm_apply_apply, typeCCoroot_mk_of_gt h]

/-- The coroot at the encoded diagonal index `(a, a, s)`, that of the long root `± 2 e_a`: the
halved `± e_a`. -/
@[simp]
theorem coroot_typeCIndexEquiv_diag (a : Fin n) (s : Bool) :
    (typeCSimplyConnectedRootDatum n).coroot (typeCIndexEquiv n (a, a, s))
      = signedCoweight (a, s) := by
  rw [coroot_typeCSimplyConnectedRootDatum, Equiv.symm_apply_apply, typeCCoroot_mk_diag]

/-! ## The simple roots and coroots -/

/-- There is room for the first `n` indices in the type `Cₙ` enumeration of `2 * n ^ 2` roots. -/
private lemma typeC_le_two_mul_sq (n : ℕ) : n ≤ 2 * n ^ 2 :=
  le_trans (Nat.le_self_pow (by norm_num) n) (Nat.le_mul_of_pos_left (n ^ 2) (by norm_num))

/-- The `i`-th simple root of type `Cₙ` sits at root index `i`, the Bourbaki node `i + 1`. -/
def typeCSimpleIndex (n : ℕ) (i : Fin n) : Fin (2 * n ^ 2) :=
  Fin.castLE (typeC_le_two_mul_sq n) i

@[simp] lemma typeCSimpleIndex_val (i : Fin n) : (typeCSimpleIndex n i : ℕ) = i := by
  simp [typeCSimpleIndex]

lemma typeCSimpleIndex_injective : Injective (typeCSimpleIndex n) :=
  Fin.castLE_injective (typeC_le_two_mul_sq n)

private lemma typeCIndexEquiv_symm_typeCSimpleIndex (i : Fin n) :
    (typeCIndexEquiv n).symm (typeCSimpleIndex n i) = (i, Order.succ i, false) := by
  have hi : (i : ℕ) < n := i.isLt
  simp [typeCIndexEquiv, typeCShapeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
    typeCSimpleIndex, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, finTwoEquiv, typeCZero]

/-- The `i`-th simple root of type `Cₙ`, in fundamental-weight coordinates. -/
private def typeCSimpleRoot (i : Fin n) : Fin n → ℤ := typeCRoot (i, Order.succ i, false)

/-- The `i`-th simple coroot of type `Cₙ`, in simple-coroot coordinates. -/
private def typeCSimpleCoroot (i : Fin n) : Fin n → ℤ := typeCCoroot (i, Order.succ i, false)

private lemma root_typeCSimpleIndex_eq (i : Fin n) :
    (typeCSimplyConnectedRootDatum n).root (typeCSimpleIndex n i) = typeCSimpleRoot i := by
  rw [root_typeCSimplyConnectedRootDatum, typeCIndexEquiv_symm_typeCSimpleIndex]
  rfl

private lemma coroot_typeCSimpleIndex_eq (i : Fin n) :
    (typeCSimplyConnectedRootDatum n).coroot (typeCSimpleIndex n i) = typeCSimpleCoroot i := by
  rw [coroot_typeCSimplyConnectedRootDatum, typeCIndexEquiv_symm_typeCSimpleIndex]
  rfl

private lemma typeCFst_simple (i : Fin n) :
    typeCFst ((i, Order.succ i, false) : TypeCIndex n) = (i, false) := rfl

private lemma typeCSnd_simple_of_lt {i : Fin n} (h : (i : ℕ) + 1 < n) :
    typeCSnd ((i, Order.succ i, false) : TypeCIndex n) = (Order.succ i, true) := by
  have hlt : i < Order.succ i := by rw [Fin.lt_def, Fin.val_orderSucc_of_lt h]; omega
  rw [typeCSnd_mk_of_lt hlt]
  simp

private lemma typeCSnd_simple_of_last {i : Fin n} (h : (i : ℕ) + 1 = n) :
    typeCSnd ((i, Order.succ i, false) : TypeCIndex n) = (i, false) := by
  rw [Fin.orderSucc_eq_self_of_not_lt (i := i) (by omega), typeCSnd_mk_of_not_lt (lt_irrefl i)]

private lemma typeCSimpleRoot_of_lt {i : Fin n} (h : (i : ℕ) + 1 < n) :
    typeCSimpleRoot i = weight n (i : ℕ) - weight n ((i : ℕ) + 1) := by
  rw [typeCSimpleRoot, typeCRoot, typeCFst_simple, typeCSnd_simple_of_lt h, pairRoot_def,
    signedWeight_false, signedWeight_true, Fin.val_orderSucc_of_lt h]
  exact (sub_eq_add_neg _ _).symm

private lemma typeCSimpleRoot_of_last {i : Fin n} (h : (i : ℕ) + 1 = n) :
    typeCSimpleRoot i = weight n (i : ℕ) + weight n (i : ℕ) := by
  rw [typeCSimpleRoot, typeCRoot, typeCFst_simple, typeCSnd_simple_of_last h, pairRoot_def,
    signedWeight_false]

private lemma typeCSimpleCoroot_eq (i : Fin n) :
    typeCSimpleCoroot i = coweight n (i : ℕ) - coweight n ((i : ℕ) + 1) := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt i.isLt) with h | h
  · rw [typeCSimpleCoroot, typeCCoroot, typeCFst_simple, typeCSnd_simple_of_last h,
      pairCoroot_self, signedCoweight_false, coweight_eq_zero_of_le (a := (i : ℕ) + 1) (by omega),
      sub_zero]
  · have hne : ((i : Fin n), false) ≠ ((Order.succ i : Fin n), true) := by simp
    rw [typeCSimpleCoroot, typeCCoroot, typeCFst_simple, typeCSnd_simple_of_lt h,
      pairCoroot_of_ne hne, signedCoweight_false, signedCoweight_true, Fin.val_orderSucc_of_lt h]
    exact (sub_eq_add_neg _ _).symm

private lemma typeCSimpleCoroot_eq_single (i : Fin n) : typeCSimpleCoroot i = Pi.single i 1 := by
  rw [typeCSimpleCoroot_eq]
  funext k
  simp only [coweight_apply, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- **The simple roots are the rows of the Cartan matrix.** In the fundamental-weight basis the
`i`-th simple root of the pinned type `Cₙ` datum is the `i`-th row of `CartanMatrix.C n`, which is
what pins the character lattice as the weight lattice. -/
@[simp] theorem root_typeCSimpleIndex (i : Fin n) :
    (typeCSimplyConnectedRootDatum n).root (typeCSimpleIndex n i) =
      fun k => CartanMatrix.C n i k := by
  rw [root_typeCSimpleIndex_eq]
  funext k
  have hk := k.isLt
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt i.isLt) with h | h
  · rw [typeCSimpleRoot_of_last h]
    simp only [weight_apply, Pi.add_apply, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  · rw [typeCSimpleRoot_of_lt h]
    simp only [weight_apply, Pi.sub_apply, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega

/-- **The simple coroots are the standard basis.** This is what pins the cocharacter lattice as the
coroot lattice, so that the datum is the simply connected one. -/
@[simp] theorem coroot_typeCSimpleIndex (i : Fin n) :
    (typeCSimplyConnectedRootDatum n).coroot (typeCSimpleIndex n i) = Pi.single i 1 := by
  rw [coroot_typeCSimpleIndex_eq, typeCSimpleCoroot_eq_single]

/-! ## The pinned base -/

private lemma typeCRoot_false_mem (a b : Fin n) :
    typeCRoot (a, b, false) ∈ AddSubmonoid.closure (range (typeCSimpleRoot (n := n))) := by
  have hS : ∀ c d : Fin n, (c : ℕ) + 1 = d → weight n c - weight n d ∈
      AddSubmonoid.closure (range (typeCSimpleRoot (n := n))) := fun c d h =>
    AddSubmonoid.subset_closure ⟨c, by rw [typeCSimpleRoot_of_lt (h ▸ d.isLt), h]⟩
  by_cases hab : a < b
  · rw [typeCRoot_mk_of_lt hab, signedWeight_false, signedWeight_false]
    exact AddSubmonoid.sub_mem_of_consecutive_sub_mem_fin _ (fun c : Fin n => weight n c) hS
      hab.le
  · rw [typeCRoot_mk_of_not_lt hab, signedWeight_false, signedWeight_false]
    exact AddSubmonoid.add_mem_of_consecutive_sub_mem_fin _ (fun c : Fin n => weight n c) hS
      (fun c hc => AddSubmonoid.subset_closure ⟨c, typeCSimpleRoot_of_last hc⟩) a b

private lemma typeCCoroot_false_mem (a b : Fin n) :
    typeCCoroot (a, b, false) ∈ AddSubmonoid.closure (range (typeCSimpleCoroot (n := n))) := by
  rw [funext (typeCSimpleCoroot_eq (n := n))]
  have hmem (c : Fin n) : coweight n c ∈
      AddSubmonoid.closure (range fun i : Fin n => coweight n i - coweight n (i + 1)) := by
    simpa [coweight_eq_zero_of_le (n := n) le_rfl] using
      sub_mem_closure_of_le (coweight n) le_rfl c.isLt.le
  rcases lt_trichotomy a b with hab | rfl | hab
  · rw [typeCCoroot_mk_of_lt hab, signedCoweight_false, signedCoweight_false]
    exact sub_mem_closure_of_le (coweight n) b.isLt.le hab.le
  · rw [typeCCoroot_mk_diag, signedCoweight_false]
    exact hmem a
  · rw [typeCCoroot_mk_of_gt hab, signedCoweight_false, signedCoweight_false]
    exact add_mem (hmem a) (hmem b)

private lemma typeCRoot_true (a b : Fin n) :
    typeCRoot (a, b, true) = -typeCRoot (a, b, false) := by
  by_cases hab : a < b
  · rw [typeCRoot_mk_of_lt hab, typeCRoot_mk_of_lt hab, signedWeight_true, signedWeight_true,
      signedWeight_false, signedWeight_false]
    abel
  · rw [typeCRoot_mk_of_not_lt hab, typeCRoot_mk_of_not_lt hab, signedWeight_true,
      signedWeight_true, signedWeight_false, signedWeight_false]
    abel

private lemma typeCCoroot_true (a b : Fin n) :
    typeCCoroot (a, b, true) = -typeCCoroot (a, b, false) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [typeCCoroot_mk_of_lt hab, typeCCoroot_mk_of_lt hab, signedCoweight_true,
      signedCoweight_true, signedCoweight_false, signedCoweight_false]
    abel
  · subst hab
    rw [typeCCoroot_mk_diag, typeCCoroot_mk_diag, signedCoweight_true, signedCoweight_false]
  · rw [typeCCoroot_mk_of_gt hab, typeCCoroot_mk_of_gt hab, signedCoweight_true,
      signedCoweight_true, signedCoweight_false, signedCoweight_false]
    abel

/-- The simple roots are the rows of `CartanMatrix.C n`, whose determinant is `2` for `0 < n`. -/
private lemma linearIndependent_typeCSimpleRoot (n : ℕ) :
    LinearIndependent ℤ (typeCSimpleRoot (n := n)) := by
  have h : typeCSimpleRoot (n := n) = fun i => CartanMatrix.C n i := by
    funext i k
    rw [← root_typeCSimpleIndex_eq, root_typeCSimpleIndex]
  rw [h]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact linearIndependent_empty_type
  · exact Matrix.linearIndependent_rows_of_det_ne_zero (by rw [CartanMatrix.C_det hn]; norm_num)

private lemma linearIndependent_typeCSimpleCoroot (n : ℕ) :
    LinearIndependent ℤ (typeCSimpleCoroot (n := n)) := by
  rw [funext typeCSimpleCoroot_eq_single]
  exact Pi.linearIndependent_single_one (Fin n) ℤ

/-- The support of the pinned base of type `Cₙ`: the first `n` root indices. -/
private def typeCSimpleSupport (n : ℕ) : Finset (Fin (2 * n ^ 2)) :=
  simpleSupport (typeCSimpleIndex_injective (n := n))

private lemma image_root_typeCSimpleSupport :
    (typeCSimplyConnectedRootDatum n).root '' (typeCSimpleSupport n : Set (Fin (2 * n ^ 2)))
      = range (typeCSimpleRoot (n := n)) := by
  rw [typeCSimpleSupport, image_simpleSupport]
  exact congrArg range (funext fun i => root_typeCSimpleIndex_eq i)

private lemma image_coroot_typeCSimpleSupport :
    (typeCSimplyConnectedRootDatum n).coroot '' (typeCSimpleSupport n : Set (Fin (2 * n ^ 2)))
      = range (typeCSimpleCoroot (n := n)) := by
  rw [typeCSimpleSupport, image_simpleSupport]
  exact congrArg range (funext fun i => coroot_typeCSimpleIndex_eq i)

/-- The Bourbaki-numbered base of the pinned simply connected root datum of type `Cₙ`. Its support
is the set of the first `n` root indices, carrying the simple roots in Bourbaki order. -/
def typeCSimplyConnectedBase (n : ℕ) : (typeCSimplyConnectedRootDatum n).Base where
  support := typeCSimpleSupport n
  linearIndepOn_root := linearIndepOn_simpleSupport _ _ <| by
    rw [funext (f := (typeCSimplyConnectedRootDatum n).root ∘ typeCSimpleIndex n)
      root_typeCSimpleIndex_eq]
    exact linearIndependent_typeCSimpleRoot n
  linearIndepOn_coroot := linearIndepOn_simpleSupport _ _ <| by
    rw [funext (f := (typeCSimplyConnectedRootDatum n).coroot ∘ typeCSimpleIndex n)
      coroot_typeCSimpleIndex_eq]
    exact linearIndependent_typeCSimpleCoroot n
  root_mem_or_neg_mem k := by
    rw [image_root_typeCSimpleSupport, root_typeCSimplyConnectedRootDatum]
    generalize (typeCIndexEquiv n).symm k = i
    obtain ⟨a, b, s⟩ := i
    cases s
    · exact Or.inl (typeCRoot_false_mem a b)
    · exact Or.inr (by rw [typeCRoot_true, neg_neg]; exact typeCRoot_false_mem a b)
  coroot_mem_or_neg_mem k := by
    rw [image_coroot_typeCSimpleSupport, coroot_typeCSimplyConnectedRootDatum]
    generalize (typeCIndexEquiv n).symm k = i
    obtain ⟨a, b, s⟩ := i
    cases s
    · exact Or.inl (typeCCoroot_false_mem a b)
    · exact Or.inr (by rw [typeCCoroot_true, neg_neg]; exact typeCCoroot_false_mem a b)

/-- **The support of the pinned base of type `Cₙ` is the set of the first `n` root indices**, which
by `TauCeti.DynkinType.root_typeCSimpleIndex` carry the simple roots in Bourbaki order. -/
@[simp] theorem mem_support_typeCSimplyConnectedBase {k : Fin (2 * n ^ 2)} :
    k ∈ (typeCSimplyConnectedBase n).support ↔ (k : ℕ) < n :=
  mem_simpleSupport_iff_lt (typeCSimpleIndex_injective (n := n)) (fun _ ↦ typeCSimpleIndex_val _)

/-- The pairing of two Bourbaki-indexed simple roots and coroots is the corresponding entry of
the type-`C` Cartan matrix. -/
@[simp] lemma pairing_typeCSimpleIndex (i j : Fin n) :
    (typeCSimplyConnectedRootDatum n).pairing (typeCSimpleIndex n i) (typeCSimpleIndex n j) =
      CartanMatrix.C n i j := by
  rw [pairing_typeCSimplyConnectedRootDatum, root_typeCSimpleIndex, coroot_typeCSimpleIndex,
    dotProduct_single, mul_one]

/-- **The pinned datum of type `Cₙ` has Cartan type `C n`.** Its Bourbaki-numbered base realizes the
standard Cartan matrix `CartanMatrix.C n`, with the node numbering of `TauCeti.DynkinType`. -/
theorem hasCartanType_typeCSimplyConnectedRootDatum (n : ℕ) :
    HasCartanType (typeCSimplyConnectedRootDatum n) (typeCSimplyConnectedBase n) (.C n) :=
  hasCartanType_of_pairing_eq (typeCSimpleIndex_injective (n := n)) rfl fun i j =>
    (pairing_typeCSimpleIndex i j).trans (by simp)

/-- **The coroots of the pinned type `Cₙ` datum span the cocharacter lattice.** This is the simply
connected lattice condition required by the pinned Chevalley--Demazure construction. Its
counterpart for the roots is deliberately absent: they span the root lattice, which sits inside the
weight lattice with index `2` whenever `0 < n` (Bourbaki, Plate III; at `n = 0` both lattices are
trivial). -/
theorem corootSpan_typeCSimplyConnectedRootDatum_eq_top (n : ℕ) :
    (typeCSimplyConnectedRootDatum n).corootSpan ℤ = ⊤ :=
  corootSpan_eq_top_of_coroot_eq_single (coroot_typeCSimpleIndex (n := n))

end DynkinType

end TauCeti

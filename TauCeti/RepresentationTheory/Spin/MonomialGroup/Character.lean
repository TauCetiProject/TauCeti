/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.Spin.MonomialGroup.Spinor

/-!
# The representations of the group of signed monomials in which `ε` acts trivially

Let `b` be an orthogonal basis of a quadratic space `(V, Q)` whose generators square to `±1`, and
let `G = CliffordAlgebra.monomialGroup Q b` be the finite group of the signed monomials `±e_s`,
with central element `ε = -1`. Since `ε` is central of order two, it acts on an irreducible
representation of `G` by `1` or by `-1`. The representations in which `ε` acts by `-1` are the
Clifford modules, classified through the spinor module in
`TauCeti.RepresentationTheory.Spin.MonomialGroup.Spinor`. This file classifies the others.

A representation in which `ε` acts by `1` is a representation of `G / ⟨ε⟩`, which is the
elementary abelian group `(ZMod 2) ^ n` (`CliffordAlgebra.monomialGroupQuotientEquiv`). Any two
signed monomials commute up to `ε` and every signed monomial squares to `1` or `ε`, so in such a
representation the operators commute and square to the identity. Over a field of characteristic
not two, Schur's lemma makes each of them `±1` on an irreducible representation, without any
algebraic closure or finite dimension assumption. So an irreducible representation in which `ε`
acts by `1` is the line of a character trivial on `ε`, that is of exactly one of the `2 ^ n` sign
characters `CliffordAlgebra.monomialGroupCharacter hb hQ t : ±e_s ↦ (-1) ^ #(s ∩ t)`.

Together with the spinor classification this describes all the irreducible representations of `G`
over a separably closed field of characteristic not two; in dimension one, for instance, all four
of them are one-dimensional.

## Main results

* `TauCeti.monomialGroup_map_neg_one_eq_one_or_eq_neg_one`: `ε` acts on an irreducible
  representation by `1` or by `-1`.
* `TauCeti.monomialGroup_existsUnique_nonempty_equiv_ofLinearCharacter`: an irreducible
  representation in which `ε` acts by `1` is equivalent to the line of the sign character `χ_t`
  for exactly one index set `t`.
* `TauCeti.monomialGroup_finrank_eq_one_of_map_neg_one_eq_one`: such a representation is a line.
* `TauCeti.monomialGroup_finrank_eq_one_of_finrank_eq_one`: in dimension one, over a separably
  closed field, every irreducible representation is a line.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open CliffordAlgebra Module Representation

namespace TauCeti

/-- **The central element `ε` acts on an irreducible representation by `±1`**: it is central and
squares to `1`, so it acts by an involutive equivariant endomorphism, which Schur's lemma makes
`±1`. -/
theorem monomialGroup_map_neg_one_eq_one_or_eq_neg_one {R M I : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {Q : QuadraticForm R M} (v : I → M) {k : Type*} [Field k]
    {W : Type*} [AddCommGroup W] [Module k W] (ρ : Representation k (monomialGroup Q v) W)
    [ρ.IsIrreducible] :
    ρ ⟨-1, neg_one_mem_monomialGroup v⟩ = 1 ∨ ρ ⟨-1, neg_one_mem_monomialGroup v⟩ = -1 := by
  set ε : monomialGroup Q v := ⟨-1, neg_one_mem_monomialGroup v⟩
  let T : IntertwiningMap ρ ρ := (ρ ε).intertwiningMap_of_isIntertwiningMap ρ ρ fun h w ↦ by
    rw [← Module.End.mul_apply, ← map_mul,
      ← Subgroup.mem_center_iff.mp (neg_one_mem_center_monomialGroup v) h, map_mul,
      Module.End.mul_apply]
  have hεε : ε * ε = 1 := Subtype.ext (Units.ext (by simp [ε]))
  have hT : T * T = 1 := DFunLike.ext _ _ fun w ↦ by
    simp [T, ← Module.End.mul_apply, ← map_mul, hεε]
  rcases (inferInstance : ρ.IsIrreducible).eq_one_or_eq_neg_one_of_mul_self_eq_one hT with h | h
  · exact Or.inl (LinearMap.ext fun w ↦ by simpa [T] using DFunLike.congr_fun h w)
  · exact Or.inr (LinearMap.ext fun w ↦ by simpa [T] using DFunLike.congr_fun h w)

section Classification

variable {R M I : Type*} [CommRing R] [Nontrivial R] [Invertible (2 : R)] [AddCommGroup M]
  [Module R M] {Q : QuadraticForm R M} [LinearOrder I] {b : Basis I R M}
  {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]

omit [Nontrivial R] in
/-- In a representation in which `ε` acts by `1`, every signed monomial acts by an operator
commuting with the whole action and squaring to the identity. On an irreducible representation it
therefore acts by `1` or by `-1`. -/
private theorem map_eq_one_or_eq_neg_one_of_map_neg_one_eq_one
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (ρ : Representation k (monomialGroup Q b) W) [ρ.IsIrreducible]
    (hρ : ρ ⟨-1, neg_one_mem_monomialGroup b⟩ = 1) (g : monomialGroup Q b) :
    ρ g = 1 ∨ ρ g = -1 := by
  -- Signed monomials commute up to `ε`, which acts trivially.
  have hcomm (h : monomialGroup Q b) : ρ g * ρ h = ρ h * ρ g := by
    rcases (monomialGroup_commuteOrNeg b
        (fun _ _ hij ↦ QuadraticMap.associated_isOrtho.mp (hb hij)) g h).out with hc | hc
    · have hgh : g * h = h * g := Subtype.ext hc.eq
      rw [← map_mul, hgh, map_mul]
    · have hgh : g * h = ⟨-1, neg_one_mem_monomialGroup b⟩ * (h * g) :=
        Subtype.ext (by simpa using hc.eq)
      rw [← map_mul, hgh, map_mul, hρ, one_mul, map_mul]
  let T : IntertwiningMap ρ ρ := (ρ g).intertwiningMap_of_isIntertwiningMap ρ ρ fun h w ↦ by
    rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply]
  -- Every signed monomial squares to `1` or `ε`, which both act trivially.
  have hT : T * T = 1 := DFunLike.ext _ _ fun w ↦ by
    have hsq : ρ g * ρ g = 1 := by
      rw [← map_mul]
      rcases monomialGroup_mul_self_eq_one_or hb hQ g with h | h <;> simp [h, hρ]
    simpa [T] using DFunLike.congr_fun hsq w
  rcases (inferInstance : ρ.IsIrreducible).eq_one_or_eq_neg_one_of_mul_self_eq_one hT with h | h
  · exact Or.inl (LinearMap.ext fun w ↦ by simpa [T] using DFunLike.congr_fun h w)
  · exact Or.inr (LinearMap.ext fun w ↦ by simpa [T] using DFunLike.congr_fun h w)

/-- **The irreducible representations in which `ε` acts by `1` are the sign characters.** For an
orthogonal basis indexed by a finite type whose generators square to `±1`, over a field of
characteristic not two, an irreducible representation of the group of signed monomials in which
`ε = -1` acts by `1` is equivalent to the line of the sign character `χ_t : ±e_s ↦ (-1) ^ #(s ∩ t)`
for exactly one index set `t`. -/
theorem monomialGroup_existsUnique_nonempty_equiv_ofLinearCharacter [Finite I] [NeZero (2 : k)]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (ρ : Representation k (monomialGroup Q b) W) [ρ.IsIrreducible]
    (hρ : ρ ⟨-1, neg_one_mem_monomialGroup b⟩ = 1) :
    ∃! t : Finset I, Nonempty (ρ.Equiv (ofLinearCharacter
      ((Units.map (Int.castRingHom k : ℤ →* k)).comp (monomialGroupCharacter hb hQ t)))) := by
  have hirr : ρ.IsIrreducible := inferInstance
  have := hirr.nontrivial
  -- A scalar operator determines its scalar, since `W` is nonzero.
  have hscalar {x y : kˣ} (h : (x : k) • (1 : Module.End k W) = (y : k) • 1) : x = y :=
    Units.ext (smul_left_injective k one_ne_zero h)
  -- Every signed monomial acts by a sign, and these signs form a character trivial on `ε`.
  have hsign (g : monomialGroup Q b) : ∃ c : kˣ, ρ g = (c : k) • 1 := by
    rcases map_eq_one_or_eq_neg_one_of_map_neg_one_eq_one hb hQ ρ hρ g with h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
  choose c hc using hsign
  let ψ : monomialGroup Q b →* kˣ := .mk' c fun g h ↦ hscalar <| by
    rw [← hc, map_mul, hc, hc, Units.val_mul, mul_smul, smul_one_mul]
  have hψ : ψ ⟨-1, neg_one_mem_monomialGroup b⟩ = 1 := hscalar (by simp [ψ, ← hc, hρ])
  obtain ⟨t, ht, huniq⟩ := existsUnique_monomialGroupCharacter_eq hb hQ ψ hψ
  refine ⟨t, (hirr.nonempty_equiv_ofLinearCharacter_iff _).mpr fun g ↦ by rw [ht]; exact hc g,
    fun t' ht' ↦ huniq t' (MonoidHom.ext fun g ↦ hscalar ?_)⟩
  rw [← (hirr.nonempty_equiv_ofLinearCharacter_iff _).mp ht' g]
  exact hc g

/-- **An irreducible representation in which `ε` acts by `1` is a line**, for an orthogonal basis
indexed by a finite type whose generators square to `±1`, over a field of characteristic not two. -/
theorem monomialGroup_finrank_eq_one_of_map_neg_one_eq_one [Finite I] [NeZero (2 : k)]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (ρ : Representation k (monomialGroup Q b) W) [ρ.IsIrreducible]
    (hρ : ρ ⟨-1, neg_one_mem_monomialGroup b⟩ = 1) :
    finrank k W = 1 := by
  obtain ⟨t, ⟨e⟩, -⟩ := monomialGroup_existsUnique_nonempty_equiv_ofLinearCharacter hb hQ ρ hρ
  rw [e.toLinearEquiv.finrank_eq, finrank_self]

end Classification

/-- **In dimension one every irreducible representation is a line.** Over a separably closed field
of characteristic not two, for an orthogonal basis of a line whose generator squares to `±1`, the
group of signed monomials has order four, and each of its irreducible representations is
one-dimensional: those in which `ε` acts by `1` are sign characters, and those in which it acts by
`-1` are spinor representations of dimension `2 ^ 0`. -/
theorem monomialGroup_finrank_eq_one_of_finrank_eq_one {F : Type*} [Field F] [IsSepClosed F]
    [Invertible (2 : F)] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} {I : Type*} [LinearOrder I] {b : Basis I F V}
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (hV : finrank F V = 1) {W : Type*} [AddCommGroup W] [Module F W]
    (ρ : Representation F (monomialGroup Q b) W) [ρ.IsIrreducible] :
    finrank F W = 1 := by
  have : NeZero (2 : F) := ⟨Invertible.ne_zero 2⟩
  have : Finite I := Module.Finite.finite_basis b
  rcases monomialGroup_map_neg_one_eq_one_or_eq_neg_one b ρ with hρ | hρ
  · exact monomialGroup_finrank_eq_one_of_map_neg_one_eq_one hb hQ ρ hρ
  · simpa using monomialGroup_finrank_eq_two_pow_of_odd hb hQ (l := 0) (by simpa using hV) ρ hρ

end TauCeti
